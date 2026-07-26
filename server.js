const express = require('express');
const http = require('http');
const { Server } = require('socket.io');
const fs = require('fs');
const path = require('path');

const app = express();
const server = http.createServer(app);
const io = new Server(server, { cors: { origin: '*' } });
app.use(express.static(__dirname));

const config = JSON.parse(fs.readFileSync(path.join(__dirname, 'config.json'), 'utf8'));
const ROSTER = config.roster;
const TIER = config.tier;
const QUESTIONS = config.questions;
const TOTAL_Q = QUESTIONS.length;

/* ── Room Code ──────────────────────────────────────── */
let roomCode = Math.random().toString(36).substring(2, 6).toUpperCase();
let verifiedSockets = new Set();

/* ── Game State ─────────────────────────────────────── */
let state = {
  phase: 'lobby',
  currentQ: -1,
  timerDuration: 0,
  phaseStart: 0,
  prevStandings: [],
  results: null,
  essayOrder: null
};

let players = {};
let answers = {};
let essays = {};
let votes = {};
let socketToName = {};
let timerHandle = null;

/* ── Levenshtein / Similarity ───────────────────────── */
function levenshtein(a, b) {
  const m = a.length, n = b.length;
  const dp = Array.from({ length: m + 1 }, () => new Array(n + 1).fill(0));
  for (let i = 0; i <= m; i++) dp[i][0] = i;
  for (let j = 0; j <= n; j++) dp[0][j] = j;
  for (let i = 1; i <= m; i++)
    for (let j = 1; j <= n; j++)
      dp[i][j] = Math.min(dp[i - 1][j] + 1, dp[i][j - 1] + 1, dp[i - 1][j - 1] + (a[i - 1] === b[j - 1] ? 0 : 1));
  return dp[m][n];
}
function similarityPct(input, reference) {
  const a = (input || '').toLowerCase().trim();
  const b = (reference || '').toLowerCase().trim();
  if (!a) return 0;
  const dist = levenshtein(a, b);
  const maxLen = Math.max(a.length, b.length, 1);
  return Math.max(0, Math.round((1 - dist / maxLen) * 100));
}

/* ── Grading ────────────────────────────────────────── */
function gradeQuestion(qIdx) {
  const q = QUESTIONS[qIdx];
  const qAnswers = answers[qIdx] || {};
  const results = [];
  const answeredNames = new Set(Object.keys(qAnswers));

  if (q.type === 'mc') {
    const correct = [], wrong = [];
    for (const [name, ans] of Object.entries(qAnswers)) {
      if (ans.value === q.correct) correct.push({ name, tMs: ans.tMs });
      else wrong.push({ name, value: ans.value });
    }
    correct.sort((a, b) => a.tMs - b.tMs);
    correct.forEach((a, i) => { a.correct = true; a.points = TIER[i] || 0; a.rank = i + 1; });
    wrong.forEach(a => { a.correct = false; a.points = 0; });
    results.push(...correct, ...wrong);
  } else if (q.type === 'similarity') {
    const list = Object.entries(qAnswers).map(([name, ans]) => ({
      name, tMs: ans.tMs, value: ans.value, sim: similarityPct(ans.value, q.reference)
    }));
    list.sort((a, b) => b.sim - a.sim || a.tMs - b.tMs);
    list.forEach((a, i) => { a.correct = a.sim >= 50; a.points = i < 5 ? TIER[i] : 0; a.rank = i + 1; });
    results.push(...list);
  } else if (q.type === 'dragmatch') {
    const isCorrect = (a) => a.value && a.value.A === q.correct.A && a.value.B === q.correct.B && a.value.C === q.correct.C;
    const correct = [], wrong = [];
    for (const [name, ans] of Object.entries(qAnswers)) {
      if (isCorrect(ans)) correct.push({ name, tMs: ans.tMs });
      else wrong.push({ name });
    }
    correct.sort((a, b) => a.tMs - b.tMs);
    correct.forEach((a, i) => { a.correct = true; a.points = TIER[i] || 0; a.rank = i + 1; });
    wrong.forEach(a => { a.correct = false; a.points = 0; });
    results.push(...correct, ...wrong);
  } else if (q.type === 'dragclassify') {
    const isCorrect = (a) => a.value && q.scenarios.every(s => a.value[s.key] === q.correct[s.key]);
    const correct = [], wrong = [];
    for (const [name, ans] of Object.entries(qAnswers)) {
      if (isCorrect(ans)) correct.push({ name, tMs: ans.tMs });
      else wrong.push({ name });
    }
    correct.sort((a, b) => a.tMs - b.tMs);
    correct.forEach((a, i) => { a.correct = true; a.points = TIER[i] || 0; a.rank = i + 1; });
    wrong.forEach(a => { a.correct = false; a.points = 0; });
    results.push(...correct, ...wrong);
  } else if (q.type === 'hotspot') {
    const isCorrect = (a) => a.value && a.value.foundCount >= 3;
    const correct = [], wrong = [];
    for (const [name, ans] of Object.entries(qAnswers)) {
      if (isCorrect(ans)) correct.push({ name, tMs: ans.tMs });
      else wrong.push({ name });
    }
    correct.sort((a, b) => a.tMs - b.tMs);
    correct.forEach((a, i) => { a.correct = true; a.points = TIER[i] || 0; a.rank = i + 1; });
    wrong.forEach(a => { a.correct = false; a.points = 0; });
    results.push(...correct, ...wrong);
  } else if (q.type === 'swipe') {
    const isCorrect = (a) => a.value && a.value.correctCount >= 3;
    const correct = [], wrong = [];
    for (const [name, ans] of Object.entries(qAnswers)) {
      if (isCorrect(ans)) correct.push({ name, tMs: ans.tMs });
      else wrong.push({ name });
    }
    correct.sort((a, b) => a.tMs - b.tMs);
    correct.forEach((a, i) => { a.correct = true; a.points = TIER[i] || 0; a.rank = i + 1; });
    wrong.forEach(a => { a.correct = false; a.points = 0; });
    results.push(...correct, ...wrong);
  } else if (q.type === 'dragrank') {
    const isCorrect = (a) => a.value && a.value.order && JSON.stringify(a.value.order) === JSON.stringify(q.correctOrderBottomToTop);
    const correct = [], wrong = [];
    for (const [name, ans] of Object.entries(qAnswers)) {
      if (isCorrect(ans)) correct.push({ name, tMs: ans.tMs });
      else wrong.push({ name });
    }
    correct.sort((a, b) => a.tMs - b.tMs);
    correct.forEach((a, i) => { a.correct = true; a.points = TIER[i] || 0; a.rank = i + 1; });
    wrong.forEach(a => { a.correct = false; a.points = 0; });
    results.push(...correct, ...wrong);
  }

  ROSTER.forEach(name => {
    if (players[name] && !answeredNames.has(name)) {
      results.push({ name, correct: false, points: 0, noAnswer: true });
    }
  });

  results.forEach(r => {
    if (players[r.name]) players[r.name].score = (players[r.name].score || 0) + (r.points || 0);
  });
  state.results = results;
}

function gradeEssayVotes() {
  const q = QUESTIONS[state.currentQ];
  const voteTally = {};
  for (const [, target] of Object.entries(votes)) {
    voteTally[target] = (voteTally[target] || 0) + 1;
  }
  const results = ROSTER.filter(n => players[n]).map(name => ({
    name,
    text: essays[name] ? essays[name].text : '',
    votes: voteTally[name] || 0,
    tMs: essays[name] ? essays[name].tMs : 999999,
    points: 0,
    rank: 0
  }));
  results.sort((a, b) => b.votes - a.votes || a.tMs - b.tMs);
  results.forEach((r, i) => {
    r.rank = i + 1;
    if (r.votes > 0 && i < 5) r.points = TIER[i];
  });
  results.forEach(r => {
    if (players[r.name]) players[r.name].score = (players[r.name].score || 0) + r.points;
  });
  state.results = results;
}

/* ── Timer helper ───────────────────────────────────── */
function startTimer(seconds, onEnd) {
  clearTimer();
  state.phaseStart = Date.now();
  state.timerDuration = seconds;
  timerHandle = setTimeout(() => { timerHandle = null; onEnd(); }, seconds * 1000);
}
function clearTimer() {
  if (timerHandle) { clearTimeout(timerHandle); timerHandle = null; }
  state.timerDuration = 0;
}

/* ── Broadcast ──────────────────────────────────────── */
function broadcastState() {
  io.emit('game:state', {
    phase: state.phase,
    currentQ: state.currentQ,
    timerDuration: state.timerDuration,
    phaseStart: state.phaseStart,
    totalQ: TOTAL_Q,
    players: Object.fromEntries(ROSTER.filter(n => players[n]).map(n => [n, { name: n, avatar: players[n].avatar, score: players[n].score || 0 }])),
    submittedCount: answers[state.currentQ] ? Object.keys(answers[state.currentQ]).length : 0,
    prevStandings: state.prevStandings,
    qData: state.currentQ >= 0 && state.currentQ < TOTAL_Q ? QUESTIONS[state.currentQ] : null,
    results: state.results
  });
}

/* ── Socket Handlers ────────────────────────────────── */
io.on('connection', (socket) => {
  console.log('Connected:', socket.id);

  /* ── Room Code Verification ─────────────────────── */
  socket.on('requestRoster', () => {
    socket.emit('rosterData', ROSTER);
  });

  socket.on('verifyRoom', (code) => {
    if ((code || '').toUpperCase() === roomCode) {
      verifiedSockets.add(socket.id);
      socket.emit('roomVerified', { ok: true });
    } else {
      socket.emit('roomVerified', { ok: false, error: 'Invalid code!' });
    }
  });

  socket.on('requestState', () => {
    broadcastState();
  });

  /* Host gets room code */
  socket.on('requestHostData', () => {
    socket.emit('hostData', { roomCode });
    broadcastState();
  });

  /* ── Student joins ──────────────────────────────── */
  socket.on('student:join', (data) => {
    if (!verifiedSockets.has(socket.id)) return socket.emit('error:msg', 'Enter the room code first.');
    const name = (data.name || '').trim();
    if (!name || !ROSTER.includes(name)) return socket.emit('error:msg', 'Invalid name.');
    if (players[name] && players[name].socketId) return socket.emit('error:msg', 'Name already in use on another device.');
    players[name] = { avatar: data.avatar || null, score: players[name]?.score || 0, socketId: socket.id };
    socketToName[socket.id] = name;
    socket.emit('student:joined', { name });
    io.emit('player:count', { count: Object.keys(players).length });
    broadcastState();
  });

  /* Avatar update */
  socket.on('student:avatar', (data) => {
    const name = socketToName[socket.id];
    if (!name) return;
    players[name].avatar = data.avatar;
    broadcastState();
  });

  /* Host controls */
  socket.on('host:start', () => {
    state.phase = 'question';
    state.currentQ = 0;
    answers[0] = {};
    const q = QUESTIONS[0];
    const timer = q.submitTimer || q.timer || 30;
    broadcastState();
    startTimer(timer, () => autoAdvance());
  });

  function autoAdvance() {
    const q = QUESTIONS[state.currentQ];
    if (q.type === 'essayvote') {
      if (state.phase === 'question') {
        startVotingPhase();
      } else if (state.phase === 'voting') {
        gradeEssayVotes();
        state.phase = 'reveal';
        broadcastState();
      }
    } else {
      gradeQuestion(state.currentQ);
      state.phase = 'reveal';
      broadcastState();
    }
  }

  socket.on('host:reveal', () => {
    clearTimer();
    const q = QUESTIONS[state.currentQ];
    if (q.type === 'essayvote' && state.phase === 'question') {
      startVotingPhase();
    } else if (q.type === 'essayvote' && state.phase === 'voting') {
      gradeEssayVotes();
      state.phase = 'reveal';
      broadcastState();
    } else {
      gradeQuestion(state.currentQ);
      state.phase = 'reveal';
      broadcastState();
    }
  });

  socket.on('host:leaderboard', () => {
    state.prevStandings = ROSTER.filter(n => players[n]).sort((a, b) => (players[b].score || 0) - (players[a].score || 0));
    state.phase = 'leaderboard';
    broadcastState();
  });

  socket.on('host:next', () => {
    clearTimer();
    const next = state.currentQ + 1;
    if (next >= TOTAL_Q) {
      state.phase = 'end';
      broadcastState();
      return;
    }
    state.currentQ = next;
    state.phase = 'question';
    answers[next] = {};
    essays = {};
    votes = {};
    const q = QUESTIONS[next];
    const timer = q.submitTimer || q.timer || 30;
    broadcastState();
    startTimer(timer, () => autoAdvance());
  });

  socket.on('host:reset', () => {
    clearTimer();
    state = { phase: 'lobby', currentQ: -1, timerDuration: 0, phaseStart: 0, prevStandings: [], results: null, essayOrder: null };
    players = {};
    answers = {};
    essays = {};
    votes = {};
    socketToName = {};
    verifiedSockets = new Set();
    roomCode = Math.random().toString(36).substring(2, 6).toUpperCase();
    broadcastState();
  });

  /* Essay voting phase setup */
  function startVotingPhase() {
    const essayNames = Object.keys(essays);
    for (let i = essayNames.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      [essayNames[i], essayNames[j]] = [essayNames[j], essayNames[i]];
    }
    state.essayOrder = essayNames;
    state.phase = 'voting';
    votes = {};
    broadcastState();
    const q = QUESTIONS[state.currentQ];
    startTimer(q.voteTimer || 30, () => {
      gradeEssayVotes();
      state.phase = 'reveal';
      broadcastState();
    });
  }

  /* ── Student answer submissions ─────────────── */
  socket.on('answer:submit', (data) => {
    const name = socketToName[socket.id];
    if (!name || state.phase !== 'question') return;
    if (!answers[state.currentQ]) answers[state.currentQ] = {};
    if (answers[state.currentQ][name]) return;
    const tMs = Date.now() - state.phaseStart;
    answers[state.currentQ][name] = { value: data.value, tMs };
    socket.emit('answer:locked');
    io.emit('answer:count', { count: Object.keys(answers[state.currentQ]).length });
  });

  socket.on('essay:submit', (data) => {
    const name = socketToName[socket.id];
    if (!name || state.phase !== 'question') return;
    if (essays[name]) return;
    essays[name] = { text: (data.text || '').slice(0, QUESTIONS[state.currentQ].maxChars), tMs: Date.now() - state.phaseStart };
    socket.emit('answer:locked');
    io.emit('answer:count', { count: Object.keys(essays).length });
    const presentCount = ROSTER.filter(n => players[n]).length;
    if (Object.keys(essays).length >= presentCount) {
      clearTimer();
      startVotingPhase();
    }
  });

  socket.on('vote:submit', (data) => {
    const name = socketToName[socket.id];
    if (!name || state.phase !== 'voting') return;
    if (votes[name]) return;
    if (data.target === name) return socket.emit('error:msg', 'Cannot vote for yourself.');
    votes[name] = data.target;
    socket.emit('vote:locked');
    io.emit('vote:count', { count: Object.keys(votes).length });
  });

  socket.on('requestEssays', () => {
    const q = QUESTIONS[state.currentQ];
    if (!q || q.type !== 'essayvote') return;
    const order = state.essayOrder || Object.keys(essays);
    socket.emit('essayData', order.map(name => ({ name, text: essays[name] ? essays[name].text : '' })));
  });

  /* Disconnect */
  socket.on('disconnect', () => {
    const name = socketToName[socket.id];
    if (name && players[name]) players[name].socketId = null;
    verifiedSockets.delete(socket.id);
    delete socketToName[socket.id];
    io.emit('player:count', { count: Object.keys(players).filter(n => players[n].socketId).length });
    console.log('Disconnected:', socket.id);
  });
});

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => console.log(`DRRM Quiz server on http://localhost:${PORT}`));
