const express = require("express");
const app = express();
const http = require("http").createServer(app);
const io = require("socket.io")(http, { cors: { origin: "*" } });

app.use(express.static("public"));

let gameState = null;
let waitingPlayers = [];
const disconnectTimers = {};
const DISCONNECT_GRACE = 5 * 60 * 1000;

// ═══════════════════════════════════════
//  牌组工具
// ═══════════════════════════════════════
function createDeck() {
  const suits = ["clubs", "diamonds", "hearts", "spades"];
  const values = [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14];
  const deck = [];
  for (const suit of suits)
    for (const value of values) deck.push({ suit, value });
  return deck;
}
function shuffle(deck) {
  for (let i = deck.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [deck[i], deck[j]] = [deck[j], deck[i]];
  }
  return deck;
}
function sortHand(hand) {
  const order = { clubs: 0, diamonds: 1, hearts: 2, spades: 3 };
  return hand.sort((a, b) =>
    order[a.suit] !== order[b.suit]
      ? order[a.suit] - order[b.suit]
      : a.value - b.value,
  );
}
function dealCards(deck) {
  const hands = [[], [], [], []];
  for (let i = 0; i < 52; i++) hands[i % 4].push(deck[i]);
  return hands.map(sortHand);
}
function findStarter(hands) {
  for (let i = 0; i < 4; i++)
    if (hands[i].some((c) => c.suit === "clubs" && c.value === 2)) return i;
  return 0;
}

// ═══════════════════════════════════════
//  牌型判断
// ═══════════════════════════════════════
function isPig(c) {
  return c.suit === "spades" && c.value === 12;
}
function isSheep(c) {
  return c.suit === "diamonds" && c.value === 11;
}
function isTransformer(c) {
  return c.suit === "clubs" && c.value === 10;
}
function isHeart(c) {
  return c.suit === "hearts";
}

// 获取一张牌的亮牌类型（null=不可亮）
function getCardDeclType(c) {
  if (isPig(c)) return "pig";
  if (isSheep(c)) return "sheep";
  if (isTransformer(c)) return "transformer";
  if (c.suit === "hearts" && c.value === 14) return "heartA";
  return null;
}

function isScoringCard(c) {
  return isPig(c) || isSheep(c) || isTransformer(c) || isHeart(c);
}
function noScoringCardsLeft(gs) {
  return gs.players.every((p) => !p.hand.some(isScoringCard));
}

// ═══════════════════════════════════════
//  亮牌辅助
// ═══════════════════════════════════════
// 将所有玩家的亮牌类型汇总为一个 Set
function getAllDeclaredTypes(declarations) {
  const types = new Set();
  Object.values(declarations || {}).forEach((arr) =>
    arr.forEach((t) => types.add(t)),
  );
  return types;
}

// ═══════════════════════════════════════
//  计分规则
// ═══════════════════════════════════════
function heartValue(value) {
  if (value === 14) return 50;
  if (value === 13) return 40;
  if (value === 12) return 30;
  if (value === 11) return 20;
  if (value >= 5) return 10;
  return 0;
}

function hasAllHearts(captured) {
  return captured.filter(isHeart).length === 13;
}
function hasGrandSlam(captured) {
  return (
    captured.some(isPig) &&
    captured.some(isSheep) &&
    captured.some(isTransformer) &&
    hasAllHearts(captured)
  );
}

// declaredTypes: Set，由 getAllDeclaredTypes 生成
function calcScore(captured, declaredTypes = new Set()) {
  const grandSlam = hasGrandSlam(captured);
  const allHearts = hasAllHearts(captured);
  const hasTrans = captured.some(isTransformer);

  if (grandSlam) return { score: 0, grandSlam: true, allHearts: false };

  const pigBase = declaredTypes.has("pig") ? 200 : 100;
  const sheepBase = declaredTypes.has("sheep") ? 200 : 100;
  const heartMult = declaredTypes.has("heartA") ? 2 : 1;
  const transMult = hasTrans ? (declaredTypes.has("transformer") ? 4 : 2) : 1;

  let score = 0;
  if (captured.some(isPig)) score += pigBase;
  if (captured.some(isSheep)) score -= sheepBase;
  if (allHearts) {
    score -= 200 * heartMult;
  } else {
    for (const c of captured)
      if (isHeart(c)) score += heartValue(c.value) * heartMult;
  }
  score *= transMult;

  return { score, grandSlam: false, allHearts };
}

function calcRoundScoresNow(gs) {
  const declaredTypes = getAllDeclaredTypes(gs.declarations);
  return gs.players.map((p) => {
    const r = calcScore(p.captured, declaredTypes);
    return r.grandSlam ? 0 : r.score;
  });
}

// ═══════════════════════════════════════
//  出牌合法性
//
//  规则：
//  · 第一小局第一墩：先手必须出梅花2
//  · 有同花色必须跟
//  · 亮出的牌在该花色首次出现时不可出（除非该花色只剩这一张）
// ═══════════════════════════════════════
function canPlay(gs, pidx, card) {
  if (gs.phase !== "playing") return false;
  const trick = gs.currentTrick;
  const hand = gs.players[pidx].hand;
  const myDecl = gs.declarations[pidx] || [];

  // ── 先手 ──
  if (trick.length === 0) {
    if (gs.roundNumber === 0 && gs.trickNumber === 0)
      return card.suit === "clubs" && card.value === 2;

    // 亮牌限制：首次出该花色时，不可以先手打出亮出的牌
    if (myDecl.length > 0) {
      const dt = getCardDeclType(card);
      if (dt && myDecl.includes(dt) && !gs.suitsEverLed.includes(card.suit)) {
        const others = hand.filter(
          (c) => c.suit === card.suit && getCardDeclType(c) !== dt,
        );
        if (others.length > 0) return false;
      }
    }
    return true;
  }

  // ── 跟牌 ──
  const leadSuit = trick[0].card.suit;
  const hasSuit = hand.some((c) => c.suit === leadSuit);
  if (!hasSuit) return true; // 无同花色，随便出

  if (card.suit !== leadSuit) return false; // 有同花色必须跟

  // 亮牌限制：该花色首次被打出时，不可出亮出的牌
  if (myDecl.length > 0 && !gs.suitsEverLed.includes(leadSuit)) {
    const dt = getCardDeclType(card);
    if (dt && myDecl.includes(dt)) {
      const others = hand.filter(
        (c) => c.suit === leadSuit && getCardDeclType(c) !== dt,
      );
      if (others.length > 0) return false;
    }
  }
  return true;
}

// ═══════════════════════════════════════
//  赢墩
// ═══════════════════════════════════════
function trickWinner(trick) {
  const lead = trick[0].card.suit;
  let best = 0;
  for (let i = 1; i < 4; i++) {
    const c = trick[i];
    if (
      c.card.suit === lead &&
      (trick[best].card.suit !== lead || c.card.value > trick[best].card.value)
    )
      best = i;
  }
  return trick[best].playerIndex;
}

// ═══════════════════════════════════════
//  初始化游戏
// ═══════════════════════════════════════
function initGame(pList, prevTotalScores, pigOwnerIdx, roundNumber) {
  const deck = shuffle(createDeck());
  const hands = dealCards(deck);
  const rn = roundNumber ?? 0;
  const starter = rn === 0 ? findStarter(hands) : pigOwnerIdx;

  return {
    phase: "declaring", // 亮牌阶段开始
    declarations: {}, // { pidx: ['pig','heartA',...] }
    declarationSubmitted: {}, // { pidx: true }
    suitsEverLed: [], // 本局已出现过的先手花色

    players: pList.map((p, i) => ({
      id: p.id,
      name: p.name,
      socketId: p.socketId,
      hand: hands[i],
      captured: [],
      online: true,
    })),
    currentTrick: [],
    currentPlayer: starter,
    trickNumber: 0,
    roundNumber: rn,
    totalScores: prevTotalScores || [0, 0, 0, 0],
  };
}

// ═══════════════════════════════════════
//  视图
// ═══════════════════════════════════════
function scoredCards(captured) {
  return captured.filter(
    (c) => isPig(c) || isSheep(c) || isTransformer(c) || isHeart(c),
  );
}

function playerView(gs, forIdx) {
  const roundScores = calcRoundScoresNow(gs);
  const phase = gs.phase;
  const submittedCount = Object.keys(gs.declarationSubmitted).length;

  return {
    myIndex: forIdx,
    myHand: gs.players[forIdx].hand,
    phase,
    // 亮牌阶段：只给自己看自己的选择；出牌阶段：公开所有人亮牌
    declarations:
      phase === "playing"
        ? gs.declarations
        : { [forIdx]: gs.declarations[forIdx] || [] },
    declarationSubmittedCount: submittedCount,
    declarationSubmittedNames: Object.keys(gs.declarationSubmitted).map(
      (i) => gs.players[i].name,
    ),
    suitsEverLed: gs.suitsEverLed,
    players: gs.players.map((p, i) => ({
      name: p.name,
      online: p.online,
      isMe: i === forIdx,
      scoredCards: scoredCards(p.captured),
      declared: phase === "playing" ? gs.declarations[i] || [] : [],
      hasSubmitted: !!gs.declarationSubmitted[i],
    })),
    currentTrick: gs.currentTrick,
    currentPlayer: gs.currentPlayer,
    trickNumber: gs.trickNumber,
    roundNumber: gs.roundNumber,
    totalScores: gs.totalScores,
    roundScores,
  };
}

function broadcast(gs) {
  gs.players.forEach((p, i) => {
    const s = io.sockets.sockets.get(p.socketId);
    if (s) s.emit("stateUpdate", playerView(gs, i));
  });
}
function broadcastNotice(msg) {
  io.emit("notice", msg);
}

// ═══════════════════════════════════════
//  Socket 事件
// ═══════════════════════════════════════
io.on("connection", (socket) => {
  console.log("连接:", socket.id);

  // ── 加入 / 重连 ──
  socket.on("join", (name) => {
    const playerName =
      String(name || "").trim() || `玩家${Math.floor(Math.random() * 100)}`;

    if (gameState) {
      const pidx = gameState.players.findIndex((p) => p.name === playerName);
      if (pidx !== -1) {
        if (disconnectTimers[pidx]) {
          clearTimeout(disconnectTimers[pidx]);
          delete disconnectTimers[pidx];
        }
        gameState.players[pidx].socketId = socket.id;
        gameState.players[pidx].online = true;
        socket.myId = pidx;
        socket.emit("stateUpdate", playerView(gameState, pidx));
        socket.emit("gameStarted");
        broadcastNotice(`✅ ${playerName} 重新连线了！`);
        return;
      }
      socket.emit("err", "游戏进行中，无法加入");
      return;
    }

    if (waitingPlayers.length >= 4) {
      socket.emit("err", "房间已满");
      return;
    }
    const idx = waitingPlayers.length;
    waitingPlayers.push({ id: idx, name: playerName, socketId: socket.id });
    socket.myId = idx;
    io.emit("waiting", {
      players: waitingPlayers.map((p) => p.name),
      count: waitingPlayers.length,
    });

    if (waitingPlayers.length === 4) {
      gameState = initGame([...waitingPlayers], null, -1, 0);
      waitingPlayers = [];
      broadcast(gameState);
      io.emit("gameStarted");
    }
  });

  // ── 提交亮牌 ──
  socket.on("submitDeclaration", (declTypes) => {
    if (!gameState || gameState.phase !== "declaring") return;
    const pidx = socket.myId;
    if (pidx === undefined) return;
    if (gameState.declarationSubmitted[pidx]) return; // 不允许重复提交

    // 校验：只能亮自己手里有的牌
    const hand = gameState.players[pidx].hand;
    const valid = (Array.isArray(declTypes) ? declTypes : []).filter((t) => {
      if (t === "pig") return hand.some(isPig);
      if (t === "sheep") return hand.some(isSheep);
      if (t === "transformer") return hand.some(isTransformer);
      if (t === "heartA")
        return hand.some((c) => c.suit === "hearts" && c.value === 14);
      return false;
    });

    gameState.declarations[pidx] = valid;
    gameState.declarationSubmitted[pidx] = true;
    const count = Object.keys(gameState.declarationSubmitted).length;

    // 广播进度（各自只看到自己的亮牌）
    broadcast(gameState);

    // 四人全部提交 → 进入出牌阶段
    if (count >= 4) {
      gameState.phase = "playing";
      broadcast(gameState); // 此时公开所有亮牌
    }
  });

  // ── 出牌 ──
  socket.on("playCard", (cardData) => {
    if (!gameState || gameState.phase !== "playing") return;
    const pidx = socket.myId;
    if (pidx === undefined) return;
    if (gameState.currentPlayer !== pidx) {
      socket.emit("err", "还没轮到你出牌");
      return;
    }

    const player = gameState.players[pidx];
    const ci = player.hand.findIndex(
      (c) => c.suit === cardData.suit && c.value === cardData.value,
    );
    if (ci === -1) {
      socket.emit("err", "无效的牌");
      return;
    }

    const card = player.hand[ci];
    if (!canPlay(gameState, pidx, card)) {
      socket.emit("err", "这张牌不能出！请跟花色");
      return;
    }

    player.hand.splice(ci, 1);
    gameState.currentTrick.push({ playerIndex: pidx, card });

    if (gameState.currentTrick.length < 4) {
      gameState.currentPlayer = (pidx + 1) % 4;
      broadcast(gameState);
    } else {
      // ── 墩结束 ──
      const trick = [...gameState.currentTrick];
      const winner = trickWinner(trick);
      const leadSuit = trick[0].card.suit;

      gameState.players[winner].captured.push(...trick.map((t) => t.card));
      gameState.trickNumber++;
      gameState.currentTrick = [];
      gameState.currentPlayer = winner;

      // 记录本墩先手花色（用于亮牌限制）
      if (!gameState.suitsEverLed.includes(leadSuit))
        gameState.suitsEverLed.push(leadSuit);

      // ── 判断本局是否结束 ──
      const roundOver =
        gameState.players[0].hand.length === 0 || noScoringCardsLeft(gameState);

      if (roundOver) {
        const declaredTypes = getAllDeclaredTypes(gameState.declarations);
        const results = gameState.players.map((p) =>
          calcScore(p.captured, declaredTypes),
        );
        const grandSlamIdx = results.findIndex((r) => r.grandSlam);

        let roundScores,
          grandSlamWinner = null;
        if (grandSlamIdx !== -1) {
          grandSlamWinner = gameState.players[grandSlamIdx].name;
          roundScores = results.map((_, i) => (i === grandSlamIdx ? 0 : 200));
        } else {
          roundScores = results.map((r) => r.score);
        }

        gameState.totalScores = gameState.totalScores.map(
          (s, i) => s + roundScores[i],
        );
        gameState.pigOwnerIdx = gameState.players.findIndex((p) =>
          p.captured.some(isPig),
        );
        gameState.nextRoundNum = gameState.roundNumber + 1;

        const escaped = gameState.players
          .map((p, i) => ({ name: p.name, score: gameState.totalScores[i] }))
          .filter((p) => p.score >= 1000);

        // 大全 或 有人出栏 → 本大局结束，下局清零重开
        const bigGameOver = grandSlamIdx !== -1 || escaped.length > 0;
        gameState.bigGameOver = bigGameOver;

        broadcast(gameState);
        io.emit("roundEnd", {
          roundScores,
          totalScores: gameState.totalScores,
          playerNames: gameState.players.map((p) => p.name),
          escaped,
          grandSlamWinner,
          bigGameOver,
          playerDeclarations: gameState.players.map(
            (_, i) => gameState.declarations[i] || [],
          ),
          capturedSpecials: gameState.players.map((p, i) => ({
            hasPig: p.captured.some(isPig),
            hasSheep: p.captured.some(isSheep),
            hasTransformer: p.captured.some(isTransformer),
            heartScore: results[i].allHearts
              ? "全红"
              : p.captured
                  .filter(isHeart)
                  .reduce(
                    (s, c) =>
                      s +
                      heartValue(c.value) *
                        (declaredTypes.has("heartA") ? 2 : 1),
                    0,
                  ),
            allHearts: results[i].allHearts,
            grandSlam: results[i].grandSlam,
          })),
        });
      } else {
        io.emit("trickWon", {
          winner,
          winnerName: gameState.players[winner].name,
          trick,
        });
        setTimeout(() => broadcast(gameState), 1500);
      }
    }
  });

  // ── 再来一局（4人全票才开局） ──
  socket.on("newGame", () => {
    if (!gameState) return;
    const pidx = socket.myId;
    if (pidx === undefined) return;

    if (!gameState.newGameVotes) gameState.newGameVotes = new Set();
    gameState.newGameVotes.add(pidx);
    const count = gameState.newGameVotes.size;
    const total = gameState.players.length;

    io.emit("newGameVote", {
      count,
      total,
      voterNames: [...gameState.newGameVotes].map(
        (i) => gameState.players[i].name,
      ),
    });

    if (count >= total) {
      // 大局结束 → 清零重开；小局结束 → 保留积分继续
      const isNewBigGame = !!gameState.bigGameOver;
      gameState = initGame(
        gameState.players.map((p) => ({ ...p })),
        isNewBigGame ? [0, 0, 0, 0] : [...gameState.totalScores],
        isNewBigGame ? -1 : (gameState.pigOwnerIdx ?? -1),
        isNewBigGame ? 0 : (gameState.nextRoundNum ?? 1),
      );
      broadcast(gameState);
      io.emit("gameStarted");
    }
  });

  // ── 重新开始（清零） ──
  socket.on("resetAll", () => {
    if (!gameState) return;
    gameState = initGame(
      gameState.players.map((p) => ({ ...p })),
      [0, 0, 0, 0],
      -1,
      0,
    );
    broadcast(gameState);
    io.emit("gameStarted");
  });

  // ── 断线处理 ──
  socket.on("disconnect", () => {
    waitingPlayers = waitingPlayers.filter((p) => p.socketId !== socket.id);
    io.emit("waiting", {
      players: waitingPlayers.map((p) => p.name),
      count: waitingPlayers.length,
    });

    if (!gameState) return;
    const pidx = gameState.players.findIndex((p) => p.socketId === socket.id);
    if (pidx === -1) return;

    gameState.players[pidx].online = false;
    const pname = gameState.players[pidx].name;
    broadcastNotice(`⚠️ ${pname} 断线了，等待重连（5分钟内有效）…`);
    broadcast(gameState);

    disconnectTimers[pidx] = setTimeout(() => {
      delete disconnectTimers[pidx];
      if (gameState && !gameState.players[pidx].online) {
        io.emit("notice", `❌ ${pname} 超时未重连，游戏结束`);
        gameState = null;
      }
    }, DISCONNECT_GRACE);
  });
});

const PORT = process.env.PORT || 3000;
http.listen(PORT, () => console.log(`🐷 拱猪服务器启动，端口 ${PORT}`));
