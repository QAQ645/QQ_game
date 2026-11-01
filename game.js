/* ============================================================
   企鹅迷宫 · 无情道
   - 纯原生 JavaScript，无依赖、无网络请求
   - 递归回溯生成 13×13 完美迷宫，保证起点到出口必有解
   ============================================================ */

(function () {
  "use strict";

  var COLS = 13;
  var ROWS = 13;
  var DURATION_OPTIONS = [2, 3, 4, 5];
  var DEFAULT_MINUTES = 3;
  var MAZE_CANDIDATES = 6;
  var TURN_THRESHOLD = 30000;

  var KEY_DIRECTIONS = {
    arrowup: [0, -1],
    w: [0, -1],
    arrowdown: [0, 1],
    s: [0, 1],
    arrowleft: [-1, 0],
    a: [-1, 0],
    arrowright: [1, 0],
    d: [1, 0]
  };

  var DIRS = [
    { dx: 0, dy: -1, wall: "n", opposite: "s" },
    { dx: 1, dy: 0, wall: "e", opposite: "w" },
    { dx: 0, dy: 1, wall: "s", opposite: "n" },
    { dx: -1, dy: 0, wall: "w", opposite: "e" }
  ];

  var FONT_SERIF = '"Songti SC", "STSong", "Noto Serif CJK SC", "SimSun", serif';
  var FONT_SANS = '"PingFang SC", "Microsoft YaHei", "Noto Sans CJK SC", sans-serif';

  var dom = {
    page: document.getElementById("pageShell"),
    timer: document.getElementById("timerValue"),
    timerBar: document.getElementById("timerBar"),
    phaseText: document.getElementById("phaseText"),
    roundNumber: document.getElementById("roundNumber"),
    canvas: document.getElementById("mazeCanvas"),
    stage: document.getElementById("mazeStage"),
    a11yStatus: document.getElementById("a11yStatus"),
    startScreen: document.getElementById("startScreen"),
    startTitle: document.getElementById("startTitle"),
    startButton: document.getElementById("startButton"),
    startButtonMeta: document.getElementById("startButtonMeta"),
    durationHint: document.getElementById("durationHint"),
    durationButtons: Array.prototype.slice.call(document.querySelectorAll(".duration-option")),
    resultScreen: document.getElementById("resultScreen"),
    resultPanel: document.getElementById("resultPanel"),
    resultTitle: document.getElementById("resultTitle"),
    resultKicker: document.getElementById("resultKicker"),
    resultDescription: document.getElementById("resultDescription"),
    resultImage: document.getElementById("resultImage"),
    resultWatermark: document.getElementById("resultWatermark"),
    resultTime: document.getElementById("resultTime"),
    resultExit: document.getElementById("resultExit"),
    againButton: document.getElementById("againButton"),
    reselectButton: document.getElementById("reselectButton")
  };

  var ctx = dom.canvas.getContext("2d");
  var selectedMinutes = DEFAULT_MINUTES;
  var phase = "ready";
  var maze = null;
  var player = { x: 0, y: 0 };
  var totalMs = 0;
  var endAt = 0;
  var round = 0;
  var timerId = 0;
  var frameId = 0;
  var resizeFrameId = 0;
  var swipe = null;

  // 装饰纸屑：固定随机分布，重绘时不会闪烁
  var SPECKS = (function () {
    var result = [];
    for (var i = 0; i < 92; i += 1) {
      var x = Math.abs(Math.sin(i * 12.9898 + 4.1414) * 43758.5453) % 1;
      var y = Math.abs(Math.sin(i * 78.233 + 1.732) * 24634.6345) % 1;
      var r = 0.45 + (Math.abs(Math.sin(i * 3.719)) % 1) * 0.9;
      result.push({ x: x, y: y, r: r });
    }
    return result;
  })();

  // 预加载本地插画；画布上的棋子只依赖 token
  var art = {
    token: new Image(),
    win: new Image(),
    lose: new Image()
  };
  art.token.src = "assets/penguin-token.png";
  art.win.src = "assets/penguin-win.png";
  art.lose.src = "assets/penguin-lose.png";
  art.token.addEventListener("load", scheduleRender);

  /* ---------- 小工具 ---------- */

  function clamp(value, min, max) {
    return Math.max(min, Math.min(max, value));
  }

  function formatClock(seconds) {
    var safe = Math.max(0, Math.floor(seconds));
    var minutes = Math.floor(safe / 60);
    var rest = safe % 60;
    return String(minutes).padStart(2, "0") + ":" + String(rest).padStart(2, "0");
  }

  function roundLabel(value) {
    return String(value).padStart(2, "0");
  }

  function shuffle(list) {
    for (var i = list.length - 1; i > 0; i -= 1) {
      var j = Math.floor(Math.random() * (i + 1));
      var item = list[i];
      list[i] = list[j];
      list[j] = item;
    }
    return list;
  }

  /* ---------- 迷宫生成 ---------- */

  // 每格四边都是墙；递归回溯会把全部格子连成一棵生成树。
  function createCell() {
    return { n: true, e: true, s: true, w: true, visited: false };
  }

  function createMaze() {
    var cells = [];
    for (var y = 0; y < ROWS; y += 1) {
      var row = [];
      for (var x = 0; x < COLS; x += 1) {
        row.push(createCell());
      }
      cells.push(row);
    }

    cells[0][0].visited = true;
    var stack = [{ x: 0, y: 0 }];

    while (stack.length > 0) {
      var current = stack[stack.length - 1];
      var candidates = [];

      for (var i = 0; i < DIRS.length; i += 1) {
        var dir = DIRS[i];
        var nx = current.x + dir.dx;
        var ny = current.y + dir.dy;
        if (nx >= 0 && nx < COLS && ny >= 0 && ny < ROWS && !cells[ny][nx].visited) {
          candidates.push({ x: nx, y: ny, dir: dir });
        }
      }

      if (candidates.length === 0) {
        stack.pop();
        continue;
      }

      // 随机选一条未打通的边，拆掉两边的墙
      var pick = candidates[Math.floor(Math.random() * candidates.length)];
      cells[current.y][current.x][pick.dir.wall] = false;
      cells[pick.y][pick.x][pick.dir.opposite] = false;
      cells[pick.y][pick.x].visited = true;
      stack.push({ x: pick.x, y: pick.y });
    }

    // 清理生成过程用的标记
    for (var cy = 0; cy < ROWS; cy += 1) {
      for (var cx = 0; cx < COLS; cx += 1) {
        delete cells[cy][cx].visited;
      }
    }

    return { cells: cells, cols: COLS, rows: ROWS };
  }

  // 用 BFS 估算起点到出口的最短步数，用来挑一张更绕的迷阵
  function solutionDistance(candidate) {
    var distances = [];
    for (var y = 0; y < ROWS; y += 1) {
      distances.push(new Array(COLS).fill(-1));
    }
    distances[0][0] = 1;
    var queue = [{ x: 0, y: 0 }];
    var head = 0;

    while (head < queue.length) {
      var current = queue[head];
      head += 1;
      var cell = candidate.cells[current.y][current.x];

      for (var i = 0; i < DIRS.length; i += 1) {
        var dir = DIRS[i];
        if (cell[dir.wall]) continue;
        var nx = current.x + dir.dx;
        var ny = current.y + dir.dy;
        if (nx < 0 || nx >= COLS || ny < 0 || ny >= ROWS) continue;
        if (distances[ny][nx] !== -1) continue;
        distances[ny][nx] = distances[current.y][current.x] + 1;
        queue.push({ x: nx, y: ny });
      }
    }

    return distances[ROWS - 1][COLS - 1];
  }

  // 生成若干候选，取起点到出口最长的一张；依然是完美迷宫，必然有解
  function buildPlayableMaze() {
    var best = null;
    var bestDistance = -1;

    for (var i = 0; i < MAZE_CANDIDATES; i += 1) {
      var candidate = createMaze();
      var distance = solutionDistance(candidate);
      if (distance > bestDistance) {
        bestDistance = distance;
        best = candidate;
      }
    }

    return best;
  }

  /* ---------- 画布渲染 ---------- */

  function scheduleRender() {
    if (resizeFrameId) cancelAnimationFrame(resizeFrameId);
    resizeFrameId = requestAnimationFrame(function (now) {
      resizeFrameId = 0;
      render(now);
    });
  }

  function fitCanvas() {
    var rect = dom.canvas.getBoundingClientRect();
    if (rect.width < 10 || rect.height < 10) return null;

    var dpr = Math.min(window.devicePixelRatio || 1, 2);
    var targetWidth = Math.round(rect.width * dpr);
    var targetHeight = Math.round(rect.height * dpr);

    if (dom.canvas.width !== targetWidth || dom.canvas.height !== targetHeight) {
      dom.canvas.width = targetWidth;
      dom.canvas.height = targetHeight;
    }

    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    return { width: rect.width, height: rect.height };
  }

  function cellCenter(x, y, offsetX, offsetY, cellSize) {
    return {
      x: offsetX + (x + 0.5) * cellSize,
      y: offsetY + (y + 0.5) * cellSize
    };
  }

  function drawWallPath(offsetX, offsetY, cellSize) {
    ctx.beginPath();

    for (var y = 0; y < ROWS; y += 1) {
      for (var x = 0; x < COLS; x += 1) {
        var cell = maze.cells[y][x];
        var left = offsetX + x * cellSize;
        var top = offsetY + y * cellSize;
        var right = left + cellSize;
        var bottom = top + cellSize;

        if (cell.n) {
          ctx.moveTo(left, top);
          ctx.lineTo(right, top);
        }
        if (cell.w) {
          ctx.moveTo(left, top);
          ctx.lineTo(left, bottom);
        }
        if (x === COLS - 1 && cell.e) {
          ctx.moveTo(right, top);
          ctx.lineTo(right, bottom);
        }
        if (y === ROWS - 1 && cell.s) {
          ctx.moveTo(left, bottom);
          ctx.lineTo(right, bottom);
        }
      }
    }
  }

  function drawExit(now, center, cellSize) {
    var pulse = phase === "playing" ? (Math.sin(now / 420) + 1) / 2 : 0.55;
    var glowRadius = cellSize * (0.55 + pulse * 0.15);

    ctx.save();
    var glow = ctx.createRadialGradient(center.x, center.y, cellSize * 0.08, center.x, center.y, glowRadius);
    glow.addColorStop(0, "rgba(173, 43, 40, 0.2)");
    glow.addColorStop(0.58, "rgba(173, 43, 40, 0.1)");
    glow.addColorStop(1, "rgba(173, 43, 40, 0)");
    ctx.fillStyle = glow;
    ctx.beginPath();
    ctx.arc(center.x, center.y, glowRadius, 0, Math.PI * 2);
    ctx.fill();

    var gateWidth = cellSize * 0.52;
    var gateHeight = cellSize * 0.55;
    var top = center.y - gateHeight * 0.46;
    var bottom = center.y + gateHeight * 0.54;
    var left = center.x - gateWidth / 2;
    var right = center.x + gateWidth / 2;

    ctx.strokeStyle = "#ad2b28";
    ctx.lineWidth = Math.max(1.8, cellSize * 0.08);
    ctx.lineCap = "round";
    ctx.lineJoin = "round";
    ctx.beginPath();
    ctx.moveTo(left - cellSize * 0.06, top);
    ctx.lineTo(right + cellSize * 0.06, top);
    ctx.moveTo(left + cellSize * 0.06, top - cellSize * 0.09);
    ctx.lineTo(right - cellSize * 0.06, top - cellSize * 0.09);
    ctx.moveTo(left + cellSize * 0.08, top);
    ctx.lineTo(left + cellSize * 0.08, bottom);
    ctx.moveTo(right - cellSize * 0.08, top);
    ctx.lineTo(right - cellSize * 0.08, bottom);
    ctx.stroke();

    ctx.fillStyle = "rgba(173, 43, 40, 0.12)";
    ctx.fillRect(left + cellSize * 0.08, top + cellSize * 0.12, gateWidth - cellSize * 0.16, gateHeight * 0.66);
    ctx.restore();
  }

  function drawStart(center, cellSize) {
    ctx.save();
    ctx.fillStyle = "rgba(37, 33, 28, 0.08)";
    ctx.beginPath();
    ctx.arc(center.x, center.y, cellSize * 0.36, 0, Math.PI * 2);
    ctx.fill();

    ctx.fillStyle = "rgba(37, 33, 28, 0.55)";
    ctx.font = "600 " + (cellSize * 0.29) + "px " + FONT_SERIF;
    ctx.textAlign = "center";
    ctx.textBaseline = "middle";
    ctx.fillText("入", center.x, center.y + cellSize * 0.01);
    ctx.restore();
  }

  function drawFallbackPenguin(center, cellSize, bob) {
    var cx = center.x;
    var cy = center.y + bob;
    var bodyW = cellSize * 0.39;
    var bodyH = cellSize * 0.52;

    ctx.fillStyle = "#1f1c18";
    ctx.beginPath();
    ctx.ellipse(cx, cy, bodyW, bodyH, 0, 0, Math.PI * 2);
    ctx.fill();

    ctx.fillStyle = "#f9f1e3";
    ctx.beginPath();
    ctx.ellipse(cx, cy + bodyH * 0.22, bodyW * 0.62, bodyH * 0.48, 0, 0, Math.PI * 2);
    ctx.fill();

    ctx.strokeStyle = "#ad2b28";
    ctx.lineWidth = Math.max(2, cellSize * 0.07);
    ctx.beginPath();
    ctx.moveTo(cx - bodyW * 0.92, cy - bodyH * 0.2);
    ctx.lineTo(cx + bodyW * 0.92, cy - bodyH * 0.2);
    ctx.stroke();

    ctx.fillStyle = "#eaa72d";
    ctx.beginPath();
    ctx.ellipse(cx, cy + bodyH * 0.07, bodyW * 0.28, bodyH * 0.18, 0, 0, Math.PI * 2);
    ctx.fill();

    ctx.fillStyle = "#fbf6ec";
    ctx.beginPath();
    ctx.arc(cx - bodyW * 0.26, cy - bodyH * 0.23, bodyW * 0.18, 0, Math.PI * 2);
    ctx.arc(cx + bodyW * 0.26, cy - bodyH * 0.23, bodyW * 0.18, 0, Math.PI * 2);
    ctx.fill();

    ctx.fillStyle = "#1f1c18";
    ctx.beginPath();
    ctx.arc(cx - bodyW * 0.26, cy - bodyH * 0.22, bodyW * 0.065, 0, Math.PI * 2);
    ctx.arc(cx + bodyW * 0.26, cy - bodyH * 0.22, bodyW * 0.065, 0, Math.PI * 2);
    ctx.fill();
  }

  function drawPlayerTag(center, cellSize) {
    var text = "找婆娘。";
    // 棋子缩到单格大小时，标签保留最低可读字号，整体仍只占一格上下
    var fontSize = clamp(cellSize * 0.3, 8.5, 10.5);
    var padX = Math.max(2.5, cellSize * 0.04);
    var height = fontSize * 1.28;

    ctx.save();
    ctx.font = "700 " + fontSize.toFixed(1) + "px " + FONT_SANS;
    var width = ctx.measureText(text).width + padX * 2;

    // 标签底边也压在本格内，不越过下边界
    var tagCenterY = center.y + cellSize * 0.48 - height / 2;
    ctx.translate(center.x, tagCenterY);
    ctx.rotate(-0.02);
    ctx.shadowColor = "rgba(32, 23, 15, 0.3)";
    ctx.shadowBlur = Math.max(1.2, cellSize * 0.045);
    ctx.shadowOffsetY = Math.max(0.8, cellSize * 0.022);
    ctx.fillStyle = "#ad2b28";
    ctx.fillRect(-width / 2, -height / 2, width, height);
    ctx.shadowColor = "transparent";
    ctx.strokeStyle = "rgba(255, 248, 235, 0.88)";
    ctx.lineWidth = Math.max(0.7, fontSize * 0.055);
    ctx.strokeRect(-width / 2, -height / 2, width, height);
    ctx.fillStyle = "#fdf6e8";
    ctx.textAlign = "center";
    ctx.textBaseline = "middle";
    ctx.fillText(text, 0, fontSize * 0.04);
    ctx.restore();
  }

  function drawPlayer(now, center, cellSize) {
    var bob = phase === "playing" ? Math.sin(now / 260) * cellSize * 0.014 : 0;
    var cx = center.x;
    var cy = center.y;
    // 棋子控制在约 1.2 格内，避免遮挡迷宫；仍保留完整身体和清晰标签
    var tokenHeight = cellSize * 1.2;
    var tokenWidth = tokenHeight * (art.token.naturalWidth / art.token.naturalHeight || 1);

    ctx.save();

    // 柔和底盘，避免黑色企鹅和墨色墙壁糊在一起
    var halo = ctx.createRadialGradient(cx, cy + cellSize * 0.02, cellSize * 0.06, cx, cy + cellSize * 0.02, cellSize * 0.4);
    halo.addColorStop(0, "rgba(255, 251, 243, 0.92)");
    halo.addColorStop(0.64, "rgba(255, 251, 243, 0.5)");
    halo.addColorStop(1, "rgba(255, 251, 243, 0)");
    ctx.fillStyle = halo;
    ctx.beginPath();
    ctx.arc(cx, cy + cellSize * 0.02, cellSize * 0.4, 0, Math.PI * 2);
    ctx.fill();

    ctx.fillStyle = "rgba(34, 27, 20, 0.2)";
    ctx.beginPath();
    ctx.ellipse(cx, cy + cellSize * 0.34, cellSize * 0.19, cellSize * 0.055, 0, 0, Math.PI * 2);
    ctx.fill();

    if (art.token.complete && art.token.naturalWidth > 0) {
      ctx.shadowColor = "rgba(255, 251, 243, 0.9)";
      ctx.shadowBlur = Math.max(1.5, cellSize * 0.06);
      ctx.drawImage(
        art.token,
        cx - tokenWidth / 2,
        // 棋子的底边对齐当前格下边界，避免下半身压到下一格
        cy + cellSize * 0.5 - tokenHeight + bob,
        tokenWidth,
        tokenHeight
      );
    } else {
      drawFallbackPenguin({ x: cx, y: cy - cellSize * 0.12 }, cellSize, bob);
    }

    ctx.restore();
    drawPlayerTag(center, cellSize);
  }

  function render(now) {
    if (!maze) return;

    var size = fitCanvas();
    if (!size) return;

    var width = size.width;
    var height = size.height;
    var boardSize = Math.min(width, height);
    var padding = Math.max(13, boardSize * 0.047);
    var cellSize = Math.min((width - padding * 2) / COLS, (height - padding * 2) / ROWS);
    var mazeWidth = cellSize * COLS;
    var mazeHeight = cellSize * ROWS;
    var offsetX = (width - mazeWidth) / 2;
    var offsetY = (height - mazeHeight) / 2;
    var stamp = typeof now === "number" ? now : performance.now();

    ctx.clearRect(0, 0, width, height);

    // 纸面底色
    ctx.fillStyle = "#f8efdf";
    ctx.fillRect(0, 0, width, height);

    var wash = ctx.createRadialGradient(
      width * 0.4,
      height * 0.34,
      Math.min(width, height) * 0.08,
      width * 0.5,
      height * 0.5,
      Math.max(width, height) * 0.74
    );
    wash.addColorStop(0, "rgba(255, 252, 244, 0.6)");
    wash.addColorStop(1, "rgba(193, 157, 109, 0.1)");
    ctx.fillStyle = wash;
    ctx.fillRect(0, 0, width, height);

    ctx.save();
    for (var i = 0; i < SPECKS.length; i += 1) {
      var speck = SPECKS[i];
      ctx.fillStyle = i % 4 === 0 ? "rgba(151, 100, 55, 0.12)" : "rgba(66, 50, 32, 0.08)";
      ctx.beginPath();
      ctx.arc(speck.x * width, speck.y * height, speck.r, 0, Math.PI * 2);
      ctx.fill();
    }
    ctx.restore();

    // 起点、出口的淡色地块
    ctx.fillStyle = "rgba(37, 33, 28, 0.045)";
    ctx.fillRect(offsetX, offsetY, cellSize, cellSize);
    ctx.fillStyle = "rgba(173, 43, 40, 0.075)";
    ctx.fillRect(
      offsetX + (COLS - 1) * cellSize,
      offsetY + (ROWS - 1) * cellSize,
      cellSize,
      cellSize
    );

    drawStart(cellCenter(0, 0, offsetX, offsetY, cellSize), cellSize);
    drawExit(stamp, cellCenter(COLS - 1, ROWS - 1, offsetX, offsetY, cellSize), cellSize);

    // 墨色迷宫墙
    drawWallPath(offsetX, offsetY, cellSize);
    ctx.save();
    ctx.strokeStyle = "#2a261f";
    ctx.lineWidth = Math.max(2, cellSize * 0.115);
    ctx.lineCap = "round";
    ctx.lineJoin = "round";
    ctx.shadowColor = "rgba(40, 30, 18, 0.14)";
    ctx.shadowBlur = Math.max(0.8, cellSize * 0.045);
    ctx.stroke();
    ctx.restore();

    drawPlayer(stamp, cellCenter(player.x, player.y, offsetX, offsetY, cellSize), cellSize);
  }

  function animate(now) {
    if (phase !== "playing") {
      frameId = 0;
      return;
    }
    render(now);
    frameId = requestAnimationFrame(animate);
  }

  function startAnimation() {
    if (frameId) cancelAnimationFrame(frameId);
    frameId = requestAnimationFrame(animate);
  }

  /* ---------- 位置与无障碍文案 ---------- */

  function positionLabel() {
    return (
      "企鹅迷宫，共 " + COLS + " 列 " + ROWS + " 行。企鹅在第 " + (player.x + 1) +
      " 列，第 " + (player.y + 1) + " 行。出口在第 " + COLS + " 列，第 " + ROWS +
      " 行。使用方向键、WASD 或滑动移动。"
    );
  }

  function updatePositionLabel() {
    dom.canvas.setAttribute("aria-label", positionLabel());
  }

  function announce(message) {
    dom.a11yStatus.textContent = message;
  }

  /* ---------- 游戏流程 ---------- */

  function chooseDuration(minutes) {
    if (DURATION_OPTIONS.indexOf(minutes) === -1) return;
    selectedMinutes = minutes;

    dom.durationButtons.forEach(function (button) {
      var active = Number(button.getAttribute("data-minutes")) === minutes;
      button.setAttribute("aria-pressed", active ? "true" : "false");
    });

    dom.startButtonMeta.textContent = minutes + " 分钟 →";
    dom.durationHint.textContent = minutes === DEFAULT_MINUTES ? "默认 3 分钟" : "已选 " + minutes + " 分钟";
  }

  function setReadyState() {
    phase = "ready";
    if (timerId) {
      clearInterval(timerId);
      timerId = 0;
    }
    if (frameId) {
      cancelAnimationFrame(frameId);
      frameId = 0;
    }
    dom.timer.textContent = "--:--";
    dom.timerBar.style.width = "100%";
    dom.timer.classList.remove("is-low");
    dom.phaseText.textContent = "未入阵";
    dom.canvas.setAttribute("aria-label", "企鹅迷宫，正在准备迷阵。");
    announce("等待入阵。");
  }

  function preparePreview() {
    maze = buildPlayableMaze();
    player = { x: 0, y: 0 };
    dom.roundNumber.textContent = roundLabel(round + 1);
    render(performance.now());
  }

  function startRound() {
    round += 1;
    maze = buildPlayableMaze();
    player = { x: 0, y: 0 };
    totalMs = selectedMinutes * 60000;
    endAt = Date.now() + totalMs;
    phase = "playing";

    dom.roundNumber.textContent = roundLabel(round);
    dom.canvas.setAttribute("aria-label", positionLabel());
    announce(
      "入阵。企鹅在第 1 列，第 1 行，出口在第 " + COLS + " 列，第 " + ROWS +
      " 行。倒计时开始。"
    );

    dom.startScreen.hidden = true;
    dom.resultScreen.hidden = true;
    dom.page.inert = false;
    document.body.classList.remove("is-modal");
    dom.phaseText.textContent = "尚存";
    dom.timer.classList.remove("is-low");
    dom.timerBar.style.width = "100%";

    render(performance.now());
    tickTimer();
    if (timerId) clearInterval(timerId);
    timerId = window.setInterval(tickTimer, 200);
    startAnimation();

    if (typeof dom.canvas.focus === "function") {
      dom.canvas.focus({ preventScroll: true });
    }
  }

  function tickTimer() {
    if (phase !== "playing") return;

    var remaining = endAt - Date.now();
    if (remaining <= 0) {
      finishRound("timeout");
      return;
    }

    dom.timer.textContent = formatClock(Math.ceil(remaining / 1000));
    dom.timerBar.style.width = clamp(remaining / totalMs, 0, 1) * 100 + "%";
    dom.timer.classList.toggle("is-low", remaining <= TURN_THRESHOLD);
  }

  function attemptMove(dx, dy) {
    if (phase !== "playing") return false;

    // 计时器即使被浏览器节流，也不允许超时后再走一步
    if (Date.now() >= endAt) {
      finishRound("timeout");
      return false;
    }

    var cell = maze.cells[player.y][player.x];
    var blocked = false;

    if (dx === 1 && cell.e) blocked = true;
    if (dx === -1 && cell.w) blocked = true;
    if (dy === 1 && cell.s) blocked = true;
    if (dy === -1 && cell.n) blocked = true;

    if (blocked) {
      announce("前方是墙，换个方向。");
      return false;
    }

    player.x += dx;
    player.y += dy;

    updatePositionLabel();
    announce("企鹅走到第 " + (player.x + 1) + " 列，第 " + (player.y + 1) + " 行。");

    if (player.x === COLS - 1 && player.y === ROWS - 1) {
      finishRound("win");
    } else {
      render(performance.now());
    }

    return true;
  }

  function finishRound(outcome) {
    if (phase !== "playing") return;

    var won = outcome === "win";
    var remaining = Math.max(0, endAt - Date.now());
    var elapsedSeconds = clamp(Math.ceil((totalMs - remaining) / 1000), 1, Math.round(totalMs / 1000));
    phase = won ? "won" : "lost";

    if (timerId) {
      clearInterval(timerId);
      timerId = 0;
    }
    if (frameId) {
      cancelAnimationFrame(frameId);
      frameId = 0;
    }

    if (won) {
      dom.timer.textContent = formatClock(Math.ceil(remaining / 1000));
      dom.timerBar.style.width = clamp(remaining / totalMs, 0, 1) * 100 + "%";
      dom.phaseText.textContent = "已损";
      announce("迷宫已破。我道心已损。");
    } else {
      dom.timer.textContent = "00:00";
      dom.timerBar.style.width = "0%";
      dom.phaseText.textContent = "崩了";
      announce("时辰已尽。我婆娘不要我了。");
    }
    dom.timer.classList.remove("is-low");

    render(performance.now());
    showResult(won, won ? elapsedSeconds : selectedMinutes * 60);
  }

  function showResult(won, displaySeconds) {
    dom.resultPanel.classList.toggle("is-win", won);
    dom.resultPanel.classList.toggle("is-lose", !won);

    dom.resultKicker.textContent = won ? "结局一 · 道心已损" : "结局二 · 时辰已尽";
    dom.resultTitle.textContent = won ? "我道心已损" : "我婆娘不要我了";
    dom.resultDescription.textContent = won
      ? "你在最后一刻找到了出口。可《无情道》翻到最后一页，写的还是她的名字。"
      : "钟声落下，迷宫还在，婆娘已经走了。下次别一边看书一边找路。";
    dom.resultImage.src = won ? art.win.src : art.lose.src;
    dom.resultImage.alt = won
      ? "捧着《无情道》的企鹅，头顶写着“我道心已损”。"
      : "委屈巴巴的企鹅，横幅上写着“我婆娘不要我了”。";
    dom.resultWatermark.textContent = won ? "损" : "空";
    dom.resultTime.textContent = formatClock(displaySeconds);
    dom.resultExit.textContent = won ? "已抵达" : "未抵达";

    dom.startScreen.hidden = true;
    dom.resultScreen.hidden = false;
    dom.page.inert = true;
    document.body.classList.add("is-modal");
    dom.resultTitle.focus({ preventScroll: true });
  }

  function openStartScreen(focusButton) {
    setReadyState();
    preparePreview();
    dom.resultScreen.hidden = true;
    dom.startScreen.hidden = false;
    dom.page.inert = true;
    document.body.classList.add("is-modal");
    if (focusButton) {
      dom.startButton.focus({ preventScroll: true });
    }
  }

  /* ---------- 控制 ---------- */

  function handleKeyDown(event) {
    if (phase !== "playing") return;
    if (event.ctrlKey || event.metaKey || event.altKey) return;

    var direction = KEY_DIRECTIONS[event.key.toLowerCase()];
    if (!direction) return;

    event.preventDefault();
    attemptMove(direction[0], direction[1]);
  }

  function handlePointerDown(event) {
    if (phase !== "playing") return;
    if (!event.isPrimary || (event.pointerType === "mouse" && event.button !== 0)) return;

    swipe = { id: event.pointerId, x: event.clientX, y: event.clientY };
    dom.stage.setPointerCapture && dom.stage.setPointerCapture(event.pointerId);
    event.preventDefault();
  }

  function handlePointerMove(event) {
    if (!swipe || event.pointerId !== swipe.id || phase !== "playing") return;

    var dx = event.clientX - swipe.x;
    var dy = event.clientY - swipe.y;
    var threshold = Math.max(18, Math.min(32, dom.stage.clientWidth * 0.05));

    if (Math.max(Math.abs(dx), Math.abs(dy)) < threshold) return;

    if (Math.abs(dx) > Math.abs(dy)) {
      attemptMove(dx > 0 ? 1 : -1, 0);
    } else {
      attemptMove(0, dy > 0 ? 1 : -1);
    }

    // 长距离滑动可以连续走多格：重新起算下一次方向
    swipe.x = event.clientX;
    swipe.y = event.clientY;
    event.preventDefault();
  }

  function endSwipe(event) {
    if (!swipe || (event && event.pointerId !== swipe.id)) return;
    if (dom.stage.hasPointerCapture && dom.stage.hasPointerCapture(swipe.id)) {
      dom.stage.releasePointerCapture(swipe.id);
    }
    swipe = null;
  }

  function trapFocus(overlay) {
    overlay.addEventListener("keydown", function (event) {
      if (event.key !== "Tab") return;

      var focusable = Array.prototype.filter.call(
        overlay.querySelectorAll("button:not([disabled]), [href], [tabindex]:not([tabindex='-1'])"),
        function (element) {
          return element.offsetWidth > 0 || element.offsetHeight > 0;
        }
      );

      if (focusable.length === 0) return;
      var first = focusable[0];
      var last = focusable[focusable.length - 1];

      if (event.shiftKey && document.activeElement === first) {
        event.preventDefault();
        last.focus();
      } else if (!event.shiftKey && document.activeElement === last) {
        event.preventDefault();
        first.focus();
      }
    });
  }

  function bindEvents() {
    dom.durationButtons.forEach(function (button) {
      button.addEventListener("click", function () {
        chooseDuration(Number(button.getAttribute("data-minutes")));
      });
    });

    dom.startButton.addEventListener("click", startRound);
    dom.againButton.addEventListener("click", startRound);
    dom.reselectButton.addEventListener("click", function () {
      openStartScreen(true);
    });

    window.addEventListener("keydown", handleKeyDown);
    dom.stage.addEventListener("pointerdown", handlePointerDown, { passive: false });
    dom.stage.addEventListener("pointermove", handlePointerMove, { passive: false });
    dom.stage.addEventListener("pointerup", endSwipe);
    dom.stage.addEventListener("pointercancel", endSwipe);
    dom.stage.addEventListener("lostpointercapture", function () {
      swipe = null;
    });

    trapFocus(dom.startScreen);
    trapFocus(dom.resultScreen);

    if ("ResizeObserver" in window) {
      var observer = new ResizeObserver(scheduleRender);
      observer.observe(dom.stage);
    } else {
      window.addEventListener("resize", scheduleRender);
    }

    // 切换前后台时，计时仍以真实时间为准；回到前台立即刷新一次
    document.addEventListener("visibilitychange", function () {
      if (!document.hidden && phase === "playing") {
        tickTimer();
        scheduleRender();
      }
    });
  }

  /* ---------- 启动 ---------- */

  bindEvents();
  chooseDuration(DEFAULT_MINUTES);
  openStartScreen(false);
})();
