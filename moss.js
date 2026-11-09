// Moss and ferns behind the page. The model is written up at github.com/PrithviHegde/moss:
// spores travel lognormal distances, and ferns rise after Weibull waiting times.
//
// Moss grows where the cursor rests. Moving the cursor clears moss along its path, and cleared
// paths regrow while the cursor is still. Ferns rise from mature, undisturbed moss (never over
// the text column), and brushing one curls it back into a fiddlehead until it sinks.
(function () {
  'use strict';

  var CELL = 4;                        // css px per grid cell, shared by moss and ferns

  // The model (same parameters as the write-up)
  var SPORE_S = 1.5;                   // lognormal shape
  var SPORE_MEAN = 1;                  // mean dispersal distance, in cells
  var SPORE_MU = Math.log(SPORE_MEAN) - SPORE_S * SPORE_S / 2;
  var FERN_K = 3;                      // Weibull shape: readiness rises the longer a patch is left alone
  var FERN_LAMBDA = 12;                // Weibull scale, seconds (median wait about 10.6 s)

  // Pacing (tuned by eye)
  var STILL_AFTER = 0.35;              // s without moving before the cursor counts as resting
  var REACH_START = 4, REACH_GROWTH = 1.4, REACH_MAX = 28;  // cells; the clump widens as you linger
  var RELEASES_PER_S = 40000;          // spore releases sampled around a resting cursor
  var OUTPOST_TAKE = 0.004;            // chance a spore landing beyond that reach takes root
  var LOBE = 9, CUSHION = 3.5;          // cells: scale of a clump's lobes, and of the cushions within it
  var REGROW_PER_S = 25000;            // samples per s that refill cleared paths anywhere
  var BRUSH = 1.6;                     // cells cleared either side of the cursor's path
  var MATURE = 8;                      // s undisturbed before moss counts as mature
  var MAX_FERNS = 8, FERN_GAP = 18;    // ferns on screen at once, and their minimum spacing in cells
  var GROW_S = 4, CURL_S = 1.1;        // s for a fern to unfurl, and to curl back and sink
  var TEXT_DIM = 0.8;                  // moss behind the text is mixed this far toward the background
                                       // (the least that keeps muted text and links at WCAG AA)

  var reduceMotion = matchMedia('(prefers-reduced-motion: reduce)');
  var darkScheme = matchMedia('(prefers-color-scheme: dark)');

  var canvas = document.createElement('canvas');
  canvas.className = 'moss';
  canvas.setAttribute('aria-hidden', 'true');
  document.body.insertBefore(canvas, document.body.firstChild);
  var ctx = canvas.getContext('2d');

  var W = 0, H = 0, img, buf;
  var born = new Float32Array(0);      // when each cell's moss was planted (s), or -1 for bare ground
  var cleared = new Uint8Array(0);     // 1 where the cursor has cleared moss that may regrow
  var colL = 0, colR = 0;              // the text column, in cells
  var moss, mossDim, fernPal;
  var ferns = [], pending = [];
  var cursor = null, lastMove = 0, nextScout = 0, lastDraw = -1, dirty = true;

  // ---- sampling ----------------------------------------------------------

  function gauss() {
    return Math.sqrt(-2 * Math.log(1 - Math.random())) * Math.cos(2 * Math.PI * Math.random());
  }
  function sporeDistance() { return Math.exp(SPORE_MU + SPORE_S * gauss()); }
  function fernWait() { return FERN_LAMBDA * Math.pow(-Math.log(1 - Math.random()), 1 / FERN_K); }

  function hash(x, y) {
    var n = Math.imul(x, 374761393) + Math.imul(y, 668265263);
    n = Math.imul(n ^ (n >>> 13), 1274126177);
    return ((n ^ (n >>> 16)) >>> 0) / 4294967296;
  }

  // Smooth value noise in [0, 1]: gives clumps lobed edges and the moss its cushions.
  function noise(x, y) {
    var ix = Math.floor(x), iy = Math.floor(y), fx = x - ix, fy = y - iy;
    fx = fx * fx * (3 - 2 * fx); fy = fy * fy * (3 - 2 * fy);
    var a = hash(ix, iy), b = hash(ix + 1, iy), c = hash(ix, iy + 1), d = hash(ix + 1, iy + 1);
    return a + (b - a) * fx + (c - a) * fy + (a - b - c + d) * fx * fy;
  }

  // ---- colours -----------------------------------------------------------

  function rgb(hex) {
    hex = hex.trim().replace('#', '');
    return [0, 2, 4].map(function (i) { return parseInt(hex.slice(i, i + 2), 16); });
  }
  function pack(c) { return ((255 << 24) | (c[2] << 16) | (c[1] << 8) | c[0]) >>> 0; }
  function mix(a, b, t) { return a.map(function (v, i) { return Math.round(v + (b[i] - v) * t); }); }

  function readColors() {
    var cs = getComputedStyle(document.documentElement);
    var v = function (name) { return rgb(cs.getPropertyValue(name)); };
    var bg = v('--bg');
    var tones = [v('--moss-1'), v('--moss-2'), v('--moss-3')];
    moss = tones.map(pack);
    mossDim = tones.map(function (c) { return pack(mix(c, bg, TEXT_DIM)); });
    fernPal = [v('--fern-stem'), v('--fern-leaf'), v('--fern-tip')].map(pack);
    dirty = true;
  }

  // ---- grid --------------------------------------------------------------

  function resize() {
    // at least 1x1: a window can report zero size while it loads in the background
    var w = Math.max(1, Math.ceil(innerWidth / CELL)), h = Math.max(1, Math.ceil(innerHeight / CELL));
    if (w !== W || h !== H) {
      var nb = new Float32Array(w * h).fill(-1), nc = new Uint8Array(w * h);
      for (var y = 0; y < Math.min(h, H); y++) {
        for (var x = 0; x < Math.min(w, W); x++) {
          nb[y * w + x] = born[y * W + x];
          nc[y * w + x] = cleared[y * W + x];
        }
      }
      W = w; H = h; born = nb; cleared = nc;
      canvas.width = W; canvas.height = H;
      canvas.style.width = W * CELL + 'px';
      canvas.style.height = H * CELL + 'px';
      img = ctx.createImageData(W, H);
      buf = new Uint32Array(img.data.buffer);
    }
    var col = document.querySelector('main').getBoundingClientRect();
    colL = Math.floor(col.left / CELL);
    colR = Math.ceil(col.right / CELL);
    dirty = true;
  }

  function isMoss(x, y) { return x >= 0 && y >= 0 && x < W && y < H && born[y * W + x] >= 0; }

  function plant(x, y, now) {
    if (x < 0 || y < 0 || x >= W || y >= H) return;
    var i = y * W + x;
    if (born[i] >= 0) return;
    born[i] = now;
    cleared[i] = 0;
    dirty = true;
  }

  // One spore from (x, y): a lognormal distance in a uniform direction. Ground the cursor
  // cleared always takes it back. Spores from around the cursor (reach > 0) take root anywhere
  // within that reach, and only rarely beyond it: those are the far outposts the fat tail makes.
  // The distance is never altered; only where a spore can establish depends on the cursor.
  function disperse(x, y, now, reach) {
    var d = sporeDistance(), a = Math.random() * 2 * Math.PI;
    var tx = Math.round(x + Math.cos(a) * d), ty = Math.round(y + Math.sin(a) * d);
    if (tx < 0 || ty < 0 || tx >= W || ty >= H) return;
    var t = ty * W + tx;
    if (born[t] >= 0) return;
    if (!cleared[t]) {
      if (!reach) return;
      var lobed = reach * (0.65 + 0.7 * noise(tx / LOBE + 50, ty / LOBE + 50));
      if (Math.hypot(tx - cursor.x, ty - cursor.y) > lobed && Math.random() > OUTPOST_TAKE) return;
    }
    plant(tx, ty, now);
  }

  function grow(now, dt, dwell) {
    var cx = cursor.x, cy = cursor.y;
    for (var dy = -1; dy <= 1; dy++) {
      for (var dx = -1; dx <= 1; dx++) plant((cx | 0) + dx, (cy | 0) + dy, now);
    }
    var reach = Math.min(REACH_MAX, REACH_START + dwell * REACH_GROWTH);
    for (var k = RELEASES_PER_S * dt; k > 0; k--) {
      var a = Math.random() * 2 * Math.PI, r = reach * Math.sqrt(Math.random());
      var x = Math.floor(cx + Math.cos(a) * r), y = Math.floor(cy + Math.sin(a) * r);
      if (isMoss(x, y)) disperse(x, y, now, reach);
    }
    for (var j = REGROW_PER_S * dt; j > 0; j--) {
      var i = (Math.random() * W * H) | 0;
      if (born[i] >= 0) disperse(i % W, (i / W) | 0, now, 0);
    }
  }

  // ---- the cursor --------------------------------------------------------

  function clearPath(x0, y0, x1, y1) {
    var len = Math.hypot(x1 - x0, y1 - y0), steps = Math.max(1, Math.ceil(len / 0.5));
    var r = Math.ceil(BRUSH);
    for (var s = 0; s <= steps; s++) {
      var px = x0 + (x1 - x0) * s / steps, py = y0 + (y1 - y0) * s / steps;
      for (var dy = -r; dy <= r; dy++) {
        for (var dx = -r; dx <= r; dx++) {
          if (dx * dx + dy * dy > BRUSH * BRUSH) continue;
          var x = Math.round(px + dx), y = Math.round(py + dy);
          if (x < 0 || y < 0 || x >= W || y >= H) continue;
          var i = y * W + x;
          if (born[i] >= 0) { born[i] = -1; cleared[i] = 1; dirty = true; }
        }
      }
      ferns.forEach(function (f) {
        if (f.curling) return;
        // a fern's body sits roughly in a circle above its base
        var bx = f.x + Math.cos(f.ang) * f.len * 0.45, by = f.y + Math.sin(f.ang) * f.len * 0.45;
        if (Math.hypot(px - bx, py - by) < f.len * 0.5) f.curling = true;
      });
    }
  }

  function onPointer(e) {
    if (e.type === 'pointerdown' && e.pointerType !== 'mouse') cursor = null;
    var x = e.clientX / CELL, y = e.clientY / CELL;
    if (cursor) {
      if (Math.hypot(x - cursor.x, y - cursor.y) < 0.75) return;
      clearPath(cursor.x, cursor.y, x, y);
    }
    cursor = { x: x, y: y };
    lastMove = performance.now() / 1000;
  }
  function onLeave(e) {
    if (e.type === 'pointerleave' || e.pointerType !== 'mouse') cursor = null;
  }

  // ---- ferns -------------------------------------------------------------

  // Look for mature, undisturbed moss away from the text and from other ferns. Each site found
  // waits a Weibull time; if its moss is disturbed before then, the fern never comes.
  function scout(now) {
    if (ferns.length + pending.length >= MAX_FERNS) return;
    for (var k = 0; k < 40; k++) {
      var i = (Math.random() * W * H) | 0;
      if (born[i] < 0 || now - born[i] < MATURE) continue;
      var x = i % W, y = (i / W) | 0, len = 14 + Math.random() * 10;
      if (y < len + 2) continue;
      if (x > colL - len * 0.55 - 2 && x < colR + len * 0.55 + 2) continue;
      var ok = true;
      for (var dy = -1; dy <= 1 && ok; dy++) {
        for (var dx = -1; dx <= 1 && ok; dx++) {
          var j = (y + dy) * W + x + dx;
          ok = isMoss(x + dx, y + dy) && now - born[j] >= MATURE / 2;
        }
      }
      if (!ok) continue;
      var near = ferns.concat(pending).some(function (f) { return Math.hypot(f.x - x, f.y - y) < FERN_GAP; });
      if (near) continue;
      pending.push({ x: x, y: y, born: born[i], due: now + fernWait(), len: len });
      return;
    }
  }

  function tendFerns(now, dt) {
    if (now >= nextScout) { nextScout = now + 0.25; scout(now); }
    pending = pending.filter(function (p) {
      if (p.x >= W || p.y >= H || born[p.y * W + p.x] !== p.born) return false;
      if (now < p.due) return true;
      ferns.push({
        x: p.x + 0.5, y: p.y + 0.5,
        ang: -Math.PI / 2 + (Math.random() - 0.5) * 0.8,
        len: p.len,
        bend: (Math.random() - 0.3) * 0.9,
        sign: Math.random() < 0.5 ? -1 : 1,
        g: 0, curling: false
      });
      return false;
    });
    ferns.forEach(function (f) {
      f.g = f.curling ? f.g - dt / CURL_S : Math.min(1, f.g + dt / GROW_S);
    });
    ferns = ferns.filter(function (f) { return f.g > 0; });
  }

  function plot(x, y, color) {
    var ix = x | 0, iy = y | 0;
    if (ix < 0 || iy < 0 || ix >= W || iy >= H) return;
    buf[iy * W + ix] = color;
  }

  // One frond: a stem that unfurls from a fiddlehead, with paired leaflets that unfurl in turn
  // once the stem has passed them. Running g backwards curls it up again.
  function frond(x, y, ang, L, g, depth, sign, f) {
    if (g <= 0 || L < 1.5) return;
    var cur = L * g;
    var tipR = L * (depth === 0 ? 0.14 : 0.25);
    var curlAmp = (Math.PI * (depth === 0 ? 2.2 : 1.2) * (1 - g)) / tipR;
    var bend = depth === 0 ? sign * f.bend / L : sign * 0.25 / L;
    var spacing = depth === 0 ? Math.max(2.2, L * 0.065) : 1.6;
    var nextLeaf = depth === 0 ? L * 0.12 : 1.2;
    var px = x, py = y, a = ang;
    for (var s = 0; s < cur; s += 0.5) {
      var d = cur - s;
      a += (bend + sign * curlAmp * Math.exp(-d / tipR)) * 0.5;
      px += Math.cos(a) * 0.5;
      py += Math.sin(a) * 0.5;
      plot(px, py, d < 2 ? fernPal[2] : depth === 0 ? fernPal[0] : fernPal[1]);
      if (s >= nextLeaf) {
        nextLeaf += spacing;
        if (depth === 0) {
          // leaflets longest a third of the way up, tapering to the tip
          var u = s / L;
          var childL = L * 0.3 * Math.sin(Math.PI * Math.min(1, u * 0.85 + 0.12)) + 1;
          var childG = Math.min(1, (cur - s) / (childL * 2));
          var sweep = 1.15 - u * 0.4;
          frond(px, py, a + sweep, childL, childG, 1, -1, f);
          frond(px, py, a - sweep, childL, childG, 1, 1, f);
        }
      }
    }
  }

  // ---- drawing -----------------------------------------------------------

  function draw(now) {
    buf.fill(0);
    for (var y = 0; y < H; y++) {
      for (var x = 0; x < W; x++) {
        var i = y * W + x, b = born[i];
        if (b < 0) continue;
        // tone 0 is the faintest against the page and tone 2 the strongest, in both themes.
        // Young moss and clump edges are faint; mature moss forms cushions, strong at the
        // core and faint in the gaps between them.
        var n = (x > 0 && born[i - 1] >= 0) + (x < W - 1 && born[i + 1] >= 0) +
                (y > 0 && born[i - W] >= 0) + (y < H - 1 && born[i + W] >= 0);
        var ripe = Math.min(1, (now - b) / MATURE);
        var lump = noise(x / CUSHION, y / CUSHION) + (hash(x, y) - 0.5) * 0.25;
        var t = ripe * (0.35 + lump * 0.75) + (n - 4) * 0.12;
        var tone = t < 0.3 ? 0 : t < 0.68 ? 1 : 2;
        buf[i] = (x >= colL && x < colR ? mossDim : moss)[tone];
      }
    }
    ferns.forEach(function (f) {
      frond(f.x, f.y, f.ang, f.len, 1 - Math.pow(1 - f.g, 2.2), 0, f.sign, f);
    });
    ctx.putImageData(img, 0, 0);
    lastDraw = now;
    dirty = false;
  }

  // With reduced motion: no growth, just a few settled clumps in the bottom corners.
  function drawStill() {
    born.fill(-1);
    var clumps = [[0.03, 26], [0.13, 15], [0.9, 30], [0.99, 18]];
    for (var y = 0; y < H; y++) {
      for (var x = 0; x < W; x++) {
        if (x >= colL && x < colR) continue;
        var v = 0;
        clumps.forEach(function (c) {
          var dx = (x - c[0] * W) / (c[1] * 1.5), dy = (H - y) / c[1];
          v += Math.exp(-(dx * dx + dy * dy) * 2);
        });
        v += (hash(x, y) - 0.5) * 0.3;
        if (v >= 0.3) born[y * W + x] = 0;
      }
    }
    ferns = []; pending = [];
    draw(MATURE * 10);
  }

  // ---- loop --------------------------------------------------------------

  var last = performance.now() / 1000;
  function frame(ms) {
    var now = ms / 1000, dt = Math.min(0.05, now - last);
    last = now;
    var resting = cursor && now - lastMove > STILL_AFTER;
    if (resting) grow(now, dt, now - lastMove - STILL_AFTER);
    tendFerns(now, dt);
    // moss keeps maturing, so redraw now and then even when nothing moves
    if (resting || dirty || ferns.length || now - lastDraw > 0.5) draw(now);
    requestAnimationFrame(frame);
  }

  readColors();
  resize();
  darkScheme.addEventListener('change', function () { readColors(); if (reduceMotion.matches) drawStill(); });
  addEventListener('resize', function () { resize(); if (reduceMotion.matches) drawStill(); });

  if (reduceMotion.matches) {
    drawStill();
  } else {
    addEventListener('pointermove', onPointer, { passive: true });
    addEventListener('pointerdown', onPointer, { passive: true });
    addEventListener('pointerup', onLeave, { passive: true });
    addEventListener('pointercancel', onLeave, { passive: true });
    document.documentElement.addEventListener('pointerleave', onLeave);
    requestAnimationFrame(frame);
  }
})();
