// The moss garden at the top of the page. The model is written up at github.com/PrithviHegde/moss:
// spores travel lognormal distances, and the waits for new patches and for ferns are Weibull.
//
// The garden fills the top of the page and carries on down the side margins, stopping well short
// of the text. Ground stays asleep until it first scrolls into view, so visitors see each part of
// the garden begin; once seen, it keeps growing whether or not it's on screen. Moss spreads as a carpet from wherever it already grows, taking root only on ground a hidden
// habitat map marks as damp enough, so it creeps in fingers and patches rather than circles.
// Ferns rise from settled moss, more often next to other ferns, leaning whichever way they like.
// Creepers grow along the edges. The cursor only disturbs: it clears moss (which grows back),
// curls ferns back into fiddleheads, and makes creepers fold their leaves like a touch-me-not;
// a click rolls a creeper up into a coil for a while.
(function () {
  'use strict';

  var garden = document.querySelector('.garden');
  if (!garden) return;
  var intro = garden.querySelector('.intro');
  var main = document.querySelector('main');

  var P = 4;                           // css px per pixel; moss, creepers and ferns share this grid

  // The model
  var SPORE_S = 1.5, SPORE_MEAN = 1;   // lognormal spore distance, in pixels
  var SPORE_MU = Math.log(SPORE_MEAN) - SPORE_S * SPORE_S / 2;
  var SEED_K = 2, SEED_LAMBDA = 5;     // Weibull wait between spores landing somewhere new (per screenful), s
  var FERN_K = 3, FERN_LAMBDA = 6;     // Weibull wait before a fern rises from settled moss, seconds

  // Pacing and look (tuned by eye)
  var START_SEEDS = 3;
  var WAKE_SEEDS = 7;                  // spores landing per screenful of newly seen margin
  var RELEASE_RATE = 2.5;              // spores released per moss pixel per second
  var MAX_RELEASES = 2500;             // per frame, to bound the work on big pages
  var MARGIN = 12;                     // pixels kept bare between the side gardens and the text column
  var MIN_GUTTER = 14;                 // pixels: a side margin narrower than this grows nothing
  var HABITAT = 0.57, HABITAT_SOFT = 0.1;    // habitat score where moss starts, and fully, taking root
  var BRUSH = 1.6;                     // pixels cleared either side of the cursor's path
  var SPROUT = 1.2;                    // s before a moss pixel can carry a sprig
  var MATURE = 3;                      // s undisturbed before moss can carry a fern
  var MAX_FERNS = 12, FERN_GAP = 9;    // ferns at once, and their spacing in pixels
  var GROUP = 4, GROUP_R = 20;         // at most this many ferns within this many pixels
  var KIN = 0.45;                      // share of new fern sites looked for next to an existing fern
  var GROW_S = 3.5, CURL_S = 1.1;      // s for a fern to unfurl, and to curl back and sink
  var VINE_AFTER = 2, VINE_DELAY = 15; // creepers start this many s after this many ferns are fully up
  var VINE_ANYWAY = 45;                // or this many s after the garden starts, if ferns have no room
  var SPURT_MIN = 3, SPURT_MAX = 8;    // pixels a creeper sprouts in one spurt
  var REST_MIN = 1.5, REST_MAX = 4.5;  // s it rests between spurts
  var SPURT_EASE = 4;                  // how quickly a spurt settles (higher is snappier)
  var BUD_S = 0.5, UNFURL_S = 1.3;     // s a new leaf spends as a bud, then half open
  var FOLD_REACH = 24;                 // pixels along a creeper that fold when touched
  var FOLD_WAVE = 0.03;                // s for the fold to travel one pixel along the stem
  var FOLD_S = 0.25, SHUT_S = 4, OPEN_S = 1.5;   // s to fold, to stay shut, and to open again
  var COIL_S = 0.6, COILED_S = 5, UNCOIL_S = 2;  // s to roll up after a click, to stay rolled, to unroll
  var STILL_SECONDS = 70;              // with reduced motion: how long to grow before drawing once

  var reduceMotion = matchMedia('(prefers-reduced-motion: reduce)').matches;
  var root = document.documentElement;

  var canvas = document.createElement('canvas');
  canvas.setAttribute('aria-hidden', 'true');
  canvas.className = 'garden-canvas';
  document.body.insertBefore(canvas, document.body.firstChild);
  var ctx = canvas.getContext('2d');

  var W = 0, H = 0, img, buf;
  var born = new Float32Array(0);      // when each pixel's moss took root (s), or -1 for bare ground
  var cleared = new Uint8Array(0);     // 1 where the cursor cleared moss that may grow back
  var habitat = new Float32Array(0);   // how damp each pixel's ground is, 0 to 1
  var mossList = new Int32Array(0), mossAt = new Int32Array(0), mossCount = 0;   // moss pixels, for picking one at random
  var wokeAt = new Float32Array(0);    // when each row first came into view (s), or -1 while still unseen
  var awakeRows = 0, seedDebt = 0;
  var zone = { x0: 0, y0: 0, x1: 0, y1: 0 };   // the intro text, in pixels
  var heroH = 0, gutL = -1, gutR = 1e9;            // the top garden's height; where the text column's bare band starts and ends
  var ferns = [], pending = [], vines = [];
  var C = {};
  var ground = [Math.random() * 100, Math.random() * 100];   // a different habitat map on every visit
  var startedAt = 0, cursor = null, nextSeed = 0, nextScout = 0, releaseDebt = 0, started = false;

  // ---- sampling and noise ----------------------------------------------------

  function gauss() { return Math.sqrt(-2 * Math.log(1 - Math.random())) * Math.cos(2 * Math.PI * Math.random()); }
  function sporeDistance() { return Math.exp(SPORE_MU + SPORE_S * gauss()); }
  function weibull(k, lambda) { return lambda * Math.pow(-Math.log(1 - Math.random()), 1 / k); }

  function hash(x, y, s) {
    var n = Math.imul(x, 374761393) + Math.imul(y, 668265263) + Math.imul(s || 0, 1442695041);
    n = Math.imul(n ^ (n >>> 13), 1274126177);
    return ((n ^ (n >>> 16)) >>> 0) / 4294967296;
  }
  // smooth value noise in [0, 1]
  function noise(x, y) {
    var ix = Math.floor(x), iy = Math.floor(y), fx = x - ix, fy = y - iy;
    fx = fx * fx * (3 - 2 * fx); fy = fy * fy * (3 - 2 * fy);
    var a = hash(ix, iy, 9), b = hash(ix + 1, iy, 9), c = hash(ix, iy + 1, 9), d = hash(ix + 1, iy + 1, 9);
    return a + (b - a) * fx + (c - a) * fy + (a - b - c + d) * fx * fy;
  }

  // ---- colours and size --------------------------------------------------------

  var NAMES = ['wash-0', 'wash-1', 'sprig', 'sprig-arm', 'sprig-dot', 'vine', 'vine-leaf', 'vine-leaf-2', 'fern-stem', 'fern-leaf', 'fern-tip'];
  function readColors() {
    var cs = getComputedStyle(root);
    NAMES.forEach(function (n) {
      var h = cs.getPropertyValue('--' + n).trim().replace('#', '');
      C[n] = ((255 << 24) | (parseInt(h.slice(4, 6), 16) << 16) | (parseInt(h.slice(2, 4), 16) << 8) | parseInt(h.slice(0, 2), 16)) >>> 0;
    });
  }

  // The canvas covers the whole page. It is sized from the content (never from the page's own
  // scroll height, which would include the canvas and could only grow), rounded down so it never
  // adds scrolling of its own.
  function resize() {
    var page = document.documentElement, sy = window.scrollY;
    var pageH = main.getBoundingClientRect().bottom + sy;
    // at least 1x1: a window can report zero size while it loads in the background
    var w = Math.max(1, Math.floor(page.clientWidth / P)), h = Math.max(1, Math.floor(pageH / P));
    if (w !== W || h !== H) {
      var nb = new Float32Array(w * h).fill(-1), nc = new Uint8Array(w * h);
      for (var y = 0; y < Math.min(h, H); y++) {
        for (var x = 0; x < Math.min(w, W); x++) { nb[y * w + x] = born[y * W + x]; nc[y * w + x] = cleared[y * W + x]; }
      }
      var nw = new Float32Array(h).fill(-1);
      for (var r = 0; r < Math.min(h, H); r++) nw[r] = wokeAt[r];
      W = w; H = h; born = nb; cleared = nc; wokeAt = nw;
      awakeRows = 0; for (r = 0; r < H; r++) if (wokeAt[r] >= 0) awakeRows++;
      canvas.width = W; canvas.height = H;
      canvas.style.width = W * P + 'px';
      canvas.style.height = H * P + 'px';
      img = ctx.createImageData(W, H);
      buf = new Uint32Array(img.data.buffer);
      habitat = new Float32Array(W * H);
      for (var hy = 0; hy < H; hy++) {
        for (var hx = 0; hx < W; hx++) {
          habitat[hy * W + hx] = 0.65 * noise(hx / 22 + ground[0], hy / 16 + ground[1]) + 0.35 * noise(hx / 7 + ground[1], hy / 7 + ground[0]);
        }
      }
      mossList = new Int32Array(W * H); mossAt = new Int32Array(W * H).fill(-1); mossCount = 0;
      for (var i = 0; i < born.length; i++) if (born[i] >= 0) { mossList[mossCount] = i; mossAt[i] = mossCount++; }
    }
    var ir = intro.getBoundingClientRect();
    zone = {
      x0: Math.floor((ir.left - 16) / P), y0: Math.floor((ir.top + sy - 16) / P),
      x1: Math.ceil((ir.right + 16) / P), y1: Math.ceil((ir.bottom + sy + 16) / P)
    };
    heroH = Math.floor((garden.getBoundingClientRect().bottom + sy) / P);
    zone.y1 = Math.max(zone.y1, heroH + 1);   // the clearing runs on down into the bare text column
    // below the top garden, only the side margins grow anything, and not too close to the text
    var mr = main.getBoundingClientRect(), pad = parseFloat(getComputedStyle(main).paddingLeft) || 0;
    gutL = Math.floor((mr.left + pad) / P) - MARGIN;
    gutR = Math.ceil((mr.right - pad) / P) + MARGIN;
    if (gutL < MIN_GUTTER) gutL = -1;
    if (W - gutR < MIN_GUTTER) gutR = W + 1;
    layVines();
  }

  // Bare ground: the intro text's clearing at the top, and below the top garden everything but
  // the side margins. Both have a ragged edge.
  function inClearing(x, y) {
    var m = hash(x, y, 5) * 3;
    if (x > zone.x0 - m && x < zone.x1 + m && y > zone.y0 - m && y < zone.y1 + m) return true;
    return y >= heroH && x > gutL - m && x < gutR + m;
  }

  // ---- moss ----------------------------------------------------------------------

  function isMoss(x, y) { return x >= 0 && y >= 0 && x < W && y < H && born[y * W + x] >= 0; }
  function plant(x, y, now) {
    var i = y * W + x;
    if (born[i] >= 0) return;
    born[i] = now; cleared[i] = 0;
    mossList[mossCount] = i; mossAt[i] = mossCount++;
  }
  function unplant(i) {
    var j = mossAt[i], lastI = mossList[--mossCount];
    mossList[j] = lastI; mossAt[lastI] = j; mossAt[i] = -1;
    born[i] = -1; cleared[i] = 1;
  }
  // how likely a spore landing on this pixel is to take root: none on dry ground, all on damp
  function takes(i) { return Math.max(0, Math.min(1, (habitat[i] - HABITAT) / HABITAT_SOFT)); }

  // Now and then a spore lands somewhere new, on seen ground damp enough to hold it (between rows
  // y0 and y1 when given).
  function seed(now, y0, y1, tuft) {
    if (y0 === undefined) { y0 = 0; y1 = H; }
    for (var k = 0; k < 60; k++) {
      var x = (Math.random() * W) | 0, y = y0 + ((Math.random() * (y1 - y0)) | 0), i = y * W + x;
      if (wokeAt[y] < 0 || inClearing(x, y) || born[i] >= 0 || habitat[i] < HABITAT + HABITAT_SOFT) continue;
      plant(x, y, now);
      // a spore landing on newly seen ground starts as a small tuft, so it shows straight away
      if (tuft) {
        for (var dy = -1; dy <= 1; dy++) {
          for (var dx = -1; dx <= 1; dx++) {
            var tx = x + dx, ty = y + dy;
            if (tx >= 0 && ty >= 0 && tx < W && ty < H && Math.random() < 0.6 && !inClearing(tx, ty) && born[ty * W + tx] < 0) plant(tx, ty, now);
          }
        }
      }
      return;
    }
  }

  // One spore from a moss pixel: a lognormal distance in a uniform direction. It takes root with
  // the landing ground's habitat chance; ground the cursor cleared always takes moss back.
  function disperse(x, y, now) {
    var d = sporeDistance(), a = Math.random() * 2 * Math.PI;
    var tx = Math.round(x + Math.cos(a) * d), ty = Math.round(y + Math.sin(a) * d);
    if (tx < 0 || ty < 0 || tx >= W || ty >= H) return;
    var t = ty * W + tx;
    if (born[t] >= 0 || wokeAt[ty] < 0 || inClearing(tx, ty)) return;
    if (cleared[t] || Math.random() < takes(t)) plant(tx, ty, now);
  }

  // Rows wake the first time they come into view. Each newly woken stretch gets its share of
  // spores (START_SEEDS per screenful), so growth starts there while the visitor is looking.
  function wake(now) {
    var top = Math.max(0, Math.floor(window.scrollY / P)), bottom = Math.min(H, Math.ceil((window.scrollY + innerHeight) / P));
    var first = -1, last = -1;
    for (var y = top; y < bottom; y++) {
      if (wokeAt[y] >= 0) continue;
      wokeAt[y] = now; awakeRows++;
      if (first < 0) first = y;
      last = y;
    }
    if (first < 0) return;
    seedDebt += (top === 0 && first === 0 ? START_SEEDS : WAKE_SEEDS) * (last - first + 1) / Math.max(1, innerHeight / P);
    for (; seedDebt >= 1; seedDebt--) seed(now, first, last + 1, true);
  }
  function screensSeen() { return Math.max(1, awakeRows / Math.max(1, innerHeight / P)); }

  function grow(now, dt) {
    if (now >= nextSeed) { seed(now); nextSeed = now + weibull(SEED_K, SEED_LAMBDA / screensSeen()); }
    releaseDebt = Math.min(MAX_RELEASES, releaseDebt + mossCount * RELEASE_RATE * dt);
    for (; releaseDebt >= 1; releaseDebt--) {
      var i = mossList[(Math.random() * mossCount) | 0];
      disperse(i % W, (i / W) | 0, now);
    }
  }

  // ---- creepers --------------------------------------------------------------------

  // Each creeper follows one edge, drifting 1 to 4 pixels from it, with leaves at uneven spacing
  // (mostly toward the page) and the odd curled tendril. It stops short of the text.
  function layVines() {
    var below = H - heroH;
    var specs = [
      { from: 'top-left', len: 0.38 * W }, { from: 'top-right', len: 0.24 * W },
      { from: 'left-bottom', len: 0.45 * heroH }, { from: 'right-top', len: 0.3 * heroH },
      // down the page edges, beside the content
      { from: 'left-page', at: heroH + 6, len: Math.min(0.4 * below, 220) },
      { from: 'right-page', at: heroH + 30, len: Math.min(0.3 * below, 160) }
    ];
    vines = specs.map(function (s, n) {
      var horizontal = s.from.indexOf('top') === 0, L = Math.max(0, Math.round(s.len));
      var along = s.from === 'top-left' ? [1, 0] : s.from === 'top-right' ? [-1, 0] : s.from === 'left-bottom' ? [0, -1] : [0, 1];
      var inward = horizontal ? [0, 1] : s.from.indexOf('left') === 0 ? [1, 0] : [-1, 0];
      var pts = [], marks = [], lastLeaf = -9;
      for (var i = 0; i < L; i++) {
        var off = 1 + Math.round(noise(i / 9, n * 7 + 3) * 3);
        var base = s.from === 'top-left' ? [i, 0] : s.from === 'top-right' ? [W - 1 - i, 0]
          : s.from === 'left-bottom' ? [0, Math.floor(heroH) - 1 - i] : s.from === 'right-top' ? [W - 1, i]
          : s.from === 'left-page' ? [0, Math.floor(s.at) + i] : [W - 1, Math.floor(s.at) + i];
        if (base[1] >= H) break;
        var p = [base[0] + inward[0] * off, base[1] + inward[1] * off];
        if (inClearing(p[0], p[1])) break;
        pts.push(p);
        if (i - lastLeaf >= 3 && hash(i, n, 17) < 0.45) {
          lastLeaf = i;
          marks.push({ i: i, kind: hash(i, n, 19) < 0.5 ? 'leaf' : 'small', side: off >= 3 && hash(i, n, 23) < 0.3 ? -1 : 1, fold: 0, from: 0, until: 0 });
        } else if (i > 8 && hash(i, n, 21) < 0.04) {
          marks.push({ i: i, kind: 'tendril', side: 1, fold: 0, from: 0, until: 0 });
        }
      }
      var old = vines[n];
      if (old) marks.forEach(function (m) { if (m.i < old.g) m.seen = -99; });   // already grown: fully open
      return { pts: pts, along: along, inward: inward, marks: marks, g: old ? Math.min(old.g, pts.length) : 0,
               target: old ? Math.min(old.target, pts.length) : 0, start: old ? old.start : Infinity, rest: old ? old.rest : 0,
               turn: along[0] * inward[1] - along[1] * inward[0],   // which way is "toward the page" when it coils
               coil: { k: 0, c: 0, until: 0 } };
    });
  }
  // Touching a creeper folds its leaves in a wave that spreads out from the touch, like a
  // touch-me-not; they stay shut for a few seconds and then open again.
  function touchVine(v, k, now) {
    v.marks.forEach(function (m) {
      var d = Math.abs(m.i - k);
      if (d > FOLD_REACH || m.i >= v.g) return;
      var from = now + d * FOLD_WAVE;
      if (now < m.until && m.from <= from) { m.until = Math.max(m.until, from + FOLD_S + SHUT_S); return; }
      m.from = from;
      m.until = from + FOLD_S + SHUT_S;
    });
  }
  // A click rolls the creeper up from that point to its tip, like a tendril; it unrolls later.
  function coilVine(v, k, now) {
    if (v.coil.c > 0 && now < v.coil.until) k = Math.min(k, v.coil.k);
    v.coil.k = k;
    v.coil.until = now + COIL_S + COILED_S;
  }
  // Creepers wait until a couple of ferns are up, then start one by one. Each grows in spurts:
  // a few pixels that ease out and settle, then a rest. New leaves start as buds and open in turn.
  var vinesAt = null;
  function tendVines(now, dt) {
    if (vinesAt === null && (ferns.filter(function (f) { return f.g >= 1; }).length >= VINE_AFTER || now - startedAt > VINE_ANYWAY)) {
      vinesAt = now + VINE_DELAY;
      vines.forEach(function (v, n) { v.start = vinesAt + n * 3 + Math.random() * 3; });
    }
    vines.forEach(function (v) {
      v.coil.c = now < v.coil.until ? Math.min(1, v.coil.c + dt / COIL_S) : Math.max(0, v.coil.c - dt / UNCOIL_S);
      var woke = v.pts.length ? wokeAt[v.pts[0][1]] : -1;
      // a creeper down the page waits until its stretch has been seen for a while
      if (!v.coil.c && now >= v.start && woke >= 0 && now >= woke + VINE_DELAY) {
        if (now >= v.rest && v.target - v.g < 0.05 && v.target < v.pts.length) {
          v.target = Math.min(v.pts.length, v.target + SPURT_MIN + Math.random() * (SPURT_MAX - SPURT_MIN));
          v.rest = now + REST_MIN + Math.random() * (REST_MAX - REST_MIN);
        }
        v.g += (v.target - v.g) * Math.min(1, dt * SPURT_EASE);
      }
      v.marks.forEach(function (m) {
        if (m.seen === undefined && m.i < v.g - 1) m.seen = now;
        if (now >= m.from && now < m.until) m.fold = Math.min(1, m.fold + dt / FOLD_S);
        else if (now >= m.until) m.fold = Math.max(0, m.fold - dt / OPEN_S);
      });
    });
  }

  // ---- the cursor erases -------------------------------------------------------------

  function clearPath(a, b, now) {
    var len = Math.hypot(b.x - a.x, b.y - a.y), steps = Math.max(1, Math.ceil(len / 0.5)), r = Math.ceil(BRUSH);
    for (var s = 0; s <= steps; s++) {
      var px = a.x + (b.x - a.x) * s / steps, py = a.y + (b.y - a.y) * s / steps;
      for (var dy = -r; dy <= r; dy++) {
        for (var dx = -r; dx <= r; dx++) {
          if (dx * dx + dy * dy > BRUSH * BRUSH) continue;
          var x = Math.round(px + dx), y = Math.round(py + dy);
          if (x < 0 || y < 0 || x >= W || y >= H) continue;
          var i = y * W + x;
          if (born[i] >= 0) unplant(i);
        }
      }
      ferns.forEach(function (f) {
        if (f.curling) return;
        // a fern's body sits roughly in a circle above its base
        var bx = f.x + Math.cos(f.ang) * f.len * 0.45, by = f.y + Math.sin(f.ang) * f.len * 0.45;
        if (Math.hypot(px - bx, py - by) < f.len * 0.5) f.curling = true;
      });
      vines.forEach(function (v) {
        for (var k = 0; k < v.g; k++) {
          if (Math.hypot(v.pts[k][0] - px, v.pts[k][1] - py) <= BRUSH + 2) { touchVine(v, k, now); break; }
        }
      });
    }
  }

  function onPointer(e) {
    if (e.type === 'pointerdown') cursor = null;
    var r = canvas.getBoundingClientRect();
    var p = { x: (e.clientX - r.left) / P, y: (e.clientY - r.top) / P };
    if (p.x < 0 || p.y < 0 || p.x > W || p.y > H) { cursor = null; return; }
    if (e.type === 'pointerdown') {
      vines.forEach(function (v) {
        for (var k = 0; k < v.g; k++) {
          if (Math.hypot(v.pts[k][0] - p.x, v.pts[k][1] - p.y) <= 3.5) { coilVine(v, k, performance.now() / 1000); break; }
        }
      });
    }
    if (cursor && Math.hypot(p.x - cursor.x, p.y - cursor.y) >= 0.5) clearPath(cursor, p, performance.now() / 1000);
    cursor = p;
  }

  // ---- ferns -------------------------------------------------------------------------

  // Look for settled moss away from the text. Ferns spread from shared roots, so most searches
  // start next to a fern that's already up, which lets them gather in loose groups. Each site
  // found waits a Weibull time; if its moss is disturbed before then, the fern never comes.
  function scout(now) {
    if (ferns.length + pending.length >= MAX_FERNS || !mossCount) return;
    for (var k = 0; k < 40; k++) {
      var i, x, y;
      if (ferns.length && Math.random() < KIN) {
        var kin = ferns[(Math.random() * ferns.length) | 0], r = 9 + Math.random() * 9, a = Math.random() * 2 * Math.PI;
        x = Math.round(kin.x + Math.cos(a) * r); y = Math.round(kin.y + Math.sin(a) * r * 0.6);
        if (x < 1 || y < 1 || x >= W - 1 || y >= H - 1) continue;
        i = y * W + x;
      } else {
        i = mossList[(Math.random() * mossCount) | 0]; x = i % W; y = (i / W) | 0;
      }
      if (born[i] < 0 || now - born[i] < MATURE) continue;
      var len = 14 + Math.random() * 10, ok = y > 6;
      for (var dy = -1; dy <= 1 && ok; dy++) {
        for (var dx = -1; dx <= 1 && ok; dx++) ok = isMoss(x + dx, y + dy) && now - born[(y + dy) * W + x + dx] >= MATURE / 2;
      }
      if (!ok) continue;
      // a fern can lean its full length to either side: keep all of that reach on growing ground
      if (inClearing(x - len, y - len * 0.5) || inClearing(x + len, y - len * 0.5) || inClearing(x, y - len) ||
          inClearing(x - len, y) || inClearing(x + len, y)) continue;
      var all = ferns.concat(pending), near = 0;
      if (all.some(function (f) { var d = Math.hypot(f.x - x, f.y - y); if (d < GROUP_R) near++; return d < FERN_GAP; })) continue;
      if (near >= GROUP - 1) continue;   // groups stay small
      pending.push({ i: i, born: born[i], x: x, y: y, len: len, due: now + weibull(FERN_K, FERN_LAMBDA) });
      return;
    }
  }

  function tendFerns(now, dt) {
    if (now >= nextScout) { nextScout = now + 0.2; scout(now); }
    pending = pending.filter(function (p) {
      if (p.i >= born.length || born[p.i] !== p.born) return false;
      if (now < p.due) return true;
      // lean anywhere from upright to well over to one side; the further over, the more it arches
      var lean = (Math.random() - 0.5) * 2.4;
      ferns.push({
        x: p.x + 0.5, y: p.y + 0.5, ang: -Math.PI / 2 + lean, len: p.len,
        bend: 0.2 + Math.abs(lean) * 0.9, sign: lean >= 0 ? 1 : -1, g: 0, curling: false
      });
      return false;
    });
    ferns.forEach(function (f) { f.g = f.curling ? f.g - dt / CURL_S : Math.min(1, f.g + dt / GROW_S); });
    ferns = ferns.filter(function (f) { return f.g > 0; });
  }

  // ---- drawing -------------------------------------------------------------------------

  function plot(x, y, c) {
    var ix = x | 0, iy = y | 0;
    if (ix >= 0 && iy >= 0 && ix < W && iy < H) buf[iy * W + ix] = c;
  }

  // One frond: a stem that unfurls from a fiddlehead, with paired leaflets that unfurl in turn
  // once the stem has passed them. Running g backwards curls it up again.
  function frond(x, y, ang, L, g, depth, sign, f) {
    if (g <= 0 || L < 1.5) return;
    var cur = L * g, tipR = L * (depth === 0 ? 0.14 : 0.25);
    var curlAmp = (Math.PI * (depth === 0 ? 2.2 : 1.2) * (1 - g)) / tipR;
    var bend = depth === 0 ? sign * f.bend / L : sign * 0.25 / L;
    var spacing = depth === 0 ? Math.max(3, L * 0.13) : 1.6;   // room between leaflets keeps each one readable
    var nextLeaf = depth === 0 ? L * 0.12 : 1.2;
    var px = x, py = y, a = ang;
    for (var s = 0; s < cur; s += 0.5) {
      var d = cur - s;
      a += (bend + sign * curlAmp * Math.exp(-d / tipR)) * 0.5;
      px += Math.cos(a) * 0.5;
      py += Math.sin(a) * 0.5;
      plot(px, py, d < 2 ? C['fern-tip'] : depth === 0 ? C['fern-stem'] : C['fern-leaf']);
      if (s >= nextLeaf) {
        nextLeaf += spacing;
        if (depth === 0) {
          // leaflets longest a third of the way up, tapering to the tip
          var u = s / L, childL = L * 0.27 * Math.sin(Math.PI * Math.min(1, u * 0.85 + 0.12)) + 1;
          var childG = Math.min(1, (cur - s) / (childL * 2)), sweep = 1.15 - u * 0.4;
          frond(px, py, a + sweep, childL, childG, 1, -1, f);
          frond(px, py, a - sweep, childL, childG, 1, 1, f);
        }
      }
    }
  }

  // creeper leaves in the stem's own frame: [along the stem, away from the edge, colour].
  // A folding leaf draws as its half-closed shape, then as a closed leaf pressed to the stem.
  var LEAF = {
    leaf: [[0, 1, 'vine-leaf'], [1, 1, 'vine-leaf'], [1, 2, 'vine-leaf'], [2, 2, 'vine-leaf-2']],
    small: [[0, 1, 'vine-leaf'], [1, 2, 'vine-leaf-2']],
    tendril: [[0, 1, 'vine'], [0, 2, 'vine'], [1, 3, 'vine'], [2, 3, 'vine'], [2, 2, 'vine']]
  };
  var HALF = { leaf: [[0, 1, 'vine-leaf'], [1, 1, 'vine-leaf'], [2, 1, 'vine-leaf-2']], small: [[0, 1, 'vine-leaf'], [1, 1, 'vine-leaf-2']], tendril: [[0, 1, 'vine'], [1, 1, 'vine']] };
  var SHUT = { leaf: [[1, 0, 'vine-leaf'], [2, 0, 'vine-leaf']], small: [[1, 0, 'vine-leaf']], tendril: [[0, 1, 'vine']] };
  var BUD = { leaf: [[0, 1, 'vine-leaf-2']], small: [[0, 1, 'vine-leaf-2']], tendril: [[0, 1, 'vine']] };

  // Moss is a pale wash, dithered at its edges, with star-shaped sprigs over the settled middle.
  // Only the rows on screen are drawn (all of them when `whole` is set).
  function draw(now, whole) {
    var top = whole ? 0 : Math.max(0, Math.floor(window.scrollY / P) - 2);
    var bottom = whole ? H : Math.min(H, Math.ceil((window.scrollY + innerHeight) / P) + 2);
    if (bottom <= top) return;
    buf.fill(0, top * W, bottom * W);
    var x, y, i;
    for (y = top; y < bottom; y++) {
      for (x = 0; x < W; x++) {
        i = y * W + x;
        if (born[i] < 0) continue;
        var n = (x > 0 && born[i - 1] >= 0) + (x < W - 1 && born[i + 1] >= 0) + (y > 0 && born[i - W] >= 0) + (y < H - 1 && born[i + W] >= 0);
        if (n < 4 && (x + y) % 2) continue;
        buf[i] = noise(x / 4, y / 3) > 0.55 ? C['wash-1'] : C['wash-0'];
      }
    }
    for (y = Math.max(1, top); y < Math.min(H - 1, bottom); y++) {
      for (x = 1; x < W - 1; x++) {
        i = y * W + x;
        if (born[i] < 0 || now - born[i] < SPROUT) continue;
        if (born[i - 1] < 0 || born[i + 1] < 0 || born[i - W] < 0 || born[i + W] < 0) continue;
        var h = hash(x, y, 11);
        if (h < 0.1) {
          buf[i] = C.sprig;
          buf[i - 1] = C['sprig-arm']; buf[i + 1] = C['sprig-arm']; buf[i - W] = C['sprig-arm'];
          if (h < 0.05) buf[i + W] = C['sprig-arm'];
        } else if (h < 0.14) {
          buf[i] = C['sprig-dot'];
        }
      }
    }
    vines.forEach(function (v) {
      var g = Math.floor(v.g), c = v.coil.c, from = c > 0 ? Math.min(v.coil.k, g) : g;
      for (var k = 0; k < from; k++) plot(v.pts[k][0], v.pts[k][1], C.vine);
      if (c > 0 && from < g) {
        // past the click the stem bends ever more tightly toward the page, rolling into a coil;
        // c blends each pixel between where it grew and where the coil puts it
        // about two open turns show; the rest of the stem is tucked inside the coil
        var x = v.pts[from][0], y = v.pts[from][1], a = Math.atan2(v.along[1], v.along[0]);
        for (var j = from; j < g; j++) {
          var t = j - from;
          if (t < 30) {
            a += v.turn * (0.2 + 0.012 * t);
            x += Math.cos(a); y += Math.sin(a);
          }
          plot(Math.round(v.pts[j][0] + (x - v.pts[j][0]) * c), Math.round(v.pts[j][1] + (y - v.pts[j][1]) * c), C.vine);
        }
      }
      v.marks.forEach(function (m) {
        if (m.i >= g - 1 || (c > 0.2 && m.i >= from)) return;   // leaves on the coiled part are tucked away
        var p = v.pts[m.i];
        var age = m.seen === undefined ? 0 : now - m.seen;
        var shape = m.fold > 0.66 ? SHUT : m.fold > 0.2 ? HALF : age < BUD_S ? BUD : age < BUD_S + UNFURL_S ? HALF : LEAF;
        shape[m.kind].forEach(function (o) {
          plot(p[0] + v.along[0] * o[0] + v.inward[0] * o[1] * m.side, p[1] + v.along[1] * o[0] + v.inward[1] * o[1] * m.side, C[o[2]]);
        });
      });
      if (g > 2 && !c) {   // the growing tip curls toward the page
        var t = v.pts[g - 1];
        plot(t[0] + v.inward[0], t[1] + v.inward[1], C.vine);
        plot(t[0] + v.inward[0] - v.along[0], t[1] + v.inward[1] - v.along[1], C['vine-leaf-2']);
      }
    });
    ferns.forEach(function (f) { frond(f.x, f.y, f.ang, f.len, 1 - Math.pow(1 - f.g, 2.2), 0, f.sign, f); });
    ctx.putImageData(img, 0, 0, 0, top, W, bottom - top);
  }

  // ---- loop ----------------------------------------------------------------------------

  function step(now, dt) {
    if (!started) {
      started = true; startedAt = now;
      nextSeed = now + weibull(SEED_K, SEED_LAMBDA);
    }
    wake(now);
    grow(now, dt);
    tendVines(now, dt);
    tendFerns(now, dt);
  }

  var last = performance.now() / 1000;
  function frame(ms) {
    var now = ms / 1000, dt = Math.min(0.05, Math.max(0, now - last));
    last = now;
    step(now, dt);
    draw(now);
    requestAnimationFrame(frame);
  }

  readColors();
  resize();
  // the theme toggle changes data-theme on <html>; pick up the new colours when it does
  new MutationObserver(function () { readColors(); draw(reduceMotion ? STILL_SECONDS : last, reduceMotion); })
    .observe(root, { attributes: true, attributeFilter: ['data-theme'] });
  // the page changes height as fonts load and on resize
  var queued = false;
  function refit() {
    if (queued) return;
    queued = true;
    setTimeout(function () { queued = false; resize(); if (reduceMotion) draw(STILL_SECONDS, true); }, 100);
  }
  addEventListener('resize', refit);
  if ('ResizeObserver' in window) new ResizeObserver(refit).observe(main);

  if (reduceMotion) {
    // no motion: grow a settled garden in one go and draw it once
    wokeAt.fill(0); awakeRows = H;
    for (var s0 = 0; s0 < START_SEEDS * H / Math.max(1, innerHeight / P); s0++) seed(0);
    for (var t = 0; t < STILL_SECONDS; t += 0.05) step(t, 0.05);
    ferns.forEach(function (f) { f.g = 1; });
    vines.forEach(function (v) { v.g = v.target = v.pts.length; v.marks.forEach(function (m) { m.seen = -99; }); });
    draw(STILL_SECONDS, true);
  } else {
    addEventListener('pointermove', onPointer, { passive: true });
    addEventListener('pointerdown', onPointer, { passive: true });
    root.addEventListener('pointerleave', function () { cursor = null; });
    // scrolling moves the page under a still cursor; that isn't a swipe, so start afresh
    addEventListener('scroll', function () { cursor = null; }, { passive: true });
    requestAnimationFrame(frame);
  }
})();
