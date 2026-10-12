/* The river from dogaozden.com, as a page background: a fixed stone bed under a flowing surface with rain and
   cursor ripples. The water shader is the site's (pool.js) with the fish, crabs and engraved quote removed.
   Usage: <canvas id="river"></canvas> plus <script src="river/river.js" data-beds="river/"></script>.
   Knobs live in a "Tune water" panel; choices are saved in this browser only. */
(() => {
  const script = document.currentScript;
  // data-beds is a folder relative to the page (like any src attribute), not to this script.
  const base = new URL(script?.dataset.beds || 'river/', document.baseURI);
  const STORE = 'haiku-frontier-river-v4';
  const BEDS = { original: 'Original', slate: 'Slate', shingle: 'Shingle', sandbar: 'Sandbar' };
  // The live site's launch values (RIVER_LAUNCH.water), but darker by default (Doga asked), plus a page-tint knob.
  const DEFAULTS = { speed: 1, direction: 1, turbulence: 1.2, refraction: 1, rainRate: 0.7, rainStrength: 0.45, pointerStrength: 0.5, brightness: 0.12, tint: 0.78, bed: 'original' };
  const BOUNDS = { speed: [0, 3], direction: [-1, 1], turbulence: [0, 2.5], refraction: [0, 2], rainRate: [0, 6], rainStrength: [0, 4], pointerStrength: [0, 4], brightness: [0.05, 1.8], tint: [0.3, 0.97] };
  const settings = { ...DEFAULTS };
  function apply(values) {
    for (const [key, value] of Object.entries(values || {})) {
      if (key === 'bed') { if (Object.hasOwn(BEDS, value)) settings.bed = value; continue; }
      if (!Object.hasOwn(BOUNDS, key) || typeof value !== 'number' || !Number.isFinite(value)) continue;
      settings[key] = key === 'direction' ? (value < 0 ? -1 : 1) : Math.max(BOUNDS[key][0], Math.min(BOUNDS[key][1], value));
    }
    document.documentElement.style.setProperty('--river-tint', settings.tint);
  }
  try { apply(JSON.parse(localStorage.getItem(STORE))); } catch { apply({}); }
  const save = () => { try { localStorage.setItem(STORE, JSON.stringify(settings)); } catch {} };

  const canvas = document.getElementById('river');
  if (!canvas) return;
  const reduced = matchMedia('(prefers-reduced-motion: reduce)');
  let gl = null;
  for (const powerPreference of ['high-performance', 'default']) {
    try { gl = canvas.getContext('webgl', { alpha: false, antialias: false, powerPreference }); } catch {}
    if (gl) break;
  }

  const vertex = 'attribute vec2 position; void main(){gl_Position=vec4(position,0.,1.);}';
  const fragment = `precision highp float;
    uniform vec2 resolution;
    uniform float time, imageAspect, flowOffset, turbulence, refraction, brightness;
    uniform sampler2D stones;
    uniform vec4 drops[32];
    float hash(vec2 p){return fract(sin(dot(p,vec2(127.1,311.7)))*43758.5453);}
    float noise(vec2 p){
      vec2 i=floor(p),f=fract(p);f=f*f*(3.-2.*f);
      return mix(mix(hash(i),hash(i+vec2(1.,0.)),f.x),mix(hash(i+vec2(0.,1.)),hash(i+vec2(1.,1.)),f.x),f.y);
    }
    float current(vec2 p){
      // Surface features travel downstream; the photographed riverbed stays fixed.
      vec2 q=p-vec2(flowOffset,0.);
      vec2 warp=vec2(noise(q*3.7),noise(q*3.7+17.))*1.2;
      return .007*noise(q*8.+warp)+.0028*noise(q*18.+warp*2.)+.0007*noise(q*39.+warp);
    }
    vec2 gradient(vec2 p){
      float e=.004;
      vec2 slope=vec2(current(p+vec2(e,0.))-current(p-vec2(e,0.)),current(p+vec2(0.,e))-current(p-vec2(0.,e)))/(2.*e)*turbulence;
      for(int i=0;i<32;i++){
        float age=time-drops[i].z;
        if(age>0. && age<7.){
          vec2 delta=p-drops[i].xy;float d=length(delta),front=age*.19;
          float width=.035+age*.018,envelope=exp(-pow((d-front)/width,2.));
          float phase=(d-front)*115.;
          float derivative=115.*cos(phase)-sin(phase)*2.*(d-front)/(width*width);
          slope+=delta/max(d,.0001)*derivative*envelope*exp(-age*.52)*drops[i].w;
        }
      }
      return slope;
    }
    void main(){
      vec2 uv=gl_FragCoord.xy/resolution;
      float aspect=resolution.x/resolution.y;
      vec2 p=(uv-.5)*vec2(aspect,1.);
      vec2 slope=gradient(p);
      vec2 cover=aspect>imageAspect?vec2(1.,imageAspect/aspect):vec2(aspect/imageAspect,1.);
      vec2 bedUV=uv+slope*vec2(1./aspect,1.)*.16*refraction;
      vec2 refracted=(bedUV-.5)*cover+.5;
      vec3 bed=texture2D(stones,clamp(refracted,vec2(.001),vec2(.999))).rgb;
      float light=exp(-length((p-vec2(.20,.12))*vec2(.8,1.2))*1.7);
      vec3 normal=normalize(vec3(-slope*2.5,1.));
      float glint=pow(max(0.,dot(normal,normalize(vec3(.14,.21,1.)))),80.);
      vec3 color=bed*vec3(.51,.60,.64)*(.68+light*.42);
      color+=vec3(.32,.43,.46)*glint*.25;
      color+=vec3(.35,.43,.45)*min(length(slope),.5)*(.025+light*.18);
      color*=1.-.35*smoothstep(.15,.85,length((uv-.5)*vec2(1.,.8)));
      gl_FragColor=vec4(color*brightness,1.);
    }`;

  let program = null, uniforms = {}, texture = null, ready = false, imageAspect = 1.5;
  function compile(type, source) {
    const shader = gl.createShader(type); gl.shaderSource(shader, source); gl.compileShader(shader);
    if (!gl.getShaderParameter(shader, gl.COMPILE_STATUS)) throw Error(gl.getShaderInfoLog(shader));
    return shader;
  }
  function initGraphics() {
    if (!gl) return false;
    try {
      program = gl.createProgram();
      gl.attachShader(program, compile(gl.VERTEX_SHADER, vertex));
      gl.attachShader(program, compile(gl.FRAGMENT_SHADER, fragment));
      gl.linkProgram(program);
      if (!gl.getProgramParameter(program, gl.LINK_STATUS)) throw Error(gl.getProgramInfoLog(program));
      gl.useProgram(program);
      const buffer = gl.createBuffer(); gl.bindBuffer(gl.ARRAY_BUFFER, buffer);
      gl.bufferData(gl.ARRAY_BUFFER, new Float32Array([-1, -1, 1, -1, -1, 1, 1, 1]), gl.STATIC_DRAW);
      const position = gl.getAttribLocation(program, 'position');
      gl.enableVertexAttribArray(position); gl.vertexAttribPointer(position, 2, gl.FLOAT, false, 0, 0);
      uniforms = Object.fromEntries(['resolution', 'time', 'imageAspect', 'flowOffset', 'turbulence', 'refraction', 'brightness', 'drops[0]']
        .map((name) => [name, gl.getUniformLocation(program, name)]));
      texture = gl.createTexture(); gl.activeTexture(gl.TEXTURE0); gl.bindTexture(gl.TEXTURE_2D, texture);
      for (const [k, v] of [[gl.TEXTURE_MIN_FILTER, gl.LINEAR], [gl.TEXTURE_MAG_FILTER, gl.LINEAR], [gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE], [gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE]]) gl.texParameteri(gl.TEXTURE_2D, k, v);
      gl.uniform1i(gl.getUniformLocation(program, 'stones'), 0);
      return true;
    } catch (error) { console.warn('[river] WebGL unavailable:', error); return false; }
  }
  let webgl = initGraphics();
  if (!webgl) document.documentElement.classList.add('river-static');

  // Riverbed photos load one at a time; the last good one stays until a new one arrives.
  let bedImage = null, bedTicket = 0;
  function loadBed(id) {
    const ticket = ++bedTicket, image = new Image();
    image.onload = () => {
      if (ticket !== bedTicket) return;
      bedImage = image; imageAspect = image.width / image.height;
      document.documentElement.style.setProperty('--river-bed', `url("${image.src}")`);
      if (webgl) {
        gl.activeTexture(gl.TEXTURE0); gl.bindTexture(gl.TEXTURE_2D, texture);
        gl.pixelStorei(gl.UNPACK_FLIP_Y_WEBGL, true);
        gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, gl.RGBA, gl.UNSIGNED_BYTE, image);
      }
      ready = true; canvas.classList.add('ready'); draw();
    };
    image.onerror = () => { if (ticket === bedTicket) console.warn('[river] riverbed failed to load:', id); };
    image.src = new URL(`${id}.jpg`, base).href;
  }

  const drops = new Float32Array(128);
  for (let i = 0; i < 32; i++) drops[i * 4 + 2] = -100;
  let tick = 2, index = 0, lastFrame = 0, rain = 0, lastMove = 0, flowOffset = 0, lastDraw = 0, lastDrop = -100;
  const drop = (x, y, strength) => { drops.set([x, y, tick, strength], (index++ % 32) * 4); lastDrop = tick; };

  function resize() {
    const w = innerWidth, h = innerHeight;
    // Same idea as the site's performance profile: cap device pixels so a big screen stays smooth.
    const ratio = Math.min(devicePixelRatio || 1, 1.5, Math.sqrt(1100000 / Math.max(1, w * h)));
    canvas.width = Math.max(1, Math.round(w * ratio)); canvas.height = Math.max(1, Math.round(h * ratio));
    if (webgl) gl.viewport(0, 0, canvas.width, canvas.height);
    draw();
  }
  function draw() {
    if (!webgl || !ready) return;
    gl.uniform2f(uniforms.resolution, canvas.width, canvas.height);
    gl.uniform1f(uniforms.time, tick);
    gl.uniform1f(uniforms.imageAspect, imageAspect);
    gl.uniform1f(uniforms.flowOffset, flowOffset);
    gl.uniform1f(uniforms.turbulence, settings.turbulence);
    gl.uniform1f(uniforms.refraction, settings.refraction);
    gl.uniform1f(uniforms.brightness, settings.brightness);
    gl.uniform4fv(uniforms['drops[0]'], drops);
    gl.drawArrays(gl.TRIANGLE_STRIP, 0, 4);
  }
  function pointer(event, strong) {
    if (!ready || settings.pointerStrength <= 0) return;
    const x = event.clientX / innerWidth, y = 1 - event.clientY / innerHeight, aspect = innerWidth / innerHeight;
    if (strong || tick - lastMove > 0.07) { drop((x - 0.5) * aspect, y - 0.5, (strong ? 0.009 : 0.0015) * settings.pointerStrength); lastMove = tick; }
  }
  addEventListener('pointermove', (e) => pointer(e, false), { passive: true });
  addEventListener('pointerdown', (e) => pointer(e, true), { passive: true });

  function frame(now) {
    requestAnimationFrame(frame);
    const dt = lastFrame ? Math.min(Math.max(0, (now - lastFrame) / 1000), 0.05) : 0; lastFrame = now;
    if (!ready || document.hidden) return;
    const still = reduced.matches;
    // With reduced motion the current and rain stop; ripples you make yourself still play out and settle.
    if (still && tick - lastDrop > 7) return;
    tick += dt;
    if (!still) {
      const travel = 0.058 * settings.speed * settings.direction * dt;
      flowOffset += travel;
      for (let i = 0; i < 32; i++) drops[i * 4] += travel;
      if (settings.rainRate > 0) {
        rain += dt * settings.rainRate;
        while (rain >= 1) { drop((Math.random() - 0.5) * canvas.width / canvas.height, (Math.random() - 0.5) * 0.95, (0.0008 + Math.random() * 0.0006) * settings.rainStrength); rain -= 1; }
      } else rain = 0;
    }
    if (now - lastDraw >= 1000 / 30 - 1) { draw(); lastDraw = now; }
  }
  document.addEventListener('visibilitychange', () => { lastFrame = 0; });
  canvas.addEventListener('webglcontextlost', (e) => { e.preventDefault(); webgl = false; ready = false; document.documentElement.classList.add('river-static'); });
  canvas.addEventListener('webglcontextrestored', () => {
    webgl = initGraphics();
    if (webgl) { document.documentElement.classList.remove('river-static'); loadBed(settings.bed); }
  });
  addEventListener('resize', resize);
  resize(); loadBed(settings.bed); requestAnimationFrame(frame);

  /* ---------- the knobs ---------- */
  const css = `
  .rv-controls{position:fixed;right:16px;bottom:16px;z-index:30;font:12px/1.4 var(--font-body,system-ui,sans-serif);color:#dfe7e7;max-width:calc(100vw - 32px)}
  .rv-controls summary{list-style:none;cursor:pointer;width:max-content;padding:10px 15px;border:1px solid #bccbd339;border-radius:8px;background:#0b1419dc;backdrop-filter:blur(18px);-webkit-backdrop-filter:blur(18px);user-select:none}
  .rv-controls summary::-webkit-details-marker{display:none}
  .rv-controls summary span{margin-left:14px;color:#9fb9c2}
  .rv-panel{position:absolute;right:0;bottom:calc(100% + 8px);width:330px;max-width:calc(100vw - 32px);padding:17px;background:#0b1419f2;border:1px solid #bccbd339;border-radius:10px;backdrop-filter:blur(24px);-webkit-backdrop-filter:blur(24px);max-height:calc(100svh - 90px);overflow:auto;overscroll-behavior:contain;display:flex;flex-direction:column;gap:12px}
  .rv-head{display:flex;justify-content:space-between;align-items:baseline;gap:12px}
  .rv-head h2{font:400 22px/1.1 var(--font-display,Georgia,serif);margin:0;color:#eeece5}
  .rv-note{margin:0;color:#9aabb0;font-size:11.5px}
  .rv-panel label{display:grid;grid-template-columns:1fr auto;gap:4px 10px;align-items:center;color:#cbd6d8}
  .rv-panel output{font-family:var(--font-mono,ui-monospace,monospace);color:#9fb9c2;font-size:11px}
  .rv-panel input[type=range]{grid-column:1/-1;width:100%;accent-color:#9fc9d6;margin:0}
  .rv-panel select{grid-column:2;background:#0b1419;color:#dfe7e7;border:1px solid #bccbd339;border-radius:6px;padding:3px 6px;font:inherit}
  .rv-beds{display:grid;grid-template-columns:repeat(4,1fr);gap:6px}
  .rv-beds button{padding:5px 0 6px;border:1px solid #bccbd339;border-radius:7px;background:transparent;color:#cbd6d8;font:inherit;font-size:11px;cursor:pointer;display:flex;flex-direction:column;align-items:center;gap:4px}
  .rv-beds button i{display:block;width:100%;height:30px;border-radius:5px 5px 0 0;background-size:cover;background-position:center;filter:brightness(.75) saturate(.8)}
  .rv-beds button[aria-pressed=true]{border-color:#9fc9d6;color:#fff}
  .rv-row{display:flex;gap:8px;align-items:center}
  .rv-row button{padding:6px 11px;border:1px solid #bccbd339;border-radius:999px;background:transparent;color:#dfe7e7;font:inherit;cursor:pointer}
  .rv-row button:hover,.rv-beds button:hover{border-color:#9fc9d6}
  .rv-row [role=status]{color:#9fb9c2}`;
  const style = document.createElement('style'); style.textContent = css; document.head.append(style);

  const FIELDS = [
    ['speed', 'Flow speed', 0.05, (v) => `${v.toFixed(2)}\u00D7`],
    ['turbulence', 'Surface movement', 0.05, (v) => `${v.toFixed(2)}\u00D7`],
    ['refraction', 'Water distortion', 0.05, (v) => `${v.toFixed(2)}\u00D7`],
    ['rainRate', 'Rain frequency', 0.1, (v) => `${v.toFixed(1)} / sec`],
    ['rainStrength', 'Drop strength', 0.05, (v) => `${v.toFixed(2)}\u00D7`],
    ['pointerStrength', 'Cursor & tap strength', 0.05, (v) => `${v.toFixed(2)}\u00D7`],
    ['brightness', 'River visibility', 0.05, (v) => `${v.toFixed(2)}\u00D7`],
    ['tint', 'Panel tint over the river', 0.01, (v) => `${Math.round(v * 100)}%`],
  ];
  const details = document.createElement('details'); details.className = 'rv-controls';
  const summary = document.createElement('summary'); summary.innerHTML = 'Tune water <span aria-hidden="true">\u224B</span>';
  const panel = document.createElement('div'); panel.className = 'rv-panel';
  panel.innerHTML = `<div class="rv-head"><h2>Your river</h2></div>
    <p class="rv-note">The water behind this page is the river from dogaozden.com. Changes are saved in this browser.</p>
    <div class="rv-beds" role="group" aria-label="Riverbed"></div>
    <label>Flow direction<select data-key="direction"><option value="1">Left \u2192 right</option><option value="-1">Right \u2192 left</option></select></label>`;
  const beds = panel.querySelector('.rv-beds');
  for (const [id, name] of Object.entries(BEDS)) {
    const b = document.createElement('button'); b.type = 'button'; b.dataset.bed = id;
    const sw = document.createElement('i'); sw.style.backgroundImage = `url("${new URL(`${id}.jpg`, base).href}")`;
    b.append(sw, document.createTextNode(name));
    b.addEventListener('click', () => { apply({ bed: id }); save(); loadBed(id); sync(); });
    beds.append(b);
  }
  for (const [key, label, step] of FIELDS) {
    const l = document.createElement('label'); l.textContent = label;
    const out = document.createElement('output'); out.dataset.key = key;
    const input = document.createElement('input'); input.type = 'range'; input.dataset.key = key;
    input.min = BOUNDS[key][0]; input.max = BOUNDS[key][1]; input.step = step; input.setAttribute('aria-label', label);
    l.append(out, input); panel.append(l);
  }
  const row = document.createElement('div'); row.className = 'rv-row';
  row.innerHTML = '<button type="button" data-act="reset">Reset</button><button type="button" data-act="copy">Copy settings</button><span role="status"></span>';
  panel.append(row);
  details.append(summary, panel); document.body.append(details);
  function sync() {
    for (const el of panel.querySelectorAll('[data-key]')) {
      const key = el.dataset.key, value = settings[key];
      if (el.tagName === 'OUTPUT') el.textContent = FIELDS.find((f) => f[0] === key)[3](value);
      else el.value = String(value);
    }
    for (const b of beds.children) b.setAttribute('aria-pressed', String(b.dataset.bed === settings.bed));
  }
  panel.addEventListener('input', (e) => {
    const key = e.target.dataset?.key; if (!key) return;
    apply({ [key]: Number(e.target.value) }); save(); sync(); draw();
  });
  row.addEventListener('click', async (e) => {
    const act = e.target.dataset?.act, status = row.querySelector('[role=status]');
    if (act === 'reset') { const bed = settings.bed; apply(DEFAULTS); save(); if (bed !== settings.bed) loadBed(settings.bed); sync(); draw(); status.textContent = 'Reset'; }
    if (act === 'copy') {
      try { await navigator.clipboard.writeText(JSON.stringify(settings, null, 2)); status.textContent = 'Copied'; }
      catch { status.textContent = 'Copy blocked'; }
    }
  });
  details.addEventListener('keydown', (e) => { if (e.key === 'Escape') { details.open = false; summary.focus(); } });
  sync();
  window.river = { getSettings: () => ({ ...settings }), setSettings(v) { apply(v); save(); if (v?.bed) loadBed(settings.bed); sync(); draw(); } };
})();
