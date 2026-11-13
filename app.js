(() => {
  "use strict";
  const $ = (id) => document.getElementById(id);
  const COLORS = { "李白": "#6cc0de", "杜甫": "#e2ba77" };
  const data = window.POETIC_FULL_DATA;
  const status = $("chart-status");
  if (!window.echarts || !data || !Array.isArray(data.poems) || !Array.isArray(data.links)) {
    status.textContent = "星图数据未能加载，请检查站点文件是否完整。";
    console.error("星图加载失败：缺少 ECharts 或完整数据脚本");
    return;
  }

  const allPoems = data.poems, allLinks = data.links;
  const poemById = new Map(allPoems.map((poem) => [poem.id, poem]));
  const compareText = (a, b) => a < b ? -1 : a > b ? 1 : 0;
  const corePoems = [...allPoems].sort((a, b) => b.degree - a.degree || compareText(a.poet, b.poet) || compareText(a.id, b.id)).slice(0, 90);
  const coreIds = new Set(corePoems.map((poem) => poem.id));
  const coreLabelIds = new Set(["李白", "杜甫"].flatMap((poet) => corePoems.filter((poem) => poem.poet === poet).slice(0, 2).map((poem) => poem.id)));
  const breathIds = new Set(["李白", "杜甫"].flatMap((poet) => corePoems.filter((poem) => poem.poet === poet).slice(0, 3).map((poem) => poem.id)));
  const coreLinks = allLinks.filter((link) => coreIds.has(link.source) && coreIds.has(link.target));
  const adjacency = new Map(allPoems.map((poem) => [poem.id, []]));
  for (const link of allLinks) { adjacency.get(link.source).push(link); adjacency.get(link.target).push(link); }
  const state = { mode: "core", threshold: 0.7, localId: null, selected: null };
  const blankCurrent = () => ({ nodes: [], links: [], graphNodes: [], graphLinks: [], nodeIndex: new Map(), linkIndex: new Map(), linkById: new Map(), degree: new Map(), pairs: new Map() });
  let current = blankCurrent(), chart, renderToken = 0, sliderTimer, localPositions = new Map();
  let introPlayed = false, fullRevealPending = false, fullRevealTimer;
  const introTimers = [], selectionTimers = [], breathTimers = [], breathEffects = [];
  const motionQuery = window.matchMedia("(prefers-reduced-motion: reduce)");
  const panel = document.querySelector(".detail-panel");
  const search = $("poem-search"), results = $("search-results"), slider = $("threshold");
  const edgeId = (link) => `${link.source}|${link.target}`;
  const clamp = (n, min, max) => Math.max(min, Math.min(max, n));
  const escapeHtml = (value) => String(value).replace(/[&<>"']/g, (char) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" })[char]);
  function halton(index, base) { let f = 1, value = 0; while (index) { f /= base; value += f * (index % base); index = Math.floor(index / base); } return value; }
  function clearTimers(timers) { while (timers.length) clearTimeout(timers.pop()); }
  function stopBreathing() {
    clearTimers(breathTimers);
    while (breathEffects.length) {
      const { parent, halo } = breathEffects.pop();
      halo.stopAnimation(); parent.remove(halo);
    }
  }
  function cancelMotion() {
    clearTimers(introTimers); clearTimers(selectionTimers); stopBreathing();
    clearTimeout(fullRevealTimer); $("network").classList.remove("is-full-revealing");
  }

  // Seed positions come from poem IDs, then real links gently pull related poems together.
  function hashId(id) {
    let hash = 2166136261;
    for (let i = 0; i < id.length; i++) { hash ^= id.charCodeAt(i); hash = Math.imul(hash, 16777619); }
    return hash >>> 0;
  }
  function randomFrom(seed) {
    let value = seed;
    return () => {
      value += 0x6D2B79F5;
      let t = value;
      t = Math.imul(t ^ t >>> 15, t | 1);
      t ^= t + Math.imul(t ^ t >>> 7, t | 61);
      return ((t ^ t >>> 14) >>> 0) / 4294967296;
    };
  }
  const maxDegree = corePoems[0].degree;
  function seedPoint(poem) {
    const random = randomFrom(hashId(poem.id) ^ 0x85EBCA6B);
    const importance = Math.sqrt(poem.degree / maxDegree);
    const prominence = poem.degree / maxDegree;
    const side = poem.poet === "李白" ? -1 : 1;
    const xNoise = random() * 2 - 1;
    const yNoise = (random() + random() + random() - 1.5) / 1.5;
    return { x: 500 + side * (110 - 94 * importance) + xNoise * (335 - 245 * prominence),
      y: 450 + yNoise * (360 - 85 * importance) };
  }
  function relatedPositions(poems, links, core) {
    const seeds = new Map(poems.map((poem) => [poem.id, seedPoint(poem)]));
    const pulls = new Map();
    for (const link of links) {
      const source = seeds.get(link.source), target = seeds.get(link.target);
      if (!source || !target) continue;
      const weight = link.maxSimilarity * (1 + Math.log1p(link.matchCount) * 0.12);
      for (const [id, neighbor] of [[link.source, target], [link.target, source]]) {
        const sum = pulls.get(id) || { x: 0, y: 0, weight: 0 };
        sum.x += neighbor.x * weight; sum.y += neighbor.y * weight; sum.weight += weight;
        pulls.set(id, sum);
      }
    }
    const preferred = new Map();
    for (const poem of poems) {
      const seed = seeds.get(poem.id), pull = pulls.get(poem.id);
      preferred.set(poem.id, pull ? { x: seed.x * 0.84 + pull.x / pull.weight * 0.16,
        y: seed.y * 0.72 + pull.y / pull.weight * 0.28 } : seed);
    }
    if (!core) return preferred;

    // Place prominent poems first, using a small ID-seeded search to avoid collisions.
    const positions = new Map(), placed = [];
    for (const poem of [...poems].sort((a, b) => b.degree - a.degree || compareText(a.id, b.id))) {
      const origin = preferred.get(poem.id), random = randomFrom(hashId(poem.id) ^ 0xC2B2AE35);
      let best = origin, bestClearance = -Infinity;
      for (let attempt = 0; attempt < 96; attempt++) {
        const angle = random() * Math.PI * 2;
        const radius = attempt ? 12 + Math.sqrt(attempt / 95) * 95 : 0;
        const point = attempt ? { x: clamp(origin.x + Math.cos(angle) * radius, 72, 928),
          y: clamp(origin.y + Math.sin(angle) * radius, 75, 825) } : origin;
        const clearance = placed.reduce((min, other) => Math.min(min,
          Math.hypot(point.x - other.x, (point.y - other.y) * 0.74)), Infinity);
        if (clearance > bestClearance) { best = point; bestClearance = clearance; }
        if (clearance >= 31) break;
      }
      positions.set(poem.id, best);
      placed.push(best);
    }
    return positions;
  }
  function makeCorePositions(poems) { return relatedPositions(poems, coreLinks, true); }
  function makeFullPositions(poems) { return relatedPositions(poems, allLinks, false); }
  function makeLocalPositions(id) {
    const positions = new Map(), poem = poemById.get(id), neighborIds = new Set();
    for (const link of adjacency.get(id)) neighborIds.add(link.source === id ? link.target : link.source);
    positions.set(id, { x: poem.poet === "李白" ? 270 : 730, y: 450 });
    [...neighborIds].forEach((neighborId, index) => positions.set(neighborId, {
      x: (poem.poet === "李白" ? 730 : 270) + (halton(index + 1, 2) - 0.5) * 270,
      y: 65 + halton(index + 1, 3) * 770
    }));
    return positions;
  }
  function makeSparsePositions(poems) {
    const positions = new Map();
    for (const poet of ["李白", "杜甫"]) {
      const group = poems.filter((poem) => poem.poet === poet), x = poet === "李白" ? 300 : 700;
      group.forEach((poem, index) => positions.set(poem.id, {
        x: x + (index % 3 - 1) * 28,
        y: group.length === 1 ? 450 : 145 + (index + 0.5) * 610 / group.length
      }));
    }
    return positions;
  }
  const corePositions = makeCorePositions(corePoems), fullPositions = makeFullPositions(allPoems);

  function filterLinks(baseLinks) {
    if (state.threshold <= 0.7) return baseLinks;
    const visible = [];
    for (const link of baseLinks) {
      if (link.maxSimilarity + 1e-9 < state.threshold) continue;
      const matches = link.matches.filter((match) => match.similarity + 1e-9 >= state.threshold);
      if (matches.length) visible.push({ ...link, matches, matchCount: matches.length });
    }
    return visible;
  }
  function visibleNetwork() {
    const base = state.mode === "core" ? coreLinks : state.mode === "local" ? adjacency.get(state.localId) : allLinks;
    const links = filterLinks(base), ids = new Set();
    for (const link of links) { ids.add(link.source); ids.add(link.target); }
    if (state.mode === "local") ids.add(state.localId);
    const poems = (state.mode === "core" ? corePoems : allPoems).filter((poem) => ids.has(poem.id));
    return { poems, links };
  }
  function graphNode(poem, sparsePositions, visibleCount) {
    const full = state.mode === "full", local = state.mode === "local", focus = local && poem.id === state.localId;
    const pos = sparsePositions?.get(poem.id) || (full ? fullPositions.get(poem.id) : local ? localPositions.get(poem.id) : corePositions.get(poem.id));
    const size = full ? visibleCount <= 30 ? clamp(12 + Math.sqrt(poem.degree) * 0.4, 12, 20) : clamp(1.15 + 1.8 * Math.pow(poem.degree / corePoems[0].degree, 0.9), 1.15, 3)
      : local ? focus ? 20 : clamp(4 + Math.sqrt(poem.degree) * 0.45, 5, 11)
      : clamp(4 + 9.5 * Math.pow(poem.degree / corePoems[0].degree, 1.5), 4, 13.5);
    const showLabel = state.mode === "core" && coreLabelIds.has(poem.id);
    return { id: poem.id, name: poem.title, poet: poem.poet, x: pos.x, y: pos.y, symbolSize: size,
      label: showLabel ? { show: true, formatter: poem.title.length > 7 ? `${poem.title.slice(0, 7)}…` : poem.title,
        position: poem.poet === "李白" ? "right" : "left", distance: 9,
        color: poem.poet === "李白" ? "#a1d1df" : "#d8c29c", fontSize: 11, fontFamily: '"Songti SC", serif' } : { show: false },
      itemStyle: { color: COLORS[poem.poet], opacity: full ? 0.56 : 0.92,
        borderColor: poem.poet === "李白" ? "#c5e9f2" : "#f1dfb9",
        borderWidth: !full && size >= 10 ? 0.6 : 0, shadowColor: COLORS[poem.poet], shadowBlur: full ? 0 : size >= 10 ? 6 : 0 } };
  }
  function graphLink(link) {
    const item = { id: edgeId(link), source: link.source, target: link.target, maxSimilarity: link.maxSimilarity, matchCount: link.matchCount };
    if (state.mode !== "full") item.lineStyle = { color: "#b8c6c3", width: link.maxSimilarity >= 0.9 ? 0.65 : 0.4,
      opacity: 0.035 + (link.maxSimilarity - 0.7) / 0.3 * 0.065 };
    return item;
  }
  function installBreathing() {
    if (motionQuery.matches || state.mode !== "core" || state.selected || breathEffects.length) return;
    const series = chart.getModel().getSeriesByIndex(0);
    if (!series || !echarts.graphic?.Circle) return;
    const graphicData = series.getData();
    [...breathIds].forEach((id, phase) => {
      const index = current.nodeIndex.get(id), node = current.graphNodes[index];
      if (index === undefined || !node) return;
      const parent = graphicData.getItemGraphicEl(index);
      if (!parent || typeof parent.add !== "function") return;
      const halo = new echarts.graphic.Circle({ shape: { cx: 0, cy: 0, r: node.symbolSize / 2 + 3 },
        style: { fill: "transparent", stroke: COLORS[node.poet], lineWidth: 1.2, opacity: 0.08,
          shadowBlur: 4, shadowColor: COLORS[node.poet] }, silent: true });
      parent.add(halo);
      breathEffects.push({ parent, halo });
      const period = 3500 + phase % 3 * 400;
      halo.animate("style", true).when(0, { opacity: 0.08 }).when(period / 2, { opacity: 0.28 })
        .when(period, { opacity: 0.08 }).delay(phase * 330).start();
    });
  }
  function queueBreathing(delay = 0) {
    if (motionQuery.matches || state.mode !== "core") return;
    breathTimers.push(setTimeout(installBreathing, delay));
  }

  function emptyDetail() {
    state.selected = null;
    panel.classList.remove("has-detail");
    $("panel-mode").textContent = "02 / 星图";
    document.querySelector(".panel-kicker").textContent = "一诗一星";
    $("detail-title").textContent = "循星寻诗";
    $("detail-description").textContent = "将光标停在星辰上，读一首诗的名字；点击星辰或连线，探索真实的诗句回响。";
    $("selection").hidden = true; $("edge-detail").hidden = true;
  }
  function nodeDetail(id) {
    const poem = poemById.get(id), count = current.degree.get(id) || 0;
    panel.classList.add("has-detail");
    $("panel-mode").textContent = "02 / 诗歌";
    document.querySelector(".panel-kicker").textContent = "一诗一星";
    $("detail-title").textContent = "循星寻诗";
    $("detail-description").textContent = `当前星图与相似度阈值下，这首诗连接了 ${count} 首对方作品。`;
    $("selection-poet").textContent = poem.poet;
    $("selection-poet").classList.toggle("du-fu", poem.poet === "杜甫");
    $("selection-title").textContent = poem.title;
    $("selection-degree").textContent = count.toLocaleString("zh-CN");
    $("selection-matches").textContent = (current.pairs.get(id) || 0).toLocaleString("zh-CN");
    $("selection").hidden = false; $("edge-detail").hidden = true;
    document.querySelector(".panel-content").scrollTop = 0;
  }
  function edgeDetail(link) {
    const li = poemById.get(link.source), du = poemById.get(link.target);
    const matches = [...link.matches].sort((a, b) => b.similarity - a.similarity);
    panel.classList.add("has-detail");
    $("panel-mode").textContent = "02 / 句对";
    document.querySelector(".panel-kicker").textContent = "两诗相望";
    $("detail-title").textContent = "诗句对读";
    $("detail-description").textContent = `${li.title} 与 ${du.title}`;
    $("selection").hidden = true;
    $("edge-detail").innerHTML = `<div class="edge-summary">当前阈值下共 <strong>${matches.length}</strong> 组真实相似句对</div>`
      + matches.map((match) => `<article class="match-pair">
        <div class="match-side"><p class="match-poet li-bai">李白</p><p class="match-title">${escapeHtml(li.title)}</p><p class="match-line">${escapeHtml(match.liBaiLine)}</p></div>
        <div class="match-side"><p class="match-poet du-fu">杜甫</p><p class="match-title">${escapeHtml(du.title)}</p><p class="match-line">${escapeHtml(match.duFuLine)}</p></div>
        <p class="match-similarity">相似度 <strong>${match.similarity.toFixed(4)}</strong></p>
      </article>`).join("");
    $("edge-detail").hidden = false;
    document.querySelector(".panel-content").scrollTop = 0;
  }
  function startIntro(nodes, links, token) {
    const order = [...nodes].sort((a, b) => {
      const score = (node) => hashId(node.id) / 4294967296 - poemById.get(node.id).degree / maxDegree * 0.16;
      return score(a) - score(b) || compareText(a.id, b.id);
    });
    const schedule = (delay, action) => introTimers.push(setTimeout(() => {
      if (token === renderToken && state.mode === "core" && !state.selected) action();
    }, delay));
    for (let step = 1; step <= 6; step++) {
      schedule(100 + (step - 1) * 190, () => {
        const visible = new Set(order.slice(0, Math.ceil(nodes.length * step / 6)).map((node) => node.id));
        chart.setOption({ series: [{ data: nodes.map((node) => visible.has(node.id) ? node : {
          ...node, itemStyle: { ...node.itemStyle, opacity: 0 }, label: { show: false }
        }) }] }, { lazyUpdate: false });
      });
    }
    schedule(1140, () => chart.setOption({ series: [{ links: links.map((link) => ({ ...link,
      lineStyle: { ...link.lineStyle, opacity: 0 } })) }] }, { lazyUpdate: false }));
    schedule(1340, () => { chart.setOption({ series: [{ links }] }, { lazyUpdate: false }); queueBreathing(260); });
  }
  function paintSelection(type, id) {
    cancelMotion();
    if (!type) {
      chart.setOption({ series: [{ data: current.graphNodes, links: state.mode === "full" ? [] : current.graphLinks }] }, { lazyUpdate: false });
      queueBreathing(280);
      return;
    }
    const brightNodes = new Set(), brightLinks = new Set();
    if (type === "node") {
      brightNodes.add(id);
      for (const link of current.links) if (link.source === id || link.target === id) {
        brightNodes.add(link.source); brightNodes.add(link.target); brightLinks.add(edgeId(link));
      }
    } else {
      const link = current.linkById.get(id);
      brightNodes.add(link.source); brightNodes.add(link.target); brightLinks.add(id);
    }
    const styledNodes = (lit) => current.graphNodes.map((node) => ({ ...node,
      symbolSize: state.mode === "full" && lit.has(node.id)
        ? node.id === id && type === "node" ? 9 : Math.max(node.symbolSize, 3.5) : node.symbolSize,
      itemStyle: {
      ...node.itemStyle, opacity: lit.has(node.id) ? 1 : 0.09,
      shadowBlur: state.mode === "full" && node.id === id && type === "node" ? 7
        : lit.has(node.id) ? node.itemStyle.shadowBlur : 0
    } }));
    const styledLinks = (shown, opacityFor) => {
      const rendered = current.graphLinks.filter((link) => shown.has(link.id));
      return rendered.map((link) => ({ ...link, lineStyle: { ...(link.lineStyle || {}),
        opacity: opacityFor(link.id), width: 1.05 } }));
    };
    if (type !== "node" || motionQuery.matches || brightLinks.size === 0) {
      chart.setOption({ series: [{ data: styledNodes(brightNodes), links: styledLinks(brightLinks, () => 0.68) }] }, { lazyUpdate: false });
      return;
    }

    const incident = current.links.filter((link) => brightLinks.has(edgeId(link)))
      .sort((a, b) => b.maxSimilarity - a.maxSimilarity || compareText(edgeId(a), edgeId(b)));
    const firstStage = new Map(incident.map((link, index) => [edgeId(link), Math.floor(index * 5 / incident.length)]));
    chart.setOption({ series: [{ data: styledNodes(new Set([id])), links: styledLinks(new Set(), () => 0) }] }, { lazyUpdate: false });
    const token = renderToken;
    for (let stage = 0; stage < 5; stage++) {
      selectionTimers.push(setTimeout(() => {
        if (token !== renderToken || state.selected?.id !== id || state.selected.type !== "node") return;
        const shown = new Set(incident.filter((link) => firstStage.get(edgeId(link)) <= stage).map(edgeId));
        chart.setOption({ series: [{ links: styledLinks(shown, (linkId) =>
          Math.min(0.68, 0.24 + (stage - firstStage.get(linkId)) * 0.22)) }] }, { lazyUpdate: false });
      }, 100 + stage * 115));
    }
    selectionTimers.push(setTimeout(() => {
      if (token !== renderToken || state.selected?.id !== id || state.selected.type !== "node") return;
      chart.setOption({ series: [{ data: styledNodes(brightNodes), links: styledLinks(brightLinks, () => 0.68) }] }, { lazyUpdate: false });
    }, 690));
  }
  function clearSelection() { paintSelection(null); emptyDetail(); }
  function selectNode(id) {
    const index = current.nodeIndex.get(id);
    if (index === undefined) return;
    paintSelection("node", id);
    state.selected = { type: "node", id }; nodeDetail(id);
  }
  function selectEdge(id) {
    const index = current.linkIndex.get(id), link = current.linkById.get(id);
    if (index === undefined || !link) return;
    paintSelection("edge", id);
    state.selected = { type: "edge", id }; edgeDetail(link);
  }

  function updateControls() {
    for (const [id, mode] of [["view-core", "core"], ["view-full", "full"]]) {
      $(id).classList.toggle("is-active", state.mode === mode);
      $(id).setAttribute("aria-pressed", String(state.mode === mode));
    }
    $("return-core").hidden = state.mode !== "local";
    $("view-note").textContent = state.mode === "core" ? "核心网络 · degree 最高的 90 首"
      : state.mode === "full" ? "已载入完整诗歌网络 · 点击星辰查看局部关联" : "局部网络 · 真实直接关联";
    $("view-note").classList.toggle("is-full", state.mode === "full");
  }
  function draw(network, selection) {
    const full = state.mode === "full", sparse = full && network.poems.length <= 30 ? makeSparsePositions(network.poems) : null;
    const nodes = network.poems.map((poem) => graphNode(poem, sparse, network.poems.length)), links = network.links.map(graphLink);
    const intro = !introPlayed && state.mode === "core" && !motionQuery.matches && !selection;
    if (state.mode === "core") introPlayed = true;
    const displayNodes = intro ? nodes.map((node) => ({ ...node,
      itemStyle: { ...node.itemStyle, opacity: 0 }, label: { show: false } })) : nodes;
    const degree = new Map(), pairs = new Map();
    for (const link of network.links) for (const id of [link.source, link.target]) {
      degree.set(id, (degree.get(id) || 0) + 1);
      pairs.set(id, (pairs.get(id) || 0) + link.matchCount);
    }
    current = { nodes: network.poems, links: network.links, graphNodes: nodes, graphLinks: links,
      nodeIndex: new Map(nodes.map((node, index) => [node.id, index])),
      linkIndex: new Map(links.map((link, index) => [link.id, index])),
      linkById: new Map(network.links.map((link) => [edgeId(link), link])), degree, pairs };
    chart.setOption({
      backgroundColor: "transparent", animation: !full && !motionQuery.matches,
      animationDuration: 0, animationDurationUpdate: 220, animationEasingUpdate: "cubicOut",
      tooltip: { trigger: "item", confine: true, backgroundColor: "rgba(13, 28, 42, .96)",
        borderColor: "rgba(232, 214, 176, .34)", borderWidth: 1, padding: [11, 14], textStyle: { color: "#e8d6b0", fontSize: 12 },
        formatter(params) {
          if (params.dataType === "node") return `<span style="color:${COLORS[params.data.poet]}">${escapeHtml(params.data.poet)}</span><br><strong style="font-size:14px;line-height:1.9">${escapeHtml(params.data.name)}</strong>`;
          const link = current.linkById.get(params.data.id);
          return link ? `${escapeHtml(poemById.get(link.source).title)} ↔ ${escapeHtml(poemById.get(link.target).title)}<br>最高相似度 ${link.maxSimilarity.toFixed(4)} · ${link.matchCount} 组句对` : "";
        } },
      series: [{ type: "graph", layout: "none", roam: true, draggable: !full, zoom: 1,
        scaleLimit: { min: full ? 0.7 : 0.65, max: 5 }, data: displayNodes, links: full || intro ? [] : links, label: { show: false },
        lineStyle: { color: "#b8c6c3", opacity: full ? 0 : 0.06, width: full ? 0.45 : 0.5 },
        emphasis: { focus: full ? "none" : "adjacency", scale: full ? 1.15 : 1.35,
          label: { show: false },
          lineStyle: { opacity: 0.72, width: full ? 1 : 1.05 } },
        blur: { itemStyle: { opacity: full ? 0.06 : 0.18 }, lineStyle: { opacity: 0 } }
      }]
    }, { notMerge: true, lazyUpdate: false });
    $("poem-count").textContent = network.poems.length.toLocaleString("zh-CN");
    $("link-count").textContent = network.links.length.toLocaleString("zh-CN");
    status.hidden = true; chart.hideLoading();
    if (selection?.type === "node" && current.nodeIndex.has(selection.id)) selectNode(selection.id);
    else if (selection?.type === "edge" && current.linkIndex.has(selection.id)) selectEdge(selection.id);
    else emptyDetail();
    if (intro) startIntro(nodes, links, renderToken);
    else if (state.mode === "core" && !selection) queueBreathing(100);
    if (full && fullRevealPending) {
      fullRevealPending = false;
      if (!motionQuery.matches) {
        $("network").classList.add("is-full-revealing");
        fullRevealTimer = setTimeout(() => $("network").classList.remove("is-full-revealing"), 650);
      }
    }
  }
  function render(selection = state.selected) {
    cancelMotion();
    const token = ++renderToken;
    updateControls();
    const doDraw = () => { if (token === renderToken) draw(visibleNetwork(), selection); };
    if (state.mode === "full") {
      status.textContent = "正在绘制完整星图…"; status.hidden = false;
      chart.showLoading("default", { text: "正在绘制完整星图…", color: COLORS["李白"], textColor: "#e8d6b0", maskColor: "rgba(16,28,43,.78)" });
      setTimeout(doDraw, 35);
    } else doDraw();
  }
  function setMode(mode) { if (state.mode === mode) return; state.mode = mode; fullRevealPending = mode === "full";
    state.localId = null; state.selected = null; search.value = ""; hideResults(); render(null); }
  function applyThreshold() { const value = Number(slider.value); if (value === state.threshold) { status.hidden = true; return; } state.threshold = value; render(); }

  function hideResults() { results.hidden = true; search.setAttribute("aria-expanded", "false"); }
  function findPoems(query) {
    const text = query.trim().toLocaleLowerCase("zh-CN");
    if (!text) return [];
    return allPoems.filter((poem) => poem.title.toLocaleLowerCase("zh-CN").includes(text)
      || poem.id.toLocaleLowerCase("zh-CN").includes(text) || poem.poet.includes(text))
      .sort((a, b) => {
        const rank = (poem) => poem.id.toLocaleLowerCase("zh-CN") === text || poem.title.toLocaleLowerCase("zh-CN") === text ? 0
          : poem.title.toLocaleLowerCase("zh-CN").startsWith(text) ? 1
          : poem.id.toLocaleLowerCase("zh-CN").endsWith(`:${text}`) ? 2 : 3;
        return rank(a) - rank(b) || b.degree - a.degree || compareText(a.id, b.id);
      });
  }
  function showResults() {
    if (!search.value.trim()) { hideResults(); return; }
    const found = findPoems(search.value);
    results.innerHTML = found.length ? found.slice(0, 8).map((poem) =>
      `<button type="button" data-id="${escapeHtml(poem.id)}"><strong>${escapeHtml(poem.title)}</strong><small>${escapeHtml(poem.poet)} · ID ${escapeHtml(poem.id.split(":")[1])} · ${poem.degree} 首关联</small></button>`).join("")
      + (found.length > 8 ? `<p>显示前 8 首，共 ${found.length} 首；可继续输入缩小范围</p>` : "") : "<p>未找到对应诗歌</p>";
    results.hidden = false; search.setAttribute("aria-expanded", "true");
  }
  function choosePoem(id) {
    const poem = poemById.get(id); if (!poem) return;
    search.value = `${poem.poet} · ${poem.title}`; hideResults();
    if (current.nodeIndex.has(id)) { state.selected = { type: "node", id }; render(state.selected); return; }
    state.mode = "local"; state.localId = id; localPositions = makeLocalPositions(id);
    state.selected = { type: "node", id }; render(state.selected);
  }

  chart = echarts.init($("network"), null, { renderer: "canvas" });
  chart.on("click", (params) => {
    if (params.dataType === "node") selectNode(params.data.id);
    else if (params.dataType === "edge") selectEdge(params.data.id || edgeId(params.data));
  });
  chart.getZr().on("click", (event) => { if (!event.target) clearSelection(); });
  new ResizeObserver(() => chart.resize()).observe($("network"));
  $("view-core").addEventListener("click", () => setMode("core"));
  $("view-full").addEventListener("click", () => setMode("full"));
  $("return-core").addEventListener("click", () => setMode("core"));
  $("reset-view").addEventListener("click", () => render());
  slider.addEventListener("input", () => { $("threshold-value").textContent = Number(slider.value).toFixed(2);
    clearTimeout(sliderTimer);
    if (state.mode === "full") { status.textContent = "松开滑块后更新完整星图…"; status.hidden = false; }
    else sliderTimer = setTimeout(applyThreshold, 180);
  });
  slider.addEventListener("change", () => { clearTimeout(sliderTimer); applyThreshold(); });
  search.addEventListener("input", showResults); search.addEventListener("focus", showResults);
  search.addEventListener("keydown", (event) => {
    if (event.key === "Escape") hideResults();
    if (event.key === "Enter") { const first = results.querySelector("button[data-id]"); if (first) choosePoem(first.dataset.id); }
    if (event.key === "ArrowDown") results.querySelector("button[data-id]")?.focus();
  });
  results.addEventListener("click", (event) => { const button = event.target.closest("button[data-id]"); if (button) choosePoem(button.dataset.id); });
  document.addEventListener("click", (event) => { if (!event.target.closest(".search-wrap")) hideResults(); });
  motionQuery.addEventListener?.("change", () => render(state.selected));
  render(null);
})();
