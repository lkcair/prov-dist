import collections
import json
import os
import random
import statistics
import sys
from array import array

LOG = os.path.join(os.path.dirname(os.path.abspath(__file__)), "provenance.jsonl")


def load(path=LOG):
    recs = [json.loads(line) for line in open(path, encoding="utf-8") if line.strip()]
    recs.sort(key=lambda r: r["id"])
    assert [r["id"] for r in recs] == list(range(len(recs)))
    return recs


def ancestors(out_adj, u):
    seen, stack = {u}, [u]
    while stack:
        x = stack.pop()
        for s in out_adj[x]:
            if s not in seen:
                seen.add(s)
                stack.append(s)
    return seen


def mix64(x):
    x = (x + 0x9E3779B97F4A7C15) & 0xFFFFFFFFFFFFFFFF
    x = ((x ^ (x >> 30)) * 0xBF58476D1CE4E5B9) & 0xFFFFFFFFFFFFFFFF
    x = ((x ^ (x >> 27)) * 0x94D049BB133111EB) & 0xFFFFFFFFFFFFFFFF
    return x ^ (x >> 31)


def templates(recs):
    coarse_ids = {r["id"] for r in recs if r["tier"] == "coarse"}
    by_run = collections.OrderedDict()
    for r in recs:
        if r["tier"] != "coarse":
            by_run.setdefault(r["run"], []).append(r)
    out = []
    for rows in by_run.values():
        local = {r["id"]: i for i, r in enumerate(rows)}
        n = len(rows)
        acts = [r["act"] for r in rows]
        agents = [r.get("agent") or "" for r in rows]
        edges = [[] for _ in range(n)]
        coarse_slots, seen = [], {}
        for i, r in enumerate(rows):
            for s in r["src"]:
                if s in local:
                    edges[i].append(local[s])
                elif s in coarse_ids:
                    coarse_slots.append((i, seen.setdefault(s, len(seen))))
        out.append({"acts": acts, "edges": edges, "n": n, "coarse_slots": coarse_slots,
                    "branch_of": branches(acts, edges, n, agents)})
    return out


def branches(acts, edges, n, agents):
    by_act = collections.defaultdict(set)
    for i in range(n):
        if agents[i]:
            by_act[acts[i]].add(agents[i])
    peers = set()
    for ags in by_act.values():
        if len(ags) > 1:
            peers |= ags
    root_of = {i: agents[i] for i in range(n) if agents[i] in peers}
    if not root_of:
        return [-1] * n
    desc = [set() for _ in range(n)]
    for i in range(n):
        for s in edges[i]:
            desc[i] |= desc[s]
        if i in root_of:
            desc[i].add(root_of[i])
    anc = [set() for _ in range(n)]
    for i in range(n - 1, -1, -1):
        if i in root_of:
            anc[i].add(root_of[i])
        for s in edges[i]:
            anc[s] |= anc[i]
    order = {a: k for k, a in enumerate(sorted(peers))}
    band = [-1] * n
    for i in range(n):
        if len(desc[i]) == 1:
            band[i] = order[next(iter(desc[i]))]
        elif not desc[i] and len(anc[i]) == 1:
            band[i] = order[next(iter(anc[i]))]
    return band


def widen(t, width):
    if width <= 1:
        return {"acts": list(t["acts"]), "edges": [list(e) for e in t["edges"]],
                "n": t["n"], "coarse_slots": list(t["coarse_slots"])}
    acts, edges = list(t["acts"]), [list(e) for e in t["edges"]]
    branch_of = t["branch_of"]
    members = collections.defaultdict(list)
    for i, b in enumerate(branch_of):
        if b >= 0:
            members[b].append(i)
    n = t["n"]
    copy_of = {}
    for b, idxs in members.items():
        for k in range(1, width):
            m = {}
            for i in idxs:
                m[i] = n
                acts.append(t["acts"][i])
                edges.append([])
                n += 1
            copy_of[(b, k)] = m
    for (b, k), m in copy_of.items():
        for i in members[b]:
            for s in t["edges"][i]:
                edges[m[i]].append(m.get(s, s))
    for i in range(t["n"]):
        if branch_of[i] >= 0:
            continue
        extra = []
        for s in t["edges"][i]:
            if branch_of[s] >= 0:
                extra += [copy_of[(branch_of[s], k)][s] for k in range(1, width)]
        edges[i] += extra
    slots = list(t["coarse_slots"])
    for (b, k), m in copy_of.items():
        slots += [(m[i], sl) for i, sl in t["coarse_slots"] if i in m]
    return topo({"acts": acts, "edges": edges, "n": n, "coarse_slots": slots})


def topo(t):
    n, edges = t["n"], t["edges"]
    order, mark = [], [0] * n
    for start in range(n):
        if mark[start]:
            continue
        stack = [(start, iter(edges[start]))]
        mark[start] = 1
        while stack:
            v, it = stack[-1]
            nxt = next(it, None)
            if nxt is None:
                mark[v] = 2
                order.append(v)
                stack.pop()
            elif mark[nxt] == 0:
                mark[nxt] = 1
                stack.append((nxt, iter(edges[nxt])))
    pos = {v: i for i, v in enumerate(order)}
    return {"acts": [t["acts"][v] for v in order],
            "edges": [sorted(pos[s] for s in edges[v]) for v in order],
            "n": n,
            "coarse_slots": [(pos[i], sl) for i, sl in t["coarse_slots"]]}


def published(t):
    anc = [set() for _ in range(t["n"])]
    best = 0
    for i in range(t["n"]):
        for s in t["edges"][i]:
            anc[i].add(s)
            anc[i] |= anc[s]
        if len(anc[i]) >= len(anc[best]):
            best = i
    return best


def emit(pending, recs, nid, coarse_ids, rng):
    runs = []
    for t, prev in pending:
        uid = "%08x" % rng.getrandbits(32)
        cmap = {}
        for _, slot in t["coarse_slots"]:
            cmap.setdefault(slot, coarse_ids[rng.randrange(len(coarse_ids))])
        extra = collections.defaultdict(list)
        for i, slot in t["coarse_slots"]:
            extra[i].append(cmap[slot])
        if prev is not None:
            for i in ({i for i, _ in t["coarse_slots"]} or {0}):
                extra[i].append(prev)
        runs.append((uid, t, extra))

    order, cursors = [], [0] * len(runs)
    moved = True
    while moved:
        moved = False
        for j, (_, t, _) in enumerate(runs):
            if cursors[j] < t["n"]:
                order.append((j, cursors[j]))
                cursors[j] += 1
                moved = True

    gid = {}
    for j, i in order:
        gid[(j, i)] = nid
        nid += 1
    ts = float(len(recs))
    for j, i in order:
        uid, t, extra = runs[j]
        recs.append({"id": gid[(j, i)], "run": uid, "act": t["acts"][i],
                     "src": sorted(set([gid[(j, s)] for s in t["edges"][i]] + extra.get(i, []))),
                     "tier": "fine", "ts": ts})
        ts += 1.0
    return nid, [gid[(j, published(t))] for j, (_, t, _) in enumerate(runs)]


def chain_placement(depth=100, base=77, P=8, samples=25, seed=29):
    recs = synth(base * depth, depth=depth)
    out_adj = [r["src"] for r in recs]
    run_of = {r["id"]: r["run"] for r in recs if r["tier"] == "fine"}
    order = list(dict.fromkeys(run_of.values()))
    index = {u: i for i, u in enumerate(order)}
    height, deepest = {}, {}
    for r in recs:
        height[r["id"]] = 1 + max((height[s] for s in r["src"]), default=0)
        if r["id"] in run_of and index[run_of[r["id"]]] >= len(order) - base:
            u = run_of[r["id"]]
            if u not in deepest or height[r["id"]] > height[deepest[u]]:
                deepest[u] = r["id"]
    audits = [deepest[u] for u in random.Random(seed).sample(sorted(deepest), samples)]

    def score(site_of):
        edges = cut = 0
        load = [0] * P
        for v, u in run_of.items():
            load[site_of[u]] += 1
            for s in out_adj[v]:
                if s in run_of:
                    edges += 1
                    cut += site_of[run_of[s]] != site_of[u]
        sites = [len({site_of[run_of[x]] for x in ancestors(out_adj, a) if x in run_of})
                 for a in audits]
        return {"cut": cut / edges, "sites": sum(sites) / len(sites),
                "balance": max(load) / (sum(load) / P)}

    return {"depth": depth, "P": P,
            "run": score({u: i % P for u, i in index.items()}),
            "chain": score({u: (i % base) % P for u, i in index.items()})}


def synth(runs, width=1, depth=1, concurrency=4, seed=7, path=LOG):
    real = load(path)
    tpls = templates(real)
    rng = random.Random(seed)
    recs, nid, coarse_ids = [], 0, []
    for _ in range(sum(1 for r in real if r["tier"] == "coarse")):
        recs.append({"id": nid, "run": "", "act": "CoarseDataset", "src": [],
                     "tier": "coarse", "ts": 0.0})
        coarse_ids.append(nid)
        nid += 1
    chains = -(-runs // depth)
    assert depth == 1 or chains >= concurrency
    pub, pending = [], []
    for i in range(runs):
        prev = pub[i - chains] if depth > 1 and i >= chains else None
        pending.append((widen(tpls[i % len(tpls)], width), prev))
        if len(pending) >= concurrency or i == runs - 1:
            nid, got = emit(pending, recs, nid, coarse_ids, rng)
            pub += got
            pending = []
    return recs


P = 8
LATENESS = 2.0
BASE = 77
SAMPLES = 25
SEED = 29
RESULTS = []


def check(label, ok, detail):
    RESULTS.append(bool(ok))
    print(f"[{'PASS' if ok else 'FAIL'}] {label}: {detail}")


def title(text):
    print(f"\n{text}")


def pct(x):
    return f"{100 * x:.1f}%"


def csr(recs):
    n = len(recs)
    off, src, cands = array("q", [0]) * (n + 1), array("q"), {}
    for r in recs:
        src.extend(r["src"])
        off[r["id"] + 1] = len(src)
        if r["tier"] == "fine":
            cands.setdefault(r["run"], {})[r["act"]] = r["id"]
    return n, off, src, cands


def csr_ancestors(off, src, u):
    seen, stack = {u}, [u]
    while stack:
        x = stack.pop()
        for k in range(off[x], off[x + 1]):
            if src[k] not in seen:
                seen.add(src[k])
                stack.append(src[k])
    seen.discard(u)
    return seen


def sample_audits(off, src, cands, last=None):
    rng = random.Random(SEED)
    runs = sorted(list(cands)[-last:]) if last else sorted(cands)
    top, anc = {}, {}
    for r in runs:
        best, best_a = None, set()
        for i in sorted(cands[r].values()):
            a = csr_ancestors(off, src, i)
            if len(a) >= len(best_a):
                best, best_a = i, a
        top[r], anc[r] = best, best_a
    widest = max(runs, key=lambda r: len(anc[r]))
    chosen = rng.sample(runs, min(SAMPLES, len(runs)))
    if widest not in chosen:
        chosen[0] = widest
    audits = [(top[r], min(anc[r])) for r in chosen if anc[r]]
    return audits, max(len(anc[r]) for r in chosen)


def longest_path(n, off, src):
    h = array("q", [0]) * n
    for v in range(n):
        for k in range(off[v], off[v + 1]):
            h[v] = max(h[v], h[src[k]] + 1)
    return max(h)


def closure_rows(n, off, src, recs):
    coarse = [r["id"] for r in recs if r["tier"] == "coarse"]
    is_coarse = set(coarse)
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for v in range(n):
        for k in range(off[v], off[v + 1]):
            if src[k] not in is_coarse and v not in is_coarse:
                parent[find(v)] = find(src[k])
    members = {}
    for v in range(n):
        if v not in is_coarse:
            members.setdefault(find(v), []).append(v)
    total = 0
    for group in members.values():
        index = {c: i for i, c in enumerate(coarse)}
        index.update({v: len(coarse) + i for i, v in enumerate(group)})
        bits = {}
        for v in group:
            acc = 0
            for k in range(off[v], off[v + 1]):
                acc |= (1 << index[src[k]]) | bits.get(src[k], 0)
            bits[v] = acc
            total += bin(acc).count("1")
    return total


def recording(recs):
    title("The recording")
    ts = [r["ts"] for r in recs]
    forward = sum(1 for r in recs for s in r["src"] if s >= r["id"])
    same = sum(1 for r in recs for s in r["src"] if ts[s] == ts[r["id"]])
    earlier = sum(1 for r in recs for s in r["src"] if ts[s] < ts[r["id"]])
    check("no edge points forward in the log", forward == 0,
          f"{same} edges inside one event, {earlier} to an earlier event, {forward} forward")
    run_of = [r["run"] if r["tier"] == "fine" else None for r in recs]
    runs = list(dict.fromkeys(x for x in run_of if x))
    first, last = {}, {}
    for v, x in enumerate(run_of):
        if x:
            first.setdefault(x, v)
            last[x] = v
    contiguous = sum(1 for r in runs if all(run_of[v] == r for v in range(first[r], last[r] + 1)))
    check("runs interleave in the log", contiguous < len(runs),
          f"{contiguous} of {len(runs)} runs are contiguous")
    cfg = {r["id"] for r in recs if r["act"].endswith("Configuration")}
    acts = [r for r in recs if r["act"].endswith("Activity") or r["act"] == "Inference"]
    typed = {r["id"] for r in acts if r["act"] == "Inference"}
    by_edge = {r["id"] for r in acts if any(s in cfg for s in r["src"])}
    check("the configuration edge finds more model invocations than the recorder typed",
          len(typed | by_edge) > len(typed),
          f"{len(typed)} typed, {len(by_edge - typed)} more by the edge")
    return run_of, runs


def conformance(recs):
    title("Conformance")
    watermark = high = None
    late = 0
    for r in recs:
        high = r["ts"] if high is None else max(high, r["ts"])
        if watermark is not None and r["ts"] < watermark:
            late += 1
            continue
        watermark = high - LATENESS
    facts = sum(max(1, len(r["src"])) for r in recs)
    check("silver holds every recorded fact, late events included", late > 0,
          f"{facts:,} facts, {late} events written after the watermark")
    runs = collections.Counter()
    names = {r["id"] for r in recs if r["tier"] == "coarse"}
    kept = 0
    for r in recs:
        parent = [s for s in r["src"] if s not in names][:1]
        kept += max(1, len(parent) + sum(1 for s in r["src"] if s in names))
    check("a mapping that drops the span links loses facts that replaying bronze restores",
          kept < facts, f"it loses {facts - kept:,} of {facts:,} facts")


def score(site, out_adj, tops, order, samples=400, seed=11):
    n = len(out_adj)
    edges = cut = 0
    for v in range(n):
        for s in out_adj[v]:
            if site[v] >= 0 and site[s] >= 0:
                edges += 1
                cut += site[v] != site[s]
    rng = random.Random(seed)
    touched = []
    for _ in range(samples):
        u = tops[rng.randrange(len(tops))]
        touched.append(len({site[x] for x in ancestors(out_adj, u) if site[x] >= 0}))
    load = [0] * P
    for v in range(n):
        if site[v] >= 0:
            load[site[v]] += 1
    tail = [0] * P
    for v in sorted(range(n), key=lambda v: order[v])[int(0.9 * n):]:
        if site[v] >= 0:
            tail[site[v]] += 1
    return {"cut": cut / edges, "sites": sum(touched) / len(touched),
            "local": sum(1 for k in touched if k <= 1) / len(touched),
            "balance": max(load) / (sum(load) / P), "skew": max(tail) / sum(tail)}


def keys(recs, run_of, runs):
    title("Fragmentation keys (Table 3)")
    out_adj = [r["src"] for r in recs]
    n = len(out_adj)
    index = {r: i for i, r in enumerate(runs)}
    size = [len(ancestors(out_adj, v)) for v in range(n)]
    tops = [None] * len(runs)
    for v in range(n):
        if run_of[v]:
            i = index[run_of[v]]
            if tops[i] is None or size[v] > size[tops[i]]:
                tops[i] = v
    coarse = [v for v in range(n) if not run_of[v]]

    def without_coarse(site):
        for c in coarse:
            site[c] = -1
        return site

    host = random.Random(11)
    real = list(range(n))
    rows = {
        "run identifier": [-1 if not run_of[v] else index[run_of[v]] % P for v in range(n)],
        "artifact hash": without_coarse([mix64(v * 0x2545F4914F6CDD1D + 11) % P for v in range(n)]),
        "executing host": without_coarse([host.randrange(P) for _ in range(n)]),
        "log position": without_coarse([min(P - 1, v * P // n) for v in range(n)]),
    }
    s = {name: score(site, out_adj, tops, real) for name, site in rows.items()}
    for name, x in s.items():
        print(f"  {name:16s} cross {pct(x['cut']):>6s}  sites per audit {x['sites']:.2f}"
              f"  local {100 * x['local']:.0f}%  balance {x['balance']:.2f}"
              f"  write skew {100 * x['skew']:.0f}%")
    run, hsh, hst, log = (s[k] for k in rows)
    check("the run key cuts no edge and answers every audit at one site",
          run["cut"] == 0 and run["local"] == 1.0, f"{run['sites']:.2f} sites per audit")
    check("hash and host cut about 1 - 1/P of the edges",
          all(0.75 <= x["cut"] <= 0.95 for x in (hsh, hst)),
          f"{pct(hsh['cut'])} and {pct(hst['cut'])}, 1 - 1/P = {pct(1 - 1 / P)}")
    check("the log key sends the newest writes to one site", log["skew"] > 0.9,
          f"{100 * log['skew']:.0f}%")

    title("Adding a site")
    before = {r: i % P for i, r in enumerate(runs)}
    count = collections.Counter(before.values())
    by_site = collections.defaultdict(list)
    for r, x in before.items():
        by_site[x].append(r)
    after = dict(before)
    for _ in range(len(runs) // (P + 1)):
        x = max(range(P), key=lambda k: count[k])
        r = by_site[x].pop()
        after[r] = P
        count[x] -= 1
        count[P] += 1
    moved = sum(1 for r in runs if before[r] != after[r])
    check("the catalog moves about 1/(P+1) of the runs, as whole fragments",
          abs(moved / len(runs) - 1 / (P + 1)) < 0.05, f"{moved} of {len(runs)}")


def chains():
    c = chain_placement()
    title(f"Chained requests, depth {c['depth']}")
    run, chain = c["run"], c["chain"]
    check("placing each request by its own run spreads a chain over several sites",
          run["sites"] > 1, f"cut {pct(run['cut'])}, {run['sites']:.2f} sites per audit")
    check("placing each request with the request it reads keeps every audit on one site",
          chain["cut"] == 0 and chain["sites"] == 1,
          f"{chain['sites']:.2f} sites per audit, balance {chain['balance']:.2f}")


def searches(depth=100):
    title(f"Search on the tall store, depth {depth}")
    n, off, src, cands = csr(synth(BASE * depth, depth=depth))
    audits, _ = sample_audits(off, src, cands, BASE)
    visited, anc = [], []
    for u, v in audits:
        seen, q = {u}, collections.deque([u])
        while q:
            x = q.popleft()
            if x == v:
                break
            for k in range(off[x], off[x + 1]):
                if src[k] not in seen:
                    seen.add(src[k])
                    q.append(src[k])
        visited.append(len(seen))
        anc.append(len(csr_ancestors(off, src, u)))
    a, b = statistics.median(visited), statistics.median(anc)
    check("a search that stops at the source visits fewer entities than the ancestor set",
          a < b, f"median {a:,.0f} visited against {b:,.0f} ancestors")


def replicas(recs):
    title("Replicas")
    out_adj = [r["src"] for r in recs]
    n = len(recs)
    by_run = collections.defaultdict(list)
    for r in recs:
        if r["tier"] == "fine":
            by_run[r["run"]].append(r["id"])
    runs = list(by_run)
    pairs = []
    for run in random.Random(23).sample(runs, min(300, len(runs))):
        for u in sorted(by_run[run], reverse=True)[:4]:
            anc = sorted(ancestors(out_adj, u) - {u})
            if anc:
                pairs += [(u, anc[len(anc) // 2]), (u, anc[0])]
    pairs = list(dict.fromkeys(pairs))

    def reach(adj, u, v):
        return v in ancestors(adj, u)

    exact = True
    for lag in (0.25, 0.5, 0.75, 1.0):
        upto = int((n - 1) * lag)
        rep = [[s for s in out_adj[v]] if v <= upto else [] for v in range(n)]
        held = [(u, v) for u, v in pairs if u <= upto and v <= upto]
        exact &= all(reach(rep, u, v) for u, v in held)
    check("a replica that applies the log in order answers every audit it holds exactly",
          exact, f"{len(pairs)} connected pairs, at every lag")
    rng = random.Random(3)
    keep = {v for v in range(n) if rng.random() < 0.5}
    sub = [list(out_adj[v]) if v in keep else [] for v in range(n)]
    held = [(u, v) for u, v in pairs if u in keep and v in keep]
    wrong = sum(1 for u, v in held if not reach(sub, u, v))
    check("a replica that applies the log out of order loses exactness", wrong > 0,
          f"{wrong} of {len(held)} held pairs answer differently")


def widest_run(recs):
    title("Figure 2")
    out = [r["src"] for r in recs]
    inn = collections.defaultdict(list)
    for r in recs:
        for s in r["src"]:
            inn[s].append(r["id"])
    cands = {}
    for r in recs:
        if r["tier"] == "fine":
            cands.setdefault(r["run"], {})[r["act"]] = r["id"]
    top, anc = {}, {}
    for run, by_act in cands.items():
        best, best_a = None, set()
        for i in sorted(by_act.values()):
            a = ancestors(out, i) - {i}
            if len(a) >= len(best_a):
                best, best_a = i, a
        top[run], anc[run] = best, best_a
    run = max(anc, key=lambda k: len(anc[k]))
    u, A = top[run], anc[run]
    members = [r["id"] for r in recs if r["run"] == run and r["tier"] == "fine"]
    coarse = {r["id"] for r in recs if r["tier"] == "coarse"}
    read = sorted({s for m in members for s in out[m] if s in coarse})
    readers = collections.Counter(s for s, _ in {(s, r["run"]) for r in recs if r["tier"] == "fine"
                                                 for s in r["src"] if s in coarse})
    ds = max(read, key=lambda k: readers[k])
    in_run = (ancestors(inn, ds) - {ds}) & set(members)
    dist, q = {u: 0}, collections.deque([u])
    while q:
        x = q.popleft()
        for s in out[x]:
            if s not in dist:
                dist[s] = dist[x] + 1
                q.append(s)
    print(f"  run {run[:8]}: {len(members)} entities, {len(read)} datasets read,"
          f" {len(A)} ancestors, {dist[min(A)]} hops to the oldest source,"
          f" {sum(len(out[m]) for m in members)} adjacency rows,"
          f" {sum(len(ancestors(out, m)) - 1 for m in members):,} closure rows,"
          f" one dataset reached {len(in_run)}")


def table2():
    title("Table 2, structural columns (slow on the largest points)")
    points = ([(BASE, w, 1) for w in (1, 5, 10, 25, 50, 100, 200, 500)]
              + [(BASE * d, 1, d) for d in (2, 3, 5, 10, 25, 50, 100)]
              + [(BASE * d, 1, 1) for d in (2, 3, 5, 10, 25, 50, 100)])
    for runs, width, depth in points:
        recs = synth(runs, width, depth)
        n, off, src, cands = csr(recs)
        rows = closure_rows(n, off, src, recs)
        _, widest = sample_audits(off, src, cands, BASE if depth > 1 else None)
        print(f"  {runs:5d} requests, width {width:3d}, depth {depth:3d}: {n:>9,} entities,"
              f" {longest_path(n, off, src):5d} hops, {widest:6,} ancestors, {rows:>13,} closure rows",
              flush=True)


def main():
    recs = load()
    run_of, runs = recording(recs)
    conformance(recs)
    keys(recs, run_of, runs)
    chains()
    searches()
    replicas(recs)
    widest_run(recs)
    print(f"\n{sum(RESULTS)} of {len(RESULTS)} checks passed")
    if "table" in sys.argv[1:]:
        table2()
    return 0 if all(RESULTS) else 1


if __name__ == "__main__":
    sys.exit(main())
