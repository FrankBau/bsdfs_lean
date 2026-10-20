# The delay proofs on one page

Observable events: o_0 = start, o_1 … o_T = the outputs, o_{T+1} = term. The two theorems:
- `bsdfs_worst_case_delay` (WorstCase): o_τ and o_{τ+1} are at most 2k(n + m) steps apart.
- `bsdfs_amortized_delay` (Amortized): o_τ happens after at most τ(k + 2)(n + m) steps.

Paper names are in *italics*. Every Lean name below carries the paper's label in its docstring; the table at the end of NOTES.md lists them all.

## One interval

```
 |S|  o_τ                               o_τ+1
      *                                 *
       \                               /
        \                             /
         \  /\              /\       /
          \/  \/\          /  \     /
j+1 - - - - - - -\________/ - -\___/- - - - -
      +----------+----------------------+---->  position in the trace
      a descent  β        ascent        c
```

- **position**: index into the trace; `stk tr q` and `bar tr q z` are the stack and the barrier of z just before event q (Trace).
- **depth** of a call: the stack size before its push (s has depth 0). **spine** S_τ: the stack at o_τ, the output path without t.
- **interval** (a, c]: a < c consecutive observable events (`Consec`).
- **j, β** (`Shape`, where Lean's m is j + 1): the least stack size on (a, c] is j + 1, first reached right after β (*Descent Stack*).
- **descent** (a, β]: the stack shrinks from S_τ to size j + 1. Calls entered here return here, fruitless (*Call–Phase Correspondence*). All cascades of the interval run here.
- **ascent** (β, c]: calls only, no cascade (*Ascent Purity*).
- **period** τ = (β_{τ-1}, β_τ]: the ascent of interval τ-1, then o_τ, then the descent of interval τ.
- E_z, D_z: the number of calls at z entered, and of dequeues of z, in a range (`cnt`).

## The proof in five steps

```
 program bsdfs                                                BsdfsExec
   │  Hoare specs of the cascade and the call                  RunCasc, RunSearch, RunTrace
   ▼
 RunFacts      facts about single events and frames            Phases, WorstCase
   │  the six phase lemmas per interval                        Phases
   ▼
 DelayFacts
   │  (3, 4) counting by depths                                DelayFacts | Amortized
   ▼
 budgets       per interval ≤ 2k   |  per period ≤ k + 2       node_budget, edge_budget | node_period, edge_period
   │  (2) regroup the charges by nodes and edges               DelaySum | Amortized
   ▼
 charges       interval ≤ 2k(n+m)  |  prefix ≤ τ(k+2)(n+m)     interval_bound | cost_to_obs
   │  (1) ticks against charges                                Tally
   ▼
 steps         worst-case delay    |  amortized delay
```

**1. Ticks against charges** (Tally)
- Charge: `enter v` costs 1 + |succ v|, `dequeue q` costs 1 + |pred q|, `output P` costs |P|, every other event 0 (`Graph.evCost`).
- At every observable event: σ (its stamp, the ticks so far) ≤ charge up to it ≤ σ + owed, with owed = Σ |succ v| over the spine (`bsdfs_stamps`).
- Worst case: σ_c ≤ σ_a + charge(a, c] + owed(a) (`tally`). Amortized: σ_c ≤ charge(0, c].

**2. Regrouping** (DelaySum): charge(lo, hi] = Σ_z (E_z + D_z) + Σ_{(x,y) ∈ E} (E_x + D_y) + outputs. A call at x scans the edge (x, y) forward, a dequeue of y scans it backward (`lsum_posCost`, `pred_sum`, which needs `G.WF`). So a budget B per node and per edge gives B(n + m). t is never entered or dequeued; its slot takes the output, |P| ≤ k + 1.

**3. Budget per interval: 2k** (DelayFacts, *Interval Budget*)
- *One Entry per Pair per Phase*: the calls at z in one phase have distinct depths, in [j + 2, k] in the descent and in [j + 1, k] in the ascent (`Ed_le`, `Ea_le`).
- Dequeues happen only in the descent: one per drop, plus one as origin (`D_le`). The drops of y come from origins of distinct depths ≤ i, the depth of the first one (`U_le`, *Descent Origins*, *Drop Depth*).
- If y is dropped in the descent, first by an origin at depth i, the calls at y and at its predecessors in the descent have depth ≥ i + 1 (`descent_split`, *Descent Split*), and y keeps b ≥ 2 through the ascent (`obs_i`). If y is not dropped in the descent, it has at most k - j calls in both phases together (`obs_ii`).
- Together: E_z + D_z ≤ 2k (`node_budget`) and E_x + D_y + [x on the stack at a] ≤ 2k (`edge_budget`; the last term pays owed(a)). Hence 2k(n - 1) + 2km + (k + 1) ≤ 2k(n + m) (`interval_bound`).

**4. Budget per period: k + 2** (Amortized, *Period Budget*)
- Of the calls at z entered in the period, at most one is still open at o_τ (`R_le_one`). The others are fruitless and return within the period with their raise. The raises form one chain, so their depths are distinct (`nR_depth_inj`). If z or a successor of z is dropped in the descent of interval τ, first by an origin at depth i, these depths lie in [i + 1, k] (`period_split`, *Period Split*). Dequeues: one per drop plus one as origin, at most i + 1 (`D_period_le`).
- Together: E_z + D_z ≤ k + 2 and E_x + D_y ≤ k + 2 (`node_period`, `edge_period`). A period costs at most (k + 2)(n + m) (`period_cost`), and so does an ascent alone (`asc_cost`).
- Up to o_τ: τ - 1 periods and the ascent of interval τ-1 (the initial interval has an empty descent), so at most τ(k + 2)(n + m) (`cost_to_obs`).

**5. Where the facts come from.** `RunFacts` (Phases) lists about 20 facts about single events and frames of the run:
- the values that raise, fruitful and drop writes set;
- the frame of every call and *Return Value*;
- the structure of a cascade;
- *Per-Call Global Monotonicity*;
- the scans of a call;
- *Call Completeness*;
- *Cascade Witness Path*.

The Hoare specs of the cascade and the call prove them for the program (`fruitful_spec_tr`, `search_spec_tr`, collected position by position as `PosOK`, then `bsdfs_runFacts`). From them `intervalFacts` derives the six phase lemmas per interval: *Ascent Purity*, *Call–Phase Correspondence*, *Descent Origins*, *Dequeue Count*, *Descent Seal*, *One Entry per Pair per Phase*.
