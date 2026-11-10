# Research run: Is the claim that this work proves a positive mass gap for Yang-Mills theory credible?

Status: **ANSWERED** (4 of 4 sub-questions have grounded findings). Mode: grounded in the material you gave.

## What was read

- QYM_ACTUAL_MODEL_PROGRESS_AND_FAILURE_MODES.md (text, via joey_intake): read, 1 text part(s)
- TARGETS.md (text, via joey_intake): read, 1 text part(s)
- frontier_HALT.md (text, via joey_intake): read, 1 text part(s)
- v1_audit.md (text, via joey_intake): read, 1 text part(s)

## Proposed answer

**What exactly is claimed about yang-mills theory mass proves?** (quoted from your material)
> The new theorem works with an actual densely defined self-adjoint `LinearPMap`. (QYM_ACTUAL_MODEL_PROGRESS_AND_FAILURE_MODES.md)

**What argument or evidence supports the claim about yang-mills theory mass proves?** (quoted from your material)
> | Frontier | Evidence that would close the interface | Common substitute that does not close it | | --- | --- | --- | | Weak coupling | Bounds on the actual conditioned blocked Wilson integral, uniform in volume and in the declared coarse configurations, including large-field contributions and normalization | A ratio bound accepted as a theorem argument; finite samples; fixed-volume asymptotics | | Multi-step RG | An identity for each blocked law, a stable norm for the entire remainder, and constants controlled through a number of steps diverging as spacing tends to zero | One-step diagonal ca (QYM_ACTUAL_MODEL_PROGRESS_AND_FAILURE_MODES.md)

**What assumptions, limits or contradicting evidence bear on yang-mills theory mass proves?** (quoted from your material)
> | Claimed advance | What the declaration actually takes as input | What it proves | | --- | --- | --- | | Wave 2: Hessian / Brascamp–Lieb concentration | `h_subG12`, `h_subG21`: the desired two fiber-ratio inequalities with `exp(c_hess / beta)` | Log-action and remainder oscillation consequences of those ratios | | Wave 3: multiscale RG closure | An arbitrary coarse `K_carried`, its contracted oscillation, the two fiber ratios, a small infrared coupling and a tube inequality | A triangle bound for an added function and scalar invariant-region arithmetic | | Wave 4: reflection-positive Schwinge (QYM_ACTUAL_MODEL_PROGRESS_AND_FAILURE_MODES.md)

**Which parts of the claim about yang-mills theory mass proves can be checked independently?** (quoted from your material)
> 1. **Fixed-volume fluctuation remainder and small-field fiber domain (`YangMillsHaarBlocking.lean`):** `haarFullLeadingFluctuationRemainder` defines `R_β(V) := A_β(V) - β I_L(V)`, `haarFullLeadingFluctuationRemainder_vacuum_zero_and_div_beta_tendsto_zero` proves `R_β(V) / β → 0` at every fixed `(L, V)`, and `haarSmallFieldFiberSublevel_partition_pos_measure_and_largeField_damping` proves the open small-field / large-field fiber partition `D_β ⊔ D_β^c`, positive Haar sublevel measure, exponential large-field damping `exp(-β I_L(V)) exp(-β δ)`, and transverse distance control under `HaarSmallFie (QYM_ACTUAL_MODEL_PROGRESS_AND_FAILURE_MODES.md)
  Against this: "| Frontier | Named hypothesis | Where consumed | Negative control | | --- | --- | --- | --- | | Uniform weak-to-strong RG control | none yet named; the replacement contract targets `R_beta(V) = A_beta(V) - beta I_L(V)` on a declared small-field domain with its complement | `YangMillsHaarBlocking` | " (QYM_ACTUAL_MODEL_PROGRESS_AND_FAILURE_MODES.md)

## Open and next steps

- Every sub-question has a grounded finding; check the quoted passages before relying on them.

Rounds: 1; stopped because every sub-question has a grounded finding. Nothing here is marked verified unless an exact checker proved it.
