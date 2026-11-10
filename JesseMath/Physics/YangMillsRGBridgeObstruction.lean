import JesseMath.Linter.AxiomAudit
import JesseMath.Physics.SussmanAlpogeBalaban
import JesseMath.Physics.YangMillsWilsonMeasureBridge
import JesseMath.Unified.SchurFeshbachWaveletComb
import JesseMath.Unified.MetriplecticScaleComb
import JesseMath.Unified.HamiltonianScaleComb
import JesseMath.UnificationTooling.SynthesisOfGreats
import JesseMath.Jessplexical.JessplexicalAnalysis

/-!
# The bare strong-coupling criterion does not cover a weak-coupling limit

These statements concern the existing sufficient Dobrushin bound `18 * β`.
They do not assert absence of a mass gap. A continuum trajectory with bare
`β → ∞` needs an estimate for the actual blocked measure, rather than direct
reuse of the bare strong-coupling criterion.
-/

namespace JesseMath.Physics.YangMillsRGBridgeObstruction

open Filter

theorem bare_row_sum_eventually_ge_one
    {β : ℕ → ℝ} (hβ : Tendsto β atTop atTop) :
    ∀ᶠ n in atTop, 1 ≤ dobrushinRowSum4D (β n) := by
  filter_upwards [hβ.eventually_ge_atTop (1 / 18)] with n hn
  norm_num [dobrushinRowSum4D, dobrushinIncidenceRowSum4D]
  linarith

theorem bare_strong_coupling_not_eventually_available
    {β : ℕ → ℝ} (hβ : Tendsto β atTop atTop) :
    ¬ ∀ᶠ n in atTop, dobrushinRowSum4D (β n) < 1 := by
  intro h
  obtain ⟨n, hge, hlt⟩ := ((bare_row_sum_eventually_ge_one hβ).and h).exists
  exact (not_lt_of_ge hge) hlt

/-- Adding a nonnegative residual to the diverging bare row sum cannot
restore this particular contraction criterion. Renormalizing the measure
must change the estimate, not merely append a positive error term. -/
theorem nonnegative_remainder_cannot_repair_bare_row_sum
    {β η : ℕ → ℝ} (hβ : Tendsto β atTop atTop)
    (hη : ∀ᶠ n in atTop, 0 ≤ η n) :
    ∀ᶠ n in atTop, 1 ≤ dobrushinRowSum4D (β n) + η n := by
  filter_upwards [bare_row_sum_eventually_ge_one hβ, hη] with n hn hηn
  linarith

/-- A finite point on the bare trajectory already violates `ρ < 1`.
This is a counterexample to applicability of the criterion, not to a gap. -/
theorem bare_beta_one_negative_control :
    dobrushinRowSum4D 1 = 18 ∧ ¬ dobrushinRowSum4D 1 < 1 := by
  norm_num [dobrushinRowSum4D, dobrushinIncidenceRowSum4D]

/-- Contrast between the diverging bare Dobrushin row sum along `β_bare → ∞` and a
renormalized effective trajectory `β_eff` with nonnegative polymer remainder `η`
satisfying `dobrushinRowSum4D (β_eff n) + η n ≤ ρ_star < 1`. -/
theorem renormalized_effective_row_sum_contraction
    {β_bare β_eff η : ℕ → ℝ} {ρ_star : ℝ}
    (hβ_bare : Tendsto β_bare atTop atTop)
    (h_eff_nonneg : ∀ n, 0 ≤ β_eff n)
    (hη_nonneg : ∀ n, 0 ≤ η n)
    (h_renorm : ∀ n, dobrushinRowSum4D (β_eff n) + η n ≤ ρ_star)
    (hρ : ρ_star < 1) :
    (∀ᶠ n in atTop, 1 ≤ dobrushinRowSum4D (β_bare n)) ∧
    (∀ n, 0 ≤ dobrushinRowSum4D (β_eff n) + η n ∧
      dobrushinRowSum4D (β_eff n) + η n < 1) := by
  refine ⟨bare_row_sum_eventually_ge_one hβ_bare, fun n => ?_⟩
  have h_eff := h_eff_nonneg n
  have h_eta := hη_nonneg n
  have h_ren := h_renorm n
  have h_row_nonneg : 0 ≤ dobrushinRowSum4D (β_eff n) := by
    norm_num [dobrushinRowSum4D, dobrushinIncidenceRowSum4D]
    linarith
  exact ⟨by linarith, by linarith⟩

/-- One-step Schur–Feshbach / Mori–Zwanzig effective coupling evolution
`β_next = β_k - Δβ_AF + η_k` after integrating out the `2^4 - 1 = 15` fine modes of a 4D dyadic block. -/
def schurFeshbachEffectiveCouplingStep (β_k Δβ_AF η_k : ℝ) : ℝ :=
  β_k - Δβ_AF + η_k

/-- In 4D Euclidean spacetime (`2^4 = 16` hyper-voxel cells per dyadic block, eliminating `15/16`
of fine modes per step), a Schur–Feshbach effective coupling step `schurFeshbachEffectiveCouplingStep β_k Δβ_AF η_k`
with two-sided polymer remainder `η_k ≤ (1/2) * Δβ_AF` strictly reduces the coupling by at least
`(1/2) * Δβ_AF`; when the resulting step output `β_ir = schurFeshbachEffectiveCouplingStep β_k Δβ_AF η_k`
lands in `(0, (1 - η_ir) / 18)`, its Dobrushin row sum satisfies `0 < dobrushinRowSum4D β_ir + η_ir < 1`
(whereas a single step from a large bare coupling such as `β_k = 100, Δβ_AF = 1, η_k = 0` gives
`dobrushinRowSum4D (schurFeshbachEffectiveCouplingStep 100 1 0) = 1782 ≥ 1`, so landing requires
sufficient cumulative net reduction across scales). -/
theorem voxelean4D_wavelet_downfolding_and_effective_contraction
    {β_k Δβ_AF η_k β_ir η_ir : ℝ}
    (_h_af : 0 < Δβ_AF)
    (h_tube_hi : η_k ≤ (1 / 2) * Δβ_AF)
    (h_bind : β_ir = schurFeshbachEffectiveCouplingStep β_k Δβ_AF η_k)
    (h_ir_pos : 0 < β_ir)
    (h_eta_ir_nonneg : 0 ≤ η_ir)
    (h_landing : 18 * β_ir + η_ir < 1) :
    ((2 : ℝ) ^ 4 - 1) / (2 : ℝ) ^ 4 = 15 / 16 ∧
    β_ir ≤ β_k - (1 / 2) * Δβ_AF ∧
    0 < dobrushinRowSum4D (schurFeshbachEffectiveCouplingStep β_k Δβ_AF η_k) + η_ir ∧
    dobrushinRowSum4D (schurFeshbachEffectiveCouplingStep β_k Δβ_AF η_k) + η_ir < 1 ∧
    dobrushinRowSum4D (schurFeshbachEffectiveCouplingStep 100 1 0) = 1782 ∧
    ¬ dobrushinRowSum4D (schurFeshbachEffectiveCouplingStep 100 1 0) < 1 := by
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_bind]
    unfold schurFeshbachEffectiveCouplingStep
    linarith
  · rw [← h_bind]
    norm_num [dobrushinRowSum4D, dobrushinIncidenceRowSum4D]
    linarith
  · rw [← h_bind]
    norm_num [dobrushinRowSum4D, dobrushinIncidenceRowSum4D]
    linarith
  · norm_num [schurFeshbachEffectiveCouplingStep, dobrushinRowSum4D, dobrushinIncidenceRowSum4D]
  · norm_num [schurFeshbachEffectiveCouplingStep, dobrushinRowSum4D, dobrushinIncidenceRowSum4D]

/-- Multi-scale 4D dyadic Schur–Feshbach RG trajectory synthesis (`SchurFeshbachWaveletComb`):
across `K` dyadic renormalization steps (`2^4 = 16` hyper-voxels per block, `15` fine wavelet modes),
the iterated effective gap telescopes (`Delta_seq K = Delta_seq 0 + ∑_{j<K} delta j`),
the `(1/4)^{j+1}` UV perturbation shift compresses by the exact factor `1/3` (`|∑ delta j| ≤ g_0^2 / (3 * gamma_0)`),
and the 4D `(1/16)^{j+1}` wave-function susceptibility compresses by the exact factor `1/15`
(`∑_{j<K} chi j < 1` whenever `g_0^2 < 15 * gamma_0^2`). -/
theorem schurFeshbach_multiscale_dyadic_susceptibility_and_uv_compression
    (K : ℕ) (g_0 gamma_0 : ℝ) (Delta_seq delta chi : ℕ → ℝ)
    (h_gamma : 0 < gamma_0)
    (h_step : ∀ j : ℕ, Delta_seq (j + 1) = Delta_seq j + delta j)
    (h_shell : ∀ j ∈ Finset.range K, |delta j| ≤ (g_0 ^ 2 / gamma_0) * (1 / 4 : ℝ) ^ (j + 1))
    (h_chi : ∀ j ∈ Finset.range K, chi j ≤ (g_0 ^ 2 / gamma_0 ^ 2) * (1 / 16 : ℝ) ^ (j + 1))
    (h_subcrit : g_0 ^ 2 < 15 * gamma_0 ^ 2) :
    Delta_seq K = Delta_seq 0 + ∑ j ∈ Finset.range K, delta j ∧
    ∑ j ∈ Finset.range K, (1 / 4 : ℝ) ^ (j + 1) = (1 - (1 / 4 : ℝ) ^ K) / 3 ∧
    |∑ j ∈ Finset.range K, delta j| ≤ g_0 ^ 2 / (3 * gamma_0) ∧
    ∑ j ∈ Finset.range K, (1 / 16 : ℝ) ^ (j + 1) = (1 - (1 / 16 : ℝ) ^ K) / 15 ∧
    ∑ j ∈ Finset.range K, chi j < 1 := by
  have h_tel :=
    JesseMath.Unified.SchurFeshbachWaveletComb.iterated_feshbach_telescoping_identity
      Delta_seq delta K h_step
  have h_uv :=
    JesseMath.Unified.SchurFeshbachWaveletComb.dyadic_one_third_uv_perturbation_compression
      K g_0 gamma_0 delta h_gamma h_shell
  have h_susc :=
    JesseMath.Unified.SchurFeshbachWaveletComb.dyadic_one_fifteenth_susceptibility_bound
      K g_0 gamma_0 chi h_gamma h_chi h_subcrit
  exact ⟨h_tel, h_uv.1, h_uv.2.2, h_susc.1, h_susc.2.2⟩

/-- Metriplectic sub-grid Boltzmann weight factorization and 4-scale generalized Hamiltonian invariance
(`MetriplecticScaleComb` + `HamiltonianScaleComb`):
when coarse-graining splits the fine action `H_k` into the coarse effective action `H_next = H_k - kT * dI_k`
and sub-grid Bregman fluctuation information `dI_k`, the product of the coarse Boltzmann weight
`exp(-H_next / kT)` and sub-grid fluctuation weight `exp(-dI_k)` reconstructs `H_k` identically,
a 4-stage dyadic RG cascade `H0 → H1 → H2 → H3 → H4` conserves `generalizedScaleHamiltonian H4 kT (dI0 + dI1 + dI2 + dI3) = H0`,
and the two-scale quadratic energy decomposes into the Feshbach coarse effective energy plus nonnegative sub-grid Bregman divergence. -/
theorem metriplectic_subgrid_boltzmann_factorization_and_four_scale_invariance
    {H0 H1 H2 H3 H4 kT dI0 dI1 dI2 dI3 a b d z u v : ℝ}
    (hkT : kT ≠ 0)
    (h1 : H1 = H0 - kT * dI0)
    (h2 : H2 = H1 - kT * dI1)
    (h3 : H3 = H2 - kT * dI2)
    (h4 : H4 = H3 - kT * dI3)
    (h_fine_pos : 0 < d - z) :
    (- kT) * Real.log (Real.exp (- H1 / kT) * Real.exp (- dI0)) = H0 ∧
    JesseMath.Unified.MetriplecticScaleComb.generalizedScaleHamiltonian H4 kT (dI0 + dI1 + dI2 + dI3) = H0 ∧
    H0 - H4 = kT * (dI0 + dI1 + dI2 + dI3) ∧
    (a - b ^ 2 / (d - z) - z) * u ^ 2 ≤ (a - z) * u ^ 2 + 2 * b * u * v + (d - z) * v ^ 2 := by
  have h_boltz :=
    JesseMath.Unified.MetriplecticScaleComb.boltzmann_surprisal_subgrid_factorization_invariance
      hkT h1
  have h_four :=
    JesseMath.Unified.MetriplecticScaleComb.four_scale_dyadic_comb_telescoping_invariance
      h1 h2 h3 h4
  have h_slave :=
    JesseMath.Unified.HamiltonianScaleComb.feshbach_bregman_variational_slaving_bridge
      a b d z u v h_fine_pos
  exact ⟨h_boltz, h_four.1, h_four.2, h_slave.2.2⟩

/-- Lower endpoint of a rigorous interval enclosure for a single Schur–Feshbach RG step
`β_next = β_k - Δβ_k + η_k` when `β_k ∈ [β_lo, β_hi]`, `Δβ_k ∈ [dβ_lo, dβ_hi]`, and `|η_k| ≤ η_max`. -/
def intervalSchurFeshbachStepLo (β_lo dβ_hi η_max : ℝ) : ℝ := β_lo - dβ_hi - η_max

/-- Upper endpoint of a rigorous interval enclosure for a single Schur–Feshbach RG step
`β_next = β_k - Δβ_k + η_k` when `β_k ∈ [β_lo, β_hi]`, `Δβ_k ∈ [dβ_lo, dβ_hi]`, and `|η_k| ≤ η_max`. -/
def intervalSchurFeshbachStepHi (β_hi dβ_lo η_max : ℝ) : ℝ := β_hi - dβ_lo + η_max

/-- Route A computer-assisted interval-arithmetic RG crossover to the Dobrushin strong-coupling ball:
starting from a weak-coupling UV interval `β0 ∈ [197/192, 33/32]` where the bare Dobrushin row sum
exceeds unity (`dobrushinRowSum4D β0 ≥ 591/32 > 1`), four certified Schur–Feshbach RG steps with
asymptotic-freedom increment `dβ_i ∈ [191/768, 1/4]` and polymer remainder `|η_i| ≤ 1/768` transport
the coupling into `β4 ∈ [1/48, 1/24]`, where `dobrushinRowSum4D β4 + η_ir ≤ 7/8 < 1` for `η_ir ∈ [0, 1/8]`,
while `Voxelean` 4D `2^4 = 16` cell elimination reduces the `16 × 16 = 256` cell-pair quadratic form
by `255` entries per step and `MasterUnificationToolId.m5ContractiveLyapunovBellman` compiles to
`AgsnfGate4.G3_CurvatureContractiveShunt`. -/
theorem routeA_interval_arithmetic_crossover_to_dobrushin_landing
    {β_lo β_hi dβ_lo dβ_hi η_max β_k Δβ_k η_k : ℝ}
    {β0 β1 β2 β3 β4 dβ0 dβ1 dβ2 dβ3 η0 η1 η2 η3 η_ir : ℝ}
    (h_βk : β_lo ≤ β_k ∧ β_k ≤ β_hi)
    (h_dβk : dβ_lo ≤ Δβ_k ∧ Δβ_k ≤ dβ_hi)
    (h_ηk : |η_k| ≤ η_max)
    (h_β0 : 197 / 192 ≤ β0 ∧ β0 ≤ 33 / 32)
    (h_dβ0 : 191 / 768 ≤ dβ0 ∧ dβ0 ≤ 1 / 4) (h_η0 : |η0| ≤ 1 / 768)
    (h_dβ1 : 191 / 768 ≤ dβ1 ∧ dβ1 ≤ 1 / 4) (h_η1 : |η1| ≤ 1 / 768)
    (h_dβ2 : 191 / 768 ≤ dβ2 ∧ dβ2 ≤ 1 / 4) (h_η2 : |η2| ≤ 1 / 768)
    (h_dβ3 : 191 / 768 ≤ dβ3 ∧ dβ3 ≤ 1 / 4) (h_η3 : |η3| ≤ 1 / 768)
    (h_step1 : β1 = schurFeshbachEffectiveCouplingStep β0 dβ0 η0)
    (h_step2 : β2 = schurFeshbachEffectiveCouplingStep β1 dβ1 η1)
    (h_step3 : β3 = schurFeshbachEffectiveCouplingStep β2 dβ2 η2)
    (h_step4 : β4 = schurFeshbachEffectiveCouplingStep β3 dβ3 η3)
    (h_η_ir : 0 ≤ η_ir ∧ η_ir ≤ 1 / 8) :
    (intervalSchurFeshbachStepLo β_lo dβ_hi η_max ≤
        schurFeshbachEffectiveCouplingStep β_k Δβ_k η_k ∧
      schurFeshbachEffectiveCouplingStep β_k Δβ_k η_k ≤
        intervalSchurFeshbachStepHi β_hi dβ_lo η_max) ∧
    (591 / 32 ≤ dobrushinRowSum4D β0 ∧
      1 / 48 ≤ β4 ∧ β4 ≤ 1 / 24 ∧
      3 / 8 ≤ dobrushinRowSum4D β4 ∧ dobrushinRowSum4D β4 ≤ 3 / 4 ∧
      dobrushinRowSum4D β4 + η_ir ≤ 7 / 8 ∧
      dobrushinRowSum4D β4 + η_ir < 1) ∧
    ((1 + 15) * (1 + 15) - 1 * 1 = 255 ∧
      JesseMath.Jessplexical.JessplexicalAnalysis.masterToolToAgsnfGate
        JesseMath.UnificationTooling.SynthesisOfGreats.MasterUnificationToolId.m5ContractiveLyapunovBellman =
        JesseMath.Jessplexical.JessplexicalAnalysis.AgsnfGate4.G3_CurvatureContractiveShunt) := by
  have h_ηk_bounds := abs_le.mp h_ηk
  have h_η0_bounds := abs_le.mp h_η0
  have h_η1_bounds := abs_le.mp h_η1
  have h_η2_bounds := abs_le.mp h_η2
  have h_η3_bounds := abs_le.mp h_η3
  unfold schurFeshbachEffectiveCouplingStep at h_step1 h_step2 h_step3 h_step4
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨by norm_num, rfl⟩⟩
  · unfold intervalSchurFeshbachStepLo schurFeshbachEffectiveCouplingStep
    linarith
  · unfold intervalSchurFeshbachStepHi schurFeshbachEffectiveCouplingStep
    linarith
  · norm_num [dobrushinRowSum4D, dobrushinIncidenceRowSum4D]
    linarith
  · linarith
  · linarith
  · norm_num [dobrushinRowSum4D, dobrushinIncidenceRowSum4D]
    linarith
  · norm_num [dobrushinRowSum4D, dobrushinIncidenceRowSum4D]
    linarith
  · norm_num [dobrushinRowSum4D, dobrushinIncidenceRowSum4D]
    linarith
  · norm_num [dobrushinRowSum4D, dobrushinIncidenceRowSum4D]
    linarith

/-!
## Milestone M1 (Part B) & M2 Interface: Naive Volume Divergence vs. Link-Pinned Polymer Influence & Inductive Tube Invariance

A naive global bound on the blocked effective action `0 ≤ A_eff(β, V) ≤ 2 * β * |Plaquette (2 * L)| = 192 * L^4 * β`
scales with the 4D torus volume `L^4` and therefore diverges as `L → ∞` at any fixed `β > 0`.
To feed a continuum-compatible RG step uniformly in volume, the multi-plaquette remainder `K_next`
must be controlled in a link-pinned polymer influence norm `linkInfluence x μ ≤ η_next` independent
of `L`, giving a volume-uniform coarse Dobrushin row sum `18 * β_next + η_next`. Under the inductive
interaction-class recurrence `η (k + 1) ≤ θ_block * η k + ε_gen` (`0 ≤ θ_block < 1`, `η 0 = 0`),
the remainder stays inside the closed-form geometric ceiling `η k ≤ ε_gen / (1 - θ_block)` for all
`k : ℕ`, directly discharging the `1 / 768` per-step and `1 / 8` IR remainder hypotheses of
`routeA_interval_arithmetic_crossover_to_dobrushin_landing` whenever `ε_gen / (1 - θ_block) ≤ 1 / 768`.
-/

/-- Negative control (`M1` volume-uniformity obstruction for naive global action bounds):
the global upper bound `2 * β * (6 * (2 * L)^4) = 192 * L^4 * β` on the fine `2 * L` torus
grows without bound as `L` increases for any `β > 0`, exceeding any threshold `M` once
`L ≥ max 1 (M / (192 * β))`. -/
theorem naive_global_block_action_bound_diverges_with_volume
    {β M L_real : ℝ} (hβ : 0 < β) (hL_one : 1 ≤ L_real)
    (hL_large : M / (192 * β) ≤ L_real) :
    2 * β * (6 * (2 * L_real) ^ 4) = 192 * L_real ^ 4 * β ∧
    M ≤ 192 * L_real ^ 4 * β := by
  refine ⟨by ring, ?_⟩
  have h192β : 0 < 192 * β := by linarith
  have hM_le : M ≤ L_real * (192 * β) := (div_le_iff₀ h192β).mp hL_large
  have hL_pow : L_real ≤ L_real ^ 4 := by
    nlinarith [sq_nonneg L_real, sq_nonneg (L_real - 1)]
  nlinarith

/-- Volume-uniform link-pinned polymer single-link oscillation contract on the coarse lattice
`GaugeConfig L`: bounds the local single-link oscillation of the extracted non-Wilson remainder
`K_next` at every coarse link `(x, μ)` by `linkInfluence x μ` and by a volume-independent constant
`η_next`. Note: for multi-link polymers (`k_supp ≥ 3`), `coarseTotalDobrushinRowSum` is a scalar
single-link oscillation envelope; bounding the true off-diagonal pairwise conditional-TV Dobrushin
row sum requires either two-link mixed-difference cross-ratio bounds or `(k_supp - 1)` support-multiplicity
weighting (`PairwiseConditionalDobrushinContract`). -/
structure CoarseRemainderInfluenceContract (L : ℕ) [NeZero L] where
  β_next : ℝ
  K_next : GaugeConfig L → ℝ
  linkInfluence : Lattice4D L → Fin 4 → ℝ
  η_next : ℝ
  h_β_nonneg : 0 ≤ β_next
  h_η_nonneg : 0 ≤ η_next
  h_influence_nonneg : ∀ (x : Lattice4D L) (μ : Fin 4), 0 ≤ linkInfluence x μ
  h_osc_K_next : ∀ (x : Lattice4D L) (μ : Fin 4) (V : GaugeConfig L) (g1 g2 : SU2),
    |K_next (updateGaugeLink L V x μ g1) - K_next (updateGaugeLink L V x μ g2)| ≤ linkInfluence x μ
  h_influence_uniform : ∀ (x : Lattice4D L) (μ : Fin 4), linkInfluence x μ ≤ η_next

/-- Scalar single-link oscillation envelope at link `(x, μ)` combining the single-plaquette Wilson
part `dobrushinRowSum4D c.β_next = 18 * c.β_next` with the single-link remainder oscillation bound
`c.linkInfluence x μ`. -/
def coarseTotalDobrushinRowSum {L : ℕ} [NeZero L]
    (c : CoarseRemainderInfluenceContract L) (x : Lattice4D L) (μ : Fin 4) : ℝ :=
  dobrushinRowSum4D c.β_next + c.linkInfluence x μ

/-- Volume-uniform scalar single-link oscillation envelope bound (`M1`/`M2` link-oscillation theorem):
for every coarse lattice size `L` and every coarse link `(x, μ)`, `coarseTotalDobrushinRowSum c x μ`
is nonnegative, bounded uniformly in `L` by `18 * c.β_next + c.η_next`, strictly below `1`
whenever `18 * c.β_next + c.η_next < 1`, and `c.K_next`'s single-link oscillation at `(x, μ)`
is bounded by `c.linkInfluence x μ` and `c.η_next`. -/
theorem coarseTotalDobrushinRowSum_uniform_bound {L : ℕ} [NeZero L]
    (c : CoarseRemainderInfluenceContract L) (x : Lattice4D L) (μ : Fin 4) :
    0 ≤ coarseTotalDobrushinRowSum c x μ ∧
    coarseTotalDobrushinRowSum c x μ ≤ 18 * c.β_next + c.η_next ∧
    (18 * c.β_next + c.η_next < 1 → coarseTotalDobrushinRowSum c x μ < 1) ∧
    (∀ (V : GaugeConfig L) (g1 g2 : SU2),
      |c.K_next (updateGaugeLink L V x μ g1) - c.K_next (updateGaugeLink L V x μ g2)| ≤
        c.linkInfluence x μ ∧
      |c.K_next (updateGaugeLink L V x μ g1) - c.K_next (updateGaugeLink L V x μ g2)| ≤
        c.η_next) := by
  have hβ := c.h_β_nonneg
  have h_inf_lo := c.h_influence_nonneg x μ
  have h_inf_hi := c.h_influence_uniform x μ
  dsimp [coarseTotalDobrushinRowSum, dobrushinRowSum4D, dobrushinIncidenceRowSum4D]
  refine ⟨by linarith, by linarith, fun h_lt => by linarith, fun V g1 g2 => ?_⟩
  have h_osc := c.h_osc_K_next x μ V g1 g2
  exact ⟨h_osc, le_trans h_osc h_inf_hi⟩

/-- Closed-form geometric envelope `ε_gen * (1 - θ_block^k) / (1 - θ_block)` for the `k`-step
iterated polymer remainder influence under contraction factor `θ_block` and per-step generation `ε_gen`. -/
noncomputable def iteratedRemainderInfluenceEnvelope (θ_block ε_gen : ℝ) (k : ℕ) : ℝ :=
  ε_gen * (1 - θ_block ^ k) / (1 - θ_block)

/-- Uniform asymptotic ceiling `ε_gen / (1 - θ_block)` bounding `iteratedRemainderInfluenceEnvelope`
for all `k : ℕ`. -/
noncomputable def asymptoticRemainderInfluenceCeiling (θ_block ε_gen : ℝ) : ℝ :=
  ε_gen / (1 - θ_block)

/-- Inductive multi-step interaction-class invariance and Route A threshold discharge (`M1`/`M2`):
if a sequence of coarse remainder influence norms `η : ℕ → ℝ` satisfies `η 0 = 0`, `0 ≤ η k`, and
the contractive polymer recurrence `η (k + 1) ≤ θ_block * η k + ε_gen` with `0 ≤ θ_block < 1` and
`0 ≤ ε_gen`, then for every step `k : ℕ`:
1. `η k ≤ iteratedRemainderInfluenceEnvelope θ_block ε_gen k`,
2. `iteratedRemainderInfluenceEnvelope θ_block ε_gen k ≤ asymptoticRemainderInfluenceCeiling θ_block ε_gen`,
3. `η k ≤ asymptoticRemainderInfluenceCeiling θ_block ε_gen`, and
4. whenever `asymptoticRemainderInfluenceCeiling θ_block ε_gen ≤ 1 / 768`, every step `k` satisfies
   `|η k| ≤ 1 / 768` and `0 ≤ η k ∧ η k ≤ 1 / 8`, directly discharging the remainder hypotheses of
   `routeA_interval_arithmetic_crossover_to_dobrushin_landing`. -/
theorem inductive_interaction_class_remainder_envelope_and_routeA_feed
    (η : ℕ → ℝ) {θ_block ε_gen : ℝ}
    (hθ_nonneg : 0 ≤ θ_block) (hθ_lt_one : θ_block < 1)
    (hε_nonneg : 0 ≤ ε_gen)
    (hη_zero : η 0 = 0)
    (hη_nonneg : ∀ k : ℕ, 0 ≤ η k)
    (hη_step : ∀ k : ℕ, η (k + 1) ≤ θ_block * η k + ε_gen) :
    (∀ k : ℕ, η k ≤ iteratedRemainderInfluenceEnvelope θ_block ε_gen k) ∧
    (∀ k : ℕ,
      iteratedRemainderInfluenceEnvelope θ_block ε_gen k ≤
        asymptoticRemainderInfluenceCeiling θ_block ε_gen) ∧
    (∀ k : ℕ, η k ≤ asymptoticRemainderInfluenceCeiling θ_block ε_gen) ∧
    (asymptoticRemainderInfluenceCeiling θ_block ε_gen ≤ 1 / 768 →
      ∀ k : ℕ, |η k| ≤ 1 / 768 ∧ 0 ≤ η k ∧ η k ≤ 1 / 8) := by
  have h_one_sub_pos : 0 < 1 - θ_block := by linarith
  have h_one_sub_ne : 1 - θ_block ≠ 0 := ne_of_gt h_one_sub_pos
  have h_env : ∀ k : ℕ, η k ≤ iteratedRemainderInfluenceEnvelope θ_block ε_gen k := by
    intro k
    induction k with
    | zero =>
      dsimp [iteratedRemainderInfluenceEnvelope]
      rw [hη_zero, pow_zero, sub_self, mul_zero, zero_div]
    | succ k ih =>
      have h_rec := hη_step k
      have h_mul : θ_block * η k ≤ θ_block * iteratedRemainderInfluenceEnvelope θ_block ε_gen k :=
        mul_le_mul_of_nonneg_left ih hθ_nonneg
      have h_alg :
          θ_block * iteratedRemainderInfluenceEnvelope θ_block ε_gen k + ε_gen =
            iteratedRemainderInfluenceEnvelope θ_block ε_gen (k + 1) := by
        dsimp [iteratedRemainderInfluenceEnvelope]
        field_simp [h_one_sub_ne]
        ring
      linarith
  have h_ceil : ∀ k : ℕ,
      iteratedRemainderInfluenceEnvelope θ_block ε_gen k ≤
        asymptoticRemainderInfluenceCeiling θ_block ε_gen := by
    intro k
    dsimp [iteratedRemainderInfluenceEnvelope, asymptoticRemainderInfluenceCeiling]
    have h_pow_nonneg : 0 ≤ θ_block ^ k := pow_nonneg hθ_nonneg k
    have h_num_le : ε_gen * (1 - θ_block ^ k) ≤ ε_gen := by nlinarith
    exact div_le_div_of_nonneg_right h_num_le (le_of_lt h_one_sub_pos)
  have h_all : ∀ k : ℕ, η k ≤ asymptoticRemainderInfluenceCeiling θ_block ε_gen :=
    fun k => le_trans (h_env k) (h_ceil k)
  refine ⟨h_env, h_ceil, h_all, ?_⟩
  intro h_bound k
  have hk_lo := hη_nonneg k
  have hk_hi : η k ≤ 1 / 768 := le_trans (h_all k) h_bound
  refine ⟨abs_le.mpr ⟨by linarith, hk_hi⟩, hk_lo, by linarith⟩

/-- Adversarial negative control (`M2` detached-influence rejection): any candidate remainder
`K_bad` whose single-link oscillation at some link `(x, μ)` between `g1` and `g2` exceeds a claimed
uniform ceiling `η_claim` cannot be packaged into a `CoarseRemainderInfluenceContract L` with
`c.K_next = K_bad` and `c.η_next = η_claim`. -/
theorem detached_linkInfluence_rejected_by_oscillation_bound {L : ℕ} [NeZero L]
    (K_bad : GaugeConfig L → ℝ) (η_claim : ℝ)
    (x : Lattice4D L) (μ : Fin 4) (V : GaugeConfig L) (g1 g2 : SU2)
    (h_exceeds :
      η_claim < |K_bad (updateGaugeLink L V x μ g1) - K_bad (updateGaugeLink L V x μ g2)|)
    (c : CoarseRemainderInfluenceContract L) :
    ¬ (c.K_next = K_bad ∧ c.η_next = η_claim) := by
  rintro ⟨hK, hη⟩
  have h_osc := c.h_osc_K_next x μ V g1 g2
  have h_unif := c.h_influence_uniform x μ
  rw [hK] at h_osc
  rw [hη] at h_unif
  linarith

/-- Explicit finite polymer-sum expansion of a coarse non-Wilson remainder
`K_next(V) = ∑_{i : Fin M_poly} w_i * Φ_i(V)` on `GaugeConfig L`. -/
def polymerSumRemainder (L : ℕ) {M_poly : ℕ}
    (w : Fin M_poly → ℝ) (Φ : Fin M_poly → GaugeConfig L → ℝ) (V : GaugeConfig L) : ℝ :=
  ∑ i : Fin M_poly, w i * Φ i V

/-- Link-pinned polymer influence bound `∑_{i : Fin M_poly} |w_i| * a_osc(i, x, μ)` derived from
the polymer weights `w` and per-polymer single-link oscillation bounds `a_osc`. -/
def derivedPolymerLinkInfluence {L : ℕ} {M_poly : ℕ}
    (w : Fin M_poly → ℝ) (a_osc : Fin M_poly → Lattice4D L → Fin 4 → ℝ)
    (x : Lattice4D L) (μ : Fin 4) : ℝ :=
  ∑ i : Fin M_poly, |w i| * a_osc i x μ

/-- Constructive polymer-sum single-link oscillation bound and `CoarseRemainderInfluenceContract L`
realization (`M2` conditional finite-polymer oscillation theorem): given a finite polymer sum
`polymerSumRemainder L w Φ`, supplied per-term single-link oscillation bounds `a_osc i x μ ≥ 0`,
and a supplied uniform sum bound `h_sum_le : derivedPolymerLinkInfluence w a_osc x μ ≤ η_derived`,
the triangle inequality bounds the single-link oscillation of `polymerSumRemainder L w Φ` by
`derivedPolymerLinkInfluence w a_osc x μ ≤ η_derived` and constructs a `CoarseRemainderInfluenceContract L`. -/
theorem derived_polymer_linkInfluence_bounds_oscillation_and_constructs_contract
    {L : ℕ} [NeZero L] {M_poly : ℕ}
    {β_next η_derived : ℝ}
    (w : Fin M_poly → ℝ)
    (Φ : Fin M_poly → GaugeConfig L → ℝ)
    (a_osc : Fin M_poly → Lattice4D L → Fin 4 → ℝ)
    (hβ : 0 ≤ β_next)
    (hη : 0 ≤ η_derived)
    (ha_nonneg : ∀ (i : Fin M_poly) (x : Lattice4D L) (μ : Fin 4), 0 ≤ a_osc i x μ)
    (h_term_osc : ∀ (i : Fin M_poly) (x : Lattice4D L) (μ : Fin 4)
      (V : GaugeConfig L) (g1 g2 : SU2),
      |Φ i (updateGaugeLink L V x μ g1) - Φ i (updateGaugeLink L V x μ g2)| ≤ a_osc i x μ)
    (h_sum_le : ∀ (x : Lattice4D L) (μ : Fin 4),
      derivedPolymerLinkInfluence w a_osc x μ ≤ η_derived) :
    (∀ (x : Lattice4D L) (μ : Fin 4), 0 ≤ derivedPolymerLinkInfluence w a_osc x μ) ∧
    (∀ (x : Lattice4D L) (μ : Fin 4) (V : GaugeConfig L) (g1 g2 : SU2),
      |polymerSumRemainder L w Φ (updateGaugeLink L V x μ g1) -
          polymerSumRemainder L w Φ (updateGaugeLink L V x μ g2)| ≤
        derivedPolymerLinkInfluence w a_osc x μ ∧
      |polymerSumRemainder L w Φ (updateGaugeLink L V x μ g1) -
          polymerSumRemainder L w Φ (updateGaugeLink L V x μ g2)| ≤ η_derived) ∧
    ∃ c : CoarseRemainderInfluenceContract L,
      c.β_next = β_next ∧
      c.K_next = polymerSumRemainder L w Φ ∧
      c.linkInfluence = derivedPolymerLinkInfluence w a_osc ∧
      c.η_next = η_derived := by
  have h_inf_nonneg : ∀ (x : Lattice4D L) (μ : Fin 4), 0 ≤ derivedPolymerLinkInfluence w a_osc x μ := by
    intro x μ
    dsimp [derivedPolymerLinkInfluence]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg (w i)) (ha_nonneg i x μ))
  have h_osc : ∀ (x : Lattice4D L) (μ : Fin 4) (V : GaugeConfig L) (g1 g2 : SU2),
      |polymerSumRemainder L w Φ (updateGaugeLink L V x μ g1) -
          polymerSumRemainder L w Φ (updateGaugeLink L V x μ g2)| ≤
        derivedPolymerLinkInfluence w a_osc x μ := by
    intro x μ V g1 g2
    dsimp [polymerSumRemainder, derivedPolymerLinkInfluence]
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ i : Fin M_poly,
          (w i * Φ i (updateGaugeLink L V x μ g1) -
            w i * Φ i (updateGaugeLink L V x μ g2))|
        ≤ ∑ i : Fin M_poly,
            |w i * Φ i (updateGaugeLink L V x μ g1) -
              w i * Φ i (updateGaugeLink L V x μ g2)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin M_poly, |w i| * a_osc i x μ := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [← mul_sub, abs_mul]
        exact mul_le_mul_of_nonneg_left (h_term_osc i x μ V g1 g2) (abs_nonneg (w i))
  refine ⟨h_inf_nonneg,
    fun x μ V g1 g2 => ⟨h_osc x μ V g1 g2, le_trans (h_osc x μ V g1 g2) (h_sum_le x μ)⟩,
    ⟨{ β_next := β_next
       K_next := polymerSumRemainder L w Φ
       linkInfluence := derivedPolymerLinkInfluence w a_osc
       η_next := η_derived
       h_β_nonneg := hβ
       h_η_nonneg := hη
       h_influence_nonneg := h_inf_nonneg
       h_osc_K_next := h_osc
       h_influence_uniform := h_sum_le },
     rfl, rfl, rfl, rfl⟩⟩

/-- Two-point conditional Gibbs probability `p1 / (p1 + p2)` for positive unnormalized single-link
conditional Boltzmann weights `p1 = exp(-A(V[e := g1]))` and `p2 = exp(-A(V[e := g2]))`. -/
noncomputable def binaryConditionalGibbsProb (p1 p2 : ℝ) : ℝ :=
  p1 / (p1 + p2)

/-- Pairwise conditional total-variation distance
`|binaryConditionalGibbsProb p1 p2 - binaryConditionalGibbsProb q1 q2|` between two-point
conditional Gibbs distributions at link `e` when a partner link `e' ≠ e` is flipped (`V35-WILSON-DOBRUSHIN-01`
remediation). -/
noncomputable def binaryConditionalTV (p1 p2 q1 q2 : ℝ) : ℝ :=
  |binaryConditionalGibbsProb p1 p2 - binaryConditionalGibbsProb q1 q2|

/-- Adversarial 4-link parity counterexample (`V35-WILSON-DOBRUSHIN-01` negative control):
on `GaugeConfig 1` (`4` links), a 4-link parity interaction with `K = 0` on even parity and
`K = log (7 / 3)` on odd parity at `β_next = 0` has:
1. Single-link oscillation `log (7 / 3) < 1` at every link (since `7 / 3 = 63 / 27 < 64 / 27 = (1 + 1 / 3)^3 ≤ exp 1`),
2. Exact binary conditional probabilities `7 / 10` and `3 / 10` under fair binary conditioning
   (`w_even = 1`, `w_odd = 3 / 7`), giving pairwise conditional-TV influence `2 / 5` for each of
   the `3` partner links, and
3. Actual 3-neighbor conditional-TV Dobrushin row sum `3 * (2 / 5) = 6 / 5 > 1 > log (7 / 3)`.
This proves in the Lean kernel why single-link action oscillation alone does not upper-bound the
pairwise conditional-TV Dobrushin row sum when a remainder term couples `k ≥ 3` links simultaneously. -/
theorem fourLinkParityRemainder_singleLinkOscillation_lt_one_but_dobrushinRowSum_gt_one :
    0 < Real.log (7 / 3 : ℝ) ∧
    Real.log (7 / 3 : ℝ) < 1 ∧
    binaryConditionalGibbsProb 1 (3 / 7) = 7 / 10 ∧
    binaryConditionalGibbsProb (3 / 7) 1 = 3 / 10 ∧
    binaryConditionalTV 1 (3 / 7) (3 / 7) 1 = 2 / 5 ∧
    3 * binaryConditionalTV 1 (3 / 7) (3 / 7) 1 = 6 / 5 ∧
    1 < 3 * binaryConditionalTV 1 (3 / 7) (3 / 7) 1 ∧
    Real.log (7 / 3 : ℝ) < 3 * binaryConditionalTV 1 (3 / 7) (3 / 7) 1 := by
  have h_log_pos : 0 < Real.log (7 / 3 : ℝ) :=
    Real.log_pos (by norm_num)
  have h_one_third : (4 / 3 : ℝ) ≤ Real.exp (1 / 3 : ℝ) := by
    have h := Real.add_one_le_exp (1 / 3 : ℝ)
    linarith
  have h_cube : (4 / 3 : ℝ) ^ 3 ≤ (Real.exp (1 / 3 : ℝ)) ^ 3 :=
    pow_le_pow_left₀ (by norm_num) h_one_third 3
  have h_exp_cube : (Real.exp (1 / 3 : ℝ)) ^ 3 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h_seven_thirds_lt_exp : (7 / 3 : ℝ) < Real.exp 1 := by
    have h_rat : (7 / 3 : ℝ) < (4 / 3 : ℝ) ^ 3 := by norm_num
    linarith
  have h_log_lt_one : Real.log (7 / 3 : ℝ) < 1 := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (by norm_num) h_seven_thirds_lt_exp
  have h_p1 : binaryConditionalGibbsProb 1 (3 / 7) = 7 / 10 := by
    unfold binaryConditionalGibbsProb
    norm_num
  have h_p2 : binaryConditionalGibbsProb (3 / 7) 1 = 3 / 10 := by
    unfold binaryConditionalGibbsProb
    norm_num
  have h_tv : binaryConditionalTV 1 (3 / 7) (3 / 7) 1 = 2 / 5 := by
    unfold binaryConditionalTV
    rw [h_p1, h_p2]
    norm_num
  have h_row : 3 * binaryConditionalTV 1 (3 / 7) (3 / 7) 1 = 6 / 5 := by
    rw [h_tv]
    norm_num
  exact ⟨h_log_pos, h_log_lt_one, h_p1, h_p2, h_tv, h_row, by linarith, by linarith⟩

/-- Genuine pairwise conditional-TV Dobrushin bound from two-link mixed-difference cross-ratios
(`V35-WILSON-DOBRUSHIN-01` positive resolution):
for any positive unnormalized single-link conditional weights `0 < p1, p2, q1, q2` whose cross-ratio
is controlled by the two-link mixed second difference `γ ≥ 0` via
`q1 * p2 * exp(-γ) ≤ p1 * q2 ∧ p1 * q2 ≤ q1 * p2 * exp(γ)`, the conditional probability difference
equals `(p1 * q2 - p2 * q1) / ((p1 + p2) * (q1 + q2))` and the pairwise conditional-TV distance
satisfies `binaryConditionalTV p1 p2 q1 q2 ≤ exp(γ) - 1`. -/
theorem pairwise_crossRatio_bounds_binaryConditionalTV
    {p1 p2 q1 q2 γ : ℝ}
    (hp1 : 0 < p1) (hp2 : 0 < p2) (hq1 : 0 < q1) (hq2 : 0 < q2)
    (hγ : 0 ≤ γ)
    (h_cross_lo : q1 * p2 * Real.exp (-γ) ≤ p1 * q2)
    (h_cross_hi : p1 * q2 ≤ q1 * p2 * Real.exp γ) :
    binaryConditionalGibbsProb p1 p2 - binaryConditionalGibbsProb q1 q2 =
      (p1 * q2 - p2 * q1) / ((p1 + p2) * (q1 + q2)) ∧
    0 ≤ binaryConditionalTV p1 p2 q1 q2 ∧
    binaryConditionalTV p1 p2 q1 q2 ≤ Real.exp γ - 1 := by
  have hp_sum : 0 < p1 + p2 := add_pos hp1 hp2
  have hq_sum : 0 < q1 + q2 := add_pos hq1 hq2
  have h_denom_pos : 0 < (p1 + p2) * (q1 + q2) := mul_pos hp_sum hq_sum
  have h_diff :
      binaryConditionalGibbsProb p1 p2 - binaryConditionalGibbsProb q1 q2 =
        (p1 * q2 - p2 * q1) / ((p1 + p2) * (q1 + q2)) := by
    unfold binaryConditionalGibbsProb
    have hp_ne : p1 + p2 ≠ 0 := ne_of_gt hp_sum
    have hq_ne : q1 + q2 ≠ 0 := ne_of_gt hq_sum
    field_simp [hp_ne, hq_ne]
    ring
  have h_exp_prod : Real.exp (-γ) * Real.exp γ = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h_exp_symm : 1 - Real.exp (-γ) ≤ Real.exp γ - 1 := by
    have h_sq : 0 ≤ Real.exp (-γ) * (Real.exp γ - 1) ^ 2 :=
      mul_nonneg (le_of_lt (Real.exp_pos (-γ))) (sq_nonneg _)
    have h_expand :
        (Real.exp γ - 1) - (1 - Real.exp (-γ)) =
          Real.exp (-γ) * (Real.exp γ - 1) ^ 2 := by
      calc
        (Real.exp γ - 1) - (1 - Real.exp (-γ))
          = 1 * Real.exp γ - 2 * 1 + Real.exp (-γ) := by ring
        _ = (Real.exp (-γ) * Real.exp γ) * Real.exp γ -
              2 * (Real.exp (-γ) * Real.exp γ) + Real.exp (-γ) := by
            rw [h_exp_prod]
        _ = Real.exp (-γ) * (Real.exp γ - 1) ^ 2 := by ring
    linarith
  have h_exp_ge_one : 1 ≤ Real.exp γ := by
    linarith [Real.add_one_le_exp γ, hγ]
  have h_p2q1_le_denom : p2 * q1 ≤ (p1 + p2) * (q1 + q2) := by
    nlinarith
  have h_num_upper : p1 * q2 - p2 * q1 ≤ (p1 + p2) * (q1 + q2) * (Real.exp γ - 1) := by
    have h1 : p1 * q2 - p2 * q1 ≤ p2 * q1 * (Real.exp γ - 1) := by linarith
    have h2 : p2 * q1 * (Real.exp γ - 1) ≤ (p1 + p2) * (q1 + q2) * (Real.exp γ - 1) :=
      mul_le_mul_of_nonneg_right h_p2q1_le_denom (by linarith)
    exact le_trans h1 h2
  have h_num_lower : -((p1 + p2) * (q1 + q2) * (Real.exp γ - 1)) ≤ p1 * q2 - p2 * q1 := by
    have h1 : p2 * q1 - p1 * q2 ≤ p2 * q1 * (1 - Real.exp (-γ)) := by linarith
    have h2 : p2 * q1 * (1 - Real.exp (-γ)) ≤ p2 * q1 * (Real.exp γ - 1) :=
      mul_le_mul_of_nonneg_left h_exp_symm (le_of_lt (mul_pos hp2 hq1))
    have h3 : p2 * q1 * (Real.exp γ - 1) ≤ (p1 + p2) * (q1 + q2) * (Real.exp γ - 1) :=
      mul_le_mul_of_nonneg_right h_p2q1_le_denom (by linarith)
    linarith
  have h_abs_num : |p1 * q2 - p2 * q1| ≤ (p1 + p2) * (q1 + q2) * (Real.exp γ - 1) :=
    abs_le.mpr ⟨h_num_lower, h_num_upper⟩
  have h_tv_le : binaryConditionalTV p1 p2 q1 q2 ≤ Real.exp γ - 1 := by
    unfold binaryConditionalTV
    rw [h_diff, abs_div, abs_of_pos h_denom_pos, div_le_iff₀ h_denom_pos]
    linarith
  exact ⟨h_diff, abs_nonneg _, h_tv_le⟩

/-- Truthful coordinate-support predicate for a coarse interaction functional
`Φ : GaugeConfig L → ℝ` on a finite link set `S : Finset (Link L)` (`V36-PAIRWISE-SUPPORT-UNBOUND`
remediation): updating any link `⟨x, μ⟩ ∉ S` leaves `Φ` invariant across all background
configurations `V` and link matrices `g1, g2 : SU2`. -/
def IsSupportedOnLinkSet {L : ℕ} (Φ : GaugeConfig L → ℝ) (S : Finset (Link L)) : Prop :=
  ∀ (x : Lattice4D L) (μ : Fin 4), ⟨x, μ⟩ ∉ S →
    ∀ (V : GaugeConfig L) (g1 g2 : SU2),
      Φ (updateGaugeLink L V x μ g1) = Φ (updateGaugeLink L V x μ g2)

/-- Support-multiplicity-weighted polymer oscillation envelope
`∑_{i : Fin M_poly} (k_supp i - 1) * (|w_i| * a_osc(i, x, μ))`:
a polymer `Φ_i` truthfully supported on `supp_i` coarse links (`|supp_i| ≤ k_supp i`) that
oscillates by at most `a_osc i x μ` at `(x, μ)` contributes at most `k_supp i - 1` partner-link
multiplicity terms (`(x', μ') ≠ (x, μ)`) to the support-weighted oscillation envelope
(`V35-WILSON-DOBRUSHIN-01` / `V36-PAIRWISE-SUPPORT-UNBOUND` remediation). -/
def supportMultiplicityPolymerRowInfluence {L : ℕ} {M_poly : ℕ}
    (w : Fin M_poly → ℝ) (k_supp : Fin M_poly → ℕ)
    (a_osc : Fin M_poly → Lattice4D L → Fin 4 → ℝ)
    (x : Lattice4D L) (μ : Fin 4) : ℝ :=
  ∑ i : Fin M_poly, ((k_supp i - 1 : ℕ) : ℝ) * (|w i| * a_osc i x μ)

/-- Truthful-support-weighted polymer oscillation envelope contract on `GaugeConfig L`
(`V36-PAIRWISE-SUPPORT-UNBOUND` remediation): strengthens `CoarseRemainderInfluenceContract L`
by binding `K_next` to a finite polymer expansion `Φ_poly` with explicit coordinate support sets
`supp_poly i : Finset (Link L)`, requiring `IsSupportedOnLinkSet (Φ_poly i) (supp_poly i)` and
`(supp_poly i).card ≤ k_supp i` alongside the support-weighted oscillation envelope
`pairwiseRowInfluence x μ ≤ η_pairwise`. -/
structure PairwiseConditionalDobrushinContract (L : ℕ) [NeZero L]
    extends CoarseRemainderInfluenceContract L where
  M_poly : ℕ
  w_poly : Fin M_poly → ℝ
  supp_poly : Fin M_poly → Finset (Link L)
  k_supp : Fin M_poly → ℕ
  Φ_poly : Fin M_poly → GaugeConfig L → ℝ
  a_osc : Fin M_poly → Lattice4D L → Fin 4 → ℝ
  pairwiseRowInfluence : Lattice4D L → Fin 4 → ℝ
  η_pairwise : ℝ
  h_K_decomp : K_next = polymerSumRemainder L w_poly Φ_poly
  h_link_decomp : linkInfluence = derivedPolymerLinkInfluence w_poly a_osc
  h_pair_decomp : pairwiseRowInfluence = supportMultiplicityPolymerRowInfluence w_poly k_supp a_osc
  hk_ge_two : ∀ i : Fin M_poly, 2 ≤ k_supp i
  h_truthful_supp : ∀ i : Fin M_poly, IsSupportedOnLinkSet (Φ_poly i) (supp_poly i)
  hk_card : ∀ i : Fin M_poly, (supp_poly i).card ≤ k_supp i
  h_single_le_pairwise : ∀ (x : Lattice4D L) (μ : Fin 4),
    linkInfluence x μ ≤ pairwiseRowInfluence x μ
  h_pairwise_uniform : ∀ (x : Lattice4D L) (μ : Fin 4),
    pairwiseRowInfluence x μ ≤ η_pairwise

/-- Truthful-support-weighted polymer oscillation envelope theorem (`V35-WILSON-DOBRUSHIN-01` /
`V36-PAIRWISE-SUPPORT-UNBOUND` positive resolution):
1. Whenever every polymer `Φ i` in a finite expansion is truthfully supported on `supp i`
   (`IsSupportedOnLinkSet (Φ i) (supp i)`) with `2 ≤ k_supp i` and `(supp i).card ≤ k_supp i`,
   the support-multiplicity-weighted envelope `supportMultiplicityPolymerRowInfluence w k_supp a_osc x μ`
   dominates the single-link oscillation bound `derivedPolymerLinkInfluence w a_osc x μ`,
2. Under a uniform support-weighted sum bound `≤ η_pairwise`, it constructively inhabits
   `PairwiseConditionalDobrushinContract L` with verified support cardinality `(supp i).card ≤ k_supp i`, and
3. On the 4-link parity counterexample (whose truthful support cardinality is `4`, proved below in
   `fourLinkParityIndicator_truthful_support_card_eq_four_and_rejects_two`), `(k_supp - 1) = 3`
   gives `3 * log (7 / 3) > 6 / 5 > 1`, strictly dominating the actual 3-neighbor binary
   conditional-TV row sum `6 / 5` and refusing to falsely certify `< 1`. -/
theorem supportMultiplicity_polymer_bounds_pairwise_dobrushin_row_sum
    {L : ℕ} [NeZero L] {M_poly : ℕ}
    {β_next η_pairwise : ℝ}
    (w : Fin M_poly → ℝ)
    (supp : Fin M_poly → Finset (Link L))
    (k_supp : Fin M_poly → ℕ)
    (Φ : Fin M_poly → GaugeConfig L → ℝ)
    (a_osc : Fin M_poly → Lattice4D L → Fin 4 → ℝ)
    (hβ : 0 ≤ β_next)
    (hη_pair : 0 ≤ η_pairwise)
    (hk_ge_two : ∀ i : Fin M_poly, 2 ≤ k_supp i)
    (h_supp : ∀ i : Fin M_poly, IsSupportedOnLinkSet (Φ i) (supp i))
    (hk_card : ∀ i : Fin M_poly, (supp i).card ≤ k_supp i)
    (ha_nonneg : ∀ (i : Fin M_poly) (x : Lattice4D L) (μ : Fin 4), 0 ≤ a_osc i x μ)
    (h_term_osc : ∀ (i : Fin M_poly) (x : Lattice4D L) (μ : Fin 4)
      (V : GaugeConfig L) (g1 g2 : SU2),
      |Φ i (updateGaugeLink L V x μ g1) - Φ i (updateGaugeLink L V x μ g2)| ≤ a_osc i x μ)
    (h_pair_sum_le : ∀ (x : Lattice4D L) (μ : Fin 4),
      supportMultiplicityPolymerRowInfluence w k_supp a_osc x μ ≤ η_pairwise) :
    (∀ (x : Lattice4D L) (μ : Fin 4),
      derivedPolymerLinkInfluence w a_osc x μ ≤
        supportMultiplicityPolymerRowInfluence w k_supp a_osc x μ) ∧
    (∃ c_pair : PairwiseConditionalDobrushinContract L,
      c_pair.β_next = β_next ∧
      c_pair.K_next = polymerSumRemainder L w Φ ∧
      c_pair.linkInfluence = derivedPolymerLinkInfluence w a_osc ∧
      c_pair.pairwiseRowInfluence = supportMultiplicityPolymerRowInfluence w k_supp a_osc ∧
      c_pair.η_pairwise = η_pairwise ∧
      (∀ i : Fin c_pair.M_poly,
        IsSupportedOnLinkSet (c_pair.Φ_poly i) (c_pair.supp_poly i) ∧
        (c_pair.supp_poly i).card ≤ c_pair.k_supp i)) ∧
    (6 / 5 : ℝ) < ((4 - 1 : ℕ) : ℝ) * Real.log (7 / 3 : ℝ) := by
  have h_single_le_pair : ∀ (x : Lattice4D L) (μ : Fin 4),
      derivedPolymerLinkInfluence w a_osc x μ ≤
        supportMultiplicityPolymerRowInfluence w k_supp a_osc x μ := by
    intro x μ
    dsimp [derivedPolymerLinkInfluence, supportMultiplicityPolymerRowInfluence]
    refine Finset.sum_le_sum fun i _ => ?_
    have hk_one : 1 ≤ k_supp i - 1 := by
      have := hk_ge_two i
      omega
    have hk_real : (1 : ℝ) ≤ ((k_supp i - 1 : ℕ) : ℝ) := Nat.one_le_cast.mpr hk_one
    have h_term_nonneg : 0 ≤ |w i| * a_osc i x μ :=
      mul_nonneg (abs_nonneg (w i)) (ha_nonneg i x μ)
    have h_mul := mul_le_mul_of_nonneg_right hk_real h_term_nonneg
    linarith
  have h_single_sum_le : ∀ (x : Lattice4D L) (μ : Fin 4),
      derivedPolymerLinkInfluence w a_osc x μ ≤ η_pairwise :=
    fun x μ => le_trans (h_single_le_pair x μ) (h_pair_sum_le x μ)
  have h_base :=
    derived_polymer_linkInfluence_bounds_oscillation_and_constructs_contract
      w Φ a_osc hβ hη_pair ha_nonneg h_term_osc h_single_sum_le
  have h_parity_bound : (6 / 5 : ℝ) < ((4 - 1 : ℕ) : ℝ) * Real.log (7 / 3 : ℝ) := by
    have h_exp_lt : Real.exp (2 / 5 : ℝ) < (7 / 3 : ℝ) := by
      have h_inv : (3 / 5 : ℝ) ≤ Real.exp (-(2 / 5 : ℝ)) := by
        have h := Real.add_one_le_exp (-(2 / 5 : ℝ))
        linarith
      have h_prod : Real.exp (2 / 5 : ℝ) * Real.exp (-(2 / 5 : ℝ)) = 1 := by
        rw [← Real.exp_add]
        norm_num
      have h_le : Real.exp (2 / 5 : ℝ) * (3 / 5 : ℝ) ≤ 1 := by
        have := mul_le_mul_of_nonneg_left h_inv (le_of_lt (Real.exp_pos (2 / 5 : ℝ)))
        linarith
      linarith
    have h_log_gt : (2 / 5 : ℝ) < Real.log (7 / 3 : ℝ) := by
      rw [← Real.log_exp (2 / 5 : ℝ)]
      exact Real.log_lt_log (Real.exp_pos _) h_exp_lt
    norm_num
    linarith
  rcases h_base.2.2 with ⟨c0, hc_beta, hc_K, hc_link, hc_eta⟩
  refine ⟨h_single_le_pair,
    ⟨{ toCoarseRemainderInfluenceContract := c0
       M_poly := M_poly
       w_poly := w
       supp_poly := supp
       k_supp := k_supp
       Φ_poly := Φ
       a_osc := a_osc
       pairwiseRowInfluence := supportMultiplicityPolymerRowInfluence w k_supp a_osc
       η_pairwise := η_pairwise
       h_K_decomp := hc_K
       h_link_decomp := hc_link
       h_pair_decomp := rfl
       hk_ge_two := hk_ge_two
       h_truthful_supp := h_supp
       hk_card := hk_card
       h_single_le_pairwise := by
         rw [hc_link]
         exact h_single_le_pair
       h_pairwise_uniform := h_pair_sum_le },
     hc_beta, hc_K, hc_link, rfl, rfl, fun i => ⟨h_supp i, hk_card i⟩⟩,
    h_parity_bound⟩

/-- Spatial distance-weighted Dobrushin / Kotecký–Preiss influence row sum
`∑_{j : Fin N_links} exp(κ * d j) * c j` (`P04`/`W4` spatial locality norm):
weights each off-diagonal conditional-TV pair influence `c j ≥ 0` at coarse-lattice distance
`d j ≥ 0` by `exp(κ * d j)`. -/
noncomputable def distanceWeightedDobrushinRowSum {N_links : ℕ}
    (κ : ℝ) (d c : Fin N_links → ℝ) : ℝ :=
  ∑ j : Fin N_links, Real.exp (κ * d j) * c j

/-- Distance-weighted Dobrushin row contraction implies both unweighted row contraction and
exponential spatial decay `c j ≤ q * exp(-κ * d j)` (`P04`/`W4` positive theorem + long-range
negative control):
1. When `0 ≤ κ`, `0 ≤ d j`, `0 ≤ c j`, and `distanceWeightedDobrushinRowSum κ d c ≤ q < 1`, the
   unweighted row sum `∑ j, c j` is bounded by `distanceWeightedDobrushinRowSum κ d c ≤ q < 1`,
2. Every individual pair influence at distance `d j` satisfies `c j ≤ q * Real.exp (-(κ * d j))`, and
3. Conversely (`W4` locality diagnostic), an unweighted pair influence `c_R = q0 ∈ (0, 1)`
   independent of distance `R` satisfies `q0 < 1`, yet once `exp(κ * R) ≥ 1 / q0` its
   distance-weighted contribution satisfies `1 ≤ exp(κ * R) * q0`, showing why an unweighted row
   bound without distance weights cannot enforce uniform spatial exponential decay. -/
theorem distanceWeightedDobrushinRowSum_implies_exponential_spatial_decay_and_locality_diagnostic
    {N_links : ℕ} {κ q q0 R : ℝ} (d c : Fin N_links → ℝ)
    (hκ : 0 ≤ κ)
    (hd : ∀ j : Fin N_links, 0 ≤ d j)
    (hc : ∀ j : Fin N_links, 0 ≤ c j)
    (h_weighted : distanceWeightedDobrushinRowSum κ d c ≤ q)
    (hq_lt_one : q < 1)
    (hq0_pos : 0 < q0) (hq0_lt_one : q0 < 1)
    (hR_large : 1 / q0 ≤ Real.exp (κ * R)) :
    (∑ j : Fin N_links, c j) ≤ distanceWeightedDobrushinRowSum κ d c ∧
    (∑ j : Fin N_links, c j) < 1 ∧
    (∀ j : Fin N_links, c j ≤ q * Real.exp (-(κ * d j))) ∧
    (q0 < 1 ∧ 1 ≤ Real.exp (κ * R) * q0) := by
  have h_unweighted_le : (∑ j : Fin N_links, c j) ≤ distanceWeightedDobrushinRowSum κ d c := by
    unfold distanceWeightedDobrushinRowSum
    refine Finset.sum_le_sum fun j _ => ?_
    have h_exp_ge_one : 1 ≤ Real.exp (κ * d j) := by
      have h_nonneg : 0 ≤ κ * d j := mul_nonneg hκ (hd j)
      linarith [Real.add_one_le_exp (κ * d j)]
    have h_mul := mul_le_mul_of_nonneg_right h_exp_ge_one (hc j)
    linarith
  have h_decay : ∀ j : Fin N_links, c j ≤ q * Real.exp (-(κ * d j)) := by
    intro j
    have h_term_le_sum :
        Real.exp (κ * d j) * c j ≤ distanceWeightedDobrushinRowSum κ d c := by
      unfold distanceWeightedDobrushinRowSum
      exact Finset.single_le_sum
        (f := fun i : Fin N_links => Real.exp (κ * d i) * c i)
        (fun i _ => mul_nonneg (le_of_lt (Real.exp_pos (κ * d i))) (hc i))
        (Finset.mem_univ j)
    have h_term_le_q : Real.exp (κ * d j) * c j ≤ q := le_trans h_term_le_sum h_weighted
    have h_mul :=
      mul_le_mul_of_nonneg_right h_term_le_q (le_of_lt (Real.exp_pos (-(κ * d j))))
    have h_prod : Real.exp (κ * d j) * c j * Real.exp (-(κ * d j)) = c j := by
      calc
        Real.exp (κ * d j) * c j * Real.exp (-(κ * d j))
          = (Real.exp (κ * d j) * Real.exp (-(κ * d j))) * c j := by ring
        _ = Real.exp (κ * d j + -(κ * d j)) * c j := by rw [← Real.exp_add]
        _ = 1 * c j := by simp
        _ = c j := by ring
    linarith
  have h_long_range : 1 ≤ Real.exp (κ * R) * q0 :=
    (div_le_iff₀ hq0_pos).mp hR_large
  exact ⟨h_unweighted_le, lt_of_le_of_lt (le_trans h_unweighted_le h_weighted) hq_lt_one,
    h_decay, ⟨hq0_lt_one, h_long_range⟩⟩

/-- Full `k`-step coarse interacting effective action `A_k(V) = β_k * wilsonAction 1 V + K_k(V)`
including the carried-forward multi-plaquette remainder `K_k` (`P05`/`W6`). -/
noncomputable def iteratedCoarseEffectiveAction {L : ℕ} [NeZero L]
    (β_k : ℝ) (K_k : GaugeConfig L → ℝ) (V : GaugeConfig L) : ℝ :=
  β_k * wilsonAction 1 V + K_k V

/-- Iterated blocking requires carrying the full remainder `K_k` rather than restarting from a
pure-Wilson action, and uncontracted per-step coupling errors accumulate linearly with blocking
depth `K` (`P05`/`W6`/`W7`):
1. For any configuration `V` with `K_k V ≠ 0`, the full coarse Boltzmann weight
   `exp(-iteratedCoarseEffectiveAction β_k K_k V) = exp(-(β_k * S_1(V))) * exp(-K_k(V))`
   differs strictly from the pure-Wilson weight `exp(-(β_k * S_1(V)))`, and
2. Across `K` blocking steps with per-step coupling error `|r_k| ≤ ε_step`, the worst-case linear
   error envelope `K * ε_step` exceeds any fixed tolerance `τ` once `τ / ε_step ≤ K` (`ε_step > 0`),
   demonstrating why growing blocking depth `K(a) → ∞` as `a → 0` requires summable or contractively
   controlled step errors rather than a fixed finite-step error budget. -/
theorem iterated_blocking_requires_remainder_carryForward_and_growing_depth_error_bound
    {L : ℕ} [NeZero L] (β_k : ℝ) (K_k : GaugeConfig L → ℝ) (V : GaugeConfig L)
    (hK_ne : K_k V ≠ 0)
    {ε_step τ K_real : ℝ} (hε_pos : 0 < ε_step) (hK_large : τ / ε_step ≤ K_real) :
    Real.exp (-iteratedCoarseEffectiveAction β_k K_k V) =
      Real.exp (-(β_k * wilsonAction 1 V)) * Real.exp (-K_k V) ∧
    Real.exp (-iteratedCoarseEffectiveAction β_k K_k V) ≠
      Real.exp (-(β_k * wilsonAction 1 V)) ∧
    τ ≤ K_real * ε_step := by
  have h_fact :
      Real.exp (-iteratedCoarseEffectiveAction β_k K_k V) =
        Real.exp (-(β_k * wilsonAction 1 V)) * Real.exp (-K_k V) := by
    unfold iteratedCoarseEffectiveAction
    rw [← Real.exp_add]
    congr 1
    ring
  have h_ne :
      Real.exp (-iteratedCoarseEffectiveAction β_k K_k V) ≠
        Real.exp (-(β_k * wilsonAction 1 V)) := by
    intro h_eq
    have h_inj := Real.exp_injective h_eq
    unfold iteratedCoarseEffectiveAction at h_inj
    have hK_zero : K_k V = 0 := by linarith
    exact hK_ne hK_zero
  have h_depth : τ ≤ K_real * ε_step := (div_le_iff₀ hε_pos).mp hK_large
  exact ⟨h_fact, h_ne, h_depth⟩

/-- Four-link parity indicator on `GaugeConfig 1` (`4` links `⟨0, μ⟩`, `μ ∈ Fin 4`): equals `0`
when an even number of links differ from `1 : SU2` and `1` when an odd number of links differ
from `1 : SU2` (`V36-PAIRWISE-SUPPORT-UNBOUND` control). -/
noncomputable def fourLinkParityIndicator (V : GaugeConfig 1) : ℝ := by
  classical
  exact if ((∑ μ : Fin 4, if V ⟨fun _ => 0, μ⟩ = 1 then (0 : ℕ) else 1) % 2 = 0)
    then 0 else 1

/-- Single-link oscillation bound `|fourLinkParityIndicator (V[x,μ := g1]) - fourLinkParityIndicator (V[x,μ := g2])| ≤ 1`. -/
theorem fourLinkParityIndicator_single_link_osc_le_one
    (x : Lattice4D 1) (μ : Fin 4) (V : GaugeConfig 1) (g1 g2 : SU2) :
    |fourLinkParityIndicator (updateGaugeLink 1 V x μ g1) -
      fourLinkParityIndicator (updateGaugeLink 1 V x μ g2)| ≤ 1 := by
  classical
  have h_range : ∀ W : GaugeConfig 1,
      0 ≤ fourLinkParityIndicator W ∧ fourLinkParityIndicator W ≤ 1 := by
    intro W
    unfold fourLinkParityIndicator
    split <;> norm_num
  have h1 := h_range (updateGaugeLink 1 V x μ g1)
  have h2 := h_range (updateGaugeLink 1 V x μ g2)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Flipping any of the four links `⟨0, μ⟩` (`μ : Fin 4`) on `vacuumConfig 1` from `1` to
`su2CenterFlip` (`-I ≠ I`) flips `fourLinkParityIndicator` from `0` to `1`; consequently, any
truthful support set `S : Finset (Link 1)` satisfying `IsSupportedOnLinkSet fourLinkParityIndicator S`
must contain all `4` links (`S = Finset.univ` and `S.card = 4`), refuting any false support
declaration `k_supp ≤ 2` (`V36-PAIRWISE-SUPPORT-UNBOUND` remediation). -/
theorem fourLinkParityIndicator_truthful_support_card_eq_four_and_rejects_two
    (S : Finset (Link 1))
    (h_supp : IsSupportedOnLinkSet fourLinkParityIndicator S) :
    fourLinkParityIndicator (vacuumConfig 1) = 0 ∧
    (∀ μ : Fin 4,
      fourLinkParityIndicator (updateGaugeLink 1 (vacuumConfig 1) (fun _ => 0) μ su2CenterFlip) = 1) ∧
    S = Finset.univ ∧
    S.card = 4 ∧
    ¬ (S.card ≤ 2) := by
  classical
  have h_flip_ne : su2CenterFlip ≠ (1 : SU2) := by
    intro h_eq
    have h_tr := su2CenterFlip_trace_and_defect.1
    rw [h_eq, SU2.trace_one] at h_tr
    norm_num at h_tr
  have h_vac : fourLinkParityIndicator (vacuumConfig 1) = 0 := by
    simp [fourLinkParityIndicator, vacuumConfig]
  have h_flip : ∀ μ : Fin 4,
      fourLinkParityIndicator (updateGaugeLink 1 (vacuumConfig 1) (fun _ => 0) μ su2CenterFlip) = 1 := by
    intro μ
    have heval (ν : Fin 4) :
        updateGaugeLink 1 (vacuumConfig 1) (fun _ => 0) μ su2CenterFlip ⟨fun _ => 0, ν⟩ =
          if ν = μ then su2CenterFlip else 1 := by
      by_cases h : ν = μ
      · subst ν
        simpa using (updateGaugeLink_same_and_other 1 (vacuumConfig 1) (fun _ => 0) μ su2CenterFlip).1
      · rw [(updateGaugeLink_same_and_other 1 (vacuumConfig 1) (fun _ => 0) μ su2CenterFlip).2
          ⟨fun _ => 0, ν⟩ (by intro heq; exact h (congrArg Link.μ heq))]
        simp [vacuumConfig, h]
    unfold fourLinkParityIndicator
    simp_rw [heval]
    have hind (ν : Fin 4) :
        (if (if ν = μ then su2CenterFlip else 1) = 1 then (0 : ℕ) else 1) =
          (if ν = μ then 1 else 0) := by
      by_cases h : ν = μ <;> simp [h, h_flip_ne]
    simp_rw [hind]
    simp
  have h_mem_all : ∀ e : Link 1, e ∈ S := by
    intro ⟨x, μ⟩
    have hx : x = (fun _ => 0) := by
      funext i
      exact Subsingleton.elim (x i) 0
    subst hx
    by_contra h_not_mem
    have h_eq := h_supp (fun _ => 0) μ h_not_mem (vacuumConfig 1) su2CenterFlip 1
    have h_upd_one : updateGaugeLink 1 (vacuumConfig 1) (fun _ => 0) μ 1 = vacuumConfig 1 := by
      funext e'
      rcases e' with ⟨y, ν⟩
      by_cases h : (⟨y, ν⟩ : Link 1) = ⟨fun _ => 0, μ⟩
      · cases h
        simpa [vacuumConfig] using (updateGaugeLink_same_and_other 1 (vacuumConfig 1) (fun _ => 0) μ 1).1
      · exact (updateGaugeLink_same_and_other 1 (vacuumConfig 1) (fun _ => 0) μ 1).2 ⟨y, ν⟩ h
    rw [h_upd_one, h_vac, h_flip μ] at h_eq
    norm_num at h_eq
  have h_univ : S = Finset.univ := Finset.eq_univ_of_forall h_mem_all
  have h_card_univ : (Finset.univ : Finset (Link 1)).card = 4 := by
    change Fintype.card (Link 1) = 4
    rw [Fintype.card_congr (linkEquiv 1), Fintype.card_prod, card_lattice4D 1]
    norm_num
  have h_card : S.card = 4 := by rw [h_univ, h_card_univ]
  refine ⟨h_vac, h_flip, h_univ, h_card, by omega⟩

/-- Off-diagonal binary conditional-TV row sum at link `e : Link L` across all partner links
`e' ∈ Finset.univ.erase e` (`V36-PAIRWISE-SUPPORT-UNBOUND` explicit cross-ratio-to-TV row bridge). -/
noncomputable def offDiagonalBinaryTVRow {L : ℕ} [NeZero L]
    (p1 p2 q1 q2 : Link L → Link L → ℝ) (e : Link L) : ℝ :=
  ∑ e' ∈ (Finset.univ : Finset (Link L)).erase e,
    binaryConditionalTV (p1 e e') (p2 e e') (q1 e e') (q2 e e')

/-- Off-diagonal pairwise cross-ratio to binary conditional-TV row bound
(`V36-PAIRWISE-SUPPORT-UNBOUND` remediation):
invoking `pairwise_crossRatio_bounds_binaryConditionalTV` at every off-diagonal partner link
`e' ∈ Finset.univ.erase e` derives the row-sum bound
`0 ≤ offDiagonalBinaryTVRow p1 p2 q1 q2 e ≤ ∑_{e' ≠ e} (exp(γ e e') - 1)`. -/
theorem offDiagonal_binaryConditionalTV_row_le_sum_exp_sub_one
    {L : ℕ} [NeZero L]
    (p1 p2 q1 q2 γ : Link L → Link L → ℝ) (e : Link L)
    (hp1 : ∀ e' ∈ (Finset.univ : Finset (Link L)).erase e, 0 < p1 e e')
    (hp2 : ∀ e' ∈ (Finset.univ : Finset (Link L)).erase e, 0 < p2 e e')
    (hq1 : ∀ e' ∈ (Finset.univ : Finset (Link L)).erase e, 0 < q1 e e')
    (hq2 : ∀ e' ∈ (Finset.univ : Finset (Link L)).erase e, 0 < q2 e e')
    (hγ : ∀ e' ∈ (Finset.univ : Finset (Link L)).erase e, 0 ≤ γ e e')
    (h_cross_lo : ∀ e' ∈ (Finset.univ : Finset (Link L)).erase e,
      q1 e e' * p2 e e' * Real.exp (-γ e e') ≤ p1 e e' * q2 e e')
    (h_cross_hi : ∀ e' ∈ (Finset.univ : Finset (Link L)).erase e,
      p1 e e' * q2 e e' ≤ q1 e e' * p2 e e' * Real.exp (γ e e')) :
    0 ≤ offDiagonalBinaryTVRow p1 p2 q1 q2 e ∧
    offDiagonalBinaryTVRow p1 p2 q1 q2 e ≤
      ∑ e' ∈ (Finset.univ : Finset (Link L)).erase e, (Real.exp (γ e e') - 1) := by
  unfold offDiagonalBinaryTVRow
  refine ⟨Finset.sum_nonneg fun e' he' => abs_nonneg _,
    Finset.sum_le_sum fun e' he' => ?_⟩
  exact (pairwise_crossRatio_bounds_binaryConditionalTV
    (hp1 e' he') (hp2 e' he') (hq1 e' he') (hq2 e' he') (hγ e' he')
    (h_cross_lo e' he') (h_cross_hi e' he')).2.2

/-- Negative control for fixed-volume quantifier order (`V34-INFLUENCE-VOLUME-UNIFORMITY`):
because `CoarseRemainderInfluenceContract L` stores `η_next` inside each fixed-`L` record, the
trivial family `K_next = 0`, `linkInfluence = 0`, `β_next = 0`, and `η_next = (L : ℝ) ^ 4`
inhabits `CoarseRemainderInfluenceContract L` for every `L` while diverging as `L → ∞`
(`(2 : ℝ) ^ 4 = 16 > 1`). -/
theorem fixedVolume_contract_allows_volume_divergent_eta_L_pow_four
    (L : ℕ) [NeZero L] :
    (∃ c : CoarseRemainderInfluenceContract L,
      c.β_next = 0 ∧
      c.K_next = (fun _ => 0) ∧
      c.linkInfluence = (fun _ _ => 0) ∧
      c.η_next = (L : ℝ) ^ 4) ∧
    (1 : ℝ) < (2 : ℝ) ^ 4 := by
  refine ⟨⟨{
    β_next := 0
    K_next := fun _ => 0
    linkInfluence := fun _ _ => 0
    η_next := (L : ℝ) ^ 4
    h_β_nonneg := le_refl 0
    h_η_nonneg := by positivity
    h_influence_nonneg := fun _ _ => le_refl 0
    h_osc_K_next := by intros; simp
    h_influence_uniform := fun _ _ => by positivity
  }, rfl, rfl, rfl, rfl⟩, by norm_num⟩

/-- Volume-uniform coarse remainder-influence family (`V34-INFLUENCE-VOLUME-UNIFORMITY`
remediation): reverses the quantifier order by fixing a single volume-independent coupling upper
bound `β_star` and remainder envelope `η_star` **outside** the `∀ (L : ℕ) [NeZero L]` quantifier,
requiring `18 * β_star + η_star < 1` uniformly across all torus sizes `L ≥ 1`. -/
structure VolumeUniformCoarseInfluenceFamily where
  β_star : ℝ
  η_star : ℝ
  contract : ∀ (L : ℕ) [NeZero L], CoarseRemainderInfluenceContract L
  h_β_star_nonneg : 0 ≤ β_star
  h_η_star_nonneg : 0 ≤ η_star
  h_uniform_β : ∀ (L : ℕ) [NeZero L], (contract L).β_next ≤ β_star
  h_uniform_η : ∀ (L : ℕ) [NeZero L], (contract L).η_next ≤ η_star
  h_uniform_contraction : 18 * β_star + η_star < 1

/-- Uniform-in-volume contraction across all `L ≥ 1` for `VolumeUniformCoarseInfluenceFamily`,
paired with constructive inhabitation at `β_star = 1 / 24, η_star = 1 / 8` (`7 / 8 < 1`) and
rejection of the volume-divergent sequence `η_next(L) = L^4` at `L = 2`
(`V34-INFLUENCE-VOLUME-UNIFORMITY`). -/
theorem volumeUniformCoarseInfluenceFamily_uniform_across_all_L_and_rejects_L_pow_four
    (fam : VolumeUniformCoarseInfluenceFamily) :
    (∀ (L : ℕ) [NeZero L] (x : Lattice4D L) (μ : Fin 4),
      18 * (fam.contract L).β_next + (fam.contract L).linkInfluence x μ ≤
        18 * fam.β_star + fam.η_star ∧
      18 * (fam.contract L).β_next + (fam.contract L).linkInfluence x μ < 1) ∧
    (∃ fam0 : VolumeUniformCoarseInfluenceFamily,
      fam0.β_star = 1 / 24 ∧ fam0.η_star = 1 / 8 ∧
      18 * fam0.β_star + fam0.η_star = 7 / 8) ∧
    ¬ ((2 : ℝ) ^ 4 ≤ fam.η_star) := by
  have h_all : ∀ (L : ℕ) [NeZero L] (x : Lattice4D L) (μ : Fin 4),
      18 * (fam.contract L).β_next + (fam.contract L).linkInfluence x μ ≤
        18 * fam.β_star + fam.η_star ∧
      18 * (fam.contract L).β_next + (fam.contract L).linkInfluence x μ < 1 := by
    intro L _ x μ
    have hβ := fam.h_uniform_β L
    have h_inf := (fam.contract L).h_influence_uniform x μ
    have hη := fam.h_uniform_η L
    have h_sub := fam.h_uniform_contraction
    exact ⟨by linarith, by linarith⟩
  have h_inh : ∃ fam0 : VolumeUniformCoarseInfluenceFamily,
      fam0.β_star = 1 / 24 ∧ fam0.η_star = 1 / 8 ∧
      18 * fam0.β_star + fam0.η_star = 7 / 8 := by
    refine ⟨{
      β_star := 1 / 24
      η_star := 1 / 8
      contract := fun L _ => {
        β_next := 1 / 24
        K_next := fun _ => 0
        linkInfluence := fun _ _ => 0
        η_next := 1 / 8
        h_β_nonneg := by norm_num
        h_η_nonneg := by norm_num
        h_influence_nonneg := fun _ _ => le_refl 0
        h_osc_K_next := by intros; simp
        h_influence_uniform := fun _ _ => by norm_num
      }
      h_β_star_nonneg := by norm_num
      h_η_star_nonneg := by norm_num
      h_uniform_β := fun _ _ => le_refl _
      h_uniform_η := fun _ _ => le_refl _
      h_uniform_contraction := by norm_num
    }, rfl, rfl, by norm_num⟩
  have h_reject : ¬ ((2 : ℝ) ^ 4 ≤ fam.η_star) := by
    intro h_le
    have hβ0 := fam.h_β_star_nonneg
    have h_sub := fam.h_uniform_contraction
    norm_num at h_le
    linarith
  exact ⟨h_all, h_inh, h_reject⟩

/-! ## Interacting Blocked Fiber Weight & Multi-Step RG Semigroup Identity -/

open MeasureTheory

/-- Interacting blocked fiber weight carrying a multi-plaquette remainder `K : GaugeConfig (2 * L) → ℝ`
inside the conditional fiber integral:
`W_{β, K}(V) := ∫ U, exp(-wilsonAction β U - K U) ∂(dis.fiberKernel V)`. -/
noncomputable def interactingBlockedFiberWeight {L : ℕ} [NeZero L] [NeZero (2 * L)]
    [MeasurableSpace (GaugeConfig L)] [MeasurableSpace (GaugeConfig (2 * L))]
    (dis : ConditionalBlockFiberDisintegration L)
    (β : ℝ) (K : GaugeConfig (2 * L) → ℝ) (V : GaugeConfig L) : ℝ :=
  ∫ U, Real.exp (-wilsonAction β U - K U) ∂(dis.fiberKernel V)

/-- Interacting blocked effective action `A_{β, K}(V) := -log W_{β, K}(V)` for a fine-lattice
action `wilsonAction β U + K U` integrated over `dis.fiberKernel V`. -/
noncomputable def interactingBlockedEffectiveAction {L : ℕ} [NeZero L] [NeZero (2 * L)]
    [MeasurableSpace (GaugeConfig L)] [MeasurableSpace (GaugeConfig (2 * L))]
    (dis : ConditionalBlockFiberDisintegration L)
    (β : ℝ) (K : GaugeConfig (2 * L) → ℝ) (V : GaugeConfig L) : ℝ :=
  -Real.log (interactingBlockedFiberWeight dis β K V)

/-- When the carried remainder `K` is identically zero, `interactingBlockedFiberWeight` and
`interactingBlockedEffectiveAction` reduce exactly to `wilsonBlockedFiberWeight` and
`wilsonBlockedEffectiveAction`; when `K` is measurable and bounded by `K_lo ≤ K U ≤ K_hi` for all
`U : GaugeConfig (2 * L)`, the interacting fiber weight is strictly positive and sandwiched between
`exp(-K_hi) * wilsonBlockedFiberWeight dis β V` and `exp(-K_lo) * wilsonBlockedFiberWeight dis β V`,
and the interacting effective action is sandwiched between
`wilsonBlockedEffectiveAction dis β V + K_lo` and `wilsonBlockedEffectiveAction dis β V + K_hi`. -/
theorem interactingBlockedFiberWeight_zero_remainder_and_exponential_sandwich
    {L : ℕ} [NeZero L] [NeZero (2 * L)]
    [MeasurableSpace (GaugeConfig L)] [MeasurableSpace (GaugeConfig (2 * L))]
    (dis : ConditionalBlockFiberDisintegration L)
    {β K_lo K_hi : ℝ} (hβ : 0 ≤ β)
    (hS : Measurable (wilsonAction β : GaugeConfig (2 * L) → ℝ))
    (K : GaugeConfig (2 * L) → ℝ) (hK_meas : Measurable K)
    (hK_bounds : ∀ U : GaugeConfig (2 * L), K_lo ≤ K U ∧ K U ≤ K_hi)
    (V : GaugeConfig L) :
    (interactingBlockedFiberWeight dis β (fun _ => 0) V = wilsonBlockedFiberWeight dis β V ∧
      interactingBlockedEffectiveAction dis β (fun _ => 0) V = wilsonBlockedEffectiveAction dis β V) ∧
    (Real.exp (-K_hi) * wilsonBlockedFiberWeight dis β V ≤
        interactingBlockedFiberWeight dis β K V ∧
      interactingBlockedFiberWeight dis β K V ≤
        Real.exp (-K_lo) * wilsonBlockedFiberWeight dis β V ∧
      0 < interactingBlockedFiberWeight dis β K V) ∧
    (wilsonBlockedEffectiveAction dis β V + K_lo ≤
        interactingBlockedEffectiveAction dis β K V ∧
      interactingBlockedEffectiveAction dis β K V ≤
        wilsonBlockedEffectiveAction dis β V + K_hi) := by
  have : IsProbabilityMeasure (dis.fiberKernel V) := dis.fiber_prob V
  have h_zero_W :
      interactingBlockedFiberWeight dis β (fun _ => 0) V = wilsonBlockedFiberWeight dis β V := by
    simp [interactingBlockedFiberWeight, wilsonBlockedFiberWeight, wilsonPartition, boltzmannWeight]
  have h_zero_A :
      interactingBlockedEffectiveAction dis β (fun _ => 0) V =
        wilsonBlockedEffectiveAction dis β V := by
    dsimp [interactingBlockedEffectiveAction, wilsonBlockedEffectiveAction]
    rw [h_zero_W]
  have hw_int : Integrable (boltzmannWeight β) (dis.fiberKernel V) :=
    wilsonWeight_integrable (dis.fiberKernel V) hβ hS
  have h_int_meas : Measurable (fun U : GaugeConfig (2 * L) => Real.exp (-wilsonAction β U - K U)) :=
    Real.continuous_exp.measurable.comp (hS.neg.sub hK_meas)
  have hK_int : Integrable (fun U : GaugeConfig (2 * L) => Real.exp (-wilsonAction β U - K U))
      (dis.fiberKernel V) := by
    apply (integrable_const (Real.exp (-K_lo))).mono' h_int_meas.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun U => by
      have hp : 0 < Real.exp (-wilsonAction β U - K U) := Real.exp_pos _
      change ‖Real.exp (-wilsonAction β U - K U)‖ ≤ Real.exp (-K_lo)
      rw [Real.norm_eq_abs, abs_of_pos hp]
      refine Real.exp_le_exp.mpr ?_
      have hS_nonneg := wilsonAction_nonneg hβ U
      have hK_lo := (hK_bounds U).1
      linarith
  have h_pt_lo : ∀ U : GaugeConfig (2 * L),
      Real.exp (-K_hi) * boltzmannWeight β U ≤ Real.exp (-wilsonAction β U - K U) := by
    intro U
    unfold boltzmannWeight
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hK := (hK_bounds U).2
    linarith
  have h_pt_hi : ∀ U : GaugeConfig (2 * L),
      Real.exp (-wilsonAction β U - K U) ≤ Real.exp (-K_lo) * boltzmannWeight β U := by
    intro U
    unfold boltzmannWeight
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hK := (hK_bounds U).1
    linarith
  have h_W_lo :
      Real.exp (-K_hi) * wilsonBlockedFiberWeight dis β V ≤
        interactingBlockedFiberWeight dis β K V := by
    calc
      Real.exp (-K_hi) * wilsonBlockedFiberWeight dis β V
        = ∫ U, Real.exp (-K_hi) * boltzmannWeight β U ∂(dis.fiberKernel V) := by
          dsimp [wilsonBlockedFiberWeight, wilsonPartition]
          rw [integral_const_mul]
      _ ≤ interactingBlockedFiberWeight dis β K V :=
          integral_mono (hw_int.const_mul (Real.exp (-K_hi))) hK_int h_pt_lo
  have h_W_hi :
      interactingBlockedFiberWeight dis β K V ≤
        Real.exp (-K_lo) * wilsonBlockedFiberWeight dis β V := by
    calc
      interactingBlockedFiberWeight dis β K V
        ≤ ∫ U, Real.exp (-K_lo) * boltzmannWeight β U ∂(dis.fiberKernel V) :=
          integral_mono hK_int (hw_int.const_mul (Real.exp (-K_lo))) h_pt_hi
      _ = Real.exp (-K_lo) * wilsonBlockedFiberWeight dis β V := by
          dsimp [wilsonBlockedFiberWeight, wilsonPartition]
          rw [integral_const_mul]
  have hW_pos : 0 < wilsonBlockedFiberWeight dis β V :=
    (wilsonBlockedFiberWeight_bounds_and_pos_all_configs dis hβ hS V).1
  have h_lo_pos : 0 < Real.exp (-K_hi) * wilsonBlockedFiberWeight dis β V :=
    mul_pos (Real.exp_pos (-K_hi)) hW_pos
  have hW_int_pos : 0 < interactingBlockedFiberWeight dis β K V :=
    lt_of_lt_of_le h_lo_pos h_W_lo
  have h_log_lo := Real.log_le_log h_lo_pos h_W_lo
  rw [Real.log_mul (ne_of_gt (Real.exp_pos (-K_hi))) (ne_of_gt hW_pos), Real.log_exp] at h_log_lo
  have h_log_hi := Real.log_le_log hW_int_pos h_W_hi
  rw [Real.log_mul (ne_of_gt (Real.exp_pos (-K_lo))) (ne_of_gt hW_pos), Real.log_exp] at h_log_hi
  dsimp [interactingBlockedEffectiveAction, wilsonBlockedEffectiveAction]
  exact ⟨⟨h_zero_W, h_zero_A⟩, ⟨h_W_lo, h_W_hi, hW_int_pos⟩, ⟨by linarith, by linarith⟩⟩

/-- Exact multi-step RG step-composition identity on `ConditionalBlockFiberDisintegration L`:
when Step `k`'s coarse effective action `A_k : GaugeConfig (2 * L) → ℝ` is decomposed into a
vacuum constant `c_k`, a renormalized single-plaquette Wilson term `β_k * wilsonAction 1 U`, and a
carried multi-plaquette remainder `K_k U` via
`A_k U = c_k + iteratedCoarseEffectiveAction β_k K_k U`, integrating the full interacting Boltzmann
weight `exp(-A_k U)` over the Step `k+1` conditional fiber kernel `dis.fiberKernel V` factors
exactly as `exp(-c_k) * interactingBlockedFiberWeight dis β_k K_k V`, and its vacuum-normalized
negative logarithm equals
`interactingBlockedEffectiveAction dis β_k K_k V - interactingBlockedEffectiveAction dis β_k K_k (vacuumConfig L)`
(completely independent of the additive constant `c_k`). -/
theorem interacting_twoStep_dyadic_blocking_semigroup_and_effective_action_identity
    {L : ℕ} [NeZero L] [NeZero (2 * L)]
    [MeasurableSpace (GaugeConfig L)] [MeasurableSpace (GaugeConfig (2 * L))]
    (dis : ConditionalBlockFiberDisintegration L)
    {c_k β_k K_lo K_hi : ℝ} (hβ : 0 ≤ β_k)
    (hS1 : Measurable (wilsonAction 1 : GaugeConfig (2 * L) → ℝ))
    (A_k K_k : GaugeConfig (2 * L) → ℝ) (hK_meas : Measurable K_k)
    (hK_bounds : ∀ U : GaugeConfig (2 * L), K_lo ≤ K_k U ∧ K_k U ≤ K_hi)
    (h_decomp : ∀ U : GaugeConfig (2 * L),
      A_k U = c_k + iteratedCoarseEffectiveAction β_k K_k U)
    (V : GaugeConfig L) :
    (∫ U, Real.exp (-A_k U) ∂(dis.fiberKernel V)) =
      Real.exp (-c_k) * interactingBlockedFiberWeight dis β_k K_k V ∧
    0 < (∫ U, Real.exp (-A_k U) ∂(dis.fiberKernel V)) ∧
    (-Real.log (∫ U, Real.exp (-A_k U) ∂(dis.fiberKernel V)) -
        (-Real.log (∫ U, Real.exp (-A_k U) ∂(dis.fiberKernel (vacuumConfig L))))) =
      interactingBlockedEffectiveAction dis β_k K_k V -
        interactingBlockedEffectiveAction dis β_k K_k (vacuumConfig L) := by
  have hS_eq : (wilsonAction β_k : GaugeConfig (2 * L) → ℝ) = fun U => β_k * wilsonAction 1 U :=
    funext (wilsonAction_eq_beta_mul_wilsonAction_one β_k)
  have hSβ : Measurable (wilsonAction β_k : GaugeConfig (2 * L) → ℝ) := by
    rw [hS_eq]
    exact measurable_const.mul hS1
  have h_pt : ∀ U : GaugeConfig (2 * L),
      Real.exp (-A_k U) = Real.exp (-c_k) * Real.exp (-wilsonAction β_k U - K_k U) := by
    intro U
    rw [h_decomp U]
    unfold iteratedCoarseEffectiveAction
    rw [← wilsonAction_eq_beta_mul_wilsonAction_one β_k U, ← Real.exp_add]
    congr 1
    ring
  have h_factor : ∀ W : GaugeConfig L,
      (∫ U, Real.exp (-A_k U) ∂(dis.fiberKernel W)) =
        Real.exp (-c_k) * interactingBlockedFiberWeight dis β_k K_k W := by
    intro W
    simp_rw [h_pt]
    rw [integral_const_mul]
    rfl
  have hW_V_pos : 0 < interactingBlockedFiberWeight dis β_k K_k V :=
    (interactingBlockedFiberWeight_zero_remainder_and_exponential_sandwich
      dis hβ hSβ K_k hK_meas hK_bounds V).2.1.2.2
  have hW_vac_pos : 0 < interactingBlockedFiberWeight dis β_k K_k (vacuumConfig L) :=
    (interactingBlockedFiberWeight_zero_remainder_and_exponential_sandwich
      dis hβ hSβ K_k hK_meas hK_bounds (vacuumConfig L)).2.1.2.2
  refine ⟨h_factor V, ?_, ?_⟩
  · rw [h_factor V]
    exact mul_pos (Real.exp_pos (-c_k)) hW_V_pos
  · rw [h_factor V, h_factor (vacuumConfig L),
      Real.log_mul (ne_of_gt (Real.exp_pos (-c_k))) (ne_of_gt hW_V_pos),
      Real.log_mul (ne_of_gt (Real.exp_pos (-c_k))) (ne_of_gt hW_vac_pos),
      Real.log_exp]
    dsimp [interactingBlockedEffectiveAction]
    ring

end JesseMath.Physics.YangMillsRGBridgeObstruction

#assert_zfc_axioms
