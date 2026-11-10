import JesseMath.Linter.AxiomAudit
import JesseMath.Physics.YangMillsUniformHaarNeighbourhood
import JesseMath.Physics.YangMillsCutoffPathBalance
import JesseMath.Physics.YangMillsPhysicalBridges

/-!
# Necessity of fast coupling growth and anti-vacuity of the weak-coupling hypotheses

Subject: the repository's SU(2) Wilson law `wilsonMeasure (gaugeHaarMeasure L) β` on the periodic
`L⁴` torus, its total unit-coupling action `S₁ = wilsonAction 1`, and the fixed-volume cutoff
paths `(a_n, L_n, β_n)` with `L_n a_n = side` of `YangMillsCutoffPathBalance`.

1. Bridge. The named hypothesis `SingleLinkHaarMassRate` of the cutoff-path module is
   discharged on the actual SU(2) Haar measure (`haarSingleLinkMassRate`: `c₀ = 1/160000`,
   `p = 2`, `nbhd η = linkNeighbourhood (η/16)`), from `singleLinkMass_ge` and the quasi-triangle
   inequality `linkDefect_mul_le`. Its per-link factor at a fixed threshold `δ` is
   `(δ / (2400 L_n⁴))²`. The conditional theorems of that module stated under the rate hold
   unconditionally. Every ingredient (H) (`PathHaarMassBound`) with bounded thresholds has
   per-link factors tending to zero (from the private-link upper bound of
   `YangMillsUniformHaarNeighbourhood`), so no ingredient (H) with a constant factor at a fixed
   threshold exists; in particular the hypotheses of `wilsonTail_tendsto_zero_of_supercritical`
   are jointly unsatisfiable.
2. Necessity on the actual measure. Along every fixed-volume cutoff path whose bare coupling is
   at most `A + B (1/a_n)^r` with `r < 1/32`, in particular at most logarithmic in `1/a_n`, and
   along every Clause (0) coupling schedule, including the canonical SU(2) path, the actual
   total-action tail `P_n(S₁ ≥ ε)` tends to one for every `ε > 0`
   (`wilsonTail_tendsto_one_of_logarithmic`, `clauseZeroCanonicalPath_wilsonTail_tendsto_one`).
   Consequently the balance hypothesis of the cutoff-path module and the gain hypothesis of
   `haarWilsonMeasure_action_tail_tendsto_varying_volume` are unsatisfiable along such paths,
   for every choice of thresholds and per-link factors.
   Conversely the explicit schedule `β_n = (8 L_n⁴ log (2400 L_n⁴ / δ) + n) / (ε - δ)` drives
   the tail to zero along every fixed-volume geometry (`fixedVolume_concentration_dichotomy`);
   the gap between `a_n^(-1/32)` and `a_n^(-4) log (1/a_n)` growth is not closed here.
3. Anti-vacuity. Explicit inhabitants of the structures quantified by the weak-coupling
   theorems, with theorems separating them from zero or constant models:
   the canonical path, schedule, Haar ingredient (H) and single-link rate of the cutoff-path
   module; `GrowingVolumeGain`, the data and hypothesis of the varying-volume theorem of
   `YangMillsWeakCoupling` (that file declares no structure), whose inhabitants all have
   unbounded coupling and none of which lives on a logarithmic path; the volume-uniform
   influence family, with a nonzero remainder, every inhabitant of which has coupling below
   `1/18`; and `UnifiedPhysicalWilsonBlockingModel`. That structure admits inhabitants with zero
   extracted coupling and zero remainder: at zero bare coupling for every disintegration, and at
   every bare coupling for a fiber kernel that ignores the coarse configuration. On the actual
   Haar disintegration it is inhabited exactly when the extracted coupling is nonnegative, and
   for each `L ≥ 2` and every bare coupling above an `L`-dependent threshold an
   explicit model has positive extracted coupling (`exists_nondegenerate_haarModel`), from a
   lattice Stokes identity on the `2 × 2` fine square of one coarse plaquette and two-sided
   bounds on the Haar fiber weights.

Quantifiers are stated in each theorem. All statements are finite-volume statements along
explicit sequences of tori; no continuum limit, renormalization-group step or mass gap is
asserted.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace JesseMath.Physics.YangMillsWeakCouplingNecessity

open JesseMath.Physics JesseMath.Physics.YangMillsCutoffPathBalance

/-! ## 1. The single-link Haar mass rate on the actual SU(2) Haar measure -/

/-- The single-link action sublevel of the cutoff-path module is the defect neighbourhood of the
Haar-neighbourhood module. -/
theorem actionSublevel_eq_linkNeighbourhood (η : ℝ) :
    actionSublevel η = linkNeighbourhood η := rfl

/-- Four group elements of defect below `η / 16` form a plaquette word of action below `η`. -/
theorem plaquetteWord_action_lt {η : ℝ} {a b c d : SU2}
    (ha : linkDefect a < η / 16) (hb : linkDefect b < η / 16)
    (hc : linkDefect c < η / 16) (hd : linkDefect d < η / 16) :
    1 - (1 / 2 : ℝ) * (SU2.trace (a * b * c⁻¹ * d⁻¹)).re < η := by
  change linkDefect (a * b * c⁻¹ * d⁻¹) < η
  have hre : a * b * c⁻¹ * d⁻¹ = (a * b) * (c⁻¹ * d⁻¹) := by group
  rw [hre]
  have h1 := linkDefect_mul_le (a * b) (c⁻¹ * d⁻¹)
  have h2 := linkDefect_mul_le a b
  have h3 := linkDefect_mul_le c⁻¹ d⁻¹
  rw [linkDefect_inv, linkDefect_inv] at h3
  linarith

/-- The named hypothesis `SingleLinkHaarMassRate` of `YangMillsCutoffPathBalance`, discharged on
the actual SU(2) Haar measure: the neighbourhood at plaquette scale `η` is
`linkNeighbourhood (η / 16)`, and `singleLinkMass_ge` gives the rate `η² / 160000` on `(0, 1]`. -/
def haarSingleLinkMassRate : SingleLinkHaarMassRate where
  c₀ := 1 / 160000
  p := 2
  c₀_pos := by norm_num
  p_nonneg := by norm_num
  nbhd η := linkNeighbourhood (η / 16)
  plaquette_lt _ _ _ ha _ hb _ hc _ hd := plaquetteWord_action_lt ha hb hc hd
  mass_rate η hη hη1 := by
    have h := singleLinkMass_ge (η := η / 16) (by positivity) (by linarith)
    show (1 / 160000 : ℝ) * η ^ (2 : ℝ) ≤ singleLinkMass (η / 16)
    rw [Real.rpow_two]
    calc (1 / 160000 : ℝ) * η ^ 2 = (η / 16) ^ 2 / 625 := by ring
      _ ≤ singleLinkMass (η / 16) := h

theorem haarSingleLinkMassRate_c₀ : haarSingleLinkMassRate.c₀ = 1 / 160000 := rfl

theorem haarSingleLinkMassRate_p : haarSingleLinkMassRate.p = 2 := rfl

theorem haarSingleLinkMassRate_nbhd (η : ℝ) :
    haarSingleLinkMassRate.nbhd η = linkNeighbourhood (η / 16) := rfl

/-- The rate's per-link factor at a fixed total threshold `δ` is `(δ / (2400 L_n⁴))²`, the base of
`haarVacuumSublevelMass_ge`. -/
theorem haarSingleLinkMassRate_pathFactor (G : FixedVolumeGeometry) (δ : ℝ) (n : ℕ) :
    haarSingleLinkMassRate.pathFactor G δ n = (δ / (2400 * (G.sites n : ℝ) ^ 4)) ^ 2 := by
  have hL : (G.sites n : ℝ) ≠ 0 := (G.sites_pos_real n).ne'
  show (1 / 160000 : ℝ) * (δ / (6 * (G.sites n : ℝ) ^ 4)) ^ (2 : ℝ) = _
  rw [Real.rpow_two]
  field_simp
  ring

/-- Ingredient (H) at a fixed total threshold `δ ≤ 6`, supplied by the actual Haar measure with
the explicit per-link factor `(δ / (2400 L_n⁴))²`. -/
def haarPathHaarMassBound (G : FixedVolumeGeometry) {δ : ℝ} (hδ : 0 < δ) (hδ6 : δ ≤ 6) :
    PathHaarMassBound G :=
  haarSingleLinkMassRate.toPathHaarMassBound G hδ hδ6

theorem haarPathHaarMassBound_δ (G : FixedVolumeGeometry) {δ : ℝ} (hδ : 0 < δ) (hδ6 : δ ≤ 6)
    (n : ℕ) : (haarPathHaarMassBound G hδ hδ6).δ n = δ := rfl

theorem haarPathHaarMassBound_c₁ (G : FixedVolumeGeometry) {δ : ℝ} (hδ : 0 < δ) (hδ6 : δ ≤ 6)
    (n : ℕ) :
    (haarPathHaarMassBound G hδ hδ6).c₁ n = (δ / (2400 * (G.sites n : ℝ) ^ 4)) ^ 2 :=
  haarSingleLinkMassRate_pathFactor G δ n

/-- Unconditional form of `SingleLinkHaarMassRate.quartic_tendsto_atTop_of_balance`: for fixed
`0 < δ < ε`, if the balance exponent with the actual Haar factor `(δ / (2400 L_n⁴))²` tends to
`+∞` along a fixed-volume path, then `β_n a_n⁴ → ∞`. -/
theorem haar_quartic_tendsto_atTop_of_balance (P : FixedVolumeCutoffPath) {δ ε : ℝ}
    (hδ : 0 < δ) (hεδ : δ < ε)
    (hbal : Tendsto (fun n => balanceExponent (P.sites n) (P.β n) ε δ
      ((δ / (2400 * (P.sites n : ℝ) ^ 4)) ^ 2)) atTop atTop) :
    Tendsto (fun n => P.β n * P.a n ^ 4) atTop atTop := by
  refine haarSingleLinkMassRate.quartic_tendsto_atTop_of_balance P hδ hεδ ?_
  simpa only [haarSingleLinkMassRate_pathFactor] using hbal

/-- Unconditional form of `SingleLinkHaarMassRate.balanceExponent_tendsto_atBot_of_quartic_bounded`:
bounded `β_n a_n⁴` never balances the actual Haar factor at a fixed threshold. -/
theorem haar_balanceExponent_tendsto_atBot_of_quartic_bounded (P : FixedVolumeCutoffPath)
    {δ ε M : ℝ} (hδ : 0 < δ) (hquartic : ∀ n, P.β n * P.a n ^ 4 ≤ M) :
    Tendsto (fun n => balanceExponent (P.sites n) (P.β n) ε δ
      ((δ / (2400 * (P.sites n : ℝ) ^ 4)) ^ 2)) atTop atBot := by
  have h := haarSingleLinkMassRate.balanceExponent_tendsto_atBot_of_quartic_bounded P (ε := ε)
    hδ hquartic
  simpa only [haarSingleLinkMassRate_pathFactor] using h

/-- Unconditional form of `SingleLinkHaarMassRate.wilsonTail_tendsto_zero_of_rate_balance`, with
`log (1 / c₀) = log 160000` and `p = 2`. -/
theorem haar_wilsonTail_tendsto_zero_of_rate_balance (P : FixedVolumeCutoffPath) {δ ε : ℝ}
    (hδ : 0 < δ) (hδ6 : δ ≤ 6)
    (hbal : Tendsto (fun n => P.β n * (ε - δ) - 4 * (P.sites n : ℝ) ^ 4 *
      (Real.log 160000 + 2 * Real.log (6 * (P.sites n : ℝ) ^ 4 / δ))) atTop atTop) :
    Tendsto (fun n => (wilsonMeasure (gaugeHaarMeasure (P.sites n)) (P.β n)).real
      {U | ε ≤ wilsonAction 1 U}) atTop (𝓝 0) := by
  apply haarSingleLinkMassRate.wilsonTail_tendsto_zero_of_rate_balance P hδ hδ6
  have hc : Real.log (1 / haarSingleLinkMassRate.c₀) = Real.log 160000 := by
    rw [haarSingleLinkMassRate_c₀]
    norm_num
  simpa only [hc, haarSingleLinkMassRate_p] using hbal

/-! ## 2. Every ingredient (H) at bounded thresholds has vanishing per-link factors -/

theorem haarVacuumSublevelMass_mono (L : ℕ) [NeZero L] {δ δ' : ℝ} (h : δ ≤ δ') :
    haarVacuumSublevelMass L δ ≤ haarVacuumSublevelMass L δ' := by
  unfold haarVacuumSublevelMass
  exact measureReal_mono (fun U (hU : wilsonAction 1 U < δ) => lt_of_lt_of_le hU h)
    (measure_ne_top _ _)

/-- A per-link lower bound `c ^ (4 L⁴) ≤ c(L, δ)` forces
`log c ≤ log 2 / 8 - log (L⁴ / (16 δ)) / 64` once `L ≥ 2` and `16 δ ≤ L⁴`. The input is the
private-link upper bound `log_haarVacuumSublevelMass_le`. -/
theorem log_le_of_pow_le_haarVacuumSublevelMass {L : ℕ} [NeZero L] (hL : 2 ≤ L) {δ c : ℝ}
    (hδ : 0 < δ) (hδL : 16 * δ ≤ (L : ℝ) ^ 4) (hc : 0 < c)
    (hmass : c ^ (4 * L ^ 4) ≤ haarVacuumSublevelMass L δ) :
    Real.log c ≤ Real.log 2 / 8 - Real.log ((L : ℝ) ^ 4 / (16 * δ)) / 64 := by
  have hm4 : (L : ℝ) ^ 4 ≤ 4 * (privateCount L : ℝ) := by
    exact_mod_cast pow_four_le_four_mul_privateCount hL
  have hm2 : 2 * (privateCount L : ℝ) ≤ (L : ℝ) ^ 4 := by
    exact_mod_cast privateCount_mul_two_le L
  have hδm : 4 * δ ≤ (privateCount L : ℝ) := by nlinarith
  have hup := log_haarVacuumSublevelMass_le L hL hδ hδm
  have hcpow : 0 < c ^ (4 * L ^ 4) := pow_pos hc _
  have hlog := Real.log_le_log hcpow hmass
  rw [Real.log_pow] at hlog
  push_cast at hlog
  have hLpos : (0 : ℝ) < (L : ℝ) ^ 4 := by
    have : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
    positivity
  have hq : 1 ≤ (L : ℝ) ^ 4 / (16 * δ) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hY : 0 ≤ Real.log ((L : ℝ) ^ 4 / (16 * δ)) := Real.log_nonneg hq
  have hmpos : (0 : ℝ) < privateCount L := by linarith
  have hmono : Real.log ((L : ℝ) ^ 4 / (16 * δ)) ≤
      Real.log ((privateCount L : ℝ) / (4 * δ)) := by
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h1 : (privateCount L : ℝ) * Real.log 2 ≤ (L : ℝ) ^ 4 / 2 * Real.log 2 :=
    mul_le_mul_of_nonneg_right (by linarith) hlog2
  have h2 : (L : ℝ) ^ 4 / 16 * Real.log ((L : ℝ) ^ 4 / (16 * δ)) ≤
      (privateCount L : ℝ) / 4 * Real.log ((privateCount L : ℝ) / (4 * δ)) := by
    calc (L : ℝ) ^ 4 / 16 * Real.log ((L : ℝ) ^ 4 / (16 * δ))
        ≤ (L : ℝ) ^ 4 / 16 * Real.log ((privateCount L : ℝ) / (4 * δ)) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ ≤ (privateCount L : ℝ) / 4 * Real.log ((privateCount L : ℝ) / (4 * δ)) :=
          mul_le_mul_of_nonneg_right (by linarith) (hY.trans hmono)
  have key : (4 * (L : ℝ) ^ 4) * Real.log c ≤
      (4 * (L : ℝ) ^ 4) * (Real.log 2 / 8 - Real.log ((L : ℝ) ^ 4 / (16 * δ)) / 64) := by
    nlinarith
  exact le_of_mul_le_mul_left key (by positivity)

/-- Along a fixed-volume geometry, every ingredient (H) whose thresholds stay below a fixed `δbar`
has `log c₁(n) → -∞`. -/
theorem pathHaarMassBound_log_c₁_tendsto_atBot {G : FixedVolumeGeometry}
    (H : PathHaarMassBound G) {δbar : ℝ} (hδ : ∀ n, H.δ n ≤ δbar) :
    Tendsto (fun n => Real.log (H.c₁ n)) atTop atBot := by
  have hδbar : 0 < δbar := (H.δ_pos 0).trans_le (hδ 0)
  have hY : Tendsto (fun n => Real.log ((G.sites n : ℝ) ^ 4 / (16 * δbar))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (G.sites_pow_four_tendsto_atTop.atTop_div_const (by positivity))
  have h1 : Tendsto (fun n => -(Real.log ((G.sites n : ℝ) ^ 4 / (16 * δbar)) / 64) +
      Real.log 2 / 8) atTop atBot :=
    tendsto_atBot_add_const_right _ _
      (tendsto_neg_atTop_atBot.comp (hY.atTop_div_const (by norm_num : (0 : ℝ) < 64)))
  have h2 : Tendsto (fun n => Real.log 2 / 8 -
      Real.log ((G.sites n : ℝ) ^ 4 / (16 * δbar)) / 64) atTop atBot :=
    h1.congr fun n => by ring
  refine tendsto_atBot_mono' atTop ?_ h2
  filter_upwards [G.sites_tendsto_atTop.eventually_ge_atTop 2,
    G.sites_pow_four_tendsto_atTop.eventually_ge_atTop (16 * δbar)] with n hn2 hn16
  exact log_le_of_pow_le_haarVacuumSublevelMass hn2 hδbar hn16 (H.c₁_pos n)
    ((H.mass_lower n).trans (haarVacuumSublevelMass_mono _ (hδ n)))

/-- Every ingredient (H) with bounded thresholds has per-link factors tending to zero. -/
theorem pathHaarMassBound_c₁_tendsto_zero {G : FixedVolumeGeometry} (H : PathHaarMassBound G)
    {δbar : ℝ} (hδ : ∀ n, H.δ n ≤ δbar) : Tendsto H.c₁ atTop (𝓝 0) := by
  have h := Real.tendsto_exp_atBot.comp (pathHaarMassBound_log_c₁_tendsto_atBot H hδ)
  refine h.congr fun n => ?_
  simp only [Function.comp_apply, Real.exp_log (H.c₁_pos n)]

/-- The constant-factor form of ingredient (H) is false for the actual Haar measure: along any
fixed-volume geometry, no `PathHaarMassBound` has a fixed threshold and a constant per-link
factor. -/
theorem no_constant_factor_pathHaarMassBound (G : FixedVolumeGeometry) :
    ¬ ∃ (H : PathHaarMassBound G) (δ c : ℝ), (∀ n, H.δ n = δ) ∧ ∀ n, H.c₁ n = c := by
  rintro ⟨H, δ, c, hδ, hc⟩
  have h0 := pathHaarMassBound_c₁_tendsto_zero H (δbar := δ) fun n => (hδ n).le
  have hcst : Tendsto H.c₁ atTop (𝓝 c) := by
    have hfun : H.c₁ = fun _ => c := funext hc
    rw [hfun]
    exact tendsto_const_nhds
  have hc0 : c = 0 := tendsto_nhds_unique hcst h0
  have hpos := H.c₁_pos 0
  rw [hc 0, hc0] at hpos
  exact lt_irrefl 0 hpos

/-- The hypotheses `hδ : ∀ n, H.δ n = δ` and `hc₁ : ∀ n, H.c₁ n = c₁` of the cutoff-path theorem
`wilsonTail_tendsto_zero_of_supercritical` are jointly unsatisfiable: that theorem is vacuous. -/
theorem supercritical_hypotheses_unsatisfiable (P : FixedVolumeCutoffPath)
    (H : PathHaarMassBound P.toFixedVolumeGeometry) (δ c₁ : ℝ) :
    ¬ ((∀ n, H.δ n = δ) ∧ ∀ n, H.c₁ n = c₁) := fun h =>
  no_constant_factor_pathHaarMassBound P.toFixedVolumeGeometry ⟨H, δ, c₁, h.1, h.2⟩

/-- The side condition `∀ᶠ n, H.c₁ n ≤ cbar` of the cutoff-path divergence theorems holds for
every ingredient (H) with bounded thresholds and every `cbar > 0`. -/
theorem pathHaarMassBound_eventually_c₁_le {G : FixedVolumeGeometry} (H : PathHaarMassBound G)
    {δbar : ℝ} (hδ : ∀ n, H.δ n ≤ δbar) {cbar : ℝ} (hcbar : 0 < cbar) :
    ∀ᶠ n in atTop, H.c₁ n ≤ cbar :=
  ((pathHaarMassBound_c₁_tendsto_zero H hδ).eventually (gt_mem_nhds hcbar)).mono
    fun _ hn => hn.le

/-- `ClauseZeroCouplingSchedule.composedTailBound_tendsto_atTop` without its side condition on
the factors: along every Clause (0) schedule and for every ingredient (H) with bounded
thresholds, the composed total-action bound diverges. -/
theorem clauseZero_composedTailBound_tendsto_atTop {P : FixedVolumeCutoffPath}
    (S : ClauseZeroCouplingSchedule P) (H : PathHaarMassBound P.toFixedVolumeGeometry)
    {δbar : ℝ} (hδ : ∀ n, H.δ n ≤ δbar) (ε : ℝ) :
    Tendsto (fun n => composedTailBound (P.sites n) (P.β n) ε (H.δ n) (H.c₁ n)) atTop atTop :=
  S.composedTailBound_tendsto_atTop H (cbar := 1 / 2) (by norm_num)
    (pathHaarMassBound_eventually_c₁_le H hδ (by norm_num))

/-! ## 3. The actual total-action tail tends to one along slowly coupled paths -/

/-- The actual Wilson total-action tail `P_n(S₁ ≥ ε)` at cutoff `n` of a path. -/
def pathTail (P : FixedVolumeCutoffPath) (ε : ℝ) (n : ℕ) : ℝ :=
  (wilsonMeasure (gaugeHaarMeasure (P.sites n)) (P.β n)).real {U | ε ≤ wilsonAction 1 U}

/-- A constant plus a multiple of a smaller power of `x` is eventually below `x ^ a`. -/
theorem eventually_add_mul_rpow_le_rpow (C D : ℝ) {r a : ℝ} (hra : r < a) (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop, C + D * x ^ r ≤ x ^ a := by
  have h0 : Tendsto (fun x : ℝ => |D| * x ^ (r - a)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (y := a - r) (by linarith)).const_mul |D|
    simpa only [neg_sub, mul_zero] using h
  have h1 := (h0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  have h3 := (tendsto_rpow_atTop ha).eventually_ge_atTop (2 * C)
  filter_upwards [h1, h3, eventually_gt_atTop 0] with x h1 h3 hx
  have hxa : 0 < x ^ a := Real.rpow_pos_of_pos hx a
  have hsplit : x ^ r = x ^ (r - a) * x ^ a := by
    rw [← Real.rpow_add hx, sub_add_cancel]
  have hD : D * x ^ r ≤ |D| * x ^ (r - a) * x ^ a := by
    rw [hsplit, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self D) (Real.rpow_nonneg hx.le _)) hxa.le
  have h4 : |D| * x ^ (r - a) * x ^ a ≤ 1 / 2 * x ^ a :=
    mul_le_mul_of_nonneg_right h1.le hxa.le
  linarith

/-- Along a fixed-volume path, a coupling `β_n ≤ A + B (1/a_n)^r` with `r < 1/32` eventually
satisfies `2400 (β_n + 1) ≤ L_n ^ s` for `s = (max r 0 + 1/32) / 2 < 1/32`, where
`L_n = side / a_n`. -/
theorem eventually_rpow_bound_of_le_rpow_spacing (P : FixedVolumeCutoffPath) {A B r : ℝ}
    (hr : r < 1 / 32) (hβ : ∀ᶠ n in atTop, P.β n ≤ A + B * (1 / P.a n) ^ r) :
    ∀ᶠ n in atTop, 2400 * (P.β n + 1) ≤ (P.sites n : ℝ) ^ ((max r 0 + 1 / 32) / 2) := by
  have hr0 := le_max_left r 0
  have h0 := le_max_right r 0
  have hmax : max r 0 < 1 / 32 := max_lt hr (by norm_num)
  have hrs : r < (max r 0 + 1 / 32) / 2 := by linarith
  have hs : 0 < (max r 0 + 1 / 32) / 2 := by linarith
  have hev := eventually_add_mul_rpow_le_rpow (2400 * (A + 1)) (2400 * B / P.side ^ r) hrs hs
  filter_upwards [hβ, P.sites_tendsto_atTop_real.eventually hev] with n hn hL
  have hside : 0 < P.side := P.side_pos
  have ha : 1 / P.a n = (P.sites n : ℝ) / P.side := by
    rw [P.sites_eq_side_div n]
    field_simp [(P.a_pos n).ne', hside.ne']
  rw [ha, Real.div_rpow (Nat.cast_nonneg _) hside.le] at hn
  have heq : 2400 * (A + B * ((P.sites n : ℝ) ^ r / P.side ^ r) + 1) =
      2400 * (A + 1) + 2400 * B / P.side ^ r * (P.sites n : ℝ) ^ r := by ring
  nlinarith

/-- Power-law necessity along fixed-volume paths. Fix `ε > 0`. If the bare coupling of a
fixed-volume cutoff path is eventually at most `A + B (1/a_n)^r` with `r < 1/32`, the actual
total-action tail `P_n(S₁ ≥ ε)` tends to one. The proof feeds
`haarWilsonMeasure_action_tail_tendsto_one_of_le_rpow` with `L_n = side / a_n`. -/
theorem wilsonTail_tendsto_one_of_le_rpow_spacing (P : FixedVolumeCutoffPath) {A B r ε : ℝ}
    (hε : 0 < ε) (hr : r < 1 / 32)
    (hβ : ∀ᶠ n in atTop, P.β n ≤ A + B * (1 / P.a n) ^ r) :
    Tendsto (pathTail P ε) atTop (𝓝 1) := by
  have hmax : max r 0 < 1 / 32 := max_lt hr (by norm_num)
  have hs : (max r 0 + 1 / 32) / 2 < 1 / 32 := by linarith
  exact haarWilsonMeasure_action_tail_tendsto_one_of_le_rpow hε hs P.sites P.sites_tendsto_atTop
    P.β P.β_nonneg (eventually_rpow_bound_of_le_rpow_spacing P hr hβ)

/-- Logarithmic necessity along fixed-volume paths. Fix `ε > 0`. If the bare coupling of a
fixed-volume cutoff path is eventually at most `A + B log (1/a_n)`, the asymptotic-freedom
form, the actual total-action tail `P_n(S₁ ≥ ε)` tends to one. -/
theorem wilsonTail_tendsto_one_of_logarithmic (P : FixedVolumeCutoffPath) {A B ε : ℝ}
    (hε : 0 < ε) (hlog : ∀ᶠ n in atTop, P.β n ≤ A + B * Real.log (1 / P.a n)) :
    Tendsto (pathTail P ε) atTop (𝓝 1) := by
  apply wilsonTail_tendsto_one_of_le_rpow_spacing P (A := A) (B := 64 * max B 0)
    (r := 1 / 64) hε (by norm_num)
  filter_upwards [hlog, P.spacing_tendsto.eventually (gt_mem_nhds one_pos)] with n hn ha
  have hapos := P.a_pos n
  have hy : 1 ≤ 1 / P.a n := by
    rw [le_div_iff₀ hapos]
    linarith
  have hlogy : 0 ≤ Real.log (1 / P.a n) := Real.log_nonneg hy
  have hle := Real.log_le_rpow_div (x := 1 / P.a n) (ε := 1 / 64) (by positivity) (by norm_num)
  have h1 : B * Real.log (1 / P.a n) ≤ max B 0 * Real.log (1 / P.a n) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hlogy
  have h2 : max B 0 * Real.log (1 / P.a n) ≤
      max B 0 * ((1 / P.a n) ^ (1 / 64 : ℝ) / (1 / 64)) :=
    mul_le_mul_of_nonneg_left hle (le_max_right _ _)
  have h3 : max B 0 * ((1 / P.a n) ^ (1 / 64 : ℝ) / (1 / 64)) =
      64 * max B 0 * (1 / P.a n) ^ (1 / 64 : ℝ) := by ring
  linarith

/-- Every Clause (0) coupling schedule is logarithmic in the spacing:
`β_n ≤ xLand + max Bmax 0 · (log aIR + log (1/a_n)) / log 13`. -/
theorem clauseZero_coupling_le_log {P : FixedVolumeCutoffPath}
    (S : ClauseZeroCouplingSchedule P) (n : ℕ) :
    P.β n ≤ (S.xLand + max S.Bmax 0 * Real.log S.aIR / Real.log 13) +
      max S.Bmax 0 / Real.log 13 * Real.log (1 / P.a n) := by
  have hβ := S.coupling_le n
  have ha := S.spacing_le n
  have hl13 : 0 < Real.log 13 := Real.log_pos (by norm_num)
  have hapos := P.a_pos n
  have h13 : (0 : ℝ) < 13 ^ S.depth n := by positivity
  have hpow : (13 : ℝ) ^ S.depth n ≤ S.aIR / P.a n := by
    rw [le_div_iff₀ hapos]
    rw [le_div_iff₀ h13] at ha
    linarith [mul_comm (P.a n) ((13 : ℝ) ^ S.depth n)]
  have hd : (S.depth n : ℝ) * Real.log 13 ≤ Real.log S.aIR + Real.log (1 / P.a n) := by
    have h := Real.log_le_log h13 hpow
    rw [Real.log_pow, Real.log_div S.aIR_pos.ne' hapos.ne'] at h
    rw [one_div, Real.log_inv]
    linarith
  have hd' : (S.depth n : ℝ) ≤ (Real.log S.aIR + Real.log (1 / P.a n)) / Real.log 13 := by
    rw [le_div_iff₀ hl13]
    exact hd
  have hB : S.Bmax * (S.depth n : ℝ) ≤ max S.Bmax 0 * (S.depth n : ℝ) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
  have hB2 : max S.Bmax 0 * (S.depth n : ℝ) ≤
      max S.Bmax 0 * ((Real.log S.aIR + Real.log (1 / P.a n)) / Real.log 13) :=
    mul_le_mul_of_nonneg_left hd' (le_max_right _ _)
  have heq : max S.Bmax 0 * ((Real.log S.aIR + Real.log (1 / P.a n)) / Real.log 13) =
      max S.Bmax 0 * Real.log S.aIR / Real.log 13 +
        max S.Bmax 0 / Real.log 13 * Real.log (1 / P.a n) := by ring
  linarith

/-- Along every Clause (0) coupling schedule, for every `ε > 0`, the actual total-action tail
tends to one. -/
theorem clauseZero_wilsonTail_tendsto_one {P : FixedVolumeCutoffPath}
    (S : ClauseZeroCouplingSchedule P) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (pathTail P ε) atTop (𝓝 1) :=
  wilsonTail_tendsto_one_of_logarithmic P hε (Eventually.of_forall (clauseZero_coupling_le_log S))

/-- The canonical SU(2) Clause (0) path (blocking factor `b`, `m` infrared blocks of size `aIR`)
does not concentrate the total action: for every `ε > 0`, `P_K(S₁ ≥ ε) → 1` as the depth
`K → ∞`, although `β_K = K c₀(b,2) + 1/24 → ∞`. -/
theorem clauseZeroCanonicalPath_wilsonTail_tendsto_one (b m : ℕ) (hb : 13 ≤ b)
    (hb_odd : b % 2 = 1) (hm : 0 < m) (aIR : ℝ) (haIR : 0 < aIR) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (pathTail (clauseZeroCanonicalPath b m hb hb_odd hm aIR haIR) ε) atTop (𝓝 1) :=
  clauseZero_wilsonTail_tendsto_one (clauseZeroCanonicalSchedule b m hb hb_odd hm aIR haIR) hε

/-- On the canonical SU(2) Clause (0) path the action-density tails vanish, the total-action
tails tend to one, and the bare coupling diverges. -/
theorem clauseZeroCanonicalPath_density_vs_total (b m : ℕ) (hb : 13 ≤ b)
    (hb_odd : b % 2 = 1) (hm : 0 < m) (aIR : ℝ) (haIR : 0 < aIR) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (wilsonMeasure (gaugeHaarMeasure
      ((clauseZeroCanonicalPath b m hb hb_odd hm aIR haIR).sites n))
      ((clauseZeroCanonicalPath b m hb hb_odd hm aIR haIR).β n)).real
      {U | ε * ((clauseZeroCanonicalPath b m hb hb_odd hm aIR haIR).sites n : ℝ) ^ 4 ≤
        wilsonAction 1 U}) atTop (𝓝 0) ∧
    Tendsto (pathTail (clauseZeroCanonicalPath b m hb hb_odd hm aIR haIR) ε) atTop (𝓝 1) ∧
    Tendsto (clauseZeroCanonicalPath b m hb hb_odd hm aIR haIR).β atTop atTop :=
  ⟨clauseZeroCanonicalPath_densityTail_tendsto_zero b m hb hb_odd hm aIR haIR hε,
    clauseZeroCanonicalPath_wilsonTail_tendsto_one b m hb hb_odd hm aIR haIR hε,
    clauseZeroCanonicalPath_coupling_tendsto_atTop b m hb hb_odd hm aIR haIR⟩

/-! ## 4. Consequences: the balance and gain hypotheses fail along slowly coupled paths -/

/-- If the actual tail tends to one along a path, then for every ingredient (H) the balance
exponent is eventually below every positive constant. -/
theorem balanceExponent_eventually_lt_of_tail_tendsto_one (P : FixedVolumeCutoffPath)
    (H : PathHaarMassBound P.toFixedVolumeGeometry) {ε : ℝ}
    (htail : Tendsto (pathTail P ε) atTop (𝓝 1)) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n in atTop, balanceExponent (P.sites n) (P.β n) ε (H.δ n) (H.c₁ n) < c := by
  have hlt : Real.exp (-c) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  filter_upwards [htail.eventually (lt_mem_nhds hlt)] with n hn
  have hle := wilsonTail_le_exp_neg_balance P H ε n
  have h : Real.exp (-c) <
      Real.exp (-balanceExponent (P.sites n) (P.β n) ε (H.δ n) (H.c₁ n)) :=
    lt_of_lt_of_le hn hle
  rw [Real.exp_lt_exp] at h
  linarith

/-- Along every path with at most logarithmic coupling, the balance hypothesis of
`wilsonTail_tendsto_zero_of_balance` fails for every ingredient (H): no thresholds and no
per-link factors make the balance exponent diverge. -/
theorem not_balance_of_logarithmic (P : FixedVolumeCutoffPath)
    (H : PathHaarMassBound P.toFixedVolumeGeometry) {A B ε : ℝ} (hε : 0 < ε)
    (hlog : ∀ᶠ n in atTop, P.β n ≤ A + B * Real.log (1 / P.a n)) :
    ¬ Tendsto (fun n => balanceExponent (P.sites n) (P.β n) ε (H.δ n) (H.c₁ n)) atTop atTop := by
  intro hbal
  have h1 := balanceExponent_eventually_lt_of_tail_tendsto_one P H
    (wilsonTail_tendsto_one_of_logarithmic P hε hlog) one_pos
  obtain ⟨n, hn1, hn2⟩ := (h1.and (hbal.eventually_ge_atTop 1)).exists
  linarith

/-- The total-action tail is bounded by `exp (-gain)`, where `gain` is the entropy-versus-coupling
quantity of `haarWilsonMeasure_action_tail_tendsto_varying_volume`. -/
theorem wilsonTail_le_exp_neg_repositoryGain {L : ℕ} [NeZero L] {β δ ε : ℝ} (hβ : 0 ≤ β)
    (hδ : 0 < δ) :
    (wilsonMeasure (gaugeHaarMeasure L) β).real {U | ε ≤ wilsonAction 1 U} ≤
      Real.exp (-(β * (ε - δ) + Real.log (haarVacuumSublevelMass L δ))) := by
  have hc := haarVacuumSublevelMass_pos (L := L) hδ
  refine (haarWilsonMeasure_action_tail hβ hδ).trans_eq ?_
  rw [neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log hc, div_eq_mul_inv]

/-- If the actual tail tends to one along a sequence of tori, then for every choice of positive
thresholds the gain `β_n (ε - δ_n) + log c(L_n, δ_n)` is eventually below every positive
constant. -/
theorem repositoryGain_eventually_lt_of_tail_tendsto_one (sizes : ℕ → ℕ)
    [∀ n, NeZero (sizes n)] (β δ : ℕ → ℝ) {ε : ℝ} (hβ : ∀ n, 0 ≤ β n) (hδ : ∀ n, 0 < δ n)
    (htail : Tendsto (fun n => (wilsonMeasure (gaugeHaarMeasure (sizes n)) (β n)).real
      {U | ε ≤ wilsonAction 1 U}) atTop (𝓝 1)) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n in atTop, β n * (ε - δ n) + Real.log (haarVacuumSublevelMass (sizes n) (δ n)) < c := by
  have hlt : Real.exp (-c) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  filter_upwards [htail.eventually (lt_mem_nhds hlt)] with n hn
  have h := lt_of_lt_of_le hn (wilsonTail_le_exp_neg_repositoryGain (L := sizes n) (ε := ε)
    (hβ n) (hδ n))
  rw [Real.exp_lt_exp] at h
  linarith

/-- Along every fixed-volume path with at most logarithmic coupling, the hypothesis `hgain` of
`haarWilsonMeasure_action_tail_tendsto_varying_volume` fails for every choice of positive
thresholds `δ_n`. -/
theorem not_repositoryGain_of_logarithmic (P : FixedVolumeCutoffPath) {A B ε : ℝ} (hε : 0 < ε)
    (hlog : ∀ᶠ n in atTop, P.β n ≤ A + B * Real.log (1 / P.a n)) (δ : ℕ → ℝ)
    (hδ : ∀ n, 0 < δ n) :
    ¬ Tendsto (fun n => P.β n * (ε - δ n) +
      Real.log (haarVacuumSublevelMass (P.sites n) (δ n))) atTop atTop := by
  intro hgain
  have h1 := repositoryGain_eventually_lt_of_tail_tendsto_one P.sites P.β δ P.β_nonneg hδ
    (wilsonTail_tendsto_one_of_logarithmic P hε hlog) one_pos
  obtain ⟨n, hn1, hn2⟩ := (h1.and (hgain.eventually_ge_atTop 1)).exists
  linarith

/-- The explicit sufficient coupling along a fixed-volume geometry: for fixed `0 < δ < ε` with
`δ ≤ 96`, `β_n = (8 L_n⁴ log (2400 L_n⁴ / δ) + n) / (ε - δ)`. -/
def haarSchedulePath (G : FixedVolumeGeometry) {ε δ : ℝ} (hδ : 0 < δ) (hδε : δ < ε)
    (hδ96 : δ ≤ 96) : FixedVolumeCutoffPath where
  toFixedVolumeGeometry := G
  β n := (8 * (G.sites n : ℝ) ^ 4 * Real.log (2400 * (G.sites n : ℝ) ^ 4 / δ) + n) / (ε - δ)
  β_nonneg n := by
    have hL4 : (1 : ℝ) ≤ (G.sites n : ℝ) ^ 4 := one_le_pow₀ (G.one_le_sites_real n)
    have harg : 1 ≤ 2400 * (G.sites n : ℝ) ^ 4 / δ := by
      rw [le_div_iff₀ hδ]
      nlinarith
    have hlog := Real.log_nonneg harg
    apply div_nonneg _ (sub_pos.mpr hδε).le
    positivity

/-- Along every fixed-volume geometry the explicit schedule concentrates the actual total action,
and it balances the actual Haar factor, so its `β_n a_n⁴` diverges. -/
theorem haarSchedulePath_tail_tendsto_zero (G : FixedVolumeGeometry) {ε δ : ℝ} (hδ : 0 < δ)
    (hδε : δ < ε) (hδ96 : δ ≤ 96) :
    Tendsto (pathTail (haarSchedulePath G hδ hδε hδ96) ε) atTop (𝓝 0) ∧
    Tendsto (fun n => (haarSchedulePath G hδ hδε hδ96).β n * G.a n ^ 4) atTop atTop := by
  have hεδ : ε - δ ≠ 0 := (sub_pos.mpr hδε).ne'
  have hgain : Tendsto (fun n => (haarSchedulePath G hδ hδε hδ96).β n * (ε - δ) -
      8 * (G.sites n : ℝ) ^ 4 * Real.log (2400 * (G.sites n : ℝ) ^ 4 / δ)) atTop atTop := by
    refine tendsto_natCast_atTop_atTop.congr fun n => ?_
    show (n : ℝ) = (8 * (G.sites n : ℝ) ^ 4 * Real.log (2400 * (G.sites n : ℝ) ^ 4 / δ) + n) /
      (ε - δ) * (ε - δ) - 8 * (G.sites n : ℝ) ^ 4 * Real.log (2400 * (G.sites n : ℝ) ^ 4 / δ)
    rw [div_mul_cancel₀ _ hεδ]
    ring
  refine ⟨(haarWilsonMeasure_action_tail_tendsto_of_gain hδ hδ96 G.sites
    (haarSchedulePath G hδ hδε hδ96).β (haarSchedulePath G hδ hδε hδ96).β_nonneg hgain).2, ?_⟩
  refine haar_quartic_tendsto_atTop_of_balance (haarSchedulePath G hδ hδε hδ96) hδ hδε ?_
  refine hgain.congr fun n => ?_
  have hL : (0 : ℝ) < (G.sites n : ℝ) := G.sites_pos_real n
  have hq : 0 < 2400 * (G.sites n : ℝ) ^ 4 / δ := by positivity
  have hlog : Real.log (1 / (δ / (2400 * (G.sites n : ℝ) ^ 4)) ^ 2) =
      2 * Real.log (2400 * (G.sites n : ℝ) ^ 4 / δ) := by
    rw [one_div, ← inv_pow, inv_div, Real.log_pow]
    push_cast
    ring
  change _ = (haarSchedulePath G hδ hδε hδ96).β n * (ε - δ) -
    4 * (G.sites n : ℝ) ^ 4 * Real.log (1 / (δ / (2400 * (G.sites n : ℝ) ^ 4)) ^ 2)
  rw [hlog]
  ring

/-- Dichotomy along every fixed-volume geometry, for fixed `0 < δ < ε` with `δ ≤ 96`: the
explicit schedule `β_n = (8 L_n⁴ log (2400 L_n⁴ / δ) + n) / (ε - δ)` drives the actual
total-action tail to zero, while every coupling `β_n ≤ A + B log (1 / a_n)` drives it to one. -/
theorem fixedVolume_concentration_dichotomy (G : FixedVolumeGeometry) {ε δ : ℝ} (hδ : 0 < δ)
    (hδε : δ < ε) (hδ96 : δ ≤ 96) :
    Tendsto (pathTail (haarSchedulePath G hδ hδε hδ96) ε) atTop (𝓝 0) ∧
    ∀ (P : FixedVolumeCutoffPath), P.toFixedVolumeGeometry = G → ∀ A B : ℝ,
      (∀ᶠ n in atTop, P.β n ≤ A + B * Real.log (1 / P.a n)) →
        Tendsto (pathTail P ε) atTop (𝓝 1) :=
  ⟨(haarSchedulePath_tail_tendsto_zero G hδ hδε hδ96).1, fun P _ _ _ hlog =>
    wilsonTail_tendsto_one_of_logarithmic P (hδ.trans hδε) hlog⟩

/-! ## 5. Anti-vacuity: the structures of the cutoff-path module -/

/-- The canonical SU(2) Clause (0) cutoff path with blocking factor `b = 13`, one infrared block
(`m = 1`) and infrared spacing `aIR = 1`: `a_n = 13^(-n)`, `L_n = 13^n`,
`β_n = n c₀(13,2) + 1/24`. -/
def canonicalCutoffPath : FixedVolumeCutoffPath :=
  clauseZeroCanonicalPath 13 1 le_rfl (by norm_num) one_pos 1 one_pos

theorem canonicalCutoffPath_sites (n : ℕ) : canonicalCutoffPath.sites n = 13 ^ n := by
  show 1 * 13 ^ n = 13 ^ n
  ring

theorem canonicalCutoffPath_β (n : ℕ) :
    canonicalCutoffPath.β n = (n : ℝ) * sussmanOneLoopCoeff 13 2 + 1 / 24 :=
  canonicalSU2Flow_wilsonBeta_zero 13 n le_rfl (by norm_num)

/-- The canonical path is not a constant model: its coupling strictly increases from `n = 0` to
`n = 1` and diverges, and its lattice size diverges. -/
theorem canonicalCutoffPath_nondegenerate :
    canonicalCutoffPath.β 0 < canonicalCutoffPath.β 1 ∧
    Tendsto canonicalCutoffPath.β atTop atTop ∧
    Tendsto canonicalCutoffPath.sites atTop atTop := by
  have hc := sussmanOneLoopCoeff_pos (L := 13) (N := 2) (by norm_num) le_rfl
  refine ⟨?_, clauseZeroCanonicalPath_coupling_tendsto_atTop 13 1 le_rfl (by norm_num) one_pos 1
    one_pos, canonicalCutoffPath.sites_tendsto_atTop⟩
  rw [canonicalCutoffPath_β, canonicalCutoffPath_β]
  push_cast
  linarith

/-- The canonical Clause (0) schedule on `canonicalCutoffPath`. Its block-spin depth is `n`. -/
def canonicalSchedule : ClauseZeroCouplingSchedule canonicalCutoffPath :=
  clauseZeroCanonicalSchedule 13 1 le_rfl (by norm_num) one_pos 1 one_pos

theorem canonicalSchedule_depth (n : ℕ) : canonicalSchedule.depth n = n := rfl

/-- Ingredient (H) on the canonical path at the fixed threshold `δ = 1`, from the actual Haar
measure: `c₁(n) = (1 / (2400 · 13^(4n)))²`. -/
def canonicalHaarFactor : PathHaarMassBound canonicalCutoffPath.toFixedVolumeGeometry :=
  haarPathHaarMassBound canonicalCutoffPath.toFixedVolumeGeometry one_pos (by norm_num)

/-- The explicit ingredient (H) on the canonical path is not a constant model: its factor
strictly decreases from `n = 0` to `n = 1` and tends to zero, while its threshold is fixed. -/
theorem canonicalHaarFactor_nondegenerate :
    (∀ n, canonicalHaarFactor.δ n = 1) ∧
    canonicalHaarFactor.c₁ 1 < canonicalHaarFactor.c₁ 0 ∧
    Tendsto canonicalHaarFactor.c₁ atTop (𝓝 0) := by
  refine ⟨fun n => rfl, ?_, pathHaarMassBound_c₁_tendsto_zero canonicalHaarFactor
    (δbar := 1) fun n => le_rfl⟩
  show (haarPathHaarMassBound canonicalCutoffPath.toFixedVolumeGeometry one_pos _).c₁ 1 <
    (haarPathHaarMassBound canonicalCutoffPath.toFixedVolumeGeometry one_pos _).c₁ 0
  rw [haarPathHaarMassBound_c₁, haarPathHaarMassBound_c₁]
  have h0 : (canonicalCutoffPath.toFixedVolumeGeometry.sites 0 : ℝ) = 1 := by
    rw [show canonicalCutoffPath.toFixedVolumeGeometry.sites 0 = canonicalCutoffPath.sites 0
      from rfl, canonicalCutoffPath_sites]
    norm_num
  have h1 : (canonicalCutoffPath.toFixedVolumeGeometry.sites 1 : ℝ) = 13 := by
    rw [show canonicalCutoffPath.toFixedVolumeGeometry.sites 1 = canonicalCutoffPath.sites 1
      from rfl, canonicalCutoffPath_sites]
    norm_num
  rw [h0, h1]
  norm_num

/-- The single-link rate is not a constant or trivial model: every neighbourhood is nonempty,
it is a proper subset of SU(2) below plaquette scale `32`, its Haar mass is at least
`η² / 160000` on `(0, 1]` and at most `√(η / 8)`, hence tends to zero with `η`. -/
theorem haarSingleLinkMassRate_nondegenerate {η : ℝ} (hη : 0 < η) :
    (haarSingleLinkMassRate.nbhd η).Nonempty ∧
    (η < 32 → haarSingleLinkMassRate.nbhd η ≠ Set.univ) ∧
    (η ≤ 1 → η ^ 2 / 160000 ≤ SU2.haarProbability.real (haarSingleLinkMassRate.nbhd η)) ∧
    SU2.haarProbability.real (haarSingleLinkMassRate.nbhd η) ≤ Real.sqrt (η / 8) := by
  refine ⟨⟨1, one_mem_linkNeighbourhood (by positivity)⟩, fun h32 huniv => ?_, fun h1 => ?_, ?_⟩
  · have hmem : negOne ∈ haarSingleLinkMassRate.nbhd η := by
      rw [huniv]
      exact Set.mem_univ _
    change linkDefect negOne < η / 16 at hmem
    rw [linkDefect_negOne] at hmem
    linarith
  · have h := haarSingleLinkMassRate.mass_rate η hη h1
    rw [haarSingleLinkMassRate_c₀, haarSingleLinkMassRate_p, Real.rpow_two] at h
    linarith
  · have h := singleLinkMass_le_sqrt (η := η / 16) (by positivity)
    change singleLinkMass (η / 16) ≤ Real.sqrt (η / 8)
    have heq : 2 * (η / 16) = η / 8 := by ring
    rwa [heq] at h

/-! ## 6. Anti-vacuity: the varying-volume weak-coupling hypothesis -/

/-- The inputs of `haarWilsonMeasure_action_tail_tendsto_varying_volume`
(`YangMillsWeakCoupling.lean` declares no structure; this bundles the data and the hypothesis
`hgain` that its varying-volume theorem quantifies over), together with growing volume
`sizes → ∞`. -/
structure GrowingVolumeGain (ε : ℝ) where
  sizes : ℕ → ℕ
  [sizes_neZero : ∀ n, NeZero (sizes n)]
  sizes_tendsto : Tendsto sizes atTop atTop
  β : ℕ → ℝ
  δ : ℕ → ℝ
  β_nonneg : ∀ n, 0 ≤ β n
  δ_pos : ∀ n, 0 < δ n
  gain : Tendsto (fun n => β n * (ε - δ n) +
    Real.log (haarVacuumSublevelMass (sizes n) (δ n))) atTop atTop

attribute [instance] GrowingVolumeGain.sizes_neZero

/-- Every inhabitant concentrates the actual total action (the conclusion of the repository
theorem). -/
theorem GrowingVolumeGain.tail_tendsto_zero {ε : ℝ} (G : GrowingVolumeGain ε) :
    Tendsto (fun n => (wilsonMeasure (gaugeHaarMeasure (G.sizes n)) (G.β n)).real
      {U | ε ≤ wilsonAction 1 U}) atTop (𝓝 0) :=
  haarWilsonMeasure_action_tail_tendsto_varying_volume G.sizes G.β G.δ ε G.β_nonneg G.δ_pos
    G.gain

/-- Every inhabitant (with `ε > 0`) has coupling above a power of the volume infinitely often:
for every `a < 1/32`, `L_n ^ a < 2400 (β_n + 1)` frequently. -/
theorem GrowingVolumeGain.frequently_coupling_gt {ε : ℝ} (G : GrowingVolumeGain ε) (hε : 0 < ε)
    {a : ℝ} (ha : a < 1 / 32) :
    ∃ᶠ n in atTop, (G.sizes n : ℝ) ^ a < 2400 * (G.β n + 1) := by
  intro h
  have h' : ∀ᶠ n in atTop, 2400 * (G.β n + 1) ≤ (G.sizes n : ℝ) ^ a :=
    h.mono fun n hn => not_lt.mp hn
  have h1 := haarWilsonMeasure_action_tail_tendsto_one_of_le_rpow hε ha G.sizes G.sizes_tendsto
    G.β G.β_nonneg h'
  have h01 := tendsto_nhds_unique G.tail_tendsto_zero h1
  norm_num at h01

/-- No inhabitant (with `ε > 0`) has bounded coupling: constant-coupling models are excluded. -/
theorem GrowingVolumeGain.not_bounded_coupling {ε : ℝ} (G : GrowingVolumeGain ε) (hε : 0 < ε) :
    ¬ ∃ M : ℝ, ∀ n, G.β n ≤ M := by
  rintro ⟨M, hM⟩
  have hpow : Tendsto (fun n => (G.sizes n : ℝ) ^ (1 / 64 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp (tendsto_natCast_atTop_atTop.comp G.sizes_tendsto)
  have hev := hpow.eventually_ge_atTop (2400 * (M + 1))
  obtain ⟨n, hn1, hn2⟩ :=
    ((G.frequently_coupling_gt hε (a := 1 / 64) (by norm_num)).and_eventually hev).exists
  have := hM n
  linarith

/-- An explicit inhabitant: `L_n = n + 1`, fixed `δ` with `0 < δ < ε`, `δ ≤ 96`, and
`β_n = (8 L_n⁴ log (2400 L_n⁴ / δ) + n) / (ε - δ)`. The gain is at least `n`, by
`log_haarVacuumSublevelMass_ge`. -/
def scheduleGrowingVolumeGain {ε δ : ℝ} (hδ : 0 < δ) (hδε : δ < ε) (hδ96 : δ ≤ 96) :
    GrowingVolumeGain ε where
  sizes n := n + 1
  sizes_tendsto := tendsto_add_atTop_nat 1
  β n := (8 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.log (2400 * ((n + 1 : ℕ) : ℝ) ^ 4 / δ) + n) / (ε - δ)
  δ _ := δ
  β_nonneg n := by
    have hL : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    have hL4 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 4 := one_le_pow₀ hL
    have harg : 1 ≤ 2400 * ((n + 1 : ℕ) : ℝ) ^ 4 / δ := by
      rw [le_div_iff₀ hδ]
      nlinarith
    have hlog := Real.log_nonneg harg
    apply div_nonneg _ (sub_pos.mpr hδε).le
    positivity
  δ_pos _ := hδ
  gain := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    have hL : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    have hL4 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 4 := one_le_pow₀ hL
    have hlow := log_haarVacuumSublevelMass_ge (n + 1) hδ (by nlinarith)
    have hεδ : ε - δ ≠ 0 := (sub_pos.mpr hδε).ne'
    rw [div_mul_cancel₀ _ hεδ]
    linarith

/-- The explicit inhabitant is nondegenerate: volume and coupling both diverge. -/
theorem scheduleGrowingVolumeGain_nondegenerate {ε δ : ℝ} (hδ : 0 < δ) (hδε : δ < ε)
    (hδ96 : δ ≤ 96) :
    Tendsto (scheduleGrowingVolumeGain hδ hδε hδ96).sizes atTop atTop ∧
    Tendsto (scheduleGrowingVolumeGain hδ hδε hδ96).β atTop atTop := by
  refine ⟨tendsto_add_atTop_nat 1, ?_⟩
  have hεδ : 0 < ε - δ := sub_pos.mpr hδε
  refine tendsto_atTop_mono (fun n => ?_) (tendsto_natCast_atTop_atTop.atTop_div_const hεδ)
  have hL : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hL4 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 4 := one_le_pow₀ hL
  have harg : 1 ≤ 2400 * ((n + 1 : ℕ) : ℝ) ^ 4 / δ := by
    rw [le_div_iff₀ hδ]
    nlinarith
  have hlog := Real.log_nonneg harg
  show (n : ℝ) / (ε - δ) ≤
    (8 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.log (2400 * ((n + 1 : ℕ) : ℝ) ^ 4 / δ) + n) / (ε - δ)
  apply div_le_div_of_nonneg_right _ hεδ.le
  have : 0 ≤ 8 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.log (2400 * ((n + 1 : ℕ) : ℝ) ^ 4 / δ) := by
    positivity
  linarith

/-- No inhabitant is carried by a fixed-volume cutoff path with at most logarithmic coupling. -/
theorem no_growingVolumeGain_on_logarithmic_path (P : FixedVolumeCutoffPath) {A B ε : ℝ}
    (hε : 0 < ε) (hlog : ∀ᶠ n in atTop, P.β n ≤ A + B * Real.log (1 / P.a n)) :
    ¬ ∃ G : GrowingVolumeGain ε, G.sizes = P.sites ∧ G.β = P.β := by
  rintro ⟨G, hs, hb⟩
  cases G with
  | mk sizes hsz β δ hβ hδ hgain =>
    dsimp only at hs hb
    subst hs hb
    exact not_repositoryGain_of_logarithmic P hε hlog δ hδ hgain

/-- The hypotheses of the scalar multi-step envelope theorem
`multiStepCarriedForwardRemainderEnvelope_contractive_tube_and_dobrushin_landing` are satisfiable
with strictly positive contraction factor, prior remainder, Hessian constant and infrared
coupling. -/
theorem multiStepEnvelope_hypotheses_satisfiable :
    ∃ q η_prev η_star c_hess β_min β_step β_ir β_star : ℝ,
      0 < q ∧ 0 < η_prev ∧ 0 < c_hess ∧ 0 < β_ir ∧
      0 ≤ q ∧ q < 1 ∧ 0 ≤ η_prev ∧ η_prev ≤ η_star ∧ 0 ≤ c_hess ∧ 0 < β_min ∧
      β_min ≤ β_step ∧ c_hess / β_min ≤ (1 - q) * η_star ∧ 0 ≤ β_ir ∧ β_ir ≤ β_star ∧
      18 * β_star + η_star < 1 :=
  ⟨1 / 2, 1 / 4, 1 / 2, 1, 8, 8, 1 / 40, 1 / 40, by norm_num⟩

/-- Every instance of the hypotheses of the multi-step envelope theorem has infrared coupling
below `1/18`: the theorem lands in the strong-coupling (Dobrushin) regime. -/
theorem multiStepEnvelope_infrared_coupling_lt {η_star β_ir β_star : ℝ} (hη : 0 ≤ η_star)
    (hβ : β_ir ≤ β_star) (htube : 18 * β_star + η_star < 1) : β_ir < 1 / 18 := by
  linarith

/-! ## 7. Anti-vacuity: the unified physical blocking model -/

open YangMillsPhysicalBridges

/-- At zero bare coupling the blocked fiber weight is one for every disintegration. -/
theorem wilsonBlockedFiberWeight_zero_coupling {L : ℕ} [NeZero L]
    (dis : ConditionalBlockFiberDisintegration L) (V : GaugeConfig L) :
    wilsonBlockedFiberWeight dis 0 V = 1 := by
  have := dis.fiber_prob V
  unfold wilsonBlockedFiberWeight wilsonPartition boltzmannWeight
  simp [wilsonAction]

theorem wilsonBlockedNormalizedEffectiveAction_zero_coupling {L : ℕ} [NeZero L]
    (dis : ConditionalBlockFiberDisintegration L) :
    wilsonBlockedNormalizedEffectiveAction dis 0 = fun _ => 0 := by
  funext V
  unfold wilsonBlockedNormalizedEffectiveAction wilsonBlockedEffectiveAction
  rw [wilsonBlockedFiberWeight_zero_coupling, wilsonBlockedFiberWeight_zero_coupling]
  simp

theorem extracted_zero {L : ℕ} [NeZero L] (ext : LinearPlaquetteCouplingExtractor L) :
    extractedCoarseCoupling ext (fun _ => 0) = 0 ∧
      extractedCoarseRemainder ext (fun _ => 0) = fun _ => 0 := by
  have h : extractedCoarseCoupling ext (fun _ => 0) = 0 := ext.proj_const_zero 0
  refine ⟨h, ?_⟩
  funext V
  unfold extractedCoarseRemainder
  rw [h]
  ring

/-- The zero-coupling model: for every disintegration and extractor, the structure is inhabited
at `β_uv = 0` with zero coupling and zero remainder. -/
def zeroCouplingModel (L : ℕ) [NeZero L] (dis : ConditionalBlockFiberDisintegration L)
    (ext : LinearPlaquetteCouplingExtractor L) : UnifiedPhysicalWilsonBlockingModel L where
  dis := dis
  ext := ext
  β_uv := 0
  hβ_uv_nonneg := le_rfl
  hS_measurable := measurable_wilsonAction 0
  hB_measurable := measurable_dyadicLinkBlockMap L
  influence :=
    { β_next := 0
      K_next := fun _ => 0
      linkInfluence := fun _ _ => 0
      η_next := 0
      h_β_nonneg := le_rfl
      h_η_nonneg := le_rfl
      h_influence_nonneg := fun _ _ => le_rfl
      h_osc_K_next := fun _ _ _ _ _ => by simp
      h_influence_uniform := fun _ _ => le_rfl }
  h_β_extracted_eq := by
    rw [wilsonBlockedNormalizedEffectiveAction_zero_coupling, (extracted_zero ext).1]
  h_K_extracted_eq := by
    rw [wilsonBlockedNormalizedEffectiveAction_zero_coupling, (extracted_zero ext).2]

/-- Every model at zero bare coupling is the zero model. -/
theorem unifiedModel_degenerate_of_zero_coupling {L : ℕ} [NeZero L]
    (M : UnifiedPhysicalWilsonBlockingModel L) (h0 : M.β_uv = 0) :
    M.influence.β_next = 0 ∧ M.influence.K_next = fun _ => 0 := by
  have hβ := M.h_β_extracted_eq
  have hK := M.h_K_extracted_eq
  rw [h0, wilsonBlockedNormalizedEffectiveAction_zero_coupling] at hβ hK
  exact ⟨hβ.trans (extracted_zero M.ext).1, hK.trans (extracted_zero M.ext).2⟩

/-- A `ConditionalBlockFiberDisintegration` whose fiber kernel ignores the coarse configuration.
The structure has no field tying the kernel to the fiber of the blocking map, so this is an
inhabitant. -/
def constantKernelDisintegration (L : ℕ) [NeZero L] : ConditionalBlockFiberDisintegration L where
  μ_fine := gaugeHaarMeasure (2 * L)
  μ_coarse := gaugeHaarMeasure L
  fiberKernel := fun _ => gaugeHaarMeasure (2 * L)
  fine_prob := inferInstance
  coarse_prob := inferInstance
  fiber_prob := fun _ => inferInstance

theorem constantKernel_normalizedAction {L : ℕ} [NeZero L] (β : ℝ) :
    wilsonBlockedNormalizedEffectiveAction (constantKernelDisintegration L) β = fun _ => 0 := by
  funext V
  exact sub_self _

/-- With the constant kernel the structure is inhabited at every bare coupling `β ≥ 0` by a model
with zero coupling and zero remainder: the structure alone does not exclude degenerate models at
weak coupling. -/
def constantKernelModel (L : ℕ) [NeZero L] (ext : LinearPlaquetteCouplingExtractor L) {β : ℝ}
    (hβ : 0 ≤ β) : UnifiedPhysicalWilsonBlockingModel L where
  dis := constantKernelDisintegration L
  ext := ext
  β_uv := β
  hβ_uv_nonneg := hβ
  hS_measurable := measurable_wilsonAction β
  hB_measurable := measurable_dyadicLinkBlockMap L
  influence :=
    { β_next := 0
      K_next := fun _ => 0
      linkInfluence := fun _ _ => 0
      η_next := 0
      h_β_nonneg := le_rfl
      h_η_nonneg := le_rfl
      h_influence_nonneg := fun _ _ => le_rfl
      h_osc_K_next := fun _ _ _ _ _ => by simp
      h_influence_uniform := fun _ _ => le_rfl }
  h_β_extracted_eq := by
    rw [constantKernel_normalizedAction, (extracted_zero ext).1]
  h_K_extracted_eq := by
    rw [constantKernel_normalizedAction, (extracted_zero ext).2]

/-- Constructor on the actual Haar disintegration: for any extractor and bare coupling, the
model exists once the extracted coupling is nonnegative. The remainder contract uses the
repository's volume-uniform oscillation bound `12 β + 12 |β_next|`. -/
def haarModelOfSign (L : ℕ) [NeZero L] (ext : LinearPlaquetteCouplingExtractor L) {β : ℝ}
    (hβ : 0 ≤ β)
    (hsign : 0 ≤ extractedCoarseCoupling ext
      (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)) :
    UnifiedPhysicalWilsonBlockingModel L where
  dis := haarBlockDisintegration L
  ext := ext
  β_uv := β
  hβ_uv_nonneg := hβ
  hS_measurable := measurable_wilsonAction β
  hB_measurable := measurable_dyadicLinkBlockMap L
  influence :=
    { β_next := extractedCoarseCoupling ext
        (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)
      K_next := extractedCoarseRemainder ext
        (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)
      linkInfluence := fun _ _ => 12 * β + 12 * |extractedCoarseCoupling ext
        (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)|
      η_next := 12 * β + 12 * |extractedCoarseCoupling ext
        (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)|
      h_β_nonneg := hsign
      h_η_nonneg := by positivity
      h_influence_nonneg := fun _ _ => by positivity
      h_osc_K_next := fun x μ V g1 g2 =>
        (haarExtractedCoarseRemainder_singleLink_oscillation_and_twoLink_mixedDifference L ext
          (M := 0) hβ V x μ g1 g2 x μ g1 g2).1
      h_influence_uniform := fun _ _ => le_rfl }
  h_β_extracted_eq := rfl
  h_K_extracted_eq := rfl

/-- On the actual Haar disintegration the only obstruction to inhabiting the model structure at
a given extractor and bare coupling is the sign of the extracted coupling. -/
theorem exists_haarModel_iff (L : ℕ) [NeZero L] (ext : LinearPlaquetteCouplingExtractor L)
    {β : ℝ} (hβ : 0 ≤ β) :
    (∃ M : UnifiedPhysicalWilsonBlockingModel L,
        M.dis = haarBlockDisintegration L ∧ M.ext = ext ∧ M.β_uv = β) ↔
      0 ≤ extractedCoarseCoupling ext
        (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) := by
  constructor
  · rintro ⟨M, hdis, hext, hβM⟩
    have h := M.h_β_extracted_eq
    rw [hdis, hext, hβM] at h
    rw [← h]
    exact M.influence.h_β_nonneg
  · intro hsign
    exact ⟨haarModelOfSign L ext hβ hsign, rfl, rfl, rfl⟩

/-! ### A lattice Stokes identity for the dyadic blocking -/

/-- The fine-lattice site `2x` of a coarse site, as used by `dyadicLinkBlockMap`. -/
def fineSite {L : ℕ} (x : Lattice4D L) : Lattice4D (2 * L) :=
  fun i => ((2 * (x i).val : ℕ) : ZMod (2 * L))

theorem fineSite_zero (L : ℕ) : fineSite (0 : Lattice4D L) = 0 := by
  funext i
  simp [fineSite]

theorem fineSite_shift_zero {L : ℕ} (hL : 2 ≤ L) (μ : Fin 4) :
    fineSite (shift (0 : Lattice4D L) μ) = shift (shift (0 : Lattice4D (2 * L)) μ) μ := by
  have : Fact (1 < L) := ⟨by omega⟩
  funext i
  simp only [fineSite, shift, unitVec, Pi.add_apply, Pi.zero_apply, zero_add]
  split_ifs with h
  · rw [ZMod.val_one]
    push_cast
    ring
  · simp

/-- The coarse plaquette `⟨0, 0, 1⟩`. -/
def coarseP0 (L : ℕ) : Plaquette L := ⟨0, 0, 1, by decide⟩

/-- The four fine plaquettes inside the `2 × 2` fine square of `coarseP0`. -/
def fineP1 (L : ℕ) : Plaquette (2 * L) := ⟨0, 0, 1, by decide⟩
def fineP2 (L : ℕ) : Plaquette (2 * L) := ⟨shift 0 0, 0, 1, by decide⟩
def fineP3 (L : ℕ) : Plaquette (2 * L) := ⟨shift 0 1, 0, 1, by decide⟩
def fineP4 (L : ℕ) : Plaquette (2 * L) := ⟨shift (shift 0 0) 1, 0, 1, by decide⟩

/-- Lattice Stokes identity: if every coarse link is the product of its two fine links, the
coarse holonomy of `coarseP0` is a product of conjugates of the four fine plaquette holonomies
inside its `2 × 2` fine square. -/
theorem coarsePlaquette_eq_conj_product {L : ℕ} (hL : 2 ≤ L) (U : GaugeConfig (2 * L))
    (V : GaugeConfig L)
    (hV : ∀ e : Link L, V e = U ⟨fineSite e.x, e.μ⟩ * U ⟨shift (fineSite e.x) e.μ, e.μ⟩) :
    plaquetteHolonomy V (coarseP0 L) =
      (U ⟨0, 0⟩ * plaquetteHolonomy U (fineP2 L) * (U ⟨0, 0⟩)⁻¹) *
        plaquetteHolonomy U (fineP1 L) *
        ((U ⟨0, 1⟩ * U ⟨shift 0 1, 0⟩) * plaquetteHolonomy U (fineP4 L) *
          (U ⟨0, 1⟩ * U ⟨shift 0 1, 0⟩)⁻¹) *
        (U ⟨0, 1⟩ * plaquetteHolonomy U (fineP3 L) * (U ⟨0, 1⟩)⁻¹) := by
  have e1 : shift (shift (0 : Lattice4D (2 * L)) 1) 0 = shift (shift 0 0) 1 := shift_comm _ 1 0
  have e2 : shift (shift (shift (0 : Lattice4D (2 * L)) 0) 1) 0 = shift (shift (shift 0 0) 0) 1 :=
    shift_comm _ 1 0
  have e3 : shift (shift (shift (0 : Lattice4D (2 * L)) 0) 1) 1 =
      shift (shift (shift 0 1) 1) 0 := by
    rw [shift_comm (0 : Lattice4D (2 * L)) 0 1, shift_comm (shift (0 : Lattice4D (2 * L)) 1) 0 1]
  simp only [plaquetteHolonomy, coarseP0, fineP1, fineP2, fineP3, fineP4]
  rw [hV ⟨0, 0⟩, hV ⟨shift 0 0, 1⟩, hV ⟨shift 0 1, 0⟩, hV ⟨0, 1⟩]
  simp only [fineSite_zero, fineSite_shift_zero hL]
  rw [e1, e2, e3]
  group

theorem linkDefect_conj (g x : SU2) : linkDefect (g * x * g⁻¹) = linkDefect x := by
  unfold linkDefect
  rw [SU2.trace_conj]

/-- The defect of the coarse plaquette is at most four times the action of its four fine
plaquettes. -/
theorem linkDefect_coarsePlaquette_le {L : ℕ} (hL : 2 ≤ L) (U : GaugeConfig (2 * L))
    (V : GaugeConfig L)
    (hV : ∀ e : Link L, V e = U ⟨fineSite e.x, e.μ⟩ * U ⟨shift (fineSite e.x) e.μ, e.μ⟩) :
    linkDefect (plaquetteHolonomy V (coarseP0 L)) ≤
      4 * (plaquetteAction U (fineP1 L) + plaquetteAction U (fineP2 L) +
        plaquetteAction U (fineP3 L) + plaquetteAction U (fineP4 L)) := by
  rw [coarsePlaquette_eq_conj_product hL U V hV]
  set X1 := U ⟨0, 0⟩ * plaquetteHolonomy U (fineP2 L) * (U ⟨0, 0⟩)⁻¹
  set Q := plaquetteHolonomy U (fineP1 L)
  set X3 := (U ⟨0, 1⟩ * U ⟨shift 0 1, 0⟩) * plaquetteHolonomy U (fineP4 L) *
    (U ⟨0, 1⟩ * U ⟨shift 0 1, 0⟩)⁻¹
  set X4 := U ⟨0, 1⟩ * plaquetteHolonomy U (fineP3 L) * (U ⟨0, 1⟩)⁻¹
  have hassoc : X1 * Q * X3 * X4 = (X1 * Q) * (X3 * X4) := by group
  rw [hassoc]
  have h1 := linkDefect_mul_le (X1 * Q) (X3 * X4)
  have h2 := linkDefect_mul_le X1 Q
  have h3 := linkDefect_mul_le X3 X4
  have hX1 : linkDefect X1 = plaquetteAction U (fineP2 L) := linkDefect_conj _ _
  have hX3 : linkDefect X3 = plaquetteAction U (fineP4 L) := linkDefect_conj _ _
  have hX4 : linkDefect X4 = plaquetteAction U (fineP3 L) := linkDefect_conj _ _
  have hQ : linkDefect Q = plaquetteAction U (fineP1 L) := rfl
  linarith

theorem one_ne_zero_zmod_two_mul (L : ℕ) [NeZero L] : (1 : ZMod (2 * L)) ≠ 0 := by
  have : Fact (1 < 2 * L) := ⟨by have := NeZero.pos L; omega⟩
  exact one_ne_zero

/-- The four fine plaquettes are distinct, so their actions sum to at most the fine action. -/
theorem fine_sum_le_wilsonAction {L : ℕ} [NeZero L] (U : GaugeConfig (2 * L)) :
    plaquetteAction U (fineP1 L) + plaquetteAction U (fineP2 L) +
      plaquetteAction U (fineP3 L) + plaquetteAction U (fineP4 L) ≤ wilsonAction 1 U := by
  have h10 := one_ne_zero_zmod_two_mul L
  have hx : ∀ {p q : Plaquette (2 * L)} (i : Fin 4), p.x i ≠ q.x i → p ≠ q := by
    intro p q i h hpq
    exact h (by rw [hpq])
  have h12 : fineP1 L ≠ fineP2 L := hx 0 (by simp [fineP1, fineP2, shift, unitVec, h10.symm])
  have h13 : fineP1 L ≠ fineP3 L := hx 1 (by simp [fineP1, fineP3, shift, unitVec, h10.symm])
  have h14 : fineP1 L ≠ fineP4 L := hx 0 (by simp [fineP1, fineP4, shift, unitVec, h10.symm])
  have h23 : fineP2 L ≠ fineP3 L := hx 0 (by simp [fineP2, fineP3, shift, unitVec, h10])
  have h24 : fineP2 L ≠ fineP4 L := hx 1 (by simp [fineP2, fineP4, shift, unitVec, h10.symm])
  have h34 : fineP3 L ≠ fineP4 L := hx 0 (by simp [fineP3, fineP4, shift, unitVec, h10.symm])
  have hsum : ∑ p ∈ ({fineP1 L, fineP2 L, fineP3 L, fineP4 L} : Finset (Plaquette (2 * L))),
      plaquetteAction U p = plaquetteAction U (fineP1 L) + plaquetteAction U (fineP2 L) +
        plaquetteAction U (fineP3 L) + plaquetteAction U (fineP4 L) := by
    rw [Finset.sum_insert (by simp [h12, h13, h14]), Finset.sum_insert (by simp [h23, h24]),
      Finset.sum_pair h34]
    ring
  rw [← hsum]
  have hle := Finset.sum_le_univ_sum_of_nonneg (s := ({fineP1 L, fineP2 L, fineP3 L, fineP4 L} :
    Finset (Plaquette (2 * L)))) (fun p => plaquetteAction_nonneg U p)
  simpa [wilsonAction] using hle

/-! ### A nondegenerate model on the actual Haar disintegration at weak coupling -/

/-- The probe configuration: the coarse vacuum with the single link `⟨0, 0⟩` set to `-1`. -/
def probeConfig (L : ℕ) : GaugeConfig L := updateGaugeLink L (vacuumConfig L) 0 0 negOne

theorem probeConfig_holonomy {L : ℕ} (hL : 2 ≤ L) :
    plaquetteHolonomy (probeConfig L) (coarseP0 L) = negOne := by
  have hupd := updateGaugeLink_same_and_other L (vacuumConfig L) 0 0 negOne
  have hne1 : (⟨shift 0 0, 1⟩ : Link L) ≠ ⟨0, 0⟩ := by
    intro h
    have := congrArg Link.μ h
    simp at this
  have hne2 : (⟨shift 0 1, 0⟩ : Link L) ≠ ⟨0, 0⟩ := by
    have : Fact (1 < L) := ⟨by omega⟩
    intro h
    have := congrArg (fun e : Link L => e.x 1) h
    simp [shift, unitVec] at this
  have hne3 : (⟨0, 1⟩ : Link L) ≠ ⟨0, 0⟩ := by
    intro h
    have := congrArg Link.μ h
    simp at this
  simp only [plaquetteHolonomy, coarseP0, probeConfig]
  rw [hupd.1, hupd.2 _ hne1, hupd.2 _ hne2, hupd.2 _ hne3]
  simp [vacuumConfig]

open YangMillsBlockGeometry in
/-- The constructed Haar fiber over `V` blocks back to `V`, link by link. -/
theorem haarFiberReconstruction_blocks (L : ℕ) [NeZero L] (V : GaugeConfig L)
    (r : HaarFiberCoordinates L) (e : Link L) :
    V e = haarFiberReconstruction L V r ⟨fineSite e.x, e.μ⟩ *
      haarFiberReconstruction L V r ⟨shift (fineSite e.x) e.μ, e.μ⟩ := by
  have h0 := haarFiberReconstruction_first L V r e
  have h1 := haarFiberReconstruction_second L V r e
  rw [dyadicFineLink_zero] at h0
  rw [dyadicFineLink_one] at h1
  have h0' : haarFiberReconstruction L V r ⟨fineSite e.x, e.μ⟩ = r.1 e := h0
  have h1' : haarFiberReconstruction L V r ⟨shift (fineSite e.x) e.μ, e.μ⟩ =
      (r.1 e)⁻¹ * V e := h1
  rw [h0', h1']
  group

theorem integrable_reconWeight {L : ℕ} [NeZero L] {β : ℝ} (hβ : 0 ≤ β) (V : GaugeConfig L) :
    Integrable (fun r => boltzmannWeight β (haarFiberReconstruction L V r))
      (haarFiberReference L) := by
  apply (integrable_const (1 : ℝ)).mono'
    ((wilsonWeight_measurable (measurable_wilsonAction β)).comp
      (measurable_haarFiberReconstruction L V)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun r => by
    change ‖boltzmannWeight β (haarFiberReconstruction L V r)‖ ≤ 1
    rw [Real.norm_eq_abs]
    change |Real.exp (-wilsonAction β (haarFiberReconstruction L V r))| ≤ 1
    rw [abs_of_pos (Real.exp_pos _)]
    exact (boltzmannWeight_bounds hβ _).2.2

/-- Every fine configuration in the Haar fiber over the probe has fine action at least `1/2`. -/
theorem probe_fiber_action_ge {L : ℕ} [NeZero L] (hL : 2 ≤ L) (r : HaarFiberCoordinates L) :
    1 / 2 ≤ wilsonAction 1 (haarFiberReconstruction L (probeConfig L) r) := by
  have hdef := linkDefect_coarsePlaquette_le hL (haarFiberReconstruction L (probeConfig L) r)
    (probeConfig L) (haarFiberReconstruction_blocks L (probeConfig L) r)
  rw [probeConfig_holonomy hL, linkDefect_negOne] at hdef
  have hsum := fine_sum_le_wilsonAction (haarFiberReconstruction L (probeConfig L) r)
  linarith

/-- The blocked fiber weight of the probe is at most `exp (-β / 2)`. -/
theorem haarWeight_probe_le {L : ℕ} [NeZero L] (hL : 2 ≤ L) {β : ℝ} (hβ : 0 ≤ β) :
    wilsonBlockedFiberWeight (haarBlockDisintegration L) β (probeConfig L) ≤
      Real.exp (-(β / 2)) := by
  rw [haarBlockedFiberWeight_eq_integral]
  calc ∫ r, boltzmannWeight β (haarFiberReconstruction L (probeConfig L) r) ∂haarFiberReference L
      ≤ ∫ _r, Real.exp (-(β / 2)) ∂haarFiberReference L := by
        apply integral_mono (integrable_reconWeight hβ _) (integrable_const _)
        intro r
        have hS := probe_fiber_action_ge hL r
        change Real.exp (-wilsonAction β (haarFiberReconstruction L (probeConfig L) r)) ≤ _
        rw [wilsonAction_eq_beta_mul_wilsonAction_one]
        apply Real.exp_le_exp.mpr
        nlinarith
    _ = Real.exp (-(β / 2)) := by simp

/-- Near-vacuum box in the Haar fiber coordinates: first links and unused fine links all in
`linkNeighbourhood ρ`. -/
def nearVacuumBox (L : ℕ) (ρ : ℝ) : Set (HaarFiberCoordinates L) :=
  linkBox L ρ ×ˢ (Set.univ.pi fun _ : YangMillsBlockGeometry.unusedFineLinks L =>
    linkNeighbourhood ρ)

theorem measurableSet_nearVacuumBox (L : ℕ) [NeZero L] (ρ : ℝ) :
    MeasurableSet (nearVacuumBox L ρ) :=
  (MeasurableSet.univ_pi fun _ => measurableSet_linkNeighbourhood ρ).prod
    (MeasurableSet.univ_pi fun _ => measurableSet_linkNeighbourhood ρ)

open YangMillsBlockGeometry in
/-- Over the coarse vacuum, a near-vacuum box point reconstructs a fine configuration all of whose
links have defect below `ρ`. -/
theorem recon_vacuum_mem_linkBox {L : ℕ} [NeZero L] {ρ : ℝ} {r : HaarFiberCoordinates L}
    (hr : r ∈ nearVacuumBox L ρ) :
    haarFiberReconstruction L (vacuumConfig L) r ∈ linkBox (2 * L) ρ := by
  intro f _
  obtain ⟨q, rfl⟩ := (dyadicFineLinkEquiv L).surjective f
  rcases q with ⟨e, b⟩ | j
  · fin_cases b
    · change haarFiberReconstruction L _ r (dyadicFineLink L (e, 0)) ∈ linkNeighbourhood ρ
      rw [haarFiberReconstruction_first]
      exact hr.1 e (mem_univ e)
    · change haarFiberReconstruction L _ r (dyadicFineLink L (e, 1)) ∈ linkNeighbourhood ρ
      rw [haarFiberReconstruction_second]
      change linkDefect ((r.1 e)⁻¹ * vacuumConfig L e) < ρ
      have hv : vacuumConfig L e = 1 := rfl
      rw [hv, mul_one, linkDefect_inv]
      exact hr.1 e (mem_univ e)
  · change haarFiberReconstruction L _ r j.val ∈ linkNeighbourhood ρ
    rw [haarFiberReconstruction_unused]
    exact hr.2 j (mem_univ j)

theorem nearVacuumBox_measure_pos {L : ℕ} [NeZero L] {ρ : ℝ} (hρ : 0 < ρ) :
    0 < (haarFiberReference L).real (nearVacuumBox L ρ) := by
  have hA : (gaugeHaarMeasure L) (linkBox L ρ) ≠ 0 := by
    intro h0
    have h := gaugeHaarMeasure_real_linkBox L ρ
    rw [Measure.real, h0, ENNReal.toReal_zero] at h
    exact (pow_pos (singleLinkMass_pos hρ) _).ne h
  have hB : (Measure.pi fun _ : YangMillsBlockGeometry.unusedFineLinks L => SU2.haarProbability)
      (Set.univ.pi fun _ => linkNeighbourhood ρ) ≠ 0 := by
    rw [Measure.pi_pi, Finset.prod_ne_zero_iff]
    intro j _ h0
    have h := singleLinkMass_pos hρ
    unfold singleLinkMass at h
    rw [Measure.real, h0, ENNReal.toReal_zero] at h
    exact lt_irrefl 0 h
  unfold haarFiberReference nearVacuumBox
  rw [Measure.real, Measure.prod_prod]
  exact ENNReal.toReal_pos (mul_ne_zero hA hB)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))

/-- Defect scale of the near-vacuum box: `1 / (384 (2L)⁴)`, so that the reconstructed fine
action stays below `1/4`. -/
def vacuumScale (L : ℕ) : ℝ := 1 / (384 * ((2 * L : ℕ) : ℝ) ^ 4)

theorem vacuumScale_pos (L : ℕ) [NeZero L] : 0 < vacuumScale L := by
  have : (0 : ℝ) < ((2 * L : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < 2 * L by have := NeZero.pos L; omega)
  unfold vacuumScale
  positivity

/-- The blocked fiber weight of the vacuum is at least `exp (-β / 4) · m_L`, where `m_L` is the
Haar mass of the near-vacuum box. -/
theorem haarWeight_vacuum_ge {L : ℕ} [NeZero L] {β : ℝ} (hβ : 0 ≤ β) :
    Real.exp (-(β / 4)) * (haarFiberReference L).real (nearVacuumBox L (vacuumScale L)) ≤
      wilsonBlockedFiberWeight (haarBlockDisintegration L) β (vacuumConfig L) := by
  rw [haarBlockedFiberWeight_eq_integral]
  have hmeas := measurableSet_nearVacuumBox L (vacuumScale L)
  have hX : (0 : ℝ) < ((2 * L : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < 2 * L by have := NeZero.pos L; omega)
  calc Real.exp (-(β / 4)) * (haarFiberReference L).real (nearVacuumBox L (vacuumScale L))
      = ∫ r, (nearVacuumBox L (vacuumScale L)).indicator (fun _ => Real.exp (-(β / 4))) r
          ∂haarFiberReference L := by
        rw [integral_indicator_const _ hmeas, smul_eq_mul, mul_comm]
    _ ≤ ∫ r, boltzmannWeight β (haarFiberReconstruction L (vacuumConfig L) r)
          ∂haarFiberReference L := by
        apply integral_mono ((integrable_const _).indicator hmeas) (integrable_reconWeight hβ _)
        intro r
        by_cases hr : r ∈ nearVacuumBox L (vacuumScale L)
        · rw [Set.indicator_of_mem hr]
          have hS := linkBox_subset_sublevel (2 * L) (vacuumScale L) (recon_vacuum_mem_linkBox hr)
          have hval : 6 * ((2 * L : ℕ) : ℝ) ^ 4 * (16 * vacuumScale L) = 1 / 4 := by
            unfold vacuumScale
            field_simp
            ring
          change wilsonAction 1 (haarFiberReconstruction L (vacuumConfig L) r) <
            6 * ((2 * L : ℕ) : ℝ) ^ 4 * (16 * vacuumScale L) at hS
          rw [hval] at hS
          change Real.exp (-(β / 4)) ≤
            Real.exp (-wilsonAction β (haarFiberReconstruction L (vacuumConfig L) r))
          rw [wilsonAction_eq_beta_mul_wilsonAction_one]
          apply Real.exp_le_exp.mpr
          nlinarith
        · rw [Set.indicator_of_notMem hr]
          exact (Real.exp_pos _).le

/-- The vacuum-normalized Haar effective action at the probe is at least `β / 4 + log m_L`. -/
theorem haarNormalizedAction_probe_ge {L : ℕ} [NeZero L] (hL : 2 ≤ L) {β : ℝ} (hβ : 0 ≤ β) :
    β / 4 + Real.log ((haarFiberReference L).real (nearVacuumBox L (vacuumScale L))) ≤
      wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β (probeConfig L) := by
  have hm := nearVacuumBox_measure_pos (L := L) (vacuumScale_pos L)
  have hWp := (wilsonBlockedFiberWeight_bounds_and_pos_all_configs (haarBlockDisintegration L)
    hβ (measurable_wilsonAction β) (probeConfig L)).1
  have h1 : Real.log (wilsonBlockedFiberWeight (haarBlockDisintegration L) β (probeConfig L)) ≤
      -(β / 2) := by
    rw [← Real.log_exp (-(β / 2))]
    exact Real.log_le_log hWp (haarWeight_probe_le hL hβ)
  have h2 := Real.log_le_log (by positivity) (haarWeight_vacuum_ge (L := L) hβ)
  rw [Real.log_mul (Real.exp_pos _).ne' hm.ne', Real.log_exp] at h2
  unfold wilsonBlockedNormalizedEffectiveAction wilsonBlockedEffectiveAction
  linarith

theorem wilsonAction_probe_pos {L : ℕ} [NeZero L] (hL : 2 ≤ L) :
    0 < wilsonAction 1 (probeConfig L) := by
  have h := plaquetteAction_le_wilsonAction_one (probeConfig L) (coarseP0 L)
  have hp : plaquetteAction (probeConfig L) (coarseP0 L) = 2 := by
    rw [plaquetteAction_eq_linkDefect, probeConfig_holonomy hL, linkDefect_negOne]
  linarith

/-- The repository's point-probe coupling extractor at the probe configuration. -/
def probeExtractor (L : ℕ) [NeZero L] (hL : 2 ≤ L) : LinearPlaquetteCouplingExtractor L :=
  canonicalPlaquetteProbeExtractor (probeConfig L) (wilsonAction_probe_pos hL).ne'

theorem probeExtractor_coupling {L : ℕ} [NeZero L] (hL : 2 ≤ L) (β : ℝ) :
    extractedCoarseCoupling (probeExtractor L hL)
        (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) =
      wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β (probeConfig L) /
        wilsonAction 1 (probeConfig L) := by
  have hv : wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β
      (vacuumConfig L) = 0 := sub_self _
  show (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β (probeConfig L) -
      wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β (vacuumConfig L)) /
        wilsonAction 1 (probeConfig L) = _
  rw [hv, sub_zero]

/-- The weak-coupling threshold `max 0 (-4 log m_L)` of the Haar model at lattice size `L`. It
depends on `L` through the Haar mass `m_L` of the near-vacuum box. -/
def haarModelThreshold (L : ℕ) [NeZero L] : ℝ :=
  max 0 (-(4 * Real.log ((haarFiberReference L).real (nearVacuumBox L (vacuumScale L)))))

theorem probeExtractor_coupling_pos {L : ℕ} [NeZero L] (hL : 2 ≤ L) {β : ℝ}
    (hβ : haarModelThreshold L < β) :
    0 < extractedCoarseCoupling (probeExtractor L hL)
      (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) := by
  have hβ0 : 0 ≤ β := (le_max_left _ _).trans hβ.le
  rw [probeExtractor_coupling hL β]
  apply div_pos _ (wilsonAction_probe_pos hL)
  have h := haarNormalizedAction_probe_ge hL hβ0
  have hlt : -(4 * Real.log ((haarFiberReference L).real (nearVacuumBox L (vacuumScale L)))) <
      β := lt_of_le_of_lt (le_max_right _ _) hβ
  linarith

/-- The unified blocking model on the actual Haar disintegration with the probe extractor, at a
bare coupling above `haarModelThreshold L`. -/
def haarWeakCouplingModel (L : ℕ) [NeZero L] (hL : 2 ≤ L) {β : ℝ}
    (hβ : haarModelThreshold L < β) : UnifiedPhysicalWilsonBlockingModel L :=
  haarModelOfSign L (probeExtractor L hL) ((le_max_left _ _).trans hβ.le)
    (probeExtractor_coupling_pos hL hβ).le

/-- The Haar weak-coupling model is not the zero model: its bare coupling and its extracted
coupling are positive, and its decomposed coarse effective action
`β_next S₁ + K_next` is positive at the probe. Fixed: `L ≥ 2`; then any `β` above the
`L`-dependent threshold. -/
theorem haarWeakCouplingModel_nondegenerate {L : ℕ} [NeZero L] (hL : 2 ≤ L) {β : ℝ}
    (hβ : haarModelThreshold L < β) :
    (haarWeakCouplingModel L hL hβ).dis = haarBlockDisintegration L ∧
    (haarWeakCouplingModel L hL hβ).β_uv = β ∧
    0 < (haarWeakCouplingModel L hL hβ).β_uv ∧
    0 < (haarWeakCouplingModel L hL hβ).influence.β_next ∧
    0 < (haarWeakCouplingModel L hL hβ).influence.β_next * wilsonAction 1 (probeConfig L) +
      (haarWeakCouplingModel L hL hβ).influence.K_next (probeConfig L) := by
  have hβ0 : 0 ≤ β := (le_max_left _ _).trans hβ.le
  refine ⟨rfl, rfl, ?_, probeExtractor_coupling_pos hL hβ, ?_⟩
  · show 0 < β
    have hle : 0 ≤ haarModelThreshold L := le_max_left _ _
    linarith
  · show 0 < extractedCoarseCoupling (probeExtractor L hL)
        (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) *
        wilsonAction 1 (probeConfig L) +
      extractedCoarseRemainder (probeExtractor L hL)
        (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) (probeConfig L)
    unfold extractedCoarseRemainder
    have h := haarNormalizedAction_probe_ge hL hβ0
    have hlt : -(4 * Real.log ((haarFiberReference L).real (nearVacuumBox L (vacuumScale L)))) <
        β := lt_of_le_of_lt (le_max_right _ _) hβ
    linarith

/-- Anti-vacuity of the unified blocking model at weak coupling: for every `L ≥ 2` there is a
threshold beyond which every bare coupling carries a model on the actual Haar disintegration
with positive extracted coupling and nonzero coarse effective action. -/
theorem exists_nondegenerate_haarModel (L : ℕ) [NeZero L] (hL : 2 ≤ L) :
    ∃ βthr : ℝ, 0 ≤ βthr ∧ ∀ β : ℝ, βthr < β →
      ∃ M : UnifiedPhysicalWilsonBlockingModel L,
        M.dis = haarBlockDisintegration L ∧ M.β_uv = β ∧ 0 < M.influence.β_next ∧
        ∃ V : GaugeConfig L, M.influence.β_next * wilsonAction 1 V + M.influence.K_next V ≠ 0 :=
  ⟨haarModelThreshold L, le_max_left _ _, fun _ hβ =>
    ⟨haarWeakCouplingModel L hL hβ, (haarWeakCouplingModel_nondegenerate hL hβ).1,
      (haarWeakCouplingModel_nondegenerate hL hβ).2.1,
      (haarWeakCouplingModel_nondegenerate hL hβ).2.2.2.1,
      probeConfig L, (haarWeakCouplingModel_nondegenerate hL hβ).2.2.2.2.ne'⟩⟩

/-! ### The volume-uniform influence family -/

/-- A volume-uniform influence family with a nonzero, gauge-invariant remainder
`K_next = S₁ / 48` at every lattice size (the repository's own witness has `K_next = 0`). -/
def wilsonRemainderFamily : YangMillsRGBridgeObstruction.VolumeUniformCoarseInfluenceFamily where
  β_star := 1 / 48
  η_star := 1 / 4
  contract L _ :=
    { β_next := 1 / 48
      K_next := fun V => 1 / 48 * wilsonAction 1 V
      linkInfluence := fun _ _ => 1 / 4
      η_next := 1 / 4
      h_β_nonneg := by norm_num
      h_η_nonneg := by norm_num
      h_influence_nonneg := fun _ _ => by norm_num
      h_osc_K_next := fun x μ V g1 g2 => by
        have h := wilsonAction_one_updateGaugeLink_oscillation_le_twelve L V x μ g1 g2
        rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 48)]
        linarith
      h_influence_uniform := fun _ _ => le_rfl }
  h_β_star_nonneg := by norm_num
  h_η_star_nonneg := by norm_num
  h_uniform_β := fun _ _ => le_rfl
  h_uniform_η := fun _ _ => le_rfl
  h_uniform_contraction := by norm_num

/-- The remainder of `wilsonRemainderFamily` is not constant at any `L ≥ 2`. -/
theorem wilsonRemainderFamily_nonconstant (L : ℕ) [NeZero L] (hL : 2 ≤ L) :
    (wilsonRemainderFamily.contract L).K_next (vacuumConfig L) = 0 ∧
    0 < (wilsonRemainderFamily.contract L).K_next (probeConfig L) := by
  constructor
  · show 1 / 48 * wilsonAction 1 (vacuumConfig L) = 0
    rw [wilsonAction_vacuum, mul_zero]
  · show 0 < 1 / 48 * wilsonAction 1 (probeConfig L)
    have := wilsonAction_probe_pos hL
    positivity

/-- Every volume-uniform influence family has coupling below `1/18` at every lattice size, so
the family describes only the strong-coupling (Dobrushin) regime. -/
theorem volumeUniformFamily_coupling_lt
    (fam : YangMillsRGBridgeObstruction.VolumeUniformCoarseInfluenceFamily) (L : ℕ) [NeZero L] :
    (fam.contract L).β_next < 1 / 18 := by
  have h1 := fam.h_uniform_β L
  have h2 := fam.h_uniform_contraction
  have h3 := fam.h_η_star_nonneg
  linarith

#assert_zfc_axioms

end JesseMath.Physics.YangMillsWeakCouplingNecessity
