import JesseMath.Linter.AxiomAudit
import JesseMath.Physics.YangMillsWeakCoupling
import JesseMath.Physics.SussmanAlpogeBalaban
import JesseMath.Physics.YangMillsContinuumLimitBridge

/-!
# Coupling growth against Haar entropy along a fixed-volume cutoff path

`YangMillsWeakCoupling.lean` proves, for the actual SU(2) Haar Wilson law on the periodic
`L⁴` torus, the finite-volume total-action tail bound

`P_{L,β}(S₁ ≥ ε) ≤ exp(-β(ε-δ)) / c(L,δ)`,  `c(L,δ) = haarVacuumSublevelMass L δ`,

where `S₁ = wilsonAction 1`. This module follows that bound along a cutoff path
`(a_n, L_n, β_n)` with fixed physical side `L_n a_n = side` and `a_n → 0`. Two ingredients
enter and are kept separate:

* (H) a Haar-mass lower bound `c(L_n, δ_n) ≥ c₁(n) ^ (4 L_n⁴)`, where `4 L⁴` is the link count
  (`PathHaarMassBound`, a hypothesis that this module does not prove);
* (C) the bare inverse couplings `β_n` carried by the path.

Exact balance (`composedTailBound_tendsto_zero_iff`): the composed bound
`exp(-β_n(ε-δ_n)) / c₁(n) ^ (4 L_n⁴)` tends to zero if and only if the balance exponent
`β_n(ε-δ_n) - 4 L_n⁴ log(1/c₁(n))` tends to `+∞`. Under that balance the actual Wilson tail
tends to zero (`exact_balance_along_cutoff_path`). With a constant factor `c₁ < 1` and fixed
`δ < ε` the threshold is quartic in the spacing: `β_n a_n⁴` eventually above
`4 side⁴ log(1/c₁)/(ε-δ)` with a margin balances, eventually below it with a margin the composed
bound diverges, the balance forces `β_n a_n⁴` above that value eventually, and every sub-quartic
coupling (`β_n a_n⁴ → 0`), in particular every logarithmic one, fails to balance.

Repository supply of the ingredients:

* (H) at extensive thresholds `δ_n = 6 η L_n⁴` with an `n`-independent factor is supplied by
  `exists_haar_sublevel_mass_volume_bound`; these thresholds eventually exceed every fixed `ε`,
  so the composed bound stays at least one.
* (H) at a fixed threshold is supplied only with factors `c₁(n) > 0` of unknown size. The
  product-box route, the only route to (H) in the repository, gives per-link factors that tend to
  zero at any fixed threshold (`boxFactor_tendsto_zero`, from the absence of atoms in SU(2) Haar
  measure), so it cannot supply a constant factor there. A rate in the per-plaquette scale is the
  named hypothesis `SingleLinkHaarMassRate`, not proved here; its exponent is necessarily
  positive (`SingleLinkHaarMassRate.p_pos`), bounded `β_n a_n⁴` then never balances, and the
  balance forces `β_n a_n⁴ → ∞`.
* (C) from the Clause (0) flow: every `ClauseZeroCouplingSchedule` has `β_n a_n⁴ → 0`, so it never
  balances; the canonical SU(2) schedule built from `canonicalMultiStepOddFlow` is an instance.
* Action-density tails vanish along every path with `β_n → ∞` (`densityTail_tendsto_zero`), but
  their thresholds `ε L_n⁴` diverge along a fixed-volume path.

Not proved here: an upper bound on the full Haar mass `c(L,δ)` (only on box factors), any
statement that the actual tail fails to vanish, a continuum limit, or a Gaussian rate. The
negative statements concern the composed upper bound and the box route only. Downstream modules
prove the first two and supply the named rate: `YangMillsUniformHaarNeighbourhood.haarVacuumSublevelMass_le`
bounds the full Haar mass from above, `YangMillsWeakCouplingNecessity.clauseZeroCanonicalPath_wilsonTail_tendsto_one`
shows that the actual tail tends to one along the canonical Clause (0) path, and
`YangMillsWeakCouplingNecessity.haarSingleLinkMassRate` is a `SingleLinkHaarMassRate` on the actual
Haar measure.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace JesseMath.Physics.YangMillsCutoffPathBalance

open JesseMath.Physics JesseMath.FormalConjectures

/-! ## Link count of the periodic torus -/

/-- The periodic `L⁴` torus has exactly `4 L⁴` links. This is the exponent `N(L)` of the
product-Haar entropy cost. -/
theorem card_link_eq (L : ℕ) [NeZero L] : Fintype.card (Link L) = 4 * L ^ 4 := by
  rw [Fintype.card_congr (linkEquiv L), Fintype.card_prod, card_lattice4D]
  simp [Direction, Nat.mul_comm]

/-! ## Fixed-volume cutoff geometry and cutoff paths -/

/-- Lattice geometry of a fixed-volume cutoff sequence. At cutoff `n` the lattice spacing is
`a n` and the periodic torus has `sites n` sites per direction. The physical side
`sites n * a n = side` is the same for every `n`, and `a n → 0`. -/
structure FixedVolumeGeometry where
  /-- Lattice spacing at cutoff `n`. -/
  a : ℕ → ℝ
  /-- Number of lattice sites per direction at cutoff `n`. -/
  sites : ℕ → ℕ
  /-- Fixed physical side length of the periodic box. -/
  side : ℝ
  side_pos : 0 < side
  a_pos : ∀ n, 0 < a n
  side_eq : ∀ n, (sites n : ℝ) * a n = side
  spacing_tendsto : Tendsto a atTop (𝓝 0)

namespace FixedVolumeGeometry

variable (G : FixedVolumeGeometry)

theorem sites_ne_zero (n : ℕ) : G.sites n ≠ 0 := by
  intro h
  have hs := G.side_eq n
  rw [h, Nat.cast_zero, zero_mul] at hs
  exact G.side_pos.ne hs

instance instNeZeroSites (n : ℕ) : NeZero (G.sites n) := ⟨G.sites_ne_zero n⟩

theorem sites_pos_real (n : ℕ) : 0 < (G.sites n : ℝ) :=
  Nat.cast_pos.mpr (Nat.pos_of_ne_zero (G.sites_ne_zero n))

theorem one_le_sites_real (n : ℕ) : (1 : ℝ) ≤ G.sites n :=
  Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (G.sites_ne_zero n))

/-- The number of sites per direction is the physical side divided by the spacing. -/
theorem sites_eq_side_div (n : ℕ) : (G.sites n : ℝ) = G.side / G.a n := by
  rw [eq_div_iff (G.a_pos n).ne', G.side_eq n]

theorem sites_pow_four_eq (n : ℕ) : (G.sites n : ℝ) ^ 4 = G.side ^ 4 / G.a n ^ 4 := by
  rw [G.sites_eq_side_div n, div_pow]

/-- The link count in physical variables: `card (Link L_n) = 4 side⁴ / a_n⁴`. -/
theorem card_link_eq_physical (n : ℕ) :
    (Fintype.card (Link (G.sites n)) : ℝ) = 4 * G.side ^ 4 / G.a n ^ 4 := by
  rw [card_link_eq]
  push_cast
  rw [G.sites_pow_four_eq n]
  ring

/-- At fixed physical side and vanishing spacing the number of sites diverges. -/
theorem sites_tendsto_atTop_real : Tendsto (fun n => (G.sites n : ℝ)) atTop atTop := by
  have h0 : Tendsto G.a atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨G.spacing_tendsto, Eventually.of_forall G.a_pos⟩
  have h1 := (h0.inv_tendsto_nhdsGT_zero).const_mul_atTop G.side_pos
  refine h1.congr fun n => ?_
  rw [G.sites_eq_side_div n, div_eq_mul_inv]
  rfl

theorem sites_tendsto_atTop : Tendsto G.sites atTop atTop :=
  tendsto_natCast_atTop_iff.1 G.sites_tendsto_atTop_real

theorem sites_pow_four_tendsto_atTop : Tendsto (fun n => (G.sites n : ℝ) ^ 4) atTop atTop :=
  (tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).comp G.sites_tendsto_atTop_real

end FixedVolumeGeometry

/-- A fixed-volume cutoff path `(a_n, L_n, β_n)`: the geometry together with the bare inverse
coupling `β n` used in `wilsonAction`. No relation between `β n` and `a n` is assumed. -/
structure FixedVolumeCutoffPath extends FixedVolumeGeometry where
  /-- Bare inverse coupling at cutoff `n`. -/
  β : ℕ → ℝ
  β_nonneg : ∀ n, 0 ≤ β n

/-- The repository's fixed-volume dyadic refinement `a_n = side / 2^n`, `L_n = 2^n`. Its side
identity is the fifth conjunct of
`continuous_45deg_rotation_breaks_l1_exponential_correlator_and_volume_exhaustion_contrast`
in `YangMillsContinuumLimitBridge.lean`; that file contains no coupling flow. -/
def dyadicGeometry (side : ℝ) (hside : 0 < side) : FixedVolumeGeometry where
  a := fun n => side / 2 ^ n
  sites := fun n => 2 ^ n
  side := side
  side_pos := hside
  a_pos := fun n => div_pos hside (pow_pos two_pos n)
  side_eq := fun n => by
    have h := (YangMillsContinuumLimitBridge.continuous_45deg_rotation_breaks_l1_exponential_correlator_and_volume_exhaustion_contrast
      (m := 1) (t := 1) (ell_box := side) one_pos one_pos n).2.2.2.2.1
    push_cast
    rw [mul_comm]
    exact h
  spacing_tendsto := tendsto_const_nhds.div_atTop
    (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

/-! ## Composed tail bound and balance exponent -/

/-- The repository's tail bound `exp(-β(ε-δ)) / c(L,δ)` with the Haar mass replaced by a
per-link lower bound `c₁ ^ (4 L⁴)`. -/
def composedTailBound (L : ℕ) (β ε δ c₁ : ℝ) : ℝ :=
  Real.exp (-(β * (ε - δ))) / c₁ ^ (4 * L ^ 4)

/-- Balance exponent: coupling gain `β(ε-δ)` minus link entropy `4 L⁴ log(1/c₁)`. -/
def balanceExponent (L : ℕ) (β ε δ c₁ : ℝ) : ℝ :=
  β * (ε - δ) - 4 * (L : ℝ) ^ 4 * Real.log (1 / c₁)

theorem composedTailBound_eq_exp_neg_balanceExponent (L : ℕ) (β ε δ : ℝ) {c₁ : ℝ}
    (hc₁ : 0 < c₁) :
    composedTailBound L β ε δ c₁ = Real.exp (-balanceExponent L β ε δ c₁) := by
  unfold composedTailBound balanceExponent
  rw [← Real.exp_log (pow_pos hc₁ (4 * L ^ 4)), ← Real.exp_sub, Real.log_pow,
    Real.log_div one_ne_zero hc₁.ne', Real.log_one]
  congr 1
  push_cast
  ring

theorem composedTailBound_fun_eq (L : ℕ → ℕ) (β δ c₁ : ℕ → ℝ) (ε : ℝ)
    (hc₁ : ∀ n, 0 < c₁ n) :
    (fun n => composedTailBound (L n) (β n) ε (δ n) (c₁ n)) =
      fun n => Real.exp (-balanceExponent (L n) (β n) ε (δ n) (c₁ n)) :=
  funext fun n => composedTailBound_eq_exp_neg_balanceExponent (L n) (β n) ε (δ n) (hc₁ n)

/-- Exact balance condition: the composed bound vanishes along a sequence if and only if the
balance exponent diverges to `+∞`. Nothing is assumed about how `c₁` depends on `n`. -/
theorem composedTailBound_tendsto_zero_iff (L : ℕ → ℕ) (β δ c₁ : ℕ → ℝ) (ε : ℝ)
    (hc₁ : ∀ n, 0 < c₁ n) :
    Tendsto (fun n => composedTailBound (L n) (β n) ε (δ n) (c₁ n)) atTop (𝓝 0) ↔
      Tendsto (fun n => balanceExponent (L n) (β n) ε (δ n) (c₁ n)) atTop atTop := by
  rw [composedTailBound_fun_eq L β δ c₁ ε hc₁, Real.tendsto_exp_comp_nhds_zero,
    tendsto_neg_atBot_iff]

/-- The composed bound diverges if and only if the balance exponent tends to `-∞`. -/
theorem composedTailBound_tendsto_atTop_iff (L : ℕ → ℕ) (β δ c₁ : ℕ → ℝ) (ε : ℝ)
    (hc₁ : ∀ n, 0 < c₁ n) :
    Tendsto (fun n => composedTailBound (L n) (β n) ε (δ n) (c₁ n)) atTop atTop ↔
      Tendsto (fun n => balanceExponent (L n) (β n) ε (δ n) (c₁ n)) atTop atBot := by
  rw [composedTailBound_fun_eq L β δ c₁ ε hc₁, Real.tendsto_exp_comp_atTop,
    tendsto_neg_atTop_iff]

/-- A smaller per-link factor can only lower the balance exponent. -/
theorem balanceExponent_le_of_le (L : ℕ) (β ε δ : ℝ) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁)
    (h : c₁ ≤ c₂) : balanceExponent L β ε δ c₁ ≤ balanceExponent L β ε δ c₂ := by
  unfold balanceExponent
  have hlog : Real.log (1 / c₂) ≤ Real.log (1 / c₁) :=
    Real.log_le_log (one_div_pos.mpr (hc₁.trans_le h)) (one_div_le_one_div_of_le hc₁ h)
  have hL : 0 ≤ 4 * (L : ℝ) ^ 4 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hlog hL]

/-- If the threshold is at least the target (`ε ≤ δ`) the composed bound is at least one. -/
theorem one_le_composedTailBound {L : ℕ} {β ε δ c₁ : ℝ} (hβ : 0 ≤ β) (hεδ : ε ≤ δ)
    (hc₁ : 0 < c₁) (hc₁1 : c₁ ≤ 1) : 1 ≤ composedTailBound L β ε δ c₁ := by
  unfold composedTailBound
  rw [le_div_iff₀ (pow_pos hc₁ _), one_mul]
  calc c₁ ^ (4 * L ^ 4) ≤ 1 := pow_le_one₀ hc₁.le hc₁1
    _ ≤ Real.exp (-(β * (ε - δ))) := Real.one_le_exp (by nlinarith)

/-! ## The finite-volume bound on the actual Wilson law -/

/-- A positive product-Haar lower bound forces a positive sublevel threshold. -/
theorem haarVacuumSublevelMass_threshold_pos {L : ℕ} [NeZero L] {δ c₁ : ℝ} (hc₁ : 0 < c₁)
    (hmass : c₁ ^ (4 * L ^ 4) ≤ haarVacuumSublevelMass L δ) : 0 < δ := by
  rcases le_or_gt δ 0 with h | h
  · rw [haarVacuumSublevelMass_eq_zero_of_nonpos h] at hmass
    exact absurd hmass (not_le.mpr (pow_pos hc₁ _))
  · exact h

/-- A per-link lower bound on a probability mass is at most one. -/
theorem le_one_of_haarMass_lower {L : ℕ} [NeZero L] {δ c₁ : ℝ} (hc₁ : 0 < c₁)
    (hmass : c₁ ^ (4 * L ^ 4) ≤ haarVacuumSublevelMass L δ) : c₁ ≤ 1 := by
  have h1 : c₁ ^ (4 * L ^ 4) ≤ 1 := hmass.trans (haarVacuumSublevelMass_le_one δ)
  have hN : 4 * L ^ 4 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 4 (NeZero.ne L))
  exact (pow_le_one_iff_of_nonneg hc₁.le hN).1 h1

/-- The actual Wilson tail at one cutoff is bounded by the composed bound. This combines
`haarWilsonMeasure_action_tail` with the supplied per-link Haar bound. -/
theorem wilsonTail_le_composedTailBound {L : ℕ} [NeZero L] {β ε δ c₁ : ℝ}
    (hβ : 0 ≤ β) (hc₁ : 0 < c₁) (hmass : c₁ ^ (4 * L ^ 4) ≤ haarVacuumSublevelMass L δ) :
    (wilsonMeasure (gaugeHaarMeasure L) β).real {U | ε ≤ wilsonAction 1 U} ≤
      composedTailBound L β ε δ c₁ :=
  (haarWilsonMeasure_action_tail hβ (haarVacuumSublevelMass_threshold_pos hc₁ hmass)).trans
    (div_le_div_of_nonneg_left (Real.exp_pos _).le (pow_pos hc₁ _) hmass)

/-! ## Ingredient (H): Haar-mass lower bound along the path -/

/-- Ingredient (H) along a fixed-volume geometry. At cutoff `n` the product-Haar mass of the
open vacuum sublevel `{S₁ < δ n}` on the `sites n` torus is at least
`c₁ n ^ (4 sites⁴)`. The field `mass_lower` is a hypothesis: this structure does not prove it,
and `c₁` may depend on `n`. -/
structure PathHaarMassBound (G : FixedVolumeGeometry) where
  /-- Total-action threshold of the vacuum sublevel at cutoff `n`. -/
  δ : ℕ → ℝ
  /-- Per-link Haar factor at cutoff `n`. -/
  c₁ : ℕ → ℝ
  c₁_pos : ∀ n, 0 < c₁ n
  mass_lower : ∀ n, c₁ n ^ (4 * G.sites n ^ 4) ≤ haarVacuumSublevelMass (G.sites n) (δ n)

namespace PathHaarMassBound

variable {G : FixedVolumeGeometry} (H : PathHaarMassBound G)

theorem δ_pos (n : ℕ) : 0 < H.δ n :=
  haarVacuumSublevelMass_threshold_pos (H.c₁_pos n) (H.mass_lower n)

theorem c₁_le_one (n : ℕ) : H.c₁ n ≤ 1 :=
  le_one_of_haarMass_lower (H.c₁_pos n) (H.mass_lower n)

theorem log_inv_c₁_nonneg (n : ℕ) : 0 ≤ Real.log (1 / H.c₁ n) :=
  Real.log_nonneg (one_le_one_div (H.c₁_pos n) (H.c₁_le_one n))

/-- Lowering the per-link factor to at most `c` keeps ingredient (H) valid. -/
def clip (c : ℝ) (hc : 0 < c) : PathHaarMassBound G where
  δ := H.δ
  c₁ := fun n => min (H.c₁ n) c
  c₁_pos := fun n => lt_min (H.c₁_pos n) hc
  mass_lower := fun n =>
    (pow_le_pow_left₀ (lt_min (H.c₁_pos n) hc).le (min_le_left _ _) _).trans (H.mass_lower n)

theorem clip_c₁_le (c : ℝ) (hc : 0 < c) (n : ℕ) : (H.clip c hc).c₁ n ≤ c :=
  min_le_right _ _

end PathHaarMassBound

/-! ## Exact balance along a cutoff path -/

/-- Quantitative form along the path: at every cutoff the actual Wilson tail is at most
`exp(-balance)`. -/
theorem wilsonTail_le_exp_neg_balance (P : FixedVolumeCutoffPath)
    (H : PathHaarMassBound P.toFixedVolumeGeometry) (ε : ℝ) (n : ℕ) :
    (wilsonMeasure (gaugeHaarMeasure (P.sites n)) (P.β n)).real {U | ε ≤ wilsonAction 1 U} ≤
      Real.exp (-balanceExponent (P.sites n) (P.β n) ε (H.δ n) (H.c₁ n)) := by
  rw [← composedTailBound_eq_exp_neg_balanceExponent _ _ _ _ (H.c₁_pos n)]
  exact wilsonTail_le_composedTailBound (P.β_nonneg n) (H.c₁_pos n) (H.mass_lower n)

/-- The balance exponent never exceeds the entropy-versus-coupling gain that
`haarWilsonMeasure_action_tail_tendsto_varying_volume` takes as its premise. -/
theorem balanceExponent_le_repositoryGain (P : FixedVolumeCutoffPath)
    (H : PathHaarMassBound P.toFixedVolumeGeometry) (ε : ℝ) (n : ℕ) :
    balanceExponent (P.sites n) (P.β n) ε (H.δ n) (H.c₁ n) ≤
      P.β n * (ε - H.δ n) + Real.log (haarVacuumSublevelMass (P.sites n) (H.δ n)) := by
  have hpow := pow_pos (H.c₁_pos n) (4 * P.sites n ^ 4)
  have hlog := Real.log_le_log hpow (H.mass_lower n)
  rw [Real.log_pow] at hlog
  unfold balanceExponent
  rw [Real.log_div one_ne_zero (H.c₁_pos n).ne', Real.log_one]
  push_cast at hlog
  linarith

/-- The balance discharges the rate premise `hgain` of the repository theorem
`haarWilsonMeasure_action_tail_tendsto_varying_volume`. -/
theorem repositoryGain_tendsto_atTop_of_balance (P : FixedVolumeCutoffPath)
    (H : PathHaarMassBound P.toFixedVolumeGeometry) {ε : ℝ}
    (hbal : Tendsto (fun n => balanceExponent (P.sites n) (P.β n) ε (H.δ n) (H.c₁ n))
      atTop atTop) :
    Tendsto (fun n => P.β n * (ε - H.δ n) +
      Real.log (haarVacuumSublevelMass (P.sites n) (H.δ n))) atTop atTop :=
  tendsto_atTop_mono (balanceExponent_le_repositoryGain P H ε) hbal

/-- Exact balance along a fixed-volume cutoff path, with hypotheses the two ingredients:
(H) the per-link Haar bound `H` and (C) the couplings `P.β`. Fixed: the target `ε`.
1. At every cutoff the actual Wilson tail is at most `composedTailBound = exp(-balance)`.
2. The composed bound tends to zero if and only if the balance exponent tends to `+∞`.
3. If the balance exponent tends to `+∞`, the actual Wilson tail tends to zero; the proof
   feeds the repository theorem `haarWilsonMeasure_action_tail_tendsto_varying_volume`. -/
theorem exact_balance_along_cutoff_path (P : FixedVolumeCutoffPath)
    (H : PathHaarMassBound P.toFixedVolumeGeometry) (ε : ℝ) :
    (∀ n, (wilsonMeasure (gaugeHaarMeasure (P.sites n)) (P.β n)).real
        {U | ε ≤ wilsonAction 1 U} ≤
      composedTailBound (P.sites n) (P.β n) ε (H.δ n) (H.c₁ n)) ∧
    (Tendsto (fun n => composedTailBound (P.sites n) (P.β n) ε (H.δ n) (H.c₁ n)) atTop (𝓝 0) ↔
      Tendsto (fun n => balanceExponent (P.sites n) (P.β n) ε (H.δ n) (H.c₁ n))
        atTop atTop) ∧
    (Tendsto (fun n => balanceExponent (P.sites n) (P.β n) ε (H.δ n) (H.c₁ n)) atTop atTop →
      Tendsto (fun n => (wilsonMeasure (gaugeHaarMeasure (P.sites n)) (P.β n)).real
        {U | ε ≤ wilsonAction 1 U}) atTop (𝓝 0)) := by
  refine ⟨fun n => wilsonTail_le_composedTailBound (P.β_nonneg n) (H.c₁_pos n)
      (H.mass_lower n),
    composedTailBound_tendsto_zero_iff _ _ _ _ ε H.c₁_pos, fun hbal => ?_⟩
  exact haarWilsonMeasure_action_tail_tendsto_varying_volume P.sites P.β H.δ ε P.β_nonneg
    H.δ_pos (repositoryGain_tendsto_atTop_of_balance P H hbal)

/-- Main sufficiency statement: under ingredients (H) and (C) and the balance, the actual Wilson
total-action tail tends to zero along the fixed-volume cutoff path. -/
theorem wilsonTail_tendsto_zero_of_balance (P : FixedVolumeCutoffPath)
    (H : PathHaarMassBound P.toFixedVolumeGeometry) {ε : ℝ}
    (hbal : Tendsto (fun n => balanceExponent (P.sites n) (P.β n) ε (H.δ n) (H.c₁ n))
      atTop atTop) :
    Tendsto (fun n => (wilsonMeasure (gaugeHaarMeasure (P.sites n)) (P.β n)).real
      {U | ε ≤ wilsonAction 1 U}) atTop (𝓝 0) :=
  (exact_balance_along_cutoff_path P H ε).2.2 hbal

/-! ## The balance in physical variables: a quartic threshold -/

/-- Critical value of `β_n a_n⁴` for a constant per-link factor `c₁` and fixed `δ < ε`. -/
def criticalQuarticCoefficient (side ε δ c₁ : ℝ) : ℝ :=
  4 * side ^ 4 * Real.log (1 / c₁) / (ε - δ)

/-- The balance exponent in physical variables:
`(ε-δ) (β a_n⁴ - κ⋆) / a_n⁴` with `κ⋆ = criticalQuarticCoefficient`. -/
theorem balanceExponent_eq_physical (G : FixedVolumeGeometry) (n : ℕ) (β ε δ c₁ : ℝ)
    (hεδ : δ < ε) :
    balanceExponent (G.sites n) β ε δ c₁ =
      (ε - δ) * (β * G.a n ^ 4 - criticalQuarticCoefficient G.side ε δ c₁) / G.a n ^ 4 := by
  unfold balanceExponent criticalQuarticCoefficient
  rw [G.sites_pow_four_eq n]
  have ha : G.a n ≠ 0 := (G.a_pos n).ne'
  have hεδ' : ε - δ ≠ 0 := (sub_pos.mpr hεδ).ne'
  field_simp

/-- Supercritical regime: if `β_n a_n⁴` is eventually at least `κ > κ⋆`, the balance exponent
tends to `+∞`. -/
theorem balanceExponent_tendsto_atTop_of_supercritical (G : FixedVolumeGeometry) (β : ℕ → ℝ)
    {ε δ c₁ κ : ℝ} (hεδ : δ < ε) (hκ : criticalQuarticCoefficient G.side ε δ c₁ < κ)
    (hsuper : ∀ᶠ n in atTop, κ ≤ β n * G.a n ^ 4) :
    Tendsto (fun n => balanceExponent (G.sites n) (β n) ε δ c₁) atTop atTop := by
  have hεδ0 : 0 < ε - δ := sub_pos.mpr hεδ
  have hκ0 : 0 < κ - criticalQuarticCoefficient G.side ε δ c₁ := sub_pos.mpr hκ
  have hs4 : 0 < G.side ^ 4 := pow_pos G.side_pos 4
  have hC : 0 < (ε - δ) * (κ - criticalQuarticCoefficient G.side ε δ c₁) / G.side ^ 4 :=
    div_pos (mul_pos hεδ0 hκ0) hs4
  refine tendsto_atTop_mono' atTop ?_ (G.sites_pow_four_tendsto_atTop.const_mul_atTop hC)
  filter_upwards [hsuper] with n hn
  have ha4 : 0 < G.a n ^ 4 := pow_pos (G.a_pos n) 4
  have ha : G.a n ≠ 0 := (G.a_pos n).ne'
  have hs : G.side ≠ 0 := G.side_pos.ne'
  rw [balanceExponent_eq_physical G n (β n) ε δ c₁ hεδ, G.sites_pow_four_eq n]
  have heq : (ε - δ) * (κ - criticalQuarticCoefficient G.side ε δ c₁) / G.side ^ 4 *
      (G.side ^ 4 / G.a n ^ 4) =
      (ε - δ) * (κ - criticalQuarticCoefficient G.side ε δ c₁) / G.a n ^ 4 := by
    field_simp
  rw [heq]
  apply div_le_div_of_nonneg_right _ ha4.le
  exact mul_le_mul_of_nonneg_left (by linarith) hεδ0.le

/-- Subcritical regime: if `β_n a_n⁴` is eventually at most `κ < κ⋆`, the balance exponent
tends to `-∞`. -/
theorem balanceExponent_tendsto_atBot_of_subcritical (G : FixedVolumeGeometry) (β : ℕ → ℝ)
    {ε δ c₁ κ : ℝ} (hεδ : δ < ε) (hκ : κ < criticalQuarticCoefficient G.side ε δ c₁)
    (hsub : ∀ᶠ n in atTop, β n * G.a n ^ 4 ≤ κ) :
    Tendsto (fun n => balanceExponent (G.sites n) (β n) ε δ c₁) atTop atBot := by
  have hεδ0 : 0 < ε - δ := sub_pos.mpr hεδ
  have hκ0 : κ - criticalQuarticCoefficient G.side ε δ c₁ < 0 := sub_neg.mpr hκ
  have hs4 : 0 < G.side ^ 4 := pow_pos G.side_pos 4
  have hC : (ε - δ) * (κ - criticalQuarticCoefficient G.side ε δ c₁) / G.side ^ 4 < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hεδ0 hκ0) hs4
  refine tendsto_atBot_mono' atTop ?_ (G.sites_pow_four_tendsto_atTop.const_mul_atTop_of_neg hC)
  filter_upwards [hsub] with n hn
  have ha4 : 0 < G.a n ^ 4 := pow_pos (G.a_pos n) 4
  have ha : G.a n ≠ 0 := (G.a_pos n).ne'
  have hs : G.side ≠ 0 := G.side_pos.ne'
  rw [balanceExponent_eq_physical G n (β n) ε δ c₁ hεδ, G.sites_pow_four_eq n]
  have heq : (ε - δ) * (κ - criticalQuarticCoefficient G.side ε δ c₁) / G.side ^ 4 *
      (G.side ^ 4 / G.a n ^ 4) =
      (ε - δ) * (κ - criticalQuarticCoefficient G.side ε δ c₁) / G.a n ^ 4 := by
    field_simp
  rw [heq]
  apply div_le_div_of_nonneg_right _ ha4.le
  exact mul_le_mul_of_nonneg_left (by linarith) hεδ0.le

/-- Converse threshold for a constant factor: if the balance exponent tends to `+∞`, then
`β_n a_n⁴` eventually exceeds `κ⋆`. -/
theorem eventually_supercritical_of_balance (G : FixedVolumeGeometry) (β : ℕ → ℝ)
    {ε δ c₁ : ℝ} (hεδ : δ < ε)
    (hbal : Tendsto (fun n => balanceExponent (G.sites n) (β n) ε δ c₁) atTop atTop) :
    ∀ᶠ n in atTop, criticalQuarticCoefficient G.side ε δ c₁ < β n * G.a n ^ 4 := by
  have hεδ0 : 0 < ε - δ := sub_pos.mpr hεδ
  filter_upwards [hbal.eventually_gt_atTop 0] with n hn
  rw [balanceExponent_eq_physical G n (β n) ε δ c₁ hεδ] at hn
  have ha4 : 0 < G.a n ^ 4 := pow_pos (G.a_pos n) 4
  have h1 : 0 < (ε - δ) * (β n * G.a n ^ 4 - criticalQuarticCoefficient G.side ε δ c₁) := by
    have h := mul_pos hn ha4
    rwa [div_mul_cancel₀ _ ha4.ne'] at h
  by_contra hle
  rw [not_lt] at hle
  nlinarith

/-- Supercritical sufficiency on the actual Wilson law, for a fixed threshold `δ < ε` and a
constant per-link factor `c₁` supplied as ingredient (H).

**Vacuous.** No `PathHaarMassBound` has a constant threshold and a constant per-link factor
(`YangMillsWeakCouplingNecessity.supercritical_hypotheses_unsatisfiable`), so the hypotheses
`hδ` and `hc₁` are never satisfiable together and this theorem constrains no path. The
non-vacuous form is `YangMillsWeakCouplingNecessity.haar_wilsonTail_tendsto_zero_of_rate_balance`. -/
theorem wilsonTail_tendsto_zero_of_supercritical (P : FixedVolumeCutoffPath)
    (H : PathHaarMassBound P.toFixedVolumeGeometry) {ε δ c₁ κ : ℝ}
    (hδ : ∀ n, H.δ n = δ) (hc₁ : ∀ n, H.c₁ n = c₁) (hεδ : δ < ε)
    (hκ : criticalQuarticCoefficient P.side ε δ c₁ < κ)
    (hsuper : ∀ᶠ n in atTop, κ ≤ P.β n * P.a n ^ 4) :
    Tendsto (fun n => (wilsonMeasure (gaugeHaarMeasure (P.sites n)) (P.β n)).real
      {U | ε ≤ wilsonAction 1 U}) atTop (𝓝 0) := by
  apply wilsonTail_tendsto_zero_of_balance P H
  simp only [hδ, hc₁]
  exact balanceExponent_tendsto_atTop_of_supercritical P.toFixedVolumeGeometry P.β hεδ hκ hsuper

/-- Subcritical failure of the composed bound for a fixed threshold `δ < ε` and per-link
factors eventually at most `cbar`: if `β_n a_n⁴` is eventually at most `κ < κ⋆(cbar)`, the
composed bound diverges. -/
theorem composedTailBound_tendsto_atTop_of_subcritical (P : FixedVolumeCutoffPath)
    (H : PathHaarMassBound P.toFixedVolumeGeometry) {ε δ cbar κ : ℝ}
    (hδ : ∀ n, H.δ n = δ) (hc₁ : ∀ᶠ n in atTop, H.c₁ n ≤ cbar) (hεδ : δ < ε)
    (hκ : κ < criticalQuarticCoefficient P.side ε δ cbar)
    (hsub : ∀ᶠ n in atTop, P.β n * P.a n ^ 4 ≤ κ) :
    Tendsto (fun n => composedTailBound (P.sites n) (P.β n) ε (H.δ n) (H.c₁ n)) atTop atTop := by
  rw [composedTailBound_tendsto_atTop_iff _ _ _ _ ε H.c₁_pos]
  refine tendsto_atBot_mono' atTop ?_
    (balanceExponent_tendsto_atBot_of_subcritical P.toFixedVolumeGeometry P.β hεδ hκ hsub)
  filter_upwards [hc₁] with n hn
  rw [hδ n]
  exact balanceExponent_le_of_le _ _ _ _ (H.c₁_pos n) hn

/-- Sub-quartic couplings never balance. If `β_n a_n⁴ → 0` and the per-link factors are
eventually at most some `cbar < 1`, then for every target `ε` and any thresholds the balance
exponent tends to `-∞`. -/
theorem balanceExponent_tendsto_atBot_of_subquartic (P : FixedVolumeCutoffPath)
    (H : PathHaarMassBound P.toFixedVolumeGeometry) {ε cbar : ℝ} (hcbar : cbar < 1)
    (hc₁ : ∀ᶠ n in atTop, H.c₁ n ≤ cbar)
    (hsub : Tendsto (fun n => P.β n * P.a n ^ 4) atTop (𝓝 0)) :
    Tendsto (fun n => balanceExponent (P.sites n) (P.β n) ε (H.δ n) (H.c₁ n)) atTop atBot := by
  obtain ⟨n₀, hn₀⟩ := hc₁.exists
  have hcpos : 0 < cbar := (H.c₁_pos n₀).trans_le hn₀
  have hm : 0 < Real.log (1 / cbar) := Real.log_pos ((one_lt_div hcpos).mpr hcbar)
  have hs4 : 0 < P.side ^ 4 := pow_pos P.side_pos 4
  have hg : Tendsto (fun n => P.β n * P.a n ^ 4 * max ε 0 / P.side ^ 4 -
      4 * Real.log (1 / cbar)) atTop
      (𝓝 (0 * max ε 0 / P.side ^ 4 - 4 * Real.log (1 / cbar))) :=
    ((hsub.mul_const (max ε 0)).div_const (P.side ^ 4)).sub_const _
  have hneg : 0 * max ε 0 / P.side ^ 4 - 4 * Real.log (1 / cbar) < 0 := by
    rw [zero_mul, zero_div, zero_sub]
    linarith
  refine tendsto_atBot_mono' atTop ?_
    (Tendsto.atTop_mul_neg hneg P.sites_pow_four_tendsto_atTop hg)
  filter_upwards [hc₁] with n hn
  have ha : P.a n ≠ 0 := (P.a_pos n).ne'
  have hs : P.side ≠ 0 := P.side_pos.ne'
  have hR : (P.sites n : ℝ) ^ 4 * (P.β n * P.a n ^ 4 * max ε 0 / P.side ^ 4 -
      4 * Real.log (1 / cbar)) =
      P.β n * max ε 0 - 4 * (P.sites n : ℝ) ^ 4 * Real.log (1 / cbar) := by
    rw [P.sites_pow_four_eq n]
    field_simp
  rw [hR]
  have h1 : P.β n * (ε - H.δ n) ≤ P.β n * max ε 0 :=
    mul_le_mul_of_nonneg_left (by linarith [le_max_left ε 0, H.δ_pos n]) (P.β_nonneg n)
  have h2 : Real.log (1 / cbar) ≤ Real.log (1 / H.c₁ n) :=
    Real.log_le_log (one_div_pos.mpr hcpos) (one_div_le_one_div_of_le (H.c₁_pos n) hn)
  have hL : 0 ≤ 4 * (P.sites n : ℝ) ^ 4 := by positivity
  have h3 := mul_le_mul_of_nonneg_left h2 hL
  unfold balanceExponent
  linarith

/-- Under sub-quartic couplings the composed bound diverges. -/
theorem composedTailBound_tendsto_atTop_of_subquartic (P : FixedVolumeCutoffPath)
    (H : PathHaarMassBound P.toFixedVolumeGeometry) {ε cbar : ℝ} (hcbar : cbar < 1)
    (hc₁ : ∀ᶠ n in atTop, H.c₁ n ≤ cbar)
    (hsub : Tendsto (fun n => P.β n * P.a n ^ 4) atTop (𝓝 0)) :
    Tendsto (fun n => composedTailBound (P.sites n) (P.β n) ε (H.δ n) (H.c₁ n)) atTop atTop :=
  (composedTailBound_tendsto_atTop_iff _ _ _ _ ε H.c₁_pos).2
    (balanceExponent_tendsto_atBot_of_subquartic P H hcbar hc₁ hsub)

/-- Logarithmic couplings are sub-quartic: if eventually `β_n ≤ A + B log(1/a_n)`, then
`β_n a_n⁴ → 0`. Growth proportional to `log(1/a)`, the asymptotic-freedom form, is of this
type. -/
theorem subquartic_of_logarithmic (P : FixedVolumeCutoffPath) (A B : ℝ)
    (hlog : ∀ᶠ n in atTop, P.β n ≤ A + B * Real.log (1 / P.a n)) :
    Tendsto (fun n => P.β n * P.a n ^ 4) atTop (𝓝 0) := by
  have h0 : Tendsto P.a atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨P.spacing_tendsto, Eventually.of_forall P.a_pos⟩
  have hl : Tendsto (fun n => Real.log (P.a n) * P.a n ^ (4 : ℝ)) atTop (𝓝 0) :=
    (tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 4)).comp h0
  have hl' : Tendsto (fun n => Real.log (P.a n) * P.a n ^ 4) atTop (𝓝 0) := by
    refine hl.congr fun n => ?_
    congr 1
    exact_mod_cast Real.rpow_natCast (P.a n) 4
  have hupper : Tendsto (fun n => A * P.a n ^ 4 - B * (Real.log (P.a n) * P.a n ^ 4))
      atTop (𝓝 0) := by
    have h := ((P.spacing_tendsto.pow 4).const_mul A).sub (hl'.const_mul B)
    simpa using h
  refine squeeze_zero' (Eventually.of_forall fun n =>
    mul_nonneg (P.β_nonneg n) (by positivity)) ?_ hupper
  filter_upwards [hlog] with n hn
  have hlog1 : Real.log (1 / P.a n) = -Real.log (P.a n) := by
    rw [one_div, Real.log_inv]
  rw [hlog1] at hn
  have ha4 : 0 ≤ P.a n ^ 4 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hn ha4]

/-- Logarithmic couplings never balance: with factors eventually at most `cbar < 1` the
composed total-action bound diverges along the path. -/
theorem composedTailBound_tendsto_atTop_of_logarithmic (P : FixedVolumeCutoffPath)
    (H : PathHaarMassBound P.toFixedVolumeGeometry) {ε cbar : ℝ} (A B : ℝ) (hcbar : cbar < 1)
    (hc₁ : ∀ᶠ n in atTop, H.c₁ n ≤ cbar)
    (hlog : ∀ᶠ n in atTop, P.β n ≤ A + B * Real.log (1 / P.a n)) :
    Tendsto (fun n => composedTailBound (P.sites n) (P.β n) ε (H.δ n) (H.c₁ n)) atTop atTop :=
  composedTailBound_tendsto_atTop_of_subquartic P H hcbar hc₁ (subquartic_of_logarithmic P A B hlog)

/-! ## Repository supply of ingredient (H) -/

/-- The repository's volume-uniform Haar constant (`exists_haar_sublevel_mass_volume_bound`)
supplies ingredient (H) along every geometry with an `n`-independent factor, but only at the
extensive thresholds `δ n = η · 6 L_n⁴`. -/
theorem exists_extensivePathHaarMassBound (G : FixedVolumeGeometry) {η : ℝ} (hη : 0 < η) :
    ∃ H : PathHaarMassBound G, ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ (∀ n, H.c₁ n = c) ∧
      ∀ n, H.δ n = η * (6 * (G.sites n : ℝ) ^ 4) := by
  obtain ⟨c, hc, hc1, hmass⟩ := exists_haar_sublevel_mass_volume_bound hη
  exact ⟨⟨fun n => η * (6 * (G.sites n : ℝ) ^ 4), fun _ => c, fun _ => hc,
    fun n => hmass (G.sites n)⟩, c, hc, hc1, fun _ => rfl, fun _ => rfl⟩

/-- Along a fixed-volume geometry every extensive threshold eventually exceeds any fixed
target. -/
theorem extensiveThreshold_eventually_gt (G : FixedVolumeGeometry) {η : ℝ} (hη : 0 < η)
    (ε : ℝ) : ∀ᶠ n in atTop, ε < η * (6 * (G.sites n : ℝ) ^ 4) := by
  have h := G.sites_pow_four_tendsto_atTop.const_mul_atTop (mul_pos hη (by norm_num : (0 : ℝ) < 6))
  filter_upwards [h.eventually_gt_atTop ε] with n hn
  simpa only [mul_assoc] using hn

/-- Audit of the extensive Haar bound: with thresholds `δ_n = η · 6 L_n⁴` the composed
total-action bound is eventually at least one, whatever the couplings. -/
theorem extensiveHaarBound_composedTailBound_eventually_ge_one (P : FixedVolumeCutoffPath)
    (H : PathHaarMassBound P.toFixedVolumeGeometry) {η : ℝ} (hη : 0 < η)
    (hδ : ∀ n, H.δ n = η * (6 * (P.sites n : ℝ) ^ 4)) (ε : ℝ) :
    ∀ᶠ n in atTop, 1 ≤ composedTailBound (P.sites n) (P.β n) ε (H.δ n) (H.c₁ n) := by
  filter_upwards [extensiveThreshold_eventually_gt P.toFixedVolumeGeometry hη ε] with n hn
  exact one_le_composedTailBound (P.β_nonneg n) (by rw [hδ n]; exact hn.le) (H.c₁_pos n)
    (H.c₁_le_one n)

/-- The repository's extensive Haar bound never makes the fixed-target composed bound vanish
along a fixed-volume cutoff path. -/
theorem extensiveHaarBound_not_tendsto_zero (P : FixedVolumeCutoffPath)
    (H : PathHaarMassBound P.toFixedVolumeGeometry) {η : ℝ} (hη : 0 < η)
    (hδ : ∀ n, H.δ n = η * (6 * (P.sites n : ℝ) ^ 4)) (ε : ℝ) :
    ¬ Tendsto (fun n => composedTailBound (P.sites n) (P.β n) ε (H.δ n) (H.c₁ n))
      atTop (𝓝 0) := by
  intro h
  obtain ⟨n, h1, h2⟩ := ((h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).and
    (extensiveHaarBound_composedTailBound_eventually_ge_one P H hη hδ ε)).exists
  linarith

/-- The repository also supplies ingredient (H) at a fixed total threshold `δ`, by applying
`exists_haar_sublevel_mass_volume_bound` at the per-plaquette scale `δ / (6 L_n⁴)` separately
for each `n`. Only positivity of the resulting `c₁ n` is known: the repository gives no lower
bound on it as a function of `n`. -/
theorem exists_fixedThresholdPathHaarMassBound (G : FixedVolumeGeometry) {δ : ℝ}
    (hδ : 0 < δ) : ∃ H : PathHaarMassBound G, ∀ n, H.δ n = δ := by
  have key : ∀ n, ∃ c : ℝ, 0 < c ∧
      c ^ (4 * G.sites n ^ 4) ≤ haarVacuumSublevelMass (G.sites n) δ := by
    intro n
    have h6 : 0 < 6 * (G.sites n : ℝ) ^ 4 := mul_pos (by norm_num) (pow_pos (G.sites_pos_real n) 4)
    obtain ⟨c, hc, _, hmass⟩ := exists_haar_sublevel_mass_volume_bound (div_pos hδ h6)
    refine ⟨c, hc, ?_⟩
    have h := hmass (G.sites n)
    rwa [div_mul_cancel₀ δ h6.ne'] at h
  choose c hc hmass using key
  exact ⟨⟨fun _ => δ, c, hc, hmass⟩, fun _ => rfl⟩

/-- Non-vacuity of the balance hypothesis for the actual model. For every fixed-volume
geometry and fixed thresholds `0 < δ < ε` there are couplings
`β_n = (4 L_n⁴ log(1/c₁(n)) + n)/(ε-δ)` for which the repository's fixed-threshold Haar bound
satisfies the balance, so the actual tail vanishes. The size of these couplings is set by the
factors `c₁(n)`, on which the repository gives no quantitative information; this statement
supplies no rate. -/
theorem exists_balancing_couplings (G : FixedVolumeGeometry) {δ ε : ℝ} (hδ : 0 < δ)
    (hεδ : δ < ε) :
    ∃ (P : FixedVolumeCutoffPath) (H : PathHaarMassBound P.toFixedVolumeGeometry),
      P.toFixedVolumeGeometry = G ∧ (∀ n, H.δ n = δ) ∧
      Tendsto (fun n => balanceExponent (P.sites n) (P.β n) ε (H.δ n) (H.c₁ n)) atTop atTop ∧
      Tendsto (fun n => (wilsonMeasure (gaugeHaarMeasure (P.sites n)) (P.β n)).real
        {U | ε ≤ wilsonAction 1 U}) atTop (𝓝 0) := by
  obtain ⟨H, hHδ⟩ := exists_fixedThresholdPathHaarMassBound G hδ
  have hεδ0 : 0 < ε - δ := sub_pos.mpr hεδ
  let β : ℕ → ℝ := fun n =>
    (4 * (G.sites n : ℝ) ^ 4 * Real.log (1 / H.c₁ n) + n) / (ε - δ)
  have hβ : ∀ n, 0 ≤ β n := fun n =>
    div_nonneg (add_nonneg (mul_nonneg (by positivity) (H.log_inv_c₁_nonneg n))
      (Nat.cast_nonneg n)) hεδ0.le
  let P : FixedVolumeCutoffPath := { toFixedVolumeGeometry := G, β := β, β_nonneg := hβ }
  have hbal : Tendsto (fun n => balanceExponent (P.sites n) (P.β n) ε (H.δ n) (H.c₁ n))
      atTop atTop := by
    refine tendsto_natCast_atTop_atTop.congr fun n => ?_
    show (n : ℝ) = balanceExponent (G.sites n) (β n) ε (H.δ n) (H.c₁ n)
    unfold balanceExponent
    rw [hHδ n]
    simp only [β]
    rw [div_mul_cancel₀ _ hεδ0.ne']
    ring
  exact ⟨P, H, rfl, hHδ, hbal, wilsonTail_tendsto_zero_of_balance P H hbal⟩

/-! ## The product-box route gives vanishing per-link factors at a fixed threshold -/

/-- Diagonal SU(2) elements `diag(z, z̄)` for a unit complex number `z = c + i s`. -/
def su2DiagUnit (c s : ℝ) (h : c * c + s * s = 1) : SU2 where
  mat := Matrix.diagonal ![(⟨c, s⟩ : ℂ), (starRingEnd ℂ) ⟨c, s⟩]
  unitary := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i
    · simp [← Complex.normSq_eq_conj_mul_self, Complex.normSq_mk, h]
    · simp [Complex.mul_conj, Complex.normSq_mk, h]
  det_one := by
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    simp [Complex.mul_conj, Complex.normSq_mk, h]

theorem su2DiagUnit_mat00 (c s : ℝ) (h : c * c + s * s = 1) :
    (su2DiagUnit c s h).mat 0 0 = ⟨c, s⟩ := by
  simp [su2DiagUnit]

/-- An explicit injective sequence in SU(2): `diag(z_k, z̄_k)` with `Re z_k = 1/(k+2)`. -/
def su2DiagSeq (k : ℕ) : SU2 :=
  su2DiagUnit (1 / ((k : ℝ) + 2)) (Real.sqrt (1 - (1 / ((k : ℝ) + 2)) ^ 2)) (by
    have h1 : (1 / ((k : ℝ) + 2)) ^ 2 ≤ 1 := by
      have hpos : (0 : ℝ) < (k : ℝ) + 2 := by positivity
      have hle : 1 / ((k : ℝ) + 2) ≤ 1 := by
        rw [div_le_one hpos]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      have h0 : 0 ≤ 1 / ((k : ℝ) + 2) := by positivity
      nlinarith
    have hs := Real.mul_self_sqrt (show 0 ≤ 1 - (1 / ((k : ℝ) + 2)) ^ 2 by linarith)
    nlinarith)

theorem su2DiagSeq_injective : Function.Injective su2DiagSeq := by
  intro i j hij
  have h := congrArg (fun A : SU2 => (A.mat 0 0).re) hij
  simp only [su2DiagSeq, su2DiagUnit_mat00] at h
  have hi : (0 : ℝ) < (i : ℝ) + 2 := by positivity
  have hj : (0 : ℝ) < (j : ℝ) + 2 := by positivity
  rw [div_eq_div_iff hi.ne' hj.ne'] at h
  have : (i : ℝ) = j := by linarith
  exact_mod_cast this

/-- Normalized SU(2) Haar measure has no atom at the identity: by left invariance every
singleton has the same mass, and SU(2) contains infinitely many points. -/
theorem haarProbability_singleton_one : SU2.haarProbability {1} = 0 := by
  by_contra hne
  have hsing : ∀ g : SU2, SU2.haarProbability {g} = SU2.haarProbability {1} := by
    intro g
    have h := measure_preimage_mul SU2.haarProbability g⁻¹ {1}
    have hset : (fun h : SU2 => g⁻¹ * h) ⁻¹' {1} = {g} := by
      ext x
      simp [eq_comm]
    rw [hset] at h
    exact h
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt hne (by simp : (1 : ENNReal) ≠ ⊤)
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range N) : Set ℕ)
      (fun k => ({su2DiagSeq k} : Set SU2)) := by
    intro i _ j _ hij
    simp only [Function.onFun, Set.disjoint_singleton]
    exact fun h => hij (su2DiagSeq_injective h)
  have hunion := measure_biUnion_finset hdisj
    (fun k _ => measurableSet_singleton (su2DiagSeq k)) (μ := SU2.haarProbability)
  have hsum : ∑ k ∈ Finset.range N, SU2.haarProbability {su2DiagSeq k} =
      N * SU2.haarProbability {1} := by
    rw [Finset.sum_congr rfl (fun k _ => hsing (su2DiagSeq k)), Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
  have hle : SU2.haarProbability (⋃ k ∈ Finset.range N, {su2DiagSeq k}) ≤ 1 := prob_le_one
  rw [hunion, hsum] at hle
  exact absurd hle (not_le.mpr hN)

/-- The single-link action `1 - Re tr V / 2` vanishes only at the identity. -/
theorem eq_one_of_trace_action_nonpos {V : SU2} (h : 1 - (1 / 2 : ℝ) * (SU2.trace V).re ≤ 0) :
    V = 1 := by
  have h0 := SU2.col0_norm_sq V
  have h1 := SU2.col1_norm_sq V
  have hd := SU2.diag_re_bounds V
  have htr : (SU2.trace V).re = (V.mat 0 0).re + (V.mat 1 1).re := by
    simp [SU2.trace, Matrix.trace, Fin.sum_univ_two]
  rw [htr] at h
  have h00 : (V.mat 0 0).re = 1 := by linarith [hd.1.2, hd.2.2]
  have h11 : (V.mat 1 1).re = 1 := by linarith [hd.1.2, hd.2.2]
  rw [h00] at h0
  rw [h11] at h1
  have h00i : (V.mat 0 0).im = 0 := by
    nlinarith [sq_nonneg (V.mat 0 0).im, sq_nonneg (V.mat 1 0).re, sq_nonneg (V.mat 1 0).im]
  have h10r : (V.mat 1 0).re = 0 := by
    nlinarith [sq_nonneg (V.mat 0 0).im, sq_nonneg (V.mat 1 0).re, sq_nonneg (V.mat 1 0).im]
  have h10i : (V.mat 1 0).im = 0 := by
    nlinarith [sq_nonneg (V.mat 0 0).im, sq_nonneg (V.mat 1 0).re, sq_nonneg (V.mat 1 0).im]
  have h11i : (V.mat 1 1).im = 0 := by
    nlinarith [sq_nonneg (V.mat 1 1).im, sq_nonneg (V.mat 0 1).re, sq_nonneg (V.mat 0 1).im]
  have h01r : (V.mat 0 1).re = 0 := by
    nlinarith [sq_nonneg (V.mat 1 1).im, sq_nonneg (V.mat 0 1).re, sq_nonneg (V.mat 0 1).im]
  have h01i : (V.mat 0 1).im = 0 := by
    nlinarith [sq_nonneg (V.mat 1 1).im, sq_nonneg (V.mat 0 1).re, sq_nonneg (V.mat 0 1).im]
  apply SU2.ext
  show V.mat = (1 : Matrix (Fin 2) (Fin 2) ℂ)
  ext i j
  fin_cases i <;> fin_cases j
  · exact Complex.ext (by simpa [Matrix.one_apply] using h00)
      (by simpa [Matrix.one_apply] using h00i)
  · exact Complex.ext (by simpa [Matrix.one_apply] using h01r)
      (by simpa [Matrix.one_apply] using h01i)
  · exact Complex.ext (by simpa [Matrix.one_apply] using h10r)
      (by simpa [Matrix.one_apply] using h10i)
  · exact Complex.ext (by simpa [Matrix.one_apply] using h11)
      (by simpa [Matrix.one_apply] using h11i)

/-- The single-link action sublevel `{V | 1 - Re tr V / 2 < η}` in SU(2). -/
def actionSublevel (η : ℝ) : Set SU2 := {V | 1 - (1 / 2 : ℝ) * (SU2.trace V).re < η}

theorem measurableSet_actionSublevel (η : ℝ) : MeasurableSet (actionSublevel η) := by
  have hc : Continuous (fun V : SU2 => 1 - (1 / 2 : ℝ) * (SU2.trace V).re) := by
    unfold SU2.trace Matrix.trace
    fun_prop
  exact measurableSet_lt hc.measurable measurable_const

theorem actionSublevel_mono {η η' : ℝ} (h : η ≤ η') :
    actionSublevel η ⊆ actionSublevel η' :=
  fun _ hV => lt_of_lt_of_le hV h

/-- The Haar mass of the single-link action sublevel tends to zero with its scale. No rate is
claimed; the proof uses only the absence of atoms. -/
theorem haar_actionSublevel_tendsto_zero :
    Tendsto (fun η : ℝ => SU2.haarProbability.real (actionSublevel η)) (𝓝[>] 0) (𝓝 0) := by
  let A : ℕ → Set SU2 := fun k => actionSublevel (1 / ((k : ℝ) + 1))
  have hanti : Antitone A := by
    intro i j hij
    apply actionSublevel_mono
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hij 1
  have hinter : (⋂ k, A k) = {1} := by
    ext V
    simp only [Set.mem_iInter, Set.mem_singleton_iff]
    constructor
    · intro hV
      apply eq_one_of_trace_action_nonpos
      by_contra hpos
      rw [not_le] at hpos
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
      have h := hV k
      simp only [A, actionSublevel, Set.mem_ofPred_eq] at h
      linarith
    · rintro rfl k
      simp only [A, actionSublevel, Set.mem_ofPred_eq]
      rw [SU2.trace_one]
      norm_num
      positivity
  have hseq := tendsto_measure_iInter_atTop (μ := SU2.haarProbability)
    (fun k => (measurableSet_actionSublevel _).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hinter, haarProbability_singleton_one] at hseq
  have hseqR : Tendsto (fun k => SU2.haarProbability.real (A k)) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hseq
    rw [ENNReal.toReal_zero] at h
    exact h
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨k, hk⟩ := (Metric.tendsto_atTop.1 hseqR) ε hε |>.imp fun k hk => hk k le_rfl
  refine ⟨1 / ((k : ℝ) + 1), by positivity, fun η hη hdist => ?_⟩
  have hη0 : 0 < η := hη
  rw [Real.dist_eq, sub_zero, abs_of_pos hη0] at hdist
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at hk
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  exact lt_of_le_of_lt (measureReal_mono (actionSublevel_mono hdist.le) (measure_ne_top _ _)) hk

/-- Any nonempty set `K` whose four-link plaquettes all have action below `η` has Haar mass at
most that of `actionSublevel η`: right-translating by `k⁻¹` for some `k ∈ K` maps `K` into the
sublevel. This applies to the neighborhoods of `exists_haar_plaquette_neighborhood`. -/
theorem haar_le_actionSublevel_of_plaquette_nbhd {K : Set SU2} {η : ℝ} (hne : K.Nonempty)
    (hK : ∀ a ∈ K, ∀ b ∈ K, ∀ c ∈ K, ∀ d ∈ K,
      1 - (1 / 2 : ℝ) * (SU2.trace (a * b * c⁻¹ * d⁻¹)).re < η) :
    SU2.haarProbability.real K ≤ SU2.haarProbability.real (actionSublevel η) := by
  obtain ⟨k, hk⟩ := hne
  have hsub : K ⊆ (fun a : SU2 => a * k⁻¹) ⁻¹' actionSublevel η := by
    intro a ha
    have h := hK a ha k hk k hk k hk
    simp only [Set.mem_preimage, actionSublevel, Set.mem_ofPred_eq]
    simpa [mul_assoc] using h
  calc SU2.haarProbability.real K
      ≤ SU2.haarProbability.real ((fun a : SU2 => a * k⁻¹) ⁻¹' actionSublevel η) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ = SU2.haarProbability.real (actionSublevel η) := by
        simp only [Measure.real, measure_preimage_mul_right]

/-- Box factors at a fixed total threshold vanish along every fixed-volume geometry. If the
nonempty neighborhoods `K n` control plaquettes at scales `η n` with `η n · 6 L_n⁴ ≤ δ` (the
condition under which the product box over `K n` lies in `{S₁ < δ}`), then
`Haar(K n) → 0`. So the product-box route cannot supply a constant per-link factor at a fixed
threshold. -/
theorem boxFactor_tendsto_zero (G : FixedVolumeGeometry) {δ : ℝ} (hδ : 0 < δ) (η : ℕ → ℝ)
    (hηδ : ∀ n, η n * (6 * (G.sites n : ℝ) ^ 4) ≤ δ)
    (K : ℕ → Set SU2) (hne : ∀ n, (K n).Nonempty)
    (hK : ∀ n, ∀ a ∈ K n, ∀ b ∈ K n, ∀ c ∈ K n, ∀ d ∈ K n,
      1 - (1 / 2 : ℝ) * (SU2.trace (a * b * c⁻¹ * d⁻¹)).re < η n) :
    Tendsto (fun n => SU2.haarProbability.real (K n)) atTop (𝓝 0) := by
  have hden : Tendsto (fun n => 6 * (G.sites n : ℝ) ^ 4) atTop atTop :=
    G.sites_pow_four_tendsto_atTop.const_mul_atTop (by norm_num)
  have hscale : Tendsto (fun n => δ / (6 * (G.sites n : ℝ) ^ 4)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.div_atTop hden, Eventually.of_forall fun n =>
      div_pos hδ (mul_pos (by norm_num) (pow_pos (G.sites_pos_real n) 4))⟩
  refine squeeze_zero (fun n => measureReal_nonneg) (fun n => ?_)
    (haar_actionSublevel_tendsto_zero.comp hscale)
  have h6 : 0 < 6 * (G.sites n : ℝ) ^ 4 := mul_pos (by norm_num) (pow_pos (G.sites_pos_real n) 4)
  have hle : η n ≤ δ / (6 * (G.sites n : ℝ) ^ 4) := (le_div_iff₀ h6).mpr (hηδ n)
  exact (haar_le_actionSublevel_of_plaquette_nbhd (hne n) (hK n)).trans
    (measureReal_mono (actionSublevel_mono hle) (measure_ne_top _ _))

/-! ## Named missing hypothesis: a single-link Haar mass rate -/

/-- Named missing hypothesis (single-link Haar mass rate). For each per-plaquette action scale
`η > 0` an identity neighborhood `nbhd η` in SU(2) is given such that every plaquette built
from four links in it has action below `η`, and for `η ∈ (0, 1]` its Haar mass is at least
`c₀ η ^ p`. The repository proves positivity of such a mass for each fixed `η`
(`exists_haar_plaquette_neighborhood`) but no lower bound as a function of `η`. This structure
is a hypothesis; it is not proved in this module. -/
structure SingleLinkHaarMassRate where
  c₀ : ℝ
  p : ℝ
  c₀_pos : 0 < c₀
  p_nonneg : 0 ≤ p
  nbhd : ℝ → Set SU2
  plaquette_lt : ∀ η, 0 < η → ∀ a ∈ nbhd η, ∀ b ∈ nbhd η, ∀ c ∈ nbhd η, ∀ d ∈ nbhd η,
    1 - (1 / 2 : ℝ) * (SU2.trace (a * b * c⁻¹ * d⁻¹)).re < η
  mass_rate : ∀ η, 0 < η → η ≤ 1 → c₀ * η ^ p ≤ SU2.haarProbability.real (nbhd η)

/-- Product-Haar box bound for an explicit plaquette-controlling neighborhood `K`: every link
in `K` forces total action below `η · 6 L⁴`. The argument is that of
`exists_haar_sublevel_mass_volume_bound`, with `K` given instead of chosen. -/
theorem haarVacuumSublevelMass_ge_of_plaquette_nbhd (L : ℕ) [NeZero L] {K : Set SU2} {η : ℝ}
    (hK : ∀ a ∈ K, ∀ b ∈ K, ∀ c ∈ K, ∀ d ∈ K,
      1 - (1 / 2 : ℝ) * (SU2.trace (a * b * c⁻¹ * d⁻¹)).re < η) :
    SU2.haarProbability.real K ^ (4 * L ^ 4) ≤
      haarVacuumSublevelMass L (η * (6 * (L : ℝ) ^ 4)) := by
  have hplaq : (Fintype.card (Plaquette L) : ℝ) = 6 * (L : ℝ) ^ 4 := by
    exact_mod_cast card_plaquette_eq_six_mul_pow_four L
  have hbox : (gaugeHaarMeasure L).real (Set.univ.pi fun _ : Link L => K) =
      SU2.haarProbability.real K ^ (4 * L ^ 4) := by
    change (Measure.pi (fun _ : Link L => SU2.haarProbability)
      (Set.univ.pi fun _ : Link L => K)).toReal = _
    rw [Measure.pi_pi]
    simp [Measure.real, ENNReal.toReal_pow, card_link_eq]
  rw [← hbox]
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro U hU
  change wilsonAction 1 U < η * (6 * (L : ℝ) ^ 4)
  have hp : ∀ p : Plaquette L, plaquetteAction U p < η := by
    intro p
    exact hK _ (hU _ (mem_univ _)) _ (hU _ (mem_univ _))
      _ (hU _ (mem_univ _)) _ (hU _ (mem_univ _))
  calc
    wilsonAction 1 U = ∑ p : Plaquette L, plaquetteAction U p := by simp [wilsonAction]
    _ < ∑ _ : Plaquette L, η := by
      apply Finset.sum_lt_sum
      · intro p _; exact (hp p).le
      · exact ⟨⟨0, 0, 1, by decide⟩, Finset.mem_univ _, hp _⟩
    _ = _ := by simp [hplaq, mul_comm]

namespace SingleLinkHaarMassRate

variable (R : SingleLinkHaarMassRate)

/-- Per-link factor at cutoff `n` for a fixed total threshold `δ`:
`c₀ (δ / (6 L_n⁴)) ^ p`. -/
def pathFactor (G : FixedVolumeGeometry) (δ : ℝ) (n : ℕ) : ℝ :=
  R.c₀ * (δ / (6 * (G.sites n : ℝ) ^ 4)) ^ R.p

theorem pathFactor_pos (G : FixedVolumeGeometry) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    0 < R.pathFactor G δ n :=
  mul_pos R.c₀_pos (Real.rpow_pos_of_pos
    (div_pos hδ (mul_pos (by norm_num) (pow_pos (G.sites_pos_real n) 4))) _)

/-- Every single-link rate has a positive exponent: with `p = 0` the masses `Haar(nbhd η)`
would stay above `c₀`, while `haar_le_actionSublevel_of_plaquette_nbhd` and
`haar_actionSublevel_tendsto_zero` force them to zero as `η → 0`. -/
theorem p_pos : 0 < R.p := by
  rcases R.p_nonneg.lt_or_eq with hp | hp
  · exact hp
  · exfalso
    have hIoo : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < η ∧ η < 1 :=
      Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)
    have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ), (0 < η ∧ η < 1) ∧
        SU2.haarProbability.real (actionSublevel η) < R.c₀ :=
      hIoo.and (haar_actionSublevel_tendsto_zero.eventually (gt_mem_nhds R.c₀_pos))
    obtain ⟨η, ⟨hη0, hη1⟩, hηF⟩ := hev.exists
    have hmass := R.mass_rate η hη0 hη1.le
    rw [← hp, Real.rpow_zero, mul_one] at hmass
    have hne : (R.nbhd η).Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      rw [hempty, measureReal_empty] at hmass
      linarith [R.c₀_pos]
    have hbound := haar_le_actionSublevel_of_plaquette_nbhd hne (R.plaquette_lt η hη0)
    linarith

/-- The rate hypothesis yields ingredient (H) at a fixed total threshold `δ ≤ 6`, with the
explicit per-link factor `pathFactor`. -/
def toPathHaarMassBound (G : FixedVolumeGeometry) {δ : ℝ} (hδ : 0 < δ) (hδ6 : δ ≤ 6) :
    PathHaarMassBound G where
  δ := fun _ => δ
  c₁ := R.pathFactor G δ
  c₁_pos := R.pathFactor_pos G hδ
  mass_lower := fun n => by
    have h6 : 0 < 6 * (G.sites n : ℝ) ^ 4 := mul_pos (by norm_num) (pow_pos (G.sites_pos_real n) 4)
    have hη : 0 < δ / (6 * (G.sites n : ℝ) ^ 4) := div_pos hδ h6
    have hL4 : (1 : ℝ) ≤ (G.sites n : ℝ) ^ 4 := one_le_pow₀ (G.one_le_sites_real n)
    have hη1 : δ / (6 * (G.sites n : ℝ) ^ 4) ≤ 1 := by
      rw [div_le_one h6]
      linarith
    have hbox := haarVacuumSublevelMass_ge_of_plaquette_nbhd (G.sites n)
      (R.plaquette_lt _ hη)
    rw [div_mul_cancel₀ δ h6.ne'] at hbox
    exact (pow_le_pow_left₀ (R.pathFactor_pos G hδ n).le (R.mass_rate _ hη hη1) _).trans hbox

/-- Entropy per link under the rate: `log(1/c₁(n)) = log(1/c₀) + p log(6 L_n⁴ / δ)`. -/
theorem log_inv_pathFactor (G : FixedVolumeGeometry) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    Real.log (1 / R.pathFactor G δ n) =
      Real.log (1 / R.c₀) + R.p * Real.log (6 * (G.sites n : ℝ) ^ 4 / δ) := by
  have h6 : 0 < 6 * (G.sites n : ℝ) ^ 4 := mul_pos (by norm_num) (pow_pos (G.sites_pos_real n) 4)
  have hη : 0 < δ / (6 * (G.sites n : ℝ) ^ 4) := div_pos hδ h6
  have hrp : 0 < (δ / (6 * (G.sites n : ℝ) ^ 4)) ^ R.p := Real.rpow_pos_of_pos hη _
  unfold pathFactor
  rw [Real.log_div one_ne_zero (mul_pos R.c₀_pos hrp).ne', Real.log_one,
    Real.log_mul R.c₀_pos.ne' hrp.ne', Real.log_rpow hη,
    Real.log_div one_ne_zero R.c₀_pos.ne', Real.log_one,
    Real.log_div h6.ne' hδ.ne', Real.log_div hδ.ne' h6.ne']
  ring

/-- Under the rate (whose exponent is positive by `p_pos`), bounded quartic couplings
(`β_n a_n⁴ ≤ M`) never balance at a fixed threshold: the balance exponent tends to `-∞`. -/
theorem balanceExponent_tendsto_atBot_of_quartic_bounded (P : FixedVolumeCutoffPath)
    {δ ε M : ℝ} (hδ : 0 < δ) (hquartic : ∀ n, P.β n * P.a n ^ 4 ≤ M) :
    Tendsto (fun n => balanceExponent (P.sites n) (P.β n) ε δ
      (R.pathFactor P.toFixedVolumeGeometry δ n)) atTop atBot := by
  have hp := R.p_pos
  have hX : Tendsto (fun n => Real.log (6 * (P.sites n : ℝ) ^ 4 / δ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      ((P.sites_pow_four_tendsto_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 6)).atTop_div_const hδ)
  have hg : Tendsto (fun n => M * max (ε - δ) 0 / P.side ^ 4 - 4 * Real.log (1 / R.c₀) +
      -(4 * R.p) * Real.log (6 * (P.sites n : ℝ) ^ 4 / δ)) atTop atBot :=
    tendsto_atBot_add_const_left _ _ (hX.const_mul_atTop_of_neg (by linarith))
  refine tendsto_atBot_mono' atTop (Eventually.of_forall fun n => ?_)
    (Tendsto.atTop_mul_atBot₀ P.sites_pow_four_tendsto_atTop hg)
  have ha4 : 0 < P.a n ^ 4 := pow_pos (P.a_pos n) 4
  have hs : P.side ≠ 0 := P.side_pos.ne'
  have he : 0 ≤ max (ε - δ) 0 := le_max_right _ _
  have hβe : P.β n * (ε - δ) ≤ P.β n * max (ε - δ) 0 :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) (P.β_nonneg n)
  have hMe : P.β n * max (ε - δ) 0 ≤ (P.sites n : ℝ) ^ 4 * (M * max (ε - δ) 0 / P.side ^ 4) := by
    rw [P.sites_pow_four_eq n]
    have heq : P.side ^ 4 / P.a n ^ 4 * (M * max (ε - δ) 0 / P.side ^ 4) =
        M * max (ε - δ) 0 / P.a n ^ 4 := by
      field_simp
    rw [heq, le_div_iff₀ ha4]
    have := hquartic n
    nlinarith
  have hexp : (P.sites n : ℝ) ^ 4 * (M * max (ε - δ) 0 / P.side ^ 4 -
      4 * Real.log (1 / R.c₀) + -(4 * R.p) * Real.log (6 * (P.sites n : ℝ) ^ 4 / δ)) =
      (P.sites n : ℝ) ^ 4 * (M * max (ε - δ) 0 / P.side ^ 4) -
        4 * (P.sites n : ℝ) ^ 4 * (Real.log (1 / R.c₀) +
          R.p * Real.log (6 * (P.sites n : ℝ) ^ 4 / δ)) := by
    ring
  show balanceExponent (P.sites n) (P.β n) ε δ (R.pathFactor P.toFixedVolumeGeometry δ n) ≤ _
  unfold balanceExponent
  rw [R.log_inv_pathFactor P.toFixedVolumeGeometry hδ n, hexp]
  linarith

/-- Under the rate (exponent positive by `p_pos`) and fixed `0 < δ < ε`, the balance forces
more than quartic growth: if the balance exponent tends to `+∞`, then `β_n a_n⁴ → ∞`. -/
theorem quartic_tendsto_atTop_of_balance (P : FixedVolumeCutoffPath) {δ ε : ℝ} (hδ : 0 < δ)
    (hεδ : δ < ε)
    (hbal : Tendsto (fun n => balanceExponent (P.sites n) (P.β n) ε δ
      (R.pathFactor P.toFixedVolumeGeometry δ n)) atTop atTop) :
    Tendsto (fun n => P.β n * P.a n ^ 4) atTop atTop := by
  have hp := R.p_pos
  have hεδ0 : 0 < ε - δ := sub_pos.mpr hεδ
  have hX : Tendsto (fun n => Real.log (6 * (P.sites n : ℝ) ^ 4 / δ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      ((P.sites_pow_four_tendsto_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 6)).atTop_div_const hδ)
  have hlow : Tendsto (fun n => 4 * P.side ^ 4 * (Real.log (1 / R.c₀) +
      R.p * Real.log (6 * (P.sites n : ℝ) ^ 4 / δ)) / (ε - δ)) atTop atTop :=
    ((tendsto_atTop_add_const_left _ (Real.log (1 / R.c₀)) (hX.const_mul_atTop hp)).const_mul_atTop
      (mul_pos (by norm_num) (pow_pos P.side_pos 4) : (0 : ℝ) < 4 * P.side ^ 4)).atTop_div_const hεδ0
  refine tendsto_atTop_mono' atTop ?_ hlow
  filter_upwards [hbal.eventually_gt_atTop 0] with n hn
  unfold balanceExponent at hn
  rw [R.log_inv_pathFactor P.toFixedVolumeGeometry hδ n] at hn
  have ha4 : 0 < P.a n ^ 4 := pow_pos (P.a_pos n) 4
  have ha : P.a n ≠ 0 := (P.a_pos n).ne'
  have hside4 : P.side ^ 4 = (P.sites n : ℝ) ^ 4 * P.a n ^ 4 := by
    rw [P.sites_pow_four_eq n]
    field_simp
  rw [div_le_iff₀ hεδ0, hside4]
  nlinarith [mul_pos hn ha4]

/-- Under the rate, ingredient (H) and the balance give the actual tail along the path at a
fixed threshold `δ ≤ 6`. The balance reads
`β_n(ε-δ) - 4 L_n⁴ (log(1/c₀) + p log(6 L_n⁴/δ)) → +∞`. -/
theorem wilsonTail_tendsto_zero_of_rate_balance (P : FixedVolumeCutoffPath) {δ ε : ℝ}
    (hδ : 0 < δ) (hδ6 : δ ≤ 6)
    (hbal : Tendsto (fun n => P.β n * (ε - δ) - 4 * (P.sites n : ℝ) ^ 4 *
      (Real.log (1 / R.c₀) + R.p * Real.log (6 * (P.sites n : ℝ) ^ 4 / δ))) atTop atTop) :
    Tendsto (fun n => (wilsonMeasure (gaugeHaarMeasure (P.sites n)) (P.β n)).real
      {U | ε ≤ wilsonAction 1 U}) atTop (𝓝 0) := by
  apply wilsonTail_tendsto_zero_of_balance P (R.toPathHaarMassBound P.toFixedVolumeGeometry hδ hδ6)
  refine hbal.congr fun n => ?_
  change _ = balanceExponent (P.sites n) (P.β n) ε δ (R.pathFactor P.toFixedVolumeGeometry δ n)
  unfold balanceExponent
  rw [R.log_inv_pathFactor P.toFixedVolumeGeometry hδ n]

end SingleLinkHaarMassRate

/-! ## Repository supply of ingredient (C): the Clause (0) coupling flow -/

/-- A Clause (0) coupling schedule along a cutoff path. At cutoff `n` the bare coupling is the
ultraviolet value `wilsonBeta 0` of a Sussman–Alpöge Clause (0) flow which, after `depth n`
block-spin steps with its odd factor, reaches the infrared block scale `aIR`, where its Wilson
coupling is at most `xLand`. Every flow's drift ceiling `B_sharp` is at most `Bmax`. These are
properties of the supplied flows; the canonical SU(2) family satisfies them
(`clauseZeroCanonicalSchedule`). -/
structure ClauseZeroCouplingSchedule (P : FixedVolumeCutoffPath) where
  flow : ℕ → SussmanAlpogeCouplingFlow
  depth : ℕ → ℕ
  aIR : ℝ
  xLand : ℝ
  Bmax : ℝ
  aIR_pos : 0 < aIR
  spacing_eq : ∀ n, P.a n = (flow n).uvRescaledBareSpacing aIR (depth n)
  coupling_eq : ∀ n, P.β n = (flow n).wilsonBeta 0
  landing_le : ∀ n, (flow n).wilsonBeta (depth n) ≤ xLand
  drift_le : ∀ n, (flow n).B_sharp ≤ Bmax

namespace ClauseZeroCouplingSchedule

variable {P : FixedVolumeCutoffPath}

/-- The Clause (0) flow tube bounds the bare coupling linearly in the block-spin depth. -/
theorem coupling_le (S : ClauseZeroCouplingSchedule P) (n : ℕ) :
    P.β n ≤ S.xLand + S.Bmax * (S.depth n : ℝ) := by
  have htube := ((S.flow n).flow_tube 0 (S.depth n) (Nat.zero_le _)).2
  rw [Nat.cast_zero, sub_zero] at htube
  have hB : (S.flow n).B_sharp * (S.depth n : ℝ) ≤ S.Bmax * (S.depth n : ℝ) :=
    mul_le_mul_of_nonneg_right (S.drift_le n) (Nat.cast_nonneg _)
  have hland := S.landing_le n
  rw [S.coupling_eq n]
  simp only [SussmanAlpogeCouplingFlow.wilsonBeta] at hland ⊢
  linarith

/-- The bare spacing is at most `aIR / 13 ^ depth`, since every Clause (0) factor is `≥ 13`. -/
theorem spacing_le (S : ClauseZeroCouplingSchedule P) (n : ℕ) :
    P.a n ≤ S.aIR / 13 ^ S.depth n := by
  rw [S.spacing_eq n]
  simp only [SussmanAlpogeCouplingFlow.uvRescaledBareSpacing]
  have hL : (13 : ℝ) ≤ ((S.flow n).L : ℝ) := by exact_mod_cast (S.flow n).L_ge_13
  exact div_le_div_of_nonneg_left S.aIR_pos.le (pow_pos (by norm_num) _)
    (pow_le_pow_left₀ (by norm_num) hL _)

theorem depth_mul_spacing_sq_le (S : ClauseZeroCouplingSchedule P) (n : ℕ) :
    (S.depth n : ℝ) * P.a n ^ 2 ≤ S.aIR ^ 2 := by
  have hD : (S.depth n : ℝ) ≤ 169 ^ S.depth n := by
    exact_mod_cast (Nat.lt_pow_self (by norm_num : 1 < 169)).le
  have h13 : ((13 : ℝ) ^ S.depth n) ^ 2 = 169 ^ S.depth n := by
    rw [← pow_right_comm]
    norm_num
  have ha : P.a n ^ 2 ≤ S.aIR ^ 2 / 169 ^ S.depth n := by
    have h := pow_le_pow_left₀ (P.a_pos n).le (S.spacing_le n) 2
    rwa [div_pow, h13] at h
  have h169 : (0 : ℝ) < 169 ^ S.depth n := by positivity
  calc (S.depth n : ℝ) * P.a n ^ 2 ≤ 169 ^ S.depth n * (S.aIR ^ 2 / 169 ^ S.depth n) :=
        mul_le_mul hD ha (by positivity) h169.le
    _ = S.aIR ^ 2 := by field_simp

/-- Every Clause (0) schedule is sub-quartic: `β_n a_n⁴ → 0`. -/
theorem subquartic (S : ClauseZeroCouplingSchedule P) :
    Tendsto (fun n => P.β n * P.a n ^ 4) atTop (𝓝 0) := by
  have hup : ∀ n, P.β n * P.a n ^ 4 ≤
      max S.xLand 0 * P.a n ^ 4 + max S.Bmax 0 * S.aIR ^ 2 * P.a n ^ 2 := by
    intro n
    have hβ := S.coupling_le n
    have ha2 : 0 ≤ P.a n ^ 2 := by positivity
    have ha4 : 0 ≤ P.a n ^ 4 := by positivity
    have hDa := S.depth_mul_spacing_sq_le n
    have hD : (0 : ℝ) ≤ S.depth n := Nat.cast_nonneg _
    have hx := le_max_left S.xLand 0
    have hB := le_max_left S.Bmax 0
    have hB0 := le_max_right S.Bmax 0
    calc P.β n * P.a n ^ 4 ≤ (S.xLand + S.Bmax * S.depth n) * P.a n ^ 4 :=
          mul_le_mul_of_nonneg_right hβ ha4
      _ ≤ (max S.xLand 0 + max S.Bmax 0 * S.depth n) * P.a n ^ 4 := by
          apply mul_le_mul_of_nonneg_right _ ha4
          nlinarith
      _ = max S.xLand 0 * P.a n ^ 4 + max S.Bmax 0 * (S.depth n * P.a n ^ 2) * P.a n ^ 2 := by
          ring
      _ ≤ max S.xLand 0 * P.a n ^ 4 + max S.Bmax 0 * S.aIR ^ 2 * P.a n ^ 2 := by
          have h := mul_le_mul_of_nonneg_left hDa hB0
          nlinarith
  have hlim : Tendsto (fun n => max S.xLand 0 * P.a n ^ 4 +
      max S.Bmax 0 * S.aIR ^ 2 * P.a n ^ 2) atTop (𝓝 0) := by
    have h4 := (P.spacing_tendsto.pow 4).const_mul (max S.xLand 0)
    have h2 := (P.spacing_tendsto.pow 2).const_mul (max S.Bmax 0 * S.aIR ^ 2)
    simpa using h4.add h2
  exact squeeze_zero (fun n => mul_nonneg (P.β_nonneg n) (by positivity)) hup hlim

/-- Audit of ingredient (C): along a Clause (0) schedule, for any per-link factors eventually at
most `cbar < 1` and any thresholds, the balance exponent tends to `-∞`. -/
theorem balanceExponent_tendsto_atBot (S : ClauseZeroCouplingSchedule P)
    (H : PathHaarMassBound P.toFixedVolumeGeometry)
    {ε cbar : ℝ} (hcbar : cbar < 1) (hc₁ : ∀ᶠ n in atTop, H.c₁ n ≤ cbar) :
    Tendsto (fun n => balanceExponent (P.sites n) (P.β n) ε (H.δ n) (H.c₁ n)) atTop atBot :=
  balanceExponent_tendsto_atBot_of_subquartic P H hcbar hc₁ S.subquartic

/-- Along a Clause (0) schedule the composed total-action bound diverges. -/
theorem composedTailBound_tendsto_atTop (S : ClauseZeroCouplingSchedule P)
    (H : PathHaarMassBound P.toFixedVolumeGeometry)
    {ε cbar : ℝ} (hcbar : cbar < 1) (hc₁ : ∀ᶠ n in atTop, H.c₁ n ≤ cbar) :
    Tendsto (fun n => composedTailBound (P.sites n) (P.β n) ε (H.δ n) (H.c₁ n)) atTop atTop :=
  composedTailBound_tendsto_atTop_of_subquartic P H hcbar hc₁ S.subquartic

end ClauseZeroCouplingSchedule

/-- The repository's other coupling object, `BalabanRGTrajectory` (`ConstructiveYangMills.lean`),
bounds its cumulative remainder only from above. Landing at value `x` after `K` steps forces the
bare coupling above the linear floor `x + (K/2) Δ`, and every bare coupling above that floor
occurs. So this structure neither supplies nor excludes a balancing growth of the bare
coupling; it leaves that growth unconstrained from above. -/
theorem balabanRGTrajectory_bare_coupling_floor_only (a0 Δ x : ℝ) (ha0 : 0 < a0) (hΔ : 0 < Δ)
    (K : ℕ) :
    (∀ rg : BalabanRGTrajectory, rg.deltaBetaAF = Δ → rg.effectiveBeta K = x →
      x + (K : ℝ) / 2 * Δ ≤ rg.beta0) ∧
    ∀ β₀ : ℝ, x + (K : ℝ) / 2 * Δ ≤ β₀ →
      ∃ rg : BalabanRGTrajectory, rg.beta0 = β₀ ∧ rg.deltaBetaAF = Δ ∧ rg.effectiveBeta K = x := by
  refine ⟨fun rg hΔrg hx => ?_, fun β₀ hβ₀ => ?_⟩
  · have h := rg.effectiveBeta_upper_bound K
    rw [hx, hΔrg] at h
    linarith
  · let rg : BalabanRGTrajectory :=
      { beta0 := β₀
        a0 := a0
        a0_pos := ha0
        deltaBetaAF := Δ
        deltaBetaAF_pos := hΔ
        cumulativeRemainder := fun k => if k = K then x - β₀ + (K : ℝ) * Δ else 0
        remainder_controlled := by
          intro k
          show (if k = K then x - β₀ + (K : ℝ) * Δ else 0) ≤ (k : ℝ) / 2 * Δ
          split_ifs with hk
          · rw [hk]
            linarith
          · exact mul_nonneg (by positivity) hΔ.le }
    refine ⟨rg, rfl, rfl, ?_⟩
    show β₀ - (K : ℝ) * Δ + (if K = K then x - β₀ + (K : ℝ) * Δ else 0) = x
    split_ifs with hK
    · ring
    · exact absurd rfl hK

/-! ## The canonical SU(2) Clause (0) cutoff path -/

/-- The repository's canonical SU(2) Clause (0) flow with odd blocking factor `b` and
depth `K`: bare coupling `K c₀(b,2) + 1/24`, landing at `1/24` after `K` steps. -/
abbrev canonicalSU2Flow (b K : ℕ) (hb : 13 ≤ b) (hb_odd : b % 2 = 1) :
    SussmanAlpogeCouplingFlow :=
  canonicalMultiStepOddFlow CompactSimpleGaugeGroup.su2 b K hb hb_odd

theorem canonicalSU2Flow_wilsonBeta_zero (b K : ℕ) (hb : 13 ≤ b) (hb_odd : b % 2 = 1) :
    (canonicalSU2Flow b K hb hb_odd).wilsonBeta 0 = (K : ℝ) * sussmanOneLoopCoeff b 2 + 1 / 24 := by
  simp [canonicalSU2Flow, canonicalMultiStepOddFlow, mkCanonicalSussmanAlpogeCouplingFlow,
    SussmanAlpogeCouplingFlow.wilsonBeta, CompactSimpleGaugeGroup.su2]

theorem canonicalSU2Flow_B_sharp (b K : ℕ) (hb : 13 ≤ b) (hb_odd : b % 2 = 1) :
    (canonicalSU2Flow b K hb hb_odd).B_sharp = sussmanOneLoopCoeff b 2 := by
  simp [canonicalSU2Flow, canonicalMultiStepOddFlow, mkCanonicalSussmanAlpogeCouplingFlow,
    CompactSimpleGaugeGroup.su2]

theorem canonicalSU2Flow_landing (b K : ℕ) (hb : 13 ≤ b) (hb_odd : b % 2 = 1) :
    (canonicalSU2Flow b K hb hb_odd).wilsonBeta K = 1 / 24 :=
  (canonicalMultiStepOddFlow_landing_and_massGap CompactSimpleGaugeGroup.su2 b K hb hb_odd
    (a0 := 1) one_pos).1

/-- The repository's canonical SU(2) Clause (0) cutoff path. With `m ≥ 1` infrared blocks of
size `aIR` per direction, cutoff `K` has bare spacing `uvRescaledBareSpacing aIR K = aIR / b^K`,
`m b^K` sites per direction (physical side `m aIR`), and bare coupling `wilsonBeta 0` of
`canonicalMultiStepOddFlow su2 b K`. -/
def clauseZeroCanonicalPath (b m : ℕ) (hb : 13 ≤ b) (hb_odd : b % 2 = 1) (hm : 0 < m)
    (aIR : ℝ) (haIR : 0 < aIR) : FixedVolumeCutoffPath where
  a := fun K => (canonicalSU2Flow b K hb hb_odd).uvRescaledBareSpacing aIR K
  sites := fun K => m * b ^ K
  side := m * aIR
  side_pos := mul_pos (Nat.cast_pos.mpr hm) haIR
  a_pos := fun K => (canonicalSU2Flow b K hb hb_odd).uvRescaledBareSpacing_pos haIR K
  side_eq := fun K => by
    show ((m * b ^ K : ℕ) : ℝ) * (aIR / (b : ℝ) ^ K) = m * aIR
    have hb0 : (b : ℝ) ^ K ≠ 0 := pow_ne_zero _ (by exact_mod_cast (show b ≠ 0 by omega))
    push_cast
    field_simp
  spacing_tendsto := by
    show Tendsto (fun K => aIR / (b : ℝ) ^ K) atTop (𝓝 0)
    exact tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast (show 1 < b by omega)))
  β := fun K => (canonicalSU2Flow b K hb hb_odd).wilsonBeta 0
  β_nonneg := fun K => by
    rw [canonicalSU2Flow_wilsonBeta_zero]
    have hc := sussmanOneLoopCoeff_pos (L := b) (N := 2) (by omega) le_rfl
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) hc.le) (by norm_num)

/-- The canonical path carries a Clause (0) schedule: depth `K`, landing `1/24`, drift
`c₀(b,2)`. -/
def clauseZeroCanonicalSchedule (b m : ℕ) (hb : 13 ≤ b) (hb_odd : b % 2 = 1) (hm : 0 < m)
    (aIR : ℝ) (haIR : 0 < aIR) :
    ClauseZeroCouplingSchedule (clauseZeroCanonicalPath b m hb hb_odd hm aIR haIR) where
  flow := fun K => canonicalSU2Flow b K hb hb_odd
  depth := fun K => K
  aIR := aIR
  xLand := 1 / 24
  Bmax := sussmanOneLoopCoeff b 2
  aIR_pos := haIR
  spacing_eq := fun _ => rfl
  coupling_eq := fun _ => rfl
  landing_le := fun K => (canonicalSU2Flow_landing b K hb hb_odd).le
  drift_le := fun K => (canonicalSU2Flow_B_sharp b K hb hb_odd).le

/-- The canonical path's bare coupling diverges (linearly in the depth `K`). -/
theorem clauseZeroCanonicalPath_coupling_tendsto_atTop (b m : ℕ) (hb : 13 ≤ b)
    (hb_odd : b % 2 = 1) (hm : 0 < m) (aIR : ℝ) (haIR : 0 < aIR) :
    Tendsto (clauseZeroCanonicalPath b m hb hb_odd hm aIR haIR).β atTop atTop := by
  have hc := sussmanOneLoopCoeff_pos (L := b) (N := 2) (by omega) le_rfl
  have h : Tendsto (fun K : ℕ => (K : ℝ) * sussmanOneLoopCoeff b 2 + 1 / 24) atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_mul_const hc).atTop_add tendsto_const_nhds
  refine h.congr fun K => ?_
  exact (canonicalSU2Flow_wilsonBeta_zero b K hb hb_odd).symm

/-- Audit of the canonical path: for every ingredient (H) with factors eventually at most
`cbar < 1` and any thresholds, the composed total-action bound diverges along the repository's
canonical SU(2) Clause (0) path, although its bare coupling diverges. -/
theorem clauseZeroCanonicalPath_composedTailBound_tendsto_atTop (b m : ℕ) (hb : 13 ≤ b)
    (hb_odd : b % 2 = 1) (hm : 0 < m) (aIR : ℝ) (haIR : 0 < aIR)
    (H : PathHaarMassBound (clauseZeroCanonicalPath b m hb hb_odd hm aIR haIR).toFixedVolumeGeometry)
    {ε cbar : ℝ} (hcbar : cbar < 1) (hc₁ : ∀ᶠ n in atTop, H.c₁ n ≤ cbar) :
    Tendsto (fun n => composedTailBound ((clauseZeroCanonicalPath b m hb hb_odd hm aIR haIR).sites n)
      ((clauseZeroCanonicalPath b m hb hb_odd hm aIR haIR).β n) ε (H.δ n) (H.c₁ n))
      atTop atTop :=
  (clauseZeroCanonicalSchedule b m hb hb_odd hm aIR haIR).composedTailBound_tendsto_atTop H
    hcbar hc₁

/-! ## What the repository does supply along the path: action density -/

/-- Action-density tails vanish along every fixed-volume cutoff path whose coupling diverges,
by the volume-uniform threshold of `haarWilsonMeasure_density_tail_uniform`. The threshold
`ε L_n⁴ = ε side⁴ / a_n⁴` of this event diverges along the path. -/
theorem densityTail_tendsto_zero (P : FixedVolumeCutoffPath) (hβ : Tendsto P.β atTop atTop)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (wilsonMeasure (gaugeHaarMeasure (P.sites n)) (P.β n)).real
      {U | ε * (P.sites n : ℝ) ^ 4 ≤ wilsonAction 1 U}) atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun n => lt_of_lt_of_le ha measureReal_nonneg,
    fun b hb => ?_⟩
  obtain ⟨B, hB⟩ := haarWilsonMeasure_density_tail_uniform hε hb
  filter_upwards [hβ.eventually_ge_atTop B] with n hn
  exact hB (P.sites n) (P.β n) hn

/-- The density-event threshold `ε L_n⁴` diverges along every fixed-volume path. -/
theorem densityThreshold_tendsto_atTop (G : FixedVolumeGeometry) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => ε * (G.sites n : ℝ) ^ 4) atTop atTop :=
  G.sites_pow_four_tendsto_atTop.const_mul_atTop hε

/-- Along the canonical Clause (0) path the action-density tails vanish. -/
theorem clauseZeroCanonicalPath_densityTail_tendsto_zero (b m : ℕ) (hb : 13 ≤ b)
    (hb_odd : b % 2 = 1) (hm : 0 < m) (aIR : ℝ) (haIR : 0 < aIR) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (wilsonMeasure (gaugeHaarMeasure
      ((clauseZeroCanonicalPath b m hb hb_odd hm aIR haIR).sites n))
      ((clauseZeroCanonicalPath b m hb hb_odd hm aIR haIR).β n)).real
      {U | ε * ((clauseZeroCanonicalPath b m hb hb_odd hm aIR haIR).sites n : ℝ) ^ 4 ≤
        wilsonAction 1 U}) atTop (𝓝 0) :=
  densityTail_tendsto_zero _
    (clauseZeroCanonicalPath_coupling_tendsto_atTop b m hb hb_odd hm aIR haIR) hε

end JesseMath.Physics.YangMillsCutoffPathBalance

#assert_zfc_axioms
