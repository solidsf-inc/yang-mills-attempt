import JesseMath.Linter.AxiomAudit
import JesseMath.Physics.YangMillsHaarBlocking
import JesseMath.Physics.YangMillsUniformHaarNeighbourhood

/-!
# Plaquette tails of the actual Wilson measure

Everything here is about `wilsonMeasure (gaugeHaarMeasure L) β`, the finite-volume 4D SU(2) Wilson
law on `GaugeConfig L`, with no structure or hypothesis standing in for it.

The tool is one identity. In SU(2), `a + a⁻¹` is a scalar, so moving a link by `g` and by `g⁻¹` has
a second difference controlled by the defect of `g`, with no first-order term:

  `S(T_g U) + S(T_{g⁻¹} U) - 2 S(U) ≤ 12 β D(g)`.

Convexity of `exp` turns this into a transfer of Wilson mass between events, which gives:

* `wilson_plaquette_tail`: `Pr(D(U_p) ≥ t) ≥ 1 / (1 + exp(24 β t))` for `0 < t ≤ 1/2`.
* `wilson_plaquette_tail_half_exp`: `Pr(D(U_p) ≥ t) ≥ (1/2) exp(-12 β)` for `t ≤ 1`.
* `wilson_plaquette_expectation_lower`: `⟨D(U_p)⟩ ≥ 1 / (24 (1 + e) β)` for `β ≥ 1/12`.

All bounds hold for every `L ≥ 2`, with constants independent of `L`.

Limits. These are one-point estimates. None bounds a correlation between separated regions and none
gives a decay rate. Nothing here is specific to SU(2) beyond `a + a⁻¹` being scalar, which also
holds in U(1), so these bounds cannot be a mechanism for a mass gap. No target theorem uses this
module.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter
open scoped Topology Matrix

namespace JesseMath.Physics.YangMillsWilsonPlaquetteTail

/-! ## SU(2) algebra -/

/-- `a + a⁻¹` is the scalar `tr a`, written with defects. -/
theorem linkDefect_mul_add_inv_mul (a h : SU2) :
    linkDefect (a * h) + linkDefect (a⁻¹ * h) =
      2 - 2 * (1 - linkDefect a) * (1 - linkDefect h) := by
  have ha1 := a.mat_one_one
  have ha2 := a.mat_zero_one
  have hm1 : (a * h).mat = a.mat * h.mat := rfl
  have hm2 : (a⁻¹ * h).mat = a.matᴴ * h.mat := rfl
  unfold linkDefect SU2.trace
  rw [hm1, hm2, Matrix.trace_fin_two, Matrix.trace_fin_two, Matrix.trace_fin_two,
    Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [Matrix.conjTranspose_apply, ha1, ha2]
  simp only [Matrix.trace_fin_two, Complex.add_re, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im, star_neg, Complex.conj_conj]
  ring

theorem linkDefect_conj (x y : SU2) : linkDefect (x * y * x⁻¹) = linkDefect y := by
  unfold linkDefect
  rw [SU2.trace_conj]

/-- Every defect in `[0, 2]` occurs. -/
theorem exists_linkDefect_eq {δ : ℝ} (h0 : 0 ≤ δ) (h2 : δ ≤ 2) : ∃ g : SU2, linkDefect g = δ := by
  have hs : 0 ≤ 1 - (1 - δ) ^ 2 := by nlinarith
  have hq : ∑ i, (![1 - δ, Real.sqrt (1 - (1 - δ) ^ 2), 0, 0] : Fin 4 → ℝ) i ^ 2 = 1 := by
    rw [Fin.sum_univ_four]
    simp [Real.sq_sqrt hs]
  refine ⟨SU2.ofCoord _ hq, ?_⟩
  simp [linkDefect, SU2.trace, SU2.ofCoord, Matrix.trace_fin_two]
  ring

/-- The central element `-1`. -/
def centerNeg : SU2 :=
  SU2.ofCoord ![-1, 0, 0, 0] (by rw [Fin.sum_univ_four]; simp)

theorem linkDefect_centerNeg : linkDefect centerNeg = 2 := by
  simp [linkDefect, SU2.trace, centerNeg, SU2.ofCoord, Matrix.trace_fin_two]
  norm_num

theorem centerNeg_inv : centerNeg⁻¹ = centerNeg := by
  apply SU2.ext
  change centerNeg.matᴴ = centerNeg.mat
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [centerNeg, SU2.ofCoord, Matrix.conjTranspose_apply, Complex.ext_iff]

theorem linkDefect_centerNeg_mul (h : SU2) : linkDefect (centerNeg * h) = 2 - linkDefect h := by
  have h1 := linkDefect_mul_add_inv_mul centerNeg h
  rw [centerNeg_inv, linkDefect_centerNeg] at h1
  linarith

/-! ## Moving one link -/

variable {L : ℕ}

/-- Left multiplication of one link by `g`. -/
def linkMove (e : Link L) (g : SU2) (U : GaugeConfig L) : GaugeConfig L :=
  fun f => (if f = e then g else 1) * U f

theorem linkMove_of_ne (e f : Link L) (g : SU2) (U : GaugeConfig L) (h : f ≠ e) :
    linkMove e g U f = U f := by
  simp [linkMove, h]

theorem linkMove_self (e : Link L) (g : SU2) (U : GaugeConfig L) :
    linkMove e g U e = g * U e := by
  simp [linkMove]

theorem shift_ne (hL : 2 ≤ L) (x : Lattice4D L) (μ : Direction) : shift x μ ≠ x := by
  have : Fact (1 < L) := ⟨hL⟩
  intro h
  have := congrFun h μ
  simp [shift, unitVec] at this

/-- A link `e` on the boundary of `q` acts on the holonomy of `q` by a conjugate of `g^{±1}`. -/
theorem exists_conj_form (hL : 2 ≤ L) (U : GaugeConfig L) (q : Plaquette L) {e : Link L}
    (he : e ∈ plaquetteBoundaryLinks q) :
    ∃ (X : SU2) (s : Bool), ∀ g : SU2,
      plaquetteHolonomy (linkMove e g U) q =
        (X * (if s then g else g⁻¹) * X⁻¹) * plaquetteHolonomy U q := by
  have hμν : q.μ ≠ q.ν := ne_of_lt q.h
  have d12 : (⟨q.x, q.μ⟩ : Link L) ≠ ⟨shift q.x q.μ, q.ν⟩ := fun h => hμν (congrArg Link.μ h)
  have d13 : (⟨q.x, q.μ⟩ : Link L) ≠ ⟨shift q.x q.ν, q.μ⟩ :=
    fun h => shift_ne hL q.x q.ν (congrArg Link.x h).symm
  have d14 : (⟨q.x, q.μ⟩ : Link L) ≠ ⟨q.x, q.ν⟩ := fun h => hμν (congrArg Link.μ h)
  have d23 : (⟨shift q.x q.μ, q.ν⟩ : Link L) ≠ ⟨shift q.x q.ν, q.μ⟩ :=
    fun h => hμν (congrArg Link.μ h).symm
  have d24 : (⟨shift q.x q.μ, q.ν⟩ : Link L) ≠ ⟨q.x, q.ν⟩ :=
    fun h => shift_ne hL q.x q.μ (congrArg Link.x h)
  have d34 : (⟨shift q.x q.ν, q.μ⟩ : Link L) ≠ ⟨q.x, q.ν⟩ := fun h => hμν (congrArg Link.μ h)
  classical
  simp only [plaquetteBoundaryLinks, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · refine ⟨1, true, fun g => ?_⟩
    simp only [plaquetteHolonomy, linkMove_self, linkMove_of_ne _ _ _ _ d12.symm,
      linkMove_of_ne _ _ _ _ d13.symm, linkMove_of_ne _ _ _ _ d14.symm]
    simp [mul_assoc]
  · refine ⟨U ⟨q.x, q.μ⟩, true, fun g => ?_⟩
    simp only [plaquetteHolonomy, linkMove_self, linkMove_of_ne _ _ _ _ d12,
      linkMove_of_ne _ _ _ _ d23.symm, linkMove_of_ne _ _ _ _ d24.symm]
    simp [mul_assoc]
  · refine ⟨U ⟨q.x, q.μ⟩ * U ⟨shift q.x q.μ, q.ν⟩ * (U ⟨shift q.x q.ν, q.μ⟩)⁻¹, false, fun g => ?_⟩
    simp only [plaquetteHolonomy, linkMove_self, linkMove_of_ne _ _ _ _ d13,
      linkMove_of_ne _ _ _ _ d23, linkMove_of_ne _ _ _ _ d34.symm]
    simp [mul_assoc]
  · refine ⟨plaquetteHolonomy U q, false, fun g => ?_⟩
    simp only [plaquetteHolonomy, linkMove_self, linkMove_of_ne _ _ _ _ d14,
      linkMove_of_ne _ _ _ _ d24, linkMove_of_ne _ _ _ _ d34]
    simp [mul_assoc]

/-- The two-move identity on one plaquette. -/
theorem plaquetteAction_linkMove_pair (hL : 2 ≤ L) (U : GaugeConfig L) (q : Plaquette L) {e : Link L}
    (he : e ∈ plaquetteBoundaryLinks q) (g : SU2) :
    plaquetteAction (linkMove e g U) q + plaquetteAction (linkMove e g⁻¹ U) q =
      2 - 2 * (1 - linkDefect g) * (1 - plaquetteAction U q) := by
  obtain ⟨X, s, hX⟩ := exists_conj_form hL U q he
  simp only [plaquetteAction_eq_linkDefect, hX]
  cases s
  · simp only [Bool.false_eq_true, ite_false, inv_inv]
    have h := linkDefect_mul_add_inv_mul (X * g⁻¹ * X⁻¹) (plaquetteHolonomy U q)
    have hinv : (X * g⁻¹ * X⁻¹)⁻¹ = X * g * X⁻¹ := by group
    rw [hinv, linkDefect_conj, linkDefect_inv] at h
    exact h
  · simp only [ite_true]
    have h := linkDefect_mul_add_inv_mul (X * g * X⁻¹) (plaquetteHolonomy U q)
    have hinv : (X * g * X⁻¹)⁻¹ = X * g⁻¹ * X⁻¹ := by group
    rw [hinv, linkDefect_conj] at h
    exact h

theorem plaquetteAction_linkMove_of_not_mem (U : GaugeConfig L) (q : Plaquette L) {e : Link L}
    (he : e ∉ plaquetteBoundaryLinks q) (g : SU2) :
    plaquetteAction (linkMove e g U) q = plaquetteAction U q := by
  classical
  simp only [plaquetteBoundaryLinks, Finset.mem_insert, Finset.mem_singleton, not_or] at he
  obtain ⟨h1, h2, h3, h4⟩ := he
  simp only [plaquetteAction, plaquetteHolonomy, linkMove_of_ne _ _ _ _ (Ne.symm h1),
    linkMove_of_ne _ _ _ _ (Ne.symm h2), linkMove_of_ne _ _ _ _ (Ne.symm h3),
    linkMove_of_ne _ _ _ _ (Ne.symm h4)]

variable [NeZero L]

/-- The second difference of the Wilson action under `g`, `g⁻¹` on one link. -/
theorem wilsonAction_linkMove_pair_le (hL : 2 ≤ L) {β : ℝ} (hβ : 0 ≤ β) (U : GaugeConfig L)
    (e : Link L) (g : SU2) :
    wilsonAction β (linkMove e g U) + wilsonAction β (linkMove e g⁻¹ U) ≤
      2 * wilsonAction β U + 12 * β * linkDefect g := by
  classical
  have hδ := linkDefect_nonneg g
  set τ : Plaquette L → ℝ := fun q =>
    plaquetteAction (linkMove e g U) q + plaquetteAction (linkMove e g⁻¹ U) q -
      2 * plaquetteAction U q with hτ
  have hzero : ∀ q ∉ incidentPlaquettes e, τ q = 0 := by
    intro q hq
    have h1 := plaquetteAction_eq_of_agree_off_link (linkMove e g U) U e
      (fun f hf => linkMove_of_ne e f g U hf) q hq
    have h2 := plaquetteAction_eq_of_agree_off_link (linkMove e g⁻¹ U) U e
      (fun f hf => linkMove_of_ne e f g⁻¹ U hf) q hq
    simp only [hτ, h1, h2]
    ring
  have hle : ∀ q, τ q ≤ 2 * linkDefect g := by
    intro q
    by_cases he : e ∈ plaquetteBoundaryLinks q
    · have h := plaquetteAction_linkMove_pair hL U q he g
      have h0 := plaquetteAction_nonneg U q
      simp only [hτ]
      nlinarith
    · simp only [hτ, plaquetteAction_linkMove_of_not_mem U q he]
      nlinarith
  have hsum : ∑ q, τ q ≤ 12 * linkDefect g := by
    calc ∑ q, τ q = ∑ q ∈ incidentPlaquettes e, τ q := by
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro q _ hq
          exact hzero q hq
      _ ≤ ∑ _q ∈ incidentPlaquettes e, 2 * linkDefect g := Finset.sum_le_sum fun q _ => hle q
      _ = (incidentPlaquettes e).card * (2 * linkDefect g) := by simp
      _ ≤ 6 * (2 * linkDefect g) := by
          gcongr
          exact_mod_cast incidentPlaquettes_card_le_six e
      _ = 12 * linkDefect g := by ring
  have hexp : wilsonAction β (linkMove e g U) + wilsonAction β (linkMove e g⁻¹ U) -
      2 * wilsonAction β U = β * ∑ q, τ q := by
    simp only [wilsonAction, hτ, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  nlinarith [mul_le_mul_of_nonneg_left hsum hβ]

/-- Convexity turns the second difference into a pointwise bound on the Boltzmann weight. -/
theorem boltzmannWeight_le_linkMove_pair (hL : 2 ≤ L) {β : ℝ} (hβ : 0 ≤ β) (U : GaugeConfig L)
    (e : Link L) (g : SU2) :
    boltzmannWeight β U ≤ Real.exp (6 * β * linkDefect g) *
      ((boltzmannWeight β (linkMove e g U) + boltzmannWeight β (linkMove e g⁻¹ U)) / 2) := by
  have h := wilsonAction_linkMove_pair_le hL hβ U e g
  set a := wilsonAction β (linkMove e g U)
  set b := wilsonAction β (linkMove e g⁻¹ U)
  set S := wilsonAction β U
  have hmid : Real.exp (-(a + b) / 2) ≤ (Real.exp (-a) + Real.exp (-b)) / 2 := by
    have hx : Real.exp (-a) = Real.exp (-a / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hy : Real.exp (-b) = Real.exp (-b / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hxy : Real.exp (-(a + b) / 2) = Real.exp (-a / 2) * Real.exp (-b / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hx, hy, hxy]
    nlinarith [sq_nonneg (Real.exp (-a / 2) - Real.exp (-b / 2))]
  have hS : Real.exp (-S) ≤ Real.exp (6 * β * linkDefect g) * Real.exp (-(a + b) / 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  calc boltzmannWeight β U = Real.exp (-S) := rfl
    _ ≤ _ := hS
    _ ≤ Real.exp (6 * β * linkDefect g) * ((Real.exp (-a) + Real.exp (-b)) / 2) := by
        gcongr
    _ = _ := rfl

omit [NeZero L] in
@[fun_prop]
theorem continuous_linkMove (e : Link L) (g : SU2) : Continuous (linkMove e g) := by
  apply continuous_pi
  intro f
  exact continuous_const.mul (continuous_apply f)

theorem measurePreserving_linkMove (e : Link L) (g : SU2) :
    MeasurePreserving (linkMove e g) (gaugeHaarMeasure L) (gaugeHaarMeasure L) := by
  change MeasurePreserving
    (fun (U : Link L → SU2) (f : Link L) => (if f = e then g else 1) * U f)
    (Measure.pi (fun _ : Link L => SU2.haarProbability))
    (Measure.pi (fun _ : Link L => SU2.haarProbability))
  refine measurePreserving_pi (fun _ : Link L => SU2.haarProbability)
    (fun _ : Link L => SU2.haarProbability)
    (f := fun f x => (if f = e then g else 1) * x) ?_
  intro f
  exact measurePreserving_mul_left SU2.haarProbability (if f = e then g else 1)

/-! ## Wilson mass of an event -/

/-- Unnormalised Wilson mass of a set. -/
def wilsonMass (L : ℕ) [NeZero L] (β : ℝ) (A : Set (GaugeConfig L)) : ℝ :=
  ∫ U, A.indicator (boltzmannWeight β) U ∂(gaugeHaarMeasure L)

theorem wilsonWeight_indicator_integrable {β : ℝ} (hβ : 0 ≤ β) {A : Set (GaugeConfig L)}
    (hA : MeasurableSet A) :
    Integrable (A.indicator (boltzmannWeight β)) (gaugeHaarMeasure L) :=
  (wilsonWeight_integrable _ hβ (measurable_wilsonAction β)).indicator hA

theorem wilsonMass_nonneg (β : ℝ) (A : Set (GaugeConfig L)) : 0 ≤ wilsonMass L β A :=
  integral_nonneg fun U => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) U

theorem wilsonMass_univ (β : ℝ) : wilsonMass L β Set.univ = wilsonPartition (gaugeHaarMeasure L) β := by
  simp [wilsonMass, wilsonPartition]

theorem wilsonMass_comp_linkMove {β : ℝ} (hβ : 0 ≤ β) {E : Set (GaugeConfig L)} (hE : MeasurableSet E)
    (e : Link L) (g : SU2) :
    ∫ U, E.indicator (boltzmannWeight β) (linkMove e g U) ∂(gaugeHaarMeasure L) =
      wilsonMass L β E := by
  have hT := measurePreserving_linkMove (L := L) e g
  have hint := wilsonWeight_indicator_integrable hβ hE
  have := integral_map (μ := gaugeHaarMeasure L) hT.measurable.aemeasurable
    (f := E.indicator (boltzmannWeight β)) (by rw [hT.map_eq]; exact hint.aestronglyMeasurable)
  rw [hT.map_eq] at this
  exact this.symm

/-- Mass transfer: if `g` and `g⁻¹` both move `F` into `E`, the mass of `F` is at most
`exp(6 β D(g))` times the mass of `E`. -/
theorem wilsonMass_transfer (hL : 2 ≤ L) {β : ℝ} (hβ : 0 ≤ β) (e : Link L) (g : SU2)
    {F E : Set (GaugeConfig L)} (hF : MeasurableSet F) (hE : MeasurableSet E)
    (h1 : ∀ U ∈ F, linkMove e g U ∈ E) (h2 : ∀ U ∈ F, linkMove e g⁻¹ U ∈ E) :
    wilsonMass L β F ≤ Real.exp (6 * β * linkDefect g) * wilsonMass L β E := by
  have hint := wilsonWeight_indicator_integrable hβ hE
  have hcomp (g' : SU2) : Integrable (fun U => E.indicator (boltzmannWeight β) (linkMove e g' U))
      (gaugeHaarMeasure L) :=
    ((measurePreserving_linkMove (L := L) e g').integrable_comp hint.aestronglyMeasurable).mpr hint
  have hpt : ∀ U, F.indicator (boltzmannWeight β) U ≤ Real.exp (6 * β * linkDefect g) *
      ((E.indicator (boltzmannWeight β) (linkMove e g U) +
        E.indicator (boltzmannWeight β) (linkMove e g⁻¹ U)) / 2) := by
    intro U
    by_cases hU : U ∈ F
    · rw [Set.indicator_of_mem hU, Set.indicator_of_mem (h1 U hU), Set.indicator_of_mem (h2 U hU)]
      exact boltzmannWeight_le_linkMove_pair hL hβ U e g
    · rw [Set.indicator_of_notMem hU]
      have ha := Set.indicator_nonneg (s := E) (f := boltzmannWeight β)
        (fun _ _ => (Real.exp_pos _).le) (linkMove e g U)
      have hb := Set.indicator_nonneg (s := E) (f := boltzmannWeight β)
        (fun _ _ => (Real.exp_pos _).le) (linkMove e g⁻¹ U)
      positivity
  have hintR : Integrable (fun U => Real.exp (6 * β * linkDefect g) *
      ((E.indicator (boltzmannWeight β) (linkMove e g U) +
        E.indicator (boltzmannWeight β) (linkMove e g⁻¹ U)) / 2)) (gaugeHaarMeasure L) :=
    (((hcomp g).add (hcomp g⁻¹)).div_const 2).const_mul _
  have hmono := integral_mono (wilsonWeight_indicator_integrable hβ hF) hintR hpt
  rw [integral_const_mul, integral_div, integral_add (hcomp g) (hcomp g⁻¹),
    wilsonMass_comp_linkMove hβ hE, wilsonMass_comp_linkMove hβ hE] at hmono
  calc wilsonMass L β F ≤ _ := hmono
    _ = _ := by ring

/-- The normalised probability of an event, in terms of its mass. -/
theorem wilsonMeasure_real_eq {β : ℝ} (hβ : 0 ≤ β) {A : Set (GaugeConfig L)} (hA : MeasurableSet A) :
    (wilsonMeasure (gaugeHaarMeasure L) β).real A =
      wilsonMass L β A / wilsonPartition (gaugeHaarMeasure L) β := by
  have := wilsonMeasure_isProbabilityMeasure (gaugeHaarMeasure L) hβ (measurable_wilsonAction β)
  have h := integral_wilsonMeasure (gaugeHaarMeasure L) hβ (measurable_wilsonAction β)
    (A.indicator (fun _ => (1 : ℝ)))
  rw [integral_indicator_const _ hA, smul_eq_mul, mul_one] at h
  rw [h, wilsonExpectation, wilsonMass]
  congr 2
  funext U
  by_cases hU : U ∈ A <;> simp [hU]

/-! ## Tail of one plaquette -/

theorem measurableSet_plaquette_lt (p : Plaquette L) (t : ℝ) :
    MeasurableSet {U : GaugeConfig L | plaquetteAction U p < t} :=
  (isOpen_lt (continuous_plaquetteAction p) continuous_const).measurableSet

/-- The first link of a plaquette. -/
def firstLink (p : Plaquette L) : Link L := ⟨p.x, p.μ⟩

omit [NeZero L] in
theorem firstLink_mem (p : Plaquette L) : firstLink p ∈ plaquetteBoundaryLinks p := by
  classical
  simp [plaquetteBoundaryLinks, firstLink]

omit [NeZero L] in
/-- Moving the first link multiplies the holonomy on the left. -/
theorem plaquetteHolonomy_linkMove_first (hL : 2 ≤ L) (U : GaugeConfig L) (p : Plaquette L) (g : SU2) :
    plaquetteHolonomy (linkMove (firstLink p) g U) p = g * plaquetteHolonomy U p := by
  have hμν : p.μ ≠ p.ν := ne_of_lt p.h
  have d2 : (⟨shift p.x p.μ, p.ν⟩ : Link L) ≠ firstLink p := fun h => hμν (congrArg Link.μ h).symm
  have d3 : (⟨shift p.x p.ν, p.μ⟩ : Link L) ≠ firstLink p :=
    fun h => shift_ne hL p.x p.ν (congrArg Link.x h)
  have d4 : (⟨p.x, p.ν⟩ : Link L) ≠ firstLink p := fun h => hμν (congrArg Link.μ h).symm
  simp only [plaquetteHolonomy, linkMove_of_ne _ _ _ _ d2, linkMove_of_ne _ _ _ _ d3,
    linkMove_of_ne _ _ _ _ d4]
  have h1 : linkMove (firstLink p) g U ⟨p.x, p.μ⟩ = g * U ⟨p.x, p.μ⟩ := linkMove_self _ _ _
  rw [h1]
  simp [mul_assoc]

/-- The transfer step on an event `A` that the first link of `p` cannot see. -/
theorem wilsonMass_small_le (hL : 2 ≤ L) {β : ℝ} (hβ : 0 ≤ β) (p : Plaquette L)
    {A : Set (GaugeConfig L)} (hA : MeasurableSet A)
    (hinv : ∀ g U, U ∈ A → linkMove (firstLink p) g U ∈ A) {t : ℝ} (g : SU2)
    (hg : ∀ h : SU2, linkDefect h < t → t ≤ linkDefect (g * h) ∧ t ≤ linkDefect (g⁻¹ * h)) :
    wilsonMass L β (A ∩ {U | plaquetteAction U p < t}) ≤
      (Real.exp (6 * β * linkDefect g) / (1 + Real.exp (6 * β * linkDefect g))) *
        wilsonMass L β A := by
  have hS := measurableSet_plaquette_lt p t
  set F := A ∩ {U : GaugeConfig L | plaquetteAction U p < t} with hFdef
  set E := A ∩ {U : GaugeConfig L | plaquetteAction U p < t}ᶜ with hEdef
  have hF : MeasurableSet F := hA.inter hS
  have hE : MeasurableSet E := hA.inter hS.compl
  have hmove (g' : SU2) (hg' : ∀ h : SU2, linkDefect h < t → t ≤ linkDefect (g' * h)) :
      ∀ U ∈ F, linkMove (firstLink p) g' U ∈ E := by
    rintro U ⟨hUA, hUt⟩
    refine ⟨hinv g' U hUA, ?_⟩
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]
    rw [plaquetteAction_eq_linkDefect, plaquetteHolonomy_linkMove_first hL]
    exact hg' _ hUt
  have htr := wilsonMass_transfer hL hβ (firstLink p) g hF hE
    (hmove g fun h hh => (hg h hh).1) (hmove g⁻¹ fun h hh => (hg h hh).2)
  have hadd : wilsonMass L β A = wilsonMass L β F + wilsonMass L β E := by
    unfold wilsonMass
    rw [← integral_add (wilsonWeight_indicator_integrable hβ hF)
      (wilsonWeight_indicator_integrable hβ hE)]
    congr 1
    funext U
    by_cases h1 : U ∈ A <;> by_cases h2 : plaquetteAction U p < t <;>
      simp [hFdef, hEdef, Set.indicator, h1, h2]
  set x := Real.exp (6 * β * linkDefect g)
  have hx : 0 < x := Real.exp_pos _
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  nlinarith

/-- The element used below `t = 1/2`. -/
theorem exists_move_small {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 1 / 2) :
    ∃ g : SU2, linkDefect g = 4 * t ∧
      ∀ h : SU2, linkDefect h < t → t ≤ linkDefect (g * h) ∧ t ≤ linkDefect (g⁻¹ * h) := by
  obtain ⟨g, hg⟩ := exists_linkDefect_eq (δ := 4 * t) (by linarith) (by linarith)
  refine ⟨g, hg, fun h hh => ?_⟩
  have key (a : SU2) (ha : linkDefect a = 4 * t) : t ≤ linkDefect (a * h) := by
    have h1 := linkDefect_mul_le (a * h) h⁻¹
    rw [mul_inv_cancel_right, linkDefect_inv, ha] at h1
    linarith
  exact ⟨key g hg, key g⁻¹ (by rw [linkDefect_inv, hg])⟩

/-- **Tail bound.** For `L ≥ 2`, `β ≥ 0`, `0 < t ≤ 1/2`:
`Pr(D(U_p) ≥ t) ≥ 1 / (1 + exp(24 β t))`, independent of `L`. -/
theorem wilson_plaquette_tail (hL : 2 ≤ L) {β : ℝ} (hβ : 0 ≤ β) (p : Plaquette L) {t : ℝ}
    (ht : 0 < t) (ht2 : t ≤ 1 / 2) :
    1 / (1 + Real.exp (24 * β * t)) ≤
      (wilsonMeasure (gaugeHaarMeasure L) β).real {U | t ≤ plaquetteAction U p} := by
  obtain ⟨g, hg, hmv⟩ := exists_move_small ht ht2
  have hZ := wilsonPartition_pos (gaugeHaarMeasure L) hβ (measurable_wilsonAction β)
  have hS := measurableSet_plaquette_lt p t
  have hset : {U : GaugeConfig L | t ≤ plaquetteAction U p} = {U | plaquetteAction U p < t}ᶜ := by
    ext U; simp
  have hsmall := wilsonMass_small_le hL hβ p (A := Set.univ) MeasurableSet.univ
    (fun _ _ _ => Set.mem_univ _) g hmv
  have hx : 6 * β * linkDefect g = 24 * β * t := by rw [hg]; ring
  rw [hx, Set.univ_inter, wilsonMass_univ] at hsmall
  have hadd : wilsonMass L β {U | plaquetteAction U p < t} +
      wilsonMass L β {U | plaquetteAction U p < t}ᶜ = wilsonPartition (gaugeHaarMeasure L) β := by
    unfold wilsonMass
    rw [← integral_add (wilsonWeight_indicator_integrable hβ hS)
      (wilsonWeight_indicator_integrable hβ hS.compl), wilsonPartition]
    congr 1
    funext U
    by_cases h : plaquetteAction U p < t <;> simp [Set.indicator, h]
  rw [hset, wilsonMeasure_real_eq hβ hS.compl, le_div_iff₀ hZ]
  set x := Real.exp (24 * β * t)
  have hxp : 0 < x := Real.exp_pos _
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by linarith)]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)] at hsmall
  nlinarith

/-- **The one-plaquette lower bound of the review**, on the actual measure:
`Pr(D(U_p) ≥ t) ≥ (1/2) exp(-12 β)` for `t ≤ 1`. -/
theorem wilson_plaquette_tail_half_exp (hL : 2 ≤ L) {β : ℝ} (hβ : 0 ≤ β) (p : Plaquette L) {t : ℝ}
    (ht1 : t ≤ 1) :
    (1 / 2) * Real.exp (-12 * β) ≤
      (wilsonMeasure (gaugeHaarMeasure L) β).real {U | t ≤ plaquetteAction U p} := by
  have hmain : 1 / (1 + Real.exp (12 * β)) ≤
      (wilsonMeasure (gaugeHaarMeasure L) β).real {U | t ≤ plaquetteAction U p} := by
    have hZ := wilsonPartition_pos (gaugeHaarMeasure L) hβ (measurable_wilsonAction β)
    have hS := measurableSet_plaquette_lt p t
    have hset : {U : GaugeConfig L | t ≤ plaquetteAction U p} = {U | plaquetteAction U p < t}ᶜ := by
      ext U; simp
    have hmv : ∀ h : SU2, linkDefect h < t →
        t ≤ linkDefect (centerNeg * h) ∧ t ≤ linkDefect (centerNeg⁻¹ * h) := by
      intro h hh
      rw [centerNeg_inv, linkDefect_centerNeg_mul]
      constructor <;> linarith
    have hsmall := wilsonMass_small_le hL hβ p (A := Set.univ) MeasurableSet.univ
      (fun _ _ _ => Set.mem_univ _) centerNeg hmv
    have hx : 6 * β * linkDefect centerNeg = 12 * β := by rw [linkDefect_centerNeg]; ring
    rw [hx, Set.univ_inter, wilsonMass_univ] at hsmall
    have hadd : wilsonMass L β {U | plaquetteAction U p < t} +
        wilsonMass L β {U | plaquetteAction U p < t}ᶜ = wilsonPartition (gaugeHaarMeasure L) β := by
      unfold wilsonMass
      rw [← integral_add (wilsonWeight_indicator_integrable hβ hS)
        (wilsonWeight_indicator_integrable hβ hS.compl), wilsonPartition]
      congr 1
      funext U
      by_cases h : plaquetteAction U p < t <;> simp [Set.indicator, h]
    rw [hset, wilsonMeasure_real_eq hβ hS.compl, le_div_iff₀ hZ]
    set x := Real.exp (12 * β)
    have hxp : 0 < x := Real.exp_pos _
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by linarith)]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)] at hsmall
    nlinarith
  refine le_trans ?_ hmain
  have hx1 : 1 ≤ Real.exp (12 * β) := Real.one_le_exp (by linarith)
  have hinv : Real.exp (-12 * β) = (Real.exp (12 * β))⁻¹ := by rw [← Real.exp_neg]; congr 1; ring
  rw [hinv, le_div_iff₀ (by positivity)]
  have hp : 0 < Real.exp (12 * β) := Real.exp_pos _
  field_simp
  linarith

/-! ## The expected plaquette -/

/-- **Lower bound on the plaquette expectation**, of the correct order `1 / β` as `β → ∞`,
independent of `L`. -/
theorem wilson_plaquette_expectation_lower (hL : 2 ≤ L) {β : ℝ} (hβ : 1 / 12 ≤ β) (p : Plaquette L) :
    1 / (24 * (1 + Real.exp 1) * β) ≤
      ∫ U, plaquetteAction U p ∂(wilsonMeasure (gaugeHaarMeasure L) β) := by
  have hβ0 : 0 ≤ β := by linarith
  have hβp : 0 < β := by linarith
  have := wilsonMeasure_isProbabilityMeasure (gaugeHaarMeasure L) hβ0 (measurable_wilsonAction β)
  set ν := wilsonMeasure (gaugeHaarMeasure L) β
  set t : ℝ := 1 / (24 * β) with ht
  have ht0 : 0 < t := by positivity
  have ht2 : t ≤ 1 / 2 := by
    rw [ht, div_le_iff₀ (by positivity)]
    linarith
  have htail := wilson_plaquette_tail hL hβ0 p ht0 ht2
  have hexp : 24 * β * t = 1 := by rw [ht]; field_simp
  rw [hexp] at htail
  have hE : MeasurableSet {U : GaugeConfig L | t ≤ plaquetteAction U p} :=
    measurableSet_le continuous_const.measurable (continuous_plaquetteAction p).measurable
  have hint : Integrable (fun U => plaquetteAction U p) ν := by
    refine wilsonObservable_integrable _ hβ0 (measurable_wilsonAction β)
      (continuous_plaquetteAction p).measurable (B := 2) fun U => ?_
    rw [abs_of_nonneg (plaquetteAction_nonneg U p)]
    exact plaquetteAction_le_two U p
  have hmark : t * ν.real {U | t ≤ plaquetteAction U p} ≤ ∫ U, plaquetteAction U p ∂ν := by
    have hind : (fun U => ({U : GaugeConfig L | t ≤ plaquetteAction U p}).indicator (fun _ => t) U) ≤
        fun U => plaquetteAction U p := by
      intro U
      by_cases h : t ≤ plaquetteAction U p
      · simp [Set.indicator, h]
      · simpa [Set.indicator, h] using plaquetteAction_nonneg U p
    have := integral_mono ((integrable_const t).indicator hE) hint hind
    rw [integral_indicator_const _ hE, smul_eq_mul, mul_comm] at this
    exact this
  calc 1 / (24 * (1 + Real.exp 1) * β) = t * (1 / (1 + Real.exp 1)) := by
        rw [ht]; field_simp
    _ ≤ t * ν.real {U | t ≤ plaquetteAction U p} := by gcongr
    _ ≤ _ := hmark

end JesseMath.Physics.YangMillsWilsonPlaquetteTail

#assert_zfc_axioms
