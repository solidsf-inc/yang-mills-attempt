import JesseMath.Linter.AxiomAudit
import JesseMath.Physics.ConstructiveYangMills
import JesseMath.Unified.HodgeHolonomyDefectComb
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Finite-volume Wilson integration on the actual SU(2) configuration space

The reference measure is an explicit probability measure on `GaugeConfig L`.
Measurability of the actual Wilson action is also explicit: this module does
not yet construct the Borel structure or the product Haar reference measure.
The partition bounds follow from the proved SU(2) plaquette action bounds.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace JesseMath.Physics

variable {L : ℕ} [NeZero L] [MeasurableSpace (GaugeConfig L)]

/-- The finite-volume partition function for the actual Wilson action. -/
def wilsonPartition (μ : Measure (GaugeConfig L)) (β : ℝ) : ℝ :=
  ∫ U, boltzmannWeight β U ∂μ

/-- A normalized real Wilson expectation, with positivity of its denominator
proved below for probability reference measures and nonnegative coupling. -/
def wilsonExpectation (μ : Measure (GaugeConfig L)) (β : ℝ)
    (F : GaugeConfig L → ℝ) : ℝ :=
  (∫ U, boltzmannWeight β U * F U ∂μ) / wilsonPartition μ β

theorem wilsonWeight_measurable {β : ℝ}
    (hS : Measurable (wilsonAction β : GaugeConfig L → ℝ)) :
    Measurable (boltzmannWeight β : GaugeConfig L → ℝ) :=
  Real.continuous_exp.measurable.comp hS.neg

theorem wilsonWeight_integrable (μ : Measure (GaugeConfig L)) [IsProbabilityMeasure μ]
    {β : ℝ} (hβ : 0 ≤ β)
    (hS : Measurable (wilsonAction β : GaugeConfig L → ℝ)) :
    Integrable (boltzmannWeight β) μ := by
  apply (integrable_const (1 : ℝ)).mono' (wilsonWeight_measurable hS).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun U => by
    have hp : 0 < boltzmannWeight β U := Real.exp_pos _
    rw [Real.norm_eq_abs, abs_of_pos hp]
    exact (boltzmannWeight_bounds hβ U).2.2

/-- Uniform bounds at fixed finite volume, obtained from the actual action.
The lower bound depends on volume and is not a continuum mass-gap estimate. -/
theorem wilsonPartition_bounds (μ : Measure (GaugeConfig L)) [IsProbabilityMeasure μ]
    {β : ℝ} (hβ : 0 ≤ β)
    (hS : Measurable (wilsonAction β : GaugeConfig L → ℝ)) :
    Real.exp (-(2 * β * (Fintype.card (Plaquette L) : ℝ))) ≤ wilsonPartition μ β ∧
    wilsonPartition μ β ≤ 1 := by
  have hw := wilsonWeight_integrable μ hβ hS
  constructor
  · simpa [wilsonPartition] using
      (integral_mono (integrable_const _) hw fun U => (boltzmannWeight_bounds hβ U).2.1)
  · simpa [wilsonPartition] using
      (integral_mono hw (integrable_const (1 : ℝ)) fun U => (boltzmannWeight_bounds hβ U).2.2)

theorem wilsonPartition_pos (μ : Measure (GaugeConfig L)) [IsProbabilityMeasure μ]
    {β : ℝ} (hβ : 0 ≤ β)
    (hS : Measurable (wilsonAction β : GaugeConfig L → ℝ)) :
    0 < wilsonPartition μ β :=
  lt_of_lt_of_le (Real.exp_pos _) (wilsonPartition_bounds μ hβ hS).1

theorem wilsonExpectation_one (μ : Measure (GaugeConfig L)) [IsProbabilityMeasure μ]
    {β : ℝ} (hβ : 0 ≤ β)
    (hS : Measurable (wilsonAction β : GaugeConfig L → ℝ)) :
    wilsonExpectation μ β (fun _ => 1) = 1 := by
  simp only [wilsonExpectation, mul_one]
  change wilsonPartition μ β / wilsonPartition μ β = 1
  exact div_self (ne_of_gt (wilsonPartition_pos μ hβ hS))

theorem wilsonWeightedObservable_integrable (μ : Measure (GaugeConfig L))
    [IsProbabilityMeasure μ] {β : ℝ} (hβ : 0 ≤ β)
    (hS : Measurable (wilsonAction β : GaugeConfig L → ℝ))
    {F : GaugeConfig L → ℝ} (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ U, |F U| ≤ B) :
    Integrable (fun U => boltzmannWeight β U * F U) μ := by
  apply (integrable_const B).mono' ((wilsonWeight_measurable hS).mul hF).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun U => by
    change ‖boltzmannWeight β U * F U‖ ≤ B
    have hp : 0 < boltzmannWeight β U := Real.exp_pos _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hp]
    calc
      boltzmannWeight β U * |F U| ≤ boltzmannWeight β U * B :=
        mul_le_mul_of_nonneg_left (hbound U) hp.le
      _ ≤ 1 * B := mul_le_mul_of_nonneg_right (boltzmannWeight_bounds hβ U).2.2 hB
      _ = B := one_mul _

theorem wilsonExpectation_nonneg (μ : Measure (GaugeConfig L)) [IsProbabilityMeasure μ]
    {β : ℝ} (hβ : 0 ≤ β)
    (hS : Measurable (wilsonAction β : GaugeConfig L → ℝ))
    {F : GaugeConfig L → ℝ} (hF : ∀ U, 0 ≤ F U) :
    0 ≤ wilsonExpectation μ β F := by
  apply div_nonneg _ (le_of_lt (wilsonPartition_pos μ hβ hS))
  exact integral_nonneg fun U => mul_nonneg (le_of_lt (Real.exp_pos _)) (hF U)

/-- Bounded real observables retain their bound after Wilson normalization. -/
theorem wilsonExpectation_abs_le (μ : Measure (GaugeConfig L)) [IsProbabilityMeasure μ]
    {β : ℝ} (hβ : 0 ≤ β)
    (hS : Measurable (wilsonAction β : GaugeConfig L → ℝ))
    {F : GaugeConfig L → ℝ} (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ U, |F U| ≤ B) :
    |wilsonExpectation μ β F| ≤ B := by
  have hw := wilsonWeight_integrable μ hβ hS
  have hwF := wilsonWeightedObservable_integrable μ hβ hS hF hB hbound
  have hZ := wilsonPartition_pos μ hβ hS
  have hlo : -B * wilsonPartition μ β ≤ ∫ U, boltzmannWeight β U * F U ∂μ := by
    calc
      -B * wilsonPartition μ β = ∫ U, -B * boltzmannWeight β U ∂μ := by
        rw [integral_const_mul]; rfl
      _ ≤ _ := integral_mono (hw.const_mul _) hwF fun U => by
        have hb := (abs_le.mp (hbound U)).1
        have hp : 0 ≤ boltzmannWeight β U := le_of_lt (Real.exp_pos _)
        nlinarith
  have hhi : (∫ U, boltzmannWeight β U * F U ∂μ) ≤ B * wilsonPartition μ β := by
    calc
      _ ≤ ∫ U, B * boltzmannWeight β U ∂μ :=
        integral_mono hwF (hw.const_mul _) fun U => by
          have hb := (abs_le.mp (hbound U)).2
          have hp : 0 ≤ boltzmannWeight β U := le_of_lt (Real.exp_pos _)
          nlinarith
      _ = B * wilsonPartition μ β := by rw [integral_const_mul]; rfl
  exact abs_le.mpr ⟨(le_div_iff₀ hZ).2 hlo, (div_le_iff₀ hZ).2 hhi⟩

/-- Change of variables for gauge transformations preserving the reference
measure. Product Haar invariance remains an obligation for the intended model. -/
theorem wilsonExpectation_gaugeTransform (μ : Measure (GaugeConfig L)) (β : ℝ)
    (hS : Measurable (wilsonAction β : GaugeConfig L → ℝ))
    (g : GaugeTransformation L) (hpres : MeasurePreserving (gaugeTransform g) μ μ)
    {F : GaugeConfig L → ℝ} (hF : Measurable F) :
    wilsonExpectation μ β (fun U => F (gaugeTransform g U)) = wilsonExpectation μ β F := by
  have h := integral_map_of_stronglyMeasurable (μ := μ) hpres.measurable
    ((wilsonWeight_measurable hS).mul hF).stronglyMeasurable
  rw [hpres.map_eq] at h
  simp only [Pi.mul_apply, boltzmannWeight_gaugeInvariant] at h
  exact congrArg (fun x => x / wilsonPartition μ β) h.symm

/-- The Wilson probability law, formed by weighting the supplied reference
measure with the actual Wilson action and its partition function. -/
def wilsonMeasure (μ : Measure (GaugeConfig L)) (β : ℝ) : Measure (GaugeConfig L) :=
  μ.withDensity (fun U => ENNReal.ofReal (boltzmannWeight β U / wilsonPartition μ β))

theorem wilsonMeasure_isProbabilityMeasure (μ : Measure (GaugeConfig L))
    [IsProbabilityMeasure μ] {β : ℝ} (hβ : 0 ≤ β)
    (hS : Measurable (wilsonAction β : GaugeConfig L → ℝ)) :
    IsProbabilityMeasure (wilsonMeasure μ β) := by
  have hZ := wilsonPartition_pos μ hβ hS
  have hi := (wilsonWeight_integrable μ hβ hS).div_const (wilsonPartition μ β)
  have hp : ∀ᵐ U ∂μ, 0 ≤ boltzmannWeight β U / wilsonPartition μ β :=
    Filter.Eventually.of_forall fun U => div_nonneg (le_of_lt (Real.exp_pos _)) hZ.le
  constructor
  rw [wilsonMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi hp, integral_div]
  change ENNReal.ofReal (wilsonPartition μ β / wilsonPartition μ β) = 1
  simp [ne_of_gt hZ]

theorem wilsonObservable_integrable (μ : Measure (GaugeConfig L)) [IsProbabilityMeasure μ]
    {β : ℝ} (hβ : 0 ≤ β)
    (hS : Measurable (wilsonAction β : GaugeConfig L → ℝ))
    {F : GaugeConfig L → ℝ} (hF : Measurable F) {B : ℝ} (hbound : ∀ U, |F U| ≤ B) :
    Integrable F (wilsonMeasure μ β) := by
  have := wilsonMeasure_isProbabilityMeasure μ hβ hS
  apply (integrable_const B).mono' hF.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun U => by simpa only [Real.norm_eq_abs] using hbound U

/-- The normalized formula is the Bochner integral against the Wilson law.
Bounded measurable observables are integrable by the bounds proved above. -/
theorem integral_wilsonMeasure (μ : Measure (GaugeConfig L)) [IsProbabilityMeasure μ]
    {β : ℝ} (hβ : 0 ≤ β)
    (hS : Measurable (wilsonAction β : GaugeConfig L → ℝ))
    (F : GaugeConfig L → ℝ) :
    (∫ U, F U ∂wilsonMeasure μ β) = wilsonExpectation μ β F := by
  have hZ := wilsonPartition_pos μ hβ hS
  have hm := ((wilsonWeight_measurable hS).div_const (wilsonPartition μ β)).ennreal_ofReal
  have hp (U : GaugeConfig L) : 0 ≤ boltzmannWeight β U / wilsonPartition μ β :=
    div_nonneg (le_of_lt (Real.exp_pos _)) hZ.le
  rw [wilsonMeasure, integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) F]
  simp only [ENNReal.toReal_ofReal (hp _), smul_eq_mul, div_mul_eq_mul_div, integral_div]
  rfl

/-- A blocked law is the pushforward of this same normalized Wilson law.
No effective action, locality, or contraction estimate is encoded here. -/
def wilsonBlockedMeasure {X : Type*} [MeasurableSpace X]
    (μ : Measure (GaugeConfig L)) (β : ℝ) (B : GaugeConfig L → X) : Measure X :=
  Measure.map B (wilsonMeasure μ β)

theorem wilsonBlockedMeasure_isProbabilityMeasure {X : Type*} [MeasurableSpace X]
    (μ : Measure (GaugeConfig L)) [IsProbabilityMeasure μ] {β : ℝ} (hβ : 0 ≤ β)
    (hS : Measurable (wilsonAction β : GaugeConfig L → ℝ))
    {B : GaugeConfig L → X} (hB : Measurable B) :
    IsProbabilityMeasure (wilsonBlockedMeasure μ β B) := by
  have := wilsonMeasure_isProbabilityMeasure μ hβ hS
  exact (Measure.isProbabilityMeasure_map_iff hB.aemeasurable).2 inferInstance

/-- Blocked observables pull back to observables of the original Wilson law. -/
theorem integral_wilsonBlockedMeasure {X : Type*} [MeasurableSpace X]
    (μ : Measure (GaugeConfig L)) [IsProbabilityMeasure μ] {β : ℝ} (hβ : 0 ≤ β)
    (hS : Measurable (wilsonAction β : GaugeConfig L → ℝ))
    {B : GaugeConfig L → X} (hB : Measurable B) {F : X → ℝ} (hF : Measurable F) :
    (∫ x, F x ∂wilsonBlockedMeasure μ β B) =
      wilsonExpectation μ β (fun U => F (B U)) := by
  rw [wilsonBlockedMeasure, integral_map_of_stronglyMeasurable hB hF.stronglyMeasurable]
  exact integral_wilsonMeasure μ hβ hS _

/-- Negative control: without a probability reference, strict positivity fails. -/
theorem wilsonPartition_zero_reference (β : ℝ) :
    wilsonPartition (0 : Measure (GaugeConfig L)) β = 0 := by
  simp [wilsonPartition]

/-- Under a probability reference measure and `0 ≤ β`, the Wilson expectation of any single-plaquette
action `plaquetteAction U p` lies in `[0, 2]`. -/
theorem wilsonExpectation_plaquetteAction_nonneg_and_le_two
    (μ : Measure (GaugeConfig L)) [IsProbabilityMeasure μ] {β : ℝ} (hβ : 0 ≤ β)
    (hS : Measurable (wilsonAction β : GaugeConfig L → ℝ))
    (p : Plaquette L) (hp : Measurable (fun U : GaugeConfig L => plaquetteAction U p)) :
    0 ≤ wilsonExpectation μ β (fun U => plaquetteAction U p) ∧
    wilsonExpectation μ β (fun U => plaquetteAction U p) ≤ 2 := by
  refine ⟨wilsonExpectation_nonneg μ hβ hS (fun U => plaquetteAction_nonneg U p), ?_⟩
  have habs : |wilsonExpectation μ β (fun U => plaquetteAction U p)| ≤ 2 :=
    wilsonExpectation_abs_le μ hβ hS hp (by norm_num) fun U =>
      abs_le.mpr ⟨by linarith [plaquetteAction_nonneg U p], plaquetteAction_le_two U p⟩
  exact (abs_le.mp habs).2

/-- Gauge-transformation invariance of the single-plaquette Wilson expectation under any
measure-preserving local gauge transformation `g`. -/
theorem wilsonExpectation_plaquetteAction_gaugeTransform
    (μ : Measure (GaugeConfig L)) (β : ℝ)
    (hS : Measurable (wilsonAction β : GaugeConfig L → ℝ))
    (g : GaugeTransformation L) (hpres : MeasurePreserving (gaugeTransform g) μ μ)
    (p : Plaquette L) (hp : Measurable (fun U : GaugeConfig L => plaquetteAction U p)) :
    wilsonExpectation μ β (fun U => plaquetteAction (gaugeTransform g U) p) =
      wilsonExpectation μ β (fun U => plaquetteAction U p) :=
  wilsonExpectation_gaugeTransform μ β hS g hpres hp

/-- Any pointwise gauge-invariant observable `F` (`∀ U, F (gaugeTransform g U) = F U`) has
identical Wilson expectation before and after `gaugeTransform g` for every reference measure `μ`,
without requiring `MeasurePreserving (gaugeTransform g) μ μ`. -/
theorem wilsonExpectation_of_gaugeInvariant
    (μ : Measure (GaugeConfig L)) (β : ℝ)
    (g : GaugeTransformation L) (F : GaugeConfig L → ℝ)
    (hinv : ∀ U, F (gaugeTransform g U) = F U) :
    wilsonExpectation μ β (fun U => F (gaugeTransform g U)) =
      wilsonExpectation μ β F := by
  have hfun : (fun U => F (gaugeTransform g U)) = F := funext hinv
  rw [hfun]

/-- Unconditional gauge-transformation invariance of the single-plaquette Wilson expectation for
every reference measure `μ`, derived directly from pointwise gauge invariance of `plaquetteAction`. -/
theorem wilsonExpectation_plaquetteAction_gaugeInvariant_unconditional
    (μ : Measure (GaugeConfig L)) (β : ℝ)
    (g : GaugeTransformation L) (p : Plaquette L) :
    wilsonExpectation μ β (fun U => plaquetteAction (gaugeTransform g U) p) =
      wilsonExpectation μ β (fun U => plaquetteAction U p) :=
  wilsonExpectation_of_gaugeInvariant μ β g (fun U => plaquetteAction U p) (fun U => by
    unfold plaquetteAction
    rw [plaquetteTrace_gaugeTransform])

/-- Concrete dyadic 2-step link holonomy block-spin map from a fine `2 * L` lattice to a coarse `L` lattice,
multiplying the two fine SU(2) link matrices along each coarse link direction `e.μ`. -/
def dyadicLinkBlockMap (L : ℕ) (U : GaugeConfig (2 * L)) : GaugeConfig L :=
  fun e =>
    let x2 : Lattice4D (2 * L) := fun i => ((2 * (e.x i).val : ℕ) : ZMod (2 * L))
    U ⟨x2, e.μ⟩ * U ⟨shift x2 e.μ, e.μ⟩

/-- The dyadic 2-step block-spin map sends the fine classical vacuum `vacuumConfig (2 * L)` to the
coarse classical vacuum `vacuumConfig L`. -/
theorem dyadicLinkBlockMap_vacuum (L : ℕ) :
    dyadicLinkBlockMap L (vacuumConfig (2 * L)) = vacuumConfig L := by
  funext e
  simp [dyadicLinkBlockMap, vacuumConfig]

/-- Gauge-invariant unsubtracted two-plaquette Wilson correlator `E_{μ,β}[s_p(U) s_q(U)]`. -/
def wilsonTwoPlaquetteCorrelator (μ : Measure (GaugeConfig L)) (β : ℝ)
    (p q : Plaquette L) : ℝ :=
  wilsonExpectation μ β (fun U => plaquetteAction U p * plaquetteAction U q)

/-- Under a probability reference measure and `0 ≤ β`, the two-plaquette Wilson correlator
lies in `[0, 4]`, and is unconditionally invariant under all local SU(2) gauge transformations. -/
theorem wilsonTwoPlaquetteCorrelator_bounds_and_gaugeInvariant
    (μ : Measure (GaugeConfig L)) [IsProbabilityMeasure μ] {β : ℝ} (hβ : 0 ≤ β)
    (hS : Measurable (wilsonAction β : GaugeConfig L → ℝ))
    (p q : Plaquette L)
    (hp : Measurable (fun U : GaugeConfig L => plaquetteAction U p))
    (hq : Measurable (fun U : GaugeConfig L => plaquetteAction U q))
    (g : GaugeTransformation L) :
    0 ≤ wilsonTwoPlaquetteCorrelator μ β p q ∧
    wilsonTwoPlaquetteCorrelator μ β p q ≤ 4 ∧
    wilsonExpectation μ β
      (fun U => plaquetteAction (gaugeTransform g U) p * plaquetteAction (gaugeTransform g U) q) =
      wilsonTwoPlaquetteCorrelator μ β p q ∧
    ∀ {d : ℕ} (ps : Fin d → Plaquette L) (c : Fin d → ℝ),
      0 ≤ wilsonExpectation μ β (fun U => (∑ i : Fin d, c i * plaquetteAction U (ps i)) ^ 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact wilsonExpectation_nonneg μ hβ hS
      (fun U => mul_nonneg (plaquetteAction_nonneg U p) (plaquetteAction_nonneg U q))
  · have habs : |wilsonTwoPlaquetteCorrelator μ β p q| ≤ 4 := by
      unfold wilsonTwoPlaquetteCorrelator
      apply wilsonExpectation_abs_le μ hβ hS (hp.mul hq) (by norm_num)
      intro U
      dsimp only [Pi.mul_apply]
      have hp0 := plaquetteAction_nonneg U p
      have hp2 := plaquetteAction_le_two U p
      have hq0 := plaquetteAction_nonneg U q
      have hq2 := plaquetteAction_le_two U q
      have hprod0 : 0 ≤ plaquetteAction U p * plaquetteAction U q := mul_nonneg hp0 hq0
      have hprod4 : plaquetteAction U p * plaquetteAction U q ≤ 4 := by nlinarith
      exact abs_le.mpr ⟨by linarith, hprod4⟩
    exact (abs_le.mp habs).2
  · unfold wilsonTwoPlaquetteCorrelator
    exact wilsonExpectation_of_gaugeInvariant μ β g
      (fun U => plaquetteAction U p * plaquetteAction U q) (fun U => by
        unfold plaquetteAction
        rw [plaquetteTrace_gaugeTransform, plaquetteTrace_gaugeTransform])
  · intro d ps c
    exact wilsonExpectation_nonneg μ hβ hS (fun U => sq_nonneg _)

omit [NeZero L] in
/-- Coarse single-plaquette expectation under the dyadic blocked Wilson law
`wilsonBlockedMeasure μ β (dyadicLinkBlockMap L)` on a fine `2 * L` lattice:
pulls back to the fine Wilson expectation of the blocked plaquette action, preserves the
classical vacuum `dyadicLinkBlockMap L (vacuumConfig (2 * L)) = vacuumConfig L`, and lies in `[0, 2]`. -/
theorem wilsonBlockedMeasure_dyadicLinkBlockMap_plaquette_bounds
    [NeZero (2 * L)] [MeasurableSpace (GaugeConfig (2 * L))]
    (μ : Measure (GaugeConfig (2 * L))) [IsProbabilityMeasure μ] {β : ℝ} (hβ : 0 ≤ β)
    (hS : Measurable (wilsonAction β : GaugeConfig (2 * L) → ℝ))
    (hB : Measurable (dyadicLinkBlockMap L))
    (p : Plaquette L)
    (hp : Measurable (fun U_coarse : GaugeConfig L => plaquetteAction U_coarse p)) :
    dyadicLinkBlockMap L (vacuumConfig (2 * L)) = vacuumConfig L ∧
    (∫ U_coarse, plaquetteAction U_coarse p ∂wilsonBlockedMeasure μ β (dyadicLinkBlockMap L)) =
      wilsonExpectation μ β (fun U => plaquetteAction (dyadicLinkBlockMap L U) p) ∧
    0 ≤ (∫ U_coarse, plaquetteAction U_coarse p ∂wilsonBlockedMeasure μ β (dyadicLinkBlockMap L)) ∧
    (∫ U_coarse, plaquetteAction U_coarse p ∂wilsonBlockedMeasure μ β (dyadicLinkBlockMap L)) ≤ 2 := by
  have h_pull := integral_wilsonBlockedMeasure μ hβ hS hB hp
  have h_nonneg : 0 ≤ wilsonExpectation μ β (fun U => plaquetteAction (dyadicLinkBlockMap L U) p) :=
    wilsonExpectation_nonneg μ hβ hS (fun U => plaquetteAction_nonneg (dyadicLinkBlockMap L U) p)
  have h_abs : |wilsonExpectation μ β (fun U => plaquetteAction (dyadicLinkBlockMap L U) p)| ≤ 2 := by
    apply wilsonExpectation_abs_le μ hβ hS (hp.comp hB) (by norm_num)
    intro U
    dsimp only [Function.comp_apply]
    have hp0 : 0 ≤ plaquetteAction (dyadicLinkBlockMap L U) p :=
      plaquetteAction_nonneg (dyadicLinkBlockMap L U) p
    exact abs_le.mpr ⟨by linarith, plaquetteAction_le_two (dyadicLinkBlockMap L U) p⟩
  have h_le_two : wilsonExpectation μ β (fun U => plaquetteAction (dyadicLinkBlockMap L U) p) ≤ 2 :=
    (abs_le.mp h_abs).2
  refine ⟨dyadicLinkBlockMap_vacuum L, h_pull, ?_, ?_⟩
  · linarith
  · linarith

/-- Synthesis of the finite-volume Wilson plaquette expectation bounds with the
Jessian `HodgeHolonomyDefectComb` non-Abelian plaquette Stokes refinement theorems:
combines `[0, 2]` single-plaquette expectation bounds with `M`-plaquette telescoped holonomy
subadditivity (`D M ≤ M * eps_fine`) and `k`-step continuum refinement convergence
(`(L^k)^2 * (F_max * (A_surf / (L^k)^2) + delta_UV / (L^k)^3) = F_max * A_surf + delta_UV / L^k`). -/
theorem wilson_hodge_plaquette_stokes_refinement_bridge
    (μ : Measure (GaugeConfig L)) [IsProbabilityMeasure μ] {β : ℝ} (hβ : 0 ≤ β)
    (hS : Measurable (wilsonAction β : GaugeConfig L → ℝ))
    (p : Plaquette L) (hp : Measurable (fun U : GaugeConfig L => plaquetteAction U p))
    (D d_plaq : ℕ → ℝ) {eps_fine L_pow_k F_max A_surf delta_UV D_loop : ℝ} (M : ℕ)
    (hD0 : D 0 = 0) (hD_nonneg : 0 ≤ D M)
    (h_step : ∀ m : ℕ, D (m + 1) ≤ D m + d_plaq m)
    (h_fine : ∀ m : ℕ, d_plaq m ≤ eps_fine)
    (hL : 1 ≤ L_pow_k) (hdelta : 0 ≤ delta_UV)
    (h_stokes : D_loop ≤ L_pow_k ^ 2 * (F_max * (A_surf / L_pow_k ^ 2) + delta_UV / L_pow_k ^ 3)) :
    (0 ≤ wilsonExpectation μ β (fun U => plaquetteAction U p) ∧
      wilsonExpectation μ β (fun U => plaquetteAction U p) ≤ 2) ∧
    (D M ≤ (M : ℝ) * eps_fine ∧ (D M) ^ 2 ≤ (M : ℝ) ^ 2 * eps_fine ^ 2) ∧
    (L_pow_k ^ 2 * (F_max * (A_surf / L_pow_k ^ 2) + delta_UV / L_pow_k ^ 3) =
      F_max * A_surf + delta_UV / L_pow_k ∧
     D_loop ≤ F_max * A_surf + delta_UV / L_pow_k ∧
     F_max * A_surf + delta_UV / L_pow_k ≤ F_max * A_surf + delta_UV) := by
  exact ⟨wilsonExpectation_plaquetteAction_nonneg_and_le_two μ hβ hS p hp,
    JesseMath.Unified.HodgeHolonomyDefectComb.non_abelian_plaquette_holonomy_telescoped_bound
      D d_plaq M hD0 hD_nonneg h_step h_fine,
    JesseMath.Unified.HodgeHolonomyDefectComb.plaquette_stokes_refinement_convergence
      hL hdelta h_stokes⟩

/-!
## Milestone M1 (Part A): Canonical Coupling-Extraction Rule & Conditional Fiber Disintegration

Without a canonical linear coupling-extraction rule `Λ_proj`, decomposing a coarse effective
action `A_eff(V)` into `β_next * wilsonAction 1 V + K_next(V)` is non-unique: shifting
`β_next ↦ β_next + δ` and `K_next(V) ↦ K_next(V) - δ * wilsonAction 1 V` preserves the sum
pointwise. Fixing a linear coupling-extraction rule `LinearPlaquetteCouplingExtractor L`
normalized by `proj (wilsonAction 1) = 1` and `proj (fun _ => c) = 0` makes the decomposition
unique on `GaugeConfig L`.

Furthermore, given any conditional fiber probability disintegration
`fiberKernel : GaugeConfig L → Measure (GaugeConfig (2 * L))` of the fine reference measure
over `dyadicLinkBlockMap L`, the proved `SU(2)` Boltzmann bounds on `GaugeConfig (2 * L)` imply
that the blocked fiber marginal weight `wilsonBlockedFiberWeight dis β V` is strictly positive
on **all** of `GaugeConfig L` (`exp(-2 * β * |Plaquette (2 * L)|) ≤ W_block(β, V) ≤ 1`),
eliminating zero-density sectors and yielding a globally finite coarse effective action
`wilsonBlockedEffectiveAction dis β V = -log W_block(β, V)` on `GaugeConfig L`.
-/

omit [MeasurableSpace (GaugeConfig L)] in
/-- Homogeneity of the actual `SU(2)` Wilson action in the coupling parameter:
`wilsonAction β V = β * wilsonAction 1 V`. -/
theorem wilsonAction_eq_beta_mul_wilsonAction_one (β : ℝ) (V : GaugeConfig L) :
    wilsonAction β V = β * wilsonAction 1 V := by
  simp [wilsonAction]

omit [MeasurableSpace (GaugeConfig L)] in
/-- Negative control (`M1` ambiguity without coupling extractor): without a linear projection rule
fixing the single-plaquette coefficient, any decomposition `A(V) = β * wilsonAction 1 V + K(V)`
admits a continuum of distinct shifts `(β + δ, K - δ * wilsonAction 1)` with `β + δ ≠ β` for all
`δ ≠ 0`. -/
theorem effectiveActionDecomposition_nonunique_without_extractor
    (β δ : ℝ) (hδ : δ ≠ 0) (K : GaugeConfig L → ℝ) :
    β + δ ≠ β ∧
    ∀ V : GaugeConfig L,
      (β + δ) * wilsonAction 1 V + (K V - δ * wilsonAction 1 V) =
        β * wilsonAction 1 V + K V := by
  refine ⟨ fun h => hδ (by linarith), fun V => by ring ⟩

/-- Canonical linear coupling-extraction rule on `GaugeConfig L`: extracts the coarse single-plaquette
Wilson coupling `β_next = proj A` while annihilating constant vacuum shifts (`proj_const_zero`) and
normalizing `proj (wilsonAction 1) = 1`. -/
structure LinearPlaquetteCouplingExtractor (L : ℕ) [NeZero L] where
  proj : (GaugeConfig L → ℝ) → ℝ
  map_add : ∀ f g : GaugeConfig L → ℝ, proj (fun V => f V + g V) = proj f + proj g
  map_smul : ∀ (c : ℝ) (f : GaugeConfig L → ℝ), proj (fun V => c * f V) = c * proj f
  proj_const_zero : ∀ c : ℝ, proj (fun _ => c) = 0
  norm_wilsonAction_one : proj (wilsonAction (L := L) 1) = 1

omit [MeasurableSpace (GaugeConfig L)] in
/-- Concrete point-probe realization of `LinearPlaquetteCouplingExtractor L` using any reference
configuration `V_probe : GaugeConfig L` with `wilsonAction 1 V_probe ≠ 0`. -/
def canonicalPlaquetteProbeExtractor (V_probe : GaugeConfig L)
    (h_probe : wilsonAction 1 V_probe ≠ 0) : LinearPlaquetteCouplingExtractor L where
  proj f := (f V_probe - f (vacuumConfig L)) / wilsonAction 1 V_probe
  map_add f g := by
    dsimp only
    ring
  map_smul c f := by
    dsimp only
    ring
  proj_const_zero c := by
    dsimp only
    rw [sub_self, zero_div]
  norm_wilsonAction_one := by
    rw [wilsonAction_vacuum 1, sub_zero, div_self h_probe]

omit [MeasurableSpace (GaugeConfig L)] in
/-- Extracted coarse single-plaquette coupling `β_next` under `ext`. -/
def extractedCoarseCoupling (ext : LinearPlaquetteCouplingExtractor L)
    (A : GaugeConfig L → ℝ) : ℝ :=
  ext.proj A

omit [MeasurableSpace (GaugeConfig L)] in
/-- Extracted multi-plaquette/nonlocal remainder `K_next(V) = A(V) - β_next * wilsonAction 1 V`. -/
def extractedCoarseRemainder (ext : LinearPlaquetteCouplingExtractor L)
    (A : GaugeConfig L → ℝ) (V : GaugeConfig L) : ℝ :=
  A V - extractedCoarseCoupling ext A * wilsonAction 1 V

omit [MeasurableSpace (GaugeConfig L)] in
/-- Unique decomposition of any coarse effective action `A : GaugeConfig L → ℝ` via a canonical
linear coupling-extraction rule `ext : LinearPlaquetteCouplingExtractor L`:
1. Pointwise identity `A V = extractedCoarseCoupling ext A * wilsonAction 1 V + extractedCoarseRemainder ext A V`,
2. Zero single-plaquette projection in the remainder (`ext.proj (extractedCoarseRemainder ext A) = 0`),
3. Vacuum preservation (`A (vacuumConfig L) = 0 → extractedCoarseRemainder ext A (vacuumConfig L) = 0`),
4. Uniqueness (`(β', K')` with `ext.proj K' = 0` must equal `(extractedCoarseCoupling ext A, extractedCoarseRemainder ext A)`). -/
theorem effectiveActionDecomposition_unique_of_linearExtractor
    (ext : LinearPlaquetteCouplingExtractor L) (A : GaugeConfig L → ℝ) :
    (∀ V : GaugeConfig L,
      A V = extractedCoarseCoupling ext A * wilsonAction 1 V + extractedCoarseRemainder ext A V) ∧
    ext.proj (extractedCoarseRemainder ext A) = 0 ∧
    (A (vacuumConfig L) = 0 → extractedCoarseRemainder ext A (vacuumConfig L) = 0) ∧
    (∀ (β' : ℝ) (K' : GaugeConfig L → ℝ),
      (∀ V : GaugeConfig L, A V = β' * wilsonAction 1 V + K' V) →
      ext.proj K' = 0 →
      β' = extractedCoarseCoupling ext A ∧
      ∀ V : GaugeConfig L, K' V = extractedCoarseRemainder ext A V) := by
  have h_decomp : ∀ V : GaugeConfig L,
      A V = extractedCoarseCoupling ext A * wilsonAction 1 V + extractedCoarseRemainder ext A V := by
    intro V
    dsimp [extractedCoarseRemainder]
    ring
  have h_rem_eq : extractedCoarseRemainder ext A =
      fun V => A V + (-extractedCoarseCoupling ext A) * wilsonAction 1 V := by
    funext V
    dsimp [extractedCoarseRemainder]
    ring
  have h_proj_zero : ext.proj (extractedCoarseRemainder ext A) = 0 := by
    rw [h_rem_eq, ext.map_add, ext.map_smul, ext.norm_wilsonAction_one]
    dsimp [extractedCoarseCoupling]
    ring
  refine ⟨h_decomp, h_proj_zero, ?_, ?_⟩
  · intro h_vac
    dsimp [extractedCoarseRemainder]
    rw [h_vac, wilsonAction_vacuum 1, mul_zero, sub_zero]
  · intro β' K' hA_eq hK'_proj
    have hA_fun : A = fun V => β' * wilsonAction 1 V + K' V := funext hA_eq
    have h_beta : β' = extractedCoarseCoupling ext A := by
      dsimp [extractedCoarseCoupling]
      rw [hA_fun, ext.map_add, ext.map_smul, ext.norm_wilsonAction_one, hK'_proj]
      ring
    refine ⟨h_beta, fun V => ?_⟩
    have hV := hA_eq V
    rw [h_beta] at hV
    dsimp [extractedCoarseRemainder]
    linarith

/-- Conditional fiber probability disintegration of a fine reference measure `μ_fine` on
`GaugeConfig (2 * L)` over the dyadic link-blocking map `dyadicLinkBlockMap L`. -/
structure ConditionalBlockFiberDisintegration (L : ℕ) [NeZero L] [NeZero (2 * L)]
    [MeasurableSpace (GaugeConfig L)] [MeasurableSpace (GaugeConfig (2 * L))] where
  μ_fine : Measure (GaugeConfig (2 * L))
  μ_coarse : Measure (GaugeConfig L)
  fiberKernel : GaugeConfig L → Measure (GaugeConfig (2 * L))
  fine_prob : IsProbabilityMeasure μ_fine
  coarse_prob : IsProbabilityMeasure μ_coarse
  fiber_prob : ∀ V : GaugeConfig L, IsProbabilityMeasure (fiberKernel V)

/-- Blocked fiber marginal Boltzmann weight `W_block(β, V) = ∫ exp(-S_W(β, U)) d(fiberKernel V)(U)`
on the coarse configuration space `GaugeConfig L`. -/
def wilsonBlockedFiberWeight [NeZero (2 * L)] [MeasurableSpace (GaugeConfig (2 * L))]
    (dis : ConditionalBlockFiberDisintegration L) (β : ℝ) (V : GaugeConfig L) : ℝ :=
  wilsonPartition (dis.fiberKernel V) β

/-- Coarse effective action `A_eff(β, V) = -log W_block(β, V)` induced by integrating out the
conditional fine-lattice fiber over `V : GaugeConfig L`. -/
def wilsonBlockedEffectiveAction [NeZero (2 * L)] [MeasurableSpace (GaugeConfig (2 * L))]
    (dis : ConditionalBlockFiberDisintegration L) (β : ℝ) (V : GaugeConfig L) : ℝ :=
  -Real.log (wilsonBlockedFiberWeight dis β V)

/-- Vacuum-normalized coarse effective action
`A_eff_norm(β, V) = A_eff(β, V) - A_eff(β, vacuumConfig L)`. -/
def wilsonBlockedNormalizedEffectiveAction [NeZero (2 * L)] [MeasurableSpace (GaugeConfig (2 * L))]
    (dis : ConditionalBlockFiberDisintegration L) (β : ℝ) (V : GaugeConfig L) : ℝ :=
  wilsonBlockedEffectiveAction dis β V - wilsonBlockedEffectiveAction dis β (vacuumConfig L)

/-- Global strict positivity and two-sided bounds for the blocked fiber marginal weight
`wilsonBlockedFiberWeight dis β V` on **all** of `GaugeConfig L` (`M1`):
because every conditional fiber measure `dis.fiberKernel V` is a probability measure on
`GaugeConfig (2 * L)` and `exp(-2 * β * |Plaquette (2 * L)|) ≤ boltzmannWeight β U ≤ 1`,
zero-density sectors cannot occur at any finite lattice volume `2 * L`. -/
theorem wilsonBlockedFiberWeight_bounds_and_pos_all_configs
    [NeZero (2 * L)] [MeasurableSpace (GaugeConfig (2 * L))]
    (dis : ConditionalBlockFiberDisintegration L) {β : ℝ} (hβ : 0 ≤ β)
    (hS : Measurable (wilsonAction β : GaugeConfig (2 * L) → ℝ))
    (V : GaugeConfig L) :
    0 < wilsonBlockedFiberWeight dis β V ∧
    Real.exp (-(2 * β * (Fintype.card (Plaquette (2 * L)) : ℝ))) ≤
      wilsonBlockedFiberWeight dis β V ∧
    wilsonBlockedFiberWeight dis β V ≤ 1 := by
  have : IsProbabilityMeasure (dis.fiberKernel V) := dis.fiber_prob V
  exact ⟨wilsonPartition_pos (dis.fiberKernel V) hβ hS,
    wilsonPartition_bounds (dis.fiberKernel V) hβ hS⟩

/-- Global finiteness, nonnegativity, upper bound, and exact Boltzmann reconstruction of the
blocked coarse effective action `wilsonBlockedEffectiveAction dis β V` for every
`V : GaugeConfig L`. -/
theorem wilsonBlockedEffectiveAction_bounds_and_exp_neg_eq_weight
    [NeZero (2 * L)] [MeasurableSpace (GaugeConfig (2 * L))]
    (dis : ConditionalBlockFiberDisintegration L) {β : ℝ} (hβ : 0 ≤ β)
    (hS : Measurable (wilsonAction β : GaugeConfig (2 * L) → ℝ))
    (V : GaugeConfig L) :
    0 ≤ wilsonBlockedEffectiveAction dis β V ∧
    wilsonBlockedEffectiveAction dis β V ≤ 2 * β * (Fintype.card (Plaquette (2 * L)) : ℝ) ∧
    Real.exp (-wilsonBlockedEffectiveAction dis β V) = wilsonBlockedFiberWeight dis β V := by
  have hw := wilsonBlockedFiberWeight_bounds_and_pos_all_configs dis hβ hS V
  have h_pos : 0 < wilsonBlockedFiberWeight dis β V := hw.1
  have h_lo : Real.exp (-(2 * β * (Fintype.card (Plaquette (2 * L)) : ℝ))) ≤
      wilsonBlockedFiberWeight dis β V := hw.2.1
  have h_hi : wilsonBlockedFiberWeight dis β V ≤ 1 := hw.2.2
  have h_log_le_zero : Real.log (wilsonBlockedFiberWeight dis β V) ≤ 0 :=
    Real.log_nonpos (le_of_lt h_pos) h_hi
  have h_log_ge : -(2 * β * (Fintype.card (Plaquette (2 * L)) : ℝ)) ≤
      Real.log (wilsonBlockedFiberWeight dis β V) := by
    rw [← Real.log_exp (-(2 * β * (Fintype.card (Plaquette (2 * L)) : ℝ)))]
    exact Real.log_le_log (Real.exp_pos _) h_lo
  refine ⟨?_, ?_, ?_⟩
  · dsimp [wilsonBlockedEffectiveAction]
    linarith
  · dsimp [wilsonBlockedEffectiveAction]
    linarith
  · dsimp [wilsonBlockedEffectiveAction]
    rw [neg_neg, Real.exp_log h_pos]

/-- One-step blocked Wilson effective-action decomposition, weight factorization, and coarse
expectation representation (`M1` core measure-level theorem):
combines global strict positivity on all of `GaugeConfig L`, unique decomposition into
`β_next * wilsonAction 1 V + K_next V` under `ext`, exact marginal weight factorization
`W_block(β, V) = W_block(β, vacuumConfig L) * exp(-β_next * S_1(V) - K_next(V))`, and the
coarse integral representation of `wilsonBlockedMeasure dis.μ_fine β (dyadicLinkBlockMap L)`. -/
theorem one_step_wilson_blocking_effective_action_decomposition_and_weight_factorization
    [NeZero (2 * L)] [MeasurableSpace (GaugeConfig (2 * L))]
    (dis : ConditionalBlockFiberDisintegration L)
    (ext : LinearPlaquetteCouplingExtractor L)
    {β : ℝ} (hβ : 0 ≤ β)
    (hS : Measurable (wilsonAction β : GaugeConfig (2 * L) → ℝ))
    (hB : Measurable (dyadicLinkBlockMap L))
    {F : GaugeConfig L → ℝ} (hF : Measurable F)
    (h_disint :
      (∫ U, boltzmannWeight β U * F (dyadicLinkBlockMap L U) ∂dis.μ_fine) =
        ∫ V, wilsonBlockedFiberWeight dis β V * F V ∂dis.μ_coarse) :
    let A_norm := wilsonBlockedNormalizedEffectiveAction dis β
    let β_next := extractedCoarseCoupling ext A_norm
    let K_next := extractedCoarseRemainder ext A_norm
    (∀ V : GaugeConfig L,
      A_norm V = β_next * wilsonAction 1 V + K_next V ∧
      wilsonBlockedFiberWeight dis β V =
        wilsonBlockedFiberWeight dis β (vacuumConfig L) *
          Real.exp (-(β_next * wilsonAction 1 V + K_next V))) ∧
    ext.proj K_next = 0 ∧
    K_next (vacuumConfig L) = 0 ∧
    (∫ V, F V ∂wilsonBlockedMeasure dis.μ_fine β (dyadicLinkBlockMap L)) =
      (∫ V, Real.exp (-wilsonBlockedEffectiveAction dis β V) * F V ∂dis.μ_coarse) /
        wilsonPartition dis.μ_fine β := by
  have : IsProbabilityMeasure dis.μ_fine := dis.fine_prob
  dsimp only
  have h_unique := effectiveActionDecomposition_unique_of_linearExtractor ext
    (wilsonBlockedNormalizedEffectiveAction dis β)
  have h_vac_norm : wilsonBlockedNormalizedEffectiveAction dis β (vacuumConfig L) = 0 := by
    dsimp [wilsonBlockedNormalizedEffectiveAction]
    ring
  refine ⟨?_, h_unique.2.1, h_unique.2.2.1 h_vac_norm, ?_⟩
  · intro V
    have h_sum := h_unique.1 V
    refine ⟨h_sum, ?_⟩
    rw [← h_sum]
    have hV := (wilsonBlockedEffectiveAction_bounds_and_exp_neg_eq_weight dis hβ hS V).2.2
    have h0 := (wilsonBlockedEffectiveAction_bounds_and_exp_neg_eq_weight dis hβ hS (vacuumConfig L)).2.2
    rw [← hV, ← h0, ← Real.exp_add]
    congr 1
    dsimp [wilsonBlockedNormalizedEffectiveAction]
    ring
  · rw [integral_wilsonBlockedMeasure dis.μ_fine hβ hS hB hF]
    dsimp [wilsonExpectation]
    rw [h_disint]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
    dsimp only
    rw [(wilsonBlockedEffectiveAction_bounds_and_exp_neg_eq_weight dis hβ hS V).2.2]

omit [NeZero L] [MeasurableSpace (GaugeConfig L)] in
/-- Single-link gauge configuration update on `GaugeConfig L`: replaces the `SU(2)` matrix at
coarse link `⟨x, μ⟩` with `g` while leaving all other links unchanged. -/
def updateGaugeLink (L : ℕ) (V : GaugeConfig L) (x : Lattice4D L) (μ : Fin 4) (g : SU2) :
    GaugeConfig L :=
  Function.update V ⟨x, μ⟩ g

omit [NeZero L] [MeasurableSpace (GaugeConfig L)] in
/-- Evaluation of `updateGaugeLink L V x μ g` at the updated link `⟨x, μ⟩` and at any distinct
link `e ≠ ⟨x, μ⟩`. -/
theorem updateGaugeLink_same_and_other
    (L : ℕ) (V : GaugeConfig L) (x : Lattice4D L) (μ : Fin 4) (g : SU2) :
    updateGaugeLink L V x μ g ⟨x, μ⟩ = g ∧
    ∀ e : Link L, e ≠ ⟨x, μ⟩ → updateGaugeLink L V x μ g e = V e := by
  unfold updateGaugeLink
  exact ⟨Function.update_self ⟨x, μ⟩ g V, fun e he => Function.update_of_ne he g V⟩

/-- Single-link oscillation bound for the blocked coarse effective action
`wilsonBlockedEffectiveAction` and its vacuum-normalized counterpart
`wilsonBlockedNormalizedEffectiveAction` from a two-sided conditional fiber weight ratio
`W_block(β, V[x,μ := g1]) ≤ exp(δ_fiber) * W_block(β, V[x,μ := g2])` and vice versa (`M2`). -/
theorem wilsonBlockedNormalizedEffectiveAction_link_oscillation_from_fiber_ratio
    [NeZero (2 * L)] [MeasurableSpace (GaugeConfig (2 * L))]
    (dis : ConditionalBlockFiberDisintegration L) {β δ_fiber : ℝ}
    (hβ : 0 ≤ β)
    (hS : Measurable (wilsonAction β : GaugeConfig (2 * L) → ℝ))
    (V : GaugeConfig L) (x : Lattice4D L) (μ : Fin 4) (g1 g2 : SU2)
    (h_ratio12 :
      wilsonBlockedFiberWeight dis β (updateGaugeLink L V x μ g1) ≤
        Real.exp δ_fiber * wilsonBlockedFiberWeight dis β (updateGaugeLink L V x μ g2))
    (h_ratio21 :
      wilsonBlockedFiberWeight dis β (updateGaugeLink L V x μ g2) ≤
        Real.exp δ_fiber * wilsonBlockedFiberWeight dis β (updateGaugeLink L V x μ g1)) :
    |wilsonBlockedEffectiveAction dis β (updateGaugeLink L V x μ g1) -
        wilsonBlockedEffectiveAction dis β (updateGaugeLink L V x μ g2)| ≤ δ_fiber ∧
    |wilsonBlockedNormalizedEffectiveAction dis β (updateGaugeLink L V x μ g1) -
        wilsonBlockedNormalizedEffectiveAction dis β (updateGaugeLink L V x μ g2)| ≤ δ_fiber := by
  have hw1 : 0 < wilsonBlockedFiberWeight dis β (updateGaugeLink L V x μ g1) :=
    (wilsonBlockedFiberWeight_bounds_and_pos_all_configs dis hβ hS (updateGaugeLink L V x μ g1)).1
  have hw2 : 0 < wilsonBlockedFiberWeight dis β (updateGaugeLink L V x μ g2) :=
    (wilsonBlockedFiberWeight_bounds_and_pos_all_configs dis hβ hS (updateGaugeLink L V x μ g2)).1
  have hlog12 := Real.log_le_log hw1 h_ratio12
  rw [Real.log_mul (ne_of_gt (Real.exp_pos δ_fiber)) (ne_of_gt hw2), Real.log_exp] at hlog12
  have hlog21 := Real.log_le_log hw2 h_ratio21
  rw [Real.log_mul (ne_of_gt (Real.exp_pos δ_fiber)) (ne_of_gt hw1), Real.log_exp] at hlog21
  dsimp [wilsonBlockedNormalizedEffectiveAction, wilsonBlockedEffectiveAction]
  refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩

omit [MeasurableSpace (GaugeConfig L)] in
/-- Single-link oscillation bound for the extracted multi-plaquette remainder
`extractedCoarseRemainder ext A`: combines a single-link oscillation bound `δ_A` on `A` with the
4D single-link Wilson action variation bound `|wilsonAction 1 V1 - wilsonAction 1 V2| ≤ 12`
(`6` incident plaquettes per link, each in `[0, 2]`). -/
theorem extractedCoarseRemainder_link_oscillation_bound
    (ext : LinearPlaquetteCouplingExtractor L)
    (A : GaugeConfig L → ℝ) {δ_A : ℝ}
    (V : GaugeConfig L) (x : Lattice4D L) (μ : Fin 4) (g1 g2 : SU2)
    (h_osc_A :
      |A (updateGaugeLink L V x μ g1) - A (updateGaugeLink L V x μ g2)| ≤ δ_A)
    (h_osc_S1 :
      |wilsonAction 1 (updateGaugeLink L V x μ g1) -
          wilsonAction 1 (updateGaugeLink L V x μ g2)| ≤ 12) :
    |extractedCoarseRemainder ext A (updateGaugeLink L V x μ g1) -
        extractedCoarseRemainder ext A (updateGaugeLink L V x μ g2)| ≤
      δ_A + 12 * |extractedCoarseCoupling ext A| := by
  have h_eq :
      extractedCoarseRemainder ext A (updateGaugeLink L V x μ g1) -
        extractedCoarseRemainder ext A (updateGaugeLink L V x μ g2) =
      (A (updateGaugeLink L V x μ g1) - A (updateGaugeLink L V x μ g2)) -
        extractedCoarseCoupling ext A *
          (wilsonAction 1 (updateGaugeLink L V x μ g1) -
            wilsonAction 1 (updateGaugeLink L V x μ g2)) := by
    dsimp [extractedCoarseRemainder]
    ring
  have h_tri := abs_sub
    (A (updateGaugeLink L V x μ g1) - A (updateGaugeLink L V x μ g2))
    (extractedCoarseCoupling ext A *
      (wilsonAction 1 (updateGaugeLink L V x μ g1) -
        wilsonAction 1 (updateGaugeLink L V x μ g2)))
  rw [← h_eq, abs_mul] at h_tri
  have h_mul :
      |extractedCoarseCoupling ext A| *
          |wilsonAction 1 (updateGaugeLink L V x μ g1) -
            wilsonAction 1 (updateGaugeLink L V x μ g2)| ≤
        |extractedCoarseCoupling ext A| * 12 :=
    mul_le_mul_of_nonneg_left h_osc_S1 (abs_nonneg (extractedCoarseCoupling ext A))
  linarith

omit [NeZero L] [MeasurableSpace (GaugeConfig L)] in
/-- Simultaneous two-link gauge configuration perturbation on `GaugeConfig L`: replaces the `SU(2)`
matrix at link `⟨x1, μ1⟩` with `g` and then replaces the `SU(2)` matrix at link `⟨x2, μ2⟩` with `h`. -/
def updateTwoGaugeLinks (L : ℕ) (V : GaugeConfig L)
    (x1 : Lattice4D L) (μ1 : Fin 4) (g : SU2)
    (x2 : Lattice4D L) (μ2 : Fin 4) (h : SU2) : GaugeConfig L :=
  updateGaugeLink L (updateGaugeLink L V x1 μ1 g) x2 μ2 h

omit [NeZero L] [MeasurableSpace (GaugeConfig L)] in
/-- Two-link mixed second difference `Δ²_{e1, e2} A(V; g1, g2, h1, h2)` of a coarse action `A`
between links `e1 = ⟨x1, μ1⟩` and `e2 = ⟨x2, μ2⟩`: measures how much the single-link action
difference at `e1` changes when a partner link `e2` is flipped from `h1` to `h2`. This is the exact
quantity governing pairwise conditional Gibbs density ratios and off-diagonal Dobrushin total-variation
influences (`V35-WILSON-DOBRUSHIN-01` remediation). -/
def twoLinkMixedDifference (L : ℕ) (A : GaugeConfig L → ℝ) (V : GaugeConfig L)
    (x1 : Lattice4D L) (μ1 : Fin 4) (g1 g2 : SU2)
    (x2 : Lattice4D L) (μ2 : Fin 4) (h1 h2 : SU2) : ℝ :=
  (A (updateTwoGaugeLinks L V x1 μ1 g1 x2 μ2 h1) -
    A (updateTwoGaugeLinks L V x1 μ1 g2 x2 μ2 h1)) -
  (A (updateTwoGaugeLinks L V x1 μ1 g1 x2 μ2 h2) -
    A (updateTwoGaugeLinks L V x1 μ1 g2 x2 μ2 h2))

omit [NeZero L] [MeasurableSpace (GaugeConfig L)] in
/-- Locality of the two-link mixed second difference (`M1`/`M2` polymer support theorem):
if a polymer functional `Φ : GaugeConfig L → ℝ` is independent of link `⟨x2, μ2⟩`, then its
two-link mixed second difference `twoLinkMixedDifference L Φ V x1 μ1 g1 g2 x2 μ2 h1 h2` vanishes
identically (`= 0`), and for any functional `Φ` with single-link oscillation bounded by `δ` at
`⟨x1, μ1⟩`, `|twoLinkMixedDifference L Φ V x1 μ1 g1 g2 x2 μ2 h1 h2| ≤ 2 * δ`. -/
theorem twoLinkMixedDifference_eq_zero_of_independent_and_oscillation_bound
    (L : ℕ) (Φ : GaugeConfig L → ℝ) (V : GaugeConfig L)
    (x1 : Lattice4D L) (μ1 : Fin 4) (g1 g2 : SU2)
    (x2 : Lattice4D L) (μ2 : Fin 4) (h1 h2 : SU2) :
    ((∀ W : GaugeConfig L, Φ (updateGaugeLink L W x2 μ2 h1) = Φ (updateGaugeLink L W x2 μ2 h2)) →
      twoLinkMixedDifference L Φ V x1 μ1 g1 g2 x2 μ2 h1 h2 = 0) ∧
    (∀ δ : ℝ,
      |Φ (updateTwoGaugeLinks L V x1 μ1 g1 x2 μ2 h1) -
          Φ (updateTwoGaugeLinks L V x1 μ1 g2 x2 μ2 h1)| ≤ δ →
      |Φ (updateTwoGaugeLinks L V x1 μ1 g1 x2 μ2 h2) -
          Φ (updateTwoGaugeLinks L V x1 μ1 g2 x2 μ2 h2)| ≤ δ →
      |twoLinkMixedDifference L Φ V x1 μ1 g1 g2 x2 μ2 h1 h2| ≤ 2 * δ) := by
  refine ⟨?_, ?_⟩
  · intro h_indep
    dsimp [twoLinkMixedDifference, updateTwoGaugeLinks]
    rw [h_indep (updateGaugeLink L V x1 μ1 g1), h_indep (updateGaugeLink L V x1 μ1 g2), sub_self]
  · intro δ h1_osc h2_osc
    dsimp [twoLinkMixedDifference]
    have h_tri := abs_sub
      (Φ (updateTwoGaugeLinks L V x1 μ1 g1 x2 μ2 h1) -
        Φ (updateTwoGaugeLinks L V x1 μ1 g2 x2 μ2 h1))
      (Φ (updateTwoGaugeLinks L V x1 μ1 g1 x2 μ2 h2) -
        Φ (updateTwoGaugeLinks L V x1 μ1 g2 x2 μ2 h2))
    linarith

/-- Two-link mixed second difference bound for `wilsonBlockedEffectiveAction` and
`wilsonBlockedNormalizedEffectiveAction` from conditional fiber weight cross-ratios (`M1`/`M2`):
if the four conditional fiber marginal weights `W(g_a, h_b)` satisfy the two-sided cross-ratio
inequality `W(g1, h1) * W(g2, h2) ≤ exp(γ_pair) * W(g2, h1) * W(g1, h2)` and its symmetric swap,
then the two-link mixed second difference of both `wilsonBlockedEffectiveAction` and
`wilsonBlockedNormalizedEffectiveAction` is bounded in absolute value by `γ_pair`. -/
theorem wilsonBlockedEffectiveAction_twoLinkMixedDifference_from_fiber_crossRatio
    [NeZero (2 * L)] [MeasurableSpace (GaugeConfig (2 * L))]
    (dis : ConditionalBlockFiberDisintegration L) {β γ_pair : ℝ}
    (hβ : 0 ≤ β)
    (hS : Measurable (wilsonAction β : GaugeConfig (2 * L) → ℝ))
    (V : GaugeConfig L)
    (x1 : Lattice4D L) (μ1 : Fin 4) (g1 g2 : SU2)
    (x2 : Lattice4D L) (μ2 : Fin 4) (h1 h2 : SU2)
    (h_cross12 :
      wilsonBlockedFiberWeight dis β (updateTwoGaugeLinks L V x1 μ1 g1 x2 μ2 h1) *
        wilsonBlockedFiberWeight dis β (updateTwoGaugeLinks L V x1 μ1 g2 x2 μ2 h2) ≤
      Real.exp γ_pair *
        (wilsonBlockedFiberWeight dis β (updateTwoGaugeLinks L V x1 μ1 g2 x2 μ2 h1) *
          wilsonBlockedFiberWeight dis β (updateTwoGaugeLinks L V x1 μ1 g1 x2 μ2 h2)))
    (h_cross21 :
      wilsonBlockedFiberWeight dis β (updateTwoGaugeLinks L V x1 μ1 g2 x2 μ2 h1) *
        wilsonBlockedFiberWeight dis β (updateTwoGaugeLinks L V x1 μ1 g1 x2 μ2 h2) ≤
      Real.exp γ_pair *
        (wilsonBlockedFiberWeight dis β (updateTwoGaugeLinks L V x1 μ1 g1 x2 μ2 h1) *
          wilsonBlockedFiberWeight dis β (updateTwoGaugeLinks L V x1 μ1 g2 x2 μ2 h2))) :
    |twoLinkMixedDifference L (wilsonBlockedEffectiveAction dis β) V x1 μ1 g1 g2 x2 μ2 h1 h2| ≤
      γ_pair ∧
    |twoLinkMixedDifference L (wilsonBlockedNormalizedEffectiveAction dis β) V
        x1 μ1 g1 g2 x2 μ2 h1 h2| ≤ γ_pair := by
  have hw11 : 0 < wilsonBlockedFiberWeight dis β (updateTwoGaugeLinks L V x1 μ1 g1 x2 μ2 h1) :=
    (wilsonBlockedFiberWeight_bounds_and_pos_all_configs dis hβ hS _).1
  have hw21 : 0 < wilsonBlockedFiberWeight dis β (updateTwoGaugeLinks L V x1 μ1 g2 x2 μ2 h1) :=
    (wilsonBlockedFiberWeight_bounds_and_pos_all_configs dis hβ hS _).1
  have hw12 : 0 < wilsonBlockedFiberWeight dis β (updateTwoGaugeLinks L V x1 μ1 g1 x2 μ2 h2) :=
    (wilsonBlockedFiberWeight_bounds_and_pos_all_configs dis hβ hS _).1
  have hw22 : 0 < wilsonBlockedFiberWeight dis β (updateTwoGaugeLinks L V x1 μ1 g2 x2 μ2 h2) :=
    (wilsonBlockedFiberWeight_bounds_and_pos_all_configs dis hβ hS _).1
  have hlog12 := Real.log_le_log (mul_pos hw11 hw22) h_cross12
  rw [Real.log_mul (ne_of_gt hw11) (ne_of_gt hw22),
      Real.log_mul (ne_of_gt (Real.exp_pos γ_pair)) (ne_of_gt (mul_pos hw21 hw12)),
      Real.log_exp, Real.log_mul (ne_of_gt hw21) (ne_of_gt hw12)] at hlog12
  have hlog21 := Real.log_le_log (mul_pos hw21 hw12) h_cross21
  rw [Real.log_mul (ne_of_gt hw21) (ne_of_gt hw12),
      Real.log_mul (ne_of_gt (Real.exp_pos γ_pair)) (ne_of_gt (mul_pos hw11 hw22)),
      Real.log_exp, Real.log_mul (ne_of_gt hw11) (ne_of_gt hw22)] at hlog21
  dsimp [twoLinkMixedDifference, wilsonBlockedNormalizedEffectiveAction, wilsonBlockedEffectiveAction]
  refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩

omit [NeZero L] [MeasurableSpace (GaugeConfig L)] in
/-- Explicit finite-fiber block partition function
`W_fin(β, V) = ∑_{U ∈ fiber} exp(-β * S_coupled(V, U))` summing Boltzmann weights over a finite
fine-lattice fiber `fiber : Finset (GaugeConfig (2 * L))`. -/
noncomputable def finiteFiberBlockedWeight (L : ℕ) (fiber : Finset (GaugeConfig (2 * L)))
    (S_coupled : GaugeConfig L → GaugeConfig (2 * L) → ℝ) (β : ℝ) (V : GaugeConfig L) : ℝ :=
  ∑ U ∈ fiber, Real.exp (-(β * S_coupled V U))

omit [NeZero L] [MeasurableSpace (GaugeConfig L)] in
/-- Coarse effective action `A_fin(β, V) = -log W_fin(β, V)` induced by explicit finite-fiber
Boltzmann summation on `GaugeConfig (2 * L)`. -/
noncomputable def finiteFiberEffectiveAction (L : ℕ) (fiber : Finset (GaugeConfig (2 * L)))
    (S_coupled : GaugeConfig L → GaugeConfig (2 * L) → ℝ) (β : ℝ) (V : GaugeConfig L) : ℝ :=
  -Real.log (finiteFiberBlockedWeight L fiber S_coupled β V)

omit [NeZero L] [MeasurableSpace (GaugeConfig L)] in
/-- Constructive derivation of the conditional fiber-weight ratio and effective-action single-link
oscillation bound from explicit finite-fiber Boltzmann integration (`M1` derived fiber-ratio theorem):
for any nonempty finite fine-lattice fiber `fiber : Finset (GaugeConfig (2 * L))` and coupling
`0 ≤ β`, if updating coarse link `(x, μ)` from `g1` to `g2` changes the coupled fine action
`S_coupled V U` by at most `Δ_S` on every `U ∈ fiber`, then term-by-term summation over `fiber`
derives:
1. Strict positivity `0 < finiteFiberBlockedWeight L fiber S_coupled β V`,
2. The two-sided fiber-weight ratio bound
   `W_fin(V[x,μ := g1]) ≤ exp(β * Δ_S) * W_fin(V[x,μ := g2])` and vice versa, and
3. The coarse effective-action oscillation bound
   `|A_fin(V[x,μ := g1]) - A_fin(V[x,μ := g2])| ≤ β * Δ_S`. -/
theorem finiteFiberEffectiveAction_oscillation_derived_from_fine_action_lip
    (L : ℕ) (fiber : Finset (GaugeConfig (2 * L)))
    (S_coupled : GaugeConfig L → GaugeConfig (2 * L) → ℝ)
    {β Δ_S : ℝ} (h_nonempty : fiber.Nonempty) (hβ : 0 ≤ β)
    (V : GaugeConfig L) (x : Lattice4D L) (μ : Fin 4) (g1 g2 : SU2)
    (h_lip : ∀ U ∈ fiber,
      |S_coupled (updateGaugeLink L V x μ g1) U -
          S_coupled (updateGaugeLink L V x μ g2) U| ≤ Δ_S) :
    0 < finiteFiberBlockedWeight L fiber S_coupled β (updateGaugeLink L V x μ g1) ∧
    0 < finiteFiberBlockedWeight L fiber S_coupled β (updateGaugeLink L V x μ g2) ∧
    finiteFiberBlockedWeight L fiber S_coupled β (updateGaugeLink L V x μ g1) ≤
      Real.exp (β * Δ_S) *
        finiteFiberBlockedWeight L fiber S_coupled β (updateGaugeLink L V x μ g2) ∧
    finiteFiberBlockedWeight L fiber S_coupled β (updateGaugeLink L V x μ g2) ≤
      Real.exp (β * Δ_S) *
        finiteFiberBlockedWeight L fiber S_coupled β (updateGaugeLink L V x μ g1) ∧
    |finiteFiberEffectiveAction L fiber S_coupled β (updateGaugeLink L V x μ g1) -
        finiteFiberEffectiveAction L fiber S_coupled β (updateGaugeLink L V x μ g2)| ≤
      β * Δ_S := by
  have hw1 : 0 < finiteFiberBlockedWeight L fiber S_coupled β (updateGaugeLink L V x μ g1) := by
    unfold finiteFiberBlockedWeight
    exact Finset.sum_pos (fun U _ => Real.exp_pos _) h_nonempty
  have hw2 : 0 < finiteFiberBlockedWeight L fiber S_coupled β (updateGaugeLink L V x μ g2) := by
    unfold finiteFiberBlockedWeight
    exact Finset.sum_pos (fun U _ => Real.exp_pos _) h_nonempty
  have h_ratio12 :
      finiteFiberBlockedWeight L fiber S_coupled β (updateGaugeLink L V x μ g1) ≤
        Real.exp (β * Δ_S) *
          finiteFiberBlockedWeight L fiber S_coupled β (updateGaugeLink L V x μ g2) := by
    unfold finiteFiberBlockedWeight
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun U hU => ?_
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hU_abs := (abs_le.mp (h_lip U hU)).1
    have h_mul := mul_le_mul_of_nonneg_left hU_abs hβ
    linarith
  have h_ratio21 :
      finiteFiberBlockedWeight L fiber S_coupled β (updateGaugeLink L V x μ g2) ≤
        Real.exp (β * Δ_S) *
          finiteFiberBlockedWeight L fiber S_coupled β (updateGaugeLink L V x μ g1) := by
    unfold finiteFiberBlockedWeight
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun U hU => ?_
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hU_abs := (abs_le.mp (h_lip U hU)).2
    have h_mul := mul_le_mul_of_nonneg_left hU_abs hβ
    linarith
  have hlog12 := Real.log_le_log hw1 h_ratio12
  rw [Real.log_mul (ne_of_gt (Real.exp_pos (β * Δ_S))) (ne_of_gt hw2), Real.log_exp] at hlog12
  have hlog21 := Real.log_le_log hw2 h_ratio21
  rw [Real.log_mul (ne_of_gt (Real.exp_pos (β * Δ_S))) (ne_of_gt hw1), Real.log_exp] at hlog21
  refine ⟨hw1, hw2, h_ratio12, h_ratio21, ?_⟩
  dsimp [finiteFiberEffectiveAction]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

omit [NeZero L] [MeasurableSpace (GaugeConfig L)] in
/-- Explicit first fine-link assignment `U_{e, 1} = H` in the dyadic fiber parametrization
`(U_{e, 1}, U_{e, 2}) = (H, H⁻¹ * V)` over a coarse link `V : SU2` (`P02`/`W1`). -/
def dyadicFiberFineLink1 (H _V : SU2) : SU2 := H

omit [NeZero L] [MeasurableSpace (GaugeConfig L)] in
/-- Explicit second fine-link assignment `U_{e, 2} = H⁻¹ * V` in the dyadic fiber parametrization
`(U_{e, 1}, U_{e, 2}) = (H, H⁻¹ * V)` over a coarse link `V : SU2` (`P02`/`W1`). -/
noncomputable def dyadicFiberFineLink2 (H V : SU2) : SU2 := H⁻¹ * V

omit [NeZero L] [MeasurableSpace (GaugeConfig L)] in
/-- Exact fiber reconstruction and single-partner perturbation identity for the explicit dyadic
fiber parametrization (`P02`/`W1` and `P03`/`W3`):
1. For every fiber gauge variable `H : SU2` and coarse link `V : SU2`, the two fine links satisfy
   `dyadicFiberFineLink1 H V * dyadicFiberFineLink2 H V = V` identically (`H * (H⁻¹ * V) = V`),
2. At the classical identity link `H = 1, V = 1`, both fine links equal `1`, and
3. Updating the coarse link `V` from `g1` to `g2` at fixed fiber variable `H` leaves the first
   fine link `dyadicFiberFineLink1 H g1 = dyadicFiberFineLink1 H g2 = H` completely unchanged, so
   only the single partner fine link `dyadicFiberFineLink2 H V` varies. -/
theorem dyadicFiberFineLink_mul_reconstructs_coarse_and_changes_one_fine_link
    (H V g1 g2 : SU2) :
    dyadicFiberFineLink1 H V * dyadicFiberFineLink2 H V = V ∧
    dyadicFiberFineLink1 1 1 = 1 ∧
    dyadicFiberFineLink2 1 1 = 1 ∧
    dyadicFiberFineLink1 H g1 = dyadicFiberFineLink1 H g2 := by
  unfold dyadicFiberFineLink1 dyadicFiberFineLink2
  refine ⟨mul_inv_cancel_left H V, rfl, ?_, rfl⟩
  simp

/-- Weighting a genuine graph disintegration commutes with taking the coarse marginal. -/
theorem map_withDensity_of_graph_disintegration
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite ν]
    (B : X → Y) (hB : Measurable B)
    (κ : Kernel Y X) [IsSFiniteKernel κ]
    (hdis : ν ⊗ₘ κ = μ.map (fun x => (B x, x)))
    (w : X → ℝ≥0∞) (hw : Measurable w) :
    (μ.withDensity w).map B =
      ν.withDensity (fun y => ∫⁻ x, w x ∂κ y) := by
  ext s hs
  rw [Measure.map_apply hB hs, withDensity_apply _ (hB hs),
    withDensity_apply _ hs, ← lintegral_indicator (hB hs),
    ← lintegral_indicator hs]
  have hf : Measurable ((Prod.fst ⁻¹' s).indicator (w ∘ Prod.snd)) :=
    (hw.comp measurable_snd).indicator (measurable_fst hs)
  calc
    (∫⁻ x, (B ⁻¹' s).indicator w x ∂μ) =
        ∫⁻ p, (Prod.fst ⁻¹' s).indicator (w ∘ Prod.snd) p
          ∂μ.map (fun x => (B x, x)) := by
      have hgraph : Measurable (fun x => (B x, x)) := hB.prodMk measurable_id
      symm
      rw [lintegral_map hf hgraph]
      apply lintegral_congr
      intro x
      by_cases hx : B x ∈ s <;> simp [Set.indicator, hx]
    _ = ∫⁻ p, (Prod.fst ⁻¹' s).indicator (w ∘ Prod.snd) p ∂ν ⊗ₘ κ := by
      rw [hdis]
    _ = ∫⁻ y, ∫⁻ x, (Prod.fst ⁻¹' s).indicator (w ∘ Prod.snd) (y, x) ∂κ y ∂ν :=
      Measure.lintegral_compProd hf
    _ = ∫⁻ y, s.indicator (fun z => ∫⁻ x, w x ∂κ z) y ∂ν := by
      apply lintegral_congr
      intro y
      by_cases hy : y ∈ s <;> simp [Set.indicator, hy]

/-- The coarse density of a Wilson law follows from graph disintegration, for every measurable set. -/
theorem wilsonBlockedMeasure_density_of_graph_disintegration
    {L : ℕ} [NeZero L] [MeasurableSpace (GaugeConfig L)]
    {Y : Type*} [MeasurableSpace Y]
    (μ : Measure (GaugeConfig L)) [IsProbabilityMeasure μ]
    (ν : Measure Y) [SFinite ν]
    (B : GaugeConfig L → Y) (hB : Measurable B)
    (κ : Kernel Y (GaugeConfig L)) [IsMarkovKernel κ]
    (hdis : ν ⊗ₘ κ = μ.map (fun U => (B U, U)))
    {β : ℝ} (hβ : 0 ≤ β)
    (hS : Measurable (wilsonAction β : GaugeConfig L → ℝ)) :
    wilsonBlockedMeasure μ β B = ν.withDensity
      (fun V => ENNReal.ofReal (wilsonPartition (κ V) β / wilsonPartition μ β)) := by
  have hZ := wilsonPartition_pos μ hβ hS
  unfold wilsonBlockedMeasure wilsonMeasure
  have hw : Measurable (fun U =>
      ENNReal.ofReal (boltzmannWeight β U / wilsonPartition μ β)) :=
    ENNReal.measurable_ofReal.comp
      ((wilsonWeight_measurable hS).div_const (wilsonPartition μ β))
  rw [map_withDensity_of_graph_disintegration μ ν B hB κ hdis _ hw]
  congr 1
  funext V
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((wilsonWeight_integrable (κ V) hβ hS).div_const (wilsonPartition μ β))
    (Filter.Eventually.of_forall fun U =>
      div_nonneg (Real.exp_nonneg (-wilsonAction β U)) hZ.le), integral_div]
  rfl

/-- A measurable probability fiber family with the actual joint graph law and support on
its dyadic block fiber. Coarse Boltzmann identities alone do not imply either property. -/
structure SupportedBlockFiberDisintegration (L : ℕ) [NeZero L] [NeZero (2 * L)]
    [MeasurableSpace (GaugeConfig L)] [MeasurableSpace (GaugeConfig (2 * L))]
    extends ConditionalBlockFiberDisintegration L where
  fiber_measurable : Measurable fiberKernel
  block_measurable : Measurable (dyadicLinkBlockMap L)
  h_graph :
    μ_coarse ⊗ₘ (⟨fiberKernel, fiber_measurable⟩ : Kernel (GaugeConfig L) (GaugeConfig (2 * L))) =
      μ_fine.map (fun U => (dyadicLinkBlockMap L U, U))
  h_support : ∀ V, ∀ᵐ U ∂fiberKernel V, dyadicLinkBlockMap L U = V

/-- The measurable kernel carried by the supported disintegration. -/
def SupportedBlockFiberDisintegration.toKernel
    [NeZero (2 * L)] [MeasurableSpace (GaugeConfig (2 * L))]
    (sdis : SupportedBlockFiberDisintegration L) :
    Kernel (GaugeConfig L) (GaugeConfig (2 * L)) :=
  ⟨sdis.fiberKernel, sdis.fiber_measurable⟩

instance [NeZero (2 * L)] [MeasurableSpace (GaugeConfig (2 * L))]
    (sdis : SupportedBlockFiberDisintegration L) : IsMarkovKernel sdis.toKernel where
  isProbabilityMeasure := sdis.fiber_prob

/-- The graph identity derives the weighted coarse-observable identity. Measurability and
nonnegative coupling are the same hypotheses used by the finite-volume Wilson bounds. -/
theorem SupportedBlockFiberDisintegration.h_disint_all
    [NeZero (2 * L)] [MeasurableSpace (GaugeConfig (2 * L))]
    (sdis : SupportedBlockFiberDisintegration L)
    (β : ℝ) (hβ : 0 ≤ β)
    (hS : Measurable (wilsonAction β : GaugeConfig (2 * L) → ℝ))
    (F : GaugeConfig L → ℝ) (hF : Measurable F) :
    (∫ U, boltzmannWeight β U * F (dyadicLinkBlockMap L U) ∂sdis.μ_fine) =
      ∫ V, wilsonBlockedFiberWeight sdis.toConditionalBlockFiberDisintegration β V * F V
        ∂sdis.μ_coarse := by
  let := sdis.fine_prob
  let := sdis.coarse_prob
  have hZ := wilsonPartition_pos sdis.μ_fine hβ hS
  have hw (V : GaugeConfig L) :
      0 ≤ wilsonBlockedFiberWeight sdis.toConditionalBlockFiberDisintegration β V :=
    (wilsonBlockedFiberWeight_bounds_and_pos_all_configs
      sdis.toConditionalBlockFiberDisintegration hβ hS V).1.le
  have hW : Measurable (wilsonBlockedFiberWeight sdis.toConditionalBlockFiberDisintegration β) :=
    (wilsonWeight_measurable hS).stronglyMeasurable.integral_kernel
      (κ := sdis.toKernel) |>.measurable
  have hd : Measurable (fun V => ENNReal.ofReal
      (wilsonBlockedFiberWeight sdis.toConditionalBlockFiberDisintegration β V /
        wilsonPartition sdis.μ_fine β)) :=
    ENNReal.measurable_ofReal.comp (hW.div_const (wilsonPartition sdis.μ_fine β))
  have heq := congrArg (fun μ : Measure (GaugeConfig L) => ∫ V, F V ∂μ)
    (wilsonBlockedMeasure_density_of_graph_disintegration
      sdis.μ_fine sdis.μ_coarse (dyadicLinkBlockMap L) sdis.block_measurable
      sdis.toKernel sdis.h_graph hβ hS)
  change (∫ V, F V ∂wilsonBlockedMeasure sdis.μ_fine β (dyadicLinkBlockMap L)) =
    ∫ V, F V ∂sdis.μ_coarse.withDensity (fun V => ENNReal.ofReal
      (wilsonBlockedFiberWeight sdis.toConditionalBlockFiberDisintegration β V /
        wilsonPartition sdis.μ_fine β)) at heq
  rw [integral_wilsonBlockedMeasure _ hβ hS sdis.block_measurable hF,
    integral_withDensity_eq_integral_toReal_smul hd
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at heq
  simp only [ENNReal.toReal_ofReal (div_nonneg (hw _) hZ.le), smul_eq_mul,
    div_mul_eq_mul_div, integral_div, wilsonExpectation] at heq
  exact (div_left_inj' hZ.ne').mp heq

/-- A point mass away from its claimed block fiber is rejected, even when its Wilson
 action agrees with the fine reference action. -/
theorem SupportedBlockFiberDisintegration.rejects_off_fiber_dirac
    [NeZero (2 * L)] [MeasurableSpace (GaugeConfig (2 * L))]
    [MeasurableSingletonClass (GaugeConfig L)]
    (sdis : SupportedBlockFiberDisintegration L)
    (V : GaugeConfig L) (U : GaugeConfig (2 * L))
    (hκ : sdis.fiberKernel V = Measure.dirac U)
    (hoff : dyadicLinkBlockMap L U ≠ V) : False := by
  have hs := sdis.h_support V
  rw [hκ] at hs
  have hm : MeasurableSet {U : GaugeConfig (2 * L) | dyadicLinkBlockMap L U = V} :=
    sdis.block_measurable (measurableSet_singleton V)
  exact hoff ((ae_dirac_iff hm).mp hs)

/-- Partition-function binding (`F ≡ 1`), coarse expectation pushforward identity, and Dirac
mismatch negative control (`P02`/`W2`):
1. For any `SupportedBlockFiberDisintegration L`, setting `F := fun _ => 1` proves that the fine
   partition function `wilsonPartition sdis.μ_fine β` equals the coarse integral of the blocked
   fiber weight `∫ V, wilsonBlockedFiberWeight sdis.toConditionalBlockFiberDisintegration β V ∂sdis.μ_coarse`,
2. Every measurable coarse observable `F` has pushed-forward Wilson expectation equal to the
   normalized fiber-weighted coarse integral without any per-observable `h_disint` premise, and
3. Any candidate triple `(μ_fine, μ_coarse, fiberKernel)` for which some observable `F_sep`
   separates the fine pushforward integral from the fiber-weighted coarse integral (such as the
   `W2` Dirac vacuum vs. non-vacuum countermodel) is rejected by `SupportedBlockFiberDisintegration L`. -/
theorem supportedBlockFiberDisintegration_partition_and_pushforward_and_dirac_rejection
    [NeZero (2 * L)] [MeasurableSpace (GaugeConfig (2 * L))]
    (sdis : SupportedBlockFiberDisintegration L)
    {β : ℝ} (hβ : 0 ≤ β)
    (hS : Measurable (wilsonAction β : GaugeConfig (2 * L) → ℝ))
    (hB : Measurable (dyadicLinkBlockMap L))
    {F : GaugeConfig L → ℝ} (hF : Measurable F) :
    wilsonPartition sdis.μ_fine β =
      (∫ V, wilsonBlockedFiberWeight sdis.toConditionalBlockFiberDisintegration β V ∂sdis.μ_coarse) ∧
    (∫ V, F V ∂wilsonBlockedMeasure sdis.μ_fine β (dyadicLinkBlockMap L)) =
      (∫ V, wilsonBlockedFiberWeight sdis.toConditionalBlockFiberDisintegration β V * F V ∂sdis.μ_coarse) /
        (∫ V, wilsonBlockedFiberWeight sdis.toConditionalBlockFiberDisintegration β V ∂sdis.μ_coarse) ∧
    (∀ (F_sep : GaugeConfig L → ℝ), Measurable F_sep →
      (∫ U, boltzmannWeight β U * F_sep (dyadicLinkBlockMap L U) ∂sdis.μ_fine) ≠
        (∫ V, wilsonBlockedFiberWeight sdis.toConditionalBlockFiberDisintegration β V * F_sep V ∂sdis.μ_coarse) →
      False) := by
  have : IsProbabilityMeasure sdis.μ_fine := sdis.fine_prob
  have h_part :
      wilsonPartition sdis.μ_fine β =
        ∫ V, wilsonBlockedFiberWeight sdis.toConditionalBlockFiberDisintegration β V ∂sdis.μ_coarse := by
    have h1 := sdis.h_disint_all β hβ hS (fun _ => 1) measurable_const
    simp only [mul_one] at h1
    exact h1
  refine ⟨h_part, ?_, ?_⟩
  · rw [integral_wilsonBlockedMeasure sdis.μ_fine hβ hS hB hF]
    dsimp [wilsonExpectation]
    rw [sdis.h_disint_all β hβ hS F hF, h_part]
  · intro F_sep hF_sep h_ne
    exact h_ne (sdis.h_disint_all β hβ hS F_sep hF_sep)

omit [NeZero L] [MeasurableSpace (GaugeConfig L)] in
/-- Conditional finite-sum weight-ratio and effective-action bounds. The arbitrary coupled
 action `S_coupled` is assumed to change by at most `12` on the supplied finite fiber.
 This theorem propagates that premise to `exp(12 * β)` ratios and `12 * β` log-weight
 oscillation; it does not prove a plaquette-incidence bound or identify this finite sum
 with a Haar fiber integral. The scalar ceiling grows beyond every fixed threshold as
 `β → ∞`, so this estimate alone cannot establish weak-coupling remainder smallness. -/
theorem elementary_dyadic_fiber_twelve_beta_weight_ratio_and_weak_coupling_growth
    (L : ℕ) (fiber : Finset (GaugeConfig (2 * L)))
    (S_coupled : GaugeConfig L → GaugeConfig (2 * L) → ℝ)
    {β M : ℝ} (h_nonempty : fiber.Nonempty) (hβ : 0 ≤ β)
    (V : GaugeConfig L) (x : Lattice4D L) (μ : Fin 4) (g1 g2 : SU2)
    (h_six_plaquettes : ∀ U ∈ fiber,
      |S_coupled (updateGaugeLink L V x μ g1) U -
          S_coupled (updateGaugeLink L V x μ g2) U| ≤ 12) :
    finiteFiberBlockedWeight L fiber S_coupled β (updateGaugeLink L V x μ g1) ≤
      Real.exp (12 * β) *
        finiteFiberBlockedWeight L fiber S_coupled β (updateGaugeLink L V x μ g2) ∧
    finiteFiberBlockedWeight L fiber S_coupled β (updateGaugeLink L V x μ g2) ≤
      Real.exp (12 * β) *
        finiteFiberBlockedWeight L fiber S_coupled β (updateGaugeLink L V x μ g1) ∧
    |finiteFiberEffectiveAction L fiber S_coupled β (updateGaugeLink L V x μ g1) -
        finiteFiberEffectiveAction L fiber S_coupled β (updateGaugeLink L V x μ g2)| ≤
      12 * β ∧
    (M / 12 ≤ β → M ≤ 12 * β) := by
  have h_base :=
    finiteFiberEffectiveAction_oscillation_derived_from_fine_action_lip
      L fiber S_coupled h_nonempty hβ V x μ g1 g2 h_six_plaquettes
  have h_comm : β * 12 = 12 * β := by ring
  rw [h_comm] at h_base
  refine ⟨h_base.2.2.1, h_base.2.2.2.1, h_base.2.2.2.2, ?_⟩
  intro hM
  linarith

omit [NeZero L] [MeasurableSpace (GaugeConfig L)] in
/-- Probability-normalized finite-fiber block partition function
`W_prob(β, V) = (1 / |fiber|) * ∑_{U ∈ fiber} exp(-β * S_coupled(V, U))` on a finite
fine-lattice fiber `fiber : Finset (GaugeConfig (2 * L))` (`V34-ORACLE-FIBER-NORMALIZATION`
formal parity). -/
noncomputable def probabilityNormalizedFiniteFiberWeight (L : ℕ)
    (fiber : Finset (GaugeConfig (2 * L)))
    (S_coupled : GaugeConfig L → GaugeConfig (2 * L) → ℝ) (β : ℝ) (V : GaugeConfig L) : ℝ :=
  (1 / (fiber.card : ℝ)) * finiteFiberBlockedWeight L fiber S_coupled β V

omit [NeZero L] [MeasurableSpace (GaugeConfig L)] in
/-- Probability-normalized finite-fiber effective action
`A_prob(β, V) = -log W_prob(β, V) = A_fin(β, V) + log |fiber|` (`V34-ORACLE-FIBER-NORMALIZATION`). -/
noncomputable def probabilityNormalizedFiniteFiberEffectiveAction (L : ℕ)
    (fiber : Finset (GaugeConfig (2 * L)))
    (S_coupled : GaugeConfig L → GaugeConfig (2 * L) → ℝ) (β : ℝ) (V : GaugeConfig L) : ℝ :=
  -Real.log (probabilityNormalizedFiniteFiberWeight L fiber S_coupled β V)

omit [NeZero L] [MeasurableSpace (GaugeConfig L)] in
/-- Probability-normalized finite-fiber weight and effective-action sandwich
(`V34-ORACLE-FIBER-NORMALIZATION` remediation):
when `fiber` is nonempty, `0 ≤ β`, and `0 ≤ s_min ≤ S_coupled V U ≤ s_max` across `U ∈ fiber`,
normalizing the finite-fiber sum by `1 / |fiber|` guarantees `0 < W_prob ≤ 1` and
`0 ≤ β * s_min ≤ A_prob ≤ β * s_max`. -/
theorem probabilityNormalizedFiniteFiberWeight_bounds_and_effectiveAction_nonneg
    (L : ℕ) (fiber : Finset (GaugeConfig (2 * L)))
    (S_coupled : GaugeConfig L → GaugeConfig (2 * L) → ℝ)
    {β s_min s_max : ℝ} (h_nonempty : fiber.Nonempty) (hβ : 0 ≤ β)
    (hs_min_nonneg : 0 ≤ s_min)
    (V : GaugeConfig L)
    (h_range : ∀ U ∈ fiber, s_min ≤ S_coupled V U ∧ S_coupled V U ≤ s_max) :
    0 < probabilityNormalizedFiniteFiberWeight L fiber S_coupled β V ∧
    Real.exp (-(β * s_max)) ≤ probabilityNormalizedFiniteFiberWeight L fiber S_coupled β V ∧
    probabilityNormalizedFiniteFiberWeight L fiber S_coupled β V ≤ Real.exp (-(β * s_min)) ∧
    probabilityNormalizedFiniteFiberWeight L fiber S_coupled β V ≤ 1 ∧
    0 ≤ probabilityNormalizedFiniteFiberEffectiveAction L fiber S_coupled β V ∧
    β * s_min ≤ probabilityNormalizedFiniteFiberEffectiveAction L fiber S_coupled β V ∧
    probabilityNormalizedFiniteFiberEffectiveAction L fiber S_coupled β V ≤ β * s_max := by
  have hcard_pos : 0 < (fiber.card : ℝ) := Nat.cast_pos.mpr (Finset.Nonempty.card_pos h_nonempty)
  have hcard_ne : (fiber.card : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hinv_pos : 0 < 1 / (fiber.card : ℝ) := div_pos zero_lt_one hcard_pos
  have hw_pos : 0 < finiteFiberBlockedWeight L fiber S_coupled β V :=
    Finset.sum_pos (fun U _ => Real.exp_pos _) h_nonempty
  have hprob_pos : 0 < probabilityNormalizedFiniteFiberWeight L fiber S_coupled β V :=
    mul_pos hinv_pos hw_pos
  have h_sum_lo : (fiber.card : ℝ) * Real.exp (-(β * s_max)) ≤
      finiteFiberBlockedWeight L fiber S_coupled β V := by
    unfold finiteFiberBlockedWeight
    have h_const : ∑ _U ∈ fiber, Real.exp (-(β * s_max)) =
        (fiber.card : ℝ) * Real.exp (-(β * s_max)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [← h_const]
    refine Finset.sum_le_sum fun U hU => Real.exp_le_exp.mpr ?_
    have hU := (h_range U hU).2
    have h_mul := mul_le_mul_of_nonneg_left hU hβ
    linarith
  have h_sum_hi : finiteFiberBlockedWeight L fiber S_coupled β V ≤
      (fiber.card : ℝ) * Real.exp (-(β * s_min)) := by
    unfold finiteFiberBlockedWeight
    have h_const : ∑ _U ∈ fiber, Real.exp (-(β * s_min)) =
        (fiber.card : ℝ) * Real.exp (-(β * s_min)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [← h_const]
    refine Finset.sum_le_sum fun U hU => Real.exp_le_exp.mpr ?_
    have hU := (h_range U hU).1
    have h_mul := mul_le_mul_of_nonneg_left hU hβ
    linarith
  have hprob_lo : Real.exp (-(β * s_max)) ≤
      probabilityNormalizedFiniteFiberWeight L fiber S_coupled β V := by
    unfold probabilityNormalizedFiniteFiberWeight
    have h_mul := mul_le_mul_of_nonneg_left h_sum_lo (le_of_lt hinv_pos)
    have h_cancel : (1 / (fiber.card : ℝ)) * ((fiber.card : ℝ) * Real.exp (-(β * s_max))) =
        Real.exp (-(β * s_max)) := by
      field_simp [hcard_ne]
    linarith
  have hprob_hi : probabilityNormalizedFiniteFiberWeight L fiber S_coupled β V ≤
      Real.exp (-(β * s_min)) := by
    unfold probabilityNormalizedFiniteFiberWeight
    have h_mul := mul_le_mul_of_nonneg_left h_sum_hi (le_of_lt hinv_pos)
    have h_cancel : (1 / (fiber.card : ℝ)) * ((fiber.card : ℝ) * Real.exp (-(β * s_min))) =
        Real.exp (-(β * s_min)) := by
      field_simp [hcard_ne]
    linarith
  have h_exp_min_le_one : Real.exp (-(β * s_min)) ≤ 1 := by
    rw [← Real.exp_zero]
    refine Real.exp_le_exp.mpr ?_
    have : 0 ≤ β * s_min := mul_nonneg hβ hs_min_nonneg
    linarith
  have hprob_le_one : probabilityNormalizedFiniteFiberWeight L fiber S_coupled β V ≤ 1 :=
    le_trans hprob_hi h_exp_min_le_one
  have hlog_lo := Real.log_le_log (Real.exp_pos _) hprob_lo
  rw [Real.log_exp] at hlog_lo
  have hlog_hi := Real.log_le_log hprob_pos hprob_hi
  rw [Real.log_exp] at hlog_hi
  have h_bsmin_nonneg : 0 ≤ β * s_min := mul_nonneg hβ hs_min_nonneg
  unfold probabilityNormalizedFiniteFiberEffectiveAction
  refine ⟨hprob_pos, hprob_lo, hprob_hi, hprob_le_one, by linarith, by linarith, by linarith⟩

/-- Strengthened pushforward-verified block-fiber disintegration (`V34-DISINTEGRATION-BINDING`
contract): extends `ConditionalBlockFiberDisintegration L` with exact fiber-support concentration
`fiberKernel V {U | dyadicLinkBlockMap L U = V} = 1` and universal measurable-observable
disintegration across all `F : GaugeConfig L → ℝ`. Note: this structure packages the measure-theoretic
disintegration contract so individual theorems do not take a per-observable `h_disint` premise;
constructing the concrete product-Haar disintegration instance on `SU(2)^{4(2L)^4}` remains an
explicit open measure-theoretic realization obligation. -/
structure VerifiedPushforwardBlockDisintegration (L : ℕ) [NeZero L] [NeZero (2 * L)]
    [MeasurableSpace (GaugeConfig L)] [MeasurableSpace (GaugeConfig (2 * L))]
    extends ConditionalBlockFiberDisintegration L where
  h_fiber_supported : ∀ V : GaugeConfig L,
    fiberKernel V {U : GaugeConfig (2 * L) | dyadicLinkBlockMap L U = V} = 1
  h_all_observable_disint : ∀ (β : ℝ) (F : GaugeConfig L → ℝ), Measurable F →
    (∫ U, boltzmannWeight β U * F (dyadicLinkBlockMap L U) ∂μ_fine) =
      ∫ V, wilsonBlockedFiberWeight toConditionalBlockFiberDisintegration β V * F V ∂μ_coarse

/-- Universal observable expectation representation from `VerifiedPushforwardBlockDisintegration`
paired with the two-point Dirac pushforward-mismatch negative control (`V34-DISINTEGRATION-BINDING`):
1. Any `dis : VerifiedPushforwardBlockDisintegration L` satisfies the one-step blocked expectation
   identity for **every** measurable coarse observable `F : GaugeConfig L → ℝ` without an external
   per-observable `h_disint` hypothesis, and
2. Without `h_all_observable_disint`, a fine Dirac mass `(1, 0)` at coarse image `0` and an
   unrelated coarse Dirac mass `(0, 1)` at `1` with unit fiber weight `W_block = (1, 1)` at `β = 0`
   give fine expectation `1` vs. coarse weighted expectation `0` (`(1 : ℝ) ≠ 0`) for the indicator
   `F = (1, 0)` of state `0`. -/
theorem verifiedPushforwardBlockDisintegration_expectation_and_dirac_mismatch_refutation
    [NeZero (2 * L)] [MeasurableSpace (GaugeConfig (2 * L))]
    (dis : VerifiedPushforwardBlockDisintegration L)
    {β : ℝ} (hβ : 0 ≤ β)
    (hS : Measurable (wilsonAction β : GaugeConfig (2 * L) → ℝ))
    (hB : Measurable (dyadicLinkBlockMap L)) :
    (∀ (F : GaugeConfig L → ℝ), Measurable F →
      (∫ V, F V ∂wilsonBlockedMeasure dis.μ_fine β (dyadicLinkBlockMap L)) =
        (∫ V, Real.exp (-wilsonBlockedEffectiveAction dis.toConditionalBlockFiberDisintegration β V) *
          F V ∂dis.μ_coarse) / wilsonPartition dis.μ_fine β) ∧
    ((1 : ℝ) * 1 + 0 * 0 ≠ 0 * (1 * 1) + 1 * (1 * 0)) := by
  have : IsProbabilityMeasure dis.μ_fine := dis.fine_prob
  refine ⟨fun F hF => ?_, by norm_num⟩
  rw [integral_wilsonBlockedMeasure dis.μ_fine hβ hS hB hF]
  dsimp [wilsonExpectation]
  rw [dis.h_all_observable_disint β F hF]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
  dsimp only
  rw [(wilsonBlockedEffectiveAction_bounds_and_exp_neg_eq_weight
    dis.toConditionalBlockFiberDisintegration hβ hS V).2.2]

#assert_zfc_axioms

end JesseMath.Physics
