import JesseMath.Physics.YangMillsContinuumCompactness
import Mathlib.MeasureTheory.Measure.DiracProba

/-! Zero Wilson action and probability normalization do not select the vacuum Dirac law.
This is a control on the scope of the compactness conclusion, not a claim that either
Dirac law below is a weak limit of the finite-volume Wilson sequence. -/

noncomputable section
open MeasureTheory

namespace JesseMath.Physics.WilsonContinuumCompactnessNegativeControl

open YangMillsContinuumCompactness

def minusIdentity : SU2 where
  mat := -1
  unitary := by simp
  det_one := by norm_num [Matrix.det_fin_two]

theorem minusIdentity_ne_one : minusIdentity ≠ 1 := by
  intro h
  have hm := congrArg (fun U : SU2 => U.mat 0 0) h
  change (-1 : ℂ) = 1 at hm
  norm_num at hm

/-- A nonvacuum constant connection on the side-one torus, with trivial plaquettes. -/
def flatConfig : GaugeConfig 1 := fun _ => minusIdentity

theorem flatConfig_action_zero (β : ℝ) : wilsonAction β flatConfig = 0 := by
  have hp (p : Plaquette 1) : plaquetteHolonomy flatConfig p = 1 := by
    dsimp [plaquetteHolonomy, flatConfig]
    group
  have ha (p : Plaquette 1) : plaquetteAction flatConfig p = 0 := by
    simp [plaquetteAction, hp, SU2.trace_one]
  simp [wilsonAction, ha]

theorem flatConfig_ne_vacuum : flatConfig ≠ vacuumConfig 1 := by
  intro h
  exact minusIdentity_ne_one (congrFun h ⟨0, 0⟩)

def flatLaw : ProbabilityMeasure (GaugeConfig 1) := diracProba flatConfig

theorem flatLaw_action_zero :
    ∀ᵐ U ∂(flatLaw : Measure (GaugeConfig 1)), wilsonAction 1 U = 0 := by
  change ∀ᵐ U ∂Measure.dirac flatConfig, wilsonAction 1 U = 0
  rw [ae_dirac_eq]
  exact flatConfig_action_zero 1

theorem flatLaw_ne_vacuum : flatLaw ≠ diracProba (vacuumConfig 1) := by
  intro h
  exact flatConfig_ne_vacuum (injective_diracProba h)

/-- This failed stronger conclusion is excluded by an explicit normalized, flat witness. -/
theorem flat_probability_does_not_select_vacuum :
    ¬ (∀ ν : ProbabilityMeasure (GaugeConfig 1),
      (∀ᵐ U ∂(ν : Measure (GaugeConfig 1)), wilsonAction 1 U = 0) →
        ν = diracProba (vacuumConfig 1)) := by
  intro h
  exact flatLaw_ne_vacuum (h flatLaw flatLaw_action_zero)

/-- Positive control: the constructed actual law has unit normalization. -/
example (L : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β) :
    (∫ _ : GaugeConfig L, (1 : ℝ) ∂wilsonProbability L β hβ) = 1 := by
  rw [wilsonProbability_integral]
  exact wilsonExpectation_one _ hβ (measurable_wilsonAction β)

/-- The common-space cylinder is exactly the chosen finite-coordinate observable. -/
example {ι : Type*} [Fintype ι] (edges : ι → IntegerLink)
    (F : C((ι → SU2), ℝ)) (U : IntegerGaugeConfig) :
    cylinderObservable edges F U = F (fun i => U (edges i)) := rfl

/-- The actual finite law has local gauge symmetry with no supplied invariance premise. -/
example (L : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β) (g : GaugeTransformation L) :
    (wilsonProbability L β hβ).map (gaugeTransform g) = wilsonProbability L β hβ :=
  wilsonProbability_gauge_invariant L β hβ g

/-- Translation symmetry is proved for the actual normalized Wilson density. -/
example (L : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β) (a : Lattice4D L) :
    (wilsonProbability L β hβ).map (latticeTranslate a) = wilsonProbability L β hβ :=
  wilsonProbability_translation_invariant L β hβ a

/-- Symmetry inheritance requires convergence of the actual Wilson laws. -/
example (L : ℕ → ℕ) [∀ n, NeZero (L n)] (β : ℕ → ℝ) (hβ : ∀ n, 0 ≤ β n)
    (ν : ProbabilityMeasure IntegerGaugeConfig)
    (hν : Filter.Tendsto (fun n => periodicWilsonProbability (L n) (β n) (hβ n))
      Filter.atTop (nhds ν)) (a : Fin 4 → ℤ) : ν.map (integerTranslate a) = ν :=
  periodicWilsonProbability_limit_translation_invariant L β hβ ν hν a

/-- A single distinguished link on the same compact configuration space. -/
def defectConfig : IntegerGaugeConfig :=
  fun e => if e = (0, 0) then minusIdentity else 1

theorem translated_defectConfig_ne :
    integerTranslate (fun _ => 1) defectConfig ≠ defectConfig := by
  intro h
  have hv := congrFun h (0, 0)
  have ha : (fun _ : Fin 4 => (1 : ℤ)) ≠ 0 := by
    intro h'
    have hi := congrFun h' 0
    norm_num at hi
  have he : (1 : SU2) = minusIdentity := by
    simpa [integerTranslate, defectConfig, ha] using hv
  exact minusIdentity_ne_one he.symm

/-- Compactness and probability normalization alone cannot supply translation symmetry.
The actual-law hypothesis in the inheritance theorem is essential. -/
theorem compact_probability_does_not_imply_translation_invariance :
    ¬ (∀ ν : ProbabilityMeasure IntegerGaugeConfig, ∀ a : Fin 4 → ℤ,
      ν.map (integerTranslate a) = ν) := by
  intro h
  have hm := congrArg ProbabilityMeasure.toMeasure
    (h (diracProba defectConfig) (fun _ => 1))
  change (Measure.dirac defectConfig).map (integerTranslate (fun _ => 1)) =
    Measure.dirac defectConfig at hm
  rw [Measure.map_dirac' (continuous_integerTranslate _).measurable] at hm
  exact translated_defectConfig_ne (injective_dirac hm)

#assert_zfc_axioms

end JesseMath.Physics.WilsonContinuumCompactnessNegativeControl
