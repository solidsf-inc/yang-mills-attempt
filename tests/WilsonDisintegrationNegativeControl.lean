import JesseMath.Linter.AxiomAudit
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.Tactic.NormNum

/-!
Probability of both marginals and every fiber does not imply disintegration.
For the identity block map on Bool, the wrong coarse atom changes the first
coordinate of the reconstructed joint law. The singleton witness separates it
from the actual graph law exactly, without numerical approximation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace JesseMath.Tests.WilsonDisintegrationNegativeControl

def fineLaw : Measure Bool := Measure.dirac false

def wrongCoarseLaw : Measure Bool := Measure.dirac true

def fiber : Kernel Bool Bool := Kernel.const Bool (Measure.dirac false)

def graphLaw : Measure (Bool × Bool) :=
  fineLaw.map (fun u => (id u, u))

def wrongJointLaw : Measure (Bool × Bool) := wrongCoarseLaw ⊗ₘ fiber

theorem all_probability_fields :
    IsProbabilityMeasure fineLaw ∧ IsProbabilityMeasure wrongCoarseLaw ∧
      ∀ b : Bool, IsProbabilityMeasure (fiber b) := by
  constructor
  · unfold fineLaw
    infer_instance
  constructor
  · unfold wrongCoarseLaw
    infer_instance
  · intro b
    unfold fiber
    infer_instance

theorem fiber_is_markov : IsMarkovKernel fiber := by
  unfold fiber
  infer_instance

theorem graphLaw_eq : graphLaw = Measure.dirac (false, false) := by
  simp [graphLaw, fineLaw]

theorem wrongJointLaw_eq : wrongJointLaw = Measure.dirac (true, false) := by
  simp [wrongJointLaw, wrongCoarseLaw, fiber, Measure.dirac_prod_dirac]

theorem graphLaw_singleton : graphLaw {(false, false)} = 1 := by
  rw [graphLaw_eq]
  simp

theorem wrongJointLaw_singleton : wrongJointLaw {(false, false)} = 0 := by
  rw [wrongJointLaw_eq]
  simp

theorem probability_fields_do_not_imply_graph_identity : graphLaw ≠ wrongJointLaw := by
  intro h
  have hmass := congrArg (fun μ : Measure (Bool × Bool) => μ {(false, false)}) h
  rw [graphLaw_singleton, wrongJointLaw_singleton] at hmass
  exact one_ne_zero hmass

/-- Correcting the coarse marginal restores the graph identity for this fiber. -/
theorem correct_coarse_graph_identity : graphLaw = fineLaw ⊗ₘ fiber := by
  rw [graphLaw_eq]
  simp [fineLaw, fiber, Measure.dirac_prod_dirac]

end JesseMath.Tests.WilsonDisintegrationNegativeControl

#assert_zfc_axioms
