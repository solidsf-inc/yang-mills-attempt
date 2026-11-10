import JesseMath.Physics.YangMillsWilsonMeasureBridge
import JesseMath.Physics.YangMillsHaar

noncomputable section

open MeasureTheory ProbabilityTheory

namespace JesseMath.Physics.WilsonSupportedDisintegrationNegativeControl

/-- The nonidentity central element of SU(2). -/
def minusIdentity : SU2 where
  mat := -1
  unitary := by simp
  det_one := by norm_num [Matrix.det_fin_two]

theorem minusIdentity_ne_one : minusIdentity ≠ 1 := by
  intro h
  have hm := congrArg (fun U : SU2 => U.mat 0 0) h
  change (-1 : ℂ) = 1 at hm
  norm_num at hm

/-- A pure-gauge bump at the origin of the fine side-four torus. -/
def bumpGauge : GaugeTransformation 4 := by
  classical
  exact fun x => if x = 0 then minusIdentity else 1

def wrongFineConfig : GaugeConfig 4 :=
  gaugeTransform bumpGauge (vacuumConfig 4)

theorem wrongFineConfig_action_zero (β : ℝ) :
    wilsonAction β wrongFineConfig = 0 := by
  rw [wrongFineConfig, wilsonAction_gaugeTransform, wilsonAction_vacuum]

theorem wrongFineConfig_block_origin :
    dyadicLinkBlockMap 2 wrongFineConfig ⟨0, 0⟩ = minusIdentity := by
  have h1 : shift (0 : Lattice4D 4) 0 ≠ 0 := by decide
  have h2 : shift (shift (0 : Lattice4D 4) 0) 0 ≠ 0 := by decide
  change wrongFineConfig ⟨0, 0⟩ * wrongFineConfig ⟨shift 0 0, 0⟩ = minusIdentity
  simp [wrongFineConfig, gaugeTransform, bumpGauge, vacuumConfig, h1, h2]

theorem wrongFineConfig_off_fiber :
    dyadicLinkBlockMap 2 wrongFineConfig ≠ vacuumConfig 2 := by
  intro h
  have he := congrArg (fun U : GaugeConfig 2 => U ⟨0, 0⟩) h
  rw [wrongFineConfig_block_origin] at he
  exact minusIdentity_ne_one he

/-- These probability data passed the former coarse-observable-only contract. -/
def wrongData : ConditionalBlockFiberDisintegration 2 where
  μ_fine := Measure.dirac (vacuumConfig 4)
  μ_coarse := Measure.dirac (vacuumConfig 2)
  fiberKernel := fun _ => Measure.dirac wrongFineConfig
  fine_prob := inferInstance
  coarse_prob := inferInstance
  fiber_prob := fun _ => inferInstance

theorem wrongData_all_coarse_observable_identities (β : ℝ) (F : GaugeConfig 2 → ℝ) :
    (∫ U, boltzmannWeight β U * F (dyadicLinkBlockMap 2 U) ∂wrongData.μ_fine) =
      ∫ V, wilsonBlockedFiberWeight wrongData β V * F V ∂wrongData.μ_coarse := by
  simpa [wrongData, wilsonBlockedFiberWeight, wilsonPartition, boltzmannWeight,
    wilsonAction_vacuum, wrongFineConfig_action_zero] using
      congrArg F (dyadicLinkBlockMap_vacuum 2)

/-- The strengthened contract rejects the actual action-degenerate wrong fiber. -/
theorem wrongData_has_no_supported_extension :
    ¬ ∃ sdis : SupportedBlockFiberDisintegration 2,
      sdis.toConditionalBlockFiberDisintegration = wrongData := by
  rintro ⟨sdis, hs⟩
  have hκ : sdis.fiberKernel (vacuumConfig 2) = Measure.dirac wrongFineConfig := by
    have h := congrArg (fun d : ConditionalBlockFiberDisintegration 2 =>
      d.fiberKernel (vacuumConfig 2)) hs
    exact h
  exact sdis.rejects_off_fiber_dirac (vacuumConfig 2) wrongFineConfig hκ
    wrongFineConfig_off_fiber

#assert_zfc_axioms

end JesseMath.Physics.WilsonSupportedDisintegrationNegativeControl
