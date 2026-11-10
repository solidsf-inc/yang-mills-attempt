import JesseMath.Physics.YangMillsPhysicalGap
import JesseMath.Linter.AxiomAudit

noncomputable section
namespace JesseMath.Physics.YangMillsResolventTest
open JesseMath.Physics.YangMillsPhysicalGap
open scoped InnerProductSpace

def identityOperator : ℂ →ₗ.[ℂ] ℂ := (ContinuousLinearMap.id ℂ ℂ).toPMap ⊤

theorem identity_selfAdjoint : IsSelfAdjoint identityOperator := by
  rw [LinearPMap.isSelfAdjoint_def]
  unfold identityOperator
  rw [ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense _ (by simp)]
  rw [ContinuousLinearMap.adjoint_id]

theorem identity_coercive : ∀ u : identityOperator.domain,
    (1 : ℝ) * ‖(u : ℂ)‖ ^ 2 ≤ (⟪(u : ℂ), identityOperator u⟫_ℂ).re := by
  intro u
  change 1 * ‖(u : ℂ)‖ ^ 2 ≤ (⟪(u : ℂ), (u : ℂ)⟫_ℂ).re
  simpa only [one_mul, RCLike.re_to_complex] using
    (inner_self_eq_norm_sq (𝕜 := ℂ) (u : ℂ)).ge

theorem positive_identity_resolvent :
    ∃ R : ℂ →L[ℂ] ℂ,
      (∀ f : ℂ, ∃ hf : R f ∈ identityOperator.domain,
        identityOperator ⟨R f, hf⟩ - (0 : ℂ) • R f = f) ∧
      (∀ u : identityOperator.domain,
        R (identityOperator u - (0 : ℂ) • (u : ℂ)) = (u : ℂ)) ∧
      ‖R‖ ≤ 1 := by
  simpa using selfAdjoint_resolvent_below_coercive_bound
    identityOperator identity_selfAdjoint 1 0 (by norm_num) identity_coercive

theorem threshold_has_no_right_inverse :
    ¬ ∃ R : ℂ →L[ℂ] ℂ, ∀ f : ℂ, ∃ hf : R f ∈ identityOperator.domain,
      identityOperator ⟨R f, hf⟩ - (1 : ℂ) • R f = f := by
  rintro ⟨R, hR⟩
  obtain ⟨hf, h⟩ := hR 1
  simp [identityOperator] at h

theorem zero_operator_rejects_positive_coercivity :
    ¬ (∀ u : ℂ, (1 : ℝ) * ‖u‖ ^ 2 ≤ (⟪u, (0 : ℂ)⟫_ℂ).re) := by
  intro h
  have := h 1
  norm_num at this


/-- A zero domain satisfies any coercivity bound vacuously but cannot have an
everywhere-defined right inverse. The self-adjoint domain hypothesis excludes it. -/
def zeroDomainOperator : ℂ →ₗ.[ℂ] ℂ := ⟨⊥, 0⟩

theorem zero_domain_passes_coercivity : ∀ u : zeroDomainOperator.domain,
    (1 : ℝ) * ‖(u : ℂ)‖ ^ 2 ≤ (⟪(u : ℂ), zeroDomainOperator u⟫_ℂ).re := by
  intro u
  have hu : (u : ℂ) = 0 := u.property
  simp [hu, zeroDomainOperator]

theorem zero_domain_has_no_right_inverse :
    ¬ ∃ R : ℂ →L[ℂ] ℂ, ∀ f : ℂ, ∃ hf : R f ∈ zeroDomainOperator.domain,
      zeroDomainOperator ⟨R f, hf⟩ - (0 : ℂ) • R f = f := by
  rintro ⟨R, hR⟩
  obtain ⟨hf, h⟩ := hR 1
  simp [zeroDomainOperator] at h

theorem zero_domain_not_selfAdjoint : ¬ IsSelfAdjoint zeroDomainOperator := by
  intro hA
  obtain ⟨R, hR, _⟩ := selfAdjoint_resolvent_below_coercive_bound
    zeroDomainOperator hA 1 0 (by norm_num) zero_domain_passes_coercivity
  exact zero_domain_has_no_right_inverse ⟨R, hR⟩

end JesseMath.Physics.YangMillsResolventTest
#assert_zfc_axioms
