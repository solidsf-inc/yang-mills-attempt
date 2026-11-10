import Mathlib
import JesseMath.Linter.AxiomAudit

/-!
Whole-space decay from dense-core convergence of evolution operators. This is an
abstract complex Hilbert-space bridge, not a construction of the Wilson/OS
Hamiltonian. Its inputs must come from the same physical theory: a common-space
identification, normalized convergent vacua, vacuum-preserving cutoff evolution,
and a uniform decay estimate in physical time. No operator-norm convergence,
finite-dimensionality, or selected eigenstate is assumed.
-/

noncomputable section

namespace JesseMath.Physics.YangMillsPhysicalGap

open Filter
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def vacuumPart (Ω u : H) : H := ⟪Ω, u⟫_ℂ • Ω

def excitedPart (Ω u : H) : H := u - vacuumPart Ω u

theorem continuous_vacuumPart (Ω : H) : Continuous (vacuumPart Ω) := by
  exact (continuous_const.inner continuous_id).smul continuous_const

theorem continuous_excitedPart (Ω : H) : Continuous (excitedPart Ω) :=
  continuous_id.sub (continuous_vacuumPart Ω)

theorem vacuumPart_self {Ω : H} (hΩ : ‖Ω‖ = 1) : vacuumPart Ω Ω = Ω := by
  simp [vacuumPart, inner_self_eq_norm_sq_to_K, hΩ]

theorem excitedPart_orthogonal {Ω : H} (hΩ : ‖Ω‖ = 1) (u : H) :
    ⟪Ω, excitedPart Ω u⟫_ℂ = 0 := by
  simp [excitedPart, vacuumPart, inner_self_eq_norm_sq_to_K, hΩ]

theorem vacuumPart_tendsto {Ωn : ℕ → H} {Ω : H}
    (hΩ : Tendsto Ωn atTop (𝓝 Ω)) (u : H) :
    Tendsto (fun n => vacuumPart (Ωn n) u) atTop (𝓝 (vacuumPart Ω u)) :=
  (hΩ.inner tendsto_const_nhds).smul hΩ

omit [InnerProductSpace ℂ H] in
theorem normalized_vacuum_limit {Ωn : ℕ → H} {Ω : H}
    (hΩ : Tendsto Ωn atTop (𝓝 Ω)) (hnorm : ∀ n, ‖Ωn n‖ = 1) : ‖Ω‖ = 1 := by
  exact tendsto_nhds_unique hΩ.norm (by simpa only [hnorm] using tendsto_const_nhds)

theorem map_excitedPart (A : H →L[ℂ] H) {Ω : H} (hfix : A Ω = Ω) (u : H) :
    A (excitedPart Ω u) = A u - vacuumPart Ω u := by
  simp [excitedPart, vacuumPart, map_sub, map_smul, hfix]

/-- Dense-core strong convergence suffices for a bound on every vector. The
cutoff bound is on the actual moving vacuum complement; vacuum preservation
turns it into a bound on fixed-vector differences before taking the limit. -/
theorem dense_core_decay_limit (D : Set H) (hD : Dense D)
    (A : ℕ → H →L[ℂ] H) (B : H →L[ℂ] H)
    (Ωn : ℕ → H) (Ω : H) (q : ℝ)
    (hΩ : Tendsto Ωn atTop (𝓝 Ω))
    (hfix : ∀ n, A n (Ωn n) = Ωn n)
    (hstrong : ∀ u ∈ D, Tendsto (fun n => A n u) atTop (𝓝 (B u)))
    (hdecay : ∀ n u, u ∈ D →
      ‖A n (excitedPart (Ωn n) u)‖ ≤ q * ‖excitedPart (Ωn n) u‖) :
    ∀ u : H, ‖B u - vacuumPart Ω u‖ ≤ q * ‖excitedPart Ω u‖ := by
  have hcore : ∀ u ∈ D, ‖B u - vacuumPart Ω u‖ ≤ q * ‖excitedPart Ω u‖ := by
    intro u hu
    have hp := vacuumPart_tendsto hΩ u
    have hleft := ((hstrong u hu).sub hp).norm
    have hright := (tendsto_const_nhds (x := q)).mul
      (((tendsto_const_nhds (x := u)).sub hp).norm)
    apply le_of_tendsto_of_tendsto hleft hright
    exact Eventually.of_forall fun n => by
      have hd := hdecay n u hu
      rw [map_excitedPart (A n) (hfix n) u] at hd
      exact hd
  intro u
  exact le_on_closure hcore
    ((B.continuous.sub (continuous_vacuumPart Ω)).norm.continuousOn)
    ((continuous_const.mul (continuous_excitedPart Ω).norm).continuousOn) (hD u)

/-- The limiting vacuum is fixed and the estimate controls the entire excited
space, including sectors not singled out by an observable. -/
theorem dense_core_decay_limit_with_vacuum (D : Set H) (hD : Dense D)
    (A : ℕ → H →L[ℂ] H) (B : H →L[ℂ] H)
    (Ωn : ℕ → H) (Ω : H) (q : ℝ)
    (hΩ : Tendsto Ωn atTop (𝓝 Ω)) (hnorm : ∀ n, ‖Ωn n‖ = 1)
    (hfix : ∀ n, A n (Ωn n) = Ωn n)
    (hstrong : ∀ u ∈ D, Tendsto (fun n => A n u) atTop (𝓝 (B u)))
    (hdecay : ∀ n u, u ∈ D →
      ‖A n (excitedPart (Ωn n) u)‖ ≤ q * ‖excitedPart (Ωn n) u‖) :
    B Ω = Ω ∧ ∀ u, ⟪Ω, u⟫_ℂ = 0 → ‖B u‖ ≤ q * ‖u‖ := by
  have h := dense_core_decay_limit D hD A B Ωn Ω q hΩ hfix hstrong hdecay
  have hnormΩ := normalized_vacuum_limit hΩ hnorm
  constructor
  · have hself := h Ω
    rw [vacuumPart_self hnormΩ] at hself
    have hexc : excitedPart Ω Ω = 0 := by simp [excitedPart, vacuumPart_self hnormΩ]
    rw [hexc, norm_zero, mul_zero] at hself
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hself (norm_nonneg _)))
  · intro u hu
    simpa [excitedPart, vacuumPart, hu] using h u

/-- Apply the dense-core theorem at every nonnegative physical time. The
semigroup law is not needed for this limit step; identifying this evolution as
the physical semigroup and identifying its generator are separate obligations. -/
theorem evolution_decay_survives_dense_core_limit (D : Set H) (hD : Dense D)
    (Tn : ℕ → ℝ → H →L[ℂ] H) (T : ℝ → H →L[ℂ] H)
    (Ωn : ℕ → H) (Ω : H) (m : ℝ)
    (hΩ : Tendsto Ωn atTop (𝓝 Ω)) (hnorm : ∀ n, ‖Ωn n‖ = 1)
    (hfix : ∀ n t, 0 ≤ t → Tn n t (Ωn n) = Ωn n)
    (hstrong : ∀ t, 0 ≤ t → ∀ u ∈ D,
      Tendsto (fun n => Tn n t u) atTop (𝓝 (T t u)))
    (hdecay : ∀ n t, 0 ≤ t → ∀ u, u ∈ D →
      ‖Tn n t (excitedPart (Ωn n) u)‖ ≤ Real.exp (-m * t) * ‖excitedPart (Ωn n) u‖) :
    ∀ t, 0 ≤ t → T t Ω = Ω ∧
      ∀ u, ⟪Ω, u⟫_ℂ = 0 → ‖T t u‖ ≤ Real.exp (-m * t) * ‖u‖ := by
  intro t ht
  exact dense_core_decay_limit_with_vacuum D hD (fun n => Tn n t) (T t) Ωn Ω
    (Real.exp (-m * t)) hΩ hnorm (fun n => hfix n t ht) (hstrong t ht)
    (fun n u hu => hdecay n t ht u hu)

/-- A one-sided comparison at a common initial value compares right derivatives. -/
theorem right_derivative_le_of_le {f g : ℝ → ℝ} {f' g' : ℝ}
    (hf : HasDerivWithinAt f f' (Set.Ioi 0) 0)
    (hg : HasDerivWithinAt g g' (Set.Ioi 0) 0)
    (hzero : f 0 = g 0) (hle : ∀ t, 0 < t → f t ≤ g t) : f' ≤ g' := by
  have hf' := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Set.Ioi 0)).mp hf
  have hg' := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Set.Ioi 0)).mp hg
  apply le_of_tendsto_of_tendsto hf' hg'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [Set.mem_Ioi] at ht
  rw [slope_def_field, slope_def_field, hzero]
  exact div_le_div_of_nonneg_right (sub_le_sub_right (hle t ht) _) (by linarith)

/-- Coercivity follows from decay of the actual evolution and its right vector
derivative at zero. `Hu` is the value of the generator on this vector; this
statement neither assumes a bounded Hamiltonian nor extends its domain. -/
theorem generator_coercivity_of_decay (T : ℝ → H →L[ℂ] H) (u Hu : H) (m : ℝ)
    (hzero : T 0 u = u)
    (hgenerator : HasDerivWithinAt (fun t : ℝ => T t u) (-Hu) (Set.Ioi 0) 0)
    (hdecay : ∀ t, 0 < t → ‖T t u‖ ≤ Real.exp (-m * t) * ‖u‖) :
    m * ‖u‖ ^ 2 ≤ (⟪u, Hu⟫_ℂ).re := by
  have hinner := (hasDerivWithinAt_const (0 : ℝ) (Set.Ioi 0) u).inner ℂ hgenerator
  have hreal := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt 0 hinner
  have hreal' : HasDerivWithinAt (fun t : ℝ => (⟪u, T t u⟫_ℂ).re)
      (-(⟪u, Hu⟫_ℂ).re) (Set.Ioi 0) 0 := by
    simpa [Function.comp_def] using hreal
  have hexp : HasDerivWithinAt (fun t : ℝ => Real.exp (-m * t) * ‖u‖ ^ 2)
      (-m * ‖u‖ ^ 2) (Set.Ioi 0) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).const_mul (-m)).exp.mul_const (‖u‖ ^ 2)).hasDerivWithinAt
  have hle := right_derivative_le_of_le hreal' hexp
    (by rw [hzero]; simpa only [mul_zero, Real.exp_zero, one_mul, RCLike.re_to_complex] using
      (inner_self_eq_norm_sq (𝕜 := ℂ) u)) (fun t ht => by
      calc
        (⟪u, T t u⟫_ℂ).re ≤ ‖u‖ * ‖T t u‖ := re_inner_le_norm (𝕜 := ℂ) _ _
        _ ≤ ‖u‖ * (Real.exp (-m * t) * ‖u‖) :=
          mul_le_mul_of_nonneg_left (hdecay t ht) (norm_nonneg u)
        _ = Real.exp (-m * t) * ‖u‖ ^ 2 := by ring)
  linarith

/-- The operator bridge in one statement. `domain` is the generator domain,
not an assertion that an unbounded Hamiltonian is defined continuously on all
of `H`. Coercivity is derived, not stored as a hypothesis. Self-adjointness and
identification with the physical Wilson/OS dynamics remain separate inputs. -/
theorem physical_generator_bound_of_cutoff_decay (D : Set H) (hD : Dense D)
    (Tn : ℕ → ℝ → H →L[ℂ] H) (T : ℝ → H →L[ℂ] H)
    (Ωn : ℕ → H) (Ω : H) (m : ℝ)
    (domain : Submodule ℂ H) (generator : domain →ₗ[ℂ] H)
    (hΩ : Tendsto Ωn atTop (𝓝 Ω)) (hnorm : ∀ n, ‖Ωn n‖ = 1)
    (hfix : ∀ n t, 0 ≤ t → Tn n t (Ωn n) = Ωn n)
    (hstrong : ∀ t, 0 ≤ t → ∀ u ∈ D,
      Tendsto (fun n => Tn n t u) atTop (𝓝 (T t u)))
    (hdecay : ∀ n t, 0 ≤ t → ∀ u, u ∈ D →
      ‖Tn n t (excitedPart (Ωn n) u)‖ ≤ Real.exp (-m * t) * ‖excitedPart (Ωn n) u‖)
    (hzero : ∀ u : domain, T 0 u = u)
    (hgenerator : ∀ u : domain,
      HasDerivWithinAt (fun t : ℝ => T t u) (-(generator u)) (Set.Ioi 0) 0) :
    (∀ t, 0 ≤ t → T t Ω = Ω) ∧
      ∀ u : domain, ⟪Ω, (u : H)⟫_ℂ = 0 →
        m * ‖(u : H)‖ ^ 2 ≤ (⟪(u : H), generator u⟫_ℂ).re := by
  have hlim := evolution_decay_survives_dense_core_limit D hD Tn T Ωn Ω m
    hΩ hnorm hfix hstrong hdecay
  exact ⟨fun t ht => (hlim t ht).1, fun u hu =>
    generator_coercivity_of_decay T u (generator u) m (hzero u) (hgenerator u)
      (fun t ht => (hlim t ht.le).2 u hu)⟩

/-- Whole-space coercivity also controls approximate modes, not only
normalizable eigenvectors. This is a resolvent-residual bound on the declared
operator domain; it does not invoke an unformalized spectral theorem. -/
theorem generator_residual_lower_bound (u Hu : H) (m energy : ℝ)
    (hcoercive : m * ‖u‖ ^ 2 ≤ (⟪u, Hu⟫_ℂ).re) :
    (m - energy) * ‖u‖ ≤ ‖Hu - (energy : ℂ) • u‖ := by
  by_cases hu : u = 0
  · simp [hu]
  have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hcs := re_inner_le_norm (𝕜 := ℂ) u (Hu - (energy : ℂ) • u)
  have hreal : (⟪u, Hu - (energy : ℂ) • u⟫_ℂ).re = (⟪u, Hu⟫_ℂ).re - energy * ‖u‖ ^ 2 := by
    rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  rw [RCLike.re_to_complex, hreal] at hcs
  nlinarith

/-- A normalized approximate eigenvector sequence below `m` is excluded.
For a self-adjoint physical generator this is the relevant obstruction to
hidden low-energy continuous spectral modes as well as eigenstates. -/
theorem approximate_modes_respect_gap (u Hu : ℕ → H) (m energy : ℝ)
    (hnorm : ∀ n, ‖u n‖ = 1)
    (hcoercive : ∀ n, m * ‖u n‖ ^ 2 ≤ (⟪u n, Hu n⟫_ℂ).re)
    (hresidual : Tendsto (fun n => Hu n - (energy : ℂ) • u n) atTop (𝓝 0)) : m ≤ energy := by
  have hbound : ∀ n, m - energy ≤ ‖Hu n - (energy : ℂ) • u n‖ := by
    intro n
    simpa only [hnorm n, mul_one] using generator_residual_lower_bound (u n) (Hu n) m energy (hcoercive n)
  have hlim : m - energy ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds
    (by simpa only [norm_zero] using hresidual.norm) (Eventually.of_forall hbound)
  linarith

set_option maxHeartbeats 800000 in

/-- Coercivity of a self-adjoint, possibly unbounded operator puts every real
energy below the lower bound in its resolvent: there is an everywhere-defined
bounded inverse with both inverse identities and the sharp norm estimate.
For Yang--Mills this applies on the excited Hilbert space only after the actual
OS generator, its self-adjoint domain and the coercivity bound are constructed. -/
theorem selfAdjoint_resolvent_below_coercive_bound [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (m energy : ℝ)
    (henergy : energy < m)
    (hcoercive : ∀ u : A.domain, m * ‖(u : H)‖ ^ 2 ≤ (⟪(u : H), A u⟫_ℂ).re) :
    ∃ R : H →L[ℂ] H,
      (∀ f : H, ∃ hf : R f ∈ A.domain,
        A ⟨R f, hf⟩ - (energy : ℂ) • R f = f) ∧
      (∀ u : A.domain, R (A u - (energy : ℂ) • (u : H)) = (u : H)) ∧
      ‖R‖ ≤ 1 / (m - energy) := by
  let X : A.graph →L[ℂ] H :=
    (ContinuousLinearMap.fst ℂ H H).comp A.graph.subtypeL
  let Y : A.graph →L[ℂ] H :=
    (ContinuousLinearMap.snd ℂ H H).comp A.graph.subtypeL
  let B : A.graph →L[ℂ] H := Y - (energy : ℂ) • X
  have hd : 0 < m - energy := sub_pos.mpr henergy
  have hres : ∀ v : A.graph, (m - energy) * ‖X v‖ ≤ ‖B v‖ := by
    intro v
    obtain ⟨u, hu, hAu⟩ := A.mem_graph_iff.mp v.property
    have h := generator_residual_lower_bound (u : H) (A u) m energy (hcoercive u)
    change (m - energy) * ‖v.val.1‖ ≤ ‖v.val.2 - (energy : ℂ) • v.val.1‖
    simpa only [hu, hAu] using h
  have hbound : ∀ v : A.graph, ‖X v‖ ≤ (1 / (m - energy)) * ‖B v‖ := by
    intro v
    calc
      ‖X v‖ = ((m - energy) * ‖X v‖) / (m - energy) := by field_simp
      _ ≤ ‖B v‖ / (m - energy) := div_le_div_of_nonneg_right (hres v) hd.le
      _ = (1 / (m - energy)) * ‖B v‖ := by ring
  let K : ℝ := 1 + (1 + |energy|) / (m - energy)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hanti : AntilipschitzWith ⟨K, hK⟩ B := by
    apply B.antilipschitz_of_bound
    intro v
    have hx := hbound v
    have hy : ‖Y v‖ ≤ ‖B v‖ + |energy| * ‖X v‖ := by
      have hv : Y v = B v + (energy : ℂ) • X v := by simp [B]
      rw [hv]
      simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs] using
        norm_add_le (B v) ((energy : ℂ) • X v)
    change max ‖X v‖ ‖Y v‖ ≤ K * ‖B v‖
    have hN := norm_nonneg (B v)
    have hNX := norm_nonneg (X v)
    have hE := abs_nonneg energy
    have hi : 0 ≤ 1 / (m - energy) := le_of_lt (one_div_pos.mpr hd)
    have hK' : K = 1 + 1 / (m - energy) + |energy| * (1 / (m - energy)) := by
      dsimp [K]; ring
    rw [hK']
    apply max_le <;> nlinarith [mul_nonneg hE hN, mul_nonneg hE hi,
      mul_nonneg hE (sub_nonneg.mpr hx)]
  let : CompleteSpace A.graph := hA.isClosed.completeSpace_coe
  have horth : B.rangeᗮ = ⊥ := by
    apply eq_bot_iff.mpr
    intro y hy
    have hpair : ∀ u : A.domain,
        ⟪(energy : ℂ) • y, (u : H)⟫_ℂ = ⟪y, A u⟫_ℂ := by
      intro u
      let v : A.graph := ⟨((u : H), A u), A.mem_graph u⟩
      have hz := B.range.inner_left_of_mem_orthogonal (show B v ∈ B.range from ⟨v, rfl⟩) hy
      change ⟪y, A u - (energy : ℂ) • (u : H)⟫_ℂ = 0 at hz
      rw [inner_sub_right, inner_smul_right, sub_eq_zero] at hz
      simpa [inner_smul_left] using hz.symm
    have hyadj := A.mem_adjoint_domain_of_exists y ⟨(energy : ℂ) • y, hpair⟩
    have hay := LinearPMap.adjoint_apply_eq hA.dense_domain
      (⟨y, hyadj⟩ : A.adjoint.domain) hpair
    have hg : (y, (energy : ℂ) • y) ∈ A.adjoint.graph := by
      rw [← hay]
      exact A.adjoint.mem_graph ⟨y, hyadj⟩
    rw [LinearPMap.isSelfAdjoint_def.mp hA] at hg
    obtain ⟨u, hu, hAu⟩ := A.mem_graph_iff.mp hg
    have hr := generator_residual_lower_bound (u : H) (A u) m energy (hcoercive u)
    rw [hu, hAu, sub_self, norm_zero] at hr
    have hzero : y = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg y])
    simpa using hzero
  have hdense : B.range.topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, horth,
      Submodule.bot_orthogonal_eq_top]
  have hbij : Function.Bijective B :=
    B.bijective_iff_dense_range_and_antilipschitz.mpr ⟨hdense, ⟨⟨K, hK⟩, hanti⟩⟩
  let e : A.graph ≃L[ℂ] H := ContinuousLinearEquiv.ofBijective B
    (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
  let R : H →L[ℂ] H := X.comp e.symm.toContinuousLinearMap
  refine ⟨R, ?_, ?_, ?_⟩
  · intro f
    let v : A.graph := e.symm f
    obtain ⟨u, hu, hAu⟩ := A.mem_graph_iff.mp v.property
    have hRf : R f = (u : H) := hu.symm
    refine ⟨hRf ▸ u.property, ?_⟩
    have hAu' : A ⟨R f, hRf ▸ u.property⟩ = A u := by congr 1; exact Subtype.ext hRf
    rw [hAu', hRf]
    have hv : B v = f := e.apply_symm_apply f
    change v.val.2 - (energy : ℂ) • v.val.1 = f at hv
    simpa only [← hu, ← hAu] using hv
  · intro u
    let v : A.graph := ⟨((u : H), A u), A.mem_graph u⟩
    have heq : A u - (energy : ℂ) • (u : H) = e v := rfl
    rw [heq]
    change X (e.symm (e v)) = (u : H)
    rw [e.symm_apply_apply]
    rfl
  · apply R.opNorm_le_bound (by positivity)
    intro f
    have h := hbound (e.symm f)
    change ‖R f‖ ≤ (1 / (m - energy)) * ‖B (e.symm f)‖ at h
    simpa only [show B (e.symm f) = f from e.apply_symm_apply f] using h

/-- On an already identified excited Hilbert space, decay of the actual evolution
and its generator derivative give a bounded resolvent below `m`. The generator
may be unbounded; its self-adjointness and operator domain are explicit inputs. -/
theorem selfAdjoint_resolvent_of_evolution_decay [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (T : ℝ → H →L[ℂ] H) (m energy : ℝ) (henergy : energy < m)
    (hzero : ∀ u : A.domain, T 0 u = u)
    (hgenerator : ∀ u : A.domain,
      HasDerivWithinAt (fun t : ℝ => T t u) (-(A u)) (Set.Ioi 0) 0)
    (hdecay : ∀ u : A.domain, ∀ t, 0 < t →
      ‖T t u‖ ≤ Real.exp (-m * t) * ‖(u : H)‖) :
    ∃ R : H →L[ℂ] H,
      (∀ f : H, ∃ hf : R f ∈ A.domain,
        A ⟨R f, hf⟩ - (energy : ℂ) • R f = f) ∧
      (∀ u : A.domain, R (A u - (energy : ℂ) • (u : H)) = (u : H)) ∧
      ‖R‖ ≤ 1 / (m - energy) := by
  exact selfAdjoint_resolvent_below_coercive_bound A hA m energy henergy
    (fun u => generator_coercivity_of_decay T u (A u) m
      (hzero u) (hgenerator u) (hdecay u))

/-- Conditional combination of cutoff decay transfer, generator coercivity and
approximate-mode exclusion. The decay and generator derivative are supplied;
self-adjointness is not established, and neither are surjectivity or existence
of a bounded inverse. -/
theorem physical_generator_gap_and_excited_resolvent_exclusion_from_cutoff_decay
    (D : Set H) (hD : Dense D)
    (Tn : ℕ → ℝ → H →L[ℂ] H) (T : ℝ → H →L[ℂ] H)
    (Ωn : ℕ → H) (Ω : H) {m : ℝ} (hm : 0 < m)
    (domain : Submodule ℂ H) (generator : domain →ₗ[ℂ] H)
    (hΩ : Tendsto Ωn atTop (𝓝 Ω)) (hnorm : ∀ n, ‖Ωn n‖ = 1)
    (hfix : ∀ n t, 0 ≤ t → Tn n t (Ωn n) = Ωn n)
    (hstrong : ∀ t, 0 ≤ t → ∀ u ∈ D,
      Tendsto (fun n => Tn n t u) atTop (𝓝 (T t u)))
    (hdecay : ∀ n t, 0 ≤ t → ∀ u, u ∈ D →
      ‖Tn n t (excitedPart (Ωn n) u)‖ ≤ Real.exp (-m * t) * ‖excitedPart (Ωn n) u‖)
    (hzero : ∀ u : domain, T 0 u = u)
    (hgenerator : ∀ u : domain,
      HasDerivWithinAt (fun t : ℝ => T t u) (-(generator u)) (Set.Ioi 0) 0) :
    (∀ t, 0 ≤ t → T t Ω = Ω) ∧
    (∀ u : domain, ⟪Ω, (u : H)⟫_ℂ = 0 →
      m * ‖(u : H)‖ ^ 2 ≤ (⟪(u : H), generator u⟫_ℂ).re ∧
      ∀ energy : ℝ, (m - energy) * ‖(u : H)‖ ≤ ‖generator u - (energy : ℂ) • (u : H)‖) ∧
    (∀ (u_seq : ℕ → domain) (energy : ℝ),
      (∀ n, ⟪Ω, (u_seq n : H)⟫_ℂ = 0) →
      (∀ n, ‖(u_seq n : H)‖ = 1) →
      Tendsto (fun n => generator (u_seq n) - (energy : ℂ) • (u_seq n : H)) atTop (𝓝 0) →
      m ≤ energy ∧ 0 < energy) := by
  have hgen := physical_generator_bound_of_cutoff_decay D hD Tn T Ωn Ω m domain generator
    hΩ hnorm hfix hstrong hdecay hzero hgenerator
  refine ⟨hgen.1, ?_, ?_⟩
  · intro u hu
    have hcoercive := hgen.2 u hu
    exact ⟨hcoercive, fun energy => generator_residual_lower_bound (u : H) (generator u) m energy hcoercive⟩
  · intro u_seq energy horth hnorm_seq hres
    have hcoercive_seq : ∀ n, m * ‖(u_seq n : H)‖ ^ 2 ≤ (⟪(u_seq n : H), generator (u_seq n)⟫_ℂ).re :=
      fun n => hgen.2 (u_seq n) (horth n)
    have hm_le : m ≤ energy :=
      approximate_modes_respect_gap (fun n => (u_seq n : H)) (fun n => generator (u_seq n))
        m energy hnorm_seq hcoercive_seq hres
    exact ⟨hm_le, lt_of_lt_of_le hm hm_le⟩

/-- Whenever a fixed domain state `u_exc : domain` has a uniform positive excited-part norm floor
`ε_exc ≤ ‖excitedPart (Ωn n) u_exc‖` along a convergent sequence of normalized vacua `Ωn → Ω`,
the limiting excited state `u_perp = excitedPart Ω u_exc` is non-zero (`ε_exc ≤ ‖u_perp‖`, `u_perp ≠ 0`),
orthogonal to `Ω`, and carries strictly positive generator quadratic-form energy
`0 < m * ε_exc ^ 2 ≤ Re ⟪u_perp, generator u_perp⟫_ℂ` (`P11`/`M5`). -/
theorem nontrivial_excited_state_survives_cutoff_limit_and_positive_generator_energy
    (Ωn : ℕ → H) (Ω : H) {m ε_exc : ℝ} (hm : 0 < m) (hε : 0 < ε_exc)
    (domain : Submodule ℂ H) (generator : domain →ₗ[ℂ] H)
    (u_exc u_perp : domain)
    (hΩ : Tendsto Ωn atTop (𝓝 Ω)) (hnorm : ∀ n, ‖Ωn n‖ = 1)
    (h_exc_floor : ∀ n, ε_exc ≤ ‖excitedPart (Ωn n) (u_exc : H)‖)
    (h_perp_eq : (u_perp : H) = excitedPart Ω (u_exc : H))
    (hcoercive : ∀ u : domain, ⟪Ω, (u : H)⟫_ℂ = 0 →
      m * ‖(u : H)‖ ^ 2 ≤ (⟪(u : H), generator u⟫_ℂ).re) :
    (ε_exc ≤ ‖excitedPart Ω (u_exc : H)‖ ∧ excitedPart Ω (u_exc : H) ≠ 0) ∧
    (⟪Ω, (u_perp : H)⟫_ℂ = 0 ∧ m * ε_exc ^ 2 ≤ (⟪(u_perp : H), generator u_perp⟫_ℂ).re) ∧
    0 < (⟪(u_perp : H), generator u_perp⟫_ℂ).re := by
  have hp := vacuumPart_tendsto hΩ (u_exc : H)
  have hexc_tendsto : Tendsto (fun n => ‖excitedPart (Ωn n) (u_exc : H)‖)
      atTop (𝓝 ‖excitedPart Ω (u_exc : H)‖) :=
    ((tendsto_const_nhds (x := (u_exc : H))).sub hp).norm
  have h_lim_floor : ε_exc ≤ ‖excitedPart Ω (u_exc : H)‖ :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hexc_tendsto (Eventually.of_forall h_exc_floor)
  have h_ne_zero : excitedPart Ω (u_exc : H) ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le hε h_lim_floor)
  have hnormΩ : ‖Ω‖ = 1 := normalized_vacuum_limit hΩ hnorm
  have horth_perp : ⟪Ω, (u_perp : H)⟫_ℂ = 0 := by
    rw [h_perp_eq]
    exact excitedPart_orthogonal hnormΩ (u_exc : H)
  have h_coerc_perp := hcoercive u_perp horth_perp
  have h_sq_le : ε_exc ^ 2 ≤ ‖(u_perp : H)‖ ^ 2 := by
    rw [h_perp_eq]
    nlinarith [h_lim_floor, hε]
  have h_m_eps : m * ε_exc ^ 2 ≤ (⟪(u_perp : H), generator u_perp⟫_ℂ).re := by
    nlinarith [h_coerc_perp, h_sq_le, hm]
  have h_pos_re : 0 < (⟪(u_perp : H), generator u_perp⟫_ℂ).re :=
    lt_of_lt_of_le (mul_pos hm (sq_pos_of_pos hε)) h_m_eps
  exact ⟨⟨h_lim_floor, h_ne_zero⟩, ⟨horth_perp, h_m_eps⟩, h_pos_re⟩

/-- Candidate scalar rate. The integer parameter is not bound to a Lie group,
and this definition proves no Holley--Stroock, Bakry--Émery or physical gap estimate. -/
noncomputable def compactSimpleGroupPhysicalGapFloor (h_dual_coxeter : ℕ) (osc_W ell_star : ℝ) : ℝ :=
  ((h_dual_coxeter : ℝ) / 4) * Real.exp (-osc_W) / ell_star

/-- Conditional abstract synthesis. `hdecay` supplies decay at the advertised rate,
`h_exc_floor` supplies nonvanishing excitation, and `hstrong` and `hgenerator`
supply convergence and the generator derivative. No gauge group, Wilson measure,
OS reconstruction, complete space or self-adjoint physical domain is constructed.
This theorem does not discharge the physical obligations P09--P12 or M5--M6. -/
theorem j14_h2h_six_wave_master_physical_gap_and_compact_simple_group_synthesis
    (h_dual_coxeter : ℕ) (h_cox : 1 ≤ h_dual_coxeter)
    {osc_W ell_star ε_exc : ℝ} (h_osc : 0 ≤ osc_W) (h_ell : 0 < ell_star) (hε : 0 < ε_exc)
    (D : Set H) (hD : Dense D)
    (Tn : ℕ → ℝ → H →L[ℂ] H) (T : ℝ → H →L[ℂ] H)
    (Ωn : ℕ → H) (Ω : H)
    (domain : Submodule ℂ H) (generator : domain →ₗ[ℂ] H)
    (u_exc u_perp : domain)
    (hΩ : Tendsto Ωn atTop (𝓝 Ω)) (hnorm : ∀ n, ‖Ωn n‖ = 1)
    (hfix : ∀ n t, 0 ≤ t → Tn n t (Ωn n) = Ωn n)
    (hstrong : ∀ t, 0 ≤ t → ∀ u ∈ D,
      Tendsto (fun n => Tn n t u) atTop (𝓝 (T t u)))
    (hdecay : ∀ n t, 0 ≤ t → ∀ u, u ∈ D →
      ‖Tn n t (excitedPart (Ωn n) u)‖ ≤
        Real.exp (-compactSimpleGroupPhysicalGapFloor h_dual_coxeter osc_W ell_star * t) *
          ‖excitedPart (Ωn n) u‖)
    (hzero : ∀ u : domain, T 0 u = u)
    (hgenerator : ∀ u : domain,
      HasDerivWithinAt (fun t : ℝ => T t u) (-(generator u)) (Set.Ioi 0) 0)
    (h_exc_floor : ∀ n, ε_exc ≤ ‖excitedPart (Ωn n) (u_exc : H)‖)
    (h_perp_eq : (u_perp : H) = excitedPart Ω (u_exc : H)) :
    (0 < compactSimpleGroupPhysicalGapFloor h_dual_coxeter osc_W ell_star ∧
      compactSimpleGroupPhysicalGapFloor h_dual_coxeter osc_W ell_star ≤
        ((h_dual_coxeter : ℝ) / 4) / ell_star) ∧
    ((∀ t, 0 ≤ t → T t Ω = Ω) ∧ ‖Ω‖ = 1) ∧
    (excitedPart Ω (u_exc : H) ≠ 0 ∧
      compactSimpleGroupPhysicalGapFloor h_dual_coxeter osc_W ell_star * ε_exc ^ 2 ≤
        (⟪(u_perp : H), generator u_perp⟫_ℂ).re ∧
      0 < (⟪(u_perp : H), generator u_perp⟫_ℂ).re) ∧
    (∀ (u_seq : ℕ → domain) (energy : ℝ),
      (∀ n, ⟪Ω, (u_seq n : H)⟫_ℂ = 0) →
      (∀ n, ‖(u_seq n : H)‖ = 1) →
      Tendsto (fun n => generator (u_seq n) - (energy : ℂ) • (u_seq n : H)) atTop (𝓝 0) →
      compactSimpleGroupPhysicalGapFloor h_dual_coxeter osc_W ell_star ≤ energy ∧ 0 < energy) := by
  have h_cox_pos : (0 : ℝ) < (h_dual_coxeter : ℝ) :=
    Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one h_cox)
  have hm : 0 < compactSimpleGroupPhysicalGapFloor h_dual_coxeter osc_W ell_star :=
    div_pos (mul_pos (div_pos h_cox_pos (by norm_num)) (Real.exp_pos _)) h_ell
  have hexp_le_one : Real.exp (-osc_W) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hm_le : compactSimpleGroupPhysicalGapFloor h_dual_coxeter osc_W ell_star ≤
      ((h_dual_coxeter : ℝ) / 4) / ell_star := by
    dsimp [compactSimpleGroupPhysicalGapFloor]
    apply div_le_div_of_nonneg_right _ h_ell.le
    nlinarith
  have h_gap := physical_generator_gap_and_excited_resolvent_exclusion_from_cutoff_decay
    D hD Tn T Ωn Ω hm domain generator hΩ hnorm hfix hstrong hdecay hzero hgenerator
  have h_exc := nontrivial_excited_state_survives_cutoff_limit_and_positive_generator_energy
    Ωn Ω hm hε domain generator u_exc u_perp hΩ hnorm h_exc_floor h_perp_eq
    (fun u hu => (h_gap.2.1 u hu).1)
  exact ⟨⟨hm, hm_le⟩, ⟨h_gap.1, normalized_vacuum_limit hΩ hnorm⟩,
    ⟨h_exc.1.2, h_exc.2.1.2, h_exc.2.2⟩, h_gap.2.2⟩

end JesseMath.Physics.YangMillsPhysicalGap

#assert_zfc_axioms
