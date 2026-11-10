import JesseMath.Linter.AxiomAudit
import JesseMath.Physics.YangMillsWilsonLinkSpectral

/-!
# The radial Poincaré inequality for the one-link weight, on `(0, π)`

With `w = exp (t cos θ) sin² θ`, which is what the one-link weight of
`YangMillsWilsonLinkSpectral` would become in polar coordinates on `SU(2)` (that change of variables
is not formalised):

* `radial_poincare`: if `∫ u w = 0` then `3 ∫ u² w ≤ ∫ u'² w`, for every real `t`.
* `radial_poincare_variance`: the same with the weighted mean of `u` removed.
* `radial_poincare_sharp`, `nonradial_ground_state_sharp`: equality at `t = 0`, so `3` cannot be
  raised in either sector.

The proof works with the integral `P = ∫₀^θ u w` and `v = P / w`, for which `s v' + (2 k - t s²) v = s u`.
The supersolution `sin θ exp (-2 t cos θ / 5)` gives `3 ∫ v² w ≤ ∫ u² w` by the pointwise inequality
`dual_flux_le`, and `-u' P ≤ (u'² / 6 + 3 v² / 2) w` gives the result. No spectral theorem is used.

Limits. This is a statement about functions of one real variable `θ`. It is not the Poincaré
inequality on `SU(2)`, not even for class functions: the push-forward of Haar measure under `θ`
and the gradient on `SU(2)` are not formalised here. The nonradial sector is not covered by this
theorem. No target theorem uses this module.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Real

namespace JesseMath.Physics.YangMillsWilsonLinkSpectral

theorem linkWeight_pos {t θ : ℝ} (hθ : θ ∈ Ioo 0 π) : 0 < linkWeight t θ :=
  mul_pos (Real.exp_pos _) (pow_pos (Real.sin_pos_of_mem_Ioo hθ) 2)

theorem continuous_linkWeight (t : ℝ) : Continuous (linkWeight t) := by
  unfold linkWeight
  fun_prop

theorem hasDerivAt_linkWeight (t θ : ℝ) :
    HasDerivAt (linkWeight t)
      (Real.exp (t * Real.cos θ) * (2 * Real.sin θ * Real.cos θ - t * Real.sin θ ^ 3)) θ := by
  have hE : HasDerivAt (fun x => Real.exp (t * Real.cos x))
      (Real.exp (t * Real.cos θ) * (t * -Real.sin θ)) θ :=
    ((Real.hasDerivAt_cos θ).const_mul t).exp
  have hs2 : HasDerivAt (fun x => Real.sin x ^ 2) (2 * Real.sin θ * Real.cos θ) θ := by
    convert (Real.hasDerivAt_sin θ).pow 2 using 1
    ring
  refine HasDerivAt.congr_deriv (hE.fun_mul hs2) ?_
  ring

/-! ## The size of `∫ sin²` near the poles -/

theorem integral_sin_sq_le_left {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ π / 2) :
    ∫ y in (0 : ℝ)..x, Real.sin y ^ 2 ≤ π / 2 * Real.sin x ^ 3 := by
  have hx : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
  have hm : ∫ y in (0 : ℝ)..x, Real.sin y ^ 2 ≤ ∫ _y in (0 : ℝ)..x, Real.sin x ^ 2 :=
    intervalIntegral.integral_mono_on h0 (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _) fun y hy => by
        have hy0 : 0 ≤ Real.sin y :=
          Real.sin_nonneg_of_nonneg_of_le_pi hy.1 (by linarith [hy.2, Real.pi_pos])
        exact pow_le_pow_left₀ hy0
          (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hy.1, Real.pi_pos]) h1 hy.2) 2
  have hle := Real.mul_le_sin h0 h1
  have hpi := Real.pi_pos
  have hx' : x ≤ π / 2 * Real.sin x := by
    calc x = π / 2 * (2 / π * x) := by field_simp
      _ ≤ _ := by gcongr
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hm
  nlinarith [mul_le_mul_of_nonneg_right hx' (pow_nonneg hx 2)]

theorem integral_sin_sq_le_right {x : ℝ} (h0 : π / 2 ≤ x) (h1 : x ≤ π) :
    ∫ y in x..π, Real.sin y ^ 2 ≤ π / 2 * Real.sin x ^ 3 := by
  have h := integral_sin_sq_le_left (x := π - x) (by linarith) (by linarith)
  have hc := intervalIntegral.integral_comp_sub_left (a := 0) (b := π - x)
    (fun y => Real.sin y ^ 2) π
  simp only [Real.sin_pi_sub, sub_sub_cancel, sub_zero] at hc h
  linarith

/-! ## The dual inequality -/

/-- The polynomial form of the ground-state representation for `sin θ exp (-2 t cos θ / 5)`. -/
theorem dual_flux_le (E s k t v v' : ℝ) (hE : 0 ≤ E) :
    (E * (-(t * s)) * (s * (3 * k - 3 / 5 * t * s ^ 2)) +
        E * (k * (3 * k - 3 / 5 * t * s ^ 2) + s * (-3 * s - 6 / 5 * t * s * k))) * v ^ 2 +
      E * (s * (3 * k - 3 / 5 * t * s ^ 2)) * (2 * v * v') ≤
      E * (s * v' + (2 * k - t * s ^ 2) * v) ^ 2 - 3 * (v ^ 2 * (E * s ^ 2)) := by
  have hid : E * (s * v' + (2 * k - t * s ^ 2) * v) ^ 2 - 3 * (v ^ 2 * (E * s ^ 2)) -
      ((E * (-(t * s)) * (s * (3 * k - 3 / 5 * t * s ^ 2)) +
        E * (k * (3 * k - 3 / 5 * t * s ^ 2) + s * (-3 * s - 6 / 5 * t * s * k))) * v ^ 2 +
      E * (s * (3 * k - 3 / 5 * t * s ^ 2)) * (2 * v * v')) =
      E * ((s * v' - (k + 2 / 5 * t * s ^ 2) * v) ^ 2 + 6 / 25 * (t * s ^ 2 * v) ^ 2) := by
    ring
  have hnn : 0 ≤ E * ((s * v' - (k + 2 / 5 * t * s ^ 2) * v) ^ 2 + 6 / 25 * (t * s ^ 2 * v) ^ 2) := by
    positivity
  linarith

/-- The flux of `dual_flux_le`. -/
def dualFlux (t θ : ℝ) : ℝ :=
  Real.exp (t * Real.cos θ) *
    (Real.sin θ * (3 * Real.cos θ - 3 / 5 * t * Real.sin θ ^ 2))

def dualFlux' (t θ : ℝ) : ℝ :=
  Real.exp (t * Real.cos θ) * (-(t * Real.sin θ)) *
      (Real.sin θ * (3 * Real.cos θ - 3 / 5 * t * Real.sin θ ^ 2)) +
    Real.exp (t * Real.cos θ) * (Real.cos θ * (3 * Real.cos θ - 3 / 5 * t * Real.sin θ ^ 2) +
      Real.sin θ * (-3 * Real.sin θ - 6 / 5 * t * Real.sin θ * Real.cos θ))

theorem hasDerivAt_dualFlux (t θ : ℝ) : HasDerivAt (dualFlux t) (dualFlux' t θ) θ := by
  have hE : HasDerivAt (fun x => Real.exp (t * Real.cos x))
      (Real.exp (t * Real.cos θ) * (t * -Real.sin θ)) θ :=
    ((Real.hasDerivAt_cos θ).const_mul t).exp
  have hs2 : HasDerivAt (fun x => Real.sin x ^ 2) (2 * Real.sin θ * Real.cos θ) θ := by
    convert (Real.hasDerivAt_sin θ).pow 2 using 1
    ring
  have h := hE.fun_mul ((Real.hasDerivAt_sin θ).fun_mul
    (((Real.hasDerivAt_cos θ).const_mul 3).fun_sub (hs2.const_mul (3 / 5 * t))))
  refine HasDerivAt.congr_deriv h ?_
  simp only [dualFlux']
  ring

theorem continuous_dualFlux (t : ℝ) : Continuous (dualFlux t) := by
  unfold dualFlux
  fun_prop

/-- The moment `P(x) = ∫₀ˣ u w`. -/
def momentP (t : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y in (0 : ℝ)..x, u y * linkWeight t y

/-- The dual variable `v = P / w`; Lean's division gives `0` at the poles. -/
def dualV (t : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ := momentP t u x / linkWeight t x

section Dual

variable {t : ℝ} {u : ℝ → ℝ}

theorem momentP_hasDerivAt (hu : ContinuousOn u (Icc 0 π)) {x : ℝ} (hx : x ∈ Ioo 0 π) :
    HasDerivAt (momentP t u) (u x * linkWeight t x) x := by
  have hc : ContinuousOn (fun y => u y * linkWeight t y) (Icc 0 π) :=
    hu.mul (continuous_linkWeight t).continuousOn
  have hsub : uIcc 0 x ⊆ Icc 0 π := by
    rw [uIcc_of_le hx.1.le]
    exact Icc_subset_Icc le_rfl hx.2.le
  exact intervalIntegral.integral_hasDerivAt_right ((hc.mono hsub).intervalIntegrable)
    (hc.mono Ioo_subset_Icc_self |>.stronglyMeasurableAtFilter isOpen_Ioo x hx)
    (hc.continuousAt (Icc_mem_nhds hx.1 hx.2))

theorem momentP_continuousOn (hu : ContinuousOn u (Icc 0 π)) :
    ContinuousOn (momentP t u) (Icc 0 π) := by
  have hc : ContinuousOn (fun y => u y * linkWeight t y) (Icc 0 π) :=
    hu.mul (continuous_linkWeight t).continuousOn
  have hi : IntervalIntegrable (fun y => u y * linkWeight t y) volume 0 π := by
    apply ContinuousOn.intervalIntegrable
    rwa [uIcc_of_le Real.pi_pos.le]
  exact intervalIntegral.continuousOn_primitive_interval' (by
    simpa [uIcc_of_le Real.pi_pos.le] using hi) (by simp [Real.pi_pos.le]) |>.mono
    (by simp [uIcc_of_le Real.pi_pos.le])

/-- `|v| ≤ K sin θ` on `[0, π]` when `u` has weighted mean zero. -/
theorem abs_dualV_le (hu : ContinuousOn u (Icc 0 π)) (hmean : momentP t u π = 0) :
    ∃ K, ∀ x ∈ Icc 0 π, |dualV t u x| ≤ K * Real.sin x := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hu
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, Real.pi_pos.le⟩)
  set A := Real.exp |t| with hA
  have hApos : 0 < A := Real.exp_pos _
  have hEle (y : ℝ) : Real.exp (t * Real.cos y) ≤ A := by
    apply Real.exp_le_exp.mpr
    calc t * Real.cos y ≤ |t * Real.cos y| := le_abs_self _
      _ = |t| * |Real.cos y| := abs_mul _ _
      _ ≤ |t| * 1 := by gcongr; exact Real.abs_cos_le_one y
      _ = |t| := mul_one _
  have hEge (y : ℝ) : 1 ≤ A * Real.exp (t * Real.cos y) := by
    rw [hA, ← Real.exp_add]
    apply Real.one_le_exp
    have h1 := neg_abs_le (t * Real.cos y)
    have h2 : |t * Real.cos y| ≤ |t| := by
      rw [abs_mul]
      nlinarith [abs_nonneg t, Real.abs_cos_le_one y]
    linarith
  have hb (y : ℝ) (hy : y ∈ Icc 0 π) : ‖u y * linkWeight t y‖ ≤ M * A * Real.sin y ^ 2 := by
    have hw : ‖linkWeight t y‖ ≤ A * Real.sin y ^ 2 := by
      rw [linkWeight, Real.norm_of_nonneg (by positivity)]
      gcongr
      exact hEle y
    rw [norm_mul, mul_assoc]
    exact mul_le_mul (hM y hy) hw (norm_nonneg _) hM0
  have hci : ContinuousOn (fun y => u y * linkWeight t y) (Icc 0 π) :=
    hu.mul (continuous_linkWeight t).continuousOn
  have hP : ∀ x ∈ Icc 0 π, |momentP t u x| ≤ M * A * (π / 2 * Real.sin x ^ 3) := by
    intro x hx
    have hMA : 0 ≤ M * A := by positivity
    by_cases hx2 : x ≤ π / 2
    · have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
        (f := fun y => u y * linkWeight t y) (g := fun y => M * A * Real.sin y ^ 2) hx.1
        (Eventually.of_forall fun y hy =>
          hb y ⟨hy.1.le, hy.2.trans hx.2⟩) (Continuous.intervalIntegrable (by fun_prop) 0 x)
      rw [intervalIntegral.integral_const_mul] at h
      exact h.trans (mul_le_mul_of_nonneg_left (integral_sin_sq_le_left hx.1 hx2) hMA)
    · have hsplit : momentP t u x = -∫ y in x..π, u y * linkWeight t y := by
        have hadd := intervalIntegral.integral_add_adjacent_intervals
          (a := 0) (b := x) (c := π) (μ := volume) (f := fun y => u y * linkWeight t y)
          (ContinuousOn.intervalIntegrable (hci.mono (by
            rw [uIcc_of_le hx.1]; exact Icc_subset_Icc le_rfl hx.2)))
          (ContinuousOn.intervalIntegrable (hci.mono (by
            rw [uIcc_of_le hx.2]; exact Icc_subset_Icc hx.1 le_rfl)))
        unfold momentP at hmean ⊢
        linarith
      have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
        (f := fun y => u y * linkWeight t y) (g := fun y => M * A * Real.sin y ^ 2) hx.2
        (Eventually.of_forall fun y hy =>
          hb y ⟨hx.1.trans hy.1.le, hy.2⟩) (Continuous.intervalIntegrable (by fun_prop) x π)
      rw [intervalIntegral.integral_const_mul] at h
      rw [hsplit, abs_neg]
      exact h.trans (mul_le_mul_of_nonneg_left
        (integral_sin_sq_le_right (not_le.mp hx2).le hx.2) hMA)
  refine ⟨M * A * (π / 2) * A, fun x hx => ?_⟩
  have hs0 : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi hx.1 hx.2
  rcases hs0.eq_or_lt with hs | hs
  · simp [dualV, linkWeight, ← hs]
  · have hE := Real.exp_pos (t * Real.cos x)
    have hw : 0 < linkWeight t x := mul_pos hE (pow_pos hs 2)
    rw [dualV, abs_div, abs_of_pos hw, div_le_iff₀ hw]
    refine (hP x hx).trans ?_
    have hk : 0 ≤ M * A * (π / 2) * Real.sin x ^ 3 := by positivity
    calc M * A * (π / 2 * Real.sin x ^ 3) = M * A * (π / 2) * Real.sin x ^ 3 * 1 := by ring
      _ ≤ M * A * (π / 2) * Real.sin x ^ 3 * (A * Real.exp (t * Real.cos x)) :=
          mul_le_mul_of_nonneg_left (hEge x) hk
      _ = _ := by simp only [linkWeight]; ring

theorem dualV_hasDerivAt (hu : ContinuousOn u (Icc 0 π)) {x : ℝ} (hx : x ∈ Ioo 0 π) :
    HasDerivAt (dualV t u)
      (u x - dualV t u x * (2 * Real.cos x / Real.sin x - t * Real.sin x)) x := by
  have h := (momentP_hasDerivAt (t := t) hu hx).fun_div (hasDerivAt_linkWeight t x)
    (linkWeight_pos hx).ne'
  refine HasDerivAt.congr_deriv h ?_
  have hs := (Real.sin_pos_of_mem_Ioo hx).ne'
  have hE := (Real.exp_pos (t * Real.cos x)).ne'
  simp only [dualV, linkWeight]
  field_simp

theorem dualV_continuousOn (hu : ContinuousOn u (Icc 0 π)) (hmean : momentP t u π = 0) :
    ContinuousOn (dualV t u) (Icc 0 π) := by
  obtain ⟨K, hK⟩ := abs_dualV_le hu hmean
  intro x hx
  by_cases hxo : x ∈ Ioo 0 π
  · exact (dualV_hasDerivAt hu hxo).continuousAt.continuousWithinAt
  · have hsx : Real.sin x = 0 := by
      have : x = 0 ∨ x = π := by
        by_contra hne
        obtain ⟨h1, h2⟩ := not_or.mp hne
        exact hxo ⟨lt_of_le_of_ne hx.1 (Ne.symm h1), lt_of_le_of_ne hx.2 h2⟩
      rcases this with rfl | rfl <;> simp
    have hv0 : dualV t u x = 0 := by simp [dualV, linkWeight, hsx]
    have hlim : Tendsto (fun y => K * Real.sin y) (𝓝[Icc 0 π] x) (𝓝 0) := by
      have : Continuous fun y => K * Real.sin y := by fun_prop
      simpa [hsx] using (this.tendsto x).mono_left nhdsWithin_le_nhds
    have h := squeeze_zero_norm' (f := dualV t u) (t₀ := 𝓝[Icc 0 π] x)
      (Eventually.mono self_mem_nhdsWithin fun y hy => by
        simpa [Real.norm_eq_abs] using hK y hy) hlim
    change Tendsto _ _ _
    rwa [hv0]

/-- The dual inequality: `3 ∫ v² w ≤ ∫ u² w`. -/
theorem dual_inequality (hu : ContinuousOn u (Icc 0 π)) (hmean : momentP t u π = 0) :
    3 * ∫ θ in (0 : ℝ)..π, dualV t u θ ^ 2 * linkWeight t θ ≤
      ∫ θ in (0 : ℝ)..π, u θ ^ 2 * linkWeight t θ := by
  have hv := dualV_continuousOn hu hmean
  have hw := (continuous_linkWeight t).continuousOn (s := Icc 0 π)
  have hB : IntegrableOn (fun θ => dualV t u θ ^ 2 * linkWeight t θ) (Icc 0 π) :=
    ((hv.pow 2).mul hw).integrableOn_Icc
  have hU : IntegrableOn (fun θ => u θ ^ 2 * linkWeight t θ) (Icc 0 π) :=
    ((hu.pow 2).mul hw).integrableOn_Icc
  have hG := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le
    (g := fun θ => dualFlux t θ * dualV t u θ ^ 2)
    (g' := fun θ => dualFlux' t θ * dualV t u θ ^ 2 + dualFlux t θ *
      (2 * dualV t u θ * (u θ - dualV t u θ * (2 * Real.cos θ / Real.sin θ - t * Real.sin θ))))
    (φ := fun θ => u θ ^ 2 * linkWeight t θ - 3 * (dualV t u θ ^ 2 * linkWeight t θ))
    Real.pi_pos.le ((continuous_dualFlux t).continuousOn.mul (hv.pow 2))
    (fun θ hθ => by
      have h := (hasDerivAt_dualFlux t θ).fun_mul ((dualV_hasDerivAt (t := t) hu hθ).fun_pow 2)
      refine (HasDerivAt.congr_deriv h ?_).hasDerivWithinAt
      simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one])
    (hU.sub (hB.const_mul 3))
    (fun θ hθ => by
      have hs := (Real.sin_pos_of_mem_Ioo hθ).ne'
      have hE := (Real.exp_pos (t * Real.cos θ)).le
      have h := dual_flux_le _ (Real.sin θ) (Real.cos θ) t (dualV t u θ)
        (u θ - dualV t u θ * (2 * Real.cos θ / Real.sin θ - t * Real.sin θ)) hE
      have hrel : Real.sin θ * (u θ - dualV t u θ * (2 * Real.cos θ / Real.sin θ - t * Real.sin θ)) +
          (2 * Real.cos θ - t * Real.sin θ ^ 2) * dualV t u θ = Real.sin θ * u θ := by
        field_simp
        ring
      rw [hrel] at h
      simp only [dualFlux, dualFlux', linkWeight]
      linarith [h])
  have hzero : dualFlux t π * dualV t u π ^ 2 - dualFlux t 0 * dualV t u 0 ^ 2 = 0 := by
    simp [dualFlux]
  simp only [hzero] at hG
  rw [intervalIntegral.integral_sub
    ((intervalIntegrable_iff_integrableOn_Icc_of_le Real.pi_pos.le).mpr hU)
    (((intervalIntegrable_iff_integrableOn_Icc_of_le Real.pi_pos.le).mpr hB).const_mul 3),
    intervalIntegral.integral_const_mul] at hG
  linarith

/-- **The radial Poincaré inequality**, on `(0, π)` with weight `w`, for every real `t`. -/
theorem radial_poincare {u' : ℝ → ℝ} (hu : ContinuousOn u (Icc 0 π))
    (hd : ∀ θ ∈ Ioo 0 π, HasDerivAt u (u' θ) θ)
    (hint : IntegrableOn (fun θ => u' θ ^ 2 * linkWeight t θ) (Ioo 0 π))
    (hmean : ∫ θ in (0 : ℝ)..π, u θ * linkWeight t θ = 0) :
    3 * ∫ θ in (0 : ℝ)..π, u θ ^ 2 * linkWeight t θ ≤
      ∫ θ in (0 : ℝ)..π, u' θ ^ 2 * linkWeight t θ := by
  have hP0 : momentP t u π = 0 := hmean
  have hdual := dual_inequality hu hP0
  have hv := dualV_continuousOn hu hP0
  have hw := (continuous_linkWeight t).continuousOn (s := Icc 0 π)
  have hB : IntegrableOn (fun θ => dualV t u θ ^ 2 * linkWeight t θ) (Icc 0 π) :=
    ((hv.pow 2).mul hw).integrableOn_Icc
  have hU : IntegrableOn (fun θ => u θ ^ 2 * linkWeight t θ) (Icc 0 π) :=
    ((hu.pow 2).mul hw).integrableOn_Icc
  have hA : IntegrableOn (fun θ => u' θ ^ 2 * linkWeight t θ) (Icc 0 π) :=
    Iff.mpr integrableOn_Icc_iff_integrableOn_Ioo hint
  have hΦ : IntegrableOn (fun θ => (u' θ ^ 2 * linkWeight t θ) * (1 / 6) +
      3 / 2 * (dualV t u θ ^ 2 * linkWeight t θ) - u θ ^ 2 * linkWeight t θ) (Icc 0 π) :=
    ((hA.mul_const (1 / 6)).add (hB.const_mul (3 / 2))).sub hU
  have hG := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le
    (g := fun θ => -(u θ * momentP t u θ))
    (g' := fun θ => -(u' θ * momentP t u θ + u θ * (u θ * linkWeight t θ)))
    (φ := fun θ => (u' θ ^ 2 * linkWeight t θ) * (1 / 6) +
      3 / 2 * (dualV t u θ ^ 2 * linkWeight t θ) - u θ ^ 2 * linkWeight t θ)
    Real.pi_pos.le (hu.mul (momentP_continuousOn hu)).neg
    (fun θ hθ => ((hd θ hθ).fun_mul (momentP_hasDerivAt hu hθ)).fun_neg.hasDerivWithinAt)
    hΦ
    (fun θ hθ => by
      have hwp := linkWeight_pos (t := t) hθ
      have hPv : momentP t u θ = dualV t u θ * linkWeight t θ := by
        simp only [dualV]
        field_simp
      rw [hPv]
      nlinarith [mul_nonneg (sq_nonneg (u' θ + 3 * dualV t u θ)) hwp.le])
  have hzero : -(u π * momentP t u π) - -(u 0 * momentP t u 0) = 0 := by
    have h0 : momentP t u 0 = 0 := by simp [momentP]
    rw [hP0, h0]
    simp
  simp only [hzero] at hG
  have ii (f : ℝ → ℝ) (hf : IntegrableOn f (Icc 0 π)) : IntervalIntegrable f volume 0 π :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le Real.pi_pos.le).mpr hf
  rw [intervalIntegral.integral_sub (((ii _ hA).mul_const _).add ((ii _ hB).const_mul _)) (ii _ hU),
    intervalIntegral.integral_add ((ii _ hA).mul_const _) ((ii _ hB).const_mul _),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul] at hG
  linarith

end Dual

/-- The radial Poincaré inequality with the weighted mean removed. -/
theorem radial_poincare_variance (t : ℝ) {u u' : ℝ → ℝ} (hu : ContinuousOn u (Icc 0 π))
    (hd : ∀ θ ∈ Ioo 0 π, HasDerivAt u (u' θ) θ)
    (hint : IntegrableOn (fun θ => u' θ ^ 2 * linkWeight t θ) (Ioo 0 π)) :
    3 * ∫ θ in (0 : ℝ)..π, (u θ -
        (∫ x in (0 : ℝ)..π, u x * linkWeight t x) / ∫ x in (0 : ℝ)..π, linkWeight t x) ^ 2 *
        linkWeight t θ ≤
      ∫ θ in (0 : ℝ)..π, u' θ ^ 2 * linkWeight t θ := by
  have hwc := continuous_linkWeight t
  have hZ : 0 < ∫ x in (0 : ℝ)..π, linkWeight t x :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hwc.intervalIntegrable _ _)
      (fun _ hx => linkWeight_pos hx) Real.pi_pos
  set m := (∫ x in (0 : ℝ)..π, u x * linkWeight t x) / ∫ x in (0 : ℝ)..π, linkWeight t x with hm
  refine radial_poincare (t := t) (u := fun θ => u θ - m) (hu.sub continuousOn_const)
    (fun θ hθ => (hd θ hθ).sub_const m) hint ?_
  have hi : IntervalIntegrable (fun x => u x * linkWeight t x) volume 0 π := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le Real.pi_pos.le]
    exact hu.mul hwc.continuousOn
  simp only [sub_mul]
  rw [intervalIntegral.integral_sub hi ((hwc.const_mul m).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, hm]
  field_simp
  ring

/-! ## The constant `3` cannot be raised -/

theorem integral_sin_four : ∫ θ in (0 : ℝ)..π, Real.sin θ ^ 4 = 3 * π / 8 := by
  have h := integral_sin_pow (a := 0) (b := π) 2
  norm_num [integral_sin_sq] at h
  rw [h]
  ring

theorem integral_sin_two : ∫ θ in (0 : ℝ)..π, Real.sin θ ^ 2 = π / 2 := by
  simp [integral_sin_sq]

/-- Equality in `nonradial_ground_state` at `t = 0`, `v = sin`. -/
theorem nonradial_ground_state_sharp :
    3 * ∫ θ in (0 : ℝ)..π, Real.sin θ ^ 2 * linkWeight 0 θ =
      ∫ θ in (0 : ℝ)..π,
        (Real.cos θ ^ 2 + 2 / Real.sin θ ^ 2 * Real.sin θ ^ 2) * linkWeight 0 θ := by
  have hL : ∀ θ, Real.sin θ ^ 2 * linkWeight 0 θ = Real.sin θ ^ 4 := fun θ => by
    simp only [linkWeight, zero_mul, Real.exp_zero, one_mul]
    ring
  have hR : ∫ θ in (0 : ℝ)..π,
        (Real.cos θ ^ 2 + 2 / Real.sin θ ^ 2 * Real.sin θ ^ 2) * linkWeight 0 θ =
      ∫ θ in (0 : ℝ)..π, (3 * Real.sin θ ^ 2 - Real.sin θ ^ 4) := by
    rw [intervalIntegral.integral_of_le Real.pi_pos.le, intervalIntegral.integral_of_le Real.pi_pos.le,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
    have hs := (Real.sin_pos_of_mem_Ioo hθ).ne'
    have hsk := Real.sin_sq_add_cos_sq θ
    simp only [linkWeight, zero_mul, Real.exp_zero, one_mul]
    field_simp
    linear_combination hsk
  simp only [hL]
  rw [hR, intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_const_mul,
    integral_sin_four, integral_sin_two]
  ring

/-- Equality in `radial_poincare` at `t = 0`, `u = cos`, which has weighted mean zero. -/
theorem radial_poincare_sharp :
    (∫ θ in (0 : ℝ)..π, Real.cos θ * linkWeight 0 θ) = 0 ∧
    3 * ∫ θ in (0 : ℝ)..π, Real.cos θ ^ 2 * linkWeight 0 θ =
      ∫ θ in (0 : ℝ)..π, (-Real.sin θ) ^ 2 * linkWeight 0 θ := by
  have hw : ∀ θ, linkWeight 0 θ = Real.sin θ ^ 2 := fun θ => by
    simp [linkWeight]
  simp only [hw]
  constructor
  · have h : ∀ x ∈ uIcc 0 π, HasDerivAt (fun y => Real.sin y ^ 3 / 3)
        (Real.cos x * Real.sin x ^ 2) x := fun x _ => by
      have := ((Real.hasDerivAt_sin x).fun_pow 3).div_const 3
      refine HasDerivAt.congr_deriv this ?_
      simp only [Nat.cast_ofNat, Nat.add_one_sub_one]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    simp
  · have h1 : ∀ θ, Real.cos θ ^ 2 * Real.sin θ ^ 2 = Real.sin θ ^ 2 - Real.sin θ ^ 4 := fun θ => by
      have := Real.sin_sq_add_cos_sq θ
      linear_combination (Real.sin θ ^ 2) * this
    have h2 : ∀ θ, (-Real.sin θ) ^ 2 * Real.sin θ ^ 2 = Real.sin θ ^ 4 := fun θ => by ring
    simp only [h1, h2]
    rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _), integral_sin_four, integral_sin_two]
    ring

end JesseMath.Physics.YangMillsWilsonLinkSpectral

#assert_zfc_axioms
