import JesseMath.Linter.AxiomAudit
import JesseMath.Physics.YangMillsWilsonPlaquetteTail

/-!
# Collapse of the small-field event on the actual Wilson measure

Uses the mass transfer of `YangMillsWilsonPlaquetteTail` on an event the moved link cannot see.

* `wilson_smallField_tower`: for plaquettes whose first links avoid each other's boundaries,
  `Pr(all D(U_p) < t) ≤ exp(-|P| / (1 + exp(24 β t)))` for `0 < t ≤ 1/2`.
* `wilson_face_smallField_le`: the same for `N³` plaquettes in a three-dimensional face.
* `wilson_smallField_collapse`: along `β = b log k`, the event that `k³` such plaquettes all have
  `D < 2 ε / √β` has probability tending to zero, uniformly over every lattice with `2 k ≤ L`.

So a global "every plaquette in a fixed physical block is small" event has vanishing probability at
this threshold, and any small-field argument has to localise defects rather than exclude them.

Limits. This is a negative statement about one event. It says nothing about correlations and is
not a mass-gap mechanism: the proof uses only that `a + a⁻¹` is scalar, which also holds in U(1). No
target theorem uses this module.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter
open scoped Topology

namespace JesseMath.Physics.YangMillsWilsonPlaquetteTail

variable {L : ℕ} [NeZero L]

/-! ## Link-disjoint plaquettes -/

/-- All plaquettes of `P` are below `t`. -/
def smallEvent (P : Finset (Plaquette L)) (t : ℝ) : Set (GaugeConfig L) :=
  {U | ∀ p ∈ P, plaquetteAction U p < t}

theorem measurableSet_smallEvent (P : Finset (Plaquette L)) (t : ℝ) :
    MeasurableSet (smallEvent P t) := by
  have : smallEvent P t = ⋂ p ∈ P, {U | plaquetteAction U p < t} := by
    ext U; simp [smallEvent]
  rw [this]
  exact Finset.measurableSet_biInter _ fun p _ => measurableSet_plaquette_lt p t

/-- The first link of each plaquette of `P` avoids every other plaquette of `P`. -/
def FirstLinkSeparated (P : Finset (Plaquette L)) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, p ≠ q → firstLink p ∉ plaquetteBoundaryLinks q

/-- **Tower.** Mass of "all small" falls by a fixed factor per plaquette. -/
theorem wilsonMass_smallEvent_le (hL : 2 ≤ L) {β : ℝ} (hβ : 0 ≤ β) {t : ℝ} (g : SU2)
    (hg : ∀ h : SU2, linkDefect h < t → t ≤ linkDefect (g * h) ∧ t ≤ linkDefect (g⁻¹ * h))
    (P : Finset (Plaquette L)) (hP : FirstLinkSeparated P) :
    wilsonMass L β (smallEvent P t) ≤
      (Real.exp (6 * β * linkDefect g) / (1 + Real.exp (6 * β * linkDefect g))) ^ P.card *
        wilsonPartition (gaugeHaarMeasure L) β := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    have : smallEvent (∅ : Finset (Plaquette L)) t = Set.univ := by ext U; simp [smallEvent]
    simp [this, wilsonMass_univ]
  | insert p₀ P hp₀ ih =>
    have hsub : FirstLinkSeparated P := fun p hp q hq =>
      hP p (Finset.mem_insert_of_mem hp) q (Finset.mem_insert_of_mem hq)
    have hset : smallEvent (insert p₀ P) t =
        smallEvent P t ∩ {U | plaquetteAction U p₀ < t} := by
      ext U
      simp only [smallEvent, Finset.mem_insert, forall_eq_or_imp, Set.mem_ofPred_eq, Set.mem_inter_iff]
      tauto
    have hinv : ∀ g' U, U ∈ smallEvent P t → linkMove (firstLink p₀) g' U ∈ smallEvent P t := by
      intro g' U hU q hq
      have hne : p₀ ≠ q := fun h => hp₀ (h ▸ hq)
      rw [plaquetteAction_linkMove_of_not_mem U q
        (hP p₀ (Finset.mem_insert_self _ _) q (Finset.mem_insert_of_mem hq) hne) g']
      exact hU q hq
    have hstep := wilsonMass_small_le hL hβ p₀ (measurableSet_smallEvent P t) hinv g hg
    rw [hset, Finset.card_insert_of_notMem hp₀, pow_succ']
    set r := Real.exp (6 * β * linkDefect g) / (1 + Real.exp (6 * β * linkDefect g))
    have hr : 0 ≤ r := by positivity
    calc _ ≤ r * wilsonMass L β (smallEvent P t) := hstep
      _ ≤ r * (r ^ P.card * wilsonPartition (gaugeHaarMeasure L) β) := by gcongr; exact ih hsub
      _ = _ := by ring

/-- `x / (1 + x) ≤ exp(-1 / (1 + x))`. -/
theorem div_one_add_le_exp {x : ℝ} (hx : 0 < x) : x / (1 + x) ≤ Real.exp (-(1 / (1 + x))) := by
  have h := Real.add_one_le_exp (-(1 / (1 + x)))
  have : x / (1 + x) = -(1 / (1 + x)) + 1 := by field_simp; ring
  rw [this]
  exact h

/-- **Geometric decay of the small-field event.** For `0 < t ≤ 1/2`:
`Pr(all p ∈ P have D < t) ≤ exp(-|P| / (1 + exp(24 β t)))`, independent of `L`. -/
theorem wilson_smallField_tower (hL : 2 ≤ L) {β : ℝ} (hβ : 0 ≤ β) {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 1 / 2)
    (P : Finset (Plaquette L)) (hP : FirstLinkSeparated P) :
    (wilsonMeasure (gaugeHaarMeasure L) β).real (smallEvent P t) ≤
      Real.exp (-((P.card : ℝ) / (1 + Real.exp (24 * β * t)))) := by
  obtain ⟨g, hg, hmv⟩ := exists_move_small ht ht2
  have hZ := wilsonPartition_pos (gaugeHaarMeasure L) hβ (measurable_wilsonAction β)
  have h := wilsonMass_smallEvent_le hL hβ g hmv P hP
  have hx : 6 * β * linkDefect g = 24 * β * t := by rw [hg]; ring
  rw [hx] at h
  rw [wilsonMeasure_real_eq hβ (measurableSet_smallEvent P t), div_le_iff₀ hZ]
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hZ.le)
  set x := Real.exp (24 * β * t)
  have hxp : 0 < x := Real.exp_pos _
  calc (x / (1 + x)) ^ P.card ≤ (Real.exp (-(1 / (1 + x)))) ^ P.card := by
        gcongr
        exact div_one_add_le_exp hxp
    _ = _ := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring

/-! ## A concrete family in a three-dimensional face -/

/-- `N³` plaquettes in plane `(1, 2)` at `x₀ = 0`, with even coordinates. -/
def facePlaquette (L N : ℕ) (i : Fin N × Fin N × Fin N) : Plaquette L where
  x := ![0, ((2 * (i.1 : ℕ) : ℕ) : ZMod L), ((2 * (i.2.1 : ℕ) : ℕ) : ZMod L),
    ((2 * (i.2.2 : ℕ) : ℕ) : ZMod L)]
  μ := 1
  ν := 2
  h := by decide

omit [NeZero L] in
theorem natCast_zmod_inj {a b : ℕ} (ha : a < L) (hb : b < L) (h : (a : ZMod L) = (b : ZMod L)) :
    a = b := by
  have := (ZMod.natCast_eq_natCast_iff' a b L).mp h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

omit [NeZero L] in
theorem facePlaquette_injective {N : ℕ} (hN : 2 * N ≤ L) :
    Function.Injective (facePlaquette L N) := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  have hx := congrArg Plaquette.x h
  have h1 := congrFun hx 1
  have h2 := congrFun hx 2
  have h3 := congrFun hx 3
  simp only [facePlaquette, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero] at h1 h2 h3
  have e1 := natCast_zmod_inj (by omega) (by omega) h1
  have e2 := natCast_zmod_inj (by omega) (by omega) h2
  have e3 := natCast_zmod_inj (by omega) (by omega) h3
  have ea : a = a' := Fin.ext (by omega)
  have eb : b = b' := Fin.ext (by omega)
  have ec : c = c' := Fin.ext (by omega)
  simp [ea, eb, ec]

/-- The family as a finite set. -/
def faceFamily (L N : ℕ) [NeZero L] : Finset (Plaquette L) := by
  classical
  exact Finset.univ.image (facePlaquette L N)

theorem faceFamily_card {N : ℕ} (hN : 2 * N ≤ L) : (faceFamily L N).card = N ^ 3 := by
  classical
  unfold faceFamily
  rw [Finset.card_image_of_injective _ (facePlaquette_injective hN)]
  simp [Fintype.card_prod]
  ring

theorem faceFamily_separated {N : ℕ} (hN : 2 * N ≤ L) : FirstLinkSeparated (faceFamily L N) := by
  classical
  intro p hp q hq hne hmem
  simp only [faceFamily, Finset.mem_image, Finset.mem_univ, true_and] at hp hq
  obtain ⟨i, rfl⟩ := hp
  obtain ⟨j, rfl⟩ := hq
  simp only [plaquetteBoundaryLinks, Finset.mem_insert, Finset.mem_singleton, firstLink] at hmem
  rcases hmem with h | h | h | h
  · apply hne
    have hx := congrArg Link.x h
    obtain ⟨a, b, c⟩ := i
    obtain ⟨a', b', c'⟩ := j
    have h1 := congrFun hx 1
    have h2 := congrFun hx 2
    have h3 := congrFun hx 3
    simp only [facePlaquette, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero] at h1 h2 h3
    have e1 := natCast_zmod_inj (by omega) (by omega) h1
    have e2 := natCast_zmod_inj (by omega) (by omega) h2
    have e3 := natCast_zmod_inj (by omega) (by omega) h3
    have ea : a = a' := Fin.ext (by omega)
    have eb : b = b' := Fin.ext (by omega)
    have ec : c = c' := Fin.ext (by omega)
    simp [ea, eb, ec]
  · have := congrArg Link.μ h
    simp [facePlaquette] at this
  · have hx := congrFun (congrArg Link.x h) 2
    obtain ⟨a, b, c⟩ := i
    obtain ⟨a', b', c'⟩ := j
    simp only [facePlaquette, shift, unitVec, Pi.add_apply, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, ite_true] at hx
    have hx' : ((2 * (b : ℕ) : ℕ) : ZMod L) = ((2 * (b' : ℕ) + 1 : ℕ) : ZMod L) := by
      push_cast
      push_cast at hx
      simpa using hx
    have := natCast_zmod_inj (by omega) (by omega) hx'
    omega
  · have := congrArg Link.μ h
    simp [facePlaquette] at this

/-- **Volume-independent bound for the face family.** -/
theorem wilson_face_smallField_le (hL : 2 ≤ L) {N : ℕ} (hN : 2 * N ≤ L) {β : ℝ} (hβ : 0 ≤ β) {t : ℝ}
    (ht : 0 < t) (ht2 : t ≤ 1 / 2) :
    (wilsonMeasure (gaugeHaarMeasure L) β).real (smallEvent (faceFamily L N) t) ≤
      Real.exp (-((N : ℝ) ^ 3 / (1 + Real.exp (24 * β * t)))) := by
  have h := wilson_smallField_tower hL hβ ht ht2 (faceFamily L N) (faceFamily_separated hN)
  rw [faceFamily_card hN] at h
  push_cast at h
  exact h

/-- **Collapse of the small-field event along the weak-coupling trajectory.** With `β = b log k`
and threshold `t = 2 ε / √β`, the event that all `k³` face plaquettes satisfy `D < t` has
probability tending to zero, uniformly in every lattice with `2 k ≤ L`. -/
theorem wilson_smallField_collapse {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ (L : ℕ) [NeZero L], 2 * k ≤ L →
      (wilsonMeasure (gaugeHaarMeasure L) (b * Real.log k)).real
        (smallEvent (faceFamily L k) (2 * ε / Real.sqrt (b * Real.log k))) ≤ δ := by
  set c := 48 * ε * Real.sqrt b with hc
  have hcp : 0 ≤ c := by positivity
  have hlog : Tendsto (fun k : ℕ => Real.log k) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbeta : Tendsto (fun k : ℕ => b * Real.log k) atTop atTop := hlog.const_mul_atTop hb
  have hsqrt : Tendsto (fun k : ℕ => Real.sqrt (b * Real.log k)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hbeta
  have hlarge : Tendsto (fun k : ℕ => ((k : ℝ) / 2) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num)).comp
      (tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num))
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp
    ((hlog.eventually_ge_atTop (c ^ 2 + 1)).and <|
      (hsqrt.eventually_ge_atTop (4 * ε)).and <|
        (hlarge.eventually_ge_atTop (-Real.log δ)).and
          (eventually_ge_atTop 2))
  refine ⟨k₀, fun k hk L _ hkL => ?_⟩
  obtain ⟨hk1, hk2, hk3, hk4⟩ := hk₀ k hk
  have hk2' : (2 : ℝ) ≤ k := by exact_mod_cast hk4
  have hlogpos : 0 < Real.log k := by nlinarith [sq_nonneg c]
  have hβ : 0 ≤ b * Real.log k := by positivity
  have hsq : 0 < Real.sqrt (b * Real.log k) := Real.sqrt_pos.mpr (by positivity)
  have ht : 0 < 2 * ε / Real.sqrt (b * Real.log k) := by positivity
  have ht2 : 2 * ε / Real.sqrt (b * Real.log k) ≤ 1 / 2 := by
    rw [div_le_iff₀ hsq]
    linarith
  have hL : 2 ≤ L := by omega
  have hmain := wilson_face_smallField_le hL hkL hβ ht ht2
  refine hmain.trans ?_
  have hexpo : 24 * (b * Real.log k) * (2 * ε / Real.sqrt (b * Real.log k)) =
      c * Real.sqrt (Real.log k) := by
    have hr0 : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
    have hs0 : 0 < Real.sqrt (Real.log k) := Real.sqrt_pos.mpr hlogpos
    have hsplit : Real.sqrt (b * Real.log k) = Real.sqrt b * Real.sqrt (Real.log k) :=
      Real.sqrt_mul hb.le _
    have hprod : b * Real.log k = (Real.sqrt b * Real.sqrt (Real.log k)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hb.le, Real.sq_sqrt hlogpos.le]
    rw [hsplit, hprod, hc]
    field_simp
    ring
  rw [hexpo]
  have hle : c * Real.sqrt (Real.log k) ≤ Real.log k := by
    have hs0 := Real.sqrt_nonneg (Real.log k)
    have hs2 := Real.sq_sqrt hlogpos.le
    have hcs : c ≤ Real.sqrt (Real.log k) := by
      apply Real.le_sqrt_of_sq_le
      linarith
    nlinarith
  have hkpos : (0 : ℝ) < k := by linarith
  have hexp : Real.exp (c * Real.sqrt (Real.log k)) ≤ k := by
    calc _ ≤ Real.exp (Real.log k) := Real.exp_le_exp.mpr hle
      _ = k := Real.exp_log hkpos
  have hfrac : ((k : ℝ) / 2) ^ 2 ≤ (k : ℝ) ^ 3 / (1 + Real.exp (c * Real.sqrt (Real.log k))) := by
    rw [le_div_iff₀ (by positivity)]
    have : 0 ≤ (k : ℝ) ^ 2 := by positivity
    nlinarith
  have hfinal : -((k : ℝ) ^ 3 / (1 + Real.exp (c * Real.sqrt (Real.log k)))) ≤ Real.log δ := by
    linarith
  calc _ ≤ Real.exp (Real.log δ) := Real.exp_le_exp.mpr hfinal
    _ = δ := Real.exp_log hδ

end JesseMath.Physics.YangMillsWilsonPlaquetteTail

#assert_zfc_axioms
