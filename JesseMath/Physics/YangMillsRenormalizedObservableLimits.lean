import JesseMath.Linter.AxiomAudit
import JesseMath.Physics.YangMillsContinuumCompactness
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Sequences

/-!
# Physical-scale Wilson loops: gauge invariance, tightness and gauge-invariant limits

Lattice paths on the actual periodic lattice carry holonomies that transform under the
repository's local gauge action by the gauge transformation at their two endpoints. Closed
paths give exactly gauge-invariant Wilson loops, and the unit rectangle is the plaquette of
the actual Wilson action.

A physical loop is an axis-parallel rectangle with rational corner and rational side
lengths. At spacing `a` it becomes the lattice rectangle with corner `⌊b/a⌋` and sides
`⌊R/a⌋, ⌊T/a⌋`, whose physical size converges to the prescribed one as `a → 0`. Along any
sequence of cutoffs `(L n, a n, β n)` the joint laws of all physical loops under the actual
normalized Wilson probabilities live on the common space `PhysicalRectangle → ℝ`, which does
not depend on the cutoff. Holonomies transported to the lattice origin along axis tails live
on the compact space `PhysicalRectangle → SU2`, where gauge transformations act by
simultaneous conjugation at the base point.

Proved: exact gauge invariance of every observable and joint law; tightness of the
pushforward family from compactness of SU(2); subsequential weak limits; every weak limit of
the Wilson-loop laws is the trace image of a conjugation-invariant holonomy law supported on
the compact set of realizable values; exact invariance of the actual Wilson law, and of every
limit, under coordinate permutations; invariance of limits under physical translations that
are eventually lattice vectors (all dyadic translations along dyadic spacings). For a second
family, unrenormalized plaquette averages over regions of fixed physical size, the joint law
converges along every continuum cutoff path, but to the Dirac law at the all-ones vector:
a collapsed limit.

Not proved: convergence of the full sequence, tightness of multiplicatively renormalized
loops (reduced to an exact tail condition), invariance under other translations, rotations
outside the permutation group, reflection positivity, clustering, nontriviality, and
identification with a continuum SU(2) Yang–Mills theory. They are the named fields of `WilsonLoopConvergenceObligation`,
`LoopRenormalization.TailObligation` and `ContinuumIdentificationObligations`. The
unrenormalized loops are bounded, so their tightness costs nothing. Perturbation theory
predicts that they are suppressed by perimeter divergences as `a → 0`; that is not proved
here, and their limits are limit candidates only. No concentration of configurations near
flat ones along a cutoff path is assumed.

Downstream, `YangMillsOsterwalderSchraderInheritance` proves reflection positivity of the actual
lattice Wilson measure and, along continuum paths with spacings `2⁻ⁿ` and eventually even sides,
of every limit law on time-dyadic loops (`limit_isReflectionPositiveOn_timeDyadic`). There the full
`reflection_positive` field rests on the named hypothesis `DyadicTimeApproximable`, nontriviality
is equivalent to a uniform connected-correlation bound (`isNontrivial_limit_iff`), and the actual
cutoff laws are never time mixing (`not_isTimeMixing_law`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace JesseMath.Physics.YangMillsRenormalizedObservableLimits

open YangMillsContinuumCompactness

/-! ## 1. Lattice paths and holonomies on the actual periodic lattice -/

/-- One oriented step along a lattice direction, forward or backward. -/
structure LatticeStep where
  dir : Direction
  forward : Bool
  deriving DecidableEq

namespace LatticeStep

/-- The same edge traversed in the opposite orientation. -/
def reverse (s : LatticeStep) : LatticeStep := ⟨s.dir, !s.forward⟩

/-- Displacement of one step on the periodic lattice `(ℤ/Lℤ)⁴`. -/
def displacement (L : ℕ) : LatticeStep → Lattice4D L
  | ⟨μ, true⟩ => unitVec L μ
  | ⟨μ, false⟩ => -unitVec L μ

@[simp]
theorem displacement_forward (L : ℕ) (μ : Direction) :
    displacement L ⟨μ, true⟩ = unitVec L μ := rfl

@[simp]
theorem displacement_backward (L : ℕ) (μ : Direction) :
    displacement L ⟨μ, false⟩ = -unitVec L μ := rfl

theorem displacement_reverse (L : ℕ) (s : LatticeStep) :
    s.reverse.displacement L = -s.displacement L := by
  rcases s with ⟨μ, _ | _⟩ <;> simp [reverse]

end LatticeStep

variable {L : ℕ}

/-- The site reached after one step. -/
def stepTarget (x : Lattice4D L) (s : LatticeStep) : Lattice4D L :=
  x + s.displacement L

/-- Holonomy of one step: the link variable forward, its inverse backward. -/
def stepHolonomy (U : GaugeConfig L) (x : Lattice4D L) : LatticeStep → SU2
  | ⟨μ, true⟩ => U ⟨x, μ⟩
  | ⟨μ, false⟩ => (U ⟨x - unitVec L μ, μ⟩)⁻¹

@[simp]
theorem stepHolonomy_forward (U : GaugeConfig L) (x : Lattice4D L) (μ : Direction) :
    stepHolonomy U x ⟨μ, true⟩ = U ⟨x, μ⟩ := rfl

@[simp]
theorem stepHolonomy_backward (U : GaugeConfig L) (x : Lattice4D L) (μ : Direction) :
    stepHolonomy U x ⟨μ, false⟩ = (U ⟨x - unitVec L μ, μ⟩)⁻¹ := rfl

/-- Endpoint of a lattice path. -/
def pathTarget : Lattice4D L → List LatticeStep → Lattice4D L
  | x, [] => x
  | x, s :: p => pathTarget (stepTarget x s) p

/-- Ordered product of step holonomies along a lattice path. -/
def pathHolonomy (U : GaugeConfig L) : Lattice4D L → List LatticeStep → SU2
  | _, [] => 1
  | x, s :: p => stepHolonomy U x s * pathHolonomy U (stepTarget x s) p

@[simp]
theorem pathTarget_nil (x : Lattice4D L) : pathTarget x [] = x := rfl

@[simp]
theorem pathTarget_cons (x : Lattice4D L) (s : LatticeStep) (p : List LatticeStep) :
    pathTarget x (s :: p) = pathTarget (stepTarget x s) p := rfl

@[simp]
theorem pathHolonomy_nil (U : GaugeConfig L) (x : Lattice4D L) :
    pathHolonomy U x [] = 1 := rfl

@[simp]
theorem pathHolonomy_cons (U : GaugeConfig L) (x : Lattice4D L) (s : LatticeStep)
    (p : List LatticeStep) :
    pathHolonomy U x (s :: p) = stepHolonomy U x s * pathHolonomy U (stepTarget x s) p := rfl

theorem pathTarget_append (x : Lattice4D L) (p q : List LatticeStep) :
    pathTarget x (p ++ q) = pathTarget (pathTarget x p) q := by
  induction p generalizing x with
  | nil => rfl
  | cons s p ih => exact ih (stepTarget x s)

/-- The endpoint is the start plus the summed displacements. -/
theorem pathTarget_eq_add (x : Lattice4D L) (p : List LatticeStep) :
    pathTarget x p = x + (p.map (LatticeStep.displacement L)).sum := by
  induction p generalizing x with
  | nil => simp
  | cons s p ih => simp [ih, stepTarget, add_assoc]

theorem pathHolonomy_append (U : GaugeConfig L) (x : Lattice4D L) (p q : List LatticeStep) :
    pathHolonomy U x (p ++ q) = pathHolonomy U x p * pathHolonomy U (pathTarget x p) q := by
  induction p generalizing x with
  | nil => simp
  | cons s p ih => simp [ih, mul_assoc]

/-- Gauge covariance of one step under the repository's local gauge action. -/
theorem stepHolonomy_gaugeTransform (g : GaugeTransformation L) (U : GaugeConfig L)
    (x : Lattice4D L) (s : LatticeStep) :
    stepHolonomy (gaugeTransform g U) x s = g x * stepHolonomy U x s * (g (stepTarget x s))⁻¹ := by
  rcases s with ⟨μ, _ | _⟩
  · have hx : shift (x - unitVec L μ) μ = x := by simp [shift]
    have ht : stepTarget x ⟨μ, false⟩ = x - unitVec L μ := by
      simp [stepTarget, sub_eq_add_neg]
    rw [ht, stepHolonomy_backward, stepHolonomy_backward]
    change (g (x - unitVec L μ) * U ⟨x - unitVec L μ, μ⟩ *
      (g (shift (x - unitVec L μ) μ))⁻¹)⁻¹ = _
    rw [hx]
    group
  · rfl

/-- Gauge covariance of every lattice path: the holonomy is conjugated by the gauge
transformation at its two endpoints. -/
theorem pathHolonomy_gaugeTransform (g : GaugeTransformation L) (U : GaugeConfig L)
    (x : Lattice4D L) (p : List LatticeStep) :
    pathHolonomy (gaugeTransform g U) x p = g x * pathHolonomy U x p * (g (pathTarget x p))⁻¹ := by
  induction p generalizing x with
  | nil => simp
  | cons s p ih =>
    simp only [pathHolonomy_cons, pathTarget_cons, ih, stepHolonomy_gaugeTransform]
    group

/-- Reversal of a path: reversed order, each step reversed. -/
def reversePath (p : List LatticeStep) : List LatticeStep :=
  (p.map LatticeStep.reverse).reverse

@[simp]
theorem reversePath_nil : reversePath [] = [] := rfl

theorem reversePath_cons (s : LatticeStep) (p : List LatticeStep) :
    reversePath (s :: p) = reversePath p ++ [s.reverse] := by
  simp [reversePath]

theorem stepTarget_reverse (x : Lattice4D L) (s : LatticeStep) :
    stepTarget (stepTarget x s) s.reverse = x := by
  simp [stepTarget, LatticeStep.displacement_reverse]

theorem stepHolonomy_reverse (U : GaugeConfig L) (x : Lattice4D L) (s : LatticeStep) :
    stepHolonomy U (stepTarget x s) s.reverse = (stepHolonomy U x s)⁻¹ := by
  rcases s with ⟨μ, _ | _⟩
  · have h : x + -unitVec L μ = x - unitVec L μ := (sub_eq_add_neg _ _).symm
    simp [stepTarget, LatticeStep.reverse, h]
  · simp [stepTarget, LatticeStep.reverse]

theorem pathTarget_reversePath (x : Lattice4D L) (p : List LatticeStep) :
    pathTarget (pathTarget x p) (reversePath p) = x := by
  induction p generalizing x with
  | nil => rfl
  | cons s p ih =>
    rw [reversePath_cons, pathTarget_append]
    change pathTarget (pathTarget (pathTarget (stepTarget x s) p) (reversePath p)) [s.reverse] = x
    rw [ih (stepTarget x s)]
    exact stepTarget_reverse x s

/-- The reversed path, started at the endpoint, has the inverse holonomy. -/
theorem pathHolonomy_reversePath (U : GaugeConfig L) (x : Lattice4D L) (p : List LatticeStep) :
    pathHolonomy U (pathTarget x p) (reversePath p) = (pathHolonomy U x p)⁻¹ := by
  induction p generalizing x with
  | nil => simp
  | cons s p ih =>
    rw [reversePath_cons, pathHolonomy_append, pathTarget_cons, ih, pathTarget_reversePath]
    simp [stepHolonomy_reverse, mul_inv_rev]

/-- A lasso: go out along `tail`, run the closed `body`, return along the reversed tail. -/
theorem pathHolonomy_lasso (U : GaugeConfig L) (x : Lattice4D L) (tail body : List LatticeStep)
    (hbody : pathTarget (pathTarget x tail) body = pathTarget x tail) :
    pathHolonomy U x (tail ++ body ++ reversePath tail) =
      pathHolonomy U x tail * pathHolonomy U (pathTarget x tail) body *
        (pathHolonomy U x tail)⁻¹ := by
  rw [pathHolonomy_append, pathHolonomy_append, pathTarget_append, hbody,
    pathHolonomy_reversePath]

theorem pathTarget_lasso (x : Lattice4D L) (tail body : List LatticeStep)
    (hbody : pathTarget (pathTarget x tail) body = pathTarget x tail) :
    pathTarget x (tail ++ body ++ reversePath tail) = x := by
  rw [pathTarget_append, pathTarget_append, hbody, pathTarget_reversePath]

/-! ## 2. Wilson loops and their exact gauge invariance -/

/-- The normalized real SU(2) character `½ Re tr`. -/
def halfTraceRe (h : SU2) : ℝ := (1 / 2) * (SU2.trace h).re

theorem halfTraceRe_conj (k h : SU2) : halfTraceRe (k * h * k⁻¹) = halfTraceRe h := by
  simp only [halfTraceRe, SU2.trace_conj]

theorem halfTraceRe_mem_Icc (h : SU2) : halfTraceRe h ∈ Set.Icc (-1 : ℝ) 1 := by
  obtain ⟨h1, h2⟩ := SU2.trace_re_bounds h
  constructor <;> simp only [halfTraceRe] <;> linarith

@[continuity, fun_prop]
theorem continuous_halfTraceRe : Continuous halfTraceRe := by
  unfold halfTraceRe SU2.trace Matrix.trace
  fun_prop

/-- The Wilson loop of a lattice path started at `x`. -/
def wilsonLoop (U : GaugeConfig L) (x : Lattice4D L) (p : List LatticeStep) : ℝ :=
  halfTraceRe (pathHolonomy U x p)

/-- Exact local gauge invariance of every closed Wilson loop under the actual gauge action. -/
theorem wilsonLoop_gaugeTransform (g : GaugeTransformation L) (U : GaugeConfig L)
    {x : Lattice4D L} {p : List LatticeStep} (hp : pathTarget x p = x) :
    wilsonLoop (gaugeTransform g U) x p = wilsonLoop U x p := by
  rw [wilsonLoop, pathHolonomy_gaugeTransform, hp, halfTraceRe_conj]
  rfl

theorem continuous_stepHolonomy (x : Lattice4D L) (s : LatticeStep) :
    Continuous (fun U : GaugeConfig L => stepHolonomy U x s) := by
  rcases s with ⟨μ, _ | _⟩
  · exact (continuous_apply (⟨x - unitVec L μ, μ⟩ : Link L)).inv
  · exact continuous_apply (⟨x, μ⟩ : Link L)

theorem continuous_pathHolonomy (x : Lattice4D L) (p : List LatticeStep) :
    Continuous (fun U : GaugeConfig L => pathHolonomy U x p) := by
  induction p generalizing x with
  | nil => exact continuous_const
  | cons s p ih => exact (continuous_stepHolonomy x s).mul (ih _)

theorem continuous_wilsonLoop (x : Lattice4D L) (p : List LatticeStep) :
    Continuous (fun U : GaugeConfig L => wilsonLoop U x p) :=
  continuous_halfTraceRe.comp (continuous_pathHolonomy x p)

/-! ## 3. Rectangular loops; the unit rectangle is the actual plaquette -/

/-- The `r × t` rectangle in the `(μ, ν)` plane: `r` steps along `μ`, `t` along `ν`, back. -/
def rectangleSteps (μ ν : Direction) (r t : ℕ) : List LatticeStep :=
  List.replicate r ⟨μ, true⟩ ++ List.replicate t ⟨ν, true⟩ ++
    List.replicate r ⟨μ, false⟩ ++ List.replicate t ⟨ν, false⟩

/-- Every rectangle closes on the periodic lattice, for all side lengths and every `L`. -/
theorem pathTarget_rectangleSteps (x : Lattice4D L) (μ ν : Direction) (r t : ℕ) :
    pathTarget x (rectangleSteps μ ν r t) = x := by
  rw [pathTarget_eq_add]
  simp only [rectangleSteps, List.map_append, List.map_replicate, List.sum_append,
    List.sum_replicate, LatticeStep.displacement_forward, LatticeStep.displacement_backward,
    smul_neg]
  abel

theorem rectangleSteps_one_one (μ ν : Direction) :
    rectangleSteps μ ν 1 1 = [⟨μ, true⟩, ⟨ν, true⟩, ⟨μ, false⟩, ⟨ν, false⟩] := rfl

/-- The `1 × 1` rectangle based at a plaquette corner has exactly the repository's plaquette
holonomy. -/
theorem pathHolonomy_rectangleSteps_one_one (U : GaugeConfig L) (p : Plaquette L) :
    pathHolonomy U p.x (rectangleSteps p.μ p.ν 1 1) = plaquetteHolonomy U p := by
  have h1 : p.x + unitVec L p.μ + unitVec L p.ν - unitVec L p.μ = shift p.x p.ν := by
    simp only [shift]
    abel
  have h2 : p.x + unitVec L p.μ + unitVec L p.ν + -unitVec L p.μ - unitVec L p.ν = p.x := by
    abel
  rw [rectangleSteps_one_one]
  simp only [pathHolonomy_cons, pathHolonomy_nil, stepTarget, stepHolonomy_forward,
    stepHolonomy_backward, LatticeStep.displacement_forward, LatticeStep.displacement_backward,
    mul_one]
  simp only [h1, h2, plaquetteHolonomy, shift, mul_assoc]

/-- The unit Wilson loop is `1 - s_p`, with `s_p` the actual single-plaquette Wilson action. -/
theorem wilsonLoop_rectangleSteps_one_one (U : GaugeConfig L) (p : Plaquette L) :
    wilsonLoop U p.x (rectangleSteps p.μ p.ν 1 1) = 1 - plaquetteAction U p := by
  rw [wilsonLoop, pathHolonomy_rectangleSteps_one_one, halfTraceRe, plaquetteAction]
  ring

/-! ## 4. Loops of fixed physical size on the lattice of spacing `a` -/

/-- An axis-parallel rectangular loop in physical units: rational corner `base`, plane
`(μ, ν)` with `μ < ν`, and positive rational physical side lengths. -/
structure PhysicalRectangle where
  base : Fin 4 → ℚ
  μ : Direction
  ν : Direction
  plane : μ < ν
  sideμ : ℚ
  sideν : ℚ
  sideμ_pos : 0 < sideμ
  sideν_pos : 0 < sideν

instance : Countable PhysicalRectangle := by
  have hinj : Function.Injective (fun ℓ : PhysicalRectangle =>
      (ℓ.base, ℓ.μ, ℓ.ν, ℓ.sideμ, ℓ.sideν)) := by
    rintro ⟨b, μ, ν, h, R, T, hR, hT⟩ ⟨b', μ', ν', h', R', T', hR', hT'⟩ hEq
    simp only [Prod.mk.injEq] at hEq
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hEq
    rfl
  exact hinj.countable

/-- Reduction of an integer site to the periodic lattice of side `L`. -/
def latticeSite (L : ℕ) (m : Fin 4 → ℤ) : Lattice4D L := fun i => (m i : ZMod L)

namespace PhysicalRectangle

/-- Lattice corner at spacing `a`: the integer part of the physical corner in units of `a`. -/
def latticeBase (ℓ : PhysicalRectangle) (a : ℝ) : Fin 4 → ℤ :=
  fun i => ⌊(ℓ.base i : ℝ) / a⌋

/-- Number of lattice links along `μ` at spacing `a`. -/
def stepsμ (ℓ : PhysicalRectangle) (a : ℝ) : ℕ := ⌊(ℓ.sideμ : ℝ) / a⌋₊

/-- Number of lattice links along `ν` at spacing `a`. -/
def stepsν (ℓ : PhysicalRectangle) (a : ℝ) : ℕ := ⌊(ℓ.sideν : ℝ) / a⌋₊

/-- The lattice rectangle representing `ℓ` at spacing `a`. -/
def latticeLoop (ℓ : PhysicalRectangle) (a : ℝ) : List LatticeStep :=
  rectangleSteps ℓ.μ ℓ.ν (ℓ.stepsμ a) (ℓ.stepsν a)

end PhysicalRectangle

/-- Physical side discretization error is at most one lattice spacing. -/
theorem physical_side_discretization {R a : ℝ} (hR : 0 ≤ R) (ha : 0 < a) :
    a * (⌊R / a⌋₊ : ℝ) ≤ R ∧ R < a * (⌊R / a⌋₊ : ℝ) + a := by
  have h0 : 0 ≤ R / a := div_nonneg hR ha.le
  have hle : (⌊R / a⌋₊ : ℝ) ≤ R / a := Nat.floor_le h0
  have hlt : R / a < (⌊R / a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  constructor
  · calc a * (⌊R / a⌋₊ : ℝ) ≤ a * (R / a) := mul_le_mul_of_nonneg_left hle ha.le
      _ = R := by field_simp
  · calc R = a * (R / a) := by field_simp
      _ < a * ((⌊R / a⌋₊ : ℝ) + 1) := mul_lt_mul_of_pos_left hlt ha
      _ = a * (⌊R / a⌋₊ : ℝ) + a := by ring

/-- Physical corner discretization error is at most one lattice spacing. -/
theorem physical_base_discretization (b : ℝ) {a : ℝ} (ha : 0 < a) :
    a * (⌊b / a⌋ : ℝ) ≤ b ∧ b < a * (⌊b / a⌋ : ℝ) + a := by
  have hle : (⌊b / a⌋ : ℝ) ≤ b / a := Int.floor_le _
  have hlt : b / a < (⌊b / a⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  constructor
  · calc a * (⌊b / a⌋ : ℝ) ≤ a * (b / a) := mul_le_mul_of_nonneg_left hle ha.le
      _ = b := by field_simp
  · calc b = a * (b / a) := by field_simp
      _ < a * ((⌊b / a⌋ : ℝ) + 1) := mul_lt_mul_of_pos_left hlt ha
      _ = a * (⌊b / a⌋ : ℝ) + a := by ring

/-- As the spacing tends to zero, the lattice loop has the prescribed physical side lengths
and corner in the limit: `a·r → R`, `a·t → T`, `a·m → b`. This is the precise sense in
which the loops below have fixed physical size. -/
theorem physicalRectangle_scale_consistency (ℓ : PhysicalRectangle) {a : ℕ → ℝ}
    (ha : ∀ n, 0 < a n) (ha0 : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => a n * (ℓ.stepsμ (a n) : ℝ)) atTop (𝓝 (ℓ.sideμ : ℝ)) ∧
    Tendsto (fun n => a n * (ℓ.stepsν (a n) : ℝ)) atTop (𝓝 (ℓ.sideν : ℝ)) ∧
    ∀ i, Tendsto (fun n => a n * (ℓ.latticeBase (a n) i : ℝ)) atTop (𝓝 (ℓ.base i : ℝ)) := by
  have hside : ∀ R : ℝ, 0 ≤ R →
      Tendsto (fun n => a n * (⌊R / a n⌋₊ : ℝ)) atTop (𝓝 R) := by
    intro R hR
    have hlo : Tendsto (fun n => R - a n) atTop (𝓝 R) := by
      simpa using tendsto_const_nhds.sub ha0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds ?_ ?_
    · intro n
      have := (physical_side_discretization hR (ha n)).2
      simp only
      linarith
    · intro n
      exact (physical_side_discretization hR (ha n)).1
  refine ⟨hside _ (by exact_mod_cast ℓ.sideμ_pos.le), hside _ (by exact_mod_cast ℓ.sideν_pos.le),
    fun i => ?_⟩
  have hlo : Tendsto (fun n => (ℓ.base i : ℝ) - a n) atTop (𝓝 (ℓ.base i : ℝ)) := by
    simpa using tendsto_const_nhds.sub ha0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds ?_ ?_
  · intro n
    have := (physical_base_discretization (ℓ.base i : ℝ) (ha n)).2
    simp only [PhysicalRectangle.latticeBase]
    linarith
  · intro n
    exact (physical_base_discretization (ℓ.base i : ℝ) (ha n)).1

/-! ## 5. Based tails, lassos and the physical observables -/

/-- `|m|` steps along `μ`, forward if `0 ≤ m` and backward otherwise. -/
def straightSteps (μ : Direction) (m : ℤ) : List LatticeStep :=
  List.replicate m.natAbs ⟨μ, decide (0 ≤ m)⟩

theorem displacement_sum_straightSteps (μ : Direction) (m : ℤ) :
    ((straightSteps μ m).map (LatticeStep.displacement L)).sum = m • unitVec L μ := by
  unfold straightSteps
  rw [List.map_replicate, List.sum_replicate]
  rcases le_or_gt 0 m with hm | hm
  · have hd : decide (0 ≤ m) = true := decide_eq_true hm
    rw [hd, LatticeStep.displacement_forward]
    have hm' : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg hm
    rw [← natCast_zsmul, hm']
  · have hd : decide (0 ≤ m) = false := decide_eq_false (not_le.mpr hm)
    rw [hd, LatticeStep.displacement_backward, smul_neg]
    have hm' : m = -(m.natAbs : ℤ) := by omega
    conv_rhs => rw [hm']
    rw [neg_zsmul, natCast_zsmul]

/-- Axis-ordered tail from a site to the integer displacement `m`. -/
def tailSteps (m : Fin 4 → ℤ) : List LatticeStep :=
  straightSteps 0 (m 0) ++ straightSteps 1 (m 1) ++ straightSteps 2 (m 2) ++ straightSteps 3 (m 3)

theorem pathTarget_tailSteps (x : Lattice4D L) (m : Fin 4 → ℤ) :
    pathTarget x (tailSteps m) = x + latticeSite L m := by
  rw [pathTarget_eq_add]
  congr 1
  simp only [tailSteps, List.map_append, List.sum_append, displacement_sum_straightSteps]
  funext i
  fin_cases i <;> simp [latticeSite, unitVec]

/-- The lattice lasso of a physical rectangle at spacing `a`, based at the lattice origin. -/
def PhysicalRectangle.lassoLoop (ℓ : PhysicalRectangle) (a : ℝ) : List LatticeStep :=
  tailSteps (ℓ.latticeBase a) ++ ℓ.latticeLoop a ++ reversePath (tailSteps (ℓ.latticeBase a))

/-- The physical-scale Wilson loop on the lattice of side `L` and spacing `a`: an actual
continuous function of the lattice configuration. -/
def physicalWilsonLoop (L : ℕ) (a : ℝ) (ℓ : PhysicalRectangle) (U : GaugeConfig L) : ℝ :=
  wilsonLoop U (latticeSite L (ℓ.latticeBase a)) (ℓ.latticeLoop a)

/-- The holonomy of the physical loop, transported to the lattice origin along its tail. -/
def physicalBasedHolonomy (L : ℕ) (a : ℝ) (ℓ : PhysicalRectangle) (U : GaugeConfig L) : SU2 :=
  pathHolonomy U 0 (ℓ.lassoLoop a)

theorem pathTarget_latticeLoop (ℓ : PhysicalRectangle) (a : ℝ) (x : Lattice4D L) :
    pathTarget x (ℓ.latticeLoop a) = x :=
  pathTarget_rectangleSteps x _ _ _ _

theorem pathTarget_zero_tailSteps (m : Fin 4 → ℤ) :
    pathTarget (0 : Lattice4D L) (tailSteps m) = latticeSite L m := by
  rw [pathTarget_tailSteps, zero_add]

/-- Gauge invariance of each physical Wilson loop under the actual local gauge action. -/
theorem physicalWilsonLoop_gaugeTransform (a : ℝ) (ℓ : PhysicalRectangle)
    (g : GaugeTransformation L) (U : GaugeConfig L) :
    physicalWilsonLoop L a ℓ (gaugeTransform g U) = physicalWilsonLoop L a ℓ U :=
  wilsonLoop_gaugeTransform g U (pathTarget_latticeLoop ℓ a _)

/-- All local gauge transformations act on the based holonomy only through their value at
the base point, by conjugation. -/
theorem physicalBasedHolonomy_gaugeTransform (a : ℝ) (ℓ : PhysicalRectangle)
    (g : GaugeTransformation L) (U : GaugeConfig L) :
    physicalBasedHolonomy L a ℓ (gaugeTransform g U) =
      g 0 * physicalBasedHolonomy L a ℓ U * (g 0)⁻¹ := by
  unfold physicalBasedHolonomy
  rw [pathHolonomy_gaugeTransform]
  have hclosed : pathTarget (0 : Lattice4D L) (ℓ.lassoLoop a) = 0 :=
    pathTarget_lasso 0 _ _ (pathTarget_latticeLoop ℓ a _)
  rw [hclosed]

/-- The physical Wilson loop is the gauge-invariant trace of the based holonomy. -/
theorem physicalWilsonLoop_eq_halfTraceRe (a : ℝ) (ℓ : PhysicalRectangle) (U : GaugeConfig L) :
    physicalWilsonLoop L a ℓ U = halfTraceRe (physicalBasedHolonomy L a ℓ U) := by
  unfold physicalBasedHolonomy PhysicalRectangle.lassoLoop
  rw [pathHolonomy_lasso U 0 _ _ (pathTarget_latticeLoop ℓ a _), halfTraceRe_conj,
    pathTarget_zero_tailSteps]
  rfl

theorem continuous_physicalWilsonLoop (L : ℕ) (a : ℝ) (ℓ : PhysicalRectangle) :
    Continuous (physicalWilsonLoop L a ℓ) :=
  continuous_wilsonLoop _ _

theorem continuous_physicalBasedHolonomy (L : ℕ) (a : ℝ) (ℓ : PhysicalRectangle) :
    Continuous (physicalBasedHolonomy L a ℓ) :=
  continuous_pathHolonomy _ _

/-- When the spacing resolves each side by a single link, the physical Wilson loop is
`1 - s_p` for the actual plaquette at the lattice corner. -/
theorem physicalWilsonLoop_eq_one_sub_plaquetteAction (a : ℝ) (ℓ : PhysicalRectangle)
    (U : GaugeConfig L) (hμ : ℓ.stepsμ a = 1) (hν : ℓ.stepsν a = 1) :
    physicalWilsonLoop L a ℓ U =
      1 - plaquetteAction U ⟨latticeSite L (ℓ.latticeBase a), ℓ.μ, ℓ.ν, ℓ.plane⟩ := by
  unfold physicalWilsonLoop PhysicalRectangle.latticeLoop
  rw [hμ, hν]
  exact wilsonLoop_rectangleSteps_one_one U ⟨latticeSite L (ℓ.latticeBase a), ℓ.μ, ℓ.ν, ℓ.plane⟩

/-! ## 6. The common spaces of joint laws -/

/-- Common space for the joint values of all physical Wilson loops. It does not depend on
the lattice side, the spacing or the coupling. -/
abbrev WilsonLoopSpace := PhysicalRectangle → ℝ

/-- Common compact space for all based physical holonomies. -/
abbrev BasedHolonomySpace := PhysicalRectangle → SU2

/-- All physical Wilson loops of one lattice configuration. -/
def wilsonLoopVector (L : ℕ) (a : ℝ) (U : GaugeConfig L) : WilsonLoopSpace :=
  fun ℓ => physicalWilsonLoop L a ℓ U

/-- All based physical holonomies of one lattice configuration. -/
def basedHolonomyVector (L : ℕ) (a : ℝ) (U : GaugeConfig L) : BasedHolonomySpace :=
  fun ℓ => physicalBasedHolonomy L a ℓ U

/-- Coordinatewise `½ Re tr`: the gauge-invariant reduction of based holonomies. -/
def halfTraceVector (h : BasedHolonomySpace) : WilsonLoopSpace := fun ℓ => halfTraceRe (h ℓ)

/-- Simultaneous conjugation: the action of the gauge group at the base point. -/
def conjugateAll (k : SU2) (h : BasedHolonomySpace) : BasedHolonomySpace :=
  fun ℓ => k * h ℓ * k⁻¹

theorem continuous_wilsonLoopVector (L : ℕ) (a : ℝ) : Continuous (wilsonLoopVector L a) :=
  continuous_pi fun ℓ => continuous_physicalWilsonLoop L a ℓ

theorem continuous_basedHolonomyVector (L : ℕ) (a : ℝ) :
    Continuous (basedHolonomyVector L a) :=
  continuous_pi fun ℓ => continuous_physicalBasedHolonomy L a ℓ

theorem continuous_halfTraceVector : Continuous halfTraceVector :=
  continuous_pi fun ℓ => continuous_halfTraceRe.comp (continuous_apply ℓ)

theorem continuous_conjugateAll (k : SU2) : Continuous (conjugateAll k) :=
  continuous_pi fun ℓ => (continuous_const.mul (continuous_apply ℓ)).mul continuous_const

theorem wilsonLoopVector_eq_halfTraceVector (L : ℕ) (a : ℝ) (U : GaugeConfig L) :
    wilsonLoopVector L a U = halfTraceVector (basedHolonomyVector L a U) :=
  funext fun ℓ => physicalWilsonLoop_eq_halfTraceRe a ℓ U

theorem wilsonLoopVector_gaugeTransform (a : ℝ) (g : GaugeTransformation L)
    (U : GaugeConfig L) :
    wilsonLoopVector L a (gaugeTransform g U) = wilsonLoopVector L a U :=
  funext fun ℓ => physicalWilsonLoop_gaugeTransform a ℓ g U

theorem basedHolonomyVector_gaugeTransform (a : ℝ) (g : GaugeTransformation L)
    (U : GaugeConfig L) :
    basedHolonomyVector L a (gaugeTransform g U) =
      conjugateAll (g 0) (basedHolonomyVector L a U) :=
  funext fun ℓ => physicalBasedHolonomy_gaugeTransform a ℓ g U

theorem halfTraceVector_conjugateAll (k : SU2) (h : BasedHolonomySpace) :
    halfTraceVector (conjugateAll k h) = halfTraceVector h :=
  funext fun ℓ => halfTraceRe_conj k (h ℓ)

/-- The jointly realizable Wilson-loop values: the image of the compact holonomy space. -/
def wilsonLoopRange : Set WilsonLoopSpace := Set.range halfTraceVector

/-- Compactness of the realizable values, from compactness of `SU2` in the repository. -/
theorem isCompact_wilsonLoopRange : IsCompact wilsonLoopRange :=
  isCompact_range continuous_halfTraceVector

theorem wilsonLoopRange_subset_Icc :
    wilsonLoopRange ⊆ Set.pi Set.univ (fun _ => Set.Icc (-1 : ℝ) 1) := by
  rintro _ ⟨h, rfl⟩ ℓ _
  exact halfTraceRe_mem_Icc (h ℓ)

theorem measurableSet_wilsonLoopRange_compl : MeasurableSet wilsonLoopRangeᶜ :=
  isCompact_wilsonLoopRange.isClosed.measurableSet.compl

theorem wilsonLoopVector_mem_range (L : ℕ) (a : ℝ) (U : GaugeConfig L) :
    wilsonLoopVector L a U ∈ wilsonLoopRange :=
  ⟨basedHolonomyVector L a U, (wilsonLoopVector_eq_halfTraceVector L a U).symm⟩

/-- For every configuration law `Q`, not only the Wilson law, a local gauge transformation of
`Q` leaves the joint law of the physical Wilson loops unchanged. -/
theorem map_wilsonLoopVector_gaugeTransform [NeZero L] (a : ℝ)
    (Q : ProbabilityMeasure (GaugeConfig L)) (g : GaugeTransformation L) :
    (Q.map (gaugeTransform g)).map (wilsonLoopVector L a) = Q.map (wilsonLoopVector L a) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (continuous_wilsonLoopVector L a).measurable
    (continuous_gaugeTransform g).measurable]
  congr 1
  funext U
  exact wilsonLoopVector_gaugeTransform a g U

/-- For every configuration law `Q`, a local gauge transformation acts on the joint law of
based holonomies exactly by simultaneous conjugation with its value at the base point. -/
theorem map_basedHolonomyVector_gaugeTransform [NeZero L] (a : ℝ)
    (Q : ProbabilityMeasure (GaugeConfig L)) (g : GaugeTransformation L) :
    (Q.map (gaugeTransform g)).map (basedHolonomyVector L a) =
      (Q.map (basedHolonomyVector L a)).map (conjugateAll (g 0)) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (continuous_basedHolonomyVector L a).measurable
    (continuous_gaugeTransform g).measurable,
    Measure.map_map (continuous_conjugateAll (g 0)).measurable
      (continuous_basedHolonomyVector L a).measurable]
  congr 1
  funext U
  exact basedHolonomyVector_gaugeTransform a g U

/-- A law of based holonomies is gauge invariant when it is invariant under the residual
gauge action at the base point. -/
def IsGaugeInvariantHolonomyLaw (μ : ProbabilityMeasure BasedHolonomySpace) : Prop :=
  ∀ k : SU2, μ.map (conjugateAll k) = μ

/-- Gauge-invariant laws form a closed set for convergence in distribution. -/
theorem isClosed_setOf_isGaugeInvariantHolonomyLaw :
    IsClosed {μ : ProbabilityMeasure BasedHolonomySpace | IsGaugeInvariantHolonomyLaw μ} := by
  simp only [IsGaugeInvariantHolonomyLaw, Set.ofPred_forall]
  exact isClosed_iInter fun k =>
    isClosed_eq (ProbabilityMeasure.continuous_map (continuous_conjugateAll k)) continuous_id

theorem isGaugeInvariant_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {μs : ι → ProbabilityMeasure BasedHolonomySpace} {μ : ProbabilityMeasure BasedHolonomySpace}
    (h : Tendsto μs l (𝓝 μ)) (hμs : ∀ᶠ i in l, IsGaugeInvariantHolonomyLaw (μs i)) :
    IsGaugeInvariantHolonomyLaw μ :=
  isClosed_setOf_isGaugeInvariantHolonomyLaw.mem_of_tendsto h hμs

/-! ## 7. Cutoff paths and the pushforward family -/

/-- A sequence of cutoffs: lattice side `L n`, physical spacing `a n > 0`, and bare coupling
`β n ≥ 0`. No relation between them is assumed; every theorem in this section holds for every
such sequence, in particular for any asymptotically free trajectory. -/
structure CutoffPath where
  side : ℕ → ℕ
  side_pos : ∀ n, 0 < side n
  spacing : ℕ → ℝ
  spacing_pos : ∀ n, 0 < spacing n
  coupling : ℕ → ℝ
  coupling_nonneg : ∀ n, 0 ≤ coupling n

instance (P : CutoffPath) (n : ℕ) : NeZero (P.side n) := ⟨(P.side_pos n).ne'⟩

namespace CutoffPath

variable (P : CutoffPath)

/-- The actual normalized Wilson probability on the `n`-th lattice. -/
def configLaw (n : ℕ) : ProbabilityMeasure (GaugeConfig (P.side n)) :=
  wilsonProbability (P.side n) (P.coupling n) (P.coupling_nonneg n)

/-- Joint law of all physical Wilson loops at the `n`-th cutoff, on the common space. -/
def wilsonLoopLaw (n : ℕ) : ProbabilityMeasure WilsonLoopSpace :=
  (P.configLaw n).map (wilsonLoopVector (P.side n) (P.spacing n))

/-- Joint law of all based physical holonomies at the `n`-th cutoff, on the common space. -/
def basedHolonomyLaw (n : ℕ) : ProbabilityMeasure BasedHolonomySpace :=
  (P.configLaw n).map (basedHolonomyVector (P.side n) (P.spacing n))

theorem wilsonLoopLaw_eq_map_halfTraceVector (n : ℕ) :
    P.wilsonLoopLaw n = (P.basedHolonomyLaw n).map halfTraceVector := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [wilsonLoopLaw, basedHolonomyLaw, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map continuous_halfTraceVector.measurable
    (continuous_basedHolonomyVector _ _).measurable]
  congr 1
  funext U
  exact wilsonLoopVector_eq_halfTraceVector _ _ U

/-- Bounded continuous test functions of the joint law are actual normalized Wilson
expectations on the `n`-th lattice. -/
theorem integral_wilsonLoopLaw (n : ℕ) (F : WilsonLoopSpace →ᵇ ℝ) :
    ∫ w, F w ∂(P.wilsonLoopLaw n : Measure WilsonLoopSpace) =
      wilsonExpectation (gaugeHaarMeasure (P.side n)) (P.coupling n)
        (fun U => F (wilsonLoopVector (P.side n) (P.spacing n) U)) := by
  simp only [wilsonLoopLaw, ProbabilityMeasure.toMeasure_map]
  rw [integral_map (continuous_wilsonLoopVector _ _).aemeasurable
    F.continuous.aestronglyMeasurable]
  exact wilsonProbability_integral _ _ _ _

/-- Exact gauge invariance of each joint law: replacing the Wilson law by its image under
any local gauge transformation leaves the joint Wilson-loop law unchanged. -/
theorem wilsonLoopLaw_gauge_invariant (n : ℕ) (g : GaugeTransformation (P.side n)) :
    ((P.configLaw n).map (gaugeTransform g)).map (wilsonLoopVector (P.side n) (P.spacing n)) =
      P.wilsonLoopLaw n :=
  map_wilsonLoopVector_gaugeTransform _ _ g

/-- Each based-holonomy law is gauge invariant, from the proved local gauge invariance of
the actual Wilson probability. -/
theorem basedHolonomyLaw_isGaugeInvariant (n : ℕ) :
    IsGaugeInvariantHolonomyLaw (P.basedHolonomyLaw n) := by
  intro k
  have hg := wilsonProbability_gauge_invariant (P.side n) (P.coupling n) (P.coupling_nonneg n)
    (fun _ => k)
  have h : ((P.configLaw n).map (gaugeTransform (fun _ => k))).map
      (basedHolonomyVector (P.side n) (P.spacing n)) =
      ((P.configLaw n).map (basedHolonomyVector (P.side n) (P.spacing n))).map
        (conjugateAll k) :=
    map_basedHolonomyVector_gaugeTransform (P.spacing n) (P.configLaw n) (fun _ => k)
  rw [basedHolonomyLaw, ← h]
  unfold configLaw
  rw [hg]

/-- Tightness of the pushforward family on the common space. The compact set is the image of
the compact space of based holonomies; no uniformity in volume, spacing or coupling is
assumed or needed for these bounded unrenormalized observables. -/
theorem wilsonLoopLaw_isTight :
    IsTightMeasureSet {((μ : ProbabilityMeasure WilsonLoopSpace) : Measure WilsonLoopSpace) |
      μ ∈ Set.range P.wilsonLoopLaw} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε _
  refine ⟨wilsonLoopRange, isCompact_wilsonLoopRange, ?_⟩
  rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
  rw [wilsonLoopLaw, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (continuous_wilsonLoopVector _ _).measurable
      measurableSet_wilsonLoopRange_compl]
  have hempty : wilsonLoopVector (P.side n) (P.spacing n) ⁻¹' wilsonLoopRangeᶜ = ∅ := by
    ext U
    simp [wilsonLoopVector_mem_range]
  rw [hempty, measure_empty]
  exact zero_le

theorem map_halfTraceVector_range_compl (μ : ProbabilityMeasure BasedHolonomySpace) :
    (μ.map halfTraceVector : Measure WilsonLoopSpace) wilsonLoopRangeᶜ = 0 := by
  rw [ProbabilityMeasure.toMeasure_map,
    Measure.map_apply continuous_halfTraceVector.measurable measurableSet_wilsonLoopRange_compl]
  have hempty : halfTraceVector ⁻¹' wilsonLoopRangeᶜ = ∅ := by
    ext h
    simp [wilsonLoopRange]
  rw [hempty, measure_empty]

/-- Subsequential limits exist along every cutoff path. One subsequence serves the based
holonomies and all bounded continuous functions of the Wilson loops; the holonomy limit is a
gauge-invariant law; the Wilson-loop limit is its gauge-invariant reduction and is supported
on the compact realizable set. This is subsequential compactness, not convergence. -/
theorem exists_subsequential_limit :
    ∃ (φ : ℕ → ℕ) (μ : ProbabilityMeasure BasedHolonomySpace), StrictMono φ ∧
      Tendsto (fun n => P.basedHolonomyLaw (φ n)) atTop (𝓝 μ) ∧
      Tendsto (fun n => P.wilsonLoopLaw (φ n)) atTop (𝓝 (μ.map halfTraceVector)) ∧
      IsGaugeInvariantHolonomyLaw μ ∧
      (μ.map halfTraceVector : Measure WilsonLoopSpace) wilsonLoopRangeᶜ = 0 ∧
      ∀ F : WilsonLoopSpace →ᵇ ℝ,
        Tendsto (fun n => wilsonExpectation (gaugeHaarMeasure (P.side (φ n))) (P.coupling (φ n))
          (fun U => F (wilsonLoopVector (P.side (φ n)) (P.spacing (φ n)) U))) atTop
          (𝓝 (∫ w, F w ∂(μ.map halfTraceVector : Measure WilsonLoopSpace))) := by
  obtain ⟨μ, φ, hφ, hμ⟩ := CompactSpace.tendsto_subseq P.basedHolonomyLaw
  have hW : Tendsto (fun n => P.wilsonLoopLaw (φ n)) atTop (𝓝 (μ.map halfTraceVector)) := by
    have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hμ
      continuous_halfTraceVector
    simpa only [Function.comp_apply, wilsonLoopLaw_eq_map_halfTraceVector] using h
  refine ⟨φ, μ, hφ, hμ, hW, isGaugeInvariant_of_tendsto hμ
    (Eventually.of_forall fun n => P.basedHolonomyLaw_isGaugeInvariant (φ n)),
    map_halfTraceVector_range_compl μ, fun F => ?_⟩
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hW) F
  simpa only [integral_wilsonLoopLaw] using h

/-- Every weak limit of the joint Wilson-loop laws, along any sequence of cutoffs, is the
gauge-invariant reduction of a gauge-invariant law of based holonomies, and is supported on
the compact realizable set. -/
theorem wilsonLoopLaw_limit_isGaugeInvariantReduction (φ : ℕ → ℕ)
    (ν : ProbabilityMeasure WilsonLoopSpace)
    (hν : Tendsto (fun n => P.wilsonLoopLaw (φ n)) atTop (𝓝 ν)) :
    ∃ μ : ProbabilityMeasure BasedHolonomySpace,
      IsGaugeInvariantHolonomyLaw μ ∧ ν = μ.map halfTraceVector ∧
      (ν : Measure WilsonLoopSpace) wilsonLoopRangeᶜ = 0 := by
  obtain ⟨μ, ψ, hψ, hμ⟩ := CompactSpace.tendsto_subseq (fun n => P.basedHolonomyLaw (φ n))
  have h1 : Tendsto (fun n => P.wilsonLoopLaw (φ (ψ n))) atTop (𝓝 (μ.map halfTraceVector)) := by
    have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hμ
      continuous_halfTraceVector
    simpa only [Function.comp_apply, wilsonLoopLaw_eq_map_halfTraceVector] using h
  have h2 : Tendsto (fun n => P.wilsonLoopLaw (φ (ψ n))) atTop (𝓝 ν) :=
    hν.comp hψ.tendsto_atTop
  have hνμ : ν = μ.map halfTraceVector := tendsto_nhds_unique h2 h1
  refine ⟨μ, isGaugeInvariant_of_tendsto hμ
    (Eventually.of_forall fun n => P.basedHolonomyLaw_isGaugeInvariant (φ (ψ n))), hνμ, ?_⟩
  rw [hνμ]
  exact map_halfTraceVector_range_compl μ

end CutoffPath

/-! ## 8. Renormalized loops: the exact input missing for their tightness -/

/-- Uniform per-loop tails of a set of laws on the common space. -/
def UniformLoopTails (S : Set (Measure WilsonLoopSpace)) : Prop :=
  ∀ ℓ : PhysicalRectangle, ∀ ε : ℝ≥0∞, 0 < ε → ∃ C : ℝ, ∀ μ ∈ S, μ {w | C < |w ℓ|} ≤ ε

/-- On the countable product of loop coordinates, tightness is equivalent to uniform tails of
each single loop. Neither direction uses boundedness of the observables. -/
theorem isTightMeasureSet_iff_uniformLoopTails (S : Set (Measure WilsonLoopSpace)) :
    IsTightMeasureSet S ↔ UniformLoopTails S := by
  constructor
  · intro hS ℓ ε hε
    obtain ⟨K, hK, hKS⟩ := (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hS) ε hε
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := fun w : WilsonLoopSpace => w ℓ)
      (continuous_apply ℓ).continuousOn
    refine ⟨C, fun μ hμ => le_trans (measure_mono ?_) (hKS μ hμ)⟩
    intro w hw hwK
    have hb := hC w hwK
    rw [Real.norm_eq_abs] at hb
    exact (not_lt.mpr hb) hw
  · intro hT
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' PhysicalRectangle
    choose C hC using fun ℓ => hT ℓ (δ ℓ) (by exact_mod_cast hδpos ℓ)
    refine ⟨Set.pi Set.univ (fun ℓ => Set.Icc (-C ℓ) (C ℓ)),
      isCompact_univ_pi fun ℓ => isCompact_Icc, fun μ hμ => ?_⟩
    calc μ (Set.pi Set.univ (fun ℓ => Set.Icc (-C ℓ) (C ℓ)))ᶜ
        ≤ μ (⋃ ℓ, {w : WilsonLoopSpace | C ℓ < |w ℓ|}) := by
          apply measure_mono
          intro w hw
          simp only [Set.mem_compl_iff, Set.mem_pi, Set.mem_univ, true_implies,
            not_forall] at hw
          obtain ⟨ℓ, hℓ⟩ := hw
          refine Set.mem_iUnion.mpr ⟨ℓ, ?_⟩
          by_contra hle
          exact hℓ (abs_le.mp (not_lt.mp hle))
      _ ≤ ∑' ℓ, μ {w : WilsonLoopSpace | C ℓ < |w ℓ|} := measure_iUnion_le _
      _ ≤ ∑' ℓ, (δ ℓ : ℝ≥0∞) := ENNReal.tsum_le_tsum fun ℓ => hC ℓ μ hμ
      _ ≤ ε := hδsum.le

/-- Multiplicative renormalization constants, one for each cutoff and physical loop. Only
positivity is assumed. The constants expected for four-dimensional Wilson loops (perimeter
and corner divergences) are unbounded along a continuum path. -/
structure LoopRenormalization (P : CutoffPath) where
  factor : ℕ → PhysicalRectangle → ℝ
  factor_pos : ∀ n ℓ, 0 < factor n ℓ

namespace LoopRenormalization

variable {P : CutoffPath} (Z : LoopRenormalization P)

/-- Coordinatewise multiplication by the renormalization constants at cutoff `n`. -/
def rescale (n : ℕ) (w : WilsonLoopSpace) : WilsonLoopSpace := fun ℓ => Z.factor n ℓ * w ℓ

theorem continuous_rescale (n : ℕ) : Continuous (Z.rescale n) :=
  continuous_pi fun ℓ => continuous_const.mul (continuous_apply ℓ)

/-- The renormalized physical Wilson loops at cutoff `n`, as functions of the configuration. -/
def renormalizedVector (n : ℕ) (U : GaugeConfig (P.side n)) : WilsonLoopSpace :=
  Z.rescale n (wilsonLoopVector (P.side n) (P.spacing n) U)

/-- Each renormalized loop is exactly gauge invariant. -/
theorem renormalizedVector_gaugeTransform (n : ℕ) (g : GaugeTransformation (P.side n))
    (U : GaugeConfig (P.side n)) :
    Z.renormalizedVector n (gaugeTransform g U) = Z.renormalizedVector n U := by
  simp only [renormalizedVector, wilsonLoopVector_gaugeTransform]

/-- Joint law of the renormalized loops at cutoff `n`, on the common space. -/
def law (n : ℕ) : ProbabilityMeasure WilsonLoopSpace := (P.wilsonLoopLaw n).map (Z.rescale n)

/-- Exact gauge invariance of each renormalized joint law. -/
theorem law_gauge_invariant (n : ℕ) (g : GaugeTransformation (P.side n)) :
    (((P.configLaw n).map (gaugeTransform g)).map (wilsonLoopVector (P.side n) (P.spacing n))).map
      (Z.rescale n) = Z.law n := by
  rw [P.wilsonLoopLaw_gauge_invariant n g]
  rfl

theorem law_eq_map_renormalizedVector (n : ℕ) :
    Z.law n = (P.configLaw n).map (Z.renormalizedVector n) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [law, CutoffPath.wilsonLoopLaw, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (Z.continuous_rescale n).measurable
    (continuous_wilsonLoopVector _ _).measurable]
  rfl

/-- The named input that compactness does not supply for renormalized loops: uniform tails
of every renormalized loop along the cutoff path. -/
def TailObligation : Prop :=
  UniformLoopTails {((μ : ProbabilityMeasure WilsonLoopSpace) : Measure WilsonLoopSpace) |
    μ ∈ Set.range Z.law}

/-- The tail obligation is exactly tightness of the renormalized family. -/
theorem isTight_iff_tailObligation :
    IsTightMeasureSet {((μ : ProbabilityMeasure WilsonLoopSpace) : Measure WilsonLoopSpace) |
      μ ∈ Set.range Z.law} ↔ Z.TailObligation :=
  isTightMeasureSet_iff_uniformLoopTails _

/-- Bounded renormalization constants discharge the tail obligation from compactness. -/
theorem tailObligation_of_bounded (hZ : ∀ ℓ, ∃ B : ℝ, ∀ n, Z.factor n ℓ ≤ B) :
    Z.TailObligation := by
  intro ℓ ε _
  obtain ⟨B, hB⟩ := hZ ℓ
  refine ⟨B, ?_⟩
  rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
  have hmeas : MeasurableSet {w : WilsonLoopSpace | B < |w ℓ|} :=
    (isOpen_lt continuous_const (continuous_apply ℓ).abs).measurableSet
  have hmv : Measurable (Z.renormalizedVector n) :=
    ((Z.continuous_rescale n).comp (continuous_wilsonLoopVector _ _)).measurable
  rw [law_eq_map_renormalizedVector, ProbabilityMeasure.toMeasure_map, Measure.map_apply hmv hmeas]
  have hempty : Z.renormalizedVector n ⁻¹' {w : WilsonLoopSpace | B < |w ℓ|} = ∅ := by
    ext U
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    have hW := halfTraceRe_mem_Icc (pathHolonomy U
      (latticeSite (P.side n) (ℓ.latticeBase (P.spacing n))) (ℓ.latticeLoop (P.spacing n)))
    have hWabs : |physicalWilsonLoop (P.side n) (P.spacing n) ℓ U| ≤ 1 := abs_le.mpr hW
    have hZpos := Z.factor_pos n ℓ
    change |Z.factor n ℓ * physicalWilsonLoop (P.side n) (P.spacing n) ℓ U| ≤ B
    rw [abs_mul, abs_of_pos hZpos]
    calc Z.factor n ℓ * |physicalWilsonLoop (P.side n) (P.spacing n) ℓ U|
        ≤ Z.factor n ℓ * 1 := mul_le_mul_of_nonneg_left hWabs hZpos.le
      _ ≤ B := by rw [mul_one]; exact hB n
  rw [hempty, measure_empty]
  exact zero_le

/-- Under the tail obligation the renormalized laws have subsequential weak limits, by
Prokhorov's theorem. This is again subsequential compactness only. -/
theorem exists_subsequential_limit_of_tailObligation (hT : Z.TailObligation) :
    ∃ (φ : ℕ → ℕ) (ν : ProbabilityMeasure WilsonLoopSpace), StrictMono φ ∧
      Tendsto (fun n => Z.law (φ n)) atTop (𝓝 ν) := by
  have hcomp := isCompact_closure_of_isTightMeasureSet ((Z.isTight_iff_tailObligation).mpr hT)
  obtain ⟨ν, _, φ, hφ, hlim⟩ := hcomp.tendsto_subseq (x := Z.law)
    (fun n => subset_closure ⟨n, rfl⟩)
  exact ⟨φ, ν, hφ, hlim⟩

/-- The unrenormalized loops are the special case of constant factor one. -/
def unrenormalized (P : CutoffPath) : LoopRenormalization P where
  factor _ _ := 1
  factor_pos _ _ := one_pos

theorem unrenormalized_law (P : CutoffPath) (n : ℕ) :
    (unrenormalized P).law n = P.wilsonLoopLaw n := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [law, ProbabilityMeasure.toMeasure_map]
  have hid : (unrenormalized P).rescale n = id := by
    funext w ℓ
    simp [rescale, unrenormalized]
  rw [hid, Measure.map_id]

end LoopRenormalization

/-! ## 9. Convergence: the named missing input and its exact consequence -/

/-- What the compactness argument does not provide: agreement of all subsequential weak
limits of the joint Wilson-loop laws along the given cutoff path. This module does not prove
it; the negative control exhibits an actual Wilson cutoff path where it fails. -/
structure WilsonLoopConvergenceObligation (P : CutoffPath) : Prop where
  subsequential_limits_agree :
    ∀ (φ ψ : ℕ → ℕ) (ν ν' : ProbabilityMeasure WilsonLoopSpace), StrictMono φ → StrictMono ψ →
      Tendsto (fun n => P.wilsonLoopLaw (φ n)) atTop (𝓝 ν) →
      Tendsto (fun n => P.wilsonLoopLaw (ψ n)) atTop (𝓝 ν') → ν = ν'

/-- Convergence of the full sequence of joint laws is equivalent to the named obligation. -/
theorem wilsonLoopLaw_converges_iff (P : CutoffPath) :
    WilsonLoopConvergenceObligation P ↔ ∃ ν, Tendsto P.wilsonLoopLaw atTop (𝓝 ν) := by
  constructor
  · intro h
    obtain ⟨φ, μ, hφ, _, hW, _⟩ := P.exists_subsequential_limit
    refine ⟨μ.map halfTraceVector, ?_⟩
    have hK : IsCompact (Set.range fun μ : ProbabilityMeasure BasedHolonomySpace =>
        μ.map halfTraceVector) :=
      isCompact_range (ProbabilityMeasure.continuous_map continuous_halfTraceVector)
    apply hK.tendsto_nhds_of_unique_mapClusterPt (Eventually.of_forall fun n =>
      ⟨P.basedHolonomyLaw n, (P.wilsonLoopLaw_eq_map_halfTraceVector n).symm⟩)
    intro ν' _ hν'
    obtain ⟨ψ, hψ, hlim⟩ := hν'.tendsto_subseq
    exact h.subsequential_limits_agree ψ φ ν' _ hψ hφ hlim hW
  · rintro ⟨ν, hν⟩
    constructor
    intro φ ψ ν₁ ν₂ hφ hψ h₁ h₂
    have e₁ := tendsto_nhds_unique h₁ (hν.comp hφ.tendsto_atTop)
    have e₂ := tendsto_nhds_unique h₂ (hν.comp hψ.tendsto_atTop)
    rw [e₁, e₂]

/-! ## 10. Exact lattice translations and commensurate physical translations -/

theorem stepHolonomy_latticeTranslate (t : Lattice4D L) (U : GaugeConfig L) (x : Lattice4D L)
    (s : LatticeStep) :
    stepHolonomy (latticeTranslate t U) x s = stepHolonomy U (x + t) s := by
  rcases s with ⟨μ, _ | _⟩
  · have h : x - unitVec L μ + t = x + t - unitVec L μ := by abel
    simp only [stepHolonomy_backward]
    change (U ⟨x - unitVec L μ + t, μ⟩)⁻¹ = _
    simp only [h]
  · rfl

theorem stepTarget_add (x t : Lattice4D L) (s : LatticeStep) :
    stepTarget (x + t) s = stepTarget x s + t := by
  simp only [stepTarget]
  abel

/-- Path holonomies of a translated configuration are path holonomies of translated paths. -/
theorem pathHolonomy_latticeTranslate (t : Lattice4D L) (U : GaugeConfig L) (x : Lattice4D L)
    (p : List LatticeStep) :
    pathHolonomy (latticeTranslate t U) x p = pathHolonomy U (x + t) p := by
  induction p generalizing x with
  | nil => rfl
  | cons s p ih =>
    simp only [pathHolonomy_cons, stepHolonomy_latticeTranslate, ih, stepTarget_add]

theorem latticeSite_add (m k : Fin 4 → ℤ) :
    latticeSite L (m + k) = latticeSite L m + latticeSite L k := by
  funext i
  simp [latticeSite]

/-- Translation of a physical loop by a rational vector. -/
def PhysicalRectangle.translate (c : Fin 4 → ℚ) (ℓ : PhysicalRectangle) : PhysicalRectangle :=
  { ℓ with base := ℓ.base + c }

/-- The induced action of a physical translation on the common space. -/
def translateObservables (c : Fin 4 → ℚ) (w : WilsonLoopSpace) : WilsonLoopSpace :=
  fun ℓ => w (ℓ.translate c)

theorem continuous_translateObservables (c : Fin 4 → ℚ) :
    Continuous (translateObservables c) :=
  continuous_pi fun _ => continuous_apply _

/-- `c` is an integer multiple of the spacing `a` in every coordinate. -/
def IsLatticeVector (a : ℝ) (c : Fin 4 → ℚ) : Prop := ∀ i, ∃ k : ℤ, (c i : ℝ) = k * a

theorem latticeBase_translate {a : ℝ} (ha : 0 < a) {c : Fin 4 → ℚ} {k : Fin 4 → ℤ}
    (hk : ∀ i, (c i : ℝ) = k i * a) (ℓ : PhysicalRectangle) :
    (ℓ.translate c).latticeBase a = ℓ.latticeBase a + k := by
  funext i
  simp only [PhysicalRectangle.latticeBase, PhysicalRectangle.translate, Pi.add_apply,
    Rat.cast_add, hk i]
  rw [add_div, mul_div_assoc, div_self ha.ne', mul_one, Int.floor_add_intCast]

/-- A physical translation commensurate with the spacing is an exact lattice translation of
the configuration. -/
theorem translateObservables_wilsonLoopVector {a : ℝ} (ha : 0 < a) {c : Fin 4 → ℚ}
    {k : Fin 4 → ℤ} (hk : ∀ i, (c i : ℝ) = k i * a) (U : GaugeConfig L) :
    translateObservables c (wilsonLoopVector L a U) =
      wilsonLoopVector L a (latticeTranslate (latticeSite L k) U) := by
  funext ℓ
  simp only [translateObservables, wilsonLoopVector, physicalWilsonLoop, wilsonLoop]
  rw [pathHolonomy_latticeTranslate, latticeBase_translate ha hk, latticeSite_add]
  rfl

/-- Exact invariance of the joint law under every physical translation that is a lattice
vector at the given cutoff, from the proved translation invariance of the Wilson law. -/
theorem CutoffPath.wilsonLoopLaw_translate (P : CutoffPath) (n : ℕ) {c : Fin 4 → ℚ}
    (hc : IsLatticeVector (P.spacing n) c) :
    (P.wilsonLoopLaw n).map (translateObservables c) = P.wilsonLoopLaw n := by
  choose k hk using hc
  apply ProbabilityMeasure.toMeasure_injective
  simp only [CutoffPath.wilsonLoopLaw, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (continuous_translateObservables c).measurable
    (continuous_wilsonLoopVector _ _).measurable]
  have hfun : translateObservables c ∘ wilsonLoopVector (P.side n) (P.spacing n) =
      wilsonLoopVector (P.side n) (P.spacing n) ∘ latticeTranslate (latticeSite (P.side n) k) := by
    funext U
    exact translateObservables_wilsonLoopVector (P.spacing_pos n) hk U
  rw [hfun, ← Measure.map_map (continuous_wilsonLoopVector _ _).measurable
    (continuous_latticeTranslate _).measurable]
  have hinv := congrArg (fun μ : ProbabilityMeasure (GaugeConfig (P.side n)) =>
    (μ : Measure (GaugeConfig (P.side n))))
    (wilsonProbability_translation_invariant (P.side n) (P.coupling n) (P.coupling_nonneg n)
      (latticeSite (P.side n) k))
  simp only [ProbabilityMeasure.toMeasure_map] at hinv
  unfold CutoffPath.configLaw
  rw [hinv]

/-- Every weak limit is invariant under each physical translation that is eventually a
lattice vector along the cutoff path. -/
theorem CutoffPath.limit_translation_invariant (P : CutoffPath) {c : Fin 4 → ℚ}
    (hc : ∀ᶠ n in atTop, IsLatticeVector (P.spacing n) c) (φ : ℕ → ℕ)
    (hφ : Tendsto φ atTop atTop) (ν : ProbabilityMeasure WilsonLoopSpace)
    (hν : Tendsto (fun n => P.wilsonLoopLaw (φ n)) atTop (𝓝 ν)) :
    ν.map (translateObservables c) = ν := by
  have hm := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hν
    (continuous_translateObservables c)
  have hev : (fun n => (P.wilsonLoopLaw (φ n)).map (translateObservables c)) =ᶠ[atTop]
      (fun n => P.wilsonLoopLaw (φ n)) :=
    (hφ.eventually hc).mono fun n hn => P.wilsonLoopLaw_translate (φ n) hn
  exact tendsto_nhds_unique (Tendsto.congr' hev hm) hν

/-- The dyadic rational vector `j / 2^m`. -/
def dyadicVector (j : Fin 4 → ℤ) (m : ℕ) : Fin 4 → ℚ := fun i => (j i : ℚ) / 2 ^ m

theorem isLatticeVector_dyadicVector (j : Fin 4 → ℤ) {m n : ℕ} (hmn : m ≤ n) :
    IsLatticeVector ((1 / 2 : ℝ) ^ n) (dyadicVector j m) := by
  intro i
  refine ⟨j i * 2 ^ (n - m), ?_⟩
  have h2 : (2 : ℝ) ^ n = 2 ^ (n - m) * 2 ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hmn]
  simp only [dyadicVector, Rat.cast_div, Rat.cast_intCast, Rat.cast_pow, Rat.cast_ofNat,
    Int.cast_mul, Int.cast_pow, Int.cast_ofNat, one_div, inv_pow, h2]
  field_simp

/-- Along dyadic spacings `a n = 2⁻ⁿ`, every weak limit of the joint Wilson-loop laws is
invariant under every dyadic rational translation. Invariance under all rational or real
translations is not proved: it needs continuity of the limit in the loop position. -/
theorem CutoffPath.dyadic_limit_translation_invariant (P : CutoffPath)
    (hP : ∀ n, P.spacing n = (1 / 2 : ℝ) ^ n) (j : Fin 4 → ℤ) (m : ℕ) (φ : ℕ → ℕ)
    (hφ : Tendsto φ atTop atTop) (ν : ProbabilityMeasure WilsonLoopSpace)
    (hν : Tendsto (fun n => P.wilsonLoopLaw (φ n)) atTop (𝓝 ν)) :
    ν.map (translateObservables (dyadicVector j m)) = ν :=
  P.limit_translation_invariant (eventually_atTop.2 ⟨m, fun n hn => by
    rw [hP n]
    exact isLatticeVector_dyadicVector j hn⟩) φ hφ ν hν

/-! ## 11. Coordinate permutations: an exact symmetry of the actual model -/

/-- Permutation of the coordinates of a lattice site: coordinate `i` moves to `σ i`. -/
def permuteSite (σ : Equiv.Perm (Fin 4)) (x : Lattice4D L) : Lattice4D L := x ∘ σ.symm

theorem permuteSite_add (σ : Equiv.Perm (Fin 4)) (x y : Lattice4D L) :
    permuteSite σ (x + y) = permuteSite σ x + permuteSite σ y := rfl

theorem permuteSite_neg (σ : Equiv.Perm (Fin 4)) (x : Lattice4D L) :
    permuteSite σ (-x) = -permuteSite σ x := rfl

theorem permuteSite_sub (σ : Equiv.Perm (Fin 4)) (x y : Lattice4D L) :
    permuteSite σ (x - y) = permuteSite σ x - permuteSite σ y := rfl

theorem permuteSite_unitVec (σ : Equiv.Perm (Fin 4)) (μ : Direction) :
    permuteSite σ (unitVec L μ) = unitVec L (σ μ) := by
  funext i
  simp only [permuteSite, Function.comp_apply, unitVec, Equiv.symm_apply_eq]

theorem permuteSite_symm_apply (σ : Equiv.Perm (Fin 4)) (x : Lattice4D L) :
    permuteSite σ.symm (permuteSite σ x) = x := by
  funext i
  simp [permuteSite]

/-- The step along the permuted direction. -/
def permuteStep (σ : Equiv.Perm (Fin 4)) (s : LatticeStep) : LatticeStep := ⟨σ s.dir, s.forward⟩

theorem displacement_permuteStep (σ : Equiv.Perm (Fin 4)) (s : LatticeStep) :
    (permuteStep σ s).displacement L = permuteSite σ (s.displacement L) := by
  rcases s with ⟨μ, _ | _⟩
  · simp only [permuteStep, LatticeStep.displacement_backward, permuteSite_neg,
      permuteSite_unitVec]
  · simp only [permuteStep, LatticeStep.displacement_forward, permuteSite_unitVec]

theorem stepTarget_permute (σ : Equiv.Perm (Fin 4)) (x : Lattice4D L) (s : LatticeStep) :
    stepTarget (permuteSite σ x) (permuteStep σ s) = permuteSite σ (stepTarget x s) := by
  rw [stepTarget, stepTarget, displacement_permuteStep, permuteSite_add]

/-- The same configuration expressed in permuted coordinates. -/
def permuteConfig (σ : Equiv.Perm (Fin 4)) (U : GaugeConfig L) : GaugeConfig L :=
  fun e => U ⟨permuteSite σ.symm e.x, σ.symm e.μ⟩

theorem stepHolonomy_permuteConfig (σ : Equiv.Perm (Fin 4)) (U : GaugeConfig L)
    (x : Lattice4D L) (s : LatticeStep) :
    stepHolonomy (permuteConfig σ U) (permuteSite σ x) (permuteStep σ s) =
      stepHolonomy U x s := by
  rcases s with ⟨μ, _ | _⟩
  · simp only [permuteStep, stepHolonomy_backward]
    change (U ⟨permuteSite σ.symm (permuteSite σ x - unitVec L (σ μ)), σ.symm (σ μ)⟩)⁻¹ = _
    simp only [permuteSite_sub, permuteSite_symm_apply, permuteSite_unitVec,
      Equiv.symm_apply_apply]
  · simp only [permuteStep, stepHolonomy_forward]
    change U ⟨permuteSite σ.symm (permuteSite σ x), σ.symm (σ μ)⟩ = _
    simp only [permuteSite_symm_apply, Equiv.symm_apply_apply]

/-- Holonomies of permuted paths in the permuted configuration are the original holonomies. -/
theorem pathHolonomy_permuteConfig (σ : Equiv.Perm (Fin 4)) (U : GaugeConfig L)
    (x : Lattice4D L) (p : List LatticeStep) :
    pathHolonomy (permuteConfig σ U) (permuteSite σ x) (p.map (permuteStep σ)) =
      pathHolonomy U x p := by
  induction p generalizing x with
  | nil => rfl
  | cons s p ih =>
    simp only [List.map_cons, pathHolonomy_cons, stepHolonomy_permuteConfig, stepTarget_permute,
      ih]

theorem map_permuteStep_rectangleSteps (σ : Equiv.Perm (Fin 4)) (μ ν : Direction) (r t : ℕ) :
    (rectangleSteps μ ν r t).map (permuteStep σ) = rectangleSteps (σ μ) (σ ν) r t := by
  simp [rectangleSteps, List.map_replicate, permuteStep]

/-- Reversing a rectangle exchanges the roles of its two directions. -/
theorem reversePath_rectangleSteps (μ ν : Direction) (r t : ℕ) :
    reversePath (rectangleSteps μ ν r t) = rectangleSteps ν μ t r := by
  simp [reversePath, rectangleSteps, LatticeStep.reverse, List.map_replicate]

theorem halfTraceRe_inv (h : SU2) : halfTraceRe h⁻¹ = halfTraceRe h := by
  have htr : SU2.trace h⁻¹ = star (SU2.trace h) := by
    change Matrix.trace (Matrix.conjTranspose h.mat) = star (Matrix.trace h.mat)
    exact Matrix.trace_conjTranspose h.mat
  simp only [halfTraceRe, htr, Complex.star_def, Complex.conj_re]

/-- The image of a plaquette under a coordinate permutation, reordered so that `μ < ν`. -/
def permutePlaquette (σ : Equiv.Perm (Fin 4)) (p : Plaquette L) : Plaquette L :=
  if h : σ p.μ < σ p.ν then ⟨permuteSite σ p.x, σ p.μ, σ p.ν, h⟩
  else ⟨permuteSite σ p.x, σ p.ν, σ p.μ,
    lt_of_le_of_ne (not_lt.mp h) (fun heq => p.h.ne (σ.injective heq).symm)⟩

theorem permutePlaquette_symm_apply (σ : Equiv.Perm (Fin 4)) (p : Plaquette L) :
    permutePlaquette σ.symm (permutePlaquette σ p) = p := by
  rcases p with ⟨x, μ, ν, hμν⟩
  have hνμ : ¬ ν < μ := not_lt.mpr hμν.le
  by_cases h : σ μ < σ ν
  · simp [permutePlaquette, h, hμν, permuteSite_symm_apply]
  · simp [permutePlaquette, h, hνμ, permuteSite_symm_apply]

/-- Coordinate permutations act bijectively on plaquettes. -/
def permutePlaquetteEquiv (σ : Equiv.Perm (Fin 4)) : Plaquette L ≃ Plaquette L where
  toFun := permutePlaquette σ
  invFun := permutePlaquette σ.symm
  left_inv := permutePlaquette_symm_apply σ
  right_inv p := by simpa using permutePlaquette_symm_apply σ.symm p

theorem plaquetteAction_eq_one_sub_halfTraceRe (U : GaugeConfig L) (p : Plaquette L) :
    plaquetteAction U p = 1 - halfTraceRe (plaquetteHolonomy U p) := rfl

/-- The actual plaquette action is invariant under coordinate permutations, including the
orientation reversal of planes whose order is reversed. -/
theorem plaquetteAction_permuteConfig (σ : Equiv.Perm (Fin 4)) (U : GaugeConfig L)
    (p : Plaquette L) :
    plaquetteAction (permuteConfig σ U) (permutePlaquette σ p) = plaquetteAction U p := by
  have hbase : pathHolonomy (permuteConfig σ U) (permuteSite σ p.x)
      (rectangleSteps (σ p.μ) (σ p.ν) 1 1) = plaquetteHolonomy U p := by
    rw [← map_permuteStep_rectangleSteps, pathHolonomy_permuteConfig,
      pathHolonomy_rectangleSteps_one_one]
  rw [plaquetteAction_eq_one_sub_halfTraceRe, plaquetteAction_eq_one_sub_halfTraceRe]
  unfold permutePlaquette
  split_ifs with h
  · rw [← pathHolonomy_rectangleSteps_one_one]
    exact congrArg (fun z => 1 - halfTraceRe z) hbase
  · rw [← pathHolonomy_rectangleSteps_one_one]
    change 1 - halfTraceRe (pathHolonomy (permuteConfig σ U) (permuteSite σ p.x)
      (rectangleSteps (σ p.ν) (σ p.μ) 1 1)) = _
    rw [← reversePath_rectangleSteps]
    have hrev := pathHolonomy_reversePath (permuteConfig σ U) (permuteSite σ p.x)
      (rectangleSteps (σ p.μ) (σ p.ν) 1 1)
    rw [pathTarget_rectangleSteps] at hrev
    rw [hrev, hbase, halfTraceRe_inv]

/-- Exact invariance of the actual Wilson action under coordinate permutations. -/
theorem wilsonAction_permuteConfig [NeZero L] (β : ℝ) (σ : Equiv.Perm (Fin 4))
    (U : GaugeConfig L) :
    wilsonAction β (permuteConfig σ U) = wilsonAction β U := by
  have hsum : ∑ p : Plaquette L, plaquetteAction (permuteConfig σ U) p =
      ∑ p : Plaquette L, plaquetteAction U p :=
    (Fintype.sum_equiv (permutePlaquetteEquiv σ) _ _
      (fun p => (plaquetteAction_permuteConfig σ U p).symm)).symm
  simp only [wilsonAction, hsum]

/-- Link relabelling induced by a coordinate permutation. -/
def permuteLinkEquiv (σ : Equiv.Perm (Fin 4)) : Link L ≃ Link L where
  toFun e := ⟨permuteSite σ e.x, σ e.μ⟩
  invFun e := ⟨permuteSite σ.symm e.x, σ.symm e.μ⟩
  left_inv e := by
    rcases e with ⟨x, μ⟩
    simp [permuteSite_symm_apply]
  right_inv e := by
    rcases e with ⟨x, μ⟩
    simpa using permuteSite_symm_apply σ.symm x

@[continuity, fun_prop]
theorem continuous_permuteConfig (σ : Equiv.Perm (Fin 4)) :
    Continuous (permuteConfig (L := L) σ) :=
  continuous_pi fun _ => continuous_apply _

/-- Product Haar measure is invariant under the link relabelling. -/
theorem measurePreserving_permuteConfig [NeZero L] (σ : Equiv.Perm (Fin 4)) :
    MeasurePreserving (permuteConfig (L := L) σ) (gaugeHaarMeasure L) (gaugeHaarMeasure L) := by
  change MeasurePreserving
    (fun (U : Link L → SU2) (e : Link L) => U ((permuteLinkEquiv σ).symm e))
    (Measure.pi (fun _ : Link L => SU2.haarProbability))
    (Measure.pi (fun _ : Link L => SU2.haarProbability))
  have hf : (MeasurableEquiv.piCongrLeft (fun _ : Link L => SU2) (permuteLinkEquiv σ) :
      (Link L → SU2) → (Link L → SU2)) =
      (fun (U : Link L → SU2) e => U ((permuteLinkEquiv σ).symm e)) := by
    funext U e
    change (Equiv.piCongrLeft (fun _ : Link L => SU2) (permuteLinkEquiv σ) U) e = _
    rw [Equiv.piCongrLeft_apply_eq_cast]
    simp
  simpa only [hf] using
    measurePreserving_piCongrLeft (fun _ : Link L => SU2.haarProbability) (permuteLinkEquiv σ)

/-- Exact invariance of the actual normalized Wilson probability under coordinate
permutations. -/
theorem wilsonProbability_permute_invariant (L : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    (σ : Equiv.Perm (Fin 4)) :
    (wilsonProbability L β hβ).map (permuteConfig σ) = wilsonProbability L β hβ := by
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  change (∫ U, F U ∂(wilsonProbability L β hβ : Measure (GaugeConfig L)).map
    (permuteConfig σ)) = _
  rw [integral_map_of_stronglyMeasurable (continuous_permuteConfig σ).measurable
    F.continuous.measurable.stronglyMeasurable, wilsonProbability_integral,
    wilsonProbability_integral]
  have hp := measurePreserving_permuteConfig (L := L) σ
  have h := integral_map_of_stronglyMeasurable (μ := gaugeHaarMeasure L) hp.measurable
    ((wilsonWeight_measurable (measurable_wilsonAction β)).mul
      F.continuous.measurable).stronglyMeasurable
  rw [hp.map_eq] at h
  simp only [Pi.mul_apply, boltzmannWeight, wilsonAction_permuteConfig] at h
  exact congrArg (fun x => x / wilsonPartition (gaugeHaarMeasure L) β) h.symm

/-- Relabelling of the coordinate axes by a permutation, acting on physical loops. The
rectangle is the same point set with permuted coordinates; its plane is reordered. -/
def PhysicalRectangle.permute (σ : Equiv.Perm (Fin 4)) (ℓ : PhysicalRectangle) :
    PhysicalRectangle :=
  if h : σ ℓ.μ < σ ℓ.ν then
    { base := ℓ.base ∘ σ.symm, μ := σ ℓ.μ, ν := σ ℓ.ν, plane := h,
      sideμ := ℓ.sideμ, sideν := ℓ.sideν, sideμ_pos := ℓ.sideμ_pos, sideν_pos := ℓ.sideν_pos }
  else
    { base := ℓ.base ∘ σ.symm, μ := σ ℓ.ν, ν := σ ℓ.μ,
      plane := lt_of_le_of_ne (not_lt.mp h) (fun heq => ℓ.plane.ne (σ.injective heq).symm),
      sideμ := ℓ.sideν, sideν := ℓ.sideμ, sideμ_pos := ℓ.sideν_pos, sideν_pos := ℓ.sideμ_pos }

/-- The induced action of a coordinate permutation on the common space. -/
def permuteObservables (σ : Equiv.Perm (Fin 4)) (w : WilsonLoopSpace) : WilsonLoopSpace :=
  fun ℓ => w (ℓ.permute σ)

theorem continuous_permuteObservables (σ : Equiv.Perm (Fin 4)) :
    Continuous (permuteObservables σ) :=
  continuous_pi fun _ => continuous_apply _

theorem latticeBase_permute (σ : Equiv.Perm (Fin 4)) (ℓ : PhysicalRectangle) (a : ℝ) :
    (ℓ.permute σ).latticeBase a = ℓ.latticeBase a ∘ σ.symm := by
  funext i
  simp only [PhysicalRectangle.latticeBase, PhysicalRectangle.permute]
  split_ifs <;> rfl

/-- Exact step-count transformation of a physical rectangle under a coordinate permutation
`σ : Equiv.Perm (Fin 4)` at any lattice spacing `a : ℝ`: when `σ ℓ.μ < σ ℓ.ν`, the step counts
`stepsμ a` and `stepsν a` are preserved; when `¬ σ ℓ.μ < σ ℓ.ν`, they are swapped. -/
theorem PhysicalRectangle.steps_permute (σ : Equiv.Perm (Fin 4)) (ℓ : PhysicalRectangle) (a : ℝ) :
    (σ ℓ.μ < σ ℓ.ν →
      (ℓ.permute σ).stepsμ a = ℓ.stepsμ a ∧ (ℓ.permute σ).stepsν a = ℓ.stepsν a) ∧
    (¬ σ ℓ.μ < σ ℓ.ν →
      (ℓ.permute σ).stepsμ a = ℓ.stepsν a ∧ (ℓ.permute σ).stepsν a = ℓ.stepsμ a) := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩⟩ <;>
    simp [PhysicalRectangle.permute, PhysicalRectangle.stepsμ, PhysicalRectangle.stepsν, h]

/-- The floor discretization commutes exactly with coordinate permutations, so each physical
Wilson loop of the permuted loop in the permuted configuration is the original loop. -/
theorem physicalWilsonLoop_permute (σ : Equiv.Perm (Fin 4)) (a : ℝ) (ℓ : PhysicalRectangle)
    (U : GaugeConfig L) :
    physicalWilsonLoop L a (ℓ.permute σ) (permuteConfig σ U) = physicalWilsonLoop L a ℓ U := by
  have hsite : latticeSite L ((ℓ.permute σ).latticeBase a) =
      permuteSite σ (latticeSite L (ℓ.latticeBase a)) := by
    rw [latticeBase_permute]
    rfl
  unfold physicalWilsonLoop wilsonLoop
  rw [hsite]
  by_cases h : σ ℓ.μ < σ ℓ.ν
  · obtain ⟨h_sμ, h_sν⟩ := (ℓ.steps_permute σ a).1 h
    have hloop : (ℓ.permute σ).latticeLoop a = (ℓ.latticeLoop a).map (permuteStep σ) := by
      unfold PhysicalRectangle.latticeLoop
      rw [h_sμ, h_sν]
      simp only [PhysicalRectangle.permute, h, ↓reduceDIte, map_permuteStep_rectangleSteps]
    rw [hloop, pathHolonomy_permuteConfig]
  · obtain ⟨h_sμ, h_sν⟩ := (ℓ.steps_permute σ a).2 h
    have hloop : (ℓ.permute σ).latticeLoop a =
        reversePath ((ℓ.latticeLoop a).map (permuteStep σ)) := by
      unfold PhysicalRectangle.latticeLoop
      rw [h_sμ, h_sν]
      simp only [PhysicalRectangle.permute, h, ↓reduceDIte,
        map_permuteStep_rectangleSteps, reversePath_rectangleSteps]
    rw [hloop]
    have hclosed : pathTarget (permuteSite σ (latticeSite L (ℓ.latticeBase a)))
        ((ℓ.latticeLoop a).map (permuteStep σ)) =
          permuteSite σ (latticeSite L (ℓ.latticeBase a)) := by
      rw [PhysicalRectangle.latticeLoop, map_permuteStep_rectangleSteps,
        pathTarget_rectangleSteps]
    have hrev := pathHolonomy_reversePath (permuteConfig σ U)
      (permuteSite σ (latticeSite L (ℓ.latticeBase a))) ((ℓ.latticeLoop a).map (permuteStep σ))
    rw [hclosed] at hrev
    rw [hrev, pathHolonomy_permuteConfig, halfTraceRe_inv]

theorem permuteObservables_wilsonLoopVector (σ : Equiv.Perm (Fin 4)) (a : ℝ)
    (U : GaugeConfig L) :
    permuteObservables σ (wilsonLoopVector L a (permuteConfig σ U)) = wilsonLoopVector L a U :=
  funext fun ℓ => physicalWilsonLoop_permute σ a ℓ U

/-- Exact invariance of every joint Wilson-loop law under all coordinate permutations, at
every cutoff, with no commensurability condition. -/
theorem CutoffPath.wilsonLoopLaw_permute (P : CutoffPath) (n : ℕ) (σ : Equiv.Perm (Fin 4)) :
    (P.wilsonLoopLaw n).map (permuteObservables σ) = P.wilsonLoopLaw n := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [CutoffPath.wilsonLoopLaw, ProbabilityMeasure.toMeasure_map]
  have hinv := congrArg (fun μ : ProbabilityMeasure (GaugeConfig (P.side n)) =>
    (μ : Measure (GaugeConfig (P.side n))))
    (wilsonProbability_permute_invariant (P.side n) (P.coupling n) (P.coupling_nonneg n) σ)
  simp only [ProbabilityMeasure.toMeasure_map] at hinv
  unfold CutoffPath.configLaw
  rw [Measure.map_map (continuous_permuteObservables σ).measurable
    (continuous_wilsonLoopVector _ _).measurable]
  conv_lhs => rw [← hinv]
  rw [Measure.map_map ((continuous_permuteObservables σ).comp
    (continuous_wilsonLoopVector _ _)).measurable (continuous_permuteConfig σ).measurable]
  congr 1
  funext U
  exact permuteObservables_wilsonLoopVector σ _ U

/-- Every weak limit of the joint Wilson-loop laws, along every cutoff path, is invariant under
all coordinate permutations. Rotations outside this finite group are not addressed. -/
theorem CutoffPath.limit_permutation_invariant (P : CutoffPath) (φ : ℕ → ℕ)
    (ν : ProbabilityMeasure WilsonLoopSpace)
    (hν : Tendsto (fun n => P.wilsonLoopLaw (φ n)) atTop (𝓝 ν)) (σ : Equiv.Perm (Fin 4)) :
    ν.map (permuteObservables σ) = ν := by
  have hm := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hν
    (continuous_permuteObservables σ)
  simp only [P.wilsonLoopLaw_permute] at hm
  exact tendsto_nhds_unique hm hν

namespace LoopRenormalization

variable {P : CutoffPath} (Z : LoopRenormalization P)

/-- Renormalization constants that depend on a loop only through its shape and orientation. -/
def IsTranslationInvariant : Prop :=
  ∀ (n : ℕ) (c : Fin 4 → ℚ) (ℓ : PhysicalRectangle), Z.factor n (ℓ.translate c) = Z.factor n ℓ

theorem law_translate (hZ : Z.IsTranslationInvariant) (n : ℕ) {c : Fin 4 → ℚ}
    (hc : IsLatticeVector (P.spacing n) c) :
    (Z.law n).map (translateObservables c) = Z.law n := by
  have hcomm : translateObservables c ∘ Z.rescale n = Z.rescale n ∘ translateObservables c := by
    funext w ℓ
    simp only [Function.comp_apply, translateObservables, rescale, hZ n c ℓ]
  apply ProbabilityMeasure.toMeasure_injective
  simp only [law, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (continuous_translateObservables c).measurable
    (Z.continuous_rescale n).measurable, hcomm,
    ← Measure.map_map (Z.continuous_rescale n).measurable
      (continuous_translateObservables c).measurable]
  have h := congrArg (fun μ : ProbabilityMeasure WilsonLoopSpace => (μ : Measure WilsonLoopSpace))
    (P.wilsonLoopLaw_translate n hc)
  simp only [ProbabilityMeasure.toMeasure_map] at h
  rw [h]

/-- A limit law of the renormalized joint laws along a subsequence. -/
def IsLimitLaw (ν : ProbabilityMeasure WilsonLoopSpace) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun n => Z.law (φ n)) atTop (𝓝 ν)

/-- Renormalization constants invariant under relabelling of the coordinate axes. -/
def IsPermutationInvariant : Prop :=
  ∀ (n : ℕ) (σ : Equiv.Perm (Fin 4)) (ℓ : PhysicalRectangle), Z.factor n (ℓ.permute σ) = Z.factor n ℓ

theorem law_permute (hZ : Z.IsPermutationInvariant) (n : ℕ) (σ : Equiv.Perm (Fin 4)) :
    (Z.law n).map (permuteObservables σ) = Z.law n := by
  have hcomm : permuteObservables σ ∘ Z.rescale n = Z.rescale n ∘ permuteObservables σ := by
    funext w ℓ
    simp only [Function.comp_apply, permuteObservables, rescale, hZ n σ ℓ]
  apply ProbabilityMeasure.toMeasure_injective
  simp only [law, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (continuous_permuteObservables σ).measurable
    (Z.continuous_rescale n).measurable, hcomm,
    ← Measure.map_map (Z.continuous_rescale n).measurable
      (continuous_permuteObservables σ).measurable]
  have h := congrArg (fun μ : ProbabilityMeasure WilsonLoopSpace => (μ : Measure WilsonLoopSpace))
    (P.wilsonLoopLaw_permute n σ)
  simp only [ProbabilityMeasure.toMeasure_map] at h
  rw [h]

/-- Every renormalized limit law is invariant under all coordinate permutations when the
constants are. -/
theorem limit_permutation_invariant (hZ : Z.IsPermutationInvariant)
    {ν : ProbabilityMeasure WilsonLoopSpace} (hν : Z.IsLimitLaw ν) (σ : Equiv.Perm (Fin 4)) :
    ν.map (permuteObservables σ) = ν := by
  obtain ⟨φ, _, hlim⟩ := hν
  have hm := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hlim
    (continuous_permuteObservables σ)
  simp only [Z.law_permute hZ] at hm
  exact tendsto_nhds_unique hm hlim

/-- Every renormalized limit law is invariant under each physical translation that is
eventually a lattice vector, when the constants are translation invariant. -/
theorem limit_translation_invariant (hZ : Z.IsTranslationInvariant) {c : Fin 4 → ℚ}
    (hc : ∀ᶠ n in atTop, IsLatticeVector (P.spacing n) c) {ν : ProbabilityMeasure WilsonLoopSpace}
    (hν : Z.IsLimitLaw ν) :
    ν.map (translateObservables c) = ν := by
  obtain ⟨φ, hφ, hlim⟩ := hν
  have hm := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hlim
    (continuous_translateObservables c)
  have hev : (fun n => (Z.law (φ n)).map (translateObservables c)) =ᶠ[atTop]
      (fun n => Z.law (φ n)) :=
    (hφ.tendsto_atTop.eventually hc).mono fun n hn => Z.law_translate hZ (φ n) hn
  exact tendsto_nhds_unique (Tendsto.congr' hev hm) hlim

/-- Under the tail obligation, full convergence of the renormalized laws is equivalent to
uniqueness of their limit laws. -/
theorem converges_iff_limitLaw_unique (hT : Z.TailObligation) :
    (∀ ν ν', Z.IsLimitLaw ν → Z.IsLimitLaw ν' → ν = ν') ↔
      ∃ ν, Tendsto Z.law atTop (𝓝 ν) := by
  constructor
  · intro h
    obtain ⟨φ, ν, hφ, hlim⟩ := Z.exists_subsequential_limit_of_tailObligation hT
    refine ⟨ν, ?_⟩
    have hcomp := isCompact_closure_of_isTightMeasureSet ((Z.isTight_iff_tailObligation).mpr hT)
    apply hcomp.tendsto_nhds_of_unique_mapClusterPt
      (Eventually.of_forall fun n => subset_closure ⟨n, rfl⟩)
    intro ν' _ hν'
    obtain ⟨ψ, hψ, hlim'⟩ := hν'.tendsto_subseq
    exact h ν' ν ⟨ψ, hψ, hlim'⟩ ⟨φ, hφ, hlim⟩
  · rintro ⟨ν, hν⟩ ν₁ ν₂ ⟨φ, hφ, h₁⟩ ⟨ψ, hψ, h₂⟩
    rw [tendsto_nhds_unique h₁ (hν.comp hφ.tendsto_atTop),
      tendsto_nhds_unique h₂ (hν.comp hψ.tendsto_atTop)]

end LoopRenormalization

/-- Summary for an arbitrary cutoff path: every weak limit of the joint Wilson-loop laws along
indices tending to infinity is the trace image of a gauge-invariant holonomy law, is supported
on the realizable set, and is invariant under all coordinate permutations and under every
physical translation that is eventually a lattice vector. -/
theorem CutoffPath.limit_properties (P : CutoffPath) (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop)
    (ν : ProbabilityMeasure WilsonLoopSpace)
    (hν : Tendsto (fun n => P.wilsonLoopLaw (φ n)) atTop (𝓝 ν)) :
    (∃ μ : ProbabilityMeasure BasedHolonomySpace,
      IsGaugeInvariantHolonomyLaw μ ∧ ν = μ.map halfTraceVector) ∧
    (ν : Measure WilsonLoopSpace) wilsonLoopRangeᶜ = 0 ∧
    (∀ σ : Equiv.Perm (Fin 4), ν.map (permuteObservables σ) = ν) ∧
    ∀ c : Fin 4 → ℚ, (∀ᶠ n in atTop, IsLatticeVector (P.spacing n) c) →
      ν.map (translateObservables c) = ν := by
  obtain ⟨μ, hμ, hνμ, hsupp⟩ := P.wilsonLoopLaw_limit_isGaugeInvariantReduction φ ν hν
  exact ⟨⟨μ, hμ, hνμ⟩, hsupp, fun σ => P.limit_permutation_invariant φ ν hν σ,
    fun c hc => P.limit_translation_invariant hc φ hφ ν hν⟩

/-! ## 12. What identification with a continuum theory still requires -/

/-- Euclidean time reflection `x₀ ↦ -x₀` of a physical loop, as a point set. -/
def PhysicalRectangle.timeReflect (ℓ : PhysicalRectangle) : PhysicalRectangle :=
  { ℓ with base := Function.update ℓ.base 0 (-(ℓ.base 0) - if ℓ.μ = 0 then ℓ.sideμ else 0) }

/-- The induced action of time reflection on the common space. -/
def reflectObservables (w : WilsonLoopSpace) : WilsonLoopSpace := fun ℓ => w ℓ.timeReflect

/-- The loop lies in the open positive-time half-space. -/
def PhysicalRectangle.IsPositiveTime (ℓ : PhysicalRectangle) : Prop := 0 < ℓ.base 0

/-- The largest physical time reached by the loop. -/
def PhysicalRectangle.timeEnd (ℓ : PhysicalRectangle) : ℚ :=
  ℓ.base 0 + if ℓ.μ = 0 then ℓ.sideμ else 0

/-- A function on the common space that depends only on positive-time loops. -/
def DependsOnPositiveTime (F : WilsonLoopSpace → ℝ) : Prop :=
  ∀ w w' : WilsonLoopSpace, (∀ ℓ : PhysicalRectangle, ℓ.IsPositiveTime → w ℓ = w' ℓ) →
    F w = F w'

/-- Physical time translation by `t`. -/
def timeVector (t : ℕ) : Fin 4 → ℚ := fun i => if i = 0 then (t : ℚ) else 0

/-- The one-loop SU(2) asymptotic-freedom coefficient `11 / (3π²)` for `β = 4/g²`. -/
@[reducible] noncomputable def su2OneLoopBeta0 : ℝ := 11 / (3 * Real.pi ^ 2)

theorem su2OneLoopBeta0_pos : 0 < su2OneLoopBeta0 := by
  unfold su2OneLoopBeta0
  positivity

/-- A cutoff path intended for the continuum and infinite-volume limit of a compact simple gauge
model with one-loop asymptotic-freedom coefficient `beta0 > 0` (defaulting to `su2OneLoopBeta0`
for `SU(2)`). `coupling_asymptoticFreedom` is the one-loop trajectory
`β n / log (1 / a n) → beta0`. These fields specify the path; the compactness theorems above
hold for every cutoff path and use none of them. -/
structure ContinuumCutoffPath extends CutoffPath where
  beta0 : ℝ := su2OneLoopBeta0
  beta0_pos : 0 < beta0 := by positivity
  spacing_tendsto_zero : Tendsto spacing atTop (𝓝 0)
  physicalSide_tendsto_atTop : Tendsto (fun n => (side n : ℝ) * spacing n) atTop atTop
  coupling_asymptoticFreedom :
    Tendsto (fun n => coupling n / Real.log (1 / spacing n)) atTop (𝓝 beta0)

/-- Along a continuum cutoff path every lattice loop has the prescribed physical size in the
limit. -/
theorem ContinuumCutoffPath.scale_consistency (P : ContinuumCutoffPath) (ℓ : PhysicalRectangle) :
    Tendsto (fun n => P.spacing n * (ℓ.stepsμ (P.spacing n) : ℝ)) atTop (𝓝 (ℓ.sideμ : ℝ)) ∧
    Tendsto (fun n => P.spacing n * (ℓ.stepsν (P.spacing n) : ℝ)) atTop (𝓝 (ℓ.sideν : ℝ)) ∧
    ∀ i, Tendsto (fun n => P.spacing n * (ℓ.latticeBase (P.spacing n) i : ℝ)) atTop
      (𝓝 (ℓ.base i : ℝ)) :=
  physicalRectangle_scale_consistency ℓ P.spacing_pos P.spacing_tendsto_zero

/-- The path conditions under which the half-lattice reflection argument applies: spacings
`2⁻ⁿ` and eventually even sides. They are properties of the chosen path, proved for the
explicit dyadic path (`dyadicOneLoopPath_isDyadic`), not open hypotheses. -/
structure ContinuumCutoffPath.IsDyadic (P : ContinuumCutoffPath) : Prop where
  spacing_eq : ∀ n, P.spacing n = (1 / 2 : ℝ) ^ n
  eventually_even : ∀ᶠ n in atTop, Even (P.side n)

namespace LoopRenormalization

variable {P : CutoffPath} (Z : LoopRenormalization P)

/-- One name for the identification question: every two subsequential limit laws of the
renormalized loops agree. Under the tails this is full convergence
(`converges_iff_limitLaw_unique`). It is not proved for any renormalization of the actual
model; the negative control exhibits a Wilson cutoff path where it fails. -/
def LimitLawsAgree : Prop := ∀ ν ν', Z.IsLimitLaw ν → Z.IsLimitLaw ν' → ν = ν'

/-- One name for Euclidean covariance of the limits under translations: invariance under every
rational translation. Translations that are eventually lattice vectors are proved
(`limit_translation_invariant`); the remaining rational shifts are a regularity statement about
the limit, not a lattice symmetry. -/
def LimitLawsTranslationInvariant : Prop :=
  ∀ ν, Z.IsLimitLaw ν → ∀ c : Fin 4 → ℚ, ν.map (translateObservables c) = ν

/-- One name for time-reflection symmetry of the limits. On functionals of finitely many
time-dyadic loops it is proved for reflection-invariant constants along spacings `2⁻ⁿ`
(`YangMillsOsterwalderSchraderInheritance.limit_reflect_invariant_timeDyadic`); the extension
to every loop is the same regularity question as `DyadicTimeApproximable`. -/
def LimitLawsReflectionInvariant : Prop :=
  ∀ ν, Z.IsLimitLaw ν → (ν : Measure WilsonLoopSpace).map reflectObservables = ν

end LoopRenormalization

/-- The identification obligations other than reflection positivity, stated once. Every
consumer that needs these five hypotheses takes this structure; `ContinuumIdentificationObligations`
extends it with the positivity field, which along dyadic paths follows from regularity
(`YangMillsOsterwalderSchraderInheritance.continuumIdentificationObligations_of_dyadic`). -/
structure ObligationsExceptReflection (P : ContinuumCutoffPath)
    (Z : LoopRenormalization P.toCutoffPath) : Prop where
  renormalized_tails : Z.TailObligation
  limits_agree : Z.LimitLawsAgree
  translation_invariant : Z.LimitLawsTranslationInvariant
  time_mixing : ∀ ν, Z.IsLimitLaw ν → ∀ F G : WilsonLoopSpace →ᵇ ℝ,
    Tendsto (fun t : ℕ => ∫ w, F w * G (translateObservables (timeVector t) w)
        ∂(ν : Measure WilsonLoopSpace)) atTop
      (𝓝 ((∫ w, F w ∂(ν : Measure WilsonLoopSpace)) * ∫ w, G w ∂(ν : Measure WilsonLoopSpace)))
  nontrivial : ∀ ν, Z.IsLimitLaw ν → ∃ ℓ ℓ' : PhysicalRectangle, ℓ.timeEnd < ℓ'.base 0 ∧
    ¬ ProbabilityTheory.IndepFun (fun w : WilsonLoopSpace => w ℓ) (fun w => w ℓ')
      (ν : Measure WilsonLoopSpace)

/-- What identifying the limit of the renormalized Wilson loops with a continuum SU(2)
Yang–Mills theory still requires. Every field is an undischarged hypothesis; this module
proves none of them in general.
* `renormalized_tails`: uniform tails of each renormalized loop, equivalent to tightness
  (`isTight_iff_tailObligation`). Discharged only for bounded constants
  (`tailObligation_of_bounded`); the expected perimeter and corner renormalization of
  four-dimensional loops is unbounded.
* `limits_agree`: uniqueness of limit laws (`LimitLawsAgree`), equivalent to convergence given
  the tails (`converges_iff_limitLaw_unique`).
* `translation_invariant`: all rational translations (`LimitLawsTranslationInvariant`). Proved
  only for translations that are eventually lattice vectors (`limit_translation_invariant`); the
  rest needs continuity of the limit in the loop position.
* `reflection_positive`, `time_mixing`: Osterwalder–Schrader positivity and clustering.
* `nontrivial`: two time-separated loops are not independent. This alone does not exclude
  an abelian or free limit. Its failure mode is real: unrenormalized plaquette averages of
  fixed physical size converge to a Dirac law (`ContinuumCutoffPath.plaquetteAverageLaw_tendsto`).
Invariance under coordinate permutations is not listed: it is proved for every limit law when
the constants are permutation invariant (`limit_permutation_invariant`). Rotations outside
that finite group cannot be stated for axis-parallel rectangles; they need general loops. -/
structure ContinuumIdentificationObligations (P : ContinuumCutoffPath)
    (Z : LoopRenormalization P.toCutoffPath) : Prop extends ObligationsExceptReflection P Z where
  reflection_positive : ∀ ν, Z.IsLimitLaw ν → ∀ F : WilsonLoopSpace →ᵇ ℝ,
    DependsOnPositiveTime F →
      0 ≤ ∫ w, F (reflectObservables w) * F w ∂(ν : Measure WilsonLoopSpace)

/-- The obligations are coherent: together with permutation-invariant constants they produce
a genuine limit law of the renormalized loops, invariant under all rational translations and
all coordinate permutations. The permutation invariance is proved, not assumed. -/
theorem ContinuumIdentificationObligations.exists_limit {P : ContinuumCutoffPath}
    {Z : LoopRenormalization P.toCutoffPath} (h : ContinuumIdentificationObligations P Z)
    (hZσ : Z.IsPermutationInvariant) :
    ∃ ν : ProbabilityMeasure WilsonLoopSpace, Tendsto Z.law atTop (𝓝 ν) ∧ Z.IsLimitLaw ν ∧
      (∀ c : Fin 4 → ℚ, ν.map (translateObservables c) = ν) ∧
      ∀ σ : Equiv.Perm (Fin 4), ν.map (permuteObservables σ) = ν := by
  obtain ⟨ν, hν⟩ := (Z.converges_iff_limitLaw_unique h.renormalized_tails).mp h.limits_agree
  have hlim : Z.IsLimitLaw ν := ⟨id, strictMono_id, hν⟩
  exact ⟨ν, hν, hlim, h.translation_invariant ν hlim, Z.limit_permutation_invariant hZσ hlim⟩

/-- Factors identically equal to one are translation and permutation invariant and satisfy the
tail obligation, so for unrenormalized loops only the remaining fields are open. -/
theorem LoopRenormalization.unrenormalized_invariant_and_tails (P : CutoffPath) :
    (LoopRenormalization.unrenormalized P).IsTranslationInvariant ∧
    (LoopRenormalization.unrenormalized P).IsPermutationInvariant ∧
    (LoopRenormalization.unrenormalized P).TailObligation :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl,
    LoopRenormalization.tailObligation_of_bounded _ fun _ => ⟨1, fun _ => le_rfl⟩⟩

/-- The unrenormalized convergence obligation is the identification question
`LoopRenormalization.LimitLawsAgree` for the constant factor one: one question, one name. -/
theorem wilsonLoopConvergenceObligation_iff_limitLawsAgree (P : CutoffPath) :
    WilsonLoopConvergenceObligation P ↔ (LoopRenormalization.unrenormalized P).LimitLawsAgree := by
  have hlaw : (LoopRenormalization.unrenormalized P).law = P.wilsonLoopLaw :=
    funext (LoopRenormalization.unrenormalized_law P)
  unfold LoopRenormalization.LimitLawsAgree
  rw [wilsonLoopLaw_converges_iff, ← hlaw]
  exact ((LoopRenormalization.unrenormalized P).converges_iff_limitLaw_unique
    (LoopRenormalization.unrenormalized_invariant_and_tails P).2.2).symm

/-! ## 13. An explicit asymptotically free dyadic path -/

/-- A continuum cutoff path with spacing `2⁻ⁿ`, side `4ⁿ` (physical side `2ⁿ`) and the exact
one-loop trajectory `β n = (11/(3π²)) · n log 2`. It shows the path conditions are
satisfiable; nothing below claims convergence along it. -/
def dyadicOneLoopPath : ContinuumCutoffPath where
  side n := 4 ^ n
  side_pos n := by positivity
  spacing n := (1 / 2 : ℝ) ^ n
  spacing_pos n := by positivity
  coupling n := 11 / (3 * Real.pi ^ 2) * ((n : ℝ) * Real.log 2)
  coupling_nonneg n := by
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  spacing_tendsto_zero := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  physicalSide_tendsto_atTop := by
    have h : (fun n : ℕ => ((4 ^ n : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n) = fun n => (2 : ℝ) ^ n := by
      funext n
      push_cast
      rw [← mul_pow]
      norm_num
    rw [h]
    exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  coupling_asymptoticFreedom := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hlog : Real.log (1 / (1 / 2 : ℝ) ^ n) = (n : ℝ) * Real.log 2 := by
      rw [one_div_pow, one_div_one_div, Real.log_pow]
    have hpos : 0 < (n : ℝ) * Real.log 2 :=
      mul_pos (by exact_mod_cast hn) (Real.log_pos (by norm_num))
    rw [hlog, mul_div_assoc, div_self hpos.ne', mul_one]

/-- The explicit dyadic path has spacings `2⁻ⁿ` and even sides from `n = 1` on. -/
theorem dyadicOneLoopPath_isDyadic : dyadicOneLoopPath.IsDyadic where
  spacing_eq _ := rfl
  eventually_even := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    change Even (4 ^ n)
    exact (Nat.even_pow (m := 4) (n := n)).2 ⟨⟨2, rfl⟩, Nat.one_le_iff_ne_zero.mp hn⟩

/-- Along the explicit asymptotically free dyadic path: subsequential limits exist, and every
weak limit of the joint Wilson-loop laws is the trace image of a gauge-invariant holonomy law
supported on the realizable set, invariant under every dyadic translation and every coordinate
permutation. Neither convergence nor identification with a continuum theory is asserted. -/
theorem dyadicOneLoopPath_limits :
    (∃ (φ : ℕ → ℕ) (ν : ProbabilityMeasure WilsonLoopSpace), StrictMono φ ∧
      Tendsto (fun n => dyadicOneLoopPath.wilsonLoopLaw (φ n)) atTop (𝓝 ν)) ∧
    ∀ (φ : ℕ → ℕ), Tendsto φ atTop atTop → ∀ ν : ProbabilityMeasure WilsonLoopSpace,
      Tendsto (fun n => dyadicOneLoopPath.wilsonLoopLaw (φ n)) atTop (𝓝 ν) →
      (∃ μ : ProbabilityMeasure BasedHolonomySpace,
        IsGaugeInvariantHolonomyLaw μ ∧ ν = μ.map halfTraceVector ∧
        (ν : Measure WilsonLoopSpace) wilsonLoopRangeᶜ = 0) ∧
      (∀ (j : Fin 4 → ℤ) (m : ℕ), ν.map (translateObservables (dyadicVector j m)) = ν) ∧
      ∀ σ : Equiv.Perm (Fin 4), ν.map (permuteObservables σ) = ν := by
  refine ⟨?_, fun φ hφ ν hν => ⟨?_, fun j m => ?_, fun σ => ?_⟩⟩
  · obtain ⟨φ, μ, hφ, _, hW, _⟩ := dyadicOneLoopPath.exists_subsequential_limit
    exact ⟨φ, μ.map halfTraceVector, hφ, hW⟩
  · exact dyadicOneLoopPath.wilsonLoopLaw_limit_isGaugeInvariantReduction φ ν hν
  · exact dyadicOneLoopPath.dyadic_limit_translation_invariant (fun _ => rfl) j m φ hφ ν hν
  · exact dyadicOneLoopPath.limit_permutation_invariant φ ν hν σ

/-! ## 14. Physical-scale plaquette averages: full convergence to a collapsed law -/

/-- A cube of physical side `side` with rational corner, together with a plaquette plane. -/
structure PhysicalPlaquetteRegion where
  corner : Fin 4 → ℚ
  side : ℚ
  side_pos : 0 < side
  μ : Direction
  ν : Direction
  plane : μ < ν

instance : Countable PhysicalPlaquetteRegion := by
  have hinj : Function.Injective (fun R : PhysicalPlaquetteRegion =>
      (R.corner, R.side, R.μ, R.ν)) := by
    rintro ⟨c, s, hs, μ, ν, h⟩ ⟨c', s', hs', μ', ν', h'⟩ hEq
    simp only [Prod.mk.injEq] at hEq
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hEq
    rfl
  exact hinj.countable

namespace PhysicalPlaquetteRegion

/-- Lattice corner of the region at spacing `a`. -/
def latticeCorner (R : PhysicalPlaquetteRegion) (a : ℝ) : Fin 4 → ℤ :=
  fun i => ⌊(R.corner i : ℝ) / a⌋

/-- Lattice sites per direction at spacing `a`; never zero. -/
def sites (R : PhysicalPlaquetteRegion) (a : ℝ) : ℕ := ⌊(R.side : ℝ) / a⌋₊ + 1

/-- The plaquette of the region at lattice offset `k`. -/
def plaquetteAt (R : PhysicalPlaquetteRegion) (L : ℕ) (a : ℝ) (k : Fin 4 → Fin (R.sites a)) :
    Plaquette L :=
  ⟨latticeSite L (R.latticeCorner a + fun i => ((k i : ℕ) : ℤ)), R.μ, R.ν, R.plane⟩

end PhysicalPlaquetteRegion

/-- Average of the unit Wilson loops `1 - s_p` over the `(sites)^4` plaquettes of a region of
fixed physical size, on the lattice of side `L` and spacing `a`. -/
def physicalPlaquetteAverage (L : ℕ) (a : ℝ) (R : PhysicalPlaquetteRegion) (U : GaugeConfig L) :
    ℝ :=
  1 - (∑ k : Fin 4 → Fin (R.sites a), plaquetteAction U (R.plaquetteAt L a k)) /
    (R.sites a : ℝ) ^ 4

theorem sites_pow_pos (R : PhysicalPlaquetteRegion) (a : ℝ) : 0 < (R.sites a : ℝ) ^ 4 := by
  have : 0 < (R.sites a : ℝ) := by
    unfold PhysicalPlaquetteRegion.sites
    positivity
  positivity

theorem physicalPlaquetteAverage_le_one (a : ℝ) (R : PhysicalPlaquetteRegion)
    (U : GaugeConfig L) : physicalPlaquetteAverage L a R U ≤ 1 := by
  unfold physicalPlaquetteAverage
  have hs : 0 ≤ ∑ k : Fin 4 → Fin (R.sites a), plaquetteAction U (R.plaquetteAt L a k) :=
    Finset.sum_nonneg fun k _ => plaquetteAction_nonneg U _
  have := div_nonneg hs (sites_pow_pos R a).le
  linarith

/-- Exact gauge invariance of each physical plaquette average. -/
theorem physicalPlaquetteAverage_gaugeTransform (a : ℝ) (R : PhysicalPlaquetteRegion)
    (g : GaugeTransformation L) (U : GaugeConfig L) :
    physicalPlaquetteAverage L a R (gaugeTransform g U) = physicalPlaquetteAverage L a R U := by
  unfold physicalPlaquetteAverage
  congr 3
  funext k
  unfold plaquetteAction
  rw [plaquetteTrace_gaugeTransform]

theorem continuous_physicalPlaquetteAverage (L : ℕ) (a : ℝ) (R : PhysicalPlaquetteRegion) :
    Continuous (physicalPlaquetteAverage L a R) := by
  unfold physicalPlaquetteAverage
  exact continuous_const.sub ((continuous_finsetSum _ fun k _ =>
    continuous_plaquetteAction _).div_const _)

/-- Common space for the joint values of all physical plaquette averages. -/
abbrev PlaquetteAverageSpace := PhysicalPlaquetteRegion → ℝ

/-- All physical plaquette averages of one lattice configuration. -/
def plaquetteAverageVector (L : ℕ) (a : ℝ) (U : GaugeConfig L) : PlaquetteAverageSpace :=
  fun R => physicalPlaquetteAverage L a R U

theorem continuous_plaquetteAverageVector (L : ℕ) (a : ℝ) :
    Continuous (plaquetteAverageVector L a) :=
  continuous_pi fun R => continuous_physicalPlaquetteAverage L a R

/-- Joint law of all physical plaquette averages at the `n`-th cutoff. -/
def CutoffPath.plaquetteAverageLaw (P : CutoffPath) (n : ℕ) :
    ProbabilityMeasure PlaquetteAverageSpace :=
  (P.configLaw n).map (plaquetteAverageVector (P.side n) (P.spacing n))

/-- Under the actual Wilson law every plaquette has mean action at most the mean action
density `E[S₁]/L⁴`, by exact translation invariance. -/
theorem integral_plaquetteAction_le_density (L : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    (p : Plaquette L) :
    ∫ U, plaquetteAction U p ∂(wilsonProbability L β hβ : Measure (GaugeConfig L)) ≤
      (∫ U, wilsonAction 1 U ∂(wilsonProbability L β hβ : Measure (GaugeConfig L))) /
        (L : ℝ) ^ 4 := by
  set P : Measure (GaugeConfig L) := (wilsonProbability L β hβ : Measure (GaugeConfig L))
  have hint : ∀ q : Plaquette L, Integrable (fun U => plaquetteAction U q) P := fun q =>
    (continuous_plaquetteAction q).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hT : ∀ x : Lattice4D L,
      ∫ U, plaquetteAction U ⟨x, p.μ, p.ν, p.h⟩ ∂P = ∫ U, plaquetteAction U p ∂P := by
    intro x
    have hinv := congrArg ProbabilityMeasure.toMeasure
      (wilsonProbability_translation_invariant L β hβ (x - p.x))
    simp only [ProbabilityMeasure.toMeasure_map] at hinv
    have hfun : (fun U => plaquetteAction U ⟨x, p.μ, p.ν, p.h⟩) =
        fun U => plaquetteAction (latticeTranslate (x - p.x) U) p := by
      funext U
      rw [plaquetteAction_latticeTranslate]
      congr 1
      simp [plaquetteTranslationEquiv]
    rw [hfun, ← integral_map (continuous_latticeTranslate _).aemeasurable
      (continuous_plaquetteAction p).aestronglyMeasurable]
    change ∫ U, plaquetteAction U p ∂(Measure.map (latticeTranslate (x - p.x)) P) = _
    rw [hinv]
  have hsum_le : ∫ U, ∑ x : Lattice4D L, plaquetteAction U ⟨x, p.μ, p.ν, p.h⟩ ∂P ≤
      ∫ U, wilsonAction 1 U ∂P := by
    apply integral_mono (integrable_finsetSum _ fun x _ => hint _)
      ((continuous_wilsonAction 1).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
    intro U
    dsimp only
    have hemb : Function.Injective (fun x : Lattice4D L => (⟨x, p.μ, p.ν, p.h⟩ : Plaquette L)) :=
      fun x y hxy => congrArg Plaquette.x hxy
    let e : Lattice4D L ↪ Plaquette L := ⟨_, hemb⟩
    have h1 : ∑ x : Lattice4D L, plaquetteAction U ⟨x, p.μ, p.ν, p.h⟩ =
        ∑ q ∈ Finset.univ.map e, plaquetteAction U q := by
      rw [Finset.sum_map]
      rfl
    rw [h1]
    simp only [wilsonAction, one_mul]
    exact Finset.sum_le_univ_sum_of_nonneg fun q => plaquetteAction_nonneg U q
  rw [integral_finsetSum _ fun x _ => hint _] at hsum_le
  simp only [hT, Finset.sum_const, Finset.card_univ, card_lattice4D, nsmul_eq_mul,
    Nat.cast_pow] at hsum_le
  have hL : 0 < (L : ℝ) ^ 4 := pow_pos (Nat.cast_pos.mpr (NeZero.pos L)) 4
  rw [le_div_iff₀ hL]
  linarith

/-- The mean deficit of every physical plaquette average is at most the mean action density. -/
theorem integral_one_sub_physicalPlaquetteAverage_le (L : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    (a : ℝ) (R : PhysicalPlaquetteRegion) :
    ∫ U, (1 - physicalPlaquetteAverage L a R U)
        ∂(wilsonProbability L β hβ : Measure (GaugeConfig L)) ≤
      (∫ U, wilsonAction 1 U ∂(wilsonProbability L β hβ : Measure (GaugeConfig L))) /
        (L : ℝ) ^ 4 := by
  set P : Measure (GaugeConfig L) := (wilsonProbability L β hβ : Measure (GaugeConfig L))
  set D := (∫ U, wilsonAction 1 U ∂P) / (L : ℝ) ^ 4
  have hint : ∀ q : Plaquette L, Integrable (fun U => plaquetteAction U q) P := fun q =>
    (continuous_plaquetteAction q).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hfun : (fun U => 1 - physicalPlaquetteAverage L a R U) = fun U =>
      (∑ k : Fin 4 → Fin (R.sites a), plaquetteAction U (R.plaquetteAt L a k)) /
        (R.sites a : ℝ) ^ 4 := by
    funext U
    unfold physicalPlaquetteAverage
    ring
  rw [hfun, integral_div, integral_finsetSum _ fun k _ => hint _]
  have hterm : ∀ k : Fin 4 → Fin (R.sites a),
      ∫ U, plaquetteAction U (R.plaquetteAt L a k) ∂P ≤ D :=
    fun k => integral_plaquetteAction_le_density L β hβ _
  have hsum : ∑ k : Fin 4 → Fin (R.sites a), ∫ U, plaquetteAction U (R.plaquetteAt L a k) ∂P ≤
      ∑ _k : Fin 4 → Fin (R.sites a), D :=
    Finset.sum_le_sum fun k _ => hterm k
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow] at hsum
  rw [div_le_iff₀ (sites_pow_pos R a)]
  linarith

/-- Along every cutoff path whose coupling diverges, the joint law of all physical-scale
plaquette averages converges, for the full sequence, to the Dirac law at the all-ones vector.
The limit is the collapsed configuration of the unrenormalized observables: it carries no
fluctuation and no continuum information. -/
theorem CutoffPath.plaquetteAverageLaw_tendsto (P : CutoffPath)
    (hβ : Tendsto P.coupling atTop atTop) :
    Tendsto P.plaquetteAverageLaw atTop (𝓝 (diracProba (fun _ => (1 : ℝ)))) := by
  have hD := haarWilsonMeanActionDensity_tendsto_varying_volume P.side P.coupling hβ
  apply tendsto_of_forall_isOpen_le_liminf'
  intro G hG
  by_cases h1 : (fun _ => (1 : ℝ)) ∈ G
  swap
  · change Measure.dirac (fun _ => (1 : ℝ)) G ≤ _
    rw [Measure.dirac_apply' _ hG.measurableSet, Set.indicator_of_notMem h1]
    exact zero_le
  -- the complement of `G` loses all mass
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hG _ h1
  have hcoord : ∀ R ∈ I, Tendsto (fun n => (P.plaquetteAverageLaw n : Measure PlaquetteAverageSpace)
      {w | w R ∉ u R}) atTop (𝓝 0) := by
    intro R hR
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hu R hR).1 1 (hu R hR).2
    have hmeas : MeasurableSet {w : PlaquetteAverageSpace | w R ∉ u R} :=
      ((hu R hR).1.measurableSet.compl).preimage (continuous_apply R).measurable
    have hbound : ∀ n, (P.plaquetteAverageLaw n : Measure PlaquetteAverageSpace)
        {w | w R ∉ u R} ≤ ENNReal.ofReal
          ((∫ U, wilsonAction 1 U ∂(P.configLaw n : Measure (GaugeConfig (P.side n)))) /
            (P.side n : ℝ) ^ 4 / ε) := by
      intro n
      set Q : Measure (GaugeConfig (P.side n)) := (P.configLaw n).toMeasure
      rw [CutoffPath.plaquetteAverageLaw, ProbabilityMeasure.toMeasure_map,
        Measure.map_apply (continuous_plaquetteAverageVector _ _).measurable hmeas]
      have hsubset : plaquetteAverageVector (P.side n) (P.spacing n) ⁻¹' {w | w R ∉ u R} ⊆
          {U | ε ≤ 1 - physicalPlaquetteAverage (P.side n) (P.spacing n) R U} := by
        intro U hU
        simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hU ⊢
        by_contra hlt
        have hlt' := lt_of_not_ge hlt
        apply hU
        apply hball
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        have hle := physicalPlaquetteAverage_le_one (P.spacing n) R U
        change -ε < physicalPlaquetteAverage (P.side n) (P.spacing n) R U - 1 ∧
          physicalPlaquetteAverage (P.side n) (P.spacing n) R U - 1 < ε
        constructor <;> linarith
      have hf_nonneg : 0 ≤ᵐ[Q] fun U => 1 - physicalPlaquetteAverage (P.side n) (P.spacing n) R U :=
        Eventually.of_forall fun U => by
          have := physicalPlaquetteAverage_le_one (P.spacing n) R U
          simp only [Pi.zero_apply]
          linarith
      have hf_int : Integrable
          (fun U => 1 - physicalPlaquetteAverage (P.side n) (P.spacing n) R U) Q :=
        (continuous_const.sub (continuous_physicalPlaquetteAverage _ _ R)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      have hmarkov := mul_meas_ge_le_integral_of_nonneg hf_nonneg hf_int ε
      have hmean := integral_one_sub_physicalPlaquetteAverage_le (P.side n) (P.coupling n)
        (P.coupling_nonneg n) (P.spacing n) R
      have hreal : Q.real {U | ε ≤ 1 - physicalPlaquetteAverage (P.side n) (P.spacing n) R U} ≤
          (∫ U, wilsonAction 1 U ∂Q) / (P.side n : ℝ) ^ 4 / ε := by
        rw [le_div_iff₀ hε]
        change (∫ U, 1 - physicalPlaquetteAverage (P.side n) (P.spacing n) R U ∂Q) ≤
          (∫ U, wilsonAction 1 U ∂Q) / (P.side n : ℝ) ^ 4 at hmean
        linarith
      calc Q (plaquetteAverageVector (P.side n) (P.spacing n) ⁻¹' {w | w R ∉ u R})
          ≤ Q {U | ε ≤ 1 - physicalPlaquetteAverage (P.side n) (P.spacing n) R U} :=
            measure_mono hsubset
        _ = ENNReal.ofReal (Q.real
              {U | ε ≤ 1 - physicalPlaquetteAverage (P.side n) (P.spacing n) R U}) :=
            (ofReal_measureReal).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal hreal
    have hlim : Tendsto (fun n => ENNReal.ofReal
        ((∫ U, wilsonAction 1 U ∂(P.configLaw n : Measure (GaugeConfig (P.side n)))) /
          (P.side n : ℝ) ^ 4 / ε)) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n => (∫ U, wilsonAction 1 U
          ∂(P.configLaw n : Measure (GaugeConfig (P.side n)))) / (P.side n : ℝ) ^ 4 / ε)
          atTop (𝓝 (0 / ε)) := hD.div_const ε
      rw [zero_div] at h0
      simpa using ENNReal.tendsto_ofReal h0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n => zero_le) hbound
  have hcompl : Tendsto (fun n => (P.plaquetteAverageLaw n : Measure PlaquetteAverageSpace) Gᶜ)
      atTop (𝓝 0) := by
    have hsum : Tendsto (fun n => ∑ R ∈ I,
        (P.plaquetteAverageLaw n : Measure PlaquetteAverageSpace) {w | w R ∉ u R})
        atTop (𝓝 0) := by
      simpa using tendsto_finsetSum I hcoord
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun n => zero_le) (fun n => ?_)
    calc (P.plaquetteAverageLaw n : Measure PlaquetteAverageSpace) Gᶜ
        ≤ (P.plaquetteAverageLaw n : Measure PlaquetteAverageSpace)
            (⋃ R ∈ I, {w | w R ∉ u R}) := by
          apply measure_mono
          intro w hw
          simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
          by_contra hall
          simp only [not_exists, not_and, not_not] at hall
          exact hw (hsub fun R hR => hall R hR)
      _ ≤ _ := measure_biUnion_finset_le I _
  have hG1 : Tendsto (fun n => (P.plaquetteAverageLaw n : Measure PlaquetteAverageSpace) G)
      atTop (𝓝 1) := by
    have h := ENNReal.Tendsto.sub tendsto_const_nhds hcompl (Or.inl ENNReal.one_ne_top)
    rw [tsub_zero] at h
    refine h.congr fun n => ?_
    rw [← prob_compl_eq_one_sub hG.measurableSet.compl, compl_compl]
  change Measure.dirac (fun _ => (1 : ℝ)) G ≤ _
  rw [Measure.dirac_apply' _ hG.measurableSet, Set.indicator_of_mem h1, hG1.liminf_eq]
  rfl

/-- Along a continuum cutoff path the bare coupling diverges: this follows from the one-loop
trajectory field and `a → 0`. -/
theorem ContinuumCutoffPath.coupling_tendsto_atTop (P : ContinuumCutoffPath) :
    Tendsto P.coupling atTop atTop := by
  have hlog : Tendsto (fun n => Real.log (1 / P.spacing n)) atTop atTop := by
    have h0 : Tendsto P.spacing atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨P.spacing_tendsto_zero, Eventually.of_forall P.spacing_pos⟩
    have hinv : Tendsto (fun n => (P.spacing n)⁻¹) atTop atTop :=
      tendsto_inv_nhdsGT_zero.comp h0
    have hfun : (fun n => Real.log (1 / P.spacing n)) = Real.log ∘ fun n => (P.spacing n)⁻¹ := by
      funext n
      simp only [Function.comp_apply, one_div]
    rw [hfun]
    exact Real.tendsto_log_atTop.comp hinv
  have hc : (0 : ℝ) < P.beta0 := P.beta0_pos
  have hmul := Tendsto.pos_mul_atTop hc P.coupling_asymptoticFreedom hlog
  refine hmul.congr' ?_
  filter_upwards [hlog.eventually (eventually_gt_atTop 0)] with n hn
  exact div_mul_cancel₀ (P.coupling n) hn.ne'

/-- Along every continuum cutoff path the joint law of the unrenormalized physical plaquette
averages converges to the Dirac law at the all-ones vector. This is full convergence to a
collapsed limit, the failure mode that renormalization has to remove. -/
theorem ContinuumCutoffPath.plaquetteAverageLaw_tendsto (P : ContinuumCutoffPath) :
    Tendsto P.plaquetteAverageLaw atTop (𝓝 (diracProba (fun _ => (1 : ℝ)))) :=
  P.toCutoffPath.plaquetteAverageLaw_tendsto P.coupling_tendsto_atTop

/-! ### Multistep Observable Transport Telescope (R3) & Renormalized Continuum Cauchy Control -/

/-- Exact telescoping identity and triangle-inequality defect bound for any sequence of
step-`k` transported observable expectations or connected covariances `C : ℕ → ℝ` across
`K` blocking steps (`k = 0, …, K - 1`):
`C K - C 0 = ∑ k ∈ Finset.range K, (C (k + 1) - C k)` and
`|C K - C 0| ≤ ∑ k ∈ Finset.range K, |C (k + 1) - C k|`. -/
theorem multistep_observable_transport_telescope (C : ℕ → ℝ) (K : ℕ) :
    C K - C 0 = ∑ k ∈ Finset.range K, (C (k + 1) - C k) ∧
    |C K - C 0| ≤ ∑ k ∈ Finset.range K, |C (k + 1) - C k| := by
  have htel : C K - C 0 = ∑ k ∈ Finset.range K, (C (k + 1) - C k) := by
    induction K with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ← ih]
      ring
  refine ⟨htel, ?_⟩
  rw [htel]
  exact Finset.abs_sum_le_sum_abs (fun k => C (k + 1) - C k) (Finset.range K)

/-- Multistep observable transport covariance preservation under summable step defects:
if the coarse/IR reference covariance satisfies `c_floor ≤ C 0` (such as
`c_floor = (3 / 4) * 4 ^ (-5) * β ^ 4` from the single-step transfer floor `R1`) and each
blocking-step transport defect satisfies `|C (k + 1) - C k| ≤ δ k` with cumulative defect
`∑ k ∈ Finset.range K, δ k ≤ c_floor / 2`, then the `K`-step transported UV observable
covariance satisfies `c_floor / 2 ≤ C K` and `(∑ k ∈ Finset.range K, δ k) ≤ (1 / 2) * c_floor`. -/
theorem multistep_transport_covariance_lower_bound_of_step_defects
    (C δ : ℕ → ℝ) (K : ℕ) (c_floor : ℝ)
    (h_floor : c_floor ≤ C 0)
    (h_step : ∀ k ∈ Finset.range K, |C (k + 1) - C k| ≤ δ k)
    (h_sum : ∑ k ∈ Finset.range K, δ k ≤ c_floor / 2) :
    c_floor / 2 ≤ C K ∧ (∑ k ∈ Finset.range K, δ k) ≤ (1 / 2) * c_floor := by
  have htel := (multistep_observable_transport_telescope C K).2
  have hbound : |C K - C 0| ≤ ∑ k ∈ Finset.range K, δ k :=
    htel.trans (Finset.sum_le_sum h_step)
  have hlow : -(∑ k ∈ Finset.range K, δ k) ≤ C K - C 0 :=
    (abs_le.mp hbound).1
  constructor
  · linarith
  · linarith

/-- Iterated `K`-step fiber-covariance decomposition (`R3` bridge for `YangMillsObservableTransport`):
if at each dyadic blocking step `k < K` the scale-`k` covariance decomposes into the blocked
scale-`(k + 1)` covariance plus the integrated Haar fiber covariance `Δ_fiber k`
(`C k = C (k + 1) + Δ_fiber k`, matching `wilson_covariance_transport`), then:
1. Exact `K`-step identity: `C 0 = C K + ∑ k ∈ Finset.range K, Δ_fiber k`,
2. Defect bound: `|C 0 - C K| ≤ ∑ k ∈ Finset.range K, |Δ_fiber k|`, and
3. Lower-bound preservation: if `c_floor ≤ C K` and `∑ k ∈ Finset.range K, |Δ_fiber k| ≤ c_floor / 2`,
   then `c_floor / 2 ≤ C 0`. -/
theorem iterated_fiber_covariance_transport_decomposition
    (C Δ_fiber : ℕ → ℝ) (K : ℕ) (c_floor : ℝ)
    (h_one_step : ∀ k ∈ Finset.range K, C k = C (k + 1) + Δ_fiber k) :
    C 0 = C K + ∑ k ∈ Finset.range K, Δ_fiber k ∧
    |C 0 - C K| ≤ ∑ k ∈ Finset.range K, |Δ_fiber k| ∧
    (c_floor ≤ C K → (∑ k ∈ Finset.range K, |Δ_fiber k|) ≤ c_floor / 2 → c_floor / 2 ≤ C 0) := by
  have h_diff (k : ℕ) (hk : k ∈ Finset.range K) : C (k + 1) - C k = -Δ_fiber k := by
    linarith [h_one_step k hk]
  have h_tel := (multistep_observable_transport_telescope C K).1
  have h_sum_neg :
      ∑ k ∈ Finset.range K, (C (k + 1) - C k) = -∑ k ∈ Finset.range K, Δ_fiber k := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl h_diff
  have h_eq : C 0 = C K + ∑ k ∈ Finset.range K, Δ_fiber k := by
    linarith [h_tel, h_sum_neg]
  have h_abs : |C 0 - C K| ≤ ∑ k ∈ Finset.range K, |Δ_fiber k| := by
    have h_sub : C 0 - C K = ∑ k ∈ Finset.range K, Δ_fiber k := by linarith
    rw [h_sub]
    exact Finset.abs_sum_le_sum_abs Δ_fiber (Finset.range K)
  refine ⟨h_eq, h_abs, ?_⟩
  intro h_floor h_defect
  have h_lo : -(∑ k ∈ Finset.range K, |Δ_fiber k|) ≤ C 0 - C K := (abs_le.mp h_abs).1
  linarith

/-- Uniform geometric defect series bound across arbitrary blocking depth `K : ℕ`:
for a geometrically decaying per-step localization/polymer transport defect `δ k = δ₀ * q ^ k`
with `0 ≤ δ₀`, `0 ≤ q`, and `q < 1`, the cumulative `K`-step defect satisfies
`∑ k ∈ Finset.range K, (δ₀ * q ^ k) ≤ δ₀ / (1 - q)` uniformly in `K`. -/
theorem geometric_transport_defect_sum_le
    (δ₀ q : ℝ) (K : ℕ)
    (hδ0 : 0 ≤ δ₀) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑ k ∈ Finset.range K, (δ₀ * q ^ k) ≤ δ₀ / (1 - q) := by
  have hgeom : (∑ k ∈ Finset.range K, (δ₀ * q ^ k)) * (1 - q) = δ₀ - δ₀ * q ^ K := by
    induction K with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, add_mul, ih, pow_succ]
      ring
  have hq_pos : 0 < 1 - q := by linarith
  have hprod_nonneg : 0 ≤ δ₀ * q ^ K := mul_nonneg hδ0 (pow_nonneg hq0 K)
  rw [le_div_iff₀ hq_pos, hgeom]
  linarith

/-- Quantitative Cauchy bound for renormalized continuum-approximating observable expectations
with geometric step increments: if `E : ℕ → ℝ` satisfies `|E (n + 1) - E n| ≤ A * q ^ n` with
`0 ≤ A`, `0 ≤ q`, and `q < 1`, then for all `m ≤ n`,
`|E n - E m| ≤ A * q ^ m / (1 - q)`.

Note: Establishing the per-step transport defect bound `|C (k + 1) - C k| ≤ δ₀ * q ^ k` (`R3`)
and uniform continuum correlation bounds for physical smeared observables in the actual 4D
non-Abelian gauge model remain open research obligations. -/
theorem renormalized_observable_cauchy_bound_of_geometric_increments
    (E : ℕ → ℝ) (A q : ℝ)
    (hA : 0 ≤ A) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (h_inc : ∀ n : ℕ, |E (n + 1) - E n| ≤ A * q ^ n)
    {m n : ℕ} (hmn : m ≤ n) :
    |E n - E m| ≤ A * q ^ m / (1 - q) := by
  obtain ⟨K, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hstep (k : ℕ) : |E (m + (k + 1)) - E (m + k)| ≤ (A * q ^ m) * q ^ k := by
    rw [← Nat.add_assoc m k 1]
    calc
      |E (m + k + 1) - E (m + k)| ≤ A * q ^ (m + k) := h_inc (m + k)
      _ = (A * q ^ m) * q ^ k := by
        rw [pow_add]
        ring
  calc
    |E (m + K) - E m|
      = |E (m + K) - E (m + 0)| := by rw [Nat.add_zero]
    _ ≤ ∑ k ∈ Finset.range K, |E (m + (k + 1)) - E (m + k)| :=
        (multistep_observable_transport_telescope (fun k => E (m + k)) K).2
    _ ≤ ∑ k ∈ Finset.range K, ((A * q ^ m) * q ^ k) :=
        Finset.sum_le_sum (fun k _ => hstep k)
    _ ≤ (A * q ^ m) / (1 - q) :=
        geometric_transport_defect_sum_le (A * q ^ m) q K
          (mul_nonneg hA (pow_nonneg hq0 m)) hq0 hq1

end JesseMath.Physics.YangMillsRenormalizedObservableLimits

#assert_zfc_axioms
