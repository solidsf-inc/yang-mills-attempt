import JesseMath.Linter.AxiomAudit
import JesseMath.Physics.YangMillsContinuumCompactness

/-!
# Constant-cutoff scope control for the Wave 4/5 transfer contracts

These are actual applications of the transfer theorems in
`YangMillsContinuumCompactness.lean`, with the genuine side-one, zero-coupling
periodic Wilson law. All cutoffs are constant and all tested observables vanish.
The transfer contracts hold although the side length does not tend to infinity.
This checks the scope of those contracts; it does not refute Yang--Mills.
An arbitrary positive scalar in the clustering envelope identifies no Hamiltonian.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace JesseMath.Physics.YangMillsSixWaveScopeControl

open YangMillsContinuumCompactness

abbrev cutoffSide : ℕ → ℕ := fun _ => 1
abbrev cutoffCoupling : ℕ → ℝ := fun _ => 0

instance : ∀ n, NeZero (cutoffSide n) := fun _ => inferInstanceAs (NeZero 1)

theorem cutoffCoupling_nonnegative (n : ℕ) : 0 ≤ cutoffCoupling n := le_rfl

def constantWilsonLaw : ProbabilityMeasure IntegerGaugeConfig :=
  periodicWilsonProbability 1 0 (le_refl 0)

theorem constantWilsonLaw_converges :
    Tendsto (fun n => periodicWilsonProbability (cutoffSide n) (cutoffCoupling n)
      (cutoffCoupling_nonnegative n)) atTop (𝓝 constantWilsonLaw) :=
  tendsto_const_nhds

def zeroObservable : C(IntegerGaugeConfig, ℝ) := 0
def zeroCylinder : C((Fin 1 → SU2), ℝ) := 0
def originEdge : Fin 1 → IntegerLink := fun _ => (0, 0)

/-- The actual reflection-positivity transfer accepts a zero kernel, at every
matrix size and with arbitrary real coefficients, on a constant finite cutoff. -/
theorem constant_cutoff_reflection_transfer (m : ℕ) (c : Fin m → ℝ) :
    Tendsto (fun n => wilsonExpectation (gaugeHaarMeasure (cutoffSide n)) (cutoffCoupling n)
      (fun U => cylinderObservable originEdge zeroCylinder (periodicLift (cutoffSide n) U)))
      atTop (𝓝 (∫ U, cylinderObservable originEdge zeroCylinder U ∂constantWilsonLaw)) ∧
    0 ≤ ∑ a : Fin m, ∑ b : Fin m,
      c a * c b * (∫ U, zeroObservable U ∂constantWilsonLaw) := by
  exact cylinderObservable_periodicWilsonProbability_tendsto_and_reflection_positivity_transfer
    cutoffSide cutoffCoupling cutoffCoupling_nonnegative constantWilsonLaw
    constantWilsonLaw_converges originEdge zeroCylinder m c (fun _ _ => zeroObservable)
    (by intro n; simp [zeroObservable, wilsonExpectation])

/-- Every positive candidate scalar rate satisfies the actual clustering transfer
for these zero observables. No operator or generator occurs in this acceptance. -/
theorem constant_cutoff_clustering_transfer (candidateGap dist : ℝ)
    (hgap : 0 < candidateGap) (hdist : 0 ≤ dist) :
    |(∫ U, (zeroObservable * zeroObservable) U ∂constantWilsonLaw) -
      (∫ U, zeroObservable U ∂constantWilsonLaw) *
        (∫ U, zeroObservable U ∂constantWilsonLaw)| ≤
      infiniteVolumeClusterEnvelope 0 candidateGap dist ∧
    (0 ≤ infiniteVolumeClusterEnvelope 0 candidateGap dist ∧
      infiniteVolumeClusterEnvelope 0 candidateGap dist ≤ 0) ∧
    Tendsto (fun d : ℝ => infiniteVolumeClusterEnvelope 0 candidateGap d) atTop (𝓝 0) := by
  exact periodicWilsonProbability_exponential_clustering_and_dobrushin_tail_transfer
    cutoffSide cutoffCoupling cutoffCoupling_nonnegative constantWilsonLaw
    constantWilsonLaw_converges zeroObservable zeroObservable (C_clust := 0)
    (m_gap := candidateGap) (dist := dist) (le_refl 0) hgap hdist
    (by intro n; simp [zeroObservable, wilsonExpectation, infiniteVolumeClusterEnvelope])

/-- The actual isotropy transfer also accepts equal zero observables and a zero
error sequence, without requiring a rotation action or a continuum scaling. -/
theorem constant_cutoff_isotropy_transfer :
    so4IsotropicCorrelatorDefect (∫ U, zeroObservable U ∂constantWilsonLaw)
      (∫ U, zeroObservable U ∂constantWilsonLaw) = 0 ∧
    (∫ U, zeroObservable U ∂constantWilsonLaw) =
      (∫ U, zeroObservable U ∂constantWilsonLaw) := by
  exact periodicWilsonProbability_so4_isotropy_recovery_and_correlator_convergence
    cutoffSide cutoffCoupling cutoffCoupling_nonnegative constantWilsonLaw
    constantWilsonLaw_converges zeroObservable zeroObservable (fun _ => 0)
    tendsto_const_nhds (by intro n; simp)

/-- The very same cutoff sequence in all three accepted transfers is finite and
constant. Therefore those transfer contracts alone cannot force volume growth. -/
theorem constant_cutoff_does_not_tend_to_infinite_volume :
    ¬ Tendsto cutoffSide atTop atTop :=
  not_tendsto_const_atTop 1 atTop

#assert_zfc_axioms

end JesseMath.Physics.YangMillsSixWaveScopeControl
