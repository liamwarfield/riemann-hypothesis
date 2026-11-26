module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHermExtend

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsConjInvariantMollifier
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace LevelTowerAlt

theorem contDiff_star (n : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : Fin n → ℂ => star v) := (starL' ℝ : (Fin n → ℂ) ≃L[ℝ] (Fin n → ℂ)).contDiff

end LevelTowerAlt
end

section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.DeterminantLatticeGenerator
open AlgebraicGeometry CategoryTheory Matrix
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace LevelTowerAlt

namespace N1

section

variable {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V] {r : ℕ}

theorem mat_unique {b₀ : Fin r → V} (h₀ : LinearIndependent Ω b₀) {T T' : Matrix (Fin r) (Fin r) Ω}
    (h : ∀ k, ∑ k', T k' k • b₀ k' = ∑ k', T' k' k • b₀ k') : T = T' := by
  ext k' k
  exact (Fintype.linearIndependent_iffₛ.1 h₀) (fun a => T a k) (fun a => T' a k) (h k) k'

theorem mat_comp {b₀ b b' : Fin r → V} {T A : Matrix (Fin r) (Fin r) Ω}
    (h : ∀ k, b k = ∑ k', T k' k • b₀ k') (h' : ∀ k, b' k = ∑ k', A k' k • b k') (k : Fin r) :
    b' k = ∑ k', (T * A) k' k • b₀ k' := by
  rw [h' k]
  simp only [h, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

theorem exists_mat (R : Subring Ω) {b b' : Fin r → V} (h : ∀ k, b' k ∈ Submodule.span R (Set.range b)) :
    ∃ A : Matrix (Fin r) (Fin r) Ω, (∀ k, b' k = ∑ k', A k' k • b k') ∧ A.det ∈ R := by
  choose c hc using fun k => (Submodule.mem_span_range_iff_exists_fun R).1 (h k)
  refine ⟨R.subtype.mapMatrix (Matrix.of fun k' k => c k k'), fun k => ?_, ?_⟩
  · rw [← hc k]; rfl
  · rw [← RingHom.map_det]; exact SetLike.coe_mem _

theorem det_ne_zero {b₀ b : Fin r → V} {T : Matrix (Fin r) (Fin r) Ω} (hb : LinearIndependent Ω b)
    (h : ∀ k, b k = ∑ k', T k' k • b₀ k') : T.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hT⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  refine hv (funext (Fintype.linearIndependent_iff.1 hb v ?_))
  simp only [h, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k' _ => ?_
  rw [← Finset.sum_smul]
  have := congrFun hT k'
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
  rw [show ∑ i, v i * T k' i = 0 from by rw [← this]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _, zero_smul]

end

end N1

open N1

theorem determinant_lattice_generator : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (L : Lat ξ V) (r : ℕ) (b₀ b : Fin r → V) (T : Matrix (Fin r) (Fin r) Ω) (p : Cpt ξ), LinearIndependent Ω b₀ → L.IsFrameAt b p → (∀ k, b k = ∑ k', T k' k • b₀ k') → (detLat L b₀).IsGenAt p T.det := by
  intro X Ω _ ξ V _ _ L r b₀ b T p h₀ hb hT
  refine ⟨det_ne_zero hb.1 hT, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨b', T', hb', hT', rfl⟩
    obtain ⟨A, hA, hd⟩ := exists_mat (regAt ξ p) (b := b) (b' := b') fun k => by
      rw [← hb.2, hb'.2]; exact Submodule.subset_span ⟨k, rfl⟩
    have e : T' = T * A := mat_unique h₀ fun k => by rw [← hT' k, ← mat_comp hT hA k]
    rw [e, Matrix.det_mul, mul_comm]
    exact Submodule.mem_span_singleton.2 ⟨⟨A.det, hd⟩, rfl⟩
  · exact Submodule.span_le.2 (Set.singleton_subset_iff.2 (SncPiece.det_mem_detLat hb hT))

end LevelTowerAlt
end

section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.ContDiffAtLogH
open Filter Topology Metric
open scoped ContDiff
open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open ReciprocityTheory.AnForm (levi levi_comp levi_congr levi_add_smul levi_re_analytic)

namespace LevelTowerAlt

theorem levi_disc {ι : Type} [Fintype ι] {φ : (ι → ℂ) → ℝ} {δ : ℂ → ι → ℂ} {z w : ι → ℂ} (hδ : AnalyticAt ℂ δ 0)
    (hd : HasDerivAt δ w 0) (h0 : δ 0 = z) (hφ : ContDiffAt ℝ 2 φ z) :
    levi φ z w = levi (fun s : Fin 1 → ℂ => φ (δ (s 0))) 0 (fun _ => 1) := by
  subst h0
  have hτ : AnalyticAt ℂ (fun s : Fin 1 → ℂ => δ (s 0)) 0 :=
    AnalyticAt.comp (g := δ) (f := fun s : Fin 1 → ℂ => s 0) hδ
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt 0)
  have h := HasFDerivAt.comp (0 : Fin 1 → ℂ) (g := δ) (f := fun s : Fin 1 → ℂ => s 0) hd.hasFDerivAt
    (hasFDerivAt_apply 0 0)
  have h2 : fderiv ℂ (fun s : Fin 1 → ℂ => δ (s 0)) 0 (fun _ => 1) = w := by
    rw [show fderiv ℂ (fun s : Fin 1 → ℂ => δ (s 0)) 0 = _ from h.fderiv]
    simp
  have h3 := levi_comp (φ := φ) (τ := fun s : Fin 1 → ℂ => δ (s 0)) (z := 0) (fun _ => 1) hτ hφ
  rw [h2] at h3
  exact h3.symm

theorem levi_add_re {ι : Type} [Fintype ι] {f g : (ι → ℂ) → ℝ} {G : (ι → ℂ) → ℂ} {z : ι → ℂ}
    (hg : ContDiffAt ℝ 2 g z) (hG : AnalyticAt ℂ G z) (h : ∀ᶠ y in 𝓝 z, f y = g y + (G y).re) (w : ι → ℂ) :
    levi f z w = levi g z w := by
  have hR : AnalyticAt ℝ G z := hG.restrictScalars
  have hre : ContDiffAt ℝ 2 (fun y => (G y).re) z := Complex.reCLM.contDiff.contDiffAt.comp z hR.contDiffAt
  have h' : f =ᶠ[𝓝 z] fun y => g y + 1 * (G y).re := h.mono fun y hy => by simp only [hy, one_mul]
  rw [levi_congr h', levi_add_smul 1 hg hre, levi_re_analytic hG, mul_zero, add_zero]

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem log_h_smul (A : HermLine J) {z : (Σ k, J k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) {c : K → ℂ}
    (hc : ∀ k, c k ≠ 0) :
    Real.log (A.h (torusSmul c z)) = Real.log (A.h z) + ∑ k, (A.a k : ℝ) * Real.log ‖c k‖ := by
  have hp : ∀ k, ‖c k‖ ^ A.a k ≠ 0 := fun k => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  change Real.log (A.h fun p => c p.1 * z p) = _
  rw [A.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => hp k) (A.pos z hz).ne',
    Real.log_prod fun k _ => hp k, add_comm]
  simp only [Real.log_zpow]

theorem contDiffAt_log_h {A : HermLine J} (hA : IsSmoothHerm A) {z : (Σ k, J k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ContDiffAt ℝ 2 (fun z => Real.log (A.h z)) z :=
  ((ContDiffOn.contDiffAt hA (HermExtend.isOpen_blocksNe.mem_nhds hz)).log (A.pos z hz).ne').of_le
    (WithTop.coe_le_coe.2 le_top)

end LevelTowerAlt
end
