module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IotaOQContinuousInjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeEqStdPowerSeriesAtZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDecompositionBaseChange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNeZeroPs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralWittLatticeBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralWittLatticeBasis
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.SatLattice

section abstract

variable {R : Type} [CommRing R] [IsDomain R] {π : R} (O : Subring R)

theorem pid_of_fact (hπ : Irreducible π) (hO : π ∈ O)
    (h4 : ∀ w ∈ O, w ≠ 0 → ∃ (k : ℕ) (v v' : R), v ∈ O ∧ v' ∈ O ∧ v * v' = 1 ∧ w = π ^ k * v) :
    IsPrincipalIdealRing O := by
  have hu : ∀ a : O, IsUnit (a : R) → IsUnit a := by
    intro a ha
    obtain ⟨k, v, v', hv, hv', h1, h2⟩ := h4 a a.2 ha.ne_zero
    rcases k with _ | k
    · refine IsUnit.of_mul_eq_one (⟨v', hv'⟩ : O) (Subtype.ext ?_)
      simp [h2, h1]
    · exfalso
      rw [h2, pow_succ', mul_assoc] at ha
      exact hπ.not_isUnit (isUnit_of_mul_isUnit_left ha)
  have hirr : Irreducible (⟨π, hO⟩ : O) := by
    refine ⟨fun h => hπ.not_isUnit (h.map O.subtype), fun a b hab => ?_⟩
    exact (hπ.isUnit_or_isUnit (congrArg Subtype.val hab)).imp (hu a) (hu b)
  have : IsDiscreteValuationRing O := by
    refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨_, hirr, ?_⟩
    intro x hx
    obtain ⟨k, v, v', hv, hv', h1, h2⟩ := h4 x x.2 (fun h => hx (Subtype.ext h))
    refine ⟨k, ⟨⟨v, hv⟩, ⟨v', hv'⟩, Subtype.ext h1, Subtype.ext (by simp [mul_comm v' v, h1])⟩, Subtype.ext ?_⟩
    simp [h2]
  infer_instance

theorem sat_pow (hπ : π ≠ 0) (h1 : ∀ w ∈ O, π ∣ w → ∃ v ∈ O, w = π * v) (n : ℕ) (x : R)
    (hx : π ^ n * x ∈ O) : x ∈ O := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    obtain ⟨v, hv, h⟩ := h1 _ hx ⟨π ^ n * x, by ring⟩
    refine ih ?_
    have : π ^ n * x = v := mul_left_cancel₀ hπ (by rw [← h]; ring)
    rwa [this]

def divSub {d : ℕ} (Y : Matrix (Fin d) (Fin d) R) (a : R) : Submodule O (Fin d → O) where
  carrier := {x | ∀ i, a ∣ (Y *ᵥ fun j => (x j : R)) i}
  zero_mem' i := by
    simp [Matrix.mulVec, dotProduct]
  add_mem' {x y} hx hy i := by
    have : (fun j => ((x + y) j : R)) = (fun j => (x j : R)) + fun j => (y j : R) := rfl
    rw [this, Matrix.mulVec_add]
    exact dvd_add (hx i) (hy i)
  smul_mem' c x hx i := by
    have : (fun j => ((c • x) j : R)) = (c : R) • fun j => (x j : R) := rfl
    rw [this, Matrix.mulVec_smul]
    exact Dvd.dvd.mul_left (hx i) _

theorem exists_basis_matrix [IsPrincipalIdealRing O] {d : ℕ} (Y : Matrix (Fin d) (Fin d) R) (a : R) (ha : a ≠ 0)
    (haO : a ∈ O) :
    ∃ P : Matrix (Fin d) (Fin d) R, (∀ i j, P i j ∈ O) ∧ P.det ≠ 0 ∧ (∀ i j, a ∣ (Y * P) i j) ∧
      ∀ x : Fin d → R, (∀ i, x i ∈ O) → (∀ i, a ∣ (Y *ᵥ x) i) →
        ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ x = P *ᵥ w := by
  set N := divSub O Y a with hN
  have hmem : ∀ v : Fin d → O, (⟨a, haO⟩ : O) • v ∈ N := by
    intro v i
    have : (fun j => (((⟨a, haO⟩ : O) • v) j : R)) = a • fun j => (v j : R) := rfl
    rw [this, Matrix.mulVec_smul]
    exact Dvd.intro _ rfl
  let f : (Fin d → O) →ₗ[O] N := LinearMap.codRestrict N ((⟨a, haO⟩ : O) • LinearMap.id) hmem
  have hf : Function.Injective f := by
    intro v w h
    funext i
    have := congrArg (fun z : N => ((z.1 i : O) : R)) h
    exact Subtype.ext (mul_left_cancel₀ ha this)
  have hr : Module.finrank O N = d := by
    apply le_antisymm
    · simpa using N.finrank_le
    · simpa using LinearMap.finrank_le_finrank_of_injective hf
  let b := Module.finBasisOfFinrankEq O N hr
  let P : Matrix (Fin d) (Fin d) R := Matrix.of fun i j => ((b j).1 i : R)
  have hspan : ∀ x : Fin d → R, (∀ i, x i ∈ O) → (∀ i, a ∣ (Y *ᵥ x) i) →
        ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ x = P *ᵥ w := by
    intro x hx hd
    let z : N := ⟨fun i => ⟨x i, hx i⟩, hd⟩
    refine ⟨fun j => (b.repr z j : R), fun j => (b.repr z j).2, funext fun i => ?_⟩
    have := congrArg (fun z : N => ((z.1 i : O) : R)) (b.sum_repr z)
    refine Eq.trans this.symm ?_
    rw [Submodule.coe_sum, Finset.sum_apply, AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  refine ⟨P, fun i j => ((b j).1 i).2, ?_, fun i j => (b j).2 i, hspan⟩
  have hcol : ∀ j : Fin d, ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ a • (Pi.single j 1 : Fin d → R) = P *ᵥ w := by
    intro j
    refine hspan _ (fun i => ?_) (fun i => ?_)
    · by_cases h : i = j
      · simp [h, haO]
      · simp [h]
    · rw [Matrix.mulVec_smul]
      exact Dvd.intro _ rfl
  choose w _ hw using hcol
  have hPQ : P * Matrix.of (fun i j => w j i) = a • (1 : Matrix (Fin d) (Fin d) R) := by
    ext i j
    have := congrFun (hw j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Pi.single_apply] at this
    simp [Matrix.mul_apply, ← this, Matrix.one_apply]
  intro h0
  have := congrArg Matrix.det hPQ
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at this
  exact pow_ne_zero _ ha this.symm

theorem lattice_abstract [IsPrincipalIdealRing O] (hπ : π ≠ 0) (hO : π ∈ O)
    (h1 : ∀ w ∈ O, π ∣ w → ∃ v ∈ O, w = π * v) {d : ℕ} (Y : Matrix (Fin d) (Fin d) R) (c : ℕ) (u : Rˣ)
    (hdet : Y.det = π ^ c * u) :
    ∃ (m : ℕ) (P Y' : Matrix (Fin d) (Fin d) R), (∀ i j, P i j ∈ O) ∧ P.det ≠ 0 ∧ π ^ m • Y' = Y * P ∧
      (∀ v : Fin d → R, (∀ i, v i ∈ O) → ∀ n : ℕ, (∀ i, π ^ n ∣ (Y *ᵥ v) i) →
        ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ π ^ m • v = π ^ n • (P *ᵥ w)) ∧
      ∀ w : Fin d → R, (∀ i, w i ∈ O) → (∀ i, π ∣ (Y' *ᵥ w) i) → ∀ i, π ∣ w i := by
  obtain ⟨P, hPO, hP, hdv, hspan⟩ := exists_basis_matrix O Y (π ^ c) (pow_ne_zero _ hπ) (O.pow_mem hO c)
  choose y hy using hdv
  have hY' : π ^ c • Matrix.of y = Y * P := by
    ext i j
    simp [hy]
  have key : ∀ v : Fin d → R, (∀ i, v i ∈ O) → ∀ n : ℕ, (∀ i, π ^ n ∣ (Y *ᵥ v) i) →
        ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ π ^ c • v = π ^ n • (P *ᵥ w) := by
    intro v hv n hn
    choose z hz using hn
    have hz' : Y *ᵥ v = π ^ n • z := funext hz
    let x : Fin d → R := ((u⁻¹ : Rˣ) : R) • (Y.adjugate *ᵥ z)
    have hx : π ^ c • v = π ^ n • x := by
      have h := congrArg (fun t => ((u⁻¹ : Rˣ) : R) • (Y.adjugate *ᵥ t)) hz'
      simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.mulVec_smul, Matrix.smul_mulVec,
        Matrix.one_mulVec, hdet] at h
      rw [smul_smul, mul_left_comm, Units.inv_mul, mul_one, smul_comm] at h
      exact h
    have hYx : Y *ᵥ x = π ^ c • z := by
      simp only [x, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.mulVec_smul, Matrix.smul_mulVec,
        Matrix.one_mulVec, hdet]
      rw [smul_smul, mul_left_comm, Units.inv_mul, mul_one]
    obtain ⟨w, hw, hxw⟩ := hspan x (fun i => sat_pow O hπ h1 n _ (by
      have := congrFun hx i
      simp only [Pi.smul_apply, smul_eq_mul] at this
      rw [← this]
      exact O.mul_mem (O.pow_mem hO c) (hv i))) (fun i => by rw [hYx]; exact Dvd.intro _ rfl)
    exact ⟨w, hw, by rw [hx, hxw]⟩
  refine ⟨c, P, Matrix.of y, hPO, hP, hY', key, fun w hw hd => ?_⟩
  obtain ⟨w', -, h⟩ := key (P *ᵥ w) (fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact O.sum_mem fun j _ => O.mul_mem (hPO i j) (hw j)) (c + 1) (fun i => by
    rw [Matrix.mulVec_mulVec, ← hY', Matrix.smul_mulVec, pow_succ]
    exact mul_dvd_mul_left _ (hd i))
  have h2 : P *ᵥ (w - π • w') = 0 := by
    funext i
    have := congrFun h i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    refine mul_left_cancel₀ (pow_ne_zero c hπ) ?_
    linear_combination this
  have h3 := Matrix.eq_zero_of_mulVec_eq_zero hP h2
  intro i
  exact ⟨w' i, sub_eq_zero.1 (congrFun h3 i)⟩

end abstract

theorem exists_lattice_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (Y1 : Matrix (Fin d) (Fin d) (WCb l)), Y1.det ≠ 0 → ∃ (m : ℕ) (P Y' : Matrix (Fin d) (Fin d) (WCb l)), (∀ i j, P i j ∈ bk.OE) ∧ P.det ≠ 0 ∧ (l : WCb l) ^ m • Y' = Y1 * P ∧ (∀ v : Fin d → WCb l, (∀ i, v i ∈ bk.OE) → ∀ n : ℕ, (∀ i, (l : WCb l) ^ n ∣ (Y1 *ᵥ v) i) → ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (l : WCb l) ^ m • v = (l : WCb l) ^ n • (P *ᵥ w)) ∧ ∀ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) → (∀ i, (l : WCb l) ∣ (Y' *ᵥ w) i) → ∀ i, (l : WCb l) ∣ w i := by
  intro l _ K bk d Y1 hY
  obtain ⟨h1, -, -, h4, -⟩ := GlobalTheory.T.integral_elements_unit_factorization l K bk
  have hirr : Irreducible (l : WCb l) := WittVector.irreducible l
  have : PerfectRing (Cb l) l := by
    refine PerfectRing.ofSurjective _ l fun x => ?_
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
    obtain ⟨a', rfl⟩ := surjective_frobenius (OCb l) l a
    obtain ⟨b', rfl⟩ := surjective_frobenius (OCb l) l b
    exact ⟨algebraMap (OCb l) (Cb l) a' / algebraMap (OCb l) (Cb l) b', by
      simp [frobenius_def, div_pow, map_pow]⟩
  obtain ⟨c, u, hu⟩ := WittVector.exists_eq_pow_p_mul' Y1.det hY
  have := pid_of_fact bk.OE hirr (natCast_mem _ l) h4
  exact lattice_abstract bk.OE hirr.ne_zero (natCast_mem _ l) h1 Y1 c u hu

end GlobalTheory.SatLattice
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralWittLatticeBasisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralWittLattice_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (Y1 : Matrix (Fin d) (Fin d) (WCb l)), Y1.det ≠ 0 → ∃ (m : ℕ) (P Y' : Matrix (Fin d) (Fin d) (WCb l)), (∀ i j, P i j ∈ bk.OE) ∧ P.det ≠ 0 ∧ (l : WCb l) ^ m • Y' = Y1 * P ∧ (∀ v : Fin d → WCb l, (∀ i, v i ∈ bk.OE) → ∀ n : ℕ, (∀ i, (l : WCb l) ^ n ∣ (Y1 *ᵥ v) i) → ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (l : WCb l) ^ m • v = (l : WCb l) ^ n • (P *ᵥ w)) ∧ ∀ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) → (∀ i, (l : WCb l) ∣ (Y' *ᵥ w) i) → ∀ i, (l : WCb l) ∣ w i := by
  first | exact @GlobalTheory.SatLattice.exists_lattice_basis | exact GlobalTheory.SatLattice.exists_lattice_basis | (intros; apply GlobalTheory.SatLattice.exists_lattice_basis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantHermitianWeightForm
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEvalLeSumNormCoeff
namespace GlobalTheory.EvalNormCoefficientBound

theorem norm_eval_le_sum_norm_coeff {σ : Type} (P : MvPolynomial σ ℂ) (v : σ → ℂ)
    (hv : ∀ (s : σ), ‖v s‖ ≤ (1 : ℝ)) :
    ‖(MvPolynomial.eval v : MvPolynomial σ ℂ → ℂ) P‖ ≤
      ∑ d ∈ MvPolynomial.support P, ‖AddMonoidAlgebra.coeff P d‖ := by
  rw [MvPolynomial.eval_eq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun d _ => ?_))
  rw [norm_mul]
  have h1 : ‖∏ s ∈ d.support, v s ^ d s‖ ≤ 1 := by
    rw [norm_prod]
    refine Finset.prod_le_one₀ (fun s _ => norm_nonneg _) (fun s _ => ?_)
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (hv s)
  exact mul_le_of_le_one_right (norm_nonneg _) h1

end GlobalTheory.EvalNormCoefficientBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantHermitianWeightForm
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section
open MeasureTheory Topology Matrix

namespace GlobalTheory.InvFormBdd

theorem exists_form_of_bounded {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Subgroup (Matrix.GeneralLinearGroup ι ℂ)) (C : ℝ)
    (hC : ∀ h ∈ H, ∀ i j, ‖(h : Matrix ι ι ℂ) i j‖ ≤ C) :
    ∃ β : (ι → ℂ) →ₗ⋆[ℂ] (ι → ℂ) →ₗ[ℂ] ℂ, (∀ x y, β x y = starRingEnd ℂ (β y x)) ∧
      (∀ x, x ≠ 0 → 0 < (β x x).re) ∧
      ∀ h ∈ H, ∀ x y, β ((h : Matrix ι ι ℂ) *ᵥ x) ((h : Matrix ι ι ℂ) *ᵥ y) = β x y := by
  classical
  let A : Set (Matrix ι ι ℂ) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0:ℂ) C
  have hA : IsCompact A := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  let S : Set (Matrix.GeneralLinearGroup ι ℂ) :=
    Units.embedProduct (Matrix ι ι ℂ) ⁻¹' (A ×ˢ (MulOpposite.op '' A))
  have hS : IsCompact S := Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hA.prod (hA.image MulOpposite.continuous_op))
  have hHS : (H : Set (Matrix.GeneralLinearGroup ι ℂ)) ⊆ S := by
    intro h hh
    refine ⟨fun i _ j _ => ?_, ⟨(h⁻¹ : Matrix.GeneralLinearGroup ι ℂ).val, fun i _ j _ => ?_, rfl⟩⟩
    · simpa using hC h hh i j
    · simpa using hC _ (H.inv_mem hh) i j
  let K := H.topologicalClosure
  have hK : IsCompact (K : Set (Matrix.GeneralLinearGroup ι ℂ)) :=
    hS.of_isClosed_subset H.isClosed_topologicalClosure (closure_minimal hHS hS.isClosed)
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : MeasurableSpace K := borel K
  haveI : BorelSpace K := ⟨rfl⟩
  let μ : Measure K := Measure.haar
  let N : K → Matrix ι ι ℂ := fun k => ((k⁻¹ : K) : Matrix.GeneralLinearGroup ι ℂ).val
  have hN : Continuous N := Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv)
  let φ : K → (ι → ℂ) → (ι → ℂ) → ℂ := fun k x y => star (N k *ᵥ x) ⬝ᵥ (N k *ᵥ y)
  have hφc : ∀ x y, Continuous fun k => φ k x y := by
    intro x y
    have h1 : Continuous fun k => N k *ᵥ x := hN.matrix_mulVec continuous_const
    have h2 : Continuous fun k => N k *ᵥ y := hN.matrix_mulVec continuous_const
    exact (continuous_star.comp h1).dotProduct h2
  have hφi : ∀ x y, Integrable (fun k => φ k x y) μ := fun x y =>
    (hφc x y).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let β : (ι → ℂ) →ₗ⋆[ℂ] (ι → ℂ) →ₗ[ℂ] ℂ := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun x y => ∫ k, φ k x y ∂μ)
    (fun x x' y => by
      rw [← integral_add (hφi x y) (hφi x' y)]
      congr 1; funext k; simp [φ, Matrix.mulVec_add, add_dotProduct])
    (fun c x y => by
      rw [smul_eq_mul, ← integral_const_mul]
      congr 1; funext k; simp [φ, Matrix.mulVec_smul, smul_dotProduct])
    (fun x y y' => by
      rw [← integral_add (hφi x y) (hφi x y')]
      congr 1; funext k; simp [φ, Matrix.mulVec_add, dotProduct_add])
    (fun c x y => by
      rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
      congr 1; funext k; simp [φ, Matrix.mulVec_smul, dotProduct_smul])
  refine ⟨β, fun x y => ?_, fun x hx => ?_, fun h hh x y => ?_⟩
  · show ∫ k, φ k x y ∂μ = starRingEnd ℂ (∫ k, φ k y x ∂μ)
    rw [← integral_conj]
    congr 1; funext k
    set_option synthInstance.maxHeartbeats 100000 in
      simp [φ, dotProduct, map_sum, mul_comm]
  · show 0 < (∫ k, φ k x x ∂μ).re
    have e := integral_re (hφi x x)
    simp only [RCLike.re_to_complex] at e
    rw [← e]
    have hre : ∀ k, (φ k x x).re = ∑ i, ‖(N k *ᵥ x) i‖ ^ 2 := by
      intro k
      simp only [φ, dotProduct, Pi.star_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.star_def, Complex.conj_mul']
      norm_cast
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
      (Complex.continuous_re.comp (hφc x x)) (HasCompactSupport.of_compactSpace _) ?_ ?_
    · intro k
      simp only [Pi.zero_apply, Function.comp_apply, hre]
      exact Finset.sum_nonneg fun i _ => sq_nonneg _
    · simp only [Function.comp_apply, hre]
      have hN1 : N 1 = 1 := by simp [N]
      rw [hN1, Matrix.one_mulVec]
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
      refine ne_of_gt (Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, ?_⟩)
      have : x i ≠ 0 := hi
      positivity
  · show ∫ k, φ k ((h : Matrix ι ι ℂ) *ᵥ x) ((h : Matrix ι ι ℂ) *ᵥ y) ∂μ = ∫ k, φ k x y ∂μ
    have hhK : h ∈ K := H.le_topologicalClosure hh
    rw [← integral_mul_left_eq_self (μ := μ) (fun k => φ k x y) (⟨h, hhK⟩⁻¹ : K)]
    congr 1; funext k
    simp only [φ, N, _root_.mul_inv_rev, inv_inv, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec]

end GlobalTheory.InvFormBdd

noncomputable section
open MeasureTheory Topology Matrix

namespace GlobalTheory.InvFormBdd

theorem norm_eval_le {σ : Type} (P : MvPolynomial σ ℂ) (v : σ → ℂ) (hv : ∀ s, ‖v s‖ ≤ 1) :
    ‖MvPolynomial.eval v P‖ ≤ ∑ d ∈ P.support, ‖AddMonoidAlgebra.coeff P d‖ := by
  first
  | exact @_root_.GlobalTheory.EvalNormCoefficientBound.norm_eval_le_sum_norm_coeff
  | exact _root_.GlobalTheory.EvalNormCoefficientBound.norm_eval_le_sum_norm_coeff
  | (apply _root_.GlobalTheory.EvalNormCoefficientBound.norm_eval_le_sum_norm_coeff <;> assumption)
  | (intros; apply _root_.GlobalTheory.EvalNormCoefficientBound.norm_eval_le_sum_norm_coeff <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EvalNormCoefficientBound.norm_eval_le_sum_norm_coeff <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EvalNormCoefficientBound.norm_eval_le_sum_norm_coeff ..)

theorem norm_emb_le_one {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) L) (hg : g ∈ GQ0 L n) (τ : L →+* ℂ) (i j : Fin n) :
    ‖τ ((g : Matrix (Fin n) (Fin n) L) i j)‖ ≤ 1 := by
  have h1 : (g : Matrix (Fin n) (Fin n) L) * conjT (IsCMField.complexConj L : L →+* L) (g : Matrix (Fin n) (Fin n) L) = 1 := hg
  have h2 := congrFun (congrFun h1 i) i
  simp only [Matrix.mul_apply, conjT, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply_eq] at h2
  have h3 := congrArg τ h2
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_one] at h3
  have h4 : ∑ k, (‖τ ((g : Matrix (Fin n) (Fin n) L) i k)‖ ^ 2 : ℝ) = 1 := by
    have : ∑ k, ((‖τ ((g : Matrix (Fin n) (Fin n) L) i k)‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← h3]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [RingHom.coe_coe, IsCMField.complexEmbedding_complexConj, Complex.mul_conj']
      push_cast; rfl
    exact_mod_cast this
  have h5 : ‖τ ((g : Matrix (Fin n) (Fin n) L) i j)‖ ^ 2 ≤ 1 :=
    h4 ▸ Finset.single_le_sum (f := fun k => ‖τ ((g : Matrix (Fin n) (Fin n) L) i k)‖ ^ 2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  nlinarith [norm_nonneg (τ ((g : Matrix (Fin n) (Fin n) L) i j))]

end GlobalTheory.InvFormBdd


open GlobalTheory.InvFormBdd in
theorem GlobalTheory.InvFormBdd.exists_isInvForm : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n),
    ∃ β, IsInvForm a β := by
  intro L _ _ _ n a
  classical
  obtain ⟨_, ι, _, _, b, P, hP⟩ := a.alg
  let f : GQ L n →* Matrix.GeneralLinearGroup ι ℂ :=
    (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp a.ρ.asGroupHom
  have hf : ∀ γ, ((f γ : Matrix.GeneralLinearGroup ι ℂ) : Matrix ι ι ℂ) = LinearMap.toMatrix b b (a.ρ γ) := by
    intro γ; ext i j; simp [f, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply, Representation.asGroupHom_apply]
  let C : ℝ := ∑ i, ∑ j, ∑ d ∈ (P i j).support, ‖AddMonoidAlgebra.coeff (P i j) d‖
  have hC : ∀ h ∈ f.range, ∀ i j, ‖(h : Matrix ι ι ℂ) i j‖ ≤ C := by
    rintro _ ⟨γ, rfl⟩ i j
    have hγ := γ.2
    unfold GQ at hγ
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hγ
    obtain ⟨g, hg, e⟩ := hγ
    have e' : (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (g : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) := by
      rw [← e]; rfl
    rw [hf, hP γ g e']
    refine (norm_eval_le _ _ fun p => norm_emb_le_one g hg _ _ _).trans ?_
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ∑ d ∈ (P i j).support, ‖AddMonoidAlgebra.coeff (P i j) d‖)
      (fun i _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => ∑ d ∈ (P i j).support, ‖AddMonoidAlgebra.coeff (P i j) d‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  obtain ⟨β₀, h1, h2, h3⟩ := exists_form_of_bounded f.range C hC
  let e : a.W →ₗ[ℂ] (ι → ℂ) := b.equivFun.toLinearMap
  refine ⟨(β₀.comp e).compl₂ e, fun x y => ?_, fun x hx => ?_, fun γ x y => ?_⟩
  · exact h1 _ _
  · refine h2 _ ?_
    simpa [e] using hx
  · show β₀ (e (a.ρ γ x)) (e (a.ρ γ y)) = β₀ (e x) (e y)
    have hv : ∀ z, e (a.ρ γ z) = ((f γ : Matrix.GeneralLinearGroup ι ℂ) : Matrix ι ι ℂ) *ᵥ e z := by
      intro z
      rw [hf]
      exact (LinearMap.toMatrix_mulVec_repr b b (a.ρ γ) z).symm
    rw [hv, hv]
    exact h3 _ ⟨γ, rfl⟩ _ _
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantHermitianWeightFormStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_hermitian_weight_form : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n), ∃ β, IsInvForm a β := by
  first | exact @GlobalTheory.InvFormBdd.exists_isInvForm | exact GlobalTheory.InvFormBdd.exists_isInvForm | (intros; apply GlobalTheory.InvFormBdd.exists_isInvForm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeExpansionsStdBelowLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeExpansionsStdBelowLevel
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL GlobalTheory.NL.Model

noncomputable section

namespace GlobalTheory.NL.LatLow

section Series

variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]

theorem conv_eq_sum (e : PowerSeries L) {u : ℤ → M} {m : ℤ} (hm : ∀ k < m, u k = 0) (k : ℤ) (N : ℕ)
    (hN : k - m < N) :
    conv e u k = ∑ j ∈ Finset.range N, PowerSeries.coeff j e • u (k - (j : ℤ)) := by
  unfold conv
  apply finsum_eq_sum_of_support_subset
  intro j hj
  by_contra h
  simp only [Finset.coe_range, Set.mem_Iio, not_lt] at h
  apply hj
  have : k - (j : ℤ) < m := by omega
  simp [hm _ this]

theorem conv_van (e : PowerSeries L) {u : ℤ → M} {m : ℤ} (hm : ∀ k < m, u k = 0) :
    ∀ k < m, conv e u k = 0 := by
  intro k hk
  rw [conv_eq_sum e hm k 0 (by omega)]
  simp

theorem conv_mul (a b : PowerSeries L) {u : ℤ → M} {m : ℤ} (hm : ∀ k < m, u k = 0) :
    conv (a * b) u = conv a (conv b u) := by
  funext k
  set N := (k - m).toNat + 1 with hN
  rw [conv_eq_sum _ hm k N (by omega), conv_eq_sum _ (conv_van b hm) k N (by omega)]
  have h1 : ∀ i ∈ Finset.range N, PowerSeries.coeff i a • conv b u (k - (i : ℤ)) =
      ∑ j ∈ Finset.range (N - i), (PowerSeries.coeff i a * PowerSeries.coeff j b) •
        u (k - ((i + j : ℕ) : ℤ)) := by
    intro i hi
    have := Finset.mem_range.1 hi
    rw [conv_eq_sum _ hm _ (N - i) (by omega), Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul]
    congr 2
    push_cast
    ring
  rw [Finset.sum_congr rfl h1, ← Finset.sum_range_diag_flip N (fun i j =>
    (PowerSeries.coeff i a * PowerSeries.coeff j b) • u (k - ((i + j : ℕ) : ℤ)))]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := Finset.mem_range.1 hi
  have h2 : i + (n - i) = n := by omega
  rw [h2]

def tw (c : L) (Φ : M →ₗ[L] M) : (ℤ → M) →ₗ[L] (ℤ → M) where
  toFun f := fun k => c ^ k • Φ (f k)
  map_add' f g := by funext k; simp
  map_smul' a f := by funext k; simp [smul_comm a]

theorem tw_apply (c : L) (Φ : M →ₗ[L] M) (f : ℤ → M) (k : ℤ) : tw c Φ f k = c ^ k • Φ (f k) := rfl

theorem tw_van (c : L) (Φ : M →ₗ[L] M) {u : ℤ → M} {m : ℤ} (hm : ∀ k < m, u k = 0) :
    ∀ k < m, tw c Φ u k = 0 := fun k hk => by simp [tw_apply, hm k hk]

theorem tw_conv {c : L} (hc : c ≠ 0) (Φ : M →ₗ[L] M) (a : PowerSeries L) {u : ℤ → M} {m : ℤ}
    (hm : ∀ k < m, u k = 0) :
    tw c Φ (conv a u) = conv (PowerSeries.rescale c a) (tw c Φ u) := by
  funext k
  set N := (k - m).toNat + 1 with hN
  set_option synthInstance.maxHeartbeats 100000 in
    rw [tw_apply, conv_eq_sum _ hm k N (by omega), conv_eq_sum _ (tw_van c Φ hm) k N (by omega),
    map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tw_apply, map_smul, smul_smul, smul_smul, PowerSeries.coeff_rescale, zpow_sub₀ hc, zpow_natCast]
  congr 1
  field_simp

theorem std_step {A DD : Type} [CommRing A] [AddCommGroup DD] [Module A DD] (N : Submodule A DD)
    (φ : DD → DD) (Q : A) (lev : A →* PowerSeries L) (hQ : IsUnit (lev Q))
    (e e' : ↥N →+ (ℤ → M)) (D D' : Submodule L M) (c : L) (hc : c ≠ 0) (Φ : M →ₗ[L] M)
    (hΦ : Set.BijOn Φ D' D)
    (hD : ∀ x k, e x k ∈ D) (hs : ∀ x, ∃ m : ℤ, ∀ k < m, e x k = 0)
    (hsm : ∀ (a : A) (x : ↥N), e (a • x) = conv (lev a) (e x))
    (hφ : ∀ x ∈ N, ∃ k : ℕ, Q ^ k • φ x ∈ N)
    (hφinv : ∀ y ∈ N, ∃ k : ℕ, Q ^ k • y ∈ Submodule.span A (φ '' (N : Set DD)))
    (heφ : ∀ (x : ↥N) (m : ℕ) (hx : Q ^ m • φ x ∈ N),
      e ⟨Q ^ m • φ x, hx⟩ = conv (lev (Q ^ m)) (tw c Φ (e' x)))
    (h' : Std D' (latSpan (LL := L) e')) : Std D (latSpan (LL := L) e) := by
  have hv' : ∀ x, ∀ k < (0 : ℤ), e' x k = 0 := fun x => ((h' _).1 (mem_latSpan _ x)).2
  have hinv : ∀ m : ℕ, ∃ w : PowerSeries L, w * lev (Q ^ m) = 1 := fun m => by
    rw [map_pow]
    exact (hQ.pow m).exists_left_inv
  have hspan : ∀ z ∈ Submodule.span A (φ '' (N : Set DD)), ∃ (m : ℕ) (hz : Q ^ m • z ∈ N),
      ∀ k < (0 : ℤ), e ⟨Q ^ m • z, hz⟩ k = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, hx, rfl⟩ := hz
      obtain ⟨m, hm⟩ := hφ x hx
      refine ⟨m, hm, ?_⟩
      rw [heφ ⟨x, hx⟩ m hm]
      exact conv_van _ (tw_van c Φ (hv' _))
    | zero =>
      refine ⟨0, by simp, fun k _ => ?_⟩
      have : (⟨Q ^ 0 • (0 : DD), by simp⟩ : ↥N) = 0 := Subtype.ext (by simp)
      rw [this, map_zero]; rfl
    | add z z' _ _ hz hz' =>
      obtain ⟨m, hm, hz⟩ := hz
      obtain ⟨m', hm', hz'⟩ := hz'
      have key : Q ^ (m + m') • (z + z') =
          ((Q ^ m' • (⟨_, hm⟩ : ↥N) + Q ^ m • (⟨_, hm'⟩ : ↥N) : ↥N) : DD) := by
        simp only [Submodule.coe_add, Submodule.coe_smul, smul_add, smul_smul, ← pow_add, add_comm m' m]
      refine ⟨m + m', key ▸ Subtype.mem _, fun k hk => ?_⟩
      have : (⟨Q ^ (m + m') • (z + z'), key ▸ Subtype.mem _⟩ : ↥N) =
          Q ^ m' • (⟨_, hm⟩ : ↥N) + Q ^ m • (⟨_, hm'⟩ : ↥N) := Subtype.ext key
      rw [this, map_add (f := _), hsm, hsm, Pi.add_apply, conv_van _ hz k hk, conv_van _ hz' k hk, add_zero]
    | smul a z _ hz =>
      obtain ⟨m, hm, hz⟩ := hz
      have key : Q ^ m • (a • z) = ((a • (⟨_, hm⟩ : ↥N) : ↥N) : DD) := by
        simp only [Submodule.coe_smul, smul_smul, mul_comm]
      refine ⟨m, key ▸ Subtype.mem _, fun k hk => ?_⟩
      have : (⟨Q ^ m • (a • z), key ▸ Subtype.mem _⟩ : ↥N) = a • (⟨_, hm⟩ : ↥N) := Subtype.ext key
      rw [this, hsm, conv_van _ hz k hk]
  have hv : ∀ x, ∀ k < (0 : ℤ), e x k = 0 := by
    intro y
    obtain ⟨j, hj⟩ := hφinv y y.2
    obtain ⟨m, hm, hz⟩ := hspan _ hj
    have : (⟨Q ^ m • Q ^ j • (y : DD), hm⟩ : ↥N) = Q ^ (m + j) • y :=
      Subtype.ext (by simp only [Submodule.coe_smul, smul_smul, pow_add])
    rw [this, hsm] at hz
    obtain ⟨w, hw⟩ := hinv (m + j)
    obtain ⟨b, hb⟩ := hs y
    have h2 := conv_van w hz
    rwa [← conv_mul _ _ hb, hw, conv_one] at h2
  have hmap : ∀ g ∈ latSpan (LL := L) e', tw c Φ g ∈ latSpan (LL := L) e := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨a, x, rfl⟩ := hg
      obtain ⟨m, hm⟩ := hφ x x.2
      obtain ⟨w, hw⟩ := hinv m
      refine Submodule.subset_span ⟨PowerSeries.rescale c a * w, ⟨_, hm⟩, ?_⟩
      rw [heφ x m hm, ← conv_mul _ _ (tw_van c Φ (hv' x)), mul_assoc, hw, mul_one,
        tw_conv hc Φ a (hv' x)]
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add f g _ _ hf hg => rw [map_add (f := _)]; exact Submodule.add_mem _ hf hg
    | smul a f _ hf => rw [map_smul]; exact Submodule.smul_mem _ a hf
  intro f
  constructor
  · intro hf
    refine ⟨(latSpan_coeff _ D hD hs f hf).1, ?_⟩
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨a, x, rfl⟩ := hf
      exact conv_van a (hv x)
    | zero => exact fun _ _ => rfl
    | add f g _ _ hf hg => intro k hk; simp [hf k hk, hg k hk]
    | smul a f _ hf => intro k hk; simp [hf k hk]
  · rintro ⟨h1, h2⟩
    have : ∀ k, ∃ d ∈ D', Φ d = f k ∧ (k < 0 → d = 0) := by
      intro k
      by_cases hk : k < 0
      · exact ⟨0, D'.zero_mem, by rw [map_zero, h2 k hk], fun _ => rfl⟩
      · obtain ⟨d, hd, hd'⟩ := hΦ.surjOn (h1 k)
        exact ⟨d, hd, hd', fun h => absurd h hk⟩
    choose d hd hd1 hd2 using this
    have hg : (fun k => (c ^ k)⁻¹ • d k) ∈ latSpan (LL := L) e' :=
      (h' _).2 ⟨fun k => D'.smul_mem _ (hd k), fun k hk => by simp [hd2 k hk]⟩
    have h3 := hmap _ hg
    have : tw c Φ (fun k => (c ^ k)⁻¹ • d k) = f := by
      funext k
      rw [tw_apply, map_smul, smul_smul, mul_inv_cancel₀ (zpow_ne_zero k hc), one_smul, hd1]
    rwa [this] at h3

end Series


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem lat_low : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1), ζ ^ (l ^ (s - 1)) = 1 → Std (Di (HW l) h T i) (Lat C h T i ζ) := by
  intro D HW F Cm l hl K s LL h W E C T hT
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have main : ∀ (j : ℕ) (i : Let K) (ζ : ↥LL.1), ζ ^ (l ^ j) = 1 → ζ ^ (l ^ (s - 1)) = 1 →
      Std (Di (HW l) h T i) (Lat C h T i ζ) := by
    intro j
    induction j with
    | zero =>
      intro i ζ h1 _
      obtain rfl : ζ = 1 := by simpa using h1
      exact GlobalTheory.T.wach_lattice_eq_std_powerSeries_at_zero D HW F Cm l K s LL h T hT i
    | succ j ih =>
      intro i ζ h1 h2
      have hprim : ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j) := by
        obtain ⟨r, -, hr⟩ := (Nat.dvd_prime_pow hl.out).1 (orderOf_dvd_of_pow_eq_one h1)
        exact ⟨r, hr ▸ IsPrimitiveRoot.orderOf ζ⟩
      have ih' := ih (i - 1) (ζ ^ l) (by rw [← pow_mul, ← pow_succ', h1])
        (by rw [← pow_mul, mul_comm, pow_mul, h2, one_pow])
      have hQ : IsUnit (W.lev i ζ W.Q) :=
        ((GlobalTheory.T.wachLevel_expansion_at_root_of_unity D HW l K s LL h i ζ hprim).2.2.1 h2).2
      have hΦ := (GlobalTheory.T.crystallineFrobenius_bijOn_letters_directSum D HW l K s LL h T hT).1 i
      have hc : (l : ↥LL.1) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
      refine std_step (W.N T) (W.φD T) W.Q (MonoidHomClass.toMonoidHom (W.lev i ζ)) hQ
        ((C.C K s LL h).tie.levB T i ζ) ((C.C K s LL h).tie.levB T (i - 1) (ζ ^ l))
        (Di (HW l) h T i) (Di (HW l) h T (i - 1)) (l : ↥LL.1) hc _ hΦ
        ((C.C K s LL h).tie.levB_mem T i ζ) ((C.C K s LL h).tie.levB_supp T i ζ)
        (ex_smul C h T i ζ) (W.N_φ T) (W.N_φinv T) ?_ ih'
      intro x m hx
      funext k
      have := (C.C K s LL h).tie.levB_φ T hT i ζ (by rw [hp]; exact hprim) x m hx k
      rw [hp] at this
      exact this
  intro i ζ hζ
  exact main (s - 1) i ζ hζ hζ

end GlobalTheory.NL.LatLow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeExpansionsStdBelowLevelStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachLattice_expansions_std_below_level : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1), ζ ^ (l ^ (s - 1)) = 1 → Std (Di (HW l) h T i) (Lat C h T i ζ) := by
  first | exact @GlobalTheory.NL.LatLow.lat_low | exact GlobalTheory.NL.LatLow.lat_low | (intros; apply GlobalTheory.NL.LatLow.lat_low <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisTensorLatticeFilZeroGaloisStable
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisTensorLatticeFilZeroGaloisStable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.FilStable

theorem ι_σB {l : ℕ} [Fact l.Prime] (C : GlobalTheory.MemLoc.Core l) (g : Per.Gq l) (β : Per.Bcris l) :
    C.ι (Per.σB g β) = Per.σD g (C.ι β) := by
  refine RingHom.congr_fun (GlobalTheory.CrisLoc.bcris_hom_ext l
    (f := C.ι.comp (Per.σB g)) (g := (Per.σD g).comp C.ι) fun x => ?_) β
  have h1 : Per.σB g (algebraMap (Per.Acris l) (Per.Bcris l) x) =
      algebraMap (Per.Acris l) (Per.Bcris l) (GlobalTheory.MemLoc.sigA g x) :=
    GlobalTheory.CrisMaps.σB_sigA g x
  change C.ι (Per.σB g (algebraMap (Per.Acris l) (Per.Bcris l) x)) =
    Per.σD g (C.ι (algebraMap (Per.Acris l) (Per.Bcris l) x))
  rw [h1, C.ι_j, C.ι_j, GlobalTheory.MemLoc.FilLaws.σD_alg, GlobalTheory.MemLoc.CrisUnique.equivariant C.j_cris]

theorem fil_zero_stable : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (T : LocLat (Gl l) ℚ_[l] K O) (g : Gl l) (C : GlobalTheory.MemLoc.Core l), ∀ v ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x}, actB (sQ l) T g v ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ O K _ _ _ _ _ _ _ _ _ T g C v hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨β, x, hβ, rfl⟩ := hw
    refine Submodule.subset_span ⟨Per.σB (sQ l g) β, T.actT g x, ?_, ?_⟩
    rotate_left 1
    · simp only [actB, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, galOB,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      rfl
    · rw [ι_σB]
      exact (GlobalTheory.MemLoc.filD_laws l).2.2.2.2.2.1 _ 0 _ hβ
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

end GlobalTheory.BKGal.FilStable
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisTensorLatticeFilZeroGaloisStableStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bcrisTensorLattice_filZero_galois_stable :
    ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O]
      [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
      [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
      (T : LocLat (GlobalTheory.BKGal.Gl l) ℚ_[l] K O) (g : GlobalTheory.BKGal.Gl l)
      (C : GlobalTheory.MemLoc.Core l),
      ∀ v ∈ Submodule.span O {w : TW (GlobalTheory.BKReal.OB l O) T |
        ∃ (β : Per.Bcris l) (x : ↥T.L.T),
          C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x},
        GlobalTheory.BKGal.actB (GlobalTheory.BKGal.sQ l) T g v ∈
          Submodule.span O {w : TW (GlobalTheory.BKReal.OB l O) T |
            ∃ (β : Per.Bcris l) (x : ↥T.L.T),
              C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  exact @GlobalTheory.BKGal.FilStable.fil_zero_stable
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InerDecomp
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

noncomputable section
namespace GlobalTheory.InertiaDecomp
open Pointwise

theorem iner_decomp : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c') (g : ↥(GK K)), g ∈ (pc P h hN hF hS).Iner → ∃ s : ↥(GK K), s ∈ IK K ∧ s⁻¹ * g ∈ GKin h := by
  intro l _ P K K' h hN hF hS g hg
  haveI : Nontrivial P.R.B := by
    by_contra hB
    have : Subsingleton P.R.B := not_nontrivial_iff_subsingleton.mp hB
    apply (P.PD K).not_mem_filtration_two
    rw [Subsingleton.elim (P.PD K).t 0, map_zero]
    exact Submodule.zero_mem _

  have hfix : ∀ x ∈ K0 K', (g : GQ l) x = x := by
    intro x hx
    have h1 : (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B ⟨x, hx⟩) = algebraMap ↥(K0 K') P.R.B ⟨x, hx⟩ :=
      hg ⟨x, hx⟩
    rw [P.PD_actB] at h1
    have h2 := P.actQ_Kur ((g : ↥(GK K)) : GQ l) ⟨x, hx.2⟩ ⟨_, GlobalTheory.TameInertiaCyclic.map_mem_Kur _ hx.2⟩ rfl
    have h3 := (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).injective (h2.symm.trans h1)
    exact congrArg Subtype.val h3
  haveI := K'.2

  let S : Subgroup (GQ l) := (MaximalUnramifiedExtension l).fixingSubgroup ⊔ (K'.1).fixingSubgroup
  have hSo : IsOpen (S : Set (GQ l)) :=
    Subgroup.isOpen_mono le_sup_right (IntermediateField.fixingSubgroup_isOpen K'.1)
  let SC : ClosedSubgroup (GQ l) := ⟨S, Subgroup.isClosed_of_isOpen S hSo⟩
  have hfe : IntermediateField.fixedField (SC : Subgroup (GQ l)) ≤ K0 K' := by
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    refine IntermediateField.mem_inf.2 ⟨?_, ?_⟩
    · exact (InfiniteGalois.fixedField_fixingSubgroup K'.1).le
        ((IntermediateField.mem_fixedField_iff _ _).2 fun f hf => hx f (Subgroup.mem_sup_right hf))
    · exact (InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension l)).le
        ((IntermediateField.mem_fixedField_iff _ _).2 fun f hf => hx f (Subgroup.mem_sup_left hf))
  have hgS : (g : GQ l) ∈ S := by
    have e := InfiniteGalois.fixingSubgroup_fixedField SC
    have : (g : GQ l) ∈ (IntermediateField.fixedField (SC : Subgroup (GQ l))).fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact hfix x (hfe hx)
    rw [e] at this
    exact this
  haveI := GlobalTheory.FrobGen.normal_fix (l := l)
  have hgS' : (g : GQ l) ∈ ((MaximalUnramifiedExtension l).fixingSubgroup : Set (GQ l)) * ((K'.1).fixingSubgroup : Set (GQ l)) := by
    rw [← Subgroup.normal_mul]; exact hgS
  obtain ⟨b, hb, a, ha, hba⟩ := hgS'
  have haK : a ∈ GK K := GK_le h ha
  have hbK : b ∈ GK K := by
    have : b = (g : GQ l) * a⁻¹ := by rw [← hba, mul_inv_cancel_right]
    rw [this]; exact mul_mem g.2 (inv_mem haK)
  refine ⟨⟨b, hbK⟩, Subgroup.subset_closure fun x hx => GlobalTheory.FrobGen.norm_sub_lt hb x hx, ?_⟩
  rw [GKin, Subgroup.mem_subgroupOf]
  have : (((⟨b, hbK⟩ : ↥(GK K))⁻¹ * g : ↥(GK K)) : GQ l) = a := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, ← hba]; simp
  rw [this]; exact ha

end GlobalTheory.InertiaDecomp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDeRhamPlusActionMulOne
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDeRhamPlusActionMulOne
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.JumpDR

section Abstract

variable {R O B K V C : Type} [CommSemiring R] [Semiring O] [Algebra R O] [Semiring B] [Algebra R B]
  [CommSemiring K] [AddCommMonoid V] [Module K V] [Semiring C] [Module K C]

theorem tensorAct_mul (s : O → V → V) (φ : B →+* C)
    (act : O ⊗[R] B →+ (V ⊗[K] C →+ V ⊗[K] C))
    (hs : ∀ (o o' : O) (v : V), s (o * o') v = s o (s o' v))
    (h : ∀ (o : O) (b : B) (v : V) (c : C), act (o ⊗ₜ[R] b) (v ⊗ₜ[K] c) = s o v ⊗ₜ[K] (φ b * c))
    (d d' : O ⊗[R] B) (w : V ⊗[K] C) : act (d * d') w = act d (act d' w) := by
  induction d using TensorProduct.induction_on with
  | zero => simp only [zero_mul, map_zero, AddMonoidHom.zero_apply]
  | add x y hx hy => simp only [add_mul, map_add (f := _), AddMonoidHom.add_apply, hx, hy]
  | tmul o b =>
    induction d' using TensorProduct.induction_on with
    | zero => simp only [mul_zero, map_zero, AddMonoidHom.zero_apply]
    | add x y hx hy => simp only [mul_add, map_add (f := _), AddMonoidHom.add_apply, hx, hy]
    | tmul o' b' =>
      induction w using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul v c =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, h, h, h, hs, map_mul, mul_assoc]

theorem tensorAct_one (s : O → V → V) (φ : B →+* C)
    (act : O ⊗[R] B →+ (V ⊗[K] C →+ V ⊗[K] C))
    (hs : ∀ v : V, s 1 v = v)
    (h : ∀ (o : O) (b : B) (v : V) (c : C), act (o ⊗ₜ[R] b) (v ⊗ₜ[K] c) = s o v ⊗ₜ[K] (φ b * c))
    (w : V ⊗[K] C) : act 1 w = w := by
  rw [Algebra.TensorProduct.one_def]
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul v c => rw [h, hs, map_one, one_mul]

end Abstract

theorem odAct_mul_one : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → (∀ (d d' : OD l ↥(OL LL)) (w : T.V ⊗[ℚ_[l]] Pl.R.BdR), act (d * d') w = act d (act d' w)) ∧ ∀ w : T.V ⊗[ℚ_[l]] Pl.R.BdR, act 1 w = w :=
  fun _ _ LL T _ _ Td act h =>
    ⟨tensorAct_mul (fun (o : ↥(OL LL)) (v : T.V) => (o : ↥LL.1) • v) (cD Td) act
        (fun o o' v => mul_smul (o : ↥LL.1) (o' : ↥LL.1) v) h,
      tensorAct_one (fun (o : ↥(OL LL)) (v : T.V) => (o : ↥LL.1) • v) (cD Td) act
        (fun v => one_smul ↥LL.1 v) h⟩

end GlobalTheory.BKGal.JumpDR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDeRhamPlusActionMulOneStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffDeRhamPlusAction_mul_one : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → (∀ (d d' : OD l ↥(OL LL)) (w : T.V ⊗[ℚ_[l]] Pl.R.BdR), act (d * d') w = act d (act d' w)) ∧ ∀ w : T.V ⊗[ℚ_[l]] Pl.R.BdR, act 1 w = w := by
  first | exact @GlobalTheory.BKGal.JumpDR.odAct_mul_one | exact GlobalTheory.BKGal.JumpDR.odAct_mul_one | (intros; apply GlobalTheory.BKGal.JumpDR.odAct_mul_one <;> assumption)
end
end
