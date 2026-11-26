module

public import Mathlib

@[expose] public section

section -- merged from ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.GramSt
namespace ReciprocityTheory.GeometryOfNumbersTheory

open Matrix
open scoped ComplexOrder MatrixOrder

section SlopeTestRemainingChoices

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem gramSt_det_one_add_eq {Q : Matrix ι ι ℂ} (hQ : Q.PosSemidef) :
    (1 + Q).det = ((∏ i, (1 + hQ.1.eigenvalues i) : ℝ) : ℂ) := by
  set U := hQ.1.eigenvectorUnitary
  have hspec := hQ.1.spectral_theorem
  have h1 : (1 + Q) = Unitary.conjStarAlgAut ℂ _ U
      (1 + diagonal (RCLike.ofReal ∘ hQ.1.eigenvalues)) := by
    rw [map_add (f := _), map_one, ← hspec]
  have hd : (1 + diagonal (RCLike.ofReal ∘ hQ.1.eigenvalues) : Matrix ι ι ℂ) =
      diagonal (fun i => ((1 + hQ.1.eigenvalues i : ℝ) : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [h, one_apply]
  rw [h1, Unitary.conjStarAlgAut_apply, hd, det_mul, det_mul, det_diagonal, Complex.ofReal_prod]
  rw [mul_comm (det _) (∏ _, _), mul_assoc, ← det_mul]
  try rw [Unitary.coe_star]
  rw [Unitary.mul_star_self_of_mem U.2, det_one, mul_one]

theorem gramSt_det_re_le_of_sub {G H : Matrix ι ι ℂ} (hG : G.PosDef)
    (hGH : (H - G).PosSemidef) : G.det.re ≤ H.det.re := by
  set S := CFC.sqrt G with hSdef
  have hS0 : S.PosSemidef := (CFC.sqrt_nonneg G).posSemidef
  have hSS : S * S = G := CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg
  have hSh : Sᴴ = S := hS0.1
  have hdetG : G.det = S.det * S.det := by rw [← hSS, det_mul]
  have hGpos := hG.det_pos
  have hSdet : S.det ≠ 0 := by
    intro h; rw [hdetG, h, zero_mul] at hGpos; exact lt_irrefl _ hGpos
  have hSu : IsUnit S.det := isUnit_iff_ne_zero.mpr hSdet
  have hQ : (S⁻¹ * (H - G) * (S⁻¹)ᴴ).PosSemidef := hGH.mul_mul_conjTranspose_same _
  have hinvh : (S⁻¹)ᴴ = S⁻¹ := by rw [conjTranspose_nonsing_inv, hSh]
  have h2 : S * (S⁻¹ * (H - G) * (S⁻¹)ᴴ) * S = H - G := by
    rw [hinvh, show S * (S⁻¹ * (H - G) * S⁻¹) * S = (S * S⁻¹) * (H - G) * (S⁻¹ * S) by
      simp only [Matrix.mul_assoc]]
    rw [mul_nonsing_inv S hSu, nonsing_inv_mul S hSu, Matrix.one_mul, Matrix.mul_one]
  have hH : H = S * (1 + S⁻¹ * (H - G) * (S⁻¹)ᴴ) * S := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hSS, h2]; abel
  have hdetH : H.det = G.det * (1 + S⁻¹ * (H - G) * (S⁻¹)ᴴ).det := by
    conv_lhs => rw [hH]
    rw [det_mul, det_mul, hdetG]; ring
  rw [hdetH, gramSt_det_one_add_eq hQ]
  obtain ⟨hre, him⟩ := Complex.pos_iff.mp hGpos
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have h1 : (1:ℝ) ≤ ∏ i, (1 + hQ.1.eigenvalues i) := by
    calc (1:ℝ) = ∏ _i : ι, (1:ℝ) := by simp
      _ ≤ ∏ i, (1 + hQ.1.eigenvalues i) :=
        Finset.prod_le_prod₀ (fun _ _ => zero_le_one)
          (fun i _ => by linarith [hQ.eigenvalues_nonneg i])
  nlinarith

end SlopeTestRemainingChoices

section Block

variable {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]

theorem gramSt_fischer {A : Matrix m m ℂ} {B : Matrix m k ℂ} {C : Matrix k m ℂ} {D : Matrix k k ℂ}
    (h : (fromBlocks A B C D).PosDef) :
    (fromBlocks A B C D).det.re ≤ A.det.re * D.det.re := by
  have hA : A.PosDef := by
    have := h.submatrix (e := (Sum.inl : m → m ⊕ k)) Sum.inl_injective
    have e : (fromBlocks A B C D).submatrix Sum.inl Sum.inl = A := by ext; simp
    rwa [e] at this
  have hD : D.PosDef := by
    have := h.submatrix (e := (Sum.inr : k → m ⊕ k)) Sum.inr_injective
    have e : (fromBlocks A B C D).submatrix Sum.inr Sum.inr = D := by ext; simp
    rwa [e] at this
  have hC : C = Bᴴ := by
    have := (isHermitian_fromBlocks_iff.mp h.1)
    exact this.2.1.symm
  subst hC
  have : Invertible A := hA.isUnit.invertible
  have hS : (D - Bᴴ * A⁻¹ * B).PosSemidef :=
    (PosDef.fromBlocks₁₁ B D hA).mp h.posSemidef
  have hdet : (fromBlocks A B Bᴴ D).det = A.det * (D - Bᴴ * A⁻¹ * B).det := by
    rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  have hSne : (D - Bᴴ * A⁻¹ * B).det ≠ 0 := by
    intro h0
    have := h.det_pos
    rw [hdet, h0, mul_zero] at this
    exact lt_irrefl _ this
  have hSd : (D - Bᴴ * A⁻¹ * B).PosDef := hS.posDef_iff_det_ne_zero.mpr hSne
  have hdiff : (D - (D - Bᴴ * A⁻¹ * B)).PosSemidef := by
    rw [sub_sub_cancel]
    exact hA.inv.posSemidef.conjTranspose_mul_mul_same B
  have hmono := gramSt_det_re_le_of_sub hSd hdiff
  obtain ⟨hAre, hAim⟩ := Complex.pos_iff.mp hA.det_pos
  rw [hdet, Complex.mul_re, ← hAim, zero_mul, sub_zero]
  exact mul_le_mul_of_nonneg_left hmono hAre.le

end Block

theorem gramSt_fin_blocks {a b : ℕ} {M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ} (hM : M.PosDef) :
    M.det.re ≤ (M.submatrix (Fin.castAdd b) (Fin.castAdd b)).det.re *
      (M.submatrix (Fin.natAdd a) (Fin.natAdd a)).det.re := by
  have hE : M.submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks (M.submatrix (Fin.castAdd b) (Fin.castAdd b))
        (M.submatrix (Fin.castAdd b) (Fin.natAdd a))
        (M.submatrix (Fin.natAdd a) (Fin.castAdd b))
        (M.submatrix (Fin.natAdd a) (Fin.natAdd a)) := by
    ext (i | i) (j | j) <;> simp
  have hP : (M.submatrix finSumFinEquiv finSumFinEquiv).PosDef :=
    hM.submatrix finSumFinEquiv.injective
  rw [hE] at hP
  have := gramSt_fischer hP
  rwa [← hE, det_submatrix_equiv_self] at this

theorem gramSt_hadamard {k : ℕ} {D : Matrix (Fin k) (Fin k) ℂ} (hD : D.PosDef) :
    D.det.re ≤ ∏ j : Fin k, (D j j).re := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := gramSt_fin_blocks (a := k) (b := 1) hD
    have h2 := ih (hD.submatrix (Fin.castAdd_injective k 1))
    have h3 : (D.submatrix (Fin.natAdd k) (Fin.natAdd k : Fin 1 → Fin (k + 1))).det =
        D (Fin.last k) (Fin.last k) := by
      rw [det_unique]; rfl
    have h4 : 0 ≤ (D (Fin.last k) (Fin.last k)).re := (Complex.pos_iff.mp hD.diag_pos).1.le
    rw [h3] at h1
    rw [Fin.prod_univ_castSucc]
    exact h1.trans (mul_le_mul_of_nonneg_right h2 h4)

theorem posDef_det_re_pos {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef) :
    0 < G.det.re ∧ G.det.im = 0 := by
  obtain ⟨h1, h2⟩ := Complex.pos_iff.mp hG.det_pos
  exact ⟨h1, h2.symm⟩

theorem det_re_le_of_sub_posSemidef {n : ℕ} {G H : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef)
    (hGH : (H - G).PosSemidef) : G.det.re ≤ H.det.re :=
  gramSt_det_re_le_of_sub hG hGH

theorem det_re_le_mul_prod_diag {a b : ℕ} {M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ}
    (hM : M.PosDef) :
    M.det.re ≤ (M.submatrix (Fin.castAdd b) (Fin.castAdd b)).det.re *
      ∏ j : Fin b, (M (Fin.natAdd a j) (Fin.natAdd a j)).re := by
  have h1 := gramSt_fin_blocks hM
  have h2 := gramSt_hadamard (hM.submatrix (e := Fin.natAdd a) (Fin.natAdd_injective b a))
  have h0 : 0 ≤ (M.submatrix (Fin.castAdd b) (Fin.castAdd b)).det.re :=
    (Complex.pos_iff.mp (hM.submatrix (Fin.castAdd_injective a b)).det_pos).1.le
  exact h1.trans (mul_le_mul_of_nonneg_left h2 h0)

end ReciprocityTheory.GeometryOfNumbersTheory
end

section -- merged from ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
noncomputable section

namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module
open scoped ComplexOrder

structure HermFam (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V] where

  form : (K →+* ℂ) → V → V → ℂ
  add_right : ∀ σ x y z, form σ x (y + z) = form σ x y + form σ x z
  smul_right : ∀ σ (a : K) x y, form σ x (a • y) = σ a * form σ x y
  conj_symm : ∀ σ x y, starRingEnd ℂ (form σ x y) = form σ y x
  posDef : ∀ σ (n : ℕ) (v : Fin n → V), LinearIndependent K v →
    (Matrix.of fun i j => form σ (v i) (v j)).PosDef

section

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

def HermFam.gram (h : HermFam K V) (σ : K →+* ℂ) {n : ℕ} (v : Fin n → V) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => h.form σ (v i) (v j)

def HermFam.nrm (h : HermFam K V) (σ : K →+* ℂ) (x : V) : ℝ :=
  Real.sqrt (h.form σ x x).re

end

section

variable (K : Type*) [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def latRank (E : Submodule (𝓞 K) V) : ℕ :=
  finrank K (Submodule.span K (E : Set V))

def IsFrame (E : Submodule (𝓞 K) V) {r : ℕ} (v : Fin r → V) : Prop :=
  (∀ i, v i ∈ E) ∧ LinearIndependent K v ∧ (E : Set V) ⊆ Submodule.span K (Set.range v)

def meanLog (A : (K →+* ℂ) → ℝ) : ℝ :=
  (∑ σ : K →+* ℂ, Real.log (A σ)) / finrank ℚ K

variable {K}

def degreeOfFamily (h : HermFam K V) (E : Submodule (𝓞 K) V) {r : ℕ} (v : Fin r → V) : ℝ :=
  (Real.log ((Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup : ℝ)
    - (1 / 2) * ∑ σ : K →+* ℂ, Real.log (h.gram σ v).det.re) / finrank ℚ K


open Classical in
def deg (h : HermFam K V) (E : Submodule (𝓞 K) V) : ℝ := by
  classical
  exact if hE : ∃ p : (Σ r : ℕ, Fin r → V), IsFrame K E p.2 then degreeOfFamily h E hE.choose.2 else 0

end

end ReciprocityTheory.GeometryOfNumbersTheory
end
end

section -- merged from ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidSt
section -- merged from ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA
namespace ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall

open MeasureTheory

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def sqBall (r : ℕ) (E : Type*) [NormedAddCommGroup E] (R : ℝ) : Set (Fin r → E) :=
  {u | ∑ k, ‖u k‖ ^ 2 ≤ R ^ 2}

lemma norm_sq_convex_comb {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (z w : E) :
    ‖a • z + b • w‖ ^ 2 ≤ a * ‖z‖ ^ 2 + b * ‖w‖ ^ 2 := by
  have h1 : ‖a • z + b • w‖ ≤ a * ‖z‖ + b * ‖w‖ := by
    calc ‖a • z + b • w‖ ≤ ‖a • z‖ + ‖b • w‖ := norm_add_le _ _
      _ = a * ‖z‖ + b * ‖w‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
  have h2 : (a * ‖z‖ + b * ‖w‖) ^ 2 ≤ a * ‖z‖ ^ 2 + b * ‖w‖ ^ 2 := by
    obtain rfl : b = 1 - a := by linarith
    nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (‖z‖ - ‖w‖))]
  calc ‖a • z + b • w‖ ^ 2 ≤ (a * ‖z‖ + b * ‖w‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

lemma sqBall_convex (r : ℕ) (R : ℝ) : Convex ℝ (sqBall r E R) := by
  intro u hu v hv a b ha hb hab
  simp only [sqBall, Set.mem_setOf_eq] at hu hv ⊢
  calc ∑ k, ‖(a • u + b • v) k‖ ^ 2 = ∑ k, ‖a • u k + b • v k‖ ^ 2 := rfl
    _ ≤ ∑ k, (a * ‖u k‖ ^ 2 + b * ‖v k‖ ^ 2) :=
        Finset.sum_le_sum fun k _ => norm_sq_convex_comb ha hb hab _ _
    _ = a * ∑ k, ‖u k‖ ^ 2 + b * ∑ k, ‖v k‖ ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ a * R ^ 2 + b * R ^ 2 := by gcongr
    _ = R ^ 2 := by rw [← add_mul, hab, one_mul]

lemma sqBall_neg (r : ℕ) (R : ℝ) : ∀ u ∈ sqBall r E R, -u ∈ sqBall r E R := by
  intro u hu
  simpa [sqBall] using hu

lemma sqBall_subset (r : ℕ) (R : ℝ) : sqBall r E R ⊆ Metric.closedBall 0 |R| := by
  intro u hu
  simp only [sqBall, Set.mem_setOf_eq] at hu
  rw [mem_closedBall_zero_iff]
  refine (pi_norm_le_iff_of_nonneg (abs_nonneg R)).2 fun k => ?_
  have hk : ‖u k‖ ^ 2 ≤ R ^ 2 :=
    (Finset.single_le_sum (f := fun k => ‖u k‖ ^ 2) (fun k _ => by positivity)
      (Finset.mem_univ k)).trans hu
  have := sq_le_sq.mp hk
  rwa [abs_of_nonneg (norm_nonneg _)] at this

lemma sqBall_isBounded (r : ℕ) (R : ℝ) : Bornology.IsBounded (sqBall r E R) := Metric.isBounded_closedBall.subset (sqBall_subset r R)

lemma sqBall_isClosed (r : ℕ) (R : ℝ) : IsClosed (sqBall r E R) := by
  unfold sqBall
  exact isClosed_le (continuous_finsetSum _ fun k _ => (continuous_apply k).norm.pow 2)
    continuous_const

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace V] [BorelSpace V]

end Generic

end ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall
end

namespace ReciprocityTheory.GeometryOfNumbersTheory

open MeasureTheory Matrix
open scoped ComplexOrder MatrixOrder
open ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall

noncomputable def qC {r : ℕ} (G : Matrix (Fin r) (Fin r) ℂ) (y : Fin r → ℂ) : ℝ :=
  (∑ i, ∑ j, starRingEnd ℂ (y i) * G i j * y j).re

noncomputable def qR {r : ℕ} (G : Matrix (Fin r) (Fin r) ℝ) (y : Fin r → ℝ) : ℝ :=
  ∑ i, ∑ j, y i * G i j * y j

private lemma exists_factor_C {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) :
    ∃ B : Matrix (Fin r) (Fin r) ℂ, G = Bᴴ * B := by
  first
  | exact Matrix.posSemidef_iff_eq_transpose_mul_self.1 hG.posSemidef
  | exact (Matrix.posSemidef_iff_eq_conjTranspose_mul_self).1 hG.posSemidef
  | exact hG.posSemidef.exists_eq_conjTranspose_mul_self
  | (refine ⟨hG.posSemidef.sqrt, ?_⟩
     rw [hG.posSemidef.posSemidef_sqrt.isHermitian.eq, hG.posSemidef.sqrt_mul_self])
  | (refine ⟨CFC.sqrt G, ?_⟩
     have h0 : 0 ≤ G := hG.posSemidef.nonneg
     have hs : (CFC.sqrt G)ᴴ = CFC.sqrt G := (CFC.sqrt_nonneg G).isSelfAdjoint.star_eq
     rw [hs, CFC.sqrt_mul_sqrt_self G h0])

private lemma exists_factor_R {r : ℕ} {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.PosDef) :
    ∃ B : Matrix (Fin r) (Fin r) ℝ, G = Bᵀ * B := by
  have hC : ∃ B : Matrix (Fin r) (Fin r) ℝ, G = Bᴴ * B := by
    first
    | exact Matrix.posSemidef_iff_eq_transpose_mul_self.1 hG.posSemidef
    | exact (Matrix.posSemidef_iff_eq_conjTranspose_mul_self).1 hG.posSemidef
    | exact hG.posSemidef.exists_eq_conjTranspose_mul_self
    | (refine ⟨hG.posSemidef.sqrt, ?_⟩
       rw [hG.posSemidef.posSemidef_sqrt.isHermitian.eq, hG.posSemidef.sqrt_mul_self])
    | (refine ⟨CFC.sqrt G, ?_⟩
       have h0 : 0 ≤ G := hG.posSemidef.nonneg
       have hs : (CFC.sqrt G)ᴴ = CFC.sqrt G := (CFC.sqrt_nonneg G).isSelfAdjoint.star_eq
       rw [hs, CFC.sqrt_mul_sqrt_self G h0])
  obtain ⟨B, hB⟩ := hC
  exact ⟨B, by rw [hB, Matrix.conjTranspose_eq_transpose_of_trivial]⟩

private lemma qC_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (y : Fin r → ℂ) :
    qC (Bᴴ * B) y = ∑ k, ‖(B *ᵥ y) k‖ ^ 2 := by
  have h1 : (∑ i, ∑ j, starRingEnd ℂ (y i) * (Bᴴ * B) i j * y j) =
      dotProduct (star y) ((Bᴴ * B) *ᵥ y) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, Pi.star_apply, RCLike.star_def]
  unfold qC
  rw [h1, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
  simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.re_sum, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.sq_norm, Complex.normSq_apply]
  refine Finset.sum_congr rfl (fun k _ => by ring)

private lemma qR_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (y : Fin r → ℝ) :
    qR (Bᵀ * B) y = ∑ k, ‖(B *ᵥ y) k‖ ^ 2 := by
  have h1 : qR (Bᵀ * B) y = dotProduct y ((Bᵀ * B) *ᵥ y) := by
    simp only [qR, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [h1, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  simp only [dotProduct, Real.norm_eq_abs, sq_abs, sq, abs_mul_abs_self]

private lemma setC_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (R : ℝ) :
    {y | qC (Bᴴ * B) y ≤ R ^ 2} = ((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_preimage, qC_eq, LinearMap.restrictScalars_apply,
    Matrix.toLin'_apply, sqBall]

private lemma setR_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (R : ℝ) :
    {y | qR (Bᵀ * B) y ≤ R ^ 2} = (Matrix.toLin' B) ⁻¹' sqBall r ℝ R := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_preimage, qR_eq, Matrix.toLin'_apply, sqBall]
  skip

private lemma detC_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) :
    (Bᴴ * B).det = (Complex.normSq B.det : ℂ) := by
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Complex.normSq_eq_conj_mul_self]
  rfl

private theorem isBounded_preimage_sqBall_complex_of_det_ne_zero {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (hdet : B.det ≠ 0) (R : ℝ) :
    Bornology.IsBounded (((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R) := by
  have hS : IsCompact (sqBall r ℂ R) :=
    Metric.isCompact_of_isClosed_isBounded (sqBall_isClosed r R) (sqBall_isBounded r R)
  have hc' : Continuous ((Matrix.toLin' B⁻¹).restrictScalars ℝ) :=
    LinearMap.continuous_of_finiteDimensional _
  refine (hS.image hc').isBounded.subset ?_
  intro y hy
  refine ⟨(Matrix.toLin' B).restrictScalars ℝ y, hy, ?_⟩
  show Matrix.mulVec B⁻¹ (Matrix.mulVec B y) = y
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet),
    Matrix.one_mulVec]

private theorem convex_preimage_sqBall_complex {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (R : ℝ) :
    Convex ℝ (((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R) :=
  Convex.linear_preimage (sqBall_convex (E := ℂ) r R) ((Matrix.toLin' B).restrictScalars ℝ)

private theorem neg_mem_preimage_sqBall_complex {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (R : ℝ) :
    ∀ y ∈ ((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R,
      -y ∈ ((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R := by
  intro y hy
  rw [Set.mem_preimage, map_neg]
  exact sqBall_neg (E := ℂ) r R _ hy

private theorem measurableSet_preimage_sqBall_complex {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (R : ℝ) :
    MeasurableSet (((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R) := by
  have hc : Continuous ((Matrix.toLin' B).restrictScalars ℝ) :=
    LinearMap.continuous_of_finiteDimensional _
  exact ((sqBall_isClosed r R).preimage hc).measurableSet

private lemma hermitianEllipsoid_props_of_eq {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) (B : Matrix (Fin r) (Fin r) ℂ)
    (hB : G = Bᴴ * B) (R : ℝ) :
    Convex ℝ {y | qC G y ≤ R ^ 2} ∧ (∀ y ∈ {y | qC G y ≤ R ^ 2}, -y ∈ {y | qC G y ≤ R ^ 2}) ∧
      Bornology.IsBounded {y | qC G y ≤ R ^ 2} ∧ MeasurableSet {y | qC G y ≤ R ^ 2} := by
  subst hB
  have hdet : B.det ≠ 0 := by
    intro h0
    have h1 := hG.det_pos
    rw [detC_eq, h0] at h1
    simp at h1
  rw [setC_eq]
  exact ⟨convex_preimage_sqBall_complex B R, neg_mem_preimage_sqBall_complex B R, isBounded_preimage_sqBall_complex_of_det_ne_zero B hdet R, measurableSet_preimage_sqBall_complex B R⟩

theorem ellipsoidC_props {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) (R : ℝ) :
    Convex ℝ {y | qC G y ≤ R ^ 2} ∧ (∀ y ∈ {y | qC G y ≤ R ^ 2}, -y ∈ {y | qC G y ≤ R ^ 2}) ∧
      Bornology.IsBounded {y | qC G y ≤ R ^ 2} ∧ MeasurableSet {y | qC G y ≤ R ^ 2} := by
  obtain ⟨B, hB⟩ := exists_factor_C hG
  exact hermitianEllipsoid_props_of_eq hG B hB R

private theorem isBounded_preimage_sqBall_real_of_det_ne_zero {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (hdet : B.det ≠ 0) (R : ℝ) :
    Bornology.IsBounded ((Matrix.toLin' B) ⁻¹' sqBall r ℝ R) := by
  have hS : IsCompact (sqBall r ℝ R) :=
    Metric.isCompact_of_isClosed_isBounded (sqBall_isClosed r R) (sqBall_isBounded r R)
  have hc' : Continuous (Matrix.toLin' B⁻¹) := LinearMap.continuous_of_finiteDimensional _
  refine (hS.image hc').isBounded.subset ?_
  intro y hy
  refine ⟨Matrix.toLin' B y, hy, ?_⟩
  show Matrix.mulVec B⁻¹ (Matrix.mulVec B y) = y
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet),
    Matrix.one_mulVec]

private theorem convex_preimage_sqBall_real {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (R : ℝ) :
    Convex ℝ ((Matrix.toLin' B) ⁻¹' sqBall r ℝ R) :=
  Convex.linear_preimage (sqBall_convex (E := ℝ) r R) (Matrix.toLin' B)

private theorem neg_mem_preimage_sqBall_real {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (R : ℝ) :
    ∀ y ∈ (Matrix.toLin' B) ⁻¹' sqBall r ℝ R, -y ∈ (Matrix.toLin' B) ⁻¹' sqBall r ℝ R := by
  intro y hy
  rw [Set.mem_preimage, map_neg]
  exact sqBall_neg (E := ℝ) r R _ hy

private theorem measurableSet_preimage_sqBall_real {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (R : ℝ) :
    MeasurableSet ((Matrix.toLin' B) ⁻¹' sqBall r ℝ R) := by
  have hc : Continuous (Matrix.toLin' B) := LinearMap.continuous_of_finiteDimensional _
  exact ((sqBall_isClosed r R).preimage hc).measurableSet

private lemma realEllipsoid_props_of_eq {r : ℕ} {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.PosDef) (B : Matrix (Fin r) (Fin r) ℝ)
    (hB : G = Bᵀ * B) (R : ℝ) :
    Convex ℝ {y | qR G y ≤ R ^ 2} ∧ (∀ y ∈ {y | qR G y ≤ R ^ 2}, -y ∈ {y | qR G y ≤ R ^ 2}) ∧
      Bornology.IsBounded {y | qR G y ≤ R ^ 2} ∧ MeasurableSet {y | qR G y ≤ R ^ 2} := by
  subst hB
  have hdet : B.det ≠ 0 := by
    intro h0
    have h1 := hG.det_pos
    rw [Matrix.det_mul, Matrix.det_transpose, h0, mul_zero] at h1
    exact lt_irrefl _ h1
  rw [setR_eq]
  exact ⟨convex_preimage_sqBall_real B R, neg_mem_preimage_sqBall_real B R, isBounded_preimage_sqBall_real_of_det_ne_zero B hdet R, measurableSet_preimage_sqBall_real B R⟩

theorem ellipsoidR_props {r : ℕ} {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.PosDef) (R : ℝ) :
    Convex ℝ {y | qR G y ≤ R ^ 2} ∧ (∀ y ∈ {y | qR G y ≤ R ^ 2}, -y ∈ {y | qR G y ≤ R ^ 2}) ∧
      Bornology.IsBounded {y | qR G y ≤ R ^ 2} ∧ MeasurableSet {y | qR G y ≤ R ^ 2} := by
  obtain ⟨B, hB⟩ := exists_factor_R hG
  exact realEllipsoid_props_of_eq hG B hB R

end ReciprocityTheory.GeometryOfNumbersTheory
end
