module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GNConjTranspose
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDOpFF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDIdentSpec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapAAll

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ProperDomP
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerMatrixLeviBlockThree
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBQ

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem leviElement_mem_GV {k p ρ : ℕ} (q : Matrix (Fin p) (Fin p) ℂ) (hq : IsUnit q.det) : U.muP k p ρ q ∈ B.GV k (p + ρ) :=
  (Formalism.FourierDecayAlt.P.slice_membership k p ρ).2.1 q (isUnit_iff_ne_zero.mp hq)

def MuPToOm : Prop := ∀ (k p ρ : ℕ) (z z' : Fin (2 * (p + ρ) + k + 1) → ℂ), inWb k (p + ρ) z → inWb k (p + ρ) z' →
  ∀ y ∈ domP k (p + ρ) p z z', y ∈ B.GV k (p + ρ) →
  ∃ q : Matrix (Fin p) (Fin p) ℂ, IsUnit q.det ∧ ∃ V ∈ nhds y, IsCompact V ∧
    ∀ g ∈ V, g ∈ B.GV k (p + ρ) → U.muP k p ρ q * g ∈ JF.Om k (p + ρ) z z'

section zhat

variable {k p ρ : ℕ}

theorem corner_matrix_levi_block_three (z z' : Fin (2 * (p + ρ) + k + 1) → ℂ) (hz : inWb k (p + ρ) z) (hz' : inWb k (p + ρ) z')
    (q : Matrix (Fin p) (Fin p) ℂ)
    (product_first_partition : Matrix (Fin p) (Fin p) ℂ) (sizeConstantAtParamsWeight : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ) (flipOneThree : Matrix (Fin p) (Fin p) ℂ)
    (placeRankTwoOne : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ) (TaylorLogMetric : B.Mat k ρ) (flipTwoThree : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ)
    (BlochKatoReduction : Matrix (Fin p) (Fin p) ℂ) (SumRepresentations : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ) (ArithmeticCylinders : Matrix (Fin p) (Fin p) ℂ) :
    Zhat k (p + ρ) z z' (U.muP k p ρ q * U.blk3 product_first_partition sizeConstantAtParamsWeight flipOneThree placeRankTwoOne TaylorLogMetric flipTwoThree BlochKatoReduction SumRepresentations ArithmeticCylinders) =
      Matrix.reindex (Ux3.eC p ρ) (Ux3.eC p ρ) (Matrix.fromBlocks ((qᴴ)⁻¹ * (G.wMat p * BlochKatoReduction))
        ((qᴴ)⁻¹ * (G.wMat p * SumRepresentations * Formalism.QuantumDeterminants.Fm k ρ (U.lowV k p ρ z')))
        ((Formalism.QuantumDeterminants.Fm k ρ (U.lowV k p ρ z))ᴴ * (Hpk k ρ * placeRankTwoOne))
        ((Formalism.QuantumDeterminants.Fm k ρ (U.lowV k p ρ z))ᴴ * (Hpk k ρ * TaylorLogMetric) * Formalism.QuantumDeterminants.Fm k ρ (U.lowV k p ρ z'))) := by
  unfold U.muP
  rw [Ux3.block3_mul, Ux3.z_hat_of_block3 z z' hz hz']
  have hw : ∀ M : Matrix (Fin p) (Fin p) ℂ, G.wMat p * (G.wMat p * M * G.wMat p) = M * G.wMat p := by
    intro M
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Ux3.wMat_mul_self, Matrix.one_mul]
  congr 2 <;> simp only [Matrix.zero_mul, Matrix.one_mul, zero_add, add_zero, Matrix.mul_zero]
  · rw [← Matrix.mul_assoc, hw, Matrix.mul_assoc]
  · rw [← Matrix.mul_assoc (G.wMat p), hw]; simp only [Matrix.mul_assoc]

theorem zhat_eq_blk (z z' : Fin (2 * (p + ρ) + k + 1) → ℂ) (hz : inWb k (p + ρ) z) (hz' : inWb k (p + ρ) z')
    (product_first_partition : Matrix (Fin p) (Fin p) ℂ) (sizeConstantAtParamsWeight : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ) (flipOneThree : Matrix (Fin p) (Fin p) ℂ)
    (placeRankTwoOne : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ) (TaylorLogMetric : B.Mat k ρ) (flipTwoThree : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ)
    (BlochKatoReduction : Matrix (Fin p) (Fin p) ℂ) (SumRepresentations : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ) (ArithmeticCylinders : Matrix (Fin p) (Fin p) ℂ) :
    Zhat k (p + ρ) z z' (U.blk3 product_first_partition sizeConstantAtParamsWeight flipOneThree placeRankTwoOne TaylorLogMetric flipTwoThree BlochKatoReduction SumRepresentations ArithmeticCylinders) =
      Matrix.reindex (Ux3.eC p ρ) (Ux3.eC p ρ) (Matrix.fromBlocks (G.wMat p * BlochKatoReduction)
        (G.wMat p * SumRepresentations * Formalism.QuantumDeterminants.Fm k ρ (U.lowV k p ρ z'))
        ((Formalism.QuantumDeterminants.Fm k ρ (U.lowV k p ρ z))ᴴ * (Hpk k ρ * placeRankTwoOne))
        ((Formalism.QuantumDeterminants.Fm k ρ (U.lowV k p ρ z))ᴴ * (Hpk k ρ * TaylorLogMetric) * Formalism.QuantumDeterminants.Fm k ρ (U.lowV k p ρ z'))) :=
  Ux3.z_hat_of_block3 z z' hz hz' _ _ _ _ _ _ _ _ _

theorem minor_gen {m : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (Bm : Matrix (Fin p) (Fin (ρ + 1)) ℂ)
    (Cm : Matrix (Fin (ρ + 1)) (Fin p) ℂ) (Dm : Matrix (Fin (ρ + 1)) (Fin (ρ + 1)) ℂ)
    (hl : m ≤ ρ + 1) (h : p + m ≤ p + ρ + 1) :
    (Matrix.reindex (Ux3.eC p ρ) (Ux3.eC p ρ) (Matrix.fromBlocks A Bm Cm Dm)).submatrix (Fin.castLE h) (Fin.castLE h) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A (Bm.submatrix id (Fin.castLE hl))
        (Cm.submatrix (Fin.castLE hl) id) (Dm.submatrix (Fin.castLE hl) (Fin.castLE hl))) := by
  ext a b
  refine Fin.addCases (fun a => ?_) (fun a => ?_) a <;> refine Fin.addCases (fun b => ?_) (fun b => ?_) b <;>
    simp [Matrix.reindex_apply, Ux3.eC_symm_castAdd h, Ux3.eC_symm_natAdd h hl]

theorem minor_low {m : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (Bm : Matrix (Fin p) (Fin (ρ + 1)) ℂ)
    (Cm : Matrix (Fin (ρ + 1)) (Fin p) ℂ) (Dm : Matrix (Fin (ρ + 1)) (Fin (ρ + 1)) ℂ)
    (hmp : m ≤ p) (h : m ≤ p + ρ + 1) :
    (Matrix.reindex (Ux3.eC p ρ) (Ux3.eC p ρ) (Matrix.fromBlocks A Bm Cm Dm)).submatrix (Fin.castLE h) (Fin.castLE h) =
      A.submatrix (Fin.castLE hmp) (Fin.castLE hmp) := by
  have e : ∀ a : Fin m, (Ux3.eC p ρ).symm (Fin.castLE h a) = Sum.inl (Fin.castLE hmp a) := by
    intro a; rw [Equiv.symm_apply_eq]; ext; simp [Ux3.column_index_first_val]
  ext a b
  simp [Matrix.reindex_apply, e]

theorem zh_eq_blk (y : B.Mat k (p + ρ)) :
    G.wMat p * y.submatrix (fun a => U.eB k p ρ (Sum.inr a)) (fun b => U.eB k p ρ (Sum.inl (Sum.inl b))) =
      U.Zh k p ρ y := by
  ext a b
  rw [Ux3.wMat_mul_apply]
  simp only [Matrix.submatrix_apply, U.Zh]
  congr 1
  all_goals (ext; first | (rw [Ux3.block_index_last_val]; simp [Fin.val_rev]; omega) | (rw [Ux3.block_index_first_val]))

theorem minor_leviElement_mul_high (z z' : Fin (2 * (p + ρ) + k + 1) → ℂ) (hz : inWb k (p + ρ) z) (hz' : inWb k (p + ρ) z')
    (q : Matrix (Fin p) (Fin p) ℂ) (g : B.Mat k (p + ρ)) (m : ℕ) (hm : m ≤ ρ + 1) :
    Dmin k (p + ρ) z z' (U.muP k p ρ q * g) ⟨p + m, by omega⟩ =
      ((qᴴ)⁻¹).det * Dmin k (p + ρ) z z' g ⟨p + m, by omega⟩ := by
  have hg := Ux3.block3_eta g
  unfold Dmin
  rw [hg, corner_matrix_levi_block_three z z' hz hz', zhat_eq_blk z z' hz hz']
  show ((Matrix.reindex _ _ _).submatrix (Fin.castLE (show p + m ≤ p + ρ + 1 by omega))
    (Fin.castLE (show p + m ≤ p + ρ + 1 by omega))).det = _ * ((Matrix.reindex _ _ _).submatrix
      (Fin.castLE (show p + m ≤ p + ρ + 1 by omega)) (Fin.castLE (show p + m ≤ p + ρ + 1 by omega))).det
  rw [minor_gen _ _ _ _ hm, minor_gen _ _ _ _ hm, Matrix.det_reindex_self, Matrix.det_reindex_self]
  set Q := (qᴴ)⁻¹
  have e : ∀ (A : Matrix (Fin p) (Fin p) ℂ) (Bm : Matrix (Fin p) (Fin m) ℂ) (Cm : Matrix (Fin m) (Fin p) ℂ)
      (Dm : Matrix (Fin m) (Fin m) ℂ),
      Matrix.fromBlocks (Q * A) (Q * Bm) Cm Dm = Matrix.fromBlocks Q 0 0 1 * Matrix.fromBlocks A Bm Cm Dm := by
    intro A Bm Cm Dm
    rw [Matrix.fromBlocks_multiply]
    simp
  have hsub : ∀ (Bm : Matrix (Fin p) (Fin (ρ + 1)) ℂ),
      (Q * Bm).submatrix id (Fin.castLE hm) = Q * Bm.submatrix id (Fin.castLE hm) := by
    intro Bm; ext a b; simp [Matrix.mul_apply]
  rw [hsub, e, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

theorem minor_leviElement_mul_low (z z' : Fin (2 * (p + ρ) + k + 1) → ℂ) (hz : inWb k (p + ρ) z) (hz' : inWb k (p + ρ) z')
    (y : B.Mat k (p + ρ)) (hA : IsUnit (U.Zh k p ρ y).det) (m : ℕ) (hmp : m ≤ p) :
    Dmin k (p + ρ) z z' (U.muP k p ρ (U.Zh k p ρ y)ᴴ * y) ⟨m, by omega⟩ = 1 := by
  have hg := Ux3.block3_eta y
  unfold Dmin
  conv_lhs => rw [hg]
  rw [corner_matrix_levi_block_three z z' hz hz', ← hg]
  show ((Matrix.reindex _ _ _).submatrix (Fin.castLE (show m ≤ p + ρ + 1 by omega))
    (Fin.castLE (show m ≤ p + ρ + 1 by omega))).det = 1
  rw [minor_low _ _ _ _ hmp, zh_eq_blk, Matrix.conjTranspose_conjTranspose, Matrix.nonsing_inv_mul _ hA]
  have : (1 : Matrix (Fin p) (Fin p) ℂ).submatrix (Fin.castLE hmp) (Fin.castLE hmp) = 1 := by
    ext a b; simp [Matrix.one_apply, Fin.ext_iff]
  rw [this, Matrix.det_one]

end zhat

section main

variable {k p ρ : ℕ}

theorem gf_muP (z z' : Fin (2 * (p + ρ) + k + 1) → ℂ) (hz : inWb k (p + ρ) z) (hz' : inWb k (p + ρ) z')
    (q : Matrix (Fin p) (Fin p) ℂ) (g : B.Mat k (p + ρ)) :
    Gf k (p + ρ) z z' (U.muP k p ρ q * g) = Complex.normSq ((qᴴ)⁻¹).det * Gf k (p + ρ) z z' g := by
  have e1 : Fin.last (p + ρ + 1) = (⟨p + (ρ + 1), by omega⟩ : Fin (p + ρ + 2)) := Fin.ext rfl
  have e0 : (⟨p + ρ, by omega⟩ : Fin (p + ρ + 2)) = ⟨p + ρ, by omega⟩ := rfl
  unfold Gf
  rw [e1, minor_leviElement_mul_high z z' hz hz' q g (ρ + 1) le_rfl, minor_leviElement_mul_high z z' hz hz' q g ρ (by omega),
    Complex.normSq_mul, Complex.normSq_mul]
  ring

theorem det_Q_ne {A : Matrix (Fin p) (Fin p) ℂ} (hAd : A.det ≠ 0) : (((Aᴴ)ᴴ)⁻¹).det ≠ 0 := by
  rw [Matrix.conjTranspose_conjTranspose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact inv_ne_zero hAd

theorem omPlus_muP (z z' : Fin (2 * (p + ρ) + k + 1) → ℂ) (hz : inWb k (p + ρ) z) (hz' : inWb k (p + ρ) z')
    (y : B.Mat k (p + ρ)) (hy : y ∈ domP k (p + ρ) p z z') (hAd : (U.Zh k p ρ y).det ≠ 0) :
    U.muP k p ρ (U.Zh k p ρ y)ᴴ * y ∈ Q.OmPlus k (p + ρ) z z' := by
  have hQ := det_Q_ne hAd
  refine ⟨fun l hl => ?_, ?_⟩
  · by_cases hlp : l.val ≤ p
    · have e : l = ⟨l.val, by omega⟩ := Fin.ext rfl
      rw [e, minor_leviElement_mul_low z z' hz hz' y (isUnit_iff_ne_zero.mpr hAd) l.val hlp]
      exact one_ne_zero
    · have e : l = ⟨p + (l.val - p), by omega⟩ := Fin.ext (by simp only; omega)
      have hyl := hy.1 l (by omega) hl
      rw [e] at hyl ⊢
      rw [minor_leviElement_mul_high z z' hz hz' _ y (l.val - p) (by omega)]
      exact mul_ne_zero hQ hyl
  · rw [gf_muP z z' hz hz']
    exact mul_pos (Complex.normSq_pos.mpr hQ) hy.2

end main

theorem mem_of_sub_pre {k n : ℕ} {S : Set (B.Mat k n)} {f : B.Mat k n → B.Mat k n} {V : Set (B.Mat k n)}
    (hVO : V ⊆ {g | f g ∈ S}) {g : B.Mat k n} (hg : g ∈ V) : f g ∈ S := hVO hg

theorem mem_Om_of {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {x : B.Mat k r} (h1 : x ∈ B.GV k r)
    (h2 : x ∈ Q.OmPlus k r z z') : x ∈ JF.Om k r z z' := ⟨h1, h2⟩

theorem levi_move_into_big_cell : MuPToOm := by
  intro k p ρ z z' hz hz' y hy hyG
  have hDp : Dmin k (p + ρ) z z' y ⟨p, by omega⟩ ≠ 0 := hy.1 ⟨p, by omega⟩ (le_refl p) (by simp)
  have hAd : (U.Zh k p ρ y).det ≠ 0 := by
    have h := Formalism.FourierDecayAlt.P.Ux3.zhDmin k p ρ z z' y
    unfold U.DjU at h
    rw [← h]; exact hDp
  have hqu : IsUnit ((U.Zh k p ρ y)ᴴ).det := by
    rw [Matrix.det_conjTranspose]; exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hAd)
  have hy1 := omPlus_muP z z' hz hz' y hy hAd
  have hO : IsOpen {g : B.Mat k (p + ρ) | U.muP k p ρ (U.Zh k p ρ y)ᴴ * g ∈ Q.OmPlus k (p + ρ) z z'} :=
    (Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.isOpen_OmPlus z z').preimage (continuous_const.matrix_mul continuous_id)
  have hy1' : y ∈ {g : B.Mat k (p + ρ) | U.muP k p ρ (U.Zh k p ρ y)ᴴ * g ∈ Q.OmPlus k (p + ρ) z z'} := hy1
  have hmem := hO.mem_nhds hy1'
  have hLC : LocallyCompactSpace (B.Mat k (p + ρ)) :=
    inferInstanceAs (LocallyCompactSpace (Fin (2 * (p + ρ) + k + 1) → Fin (2 * (p + ρ) + k + 1) → ℂ))
  obtain ⟨V, hV, hVO, hVc⟩ := local_compact_nhds hmem
  refine ⟨(U.Zh k p ρ y)ᴴ, hqu, ?_⟩
  refine ⟨V, hV, hVc, ?_⟩
  intro g hg hgG
  have h1 : U.muP k p ρ (U.Zh k p ρ y)ᴴ * g ∈ B.GV k (p + ρ) := by
    have hm := leviElement_mem_GV (k := k) (ρ := ρ) (U.Zh k p ρ y)ᴴ hqu
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hm hgG
  have h2 : U.muP k p ρ (U.Zh k p ρ y)ᴴ * g ∈ Q.OmPlus k (p + ρ) z z' :=
    mem_of_sub_pre (f := fun g => U.muP k p ρ (U.Zh k p ρ y)ᴴ * g) hVO hg
  exact mem_Om_of h1 h2

end Formalism.FourierDecayAlt.P.PBQ
end
end

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBQ

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem properE {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq)
    (e : p + ρ = n) (Cs : Set (B.Mat k n)) (hCs : IsCompact Cs) :
    PartialBesselProperness.Proper Bj B0 e Cs (domP k n p B0.z B0.z') := by
  subst e
  exact properA Bj B0 (fun q hq => leviElement_mem_GV q hq)
    (fun y hy hyG => levi_move_into_big_cell k p ρ B0.z B0.z' B0.z_mem B0.z'_mem y hy hyG) Cs hCs

def ProperDomP : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (j : ℕ) (hj : j ≤ P.r) (Cs : Set (B.Mat P.k P.r)), IsCompact Cs →
    PartialBesselProperness.Proper (p.T.bs j) p.T.base (by omega : j + (P.r - j) = P.r) Cs (domP P.k P.r j p.T.base.z p.T.base.z')

end Formalism.FourierDecayAlt.P.PBQ

namespace Formalism.FourierDecayAlt.P

theorem proper_left_variables_domain : PBQ.ProperDomP := by
  intro Wp Wq _ _ _ _ _ _ P p j hj Cs hCs
  exact PBQ.properE (p.T.bs j) p.T.base _ Cs hCs

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PointLevelZeroEqEmbedding
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section zero

variable {k ρ : ℕ}

theorem block_three_zero_size_eq {n : ℕ} (e : 0 + ρ = n) (A11 : Matrix (Fin 0) (Fin 0) ℂ)
    (A12 : Matrix (Fin 0) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin 0) (Fin 0) ℂ)
    (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin 0) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin 0) ℂ)
    (A31 : Matrix (Fin 0) (Fin 0) ℂ) (A32 : Matrix (Fin 0) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin 0) (Fin 0) ℂ) :
    D.castM e (U.blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33) = D.castM (by omega : ρ = n) A22 := by
  subst e
  ext p q
  rw [LeftFubiniLemmas.castM_apply', LeftFubiniLemmas.castM_apply']
  have hp : (Fin.cast (by omega) p : Fin (2 * (0 + ρ) + k + 1)) = U.eB k 0 ρ (Sum.inl (Sum.inr (Fin.cast (by omega) p))) := by
    ext; rw [Ux3.block_index_middle_val]; simp
  have hq : (Fin.cast (by omega) q : Fin (2 * (0 + ρ) + k + 1)) = U.eB k 0 ρ (Sum.inl (Sum.inr (Fin.cast (by omega) q))) := by
    ext; rw [Ux3.block_index_middle_val]; simp
  rw [hp, hq, Ux3.block3_apply]
  simp

theorem castM_one {a b : ℕ} (h : a = b) : D.castM h (1 : B.Mat k a) = 1 := by
  subst h; exact Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl 1

theorem rn_zero0 (x : U.RC k 0 ρ) : U.Rn k 0 ρ x = 1 := by
  have h1 : D.castM (Nat.zero_add ρ) (U.Rn k 0 ρ x) = 1 := by
    unfold U.Rn
    rw [block_three_zero_size_eq]
    exact castM_one _
  have h2 := Formalism.FourierDecayAlt.P.PBH.asm_castM_symm (Nat.zero_add ρ) (U.Rn k 0 ρ x)
  rw [h1, castM_one] at h2
  exact h2.symm

theorem embG_zero0 {n : ℕ} (e : 0 + ρ = n) (y : B.Mat k ρ) :
    D.castM e (U.embG k 0 ρ y) = D.castM (by omega : ρ = n) y := by
  unfold U.embG
  exact block_three_zero_size_eq e _ _ _ _ _ _ _ _ _

end zero

section side

variable {k : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem jf_left {r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (H : B.Mat k r → (Wq →L[ℂ] Wp))
    (hHc : ContinuousOn H (B.GV k r)) (g : B.Mat k r) (hg : g ∈ B.GV k r)
    (hI : Integrable (JF.integrand Bs H g) Bs.μSS) :
    B.JF Bs H g = ∫ x, psi k r Bs.z cStd (Matrix.of x.2) •
      (Bs.π (Matrix.of x.1)).comp (PBG.Kr Bs H ((Matrix.of x.1)⁻¹ * (Matrix.of x.2)⁻¹ * g)) ∂(Bs.μW.prod Bs.μN) := by
  have := Formalism.FourierDecayAlt.P.B6.haar_sigmaFinite Bs.haarW
  have := Formalism.FourierDecayAlt.P.B6.haar_sigmaFinite Bs.haarN
  have := Formalism.FourierDecayAlt.P.B6.haar_sigmaFinite Bs.haarW'
  have hint : ∀ P, JF.integrand Bs H g P = (1 : ℝ) • D.orbIntegrand Bs g H P := by
    intro P
    rw [one_smul]
    unfold JF.integrand D.orbIntegrand
    rw [VandermondePolynomialIntegral.xi11]
    rfl
  have hI1 : Integrable (fun P => (1 : ℝ) • D.orbIntegrand Bs g H P) Bs.μSS :=
    hI.congr (Filter.Eventually.of_forall hint)
  have hR : ∀ᵐ x ∂(Bs.μW.prod Bs.μN),
      Integrable (VandermondePolynomialIntegral.rint Bs H ((Matrix.of x.1)⁻¹ * (Matrix.of x.2)⁻¹ * g)) (Bs.μW'.prod Bs.μN) := by
    have hI' : Integrable (fun P => (1 : ℝ) • D.orbIntegrand Bs g H P)
        ((Bs.μW.prod Bs.μN).prod (Bs.μW'.prod Bs.μN)) := hI1
    have hgood : ∀ᵐ x ∂(Bs.μW.prod Bs.μN), (Matrix.of x.1 : B.Mat k r) ∈ UWset k r Bs.z ∧
        (Matrix.of x.2 : B.Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r := by
      have a1 : ∀ᵐ x ∂(Bs.μW.prod Bs.μN), (Matrix.of x.1 : B.Mat k r) ∈ UWset k r Bs.z :=
        Measure.quasiMeasurePreserving_fst.ae (Formalism.FourierDecayAlt.P.B6.haar_ae Bs.haarW)
      have a2 : ∀ᵐ x ∂(Bs.μW.prod Bs.μN), (Matrix.of x.2 : B.Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r :=
        Measure.quasiMeasurePreserving_snd.ae (Formalism.FourierDecayAlt.P.B6.haar_ae Bs.haarN)
      filter_upwards [a1, a2] with x h1 h2 using ⟨h1, h2⟩
    filter_upwards [hI'.prod_right_ae, hgood] with x hx hxg
    have hx0 : (Matrix.of x.1 : B.Mat k r)⁻¹ * (Matrix.of x.2)⁻¹ * g ∈ B.GV k r :=
      Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hxg.1.1)
        (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hxg.2.1)) hg
    refine Integrable.mono' hx.norm (VandermondePolynomialIntegral.rint_aesm Bs _ hx0 hHc) (Filter.Eventually.of_forall fun y => ?_)
    have hs := VandermondePolynomialIntegral.orb_split_pt Bs g (fun _ => 1) H x y
    show ‖VandermondePolynomialIntegral.rint Bs H _ y‖ ≤ ‖(1 : ℝ) • D.orbIntegrand Bs g H (x, y)‖
    rw [hs, norm_smul, norm_mul, VandermondePolynomialIntegral.norm_psi]
    simp only [Complex.ofReal_one, norm_one, one_mul]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    rw [← Bs.π_unitary _ hxg.1 (VandermondePolynomialIntegral.rint Bs H _ y v)]
    exact ((Bs.π (Matrix.of x.1)).comp (VandermondePolynomialIntegral.rint Bs H _ y)).le_opNorm v
  have hfub := VandermondePolynomialIntegral.fub Bs g (fun _ => 1) (fun _ => rfl) H hI1 hR
  have hJ : B.JF Bs H g = ∫ P, JF.integrand Bs H g P ∂Bs.μSS := rfl
  rw [hJ, integral_congr_ae (Filter.Eventually.of_forall hint), hfub.2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  unfold VandermondePolynomialIntegral.lint
  simp only [Complex.ofReal_one, one_mul]

theorem muRC0_real (ρ : ℕ) : (U.muRC k 0 ρ).real Set.univ = 1 := by
  have : IsEmpty (G.UT 0) := ⟨fun q => Fin.elim0 q.1.1⟩
  unfold U.muRC
  rw [Measure.volume_eq_prod, measureReal_def, ← Set.univ_prod_univ, Measure.prod_prod,
    Measure.volume_eq_prod, ← Set.univ_prod_univ, Measure.prod_prod]
  simp [volume_pi, Measure.pi_univ]

theorem pbF_zero {ρ n : ℕ} (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : 0 + ρ = n)
    (H : B.Mat k n → (Wq →L[ℂ] Wp)) (y : B.Mat k n) :
    PBQ.pbF Bj B0 e H y = ∫ q, psi k ρ Bj.z cStd (Matrix.of q.2) •
      (Bj.π (Matrix.of q.1)).comp
        (PBG.Kr B0 H (D.castM (by omega : ρ = n) ((Matrix.of q.1 : B.Mat k ρ)⁻¹ * (Matrix.of q.2)⁻¹) * y))
      ∂(Bj.μW.prod Bj.μN) := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) 0 ρ
  have hz := Bj.z_mem
  unfold PBQ.pbF PBQ.muXP
  have hae : (PBQ.pbI Bj B0 e H y) =ᵐ[(Bj.μW.prod Bj.μN).prod (U.muRC k 0 ρ)] fun x =>
      psi k ρ Bj.z cStd (Matrix.of x.1.2) • (Bj.π (Matrix.of x.1.1)).comp
        (PBG.Kr B0 H (D.castM (by omega : ρ = n) ((Matrix.of x.1.1 : B.Mat k ρ)⁻¹ * (Matrix.of x.1.2)⁻¹) * y)) := by
    filter_upwards [PBQ.ae_goodP (p := 0) Bj] with x hx
    unfold PBQ.pbI PBQ.cP PBQ.sP
    rw [if_pos hx]
    simp only [rn_zero0, Matrix.one_mul, embG_zero0, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one (LeftFubiniLemmas.inWb_liftVec hz), mul_one]
  rw [integral_congr_ae hae]
  rw [integral_fun_fst (fun q : Mt k ρ × Mt k ρ => psi k ρ Bj.z cStd (Matrix.of q.2) • (Bj.π (Matrix.of q.1)).comp
    (PBG.Kr B0 H (D.castM (by omega : ρ = n) ((Matrix.of q.1 : B.Mat k ρ)⁻¹ * (Matrix.of q.2)⁻¹) * y))),
    muRC0_real, one_smul]

theorem point_level_zero_eq_embedding (P : M.Par) (hj : 0 + 1 ≤ P.r) (Z : Matrix (Fin 0) (Fin 0) ℂ) (τ : ℂ)
    (γ : B.Mat P.k (P.r - (0 + 1))) : LevelPointCoordinates.x0 P.k P.r 0 hj Z τ γ = LevelPointCoordinates.mLev P 0 hj τ γ := by
  have hz : LevelPointCoordinates.zfull Z τ = Matrix.of fun _ _ => τ := by
    ext i l
    rw [LevelPointCoordinates.zfull_apply]
    have hi : i.val = 0 := by have := i.isLt; omega
    have hl : l.val = 0 := by have := l.isLt; omega
    simp [hi]
  unfold LevelPointCoordinates.x0 LevelPointCoordinates.mLev
  rw [hz]

end side

section main

open Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.PBQ

theorem jfZero {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (hj : 0 + 1 ≤ P.r) (γ : B.Mat P.k (P.r - (0 + 1))) (hγ : γ ∈ B.GV P.k (P.r - (0 + 1)))
    (hΩ : γ ∈ Q.OmPlus P.k (P.r - (0 + 1)) (p.T.bs (0 + 1)).z (p.T.bs (0 + 1)).z') (τ : ℂ) (hτ : τ ≠ 0)
    (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hH : KB.CptCoef p.T.base H) (Z : Matrix (Fin 0) (Fin 0) ℂ) :
    B.JF (p.T.bs 0) H (LevelPointCoordinates.mLev P 0 hj τ γ) =
      PBQ.pbF (p.T.bs 0) p.T.base (by omega : 0 + (P.r - 0) = P.r) H (LevelPointCoordinates.x0 P.k P.r 0 hj Z τ γ) := by
  have hg0 : LevelPointCoordinates.mLev P 0 hj τ γ ∈ JF.Om P.k (P.r - 0) (p.T.bs 0).z (p.T.bs 0).z' := by
    have hm := Formalism.FourierDecayAlt.P.PBH.mcOm P.k (P.r - (0 + 1)) (p.T.bs (0 + 1)).z (p.T.bs (0 + 1)).z'
      (p.T.bs (0 + 1)).z_mem (p.T.bs (0 + 1)).z'_mem τ hτ γ hγ hΩ
    have hm2 := Formalism.FourierDecayAlt.P.PBH.om_cast (by omega : P.r - (0 + 1) + 1 = P.r - 0) _ _ _ hm
    rw [Formalism.FourierDecayAlt.P.PBH.castM_castM', Formalism.FourierDecayAlt.P.PBH.asm_castV_castV, Formalism.FourierDecayAlt.P.PBH.asm_castV_castV,
      ← Formalism.FourierDecayAlt.P.PBH.levTower_bs_z_eq_castV_liftVec p.T 0 hj, ← Formalism.FourierDecayAlt.P.PBH.levTower_bs_z'_eq_castV_liftVec p.T 0 hj] at hm2
    exact hm2
  have hCpt : KB.CptCoef (p.T.bs 0) H := hH
  rw [jf_left (p.T.bs 0) H (Formalism.FourierDecayAlt.P.PBH.asm_contOn_of_ckOn hCpt.1) _ hg0.1
    (Formalism.FourierDecayAlt.P.PBH.rhs_int (p.T.bs 0) H hCpt _ hg0), pbF_zero, point_level_zero_eq_embedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  beta_reduce
  rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  rfl

theorem side0Zero_of (hW : PartialBesselProperness.PbWords) (hPr : ProperLeftVariablesDomain) (hPts : CutHB.Pts) : CutHB.Side0Zero := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh γ hj0 hF hw hγ hΩ e τ hτ
  subst hj0
  have hnil : h = [] := by
    cases h with
    | nil => rfl
    | cons b t =>
      exfalso
      have h1 := (hh.1 b (List.mem_cons.2 (Or.inl rfl))).1
      have h2 := hh.2
      simp only [D.ptSize, List.map_cons, List.sum_cons] at h2
      omega
  subst hnil

  set H : B.Mat P.k P.r → (Wq →L[ℂ] Wp) := D.uwG P.k P.r p.T.base.z p.T.base.z' F 0 (by omega) w e with hHdef
  have hG0 : KB.slv p.T F 0 (by omega) w [] hh.2 e = H := by
    funext y
    unfold KB.slv D.castF
    refine (Formalism.FourierDecayAlt.P.Dx1.SN.sliceAt_nil P.k P.r _ _ p.T.base.z_mem p.T.base.z'_mem H _).trans ?_
    exact congrArg H (Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl y)
  have hCpt : KB.CptCoef (p.T.bs 0) H := hG0 ▸ Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F 0 (by omega) w [] hh hF e

  have hg0 : LevelPointCoordinates.mLev P 0 hj τ γ ∈ JF.Om P.k (P.r - 0) (p.T.bs 0).z (p.T.bs 0).z' := by
    have hm := Formalism.FourierDecayAlt.P.PBH.mcOm P.k (P.r - (0 + 1)) (p.T.bs (0 + 1)).z (p.T.bs (0 + 1)).z'
      (p.T.bs (0 + 1)).z_mem (p.T.bs (0 + 1)).z'_mem τ hτ γ hγ hΩ
    have hm2 := Formalism.FourierDecayAlt.P.PBH.om_cast (by omega : P.r - (0 + 1) + 1 = P.r - 0) _ _ _ hm
    rw [Formalism.FourierDecayAlt.P.PBH.castM_castM', Formalism.FourierDecayAlt.P.PBH.asm_castV_castV, Formalism.FourierDecayAlt.P.PBH.asm_castV_castV,
      ← Formalism.FourierDecayAlt.P.PBH.levTower_bs_z_eq_castV_liftVec p.T 0 hj, ← Formalism.FourierDecayAlt.P.PBH.levTower_bs_z'_eq_castV_liftVec p.T 0 hj] at hm2
    exact hm2

  have hL := jf_left (p.T.bs 0) H (Formalism.FourierDecayAlt.P.PBH.asm_contOn_of_ckOn hCpt.1) _ hg0.1
    (Formalism.FourierDecayAlt.P.PBH.rhs_int (p.T.bs 0) H hCpt _ hg0)
  rw [hG0, hL]

  have hE : IsEmpty (U.LW (D.ptPerm ([] : C.LPt))) := ⟨fun q => Fin.elim0 (q.1.1 : Fin 0)⟩
  have hF0 : IsEmpty (Fin (D.ptSize ([] : C.LPt))) := ⟨fun i => Fin.elim0 (i : Fin 0)⟩
  set x₀ : XH ([] : C.LPt) := fun q => (hE.false q).elim with hx₀
  have hone : ∫ v, ellH ([] : C.LPt) v (CutHB.phf p F 0 hj w [] hh.2 γ v e τ) =
      CutHB.phf p F 0 hj w [] hh.2 γ x₀ e τ := by
    rw [volume_pi, Measure.pi_of_empty (fun _ => volume) x₀, integral_dirac]
    unfold ellH
    have hs : U.subS (LeftFubiniLemmas.lhOf (D.ptPerm ([] : C.LPt)) x₀) = 0 := by
      unfold U.subS
      exact Finset.sum_of_isEmpty _
    rw [hs]
    simp [G.psi]
  rw [hone]

  obtain ⟨R, hRF⟩ := hF.2.1
  have hpts := hPts Wp Wq P p 0 hj [] hh γ hγ hΩ x₀
  have hy0D := hpts.2 τ hτ
  have hy0G := LevelPointCoordinates.x0_GV hj hpts.1 hτ hγ
  have hPW := hW P.k 0 (P.r - 0) P.r Wp Wq (p.T.bs 0) p.T.base (by omega) (p.T.z_lev 0 (Nat.zero_le _)).symm 0
    (Nat.zero_le _) F {g | B.gN g ≤ R} (fun g hg _ => hF.1 g hg) (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le _ _ R)
    (fun g hg hgC => by
      by_contra h0
      exact hgC (hRF g hg h0))
    (domP P.k P.r 0 p.T.base.z p.T.base.z') (isOpen_domP _ _ _ _ _)
    (fun g hg => hg.1 ⟨0, by omega⟩ (le_refl _) (Nat.zero_le _))
    (hPr Wp Wq P p 0 (Nat.zero_le _) _ (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le _ _ R)) w e _ hy0D hy0G
  unfold CutHB.phf pbT
  rw [hPW, pbF_zero, point_level_zero_eq_embedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  beta_reduce
  rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  rfl

end main

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDJNice
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutSE

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem radial_orbital_niceness : RDJNice := by
  intro k r Wp Wq _ _ _ _ _ _ D F hF
  obtain ⟨ε, hε, hN⟩ := hF
  have h := Formalism.FourierDecayAlt.P.bessel_function_finite_class k r Wp Wq D F ε hε hN
  refine ⟨by rw [ffl_om_eq]; exact h, ?_⟩
  intro g₀ hg₀
  obtain ⟨U, F', hU, hgU, hc, he⟩ := h.1 g₀ ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hg₀.1, hg₀.2⟩
  exact ⟨U, F', hU, hgU, by exact_mod_cast hc, fun g hg hgG => he g hg (Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hgG)⟩

end Formalism.FourierDecayAlt.P.CutSE
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHBSupp
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.PBQ

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def ProperDomP : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (j : ℕ) (hj : j ≤ P.r) (Cs : Set (B.Mat P.k P.r)), IsCompact Cs →
    PartialBesselProperness.Proper (p.T.bs j) p.T.base (by omega : j + (P.r - j) = P.r) Cs (domP P.k P.r j p.T.base.z p.T.base.z')

theorem zxH_rfl (h : C.LPt) (v : XH h) : zxH h (D.ptSize h) rfl v = LeftFubiniLemmas.lhOf (D.ptPerm h) v *
    U.hMat (D.ptPerm h) (D.ptDiag h) := by
  first
  | rfl
  | simp [zxH]

theorem supp_of (hW : PartialBesselProperness.PbWords) (hP : ProperDomP) : Supp := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh γ hF hw hγ hΩ K _ hK0
  obtain ⟨hh1, hh2⟩ := hh
  subst hh2
  have hhh : D.IsLocPt h (D.ptSize h) := ⟨hh1, rfl⟩
  obtain ⟨R, hR⟩ := hF.2.1
  set Cs : Set (B.Mat P.k P.r) := {g | B.gN g ≤ R} with hCs
  have hCc : IsCompact Cs := Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le P.k P.r R
  have e : D.ptSize h + (P.r - D.ptSize h) = P.r := by omega
  have hd : ∀ i, D.ptDiag h i ≠ 0 := ptDiag_ne hhh

  have hR1 : ∀ ew : Wd.Ix (Fin w.length), ∃ R1 : ℝ, ∀ v : XH h, R1 < ‖v‖ → ∀ g ∈ B.GV P.k P.r,
      U.Zh P.k (D.ptSize h) (P.r - D.ptSize h) (D.castM e.symm g) =
        LeftFubiniLemmas.lhOf (D.ptPerm h) v * U.hMat (D.ptPerm h) (D.ptDiag h) →
      pbF (p.T.bs (D.ptSize h)) p.T.base e
        (D.uwG P.k P.r p.T.base.z p.T.base.z' F (D.ptSize h) (by omega) w ew) g = 0 := by
    intro ew
    refine pb_head_support (p.T.bs (D.ptSize h)) p.T.base e (D.ptPerm h) (D.ptDiag h) hd _ Cs hCc ?_
    intro g hg hgC
    by_contra hne
    exact hgC (Formalism.FourierDecayAlt.P.PBG.uwG_supp p.T.base.z p.T.base.z' F R hR (D.ptSize h) (by omega) w ew g hg hne)
  choose R1 hR1 using hR1
  refine ⟨⋃ ew, Metric.closedBall (0 : XH h) (R1 ew), isCompact_iUnion fun ew => isCompact_closedBall _ _,
    fun v hv τ hτK ew => ?_⟩
  have hτ : τ ≠ 0 := hK0 hτK
  have hvR : R1 ew < ‖v‖ := by
    by_contra hle
    have hle : ‖v‖ ≤ R1 ew := not_lt.mp hle
    exact hv (Set.mem_iUnion.2 ⟨ew, by rw [Metric.mem_closedBall, dist_zero_right]; exact hle⟩)
  have hpt := pts Wp Wq P p (D.ptSize h) hj h hhh γ hγ hΩ v
  have hyD := hpt.2 τ hτ
  have hyG := x0_GV hj hpt.1 hτ hγ
  have hz : p.T.base.z = D.castV e (liftVec P.k (D.ptSize h) (P.r - D.ptSize h) (p.T.bs (D.ptSize h)).z) :=
    (p.T.z_lev (D.ptSize h) (by omega)).symm
  have hPW := hW P.k (D.ptSize h) (P.r - D.ptSize h) P.r Wp Wq (p.T.bs (D.ptSize h)) p.T.base e hz (D.ptSize h)
    (by omega) F Cs (fun g hg _ => hF.1 g hg) hCc
    (fun g hg hgC => by
      by_contra hne
      exact hgC (hR g hg hne))
    (domP P.k P.r (D.ptSize h) p.T.base.z p.T.base.z') (isOpen_domP _ _ _ _ _)
    (fun g hg => hg.1 ⟨D.ptSize h, by omega⟩ (show D.ptSize h ≤ D.ptSize h from le_rfl) (show D.ptSize h ≤ P.r by omega))
    (hP Wp Wq P p (D.ptSize h) (by omega) Cs hCc) w ew _ hyD hyG
  unfold phf
  unfold pbT
  rw [hPW]
  refine hR1 ew v hvR _ hyG ?_
  rw [leading_block_of_base_point hj _ τ γ e.symm, zxH_rfl]

end Formalism.FourierDecayAlt.P.CutHB
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpA
open MeasureTheory
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

def RDSPolyProp : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (o κ : ℕ) (Θ : B.DiffOp k r Wp Wq), CutMP.PolyOp o κ Θ → B.Commutes D (B.GPos D) Θ → OpProp1 D Θ

def RDSAGrp : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (D : B.RealPlaceData P.k P.r Wp Wq), IsPlace P D.z D.z' D.π D.π' → ∀ y : ℂ,
    ∃ Θ Θv : B.DiffOp P.k P.r Wp Wq, (∃ o κ : ℕ, CutMP.PolyOp o κ Θ) ∧ (∃ o κ : ℕ, CutMP.PolyOp o κ Θv) ∧
      B.Commutes D (B.GPos D) Θ ∧ B.Commutes D (B.GPos D) Θv ∧
      ∀ J : B.Mat P.k P.r → (Wq →L[ℂ] Wp), J ∈ Q.FFl P.k P.r D.z D.z' D.π D.π' 0 (JF.Om P.k P.r D.z D.z') →
        ∀ x ∈ DomR P.k P.r D.z D.z',
          resG P.k P.r (Fin.last P.r) (B.opApply Θ J) x.1 x.2 =
              CutMP.dMul (CutMP.drF P.r) (Q.crd (Q.cmp (Q.vAB P.r y P.r) 0) (resG P.k P.r (Fin.last P.r) J)) x.1 x.2 ∧
            resG P.k P.r (Fin.last P.r) (B.opApply Θv J) x.1 x.2 =
              CutMP.dMul (CutMP.drbF P.r) (Q.crd (Q.cmp (CutMP.vABm P.r y P.r) 0) (resG P.k P.r (Fin.last P.r) J))
                x.1 x.2

def RDSARad : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π')
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r), IsActualLevel X L →
    ∀ (y : ℂ) (Φ : RadSp P.k P.r z z' π π'),
      (((L.Ahat y).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) =
          CutMP.dMul (CutMP.drF P.r) (Q.crd (Q.cmp (Q.vAB P.r y P.r) 0) (Φ : Fn P.k P.r (Wq →L[ℂ] Wp))) ∧
        (((L.Ahatv y).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) =
          CutMP.dMul (CutMP.drbF P.r) (Q.crd (Q.cmp (CutMP.vABm P.r y P.r) 0) (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)))

def RDSALoc : Prop :=
  ∀ (r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (y : ℂ) (f f' : (Fin r → ℂ) → E),
    (∀ c ∈ OmX r, f c = f' c) → ∀ c ∈ OmX r,
      (Q.vAB r y r).1 f c = (Q.vAB r y r).1 f' c ∧ (CutMP.vABm r y r).1 f c = (CutMP.vABm r y r).1 f' c

theorem rds_dMul_loc {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (hLoc : RDSALoc) (y : ℂ)
    (Φ Ψ : Fn k r E) (g : Mx k r) (hΦΨ : ∀ c ∈ OmX r, Φ c g = Ψ c g) (c : Fin r → ℂ) (hc : c ∈ OmX r) :
    CutMP.dMul (CutMP.drF r) (Q.crd (Q.cmp (Q.vAB r y r) 0) Φ) c g =
        CutMP.dMul (CutMP.drF r) (Q.crd (Q.cmp (Q.vAB r y r) 0) Ψ) c g ∧
      CutMP.dMul (CutMP.drbF r) (Q.crd (Q.cmp (CutMP.vABm r y r) 0) Φ) c g =
        CutMP.dMul (CutMP.drbF r) (Q.crd (Q.cmp (CutMP.vABm r y r) 0) Ψ) c g := by
  obtain ⟨h1, h2⟩ := hLoc r E y (fun c' => Φ c' g) (fun c' => Ψ c' g) (fun c' hc' => hΦΨ c' hc') c hc
  simp only [CutMP.dMul, Q.crd, Q.cmp, if_true]
  exact ⟨by rw [h1], by rw [h2]⟩

theorem rDSOpA_of_parts (hP : RDSPolyProp) (hG : RDSAGrp) (hR : RDSARad) (hLoc : RDSALoc) : RDSOpA := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD _ _ hz hz' hπ hπ' _ Y _ _ _ _
  subst hz hz' hπ hπ'
  obtain ⟨hPl, -, hL, -⟩ := hD
  obtain ⟨Θ, Θv, ⟨o, κ, hpo⟩, hpv, hc, hcv, hres⟩ := hG Wp Wq P D hPl Y
  refine ⟨Θ, hP P.k P.r Wp Wq D o κ Θ hpo hc, ?_⟩
  intro J hJ Φ hΦ x hx
  have e := congrFun (congrFun (hR Wp Wq P D.z D.z' D.π D.π' X L hL Y Φ).1 x.1) x.2
  refine ((hres J hJ x hx).1).trans (Eq.trans ?_ e.symm)
  obtain ⟨hc1, hg1, hG1⟩ := hx
  exact (rds_dMul_loc hLoc Y _ _ x.2
    (fun c' hc' => (hΦ (c', x.2) ⟨hc', hg1, hG1⟩).symm) x.1 hc1).1

theorem rDSOpAv_of_parts (hP : RDSPolyProp) (hG : RDSAGrp) (hR : RDSARad) (hLoc : RDSALoc) : RDSOpAv := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD _ _ hz hz' hπ hπ' _ Y _ _ _ _
  subst hz hz' hπ hπ'
  obtain ⟨hPl, -, hL, -⟩ := hD
  obtain ⟨Θ, Θv, hpa, ⟨o, κ, hpo⟩, hca, hc, hres⟩ := hG Wp Wq P D hPl (Y + 1)
  refine ⟨Θv, hP P.k P.r Wp Wq D o κ Θv hpo hc, ?_⟩
  intro J hJ Φ hΦ x hx
  have e := congrFun (congrFun (hR Wp Wq P D.z D.z' D.π D.π' X L hL (Y + 1) Φ).2 x.1) x.2
  refine ((hres J hJ x hx).2).trans (Eq.trans ?_ e.symm)
  obtain ⟨hc1, hg1, hG1⟩ := hx
  exact (rds_dMul_loc hLoc (Y + 1) _ _ x.2
    (fun c' hc' => (hΦ (c', x.2) ⟨hc', hg1, hG1⟩).symm) x.1 hc1).2

end Formalism.FourierDecayAlt.P.CutSE
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSCoordAdj
open MeasureTheory Filter Topology
open scoped Matrix ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section Mul

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [FiniteDimensional ℂ Wp]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem rAdj_realMul (μ : Measure (Mt k r)) (W : Module.End ℂ (RadSp k r z z' π π')) (m : Mx k r → ℝ)
    (hW : ∀ (Φ : RadSp k r z z' π π'), ∀ x ∈ DomR k r z z',
      (W Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = ((m x.2 : ℝ) : ℂ) • (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2) :
    RAdj μ (mkP W W) := by
  have hval : ∀ (Φ : RadSp k r z z' π π') (x : (Fin r → ℂ) × Mx k r),
      (W Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = ((m x.2 : ℝ) : ℂ) • (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 := by
    intro Φ x
    by_cases hx : x ∈ DomR k r z z'
    · exact hW Φ x hx
    · rw [Formalism.FourierDecayAlt.P5.radSp_zero_off (W Φ) hx, Formalism.FourierDecayAlt.P5.radSp_zero_off Φ hx, smul_zero]
  have htest : ∀ Ψ : RadSp k r z z' π π', RTest Ψ → RTest (W Ψ) := by
    rintro Ψ ⟨K, hK, hKD, h0⟩
    exact ⟨K, hK, hKD, fun x hx => by rw [hval, h0 x hx, smul_zero]⟩
  have hip : ∀ Φ Ψ : RadSp k r z z' π π', radIp μ (W Φ) Ψ = radIp μ Φ (W Ψ) := by
    intro Φ Ψ
    unfold radIp
    congr 1; funext c; congr 1; funext x
    have e1 := hval Φ (c, Matrix.of x)
    have e2 := hval Ψ (c, Matrix.of x)
    simp only at e1 e2
    rw [e1, e2, hsVec_smul_rd, hsVec_smul_rd, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  exact ⟨htest, htest, fun Φ Ψ _ => hip Φ Ψ, fun Φ Ψ _ => hip Φ Ψ⟩

end Mul

theorem spectral_function_adjoint : RDSFnAdj := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD _ _ _ _ _ _ _
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hGGi, -⟩ := hD.2.2.1
  rw [hGGi]
  refine rAdj_realMul μ (X.fn 5) (fun g => (GGl P.k P.r z z' g)⁻¹) fun Φ x hx => ?_
  rw [X.fn_apply 5 Φ x hx]
  simp [fnVal]

section MulC

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [FiniteDimensional ℂ Wp]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem rAdj_mulPair (μ : Measure (Mt k r)) (W W' : Module.End ℂ (RadSp k r z z' π π')) (m : (Fin r → ℂ) → ℂ)
    (hW : ∀ (Φ : RadSp k r z z' π π') c g, (W Φ : Fn k r (Wq →L[ℂ] Wp)) c g = m c • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g)
    (hW' : ∀ (Φ : RadSp k r z z' π π') c g,
      (W' Φ : Fn k r (Wq →L[ℂ] Wp)) c g = conj (m c) • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g) :
    RAdj μ (mkP W W') ∧ RAdj μ (mkP W' W) := by
  have ht : ∀ (V : Module.End ℂ (RadSp k r z z' π π')) (m' : (Fin r → ℂ) → ℂ),
      (∀ (Φ : RadSp k r z z' π π') c g, (V Φ : Fn k r (Wq →L[ℂ] Wp)) c g = m' c • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g) →
      ∀ Ψ, RTest Ψ → RTest (V Ψ) := by
    rintro V m' hV Ψ ⟨K, hK, hKD, h0⟩
    exact ⟨K, hK, hKD, fun x hx => by rw [hV, h0 x hx, smul_zero]⟩
  have h1 : ∀ Φ Ψ : RadSp k r z z' π π', radIp μ (W Φ) Ψ = radIp μ Φ (W' Ψ) := by
    intro Φ Ψ
    unfold radIp
    congr 1; funext c; congr 1; funext x
    rw [hW, hW', hsVec_smul_rd, hsVec_smul_rd, inner_smul_left, inner_smul_right]
  have h2 : ∀ Φ Ψ : RadSp k r z z' π π', radIp μ (W' Φ) Ψ = radIp μ Φ (W Ψ) := by
    intro Φ Ψ
    unfold radIp
    congr 1; funext c; congr 1; funext x
    rw [hW, hW', hsVec_smul_rd, hsVec_smul_rd, inner_smul_left, inner_smul_right, Complex.conj_conj]
  exact ⟨⟨ht W m hW, ht W' _ hW', fun Φ Ψ _ => h1 Φ Ψ, fun Φ Ψ _ => h2 Φ Ψ⟩,
    ⟨ht W' _ hW', ht W m hW, fun Φ Ψ _ => h2 Φ Ψ, fun Φ Ψ _ => h1 Φ Ψ⟩⟩

end MulC

def RDSPAdj : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq), IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' →
    D.π = π → D.π' = π' → 0 < P.r →
    ∀ l, RAdj μ (L.p l) ∧ RAdj μ (L.pb l)

theorem rDSCoordAdj_of_p (hp : RDSPAdj) : RDSCoordAdj := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' hr l
  obtain ⟨-, -, hc, hci, hcb, hcbi, -⟩ := hD.2.2.1
  obtain ⟨hpl, hpbl⟩ := hp Wp Wq P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' hr l
  have e : ∀ (i : Fin 6) (Φ : RadSp P.k P.r z z' π π') c g,
      (X.op l i Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = Formalism.QuantumDeterminants.opL l i (fun c' => (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c' g) c :=
    fun i Φ c g => by rw [X.op_apply]; rfl
  have C1 := rAdj_mulPair μ (X.op l 1) (X.op l 4) (fun c => c l) (fun Φ c g => by rw [e]; rfl)
    (fun Φ c g => by rw [e]; rfl)
  have C2 := rAdj_mulPair μ (X.op l 2) (X.op l 5) (fun c => (c l)⁻¹) (fun Φ c g => by rw [e]; rfl)
    (fun Φ c g => by rw [e]; simp [Formalism.QuantumDeterminants.opL, Formalism.QuantumDeterminants.cbiOp, map_inv₀])
  refine ⟨hpl, hpbl, ?_, ?_, ?_, ?_⟩
  · rw [hc]; exact C1.1
  · rw [hci]; exact C2.1
  · rw [hcb]; exact C1.2
  · rw [hcbi]; exact C2.2

section IpLin

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [FiniteDimensional ℂ Wp]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end IpLin

end Formalism.FourierDecayAlt.P.CutSE
end
end
