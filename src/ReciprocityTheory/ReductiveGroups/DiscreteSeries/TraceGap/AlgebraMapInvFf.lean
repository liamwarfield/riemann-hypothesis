module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.MemHighestWeightSubIff

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.AdPhysDiagSingle
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

theorem fockBasis_eq (S : Finset (Fin (n * n))) :
    fockBasis n S = ExteriorAlgebra.ιMulti ℂ S.card
      (fun i => Pi.single (finProdFinEquiv.symm (S.orderEmbOfFin rfl i)) (1 : ℂ)) := by
  have hb : fockBasis n S = ExteriorAlgebra.ιMulti ℂ S.card
      (((Pi.basisFun ℂ (Fin n × Fin n)).reindex finProdFinEquiv) ∘ S.orderEmbOfFin rfl) := by
    rw [fockBasis, ExteriorAlgebra.basis_apply]
    rfl
  have hv : ((Pi.basisFun ℂ (Fin n × Fin n)).reindex finProdFinEquiv) ∘ S.orderEmbOfFin rfl =
      fun i => Pi.single (finProdFinEquiv.symm (S.orderEmbOfFin rfl i)) (1 : ℂ) := by
    funext i
    simp
  rw [hb, hv]

theorem adPhys_single (k : Matrix (Fin n) (Fin n) ℂ) (y : Fin n × Fin n) :
    adPhys ε k (Pi.single y 1) = ∑ x, adMat ε k x y • Pi.single x (1 : ℂ) := by
  funext z
  simp [adPhys, Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_apply]

theorem adPhys_diag_single (s : Fin n → ℂ) (x : Fin n × Fin n) :
    adPhys ε (Matrix.diagonal s) (Pi.single x 1) = modeChar ε s x • Pi.single x (1 : ℂ) := by
  funext y
  simp only [adPhys, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.smul_apply, smul_eq_mul]
  by_cases h : y = x
  · subst h
    by_cases hy : IsPhys ε y <;> simp [adMat, modeChar, hy]
  · simp only [h, if_false]
    obtain ⟨y1, y2⟩ := y
    obtain ⟨x1, x2⟩ := x
    simp only [adMat, Matrix.diagonal_apply]
    split_ifs <;> simp_all

theorem ff_diag (s : Fin n → ℂ) (S : Finset (Fin (n * n))) :
    ff ε (Matrix.diagonal s) (fockBasis n S) =
      (∏ m ∈ S, modeChar ε s (finProdFinEquiv.symm m)) • fockBasis n S := by
  rw [fockBasis_eq, ff, ExteriorAlgebra.map_apply_ιMulti]
  simp only [Function.comp_def, adPhys_diag_single]
  rw [AlternatingMap.map_smul_univ]
  congr 1
  conv_rhs => rw [← S.map_orderEmbOfFin_univ rfl]
  rw [Finset.prod_map]
  rfl

def adPoly (ε : Fin n → Bool) (x y : Fin n × Fin n) : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ :=
  if IsPhys ε x then
    (if IsPhys ε y then MvPolynomial.X (Sum.inl (x.1, y.1)) * MvPolynomial.X (Sum.inr (x.2, y.2)) else 0)
  else if x = y then 1 else 0

theorem eval_adPoly (k : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n × Fin n) :
    MvPolynomial.eval (Sum.elim (fun p => k p.1 p.2) (fun p => star (k p.1 p.2))) (adPoly ε x y) =
      adMat ε k x y := by
  unfold adPoly adMat
  split_ifs <;> simp

theorem ffMat_eq (k : Matrix (Fin n) (Fin n) ℂ) (S T : Finset (Fin (n * n))) :
    ffMat ε k S T = ∑ h : Fin T.card → Fin n × Fin n,
      (∏ i, adMat ε k (h i) (finProdFinEquiv.symm (T.orderEmbOfFin rfl i))) *
        (fockBasis n).repr (ExteriorAlgebra.ιMulti ℂ T.card (fun i => Pi.single (h i) (1 : ℂ))) S := by
  rw [ffMat, LinearMap.toMatrix_apply, AlgHom.toLinearMap_apply, fockBasis_eq, ff,
    ExteriorAlgebra.map_apply_ιMulti]
  simp only [Function.comp_def, adPhys_single]
  have h := (ExteriorAlgebra.ιMulti ℂ T.card).toMultilinearMap.map_sum
    (fun i x => adMat ε k x (finProdFinEquiv.symm (T.orderEmbOfFin rfl i)) • Pi.single x (1 : ℂ))
  simp only [AlternatingMap.coe_multilinearMap] at h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [AlternatingMap.map_smul_univ, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem ffMat_poly (S T : Finset (Fin (n * n))) :
    ∃ P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ, ∀ k : Matrix (Fin n) (Fin n) ℂ,
      ffMat ε k S T = MvPolynomial.eval (Sum.elim (fun p => k p.1 p.2) (fun p => star (k p.1 p.2))) P := by
  refine ⟨∑ h : Fin T.card → Fin n × Fin n,
    (∏ i, adPoly ε (h i) (finProdFinEquiv.symm (T.orderEmbOfFin rfl i))) *
      MvPolynomial.C ((fockBasis n).repr (ExteriorAlgebra.ιMulti ℂ T.card (fun i => Pi.single (h i) (1 : ℂ))) S),
    fun k => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ffMat_eq, map_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [map_mul, map_prod, MvPolynomial.eval_C]
  simp only [eval_adPoly]

theorem ffMat_continuous (S T : Finset (Fin (n * n))) :
    Continuous fun k : Matrix (Fin n) (Fin n) ℂ => ffMat ε k S T := by
  obtain ⟨P, hP⟩ := ffMat_poly (ε := ε) S T
  simp only [hP]
  refine (MvPolynomial.continuous_eval P).comp ?_
  refine continuous_pi fun p => ?_
  rcases p with p | p
  · exact (continuous_apply p.2).comp (continuous_apply p.1)
  · exact continuous_star.comp ((continuous_apply p.2).comp (continuous_apply p.1))

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

theorem cpV_eq_sum (v : Fin n × Fin n → ℂ) : cpV v = ∑ x, v x • cpFock (n := n) x.1 x.2 := by
  refine LinearMap.ext fun y => ?_
  have hv : v = ∑ x, v x • Pi.single x (1 : ℂ) := by
    funext z
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [cpV, cpFock, LinearMap.sum_apply, Finset.sum_mul]

theorem cmV_eq_sum (v : Fin n × Fin n → ℂ) : cmV v = ∑ x, star (v x) • cmFock (n := n) x.1 x.2 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [cmV, dualV, map_sum]
  simp only [map_smul]
  rfl

theorem toMatrix_cmV (v : Fin n × Fin n → ℂ) :
    LinearMap.toMatrix (fockBasis n) (fockBasis n) (cmV v) =
      (LinearMap.toMatrix (fockBasis n) (fockBasis n) (cpV v))ᴴ := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [cmV_eq_sum, cpV_eq_sum, map_sum, map_sum, Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul, map_smul, Matrix.conjTranspose_smul, lf_toMatrix_cm, lf_toMatrix_cp, fockMatrix_conjTranspose_eq_transpose]

theorem adPhys_kkH {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (w : Fin n × Fin n → ℂ) :
    adPhys ε k (adPhys ε kᴴ w) = w := by
  have hkk : k * kᴴ = 1 := by
    have := hk.1
    rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose] at this
    exact this
  rw [← LinearMap.comp_apply, ← adPhys_mul hk (kset_conjTranspose hk), hkk]
  simp [adPhys, adMat_one]

theorem ffMat_H_cp {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (w : Fin n × Fin n → ℂ) :
    LinearMap.toMatrix (fockBasis n) (fockBasis n) (cpV (adPhys ε kᴴ w)) * (ffMat ε k)ᴴ =
      (ffMat ε k)ᴴ * LinearMap.toMatrix (fockBasis n) (fockBasis n) (cpV w) := by
  have h := congrArg (LinearMap.toMatrix (fockBasis n) (fockBasis n)) (ff_cmV hk (adPhys ε kᴴ w))
  rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, adPhys_kkH hk, toMatrix_cmV, toMatrix_cmV] at h
  have h2 := congrArg Matrix.conjTranspose h
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_conjTranspose] at h2
  exact h2

theorem nH_cpV {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (w : Fin n × Fin n → ℂ) (z : Fock n) :
    Matrix.toLin (fockBasis n) (fockBasis n) (ffMat ε k)ᴴ (cpV w z) =
      cpV (adPhys ε kᴴ w) (Matrix.toLin (fockBasis n) (fockBasis n) (ffMat ε k)ᴴ z) := by
  have h := congrArg (Matrix.toLin (fockBasis n) (fockBasis n)) (ffMat_H_cp hk w)
  rw [Matrix.toLin_mul (v₁ := fockBasis n) (v₂ := fockBasis n) (v₃ := fockBasis n),
    Matrix.toLin_mul (v₁ := fockBasis n) (v₂ := fockBasis n) (v₃ := fockBasis n),
    Matrix.toLin_toMatrix, Matrix.toLin_toMatrix] at h
  have h3 := LinearMap.congr_fun h z
  simp only [LinearMap.comp_apply] at h3
  exact h3.symm

theorem algebraMapInv_ff (k : Matrix (Fin n) (Fin n) ℂ) (x : Fock n) :
    ExteriorAlgebra.algebraMapInv (ff ε k x) = ExteriorAlgebra.algebraMapInv x := by
  have : (ExteriorAlgebra.algebraMapInv (R := ℂ) (M := Fin n × Fin n → ℂ)).comp (ff ε k) =
      ExteriorAlgebra.algebraMapInv := by
    apply ExteriorAlgebra.hom_ext
    refine LinearMap.ext fun m => ?_
    simp [ff, ExteriorAlgebra.algebraMapInv]
  exact AlgHom.congr_fun this x

theorem ιMulti_card_zero (p : ℕ) (v : Fin p → (Fin n × Fin n → ℂ)) (hp : p = 0) :
    ExteriorAlgebra.ιMulti ℂ p v = 1 := by
  subst hp
  exact ExteriorAlgebra.ιMulti_zero_apply v

theorem algebraMapInv_ιMulti_pos (p : ℕ) (v : Fin p → (Fin n × Fin n → ℂ)) (hp : 0 < p) :
    ExteriorAlgebra.algebraMapInv (ExteriorAlgebra.ιMulti ℂ p v) = 0 := by
  cases p with
  | zero => omega
  | succ p =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, map_mul]
    simp [ExteriorAlgebra.algebraMapInv]

theorem repr_empty (x : Fock n) : (fockBasis n).repr x ∅ = ExteriorAlgebra.algebraMapInv x := by
  have : Finsupp.lapply ∅ ∘ₗ (fockBasis n).repr.toLinearMap =
      (ExteriorAlgebra.algebraMapInv (R := ℂ) (M := Fin n × Fin n → ℂ)).toLinearMap := by
    refine (fockBasis n).ext fun T => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply,
      AlgHom.toLinearMap_apply]
    rw [fockBasis_eq]
    rcases Nat.eq_zero_or_pos T.card with h | h
    · have hT : T = ∅ := Finset.card_eq_zero.mp h
      rw [ιMulti_card_zero _ _ h, map_one, hT, Finsupp.single_eq_same]
    · have hT : T ≠ ∅ := Finset.nonempty_iff_ne_empty.mp (Finset.card_pos.mp h)
      rw [algebraMapInv_ιMulti_pos _ _ h]
      simp [hT]
  exact LinearMap.congr_fun this x

theorem ffMat_empty_row (k : Matrix (Fin n) (Fin n) ℂ) (T : Finset (Fin (n * n))) :
    ffMat ε k ∅ T = if T = ∅ then 1 else 0 := by
  rw [ffMat, LinearMap.toMatrix_apply, AlgHom.toLinearMap_apply, repr_empty, algebraMapInv_ff, ← repr_empty,
    Module.Basis.repr_self, Finsupp.single_apply]

theorem nH_one (k : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.toLin (fockBasis n) (fockBasis n) (ffMat ε k)ᴴ 1 = 1 := by
  have h1 : (1 : Fock n) = fockBasis n ∅ := by
    rw [fockBasis_eq, ιMulti_card_zero _ _ Finset.card_empty]
  rw [h1, Matrix.toLin_self, Finset.sum_eq_single ∅]
  · simp [conjTranspose_apply, ffMat_empty_row]
  · intro T _ hT
    simp [conjTranspose_apply, ffMat_empty_row, hT]
  · simp

theorem nH_mul {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (x : Fock n) :
    ∀ y : Fock n, Matrix.toLin (fockBasis n) (fockBasis n) (ffMat ε k)ᴴ (x * y) =
      ff ε kᴴ x * Matrix.toLin (fockBasis n) (fockBasis n) (ffMat ε k)ᴴ y := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    intro y
    simp [Algebra.algebraMap_eq_smul_one]
  | add x x' hx hx' =>
    intro y
    rw [add_mul, map_add (f := _), hx, hx', map_add (f := _), add_mul]
  | ι_mul x m hx =>
    intro y
    have h := nH_cpV hk m (x * y)
    simp only [cpV, LinearMap.mulLeft_apply] at h
    rw [mul_assoc, h, hx, map_mul, ff, ExteriorAlgebra.map_apply_ι, mul_assoc]

theorem nH_eq {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    Matrix.toLin (fockBasis n) (fockBasis n) (ffMat ε k)ᴴ = (ff ε kᴴ).toLinearMap := by
  refine LinearMap.ext fun x => ?_
  have h := nH_mul hk x 1
  rw [mul_one, nH_one, mul_one] at h
  exact h

theorem ffMat_unitary {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    ffMat ε k ∈ Matrix.unitaryGroup (Finset (Fin (n * n))) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]
  have h1 : (ffMat ε k)ᴴ = LinearMap.toMatrix (fockBasis n) (fockBasis n) (ff ε kᴴ).toLinearMap := by
    rw [← nH_eq hk, LinearMap.toMatrix_toLin]
  have hkk : kᴴ * k = 1 := by
    have := hk.1
    rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose] at this
    exact this
  have h2 : (ff ε kᴴ).toLinearMap * (ff ε k).toLinearMap = 1 := by
    refine LinearMap.ext fun x => ?_
    rw [Module.End.mul_apply, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, ← AlgHom.comp_apply,
      ← ff_mul (kset_conjTranspose hk) hk, hkk, ff_one]
    rfl
  rw [h1, ffMat, ← LinearMap.toMatrix_mul, h2, LinearMap.toMatrix_one]

end ReciprocityTheory.ChartRestriction.DS.TRGap
