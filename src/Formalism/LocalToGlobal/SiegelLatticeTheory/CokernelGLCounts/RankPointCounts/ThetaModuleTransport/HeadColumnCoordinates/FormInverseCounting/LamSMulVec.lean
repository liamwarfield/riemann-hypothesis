module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.AlgInj

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.DetSmulMk
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.MemHeadColsIff
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.FormCOfRel
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.SumGramInr
noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (cj : E →+* E) {r : ℕ}

theorem sum_gram_inl (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) (c : Ix r → E)
    (j : Fin (r + 1)) :
    ∑ i, c i * gramC cj Z T T' i (Sum.inl j) =
      (∑ b, Z j b * c (Sum.inr b)) - (if j = Fin.last r then T * c (Sum.inl (Fin.last r)) else 0) := by
  rw [Fintype.sum_sum_type]
  simp only [gramC, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.of_apply,
    Matrix.transpose_apply]
  by_cases hj : j = Fin.last r
  · subst hj
    simp only [and_true, if_true, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ]
    rw [mul_comm (c _) (-T), neg_mul, Finset.sum_congr rfl (fun b _ => mul_comm (c (Sum.inr b)) _)]
    ring
  · simp only [hj, and_false, if_false, mul_zero, Finset.sum_const_zero, zero_add, sub_zero]
    exact Finset.sum_congr rfl (fun b _ => mul_comm _ _)

theorem sum_gram_inr (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) (c : Ix r → E)
    (j : Fin (r + 1)) :
    ∑ i, c i * gramC cj Z T T' i (Sum.inr j) =
      (∑ a, cj (Z a j) * c (Sum.inl a)) - (if j = Fin.last r then T' * c (Sum.inr (Fin.last r)) else 0) := by
  rw [Fintype.sum_sum_type]
  simp only [gramC, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
  by_cases hj : j = Fin.last r
  · subst hj
    simp only [and_true, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [mul_comm (c _) (-T'), neg_mul, Finset.sum_congr rfl (fun a _ => mul_comm (c (Sum.inl a)) _)]
    ring
  · simp only [hj, and_false, if_false, mul_zero, Finset.sum_const_zero, add_zero, sub_zero]
    exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
end
end

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

theorem formC_of_rel (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E)
    (hG : IsUnit (gramC cj Z T T').det) (Y W : Ix r → O) (c : Ix r → E)
    (hY : ∀ j, (Y j : E) = ∑ i, c i * gramC cj Z T T' i j) :
    formC O cj Z T T' Y W = ∑ j, c j * cj (W j) := by
  have hc : Matrix.vecMul (fun j => (Y j : E)) (gramC cj Z T T')⁻¹ = c := by
    have hYv : (fun j => (Y j : E)) = Matrix.vecMul c (gramC cj Z T T') := by
      funext j
      rw [hY j]
      rfl
    rw [hYv, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hG, Matrix.vecMul_one]
  unfold formC
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_mul, ← congrFun hc j]
  rfl

def cvec (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) (Y : Ix r → O) : Ix r → E :=
  Sum.elim
    (fun a => (∑ j, cj (Z⁻¹ j a) * (Y (Sum.inr j) : E)) +
      T' * lamC Z (fun j => (Y (Sum.inl j) : E)) * cj (Z⁻¹ (Fin.last r) a))
    (fun b => (Z⁻¹.mulVec (fun j => (Y (Sum.inl j) : E))) b +
      T * lamStarC cj Z (fun j => (Y (Sum.inr j) : E)) * Z⁻¹ b (Fin.last r))

theorem cvec_gram (hcj : ∀ x, cj (cj x) = x) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hu : IsUnit Z.det) (hκ : Z⁻¹ (Fin.last r) (Fin.last r) = 0) (T T' : E) (Y : Ix r → O) :
    ∀ j, (Y j : E) = ∑ i, cvec O cj Z T T' Y i * gramC cj Z T T' i j := by
  have hZ : Z * Z⁻¹ = 1 := Matrix.mul_nonsing_inv Z hu
  have hZ' : Z⁻¹ * Z = 1 := Matrix.nonsing_inv_mul Z hu
  have cl : cvec O cj Z T T' Y (Sum.inl (Fin.last r)) =
      lamStarC cj Z (fun j => (Y (Sum.inr j) : E)) := by
    simp only [cvec, Sum.elim_inl, hκ, map_zero, mul_zero, add_zero, lamStarC]
  have cr : cvec O cj Z T T' Y (Sum.inr (Fin.last r)) = lamC Z (fun j => (Y (Sum.inl j) : E)) := by
    simp only [cvec, Sum.elim_inr, hκ, mul_zero, add_zero, lamC]
  intro j
  rcases j with j | j
  · rw [sum_gram_inl, cl]
    have a1 : ∑ b, Z j b * Z⁻¹.mulVec (fun k => (Y (Sum.inl k) : E)) b = (Y (Sum.inl j) : E) := by
      have := congrFun (show Z.mulVec (Z⁻¹.mulVec (fun k => (Y (Sum.inl k) : E))) =
        (fun k => (Y (Sum.inl k) : E)) by rw [Matrix.mulVec_mulVec, hZ, Matrix.one_mulVec]) j
      simpa only [Matrix.mulVec, dotProduct] using this
    have a2 : ∑ b, Z j b * Z⁻¹ b (Fin.last r) = if j = Fin.last r then 1 else 0 := by
      have := congrFun (congrFun hZ j) (Fin.last r)
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      exact this
    have e1 : ∑ b, Z j b * cvec O cj Z T T' Y (Sum.inr b) =
        (Y (Sum.inl j) : E) + T * lamStarC cj Z (fun k => (Y (Sum.inr k) : E)) *
          (if j = Fin.last r then 1 else 0) := by
      simp only [cvec, Sum.elim_inr]
      rw [← a1, ← a2, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun b _ => by ring)
    rw [e1]
    split_ifs <;> ring
  · rw [sum_gram_inr, cr]
    have a1 : ∀ k, ∑ a, cj (Z a j) * cj (Z⁻¹ k a) = if k = j then 1 else 0 := by
      intro k
      have := congrFun (congrFun hZ' k) j
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_one cj, ← map_zero cj, ← apply_ite cj, ← this, map_sum]
      exact Finset.sum_congr rfl (fun a _ => by rw [map_mul, mul_comm])
    have e1 : ∑ a, cj (Z a j) * cvec O cj Z T T' Y (Sum.inl a) =
        (Y (Sum.inr j) : E) + T' * lamC Z (fun k => (Y (Sum.inl k) : E)) *
          (if Fin.last r = j then 1 else 0) := by
      simp only [cvec, Sum.elim_inl]
      rw [← a1 (Fin.last r)]
      have a3 : ∑ a, cj (Z a j) * ∑ k, cj (Z⁻¹ k a) * (Y (Sum.inr k) : E) = (Y (Sum.inr j) : E) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        have : ∀ k, ∑ a, cj (Z a j) * (cj (Z⁻¹ k a) * (Y (Sum.inr k) : E)) =
            (if k = j then 1 else 0) * (Y (Sum.inr k) : E) := by
          intro k
          rw [← a1 k, Finset.sum_mul]
          exact Finset.sum_congr rfl (fun a _ => by ring)
        simp_rw [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [← a3, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    rw [e1]
    by_cases hj : j = Fin.last r
    · subst hj; simp only [if_true]; ring
    · rw [if_neg hj, if_neg (Ne.symm hj)]; ring

theorem formC_eq (hcj : ∀ x, cj (cj x) = x) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
    (hu : IsUnit (Z.map O.subtype).det) (hκ : (Z.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0)
    (T T' : E) (hG : IsUnit (gramC cj (Z.map O.subtype) T T').det) (Y W : Ix r → O) :
    formC O cj (Z.map O.subtype) T T' Y W =
      bRaw O cj Z (fun j => Y (Sum.inl j)) (fun j => W (Sum.inr j)) +
      cj (bRaw O cj Z (fun j => W (Sum.inl j)) (fun j => Y (Sum.inr j))) +
      T' * lamC (Z.map O.subtype) (fun j => (Y (Sum.inl j) : E)) *
        cj (lamC (Z.map O.subtype) (fun j => (W (Sum.inl j) : E))) +
      T * lamStarC cj (Z.map O.subtype) (fun j => (Y (Sum.inr j) : E)) *
        cj (lamStarC cj (Z.map O.subtype) (fun j => (W (Sum.inr j) : E))) := by
  rw [formC_of_rel O cj _ T T' hG Y W _ (cvec_gram O cj hcj _ hu hκ T T' Y), Fintype.sum_sum_type]
  simp only [cvec, Sum.elim_inl, Sum.elim_inr, add_mul, Finset.sum_add_distrib]
  have s1 : ∑ a, (∑ k, cj ((Z.map O.subtype)⁻¹ k a) * (Y (Sum.inr k) : E)) * cj (W (Sum.inl a) : E) =
      cj (bRaw O cj Z (fun j => W (Sum.inl j)) (fun j => Y (Sum.inr j))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [bRaw, map_sum, map_mul, hcj, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun a _ => by ring))
  have s3 : ∑ b, (Z.map O.subtype)⁻¹.mulVec (fun j => (Y (Sum.inl j) : E)) b * cj (W (Sum.inr b) : E) =
      bRaw O cj Z (fun j => Y (Sum.inl j)) (fun j => W (Sum.inr j)) := by
    simp only [bRaw]
    exact Finset.sum_congr rfl (fun b _ => mul_comm _ _)
  have s2 : ∑ a, T' * lamC (Z.map O.subtype) (fun j => (Y (Sum.inl j) : E)) *
        cj ((Z.map O.subtype)⁻¹ (Fin.last r) a) * cj (W (Sum.inl a) : E) =
      T' * lamC (Z.map O.subtype) (fun j => (Y (Sum.inl j) : E)) *
        cj (lamC (Z.map O.subtype) (fun j => (W (Sum.inl j) : E))) := by
    have e : cj (lamC (Z.map O.subtype) (fun j => (W (Sum.inl j) : E))) =
        ∑ a, cj ((Z.map O.subtype)⁻¹ (Fin.last r) a) * cj (W (Sum.inl a) : E) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [lamC, Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [e, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a _ => by ring)
  have s4 : ∑ b, T * lamStarC cj (Z.map O.subtype) (fun j => (Y (Sum.inr j) : E)) *
        (Z.map O.subtype)⁻¹ b (Fin.last r) * cj (W (Sum.inr b) : E) =
      T * lamStarC cj (Z.map O.subtype) (fun j => (Y (Sum.inr j) : E)) *
        cj (lamStarC cj (Z.map O.subtype) (fun j => (W (Sum.inr j) : E))) := by
    have e : cj (lamStarC cj (Z.map O.subtype) (fun j => (W (Sum.inr j) : E))) =
        ∑ b, (Z.map O.subtype)⁻¹ b (Fin.last r) * cj (W (Sum.inr b) : E) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [lamStarC, map_sum, map_mul, hcj]
    rw [e, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun b _ => by ring)
  linear_combination s1 + s2 + s3 + s4

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
end
end

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

theorem mem_relC_iff (hO : ∀ x ∈ O, cj x ∈ O) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (t t' : O)
    (Y : Ix r → O) :
    Y ∈ relC O cj (Z.map O.subtype) t t' ↔ ∃ c₁ c₂ : Fin (r + 1) → O,
      (fun j => Y (Sum.inl j)) = Z.mulVec c₂ - (t * c₁ (Fin.last r)) • Pi.single (Fin.last r) 1 ∧
      (fun j => Y (Sum.inr j)) =
        (cjT O cj hO Z).mulVec c₁ - (t' * c₂ (Fin.last r)) • Pi.single (Fin.last r) 1 := by
  have kl : ∀ (c : Ix r → E) (j : Fin (r + 1)), ∑ i, c i * gramC cj (Z.map O.subtype) t t' i (Sum.inl j) =
      (∑ b, (Z j b : E) * c (Sum.inr b)) - (if j = Fin.last r then (t : E) * c (Sum.inl (Fin.last r)) else 0) :=
    fun c j => sum_gram_inl cj _ _ _ c j
  have kr : ∀ (c : Ix r → E) (j : Fin (r + 1)), ∑ i, c i * gramC cj (Z.map O.subtype) t t' i (Sum.inr j) =
      (∑ a, cj (Z a j : E) * c (Sum.inl a)) -
        (if j = Fin.last r then (t' : E) * c (Sum.inr (Fin.last r)) else 0) :=
    fun c j => sum_gram_inr cj _ _ _ c j
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun a => c (Sum.inl a), fun b => c (Sum.inr b), ?_, ?_⟩
    · funext j
      apply Subtype.ext
      rw [hc (Sum.inl j), kl (fun i => (c i : E)) j]
      by_cases hj : j = Fin.last r
      · subst hj; simp [Matrix.mulVec, dotProduct]
      · simp [hj, Matrix.mulVec, dotProduct]
    · funext j
      apply Subtype.ext
      rw [hc (Sum.inr j), kr (fun i => (c i : E)) j]
      by_cases hj : j = Fin.last r
      · subst hj; simp [Matrix.mulVec, dotProduct, cjT]
      · simp [hj, Matrix.mulVec, dotProduct, cjT]
  · rintro ⟨c₁, c₂, h₁, h₂⟩
    refine ⟨Sum.elim c₁ c₂, ?_⟩
    rintro (j | j)
    · rw [kl, show (Y (Sum.inl j) : E) = ((fun j => Y (Sum.inl j)) j : E) from rfl, h₁]
      by_cases hj : j = Fin.last r
      · subst hj; simp [Matrix.mulVec, dotProduct]
      · simp [hj, Matrix.mulVec, dotProduct]
    · rw [kr, show (Y (Sum.inr j) : E) = ((fun j => Y (Sum.inr j)) j : E) from rfl, h₂]
      by_cases hj : j = Fin.last r
      · subst hj; simp [Matrix.mulVec, dotProduct, cjT]
      · simp [hj, Matrix.mulVec, dotProduct, cjT]

theorem mem_headCols_iff {R : Type} [CommRing R] (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
    (k : Fin (r + 1) → R) :
    k ∈ headCols Z ↔ ∃ w : Fin (r + 1) → R, w (Fin.last r) = 0 ∧ k = Z.mulVec w := by
  unfold headCols
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨Fin.snoc c 0, by simp, ?_⟩
    ext i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, mul_comm]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨fun a => w a.castSucc, ?_⟩
    ext i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hw, mul_comm]

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
end
end

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

def lamL (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) : (Fin (r + 1) → O) →ₗ[O] E where
  toFun y := lamC (Z.map O.subtype) (fun j => (y j : E))
  map_add' a b := by simp [lamC, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    simp [lamC, Matrix.mulVec, dotProduct, Finset.mul_sum, Subring.smul_def, mul_left_comm]

theorem lamL_apply (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (y : Fin (r + 1) → O) :
    lamL O Z y = lamC (Z.map O.subtype) (fun j => (y j : E)) := rfl

theorem lamL_mulVec (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hu : IsUnit (Z.map O.subtype).det)
    (w : Fin (r + 1) → O) : lamL O Z (Z.mulVec w) = (w (Fin.last r) : E) := by
  rw [lamL_apply, lamC]
  have hv : (fun j => ((Z.mulVec w j : O) : E)) = (Z.map O.subtype).mulVec (fun j => (w j : E)) := by
    funext j
    exact RingHom.map_mulVec O.subtype Z w j
  rw [hv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

theorem lamL_K (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hu : IsUnit (Z.map O.subtype).det)
    (k : Fin (r + 1) → O) (hk : k ∈ headCols Z) : lamL O Z k = 0 := by
  obtain ⟨w, hw, rfl⟩ := (mem_headCols_iff Z k).1 hk
  rw [lamL_mulVec O Z hu, hw]; rfl

theorem bvec_eq (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) :
    (fun i => Z i (Fin.last r)) = Z.mulVec (Pi.single (Fin.last r) 1) := col_eq_mulVec Z _

theorem lamL_b (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hu : IsUnit (Z.map O.subtype).det) :
    lamL O Z (fun i => Z i (Fin.last r)) = 1 := by
  rw [bvec_eq, lamL_mulVec O Z hu]; simp

theorem det_smul_mk' (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (v : Fin (r + 1) → O) :
    Z.det • (Submodule.Quotient.mk v : MbMod Z) =
      (Z.adjugate.mulVec v) (Fin.last r) • bCls Z := by
  rw [← Submodule.Quotient.mk_smul, bCls, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
  set u := Z.adjugate.mulVec v
  have hdv : Z.det • v = Z.mulVec u := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hdv, bvec_eq, ← Matrix.mulVec_smul, ← Matrix.mulVec_sub]
  exact (mem_headCols_iff Z _).mpr ⟨_, by simp, rfl⟩

theorem det_coe (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) : ((Z.det : O) : E) = (Z.map O.subtype).det := by
  exact RingHom.map_det O.subtype Z

theorem det_mul_lamL (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hu : IsUnit (Z.map O.subtype).det)
    (v : Fin (r + 1) → O) :
    (Z.det : E) * lamL O Z v = ((Z.adjugate.mulVec v) (Fin.last r) : E) := by
  rw [det_coe, lamL_apply, lamC, Matrix.inv_def, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul,
    ← mul_assoc, Ring.mul_inverse_cancel _ hu, one_mul]
  have h1 := RingHom.map_mulVec O.subtype Z.adjugate v (Fin.last r)
  have h2 := RingHom.map_adjugate O.subtype Z
  simp only [RingHom.mapMatrix_apply] at h2
  rw [← h2] at *
  exact h1.symm

theorem lam_keep {Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O} (hu₁ : IsUnit (Z₁.map O.subtype).det)
    (hu₂ : IsUnit (Z₂.map O.subtype).det) (γ : MbMod Z₁ →ₗ[O] MbMod Z₂) (hb : γ (bCls Z₁) = bCls Z₂)
    (y₁ y₂ : Fin (r + 1) → O)
    (h : γ (Submodule.Quotient.mk y₁) = Submodule.Quotient.mk y₂) : lamL O Z₂ y₂ = lamL O Z₁ y₁ := by
  let Λ := (headCols Z₂).liftQ (lamL O Z₂) (fun k hk => LinearMap.mem_ker.mpr (lamL_K O Z₂ hu₂ k hk))
  have hΛb : Λ (bCls Z₂) = 1 := lamL_b O Z₂ hu₂
  have hΛy : Λ (Submodule.Quotient.mk y₂) = lamL O Z₂ y₂ := rfl
  have key := congrArg (fun q => Λ (γ q)) (det_smul_mk' O Z₁ y₁)
  simp only [map_smul, hb, h, hΛb, hΛy] at key
  have hdet : IsUnit ((Z₁.det : O) : E) := by rw [det_coe]; exact hu₁
  apply hdet.mul_left_cancel
  rw [det_mul_lamL O Z₁ hu₁ y₁]
  rw [Subring.smul_def, Subring.smul_def, smul_eq_mul, smul_eq_mul, mul_one] at key
  exact key

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
end
end

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

theorem bRaw_e (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (y : Fin (r + 1) → O) :
    bRaw O cj Z y (Pi.single (Fin.last r) 1) = lamL O Z y := by
  unfold bRaw
  rw [Finset.sum_eq_single (Fin.last r)]
  · simp [lamL, lamC]
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · simp

theorem bRaw_b_mem (hcj : ∀ x, cj (cj x) = x) (hO : ∀ x ∈ O, cj x ∈ O)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hu : IsUnit (Z.map O.subtype).det)
    (y : Fin (r + 1) → O) : bRaw O cj Z y (fun i => cjT O cj hO Z i (Fin.last r)) ∈ O := by
  unfold bRaw
  have hinv : (Z.map O.subtype) * (Z.map O.subtype)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have e : ∀ j, cj ((cjT O cj hO Z j (Fin.last r) : O) : E) = (Z.map O.subtype) (Fin.last r) j := fun j => hcj _
  simp only [e]
  rw [show ∑ j, (Z.map O.subtype) (Fin.last r) j * ((Z.map O.subtype)⁻¹.mulVec (fun i => (y i : E))) j =
      ((Z.map O.subtype).mulVec ((Z.map O.subtype)⁻¹.mulVec (fun i => (y i : E)))) (Fin.last r) from rfl,
    Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  exact (y _).2

theorem lamS_mulVec (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hO : ∀ x ∈ O, cj x ∈ O)
    (hu : IsUnit (Z.map O.subtype).det) (w : Fin (r + 1) → O) :
    lamS O cj Z ((cjT O cj hO Z).mulVec w) = (w (Fin.last r) : E) := by
  unfold lamS lamStarC
  have hinv : (Z.map O.subtype) * (Z.map O.subtype)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hcoe : ∀ b, (((cjT O cj hO Z).mulVec w b : O) : E) = ∑ c, cj ((Z c b : O) : E) * (w c : E) := by
    intro b
    simp [Matrix.mulVec, dotProduct, cjT]
  simp only [hcoe, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hrow : ∀ c, ∑ b, cj ((Z.map O.subtype)⁻¹ b (Fin.last r)) * (cj ((Z c b : O) : E) * (w c : E)) =
      cj (if c = Fin.last r then 1 else 0) * (w c : E) := by
    intro c
    have h1 := congrFun (congrFun hinv c) (Fin.last r)
    rw [Matrix.mul_apply, Matrix.one_apply] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h1, map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    rw [map_mul]
    simp only [Matrix.map_apply, Subring.coe_subtype]
    ring
  rw [Finset.sum_congr rfl (fun c _ => hrow c)]
  simp [apply_ite cj]

theorem lamS_K (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hO : ∀ x ∈ O, cj x ∈ O)
    (hu : IsUnit (Z.map O.subtype).det) (k : Fin (r + 1) → O)
    (hk : k ∈ headCols (cjT O cj hO Z)) : lamS O cj Z k = 0 := by
  unfold headCols at hk
  have hinv : (Z.map O.subtype) * (Z.map O.subtype)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  induction hk using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    unfold lamS lamStarC
    have h1 := congrFun (congrFun hinv a.castSucc) (Fin.last r)
    rw [Matrix.mul_apply, Matrix.one_apply_ne (Fin.castSucc_lt_last a).ne] at h1
    have key : ∑ b, cj ((Z.map O.subtype)⁻¹ b (Fin.last r)) * ((cjT O cj hO Z b a.castSucc : O) : E) =
        cj (∑ b, (Z.map O.subtype) a.castSucc b * (Z.map O.subtype)⁻¹ b (Fin.last r)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [map_mul, mul_comm]
      rfl
    rw [key, h1, map_zero]
  | zero =>
    unfold lamS lamStarC
    simp
  | add x y _ _ hx hy =>
    unfold lamS lamStarC at hx hy ⊢
    simp only [Pi.add_apply, Subring.coe_add, mul_add, Finset.sum_add_distrib, hx, hy, add_zero]
  | smul c x _ hx =>
    unfold lamS lamStarC at hx ⊢
    calc ∑ b, cj ((Z.map O.subtype)⁻¹ b (Fin.last r)) * (((c • x) b : O) : E) =
          (c : E) * ∑ b, cj ((Z.map O.subtype)⁻¹ b (Fin.last r)) * ((x b : O) : E) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          simp only [Pi.smul_apply, smul_eq_mul, Subring.coe_mul]
          ring
      _ = 0 := by rw [hx, mul_zero]

theorem lamS_b (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hO : ∀ x ∈ O, cj x ∈ O)
    (hu : IsUnit (Z.map O.subtype).det) :
    lamS O cj Z (fun i => cjT O cj hO Z i (Fin.last r)) = 1 := by
  unfold lamS lamStarC
  have hinv : (Z.map O.subtype) * (Z.map O.subtype)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have h1 := congrFun (congrFun hinv (Fin.last r)) (Fin.last r)
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
  have key : ∑ b, cj ((Z.map O.subtype)⁻¹ b (Fin.last r)) * ((cjT O cj hO Z b (Fin.last r) : O) : E) =
      cj (∑ b, (Z.map O.subtype) (Fin.last r) b * (Z.map O.subtype)⁻¹ b (Fin.last r)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [map_mul, mul_comm]
    rfl
  rw [key, h1, map_one]

theorem lamS_e (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
    (hκ : (Z.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0) :
    lamS O cj Z (Pi.single (Fin.last r) 1) = 0 := by
  unfold lamS lamStarC
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [hκ, map_zero, zero_mul]
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · simp

variable (hcj : ∀ x, cj (cj x) = x) (hO : ∀ x ∈ O, cj x ∈ O)
variable {Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O}
include hcj

theorem pair_e (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hκ₁ : (Z₁.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0)
    (hκ₂ : (Z₂.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0)
    (p : PairSet O cj hO Z₁ Z₂) : p.1.2 (eCl (cjT O cj hO Z₁)) = eCl (cjT O cj hO Z₂) := by
  obtain ⟨y₂', hy⟩ := Submodule.Quotient.mk_surjective _ (p.1.2 (eCl (cjT O cj hO Z₁)))
  rw [← hy, eCl, ← sub_eq_zero, ← Submodule.Quotient.mk_sub]
  apply mk_eq_zero_of O cj hcj hO Z₂ hu₂
  · intro y
    obtain ⟨y₁, hy₁⟩ := Submodule.Quotient.mk_surjective _ (p.1.1.symm (Submodule.Quotient.mk y))
    have e1 : p.1.1 (Submodule.Quotient.mk y₁) = Submodule.Quotient.mk y := by
      rw [hy₁]; exact p.1.1.apply_symm_apply _
    have A := p.2.2.2 y₁ (Pi.single (Fin.last r) 1) y y₂' e1 hy.symm
    rw [bRaw_e O cj Z₁, ← lam_keep O hu₁ hu₂ p.1.1.toLinearMap p.2.1.1 y₁ y e1] at A
    rw [bRaw_sub_right, bRaw_e]
    exact A
  · rw [lamS_sub, p.2.2.1 _ y₂' hy.symm, lamS_e O cj Z₁ hκ₁, lamS_e O cj Z₂ hκ₂, sub_zero]

theorem pair_b (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (p : PairSet O cj hO Z₁ Z₂) : p.1.2 (bCls (cjT O cj hO Z₁)) = bCls (cjT O cj hO Z₂) := by
  obtain ⟨y₂', hy⟩ := Submodule.Quotient.mk_surjective _ (p.1.2 (bCls (cjT O cj hO Z₁)))
  rw [← hy, bCls, ← sub_eq_zero, ← Submodule.Quotient.mk_sub]
  apply mk_eq_zero_of O cj hcj hO Z₂ hu₂
  · intro y
    obtain ⟨y₁, hy₁⟩ := Submodule.Quotient.mk_surjective _ (p.1.1.symm (Submodule.Quotient.mk y))
    have e1 : p.1.1 (Submodule.Quotient.mk y₁) = Submodule.Quotient.mk y := by
      rw [hy₁]; exact p.1.1.apply_symm_apply _
    have A := p.2.2.2 y₁ _ y y₂' e1 hy.symm
    rw [bRaw_sub_right]
    have B := O.add_mem A (bRaw_b_mem O cj hcj hO Z₁ hu₁ y₁)
    rw [sub_add_cancel] at B
    exact O.sub_mem B (bRaw_b_mem O cj hcj hO Z₂ hu₂ y)
  · rw [lamS_sub, p.2.2.1 _ y₂' hy.symm, lamS_b O cj Z₁ hO hu₁, lamS_b O cj Z₂ hO hu₂, sub_self]

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
