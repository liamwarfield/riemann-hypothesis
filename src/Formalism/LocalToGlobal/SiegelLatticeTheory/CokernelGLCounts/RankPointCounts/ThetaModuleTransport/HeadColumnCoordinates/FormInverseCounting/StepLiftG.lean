module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.ZzMinusSecondProjTranspose

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.SecondProjDiagonalEmbed
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.GramMapSecondProjTranspose
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.GramUnitG
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.DuIsoB
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.SecondProjIotaOneEqZero
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.DuForm
noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem map_inv_of {K L : Type} [CommRing K] [CommRing L] {n : Type} [Fintype n] [DecidableEq n]
    (f : K →+* L) (A : Matrix n n K) (hA : IsUnit A.det) : (A⁻¹).map f = (A.map f)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul A hA, Matrix.map_one f f.map_zero f.map_one]

theorem splitFirstProj_conj (x : E) : ph1 g (M.L.cj x) = ph2 g x := by
  change (g.e (M.L.cj x)).1 = (g.e x).2
  rw [g.e_cj]
  rfl

theorem splitFirstProj_algebraMap (a : F) : ph1 g (algebraMap F E a) = a := by
  change (g.e (algebraMap F E a)).1 = a
  rw [AlgEquiv.commutes]
  rfl

def gHat (g : SplitG M.L) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) : Matrix (Ix r) (Ix r) F :=
  Matrix.fromBlocks (Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then -T else 0)
    (Zh.map (ph2 g)) (Zh.map (ph1 g)).transpose
    (Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then -T' else 0)

def pM (r : ℕ) (x : F) : Matrix (Ix r) (Ix r) F := Matrix.fromBlocks 1 (-x • 1) 0 (x • 1)

theorem map_gramG (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T')).map
        (ph1 g) = (pM r (g.q : F)⁻¹).transpose * gHat g Zh T T' * pM r (g.q : F)⁻¹ := by
  simp only [gramG, gHat, pM, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.transpose_one, Matrix.transpose_zero, Matrix.transpose_smul,
    Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, Matrix.smul_mul, Matrix.mul_smul,
    add_zero, zero_add]
  congr 1 <;> ext a b <;>
    by_cases h : a = Fin.last r ∧ b = Fin.last r <;>
    simp [cor, h, splitFirstProj_conj, splitFirstProj_algebraMap, map_mul, map_add (f := _), map_neg, map_sub, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply] <;>
    ring

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

def uV (g : SplitG M.L) (l : Fin (r + 1) → M.R) : Ix r → F :=
  Sum.elim (fun a => ph1 g (l a)) (fun a => ph2 g (l a))

def qM (r : ℕ) (x : F) : Matrix (Ix r) (Ix r) F := Matrix.fromBlocks 1 1 0 (x • 1)

theorem pM_mul_qM (x : F) (hx : x ≠ 0) : pM r x⁻¹ * qM r x = 1 := by
  rw [pM, qM, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  congr 1 <;> simp [smul_smul, mul_inv_cancel₀ hx]

theorem firstProj_iotaOne_cases (hs : M.split = some g) (l : Fin (r + 1) → M.R) (i : Ix r) :
    ph1 g (iota1 hs l i : E) = match i with
      | Sum.inl a => ph1 g (l a)
      | Sum.inr a => (ph2 g (l a) - ph1 g (l a)) / (g.q : F) := by
  rcases i with a | a <;> simp [iota1, firstProj_apply, secondProj_apply]

theorem secondProj_iotaOne_eq_zero (hs : M.split = some g) (l : Fin (r + 1) → M.R) (i : Ix r) :
    ph2 g (iota1 hs l i : E) = 0 := by
  rcases i with a | a <;> simp [iota1, secondProj_apply]

theorem vecMul_qM (hs : M.split = some g) (l : Fin (r + 1) → M.R) :
    Matrix.vecMul (fun i => ph1 g (iota1 hs l i : E)) (qM r (g.q : F)) = uV g l := by
  have hq := q_ne g
  funext k
  rcases k with a | a
  · simp [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, qM, firstProj_iotaOne_cases, uV, Matrix.one_apply]
  · simp [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, qM, firstProj_iotaOne_cases, uV, Matrix.one_apply]
    field_simp
    ring

theorem splitForm_iota_secondProj (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (l w : Fin (r + 1) → M.R) :
    ph2 g (formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
      (algebraMap F E T') (iota1 hs l) (iota2 hs w)) = 0 := by
  unfold formG
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_mul, secondProj_iotaOne_eq_zero]

theorem splitForm_iota_firstProj (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (hG : IsUnit (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
      (algebraMap F E T')).det)
    (l w : Fin (r + 1) → M.R) :
    ph1 g (formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
      (algebraMap F E T') (iota1 hs l) (iota2 hs w)) =
      dotProduct (uV g l) (Matrix.mulVec (gHat g Zh T T')⁻¹ (uV g w)) := by
  set G := gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T')
  have hq := q_ne g
  have hcw : ∀ j, ph1 g ((M.L.cj : E →+* E) (iota2 hs w j : E)) = ph1 g (iota1 hs w j : E) := by
    intro j
    show ph1 g (M.L.cj (M.L.cj (iota1 hs w j : E))) = _
    rw [M.L.cj_cj]
  have h1 : ph1 g (formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
      (algebraMap F E T') (iota1 hs l) (iota2 hs w)) =
      dotProduct (fun i => ph1 g (iota1 hs l i : E)) (Matrix.mulVec (G.map (ph1 g))⁻¹ fun j => ph1 g (iota1 hs w j : E)) := by
    rw [← map_inv_of (ph1 g) G hG]
    unfold formG
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, hcw, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hP : (pM r (g.q : F)⁻¹)⁻¹ = qM r (g.q : F) := Matrix.inv_eq_right_inv (pM_mul_qM _ hq)
  have hPt : ((pM r (g.q : F)⁻¹).transpose)⁻¹ = (qM r (g.q : F)).transpose := by
    rw [← Matrix.transpose_nonsing_inv, hP]
  rw [h1, map_gramG, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hP, hPt, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, vecMul_qM, vecMul_qM]

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem isoB_of (hs : M.split = some g) (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    {Z₁ Z₂ Zσ₁ Zσ₂ : M.Mat (r + 1)} {TT : M.R}
    (hG₁ : IsUnit (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh₁ (algebraMap F E T)
      (algebraMap F E T')).det)
    (hG₂ : IsUnit (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh₂ (algebraMap F E T)
      (algebraMap F E T')).det)
    (θ₁ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (θ₂ : DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT)
    (h : ∀ l l₂ w w₂ : Fin (r + 1) → M.R, θ₁ (mk1 hs Z₁ TT l) = mk1 hs Z₂ TT l₂ →
      θ₂ (mk1 hs Zσ₁ TT w) = mk1 hs Zσ₂ TT w₂ →
      dotProduct (uV g l₂) (Matrix.mulVec (gHat g Zh₂ T T')⁻¹ (uV g w₂)) -
        dotProduct (uV g l) (Matrix.mulVec (gHat g Zh₁ T T')⁻¹ (uV g w)) ∈ 𝒪[F]) :
    IsoB hs Zh₁ Zh₂ T T' θ₁ θ₂ := by
  intro l l₂ w w₂ hl hw
  apply mem_O_of_comp g
  · rw [map_sub, Prod.fst_sub, ← firstProj_apply, ← firstProj_apply, splitForm_iota_firstProj hs Zh₂ T T' hG₂,
      splitForm_iota_firstProj hs Zh₁ T T' hG₁]
    exact h l l₂ w w₂ hl hw
  · rw [map_sub, Prod.snd_sub, ← secondProj_apply, ← secondProj_apply, splitForm_iota_secondProj, splitForm_iota_secondProj, sub_zero]
    exact zero_mem _

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

def GramUnitG : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L) (r : ℕ) (T T' : F) (TT : M.R)
    (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z Zσ : M.Mat (r + 1)),
    GHyp M g T T' TT Zh Z Zσ →
    IsUnit (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
      (algebraMap F E T')).det

def StepDuF : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L) (hs : M.split = some g) (r : ℕ) (T T' : F) (TT : M.R)
    (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ Zσ₁ Zσ₂ : M.Mat (r + 1)),
    GHyp M g T T' TT Zh₁ Z₁ Zσ₁ → GHyp M g T T' TT Zh₂ Z₂ Zσ₂ → KapEq Zh₁ Zh₂ →
    ∀ γ : IsoMbe Z₁.Z Z₂.Z, ∃ γ' : IsoMbe Zσ₁.Z Zσ₂.Z,
      ∀ (θ₁ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (θ₂ : DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT),
        Ind hs γ θ₁ → Ind hs γ' θ₂ →
        ∀ l l₂ w w₂ : Fin (r + 1) → M.R, θ₁ (mk1 hs Z₁ TT l) = mk1 hs Z₂ TT l₂ →
          θ₂ (mk1 hs Zσ₁ TT w) = mk1 hs Zσ₂ TT w₂ →
          dotProduct (uV g l₂) (Matrix.mulVec (gHat g Zh₂ T T')⁻¹ (uV g w₂)) -
            dotProduct (uV g l) (Matrix.mulVec (gHat g Zh₁ T T')⁻¹ (uV g w)) ∈ 𝒪[F]

theorem stepDu_of (hU : GramUnitG) (h : StepDuF) : StepDu := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' TT Zh₁ Zh₂ Z₁ Z₂ Zσ₁ Zσ₂ h₁ h₂ hk γ
  obtain ⟨γ', hγ'⟩ := h F E M g hs r T T' TT Zh₁ Zh₂ Z₁ Z₂ Zσ₁ Zσ₂ h₁ h₂ hk γ
  exact ⟨γ', fun θ₁ θ₂ i₁ i₂ => isoB_of hs Zh₁ Zh₂ T T'
    (hU F E M g r T T' TT Zh₁ Z₁ Zσ₁ h₁) (hU F E M g r T T' TT Zh₂ Z₂ Zσ₂ h₂) θ₁ θ₂ (hγ' θ₁ θ₂ i₁ i₂)⟩

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

theorem corner_mul {K : Type} [Field K] {r : ℕ} (a d : K) (X : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    (Matrix.of fun i j : Fin (r + 1) => if i = Fin.last r ∧ j = Fin.last r then d else 0) * X *
      (Matrix.of fun i j : Fin (r + 1) => if i = Fin.last r ∧ j = Fin.last r then a else 0) =
      Matrix.of fun i j => cor r i j (d * X (Fin.last r) (Fin.last r) * a) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, cor]
  by_cases hi : i = Fin.last r <;> by_cases hj : j = Fin.last r <;>
    simp [hi, hj, Finset.sum_ite_eq', Finset.sum_ite_eq, mul_assoc]

theorem det_corner_blocks_ne {K : Type} [Field K] {r : ℕ} (a d : K) (B C : Matrix (Fin (r + 1)) (Fin (r + 1)) K)
    (hB : B.det ≠ 0)
    (h : B.det * C.det - a * d * ((B.submatrix Fin.castSucc Fin.castSucc).det *
      (C.submatrix Fin.castSucc Fin.castSucc).det) ≠ 0) :
    (Matrix.fromBlocks (Matrix.of fun i j : Fin (r + 1) => if i = Fin.last r ∧ j = Fin.last r then a else 0) B C
      (Matrix.of fun i j : Fin (r + 1) => if i = Fin.last r ∧ j = Fin.last r then d else 0)).det ≠ 0 := by
  set A : Matrix (Fin (r + 1)) (Fin (r + 1)) K := Matrix.of fun i j => if i = Fin.last r ∧ j = Fin.last r then a else 0
  set D : Matrix (Fin (r + 1)) (Fin (r + 1)) K := Matrix.of fun i j => if i = Fin.last r ∧ j = Fin.last r then d else 0
  set J : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) K := Matrix.fromBlocks 0 1 1 0
  have hJ : Matrix.fromBlocks B A D C * J = Matrix.fromBlocks A B C D := by
    simp [J, Matrix.fromBlocks_multiply]
  have hJJ : J * J = 1 := by
    simp [J, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have hJd : J.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hJJ
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  rw [← hJ, Matrix.det_mul]
  refine mul_ne_zero ?_ hJd
  haveI : Invertible B := Matrix.invertibleOfIsUnitDet B (isUnit_iff_ne_zero.mpr hB)
  rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv, corner_mul]
  have hsub : C - (Matrix.of fun i j => cor r i j (d * B⁻¹ (Fin.last r) (Fin.last r) * a)) =
      C + Matrix.of fun i j => cor r i j (-(d * B⁻¹ (Fin.last r) (Fin.last r) * a)) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.of_apply, cor]
    split_ifs <;> ring
  have hinv : B⁻¹ (Fin.last r) (Fin.last r) = (B.submatrix Fin.castSucc Fin.castSucc).det / B.det := by
    rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last,
      Ring.inverse_eq_inv', smul_eq_mul]
    have h2 : ((-1 : K) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) = 1 := by
      rw [Fin.val_last]; exact Even.neg_one_pow ⟨r, rfl⟩
    rw [h2, one_mul, div_eq_inv_mul]
  rw [hsub, det_add_cor, hinv]
  intro h0
  apply h
  have : B.det * (C.det + -(d * ((B.submatrix Fin.castSucc Fin.castSucc).det / B.det) * a) *
      (C.submatrix Fin.castSucc Fin.castSucc).det) = B.det * C.det - a * d * ((B.submatrix Fin.castSucc Fin.castSucc).det *
      (C.submatrix Fin.castSucc Fin.castSucc).det) := by
    field_simp
    ring
  rw [← this, h0]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem splitSecondProj_algebraMap (a : F) : ph2 g (algebraMap F E a) = a := by
  show (g.e (algebraMap F E a)).2 = a
  rw [AlgEquiv.commutes]
  rfl

theorem ph2_cj_eq_ph1 (x : E) : ph2 g (M.L.cj x) = ph1 g x := by
  show (g.e (M.L.cj x)).2 = (g.e x).1
  rw [g.e_cj]
  rfl

theorem gram_map_secondProj_transpose (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T')).map
        (ph2 g) =
      ((gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
        (algebraMap F E T')).map (ph1 g)).transpose := by
  have hcor : ∀ (φ : E →+* F) (a b : Fin (r + 1)) (c : E), φ (cor r a b c) = cor r a b (φ c) := by
    intro φ a b c
    unfold cor
    split_ifs <;> simp
  have hcorS : ∀ (a b : Fin (r + 1)) (c : F), cor r a b c = cor r b a c := by
    intro a b c
    unfold cor
    simp only [and_comm]
  have h1 : ∀ x, ph1 g (M.L.cj x) = ph2 g x := by
    intro x
    show (g.e (M.L.cj x)).1 = (g.e x).2
    rw [g.e_cj]
    rfl
  have ha1 : ∀ a : F, ph1 g (algebraMap F E a) = a := by
    intro a
    show (g.e (algebraMap F E a)).1 = a
    rw [AlgEquiv.commutes]
    rfl
  unfold gramG
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]
  congr 1
  · ext a b
    simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply, hcor, map_neg, splitSecondProj_algebraMap, ha1]
    exact hcorS _ _ _
  all_goals
    ext a b
    simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply, hcor, map_mul, map_add (f := _), map_neg,
      map_sub, RingHom.coe_coe, splitSecondProj_algebraMap, ph2_cj_eq_ph1, h1, ha1]
    first | ring1 | (rw [hcorS]; done) | (rw [hcorS]; ring1)

theorem det_pM_ne (x : F) (hx : x ≠ 0) : (pM r x⁻¹).det ≠ 0 := by
  unfold pM
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_smul, Matrix.det_one, mul_one]
  exact pow_ne_zero _ (inv_ne_zero hx)

theorem gramUnit_split_holds : GramUnitG := by
  intro F _ _ _ E _ _ _ _ M g r T T' TT Zh Z Zσ h
  obtain ⟨-, -, -, -, -, hdet, hx⟩ := h
  have hq := q_ne g
  have h1 : ph1 g (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
      (algebraMap F E T')).det ≠ 0 := by
    rw [det_ph, map_gramG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    refine mul_ne_zero (mul_ne_zero (det_pM_ne _ hq) ?_) (det_pM_ne _ hq)
    unfold gHat
    obtain ⟨-, hd2⟩ := (isUnit_iff_ph (g := g) _).1 hdet
    obtain ⟨hx1, -⟩ := (isUnit_iff_ph (g := g) _).1 hx
    refine det_corner_blocks_ne (-T) (-T') _ _ (by rwa [← det_ph]) ?_
    have hm : ((Zh.map (ph1 g)).transpose.submatrix Fin.castSucc Fin.castSucc).det =
        ph1 g (Zh.submatrix Fin.castSucc Fin.castSucc).det := by
      rw [det_ph]
      exact Matrix.det_transpose _
    rw [hm, Matrix.det_transpose]
    simp only [Matrix.submatrix_map, ← det_ph]
    convert hx1 using 1
    simp only [map_sub, map_mul, splitFirstProj_conj, splitFirstProj_algebraMap]
    ring
  have h2 : ph2 g (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
      (algebraMap F E T')).det ≠ 0 := by
    rw [det_ph, gram_map_secondProj_transpose, Matrix.det_transpose, ← det_ph]
    exact h1
  exact (isUnit_iff_ph (g := g) _).2 ⟨h1, h2⟩

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem zzPlus_firstProj_corner (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) (a b : Fin (r + 1)) :
    ph1 g (HermSp.ZZplusOf M Zh T T' a b) =
      (g.q : F)⁻¹ * ph1 g (Zh a b) + (if a = Fin.last r ∧ b = Fin.last r then T / (g.q : F) else 0) := by
  have h1 : ∀ x : E, ph1 g x = (g.e x).1 := fun x => rfl
  simp only [HermSp.ZZplusOf, hs, Matrix.of_apply]
  split_ifs with hab <;> simp only [h1, map_sub, AlgEquiv.apply_symm_apply, map_zero, Prod.fst_zero, Prod.fst_sub,
    sub_zero, add_zero] <;> ring

theorem zzPlus_secondProj_corner (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) (a b : Fin (r + 1)) :
    ph2 g (HermSp.ZZplusOf M Zh T T' a b) =
      -((g.q : F)⁻¹ * ph2 g (Zh b a)) + (if a = Fin.last r ∧ b = Fin.last r then -(T' / (g.q : F)) else 0) := by
  have h2 : ∀ x : E, ph2 g x = (g.e x).2 := fun x => rfl
  simp only [HermSp.ZZplusOf, hs, Matrix.of_apply]
  split_ifs with hab <;> simp only [h2, map_sub, AlgEquiv.apply_symm_apply, map_zero, Prod.snd_zero, Prod.snd_sub,
    sub_zero, add_zero] <;> ring

def lamV (g : SplitG M.L) (m : Fin (r + 1) → M.R) : Ix r → F :=
  Sum.elim (fun a => -(ph2 g (m a)) / (g.q : F)) (fun a => ph1 g (m a) / (g.q : F))

theorem firstProj_ring_sum (s : Finset (Fin (r + 1))) (f : Fin (r + 1) → M.R) :
    ph1 g ((∑ j ∈ s, f j : M.R) : E) = ∑ j ∈ s, ph1 g (f j : E) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [AddSubmonoidClass.coe_finsetSum, map_sum]

theorem secondProj_ring_sum (s : Finset (Fin (r + 1))) (f : Fin (r + 1) → M.R) :
    ph2 g ((∑ j ∈ s, f j : M.R) : E) = ∑ j ∈ s, ph2 g (f j : E) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [AddSubmonoidClass.coe_finsetSum, map_sum]

theorem firstProj_diagonalEmbed (hs : M.split = some g) (c : 𝒪[F]) : ph1 g ((dgR hs c : M.R) : E) = c := by
  show (g.e (algebraMap F E (c : F))).1 = c
  rw [AlgEquiv.commutes]
  rfl

theorem secondProj_diagonalEmbed (hs : M.split = some g) (c : 𝒪[F]) : ph2 g ((dgR hs c : M.R) : E) = c := by
  show (g.e (algebraMap F E (c : F))).2 = c
  rw [AlgEquiv.commutes]
  rfl

theorem uV_llMap (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (Z : M.Mat (r + 1)) (TT : M.R) (hZ : Z.Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T')
    (hTT : g.e (TT : E) = (T, T')) (m : Fin (r + 1) → M.R) :
    uV g (llMap hs Z TT m) = Matrix.vecMul (lamV g m) (gHat g Zh T T') := by
  have hZe : ∀ i j, ((Z.Z i j : M.R) : E) = HermSp.ZZplusOf M Zh T T' i j := fun i j => by
    rw [← hZ]; rfl
  have hT1 : ph1 g (TT : E) = T := by rw [firstProj_apply, hTT]
  have hT2 : ph2 g (TT : E) = T' := by rw [secondProj_apply, hTT]
  have hq := q_ne g
  obtain ⟨Zf, rfl⟩ : ∃ Zf : Fin (r + 1) → Fin (r + 1) → E, Matrix.of Zf = Zh := ⟨Zh, rfl⟩
  have hsum1 : ∀ i, ∑ x, (g.e (Zf i x)).1 * (g.e (m x : E)).1 * (g.q : F)⁻¹ =
      ∑ x, (g.q : F)⁻¹ * (g.e (m x : E)).1 * (g.e (Zf i x)).1 := fun i => Finset.sum_congr rfl fun x _ => by ring
  have hsum2 : ∀ i, ∑ x, (g.e (Zf x i)).2 * (g.e (m x : E)).2 * (g.q : F)⁻¹ =
      ∑ x, (g.q : F)⁻¹ * (g.e (m x : E)).2 * (g.e (Zf x i)).2 := fun i => Finset.sum_congr rfl fun x _ => by ring
  have hsum3 : ∀ i, ∑ x, (g.e (Zf x i)).2 * (g.e (m x : E)).2 / (g.q : F) =
      ∑ x, (g.e (m x : E)).2 * (g.e (Zf x i)).2 / (g.q : F) := fun i => Finset.sum_congr rfl fun x _ => by ring
  funext k
  rcases k with i | i
  · simp only [uV, Sum.elim_inl, llMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.mulVec, dotProduct, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, map_sub, map_mul, firstProj_ring_sum,
      hZe, zzPlus_firstProj_corner hs, hT1, firstProj_diagonalEmbed, trO_coe, Matrix.vecMul, Fintype.sum_sum_type, lamV, Sum.elim_inr,
      gHat, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.of_apply, Matrix.transpose_apply,
      Matrix.map_apply, eV]
    by_cases hi : i = Fin.last r
    · subst hi
      simp [Pi.single_apply, firstProj_apply, secondProj_apply, Finset.sum_add_distrib, add_mul, Finset.mul_sum, ite_and]
      field_simp
      first
        | done
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; done)
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring)
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring_nf)
    · simp [Pi.single_apply, hi, firstProj_apply, secondProj_apply, Finset.sum_add_distrib, add_mul, Finset.mul_sum, ite_and]
      field_simp
      first
        | done
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; done)
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring)
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring_nf)
  · simp only [uV, Sum.elim_inr, llMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.mulVec, dotProduct, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, map_sub, map_mul, secondProj_ring_sum,
      hZe, zzPlus_secondProj_corner hs, hT2, secondProj_diagonalEmbed, trO_coe, Matrix.vecMul, Fintype.sum_sum_type, lamV, Sum.elim_inl,
      gHat, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, Matrix.transpose_apply,
      Matrix.map_apply, eV]
    by_cases hi : i = Fin.last r
    · subst hi
      simp [Pi.single_apply, firstProj_apply, secondProj_apply, Finset.sum_add_distrib, add_mul, Finset.mul_sum, ite_and]
      field_simp
      first
        | done
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; done)
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring)
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring_nf)
    · simp [Pi.single_apply, hi, firstProj_apply, secondProj_apply, Finset.sum_add_distrib, add_mul, Finset.mul_sum, ite_and]
      field_simp
      first
        | done
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; done)
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring)
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring_nf)

theorem lamV_dot_mem (hs : M.split = some g) (m w : Fin (r + 1) → M.R) :
    dotProduct (lamV g m) (uV g w) ∈ 𝒪[F] := by
  classical
  have hq : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext h)
  unfold dotProduct lamV uV
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [← Finset.sum_add_distrib]
  apply sum_mem
  intro a _
  obtain ⟨hm1, hm2, cm, hcm⟩ := comp_of_mem_R hs (m a).2
  obtain ⟨hw1, hw2, cw, hcw⟩ := comp_of_mem_R hs (w a).2
  have key : -(ph2 g (m a : E)) / (g.q : F) * ph1 g (w a : E) + ph1 g (m a : E) / (g.q : F) * ph2 g (w a : E) =
      (cm : F) * (g.e (w a : E)).2 - (g.e (m a : E)).2 * (cw : F) := by
    show -((g.e (m a : E)).2) / (g.q : F) * (g.e (w a : E)).1 +
      (g.e (m a : E)).1 / (g.q : F) * (g.e (w a : E)).2 = _
    have e1 : (g.e (m a : E)).1 = (g.e (m a : E)).2 + (g.q : F) * cm := by linear_combination hcm
    have e2 : (g.e (w a : E)).1 = (g.e (w a : E)).2 + (g.q : F) * cw := by linear_combination hcw
    rw [e1, e2]
    field_simp
    ring
  rw [key]
  exact sub_mem (mul_mem cm.2 hw2) (mul_mem hm2 cw.2)

theorem dot_inv_vecMul {n : Type} [Fintype n] [DecidableEq n] (G : Matrix n n F) (hG : IsUnit G.det)
    (lam x : n → F) : dotProduct (Matrix.vecMul lam G) (Matrix.mulVec G⁻¹ x) = dotProduct lam x := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hG, Matrix.vecMul_one]

theorem dot_inv_mulVec {n : Type} [Fintype n] [DecidableEq n] (G : Matrix n n F) (hG : IsUnit G.det)
    (mu x : n → F) : dotProduct x (Matrix.mulVec G⁻¹ (Matrix.mulVec G mu)) = dotProduct x mu := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hG, Matrix.one_mulVec]

theorem gHat_cj (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    gHat g (Zh.map M.L.cj) T T' = (gHat g Zh T T').transpose := by
  have hcj1 : ∀ x : E, ph1 g (M.L.cj x) = ph2 g x := fun x => by
    show (g.e (M.L.cj x)).1 = (g.e x).2
    rw [g.e_cj]
    rfl
  have hcj2 : ∀ x : E, ph2 g (M.L.cj x) = ph1 g x := fun x => by
    show (g.e (M.L.cj x)).2 = (g.e x).1
    rw [g.e_cj]
    rfl
  unfold gHat
  rw [Matrix.fromBlocks_transpose, Matrix.transpose_transpose]
  congr 1
  · ext a b
    simp only [Matrix.of_apply, Matrix.transpose_apply]
    exact if_congr and_comm rfl rfl
  · ext a b
    simp only [Matrix.map_apply, hcj2]
  · ext a b
    simp only [Matrix.transpose_apply, Matrix.map_apply, hcj1]
  · ext a b
    simp only [Matrix.of_apply, Matrix.transpose_apply]
    exact if_congr and_comm rfl rfl

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

def StepLiftG : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L) (_hs : M.split = some g) (r : ℕ) (T T' : F) (TT : M.R)
    (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ Zσ₁ Zσ₂ : M.Mat (r + 1)),
    GHyp M g T T' TT Zh₁ Z₁ Zσ₁ → GHyp M g T T' TT Zh₂ Z₂ Zσ₂ →
    ∀ γ : IsoMbe Z₁.Z Z₂.Z, ∃ (P Q P' : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R) (γ' : IsoMbe Zσ₁.Z Zσ₂.Z),
      (∀ v, γ.1 (Submodule.Quotient.mk v) = Submodule.Quotient.mk (P.mulVec v)) ∧
      (∀ w, γ'.1 (Submodule.Quotient.mk w) = Submodule.Quotient.mk (P'.mulVec w)) ∧
      P * Z₁.Z = Z₂.Z * Q ∧
      (∀ i, P i (Fin.last r) = if i = Fin.last r then 1 else 0) ∧
      (∀ j, Q (Fin.last r) j = if j = Fin.last r then 1 else 0) ∧
      ∀ w : Fin (r + 1) → M.R, ∃ m : Fin (r + 1) → M.R, m (Fin.last r) = 0 ∧
        ∀ i, ∑ j, M.L.cj (Q j i : E) * ((P'.mulVec w) j : E) = (w i : E) + ((Zσ₁.Z.mulVec m) i : E)

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
