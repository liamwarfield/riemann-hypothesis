module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRedField
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DBoundB

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenFinSt
noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.AdelicU GlobalTheory.StdUnn IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

abbrev Ev (D : D7) (v : GlobalTheory.FinPl.Pl D) := Fv D.host.F v ⊗[D.host.F] D.host.E

def IsIntUnit {D : D7} {v : GlobalTheory.FinPl.Pl D} (z : Ev D v) : Prop :=
  z ∈ intLoc D.host.F D.host.E v ∧ ∃ z' ∈ intLoc D.host.F D.host.E v, z * z' = 1

def cTv {D : D7} {v : GlobalTheory.FinPl.Pl D} (a : Matrix (Fin n) (Fin n) (Ev D v)) : Matrix (Fin n) (Fin n) (Ev D v) :=
  (a.map (sigR (Fv D.host.F v) D.sp.cm.sig)).transpose

def LocGood {D : D7} {v : GlobalTheory.FinPl.Pl D} (kv : Matrix (Fin (n + n)) (Fin (n + n)) (Ev D v))
    (a : Matrix (Fin n) (Fin n) (Ev D v)) (I : Finset (Fin n)) : Prop :=
  (∀ i j, a i j ∈ intLoc D.host.F D.host.E v) ∧ IsIntUnit a.det ∧
    IsIntUnit (blkDm (kv * blk4 a 0 0 (cTv a)⁻¹ * wIm I)).det

def LocFin : Prop :=
  ∀ (D : D7) (n : ℕ), ∀ k ∈ K D n, ∀ v : GlobalTheory.FinPl.Pl D,
    ∃ (a : Matrix (Fin n) (Fin n) (Ev D v)) (I : Finset (Fin n)), LocGood ((mat k).map (GlobalTheory.FinPl.compAt D v)) a I

def GlueLevi : Prop :=
  ∀ (D : D7) (n : ℕ) (a : ∀ v : GlobalTheory.FinPl.Pl D, Matrix (Fin n) (Fin n) (Ev D v)),
    (∀ v i j, a v i j ∈ intLoc D.host.F D.host.E v) → (∀ v, IsIntUnit (a v).det) →
    ∃ m : G D n, m ∈ genSet D n ∧ (∀ v, (mat m).map (GlobalTheory.FinPl.compAt D v) = blk4 (a v) 0 0 (cTv (a v))⁻¹) ∧
      ∀ τ, (mat m).map (Formalism.IndefR.Eqv.psiT D τ) = 1

def GlueW : Prop :=
  ∀ (D : D7) (n : ℕ) (I : GlobalTheory.FinPl.Pl D → Finset (Fin n)),
    ∃ w ∈ Subgroup.closure (genSet D n), (∀ v, (mat w).map (GlobalTheory.FinPl.compAt D v) = wIm (I v)) ∧
      ∀ τ, (mat w).map (Formalism.IndefR.Eqv.psiT D τ) = 1

def UnitAE : Prop :=
  ∀ (D : D7) (d : AE D), (∀ τ, Formalism.IndefR.Eqv.psiT D τ d ≠ 0) → (∀ v, IsIntUnit (GlobalTheory.FinPl.compAt D v d)) → IsUnit d

end PositivityTheory.Rg.Sw.Glob
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenInf
noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GenInfH

open PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.PlaceFactsH
open Formalism.IndefR.Eqv (psiT glueA splitInv psiT_glueA finPart_glueA ae_ext' mat_ext)

variable {D : D7} {n : ℕ}

theorem isUnit_of_comps (x : AE D) (h1 : ∀ τ, psiT D τ x ≠ 0) (h2 : IsUnit (finPart D x)) : IsUnit x := by
  obtain ⟨u, hu⟩ := h2
  set y : AE D := glueA D (splitInv D fun τ => (psiT D τ x)⁻¹) ((u⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : _)
  have hxy : x * y = 1 := by
    apply ae_ext' D
    · intro τ
      rw [map_mul, psiT_glueA, map_one, mul_inv_cancel₀ (h1 τ)]
    · rw [map_mul, finPart_glueA, map_one, ← hu, Units.mul_inv]
  exact ⟨⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, rfl⟩

theorem cT_blk4 {R : Type} [CommRing R] (σ : R →+* R) (a b c d : Matrix (Fin n) (Fin n) R) :
    Formalism.UG.cT σ (blk4 a b c d) = blk4 (Formalism.UG.cT σ a) (Formalism.UG.cT σ c) (Formalism.UG.cT σ b) (Formalism.UG.cT σ d) := by
  ext i j
  simp only [Formalism.UG.cT, blk4, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl

theorem cT_zero' {R : Type} [CommRing R] (σ : R →+* R) : Formalism.UG.cT σ (0 : Matrix (Fin n) (Fin n) R) = 0 := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_neg' {R : Type} [CommRing R] (σ : R →+* R) (M : Matrix (Fin n) (Fin n) R) :
    Formalism.UG.cT σ (-M) = -Formalism.UG.cT σ M := by
  ext i j; simp [Formalism.UG.cT]

theorem blk4_neg {R : Type} [CommRing R] (a b c d : Matrix (Fin n) (Fin n) R) :
    blk4 (-a) (-b) (-c) (-d) = -blk4 a b c d := by
  ext i j
  simp only [blk4, Matrix.neg_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl

theorem blkDm_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    blkDm (M.map f) = (blkDm M).map f := by
  ext i j; rfl

theorem blkDm_one {R : Type} [CommRing R] : blkDm (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 1 := by
  ext i j
  simp [blkDm, Matrix.toBlocks₂₂, Matrix.one_apply]

theorem eI_mul_self {R : Type} [CommRing R] (I : Finset (Fin n)) : (eI I : Matrix (Fin n) (Fin n) R) * eI I = eI I := by
  simp only [eI, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : i ∈ I <;> simp [h]

theorem eI_conjTranspose (I : Finset (Fin n)) : (eI I : Matrix (Fin n) (Fin n) ℂ)ᴴ = eI I := by
  simp only [eI, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  by_cases h : i ∈ I <;> simp [h]

theorem weyl_idem {R : Type} [CommRing R] (e : Matrix (Fin n) (Fin n) R) (he : e * e = e) :
    blk4 1 e 0 1 * blk4 1 0 (-e) 1 * blk4 1 e 0 1 = blk4 (1 - e) e (-e) (1 - e) := by
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg,
    Matrix.neg_mul, Matrix.add_mul, he]
  congr 1 <;> abel

theorem unip_unitary {R : Type} [CommRing R] (σ : R →+* R) (b : Matrix (Fin n) (Fin n) R) (hb : Formalism.UG.cT σ b = b) :
    Formalism.UG.cT σ (blk4 1 b 0 1) * blk4 0 1 (-1) 0 * blk4 1 b 0 1 = blk4 0 1 (-1) 0 := by
  rw [cT_blk4, Formalism.UG.cT_one, cT_zero', hb, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg,
    Matrix.neg_mul]
  congr 1 <;> simp

theorem unipBar_unitary {R : Type} [CommRing R] (σ : R →+* R) (c : Matrix (Fin n) (Fin n) R) (hc : Formalism.UG.cT σ c = c) :
    Formalism.UG.cT σ (blk4 1 0 c 1) * blk4 0 1 (-1) 0 * blk4 1 0 c 1 = blk4 0 1 (-1) 0 := by
  rw [cT_blk4, Formalism.UG.cT_one, cT_zero', hc, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg,
    Matrix.neg_mul]
  congr 1 <;> simp

theorem JR_Jst (D : D7) (n : ℕ) : JR (F := D.host.F) (AF D.host.F) (Jst D n) = blk4 0 1 (-1) 0 := by
  rw [JR, Jst, block_matrix_map, Matrix.map_neg _ (map_neg _), Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_zero _ (map_zero _)]

def nEl (b : Matrix (Fin n) (Fin n) (AE D)) (hb : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) b = b) : G D n :=
  (⟨⟨blk4 1 b 0 1, blk4 1 (-b) 0 1,
      by rw [submatrix_fromBlocks_mul]; simp [block_matrix_one],
      by rw [submatrix_fromBlocks_mul]; simp [block_matrix_one]⟩,
    by
      show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (blk4 1 b 0 1) * JR (AF D.host.F) (Jst D n) * blk4 1 b 0 1 =
        JR (AF D.host.F) (Jst D n)
      rw [JR_Jst]; exact unip_unitary _ b hb⟩ : HR (AF D.host.F) D.sp.cm.sig (Jst D n))

def nBarEl (c : Matrix (Fin n) (Fin n) (AE D)) (hc : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) c = c) : G D n :=
  (⟨⟨blk4 1 0 c 1, blk4 1 0 (-c) 1,
      by rw [submatrix_fromBlocks_mul]; simp [block_matrix_one],
      by rw [submatrix_fromBlocks_mul]; simp [block_matrix_one]⟩,
    by
      show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (blk4 1 0 c 1) * JR (AF D.host.F) (Jst D n) * blk4 1 0 c 1 =
        JR (AF D.host.F) (Jst D n)
      rw [JR_Jst]; exact unipBar_unitary _ c hc⟩ : HR (AF D.host.F) D.sp.cm.sig (Jst D n))

theorem mat_nEl (b : Matrix (Fin n) (Fin n) (AE D)) (hb) : mat (nEl b hb) = blk4 1 b 0 1 := rfl

theorem mat_nBarEl (c : Matrix (Fin n) (Fin n) (AE D)) (hc) : mat (nBarEl c hc) = blk4 1 0 c 1 := rfl

theorem cT_starRingEnd (M : Matrix (Fin (n + n)) (Fin (n + n)) ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]


set_option maxHeartbeats 1000000 in
theorem exists_I (hL : LocRedField) (k : G D n) (τ : D.what₂.Tau) :
    ∃ I : Finset (Fin n), IsUnit (blkDm ((mat k).map (psiT D τ) * wIm I)).det := by
  set M := (mat k).map (psiT D τ) with hM
  have hgU : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mat k) * JR (AF D.host.F) (Jst D n) * mat k =
      JR (AF D.host.F) (Jst D n) := k.2
  have hu : Mᴴ * blk4 0 1 (-1) 0 * M = blk4 0 1 (-1) 0 := by
    have := congrArg (fun X => X.map (psiT D τ)) hgU
    simp only [Matrix.map_mul, cT_map_psiT', Jst_map_psiT] at this
    exact this
  have hJJ : (blk4 (0 : Matrix (Fin n) (Fin n) ℂ) 1 (-1) 0) * blk4 0 1 (-1) 0 = -1 := by
    rw [submatrix_fromBlocks_mul]
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg,
      Matrix.neg_mul, neg_neg]
    rw [← block_matrix_one, ← blk4_neg, neg_zero]
  have hinv : ((-(blk4 0 1 (-1) 0)) * Mᴴ * blk4 0 1 (-1) 0) * M = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hu, Matrix.neg_mul, hJJ, neg_neg]
  have hdet : IsUnit M.det := Matrix.isUnit_det_of_left_inverse hinv
  have hg : Matrix.nonsingInvUnit M hdet ∈ Formalism.UG.UJ (starRingEnd ℂ) (J2 ℂ n) := by
    show Formalism.UG.cT (starRingEnd ℂ) M * J2 ℂ n * M = J2 ℂ n
    rw [cT_starRingEnd]
    exact hu
  obtain ⟨I, hI⟩ := hL ℂ (starRingEnd ℂ) (fun a => star_star a) n _ hg
  exact ⟨I, hI⟩

end PositivityTheory.Rg.Sw.Glob.GenInfH

namespace PositivityTheory.Rg.Sw.Glob

open GenInfH PlaceFactsH
open Formalism.IndefR.Eqv (psiT glueA splitInv psiT_glueA finPart_glueA ae_ext' mat_ext)

set_option maxHeartbeats 1000000 in
theorem kInInf_of (hU : UnitD) (hL : LocRedField) : KInInf := by
  intro D n k hk hfin
  classical
  choose I hI using exists_I hL k
  set B : Matrix (Fin n) (Fin n) (AE D) :=
    Matrix.of fun i j => glueA D (splitInv D fun τ => (eI (I τ) : Matrix (Fin n) (Fin n) ℂ) i j) 0 with hBdef
  have hBτ : ∀ τ, B.map (psiT D τ) = eI (I τ) := by
    intro τ; ext i j; simp only [hBdef, Matrix.map_apply, Matrix.of_apply, psiT_glueA]
  have hBf : B.map (finPart D) = 0 := by
    ext i j; simp only [hBdef, Matrix.map_apply, Matrix.of_apply, finPart_glueA, Matrix.zero_apply]
  have hBB : B * B = B := by
    apply mat_ext D
    · intro τ; rw [Matrix.map_mul, hBτ, eI_mul_self]
    · rw [Matrix.map_mul, hBf, Matrix.zero_mul]
  have hBc : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) B = B := by
    apply mat_ext D
    · intro τ; rw [cT_map_psiT', hBτ, eI_conjTranspose]
    · rw [PositivityTheory.Rg.Sw.Glob.EmbP.cT_map_fin, hBf]
      ext i j; simp [Formalism.UG.cT]
  have hBc' : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (-B) = -B := by rw [cT_neg', hBc]
  set W : G D n := nEl B hBc * nBarEl (-B) hBc' * nEl B hBc with hW
  have hWmat : mat W = blk4 1 B 0 1 * blk4 1 0 (-B) 1 * blk4 1 B 0 1 := rfl
  have hWτ : ∀ τ, (mat W).map (psiT D τ) = wIm (I τ) := by
    intro τ
    rw [hWmat, Matrix.map_mul, Matrix.map_mul, block_matrix_map, block_matrix_map, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_zero _ (map_zero _), Matrix.map_neg _ (map_neg _), hBτ, weyl_idem _ (eI_mul_self _)]
    rfl
  have hWf : (mat W).map (finPart D) = 1 := by
    rw [hWmat, Matrix.map_mul, Matrix.map_mul, block_matrix_map, block_matrix_map, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_zero _ (map_zero _), Matrix.map_neg _ (map_neg _), hBf, neg_zero, block_matrix_one, Matrix.one_mul, Matrix.one_mul]
  have hunit : IsUnit (blkDm (mat (k * W))).det := by
    apply GenInfH.isUnit_of_comps
    · intro τ
      rw [RingHom.map_det, RingHom.mapMatrix_apply, ← blkDm_map, mat_mul', Matrix.map_mul, hWτ]
      exact (hI τ).ne_zero
    · rw [RingHom.map_det, RingHom.mapMatrix_apply, ← blkDm_map, mat_mul', Matrix.map_mul, hfin, hWf, Matrix.one_mul,
        blkDm_one, Matrix.det_one]
      exact isUnit_one
  have h1 := hU D n (k * W) hunit
  have h2 : W ∈ Subgroup.closure (genSet D n) := by
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
    · exact Subgroup.subset_closure (Or.inl ⟨B, rfl⟩)
    · exact Subgroup.subset_closure (Or.inr (Or.inr ⟨-B, rfl⟩))
    · exact Subgroup.subset_closure (Or.inl ⟨B, rfl⟩)
  have : k = (k * W) * W⁻¹ := by group
  rw [this]
  exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)

end PositivityTheory.Rg.Sw.Glob
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.BlockLowerRightMulBlockMatrix
noncomputable section

open Matrix GlobalTheory.StdUnn

namespace PositivityTheory.Rg.Sw.Glob.Gen2H

section Ring

variable {R : Type} [CommRing R] {n : ℕ}

theorem submatrix_fromBlocks_levi (P Q S T : Matrix (Fin n) (Fin n) R) :
    (blk4 P Q S T).submatrix finSumFinEquiv finSumFinEquiv = fromBlocks P Q S T := by
  unfold blk4
  rw [Matrix.submatrix_submatrix]
  simp

theorem block_lower_right_mul_block_matrix (M : Matrix (Fin (n + n)) (Fin (n + n)) R) (P Q S T : Matrix (Fin n) (Fin n) R) :
    blkDm (M * blk4 P Q S T) =
      (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ * Q +
        (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂ * T := by
  unfold blkDm
  rw [← Matrix.submatrix_mul_equiv M (blk4 P Q S T) finSumFinEquiv finSumFinEquiv finSumFinEquiv, submatrix_fromBlocks_levi]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (M.submatrix finSumFinEquiv finSumFinEquiv)]
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₂]

theorem block_matrix_mul (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  unfold blk4
  rw [Matrix.submatrix_mul_equiv (fromBlocks a b c d) (fromBlocks a' b' c' d') finSumFinEquiv.symm finSumFinEquiv.symm
    finSumFinEquiv.symm, Matrix.fromBlocks_multiply]

theorem vecMul_mix (C D : Matrix (Fin n) (Fin n) R) (I : Finset (Fin n)) (u : Fin n → R) (j : Fin n) :
    vecMul u (C * eI I + D * (1 - eI I)) j = if j ∈ I then vecMul u C j else vecMul u D j := by
  classical
  have h2 : (1 : Matrix (Fin n) (Fin n) R) - eI I = diagonal (fun i => if i ∈ I then (0 : R) else 1) := by
    rw [eI, ← diagonal_one, diagonal_sub]
    congr 1; funext i; split_ifs <;> simp
  rw [h2, eI, vecMul_add, Pi.add_apply, ← vecMul_vecMul, ← vecMul_vecMul, vecMul_diagonal, vecMul_diagonal]
  split_ifs <;> simp

end Ring

section Field

variable {k : Type} [Field k] {n : ℕ}

theorem cT_fromBlocks (σ : k →+* k) (A B C D : Matrix (Fin n) (Fin n) k) :
    Formalism.UG.cT σ (fromBlocks A B C D) =
      fromBlocks (Formalism.UG.cT σ A) (Formalism.UG.cT σ C) (Formalism.UG.cT σ B) (Formalism.UG.cT σ D) := by
  simp [Formalism.UG.cT, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]

theorem cT_submatrix (σ : k →+* k) (M : Matrix (Fin (n + n)) (Fin (n + n)) k) :
    (Formalism.UG.cT σ M).submatrix finSumFinEquiv finSumFinEquiv =
      Formalism.UG.cT σ (M.submatrix finSumFinEquiv finSumFinEquiv) := by
  ext i j
  rfl

theorem lower_rel (σ : k →+* k) (g : GL (Fin (n + n)) k) (hg : g ∈ Formalism.UG.UJ σ (J2 k n)) :
    let Gs := (g : Matrix (Fin (n + n)) (Fin (n + n)) k).submatrix finSumFinEquiv finSumFinEquiv
    Gs.toBlocks₂₁ * Formalism.UG.cT σ Gs.toBlocks₂₂ = Gs.toBlocks₂₂ * Formalism.UG.cT σ Gs.toBlocks₂₁ := by
  intro Gs
  have h0 : Formalism.UG.cT σ (g : Matrix (Fin (n + n)) (Fin (n + n)) k) * J2 k n * (g : Matrix (Fin (n + n)) (Fin (n + n)) k) =
      J2 k n := hg
  set J' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k := fromBlocks 0 1 (-1) 0 with hJ'
  have hJs : (J2 k n).submatrix finSumFinEquiv finSumFinEquiv = J' := by rw [J2, submatrix_fromBlocks_levi]
  have h1 : Formalism.UG.cT σ Gs * J' * Gs = J' := by
    have := congrArg (fun M => M.submatrix finSumFinEquiv finSumFinEquiv) h0
    rw [← Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv _, ← Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv _,
      cT_submatrix, hJs] at this
    exact this
  have hJJ : J' * J' = -1 := by
    rw [hJ', Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg, zero_add, add_zero]
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg, neg_zero]
  have h2 : (-J' * Formalism.UG.cT σ Gs * J') * Gs = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Formalism.UG.cT σ Gs), h1, Matrix.neg_mul, hJJ, neg_neg]
  have h3 : Gs * (-J' * Formalism.UG.cT σ Gs * J') = 1 := mul_eq_one_comm.mp h2
  have h4 : Gs * J' * Formalism.UG.cT σ Gs = J' := by
    calc Gs * J' * Formalism.UG.cT σ Gs = Gs * J' * Formalism.UG.cT σ Gs * (J' * J') * (-1) := by rw [hJJ]; noncomm_ring
      _ = (Gs * (-J' * Formalism.UG.cT σ Gs * J')) * J' := by noncomm_ring
      _ = J' := by rw [h3, Matrix.one_mul]
  have h5 := congrArg Matrix.toBlocks₂₂ h4
  conv_lhs at h5 => rw [← Matrix.fromBlocks_toBlocks Gs, cT_fromBlocks, hJ']
  rw [hJ', Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₂,
    Matrix.toBlocks_fromBlocks₂₂] at h5
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero, Matrix.neg_mul] at h5
  rw [neg_add_eq_zero] at h5
  exact h5.symm

theorem lower_inj (g : GL (Fin (n + n)) k) (u : Fin n → k)
    (hC : u ᵥ* ((g : Matrix (Fin (n + n)) (Fin (n + n)) k).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0)
    (hD : u ᵥ* ((g : Matrix (Fin (n + n)) (Fin (n + n)) k).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂ = 0) :
    u = 0 := by
  classical
  set Gs := (g : Matrix (Fin (n + n)) (Fin (n + n)) k).submatrix finSumFinEquiv finSumFinEquiv with hGs
  let w : Fin n ⊕ Fin n → k := Sum.elim 0 u
  have hw : w ᵥ* Gs = 0 := by
    funext x
    rcases x with i | i
    · have := congrFun hC i
      simpa [w, vecMul, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₂₁] using this
    · have := congrFun hD i
      simpa [w, vecMul, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₂₂] using this
  have hdet : Gs.det ≠ 0 := by
    rw [hGs, Matrix.det_submatrix_equiv_self]
    exact (Matrix.GeneralLinearGroup.det g).ne_zero
  have hw0 : w = 0 := by
    by_contra hne
    exact hdet (Matrix.exists_vecMul_eq_zero_iff.1 ⟨w, hne, hw⟩)
  funext j
  have := congrFun hw0 (Sum.inr j)
  simpa [w] using this

theorem conj_vecMul (σ : k →+* k) (u' : Fin n → k) (Y : Matrix (Fin n) (Fin n) k) (i : Fin n) :
    σ ((u' ᵥ* Y) i) = (Formalism.UG.cT σ Y *ᵥ (fun l => σ (u' l))) i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [vecMul, mulVec, dotProduct, Formalism.UG.cT, map_sum, map_mul, mul_comm]

theorem iso_eq (σ : k →+* k) (u u' : Fin n → k) (X Y : Matrix (Fin n) (Fin n) k) :
    ∑ i, (u ᵥ* X) i * σ ((u' ᵥ* Y) i) = u ⬝ᵥ ((X * Formalism.UG.cT σ Y) *ᵥ (fun l => σ (u' l))) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conj_vecMul]

end Field

end PositivityTheory.Rg.Sw.Glob.Gen2H

namespace PositivityTheory.Rg.Sw.Glob

open Gen2H

theorem locRedField : LocRedField := by
  intro k _ σ hσ n g hg
  classical
  set Gs := (g : Matrix (Fin (n + n)) (Fin (n + n)) k).submatrix finSumFinEquiv finSumFinEquiv with hGs
  set C := Gs.toBlocks₂₁ with hC
  set D := Gs.toBlocks₂₂ with hD
  have hrel : C * Formalism.UG.cT σ D = D * Formalism.UG.cT σ C := lower_rel σ g hg
  have hiso : ∀ u u' : Fin n → k,
      ∑ i, (u ᵥ* C) i * σ ((u' ᵥ* D) i) = ∑ i, (u ᵥ* D) i * σ ((u' ᵥ* C) i) := by
    intro u u'
    rw [iso_eq, iso_eq, hrel]
  let Surj : Finset (Fin n) → Prop := fun I => ∀ t : Fin n → k, ∃ u : Fin n → k, u ᵥ* D = 0 ∧ ∀ i ∈ I, (u ᵥ* C) i = t i
  have h0 : Surj ∅ := fun t => ⟨0, by simp, by simp⟩
  obtain ⟨I, hI, hmax⟩ := Finset.exists_max_image ((Finset.univ : Finset (Finset (Fin n))).filter Surj) Finset.card
    ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩⟩
  have hSI : Surj I := (Finset.mem_filter.1 hI).2
  have hInj : ∀ u : Fin n → k, u ᵥ* D = 0 → (∀ i ∈ I, (u ᵥ* C) i = 0) → u ᵥ* C = 0 := by
    intro u hu hI0
    by_contra hne
    obtain ⟨j, hj⟩ : ∃ j, (u ᵥ* C) j ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (funext h)
    have hjI : j ∉ I := fun h => hj (hI0 j h)
    have hS : Surj (insert j I) := by
      intro t
      obtain ⟨u', hu', ht⟩ := hSI t
      refine ⟨u' + ((t j - (u' ᵥ* C) j) / (u ᵥ* C) j) • u, ?_, ?_⟩
      · rw [add_vecMul, smul_vecMul, hu', hu, smul_zero, add_zero]
      · intro i hi
        rw [add_vecMul, smul_vecMul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rcases Finset.mem_insert.1 hi with rfl | hi
        · field_simp
          ring
        · rw [ht i hi, hI0 i hi, mul_zero, add_zero]
    have := hmax (insert j I) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hS⟩)
    rw [Finset.card_insert_of_notMem hjI] at this
    omega
  refine ⟨I, ?_⟩
  rw [wIm, block_lower_right_mul_block_matrix, ← hGs, ← hC, ← hD, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  have hmix : ∀ j, (j ∈ I → (u ᵥ* C) j = 0) ∧ (j ∉ I → (u ᵥ* D) j = 0) := by
    intro j
    have := congrFun hu j
    rw [vecMul_mix] at this
    by_cases h : j ∈ I
    · rw [if_pos h] at this
      exact ⟨fun _ => this, fun h' => absurd h h'⟩
    · rw [if_neg h] at this
      exact ⟨fun h' => absurd h' h, fun _ => this⟩
  have hD0 : u ᵥ* D = 0 := by
    funext j
    by_cases hj : j ∈ I
    · obtain ⟨u', hu', ht⟩ := hSI (fun i => if i = j then 1 else 0)
      have h := hiso u u'
      rw [hu'] at h
      simp only [Pi.zero_apply, map_zero, mul_zero, Finset.sum_const_zero] at h
      have hterm : ∀ i, (u ᵥ* D) i * σ ((u' ᵥ* C) i) = if i = j then (u ᵥ* D) j else 0 := by
        intro i
        by_cases hi : i ∈ I
        · rw [ht i hi]
          by_cases hij : i = j
          · subst hij
            simp
          · simp [hij]
        · have hne : i ≠ j := fun e => hi (e ▸ hj)
          rw [(hmix i).2 hi]
          simp [hne]
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_ite_eq'] at h
      simpa using h.symm
    · exact (hmix j).2 hj
  have hC0 : u ᵥ* C = 0 := hInj u hD0 (fun i hi => (hmix i).1 hi)
  exact hu0 (lower_inj g u hC0 hD0)

end PositivityTheory.Rg.Sw.Glob
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DilDSt
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.IteratedDerivOfReal
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.CompAtAdd
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.TraceGramBReal
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DilAH

variable {D : D7} {n : ℕ}

theorem cLoc_pos {l : D.what₂.Tau → ℝ} {τ : D.what₂.Tau} (h : l τ ≠ 0) : 0 < cLoc l τ := by
  unfold cLoc; have := abs_pos.2 h; positivity

theorem abs_tLoc (l : D.what₂.Tau → ℝ) (τ : D.what₂.Tau) : |tLoc l τ| = cLoc l τ := by
  unfold tLoc cLoc; rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

theorem trace_gramB_real {m : ℕ} (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) :
    (gramB ε b u).trace = ((∑ a ∈ Finset.univ.filter (fun a => ε a = b), ∑ j, ‖u a j‖ ^ 2 : ℝ) : ℂ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramB, evX, Qb, map_sum, map_mul, MvPolynomial.eval_X, if_true, Bool.false_eq_true, if_false,
    Matrix.trace, Matrix.diag]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.conj_mul', Complex.star_def]

theorem sum_filter_bool {m : ℕ} (ε : Fin m → Bool) (f : Fin m → ℝ) :
    ∑ a ∈ Finset.univ.filter (fun a => ε a = true), f a + ∑ a ∈ Finset.univ.filter (fun a => ε a = false), f a =
      ∑ a, f a := by
  rw [← Finset.sum_union]
  · congr 1; ext a; cases ε a <;> simp
  · rw [Finset.disjoint_filter]; intro a _ h; simp [h]

theorem gC_gauss {m : ℕ} (ε : Fin m → Bool) (t c : ℝ) (hc : 0 < c) (δ : ℝ) (u : Fin m → Fin n → ℂ) :
    gC ε t c ((Complex.I * (δ / c : ℝ)) • 1) ((-(Complex.I * (δ / c : ℝ))) • 1) u =
      Complex.exp (-((δ * ∑ a, ∑ j, ‖u a j‖ ^ 2 : ℝ) : ℂ)) := by
  unfold gC
  congr 1
  simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul, trace_gramB_real]
  have h := sum_filter_bool (epsT t ε) (fun a => ∑ j, ‖u a j‖ ^ 2)
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [← h]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

theorem fP_one {m : ℕ} (ε : Fin m → Bool) (t c : ℝ) (hc : 0 < c) :
    fP c (1 : PX m n) = gZf ε t c (Complex.I • 1) := by
  funext u
  have e1 : gZf ε t c (Complex.I • 1) u = gC ε t c ((Complex.I * (c / c : ℝ)) • 1) ((-(Complex.I * (c / c : ℝ))) • 1) u := by
    unfold gZf gC
    rw [div_self hc.ne', Complex.ofReal_one, mul_one, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Complex.star_def, Complex.conj_I]
  rw [e1, gC_gauss ε t c hc c u]
  simp [fP, evX, gs]

end PositivityTheory.Rg.Sw.Glob.DilAH
end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DilBH

variable {D : D7} {n : ℕ}

theorem compAt_add {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (x y : Mx D m n) :
    compAt θ τ (x + y) = compAt θ τ x + compAt θ τ y := by
  ext i j
  simp only [compAt, Matrix.map_apply, Matrix.add_apply, map_add (f := _)]

theorem pointAt {m : ℕ} (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ)
    (hfr : IsUnit fr.det) (x₀ : Mx D m n) (u : Fin m → Fin n → ℂ) :
    ∃ x : Mx D m n, fr⁻¹ * compAt θ τ x = Matrix.of u ∧ (∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x₀) ∧
      x.map (finPart D) = x₀.map (finPart D) := by
  obtain ⟨L, _, hLf, hLz⟩ :=
    Formalism.IndefR.Eqv.lineAtExists_holds D θ hθ m n τ (fr * Matrix.of u - compAt θ τ x₀)
  refine ⟨x₀ + L 1, ?_, ?_, ?_⟩
  · rw [compAt_add, hLz 1 τ, if_pos rfl, Complex.ofReal_one, one_smul]
    have hs : compAt θ τ x₀ + (fr * Matrix.of u - compAt θ τ x₀) = fr * Matrix.of u := by abel
    rw [hs]
    exact Matrix.nonsing_inv_mul_cancel_left _ _ hfr
  · intro τ' h
    rw [compAt_add, hLz 1 τ', if_neg h, add_zero]
  · ext i j
    have h1 := congrFun (congrFun (hLf 1) i) j
    simp only [Matrix.map_apply, Matrix.add_apply, map_add (f := _), Matrix.zero_apply] at h1 ⊢
    rw [h1, add_zero]

end PositivityTheory.Rg.Sw.Glob.DilBH
end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DilCH

variable {D : D7} {n : ℕ} {θ : InfFam D} {V : HSp D} {τ : D.what₂.Tau} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem tens_cancel (hθ : IsInfFam θ) (hfr : IsUnit fr.det) {Ψ : Mx D V.rank n → ℂ} (hΨ : AwayCls θ τ fr Ψ)
    {x₀ : Mx D V.rank n} (hx₀ : Ψ x₀ ≠ 0) {F G : (Fin V.rank → Fin n → ℂ) → ℂ}
    (h : tens θ τ fr F Ψ = tens θ τ fr G Ψ) : F = G := by
  funext u
  obtain ⟨x, hxu, hxo, hxf⟩ := DilBH.pointAt θ hθ τ fr hfr x₀ u
  have hΨx : Ψ x = Ψ x₀ := hΨ.1 x x₀ hxo hxf
  have := congrFun h x
  simp only [tens, hxu, hΨx] at this
  exact mul_right_cancel₀ hx₀ this

variable {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {ι : GR n →* G D n}
  {L : GR n → ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ)}

theorem L_sub (hL : IsLocFact ω τ fr ι L) (hθ : IsInfFam θ) (hfr : IsUnit fr.det) {Ψ : Mx D V.rank n → ℂ}
    (hΨ : AwayCls θ τ fr Ψ) {x₀ : Mx D V.rank n} (hx₀ : Ψ x₀ ≠ 0) (y : GR n) {f g : (Fin V.rank → Fin n → ℂ) → ℂ}
    (hf : IsSch f) (hg : IsSch g) : L y (f - g) = L y f - L y g := by
  have h := hL.2 y Ψ hΨ (f - g) (SchwartzDifferenceQuotient.isSch_sub hf hg)
  have e : (⟨tens θ τ fr (f - g) Ψ, hΨ.2 _ (SchwartzDifferenceQuotient.isSch_sub hf hg)⟩ : schwartzA θ V.rank n) =
      ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ - ⟨tens θ τ fr g Ψ, hΨ.2 g hg⟩ :=
    Subtype.ext (by funext x; simp only [tens, Submodule.coe_sub]; show (f _ - g _) * _ = f _ * _ - g _ * _; ring)
  rw [e, map_sub, Submodule.coe_sub, hL.2 y Ψ hΨ f hf, hL.2 y Ψ hΨ g hg] at h
  refine tens_cancel hθ hfr hΨ hx₀ ?_
  rw [← h]; funext x
  show tens θ τ fr (L y f) Ψ x - tens θ τ fr (L y g) Ψ x = _
  simp only [tens]
  show _ = (L y f _ - L y g _) * _
  ring

theorem L_smul (hL : IsLocFact ω τ fr ι L) (hθ : IsInfFam θ) (hfr : IsUnit fr.det) {Ψ : Mx D V.rank n → ℂ}
    (hΨ : AwayCls θ τ fr Ψ) {x₀ : Mx D V.rank n} (hx₀ : Ψ x₀ ≠ 0) (y : GR n) (a : ℂ) {f : (Fin V.rank → Fin n → ℂ) → ℂ}
    (hf : IsSch f) : L y (fun u => a * f u) = fun u => a * L y f u := by
  have h := hL.2 y Ψ hΨ _ (SchwartzDifferenceQuotient.isSch_smul a hf)
  have e : (⟨tens θ τ fr (fun u => a * f u) Ψ, hΨ.2 _ (SchwartzDifferenceQuotient.isSch_smul a hf)⟩ : schwartzA θ V.rank n) =
      a • ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ :=
    Subtype.ext (by funext x; simp [tens, mul_assoc])
  rw [e, map_smul, Submodule.coe_smul, hL.2 y Ψ hΨ f hf] at h
  refine tens_cancel hθ hfr hΨ hx₀ ?_
  rw [← h]; funext x; simp [tens, mul_assoc]

theorem L_mul (hL : IsLocFact ω τ fr ι L) (hθ : IsInfFam θ) (hfr : IsUnit fr.det) {Ψ : Mx D V.rank n → ℂ}
    (hΨ : AwayCls θ τ fr Ψ) {x₀ : Mx D V.rank n} (hx₀ : Ψ x₀ ≠ 0) (y y' : GR n) {f : (Fin V.rank → Fin n → ℂ) → ℂ}
    (hf : IsSch f) : L (y * y') f = L y (L y' f) := by
  have h := hL.2 (y * y') Ψ hΨ f hf
  have h' : ω (ι y') ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ = ⟨tens θ τ fr (L y' f) Ψ, hΨ.2 _ (hL.1 y' f hf)⟩ :=
    Subtype.ext (hL.2 y' Ψ hΨ f hf)
  rw [map_mul, map_mul, Module.End.mul_apply, h', hL.2 y Ψ hΨ _ (hL.1 y' f hf)] at h
  exact tens_cancel hθ hfr hΨ hx₀ h.symm

theorem diffOn_iteratedDeriv {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (r : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv r f) U := by
  induction r with
  | zero => simpa using hf
  | succ r ih => rw [iteratedDeriv_succ]; exact ih.deriv hU

theorem iteratedDeriv_ofReal {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hR : ∀ s : ℝ, (s : ℂ) ∈ U) (r : ℕ) : iteratedDeriv r (fun t : ℝ => f t) = fun t : ℝ => iteratedDeriv r f t := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have hd : DifferentiableAt ℂ (iteratedDeriv r f) t :=
      (diffOn_iteratedDeriv hU hf r).differentiableAt (hU.mem_nhds (hR t))
    rw [iteratedDeriv_succ]
    exact (hd.hasDerivAt.comp_ofReal).deriv

end PositivityTheory.Rg.Sw.Glob.DilCH
end
end

noncomputable section

open Topology

namespace PositivityTheory.Rg.Sw.Glob

def ContDeriv : Prop :=
  ∀ (m n : ℕ) (U : Set ℂ), IsOpen U → ∀ f : ℂ → (Fin m → Fin n → ℂ) → ℂ,
    ContinuousOn (fun p : ℂ × (Fin m → Fin n → ℂ) => f p.1 p.2) (U ×ˢ Set.univ) →
    (∀ u, DifferentiableOn ℂ (fun z => f z u) U) →
    ∀ r : ℕ, ContinuousOn (fun p : ℂ × (Fin m → Fin n → ℂ) => iteratedDeriv r (fun z => f z p.2) p.1) (U ×ˢ Set.univ)

def SchScale : Prop :=
  ∀ (m n : ℕ) (f : (Fin m → Fin n → ℂ) → ℂ) (s : ℝ) (X : Fin n → ℝ) (a : ℂ), IsSch f →
    IsSch (fun u => a * f (fun i j => u i j * Real.exp (s * X j)))

end PositivityTheory.Rg.Sw.Glob
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenTop
noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.AdelicU GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GenTopH

variable {D : D7} {n : ℕ}

theorem mat_projFin (g : G D n) : (mat g).map (finPart D) = (HA.mat _ D.sp.cm.sig (Jst D n) (projFin D.sp.cm.sig (Jst D n) g)).1 :=
  rfl

theorem mat_projInf (g : G D n) : (mat g).map (infPart D) = (HA.mat _ D.sp.cm.sig (Jst D n) (projInf D.sp.cm.sig (Jst D n) g)).1 :=
  rfl

end PositivityTheory.Rg.Sw.Glob.GenTopH

namespace PositivityTheory.Rg.Sw.Glob

theorem genA_of : UnitD → PIn → KInInf → KInFin → GenA := by
  intro _ hP hKi hKf D n
  show Subgroup.closure (genSet D n) = ⊤
  rw [eq_top_iff]
  intro g _
  obtain ⟨p, hp, k, hk, rfl⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D n g
  refine Subgroup.mul_mem _ (hP D n p hp) ?_
  rw [← ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig (Jst D n) k]
  have hk' := mem_levelAll.1 hk
  refine Subgroup.mul_mem _ (hKi D n _ ?_ ?_) (hKf D n _ ?_ ?_)
  · refine mem_levelAll.2 ⟨fun v => ?_, fun w => ?_⟩
    · rw [proj_ofInf]; exact one_mem _
    · rw [projArch_ofInf, projInfArch_projInf]; exact hk'.2 w
  · rw [GenTopH.mat_projFin, projFin_ofInf]; rfl
  · refine mem_levelAll.2 ⟨fun v => ?_, fun w => ?_⟩
    · rw [proj_ofFin, projFinLoc_projFin]; exact hk'.1 v
    · rw [projArch_ofFin]; exact one_mem _
  · intro τ
    have e : Formalism.IndefR.Eqv.psiT D τ = (Formalism.IndefR.Eqv.thetaC D τ).comp (infPart D) := rfl
    rw [e, RingHom.coe_comp, ← Matrix.map_map, GenTopH.mat_projInf, projInf_ofFin]
    exact Matrix.map_one _ (map_zero _) (map_one _)

end PositivityTheory.Rg.Sw.Glob
end
end
