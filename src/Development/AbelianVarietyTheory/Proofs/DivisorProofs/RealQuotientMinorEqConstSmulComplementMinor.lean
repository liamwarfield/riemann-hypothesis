module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryMinorMapRealPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicFactorFiniteMod

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetCharInvariantSameValueTwisted
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetCharInvariantSameValueTwisted
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.MinorFrame

open MvPolynomial

theorem colSub_totalDegree_le {ι : Type} [Fintype ι] {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    (colSub g P).totalDegree ≤ P.totalDegree := by
  classical
  unfold colSub
  conv_lhs => rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [aeval_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [algebraMap_eq, totalDegree_C, zero_add]
  refine le_trans ?_ (le_totalDegree hs)
  unfold Finsupp.prod Finsupp.sum
  refine (totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (totalDegree_pow _ _).trans ?_
  have h1 : (∑ j' : Fin a, C (g i.1 j' i.2.2) * (X (i.1, i.2.1, j') : Pol ι d a)).totalDegree ≤ 1 :=
    totalDegree_finsetSum_le fun j _ => (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])
  calc s i * _ ≤ s i * 1 := Nat.mul_le_mul_left _ h1
    _ = s i := mul_one _

theorem star_detChar_mul_detChar {ι : Type} [Fintype ι] {a : ℕ} (n : ι → ℕ) (g : ι → Matrix.unitaryGroup (Fin a) ℂ) :
    starRingEnd ℂ (detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ))) *
      detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) = 1 := by
  unfold detChar
  rw [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun τ _ => ?_
  rw [map_pow, ← mul_pow]
  have h : starRingEnd ℂ (g τ : Matrix (Fin a) (Fin a) ℂ).det * (g τ : Matrix (Fin a) (Fin a) ℂ).det = 1 := by
    rw [starRingEnd_apply, ← Matrix.det_conjTranspose, ← Matrix.det_mul, ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.1 (g τ).2,
      Matrix.det_one]
  rw [h, one_pow]

@[reducible] def fockCore {σ : Type} (S : Submodule ℂ (MvPolynomial σ ℂ)) : InnerProductSpace.Core ℂ S where
  inner x y := Formalism.L2.DIV.fockS x.1 y.1
  conj_inner_symm x y := (fockS_conj x.1 y.1).symm
  re_inner_nonneg x := by
    by_cases hx : x.1 = 0
    · simp [hx, Formalism.L2.DIV.fockS]
    · exact (fockS_self_re_pos hx).le
  add_left x y z := by
    show Formalism.L2.DIV.fockS (x.1 + y.1) z.1 = _
    rw [← Formalism.L2.DIV.fockL_apply, LinearMap.map_add₂]
    rfl
  smul_left x y r := by
    show Formalism.L2.DIV.fockS (r • x.1) y.1 = _
    rw [← Formalism.L2.DIV.fockL_apply, LinearMap.map_smulₛₗ₂, smul_eq_mul]
    rfl
  definite x hx := by
    by_contra h
    have h' : x.1 ≠ 0 := fun e => h (Subtype.ext e)
    have := fockS_self_re_pos h'
    rw [show Formalism.L2.DIV.fockS x.1 x.1 = 0 from hx] at this
    simp at this

theorem exists_mem_inv_eq_of_twisted : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) (Pr : Type) [AddCommGroup Pr] [Module ℂ Pr]
    (q : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] Pr),
    (∀ (g : ι → Matrix.unitaryGroup (Fin a) ℂ) (P : GlobalTheory.MinorFrame.Pol ι d a),
      q (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P) = GlobalTheory.MinorFrame.detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • q P) →
    ∀ P : GlobalTheory.MinorFrame.Pol ι d a, ∃ P₀ ∈ GlobalTheory.MinorFrame.inv (ι := ι) a d n, q P = q P₀ := by
  intro ι _ a d n Pr _ _ q hq P
  classical
  let S : Submodule ℂ (Pol ι d a) := restrictTotalDegree (Var ι d a) ℂ P.totalDegree
  haveI : FiniteDimensional ℂ S :=
    inferInstanceAs (Module.Finite ℂ (restrictTotalDegree (Var ι d a) ℂ P.totalDegree))
  letI : InnerProductSpace.Core ℂ S := fockCore S
  letI : NormedAddCommGroup S := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ S := InnerProductSpace.ofCore _
  have hmemS : ∀ (g : ι → Matrix (Fin a) (Fin a) ℂ) (x : Pol ι d a), x ∈ S → colSub g x ∈ S := fun g x hx =>
    (mem_restrictTotalDegree _ _ _).2 ((colSub_totalDegree_le g x).trans ((mem_restrictTotalDegree _ _ _).1 hx))
  let gen : Set S := {w | ∃ (g : ι → Matrix.unitaryGroup (Fin a) ℂ) (x : S),
      (w : Pol ι d a) = colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) x.1 -
        detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • x.1}
  let K : Submodule ℂ S := Submodule.span ℂ gen
  have hK : ∀ w ∈ K, q (w : Pol ι d a) = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, y, hy⟩ := hx
      rw [hy, map_sub, map_smul, hq, sub_self]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul r x _ hx => simp [hx]
  have hPS : P ∈ S := (mem_restrictTotalDegree _ _ _).2 le_rfl
  obtain ⟨y, hy, z, hz, hyz⟩ := K.exists_add_mem_mem_orthogonal (⟨P, hPS⟩ : S)
  refine ⟨z.1, ?_, ?_⟩
  · intro g
    set G := colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) z.1 with hG
    set c := detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) with hc
    let w : S := ⟨G - c • z.1, S.sub_mem (hmemS _ _ z.2) (S.smul_mem c z.2)⟩
    have hw : w ∈ K := Submodule.subset_span ⟨g, z, rfl⟩
    have h1 : Formalism.L2.DIV.fockL z.1 (G - c • z.1) = 0 := Submodule.inner_left_of_mem_orthogonal hw hz
    have h2 : Formalism.L2.DIV.fockL (G - c • z.1) z.1 = 0 := Submodule.inner_right_of_mem_orthogonal hw hz
    have hinv : Formalism.L2.DIV.fockL G G = Formalism.L2.DIV.fockL z.1 z.1 := by
      rw [Formalism.L2.DIV.fockL_apply, Formalism.L2.DIV.fockL_apply, hG, fockS_colSub_unitary]
    have hcc := star_detChar_mul_detChar n g
    rw [← hc] at hcc
    have e1 : Formalism.L2.DIV.fockL (G - c • z.1) (G - c • z.1) =
        Formalism.L2.DIV.fockL (G - c • z.1) G - c * Formalism.L2.DIV.fockL (G - c • z.1) z.1 := by
      rw [map_sub, map_smul, smul_eq_mul]
    have e2 : Formalism.L2.DIV.fockL (G - c • z.1) G =
        Formalism.L2.DIV.fockL G G - starRingEnd ℂ c * Formalism.L2.DIV.fockL z.1 G := by
      rw [LinearMap.map_sub₂, LinearMap.map_smulₛₗ₂, smul_eq_mul]
    have h1' : Formalism.L2.DIV.fockL z.1 G - c * Formalism.L2.DIV.fockL z.1 z.1 = 0 := by
      rw [← h1, map_sub, map_smul, smul_eq_mul]
    have hWW : Formalism.L2.DIV.fockL (G - c • z.1) (G - c • z.1) = 0 := by
      linear_combination e1 + e2 - c * h2 + hinv - starRingEnd ℂ c * h1' - Formalism.L2.DIV.fockL z.1 z.1 * hcc
    by_contra hne
    have hne' : G - c • z.1 ≠ 0 := sub_ne_zero.2 hne
    have := fockS_self_re_pos hne'
    rw [← Formalism.L2.DIV.fockL_apply, hWW] at this
    simp at this
  · have hP : P = y.1 + z.1 := congrArg Subtype.val hyz
    rw [hP, map_add (f := _), hK y hy, zero_add]

end GlobalTheory.MinorFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetCharInvariantSameValueTwistedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_detCharInvariant_same_value_twisted : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) (Pr : Type) [AddCommGroup Pr] [Module ℂ Pr]
    (q : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] Pr),
    (∀ (g : ι → Matrix.unitaryGroup (Fin a) ℂ) (P : GlobalTheory.MinorFrame.Pol ι d a),
      q (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P) = GlobalTheory.MinorFrame.detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • q P) →
    ∀ P : GlobalTheory.MinorFrame.Pol ι d a, ∃ P₀ ∈ GlobalTheory.MinorFrame.inv (ι := ι) a d n, q P = q P₀ := by
  first | exact @GlobalTheory.MinorFrame.exists_mem_inv_eq_of_twisted | exact GlobalTheory.MinorFrame.exists_mem_inv_eq_of_twisted | (intros; apply GlobalTheory.MinorFrame.exists_mem_inv_eq_of_twisted <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDetCharInvariantsRowSubstitutionIrreducible
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigMatConjTransposeMul
open Classical

noncomputable section

open MvPolynomial Matrix

namespace GlobalTheory.MinorFrame.FockRowSub

variable {ι : Type} [Fintype ι] {a d : ℕ}

def rowEquiv (ι : Type) [Fintype ι] (d : ℕ) : Fin d × ι ≃ Fin (Fintype.card (Fin d × ι)) :=
  Fintype.equivFin _

def varFlat (ι : Type) [Fintype ι] (d a : ℕ) : Var ι d a → Fin (Fintype.card (Fin d × ι)) × Fin a :=
  fun y => (rowEquiv ι d (y.2.1, y.1), y.2.2)

theorem varFlat_injective : Function.Injective (varFlat ι d a) := by
  intro y z h
  simp only [varFlat, Prod.mk.injEq] at h
  have h1 := (rowEquiv ι d).injective h.1
  simp only [Prod.mk.injEq] at h1
  exact Prod.ext h1.2 (Prod.ext h1.1 h.2)

def bigMat (κ : ι → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (Fintype.card (Fin d × ι))) (Fin (Fintype.card (Fin d × ι))) ℂ :=
  (blockDiagonal κ).submatrix (rowEquiv ι d).symm (rowEquiv ι d).symm

theorem rename_rowSub (κ : ι → Matrix (Fin d) (Fin d) ℂ) (P : Pol ι d a) :
    rename (varFlat ι d a) (rowSub κ P) = ReciprocityTheory.PGsh.rowSubst (bigMat κ) (rename (varFlat ι d a) P) := by
  have key : (rename (varFlat ι d a)).comp (rowSub κ) =
      (ReciprocityTheory.PGsh.rowSubst (bigMat κ)).comp (rename (varFlat ι d a)) := by
    refine MvPolynomial.algHom_ext fun y => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, rowSub, aeval_X, rename_X, ReciprocityTheory.PGsh.rowSubst_X,
      ← (rowEquiv ι d).sum_comp, Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single y.1]
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [map_sum, map_mul, rename_C, rename_X, bigMat, submatrix_apply, varFlat, Equiv.symm_apply_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [blockDiagonal_apply_eq]
    · intro τ _ hτ
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [bigMat, varFlat, blockDiagonal_apply_ne _ _ _ hτ]
    · simp
  exact congrArg (fun f => f P) key

theorem bigMat_conjTranspose_mul (κ : ι → Matrix.unitaryGroup (Fin d) ℂ) :
    (bigMat fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ))ᴴ * bigMat (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) = 1 := by
  rw [bigMat, conjTranspose_submatrix, submatrix_mul_equiv, blockDiagonal_conjTranspose, ← blockDiagonal_mul]
  have h : ∀ τ, (κ τ : Matrix (Fin d) (Fin d) ℂ)ᴴ * (κ τ : Matrix (Fin d) (Fin d) ℂ) = 1 := fun τ => by
    have := (κ τ).2
    rw [Matrix.mem_unitaryGroup_iff'] at this
    simpa [Matrix.star_eq_conjTranspose] using this
  simp only [h]
  rw [show (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) = (1 : ι → Matrix (Fin d) (Fin d) ℂ) from rfl,
    blockDiagonal_one, submatrix_one_equiv]

theorem fockS_eq_fischer {ν : ℕ} {κ : Type} (f g : MvPolynomial (Fin ν × κ) ℂ) :
    Formalism.L2.DIV.fockS f g = ReciprocityTheory.PGsh.fischer g f := by
  rw [Formalism.L2.DIV.fockS_eq_sum f g (g.support ∪ f.support) Finset.subset_union_right, ReciprocityTheory.PGsh.fischer]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Formalism.L2.DIV.mfact, Finsupp.prod, RCLike.star_def]
  ring

end GlobalTheory.MinorFrame.FockRowSub

namespace GlobalTheory.MinorFrame

open FockRowSub

theorem fockS_rowSub_unitary {ι : Type} [Fintype ι] (a d : ℕ) (κ : ι → Matrix.unitaryGroup (Fin d) ℂ)
    (P Q : Pol ι d a) :
    Formalism.L2.DIV.fockS (rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P)
      (rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) Q) = Formalism.L2.DIV.fockS P Q := by
  rw [← GlobalTheory.Proof.ColumnInclusionRenaming.fockS_rename varFlat_injective, rename_rowSub, rename_rowSub, fockS_eq_fischer,
    ReciprocityTheory.PGsh.fischer_rowSubst, ReciprocityTheory.PGsh.rowSubst_mul, bigMat_conjTranspose_mul, ReciprocityTheory.PGsh.rowSubst_one,
    ← fockS_eq_fischer, GlobalTheory.Proof.ColumnInclusionRenaming.fockS_rename varFlat_injective]

end GlobalTheory.MinorFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSubEqDetCharSmulOfMemInv
open Classical

noncomputable section

namespace GlobalTheory.MinorFrame

open MvPolynomial

variable {ι : Type} [Fintype ι]

def genColSub (d a : ℕ) : Pol ι d a →ₐ[ℂ] MvPolynomial (Var ι d a) (MvPolynomial (ι × Fin a × Fin a) ℂ) :=
  aeval fun y => ∑ j' : Fin a, C (X (y.1, j', y.2.2)) * X (y.1, y.2.1, j')

omit [Fintype ι] in
theorem map_eval_genColSub {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    map (eval fun x : ι × Fin a × Fin a => g x.1 x.2.1 x.2.2) (genColSub d a P) = colSub g P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [genColSub, colSub, algebraMap_eq]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p y hp =>
    simp only [map_mul, hp]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [genColSub, colSub, map_sum]

def genDetChar (a : ℕ) (n : ι → ℕ) : MvPolynomial (ι × Fin a × Fin a) ℂ :=
  ∏ τ, (Matrix.of fun i j => (X (τ, i, j) : MvPolynomial (ι × Fin a × Fin a) ℂ)).det ^ n τ

theorem eval_genDetChar {a : ℕ} (n : ι → ℕ) (g : ι → Matrix (Fin a) (Fin a) ℂ) :
    eval (fun x : ι × Fin a × Fin a => g x.1 x.2.1 x.2.2) (genDetChar a n) = detChar n g := by
  rw [genDetChar, map_prod, detChar]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow, RingHom.map_det]
  congr 2
  ext i j
  simp

theorem colSub_eq_detChar_smul_of_mem_inv {a d : ℕ} (n : ι → ℕ) (P : Pol ι d a) (hP : P ∈ inv a d n)
    (g : ι → Matrix (Fin a) (Fin a) ℂ) : colSub g P = detChar n g • P := by
  set D : MvPolynomial (Var ι d a) (MvPolynomial (ι × Fin a × Fin a) ℂ) :=
    genColSub d a P - C (genDetChar a n) * map C P with hDdef
  have hD : ∀ g : ι → Matrix (Fin a) (Fin a) ℂ,
      map (eval fun x : ι × Fin a × Fin a => g x.1 x.2.1 x.2.2) D = colSub g P - detChar n g • P := by
    intro g
    rw [hDdef, map_sub, map_mul, map_C, map_eval_genColSub, eval_genDetChar, map_map, smul_eq_C_mul]
    congr 2
    have : (eval fun x : ι × Fin a × Fin a => g x.1 x.2.1 x.2.2).comp (C : ℂ →+* MvPolynomial (ι × Fin a × Fin a) ℂ) =
        RingHom.id ℂ := by ext; simp
    rw [this, map_id]
  have hD0 : D = 0 := by
    refine MvPolynomial.ext _ _ fun m => ?_
    simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    refine Formalism.L2.Col.eq_zero_of_forall_unitary (ι := ι) (n := a) (fun _ => 1) (fun _ => by simp) _ fun u hu => ?_
    simp only [Matrix.one_mul]
    rw [← coeff_map, hD u]
    have hu' : ∀ τ, u τ ∈ Matrix.unitaryGroup (Fin a) ℂ := fun τ =>
      Matrix.mem_unitaryGroup_iff'.mpr (by simpa [Matrix.star_eq_conjTranspose] using hu τ)
    have := hP (fun τ => ⟨u τ, hu' τ⟩)
    simp only at this
    simp only [this, sub_self, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  have := hD g
  rw [hD0, _root_.map_zero] at this
  exact (sub_eq_zero.mp this.symm)

end GlobalTheory.MinorFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDetCharInvariantsRowSubstitutionIrreducible
noncomputable section
open MvPolynomial
namespace GlobalTheory.MinorFrame.RowIrr
open GlobalTheory.MinorFrame
variable {ι : Type} [Fintype ι]

theorem exists_unitary_eval_ne {a d : ℕ} (h : a ≤ d) (P : Pol ι d a) (hP : P ≠ 0) :
    ∃ κ : ι → Matrix.unitaryGroup (Fin d) ℂ,
      eval (basePt ι d a) (rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P) ≠ 0 := by
  by_contra hall
  push_neg at hall
  apply hP
  let f : Var ι d a → MvPolynomial (ι × Fin d × Fin d) ℂ := fun y => X (y.1, Fin.castLE h y.2.2, y.2.1)
  have key : ∀ (Q : Pol ι d a) (w : ι × Fin d × Fin d → ℂ),
      eval w (aeval f Q) = eval (fun y => eval w (f y)) Q := by
    intro Q w
    induction Q using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p y hp => simp only [map_mul, hp, aeval_X, eval_X]
  have hF0 : aeval f P = 0 := by
    refine Formalism.L2.Col.eq_zero_of_forall_unitary (ι := ι) (n := d) (fun _ => 1) (fun _ => by simp) _ fun u hu => ?_
    simp only [Matrix.one_mul]
    rw [key]
    have hu' : ∀ τ, u τ ∈ Matrix.unitaryGroup (Fin d) ℂ := fun τ =>
      Matrix.mem_unitaryGroup_iff'.mpr (by simpa [Matrix.star_eq_conjTranspose] using hu τ)
    have := hall (fun τ => ⟨u τ, hu' τ⟩)
    rw [eval_rowSub] at this
    refine (congrArg (fun F => eval F P) (funext fun y => ?_)).trans this
    simp only [f, eval_X]
    rw [Finset.sum_eq_single (Fin.castLE h y.2.2)]
    · simp [basePt]
    · intro b _ hb
      have : (b : ℕ) ≠ (y.2.2 : ℕ) := fun e => hb (Fin.ext (by simpa using e))
      simp [basePt, this]
    · simp
  refine MvPolynomial.funext fun z => ?_
  let w : ι × Fin d × Fin d → ℂ := fun x => if hr : (x.2.1 : ℕ) < a then z (x.1, x.2.2, ⟨x.2.1, hr⟩) else 0
  have := key P w
  rw [hF0, map_zero] at this
  rw [map_zero, this]
  exact congrArg (fun F => eval F P) (funext fun y => by simp [f, w])

theorem rowSub_lowScal_X {d a : ℕ} (t : ℂ) (y : Var ι d a) :
    (∑ i' : Fin d, C (lowScal d a t i' y.2.1) * (X (y.1, i', y.2.2) : Pol ι d a)) =
      C (if (y.2.1 : ℕ) < a then 1 else t) * X y := by
  obtain ⟨τ, i, j⟩ := y
  rw [Finset.sum_eq_single i]
  · simp [lowScal]
  · intro b _ hb
    simp [lowScal, Matrix.diagonal_apply_ne _ hb]
  · simp

def lowDeg {d a : ℕ} (s : Var ι d a →₀ ℕ) : ℕ := s.sum fun y e => if (y.2.1 : ℕ) < a then 0 else e

theorem rowSub_lowScal_monomial {d a : ℕ} (t : ℂ) (s : Var ι d a →₀ ℕ) (c : ℂ) :
    rowSub (fun _ => lowScal d a t) (monomial s c : Pol ι d a) = monomial s (c * t ^ lowDeg s) := by
  unfold rowSub
  rw [aeval_monomial]
  simp only [rowSub_lowScal_X, mul_pow, Finsupp.prod_mul]
  have h1 : (s.prod fun y k => (C (if (y.2.1 : ℕ) < a then 1 else t) : Pol ι d a) ^ k) = C (t ^ lowDeg s) := by
    unfold Finsupp.prod lowDeg Finsupp.sum
    rw [← Finset.prod_pow_eq_pow_sum, map_prod]
    refine Finset.prod_congr rfl fun y _ => ?_
    beta_reduce
    split_ifs <;> simp
  rw [h1, ← monomial_eq, algebraMap_eq, C_mul_monomial]

theorem lowDeg_le {d a : ℕ} (s : Var ι d a →₀ ℕ) : lowDeg s ≤ s.sum fun _ e => e := by
  unfold lowDeg Finsupp.sum
  exact Finset.sum_le_sum fun y _ => by beta_reduce; split_ifs <;> omega

theorem lowScal_mem_unitary {d a : ℕ} {t : ℂ} (ht : ‖t‖ = 1) : lowScal d a t ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  rw [lowScal, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases hi : (i : ℕ) < a
  · simp [hi]
  · simp only [Pi.star_apply, hi, if_false, RCLike.star_def]
    rw [Complex.conj_mul', ht]; simp

theorem rowSub_lowScal_zero_mem {a d : ℕ} (S : Submodule ℂ (Pol ι d a))
    (hS : ∀ (κ : ι → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ S, rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P ∈ S)
    (P : Pol ι d a) (hP : P ∈ S) : rowSub (fun _ => lowScal d a 0) P ∈ S := by
  set M := P.totalDegree + 1 with hMdef
  have hM : M ≠ 0 := by omega
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / M)
  have hω : IsPrimitiveRoot ω M := Complex.isPrimitiveRoot_exp M hM
  have hωn : ∀ k : ℕ, ‖ω ^ k‖ = 1 := fun k => by rw [norm_pow, hω.norm'_eq_one hM, one_pow]
  have heq : rowSub (fun _ => lowScal d a 0) P =
      ∑ k ∈ Finset.range M, (M : ℂ)⁻¹ • rowSub (fun _ => lowScal d a (ω ^ k)) P := by
    conv_lhs => rw [as_sum P]
    conv_rhs => rw [as_sum P]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, rowSub_lowScal_monomial, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s hs => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_congr rfl (fun x _ => by rw [smul_monomial]), ← map_sum]
    congr 1
    have hb : lowDeg s < M := lt_of_le_of_lt (lowDeg_le s) (by have := le_totalDegree hs; omega)
    have hx : ∀ x : ℕ, (ω ^ x) ^ lowDeg s = (ω ^ lowDeg s) ^ x := fun x => by rw [← pow_mul, ← pow_mul, mul_comm]
    simp_rw [hx, smul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM
    by_cases hb0 : lowDeg s = 0
    · simp only [hb0, pow_zero, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      field_simp
    · have hne : ω ^ lowDeg s ≠ 1 := hω.pow_ne_one_of_pos_of_lt hb0 hb
      rw [geom_sum_eq hne, show (ω ^ lowDeg s) ^ M = 1 by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow],
        sub_self, zero_div, zero_pow hb0]
      simp
  rw [heq]
  refine S.sum_mem fun k _ => S.smul_mem _ ?_
  exact hS (fun _ => ⟨lowScal d a (ω ^ k), lowScal_mem_unitary (hωn k)⟩) P hP

theorem rowSub_lowScal_zero_of_mem_inv {a d : ℕ} (h : a ≤ d) (n : ι → ℕ) (P : Pol ι d a) (hP : P ∈ inv a d n) :
    rowSub (fun _ => lowScal d a 0) P = eval (basePt ι d a) P • topMinors h n := by
  refine MvPolynomial.funext fun z => ?_
  let g : ι → Matrix (Fin a) (Fin a) ℂ := fun τ => Matrix.of fun i j => z (τ, Fin.castLE h i, j)
  have hc := congrArg (eval (basePt ι d a)) (colSub_eq_detChar_smul_of_mem_inv n P hP g)
  rw [eval_colSub, smul_eq_C_mul, map_mul, eval_C] at hc
  have hv : eval z (topMinors h n) = detChar n g := by
    have hm : ∀ τ, (RingHom.mapMatrix (eval z))
        (Matrix.of fun i i' : Fin a => (X (τ, (topRows h).1 i, i') : Pol ι d a)) = g τ := fun τ => by
      ext i j; simp [g, topRows]
    simp only [topMinors, prodMinors, minorAt, map_prod, map_pow, RingHom.map_det, hm, detChar, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  have hpt : (fun y : Var ι d a => ∑ i' : Fin d, lowScal d a 0 i' y.2.1 * z (y.1, i', y.2.2)) =
      fun y => ∑ j' : Fin a, g y.1 j' y.2.2 * basePt ι d a (y.1, y.2.1, j') := by
    funext y
    rw [Finset.sum_eq_single y.2.1 (fun b _ hb => by simp [lowScal, Matrix.diagonal_apply_ne _ hb]) (by simp)]
    by_cases hy : (y.2.1 : ℕ) < a
    · rw [Finset.sum_eq_single ⟨y.2.1, hy⟩]
      · simp [lowScal, hy, g, basePt]
      · intro b _ hb
        have : (y.2.1 : ℕ) ≠ (b : ℕ) := fun e => hb (Fin.ext e.symm)
        simp [basePt, this]
      · simp
    · rw [Finset.sum_eq_zero]
      · simp [lowScal, hy]
      · intro b _
        have : (y.2.1 : ℕ) ≠ (b : ℕ) := fun e => hy (e ▸ b.2)
        simp [basePt, this]
  rw [eval_rowSub, hpt, hc, smul_eq_C_mul, map_mul, eval_C, hv, mul_comm]

theorem exists_fockS_orth {σ : Type} (V N : Submodule ℂ (MvPolynomial σ ℂ)) [FiniteDimensional ℂ V] (hNV : N < V) :
    ∃ Q ∈ V, Q ≠ 0 ∧ ∀ P ∈ N, Formalism.L2.DIV.fockS P Q = 0 := by
  classical
  haveI : FiniteDimensional ℂ N := Submodule.finiteDimensional_of_le hNV.le
  have hlt : Module.finrank ℂ N < Module.finrank ℂ V := Submodule.finrank_lt_finrank_of_lt hNV
  let b := Module.finBasis ℂ N
  let L : V →ₗ[ℂ] (Fin (Module.finrank ℂ N) → ℂ) :=
    LinearMap.pi fun i => (Formalism.L2.DIV.fockL ((b i : N) : MvPolynomial σ ℂ)).comp V.subtype
  have hker : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hlt)
  obtain ⟨Q, hQ, hQ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨Q, Q.2, fun h => hQ0 (Subtype.ext h), fun P hP => ?_⟩
  have hQi : ∀ i, Formalism.L2.DIV.fockS ((b i : N) : MvPolynomial σ ℂ) Q = 0 := fun i => by
    have := congrFun (LinearMap.mem_ker.mp hQ) i
    simpa [L, Formalism.L2.DIV.fockL_apply] using this
  have hsum := b.sum_repr ⟨P, hP⟩
  have hPe : P = ∑ i, (b.repr ⟨P, hP⟩ i) • ((b i : N) : MvPolynomial σ ℂ) := by
    have := congrArg Subtype.val hsum
    rw [Submodule.coe_sum] at this
    simp only [Submodule.coe_smul] at this
    exact this.symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hPe, ← Formalism.L2.DIV.fockL_apply, map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, Formalism.L2.DIV.fockL_apply, hQi i, smul_zero]

theorem inv_finiteDimensional (a d : ℕ) (n : ι → ℕ) : FiniteDimensional ℂ (inv (ι := ι) a d n) := by
  classical
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range (prodMinors (ι := ι) (a := a) (d := d) (n := n)))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  exact Submodule.finiteDimensional_of_le (inv_le_span_prodMinors a d n)

theorem topMinors_mem {a d : ℕ} (h : a ≤ d) (n : ι → ℕ) (S : Submodule ℂ (Pol ι d a)) (hSI : S ≤ inv a d n)
    (hS : ∀ (κ : ι → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ S, rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P ∈ S)
    (hS0 : S ≠ ⊥) : topMinors h n ∈ S := by
  obtain ⟨P, hPS, hP0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  obtain ⟨κ, hκ⟩ := exists_unitary_eval_ne h P hP0
  set P' := rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P
  have h1 : rowSub (fun _ => lowScal d a 0) P' ∈ S := rowSub_lowScal_zero_mem S hS P' (hS κ P hPS)
  rw [rowSub_lowScal_zero_of_mem_inv h n P' (hSI (hS κ P hPS))] at h1
  have := S.smul_mem (eval (basePt ι d a) P')⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hκ, one_smul] at this

end GlobalTheory.MinorFrame.RowIrr

end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.MinorFrame.RowIrr

theorem inv_irreducible : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ), a ≤ d →
    ∀ N : Submodule ℂ (GlobalTheory.MinorFrame.Pol ι d a), N ≤ GlobalTheory.MinorFrame.inv (ι := ι) a d n →
    (∀ (κ : ι → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ N, GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P ∈ N) →
    N = ⊥ ∨ N = GlobalTheory.MinorFrame.inv (ι := ι) a d n := by
  intro ι _ a d n h N hNI hN
  by_cases hN0 : N = ⊥
  · exact Or.inl hN0
  refine Or.inr ?_
  by_contra hne
  haveI := inv_finiteDimensional (ι := ι) a d n
  obtain ⟨Q, hQI, hQ0, hQN⟩ := exists_fockS_orth (inv a d n) N (lt_of_le_of_ne hNI hne)
  let M : Submodule ℂ (GlobalTheory.MinorFrame.Pol ι d a) :=
    { carrier := {R | R ∈ GlobalTheory.MinorFrame.inv a d n ∧ ∀ P ∈ N, Formalism.L2.DIV.fockS P R = 0}
      add_mem' := fun {R R'} hR hR' => ⟨(GlobalTheory.MinorFrame.inv a d n).add_mem hR.1 hR'.1, fun P hP => by
        rw [← Formalism.L2.DIV.fockL_apply, map_add (f := _), Formalism.L2.DIV.fockL_apply, Formalism.L2.DIV.fockL_apply, hR.2 P hP, hR'.2 P hP,
          add_zero]⟩
      zero_mem' := ⟨(GlobalTheory.MinorFrame.inv a d n).zero_mem, fun P _ => by
        rw [← Formalism.L2.DIV.fockL_apply, map_zero]⟩
      smul_mem' := fun c {R} hR => ⟨(GlobalTheory.MinorFrame.inv a d n).smul_mem c hR.1, fun P hP => by
        rw [← Formalism.L2.DIV.fockL_apply, map_smul, Formalism.L2.DIV.fockL_apply, hR.2 P hP, smul_zero]⟩ }
  have hMI : M ≤ GlobalTheory.MinorFrame.inv a d n := fun R hR => hR.1
  have hMs : ∀ (κ : ι → Matrix.unitaryGroup (Fin d) ℂ), ∀ R ∈ M,
      GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) R ∈ M := by
    intro κ R hR
    refine ⟨GlobalTheory.MinorFrame.rowSub_mem_inv _ hR.1, fun P hP => ?_⟩
    have hP' : P = GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ))
        (GlobalTheory.MinorFrame.rowSub (fun τ => ((star (κ τ) : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)) P) := by
      rw [rowSub_rowSub]
      have : (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ) * ((star (κ τ) : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)) =
          fun _ => 1 := by
        funext τ
        exact Unitary.mul_star_self_of_mem (κ τ).2
      rw [this, rowSub_one]
    rw [hP', GlobalTheory.MinorFrame.fockS_rowSub_unitary]
    exact hR.2 _ (hN (fun τ => star (κ τ)) P hP)
  have hM0 : M ≠ ⊥ := by
    intro hM
    apply hQ0
    have : Q ∈ M := ⟨hQI, hQN⟩
    rw [hM] at this
    exact (Submodule.mem_bot ℂ).1 this
  have h1 := topMinors_mem h n N hNI hN hN0
  have h2 := topMinors_mem h n M hMI hMs hM0
  have h3 := h2.2 _ h1
  have := GlobalTheory.MinorFrame.fockS_self_re_pos (topMinors_ne_zero (ι := ι) h n)
  rw [h3] at this
  simp at this

end GlobalTheory.MinorFrame.RowIrr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDetCharInvariantsRowSubstitutionIrreducibleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockDetCharInvariants_rowSubstitution_irreducible : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ), a ≤ d →
    ∀ N : Submodule ℂ (GlobalTheory.MinorFrame.Pol ι d a), N ≤ GlobalTheory.MinorFrame.inv (ι := ι) a d n →
    (∀ (κ : ι → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ N, GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P ∈ N) →
    N = ⊥ ∨ N = GlobalTheory.MinorFrame.inv (ι := ι) a d n := by
  first | exact @GlobalTheory.MinorFrame.RowIrr.inv_irreducible | exact GlobalTheory.MinorFrame.RowIrr.inv_irreducible | (intros; apply GlobalTheory.MinorFrame.RowIrr.inv_irreducible <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealQuotientMinorEqConstSmulComplementMinor
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SchurQuot

open GlobalTheory.MinorFrame

theorem map_conj_mem_unitaryGroup {d : ℕ} (A : Matrix.unitaryGroup (Fin d) ℂ) :
    (A : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ) ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h := Matrix.mem_unitaryGroup_iff.1 A.2
  calc (A : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ) * star ((A : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ))
        = ((A : Matrix (Fin d) (Fin d) ℂ) * star (A : Matrix (Fin d) (Fin d) ℂ)).transpose := by
          ext i j
          simp only [Matrix.transpose_apply, Matrix.mul_apply, Matrix.star_apply, Matrix.map_apply, RCLike.star_def,
            Complex.conj_conj]
          exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    _ = 1 := by rw [h, Matrix.transpose_one]

variable {ι : Type} [Fintype ι]

def conjFam {d : ℕ} (κ : ι → Matrix.unitaryGroup (Fin d) ℂ) : ι → Matrix.unitaryGroup (Fin d) ℂ :=
  fun τ => ⟨(κ τ : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ), map_conj_mem_unitaryGroup (κ τ)⟩

theorem conjFam_map {d : ℕ} (κ : ι → Matrix.unitaryGroup (Fin d) ℂ) :
    (fun τ => ((conjFam κ τ : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ)) =
      fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ) := by
  funext τ
  ext i j
  simp [conjFam]

theorem detChar_unitary_ne_zero {d : ℕ} (n : ι → ℕ) (κ : ι → Matrix.unitaryGroup (Fin d) ℂ) :
    detChar n (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) ≠ 0 := by
  unfold detChar
  refine Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ ?_
  have h := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff.1 (κ τ).2)
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact left_ne_zero_of_mul_eq_one h

theorem inv_inf_ker_stable {a d : ℕ} (n₀ : ι → ℕ) {Pr : Type} [AddCommGroup Pr] [Module ℂ Pr]
    (h : Pol ι d a →ₗ[ℂ] Pr) (σ : (ι → Matrix (Fin d) (Fin d) ℂ) → Module.End ℂ Pr)
    (hh : ∀ (κ : ι → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ inv (ι := ι) a d n₀,
      h (rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ)) P) = σ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) (h P))
    (κ : ι → Matrix.unitaryGroup (Fin d) ℂ) :
    ∀ P ∈ inv (ι := ι) a d n₀ ⊓ LinearMap.ker h, rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P ∈ inv (ι := ι) a d n₀ ⊓ LinearMap.ker h := by
  intro P hP
  obtain ⟨hPV, hPk⟩ := Submodule.mem_inf.1 hP
  refine Submodule.mem_inf.2 ⟨rowSub_mem_inv _ hPV, ?_⟩
  rw [LinearMap.mem_ker] at hPk ⊢
  have := hh (conjFam κ) P hPV
  rw [conjFam_map] at this
  rw [this, hPk, map_zero]

end GlobalTheory.SchurQuot

namespace GlobalTheory.SchurQuot

open GlobalTheory.MinorFrame

variable {ι : Type} [Fintype ι]

theorem quot_eq_zero_of_weight_ne {a d : ℕ} (ha : 0 < a) {n n₀ : ι → ℕ} (hn : n ≠ n₀) {Pr : Type} [AddCommGroup Pr]
    [Module ℂ Pr] (q : Pol ι d a →ₗ[ℂ] Pr)
    (hq : ∀ (g : ι → Matrix.unitaryGroup (Fin a) ℂ) (P : Pol ι d a),
      q (colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P) = detChar n₀ (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • q P)
    {P : Pol ι d a} (hP : ∀ g : ι → Matrix (Fin a) (Fin a) ℂ, colSub g P = detChar n g • P) : q P = 0 := by
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_unitary_detPowCharacter_separates_weights a ha n n₀ hn
  have h1 := hq g P
  rw [hP, map_smul] at h1
  have h2 : (detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) - detChar n₀ (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ))) • q P = 0 := by
    rw [sub_smul, h1, sub_self]
  exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hg)

theorem finiteDimensional_inv (a d : ℕ) (n : ι → ℕ) : FiniteDimensional ℂ (inv (ι := ι) a d n) := by
  have hfin : (Set.range (prodMinors (ι := ι) (a := a) (d := d) (n := n))).Finite := Set.finite_range _
  haveI := FiniteDimensional.span_of_finite ℂ hfin
  exact Submodule.finiteDimensional_of_le (GlobalTheory.MinorFrame.inv_le_span_prodMinors a d n)

theorem exists_const_of_equivariant {a d : ℕ} (had : a ≤ d) (n₀ : ι → ℕ) (Pr : Type) [AddCommGroup Pr] [Module ℂ Pr]
    (q F : Pol ι d a →ₗ[ℂ] Pr) (σ : (ι → Matrix (Fin d) (Fin d) ℂ) → Module.End ℂ Pr) [Nontrivial Pr]
    (hqs : Function.Surjective q)
    (hq : ∀ (g : ι → Matrix.unitaryGroup (Fin a) ℂ) (P : Pol ι d a),
      q (colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P) = detChar n₀ (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • q P)
    (hqσ : ∀ (κ : ι → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ inv (ι := ι) a d n₀,
      q (rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ)) P) = σ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) (q P))
    (hFσ : ∀ (κ : ι → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ inv (ι := ι) a d n₀,
      F (rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ)) P) = σ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) (F P))
    (hF : ∃ P ∈ inv (ι := ι) a d n₀, F P ≠ 0) :
    ∃ ρ : ℂ, ρ ≠ 0 ∧ ∀ P ∈ inv (ι := ι) a d n₀, F P = ρ • q P := by
  set V := inv (ι := ι) a d n₀ with hV

  have havg := GlobalTheory.T.exists_detCharInvariant_same_value_twisted a d n₀ Pr q hq
  have hsurj : Function.Surjective (q ∘ₗ V.subtype) := by
    intro x
    obtain ⟨P, rfl⟩ := hqs x
    obtain ⟨P₀, hP₀, he⟩ := havg P
    exact ⟨⟨P₀, hP₀⟩, he.symm⟩

  have hker := GlobalTheory.T.fockDetCharInvariants_rowSubstitution_irreducible a d n₀ had (V ⊓ LinearMap.ker q) inf_le_left
    (inv_inf_ker_stable n₀ q σ hqσ)
  have hinj : Function.Injective (q ∘ₗ V.subtype) := by
    rcases hker with h0 | hV'
    · rw [← LinearMap.ker_eq_bot]
      rw [eq_bot_iff] at h0 ⊢
      intro P hP
      have h' := h0 (Submodule.mem_inf.2 ⟨P.2, hP⟩)
      exact (Submodule.mem_bot ℂ).2 (Subtype.ext ((Submodule.mem_bot ℂ).1 h'))
    · exfalso
      obtain ⟨x, hx⟩ := exists_ne (0 : Pr)
      obtain ⟨P, hP⟩ := hsurj x
      have : (P : Pol ι d a) ∈ V ⊓ LinearMap.ker q := by rw [hV']; exact P.2
      exact hx (hP.symm.trans (LinearMap.mem_ker.1 (Submodule.mem_inf.1 this).2))
  let e : V ≃ₗ[ℂ] Pr := LinearEquiv.ofBijective (q ∘ₗ V.subtype) ⟨hinj, hsurj⟩
  haveI : FiniteDimensional ℂ V := finiteDimensional_inv a d n₀
  haveI : Nontrivial V := e.toEquiv.nontrivial
  let E : Module.End ℂ V := e.symm.toLinearMap ∘ₗ F ∘ₗ V.subtype
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue E
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hEv : E v = c • v := hv.apply_eq_smul
  have hFv : F v = c • q v := by
    have h1 : e (E v) = F v := by simp [E]
    have h2 : e (c • v) = c • q v := by rw [map_smul]; rfl
    rw [← h1, hEv, h2]

  have hFc : ∀ (κ : ι → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ V,
      (F - c • q) (rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ)) P) =
        σ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) ((F - c • q) P) := by
    intro κ P hP
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, hFσ κ P hP, hqσ κ P hP]
  have hker2 := GlobalTheory.T.fockDetCharInvariants_rowSubstitution_irreducible a d n₀ had (V ⊓ LinearMap.ker (F - c • q)) inf_le_left
    (inv_inf_ker_stable n₀ (F - c • q) σ hFc)
  have hall : ∀ P ∈ V, F P = c • q P := by
    rcases hker2 with h0 | hV'
    · exfalso
      have : (v : Pol ι d a) ∈ V ⊓ LinearMap.ker (F - c • q) := by
        refine Submodule.mem_inf.2 ⟨v.2, ?_⟩
        rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero]
        exact hFv
      have h' : (v : Pol ι d a) ∈ (⊥ : Submodule ℂ (Pol ι d a)) := h0 ▸ this
      exact hv.2 (Subtype.ext ((Submodule.mem_bot ℂ).1 h'))
    · intro P hP
      have : P ∈ V ⊓ LinearMap.ker (F - c • q) := by rw [hV']; exact hP
      have := LinearMap.mem_ker.1 (Submodule.mem_inf.1 this).2
      rw [LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero] at this
      exact this
  refine ⟨c, ?_, hall⟩
  rintro rfl
  obtain ⟨P, hP, hFP⟩ := hF
  exact hFP (by rw [hall P hP, zero_smul])

end GlobalTheory.SchurQuot

namespace GlobalTheory.SchurQuot

open GlobalTheory.MinorFrame

theorem minorF_eq_prodMinors (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n) :
    GlobalTheory.BotFormula.minorF rfl rfl T = prodMinors (ι := D.what₂.Tau) (n := n) T := by
  unfold GlobalTheory.BotFormula.minorF GlobalTheory.NormSum.minorPol prodMinors minorAt
  rw [show (fun k : D.what₂.Tau × Fin d × Fin a => (k.1, Fin.cast rfl k.2.1, Fin.cast rfl k.2.2)) = id from
    funext fun k => rfl, MvPolynomial.rename_id]
  rfl

theorem quot_minor_eq_const_smul_compl : ∀ (D : D7) {a a' d : ℕ} (had : a + a' = d) (n₀ : D.what₂.Tau → ℕ) (Pr : Type) [AddCommGroup Pr] [Module ℂ Pr]
    (q : PolF D d a →ₗ[ℂ] Pr) (q' : PolF D d a' →ₗ[ℂ] Pr) (σ : (D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ) → Module.End ℂ Pr),
    0 < a → 0 < a' → Nontrivial Pr → Function.Surjective q → Function.Surjective q' →
    (∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin a) ℂ) (P : PolF D d a),
      q (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P) = GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • q P) →
    (∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin a') ℂ) (P : PolF D d a'),
      q' (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin a') (Fin a') ℂ)) P) = GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin a') (Fin a') ℂ)) • q' P) →
    (∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) a d n₀,
      q (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ)) P) = σ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) (q P)) →
    (∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) a' d n₀,
      q' (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) • σ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) (q' P)) →
    ∃ ρ : ℂ, ρ ≠ 0 ∧ ∀ (n : D.what₂.Tau → ℕ) (T : Tup D a d n), ∃ ε : ℤˣ,
      q (GlobalTheory.BotFormula.minorF rfl rfl T) = (ρ * ((ε : ℤ) : ℂ)) • q' (GlobalTheory.BotFormula.minorF rfl rfl (GlobalTheory.BotMatch.complTup D had T)) := by
  intro D a a' d had n₀ Pr _ _ q q' σ ha ha' hPr hqs hq's hq hq' hqσ hq'σ
  obtain ⟨Pl, ε, hPlT, hPlκ⟩ := GlobalTheory.T.exists_complementaryMinor_map_realPlaces D had n₀

  have hPlV : ∀ P ∈ inv (ι := D.what₂.Tau) a d n₀, Pl P ∈ inv (ι := D.what₂.Tau) a' d n₀ := by
    intro P hP
    have hle : Submodule.span ℂ (Set.range (prodMinors (ι := D.what₂.Tau) (a := a) (d := d) (n := n₀))) ≤
        (inv (ι := D.what₂.Tau) a' d n₀).comap Pl := by
      rw [Submodule.span_le]
      rintro _ ⟨T, rfl⟩
      show Pl (prodMinors T) ∈ inv (ι := D.what₂.Tau) a' d n₀
      have h := hPlT T
      rw [minorF_eq_prodMinors, minorF_eq_prodMinors] at h
      rw [h]
      exact Submodule.smul_mem _ _ (prodMinors_mem_inv _)
    exact hle (GlobalTheory.MinorFrame.inv_le_span_prodMinors a d n₀ hP)
  let F : PolF D d a →ₗ[ℂ] Pr := q' ∘ₗ Pl
  have hFσ : ∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ inv (ι := D.what₂.Tau) a d n₀,
      F (rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ)) P) =
        σ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) (F P) := by
    intro κ P hP
    simp only [F, LinearMap.comp_apply]
    rw [hPlκ κ P hP, map_smul, hq'σ κ (Pl P) (hPlV P hP), smul_smul,
      inv_mul_cancel₀ (detChar_unitary_ne_zero n₀ κ), one_smul]

  have hF : ∃ P ∈ inv (ι := D.what₂.Tau) a d n₀, F P ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨x, hx⟩ := exists_ne (0 : Pr)
    obtain ⟨P', rfl⟩ := hq's x
    obtain ⟨P₀, hP₀, he⟩ := GlobalTheory.T.exists_detCharInvariant_same_value_twisted a' d n₀ Pr q' hq' P'
    apply hx
    rw [he]
    have hle : Submodule.span ℂ (Set.range (prodMinors (ι := D.what₂.Tau) (a := a') (d := d) (n := n₀))) ≤
        LinearMap.ker q' := by
      rw [Submodule.span_le]
      rintro _ ⟨T', rfl⟩
      obtain ⟨T, rfl⟩ := (GlobalTheory.BotMatch.complTup_bijective D had).2 T'
      have h0 := hcon (prodMinors T) (prodMinors_mem_inv T)
      have h := hPlT T
      rw [minorF_eq_prodMinors, minorF_eq_prodMinors] at h
      simp only [F, LinearMap.comp_apply, h, map_smul] at h0
      show q' (prodMinors (GlobalTheory.BotMatch.complTup D had T)) = 0
      have hε : ((ε T : ℤ) : ℂ) ≠ 0 := by
        rcases Int.units_eq_one_or (ε T) with h1 | h1 <;> simp [h1]
      exact (smul_eq_zero.1 h0).resolve_left hε
    exact hle (GlobalTheory.MinorFrame.inv_le_span_prodMinors a' d n₀ hP₀)
  obtain ⟨ρ, hρ, hFq⟩ := exists_const_of_equivariant (by omega) n₀ Pr q F σ hqs hq hqσ hFσ hF
  refine ⟨ρ⁻¹, inv_ne_zero hρ, fun n T => ?_⟩
  by_cases hn : n = n₀
  · subst hn
    refine ⟨ε T, ?_⟩
    have h := hFq (prodMinors T) (prodMinors_mem_inv T)
    have hT := hPlT T
    rw [minorF_eq_prodMinors, minorF_eq_prodMinors] at hT ⊢
    simp only [F, LinearMap.comp_apply, hT, map_smul] at h
    rw [mul_smul, h, smul_smul, inv_mul_cancel₀ hρ, one_smul]
  · refine ⟨1, ?_⟩
    rw [minorF_eq_prodMinors, minorF_eq_prodMinors]
    rw [quot_eq_zero_of_weight_ne ha hn q hq (fun g => colSub_prodMinors g T),
      quot_eq_zero_of_weight_ne ha' hn q' hq' (fun g => colSub_prodMinors g _), smul_zero]

end GlobalTheory.SchurQuot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealQuotientMinorEqConstSmulComplementMinorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realQuotient_minor_eq_const_smul_complementMinor : ∀ (D : D7) {a a' d : ℕ} (had : a + a' = d) (n₀ : D.what₂.Tau → ℕ) (Pr : Type) [AddCommGroup Pr] [Module ℂ Pr]
    (q : PolF D d a →ₗ[ℂ] Pr) (q' : PolF D d a' →ₗ[ℂ] Pr) (σ : (D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ) → Module.End ℂ Pr),
    0 < a → 0 < a' → Nontrivial Pr → Function.Surjective q → Function.Surjective q' →
    (∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin a) ℂ) (P : PolF D d a),
      q (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P) = GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • q P) →
    (∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin a') ℂ) (P : PolF D d a'),
      q' (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin a') (Fin a') ℂ)) P) = GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin a') (Fin a') ℂ)) • q' P) →
    (∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) a d n₀,
      q (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ)) P) = σ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) (q P)) →
    (∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) a' d n₀,
      q' (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) • σ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) (q' P)) →
    ∃ ρ : ℂ, ρ ≠ 0 ∧ ∀ (n : D.what₂.Tau → ℕ) (T : Tup D a d n), ∃ ε : ℤˣ,
      q (GlobalTheory.BotFormula.minorF rfl rfl T) = (ρ * ((ε : ℤ) : ℂ)) • q' (GlobalTheory.BotFormula.minorF rfl rfl (GlobalTheory.BotMatch.complTup D had T)) := by
  first | exact @GlobalTheory.SchurQuot.quot_minor_eq_const_smul_compl | exact GlobalTheory.SchurQuot.quot_minor_eq_const_smul_compl | (intros; apply GlobalTheory.SchurQuot.quot_minor_eq_const_smul_compl <;> assumption)
end
