module

public import Formalism.LocalToGlobal.HermitianForms.TiedBrRep
public import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.ClsSum

@[expose] public section

section -- merged from Formalism.LocalToGlobal.HermitianForms.TiedBrProof
section -- merged from Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LowerTieChain
open MvPolynomial

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br Formalism.GradedWeylDivisibility Formalism.REAL

section LcOne

open Formalism.BranchingDeterminantCap

variable {N n : ℕ} (hN : N = n + 1) (l : DomWeight N) (s : DomWeight n)

end LcOne

end Formalism.L2.Ker

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br Formalism.GradedWeylDivisibility Formalism.REAL

section LcTen

open Formalism.BranchingDeterminantCap

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def tSpan {n : ℕ} (V : ι → Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ)) :
    Submodule ℂ (MvPolynomial (ι × Fin n × Fin n) ℂ) :=
  Submodule.span ℂ {p | ∃ f : ι → MvPolynomial (Fin n × Fin n) ℂ, (∀ τ, f τ ∈ V τ) ∧ p = Formalism.MainNotions.product_first_zeroth_parts.ten f}

theorem lc_blk_mem {n n' : ℕ} (A : ι → MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin n') ℂ)
    (V : ι → Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ)) (W : ι → Submodule ℂ (MvPolynomial (Fin n' × Fin n') ℂ))
    (hA : ∀ τ, ∀ F ∈ V τ, A τ F ∈ W τ) (x : MvPolynomial (ι × Fin n × Fin n) ℂ) (hx : x ∈ tSpan V) :
    Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => ⇑(A τ)) x ∈ tSpan W := by
  induction hx using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨f, hf, rfl⟩ := hp
    rw [Formalism.MainNotions.product_first_zeroth_parts.blk_ten]
    exact Submodule.subset_span ⟨_, fun τ => hA τ _ (hf τ), rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

end LcTen

end Formalism.L2.Ker

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br Formalism.GradedWeylDivisibility Formalism.REAL

section LcBr

open Formalism.BranchingDeterminantCap

variable {N n : ℕ} (hN : N = n + 1) (l : DomWeight N) (s : DomWeight n)

end LcBr

section LcBrTen

open Formalism.BranchingDeterminantCap

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N n : ℕ} (hN : N = n + 1) (l : ι → DomWeight N) (s : ι → DomWeight n)

end LcBrTen

section LcFrame

variable {N n : ℕ} (hN : N = n + 1) (l : DomWeight N) (s : DomWeight n)

end LcFrame

end Formalism.L2.Ker

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br Formalism.GradedWeylDivisibility Formalism.REAL

section LcFrameTen

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N n : ℕ} (hN : N = n + 1) (l : ι → DomWeight N) (s : ι → DomWeight n)

theorem lc_blk_sqAct_mem {k : ℕ} (m : ι → DomWeight k) (g : ι → GL (Fin k) ℂ) (p : MvPolynomial (ι × Fin k × Fin k) ℂ)
    (hp : p ∈ Formalism.MainNotions.product_first_zeroth_parts.CSpan m) : Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => sqAct ℂ k (m τ) (g τ)) p ∈ Formalism.MainNotions.product_first_zeroth_parts.CSpan m := by
  have e : (fun τ => sqAct ℂ k (m τ) (g τ)) = fun τ => ⇑(ta_sqActL (m τ) (g τ)) :=
    funext fun τ => (ta_sqActL_coe _ _).symm
  rw [e]
  exact lc_blk_mem (fun τ => ta_sqActL (m τ) (g τ)) (fun τ => delSq ℂ k (m τ)) (fun τ => delSq ℂ k (m τ))
    (fun τ F hF => by rw [ta_sqActL_coe]; exact eps_sqAct_mem k (m τ) (g τ) F hF) p hp

end LcFrameTen

section LcRec

open Formalism.MainNotions.product_first_zeroth_parts

variable {D : Formalism.BasicNotions.D7} {u : D.what₂.Word}

end LcRec

end Formalism.L2.Ker

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br Formalism.GradedWeylDivisibility Formalism.REAL

section LcLog

open Formalism.MainNotions.product_first_zeroth_parts

variable {D : Formalism.BasicNotions.D7} {u : D.what₂.Word}

end LcLog

end Formalism.L2.Ker
end
end

section -- merged from Formalism.LocalToGlobal.HermitianForms.TiedBrCl
section -- merged from Formalism.LocalToGlobal.HermitianForms.TiedBrCo
noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts

section Inv

variable {ι : Type} [Fintype ι] {n : ℕ}


open Classical in
def fnInv (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) (M : ι → Matrix (Fin n) (Fin n) ℂ) :
    (Frames G → ℂ) →ₗ[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ :=
  if h : ∀ τ, IsUnit (M τ).det then
    Classical.choose (LinearMap.exists_leftInverse_of_injective (fnOf G s M)
      (LinearMap.ker_eq_bot.mpr (fnOf_injective G s M h)))
  else 0

theorem fnInv_fnOf (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) (M : ι → Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ τ, IsUnit (M τ).det) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) : fnInv G s M (fnOf G s M P) = P := by
  classical
  unfold fnInv
  rw [dite_eq_left h]
  exact LinearMap.congr_fun (Classical.choose_spec (LinearMap.exists_leftInverse_of_injective (fnOf G s M)
      (LinearMap.ker_eq_bot.mpr (fnOf_injective G s M h)))) P

end Inv

variable {D : D7} {u : D.what₂.Word}

def bZg (u : D.what₂.Word) (z0 : Fin (D.R.N D.R.m) → D.host.E) (B' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) :
    Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E :=
  fun a b => if hb : (b : ℕ) < D.R.N D.R.m - 1 then (iXm D * B') a ⟨b, hb⟩ else z0 a / ((D.mem u).A.T : D.host.E)

end Formalism.L2.Forms
end
end

noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Matrix

theorem exists_change {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ)
    (M M' : ι → Matrix (Fin n) (Fin n) ℂ) (hM : ∀ τ, IsUnit (M τ).det) (P : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (hP : P ∈ CSpan lam) : ∃ Q ∈ CSpan lam, fnOf G s M' P = fnOf G s M Q := by
  refine ⟨_, ?_, fnOf_change G s M M' hM P⟩
  exact Submodule.smul_mem _ _ (blkRow_mem _ _ hP)

variable {D : D7} {u : D.what₂.Word}

theorem atInf_inv_isUnit {n : ℕ} (A : Matrix (Fin n) (Fin n) D.host.E) (hA : IsUnit A.det) (τ : D.what₂.Tau) :
    IsUnit (atInf (embT D) A⁻¹ τ).det := by
  unfold atInf
  have h := (Matrix.isUnit_nonsing_inv_det A hA).map (embT D τ)
  first
  | (rw [RingHom.map_det, RingHom.mapMatrix_apply] at h; exact h)
  | simpa [RingHom.map_det] using h
  | simpa [AlgHom.map_det] using h

variable (Tf : FormsTied D u)
  (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
  (hB : ∀ w c, IsUnit (B w c).det)

include hB


end Formalism.L2.Forms
end
end

noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Matrix MvPolynomial

section GlobalTheory

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem blkRow_ten (K : ι → Matrix (Fin n) (Fin n) ℂ) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    blkRow K (Formalism.MainNotions.product_first_zeroth_parts.ten f) = Formalism.MainNotions.product_first_zeroth_parts.ten (fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (K τ) (f τ)) := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.ten
  rw [map_prod]
  exact Finset.prod_congr rfl fun τ _ => blkRow_rename K τ (f τ)

theorem blkRow_eq_blk (K : ι → Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    blkRow K P = Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => ⇑((Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (K τ)).toLinearMap)) P := by
  have h : (blkRow K).toLinearMap = Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => ⇑((Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (K τ)).toLinearMap)) := by
    apply (MvPolynomial.basisMonomials (ι × Fin n × Fin n) ℂ).ext
    intro mon
    rw [MvPolynomial.coe_basisMonomials, Formalism.L2.Ker.ta_blk_monomial]
    have hm : (MvPolynomial.monomial mon (1 : ℂ)) = Formalism.MainNotions.product_first_zeroth_parts.ten fun τ => MvPolynomial.monomial
        (mon.comapDomain (Prod.mk τ) (Prod.mk_right_injective τ).injOn) (1 : ℂ) := by
      rw [Formalism.MainNotions.product_first_zeroth_parts.ten_monomial, Formalism.L2.Ker.ta_sum_map_comap]
    rw [AlgHom.toLinearMap_apply]
    dsimp only
    rw [hm, blkRow_ten]
    rfl
  exact LinearMap.congr_fun h P

end GlobalTheory

section GLBlk

theorem embGL_val {R : Type} [CommRing R] {n N : ℕ} (h : n + 1 = N) (G : GL (Fin n) R) :
    ((Formalism.MainNotions.PrimeDegreeVariant.embGL R n N h G : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) =
      Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (Matrix.fromBlocks (G : Matrix (Fin n) (Fin n) R) 0 0 (1 : Matrix (Fin 1) (Fin 1) R)) := rfl

theorem detPow_embGL {R : Type} [CommRing R] {n N : ℕ} (h : n + 1 = N) (G : GL (Fin n) R) (c : ℤ) :
    detPow R N (Formalism.MainNotions.PrimeDegreeVariant.embGL R n N h G) c = detPow R n G c := by
  unfold detPow
  congr 2
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, embGL_val, Matrix.det_reindex_self,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

theorem rowAct_tr_eq {k : ℕ} (l : DomWeight k) (G : GL (Fin k) ℂ) (f : MvPolynomial (Fin k × Fin k) ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := k) (G : Matrix (Fin k) (Fin k) ℂ).transpose f = (detPow ℂ k G l.detShift)⁻¹ • sqAct ℂ k l G f := by
  unfold sqAct
  rw [smul_smul, inv_mul_cancel₀ (by unfold detPow; exact Units.ne_zero _), one_smul]

theorem brOne_rowAct {N n : ℕ} (hN : N = n + 1) (l : DomWeight N) (s : DomWeight n)
    (hS : Formalism.L2.Col.Br.SameShift l s) (G : GL (Fin n) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    Formalism.L2.Ker.brOne ℂ hN l s (Formalism.GradedWeylDivisibility.rowAct ℂ (n := N)
              ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm G : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).transpose f) =
      Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (G : Matrix (Fin n) (Fin n) ℂ).transpose (Formalism.L2.Ker.brOne ℂ hN l s f) := by
  rw [rowAct_tr_eq l, rowAct_tr_eq s, map_smul, Formalism.L2.Ker.brOne_sqAct hN l s hS G f, detPow_embGL]
  rw [show s.detShift = l.detShift from hS]

end GLBlk

variable {D : D7} {u : D.what₂.Word}

def dgE (B' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) :
    Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E :=
  Matrix.reindex (finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (finSumFinEquiv.trans (finCongr (Nm_succ D.R)))
    (Matrix.fromBlocks B' 0 0 (1 : Matrix (Fin 1) (Fin 1) D.host.E))

theorem bZg_eq_mul (z0 : Fin (D.R.N D.R.m) → D.host.E) (B' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) :
    bZg u z0 B' = bZ u z0 * dgE B' := by
  ext a b
  obtain ⟨x, rfl⟩ := (finSumFinEquiv.trans (finCongr (Nm_succ D.R))).surjective b
  rw [Matrix.mul_apply, ← (finSumFinEquiv.trans (finCongr (Nm_succ D.R))).sum_comp, Fintype.sum_sum_type]
  rcases x with i | i
  · simp [bZg, bZ, dgE, Matrix.mul_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  · have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp [bZg, bZ, dgE, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem atInf_inv_inv {n : ℕ} (A : Matrix (Fin n) (Fin n) D.host.E) (hA : IsUnit A.det) (τ : D.what₂.Tau) :
    (atInf (embT D) A⁻¹ τ)⁻¹ = atInf (embT D) A τ := by
  apply Matrix.inv_eq_left_inv
  show A.map (embT D τ) * (A⁻¹).map (embT D τ) = 1
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hA, Matrix.map_one _ (map_zero _) (map_one _)]

def glT (B' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) (hB' : IsUnit B'.det) (τ : D.what₂.Tau) :
    GL (Fin (D.R.N D.R.m - 1)) ℂ :=
  Matrix.nonsingInvUnit ((B'.map (embT D τ)).transpose) (by
    rw [Matrix.det_transpose, show B'.map (embT D τ) = (embT D τ).mapMatrix B' from rfl, ← RingHom.map_det]
    exact hB'.map _)

theorem glT_val (B' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) (hB' : IsUnit B'.det) (τ : D.what₂.Tau) :
    ((glT B' hB' τ : GL (Fin (D.R.N D.R.m - 1)) ℂ) : Matrix _ _ ℂ) = (B'.map (embT D τ)).transpose := rfl

theorem embGL_glT (B' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) (hB' : IsUnit B'.det) (τ : D.what₂.Tau) :
    ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (glT B' hB' τ) : GL (Fin (D.R.N D.R.m)) ℂ) : Matrix _ _ ℂ).transpose =
      (dgE B').map (embT D τ) := by
  rw [embGL_val, Matrix.transpose_reindex, Matrix.fromBlocks_transpose, glT_val, Matrix.transpose_transpose,
    Matrix.transpose_zero, Matrix.transpose_zero, Matrix.transpose_one]
  unfold dgE
  rw [Matrix.reindex_apply, Matrix.reindex_apply, ← Matrix.submatrix_map, Matrix.fromBlocks_map,
    Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]

theorem blk_sqAct_eq {ι : Type} [Fintype ι] {n : ℕ} (l : ι → DomWeight n) (g : ι → GL (Fin n) ℂ)
    (Q : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => sqAct ℂ n (l τ) (g τ)) Q =
      (∏ τ, detPow ℂ n (g τ) (l τ).detShift) • blkRow (fun τ => (g τ : Matrix (Fin n) (Fin n) ℂ).transpose) Q := by
  have e : (fun τ => sqAct ℂ n (l τ) (g τ)) = fun τ => ⇑(detPow ℂ n (g τ) (l τ).detShift •
      (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g τ : Matrix (Fin n) (Fin n) ℂ).transpose).toLinearMap) :=
    funext fun τ => (Formalism.L2.Ker.ta_sqActL_coe _ _).symm
  rw [e, Formalism.L2.Ker.blk_smul, blkRow_eq_blk]
  rfl

theorem fnOf_sqAct {ι : Type} [Fintype ι] {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ) (l : ι → DomWeight n)
    (M o : ι → Matrix (Fin n) (Fin n) ℂ) (ho : ∀ τ, IsUnit (o τ).det) (g : ι → GL (Fin n) ℂ)
    (hg : ∀ τ, (g τ : Matrix (Fin n) (Fin n) ℂ) = (M τ * o τ).transpose) (Q : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    fnOf G (fun τ => (l τ).detShift) (fun τ => (o τ)⁻¹) (Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => sqAct ℂ n (l τ) (g τ)) Q) =
      fnOf G (fun τ => (l τ).detShift) M Q := by
  have hi : ∀ τ, IsUnit ((o τ)⁻¹).det := fun τ => Matrix.isUnit_nonsing_inv_det _ (ho τ)
  rw [fnOf_change G _ (fun τ => (o τ)⁻¹) M hi Q, blk_sqAct_eq]
  have hK : (fun τ => M τ * ((fun τ => (o τ)⁻¹) τ)⁻¹) = fun τ => (g τ : Matrix (Fin n) (Fin n) ℂ).transpose := by
    funext τ
    simp only [hg, Matrix.transpose_transpose, Matrix.nonsing_inv_nonsing_inv _ (ho τ)]
  rw [hK]
  congr 2
  refine Finset.prod_congr rfl fun τ _ => ?_
  unfold detPow
  rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, hg, Matrix.det_transpose,
    Matrix.nonsing_inv_nonsing_inv _ (ho τ)]

def gPof (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hB : ∀ w c, IsUnit (B w c).det) (o : FrP D) :
    D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ :=
  fun w c τ => Matrix.nonsingInvUnit ((atInf (embT D) (B w c)⁻¹ τ * o.1 τ).transpose) (by
    rw [Matrix.det_transpose, Matrix.det_mul]; exact (atInf_inv_isUnit _ (hB w c) τ).mul (o.2 τ))

theorem shift_sgTr (τ : D.what₂.Tau) : (sgTr D u τ).detShift = shiftOf (sgT u) τ := by
  have hk := D.R.m_add_three_le_k
  have hN : D.R.N D.R.m = D.R.k + D.R.m * (D.R.t + 1) := rfl
  have h2 : 0 < D.R.N D.R.m - 1 := by omega
  simp only [shiftOf, sgT, sgTr]
  rw [detShift_shW _ _ h2, detShift_wSh _ _ h2]
  rfl

theorem cspan_sgTr : Formalism.MainNotions.product_first_zeroth_parts.CSpan (sgTr D u) = Formalism.MainNotions.product_first_zeroth_parts.CSpan (D.fm u).sg := by
  simp only [Formalism.MainNotions.product_first_zeroth_parts.CSpan, sgTr, delSq_wSh]

end Formalism.L2.Forms
end
end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix MvPolynomial NumberField

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem beOn_closedS (Tf : FormsTiedSym D u Ch chOf) (h : Formalism.L2.Ker.BeOnTie D u) (τ : D.what₂.Tau) :
    (D.fm u).beOn τ = Formalism.L2.Ker.beOnVal (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) := by
  rw [h τ]
  exact Formalism.L2.Ker.beOnEq D u τ (interlaceTr D u (sg_interlace Tf.valP) τ)

def LowerMapTieSym (Tf : FormsTiedSym D u Ch chOf) : Prop :=
  IsUnit (bZ u Tf.til.z0).det → ∀ (ψ : (D.mem u).P.Wz) (c : (D.fm u).clsP)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ),
    P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m) →
    (∀ s, Tf.eWz ψ c s =
      fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s)) →
    Tf.valP.eW ((D.mem u).P.lowerMap ψ) c = fnOf _ (shiftOf (sgT u)) 1 (Formalism.L2.Ker.brTen D u P)

structure LowerSymmetricCompatible (Tf : FormsTiedSym D u Ch chOf) : Prop where
  beOn : Formalism.L2.Ker.BeOnTie D u
  map : LowerMapTieSym Tf

theorem LowerMapTieSym.pt_eq {Tf : FormsTiedSym D u Ch chOf} (h : LowerMapTieSym Tf) (hB : IsUnit (bZ u Tf.til.z0).det) (φ : Fn D u D.R.m) (c : (D.fm u).clsP)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ) (hP : P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m))
    (hv : ∀ s, Tf.eWz ((D.mem u).P.evz φ) c s =
      fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s)) :
    Tf.valP.eW (Pt D u φ) c = fnOf _ (shiftOf (sgT u)) 1 (Formalism.L2.Ker.brTen D u P) :=
  h hB _ c P hP hv

theorem archimedeanSignatureMatching_of_trivial_branching_symm (Tf : FormsTiedSym D u Ch chOf) (P : Pend D u)
    (hP : ∀ τ, P.br τ = Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)) : ArchimedeanSignatureMatching P := by
  intro τ
  rw [hP τ]
  exact Formalism.L2.Ker.brOneIsBr D u τ (interlaceTr D u (sg_interlace Tf.valP) τ)

theorem quotient_not_in_range_symmetric (Tf : FormsTiedSym D u Ch chOf) (x : Fin (D.R.N D.R.m - 1) → D.host.E) :
    iXm D *ᵥ x ≠ fun i => Tf.til.z0 i / ((D.mem u).A.T : D.host.E) := by
  letI := D.host.cmStar
  obtain ⟨a, ha⟩ := Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line
  have hT : ((D.mem u).A.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h := Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
    rw [ha, zero_smul] at h
    simp [Formalism.UG.hform] at h
    exact hT h.symm
  intro hx
  simp only [iXm, LinearMap.toMatrix'_mulVec] at hx
  have hc : iXc D x = (a / ((D.mem u).A.T : D.host.E)) • zc D := by
    rw [hx]; funext i; rw [ha]; simp [Pi.smul_apply, smul_eq_mul]; ring
  unfold iXc zc at hc
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, ← map_smul,
    EmbeddingLike.apply_eq_iff_eq] at hc
  have h1 := D.sp.z_orth ((D.sp.X'.frame.equivFun.trans
      (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankP D)).symm)).symm x)
  rw [hc, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at h1
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact div_ne_zero ha0 hT ((map_eq_zero _).mp h2)
  · exact D.sp.z_anis h2

theorem bZ_isUnitS (Tf : FormsTiedSym D u Ch chOf) : IsUnit (bZ u Tf.til.z0).det :=
  isUnit_det_cols (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R) (iXm D) (fun i => Tf.til.z0 i / ((D.mem u).A.T : D.host.E))
    (iXm_mulVec_injective D) (quotient_not_in_range_symmetric Tf)

def trEvS (Tf : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP) :
    ((D.mem u).C.Y D.R.m → ℂ) →ₗ[ℂ] (Fr D D.R.m le_rfl → ℂ) :=
  ((((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi (Tf.tilAd.ka c))⁻¹ : ℂˣ) : ℂ) •
    LinearMap.funLeft ℂ ℂ (fun y : Fr D D.R.m le_rfl => (Tf.val D.R.m le_rfl (Or.inr rfl)).eY.symm
      (y.tr (atInf (embT D) ((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E))
        (isUnit_det_atInf (embT D) ((Tf.til.ga c).1)⁻¹)))

def coMTS (Tf : FormsTiedSym D u Ch chOf) (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (w : D.what₂.places.Pl) (c : (D.fm u).clsP) :
    ((D.mem u).C.Y D.R.m → ℂ) →ₗ[ℂ] MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ :=
  fnInv (gramC (gramN D D.R.m le_rfl) (embT D)) (shiftOf (lamT u D.R.m))
    (atInf (embT D) (bZg u Tf.til.z0 (B w c))⁻¹) ∘ₗ trEvS Tf c

def coPTS (Tf : FormsTiedSym D u Ch chOf) (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (w : D.what₂.places.Pl) :
    (D.mem u).P.Wrow →ₗ[ℂ] ((D.fm u).clsP → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ) :=
  LinearMap.pi fun c => fnInv (gramC (gramP D) (embT D)) (shiftOf (sgT u)) (atInf (embT D) (B w c)⁻¹) ∘ₗ
    (LinearMap.proj c ∘ₗ Tf.valP.eW.toLinearMap)

theorem trEv_eqS (Tf : FormsTiedSym D u Ch chOf) (φ : Fn D u D.R.m) (c : (D.fm u).clsP) (y : Fr D D.R.m le_rfl) :
    trEvS Tf c (φ ((D.fm u).til c)) y = Tf.eWz ((D.mem u).P.evz φ) c ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY.symm y) := by
  rw [Tf.evz φ c _ ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY.symm
      (y.tr (atInf (embT D) ((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E))
        (isUnit_det_atInf (embT D) ((Tf.til.ga c).1)⁻¹)))]
  · rfl
  · intro τ
    simp only [Equiv.apply_symm_apply]
    show y.1 τ = atInf (embT D) (Tf.til.ga c).1.1 τ *
      (atInf (embT D) ((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) τ * y.1 τ)
    rw [← Matrix.mul_assoc, atInf_mul_inv, Matrix.one_mul]


set_option maxHeartbeats 2000000 in
theorem val_repS (Tf : FormsTiedSym D u Ch chOf) (φ : Formalism.MainNotions.product_first_zeroth_parts.Fn D u D.R.m) (hφ : φ ∈ (D.fm u).Fi D.R.m) (c : (D.fm u).clsP) :
    ∃ P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m), ∀ s, Tf.eWz ((D.mem u).P.evz φ) c s =
      fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s) := by
  have hF := ((Tf.val D.R.m le_rfl (Or.inr rfl)).Fi φ).1 hφ
  obtain ⟨g, hg, hres⟩ := Submodule.mem_map.1 hF
  have hval := (Submodule.mem_pi.1 (Submodule.mem_inf.1 hg).2) ((Tf.cls D.R.m le_rfl (Or.inr rfl)).y ((D.fm u).til c)) (Set.mem_univ _)
  obtain ⟨P0, hP0, hfn⟩ := Submodule.mem_map.1 hval
  have hP0' : P0 ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m) := by
    have := CSpan_shW ((D.fm u).lam D.R.m) (fun _ => ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ))
    unfold lamT at hP0
    rw [this] at hP0
    exact hP0
  have hφv : ∀ z, φ ((D.fm u).til c) ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY.symm z) =
      fnOf _ (shiftOf (lamT u D.R.m)) 1 P0 z := by
    intro z
    have := congrFun (congrFun hres ((D.fm u).til c)) z
    rw [← this, hfn]
    rfl
  set ginv : GL (Fin (D.R.N D.R.m)) D.host.E := ((Tf.til.ga c).1)⁻¹
  set M' : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ := atInf (embT D) (ginv : Matrix _ _ D.host.E)
  have hB := mZ_isUnit (bZ_isUnitS Tf)
  obtain ⟨P, hP, hPy⟩ := exists_rep ((D.fm u).lam D.R.m) _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) M' hB
    (isUnit_det_atInf (embT D) ginv) P0 hP0' ((((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi (Tf.tilAd.ka c))⁻¹ : ℂˣ) : ℂ)
  refine ⟨P, hP, fun s => ?_⟩
  rw [Tf.evz φ c s ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY.symm (((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s).tr M' (isUnit_det_atInf (embT D) ginv)))]
  · rw [hφv]; exact hPy _
  · intro τ
    simp only [Equiv.apply_symm_apply]
    show ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s).1 τ = atInf (embT D) (Tf.til.ga c).1.1 τ * (M' τ * ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s).1 τ)
    rw [← Matrix.mul_assoc, atInf_mul_inv, Matrix.one_mul]

end Formalism.L2.GlobalTheoryTheory.Br
