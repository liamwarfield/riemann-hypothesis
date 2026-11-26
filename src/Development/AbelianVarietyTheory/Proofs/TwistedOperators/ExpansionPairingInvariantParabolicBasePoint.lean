module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingExpansionProductFunctionFixedByKplus

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairVecSumEqOfProdEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.TopZeroInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopZeroInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}


variable (W) in
def thetaSub (p : Pair T) : Submodule ℂ (WO (G.pS p) (G.pT p) → ℂ) where
  carrier := {f | IsThetaFunO W.ψ _ _ f}
  add_mem' := by
    intro f g hf hg
    change IsThetaFunO W.ψ _ _ f at hf
    change IsThetaFunO W.ψ _ _ g at hg
    refine ⟨?_, ?_, hf.cont.add hg.cont, fun k L hL hfin w =>
      (hf.smooth k L hL hfin w).add (hg.smooth k L hL hfin w)⟩
    · intro γ w
      simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
    · obtain ⟨A, hA, hAf⟩ := hf.level
      obtain ⟨B, hB, hBg⟩ := hg.level
      refine ⟨A ⊓ B, hA.inter hB, fun u hu hfin => ?_⟩
      funext w
      have ef := congrFun (hAf u hu.1 hfin) w
      have eg := congrFun (hBg u hu.2 hfin) w
      unfold heisO at ef eg ⊢
      rw [Pi.add_apply, Pi.add_apply, mul_add, ef, eg]
  zero_mem' := by
    refine ⟨?_, ⟨⊤, isOpen_univ, ?_⟩, continuous_const, fun _ _ _ _ _ => contDiff_const⟩
    · intro γ w
      simp only [Pi.zero_apply, mul_zero]
    · intro u _ _
      funext w
      simp only [heisO, Pi.zero_apply, mul_zero]
  smul_mem' c f hf := by
    change IsThetaFunO W.ψ _ _ f at hf
    refine ⟨?_, ?_, hf.cont.const_smul c, fun k L hL hfin w =>
      (hf.smooth k L hL hfin w).const_smul c⟩
    · intro γ w
      rw [Pi.smul_apply, Pi.smul_apply, hf.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
    · obtain ⟨A, hA, hAf⟩ := hf.level
      refine ⟨A, hA, fun u hu hfin => ?_⟩
      funext w
      have ef := congrFun (hAf u hu hfin) w
      unfold heisO at ef ⊢
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, ef]

theorem colV_congr (S : GridChoice W U) {t : T} {fs fs' : Vecs G t} (h : ∀ j, fs (.inl j) = fs' (.inl j))
    (x : ∀ j, FinPt G (.top j)) : colV S fs x = colV S fs' x := by
  have e : (fun j => if h : j < D.R.m then kkVec S (.top t j) (fs (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) =
      (fun j => if h : j < D.R.m then kkVec S (.top t j) (fs' (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) := by
    funext j; split_ifs with hj
    · rw [h]
    · rfl
  simp only [colV, e]

theorem rowV_congr (S : GridChoice W U) {t : T} {fs fs' : Vecs G t} (h : ∀ i, fs (.inr i) = fs' (.inr i))
    (y : ∀ i, FinPt G (.grid i D.R.m)) : rowV S fs y = rowV S fs' y := by
  have e : (fun i => if h : i < D.R.m then kkVec S (.chi i D.R.m) (fs (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) =
      (fun i => if h : i < D.R.m then kkVec S (.chi i D.R.m) (fs' (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) := by
    funext i; split_ifs with hi
    · rw [h]
    · rfl
  simp only [rowV, e]

theorem colK_update (S : GridChoice W U) {t : T} (fs : Vecs G t) (x : ∀ j, FinPt G (.top j)) (j₀ : Fin D.R.m)
    (F : WO (G.pS (arrP t (.inl j₀ : Arr D))) (G.pT (arrP t (.inl j₀ : Arr D))) → ℂ) :
    (fun j => if h : j < D.R.m then kkVec S (.top t j) (Function.update fs (.inl j₀) F (.inl ⟨j, h⟩)) (x j) (x (j + 1))
      else 0) =
    Function.update (fun j => if h : j < D.R.m then kkVec S (.top t j) (fs (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) j₀.1
      (kkVec S (.top t j₀.1) F (x j₀.1) (x (j₀.1 + 1))) := by
  funext j
  by_cases hj : j = j₀.1
  · subst hj
    rw [Function.update_self, dif_pos j₀.2]
    show kkVec S (.top t j₀.1) (Function.update fs (.inl j₀) F (.inl j₀)) _ _ = _
    rw [Function.update_self]
  · rw [Function.update_of_ne hj]
    split_ifs with h
    · rw [Function.update_of_ne]
      intro e; exact hj (congrArg Fin.val (Sum.inl_injective e))
    · rfl

end GlobalTheory.TopZeroInv

namespace GlobalTheory.TopZeroInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem rowK_update (S : GridChoice W U) {t : T} (fs : Vecs G t) (y : ∀ i, FinPt G (.grid i D.R.m)) (i₀ : Fin D.R.m)
    (F : WO (G.pS (arrP t (.inr i₀ : Arr D))) (G.pT (arrP t (.inr i₀ : Arr D))) → ℂ) :
    (fun i => if h : i < D.R.m then kkVec S (.chi i D.R.m) (Function.update fs (.inr i₀) F (.inr ⟨i, h⟩)) (y i) (y (i + 1))
      else 0) =
    Function.update (fun i => if h : i < D.R.m then kkVec S (.chi i D.R.m) (fs (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) i₀.1
      (kkVec S (.chi i₀.1 D.R.m) F (y i₀.1) (y (i₀.1 + 1))) := by
  funext i
  by_cases hi : i = i₀.1
  · subst hi
    rw [Function.update_self, dif_pos i₀.2]
    show kkVec S (.chi i₀.1 D.R.m) (Function.update fs (.inr i₀) F (.inr i₀)) _ _ = _
    rw [Function.update_self]
  · rw [Function.update_of_ne hi]
    split_ifs with h
    · rw [Function.update_of_ne]
      intro e; exact hi (congrArg Fin.val (Sum.inr_injective e))
    · rfl

theorem colV_update_add (S : GridChoice W U) {t : T} (fs : Vecs G t) (x : ∀ j, FinPt G (.top j)) (j₀ : Fin D.R.m)
    {F F' : WO (G.pS (arrP t (.inl j₀ : Arr D))) (G.pT (arrP t (.inl j₀ : Arr D))) → ℂ}
    (hF : IsThetaFunO W.ψ _ _ F) (hF' : IsThetaFunO W.ψ _ _ F') :
    colV S (Function.update fs (.inl j₀) (F + F')) x =
      colV S (Function.update fs (.inl j₀) F) x + colV S (Function.update fs (.inl j₀) F') x := by
  have h : kkVec S (.top t j₀.1) (F + F') (x j₀.1) (x (j₀.1 + 1)) =
      kkVec S (.top t j₀.1) F (x j₀.1) (x (j₀.1 + 1)) + kkVec S (.top t j₀.1) F' (x j₀.1) (x (j₀.1 + 1)) :=
    GlobalTheory.T.normalizedKernelOfVector_add S (.top t j₀.1) hF hF' _ _
  rw [colV, colV, colV, colK_update, colK_update, colK_update, h, GlobalTheory.T.linearMapChainComposite_update_add _ _ _ _ _ j₀.2, LinearMap.add_comp]

theorem colV_update_smul (S : GridChoice W U) {t : T} (fs : Vecs G t) (x : ∀ j, FinPt G (.top j)) (j₀ : Fin D.R.m) (c : ℂ)
    (F : WO (G.pS (arrP t (.inl j₀ : Arr D))) (G.pT (arrP t (.inl j₀ : Arr D))) → ℂ) :
    colV S (Function.update fs (.inl j₀) (c • F)) x = c • colV S (Function.update fs (.inl j₀) F) x := by
  have h : kkVec S (.top t j₀.1) (c • F) (x j₀.1) (x (j₀.1 + 1)) = c • kkVec S (.top t j₀.1) F (x j₀.1) (x (j₀.1 + 1)) :=
    GlobalTheory.T.normalizedKernelOfVector_smul S (.top t j₀.1) c F _ _
  rw [colV, colV, colK_update, colK_update, h, GlobalTheory.T.linearMapChainComposite_update_smul _ _ _ _ _ j₀.2, LinearMap.smul_comp]

theorem rowV_update_add (S : GridChoice W U) {t : T} (fs : Vecs G t) (y : ∀ i, FinPt G (.grid i D.R.m)) (i₀ : Fin D.R.m)
    {F F' : WO (G.pS (arrP t (.inr i₀ : Arr D))) (G.pT (arrP t (.inr i₀ : Arr D))) → ℂ}
    (hF : IsThetaFunO W.ψ _ _ F) (hF' : IsThetaFunO W.ψ _ _ F') :
    rowV S (Function.update fs (.inr i₀) (F + F')) y =
      rowV S (Function.update fs (.inr i₀) F) y + rowV S (Function.update fs (.inr i₀) F') y := by
  have h : kkVec S (.chi i₀.1 D.R.m) (F + F') (y i₀.1) (y (i₀.1 + 1)) =
      kkVec S (.chi i₀.1 D.R.m) F (y i₀.1) (y (i₀.1 + 1)) + kkVec S (.chi i₀.1 D.R.m) F' (y i₀.1) (y (i₀.1 + 1)) :=
    GlobalTheory.T.normalizedKernelOfVector_add S (.chi i₀.1 D.R.m) hF hF' _ _
  rw [rowV, rowV, rowV, rowK_update, rowK_update, rowK_update, h, GlobalTheory.T.linearMapChainComposite_update_add _ _ _ _ _ i₀.2, LinearMap.add_comp]

theorem rowV_update_smul (S : GridChoice W U) {t : T} (fs : Vecs G t) (y : ∀ i, FinPt G (.grid i D.R.m)) (i₀ : Fin D.R.m)
    (c : ℂ) (F : WO (G.pS (arrP t (.inr i₀ : Arr D))) (G.pT (arrP t (.inr i₀ : Arr D))) → ℂ) :
    rowV S (Function.update fs (.inr i₀) (c • F)) y = c • rowV S (Function.update fs (.inr i₀) F) y := by
  have h : kkVec S (.chi i₀.1 D.R.m) (c • F) (y i₀.1) (y (i₀.1 + 1)) = c • kkVec S (.chi i₀.1 D.R.m) F (y i₀.1) (y (i₀.1 + 1)) :=
    GlobalTheory.T.normalizedKernelOfVector_smul S (.chi i₀.1 D.R.m) c F _ _
  rw [rowV, rowV, rowK_update, rowK_update, h, GlobalTheory.T.linearMapChainComposite_update_smul _ _ _ _ _ i₀.2, LinearMap.smul_comp]

end GlobalTheory.TopZeroInv

namespace GlobalTheory.TopZeroInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem coe_update {t : T} (m : ∀ l : Arr D, thetaSub W (arrP t l)) (i : Arr D) (z : thetaSub W (arrP t i)) :
    (fun l => ((Function.update m i z l : thetaSub W (arrP t l)) : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) =
      Function.update (fun l => (m l : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) i (z : _ → ℂ) :=
  funext fun l => Function.apply_update (fun l (q : thetaSub W (arrP t l)) => (q : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) m i z l

theorem pairVec_apply (S : GridChoice W U) {t : T} (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (fs : Vecs G t)
    (v : VV ℂ (wt G (.top 0))) (w : VV ℂ (listedWt G (.grid 0 D.R.m))) :
    pairVec S x y fs v w =
      brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m)) (colV S fs x v) (rowV S fs y w) := rfl

def pairML (S : GridChoice W U) {t : T} (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m))
    (v : VV ℂ (wt G (.top 0))) (w : VV ℂ (listedWt G (.grid 0 D.R.m))) :
    (∀ l : Arr D, thetaSub W (arrP t l)) →ₘₗ[ℂ] ℂ where
  toFun fs := pairVec S (t := t) x y (fun l => ((fs l : thetaSub W (arrP t l)) : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) v w
  map_update_add' := by
    intro inst m i a b
    obtain rfl : inst = (by clear inst; infer_instance : DecidableEq (Arr D)) := Subsingleton.elim _ _
    simp only [coe_update, Submodule.coe_add]
    rcases i with j₀ | i₀
    · have hr : ∀ F, rowV S (Function.update (fun l => (m l : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) (.inl j₀) F) y =
          rowV S (fun l => (m l : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) y := fun F =>
        rowV_congr S (fun i => Function.update_of_ne (Sum.inr_ne_inl) _ _) y
      rw [pairVec_apply, pairVec_apply, pairVec_apply, hr, hr, hr, colV_update_add S _ x j₀ a.2 b.2, LinearMap.add_apply]
      exact LinearMap.map_add₂ _ _ _ _
    · have hc : ∀ F, colV S (Function.update (fun l => (m l : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) (.inr i₀) F) x =
          colV S (fun l => (m l : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) x := fun F =>
        colV_congr S (fun j => Function.update_of_ne (Sum.inl_ne_inr) _ _) x
      rw [pairVec_apply, pairVec_apply, pairVec_apply, hc, hc, hc, rowV_update_add S _ y i₀ a.2 b.2, LinearMap.add_apply]
      exact map_add _ _ _
  map_update_smul' := by
    intro inst m i c a
    obtain rfl : inst = (by clear inst; infer_instance : DecidableEq (Arr D)) := Subsingleton.elim _ _
    simp only [coe_update, Submodule.coe_smul, RingHom.id_apply]
    rcases i with j₀ | i₀
    · have hr : ∀ F, rowV S (Function.update (fun l => (m l : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) (.inl j₀) F) y =
          rowV S (fun l => (m l : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) y := fun F =>
        rowV_congr S (fun i => Function.update_of_ne (Sum.inr_ne_inl) _ _) y
      rw [pairVec_apply, pairVec_apply, hr, hr, colV_update_smul S _ x j₀, LinearMap.smul_apply]
      exact LinearMap.map_smul₂ _ _ _ _
    · have hc : ∀ F, colV S (Function.update (fun l => (m l : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) (.inr i₀) F) x =
          colV S (fun l => (m l : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) x := fun F =>
        colV_congr S (fun j => Function.update_of_ne (Sum.inl_ne_inr) _ _) x
      rw [pairVec_apply, pairVec_apply, hc, hc, rowV_update_smul S _ y i₀, LinearMap.smul_apply]
      exact map_smul _ _ _

end GlobalTheory.TopZeroInv

namespace GlobalTheory.TopZeroInv

theorem pairVec_sum_eq_of_prod_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} {κ : Type} (a : κ →₀ ℂ) (f g : κ → Vecs G t)
    (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (v : VV ℂ (wt G (.top 0)))
    (w : VV ℂ (listedWt G (.grid 0 D.R.m))),
    (∀ c ∈ a.support, ∀ l, IsThetaFunO W.ψ _ _ (f c l)) → (∀ c ∈ a.support, ∀ l, IsThetaFunO W.ψ _ _ (g c l)) →
    (∀ z : ∀ l : Arr D, WO (G.pS (arrP t l)) (G.pT (arrP t l)),
      (a.sum fun c b => b * ∏ l, f c l (z l)) = a.sum fun c b => b * ∏ l, g c l (z l)) →
    (a.sum fun c b => b * pairVec S x y (f c) v w) = a.sum fun c b => b * pairVec S x y (g c) v w := by
  intro D T L sc G W U S t κ a f g x y v w hf hg hprod
  classical
  let f' : κ → ∀ l : Arr D, thetaSub W (arrP t l) := fun c l => if h : c ∈ a.support then ⟨f c l, hf c h l⟩ else 0
  let g' : κ → ∀ l : Arr D, thetaSub W (arrP t l) := fun c l => if h : c ∈ a.support then ⟨g c l, hg c h l⟩ else 0
  have ef : ∀ c ∈ a.support, ∀ l, ((f' c l : thetaSub W (arrP t l)) : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ) = f c l :=
    fun c h l => by simp only [f', dif_pos h]
  have eg : ∀ c ∈ a.support, ∀ l, ((g' c l : thetaSub W (arrP t l)) : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ) = g c l :=
    fun c h l => by simp only [g', dif_pos h]
  have key := GlobalTheory.T.multilinearMap_sum_eq_of_sum_prod_eval_eq (fun l : Arr D => thetaSub W (arrP t l)) (pairML S x y v w) a f' g' (fun z => by
    have := hprod z
    unfold Finsupp.sum at this ⊢
    refine (Finset.sum_congr rfl fun c h => ?_).trans (this.trans (Finset.sum_congr rfl fun c h => ?_))
    · simp only [ef c h]
    · simp only [eg c h])
  unfold Finsupp.sum at key ⊢
  refine (Finset.sum_congr rfl fun c h => ?_).trans (key.trans (Finset.sum_congr rfl fun c h => ?_))
  · change _ = _ * pairVec S (t := t) x y (fun l => ((f' c l : thetaSub W (arrP t l)) : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) v w
    rw [funext (ef c h)]
  · change _ * pairVec S (t := t) x y (fun l => ((g' c l : thetaSub W (arrP t l)) : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) v w = _
    rw [funext (eg c h)]

end GlobalTheory.TopZeroInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VecIsThetaFunO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.TopZeroInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopZeroInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem vec_isThetaFunO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} {p : Pair T}, DefPair D.R.m p → ∀ d : FinDatum G t p, S.Z.HasVec d →
    IsThetaFunO W.ψ (G.pS p) (G.pT p) (S.Z.vec d) := by
  intro D T L sc G W U S t p hp d hd
  have hIn : p.InRange D.R.m := by
    have hn := hp.nodes
    cases p <;> simp only [DefPair, DefNode] at hp hn <;> simp only [Pair.InRange, Node.InRange] <;> omega
  exact GlobalTheory.LastVertexInv.vec_theta S hp hIn d hd

end GlobalTheory.TopZeroInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionPairingInvariantParabolicBasePoint
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.TopZeroInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopZeroInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem pairVec_move (S : GridChoice W U) {t : T} (fs : Vecs G t) (hf : IsThetaFunO W.ψ _ _ (fs first))
    (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.top 0)) :
    pairVec S (Function.update x 0 (x 0 * k)) y fs =
      pairVec S x y (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs) := by
  have hj : ∀ j, (if h : j < D.R.m then kkVec S (.top t j) (fs (.inl ⟨j, h⟩)) (Function.update x 0 (x 0 * k) j)
          (Function.update x 0 (x 0 * k) (j + 1)) else 0) =
        (if h : j < D.R.m then kkVec S (.top t j)
          (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) := by
    intro j
    by_cases h : j < D.R.m
    · rw [dite_eq_left h, dite_eq_left h]
      rcases j with _ | j
      · have e1 : Function.update x 0 (x 0 * k) 0 = x 0 * k := Function.update_self _ _ _
        have e2 : Function.update x 0 (x 0 * k) (0 + 1) = x (0 + 1) := Function.update_of_ne (by omega) _ _
        have e3 : moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs (.inl ⟨0, h⟩) =
            W.om (.top t 0) (G.toPair (.top t 0) ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)).1 1) (fs first) :=
          Function.update_self _ _ _
        rw [e1, e2, e3]
        unfold kkVec
        have e4 : x 0 * k * S.N.u (Pair.small (.top t 0)) =
            (x 0 * S.N.u (.top 0)) * ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) := by group
        rw [e4, GlobalTheory.KerTrans.fockComp_mul_fin W _ (p := .top t 0) (show (Pair.top t 0 : Pair T).InRange D.R.m from
          show 1 ≤ D.R.m by have := D.R.two_le_m; omega) (fs (.inl ⟨0, h⟩)) hf]
        rfl
      · have e1 : Function.update x 0 (x 0 * k) (j + 1) = x (j + 1) := Function.update_of_ne (by omega) _ _
        have e2 : Function.update x 0 (x 0 * k) (j + 1 + 1) = x (j + 1 + 1) := Function.update_of_ne (by omega) _ _
        have e3 : moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs (.inl ⟨j + 1, h⟩) = fs (.inl ⟨j + 1, h⟩) :=
          Function.update_of_ne (by simp [first]) _ _
        rw [e1, e2, e3]
    · rw [dite_eq_right h, dite_eq_right h]
  have hcol : colV S fs (Function.update x 0 (x 0 * k)) =
      colV S (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs) x := by
    have hfam : (fun j => if h : j < D.R.m then kkVec S (.top t j) (fs (.inl ⟨j, h⟩)) (Function.update x 0 (x 0 * k) j)
          (Function.update x 0 (x 0 * k) (j + 1)) else 0) =
        (fun j => if h : j < D.R.m then kkVec S (.top t j)
          (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) :=
      funext hj
    unfold colV
    rw [hfam]
  have hri : ∀ i, (if h : i < D.R.m then kkVec S (.chi i D.R.m) (fs (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) =
      (if h : i < D.R.m then kkVec S (.chi i D.R.m)
        (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) := by
    intro i
    by_cases h : i < D.R.m
    · rw [dite_eq_left h, dite_eq_left h]
      have e3 : moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs (.inr ⟨i, h⟩) = fs (.inr ⟨i, h⟩) :=
        Function.update_of_ne (by simp [first]) _ _
      rw [e3]
    · rw [dite_eq_right h, dite_eq_right h]
  have hrow : rowV S fs y = rowV S (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs) y := by
    have hfam : (fun i => if h : i < D.R.m then kkVec S (.chi i D.R.m) (fs (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) =
      (fun i => if h : i < D.R.m then kkVec S (.chi i D.R.m)
        (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) := funext hri
    unfold rowV
    rw [hfam]
  unfold pairVec
  rw [hcol, hrow]

theorem pairPts_update_top_zero : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))),
    (∀ (x : FinPt G (.top 0)) (k : FinPt G (.top 0)), finG (G.V (.top 0)) k ∈ G.Kplus → Ψ (x * k) = Ψ x) →
    ∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.top 0)),
      finG (G.V (.top 0)) k ∈ S.levTop t Φ β 0 (by have := D.R.two_le_m; omega) →
      pairPts S τ (Function.update x 0 (x 0 * k)) y (Ψ (x 0 * k)) (F (y 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0)) := by
  intro D T L sc G W U S t Φ β τ μ₀ hL hq hc ht hβ hτ hv Ψ F hΨ x y k hk
  have hk' : finG (G.V (.top 0)) k ∈ G.Kplus := hk
  rw [hΨ _ _ hk', pairPts_eq, pairPts_eq]
  have hth : ∀ d ∈ τ.support, ∀ l, IsThetaFunO W.ψ _ _ (vecsOf S d l) := fun d hd l => by
    rcases l with j | i
    · exact GlobalTheory.TopZeroInv.vec_isThetaFunO S (p := .top t j) (show DefPair D.R.m (Pair.top t (j : ℕ)) from j.2) _ ((hv d hd).1 j)
    · exact GlobalTheory.TopZeroInv.vec_isThetaFunO S (p := .chi i D.R.m) (show DefPair D.R.m (Pair.chi (i : ℕ) D.R.m : Pair T) from ⟨i.2, rfl⟩) _ ((hv d hd).2 i)
  have hp0 : (Pair.top t 0 : Pair T).InRange D.R.m := show 1 ≤ D.R.m by have := D.R.two_le_m; omega
  have hmv : ∀ d ∈ τ.support, ∀ l,
      IsThetaFunO W.ψ _ _ (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) (vecsOf S d) l) := by
    intro d hd l
    by_cases hl : l = first
    · subst hl
      have e : moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) (vecsOf S d) first =
          W.om (.top t 0) (G.toPair (.top t 0) ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)).1 1) (vecsOf S d first) :=
        Function.update_self _ _ _
      rw [e]
      exact (W.om_is _ hp0).om_pres _ _ (hth d hd first)
    · have e : moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) (vecsOf S d) l = vecsOf S d l :=
        Function.update_of_ne hl _ _
      rw [e]
      exact hth d hd l
  calc (τ.sum fun d a => a * pairVec S (Function.update x 0 (x 0 * k)) y (vecsOf S d) (Ψ (x 0)) (F (y 0)))
      = τ.sum fun d a => a * pairVec S x y (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) (vecsOf S d))
          (Ψ (x 0)) (F (y 0)) :=
        Finset.sum_congr rfl fun d hd => by dsimp only; rw [pairVec_move S _ (hth d hd first)]
    _ = τ.sum fun d a => a * pairVec S x y (vecsOf S d) (Ψ (x 0)) (F (y 0)) :=
        GlobalTheory.TopZeroInv.pairVec_sum_eq_of_prod_eq S τ _ _ x y _ _ hmv hth (GlobalTheory.T.unfoldingExpansion_productFunction_fixed_by_Kplus S ht hL hq hc ht hβ hτ hv k hk')

end GlobalTheory.TopZeroInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionPairingInvariantParabolicBasePointStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansionPairing_invariant_parabolic_basePoint : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))),
    (∀ (x : FinPt G (.top 0)) (k : FinPt G (.top 0)), finG (G.V (.top 0)) k ∈ G.Kplus → Ψ (x * k) = Ψ x) →
    ∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.top 0)),
      finG (G.V (.top 0)) k ∈ S.levTop t Φ β 0 (by have := D.R.two_le_m; omega) →
      pairPts S τ (Function.update x 0 (x 0 * k)) y (Ψ (x 0 * k)) (F (y 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0)) := by
  first | exact @GlobalTheory.TopZeroInv.pairPts_update_top_zero | exact GlobalTheory.TopZeroInv.pairPts_update_top_zero | (intros; apply GlobalTheory.TopZeroInv.pairPts_update_top_zero <;> assumption)
end
