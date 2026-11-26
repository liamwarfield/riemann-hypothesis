module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionProductInvariantInnerVertexLevel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionPairingInvariantParabolicBasePoint
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionPairingInvariantInnerVertexLevelTer

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionPairingInvariantInnerVertexLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairVEqOfProdFunEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ExpansionInvariance

theorem chainTo_congr_lt {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    {k k' : ∀ j, V j →ₗ[ℂ] V (j + 1)} : ∀ n, (∀ j, j < n → k j = k' j) → chainTo k n = chainTo k' n
  | 0, _ => rfl
  | n + 1, h => by
    show k n ∘ₗ chainTo k n = k' n ∘ₗ chainTo k' n
    rw [h n n.lt_succ_self, chainTo_congr_lt n fun j hj => h j (by omega)]

theorem chainTo_add_at {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    {k₁ k₂ k₃ : ∀ j, V j →ₗ[ℂ] V (j + 1)} (j₀ : ℕ) (h₂ : ∀ j, j ≠ j₀ → k₂ j = k₁ j) (h₃ : ∀ j, j ≠ j₀ → k₃ j = k₁ j)
    (h : k₁ j₀ = k₂ j₀ + k₃ j₀) : ∀ n, j₀ < n → chainTo k₁ n = chainTo k₂ n + chainTo k₃ n
  | 0, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, hn => by
    show k₁ n ∘ₗ chainTo k₁ n = k₂ n ∘ₗ chainTo k₂ n + k₃ n ∘ₗ chainTo k₃ n
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h' | h'
    · rw [chainTo_add_at j₀ h₂ h₃ h n h', h₂ n (by omega), h₃ n (by omega), LinearMap.comp_add]
    · subst h'
      rw [chainTo_congr_lt (k := k₂) (k' := k₁) j₀ (fun j hj => h₂ j (by omega)),
        chainTo_congr_lt (k := k₃) (k' := k₁) j₀ (fun j hj => h₃ j (by omega)), h, LinearMap.add_comp]

theorem chainTo_smul_at {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    {k₁ k₂ : ∀ j, V j →ₗ[ℂ] V (j + 1)} (j₀ : ℕ) (a : ℂ) (h₂ : ∀ j, j ≠ j₀ → k₂ j = k₁ j)
    (h : k₁ j₀ = a • k₂ j₀) : ∀ n, j₀ < n → chainTo k₁ n = a • chainTo k₂ n
  | 0, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, hn => by
    show k₁ n ∘ₗ chainTo k₁ n = a • (k₂ n ∘ₗ chainTo k₂ n)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h' | h'
    · rw [chainTo_smul_at j₀ a h₂ h n h', h₂ n (by omega), LinearMap.comp_smul]
    · subst h'
      rw [chainTo_congr_lt (k := k₂) (k' := k₁) j₀ (fun j hj => h₂ j (by omega)), h, LinearMap.smul_comp]

theorem jetOp_mul_tab {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a)
    (lam' : ι → DomWeight b) (c : K) (J : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) :
    Formalism.L2.Ker.jetOp lam lam' (fun k => c * J k) n = c • Formalism.L2.Ker.jetOp lam lam' J n := by
  have e : Formalism.L2.Ker.jetLin (fun k => c * J k) = c • Formalism.L2.Ker.jetLin J := by
    refine (MvPolynomial.basisMonomials ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) K).ext fun m => ?_
    simp only [Formalism.L2.Ker.jetLin, LinearMap.smul_apply, Module.Basis.constr_basis, MvPolynomial.smul_monomial,
      smul_eq_mul]
  ext1 P
  simp only [Formalism.L2.Ker.jetOp, Formalism.L2.Ker.jetMap, e, LinearMap.comp_apply, LinearMap.smul_apply, map_smul]

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem kkVec_smul (S : GridChoice W U) (p : Pair T) (a : ℂ) (f : WO (G.pS p) (G.pT p) → ℂ) (x : FinPt G p.small)
    (y : FinPt G p.big) : GlobalTheory.TopZeroInv.kkVec S p (a • f) x y = a • GlobalTheory.TopZeroInv.kkVec S p f x y := by
  have hJ : ∀ x' y', jetTab W S.N.frC p (a • f) x' y' = fun k => a * jetTab W S.N.frC p f x' y' k := by
    intro x' y'
    funext k
    simp only [jetTab, kerFin, fockIn, GlobalTheory.FiniteFock.pureTensorO_smul, GridData.Weil.ker, thetaKO, map_smul,
      Pi.smul_apply, smul_eq_mul]
  unfold GlobalTheory.TopZeroInv.kkVec fockComp
  rw [hJ, jetOp_mul_tab, smul_comm]

def colML (S : GridChoice W U) (t : T) (x : ∀ j, FinPt G (.top j)) :
    MultilinearMap (RingHom.id ℂ) (fun j : Fin D.R.m => ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))))
      (VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (wt G (.top D.R.m))) where
  toFun cc := colMapV S t (fun j => (cc j : WO _ _ → ℂ)) x
  map_update_add' := by
    intro _ cc j₀ a b
    unfold colMapV
    rw [← LinearMap.add_comp]
    congr 1
    refine chainTo_add_at j₀.1 ?_ ?_ ?_ D.R.m j₀.2
    · intro j hj
      dsimp only
      split_ifs with h
      · have hne : (⟨j, h⟩ : Fin D.R.m) ≠ j₀ := fun e => hj (congrArg Fin.val e)
        simp only [Function.update_of_ne hne]
      · rfl
    · intro j hj
      dsimp only
      split_ifs with h
      · have hne : (⟨j, h⟩ : Fin D.R.m) ≠ j₀ := fun e => hj (congrArg Fin.val e)
        simp only [Function.update_of_ne hne]
      · rfl
    · simp only [dif_pos j₀.2, Fin.eta, Function.update_self, Submodule.coe_add]
      exact GlobalTheory.TopZeroInv.kkVec_add S _ a.2 b.2 _ _
  map_update_smul' := by
    intro _ cc j₀ c a
    unfold colMapV
    rw [← LinearMap.smul_comp]
    congr 1
    refine chainTo_smul_at j₀.1 c ?_ ?_ D.R.m j₀.2
    · intro j hj
      dsimp only
      split_ifs with h
      · have hne : (⟨j, h⟩ : Fin D.R.m) ≠ j₀ := fun e => hj (congrArg Fin.val e)
        simp only [Function.update_of_ne hne]
      · rfl
    · simp only [dif_pos j₀.2, Fin.eta, Function.update_self, Submodule.coe_smul]
      exact kkVec_smul S _ c _ _ _

def rowML (S : GridChoice W U) (t : T) (y : ∀ i, FinPt G (.grid i D.R.m)) :
    MultilinearMap (RingHom.id ℂ) (fun i : Fin D.R.m => ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))))
      (VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] VV ℂ (wt G (.grid D.R.m D.R.m))) where
  toFun rr := rowMapV S (fun i => (rr i : WO _ _ → ℂ)) y
  map_update_add' := by
    intro _ rr i₀ a b
    unfold rowMapV
    rw [← LinearMap.add_comp]
    congr 1
    refine chainTo_add_at i₀.1 ?_ ?_ ?_ D.R.m i₀.2
    · intro i hi
      dsimp only
      split_ifs with h
      · have hne : (⟨i, h⟩ : Fin D.R.m) ≠ i₀ := fun e => hi (congrArg Fin.val e)
        simp only [Function.update_of_ne hne]
      · rfl
    · intro i hi
      dsimp only
      split_ifs with h
      · have hne : (⟨i, h⟩ : Fin D.R.m) ≠ i₀ := fun e => hi (congrArg Fin.val e)
        simp only [Function.update_of_ne hne]
      · rfl
    · simp only [dif_pos i₀.2, Fin.eta, Function.update_self, Submodule.coe_add]
      exact GlobalTheory.TopZeroInv.kkVec_add S _ a.2 b.2 _ _
  map_update_smul' := by
    intro _ rr i₀ c a
    unfold rowMapV
    rw [← LinearMap.smul_comp]
    congr 1
    refine chainTo_smul_at i₀.1 c ?_ ?_ D.R.m i₀.2
    · intro i hi
      dsimp only
      split_ifs with h
      · have hne : (⟨i, h⟩ : Fin D.R.m) ≠ i₀ := fun e => hi (congrArg Fin.val e)
        simp only [Function.update_of_ne hne]
      · rfl
    · simp only [dif_pos i₀.2, Fin.eta, Function.update_self, Submodule.coe_smul]
      exact kkVec_smul S _ c _ _ _

def pairRowL (S : GridChoice W U) (t : T) (y : ∀ i, FinPt G (.grid i D.R.m)) (u : VV ℂ (wt G (.top 0)))
    (v : VV ℂ (listedWt G (.grid 0 D.R.m))) :
    (VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (wt G (.top D.R.m))) →ₗ[ℂ]
      MultilinearMap (RingHom.id ℂ) (fun i : Fin D.R.m => ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)))) ℂ where
  toFun A := ((brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m)) (A u)).comp
    (LinearMap.applyₗ v)).compMultilinearMap (rowML S t y)
  map_add' A B := by
    ext rr
    simp only [LinearMap.add_apply, map_add (f := _), LinearMap.add_comp, MultilinearMap.add_apply]
    rfl
  map_smul' c A := by
    ext rr
    simp only [LinearMap.smul_apply, map_smul, LinearMap.smul_comp, MultilinearMap.smul_apply, RingHom.id_apply]
    rfl

def pairML (S : GridChoice W U) (t : T) (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m))
    (u : VV ℂ (wt G (.top 0))) (v : VV ℂ (listedWt G (.grid 0 D.R.m))) :
    MultilinearMap (RingHom.id ℂ) (fun j : Fin D.R.m => ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))))
      (MultilinearMap (RingHom.id ℂ) (fun i : Fin D.R.m => ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)))) ℂ) :=
  (pairRowL S t y u v).compMultilinearMap (colML S t x)

theorem pairML_apply (S : GridChoice W U) (t : T) (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m))
    (u : VV ℂ (wt G (.top 0))) (v : VV ℂ (listedWt G (.grid 0 D.R.m))) (cc rr) :
    pairML S t x y u v cc rr = (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))).compl₁₂
      (colMapV S t (fun j => (cc j : WO _ _ → ℂ)) x) (rowMapV S (fun i => (rr i : WO _ _ → ℂ)) y) u v := rfl

theorem pairV_eq_of_prodFun_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T)
    {δ : Type} (τ : δ →₀ ℂ) (c c' : δ → ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ)
    (r r' : δ → ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ),
    (∀ d ∈ τ.support, ∀ j : Fin D.R.m, IsThetaFunO W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) (c d j) ∧
      IsThetaFunO W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) (c' d j)) →
    (∀ d ∈ τ.support, ∀ i : Fin D.R.m, IsThetaFunO W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (r d i) ∧
      IsThetaFunO W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (r' d i)) →
    (∀ (w : ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)))
      (z : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (τ.sum fun d a => a * (∏ j, c d j (w j)) * ∏ i, r d i (z i)) = τ.sum fun d a => a * (∏ j, c' d j (w j)) * ∏ i, r' d i (z i)) →
    ∀ x y, pairV S t τ c r x y = pairV S t τ c' r' x y := by
  intro D T L sc G W U S t δ τ c c' r r' hc hr hprod x y
  classical
  refine LinearMap.ext fun u => LinearMap.ext fun v => ?_
  let f : δ → ∀ j : Fin D.R.m, ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))) :=
    fun d j => if h : d ∈ τ.support then ⟨c d j, (hc d h j).1⟩ else 0
  let f' : δ → ∀ j : Fin D.R.m, ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))) :=
    fun d j => if h : d ∈ τ.support then ⟨c' d j, (hc d h j).2⟩ else 0
  let g : δ → ∀ i : Fin D.R.m, ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :=
    fun d i => if h : d ∈ τ.support then ⟨r d i, (hr d h i).1⟩ else 0
  let g' : δ → ∀ i : Fin D.R.m, ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :=
    fun d i => if h : d ∈ τ.support then ⟨r' d i, (hr d h i).2⟩ else 0
  have ef : ∀ d ∈ τ.support, (fun j => (f d j : WO _ _ → ℂ)) = c d := fun d hd => funext fun j => by simp only [f, dif_pos hd]
  have ef' : ∀ d ∈ τ.support, (fun j => (f' d j : WO _ _ → ℂ)) = c' d := fun d hd => funext fun j => by simp only [f', dif_pos hd]
  have eg : ∀ d ∈ τ.support, (fun i => (g d i : WO _ _ → ℂ)) = r d := fun d hd => funext fun i => by simp only [g, dif_pos hd]
  have eg' : ∀ d ∈ τ.support, (fun i => (g' d i : WO _ _ → ℂ)) = r' d := fun d hd => funext fun i => by simp only [g', dif_pos hd]
  have key := GlobalTheory.funProd_multilinear_sum_eq (pairML S t x y u v) τ f f' g g' (fun w z => by
    rw [Finsupp.sum, Finsupp.sum]
    have h1 := hprod w z
    rw [Finsupp.sum, Finsupp.sum] at h1
    refine (Finset.sum_congr rfl fun d hd => ?_).trans (h1.trans (Finset.sum_congr rfl fun d hd => ?_))
    · rw [← ef d hd, ← eg d hd]
    · rw [← ef' d hd, ← eg' d hd])
  have hL : ∀ (cc : δ → ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ)
      (rr : δ → ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)
      (F : δ → ∀ j : Fin D.R.m, ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))))
      (H : δ → ∀ i : Fin D.R.m, ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)))),
      (∀ d ∈ τ.support, (fun j => (F d j : WO _ _ → ℂ)) = cc d) → (∀ d ∈ τ.support, (fun i => (H d i : WO _ _ → ℂ)) = rr d) →
      pairV S t τ cc rr x y u v = τ.sum fun d a => a * pairML S t x y u v (F d) (H d) := by
    intro cc rr F H hF hH
    unfold pairV
    rw [Finsupp.sum, Finsupp.sum, LinearMap.sum_apply, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, pairML_apply, hF d hd, hH d hd]
  rw [hL c r f g ef eg, hL c' r' f' g' ef' eg']
  exact key

end GlobalTheory.ExpansionInvariance

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VecIsThetaFunOAlt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.VecThetaDef

theorem vec_isThetaFunO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} {N : Std G U} (Z : Normal W N)
    {t : T} {p : Pair T} (d : FinDatum G t p), DefPair D.R.m p → p.InRange D.R.m → Z.HasVec d →
    IsThetaFunO W.ψ (G.pS p) (G.pT p) (Z.vec d) := by
  intro D T L sc G W U N Z t p d hp hIn h
  obtain ⟨f, hf⟩ := h
  rw [Normal.vec, FinDatum.vec_eq W hf]
  exact (W.om_is p hIn).om_pres _ _
    (GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is hf (Z.vac_is p hp).2.theta)

end GlobalTheory.VecThetaDef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCompTranslate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FockTranslate

theorem compAt_fin {D : D7} (θ : InfFam D) (τ : D.what₂.Tau) {V : HSp D} (g : GA D V) (hg : g ∈ Formalism.L2.Theta.GfC V) :
    Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V g) = 1 := by
  have h6 : (Formalism.L2.Theta.mt V g).map (Formalism.L2.Theta.infPart D) = 1 :=
    congrArg Units.val (show Formalism.L2.Theta.infHom V g = 1 from hg)
  unfold Formalism.IndefR.Datum.compAt
  rw [show (Formalism.L2.Theta.mt V g).map (fun a => θ τ (Formalism.L2.Theta.infPart D a)) =
    ((Formalism.L2.Theta.mt V g).map (Formalism.L2.Theta.infPart D)).map (θ τ) from (Matrix.map_map).symm, h6]
  exact Matrix.map_one _ (θ τ).map_zero (θ τ).map_one

theorem fockComp_translate : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (B : VertexFrames G) (t : T) (j : ℕ),
    j + 1 ≤ D.R.m → ∀ (f : WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ),
    IsThetaFunO W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) f →
    ∀ (a k₁ : FinPt G (.top j)) (b k₂ : FinPt G (.top (j + 1))),
      fockComp W B (.top t j) f (a * k₁) (b * k₂) =
        fockComp W B (.top t j) (W.om (.top t j) ((k₁ : GA D (G.V (.top j))), (k₂ : GA D (G.V (.top (j + 1))))) f) a b := by
  intro D T L sc G W B t j hj f hf a k₁ b k₂
  have hom := W.om_is (.top t j) hj
  have hcomm : ∀ P, W.om (.top t j) ((k₁ : GA D (G.V (.top j))), (k₂ : GA D (G.V (.top (j + 1)))))
      (fockIn W B (.top t j) f P) = fockIn W B (.top t j) (W.om (.top t j) ((k₁ : GA D (G.V (.top j))), (k₂ : GA D (G.V (.top (j + 1))))) f) P := by
    intro P
    unfold fockIn
    refine Formalism.IndefR.Eqv.KerDiag.comm_pureTensorO W.ψ_std W.θ W.θ_is _ _ _ _ _ (fun τ z g hg => ?_) hf P
    rw [GlobalTheory.OrientedHeis.om_dRho hom W.θ_is _ _ τ z hg, compAt_fin W.θ τ _ k₂.2, compAt_fin W.θ τ _ (inv_mem k₁.2),
      Matrix.one_mul, Matrix.mul_one]
  unfold fockComp
  congr 1
  funext M
  unfold jetTab kerFin GridData.Weil.ker
  simp only [GridData.toPair, thetaKO, Subgroup.coe_mul]
  rw [show ((a : GA D (G.V (.top j))) * k₁, (b : GA D (G.V (.top (j + 1)))) * k₂) =
    ((a : GA D (G.V (.top j))), (b : GA D (G.V (.top (j + 1))))) * ((k₁ : GA D (G.V (.top j))), (k₂ : GA D (G.V (.top (j + 1))))) from rfl,
    map_mul, Module.End.mul_apply, hcomm]

end GlobalTheory.FockTranslate

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionPairingInvariantInnerVertexLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ExpansionInvariance


variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} in
theorem colMapV_congr (S : GridChoice W U) (t : T)
    (v v' : ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ) (x x' : ∀ j, FinPt G (.top j))
    (h : ∀ j (hj : j < D.R.m), fockComp W S.N.frC (.top t j) (v ⟨j, hj⟩) (x j * S.N.u _) (x (j + 1) * S.N.u _) =
      fockComp W S.N.frC (.top t j) (v' ⟨j, hj⟩) (x' j * S.N.u _) (x' (j + 1) * S.N.u _)) :
    colMapV S t v x = colMapV S t v' x' := by
  have e : (fun j => if hj : j < D.R.m then S.Z.scal 1 (.top t j) •
      fockComp W S.N.frC (.top t j) (v ⟨j, hj⟩) (x j * S.N.u _) (x (j + 1) * S.N.u _) else 0) =
      (fun j => if hj : j < D.R.m then S.Z.scal 1 (.top t j) •
      fockComp W S.N.frC (.top t j) (v' ⟨j, hj⟩) (x' j * S.N.u _) (x' (j + 1) * S.N.u _) else 0) := by
    funext j
    by_cases hj : j < D.R.m
    · rw [dite_eq_left hj, dite_eq_left hj, h j hj]
    · rw [dite_eq_right hj, dite_eq_right hj]
  unfold colMapV
  rw [e]

theorem pairPts_update_top : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))),
    ∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (j : ℕ) (hj : 0 < j) (hjm : j < D.R.m) (k : FinPt G (.top j)),
      finG (G.V (.top j)) k ∈ S.levTop t Φ β j hjm →
      pairPts S τ (Function.update x j (x j * k)) y (Ψ (Function.update x j (x j * k) 0)) (F (y 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0)) := by
  intro D T L sc G W U S t Φ β τ μ₀ hL hde hc ht hβ hτ hv Ψ F x y j hj hjm k hk
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hx0 : Function.update x (j + 1) (x (j + 1) * k) 0 = x 0 := Function.update_of_ne (by omega) _ _
  rw [hx0, pairPts_eq_pairV, pairPts_eq_pairV]
  set u := S.N.u (.top (j + 1)) with hu
  set g : FinPt G (.top (j + 1)) := u⁻¹ * k * u with hg
  have thv : ∀ d ∈ τ.support, ∀ j' : Fin D.R.m, IsThetaFunO W.ψ (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)) (S.Z.vec (d.1 j')) :=
    fun d hd j' => GlobalTheory.VecThetaDef.vec_isThetaFunO S.Z (d.1 j') (show j'.1 + 1 ≤ D.R.m by omega) (by simp [Pair.InRange, Node.InRange]; try omega) ((hv d hd).1 j')
  have hcol : ∀ d ∈ τ.support, colMapV S t (fun j' => S.Z.vec (d.1 j')) (Function.update x (j + 1) (x (j + 1) * k)) =
      colMapV S t (movedCol S d j hjm g) x := by
    intro d hd
    refine colMapV_congr S t _ _ _ _ fun j' hj' => ?_
    by_cases h1 : j = j'
    · subst h1
      have hA := GlobalTheory.FockTranslate.fockComp_translate W S.N.frC t j (by omega) _ (thv d hd ⟨j, hj'⟩) (x j * S.N.u _) 1 (x (j + 1) * u) g
      rw [mul_one] at hA
      have e1 : x (j + 1) * k * u = x (j + 1) * u * g := by rw [hg]; group
      have m1 : (⟨j, hj'⟩ : Fin D.R.m) ≠ ⟨j + 1, hjm⟩ := by intro h; simp [Fin.ext_iff] at h
      rw [Function.update_of_ne (by omega : j ≠ j + 1), Function.update_self, e1, hA, movedCol,
        Function.update_of_ne m1, Function.update_self]
      try simp only [OneMemClass.coe_one]
      all_goals rfl
    · by_cases h2 : j + 1 = j'
      · subst h2
        have hA := GlobalTheory.FockTranslate.fockComp_translate W S.N.frC t (j + 1) (by omega) _ (thv d hd ⟨j + 1, hj'⟩) (x (j + 1) * u) g (x (j + 1 + 1) * S.N.u _) 1
        rw [mul_one] at hA
        have e1 : x (j + 1) * k * u = x (j + 1) * u * g := by rw [hg]; group
        rw [Function.update_self, Function.update_of_ne (by omega : j + 1 + 1 ≠ j + 1), e1, hA, movedCol, Function.update_self]
        try simp only [OneMemClass.coe_one]
        all_goals rfl
      · have m1 : (⟨j', hj'⟩ : Fin D.R.m) ≠ ⟨j + 1, hjm⟩ := by intro h; simp [Fin.ext_iff] at h; omega
        have m2 : (⟨j', hj'⟩ : Fin D.R.m) ≠ ⟨j, by omega⟩ := by intro h; simp [Fin.ext_iff] at h; omega
        rw [Function.update_of_ne (by omega : j' ≠ j + 1), Function.update_of_ne (by omega : j' + 1 ≠ j + 1), movedCol,
          Function.update_of_ne m1, Function.update_of_ne m2]
  have key : pairV S t τ (fun d j' => S.Z.vec (d.1 j')) (fun d i => S.Z.vec (d.2 i)) (Function.update x (j + 1) (x (j + 1) * k)) y =
      pairV S t τ (fun d => movedCol S d j hjm g) (fun d i => S.Z.vec (d.2 i)) x y := by
    unfold pairV
    refine Finsupp.sum_congr fun d hd => ?_
    rw [hcol d hd]
  rw [key]
  refine congrArg (fun φ => φ (Ψ (x 0)) (F (y 0))) (GlobalTheory.ExpansionInvariance.pairV_eq_of_prodFun_eq S t τ _ _ _ _ ?_ ?_ (GlobalTheory.T.expansion_product_invariant_inner_vertex_level S hL hde hc ht hβ hτ hv j hjm k hk) x y)
  · intro d hd j'
    refine ⟨?_, thv d hd j'⟩
    by_cases h2 : j' = ⟨j + 1, hjm⟩
    · subst h2
      rw [movedCol, Function.update_self]
      exact (W.om_is _ (by simp [Pair.InRange, Node.InRange]; try omega)).om_pres _ _ (thv d hd _)
    · by_cases h1 : j' = ⟨j, by omega⟩
      · subst h1
        rw [movedCol, Function.update_of_ne h2, Function.update_self]
        exact (W.om_is _ (by simp [Pair.InRange, Node.InRange]; try omega)).om_pres _ _ (thv d hd _)
      · rw [movedCol, Function.update_of_ne h2, Function.update_of_ne h1]
        exact thv d hd j'
  · intro d hd i
    have h := GlobalTheory.VecThetaDef.vec_isThetaFunO S.Z (d.2 i) (show i.1 + 1 ≤ D.R.m ∧ D.R.m = D.R.m by omega) (show i.1 + 1 ≤ D.R.m ∧ D.R.m ≤ D.R.m by omega) ((hv d hd).2 i)
    exact ⟨h, h⟩

end GlobalTheory.ExpansionInvariance

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionPairingInvariantInnerVertexLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansionPairing_invariant_inner_vertex_level : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))),
    ∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (j : ℕ) (hj : 0 < j) (hjm : j < D.R.m) (k : FinPt G (.top j)),
      finG (G.V (.top j)) k ∈ S.levTop t Φ β j hjm →
      pairPts S τ (Function.update x j (x j * k)) y (Ψ (Function.update x j (x j * k) 0)) (F (y 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0)) := by
  first | exact @GlobalTheory.ExpansionInvariance.pairPts_update_top | exact GlobalTheory.ExpansionInvariance.pairPts_update_top | (intros; apply GlobalTheory.ExpansionInvariance.pairPts_update_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionPairingInvariantLastVertexLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColMapVUpdateLast
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LastColumnMove

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem fockComp_mul_right (B : VertexFrames G) (t : T) (j : ℕ) (hj : (Pair.top t j : Pair T).InRange D.R.m)
    {f : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ} (hf : IsThetaFunO W.ψ _ _ f)
    (a : FinPt G (.top j)) (b h : FinPt G (.top (j + 1))) :
    fockComp W B (.top t j) f a (b * h) = fockComp W B (.top t j) (W.om (.top t j) (G.toPair (.top t j) 1 h.1) f) a b := by
  unfold fockComp
  congr 1
  funext k
  unfold jetTab kerFin GridData.Weil.ker thetaKO
  have e1 : G.toPair (.top t j) (a : GA D (G.V (Pair.top t j : Pair T).small)) ((b * h : FinPt G (.top (j + 1))) : GA D _) =
      G.toPair (.top t j) a b * G.toPair (.top t j) 1 h.1 := by
    simp [GridData.toPair, Prod.ext_iff]
  have e2 : G.toPair (.top t j) 1 h.1 = ((1 : GA D _), h.1) := rfl
  rw [e1, map_mul, Module.End.mul_apply, e2]
  unfold fockIn
  rw [GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ _ _ _ _ (W.om _) (W.om_is _ hj) W.θ W.θ_is 1 (one_mem _) h.1 h.2 _ _ _ _ f _ hf]

theorem update_top_eq {a b : ℕ} (h : a = b) (x : ∀ j, FinPt G (.top j)) (v : FinPt G (.top a)) :
    Function.update x a v b = h ▸ v := by
  subst h; simp

theorem cast_mul_top {a b : ℕ} (h : a = b) (x : ∀ j, FinPt G (.top j)) (p : FinPt G (.top a)) :
    (h ▸ (x a * p) : FinPt G (.top b)) = x b * (h ▸ p : FinPt G (.top b)) := by
  subst h; rfl

theorem cast_conj_top {a b : ℕ} (h : a = b) (u : ∀ X : Node, FinPt G X) (p : FinPt G (.top a)) :
    (h ▸ ((u (.top a))⁻¹ * p * u (.top a)) : FinPt G (.top b)) = (u (.top b))⁻¹ * (h ▸ p : FinPt G (.top b)) * u (.top b) := by
  subst h; rfl

end GlobalTheory.LastColumnMove

namespace GlobalTheory.LastColumnMove

theorem colMapV_update_last : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} (fs : ∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ) (x : ∀ j, FinPt G (.top j)) (g : FinPt G (.top D.R.m)),
    IsThetaFunO W.ψ (G.pS (.top t (lastIx D))) (G.pT (.top t (lastIx D))) (fs (lastIx D)) →
    colMapV S fs (Function.update x D.R.m (x D.R.m * g)) = colMapV S (Function.update fs (lastIx D) (colShift S t g (fs (lastIx D)))) x := by
  intro D T L sc G W U S t fs x g hf
  unfold colMapV
  refine congrArg (fun k => LinearMap.comp (chainTo (V := fun j => VV ℂ (wt G (.top j))) k D.R.m) _) ?_
  funext j
  by_cases hjm : j < D.R.m
  · rw [dite_eq_left hjm, dite_eq_left hjm]
    by_cases hj1 : j + 1 < D.R.m
    · have h1 : j ≠ D.R.m := by omega
      have h2 : j + 1 ≠ D.R.m := by omega
      have h3 : (⟨j, hjm⟩ : Fin D.R.m) ≠ lastIx D := by
        intro h; have := congrArg Fin.val h; simp [lastIx] at this; omega
      rw [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
    · obtain rfl : j = (lastIx D : ℕ) := by simp [lastIx]; omega
      have h1 : ((lastIx D : ℕ)) ≠ D.R.m := by have := lastIx_succ D; omega
      rw [Function.update_of_ne h1, update_top_eq (lastIx_succ D), cast_mul_top (lastIx_succ D)]
      have e : ∀ a p v : FinPt G (.top ((lastIx D : ℕ) + 1)), a * p * v = a * v * (v⁻¹ * p * v) := by
        intro a p v; group
      rw [e, ← cast_conj_top (lastIx_succ D) S.N.u]
      have hf' : IsThetaFunO W.ψ _ _ (fs ⟨(lastIx D : ℕ), hjm⟩) := hf
      rw [fockComp_mul_right _ t _ (inRange_top t (lastIx D)) hf',
        show Function.update fs (lastIx D) (colShift S t g (fs (lastIx D))) ⟨(lastIx D : ℕ), hjm⟩ =
          colShift S t g (fs (lastIx D)) from Function.update_self _ _ _]
      rfl
  · rw [dite_eq_right hjm, dite_eq_right hjm]

end GlobalTheory.LastColumnMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowMapVUpdateLast
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LastRowMove

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem negGA_mem_fin (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) : negGA V g ∈ GfC (negSp V) := by
  have e : matHom (negSp V) (negGA V g) = matHom V g := Units.ext (mt_negGA V g)
  simp only [GfC, MonoidHom.mem_ker, infHom, MonoidHom.comp_apply] at hg ⊢
  rw [e]
  exact hg

theorem fockComp_mul_right (B : VertexFrames G) (i : ℕ) (hi : (Pair.chi i D.R.m : Pair T).InRange D.R.m)
    {f : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ} (hf : IsThetaFunO W.ψ _ _ f)
    (a : FinPt G (.grid i D.R.m)) (b h : FinPt G (.grid (i + 1) D.R.m)) :
    fockComp W B (.chi i D.R.m : Pair T) f a (b * h) =
      fockComp W B (.chi i D.R.m : Pair T) (W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m : Pair T) 1 h.1) f) a b := by
  unfold fockComp
  congr 1
  funext k
  unfold jetTab kerFin GridData.Weil.ker thetaKO
  have e1 : G.toPair (.chi i D.R.m : Pair T) (a : GA D (G.V (Pair.chi i D.R.m : Pair T).small))
      ((b * h : FinPt G (.grid (i + 1) D.R.m)) : GA D _) =
      G.toPair (.chi i D.R.m : Pair T) a b * G.toPair (.chi i D.R.m : Pair T) 1 h.1 := by
    simp [GridData.toPair, Prod.ext_iff, map_mul]
  have e2 : G.toPair (.chi i D.R.m : Pair T) 1 h.1 = (negGA _ h.1, (1 : GA D _)) := rfl
  rw [e1, map_mul, Module.End.mul_apply, e2]
  unfold fockIn
  rw [GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ _ _ _ _ (W.om _) (W.om_is _ hi) W.θ W.θ_is (negGA _ h.1) (negGA_mem_fin _ h.2)
    1 (one_mem _) _ _ _ _ f _ hf]

theorem update_grid_eq {a b : ℕ} (h : a = b) (y : ∀ i, FinPt G (.grid i D.R.m)) (v : FinPt G (.grid a D.R.m)) :
    Function.update y a v b = h ▸ v := by
  subst h; simp

theorem cast_mul_grid {a b : ℕ} (h : a = b) (y : ∀ i, FinPt G (.grid i D.R.m)) (p : FinPt G (.grid a D.R.m)) :
    (h ▸ (y a * p) : FinPt G (.grid b D.R.m)) = y b * (h ▸ p : FinPt G (.grid b D.R.m)) := by
  subst h; rfl

theorem cast_conj_grid {a b : ℕ} (h : a = b) (u : ∀ X : Node, FinPt G X) (p : FinPt G (.grid a D.R.m)) :
    (h ▸ ((u (.grid a D.R.m))⁻¹ * p * u (.grid a D.R.m)) : FinPt G (.grid b D.R.m)) =
      (u (.grid b D.R.m))⁻¹ * (h ▸ p : FinPt G (.grid b D.R.m)) * u (.grid b D.R.m) := by
  subst h; rfl

end GlobalTheory.LastRowMove

namespace GlobalTheory.LastRowMove

theorem rowMapV_update_last : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (gs : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.grid D.R.m D.R.m)),
    IsThetaFunO W.ψ (G.pS (.chi (lastIx D) D.R.m : Pair T)) (G.pT (.chi (lastIx D) D.R.m : Pair T)) (gs (lastIx D)) →
    rowMapV S gs (Function.update y D.R.m (y D.R.m * k)) = rowMapV S (Function.update gs (lastIx D) (rowShift S k (gs (lastIx D)))) y := by
  intro D T L sc G W U S gs y k hf
  unfold rowMapV
  refine congrArg (fun q => LinearMap.comp (chainTo (V := fun i => VV ℂ (wt G (.grid i D.R.m))) q D.R.m) _) ?_
  funext j
  by_cases hjm : j < D.R.m
  · rw [dite_eq_left hjm, dite_eq_left hjm]
    by_cases hj1 : j + 1 < D.R.m
    · have h1 : j ≠ D.R.m := by omega
      have h2 : j + 1 ≠ D.R.m := by omega
      have h3 : (⟨j, hjm⟩ : Fin D.R.m) ≠ lastIx D := by
        intro h; have := congrArg Fin.val h; simp [lastIx] at this; omega
      rw [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
    · obtain rfl : j = (lastIx D : ℕ) := by simp [lastIx]; omega
      have h1 : ((lastIx D : ℕ)) ≠ D.R.m := by have := lastIx_succ D; omega
      rw [Function.update_of_ne h1, update_grid_eq (lastIx_succ D), cast_mul_grid (lastIx_succ D)]
      have e : ∀ a p v : FinPt G (.grid ((lastIx D : ℕ) + 1) D.R.m), a * p * v = a * v * (v⁻¹ * p * v) := by
        intro a p v; group
      rw [e, ← cast_conj_grid (lastIx_succ D) S.N.u]
      have hf' : IsThetaFunO W.ψ _ _ (gs ⟨(lastIx D : ℕ), hjm⟩) := hf
      rw [fockComp_mul_right _ _ (inRange_chi (lastIx D)) hf',
        show Function.update gs (lastIx D) (rowShift S k (gs (lastIx D))) ⟨(lastIx D : ℕ), hjm⟩ =
          rowShift S k (gs (lastIx D)) from Function.update_self _ _ _]
      rfl
  · rw [dite_eq_right hjm, dite_eq_right hjm]

end GlobalTheory.LastRowMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionPairingInvariantLastVertexLevel
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LastVertexInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

open GlobalTheory.ExpansionInvariance in
theorem pairPts_last_invariant (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T}
    (hL : L.Is μ₀) (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (ht : t ∈ U) (hβ : β ∈ S.supp t Φ) (hτ : S.IsExpansion t Φ β τ)
    (hv : ∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i))
    (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m)))
    (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.grid D.R.m D.R.m))
    (hx : x D.R.m = finEmb G.sp.topDec (y D.R.m)) (hk : finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl) :
    pairPts S τ (Function.update x D.R.m (finEmb G.sp.topDec (y D.R.m * k))) (Function.update y D.R.m (y D.R.m * k))
        (Ψ (Function.update x D.R.m (finEmb G.sp.topDec (y D.R.m * k)) 0)) (F (Function.update y D.R.m (y D.R.m * k) 0)) =
      pairPts S τ x y (Ψ (x 0)) (F (y 0)) := by
  have hm := D.R.two_le_m
  have h0x : Function.update x D.R.m (finEmb G.sp.topDec (y D.R.m * k)) 0 = x 0 :=
    Function.update_of_ne (by omega) _ _
  have h0y : Function.update y D.R.m (y D.R.m * k) 0 = y 0 := Function.update_of_ne (by omega) _ _
  rw [h0x, h0y, GlobalTheory.FunObj.SumModel.finEmb_mul, ← hx]
  have hth : ∀ d ∈ τ.support, (∀ j, IsThetaFunO W.ψ _ _ (S.Z.vec (d.1 j))) ∧ ∀ i, IsThetaFunO W.ψ _ _ (S.Z.vec (d.2 i)) :=
    fun d hd => ⟨fun j => vec_theta S (defPair_top t j) (inRange_top t j) _ ((hv d hd).1 j),
      fun i => vec_theta S (defPair_chi i) (inRange_chi i) _ ((hv d hd).2 i)⟩
  obtain ⟨M, hM⟩ := GlobalTheory.ArrowMultilinear.pairing_multilinear S t x y (Ψ (x 0)) (F (y 0))
  set uc : PureDat G t → ∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ := fun d =>
    Function.update (fun j => S.Z.vec (d.1 j)) (lastIx D) (colShift S t (finEmb G.sp.topDec k) (S.Z.vec (d.1 (lastIx D))))
    with huc
  set ur : PureDat G t → ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ := fun d =>
    Function.update (fun i => S.Z.vec (d.2 i)) (lastIx D) (rowShift S k (S.Z.vec (d.2 (lastIx D)))) with hur
  have thc : ∀ d ∈ τ.support, ∀ j, IsThetaFunO W.ψ _ _ (uc d j) := by
    intro d hd j
    by_cases hj : j = lastIx D
    · subst hj
      simp only [huc, Function.update_self]
      exact colShift_theta S t _ ((hth d hd).1 _)
    · simp only [huc, Function.update_of_ne hj]
      exact (hth d hd).1 j
  have thr : ∀ d ∈ τ.support, ∀ i, IsThetaFunO W.ψ _ _ (ur d i) := by
    intro d hd i
    by_cases hi : i = lastIx D
    · subst hi
      simp only [hur, Function.update_self]
      exact rowShift_theta S k ((hth d hd).2 _)
    · simp only [hur, Function.update_of_ne hi]
      exact (hth d hd).2 i
  have lhs : pairPts S τ (Function.update x D.R.m (x D.R.m * finEmb G.sp.topDec k)) (Function.update y D.R.m (y D.R.m * k))
      (Ψ (x 0)) (F (y 0)) = τ.sum fun d a => a * M (fun j => toTh W _ (uc d j)) (fun i => toTh W _ (ur d i)) := by
    simp only [pairPts, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun d hd => ?_
    congr 1
    rw [hM, colMap_eq, rowMap_eq, GlobalTheory.LastColumnMove.colMapV_update_last S _ x _ ((hth d hd).1 _), GlobalTheory.LastRowMove.rowMapV_update_last S _ y _ ((hth d hd).2 _)]
    have e1 : (fun j : Fin D.R.m => (toTh W _ (uc d j) : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ)) = uc d :=
      funext fun j => coe_toTh W _ (thc d hd j)
    have e2 : (fun i : Fin D.R.m => (toTh W _ (ur d i) : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)) = ur d :=
      funext fun i => coe_toTh W _ (thr d hd i)
    rw [e1, e2]
  have rhs : pairPts S τ x y (Ψ (x 0)) (F (y 0)) =
      τ.sum fun d a => a * M (fun j => toTh W _ (S.Z.vec (d.1 j))) (fun i => toTh W _ (S.Z.vec (d.2 i))) := by
    simp only [pairPts, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun d hd => ?_
    congr 1
    rw [hM, colMap_eq, rowMap_eq]
    have e1 : (fun j : Fin D.R.m => (toTh W _ (S.Z.vec (d.1 j)) : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ)) = fun j : Fin D.R.m => S.Z.vec (d.1 j) :=
      funext fun j => coe_toTh W _ ((hth d hd).1 j)
    have e2 : (fun i : Fin D.R.m => (toTh W _ (S.Z.vec (d.2 i)) : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)) =
        fun i : Fin D.R.m => S.Z.vec (d.2 i) :=
      funext fun i => coe_toTh W _ ((hth d hd).2 i)
    rw [e1, e2]
  rw [lhs, rhs]
  refine GlobalTheory.funProd_multilinear_sum_eq M τ _ _ _ _ fun w v => ?_
  have key := GlobalTheory.T.productFunction_totalTensor_invariant_lastArrows S hL hde hc ht hβ hτ hv k hk w v
  simp only [Finsupp.sum] at key ⊢
  refine (Finset.sum_congr rfl fun d hd => ?_).trans (key.trans (Finset.sum_congr rfl fun d hd => ?_))
  · simp only [coe_toTh W _ (thc d hd _), coe_toTh W _ (thr d hd _)]
    rfl
  · simp only [coe_toTh W _ ((hth d hd).1 _), coe_toTh W _ ((hth d hd).2 _)]

end GlobalTheory.LastVertexInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionPairingInvariantLastVertexLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansion_pairing_invariant_last_vertex_level : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) →
    (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) →
    t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))),
    ∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.grid D.R.m D.R.m)),
      x D.R.m = finEmb G.sp.topDec (y D.R.m) → finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl →
      pairPts S τ (Function.update x D.R.m (finEmb G.sp.topDec (y D.R.m * k))) (Function.update y D.R.m (y D.R.m * k))
        (Ψ (Function.update x D.R.m (finEmb G.sp.topDec (y D.R.m * k)) 0)) (F (Function.update y D.R.m (y D.R.m * k) 0)) =
      pairPts S τ x y (Ψ (x 0)) (F (y 0)) := by
  first | exact @GlobalTheory.LastVertexInv.pairPts_last_invariant | exact GlobalTheory.LastVertexInv.pairPts_last_invariant | (intros; apply GlobalTheory.LastVertexInv.pairPts_last_invariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalisedKernelExpansionSumLevelInvariant
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.ExpansionInvariance

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem levels_invariant (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T}
    (hL : L.Is μ₀) (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (ht : t ∈ U)
    (hβ : β ∈ S.supp t Φ) (hτ : S.IsExpansion t Φ β τ)
    (hv : ∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i))
    (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))) :
    (∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (j : ℕ) (hj : 0 < j) (hjm : j < D.R.m) (k : FinPt G (.top j)),
      finG (G.V (.top j)) k ∈ S.levTop t Φ β j hjm →
      pairPts S τ (Function.update x j (x j * k)) y (Ψ (Function.update x j (x j * k) 0)) (F (y 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0))) ∧
    ((∀ (x : FinPt G (.top 0)) (k : FinPt G (.top 0)), finG (G.V (.top 0)) k ∈ G.Kplus → Ψ (x * k) = Ψ x) →
    ∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.top 0)),
      finG (G.V (.top 0)) k ∈ S.levTop t Φ β 0 (by have := D.R.two_le_m; omega) →
      pairPts S τ (Function.update x 0 (x 0 * k)) y (Ψ (x 0 * k)) (F (y 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0))) ∧
    (∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (i : ℕ) (hi : 0 < i) (him : i < D.R.m) (k : FinPt G (.grid i D.R.m)),
      finG (G.V (.grid i D.R.m)) k ∈ S.levRow t i him.le →
      pairPts S τ x (Function.update y i (y i * k)) (Ψ (x 0)) (F (Function.update y i (y i * k) 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0))) ∧
    (∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.grid D.R.m D.R.m)),
      x D.R.m = finEmb G.sp.topDec (y D.R.m) → finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl →
      pairPts S τ (Function.update x D.R.m (finEmb G.sp.topDec (y D.R.m * k))) (Function.update y D.R.m (y D.R.m * k))
        (Ψ (Function.update x D.R.m (finEmb G.sp.topDec (y D.R.m * k)) 0)) (F (Function.update y D.R.m (y D.R.m * k) 0)) =
      pairPts S τ x y (Ψ (x 0)) (F (y 0))) :=
  ⟨GlobalTheory.T.expansionPairing_invariant_inner_vertex_level S hL hde hc ht hβ hτ hv Ψ F, GlobalTheory.T.expansionPairing_invariant_parabolic_basePoint S hL hde hc ht hβ hτ hv Ψ F,
    GlobalTheory.T.expansionPairing_invariant_innerVertex_level S hL hde hc ht hβ hτ hv Ψ F, GlobalTheory.T.expansion_pairing_invariant_last_vertex_level S hL hde hc ht hβ hτ hv Ψ F⟩

end GlobalTheory.ExpansionInvariance

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalisedKernelExpansionSumLevelInvariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedKernelExpansionSum_levelInvariant : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ → (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) → ∀ (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))),
    (∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (j : ℕ) (hj : 0 < j) (hjm : j < D.R.m) (k : FinPt G (.top j)),
      finG (G.V (.top j)) k ∈ S.levTop t Φ β j hjm →
      pairPts S τ (Function.update x j (x j * k)) y (Ψ (Function.update x j (x j * k) 0)) (F (y 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0))) ∧
    ((∀ (x : FinPt G (.top 0)) (k : FinPt G (.top 0)), finG (G.V (.top 0)) k ∈ G.Kplus → Ψ (x * k) = Ψ x) →
    ∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.top 0)),
      finG (G.V (.top 0)) k ∈ S.levTop t Φ β 0 (by have := D.R.two_le_m; omega) →
      pairPts S τ (Function.update x 0 (x 0 * k)) y (Ψ (x 0 * k)) (F (y 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0))) ∧
    (∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (i : ℕ) (hi : 0 < i) (him : i < D.R.m) (k : FinPt G (.grid i D.R.m)),
      finG (G.V (.grid i D.R.m)) k ∈ S.levRow t i him.le →
      pairPts S τ x (Function.update y i (y i * k)) (Ψ (x 0)) (F (Function.update y i (y i * k) 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0))) ∧
    (∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.grid D.R.m D.R.m)),
      x D.R.m = finEmb G.sp.topDec (y D.R.m) → finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl →
      pairPts S τ (Function.update x D.R.m (finEmb G.sp.topDec (y D.R.m * k))) (Function.update y D.R.m (y D.R.m * k))
        (Ψ (Function.update x D.R.m (finEmb G.sp.topDec (y D.R.m * k)) 0)) (F (Function.update y D.R.m (y D.R.m * k) 0)) =
      pairPts S τ x y (Ψ (x 0)) (F (y 0))) := by
  first | exact @GlobalTheory.ExpansionInvariance.levels_invariant | exact GlobalTheory.ExpansionInvariance.levels_invariant | (intros; apply GlobalTheory.ExpansionInvariance.levels_invariant <;> assumption)
end
