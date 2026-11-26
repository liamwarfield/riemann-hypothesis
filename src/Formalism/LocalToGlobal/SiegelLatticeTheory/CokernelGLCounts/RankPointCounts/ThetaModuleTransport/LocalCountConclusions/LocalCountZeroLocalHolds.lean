module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.AssembleG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.FwdEx

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.AssembleL
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.ThetaPMem
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.FormPair
noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}
variable (hcj : ∀ x, cj (cj x) = x) (hO : ∀ x ∈ O, cj x ∈ O) (t t' : O)
variable {Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O}
include hcj

theorem form_pair (ht : cj (t : E) = t) (ht' : cj (t' : E) = t')
    (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hκ₁ : (Z₁.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0)
    (hκ₂ : (Z₂.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0)
    (hG₁ : IsUnit (gramC cj (Z₁.map O.subtype) t t').det)
    (hG₂ : IsUnit (gramC cj (Z₂.map O.subtype) t t').det)
    (p : PairSet O cj hO Z₁ Z₂) (Y W : Ix r → O) :
    formC O cj (Z₂.map O.subtype) t t'
        (Sum.elim (liftOf O p.1.1.toLinearMap fun j => Y (Sum.inl j))
          (liftOf O p.1.2.toLinearMap fun j => Y (Sum.inr j)))
        (Sum.elim (liftOf O p.1.1.toLinearMap fun j => W (Sum.inl j))
          (liftOf O p.1.2.toLinearMap fun j => W (Sum.inr j))) -
      formC O cj (Z₁.map O.subtype) t t' Y W ∈ O := by
  have hl : ∀ y : Fin (r + 1) → O, (Submodule.Quotient.mk (liftOf O p.1.1.toLinearMap y) : MbMod Z₂) =
      p.1.1.toLinearMap (Submodule.Quotient.mk y) := fun y => liftOf_spec O _ y
  have hr : ∀ y : Fin (r + 1) → O, (Submodule.Quotient.mk (liftOf O p.1.2.toLinearMap y) : MbMod (cjT O cj hO Z₂)) =
      p.1.2.toLinearMap (Submodule.Quotient.mk y) := fun y => liftOf_spec O _ y
  have hb : ∀ y y' : Fin (r + 1) → O,
      bRaw O cj Z₂ (liftOf O p.1.1.toLinearMap y) (liftOf O p.1.2.toLinearMap y') - bRaw O cj Z₁ y y' ∈ O :=
    fun y y' => p.2.2.2 y y' _ _ (hl y).symm (hr y').symm
  have hL : ∀ y : Fin (r + 1) → O,
      lamC (Z₂.map O.subtype) (fun j => ((liftOf O p.1.1.toLinearMap y j : O) : E)) =
        lamC (Z₁.map O.subtype) (fun j => ((y j : O) : E)) := by
    intro y
    have key := lam_keep O hu₁ hu₂ p.1.1.toLinearMap p.2.1.1 y _ (hl y).symm
    simpa [lamL_apply] using key
  have hS : ∀ y : Fin (r + 1) → O,
      lamStarC cj (Z₂.map O.subtype) (fun j => ((liftOf O p.1.2.toLinearMap y j : O) : E)) =
        lamStarC cj (Z₁.map O.subtype) (fun j => ((y j : O) : E)) :=
    fun y => p.2.2.1 y _ (hr y).symm
  rw [formC_eq O cj hcj Z₂ hu₂ hκ₂ _ _ hG₂, formC_eq O cj hcj Z₁ hu₁ hκ₁ _ _ hG₁]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [hL, hL, hS, hS]
  have key := O.add_mem (hb (fun j => Y (Sum.inl j)) (fun j => W (Sum.inr j)))
    (hO _ (hb (fun j => W (Sum.inl j)) (fun j => Y (Sum.inr j))))
  rw [map_sub] at key
  convert key using 1
  ring

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
end
end

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}
theorem elim_sub (a b c d : Fin (r + 1) → O) :
    (Sum.elim a b : Ix r → O) - Sum.elim c d = Sum.elim (a - c) (b - d) := by
  funext i; cases i <;> rfl

variable (hcj : ∀ x, cj (cj x) = x) (hO : ∀ x ∈ O, cj x ∈ O) (t t' : O)
variable {Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O}
include hcj

def thetaP (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hκ₁ : (Z₁.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0)
    (hκ₂ : (Z₂.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0) (p : PairSet O cj hO Z₁ Z₂) :
    DDc O cj (Z₁.map O.subtype) t t' ≃ₗ[O] DDc O cj (Z₂.map O.subtype) t t' :=
  thetaOf O cj hO t t' p.1.1 p.1.2 p.2.1.1 p.2.1.2 (pair_b O cj hcj hO hu₁ hu₂ p)
    (pair_e O cj hcj hO hu₁ hu₂ hκ₁ hκ₂ p)

private theorem thetaP_mk_eq_mk_sum_elim_liftOf (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hκ₁ : (Z₁.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0)
    (hκ₂ : (Z₂.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0) (p : PairSet O cj hO Z₁ Z₂)
    (Y : Ix r → O) :
    thetaP O cj hcj hO t t' hu₁ hu₂ hκ₁ hκ₂ p (Submodule.Quotient.mk Y) =
      Submodule.Quotient.mk (Sum.elim (liftOf O p.1.1.toLinearMap fun j => Y (Sum.inl j))
        (liftOf O p.1.2.toLinearMap fun j => Y (Sum.inr j))) := rfl

private theorem mk_sum_elim_eq_of_sub_mem_headCols (a a' b b' : Fin (r + 1) → O) (ha : a - a' ∈ headCols Z₂)
    (hb : b - b' ∈ headCols (cjT O cj hO Z₂)) :
    (Submodule.Quotient.mk (Sum.elim a b) : DDc O cj (Z₂.map O.subtype) t t') =
      Submodule.Quotient.mk (Sum.elim a' b') := by
  apply (Submodule.Quotient.eq _).mpr
  rw [elim_sub]
  exact mem_relC_of_K O cj hO Z₂ t t' _ _ ha hb

private theorem lamC_eq_of_pairSet_mk_eq (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (p : PairSet O cj hO Z₁ Z₂) (y y₂ : Fin (r + 1) → O)
    (h : p.1.1 (Submodule.Quotient.mk y) = Submodule.Quotient.mk y₂) :
    lamC (Z₂.map O.subtype) (fun j => ((y₂ j : O) : E)) = lamC (Z₁.map O.subtype) (fun j => ((y j : O) : E)) := by
  have key := lam_keep O hu₁ hu₂ p.1.1.toLinearMap p.2.1.1 y y₂ h
  simpa [lamL_apply] using key

theorem thetaP_mem (ht : cj (t : E) = t) (ht' : cj (t' : E) = t')
    (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hκ₁ : (Z₁.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0)
    (hκ₂ : (Z₂.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0)
    (hG₁ : IsUnit (gramC cj (Z₁.map O.subtype) t t').det)
    (hG₂ : IsUnit (gramC cj (Z₂.map O.subtype) t t').det)
    (p : PairSet O cj hO Z₁ Z₂) :
    thetaP O cj hcj hO t t' hu₁ hu₂ hκ₁ hκ₂ p ∈ ThetaC O cj (Z₁.map O.subtype) (Z₂.map O.subtype) t t' := by
  have hl : ∀ y : Fin (r + 1) → O,
      p.1.1 (Submodule.Quotient.mk (liftOf O p.1.1.symm.toLinearMap y)) = Submodule.Quotient.mk y := by
    intro y
    rw [liftOf_spec]
    exact p.1.1.apply_symm_apply _
  have hr : ∀ y : Fin (r + 1) → O,
      p.1.2 (Submodule.Quotient.mk (liftOf O p.1.2.symm.toLinearMap y)) = Submodule.Quotient.mk y := by
    intro y
    rw [liftOf_spec]
    exact p.1.2.apply_symm_apply _
  have he2 := pair_e O cj hcj hO hu₁ hu₂ hκ₁ hκ₂ p
  refine ⟨?_, ?_, ?_⟩
  · intro Y W Y₂ W₂ hY hW
    rw [thetaP_mk_eq_mk_sum_elim_liftOf] at hY hW
    have hY' := (Submodule.Quotient.eq _).mp hY.symm
    have hW' := (Submodule.Quotient.eq _).mp hW.symm
    have e1 : formC O cj (Z₂.map O.subtype) t t' Y₂ W₂ - formC O cj (Z₁.map O.subtype) t t' Y W =
        formC O cj (Z₂.map O.subtype) t t' (Y₂ - Sum.elim (liftOf O p.1.1.toLinearMap fun j => Y (Sum.inl j))
            (liftOf O p.1.2.toLinearMap fun j => Y (Sum.inr j))) W₂ +
          formC O cj (Z₂.map O.subtype) t t' (Sum.elim (liftOf O p.1.1.toLinearMap fun j => Y (Sum.inl j))
            (liftOf O p.1.2.toLinearMap fun j => Y (Sum.inr j)))
            (W₂ - Sum.elim (liftOf O p.1.1.toLinearMap fun j => W (Sum.inl j))
              (liftOf O p.1.2.toLinearMap fun j => W (Sum.inr j))) +
          (formC O cj (Z₂.map O.subtype) t t'
            (Sum.elim (liftOf O p.1.1.toLinearMap fun j => Y (Sum.inl j))
              (liftOf O p.1.2.toLinearMap fun j => Y (Sum.inr j)))
            (Sum.elim (liftOf O p.1.1.toLinearMap fun j => W (Sum.inl j))
              (liftOf O p.1.2.toLinearMap fun j => W (Sum.inr j))) -
            formC O cj (Z₁.map O.subtype) t t' Y W) := by
      rw [formC_sub_left, formC_sub_right]
      ring
    rw [e1]
    exact O.add_mem (O.add_mem (formC_rel_left O cj _ _ _ hG₂ hO _ _ hY')
      (formC_rel_right O cj hcj _ _ _ ht ht' hG₂ hO _ _ hW'))
      (form_pair O cj hcj hO t t' ht ht' hu₁ hu₂ hκ₁ hκ₂ hG₁ hG₂ p Y W)
  · apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨Y, hY0, rfl⟩, rfl⟩
      simp only [GamC, Set.mem_setOf_eq]
      refine ⟨Sum.elim (Y (Sum.inl (Fin.last r)) • Pi.single (Fin.last r) 1)
        (liftOf O p.1.2.toLinearMap fun j => Y (Sum.inr j)), fun a => ?_, ?_⟩
      · simp [Pi.single_apply, Fin.castSucc_ne_last]
      · refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · show thetaP O cj hcj hO t t' hu₁ hu₂ hκ₁ hκ₂ p (Submodule.Quotient.mk Y) = _
          rw [thetaP_mk_eq_mk_sum_elim_liftOf, supp_inl O Y hY0]
          exact mk_sum_elim_eq_of_sub_mem_headCols O cj hcj hO t t' _ _ _ _ (lift_e_mem O (f := p.1.1.toLinearMap) p.2.1.2 _)
            (by rw [sub_self]; exact zero_mem _)
        · simp
        · exact (p.2.2.1 _ _ (liftOf_spec O _ _).symm).symm
    · rintro _ ⟨Y₂, hY0, rfl⟩
      refine ⟨(Submodule.Quotient.mk (Sum.elim (Y₂ (Sum.inl (Fin.last r)) • Pi.single (Fin.last r) 1)
          (liftOf O p.1.2.symm.toLinearMap fun j => Y₂ (Sum.inr j))),
          (((Sum.elim (Y₂ (Sum.inl (Fin.last r)) • Pi.single (Fin.last r) 1)
            (liftOf O p.1.2.symm.toLinearMap fun j => Y₂ (Sum.inr j)) : Ix r → O) (Sum.inl (Fin.last r)) : O) : E),
          lamStarC cj (Z₁.map O.subtype) fun b => (((Sum.elim (Y₂ (Sum.inl (Fin.last r)) • Pi.single (Fin.last r) 1)
            (liftOf O p.1.2.symm.toLinearMap fun j => Y₂ (Sum.inr j)) : Ix r → O) (Sum.inr b) : O) : E)), ?_, ?_⟩
      · simp only [GamC, Set.mem_setOf_eq]
        refine ⟨_, fun a => ?_, rfl⟩
        simp [Pi.single_apply, Fin.castSucc_ne_last]
      · have hY₂ : Y₂ = Sum.elim (Y₂ (Sum.inl (Fin.last r)) • Pi.single (Fin.last r) 1) (fun j => Y₂ (Sum.inr j)) := by
          rw [← supp_inl O Y₂ hY0]
          exact elim_eta O Y₂
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · show thetaP O cj hcj hO t t' hu₁ hu₂ hκ₁ hκ₂ p (Submodule.Quotient.mk _) = Submodule.Quotient.mk Y₂
          rw [thetaP_mk_eq_mk_sum_elim_liftOf]
          conv_rhs => rw [hY₂]
          exact mk_sum_elim_eq_of_sub_mem_headCols O cj hcj hO t t' _ _ _ _ (lift_e_mem O (f := p.1.1.toLinearMap) p.2.1.2 _)
            (lift_rep_mem O p.1.2 _ _ (liftOf_spec O _ _))
        · simp
        · exact (p.2.2.1 _ _ (hr _)).symm
  · apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨Y, hY0, rfl⟩, rfl⟩
      simp only [GamC', Set.mem_setOf_eq]
      refine ⟨Sum.elim (liftOf O p.1.1.toLinearMap fun j => Y (Sum.inl j))
        (Y (Sum.inr (Fin.last r)) • Pi.single (Fin.last r) 1), fun a => ?_, ?_⟩
      · simp [Pi.single_apply, Fin.castSucc_ne_last]
      · refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · show thetaP O cj hcj hO t t' hu₁ hu₂ hκ₁ hκ₂ p (Submodule.Quotient.mk Y) = _
          rw [thetaP_mk_eq_mk_sum_elim_liftOf, supp_inr O Y hY0]
          exact mk_sum_elim_eq_of_sub_mem_headCols O cj hcj hO t t' _ _ _ _ (by rw [sub_self]; exact zero_mem _)
            (lift_e_mem O (f := p.1.2.toLinearMap) he2 _)
        · exact (lamC_eq_of_pairSet_mk_eq O cj hcj hO hu₁ hu₂ p _ _ (liftOf_spec O _ _).symm).symm
        · simp
    · rintro _ ⟨Y₂, hY0, rfl⟩
      refine ⟨(Submodule.Quotient.mk (Sum.elim (liftOf O p.1.1.symm.toLinearMap fun j => Y₂ (Sum.inl j))
          (Y₂ (Sum.inr (Fin.last r)) • Pi.single (Fin.last r) 1)),
          lamC (Z₁.map O.subtype) fun a => (((Sum.elim (liftOf O p.1.1.symm.toLinearMap fun j => Y₂ (Sum.inl j))
            (Y₂ (Sum.inr (Fin.last r)) • Pi.single (Fin.last r) 1) : Ix r → O) (Sum.inl a) : O) : E),
          (((Sum.elim (liftOf O p.1.1.symm.toLinearMap fun j => Y₂ (Sum.inl j))
            (Y₂ (Sum.inr (Fin.last r)) • Pi.single (Fin.last r) 1) : Ix r → O) (Sum.inr (Fin.last r)) : O) : E)),
          ?_, ?_⟩
      · simp only [GamC', Set.mem_setOf_eq]
        refine ⟨_, fun a => ?_, rfl⟩
        simp [Pi.single_apply, Fin.castSucc_ne_last]
      · have hY₂ : Y₂ = Sum.elim (fun j => Y₂ (Sum.inl j)) (Y₂ (Sum.inr (Fin.last r)) • Pi.single (Fin.last r) 1) := by
          rw [← supp_inr O Y₂ hY0]
          exact elim_eta O Y₂
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · show thetaP O cj hcj hO t t' hu₁ hu₂ hκ₁ hκ₂ p (Submodule.Quotient.mk _) = Submodule.Quotient.mk Y₂
          rw [thetaP_mk_eq_mk_sum_elim_liftOf]
          conv_rhs => rw [hY₂]
          exact mk_sum_elim_eq_of_sub_mem_headCols O cj hcj hO t t' _ _ _ _ (lift_rep_mem O p.1.1 _ _ (liftOf_spec O _ _))
            (lift_e_mem O (f := p.1.2.toLinearMap) he2 _)
        · exact (lamC_eq_of_pairSet_mk_eq O cj hcj hO hu₁ hu₂ p _ _ (hl _)).symm
        · simp

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.AlgTop
namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

theorem locCnt0L_of_stepPair (h : StepPair) : Formalism.L2.SG.LocalCountModules.LocCnt0L.LocCnt0L :=
  locCnt0L_of_pair h stepInj Formalism.L2.SG.LocalCountModules.UnramifiedPairingLinear.stepAdj

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
end

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.LocCnt0LAlg Formalism.L2.SG.LocalCountModules.UnramifiedPairingLinear

namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

theorem card_of_constr (hO : ∀ x ∈ O, cj x ∈ O) (t t' : O)
    (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
    (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hη₂ : EtaNZD O cj Z₂ (t : E) (t' : E))
    (hf' : ∀ θ ∈ ThetaC O cj (Z₁.map O.subtype) (Z₂.map O.subtype) t t',
      ∃ p : PairSet O cj hO Z₁ Z₂, (∀ m, θ (iL O cj hO Z₁ t t' m) = iL O cj hO Z₂ t t' (p.1.1 m)) ∧
        ∀ m, θ (iR O cj hO Z₁ t t' m) = iR O cj hO Z₂ t t' (p.1.2 m))
    (hb' : ∀ p : PairSet O cj hO Z₁ Z₂, ∃ θ ∈ ThetaC O cj (Z₁.map O.subtype) (Z₂.map O.subtype) t t',
      (∀ m, θ (iL O cj hO Z₁ t t' m) = iL O cj hO Z₂ t t' (p.1.1 m)) ∧
        ∀ m, θ (iR O cj hO Z₁ t t' m) = iR O cj hO Z₂ t t' (p.1.2 m)) :
    Nat.card (ThetaC O cj (Z₁.map O.subtype) (Z₂.map O.subtype) t t') =
      Nat.card (PairSet O cj hO Z₁ Z₂) := by
  choose F hF using hf'
  choose G hGmem hG using hb'
  have lamP : ∀ (q : PairSet O cj hO Z₁ Z₂) (m : MbMod Z₁),
      lamLQ O Z₂ hu₂ (q.1.1 m) = lamLQ O Z₁ hu₁ m := by
    intro q m
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    obtain ⟨y₂, hy₂⟩ := Submodule.Quotient.mk_surjective _ (q.1.1 (Submodule.Quotient.mk y))
    rw [← hy₂, lamLQ_mk, lamLQ_mk]
    exact lam_keep O hu₁ hu₂ (q.1.1 : MbMod Z₁ →ₗ[O] MbMod Z₂) q.2.1.1 y y₂ hy₂.symm
  have lamQ : ∀ (q : PairSet O cj hO Z₁ Z₂) (m : MbMod (cjT O cj hO Z₁)),
      lamSQ O cj hO Z₂ hu₂ (q.1.2 m) = lamSQ O cj hO Z₁ hu₁ m := by
    intro q m
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    obtain ⟨y₂, hy₂⟩ := Submodule.Quotient.mk_surjective _ (q.1.2 (Submodule.Quotient.mk y))
    rw [← hy₂, lamSQ_mk, lamSQ_mk]
    exact q.2.2.1 y y₂ hy₂.symm
  let f : ↥(ThetaC O cj (Z₁.map O.subtype) (Z₂.map O.subtype) (t : E) (t' : E)) →
      PairSet O cj hO Z₁ Z₂ := fun θ => F θ.1 θ.2
  let g : PairSet O cj hO Z₁ Z₂ →
      ↥(ThetaC O cj (Z₁.map O.subtype) (Z₂.map O.subtype) (t : E) (t' : E)) :=
    fun p => ⟨G p, hGmem p⟩
  have hfi : Function.Injective f := by
    intro θ θ' hθ
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hv : v = Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) := (Sum.elim_comp_inl_inr v).symm
    rw [hv, mk_elim O cj hO Z₁ t t', map_add (f := _), map_add (f := _), (hF θ.1 θ.2).1, (hF θ.1 θ.2).2,
      (hF θ'.1 θ'.2).1, (hF θ'.1 θ'.2).2]
    change f θ = f θ' at hθ
    simp only [f] at hθ
    rw [hθ]
  have hgi : Function.Injective g := by
    intro p p' hp
    have h1 : G p = G p' := congrArg Subtype.val hp
    have k1 : ∀ m, p.1.1 m = p'.1.1 m := by
      intro m
      apply uniqL O cj hO Z₂ hu₂ t t' hη₂
      · rw [← (hG p).1, ← (hG p').1, h1]
      · rw [lamP p m, lamP p' m]
    have k2 : ∀ m, p.1.2 m = p'.1.2 m := by
      intro m
      apply uniqR O cj hO Z₂ hu₂ t t' hη₂
      · rw [← (hG p).2, ← (hG p').2, h1]
      · rw [lamQ p m, lamQ p' m]
    apply Subtype.ext
    apply Prod.ext
    · exact LinearEquiv.ext k1
    · exact LinearEquiv.ext k2
  obtain ⟨e, he⟩ := Function.Embedding.schroeder_bernstein hfi hgi
  exact Nat.card_congr (Equiv.ofBijective e he)

theorem bwd0 (hcj : ∀ x, cj (cj x) = x) (hO : ∀ x ∈ O, cj x ∈ O) (t t' : O)
    (ht : cj (t : E) = t) (ht' : cj (t' : E) = t') {Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O}
    (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hκ₁ : (Z₁.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0)
    (hκ₂ : (Z₂.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0)
    (hG₁ : IsUnit (gramC cj (Z₁.map O.subtype) t t').det)
    (hG₂ : IsUnit (gramC cj (Z₂.map O.subtype) t t').det) (p : PairSet O cj hO Z₁ Z₂) :
    ∃ θ ∈ ThetaC O cj (Z₁.map O.subtype) (Z₂.map O.subtype) t t',
      (∀ m, θ (iL O cj hO Z₁ t t' m) = iL O cj hO Z₂ t t' (p.1.1 m)) ∧
        ∀ m, θ (iR O cj hO Z₁ t t' m) = iR O cj hO Z₂ t t' (p.1.2 m) := by
  refine ⟨thetaP O cj hcj hO t t' hu₁ hu₂ hκ₁ hκ₂ p,
    thetaP_mem O cj hcj hO t t' ht ht' hu₁ hu₂ hκ₁ hκ₂ hG₁ hG₂ p, ?_, ?_⟩
  · intro m
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    have hy : p.1.1 (Submodule.Quotient.mk y) =
        Submodule.Quotient.mk (liftOf O (p.1.1 : MbMod Z₁ →ₗ[O] MbMod Z₂) y) :=
      (liftOf_spec O _ y).symm
    rw [iL_mk, hy, iL_mk]
    simp only [thetaP, thetaOf]
    erw [LinearEquiv.ofLinear_apply, Submodule.mapQ_apply, sumMap_apply]
    congr 1
    funext i
    cases i <;> simp <;> exact congrFun (map_zero _) _
  · intro m
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    have hy : p.1.2 (Submodule.Quotient.mk y) =
        Submodule.Quotient.mk
          (liftOf O (p.1.2 : MbMod (cjT O cj hO Z₁) →ₗ[O] MbMod (cjT O cj hO Z₂)) y) :=
      (liftOf_spec O _ y).symm
    rw [iR_mk, hy, iR_mk]
    simp only [thetaP, thetaOf]
    erw [LinearEquiv.ofLinear_apply, Submodule.mapQ_apply, sumMap_apply]
    congr 1
    funext i
    cases i <;> simp <;> exact congrFun (map_zero _) _

theorem stepPair_of_fwd (hf : FwdEx) : StepPair := by
  intro E _ O cj hcj hO r T T' hT hT' hcT hcT' Z₁ Z₂ hu₁ hu₂ hs₁ hs₂ hg₁ hg₂
  obtain ⟨t, rfl⟩ : ∃ t : O, (t : E) = T := ⟨⟨T, hT⟩, rfl⟩
  obtain ⟨t', rfl⟩ : ∃ t' : O, (t' : E) = T' := ⟨⟨T', hT'⟩, rfl⟩
  have hκ₁ : (Z₁.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0 :=
    hu₁.mul_left_eq_zero.mp ((kap_mul_det O Z₁ hu₁).trans hs₁)
  have hκ₂ : (Z₂.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0 :=
    hu₂.mul_left_eq_zero.mp ((kap_mul_det O Z₂ hu₂).trans hs₂)
  have hk : kap O Z₂ = kap O Z₁ := hκ₂.trans hκ₁.symm
  have hη : EtaNZD O cj Z₂ (t : E) (t' : E) := fun u hu => eta_nzd O cj hcj Z₂ hu₂ _ _ hg₂ u hu
  exact card_of_constr O cj hO t t' Z₁ Z₂ hu₁ hu₂ hη
    (hf E O cj hcj hO r t t' hcT hcT' Z₁ Z₂ hu₁ hu₂ hk hg₁ hg₂)
    (bwd0 O cj hcj hO t t' hcT hcT' hu₁ hu₂ hκ₁ hκ₂ hg₁ hg₂)

theorem locCnt0L_of_fwd (hf : FwdEx) : Formalism.L2.SG.LocalCountModules.LocCnt0L.LocCnt0L :=
  locCnt0L_of_stepPair (stepPair_of_fwd hf)

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic
end
end

namespace Formalism.L2.SG.LocalCountModules

theorem localCountZeroLocal_holds : Formalism.L2.SG.LocalCountModules.LocCnt0L.LocCnt0L :=
  Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic.locCnt0L_of_fwd Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic.fwdEx

end Formalism.L2.SG.LocalCountModules
