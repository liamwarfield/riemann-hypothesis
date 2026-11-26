module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.PairGSteps

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.ElimSplit
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.GsEquivSpec
noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.LocCnt0LAlg Formalism.L2.SG.LocalCountModules.UnramifiedPairingLinear

namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}
variable (hO : ∀ x ∈ O, cj x ∈ O)
include hO

theorem rel_b (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (t t' : O) :
    iL O cj hO Z t t' (bCls Z) = iR O cj hO Z t t' (t' • eCl (cjT O cj hO Z)) := by
  unfold bCls eCl
  rw [map_smul, iL, iR, Submodule.liftQ_apply, Submodule.liftQ_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.eq, mem_relC_iff O cj hO Z t t']
  refine ⟨0, Pi.single (Fin.last r) 1, ?_, ?_⟩
  · funext j
    simp [elimL, elimR, Matrix.mulVec_single, Pi.single_apply]
  · funext j
    simp [elimL, elimR, Matrix.mulVec_zero, Pi.single_apply]

section Fwd

variable (t t' : O) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
  (θ : DDc O cj (Z₁.map O.subtype) t t' ≃ₗ[O] DDc O cj (Z₂.map O.subtype) t t')

omit hO in
theorem gam_fwd (hΓ : (fun p => (θ p.1, p.2)) '' GamC O cj (Z₁.map O.subtype) t t' = GamC O cj (Z₂.map O.subtype) t t') : ∀ p ∈ GamC O cj (Z₁.map O.subtype) t t',
    (θ.toLinearMap p.1, p.2) ∈ GamC O cj (Z₂.map O.subtype) t t' := by
  intro p hp
  rw [← hΓ]
  exact ⟨p, hp, rfl⟩

omit hO in
theorem gam_bwd (hΓ : (fun p => (θ p.1, p.2)) '' GamC O cj (Z₁.map O.subtype) t t' = GamC O cj (Z₂.map O.subtype) t t') : ∀ p ∈ GamC O cj (Z₂.map O.subtype) t t',
    (θ.symm.toLinearMap p.1, p.2) ∈ GamC O cj (Z₁.map O.subtype) t t' := by
  intro p hp
  rw [← hΓ] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  have e : θ.symm.toLinearMap (θ q.1) = q.1 := θ.symm_apply_apply q.1
  show (θ.symm.toLinearMap (θ q.1), q.2) ∈ _
  rw [e]
  exact hq

omit hO in
theorem gam_fwd' (hΓ' : (fun p => (θ p.1, p.2)) '' GamC' O cj (Z₁.map O.subtype) t t' = GamC' O cj (Z₂.map O.subtype) t t') : ∀ p ∈ GamC' O cj (Z₁.map O.subtype) t t',
    (θ.toLinearMap p.1, p.2) ∈ GamC' O cj (Z₂.map O.subtype) t t' := by
  intro p hp
  rw [← hΓ']
  exact ⟨p, hp, rfl⟩

omit hO in
theorem gam_bwd' (hΓ' : (fun p => (θ p.1, p.2)) '' GamC' O cj (Z₁.map O.subtype) t t' = GamC' O cj (Z₂.map O.subtype) t t') : ∀ p ∈ GamC' O cj (Z₂.map O.subtype) t t',
    (θ.symm.toLinearMap p.1, p.2) ∈ GamC' O cj (Z₁.map O.subtype) t t' := by
  intro p hp
  rw [← hΓ'] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  have e : θ.symm.toLinearMap (θ q.1) = q.1 := θ.symm_apply_apply q.1
  show (θ.symm.toLinearMap (θ q.1), q.2) ∈ _
  rw [e]
  exact hq

def gsEquiv (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det) (hη₁ : EtaNZD O cj Z₁ t t') (hη₂ : EtaNZD O cj Z₂ t t')
    (hΓ : (fun p => (θ p.1, p.2)) '' GamC O cj (Z₁.map O.subtype) t t' = GamC O cj (Z₂.map O.subtype) t t') :
    MbMod (cjT O cj hO Z₁) ≃ₗ[O] MbMod (cjT O cj hO Z₂) :=
  LinearEquiv.ofLinear (gsLin O cj hO t t' Z₁ Z₂ hu₁ hu₂ hη₂ θ.toLinearMap (gam_fwd O cj t t' Z₁ Z₂ θ hΓ))
    (gsLin O cj hO t t' Z₂ Z₁ hu₂ hu₁ hη₁ θ.symm.toLinearMap (gam_bwd O cj t t' Z₁ Z₂ θ hΓ))
    (by
      apply LinearMap.ext; intro m
      have s1 := gsLin_spec O cj hO t t' Z₁ Z₂ hu₁ hu₂ hη₂ θ.toLinearMap (gam_fwd O cj t t' Z₁ Z₂ θ hΓ)
      have s2 := gsLin_spec O cj hO t t' Z₂ Z₁ hu₂ hu₁ hη₁ θ.symm.toLinearMap (gam_bwd O cj t t' Z₁ Z₂ θ hΓ)
      apply uniqR O cj hO Z₂ hu₂ t t' hη₂
      · rw [LinearMap.comp_apply, ← (s1 _).1, ← (s2 m).1, LinearMap.id_apply]
        simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
      · rw [LinearMap.comp_apply, (s1 _).2, (s2 m).2, LinearMap.id_apply])
    (by
      apply LinearMap.ext; intro m
      have s1 := gsLin_spec O cj hO t t' Z₁ Z₂ hu₁ hu₂ hη₂ θ.toLinearMap (gam_fwd O cj t t' Z₁ Z₂ θ hΓ)
      have s2 := gsLin_spec O cj hO t t' Z₂ Z₁ hu₂ hu₁ hη₁ θ.symm.toLinearMap (gam_bwd O cj t t' Z₁ Z₂ θ hΓ)
      apply uniqR O cj hO Z₁ hu₁ t t' hη₁
      · rw [LinearMap.comp_apply, ← (s2 _).1, ← (s1 m).1, LinearMap.id_apply]
        simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
      · rw [LinearMap.comp_apply, (s2 _).2, (s1 m).2, LinearMap.id_apply])

def gEquiv (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det) (hη₁ : EtaNZD O cj Z₁ t t') (hη₂ : EtaNZD O cj Z₂ t t')
    (hΓ' : (fun p => (θ p.1, p.2)) '' GamC' O cj (Z₁.map O.subtype) t t' = GamC' O cj (Z₂.map O.subtype) t t') :
    MbMod Z₁ ≃ₗ[O] MbMod Z₂ :=
  LinearEquiv.ofLinear (gLin O cj hO t t' Z₁ Z₂ hu₁ hu₂ hη₂ θ.toLinearMap (gam_fwd' O cj t t' Z₁ Z₂ θ hΓ'))
    (gLin O cj hO t t' Z₂ Z₁ hu₂ hu₁ hη₁ θ.symm.toLinearMap (gam_bwd' O cj t t' Z₁ Z₂ θ hΓ'))
    (by
      apply LinearMap.ext; intro m
      have s1 := gLin_spec O cj hO t t' Z₁ Z₂ hu₁ hu₂ hη₂ θ.toLinearMap (gam_fwd' O cj t t' Z₁ Z₂ θ hΓ')
      have s2 := gLin_spec O cj hO t t' Z₂ Z₁ hu₂ hu₁ hη₁ θ.symm.toLinearMap (gam_bwd' O cj t t' Z₁ Z₂ θ hΓ')
      apply uniqL O cj hO Z₂ hu₂ t t' hη₂
      · rw [LinearMap.comp_apply, ← (s1 _).1, ← (s2 m).1, LinearMap.id_apply]
        simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
      · rw [LinearMap.comp_apply, (s1 _).2, (s2 m).2, LinearMap.id_apply])
    (by
      apply LinearMap.ext; intro m
      have s1 := gLin_spec O cj hO t t' Z₁ Z₂ hu₁ hu₂ hη₂ θ.toLinearMap (gam_fwd' O cj t t' Z₁ Z₂ θ hΓ')
      have s2 := gLin_spec O cj hO t t' Z₂ Z₁ hu₂ hu₁ hη₁ θ.symm.toLinearMap (gam_bwd' O cj t t' Z₁ Z₂ θ hΓ')
      apply uniqL O cj hO Z₁ hu₁ t t' hη₁
      · rw [LinearMap.comp_apply, ← (s2 _).1, ← (s1 m).1, LinearMap.id_apply]
        simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
      · rw [LinearMap.comp_apply, (s2 _).2, (s1 m).2, LinearMap.id_apply])

theorem gsEquiv_spec (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det) (hη₁ : EtaNZD O cj Z₁ t t') (hη₂ : EtaNZD O cj Z₂ t t')
    (hΓ : (fun p => (θ p.1, p.2)) '' GamC O cj (Z₁.map O.subtype) t t' = GamC O cj (Z₂.map O.subtype) t t') (m : MbMod (cjT O cj hO Z₁)) :
    θ (iR O cj hO Z₁ t t' m) = iR O cj hO Z₂ t t' (gsEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ m) ∧
      lamSQ O cj hO Z₂ hu₂ (gsEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ m) = lamSQ O cj hO Z₁ hu₁ m := gsLin_spec O cj hO t t' Z₁ Z₂ hu₁ hu₂ hη₂ θ.toLinearMap (gam_fwd O cj t t' Z₁ Z₂ θ hΓ) m

theorem gEquiv_spec (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det) (hη₁ : EtaNZD O cj Z₁ t t') (hη₂ : EtaNZD O cj Z₂ t t')
    (hΓ' : (fun p => (θ p.1, p.2)) '' GamC' O cj (Z₁.map O.subtype) t t' = GamC' O cj (Z₂.map O.subtype) t t') (m : MbMod Z₁) :
    θ (iL O cj hO Z₁ t t' m) = iL O cj hO Z₂ t t' (gEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ' m) ∧
      lamLQ O Z₂ hu₂ (gEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ' m) = lamLQ O Z₁ hu₁ m := gLin_spec O cj hO t t' Z₁ Z₂ hu₁ hu₂ hη₂ θ.toLinearMap (gam_fwd' O cj t t' Z₁ Z₂ θ hΓ') m

end Fwd

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic
end
end

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.LocCnt0LAlg Formalism.L2.SG.LocalCountModules.UnramifiedPairingLinear

namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}
variable (hO : ∀ x ∈ O, cj x ∈ O)
include hO

section Props

variable (t t' : O) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
  (θ : DDc O cj (Z₁.map O.subtype) t t' ≃ₗ[O] DDc O cj (Z₂.map O.subtype) t t')

theorem elim_split (Y : Ix r → O) :
    (Submodule.Quotient.mk Y : DDc O cj (Z₂.map O.subtype) t t') =
      iL O cj hO Z₂ t t' (Submodule.Quotient.mk (fun a => Y (Sum.inl a))) +
        iR O cj hO Z₂ t t' (Submodule.Quotient.mk (fun b => Y (Sum.inr b))) := by
  have e1 : iL O cj hO Z₂ t t' (Submodule.Quotient.mk (fun a => Y (Sum.inl a))) =
      (Submodule.Quotient.mk (elimL O (fun a => Y (Sum.inl a))) : DDc O cj (Z₂.map O.subtype) t t') := rfl
  have e2 : iR O cj hO Z₂ t t' (Submodule.Quotient.mk (fun b => Y (Sum.inr b))) =
      (Submodule.Quotient.mk (elimR O (fun b => Y (Sum.inr b))) : DDc O cj (Z₂.map O.subtype) t t') := rfl
  rw [e1, e2, ← Submodule.Quotient.mk_add]
  congr 1
  funext i
  rcases i with i | i <;> simp [elimL, elimR]

theorem gs_e (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hη₁ : EtaNZD O cj Z₁ t t') (hη₂ : EtaNZD O cj Z₂ t t') (hκ : kap O Z₂ = kap O Z₁)
    (hΓ : (fun p => (θ p.1, p.2)) '' GamC O cj (Z₁.map O.subtype) t t' = GamC O cj (Z₂.map O.subtype) t t')
    (hΓ' : (fun p => (θ p.1, p.2)) '' GamC' O cj (Z₁.map O.subtype) t t' = GamC' O cj (Z₂.map O.subtype) t t') :
    gsEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ (eCl (cjT O cj hO Z₁)) = eCl (cjT O cj hO Z₂) := by
  have sp := gsEquiv_spec O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ (eCl (cjT O cj hO Z₁))
  have hp : ((Submodule.Quotient.mk (Sum.elim (0 : Fin (r + 1) → O) (Pi.single (Fin.last r) 1)) :
      DDc O cj (Z₁.map O.subtype) t t'), ((0 : E), (1 : E))) ∈ GamC' O cj (Z₁.map O.subtype) t t' :=
    ⟨Sum.elim 0 (Pi.single (Fin.last r) 1), fun b => Pi.single_eq_of_ne (Fin.castSucc_ne_last b) _,
      by simp [lamC, Matrix.mulVec, dotProduct]⟩
  obtain ⟨Y₂, hY₂, he⟩ := gam_fwd' O cj t t' Z₁ Z₂ θ hΓ' _ hp
  simp only [Prod.mk.injEq] at he
  obtain ⟨h1, h2, h3⟩ := he
  have hr : (fun b => Y₂ (Sum.inr b)) = Pi.single (Fin.last r) 1 := by
    funext b
    refine Fin.lastCases ?_ (fun j => ?_) b
    · rw [Pi.single_eq_same]; exact Subtype.ext h3.symm
    · rw [hY₂ j, Pi.single_eq_of_ne (Fin.castSucc_ne_last j)]
  set gs := gsEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ
  obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (gs (eCl (cjT O cj hO Z₁)))
  have key : iR O cj hO Z₂ t t' (gs (eCl (cjT O cj hO Z₁))) =
      iL O cj hO Z₂ t t' (Submodule.Quotient.mk (fun a => Y₂ (Sum.inl a))) +
        iR O cj hO Z₂ t t' (eCl (cjT O cj hO Z₂)) := by
    rw [← sp.1, eCl, iR_mk]
    show θ (Submodule.Quotient.mk (Sum.elim 0 (Pi.single (Fin.last r) 1))) = _
    rw [show θ (Submodule.Quotient.mk (Sum.elim 0 (Pi.single (Fin.last r) 1))) = Submodule.Quotient.mk Y₂ from h1,
      elim_split O cj hO t t' Z₂, hr]
    rfl
  have hz : (Submodule.Quotient.mk (Sum.elim (fun a => Y₂ (Sum.inl a)) (Pi.single (Fin.last r) 1 - v)) :
      DDc O cj (Z₂.map O.subtype) t t') = 0 := by
    rw [mk_elim O cj hO Z₂ t t', Submodule.Quotient.mk_sub, map_sub, ← eCl, hv, key]
    abel
  have hl : lamL O Z₂ (fun a => Y₂ (Sum.inl a)) = 0 := by rw [lamL_apply]; exact h2.symm
  have hl' : lamS O cj Z₂ (Pi.single (Fin.last r) 1 - v) = 0 := by
    have e1 := sp.2
    rw [← hv, lamSQ_mk, eCl, lamSQ_mk, lamS_e'] at e1
    rw [lamS_sub, lamS_e', e1, hκ, sub_self]
  have := (ker_zero O cj hO Z₂ hu₂ t t' hη₂ _ _ hz hl hl').2
  rw [Submodule.Quotient.mk_sub, sub_eq_zero] at this
  rw [← hv, ← this]
  rfl

theorem g_e (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hη₁ : EtaNZD O cj Z₁ t t') (hη₂ : EtaNZD O cj Z₂ t t') (hκ : kap O Z₂ = kap O Z₁)
    (hΓ : (fun p => (θ p.1, p.2)) '' GamC O cj (Z₁.map O.subtype) t t' = GamC O cj (Z₂.map O.subtype) t t')
    (hΓ' : (fun p => (θ p.1, p.2)) '' GamC' O cj (Z₁.map O.subtype) t t' = GamC' O cj (Z₂.map O.subtype) t t') :
    gEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ' (eCl Z₁) = eCl Z₂ := by
  have sp := gEquiv_spec O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ' (eCl Z₁)
  have hp : ((Submodule.Quotient.mk (Sum.elim (Pi.single (Fin.last r) 1) (0 : Fin (r + 1) → O)) :
      DDc O cj (Z₁.map O.subtype) t t'), ((1 : E), (0 : E))) ∈ GamC O cj (Z₁.map O.subtype) t t' :=
    ⟨Sum.elim (Pi.single (Fin.last r) 1) 0, fun a => Pi.single_eq_of_ne (Fin.castSucc_ne_last a) _,
      by simp [lamStarC]⟩
  obtain ⟨Y₂, hY₂, he⟩ := gam_fwd O cj t t' Z₁ Z₂ θ hΓ _ hp
  simp only [Prod.mk.injEq] at he
  obtain ⟨h1, h2, h3⟩ := he
  have hl0 : (fun a => Y₂ (Sum.inl a)) = Pi.single (Fin.last r) 1 := by
    funext b
    refine Fin.lastCases ?_ (fun j => ?_) b
    · rw [Pi.single_eq_same]; exact Subtype.ext h2.symm
    · rw [hY₂ j, Pi.single_eq_of_ne (Fin.castSucc_ne_last j)]
  set g := gEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ'
  obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (g (eCl Z₁))
  have key : iL O cj hO Z₂ t t' (g (eCl Z₁)) =
      iL O cj hO Z₂ t t' (eCl Z₂) +
        iR O cj hO Z₂ t t' (Submodule.Quotient.mk (fun b => Y₂ (Sum.inr b))) := by
    rw [← sp.1, eCl, iL_mk]
    show θ (Submodule.Quotient.mk (Sum.elim (Pi.single (Fin.last r) 1) 0)) = _
    rw [show θ (Submodule.Quotient.mk (Sum.elim (Pi.single (Fin.last r) 1) 0)) = Submodule.Quotient.mk Y₂ from h1,
      elim_split O cj hO t t' Z₂, hl0]
    rfl
  have hz : (Submodule.Quotient.mk (Sum.elim (v - Pi.single (Fin.last r) 1) (-(fun b => Y₂ (Sum.inr b)))) :
      DDc O cj (Z₂.map O.subtype) t t') = 0 := by
    rw [mk_elim O cj hO Z₂ t t', Submodule.Quotient.mk_sub, Submodule.Quotient.mk_neg, map_sub, map_neg, ← eCl,
      hv, key]
    abel
  have hl : lamL O Z₂ (v - Pi.single (Fin.last r) 1) = 0 := by
    have e1 := sp.2
    rw [← hv, lamLQ_mk, eCl, lamLQ_mk, lamL_e'] at e1
    rw [map_sub, lamL_e', e1, hκ, sub_self]
  have hl' : lamS O cj Z₂ (-(fun b => Y₂ (Sum.inr b))) = 0 := by
    have : lamS O cj Z₂ (fun b => Y₂ (Sum.inr b)) = 0 := h3.symm
    rw [show (-(fun b => Y₂ (Sum.inr b)) : Fin (r + 1) → O) = 0 - (fun b => Y₂ (Sum.inr b)) by rw [zero_sub],
      lamS_sub, lamS_zero, this, sub_zero]
  have := (ker_zero O cj hO Z₂ hu₂ t t' hη₂ _ _ hz hl hl').1
  rw [Submodule.Quotient.mk_sub, sub_eq_zero] at this
  rw [← hv, this]
  rfl

theorem g_b (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hη₁ : EtaNZD O cj Z₁ t t') (hη₂ : EtaNZD O cj Z₂ t t') (hκ : kap O Z₂ = kap O Z₁)
    (hΓ : (fun p => (θ p.1, p.2)) '' GamC O cj (Z₁.map O.subtype) t t' = GamC O cj (Z₂.map O.subtype) t t')
    (hΓ' : (fun p => (θ p.1, p.2)) '' GamC' O cj (Z₁.map O.subtype) t t' = GamC' O cj (Z₂.map O.subtype) t t') :
    gEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ' (bCls Z₁) = bCls Z₂ := by
  have sp := gEquiv_spec O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ' (bCls Z₁)
  have sps := gsEquiv_spec O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ (eCl (cjT O cj hO Z₁))
  apply uniqL O cj hO Z₂ hu₂ t t' hη₂
  · rw [← sp.1, rel_b, map_smul, map_smul, sps.1, gs_e O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hκ hΓ hΓ', rel_b,
      map_smul]
  · rw [sp.2, bCls, bCls, lamLQ_mk, lamLQ_mk, lamL_b O Z₁ hu₁, lamL_b O Z₂ hu₂]

end Props

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.FormCLR
noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.LocCnt0LAlg Formalism.L2.SG.LocalCountModules.UnramifiedPairingLinear

namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

theorem formC_LR (hcj : ∀ x, cj (cj x) = x) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
    (hu : IsUnit (Z.map O.subtype).det) (T T' : E) (hG : IsUnit (gramC cj (Z.map O.subtype) T T').det)
    (Y W : Ix r → O) (hY : ∀ j, Y (Sum.inr j) = 0) (hW : ∀ j, W (Sum.inl j) = 0) :
    formC O cj (Z.map O.subtype) T T' Y W =
      bRaw O cj Z (fun j => Y (Sum.inl j)) (fun j => W (Sum.inr j)) +
        T * cG O cj Z T T' Y (Sum.inl (Fin.last r)) *
          cj (lamStarC cj (Z.map O.subtype) (fun j => (W (Sum.inr j) : E))) := by
  set G := gramC cj (Z.map O.subtype) T T' with hGdef
  set c := cG O cj Z T T' Y with hcdef
  have hvm : Matrix.vecMul c G = fun j => (↑(Y j) : E) := by
    rw [hcdef]
    unfold cG
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hG, Matrix.vecMul_one]
  have hrel : ∀ j, (↑(Y j) : E) = ∑ i, c i * G i j := by
    intro j
    rw [← congrFun hvm j]
    rfl
  rw [formC_of_rel O cj (Z.map O.subtype) T T' hG Y W c hrel, Fintype.sum_sum_type]
  simp only [hW, ZeroMemClass.coe_zero, map_zero, mul_zero, Finset.sum_const_zero, zero_add]
  have hZ : ∀ j, ∑ b, (Z.map O.subtype) j b * c (Sum.inr b) =
      ↑(Y (Sum.inl j)) + if j = Fin.last r then T * c (Sum.inl (Fin.last r)) else 0 := by
    intro j
    rw [hrel (Sum.inl j), Fintype.sum_sum_type]
    simp only [hGdef, gramC, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.transpose_apply,
      Matrix.of_apply]
    by_cases hj : j = Fin.last r
    · subst hj
      simp [mul_comm]
    · simp [hj, mul_comm]
  have hcR : (fun b => c (Sum.inr b)) = Matrix.mulVec (Z.map O.subtype)⁻¹
      (fun j => (↑(Y (Sum.inl j)) : E) + if j = Fin.last r then T * c (Sum.inl (Fin.last r)) else 0) := by
    have hv : Matrix.mulVec (Z.map O.subtype) (fun b => c (Sum.inr b)) =
        fun j => (↑(Y (Sum.inl j)) : E) + if j = Fin.last r then T * c (Sum.inl (Fin.last r)) else 0 := by
      funext j
      exact hZ j
    rw [← hv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  have hcb : ∀ b, c (Sum.inr b) = Matrix.mulVec (Z.map O.subtype)⁻¹ (fun j => (↑(Y (Sum.inl j)) : E)) b +
      T * c (Sum.inl (Fin.last r)) * (Z.map O.subtype)⁻¹ b (Fin.last r) := by
    intro b
    have h := congrFun hcR b
    rw [h]
    simp only [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hcb, bRaw, lamStarC, map_sum, map_mul, hcj]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem fwd_B (hcj : ∀ x, cj (cj x) = x) (hO : ∀ x ∈ O, cj x ∈ O) (t t' : O)
    (hcT : cj (t : E) = t) (hcT' : cj (t' : E) = t') {Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O}
    (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hκ : kap O Z₂ = kap O Z₁)
    (hG₁ : IsUnit (gramC cj (Z₁.map O.subtype) t t').det)
    (hG₂ : IsUnit (gramC cj (Z₂.map O.subtype) t t').det)
    (θ : DDc O cj (Z₁.map O.subtype) t t' ≃ₗ[O] DDc O cj (Z₂.map O.subtype) t t')
    (hθ : θ ∈ ThetaC O cj (Z₁.map O.subtype) (Z₂.map O.subtype) t t')
    (γ : MbMod Z₁ →ₗ[O] MbMod Z₂) (γs : MbMod (cjT O cj hO Z₁) →ₗ[O] MbMod (cjT O cj hO Z₂))
    (hγ : ∀ m, θ (iL O cj hO Z₁ t t' m) = iL O cj hO Z₂ t t' (γ m))
    (hγs : ∀ m, θ (iR O cj hO Z₁ t t' m) = iR O cj hO Z₂ t t' (γs m))
    (hl : ∀ m, lamLQ O Z₂ hu₂ (γ m) = lamLQ O Z₁ hu₁ m)
    (hls : ∀ m, lamSQ O cj hO Z₂ hu₂ (γs m) = lamSQ O cj hO Z₁ hu₁ m) :
    ∀ y y' y₂ y₂' : Fin (r + 1) → O, γ (Submodule.Quotient.mk y) = Submodule.Quotient.mk y₂ →
      γs (Submodule.Quotient.mk y') = Submodule.Quotient.mk y₂' →
      bRaw O cj Z₂ y₂ y₂' - bRaw O cj Z₁ y y' ∈ O := by
  intro y y' y₂ y₂' h1 h2
  have e1 : θ (Submodule.Quotient.mk (Sum.elim y 0)) = Submodule.Quotient.mk (Sum.elim y₂ 0) := by
    rw [← iL_mk O cj hO Z₁ t t' y, hγ, h1, iL_mk]
  have e2 : θ (Submodule.Quotient.mk (Sum.elim (0 : Fin (r + 1) → O) y')) =
      Submodule.Quotient.mk (Sum.elim (0 : Fin (r + 1) → O) y₂') := by
    rw [← iR_mk O cj hO Z₁ t t' y', hγs, h2, iR_mk]
  have key := hθ.1 _ _ _ _ e1 e2
  have hly : lamC (Z₂.map O.subtype) (fun j => ((Sum.elim y₂ 0 : Ix r → O) (Sum.inl j) : E)) =
      lamC (Z₁.map O.subtype) (fun j => ((Sum.elim y 0 : Ix r → O) (Sum.inl j) : E)) := by
    have := hl (Submodule.Quotient.mk y)
    rw [h1, lamLQ_mk, lamLQ_mk] at this
    exact this
  have hly' : lamStarC cj (Z₂.map O.subtype) (fun j => ((Sum.elim y₂ 0 : Ix r → O) (Sum.inr j) : E)) =
      lamStarC cj (Z₁.map O.subtype) (fun j => ((Sum.elim y 0 : Ix r → O) (Sum.inr j) : E)) := by
    simp [lamStarC]
  have hls' : lamStarC cj (Z₂.map O.subtype) (fun j => ((Sum.elim 0 y₂' : Ix r → O) (Sum.inr j) : E)) =
      lamStarC cj (Z₁.map O.subtype) (fun j => ((Sum.elim 0 y' : Ix r → O) (Sum.inr j) : E)) := by
    have := hls (Submodule.Quotient.mk y')
    rw [h2, lamSQ_mk, lamSQ_mk] at this
    exact this
  obtain ⟨c1, -⟩ := cG_transfer O cj hcj Z₁ Z₂ hu₁ hu₂ t t' hG₁ hG₂ hκ _ _ hly hly'
  rw [formC_LR O cj hcj Z₂ hu₂ t t' hG₂ _ _ (fun j => rfl) (fun j => rfl),
    formC_LR O cj hcj Z₁ hu₁ t t' hG₁ _ _ (fun j => rfl) (fun j => rfl), c1, hls',
    add_sub_add_right_eq_sub] at key
  exact key

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic
end
end

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.LocCnt0LAlg Formalism.L2.SG.LocalCountModules.UnramifiedPairingLinear

namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

theorem fwdEx : FwdEx := by
  intro E _ O cj hcj hO r t t' ht ht' Z₁ Z₂ hu₁ hu₂ hk hg₁ hg₂ θ hθ
  have hη₁ : EtaNZD O cj Z₁ (t : E) (t' : E) := eta_nzd O cj hcj Z₁ hu₁ _ _ hg₁
  have hη₂ : EtaNZD O cj Z₂ (t : E) (t' : E) := eta_nzd O cj hcj Z₂ hu₂ _ _ hg₂
  have hΓ := hθ.2.1
  have hΓ' := hθ.2.2
  have sL := fun m => gEquiv_spec O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ' m
  have sR := fun m => gsEquiv_spec O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ m
  refine ⟨⟨(gEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ',
      gsEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ),
      ⟨g_b O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hk hΓ hΓ',
        g_e O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hk hΓ hΓ'⟩, ?_, ?_⟩,
    fun m => (sL m).1, fun m => (sR m).1⟩
  · intro y' y₂' h
    have key := (sR (Submodule.Quotient.mk y')).2
    rw [h, lamSQ_mk, lamSQ_mk] at key
    exact key
  · intro y y' y₂ y₂' h h'
    exact fwd_B O cj hcj hO t t' ht ht' hu₁ hu₂ hk hg₁ hg₂ θ hθ
      (gEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ').toLinearMap
      (gsEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ).toLinearMap
      (fun m => (sL m).1) (fun m => (sR m).1) (fun m => (sL m).2) (fun m => (sR m).2)
      y y' y₂ y₂' h h'

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic
