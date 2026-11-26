module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.ModularBoundZeroHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.CoordLHolds

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.LamStarCMulVec
noncomputable section

open Formalism.MainNotions.S.Loc

namespace Formalism.L2.SG.LocalCountModules.LocCntCommon

section Alg

variable {E : Type} [CommRing E] {O : Subring E} (cj : E →+* E) {r : ℕ}

theorem lamStarC_add (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (y y' : Fin (r + 1) → E) :
    lamStarC cj Z (y + y') = lamStarC cj Z y + lamStarC cj Z y' := by
  simp [lamStarC, mul_add, Finset.sum_add_distrib]

theorem lamStarC_mulVec (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hu : IsUnit Z.det)
    (w : Fin (r + 1) → E) :
    lamStarC cj Z (fun b => ∑ a, cj (Z a b) * w a) = w (Fin.last r) := by
  have h : ∀ a, ∑ b, cj (Z⁻¹ b (Fin.last r)) * cj (Z a b) = if a = Fin.last r then 1 else 0 := by
    intro a
    have := congrFun (congrFun (Matrix.mul_nonsing_inv Z hu) a) (Fin.last r)
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_one cj, ← map_zero cj, ← apply_ite cj, ← this, map_sum]
    exact Finset.sum_congr rfl fun b _ => by rw [map_mul, mul_comm]
  simp only [lamStarC, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← mul_assoc, ← Finset.sum_mul, h, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

end Alg

end Formalism.L2.SG.LocalCountModules.LocCntCommon
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocCnt0L
namespace Formalism.L2.SG.LocalCountModules.LocCnt0L

def LocCnt0L : Prop :=
  Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, Formalism.L2.SG.LsDatumA.ModSide0 M r n false)

end Formalism.L2.SG.LocalCountModules.LocCnt0L
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.AlgDefs
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.LocCnt0LOfTheta
noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LWork

theorem locCnt0L_of
    (h1 : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n, ThetaMbe0 M r n false))
    (h2 : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r, Mbe0 M r)) :
    Formalism.L2.SG.LocalCountModules.LocCnt0L.LocCnt0L := by
  intro F _ _ _ E _ _ _ _ M hOK r n hmode V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD Z₁ Z₂ e₁ e₂
  have hs : M.split = none := by simpa using hmode
  rw [h1 F E M hOK r n hmode V H hn t₁ f₂ f₂' φ φ' hyp hD Z₁ Z₂ e₁ e₂]
  refine h2 F E M hOK r Z₁ Z₂ ?_ ?_
  · have : Z₁.Z.map M.R.subtype = H.Zhat t₁.f t₁.f' := by
      rw [e₁]; exact zzplusOf_none hs _ _ _
    unfold headDet; rw [this, ← dl_eq_det]; exact hD
  · have : Z₂.Z.map M.R.subtype = H.Zhat f₂ f₂' := by
      rw [e₂]; exact zzplusOf_none hs _ _ _
    unfold headDet; rw [this, ← dl_eq_det]; exact dl_zero_two hyp hD

theorem locCnt0L_of_theta
    (h1 : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n, ThetaMbe0 M r n false)) :
    Formalism.L2.SG.LocalCountModules.LocCnt0L.LocCnt0L :=
  locCnt0L_of h1 (fun _ _ _ _ _ _ _ _ _ M _ r => modularBoundZero_holds M r)

theorem locCnt0L_of_coordL_unramified (h1 : CoordL) (h2 : UnramifiedIsoCountZero) : Formalism.L2.SG.LocalCountModules.LocCnt0L.LocCnt0L :=
  locCnt0L_of_theta (thetaMbe0_L_of h1 h2)

theorem locCnt0L_of_alg (h2 : UnramifiedIsoCountZero) : Formalism.L2.SG.LocalCountModules.LocCnt0L.LocCnt0L :=
  locCnt0L_of_coordL_unramified coordL_holds h2

end Formalism.L2.SG.LocalCountModules.LocCnt0LWork
end
end

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

def cjT (hO : ∀ x ∈ O, cj x ∈ O) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) O :=
  fun a b => ⟨cj (Z b a), hO _ (Z b a).2⟩

def bRaw (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (y y' : Fin (r + 1) → O) : E :=
  ∑ j, cj (y' j) * ((Z.map O.subtype)⁻¹.mulVec (fun i => (y i : E))) j

def lamS (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (y' : Fin (r + 1) → O) : E :=
  lamStarC cj (Z.map O.subtype) (fun b => (y' b : E))

def PairSet (hO : ∀ x ∈ O, cj x ∈ O) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O) : Type :=
  {p : (MbMod Z₁ ≃ₗ[O] MbMod Z₂) × (MbMod (cjT O cj hO Z₁) ≃ₗ[O] MbMod (cjT O cj hO Z₂)) //
    (p.1 (bCls Z₁) = bCls Z₂ ∧ p.1 (eCl Z₁) = eCl Z₂) ∧
    (∀ y' y₂' : Fin (r + 1) → O, p.2 (Submodule.Quotient.mk y') = Submodule.Quotient.mk y₂' →
      lamS O cj Z₂ y₂' = lamS O cj Z₁ y') ∧
    (∀ y y' y₂ y₂' : Fin (r + 1) → O, p.1 (Submodule.Quotient.mk y) = Submodule.Quotient.mk y₂ →
      p.2 (Submodule.Quotient.mk y') = Submodule.Quotient.mk y₂' →
      bRaw O cj Z₂ y₂ y₂' - bRaw O cj Z₁ y y' ∈ O)}

def projP (hO : ∀ x ∈ O, cj x ∈ O) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
    (p : PairSet O cj hO Z₁ Z₂) : IsoMbe Z₁ Z₂ :=
  (⟨p.1.1, p.2.1⟩ : {γ : MbMod Z₁ ≃ₗ[O] MbMod Z₂ // γ (bCls Z₁) = bCls Z₂ ∧ γ (eCl Z₁) = eCl Z₂})

def StepPair : Prop :=
  ∀ (E : Type) [CommRing E] (O : Subring E) (cj : E →+* E), (∀ x, cj (cj x) = x) →
    ∀ (hO : ∀ x ∈ O, cj x ∈ O) (r : ℕ) (T T' : E), T ∈ O → T' ∈ O → cj T = T → cj T' = T' →
    ∀ (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O),
    IsUnit (Z₁.map O.subtype).det → IsUnit (Z₂.map O.subtype).det →
    ((Z₁.map O.subtype).submatrix Fin.castSucc Fin.castSucc).det = 0 →
    ((Z₂.map O.subtype).submatrix Fin.castSucc Fin.castSucc).det = 0 →
    IsUnit (gramC cj (Z₁.map O.subtype) T T').det → IsUnit (gramC cj (Z₂.map O.subtype) T T').det →
    Nat.card (ThetaC O cj (Z₁.map O.subtype) (Z₂.map O.subtype) T T') =
      Nat.card (PairSet O cj hO Z₁ Z₂)

def StepInj : Prop :=
  ∀ (E : Type) [CommRing E] (O : Subring E) (cj : E →+* E), (∀ x, cj (cj x) = x) →
    ∀ (hO : ∀ x ∈ O, cj x ∈ O) (r : ℕ) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O),
    IsUnit (Z₁.map O.subtype).det → IsUnit (Z₂.map O.subtype).det →
    Function.Injective (projP O cj hO Z₁ Z₂)

def StepAdj : Prop :=
  ∀ (E : Type) [CommRing E] (O : Subring E) (cj : E →+* E), (∀ x, cj (cj x) = x) →
    ∀ (hO : ∀ x ∈ O, cj x ∈ O) (r : ℕ) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O),
    IsUnit (Z₁.map O.subtype).det → IsUnit (Z₂.map O.subtype).det →
    ((Z₁.map O.subtype).submatrix Fin.castSucc Fin.castSucc).det = 0 →
    ((Z₂.map O.subtype).submatrix Fin.castSucc Fin.castSucc).det = 0 →
    Function.Surjective (projP O cj hO Z₁ Z₂)

theorem unramifiedIsoCount_of_pair_inj_adj (h1 : StepPair) (hi : StepInj) (h2 : StepAdj) : UnramifiedIsoCountZero := by
  intro E _ O cj hcj hO r T T' hT hT' hcT hcT' Z₁ Z₂ hu₁ hu₂ hd₁ hd₂ hg₁ hg₂
  rw [h1 E O cj hcj hO r T T' hT hT' hcT hcT' Z₁ Z₂ hu₁ hu₂ hd₁ hd₂ hg₁ hg₂]
  exact Nat.card_congr (Equiv.ofBijective _
    ⟨hi E O cj hcj hO r Z₁ Z₂ hu₁ hu₂, h2 E O cj hcj hO r Z₁ Z₂ hu₁ hu₂ hd₁ hd₂⟩)

theorem locCnt0L_of_pair (h1 : StepPair) (hi : StepInj) (h2 : StepAdj) :
    Formalism.L2.SG.LocalCountModules.LocCnt0L.LocCnt0L :=
  Formalism.L2.SG.LocalCountModules.LocCnt0LWork.locCnt0L_of_alg (unramifiedIsoCount_of_pair_inj_adj h1 hi h2)

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
end
end

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

theorem bRaw_sub_right (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (y a c : Fin (r + 1) → O) :
    bRaw O cj Z y (a - c) = bRaw O cj Z y a - bRaw O cj Z y c := by
  unfold bRaw
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Pi.sub_apply]
  push_cast
  rw [map_sub, sub_mul]

theorem lamS_sub (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (a c : Fin (r + 1) → O) :
    lamS O cj Z (a - c) = lamS O cj Z a - lamS O cj Z c := by
  unfold lamS
  have h := lamStarC_add cj (Z.map O.subtype) (fun b => (((a - c) b : O) : E)) (fun b => ((c b : O) : E))
  have e : ((fun b => (((a - c) b : O) : E)) + fun b => ((c b : O) : E)) = fun b => ((a b : O) : E) := by
    funext b
    simp
  rw [e] at h
  exact eq_sub_of_add_eq h.symm

theorem coe_single (a : Fin (r + 1)) :
    (fun j => (((Pi.single a (1 : O) : Fin (r + 1) → O) j : O) : E)) = Pi.single a 1 := by
  funext j
  by_cases h : j = a
  · subst h
    simp
  · simp [Pi.single_apply, h]

theorem mk_eq_zero_of (hcj : ∀ x, cj (cj x) = x) (hO : ∀ x ∈ O, cj x ∈ O)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hu : IsUnit (Z.map O.subtype).det)
    (y' : Fin (r + 1) → O) (hB : ∀ y, bRaw O cj Z y y' ∈ O) (hl : lamS O cj Z y' = 0) :
    (Submodule.Quotient.mk y' : MbMod (cjT O cj hO Z)) = 0 := by
  set Ze := Z.map O.subtype with hZe
  let w' : Fin (r + 1) → E := fun a => ∑ j, cj (Ze⁻¹ j a) * (y' j : E)
  have hB1 : ∀ a, bRaw O cj Z (Pi.single a 1) y' = cj (w' a) := by
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [bRaw, w', map_sum, map_mul, hcj]
    rw [coe_single, Matrix.mulVec_single_one]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]; rfl
  have hw : ∀ a, w' a ∈ O := by
    intro a
    have := hO _ (hB1 a ▸ hB (Pi.single a 1))
    rwa [hcj] at this
  have hlast : w' (Fin.last r) = 0 := hl
  have hinv : Ze⁻¹ * Ze = 1 := Matrix.nonsing_inv_mul _ hu
  have key : ∀ b, (y' b : E) = ∑ a, cj (Ze a b) * w' a := by
    intro b
    simp only [w', Finset.mul_sum]
    rw [Finset.sum_comm]
    have h2 : ∀ j, ∑ a, cj (Ze a b) * (cj (Ze⁻¹ j a) * (y' j : E)) =
        cj ((Ze⁻¹ * Ze) j b) * (y' j : E) := by
      intro j
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.mul_apply, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_mul]; ring
    simp only [h2, hinv, Matrix.one_apply]
    simp
  let wO : Fin (r + 1) → O := fun a => ⟨w' a, hw a⟩
  have hwO : wO (Fin.last r) = 0 := Subtype.ext hlast
  have hy : y' = (cjT O cj hO Z).mulVec wO := by
    funext b
    apply Subtype.ext
    rw [key b]
    simp [Matrix.mulVec, dotProduct, cjT, wO, Ze]
  rw [Submodule.Quotient.mk_eq_zero, hy]
  exact mulVec_mem_headCols _ _ hwO

theorem stepInj : StepInj := by
  intro E _ O cj hcj hO r Z₁ Z₂ hu₁ hu₂ p q hpq
  obtain ⟨⟨γ, γs⟩, hp⟩ := p
  obtain ⟨⟨γ', γs'⟩, hq⟩ := q
  have h1 : γ = γ' := congrArg (fun x : IsoMbe Z₁ Z₂ => x.1) hpq
  subst h1
  have hs : γs = γs' := by
    apply LinearEquiv.ext
    intro ms
    obtain ⟨y', rfl⟩ := Submodule.Quotient.mk_surjective _ ms
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (γs (Submodule.Quotient.mk y'))
    obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (γs' (Submodule.Quotient.mk y'))
    rw [← ha, ← hc, ← sub_eq_zero, ← Submodule.Quotient.mk_sub]
    apply mk_eq_zero_of O cj hcj hO Z₂ hu₂
    · intro y
      obtain ⟨y₁, hy₁⟩ := Submodule.Quotient.mk_surjective _ (γ.symm (Submodule.Quotient.mk y))
      have e1 : γ (Submodule.Quotient.mk y₁) = Submodule.Quotient.mk y := by
        rw [hy₁]; exact γ.apply_symm_apply _
      have A := hp.2.2 y₁ y' y a e1 ha.symm
      have B := hq.2.2 y₁ y' y c e1 hc.symm
      have := O.sub_mem A B
      rw [sub_sub_sub_cancel_right] at this
      rw [bRaw_sub_right]
      exact this
    · rw [lamS_sub, hp.2.1 y' a ha.symm, hq.2.1 y' c hc.symm, sub_self]
  subst hs
  rfl

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
