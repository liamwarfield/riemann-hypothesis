module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountOfIntegral
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountOfShUnit
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountOfModUnits
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeadMAddCorner
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountOfSteps
noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel
open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lead

variable {K : Type*} [CommRing K]

def leadM {m : ℕ} (X : Matrix (Fin m) (Fin m) K) (l : ℕ) : K :=
  if hl : l ≤ m then (X.submatrix (Fin.castLE hl) (Fin.castLE hl)).det else 0

theorem sum_castLE {A : Type*} [AddCommMonoid A] {l m : ℕ} (hl : l ≤ m) (g : Fin m → A)
    (hg : ∀ a : Fin m, l ≤ a.val → g a = 0) : ∑ a, g a = ∑ a : Fin l, g (Fin.castLE hl a) := by
  have e : ∑ a : Fin l, g (Fin.castLE hl a) = ∑ a ∈ Finset.univ.map (Fin.castLEEmb hl), g a := by
    rw [Finset.sum_map]; rfl
  rw [e]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro a _ ha
  apply hg
  by_contra h
  exact ha (Finset.mem_map.2 ⟨⟨a.val, Nat.lt_of_not_le h⟩, Finset.mem_univ _, Fin.ext rfl⟩)

theorem leadM_mul {m : ℕ} {L X U : Matrix (Fin m) (Fin m) K} (hL : IsLo L) (hU : IsUp U) (l : ℕ) :
    leadM (L * X * U) l = leadM X l := by
  unfold leadM
  split_ifs with hl
  · have e : (L * X * U).submatrix (Fin.castLE hl) (Fin.castLE hl) =
        L.submatrix (Fin.castLE hl) (Fin.castLE hl) * X.submatrix (Fin.castLE hl) (Fin.castLE hl) *
          U.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_apply]
      refine (sum_castLE hl _ ?_).trans (Finset.sum_congr rfl fun b _ => ?_)
      · intro b hb
        have hj := j.isLt
        rw [hU.2 _ _ (by simp only [Fin.lt_def, Fin.val_castLE]; omega), mul_zero]
      · congr 1
        refine sum_castLE hl _ fun a ha => ?_
        have hi := i.isLt
        rw [hL.2 _ _ (by simp only [Fin.lt_def, Fin.val_castLE]; omega), zero_mul]
    rw [e, Matrix.det_mul, Matrix.det_mul]
    have h1 : (L.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 :=
      det_lo' ⟨fun a => hL.1 _, fun a b hab => hL.2 _ _ hab⟩
    have h2 : (U.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 :=
      det_up' ⟨fun a => hU.1 _, fun a b hab => hU.2 _ _ hab⟩
    rw [h1, h2, one_mul, mul_one]
  · rfl

end Lead

section Mats

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E)

def mkMat {m : ℕ} (P : Matrix (Fin m) (Fin m) E) (hP : ∀ a b, P a b ∈ M.R) (hu : IsUnit P.det) : M.Mat m :=
  ⟨Matrix.of fun a b => ⟨P a b, hP a b⟩, by
    have : (Matrix.of fun a b => (⟨P a b, hP a b⟩ : M.R)).map M.R.subtype = P := rfl
    rw [this]; exact hu⟩

theorem clsOf_mk {m : ℕ} (P : Matrix (Fin (m + 1)) (Fin (m + 1)) E) (hP : ∀ a b, P a b ∈ M.R)
    (hu : IsUnit P.det) : clsOf M P = some (Quotient.mk (M.isoSetoid m) (mkMat M P hP hu)) := by
  unfold clsOf
  rw [dif_pos ⟨hP, hu⟩]
  rfl

theorem clsOf_map {m : ℕ} (Z : M.Mat (m + 1)) :
    clsOf M (Z.Z.map M.R.subtype) = some (Quotient.mk (M.isoSetoid m) Z) := by
  exact clsOf_mk M (Z.Z.map M.R.subtype) (fun a b => (Z.Z a b).2) Z.unit

theorem nIso_mk_out {m : ℕ} (Z₁ Z₂ : M.Mat (m + 1)) :
    M.nIso (Quotient.out (Quotient.mk (M.isoSetoid m) Z₁)) (Quotient.out (Quotient.mk (M.isoSetoid m) Z₂)) =
      M.nIso Z₁ Z₂ := by
  have h1 : Nonempty (M.Iso (Quotient.out (Quotient.mk (M.isoSetoid m) Z₁)) Z₁) :=
    Quotient.mk_out (s := M.isoSetoid m) Z₁
  have h2 : Nonempty (M.Iso (Quotient.out (Quotient.mk (M.isoSetoid m) Z₂)) Z₂) :=
    Quotient.mk_out (s := M.isoSetoid m) Z₂
  exact nIso_congr M h1.some h2.some

def headMat {m : ℕ} (P : Matrix (Fin (m + 1)) (Fin (m + 1)) E) (hP : ∀ a b, P a b ∈ M.R)
    (hu : IsUnit (leadM P m)) : M.Mat m :=
  ⟨Matrix.of fun a b => ⟨P a.castSucc b.castSucc, hP _ _⟩, by
    have e1 : (Matrix.of fun a b => (⟨P a.castSucc b.castSucc, hP _ _⟩ : M.R)).map M.R.subtype =
        P.submatrix (Fin.castLE (Nat.le_succ m)) (Fin.castLE (Nat.le_succ m)) := by
      ext a b; rfl
    have e2 : leadM P m = (P.submatrix (Fin.castLE (Nat.le_succ m)) (Fin.castLE (Nat.le_succ m))).det := by
      unfold leadM; exact dif_pos _
    rw [e1, ← e2]; exact hu⟩

end Mats

section Cut

def BridgeBA : Prop :=
  ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E) (m : ℕ) (n s : E) (P₁ P₂ X₁ X₂ L₁ U₁ L₂ U₂ : Matrix (Fin (m + 1)) (Fin (m + 1)) E),
    IsLo L₁ → IsUp U₁ → IsLo L₂ → IsUp U₂ → P₁ = L₁ * X₁ * U₁ → P₂ = L₂ * X₂ * U₂ →
    (∀ a : Fin m, X₁ a.castSucc (Fin.last m) = 0 ∧ X₁ (Fin.last m) a.castSucc = 0 ∧
      X₂ a.castSucc (Fin.last m) = 0 ∧ X₂ (Fin.last m) a.castSucc = 0) →
    X₁ (Fin.last m) (Fin.last m) = s → X₂ (Fin.last m) (Fin.last m) = s → IsUnit (s + n) → n ∈ M.R →
    ∀ (Y₁ Y₂ : M.Mat m) (be₁ be₂ al₁ al₂ : Fin m → M.R),
      (∀ a b : Fin m, (Y₁.Z a b : E) = P₁ a.castSucc b.castSucc ∧ (Y₂.Z a b : E) = P₂ a.castSucc b.castSucc) →
      (∀ a : Fin m, (be₁ a : E) = P₁ a.castSucc (Fin.last m) ∧ (be₂ a : E) = P₂ a.castSucc (Fin.last m) ∧
        (al₁ a : E) = P₁ (Fin.last m) a.castSucc ∧ (al₂ a : E) = P₂ (Fin.last m) a.castSucc) →
      (∀ a b, P₁ a b ∈ M.R) → (∀ a b, P₂ a b ∈ M.R) →
      ∃ Z₁ Z₂ : M.Mat (m + 1), Z₁.Z.map M.R.subtype = P₁ + n • Ecorner m ∧
        Z₂.Z.map M.R.subtype = P₂ + n • Ecorner m ∧ M.nIsoBA Y₁ Y₂ be₁ be₂ al₁ al₂ = M.nIso Z₁ Z₂

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

def LeadZZ : Prop :=
  ∀ (p : PlF D) (Zh : MatP D p) (T T' : (D.s.atP p).Fp),
    (leadM Zh D.R.rS = 0 ↔ leadM (Loc.HermSp.ZZplusOf (Zd.M p) Zh T T') D.R.rS = 0) ∧
    (IsUnit (leadM Zh D.R.rS) ↔ IsUnit (leadM (Loc.HermSp.ZZplusOf (Zd.M p) Zh T T') D.R.rS)) ∧
    (leadM Zh D.R.rS = 0 → IsUnit (leadM Zh (D.R.rS + 1)) →
      IsUnit (Loc.HermSp.ZZplusOf (Zd.M p) Zh T T').det)

def ModKind : Prop :=
  ∀ (p : PlF D) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)),
    (Dmin w D.R.rS = 0 → leadM (modMat Zd.δ T T' p w) D.R.rS = 0) ∧
    (Dmin w D.R.rS ≠ 0 → IsUnit (leadM (modMat Zd.δ T T' p w) D.R.rS) ∧
      (∀ a : Fin D.R.rS, modMat Zd.δ T T' p w a.castSucc (Fin.last D.R.rS) = 0 ∧
        modMat Zd.δ T T' p w (Fin.last D.R.rS) a.castSucc = 0) ∧
      modMat Zd.δ T T' p w (Fin.last D.R.rS) (Fin.last D.R.rS) =
        blkMod Zd.δ T T' p (D.R.rS + 1) 1 (zetaOf w) ∧
      IsUnit (blkMod Zd.δ T T' p (D.R.rS + 1) 1 (zetaOf w) +
        ((nSh (blkMod Zd.δ T T' p (D.R.rS + 1) 1 (zetaOf w)) : ℕ) : (D.s.atP p).Ep)))

theorem add_cornE_zero (p : PlF D) (X : MatP D p) : X + cornE p 0 = X := by
  ext a b; simp [cornE]

theorem loUp_of_hyp {p : PlF D} {uL uU : MatP D p} (h1 : ∀ a, uL a a = 1 ∧ uU a a = 1)
    (h2 : ∀ a b, a < b → uL a b = 0 ∧ uU b a = 0) : IsLo uL ∧ IsUp uU :=
  ⟨⟨fun a => (h1 a).1, fun a b hab => (h2 a b hab).1⟩, ⟨fun a => (h1 a).2, fun a b hab => (h2 a b hab).2⟩⟩


set_option maxHeartbeats 1000000 in
theorem partnerIsomorphismCount_of_bounds (hT2 : Formalism.MainNotions.ThinScalesBound.T2 D) (hI : IntGenP Zd) (hL : LeadZZ Zd) (hK : ModKind Zd) (hB : BridgeBA) :
    PartnerIsomorphismCount Zd := by
  intro p T T' w w' t₁ f₂' φ φ' hk hT hT' hyp h1 h2 hint2
  have hkd : (Dmin w D.R.rS = 0 ↔ Dmin w' D.R.rS = 0) := by
    have hk' := hk
    unfold kind at hk'
    constructor
    · intro h; by_contra h'; rw [if_pos h, if_neg h'] at hk'; exact absurd hk' (by simp)
    · intro h; by_contra h'; rw [if_neg h', if_pos h] at hk'; exact absurd hk' (by simp)
  obtain ⟨uL, uU, hd, ho, hP1⟩ := h1
  obtain ⟨uL', uU', hd', ho', hP2⟩ := h2
  obtain ⟨hLo, hUp⟩ := loUp_of_hyp hd ho
  obtain ⟨hLo', hUp'⟩ := loUp_of_hyp hd' ho'
  have hT2p := hT2 _ _ (Zd.M p) (Zd.agree p).1 (Vp D p) (locH Zd p) (finrank_Vp p) t₁ hyp.1 t₁.f f₂' φ φ'
    hyp.2.1 hyp.2.2.1 hyp.2.2.2.1 hyp.2.2.2.2.1 hyp.2.2.2.2.2
  dsimp only at hT2p
  have hint1 : ∀ a b, (locH Zd p).ZZplus t₁ a b ∈ (Zd.M p).R := hI p t₁ hyp.1
  have hLZ1 := hL p ((locH Zd p).Zhat t₁.f t₁.f') t₁.T t₁.T'
  have hLZ2 := hL p ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T'
  have hlead1 : leadM ((locH Zd p).ZZplus t₁) D.R.rS = leadM (modMat Zd.δ T T' p w) D.R.rS := by
    rw [hP1]; exact leadM_mul hLo hUp _
  have hlead2 : leadM (Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T') D.R.rS =
      leadM (modMat Zd.δ T T' p w') D.R.rS := by
    rw [hP2]; exact leadM_mul hLo' hUp' _
  by_cases hD : Dmin w D.R.rS = 0
  · have hD' := hkd.1 hD
    have hsh : cornerSh Zd.δ T T' p w = 0 := by unfold cornerSh; rw [if_pos hD]
    have hsh' : cornerSh Zd.δ T T' p w' = 0 := by unfold cornerSh; rw [if_pos hD']
    have e1 : (locH Zd p).ZZplus t₁ + cornE p (cornerSh Zd.δ T T' p w) = (locH Zd p).ZZplus t₁ := by
      rw [hsh]; exact add_cornE_zero _ _
    have e2 : Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T' + cornE p (cornerSh Zd.δ T T' p w') =
        Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T' := by
      rw [hsh']; exact add_cornE_zero _ _
    rw [e1, e2]
    have hl1 : leadM ((locH Zd p).ZZplus t₁) D.R.rS = 0 := hlead1.trans ((hK p T T' w).1 hD)
    have hl2 : leadM (Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T') D.R.rS = 0 :=
      hlead2.trans ((hK p T T' w').1 hD')
    have hDl : (locH Zd p).Dl t₁.f t₁.f' D.R.rS = 0 := hLZ1.1.2 hl1
    have hu1 : IsUnit ((locH Zd p).ZZplus t₁).det := hLZ1.2.2 (hLZ1.1.2 hl1) hyp.1.1.2.2.2.1
    by_cases hu2 : IsUnit (Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T').det
    · rw [clsOf_mk (Zd.M p) _ hint1 hu1, clsOf_mk (Zd.M p) _ hint2 hu2]
      show _ = (Zd.M p).nIso _ _
      rw [nIso_mk_out]
      exact hT2p.1 hDl _ _ rfl rfl
    · have hc2 : clsOf (Zd.M p) (Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T') = none := by
        unfold clsOf; rw [dite_eq_right (fun h => hu2 h.2)]
      rw [hc2]
      have h0 : ∀ o : Option ((Zd.M p).Cls D.R.rS), nIsoO Zd.M p o none = 0 := fun o => by cases o <;> rfl
      rw [h0, Nat.card_eq_zero]
      left
      constructor
      rintro ⟨Λ₂, hg, -⟩
      exact hu2 (hLZ2.2.2 (hLZ2.1.2 hl2) hg.1.2.2.2.1)
  · have hD' : Dmin w' D.R.rS ≠ 0 := fun h => hD (hkd.2 h)
    have hz : zetaOf w = zetaOf w' := by
      unfold kind at hk; rw [if_neg hD, if_neg hD'] at hk; exact Option.some_inj.1 hk
    obtain ⟨hu1, hcol1, hc1, hs1⟩ := (hK p T T' w).2 hD
    obtain ⟨hu2, hcol2, hc2, -⟩ := (hK p T T' w').2 hD'
    rw [← hz] at hc2
    have hsh : cornerSh Zd.δ T T' p w =
        ((nSh (blkMod Zd.δ T T' p (D.R.rS + 1) 1 (zetaOf w)) : ℕ) : (D.s.atP p).Ep) := by
      unfold cornerSh; rw [if_neg hD]
    have hsh' : cornerSh Zd.δ T T' p w' =
        ((nSh (blkMod Zd.δ T T' p (D.R.rS + 1) 1 (zetaOf w)) : ℕ) : (D.s.atP p).Ep) := by
      unfold cornerSh; rw [if_neg hD', ← hz]
    rw [hsh, hsh', cornE_eq]
    have hl1 : IsUnit (leadM ((locH Zd p).ZZplus t₁) D.R.rS) := hlead1 ▸ hu1
    have hl2 : IsUnit (leadM (Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T') D.R.rS) :=
      hlead2 ▸ hu2
    have hDl : IsUnit ((locH Zd p).Dl t₁.f t₁.f' D.R.rS) := hLZ1.2.1.2 hl1
    have hcard := hT2p.2 hDl (headMat (Zd.M p) _ hint1 hl1) (headMat (Zd.M p) _ hint2 hl2)
      (fun a => ⟨(locH Zd p).ZZplus t₁ a.castSucc (Fin.last _), hint1 _ _⟩)
      (fun a => ⟨Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T' a.castSucc (Fin.last _),
        hint2 _ _⟩)
      (fun a => ⟨(locH Zd p).ZZplus t₁ (Fin.last _) a.castSucc, hint1 _ _⟩)
      (fun a => ⟨Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T' (Fin.last _) a.castSucc,
        hint2 _ _⟩)
      (fun a b => ⟨rfl, rfl⟩) (fun a => ⟨rfl, rfl, rfl, rfl⟩)
    obtain ⟨Z₁, Z₂, e₁, e₂, hb⟩ := hB (Zd.M p) D.R.rS _ _ _ _ _ _ _ _ _ _ hLo hUp hLo' hUp' hP1 hP2
      (fun a => ⟨(hcol1 a).1, (hcol1 a).2, (hcol2 a).1, (hcol2 a).2⟩) hc1 hc2 hs1
      (natCast_mem _ _) (headMat (Zd.M p) _ hint1 hl1) (headMat (Zd.M p) _ hint2 hl2)
      (fun a => ⟨(locH Zd p).ZZplus t₁ a.castSucc (Fin.last _), hint1 _ _⟩)
      (fun a => ⟨Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T' a.castSucc (Fin.last _),
        hint2 _ _⟩)
      (fun a => ⟨(locH Zd p).ZZplus t₁ (Fin.last _) a.castSucc, hint1 _ _⟩)
      (fun a => ⟨Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T' (Fin.last _) a.castSucc,
        hint2 _ _⟩)
      (fun a b => ⟨rfl, rfl⟩) (fun a => ⟨rfl, rfl, rfl, rfl⟩) hint1 hint2
    refine (show Nat.card (locSet Zd p t₁ f₂' φ φ') = _ from hcard).trans ?_
    have c1 : clsOf (Zd.M p) ((locH Zd p).ZZplus t₁ +
        ((nSh (blkMod Zd.δ T T' p (D.R.rS + 1) 1 (zetaOf w)) : ℕ) : (D.s.atP p).Ep) • Ecorner D.R.rS) =
        some (Quotient.mk ((Zd.M p).isoSetoid D.R.rS) Z₁) := by
      have h := clsOf_map (Zd.M p) Z₁; rw [e₁] at h; exact h
    have c2 : clsOf (Zd.M p) (Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T' +
        ((nSh (blkMod Zd.δ T T' p (D.R.rS + 1) 1 (zetaOf w)) : ℕ) : (D.s.atP p).Ep) • Ecorner D.R.rS) =
        some (Quotient.mk ((Zd.M p).isoSetoid D.R.rS) Z₂) := by
      have h := clsOf_map (Zd.M p) Z₂; rw [e₂] at h; exact h
    exact hb.trans ((nIso_mk_out _ Z₁ Z₂).symm.trans (congrArg₂ (nIsoO Zd.M p) c1 c2).symm)

end Cut

end Formalism.L2.SG.Pf.PCount
end
end

noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open Formalism.MainNotions.S Formalism.L2.SG.Pf.AtPt

section LeadLemmas

variable {K K' : Type*} [CommRing K] [CommRing K']

theorem det_map' {m : ℕ} (f : K →+* K') (A : Matrix (Fin m) (Fin m) K) : (A.map f).det = f A.det :=
  (RingHom.map_det f A).symm

theorem leadM_top {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : leadM A (r + 1) = A.det := by
  unfold leadM; rw [dite_eq_left le_rfl]; rfl

theorem leadM_map {m : ℕ} (f : K →+* K') (A : Matrix (Fin m) (Fin m) K) (l : ℕ) :
    leadM (A.map f) l = f (leadM A l) := by
  unfold leadM
  split_ifs with hl
  · rw [RingHom.map_det]; rfl
  · simp

theorem leadM_smul {m : ℕ} (c : K) (A : Matrix (Fin m) (Fin m) K) (l : ℕ) :
    leadM (c • A) l = c ^ l * leadM A l := by
  unfold leadM
  split_ifs with hl
  · rw [show (c • A).submatrix (Fin.castLE hl) (Fin.castLE hl) = c • A.submatrix (Fin.castLE hl) (Fin.castLE hl)
      from rfl, Matrix.det_smul, Fintype.card_fin]
  · simp

theorem leadM_transpose {m : ℕ} (A : Matrix (Fin m) (Fin m) K) (l : ℕ) : leadM A.transpose l = leadM A l := by
  unfold leadM
  split_ifs with hl
  · rw [← Matrix.det_transpose]; rfl
  · rfl

theorem castLE_ne_last {r : ℕ} (a : Fin r) : Fin.castLE (Nat.le_succ r) a ≠ Fin.last r := by
  intro h
  have h1 := congrArg Fin.val h
  have h2 := a.isLt
  simp at h1
  omega

theorem leadM_add_corner {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (c : K) :
    leadM (A + c • Ecorner r) r = leadM A r := by
  unfold leadM
  rw [dite_eq_left (Nat.le_succ r), dite_eq_left (Nat.le_succ r)]
  congr 1
  ext a b
  simp [Ecorner, castLE_ne_last a]

theorem det_add_corner {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (c : K) :
    (A + c • Ecorner r).det = A.det + c * leadM A r := by
  have hE : A + c • Ecorner r =
      A.updateRow (Fin.last r) (A (Fin.last r) + c • Pi.single (Fin.last r) 1) := by
    ext a b
    by_cases ha : a = Fin.last r
    · subst ha
      by_cases hb : b = Fin.last r
      · subst hb; simp [Ecorner]
      · simp [Ecorner, hb]
    · simp [Ecorner, ha]
  rw [hE, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  congr 2
  rw [Matrix.det_succ_row _ (Fin.last r), Fin.sum_univ_castSucc]
  have h0 : ∀ j : Fin r, (A.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)) (Fin.last r) j.castSucc = 0 := by
    intro j
    rw [Matrix.updateRow_self, Pi.single_eq_of_ne (Fin.castSucc_ne_last j)]
  simp only [h0, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, Matrix.updateRow_self,
    Pi.single_eq_same, mul_one, Fin.succAbove_last]
  have hs : (A.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)).submatrix Fin.castSucc Fin.castSucc =
      A.submatrix (Fin.castLE (Nat.le_succ r)) (Fin.castLE (Nat.le_succ r)) := by
    ext a b
    simp only [Matrix.submatrix_apply]
    rw [Matrix.updateRow_ne (Fin.castSucc_ne_last a)]
    rfl
  rw [hs, leadM, dite_eq_left (Nat.le_succ r)]
  have hpow : ((-1 : K) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) = 1 := Even.neg_one_pow ⟨_, rfl⟩
  rw [hpow, one_mul]

end LeadLemmas

section Model

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem leadZZ_model (M : Loc.Model F E) {r : ℕ} (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (leadM Zh r = 0 ↔ leadM (Loc.HermSp.ZZplusOf M Zh T T') r = 0) ∧
    (IsUnit (leadM Zh r) ↔ IsUnit (leadM (Loc.HermSp.ZZplusOf M Zh T T') r)) ∧
    (leadM Zh r = 0 → IsUnit (leadM Zh (r + 1)) → IsUnit (Loc.HermSp.ZZplusOf M Zh T T').det) := by
  rcases hs : M.split with _ | g
  · have e : Loc.HermSp.ZZplusOf M Zh T T' = Zh := by unfold Loc.HermSp.ZZplusOf; rw [hs]
    rw [e, ← leadM_top]
    exact ⟨Iff.rfl, Iff.rfl, fun _ h => h⟩
  · set q : F := (g.q : F) with hq
    have hq0 : q ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext h)
    let π₁ : E →+* F := (RingHom.fst F F).comp g.e.toRingEquiv.toRingHom
    let π₂ : E →+* F := (RingHom.snd F F).comp g.e.toRingEquiv.toRingHom
    have hzero : ∀ x : E, x = 0 ↔ π₁ x = 0 ∧ π₂ x = 0 := by
      intro x
      constructor
      · rintro rfl; simp
      · rintro ⟨h1, h2⟩
        have : g.e x = 0 := Prod.ext h1 h2
        exact (map_eq_zero_iff g.e g.e.injective).1 this
    have hunit : ∀ x : E, IsUnit x ↔ π₁ x ≠ 0 ∧ π₂ x ≠ 0 := by
      intro x
      rw [← MulEquiv.isUnit_map g.e.toMulEquiv, Prod.isUnit_iff, isUnit_iff_ne_zero, isUnit_iff_ne_zero]
      rfl
    have e1 : (Loc.HermSp.ZZplusOf M Zh T T').map π₁ = q⁻¹ • Zh.map π₁ + (T / q) • Ecorner r := by
      ext a b
      unfold Loc.HermSp.ZZplusOf; rw [hs]
      by_cases hab : a = Fin.last r ∧ b = Fin.last r
      · simp [π₁, hab, Ecorner, q, div_eq_inv_mul] <;> ring
      · simp [π₁, hab, Ecorner, q, div_eq_inv_mul] <;> ring
    have e2 : (Loc.HermSp.ZZplusOf M Zh T T').map π₂ = (-q⁻¹) • (Zh.map π₂).transpose + (-(T' / q)) • Ecorner r := by
      ext a b
      unfold Loc.HermSp.ZZplusOf; rw [hs]
      by_cases hab : a = Fin.last r ∧ b = Fin.last r
      · simp [π₂, hab, Ecorner, q, div_eq_inv_mul] <;> ring
      · simp [π₂, hab, Ecorner, q, div_eq_inv_mul] <;> ring
    have l1 : π₁ (leadM (Loc.HermSp.ZZplusOf M Zh T T') r) = q⁻¹ ^ r * π₁ (leadM Zh r) := by
      rw [← leadM_map, e1, leadM_add_corner, leadM_smul, leadM_map]
    have l2 : π₂ (leadM (Loc.HermSp.ZZplusOf M Zh T T') r) = (-q⁻¹) ^ r * π₂ (leadM Zh r) := by
      rw [← leadM_map, e2, leadM_add_corner, leadM_smul, leadM_transpose, leadM_map]
    have hq1 : q⁻¹ ^ r ≠ 0 := pow_ne_zero _ (inv_ne_zero hq0)
    have hq2 : (-q⁻¹) ^ r ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero hq0))
    refine ⟨?_, ?_, ?_⟩
    · rw [hzero, hzero (leadM _ r), l1, l2, mul_eq_zero, mul_eq_zero]
      simp [hq0]
    · rw [hunit, hunit (leadM _ r), l1, l2]
      simp [hq0]
    · intro h0 hu
      rw [leadM_top] at hu
      rw [hunit] at hu ⊢
      have z := (hzero _).1 h0
      rw [← det_map', ← det_map', e1, e2, det_add_corner, det_add_corner, leadM_smul, leadM_smul,
        leadM_transpose, leadM_map, leadM_map, z.1, z.2, Matrix.det_smul, Matrix.det_smul,
        Matrix.det_transpose, det_map', det_map']
      simp only [mul_zero, add_zero, Fintype.card_fin]
      exact ⟨mul_ne_zero (pow_ne_zero _ (inv_ne_zero hq0)) hu.1,
        mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero hq0))) hu.2⟩

end Model

theorem leadZZ_holds {D : Formalism.BasicNotions.D7} (Zd : Formalism.L2.SG.TermLoc.LocDat D) : LeadZZ Zd :=
  fun p Zh T T' => leadZZ_model (Zd.M p) Zh T T'

end Formalism.L2.SG.Pf.PCount
end
end

noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

section Shape

variable {K : Type*} [CommRing K] {r : ℕ}

theorem leadM_zero_row (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (k : Fin (r + 1)) (hk : k ≠ Fin.last r)
    (h : ∀ b, b ≠ Fin.last r → A k b = 0) : leadM A r = 0 := by
  have hk' : k.val < r := Fin.val_lt_last hk
  unfold leadM
  rw [dite_eq_left (Nat.le_succ r)]
  refine Matrix.det_eq_zero_of_row_eq_zero ⟨k.val, hk'⟩ fun b => ?_
  simp only [Matrix.submatrix_apply]
  have e : Fin.castLE (Nat.le_succ r) ⟨k.val, hk'⟩ = k := Fin.ext rfl
  rw [e]
  exact h _ (castLE_ne_last b)

theorem det_of_corner (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K)
    (h : ∀ a : Fin r, A a.castSucc (Fin.last r) = 0 ∧ A (Fin.last r) a.castSucc = 0) :
    A.det = A (Fin.last r) (Fin.last r) * leadM A r := by
  have hA : A = (A + (-A (Fin.last r) (Fin.last r)) • Ecorner r) + A (Fin.last r) (Fin.last r) • Ecorner r := by
    rw [add_assoc, ← add_smul, neg_add_cancel, zero_smul, add_zero]
  have h0 : (A + (-A (Fin.last r) (Fin.last r)) • Ecorner r).det = 0 := by
    refine Matrix.det_eq_zero_of_row_eq_zero (Fin.last r) fun b => ?_
    by_cases hb : b = Fin.last r
    · subst hb; simp [Ecorner]
    · obtain ⟨b', rfl⟩ := Fin.exists_castSucc_eq.2 hb
      simp [Ecorner, (h b').2, Fin.castSucc_ne_last]
  conv_lhs => rw [hA]
  rw [det_add_corner, h0, zero_add, leadM_add_corner]

end Shape

section ModShape

variable {D : Formalism.BasicNotions.D7}

theorem lead_zero_of_sg (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1))
    (h : sgF w (Fin.last D.R.rS) ≠ Fin.last D.R.rS) :
    leadM (modMat δ T T' p w) D.R.rS = 0 ∧ Dmin w D.R.rS = 0 := by
  constructor
  · exact leadM_zero_row _ (sgF w (Fin.last _)) h fun b hb => by
      rw [modMat_apply', if_neg (by rw [sgF_sgF]; exact hb)]
  · exact leadM_zero_row (ptMat w) (sgF w (Fin.last _)) h fun b hb => by
      rw [ptMat_apply', if_neg (by rw [sgF_sgF]; exact hb)]

theorem shape_of_sg (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1))
    (h : sgF w (Fin.last D.R.rS) = Fin.last D.R.rS) :
    (∀ a : Fin D.R.rS, modMat δ T T' p w a.castSucc (Fin.last _) = 0 ∧
      modMat δ T T' p w (Fin.last _) a.castSucc = 0) ∧
    (∀ a : Fin D.R.rS, ptMat w a.castSucc (Fin.last _) = 0 ∧ ptMat w (Fin.last _) a.castSucc = 0) ∧
    modMat δ T T' p w (Fin.last _) (Fin.last _) = blkMod δ T T' p (D.R.rS + 1) 1 (pTau w.1 D.R.rS) ∧
    ptMat w (Fin.last _) (Fin.last _) = pTau w.1 D.R.rS := by
  have hne : ∀ a : Fin D.R.rS, a.castSucc ≠ sgF w (Fin.last _) := fun a => by
    rw [h]; exact Fin.castSucc_ne_last a
  have hne' : ∀ a : Fin D.R.rS, Fin.last _ ≠ sgF w a.castSucc := fun a e => by
    have := congrArg (sgF w) e
    rw [sgF_sgF, h] at this
    exact Fin.castSucc_ne_last a this.symm
  have hp : pSig w.1 D.R.rS = D.R.rS := by
    have := congrArg Fin.val h
    simpa [sgF] using this
  have hsum := w.2.2
  obtain ⟨-, -, h3, -, h5⟩ := pBlock w.1 D.R.rS (by rw [hsum]; omega)
  have h5' := h5 (by rw [hsum])
  rw [hsum] at h5'
  rw [hp] at h3
  refine ⟨fun a => ⟨?_, ?_⟩, fun a => ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [modMat_apply', if_neg (hne' a)]
  · rw [modMat_apply', if_neg (hne a)]
  · rw [ptMat_apply', if_neg (hne' a)]
  · rw [ptMat_apply', if_neg (hne a)]
  · rw [modMat_apply', if_pos h.symm]
    simp only [Fin.val_last]
    rw [show 1 + pSt w.1 D.R.rS = D.R.rS + 1 by omega, show pSz w.1 D.R.rS = 1 by omega]
  · rw [ptMat_apply', if_pos h.symm]
    simp only [Fin.val_last]

variable (Zd : LocDat D)

def ModUnits : Prop :=
  ∀ (p : PlF D) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)), sgF w (Fin.last D.R.rS) = Fin.last D.R.rS →
    Dmin w D.R.rS ≠ 0 ∧ IsUnit (leadM (modMat Zd.δ T T' p w) D.R.rS) ∧
    IsUnit (blkMod Zd.δ T T' p (D.R.rS + 1) 1 (pTau w.1 D.R.rS) +
      ((nSh (blkMod Zd.δ T T' p (D.R.rS + 1) 1 (pTau w.1 D.R.rS)) : ℕ) : (D.s.atP p).Ep))

theorem modKind_of (hU : ModUnits Zd) : ModKind Zd := by
  intro p T T' w
  by_cases hs : sgF w (Fin.last D.R.rS) = Fin.last D.R.rS
  · obtain ⟨hD, hu, hn⟩ := hU p T T' w hs
    obtain ⟨hm, hpt, hc, hpc⟩ := shape_of_sg Zd.δ T T' p w hs
    have hz : zetaOf w = pTau w.1 D.R.rS := by
      unfold zetaOf
      have e : Dmin w (D.R.rS + 1) = pTau w.1 D.R.rS * Dmin w D.R.rS := by
        show leadM (ptMat w) (D.R.rS + 1) = _ * leadM (ptMat w) D.R.rS
        rw [leadM_top, det_of_corner _ hpt, hpc]
      rw [e, mul_div_cancel_right₀ _ hD]
    refine ⟨fun h => absurd h hD, fun _ => ⟨hu, hm, ?_, ?_⟩⟩ <;> rw [hz]
    · exact hc
    · exact hn
  · obtain ⟨h1, h2⟩ := lead_zero_of_sg Zd.δ T T' p w hs
    exact ⟨fun _ => h1, fun h => absurd h2 h⟩

theorem partnerCount_of_modUnits (hT2 : Formalism.MainNotions.ThinScalesBound.T2 D) (hI : IntGenP Zd) (hU : ModUnits Zd) (hB : BridgeBA) : PartnerIsomorphismCount Zd :=
  partnerIsomorphismCount_of_bounds Zd hT2 hI (leadZZ_holds Zd) (modKind_of Zd hU) hB

end ModShape

end Formalism.L2.SG.Pf.PCount
end
end

noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

section Mono

variable {K : Type*} [CommRing K]

theorem isUnit_det_monomial {m : ℕ} (σ : Fin m → Fin m) (hσ : ∀ a, σ (σ a) = a) (v : Fin m → K)
    (hv : ∀ a, IsUnit (v a)) (A : Matrix (Fin m) (Fin m) K) (hA : ∀ a b, A a b = if b = σ a then v a else 0) :
    IsUnit A.det := by
  let P : Matrix (Fin m) (Fin m) K := Matrix.of fun a b => if b = σ a then 1 else 0
  have hAP : A = Matrix.diagonal v * P := by
    ext a b
    rw [hA, Matrix.diagonal_mul]
    simp [P]
  have hPP : P * P = 1 := by
    ext a c
    simp only [P, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_eq_single (σ a)]
    · simp only [if_true, hσ]
      by_cases h : c = a
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun h' => h h'.symm)]
    · intro b _ hb; rw [if_neg hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hP : IsUnit P.det := isUnit_iff_exists_inv.2 ⟨P.det, by rw [← Matrix.det_mul, hPP, Matrix.det_one]⟩
  rw [hAP, Matrix.det_mul, Matrix.det_diagonal]
  have hprod : IsUnit (∏ a, v a) := ⟨∏ a, (hv a).unit, by simp [Units.coe_prod]⟩
  exact hprod.mul hP

theorem isUnit_lead_monomial {r : ℕ} (σ : Fin (r + 1) → Fin (r + 1)) (hσ : ∀ a, σ (σ a) = a)
    (hl : σ (Fin.last r) = Fin.last r) (v : Fin (r + 1) → K) (hv : ∀ a : Fin r, IsUnit (v a.castSucc))
    (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (hA : ∀ a b, A a b = if b = σ a then v a else 0) :
    IsUnit (leadM A r) := by
  have hne : ∀ a : Fin r, σ (Fin.castLE (Nat.le_succ r) a) ≠ Fin.last r := fun a h =>
    castLE_ne_last a (by rw [← hσ (Fin.castLE (Nat.le_succ r) a), h, hl])
  let σ' : Fin r → Fin r := fun a => ⟨(σ (Fin.castLE (Nat.le_succ r) a)).val, Fin.val_lt_last (hne a)⟩
  have hcast : ∀ a : Fin r, Fin.castLE (Nat.le_succ r) (σ' a) = σ (Fin.castLE (Nat.le_succ r) a) :=
    fun a => Fin.ext rfl
  have hσ' : ∀ a, σ' (σ' a) = a := fun a => by
    apply Fin.ext
    show (σ (Fin.castLE (Nat.le_succ r) (σ' a))).val = a.val
    rw [hcast, hσ]
    rfl
  unfold leadM
  rw [dite_eq_left (Nat.le_succ r)]
  refine isUnit_det_monomial σ' hσ' (fun a => v (Fin.castLE (Nat.le_succ r) a)) (fun a => ?_) _ (fun a b => ?_)
  · rw [show Fin.castLE (Nat.le_succ r) a = a.castSucc from Fin.ext rfl]; exact hv a
  · simp only [Matrix.submatrix_apply]
    rw [hA]
    by_cases h : b = σ' a
    · rw [if_pos h, if_pos (by rw [h, hcast])]
    · rw [if_neg h, if_neg (fun h' => h (Fin.castLE_injective _ (h'.trans (hcast a).symm)))]

end Mono

section Units

variable {D : Formalism.BasicNotions.D7}

theorem twist_isUnit (p : PlF D) (s : ℕ) {x : (D.s.atP p).Ep} (hx : IsUnit x) : IsUnit (twist p s x) := by
  unfold twist
  rcases hs : (D.s.atP p).split with _ | sg
  · exact hx
  · have hx' : IsUnit (sg.e x) := hx.map sg.e
    rw [Prod.isUnit_iff] at hx'
    have hy : IsUnit (((sg.e x).1, (-1) ^ s * (sg.e x).2) : (D.s.atP p).Fp × (D.s.atP p).Fp) :=
      Prod.isUnit_iff.2 ⟨hx'.1, ((isUnit_neg_one).pow s).mul hx'.2⟩
    exact hy.map sg.e.symm

theorem qE_isUnit (p : PlF D) : IsUnit (qE p) := by
  unfold qE
  rcases hs : (D.s.atP p).split with _ | sg
  · exact isUnit_one
  · have hq : ((sg.q : (D.s.atP p).Fp)) ≠ 0 := fun h => sg.q_irr.ne_zero (Subtype.ext h)
    exact (isUnit_iff_ne_zero.2 hq).map _

variable (Zd : LocDat D)

theorem blkMod_isUnit (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (a : Fin (D.R.rS + 1))
    (ha : a ≠ Fin.last D.R.rS) :
    IsUnit (blkMod Zd.δ T T' p (1 + pSt w.1 a.val) (pSz w.1 a.val) (pTau w.1 a.val)) := by
  rw [modMat_blk Zd T T' p w a, if_neg (fun h => ha h.1), sub_zero]
  have hy := yP_ne Zd p
  have hcf : ∀ b, cf Zd p b ≠ 0 := fun b => pow_ne_zero _ (inv_ne_zero hy)
  refine ((isUnit_iff_ne_zero.2 (mul_ne_zero (hcf a) (hcf _))).map _).mul ?_ |>.mul ?_
  · exact twist_isUnit p _ ((isUnit_iff_ne_zero.2 (pTau_ne' w a)).map _)
  · obtain ⟨u, hu⟩ := qE_isUnit p
    rw [← hu, Ring.inverse_unit]
    exact u⁻¹.isUnit

def ShUnit (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p : PlF D) (c : (D.s.atP p).Ep), ∃ n : Fin 3, IsUnit (c + (((n : Fin 3) : ℕ) : (D.s.atP p).Ep))

theorem nSh_isUnit {A : Type} [Ring A] (c : A) (h : ∃ n : Fin 3, IsUnit (c + (((n : Fin 3) : ℕ) : A))) :
    IsUnit (c + ((nSh c : ℕ) : A)) := by
  unfold nSh
  rw [dite_eq_left h]
  exact h.choose_spec

theorem modUnits_of (hS : ShUnit D) : ModUnits Zd := by
  intro p T T' w hl
  refine ⟨?_, ?_, nSh_isUnit _ (hS p _)⟩
  · have h := isUnit_lead_monomial (sgF w) (sgF_sgF w) hl (fun a => pTau w.1 a.val)
      (fun a => isUnit_iff_ne_zero.2 (pTau_ne' w _)) (ptMat w) (ptMat_apply' w)
    exact h.ne_zero
  · exact isUnit_lead_monomial (sgF w) (sgF_sgF w) hl _
      (fun a => blkMod_isUnit Zd T T' p w a.castSucc (Fin.castSucc_ne_last a)) _ (modMat_apply' Zd.δ T T' p w)

theorem partnerCount_of_shUnit (hT2 : Formalism.MainNotions.ThinScalesBound.T2 D) (hI : IntGenP Zd) (hS : ShUnit D) (hB : BridgeBA) : PartnerIsomorphismCount Zd :=
  partnerCount_of_modUnits Zd hT2 hI (modUnits_of Zd hS) hB

end Units

end Formalism.L2.SG.Pf.PCount
end
end

noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

theorem shUnit_holds (D : Formalism.BasicNotions.D7) : ShUnit D := by
  intro p c
  haveI : CharZero (D.s.atP p).Fp := (D.s.atP p).char0
  haveI : Module.Free (D.s.atP p).Fp (D.s.atP p).Ep := (D.s.atP p).free
  haveI : FiniteDimensional (D.s.atP p).Fp (D.s.atP p).Ep :=
    Module.finite_of_finrank_pos (by rw [(D.s.atP p).rank]; norm_num)
  by_contra hcon
  simp only [not_exists] at hcon
  let f : Module.End (D.s.atP p).Fp (D.s.atP p).Ep := LinearMap.mulLeft (D.s.atP p).Fp c
  have hev : ∀ n : Fin 3, ∃ y : (D.s.atP p).Ep, f.HasEigenvector (-(((n : ℕ) : (D.s.atP p).Fp))) y := by
    intro n
    have hnu := hcon n
    have hni : ¬ Function.Injective
        (LinearMap.mulLeft (D.s.atP p).Fp (c + (((n : ℕ)) : (D.s.atP p).Ep))) := by
      intro hinj
      obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.1 hinj) 1
      exact hnu (isUnit_iff_exists_inv.2 ⟨y, hy⟩)
    rw [← LinearMap.ker_eq_bot, ← ne_eq, Submodule.ne_bot_iff] at hni
    obtain ⟨y, hyk, hy0⟩ := hni
    refine ⟨y, ?_, hy0⟩
    rw [Module.End.mem_eigenspace_iff]
    have h1 : (c + (((n : ℕ)) : (D.s.atP p).Ep)) * y = 0 := hyk
    rw [add_mul] at h1
    show c * y = _
    rw [eq_neg_of_add_eq_zero_left h1, neg_smul, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  choose y hy using hev
  have hinj : Function.Injective (fun n : Fin 3 => -(((n : ℕ) : (D.s.atP p).Fp))) := fun a b h => by
    have h' : ((a : ℕ) : (D.s.atP p).Fp) = ((b : ℕ) : (D.s.atP p).Fp) := neg_inj.1 h
    exact Fin.ext (Nat.cast_injective h')
  have hli := Module.End.eigenvectors_linearIndependent' f _ hinj y hy
  have hc := hli.fintype_card_le_finrank
  rw [Fintype.card_fin, (D.s.atP p).rank] at hc
  omega

theorem partnerCount_of_integral {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (hT2 : Formalism.MainNotions.ThinScalesBound.T2 D) (hI : IntGenP Zd)
    (hB : BridgeBA) : PartnerIsomorphismCount Zd :=
  partnerCount_of_shUnit Zd hT2 hI (shUnit_holds D) hB

end Formalism.L2.SG.Pf.PCount
end
end

noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open Formalism.MainNotions.S Formalism.L2.SG.Pf.AtPt

def BridgeIso : Prop :=
  ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E) (m : ℕ) (n s : E) (P₁ P₂ X₁ X₂ L₁ U₁ L₂ U₂ : Matrix (Fin (m + 1)) (Fin (m + 1)) E),
    IsLo L₁ → IsUp U₁ → IsLo L₂ → IsUp U₂ → P₁ = L₁ * X₁ * U₁ → P₂ = L₂ * X₂ * U₂ →
    (∀ a : Fin m, X₁ a.castSucc (Fin.last m) = 0 ∧ X₁ (Fin.last m) a.castSucc = 0 ∧
      X₂ a.castSucc (Fin.last m) = 0 ∧ X₂ (Fin.last m) a.castSucc = 0) →
    X₁ (Fin.last m) (Fin.last m) = s → X₂ (Fin.last m) (Fin.last m) = s → IsUnit (s + n) → n ∈ M.R →
    ∀ (Y₁ Y₂ : M.Mat m) (be₁ be₂ al₁ al₂ : Fin m → M.R),
      (∀ a b : Fin m, (Y₁.Z a b : E) = P₁ a.castSucc b.castSucc ∧ (Y₂.Z a b : E) = P₂ a.castSucc b.castSucc) →
      (∀ a : Fin m, (be₁ a : E) = P₁ a.castSucc (Fin.last m) ∧ (be₂ a : E) = P₂ a.castSucc (Fin.last m) ∧
        (al₁ a : E) = P₁ (Fin.last m) a.castSucc ∧ (al₂ a : E) = P₂ (Fin.last m) a.castSucc) →
      (∀ a b, P₁ a b ∈ M.R) → (∀ a b, P₂ a b ∈ M.R) →
      ∀ Z₁ Z₂ : M.Mat (m + 1), Z₁.Z.map M.R.subtype = P₁ + n • Ecorner m →
        Z₂.Z.map M.R.subtype = P₂ + n • Ecorner m → M.nIsoBA Y₁ Y₂ be₁ be₂ al₁ al₂ = M.nIso Z₁ Z₂

section Det

variable {K : Type*} [CommRing K] {m : ℕ}

theorem det_shift {n s : K} {P X L U : Matrix (Fin (m + 1)) (Fin (m + 1)) K} (hL : IsLo L) (hU : IsUp U)
    (hP : P = L * X * U) (hX : ∀ a : Fin m, X a.castSucc (Fin.last m) = 0 ∧ X (Fin.last m) a.castSucc = 0)
    (hs : X (Fin.last m) (Fin.last m) = s) : (P + n • Ecorner m).det = (s + n) * leadM P m := by
  have e : P + n • Ecorner m = L * (X + n • Ecorner m) * U := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, lo_corner_up hL hU, hP]
  have hX' : ∀ a : Fin m, (X + n • Ecorner m : Matrix (Fin (m + 1)) (Fin (m + 1)) K) a.castSucc (Fin.last m) = 0 ∧
      (X + n • Ecorner m : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) a.castSucc = 0 := fun a => by
    simp [Ecorner, (hX a).1, (hX a).2, Fin.castSucc_ne_last]
  rw [e, Matrix.det_mul, Matrix.det_mul, det_lo' hL, det_up' hU, one_mul, mul_one, det_of_corner _ hX',
    leadM_add_corner, hP, leadM_mul hL hU]
  simp [Ecorner, hs]

end Det

section Model

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem lead_eq_head (M : Loc.Model F E) {m : ℕ} (P : Matrix (Fin (m + 1)) (Fin (m + 1)) E) (Y : M.Mat m)
    (hY : ∀ a b : Fin m, (Y.Z a b : E) = P a.castSucc b.castSucc) : leadM P m = (Y.Z.map M.R.subtype).det := by
  unfold leadM
  rw [dite_eq_left (Nat.le_succ m)]
  congr 1
  ext a b
  exact (hY a b).symm

end Model

theorem bridgeBA_of (hI : BridgeIso) : BridgeBA := by
  intro F _ _ _ E _ _ _ _ M m n s P₁ P₂ X₁ X₂ L₁ U₁ L₂ U₂ hL₁ hU₁ hL₂ hU₂ hP₁ hP₂ hX h₁ h₂ hsn hn Y₁ Y₂
    be₁ be₂ al₁ al₂ hY hba hi₁ hi₂
  have hX₁ : ∀ a : Fin m, X₁ a.castSucc (Fin.last m) = 0 ∧ X₁ (Fin.last m) a.castSucc = 0 :=
    fun a => ⟨(hX a).1, (hX a).2.1⟩
  have hX₂ : ∀ a : Fin m, X₂ a.castSucc (Fin.last m) = 0 ∧ X₂ (Fin.last m) a.castSucc = 0 :=
    fun a => ⟨(hX a).2.2.1, (hX a).2.2.2⟩
  have hu₁ : IsUnit (P₁ + n • Ecorner m).det := by
    rw [det_shift hL₁ hU₁ hP₁ hX₁ h₁, lead_eq_head M P₁ Y₁ fun a b => (hY a b).1]
    exact hsn.mul Y₁.unit
  have hu₂ : IsUnit (P₂ + n • Ecorner m).det := by
    rw [det_shift hL₂ hU₂ hP₂ hX₂ h₂, lead_eq_head M P₂ Y₂ fun a b => (hY a b).2]
    exact hsn.mul Y₂.unit
  have hint : ∀ {P : Matrix (Fin (m + 1)) (Fin (m + 1)) E}, (∀ a b, P a b ∈ M.R) →
      ∀ a b, (P + n • Ecorner m : Matrix (Fin (m + 1)) (Fin (m + 1)) E) a b ∈ M.R := fun hP a b => by
    simp only [Matrix.add_apply, Matrix.smul_apply, Ecorner, Matrix.of_apply, smul_eq_mul]
    split_ifs
    · exact M.R.add_mem (hP a b) (by rw [mul_one]; exact hn)
    · rw [mul_zero, add_zero]; exact hP a b
  refine ⟨mkMat M _ (hint hi₁) hu₁, mkMat M _ (hint hi₂) hu₂, rfl, rfl, ?_⟩
  exact hI M m n s P₁ P₂ X₁ X₂ L₁ U₁ L₂ U₂ hL₁ hU₁ hL₂ hU₂ hP₁ hP₂ hX h₁ h₂ hsn hn Y₁ Y₂ be₁ be₂ al₁ al₂ hY hba
    hi₁ hi₂ _ _ rfl rfl

theorem partnerCount_of_iso {D : Formalism.BasicNotions.D7} (Zd : Formalism.L2.SG.TermLoc.LocDat D) (hT2 : Formalism.MainNotions.ThinScalesBound.T2 D)
    (hI : IntGenP Zd) (hB : BridgeIso) : PartnerIsomorphismCount Zd :=
  partnerCount_of_integral Zd hT2 hI (bridgeBA_of hB)

end Formalism.L2.SG.Pf.PCount
