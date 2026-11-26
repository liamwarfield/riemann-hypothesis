module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestSupportFamiliesStaircaseCosets
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopOrthAtEmb
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingsOfChain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstVertexWeilOrbitValue
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierCoeffScalarInvariant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplitting
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftVerticalCuspidalSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalAlongRightGridArrows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalAlongDownGridArrows

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowGrpEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CellMass

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

def rowN (j : ℕ) : Subgroup (GA D (G.V (.grid D.R.m j))) :=
  if h : j + 2 * ((D.R.m - 1 - j) / 2) + 1 = D.R.m then GlobalTheory.MixPer.flagN (rowJac G j (by omega) ((D.R.m - 1 - j) / 2) (by omega))
  else if h' : j + 2 * ((D.R.m - 2 - j) / 2) + 2 = D.R.m then GlobalTheory.MixPer.flagN (besDecAt G j _ h') else ⊥

def rowEmb (j : ℕ) : GA D (G.V (.top j)) →* GA D (G.V (.grid D.R.m j)) :=
  if h : j + 2 * ((D.R.m - 1 - j) / 2) + 1 = D.R.m then (rowJac G j (by omega) ((D.R.m - 1 - j) / 2) (by omega)).emb0
  else if h' : j + 2 * ((D.R.m - 2 - j) / 2) + 2 = D.R.m then
    GlobalTheory.MixPer.embA (besDecAt G j _ h') (GlobalTheory.OrthSumExists.orthDecHsum D _ _) else 1

theorem rowGrp_eq (j : ℕ) : rowGrp G j = rowN G j ⊔ (rowEmb G j).range := by
  unfold rowGrp rowN rowEmb
  split_ifs
  · rfl
  · rfl
  · simp

def prSet (j : ℕ) (b : GfC (G.V (.grid D.R.m j))) : Set (GfC (G.V (.top j))) :=
  {g | ∃ n ∈ rowN G j, (b.1)⁻¹ * (n * rowEmb G j g.1) * b.1 ∈ latGrp G j}

end GlobalTheory.CellMass
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.QEqColPer
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DblHandEqBiLift
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DblHandOfChars
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf GlobalTheory.FunObj GlobalTheory.RowUnf GlobalTheory.RowChain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain

theorem dbl_hand_of_chars {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T)
    {M : GlobalTheory.FunObj.Vol G} (hM : M.Is t) (σ j : ℕ) (hj : j + 2 * (σ + 1) + 2 = D.R.m) (χz : (AE D)ˣ →* Circle)
    (hz : IsHeckeChar D χz) (hzr : ResEta D χz 1)
    (e1 : G.chrS (.mu t D.R.m j) = G.chrS (.top t j) * χz) (e2 : G.chrT (.mu t D.R.m j) = G.chrT (.top t j))
    (e3 : G.chrS (.mu t D.R.m (j + 1)) = G.chrS (.top t (j + 1)))
    (e4 : G.chrT (.mu t D.R.m (j + 1)) = G.chrT (.top t (j + 1)) * χz) : ∀ (vN : VolN (besDecAt G j (σ + 1) hj))
    (Φ₁ : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ)
    (Φ₂ : WO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m (j + 1 + 1))) → ℂ) (φ : GA D (G.V (.top j)) → ℂ),
    IsThetaFunO Wl.ψ _ _ Φ₁ → IsThetaFunO Wl.ψ _ _ Φ₂ → IsContAut (G.V (.top j)) φ →
    ∀ (g : GA D (G.V (.grid D.R.m j))) (h₁ : GA D (G.V (.grid D.R.m (j + 1)))) (h₂ : GA D (G.V (.grid D.R.m (j + 1 + 1)))),
      Chain.hand (stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)))
        (stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)) (besDecAt G (j + 1 + 1) σ (by omega)))
        (linkAt hM j σ hj vN (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some) ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some)
        (B := besAt G hM j (σ + 1) hj vN) (J := jacAt G hM (j + 1) (σ + 1) (by omega))
        (B' := besAt G hM (j + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
        Φ₁ Φ₂ φ g h₁ h₂ =
      GlobalTheory.SeeSaw.biLift (Wl.om (.top t j)) (Wl.om (.top t (j + 1)))
        (volAt hM (.top j) (by show j ≤ D.R.m; omega)) (volAt hM (.top (j + 1)) (by show j + 1 ≤ D.R.m; omega)) φ
        (contr (linkAt hM j σ hj vN (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some) (G.V (.top (j + 1)))
          ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some)
          (flatBF (B := besAt G hM j (σ + 1) hj vN) (J := jacAt G hM (j + 1) (σ + 1) (by omega))
            (stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)))
            ((stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))).om
              (g, h₁) Φ₁))
          (flatFB (J := jacAt G hM (j + 1) (σ + 1) (by omega))
            (B := besAt G hM (j + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
            (stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
              (besDecAt G (j + 1 + 1) σ (by omega)))
            ((stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
              (besDecAt G (j + 1 + 1) σ (by omega))).om (h₁, h₂) Φ₂))) := by
  intro vN Φ₁ Φ₂ φ hΦ₁ hΦ₂ hφ g h₁ h₂
  have rA : Pair.InRange D.R.m (.top t j) := by
    simp [Pair.InRange, Pair.big, Node.InRange]; omega
  have rB : Pair.InRange D.R.m (.top t (j + 1)) := by
    simp [Pair.InRange, Pair.big, Node.InRange]; omega
  have hA := Wl.om_is (.top t j) rA
  have hB := Wl.om_is (.top t (j + 1)) rB
  have hoa : IsWeilDatumO Wl.ψ (G.V (.top j)) (G.V (.top (j + 1))) (G.chrS (.top t j)) (G.chrT (.mu t D.R.m j))
      (Wl.om (.top t j)) := e2 ▸ hA
  have hob : IsWeilDatumO Wl.ψ (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) (G.chrS (.mu t D.R.m (j + 1)))
      (G.chrT (.top t (j + 1))) (Wl.om (.top t (j + 1))) := e3 ▸ hB
  obtain ⟨omz, hoz⟩ := GlobalTheory.WeilDatumExistence.weilDatumExists D (GlobalTheory.SeeSaw.Model.nLine D) (G.V (.top (j + 1))) Wl.ψ χz
    (G.chrT (.mu t D.R.m j)) Wl.ψ_std hz hoa.hecT hzr hoa.resT
  obtain ⟨omz', hoz'⟩ := GlobalTheory.WeilDatumExistence.weilDatumExists D (G.V (.top (j + 1))) (GlobalTheory.SeeSaw.Model.nLine D) Wl.ψ
    (G.chrS (.mu t D.R.m (j + 1))) χz Wl.ψ_std hob.hecS hz hob.resS hzr
  have hth := GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) Wl.ψ
  let B := besAt G hM j (σ + 1) hj vN
  let J := jacAt G hM (j + 1) (σ + 1) (by omega)
  let B' := besAt G hM (j + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN (besDecAt G (j + 1 + 1) σ (by omega))).some
  let s₁ : StepBF Wl.ψ B J :=
    stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
  let s₂ : StepFB Wl.ψ J B' :=
    stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)) (besDecAt G (j + 1 + 1) σ (by omega))
  have hΞ₁ : IsThetaFunO Wl.ψ B.V₀ J.W₀ (flatBF s₁ (s₁.om (g, h₁) Φ₁)) :=
    hth.1 (σ + 1) B J s₁ _ (s₁.weil.om_pres (g, h₁) Φ₁ hΦ₁)
  have hΞ₂ : IsThetaFunO Wl.ψ J.W₀ B'.V₀ (flatFB s₂ (s₂.om (h₁, h₂) Φ₂)) :=
    hth.2 σ J B' s₂ _ (s₂.weil.om_pres (h₁, h₂) Φ₂ hΦ₂)
  funext h₂'
  exact (GlobalTheory.Unf.Contr.contrLaw D Wl.ψ σ B J B' s₁ s₂ (linkAt hM j σ hj vN (by omega) _)
    ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some) (G.chrS (.top t j)) (G.chrT (.top t (j + 1))) χz
    (Wl.om (.top t j)) omz (Wl.om (.top t (j + 1))) omz' e1 e4 hoa hoz hob hoz' φ _ _ hφ hΞ₁ hΞ₂).2.2 h₂'

end GlobalTheory.RowChain
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf GlobalTheory.FunObj GlobalTheory.RowUnf GlobalTheory.RowChain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain

theorem dbl_hand_eq_biLift : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) {M : GlobalTheory.FunObj.Vol G}
    (hM : M.Is t) (σ j : ℕ) (hj : j + 2 * (σ + 1) + 2 = D.R.m) (vN : VolN (besDecAt G j (σ + 1) hj))
    (Φ₁ : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ)
    (Φ₂ : WO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m (j + 1 + 1))) → ℂ) (φ : GA D (G.V (.top j)) → ℂ),
    IsThetaFunO Wl.ψ _ _ Φ₁ → IsThetaFunO Wl.ψ _ _ Φ₂ → IsContAut (G.V (.top j)) φ →
    ∀ (g : GA D (G.V (.grid D.R.m j))) (h₁ : GA D (G.V (.grid D.R.m (j + 1)))) (h₂ : GA D (G.V (.grid D.R.m (j + 1 + 1)))),
      Chain.hand (stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)))
        (stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)) (besDecAt G (j + 1 + 1) σ (by omega)))
        (linkAt hM j σ hj vN (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some) ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some)
        (B := besAt G hM j (σ + 1) hj vN) (J := jacAt G hM (j + 1) (σ + 1) (by omega))
        (B' := besAt G hM (j + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
        Φ₁ Φ₂ φ g h₁ h₂ =
      GlobalTheory.SeeSaw.biLift (Wl.om (.top t j)) (Wl.om (.top t (j + 1)))
        (volAt hM (.top j) (by show j ≤ D.R.m; omega)) (volAt hM (.top (j + 1)) (by show j + 1 ≤ D.R.m; omega)) φ
        (contr (linkAt hM j σ hj vN (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some) (G.V (.top (j + 1)))
          ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some)
          (flatBF (B := besAt G hM j (σ + 1) hj vN) (J := jacAt G hM (j + 1) (σ + 1) (by omega))
            (stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)))
            ((stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))).om
              (g, h₁) Φ₁))
          (flatFB (J := jacAt G hM (j + 1) (σ + 1) (by omega))
            (B := besAt G hM (j + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
            (stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
              (besDecAt G (j + 1 + 1) σ (by omega)))
            ((stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
              (besDecAt G (j + 1 + 1) σ (by omega))).om (h₁, h₂) Φ₂))) := by
  intro D T L sc G Wl t M hM σ j hj vN

  obtain ⟨χz, hz, hzr, -, hEven, hOdd⟩ := GlobalTheory.T.thetaGrid_lastRow_column_characters_differ G Wl t

  have hjOdd : (D.R.m - 1 - j) % 2 = 1 := by omega
  have hjEven : (D.R.m - 1 - (j + 1)) % 2 = 0 := by omega
  have hS₁ := (hOdd j (by omega) hjOdd).1
  have hT₁ := (hOdd j (by omega) hjOdd).2
  have hS₂ := (hEven (j + 1) (by omega) hjEven).1
  have hT₂ := (hEven (j + 1) (by omega) hjEven).2
  exact dbl_hand_of_chars G Wl t hM σ j hj χz hz hzr hS₁ hT₁ hS₂ hT₂ vN

end GlobalTheory.RowChain
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (Wl : G.Weil) {t : T} {M : Vol G}

theorem Q_eq_colPer (hM : M.Is t) : ∀ (σ j : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (vN : VolN (besDecAt G j σ hj))
    (Φ : (chainFrom G Wl t hM σ j hj vN).Data), (chainFrom G Wl t hM σ j hj vN).IsTheta Φ →
    ∀ (F : Fn G (.grid D.R.m D.R.m)), IsContAut _ F → ∀ (φ : GA D (G.V (.top j)) → ℂ), IsContAut _ φ →
    ∀ (g : GA D (G.V (.grid D.R.m j))) (h : (chainFrom G Wl t hM σ j hj vN).Var),
      (chainFrom G Wl t hM σ j hj vN).Q Φ F φ g h = colPer Wl hM σ j hj vN Φ F φ g h
  | 0, j, hj, vN, Φ, hΦ, F, hF, φ, hφ, g, _ => LastSeeSawStep.main G Wl t hM j hj vN Φ.1 Φ.2 F φ hΦ.1 hΦ.2 hF hφ g
  | σ + 1, j, hj, vN, Φ, hΦ, F, hF, φ, hφ, g, h => by
    have ih := Q_eq_colPer hM σ (j + 1 + 1) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some Φ.2.2 hΦ.2.2 F hF
    let B := besAt G hM j (σ + 1) hj vN
    let J := jacAt G hM (j + 1) (σ + 1) (by omega)
    let B' := besAt G hM (j + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN (besDecAt G (j + 1 + 1) σ (by omega))).some
    let s₁ : StepBF Wl.ψ B J :=
      stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
    let s₂ : StepFB Wl.ψ J B' :=
      stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)) (besDecAt G (j + 1 + 1) σ (by omega))
    have t₁ : IsThetaFunO Wl.ψ B.V₀ J.W₀ (flatBF s₁ (s₁.om (g, h.1) Φ.1)) :=
      (GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) Wl.ψ).1 _ B J s₁ _ (s₁.weil.om_pres (g, h.1) _ hΦ.1)
    have t₂ : IsThetaFunO Wl.ψ J.W₀ B'.V₀ (flatFB s₂ (s₂.om (h.1, h.2.1) Φ.2.1)) :=
      (GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) Wl.ψ).2 _ J B' s₂ _ (s₂.weil.om_pres (h.1, h.2.1) _ hΦ.2.1)
    have hc := GlobalTheory.FinPl.ValDbl.contAut_hand0 s₁ s₂ (linkAt hM j σ hj vN (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some) hφ t₁ t₂
    have e := ih _ hc h.2.1 h.2.2
    refine e.trans ?_
    show colPer Wl hM σ (j + 1 + 1) _ _ Φ.2.2 F _ h.2.1 h.2.2 = colPer Wl hM σ (j + 1 + 1) _ _ Φ.2.2 F _ h.2.1 h.2.2
    congr 1
    exact dbl_hand_eq_biLift G Wl t hM σ j hj vN Φ.1 Φ.2.1 φ hΦ.1 hΦ.2.1 hφ g h.1 h.2.1

end GlobalTheory.RowChain

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (Wl : G.Weil) {t : T} {M : Vol G}

theorem iter_chain (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) (hd : AllTheta G Wl t d) (F : Fn G (.grid D.R.m D.R.m))
    (hF : IsContAut _ F) (φ : GA D (G.V (.top 0)) → ℂ) (hφ : IsContAut _ φ)
    (hR : (chain G Wl t hM).Rapid (chainData G Wl t hM d) F) :
    (chain G Wl t hM).Iter ((chain G Wl t hM).Q (chainData G Wl t hM d) F φ 1)
      ((topLev G hM).per Wl.ψ φ ((chain G Wl t hM).down (chainData G Wl t hM d) F)) := by
  have h := (GlobalTheory.Unf.unfoldings_of_chain D).2.2.2.2.2.1 Wl.ψ _ _ _ (chain G Wl t hM) (chainData G Wl t hM d) F φ 1
    (chainData_isTheta G Wl t hM d hd) hF hφ hR
  have e : rTrans 1 ((chain G Wl t hM).down (chainData G Wl t hM d) F) = (chain G Wl t hM).down (chainData G Wl t hM d) F := by
    funext z; simp [rTrans]
  rwa [e] at h

theorem chain_Q_eq (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) (hd : AllTheta G Wl t d) (F : Fn G (.grid D.R.m D.R.m))
    (hF : IsContAut _ F) (φ : GA D (G.V (.top 0)) → ℂ) (hφ : IsContAut _ φ) (h' : (chain G Wl t hM).Var) :
    (chain G Wl t hM).Q (chainData G Wl t hM d) F φ 1 h' =
      colPer Wl hM _ 0 top_idx (topVN hM) (chainData G Wl t hM d) F φ 1 h' :=
  Q_eq_colPer Wl hM _ 0 top_idx (topVN hM) _ (chainData_isTheta G Wl t hM d hd) F hF φ hφ 1 h'

theorem iter_colPer (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) (hd : AllTheta G Wl t d) (F : Fn G (.grid D.R.m D.R.m))
    (hF : IsContAut _ F) (φ : GA D (G.V (.top 0)) → ℂ) (hφ : IsContAut _ φ)
    (hR : (chain G Wl t hM).Rapid (chainData G Wl t hM d) F) :
    (chain G Wl t hM).Iter (colPer Wl hM _ 0 top_idx (topVN hM) (chainData G Wl t hM d) F φ 1)
      ((topLev G hM).per Wl.ψ φ ((chain G Wl t hM).down (chainData G Wl t hM d) F)) := by
  have h := iter_chain Wl hM d hd F hF φ hφ hR
  have e : (chain G Wl t hM).Q (chainData G Wl t hM d) F φ 1 = colPer Wl hM _ 0 top_idx (topVN hM) (chainData G Wl t hM d) F φ 1 :=
    funext (chain_Q_eq Wl hM d hd F hF φ hφ)
  rwa [e] at h

end GlobalTheory.RowChain
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedTensorEigenvalueLaws
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData
open GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FirstRowEndLaw

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] {Γ : Grid k}

theorem flipTensor_smul (s : Assignment) (ψ : AddChar k Circle) (ϖ : kˣ) (e i j : ℕ) (J : Γ.Level) (c : ℂ)
    (T : Γ.Args → ℂ) : Γ.flipTensor s ψ ϖ e i j J (c • T) = c • Γ.flipTensor s ψ ϖ e i j J T := by
  funext x
  exact GlobalTheory.FlipAdm.squareFlip_const_mul _ _ _ _ _ _ _ c _ _

theorem flips_law {ψ : AddChar k Circle} {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1) (he : 1 ≤ e)
    (g : Γ.VertexGroup) (hK : ∀ Y, g Y ∈ KO k _) (c : ℂ) :
    ∀ (l : List (ℕ × ℕ)) (St : Γ.PiLocalization₂), (∀ x ∈ l, CondLE ϖ e (Γ.nu x.1 x.2)) → (∀ x ∈ l, g x = 1) →
      CanFlip St.path l → (∀ X, IsOpen (St.level X : Set (GL (Fin (Γ.rank X)) k)) ∧ St.level X ≤ KO k _) →
      St.IsAdmissible .one ϖ e → Γ.pathAct .one St.path g St.tensor = c • St.tensor →
      Γ.pathAct .one (St.flips .one ψ ϖ e l).path g (St.flips .one ψ ϖ e l).tensor =
        c • (St.flips .one ψ ϖ e l).tensor := by
  intro l
  induction l with
  | nil => intro St _ _ _ _ _ h; exact h
  | cons x l ih =>
    intro St hν hg hc hJ hT hlaw
    obtain _ | ⟨hp, hc'⟩ := hc
    have hJ' : ∀ X, IsOpen ((St.flip .one ψ ϖ e x).level X : Set (GL (Fin (Γ.rank X)) k)) ∧
        (St.flip .one ψ ϖ e x).level X ≤ KO k _ := fun X => by
      change IsOpen (Γ.flipLevel x.1 x.2 St.level X : Set (GL (Fin (Γ.rank X)) k)) ∧ Γ.flipLevel x.1 x.2 St.level X ≤ _
      by_cases hX : X = (x.1 + 1, x.2 + 1)
      · subst hX; simp only [Grid.flipLevel, Function.update_self]; exact ⟨isOpen_KO, le_rfl⟩
      · simp only [Grid.flipLevel, Function.update_of_ne hX]; exact hJ X
    refine ih (St.flip .one ψ ϖ e x) (fun y hy => hν y (List.mem_cons_of_mem _ hy))
      (fun y hy => hg y (List.mem_cons_of_mem _ hy)) hc' hJ'
      (GlobalTheory.FlipAdm.isAdmissible_flip ψ ϖ e hϖ hψ he St x (hν x List.mem_cons_self) hp hJ hT) ?_
    have hν0 := hν x List.mem_cons_self
    have hg0 := hg x List.mem_cons_self
    obtain ⟨i, j⟩ := x
    obtain ⟨γ, J, T⟩ := St
    obtain ⟨l₁, l₂, hγ, hfl⟩ := GlobalTheory.FlipAdm.exists_split hT.path hp
    have hTt := hT.tensor
    simp only at hγ hfl hlaw hTt hν0 hg0 hJ
    change Γ.pathAct .one (flipPath i j γ) g (Γ.flipTensor .one ψ ϖ e i j J T) = c • Γ.flipTensor .one ψ ϖ e i j J T
    rw [hfl]
    subst hγ
    rw [GlobalTheory.FlipAdm.pathAct_flipTensor hϖ hψ he hν0 (hJ (i, j)).1 (hJ (i, j)).2 l₁ l₂ hTt g hg0 hK, hlaw,
      flipTensor_smul]

end Local

end GlobalTheory.FirstRowEndLaw

namespace GlobalTheory.FirstRowEndLaw

open GlobalTheory.FunObj.GivenAdm

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}
variable {μ₀ : T} {G : GridData L sc} {t : T} {w : Pl D.host.E}

theorem stepType_laws (hL : L.Is μ₀) (hw : w ∈ locPl G t) (j : ℕ) :
    (∀ i, (stepType L t w i).J = stepGroup L t w i) ∧
      ∃ ν : (Kw w)ˣ →* ℂˣ, (∀ x : (Kw w)ˣ, valuation (Kw w) (x : Kw w) = 1 → (locGrid G t w).mu (j + 1) x = (ν x)⁻¹) ∧
        HasTypes ν (stepType L t w j).toLevel (stepType L t w (j + 1)).toLevel (stepFn L t w j) := by
  have hmu : ∀ j x, (locGrid G t w).mu j x = (muBase L j).loc w x * (L.xiH t).loc w x := fun _ _ => rfl
  by_cases hP : w ∈ L.Pg
  · have hQ : w ∉ L.Q t := fun h => (over_of_mem_Pg hL hP).elim fun i hi => not_over_of_mem_Q hL h i hi
    have h0 : w ∈ G.pl.W0 := (mem_locPl.1 hw).resolve_right hQ
    refine ⟨fun i => by simp only [stepType, stepGroup, if_pos hP], ?_⟩
    simp only [stepType, stepFn, if_pos hP]
    exact ⟨_, fun x hx => by simp [hmu, xi_unr hL h0 hQ x hx], TypeDatum.hasTypes_iterPhi _ _ _ j⟩
  by_cases hQ : w ∈ L.Q t
  · have hδ : IsTame ((L.xiH t).loc w)⁻¹ := fun x hx => by
      rw [MonoidHom.inv_apply, isTame_loc (hL.xi_tame t w) x hx, inv_one]
    refine ⟨fun i => by simp only [stepType, stepGroup, if_neg hP, if_pos hQ, dif_pos (And.intro hQ hδ)]; rfl, ?_⟩
    simp only [stepType, stepFn, if_neg hP, if_pos hQ, dif_pos (And.intro hQ hδ)]
    exact ⟨_, fun x hx => by simp [hmu, muBase_unr hL hw hP _ x hx],
      hasTypes_parPhi hδ (ν := 1) fun _ _ => rfl⟩
  · have hn : ¬ (w ∈ L.Q t ∧ IsTame ((L.xiH t).loc w)⁻¹) := fun h => hQ h.1
    refine ⟨fun i => by simp only [stepType, stepGroup, if_neg hP, if_neg hQ, dif_neg hn]; rfl, ?_⟩
    simp only [stepType, stepFn, if_neg hP, if_neg hQ, dif_neg hn]
    exact ⟨1, fun x hx => by
      simp [hmu, muBase_unr hL hw hP _ x hx, xi_unr hL ((mem_locPl.1 hw).resolve_right hQ) hQ x hx], hasTypes_vacuum⟩

end GlobalTheory.FirstRowEndLaw

namespace GlobalTheory.FirstRowEndLaw

open GlobalTheory.FunObj.GivenAdm

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} {G : GridData L sc} {t : T} {w : Pl D.host.E}

theorem givenPath_succ (n : ℕ) : SplitFlip.givenPath (n + 1) =
    Edge.theta 0 n :: ((List.range n).reverse.map (Edge.theta 0) ++ (List.range (n + 1)).map (Edge.ex · 0)) := by
  simp [SplitFlip.givenPath, List.range_succ]

theorem not_touch_rest (n : ℕ) : ∀ b ∈ (List.range n).reverse.map (Edge.theta 0) ++ (List.range (n + 1)).map (Edge.ex · 0),
    b.src ≠ (0, n + 1) ∧ b.tgt ≠ (0, n + 1) := by
  intro b hb
  simp only [List.mem_append, List.mem_map, List.mem_reverse, List.mem_range] at hb
  rcases hb with ⟨j, hj, rfl⟩ | ⟨i, -, rfl⟩
  · simp [Edge.src, Edge.tgt]; omega
  · simp [Edge.src, Edge.tgt]

theorem given_law_at (hL : L.Is μ₀) (B : Frames G) (Φ : G.Datum) (hw : w ∈ locPl G t) :
    ∀ (m : ℕ), m ≠ 0 → ∀ (κ : GL (Fin ((locGrid G t w).rank (0, m))) (Kw w)), κ ∈ givenLevel G t w (0, m) →
    (locGrid G t w).pathAct .one (SplitFlip.givenPath m) (Pi.mulSingle (0, m) κ)
        ((locGrid G t w).lines₂ (SplitFlip.givenPath m) (givenDatum t w B Φ)) =
      endLamAt G t w m κ • (locGrid G t w).lines₂ (SplitFlip.givenPath m) (givenDatum t w B Φ) := by
  intro m
  cases m with
  | zero => exact fun h => absurd rfl h
  | succ n =>
    intro _ κ hκ
    obtain ⟨hJ, ν, hν, H⟩ := stepType_laws (L := L) (G := G) (t := t) (w := w) hL hw n
    have hKO : ∀ Y, (Pi.mulSingle (0, n + 1) κ : (locGrid G t w).VertexGroup) Y ∈ KO (Kw w) _ := fun Y => by
      by_cases hY : Y = (0, n + 1)
      · subst hY; simpa using (givenLevel_open hL hw (0, n + 1)).2 hκ
      · rw [Pi.mulSingle_eq_of_ne hY]; exact one_mem _
    have hκ' : (reGL (ixFin G t w (n + 1))).symm κ ∈ (stepType L t w (n + 1)).J := by
      rw [hJ]
      obtain ⟨y, hy, rfl⟩ := hκ
      simpa using hy
    have h1 : (1 : GL (Ix (Fin D.R.r) (Fin D.R.t) n) (Kw w)) ∈ (stepType L t w n).J := one_mem _
    have key : ∀ x : (locGrid G t w).Args,
        (locGrid G t w).edgeFactor .one (Pi.mulSingle (0, n + 1) κ) (.theta 0 n) *
            givenDatum t w B Φ (.theta 0 n) ((locGrid G t w).moveArgs .one (Pi.mulSingle (0, n + 1) κ) x (.theta 0 n)) =
          endLamAt G t w (n + 1) κ * givenDatum t w B Φ (.theta 0 n) (x (.theta 0 n)) := by
      intro x
      have e := law_of_hasTypes H ⟨1, h1⟩ ⟨_, hκ'⟩
        ((x (.theta 0 n))ᵀ.submatrix (ixFin G t w (n + 1)) (ixFin G t w n))
      have hd : gdet ((reGL (ixFin G t w (n + 1))).symm κ) = gdet κ :=
        (det_reGL (ixFin G t w (n + 1)) _).symm.trans (by rw [MulEquiv.apply_symm_apply])
      rw [edgeFactor_eq hKO, endLamAt, dif_pos hκ']
      simp only [Edge.src, Edge.tgt, Grid.blockChar, Pi.mulSingle_eq_same,
        Pi.mulSingle_eq_of_ne (show ((0 : ℕ), n) ≠ (0, n + 1) by simp)]
      have hv : valuation (Kw w) (gdet κ : Kw w) = 1 := valuation_gdet_of_mem_KO (by simpa using hKO (0, n + 1))
      have hl1 : (stepType L t w n).lam ⟨1, h1⟩ = 1 := map_one _
      set κ' := (reGL (ixFin G t w (n + 1))).symm κ with hκ'def
      set X := (x (.theta 0 n))ᵀ.submatrix (ixFin G t w (n + 1)) (ixFin G t w n) with hX
      have e' : ((ν (gdet (1 : GL (Ix (Fin D.R.r) (Fin D.R.t) n) (Kw w)))) : ℂ) * (((ν (gdet κ'))⁻¹ : ℂˣ) : ℂ) *
          stepFn L t w n ((κ'⁻¹).val * X * (1 : GL (Ix (Fin D.R.r) (Fin D.R.t) n) (Kw w)).val) =
          (((stepType L t w n).lam ⟨1, h1⟩ / (stepType L t w (n + 1)).lam ⟨κ', hκ'⟩ : ℂˣ) : ℂ) * stepFn L t w n X := e
      have hmv : givenDatum t w B Φ (.theta 0 n)
          ((locGrid G t w).moveArgs .one (Pi.mulSingle (0, n + 1) κ) x (.theta 0 n)) =
          stepFn L t w n ((κ'⁻¹).val * X) := by
        simp only [givenDatum]
        congr 1
        rw [hκ'def, ← map_inv, reGL_symm_val, hX, submatrix_mul_equiv]
        simp only [Grid.moveArgs, Assignment.read, Edge.src, Edge.tgt, Pi.mulSingle_eq_same,
          Pi.mulSingle_eq_of_ne (show ((0 : ℕ), n) ≠ (0, n + 1) by simp), invT_val, invT_inv_val, transpose_mul,
          transpose_transpose, Matrix.mul_assoc, map_one, inv_one, Units.val_one, Matrix.mul_one, Matrix.one_mul]
      have hg1 : ∀ {a : Type} [Fintype a] [DecidableEq a], gdet (1 : GL a (Kw w)) = 1 := fun {_ _ _} => map_one _
      rw [hmv]
      simp only [hl1, hd, hg1, map_one, inv_one, Units.val_one, mul_one, one_mul, one_div, Matrix.mul_one] at e'
      rw [hν _ hv, hg1, map_one, inv_one, Units.val_one, mul_one, e']
      rfl
    funext x
    rw [givenPath_succ]
    simp only [Grid.pathAct, Grid.lines₂, Pi.smul_apply, smul_eq_mul, List.map_cons, List.prod_cons]
    have hr1 : (((List.range n).reverse.map (Edge.theta 0) ++ (List.range (n + 1)).map (Edge.ex · 0)).map
        ((locGrid G t w).edgeFactor .one (Pi.mulSingle (0, n + 1) κ))).prod = 1 :=
      List.prod_eq_one fun c hc => by
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hc
        obtain ⟨hs, ht⟩ := not_touch_rest n b (by simpa using hb)
        simp [Grid.edgeFactor, Pi.mulSingle_eq_of_ne hs, Pi.mulSingle_eq_of_ne ht]
    have hr2 : ((List.range n).reverse.map (Edge.theta 0) ++ (List.range (n + 1)).map (Edge.ex · 0)).map
        (fun b => givenDatum t w B Φ b ((locGrid G t w).moveArgs .one (Pi.mulSingle (0, n + 1) κ) x b)) =
        ((List.range n).reverse.map (Edge.theta 0) ++ (List.range (n + 1)).map (Edge.ex · 0)).map
          (fun b => givenDatum t w B Φ b (x b)) :=
      List.map_congr_left fun b hb => by
        obtain ⟨hs, ht⟩ := not_touch_rest n b hb
        congr 1
        simp [Grid.moveArgs, Pi.mulSingle_eq_of_ne hs, Pi.mulSingle_eq_of_ne ht]
    rw [hr1, hr2, mul_one, ← mul_assoc, key x]
    ring

end GlobalTheory.FirstRowEndLaw

namespace GlobalTheory.FirstRowEndLaw

open GlobalTheory.FunObj.GivenAdm

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} {G : GridData L sc} {w : Pl D.host.E}

theorem Tflip_law (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (hw : w ∈ locPl G t)
    (κ : GL (Fin ((locGrid G t w).rank (0, D.R.m))) (Kw w)) (hκ : κ ∈ givenLevel G t w (0, D.R.m)) :
    (locGrid G t w).pathAct .one (oppositePath D.R.m) (Pi.mulSingle (0, D.R.m) κ) (Tflip W B t Φ w) =
      endLam G t w κ • Tflip W B t Φ w := by
  have hg := (Good.locGrid_isGood hL G W t hde hc).1 w hw
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h00 := hg.square 0 hm 0 hm
  have hν : ∀ x ∈ flipOrder D.R.m, CondLE (unifAt w) (depthAt G w) ((locGrid G t w).nu x.1 x.2) := by
    intro x hx
    simp only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, j, hj, rfl⟩ := hx
    rw [← Grid.alpha_div_beta]
    exact (hg.square i hi j hj).condν
  have hg1 : ∀ x ∈ flipOrder D.R.m, (Pi.mulSingle (0, D.R.m) κ : (locGrid G t w).VertexGroup) x = 1 := by
    intro x hx
    simp only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, j, hj, rfl⟩ := hx
    exact Pi.mulSingle_eq_of_ne (by simp; omega) _
  have hK : ∀ Y, (Pi.mulSingle (0, D.R.m) κ : (locGrid G t w).VertexGroup) Y ∈ KO (Kw w) _ := fun Y => by
    by_cases hY : Y = (0, D.R.m)
    · subst hY; simpa using (givenLevel_open hL hw (0, D.R.m)).2 hκ
    · rw [Pi.mulSingle_eq_of_ne hY]; exact one_mem _
  have hbase := given_law_at hL B Φ hw D.R.m hm.ne' κ hκ
  have key := flips_law h00.unif h00.cond h00.one_le _ hK (endLam G t w κ) (flipOrder D.R.m) (givenStage t w B Φ) hν hg1
    (canFlip_flipOrder _).1 (fun X => givenLevel_open hL hw X) (givenStage_isAdmissible hL B t Φ hw) hbase
  change (locGrid G t w).pathAct .one (flipStage t w B W Φ).path _ (flipStage t w B W Φ).tensor =
    _ • (flipStage t w B W Φ).tensor at key
  rw [(flipStage_path_level t w B W Φ).1] at key
  exact key

end GlobalTheory.FirstRowEndLaw

namespace GlobalTheory.FirstRowEndLaw


open Formalism.MainNotions in
theorem pde_ne_q' {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {large₂ : SizeData₂ D} {F : Face D A}
    (h : GlobalTheory.RowClaim.HidaSetting large₂ R F) : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q) := by
  obtain ⟨⟨P, -, -⟩, -⟩ := h.size
  have key : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q) := fun p hp hpp =>
    UpperTheory.Ram.Fun.coprime_QSq_of_splitK D.host hpp (P.level_split p hp)
  exact ⟨key _ D.host.pde_level.1 D.host.pde_prime, key _ D.host.pde_level.2 D.host.pde'_prime⟩


end GlobalTheory.FirstRowEndLaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticesDifferentiableOperator
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct

open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.MovedDict

theorem negGA_mem_GfC' {D : D7} (V : HSp D) {g : Formalism.L2.Theta.GA D V} (hg : g ∈ GfC V) : negGA V g ∈ GfC (negSp V) := by
  have e : matHom (negSp V) (negGA V g) = matHom V g := Units.ext (mt_negGA V g)
  simp only [GfC, MonoidHom.mem_ker, infHom, MonoidHom.comp_apply] at hg ⊢
  rw [e]
  exact hg

theorem jetTab_heisO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc}
    (W : G.Weil) (B : VertexFrames G) (p : GlobalTheory.ChiGrid.Pair T), DefPair D.R.m p → ∀ f : WO (G.pS p) (G.pT p) → ℂ,
    IsThetaFunO W.ψ _ _ f → ∀ w : WO (G.pS p) (G.pT p), ∀ (x : FinPt G p.small) (y : FinPt G p.big)
    (mon : DVar D.what₂.Tau (G.V p.small).rank (G.V p.big).rank →₀ ℕ),
    jetTab W B p (heisO W.ψ _ _ w f) x y mon = fockIn W B p (heisO W.ψ _ _ (actO _ _ (G.toPair p x y).1 (G.toPair p x y).2 w)
      (W.om p (G.toPair p x y) f)) (MvPolynomial.monomial (mon.mapDomain (fvar G p)) 1) 0 := by
  intro D T L sc G W B p hp f hf w x y mon
  have hn := DefPair.nodes hp
  have hom := W.om_is p (by cases p <;> simp only [DefPair, DefNode] at hp hn <;> simp only [Pair.InRange, Node.InRange] <;> omega)
  have mem : (G.toPair p x y).1 ∈ GfC (G.pS p) ∧ (G.toPair p x y).2 ∈ GfC (G.pT p) := by
    cases p with
    | chi i j => exact ⟨negGA_mem_GfC' _ y.2, x.2⟩
    | mu t i j => exact ⟨x.2, y.2⟩
    | core i => exact ⟨negGA_mem_GfC' _ y.2, x.2⟩
    | top t j => exact ⟨x.2, y.2⟩
  have hth := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all W.ψ_std hf w
  have e := GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ _ _ _ _ (W.om p) hom W.θ W.θ_is _ mem.1 _ mem.2
    (G.cartS W.cart p) (G.onT W.cart p) (G.onS B p) (G.onT B p) _ (MvPolynomial.monomial (mon.mapDomain (fvar G p)) 1) hth
  rw [hom.om_heis _ _ w f hf] at e
  simp only [jetTab, GlobalTheory.FunObj.kerFin, GridData.Weil.ker, thetaKO, fockIn]
  rw [e]

theorem actO_nsmul {D : D7} (S T : HSp D) (g : Formalism.L2.Theta.GA D S) (h : Formalism.L2.Theta.GA D T) (n : ℕ) (w : WO S T) :
    actO S T g h (n • w) = n • actO S T g h w := by
  unfold actO
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, succ_nsmul, Matrix.mul_add, Matrix.add_mul, ih]

end GlobalTheory.MovedDict

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModulusIdealOffS0Trivial
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModulusIdealOffS0Trivial
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.ModulUnit

open GlobalTheory.ChiGrid

theorem exists_int_mem_modul {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (v : GlobalTheory.FinPl.Pl D)
    (hv : v ∉ P.S0) : ∃ t : 𝓞 D.host.F, t ∉ v.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈ P.modul sc := by
  have hne : ∀ v' ∈ P.S0, ∃ t : 𝓞 D.host.F, t ∈ v'.asIdeal ∧ t ∉ v.asIdeal := by
    intro v' hv'
    by_contra hc
    push_neg at hc
    have hle : v'.asIdeal ≤ v.asIdeal := fun t ht => hc t ht
    have heq : v'.asIdeal = v.asIdeal := v'.isMaximal.eq_of_le v.isPrime.ne_top hle
    have : v' = v := HeightOneSpectrum.ext heq
    exact hv (this ▸ hv')
  choose! f hf using hne
  refine ⟨∏ v' ∈ P.S0, f v' ^ P.depth sc v', ?_, ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨v', hv', h⟩
    exact (hf v' hv').2 (v.isPrime.mem_of_pow_mem _ h)
  · rw [map_prod, Places.modul]
    refine Ideal.prod_mem_prod fun v' hv' => ?_
    rw [map_pow]
    refine Ideal.pow_mem_pow ?_ _
    have e : ((P.w v').under (𝓞 D.host.F)).asIdeal = v'.asIdeal := by rw [P.under_w hv']
    have h1 : f v' ∈ ((P.w v').under (𝓞 D.host.F)).asIdeal := e ▸ (hf v' hv').1
    exact h1

end GlobalTheory.ModulUnit

theorem GlobalTheory.ModulUnit.idV_modul_eq_one : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (v : GlobalTheory.FinPl.Pl D), v ∉ P.S0 → GlobalTheory.SeeSaw.idV ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) v = GlobalTheory.SeeSaw.idV 1 v := by
  intro D T L P sc v hv
  obtain ⟨t, ht, htm⟩ := GlobalTheory.ModulUnit.exists_int_mem_modul P sc v hv
  apply le_antisymm
  · exact GlobalTheory.SeeSaw.idV_mono FractionalIdeal.coeIdeal_le_one v
  · rw [GlobalTheory.SeeSaw.idV, AddSubgroup.closure_le]
    rintro _ ⟨α, hα, hαv, a, ha, rfl⟩
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [GlobalTheory.IdVGen.tmul_eq ht α]
    obtain ⟨h1, h2⟩ := GlobalTheory.IdVGen.smul_inv_mem ht hα hαv
    refine AddSubgroup.subset_closure ⟨_, h1, h2, _, ?_, rfl⟩
    rw [FractionalIdeal.mem_coeIdeal]
    exact ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t * o, Ideal.mul_mem_right _ _ htm, by rw [map_mul]; rfl⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModulusIdealOffS0TrivialStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_ideal_off_S0_trivial : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (v : GlobalTheory.FinPl.Pl D), v ∉ P.S0 → GlobalTheory.SeeSaw.idV ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) v = GlobalTheory.SeeSaw.idV 1 v := by
  first | exact @GlobalTheory.ModulUnit.idV_modul_eq_one | exact GlobalTheory.ModulUnit.idV_modul_eq_one | (intros; apply GlobalTheory.ModulUnit.idV_modul_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridBasePointTrivialOffTensorPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridBasePointTrivialOffTensorPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowVal

theorem placeIdem_eq_under_of_idemAt {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D}
    (h : Formalism.L2.NTheta.IsIdemAt e P) {v' : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v' ε)
    (hs : e + cA D e = algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) ε) : v' = P.under (𝓞 D.host.F) := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨h1, h2, -⟩ := h.1
  have hm : e * (e + cA D e) = e := by rw [mul_add, h1, h2, add_zero]
  by_contra hne
  have h0 := (GlobalTheory.IdemSupport.place_comp hΦ hε).2.2 P (fun e => hne e.symm)
  have h3 := GlobalTheory.IdemSupport.ev_mul (Φ := Φ) e (e + cA D e) P
  rw [hm, hs, h0, mul_zero, (GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ h).2.1] at h3
  exact one_ne_zero h3

theorem base_mt_mulVec_off : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (B : Frames G) (b : Pts G), IsBase t B b → ∀ v : GlobalTheory.FinPl.Pl D, (∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ v) → ∀ y : Fin (G.V (.grid D.R.m 0)).rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → Formalism.L2.Theta.mt _ (b 0) *ᵥ y = y := by
  intro D T L sc G t B b hb v hv y hy
  obtain ⟨e, ⟨⟨es, hes, rfl⟩, -⟩, hsupp, -⟩ := hb.1
  have hkill : ∀ PP ∈ locPl G t, ∀ a ∈ idAt D (· = v), (es PP + cA D (es PP)) * a = 0 := by
    intro PP hPP a ha
    obtain ⟨-, -, v', ε, hε, hs⟩ := (hes PP hPP).1
    have hv' : v' = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) := placeIdem_eq_under_of_idemAt (hes PP hPP) hε hs
    rw [hs]
    apply (GlobalTheory.FinPl.placeIdem_acts D v' ε hε).2
    rw [GlobalTheory.FinPl.mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at ha ⊢
    refine ⟨ha.1, fun w hw => ha.2 w ?_⟩
    intro h
    apply hw
    intro hwv'
    exact hv PP hPP (hv'.symm.trans (hwv'.symm.trans h))
  have hz : ∀ i, ((Formalism.L2.Theta.mt _ (b 0) - 1) *ᵥ y) i ∈ idAt D (· = v) := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)
  have hE : ∀ i, ((Formalism.L2.Theta.mt _ (b 0) - 1) *ᵥ y) i =
      ((∑ PP ∈ locPl G t, es PP) + cA D (∑ PP ∈ locPl G t, es PP)) * ((Formalism.L2.Theta.mt _ (b 0) - 1) *ᵥ y) i := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, hsupp i j]
  have h0 : (Formalism.L2.Theta.mt _ (b 0) - 1) *ᵥ y = 0 := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hE i, map_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
    exact Finset.sum_eq_zero fun PP hPP => hkill PP hPP _ (hz i)
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
  exact h0

end GlobalTheory.RowVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridBasePointTrivialOffTensorPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridBasePoint_trivial_offTensorPlaces : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (B : Frames G) (b : Pts G), IsBase t B b → ∀ v : GlobalTheory.FinPl.Pl D, (∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ v) → ∀ y : Fin (G.V (.grid D.R.m 0)).rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → Formalism.L2.Theta.mt _ (b 0) *ᵥ y = y := by
  first | exact @GlobalTheory.RowVal.base_mt_mulVec_off | exact GlobalTheory.RowVal.base_mt_mulVec_off | (intros; apply GlobalTheory.RowVal.base_mt_mulVec_off <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PathConvergenceHorizontalTheta
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowStart

theorem setIntegral_fd_eq {D : D7} (V : HSp D) (μ : Measure (GA D V)) (hμ : μ.IsHaarMeasure) (𝓕 𝓕' : Set (GA D V))
    (h1 : IsFundamentalDomain (GQ V) 𝓕 μ) (h2 : IsFundamentalDomain (GQ V) 𝓕' μ) (f : GA D V → ℂ)
    (hf : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) : ∫ g in 𝓕, f g ∂μ = ∫ g in 𝓕', f g ∂μ := by
  haveI := hμ
  exact h1.setIntegral_eq h2 fun γ g => by
    simp only [Subgroup.smul_def, smul_eq_mul]
    exact hf γ γ.2 g

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem IsCuspListed.left {θ : InfFam D} {X : Node} {F : Fn G X} (h : IsCuspListed θ X F) :
    ∀ γ ∈ GQ (G.V X), ∀ g, F (γ * g) = F g := h.1.toIsAutFun.left

theorem measEq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (M M' : Vol G) (X : Node) (K : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D))), M.IsAt X K → M'.IsAt X K → M.ν X = M'.ν X := GlobalTheory.T.gridVertexMeasure_eq_of_same_normalisation

theorem kerA_right_rat (W : G.Weil) {i : ℕ} (hi : i < D.R.m) {f : Sch G (.right i 0)}
    (hf : IsThetaFunO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) f) :
    ∀ γ ∈ GQ (G.V (.grid i 0)), ∀ g h, W.kerA (.right i 0) f (γ * g) h = W.kerA (.right i 0) f g h := by
  intro γ hγ g h
  have H := (GlobalTheory.thetaKO_continuous_and_rat_invariant W.ψ _ _ _ _ (W.om (.chi i 0))
    (W.om_is (.chi i 0) ⟨hi, Nat.zero_le _⟩) f hf).2 1 (Subgroup.one_mem _) γ hγ (negGA _ h) g
  rw [one_mul] at H
  exact H

theorem liftA_right_eq (W : G.Weil) (M M' : Vol G) {i : ℕ} {K : Subgroup (GL (Fin (G.V (.grid i 0)).rank) (Lev.EAf D))}
    (h : M.IsAt (.grid i 0) K) (h' : M'.IsAt (.grid i 0) K) (f : Sch G (.right i 0)) (F : Fn G (.grid i 0))
    (hinv : ∀ γ ∈ GQ (G.V (.grid i 0)), ∀ g x, W.kerA (.right i 0) f (γ * g) x * F (γ * g) = W.kerA (.right i 0) f g x * F g) :
    liftA W M (.right i 0) f F = liftA W M' (.right i 0) f F := by
  funext x
  have e := measEq M M' _ _ h h'
  rw [liftA_apply, liftA_apply]
  have h1 := h.haar_fund
  have h2 := h'.haar_fund
  simp only [Arrow.src] at h1 h2 e ⊢
  rw [e] at h1 ⊢
  exact setIntegral_fd_eq _ _ h2.1 _ _ h1.2 h2.2 _ fun γ hγ g => hinv γ hγ g x

end GlobalTheory.RowStart

namespace GlobalTheory.RowStart

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem rowCore (W : G.Weil) (M₀ M : Vol G) (ρm : RealMatch W) (t : T) (ρ : G.RealVec) (Φ : G.Datum)
    (hstep : CuspStep W M ρm t)
    (hloc : ∀ (i : Fin D.R.m) (κ : G.CosAt i), ∃ e, IsIdemSum e (locPl G t) ∧
      ∃ φ, IsLocVec W (.chi (i : ℕ) 0) e (W.vac i) φ (W.cosVec i κ))
    (hth : ∀ i : Fin D.R.m, IsThetaFunO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (W.datum ρ Φ i))
    (h₀ : M₀.IsRow) (h₁ : M.IsRow) (u : Fn G (.grid 0 0)) (hu : IsCuspListed W.θ (.grid 0 0) u) :
    ∀ n (hn : n ≤ D.R.m), PathConv W M (rowPath T 0 n) (rowFam 0 n fun i : Fin n => W.datum ρ Φ (Fin.castLE hn i)) u ∧
      IsCuspListed W.θ (.grid n 0) (liftP W M (rowPath T 0 n) (rowFam 0 n fun i : Fin n => W.datum ρ Φ (Fin.castLE hn i)) u) ∧
      liftP W M₀ (rowPath T 0 n) (rowFam 0 n fun i : Fin n => W.datum ρ Φ (Fin.castLE hn i)) u =
        liftP W M (rowPath T 0 n) (rowFam 0 n fun i : Fin n => W.datum ρ Φ (Fin.castLE hn i)) u := by
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨trivial, hu, rfl⟩
  | succ n ih =>
    intro hn
    obtain ⟨c, hc, e⟩ := ih (by omega)
    set F := liftP W M (rowPath T 0 n) (rowFam 0 n fun i : Fin n => W.datum ρ Φ (Fin.castLE (by omega) i)) u with hF
    let k : Fin D.R.m := ⟨n, by omega⟩
    obtain ⟨e', he', φ, hφ⟩ := hloc k (Φ k)
    have hv : IsLocVec W (Arrow.right n 0 : Arrow T).pair e' (vacOf ρm (.right n 0)) φ (W.cosVec n (Φ k)) := by
      show IsLocVec W (.chi n 0) e' (ρm.vX n 0) φ (W.cosVec n (Φ k))
      rw [ρm.vX_row n]; exact hφ
    obtain ⟨hconv, hcusp⟩ := hstep (.right n 0) (Or.inl ⟨n, 0, by omega, Nat.zero_le _, rfl⟩) e' he' φ _ hv (ρ k) F hc
    refine ⟨⟨c, hconv⟩, hcusp, ?_⟩
    show liftA W M₀ (.right n 0) (W.datum ρ Φ k) (liftP W M₀ (rowPath T 0 n)
        (rowFam 0 n fun i : Fin n => W.datum ρ Φ (Fin.castLE (by omega) i)) u) = liftA W M (.right n 0) (W.datum ρ Φ k) F
    rw [e]
    refine liftA_right_eq W M₀ M (h₀.row n (by omega)) (h₁.row n (by omega)) _ F fun γ hγ g x => ?_
    rw [kerA_right_rat W (by omega) (hth k) γ hγ g x, IsCuspListed.left hc γ hγ g]

end GlobalTheory.RowStart

namespace GlobalTheory.RowStart

end GlobalTheory.RowStart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnCombinationsComposeLargeDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnCombinationsComposeLargeDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ColComb

variable {D : D7}

theorem comb_apply (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) (w : WO S T) :
    comb ψ S T c f w = ∑ u ∈ c.support, c u * (ψ (symplOH S T w u) * f (w + u)) := by
  unfold comb
  rw [Finset.sum_apply]
  rfl

theorem comb_comm (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c₁ : WO A S →₀ ℂ) (c₂ : WO S A' →₀ ℂ)
    (G : WO A S → WO S A' → ℂ) (u : WO A S) (v : WO S A') :
    comb ψ S A' c₂ (fun v' => comb ψ A S c₁ (fun u' => G u' v') u) v =
      comb ψ A S c₁ (fun u' => comb ψ S A' c₂ (G u') v) u := by
  simp only [comb_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem biComb_biComb (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c₁ c₁' c₁'' : WO A S →₀ ℂ) (c₂ c₂' c₂'' : WO S A' →₀ ℂ)
    (h₁ : ∀ f, comb ψ A S c₁'' f = comb ψ A S c₁ (comb ψ A S c₁' f))
    (h₂ : ∀ f, comb ψ S A' c₂'' f = comb ψ S A' c₂ (comb ψ S A' c₂' f)) (F : WO A S → WO S A' → ℂ) :
    biComb ψ A S A' c₁ c₂ (biComb ψ A S A' c₁' c₂' F) = biComb ψ A S A' c₁'' c₂'' F := by
  funext u v
  show comb ψ A S c₁ (fun u' => comb ψ S A' c₂ (fun v' => comb ψ A S c₁' (fun u'' => comb ψ S A' c₂' (F u'') v') u') v) u =
    comb ψ A S c₁'' (fun u' => comb ψ S A' c₂'' (F u') v) u
  rw [h₁]
  congr 1
  funext u'
  rw [comb_comm]
  simp only [h₂]

end GlobalTheory.ColComb

open GlobalTheory.ColComb in
theorem GlobalTheory.ColComb.main : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (c : Combs ch.G) (c' c'' : ∀ j : ℕ, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ), (∀ j, j < D.R.m → ∀ f, comb ch.W.ψ _ _ (c'' j) f = comb ch.W.ψ _ _ (c.1 j) (comb ch.W.ψ _ _ (c' j) f)) → ∀ (C : BiFam ch.G) (u : ColPt ch.G), evT (combC ch.W c (combC ch.W (c', 0) C)) 1 u 0 = evT (combC ch.W (c'', 0) C) 1 u 0 := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intro D _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ ch _ _
  beta_reduce
  intro c c' c'' hc C u
  unfold evT
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  have hk' : 2 * k + 1 < D.R.m := by
    have := Finset.mem_range.mp hk
    omega
  simp only [combC]
  rw [biComb_biComb (h₁ := hc (2 * k) (by omega)) (h₂ := hc (2 * k + 1) hk')]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnCombinationsComposeLargeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnCombinations_compose_largeDepth : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (c : Combs ch.G) (c' c'' : ∀ j : ℕ, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ), (∀ j, j < D.R.m → ∀ f, comb ch.W.ψ _ _ (c'' j) f = comb ch.W.ψ _ _ (c.1 j) (comb ch.W.ψ _ _ (c' j) f)) → ∀ (C : BiFam ch.G) (u : ColPt ch.G), evT (combC ch.W c (combC ch.W (c', 0) C)) 1 u 0 = evT (combC ch.W (c'', 0) C) 1 u 0 := by
  first | exact @GlobalTheory.ColComb.main | exact GlobalTheory.ColComb.main | (intros; apply GlobalTheory.ColComb.main <;> assumption)
end
end
