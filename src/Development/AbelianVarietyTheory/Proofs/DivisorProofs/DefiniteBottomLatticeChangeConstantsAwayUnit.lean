module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeLowerBlockVectorMultipleKernelTranslate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleConstantsEqOfSameLattices

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeesawTripleMovedToSelfDualIsValid
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedVacuumNegHomEqVacuumMovedLattices
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Grid Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Mult MeasureTheory

private theorem isVacO_move {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (hW : IsWeilDatumO ψ S T χS χT om)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (LS MS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT MT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hLS : IsSelfDualC S LS) (hMS : IsSelfDualC S MS) (hLT : IsSelfDualC T LT) (hMT : IsSelfDualC T MT)
    (g : GA D S) (hg : g ∈ GfC S) (h : GA D T) (hh : h ∈ GfC T)
    (mg : GlobalTheory.FinPl.Moves S g LS MS (fun _ => True)) (mh : GlobalTheory.FinPl.Moves T h LT MT (fun _ => True))
    (f : WO S T → ℂ) (hf : IsVacO ψ θ S T sS sT LS LT f) : IsVacO ψ θ S T sS sT MS MT (om (g, h) f) := by
  have hθ : IsInfFam θ := hf.2.inf
  refine GlobalTheory.WeilVacMove.isVacO_om D ψ θ S T χS χT om hW hθ sS sS sT sT _ _ _ _ g h
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hg, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hh, Matrix.mul_one, Matrix.one_mul]) (fun u => ?_) f hf
  have key := GlobalTheory.VacMove.mem_latO_iff_actO hLS hMS hLT hMT mg mh
  have back : actO S T g h (actO S T g⁻¹ h⁻¹ u) = u := by
    have := GlobalTheory.WeilVacMove.actO_inv_actO g⁻¹ h⁻¹ u
    rwa [inv_inv, inv_inv] at this
  refine ⟨fun hu => ⟨actO S T g⁻¹ h⁻¹ u, (key _).2 (by rwa [back]), back.symm⟩, ?_⟩
  rintro ⟨u₀, hu₀, rfl⟩
  exact (key _).1 hu₀

theorem _root_.GlobalTheory.T.movedVacuum_negHom_eq_vacuum_movedLattices : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    ∀ g ∈ GfC A, ∀ g' ∈ GfC A', ∀ h ∈ GfC WW,
    GlobalTheory.FinPl.Moves A g Y.rA.Λ ΛA (fun _ => True) → GlobalTheory.FinPl.Moves A' g' Y.rA'.Λ ΛA' (fun _ => True) →
    GlobalTheory.FinPl.Moves WW h Y.rW.Λ ΛW (fun _ => True) →
    ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r t ≠ 0 ∧ r' t ≠ 0) →
    (∀ t, Y.ω t (g, h) Y.vac = r t • Y.ω t₀ (g, h) Y.vac) → (∀ t, Y.ω' t (g', h) Y.vac' = r' t • Y.ω' t₀ (g', h) Y.vac') →
    IsVacO ψ θ (neg A) WW (fun τ => -(moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA.s τ) (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.s (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA.Λ (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.Λ (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').vac := by
  intro D T A A' WW Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mg mg' mh t₀ r r' hr hrt hrt'
  have hWd : IsWeilDatumO ψ (neg A) WW _ _ ((Y.ω t₀).toSgn true) := hY.weil t₀
  have hg₁ : (GlobalTheory.Grid.ofSgn true A).symm g ∈ GfC (neg A) := hg
  have mg₁ : GlobalTheory.FinPl.Moves (neg A) ((GlobalTheory.Grid.ofSgn true A).symm g) Y.rA.Λ ΛA (fun _ => True) := mg
  have key := isVacO_move ψ θ (neg A) WW _ _ ((Y.ω t₀).toSgn true) hWd (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.Λ ΛA Y.rW.Λ ΛW
    (GlobalTheory.RowTest.isSelfDualC_neg' hY.rigA.1) (GlobalTheory.RowTest.isSelfDualC_neg' hA) hY.rigW.1 hW
    ((GlobalTheory.Grid.ofSgn true A).symm g) hg₁ h hh mg₁ mh Y.vac hY.isVac
  have e : ((Y.ω t₀).toSgn true) ((GlobalTheory.Grid.ofSgn true A).symm g, h) Y.vac = Y.ω t₀ (g, h) Y.vac := rfl
  rw [e] at key
  have e1 : (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA.s = Y.rA.s := rfl
  have e2 : (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.s = Y.rW.s := rfl
  have e3 : (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA.Λ = ΛA := rfl
  have e4 : (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.Λ = ΛW := rfl
  have e5 : (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').vac = Y.ω t₀ (g, h) Y.vac := rfl
  rw [e1, e2, e3, e4, e5]
  exact key
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedFiniteDatumEqStandardPairSecondMember
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedFiniteDatumEqStandardPairSecondMember
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Grid Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Mult MeasureTheory

noncomputable section

namespace GlobalTheory.BotMoveSnd

variable {D : D7}

theorem heisO_smul' {S T : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (w : WO S T) (ζ : ℂ) (g : WO S T → ℂ) :
    heisO ψ S T w (ζ • g) = ζ • heisO ψ S T w g := by
  funext x
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem isPlaceModel_smul {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {Λ : AddSubgroup (WO S T)} {c : ℂ}
    (a : ℂ) {g₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hT : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c g₀ Tm) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c (a • g₀) (a • Tm) :=
  { trans := fun Φ hΦ x hx => by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, hT.trans Φ hΦ x hx, heisO_smul']
    modul := fun Φ hΦ y hy => by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, hT.modul Φ hΦ y hy, heisO_smul']
    vac := by rw [LinearMap.smul_apply, hT.vac] }

theorem isThetaAt_rescale {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {Λ : AddSubgroup (WO S T)} {c κ : ℂ}
    {f₀ Φ f : WO S T → ℂ} (hκ : κ ≠ 0) (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c (κ • f₀) Φ f) :
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ (κ⁻¹ • f) := by
  obtain ⟨⟨Tm, hT⟩, hall⟩ := h
  refine ⟨⟨κ⁻¹ • Tm, ?_⟩, fun Tm' hT' => ?_⟩
  · have := isPlaceModel_smul κ⁻¹ hT
    rwa [smul_smul, inv_mul_cancel₀ hκ, one_smul] at this
  · rw [hall _ (isPlaceModel_smul κ hT'), LinearMap.smul_apply, smul_smul, inv_mul_cancel₀ hκ, one_smul]

theorem isHalf_iff_smul {m n : ℕ} (c : AE D) (u : Mx D m n) : IsHalf c u ↔ c • u = u :=
  ⟨fun h => Matrix.ext fun i j => h i j, fun h i j => congrFun (congrFun h i) j⟩

theorem isHalf_actO' {S T : HSp D} (c : AE D) (g : GA D S) (h : GA D T) {x : WO S T} (hx : IsHalf c x) :
    IsHalf c (actO S T g h x) := by
  rw [isHalf_iff_smul] at hx ⊢
  rw [GlobalTheory.VacMove.actO_eq]
  conv_rhs => rw [← hx]
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem isHalf_actO_inv_iff {S T : HSp D} (c : AE D) (g : GA D S) (h : GA D T) (x : WO S T) :
    IsHalf c (actO S T g⁻¹ h⁻¹ x) ↔ IsHalf c x := by
  refine ⟨fun hx => ?_, isHalf_actO' c _ _⟩
  have := isHalf_actO' c g h hx
  have e := GlobalTheory.SplitHecke.actO_inv_actO (S := S) (T := T) g⁻¹ h⁻¹ x
  simp only [inv_inv] at e
  rwa [e] at this

theorem frame_move_alg {R : Type} [CommRing R] {s t : ℕ} (a βS : GL (Fin s) R) (b βT : GL (Fin t) R)
    (K : Matrix (Fin s) (Fin t) R) :
    ((a * βS)⁻¹ : GL (Fin s) R).1 * K * (b * βT).1 =
      (βS⁻¹).1 * (a⁻¹).1 * βS.1 * ((βS⁻¹).1 * K * βT.1) * ((βT⁻¹ * b⁻¹ * βT)⁻¹ : GL (Fin t) R).1 := by
  have e1 : (βS.1 : Matrix (Fin s) (Fin s) R) * (βS⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e2 : (βT.1 : Matrix (Fin t) (Fin t) R) * (βT⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e3 : ((βT⁻¹ * b⁻¹ * βT)⁻¹ : GL (Fin t) R) = βT⁻¹ * b * βT := by group
  rw [e3, _root_.mul_inv_rev]
  simp only [Units.val_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc βS.1 (βS⁻¹).1, e1, Matrix.one_mul, ← Matrix.mul_assoc βT.1 (βT⁻¹).1, e2, Matrix.one_mul]

theorem frMapAdj_move (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (g : GA D S)
    (h : GA D T) (x : WO S T) :
    frMapAdj S T (Lev.finE S g * βS) (Lev.finE T h * βT) x = frMapAdj S T βS βT (actO S T g⁻¹ h⁻¹ x) := by
  have split : actO S T g⁻¹ h⁻¹ x = actO S T g⁻¹ 1 (actO S T 1 h⁻¹ x) := by
    simp only [GlobalTheory.VacMove.actO_eq, inv_one, GlobalTheory.VacMove.mt_one₀, Matrix.one_mul, Matrix.mul_one]
  rw [split, GlobalTheory.FreeBlockTwist.frMapAdj_actO_one, GlobalTheory.AdjAct.frMapAdj_actO, ← GlobalTheory.AdjAct.finE_inv_val, ← map_inv]
  unfold frMapAdj
  rw [map_inv (Lev.finE S), map_inv (Lev.finE T), ← Matrix.mul_assoc]
  exact frame_move_alg (R := EAf D) (Lev.finE S g) βS (Lev.finE T h) βT _

theorem stdSnd_move (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E)) (a : ℕ) (S T : HSp D)
    (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (g : GA D S) (h : GA D T) (x : WO S T) :
    stdSnd ν e I a S T (Lev.finE S g * βS) (Lev.finE T h * βT) x = stdSnd ν e I a S T βS βT (actO S T g⁻¹ h⁻¹ x) := by
  unfold stdSnd dualCoord
  rw [frMapAdj_move]
  rw [propext (isHalf_actO_inv_iff (cA D e) g h x)]

theorem snd_moved : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    ∀ g ∈ GfC A, ∀ g' ∈ GfC A', ∀ h ∈ GfC WW,
    GlobalTheory.FinPl.Moves A g Y.rA.Λ ΛA (fun _ => True) → GlobalTheory.FinPl.Moves A' g' Y.rA'.Λ ΛA' (fun _ => True) →
    GlobalTheory.FinPl.Moves WW h Y.rW.Λ ΛW (fun _ => True) →
    ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r t ≠ 0 ∧ r' t ≠ 0) →
    (∀ t, Y.ω t (g, h) Y.vac = r t • Y.ω t₀ (g, h) Y.vac) → (∀ t, Y.ω' t (g', h) Y.vac' = r' t • Y.ω' t₀ (g', h) Y.vac') →
    ∀ t, IsThetaAt ψ (symplO A' WW) (heisO ψ A' WW) (cA D ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').e t)) (latO A' WW (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA'.Λ (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.Λ fun _ => True) 1 (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').vac'
    (stdSnd (α t / β t) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').e t) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ideal S t) A.rank A' WW (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA'.β (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.β) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').f' t) := by
  intro D T A A' WW Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mA mA' mW t₀ r r' hr hv hv' t
  have hWe : IsWeilDatumO ψ A' WW (α t) (α t / β t) (Y.ω' t) := (GlobalTheory.Grid.isWeil_false ψ A' WW _ _ _).1 (hY.weil' t)
  have hee : cA D (Y.e t) * cA D (Y.e t) = cA D (Y.e t) := by
    rw [← map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self (hY.idem t)]
  have hinf : infPart D (cA D (Y.e t)) = 0 :=
    GlobalTheory.PlaceDatum.infPart_cA (GlobalTheory.PlaceDatum.infPart_idemSum (hY.idem t))
  have hm := GlobalTheory.VacMove.isThetaAt_moveLat D ψ A' WW (α t) (α t / β t) (Y.ω' t) hWe Y.rA'.Λ ΛA' Y.rW.Λ ΛW hY.rigA'.1 hA'
    hY.rigW.1 hW g' hg' h hh mA' mW (cA D (Y.e t)) _ Y.vac' (Y.f' t) hee hinf hY.isVac'.2.theta
    (GlobalTheory.ConstRatio.theta_f hY t).2 (hY.snd t)
  rw [hv' t] at hm
  have hm2 := isThetaAt_rescale (hr t).2 hm
  have hΦ : (fun x => stdSnd (α t / β t) (Y.e t) (Y.ideal S t) A.rank A' WW Y.rA'.β Y.rW.β (actO A' WW g'⁻¹ h⁻¹ x)) =
      stdSnd (α t / β t) (Y.e t) (Y.ideal S t) A.rank A' WW (Lev.finE A' g' * Y.rA'.β) (Lev.finE WW h * Y.rW.β) :=
    funext fun x => (stdSnd_move _ _ _ _ _ _ _ _ _ _ x).symm
  rw [hΦ] at hm2
  exact hm2

end GlobalTheory.BotMoveSnd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedFiniteDatumEqStandardPairSecondMemberStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Grid Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Mult MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translated_finite_datum_eq_standardPairSecondMember : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    ∀ g ∈ GfC A, ∀ g' ∈ GfC A', ∀ h ∈ GfC WW,
    GlobalTheory.FinPl.Moves A g Y.rA.Λ ΛA (fun _ => True) → GlobalTheory.FinPl.Moves A' g' Y.rA'.Λ ΛA' (fun _ => True) →
    GlobalTheory.FinPl.Moves WW h Y.rW.Λ ΛW (fun _ => True) →
    ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r t ≠ 0 ∧ r' t ≠ 0) →
    (∀ t, Y.ω t (g, h) Y.vac = r t • Y.ω t₀ (g, h) Y.vac) → (∀ t, Y.ω' t (g', h) Y.vac' = r' t • Y.ω' t₀ (g', h) Y.vac') →
    ∀ t, IsThetaAt ψ (symplO A' WW) (heisO ψ A' WW) (cA D ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').e t)) (latO A' WW (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA'.Λ (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.Λ fun _ => True) 1 (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').vac'
    (stdSnd (α t / β t) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').e t) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ideal S t) A.rank A' WW (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA'.β (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.β) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').f' t) := by
  first | exact @GlobalTheory.BotMoveSnd.snd_moved | exact GlobalTheory.BotMoveSnd.snd_moved | (intros; apply GlobalTheory.BotMoveSnd.snd_moved <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedFiniteDatumNegHomEqStandardPairFirst
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Grid Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Mult MeasureTheory

namespace GlobalTheory.BotMove.Fst

private theorem selfDual_neg {D : D7} {A : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} (hA : IsSelfDualC A Λ) :
    IsSelfDualC (GlobalTheory.Grid.neg A) Λ := by
  refine ⟨hA.1, fun y => (hA.2 y).trans (forall₂_congr fun x _ => ⟨fun ⟨c, hc⟩ => ⟨-c, ?_⟩, fun ⟨c, hc⟩ => ⟨-c, ?_⟩⟩)⟩
  · simp [GlobalTheory.Grid.neg_gram, hc]
  · simp [GlobalTheory.Grid.neg_gram] at hc ⊢
    exact neg_eq_iff_eq_neg.2 hc

private theorem placeModel_smul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {e : AE D} {Λ : AddSubgroup (WO S T)}
    {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (h : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm) (c : ℂ) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 (c • f₀) (c • Tm) := by
  have hs : ∀ x (F : WO S T → ℂ), heisO ψ S T x (c • F) = c • heisO ψ S T x F := fun x F => by
    funext w
    simp only [heisO, Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, hs, h.trans Φ hΦ x hx]
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, hs, h.modul Φ hΦ y hy]
  · rw [LinearMap.smul_apply, h.vac]

private theorem thetaAt_smul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {e : AE D} {Λ : AddSubgroup (WO S T)}
    {f₀ Φ f : WO S T → ℂ} {c : ℂ} (hc : c ≠ 0)
    (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 (c • f₀) Φ f) :
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ (c⁻¹ • f) := by
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := h
  refine ⟨⟨c⁻¹ • T₀, ?_⟩, fun T' hT' => ?_⟩
  · have := placeModel_smul hT₀ c⁻¹
    rwa [inv_smul_smul₀ hc] at this
  · have e1 : f = (c • T') Φ := hall _ (placeModel_smul hT' c)
    show c⁻¹ • f = T' Φ
    rw [e1, LinearMap.smul_apply, inv_smul_smul₀ hc]

private theorem thetaAt_move {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {Λ M : GlobalTheory.FinPl.Lat S} {Λ' M' : GlobalTheory.FinPl.Lat T} (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M) (hΛ' : IsSelfDualC T Λ')
    (hM' : IsSelfDualC T M') {b : GA D S} {b' : GA D T} (hb : GlobalTheory.FinPl.Moves S b Λ M (fun _ => True))
    (hb' : GlobalTheory.FinPl.Moves T b' Λ' M' (fun _ => True)) {e : AE D} {Φ f₀ f : WO S T → ℂ} (hee : e * e = e)
    (hinf : infPart D e = 0) (hf₀ : IsThetaFunO ψ S T f₀)
    (hf : IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (Λ : Set _) (Λ' : Set _) fun _ => True) 1 f₀ Φ f) :
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 (om (b, b') f₀)
      (fun x => Φ (actO S T b⁻¹ b'⁻¹ x)) (om (b, b') f) := by
  have key := GlobalTheory.VacMove.mem_latO_iff_actO hΛ hM hΛ' hM' hb hb'
  have key' := GlobalTheory.VacMove.mem_latO_iff_actO hM hΛ hM' hΛ' (GlobalTheory.VacMove.moves_inv hb) (GlobalTheory.VacMove.moves_inv hb')
  have omm : ∀ p q (X : WO S T → ℂ), om p (om q X) = om (p * q) X := fun p q X => by
    rw [map_mul]; rfl
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hf
  have th0 := GlobalTheory.SchrTheta.isTheta_placeModel D ψ hW.std S T Λ Λ' hΛ hΛ' e hee hinf f₀ hf₀ T₀ hT₀
  refine ⟨⟨_, GlobalTheory.SplitMove.isPlaceModel_move₂ hW key hT₀ th0⟩, fun T' hT' => ?_⟩
  have th1 := GlobalTheory.SchrTheta.isTheta_placeModel D ψ hW.std S T M M' hM hM' e hee hinf _
    (hW.om_pres _ _ hf₀) T' hT'
  have pm := GlobalTheory.SplitMove.isPlaceModel_move₂ hW key' hT' th1
  have ev : om (b⁻¹, b'⁻¹) (om (b, b') f₀) = f₀ := by
    rw [omm, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one]; rfl
  rw [ev] at pm
  have hf' : f = om (b⁻¹, b'⁻¹) (T' fun t => Φ (actO S T b⁻¹ b'⁻¹ t)) := hall _ pm
  rw [hf', omm, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one]; rfl

private theorem frMapO_move {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (g : GA D S) (h : GA D T) (x : WO S T) :
    frMapO S T (Lev.finE S g * βS) (Lev.finE T h * βT) x = frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x) := by
  have e1 : (Formalism.L2.Theta.mt T h⁻¹).map (toEAf D) = ((Lev.finE T h)⁻¹).val := by
    rw [← map_inv]; rfl
  have e2 : (Formalism.L2.Theta.mt S g).map (toEAf D) = (Lev.finE S g).val := rfl
  rw [frMapO, frMapO, actO, inv_inv, Matrix.map_mul, Matrix.map_mul, e1, e2, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
  simp only [Matrix.mul_assoc]

private theorem stdFst_move {D : D7} (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E)) (S T : HSp D)
    (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (g : GA D S) (h : GA D T) :
    stdFst ν e I S T (Lev.finE S g * βS) (Lev.finE T h * βT) = fun x => stdFst ν e I S T βS βT (actO S T g⁻¹ h⁻¹ x) := by
  funext x
  unfold stdFst
  rw [frMapO_move, GlobalTheory.SchrMove.isHalf_actO_iff g⁻¹ h⁻¹ x]

end GlobalTheory.BotMove.Fst

theorem _root_.GlobalTheory.T.movedFiniteDatum_negHom_eq_standardPair_first : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    ∀ g ∈ GfC A, ∀ g' ∈ GfC A', ∀ h ∈ GfC WW,
    GlobalTheory.FinPl.Moves A g Y.rA.Λ ΛA (fun _ => True) → GlobalTheory.FinPl.Moves A' g' Y.rA'.Λ ΛA' (fun _ => True) →
    GlobalTheory.FinPl.Moves WW h Y.rW.Λ ΛW (fun _ => True) →
    ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r t ≠ 0 ∧ r' t ≠ 0) →
    (∀ t, Y.ω t (g, h) Y.vac = r t • Y.ω t₀ (g, h) Y.vac) → (∀ t, Y.ω' t (g', h) Y.vac' = r' t • Y.ω' t₀ (g', h) Y.vac') →
    ∀ t, IsThetaAt ψ (symplO (neg A) WW) (heisO ψ (neg A) WW) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').e t) (latO (neg A) WW (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA.Λ (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.Λ fun _ => True) 1 (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').vac
    (stdFst (α t / β t) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').e t) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ideal S t) A WW (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA.β (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.β) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').f t) := by
  intro D T A A' WW Y ψ θ α β νH S hY ΛA ΛA' ΛW hA _ hW g _ g' _ h _ mA _ mW t₀ r r' hr hv _ t
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hY.idem t)
  have mA' : GlobalTheory.FinPl.Moves (neg A) ((ofSgn true A).symm g) Y.rA.Λ ΛA (fun _ => True) := mA
  have h1 := GlobalTheory.BotMove.Fst.thetaAt_move (S := neg A) (hY.weil t) (GlobalTheory.BotMove.Fst.selfDual_neg hY.rigA.1)
    (GlobalTheory.BotMove.Fst.selfDual_neg hA) hY.rigW.1 hW mA' mW ho.idem ho.infPart_eq hY.isVac.2.theta (hY.fst t)
  have e1 : ∀ F, (Y.ω t).toSgn true ((ofSgn true A).symm g, h) F = Y.ω t (g, h) F := fun F => rfl
  rw [e1, e1, hv t] at h1
  have h2 := GlobalTheory.BotMove.Fst.thetaAt_smul (hr t).1 h1
  have e2 := GlobalTheory.BotMove.Fst.stdFst_move (α t / β t) (Y.e t) (Y.ideal S t) A WW Y.rA.β Y.rW.β g h
  show IsThetaAt ψ (symplO (neg A) WW) (heisO ψ (neg A) WW) (Y.e t) (latO (neg A) WW ΛA ΛW fun _ => True) 1 (Y.ω t₀ (g, h) Y.vac)
    (stdFst (α t / β t) (Y.e t) (Y.ideal S t) A WW (Lev.finE A g * Y.rA.β) (Lev.finE WW h * Y.rW.β))
    ((r t)⁻¹ • Y.ω t (g, h) (Y.f t))
  rw [e2]
  exact h2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedVacuumHomEqVacuumMovedLattices
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Grid Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Mult MeasureTheory

theorem _root_.GlobalTheory.T.movedVacuum_hom_eq_vacuum_movedLattices : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    ∀ g ∈ GfC A, ∀ g' ∈ GfC A', ∀ h ∈ GfC WW,
    GlobalTheory.FinPl.Moves A g Y.rA.Λ ΛA (fun _ => True) → GlobalTheory.FinPl.Moves A' g' Y.rA'.Λ ΛA' (fun _ => True) →
    GlobalTheory.FinPl.Moves WW h Y.rW.Λ ΛW (fun _ => True) →
    ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r t ≠ 0 ∧ r' t ≠ 0) →
    (∀ t, Y.ω t (g, h) Y.vac = r t • Y.ω t₀ (g, h) Y.vac) → (∀ t, Y.ω' t (g', h) Y.vac' = r' t • Y.ω' t₀ (g', h) Y.vac') →
    IsVacO ψ θ A' WW (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA'.s (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.s (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA'.Λ (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.Λ (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').vac' := by
  intro D T A A' WW Y ψ θ α β νH S hY ΛA ΛA' ΛW _ hΛA' hΛW g _ g' hg' h hh _ mA' mW t₀ r r' _ _ _
  have hW : IsWeilDatumO ψ A' WW _ _ (Y.ω' t₀) := hY.weil' t₀
  have hvac : IsVacO ψ θ A' WW Y.rA'.s Y.rW.s Y.rA'.Λ Y.rW.Λ Y.vac' := hY.isVac'
  have hθ : IsInfFam θ := hvac.2.inf
  have key := GlobalTheory.VacMove.mem_latO_iff_actO hY.rigA'.1 hΛA' hY.rigW.1 hΛW mA' mW
  have key' := GlobalTheory.VacMove.mem_latO_iff_actO hΛA' hY.rigA'.1 hΛW hY.rigW.1 (GlobalTheory.VacMove.moves_inv mA')
    (GlobalTheory.VacMove.moves_inv mW)
  show IsVacO ψ θ A' WW Y.rA'.s Y.rW.s ΛA' ΛW (Y.ω' t₀ (g', h) Y.vac')
  refine GlobalTheory.WeilVacMove.isVacO_om D ψ θ A' WW _ _ (Y.ω' t₀) hW hθ Y.rA'.s Y.rA'.s Y.rW.s Y.rW.s _ _ _ _ g' h
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hg', Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hh, Matrix.mul_one, Matrix.one_mul])
    (fun u => ⟨fun hu => ⟨_, (key' u).1 hu, ?_⟩, ?_⟩) Y.vac' hvac
  · have e := GlobalTheory.WeilVacMove.actO_inv_actO g'⁻¹ h⁻¹ u
    rw [inv_inv, inv_inv] at e
    exact e.symm
  · rintro ⟨u₀, hu₀, rfl⟩
    exact (key u₀).1 hu₀
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarFundamentalDomainRightTranslateUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarFundamentalDomainRightTranslateUnitary
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Grid Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Mult MeasureTheory

theorem GlobalTheory.RightTranslateFundDomain.haar_and_fundDomain : ∀ {D : D7} {V : HSp D} (m : MeasureTheory.Measure (GA D V)) (fd : Set (GA D V)) (g : GA D V), m.IsHaarMeasure → MeasureTheory.IsFundamentalDomain (GQ V) fd m → (m.map (fun x => x * g⁻¹)).IsHaarMeasure ∧ MeasureTheory.IsFundamentalDomain (GQ V) ((fun x => x * g) ⁻¹' fd) (m.map (fun x => x * g⁻¹)) := by
  intro D V m fd g hm hfd
  have hmeas : Measurable (fun x : GA D V => x * g⁻¹) := measurable_mul_const g⁻¹
  refine ⟨?_, ?_⟩
  · have h := Measure.isHaarMeasure_map_mul_right m g⁻¹
    exact h
  · refine hfd.preimage_of_equiv (e := id) ?_ Function.bijective_id ?_
    · refine ⟨(measurable_mul_const g).aemeasurable, ?_⟩
      rw [Measure.map_map (measurable_mul_const g) hmeas]
      have : ((fun x : GA D V => x * g) ∘ fun x => x * g⁻¹) = id := by
        funext x; simp
      rw [this, Measure.map_id]
    · intro h x
      show (h • x) * g = h • (x * g)
      simp [Submonoid.smul_def, Subgroup.smul_def, mul_assoc]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarFundamentalDomainRightTranslateUnitaryStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Grid Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Mult MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_fundamentalDomain_rightTranslate_unitary : ∀ {D : D7} {V : HSp D} (m : MeasureTheory.Measure (GA D V)) (fd : Set (GA D V)) (g : GA D V), m.IsHaarMeasure → MeasureTheory.IsFundamentalDomain (GQ V) fd m → (m.map (fun x => x * g⁻¹)).IsHaarMeasure ∧ MeasureTheory.IsFundamentalDomain (GQ V) ((fun x => x * g) ⁻¹' fd) (m.map (fun x => x * g⁻¹)) := by
  first | exact @GlobalTheory.RightTranslateFundDomain.haar_and_fundDomain | exact GlobalTheory.RightTranslateFundDomain.haar_and_fundDomain | (intros; apply GlobalTheory.RightTranslateFundDomain.haar_and_fundDomain <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeesawTripleMovedToSelfDualIsValid
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Grid Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Mult MeasureTheory

noncomputable section

namespace GlobalTheory.BotMove

theorem rig_move {D : D7} {V : HSp D} (rr : Rig V) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (g : GA D V)
    (hr : rr.Is) (hΛ : IsSelfDualC V Λ) (hm : GlobalTheory.FinPl.Moves V g rr.Λ Λ (fun _ => True)) :
    Rig.Is (⟨Λ, Lev.finE V g * rr.β, rr.s, rr.B⟩ : Rig V) :=
  ⟨hΛ, GlobalTheory.Core.Mi.FrameMove.isFrame_of_moves D V g rr.Λ Λ rr.β hm hr.2.1, hr.2.2⟩

theorem moveTri_is : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    ∀ g ∈ GfC A, ∀ g' ∈ GfC A', ∀ h ∈ GfC WW,
    GlobalTheory.FinPl.Moves A g Y.rA.Λ ΛA (fun _ => True) → GlobalTheory.FinPl.Moves A' g' Y.rA'.Λ ΛA' (fun _ => True) →
    GlobalTheory.FinPl.Moves WW h Y.rW.Λ ΛW (fun _ => True) →
    ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r t ≠ 0 ∧ r' t ≠ 0) →
    (∀ t, Y.ω t (g, h) Y.vac = r t • Y.ω t₀ (g, h) Y.vac) → (∀ t, Y.ω' t (g', h) Y.vac' = r' t • Y.ω' t₀ (g', h) Y.vac') →
    (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').Is ψ θ α β νH S := by
  intro D T A A' WW Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mA mA' mW t₀ r r' hr hv hv'
  exact ⟨hY.rank, rig_move _ _ _ hY.rigA hA mA, rig_move _ _ _ hY.rigA' hA' mA', rig_move _ _ _ hY.rigW hW mW, hY.weil,
    hY.weil', GlobalTheory.T.movedVacuum_negHom_eq_vacuum_movedLattices Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mA mA' mW t₀ r r' hr hv hv', GlobalTheory.T.movedVacuum_hom_eq_vacuum_movedLattices Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mA mA' mW t₀ r r' hr hv hv', hY.idem, hY.expo, GlobalTheory.T.movedFiniteDatum_negHom_eq_standardPair_first Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mA mA' mW t₀ r r' hr hv hv',
    GlobalTheory.T.translated_finite_datum_eq_standardPairSecondMember Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mA mA' mW t₀ r r' hr hv hv', GlobalTheory.T.haar_fundamentalDomain_rightTranslate_unitary _ _ g hY.meas.1 hY.meas.2, GlobalTheory.T.haar_fundamentalDomain_rightTranslate_unitary _ _ g' hY.meas'.1 hY.meas'.2⟩

end GlobalTheory.BotMove

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeesawTripleMovedToSelfDualIsValidStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeesawTriple_moved_to_selfDual_isValid : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    ∀ g ∈ GfC A, ∀ g' ∈ GfC A', ∀ h ∈ GfC WW,
    GlobalTheory.FinPl.Moves A g Y.rA.Λ ΛA (fun _ => True) → GlobalTheory.FinPl.Moves A' g' Y.rA'.Λ ΛA' (fun _ => True) →
    GlobalTheory.FinPl.Moves WW h Y.rW.Λ ΛW (fun _ => True) →
    ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r t ≠ 0 ∧ r' t ≠ 0) →
    (∀ t, Y.ω t (g, h) Y.vac = r t • Y.ω t₀ (g, h) Y.vac) → (∀ t, Y.ω' t (g', h) Y.vac' = r' t • Y.ω' t₀ (g', h) Y.vac') →
    (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').Is ψ θ α β νH S := by
  first | exact @GlobalTheory.BotMove.moveTri_is | exact GlobalTheory.BotMove.moveTri_is | (intros; apply GlobalTheory.BotMove.moveTri_is <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedSeesawTripleThetaIntegralEqScaled
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedSeesawTripleThetaIntegralEqScaled
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove

noncomputable section

open MeasureTheory GlobalTheory.Grid

namespace GlobalTheory.BotMove

variable {D : D7} {T : Type} {A A' WW : HSp D}

theorem moveTri_ker (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    {α β : T → ((AE D)ˣ →* Circle)} {νH : T → HChar D.host.E} {S : T → Finset (Formalism.L2.DIV.Pl D.host.E)}
    (hY : Y.Is ψ θ α β νH S) (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E))
    {g : GA D A} (hg : g ∈ GfC A) (g' : GA D A') {h : GA D WW} (hh : h ∈ GfC WW) (t₀ : T) (r r' : T → ℂ)
    (t : T) (P : PolF D WW.rank A.rank) (y : GA D WW) (x : GA D A) :
    (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker ψ θ t P y x = (r t)⁻¹ * Y.ker ψ θ t P (y * h) (x * g) := by
  have hgs : (ofSgn true A).symm g ∈ GfC (neg A) := hg
  have key : Y.ω t (g, h) (pureTensorO ψ θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) P) =
      pureTensorO ψ θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.ω t (g, h) (Y.f t)) P :=
    (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ (neg A) WW _ _ ((Y.ω t).toSgn true) (hY.weil t) hY.isVac.2.inf
      (fun τ => -Y.rA.s τ) (fun τ => -Y.rA.s τ) Y.rA.B Y.rA.B Y.rW.s Y.rW.s Y.rW.B Y.rW.B ((ofSgn true A).symm g) h
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hgs, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hh, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hgs, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hh, Matrix.one_mul])
      (Y.f t) (GlobalTheory.ConstRatio.theta_f hY t).1 P).2
  show Y.ω t (x, y) (pureTensorO ψ θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B
      ((r t)⁻¹ • Y.ω t (g, h) (Y.f t)) P) 0 =
    (r t)⁻¹ * Y.ω t (x * g, y * h) (pureTensorO ψ θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) P) 0
  rw [GlobalTheory.FiniteFock.pureTensorO_smul, map_smul, Pi.smul_apply, smul_eq_mul, ← key, ← Module.End.mul_apply, ← map_mul]
  rfl

theorem moveTri_I : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    ∀ g ∈ GfC A, ∀ (g' : GA D A'), ∀ h ∈ GfC WW, ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r t ≠ 0) →
    ∀ t P (y : GA D WW),
      (MeasureTheory.IntegrableOn ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker ψ θ t P y) (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').fd
          (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').m ↔ MeasureTheory.IntegrableOn (Y.ker ψ θ t P (y * h)) Y.fd Y.m) ∧
      (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').I ψ θ t P y = (r t)⁻¹ * Y.I ψ θ t P (y * h) := by
  intro D T A A' WW Y ψ θ α β νH S hY ΛA ΛA' ΛW g hg g' h hh t₀ r r' hr t P y
  have hk : (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker ψ θ t P y = fun x => (r t)⁻¹ * Y.ker ψ θ t P (y * h) (x * g) :=
    funext (moveTri_ker Y ψ θ hY ΛA ΛA' ΛW hg g' hh t₀ r r' t P y)
  have he : MeasurableEmbedding (fun x : GA D A => x * g⁻¹) := (MeasurableEquiv.mulRight g⁻¹).measurableEmbedding
  have hpre : (fun x : GA D A => x * g⁻¹) ⁻¹' ((fun x => x * g) ⁻¹' Y.fd) = Y.fd := by
    ext x; simp
  have hu : IsUnit (r t)⁻¹ := isUnit_iff_ne_zero.2 (inv_ne_zero (hr t))
  constructor
  · show IntegrableOn ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker ψ θ t P y) ((fun x => x * g) ⁻¹' Y.fd)
      (Y.m.map fun x => x * g⁻¹) ↔ _
    rw [he.integrableOn_map_iff, hpre, hk]
    simp only [Function.comp_def, inv_mul_cancel_right]
    exact integrable_const_mul_iff hu _
  · show ∫ x in (fun x => x * g) ⁻¹' Y.fd, (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker ψ θ t P y x ∂(Y.m.map fun x => x * g⁻¹) =
      (r t)⁻¹ * ∫ x in Y.fd, Y.ker ψ θ t P (y * h) x ∂Y.m
    rw [he.setIntegral_map, hpre, hk]
    simp only [inv_mul_cancel_right]
    exact integral_const_mul _ _

end GlobalTheory.BotMove

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedSeesawTripleThetaIntegralEqScaledStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedSeesawTriple_thetaIntegral_eq_scaled : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    ∀ g ∈ GfC A, ∀ (g' : GA D A'), ∀ h ∈ GfC WW, ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r t ≠ 0) →
    ∀ t P (y : GA D WW),
      (MeasureTheory.IntegrableOn ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker ψ θ t P y) (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').fd
          (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').m ↔ MeasureTheory.IntegrableOn (Y.ker ψ θ t P (y * h)) Y.fd Y.m) ∧
      (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').I ψ θ t P y = (r t)⁻¹ * Y.I ψ θ t P (y * h) := by
  first | exact @GlobalTheory.BotMove.moveTri_I | exact GlobalTheory.BotMove.moveTri_I | (intros; apply GlobalTheory.BotMove.moveTri_I <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedSeesawTriplePrimeThetaIntegralEqScaled
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedSeesawTriplePrimeThetaIntegralEqScaled
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove

namespace GlobalTheory.BotMove

open MeasureTheory

theorem int_prime_moveTri : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    ∀ (g : GA D A), ∀ g' ∈ GfC A', ∀ h ∈ GfC WW, ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r' t ≠ 0) →
    ∀ t P (y : GA D WW),
      (MeasureTheory.IntegrableOn ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker' ψ θ t P y) (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').fd'
          (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').m' ↔ MeasureTheory.IntegrableOn (Y.ker' ψ θ t P (y * h)) Y.fd' Y.m') ∧
      (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').I' ψ θ t P y = (r' t)⁻¹ * Y.I' ψ θ t P (y * h) := by
  intro D T A A' WW Y ψ θ α β νH S hY ΛA ΛA' ΛW g g' hg' h hh t₀ r r' hr' t P y
  have hW : IsWeilDatumO ψ A' WW (α t) (α t / β t) (Y.ω' t) := hY.weil' t
  have hθ : IsInfFam θ := hY.isVac'.2.inf
  have hf := (GlobalTheory.ConstRatio.theta_f hY t).2
  have hk : ∀ x, (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker' ψ θ t P y x = (r' t)⁻¹ * Y.ker' ψ θ t P (y * h) (x * g') := by
    intro x
    change thetaKO (Y.ω' t) x y (pureTensorO ψ θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B
      ((r' t)⁻¹ • Y.ω' t (g', h) (Y.f' t)) P) = (r' t)⁻¹ * thetaKO (Y.ω' t) (x * g') (y * h)
        (pureTensorO ψ θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B (Y.f' t) P)
    rw [GlobalTheory.FiniteFock.pureTensorO_smul, ← (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ A' WW _ _ (Y.ω' t) hW hθ
      Y.rA'.s Y.rA'.s Y.rA'.B Y.rA'.B Y.rW.s Y.rW.s Y.rW.B Y.rW.B g' h
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hg', Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hh, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hg', Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hh, Matrix.one_mul]) _ hf P).2]
    simp only [thetaKO, map_smul, Pi.smul_apply, smul_eq_mul]
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk]
  let e : GA D A' ≃ᵐ GA D A' := MeasurableEquiv.mulRight g'⁻¹
  have hm : (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').m' = Y.m'.map e := rfl
  have hs : e ⁻¹' (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').fd' = Y.fd' := by
    ext x
    change x * g'⁻¹ * g' ∈ Y.fd' ↔ x ∈ Y.fd'
    rw [inv_mul_cancel_right]
  have hc : ∀ x, (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker' ψ θ t P y (e x) = (r' t)⁻¹ * Y.ker' ψ θ t P (y * h) x := by
    intro x
    rw [hk]
    change (r' t)⁻¹ * Y.ker' ψ θ t P (y * h) (x * g'⁻¹ * g') = _
    rw [inv_mul_cancel_right]
  have hu : IsUnit (r' t)⁻¹ := IsUnit.mk0 _ (inv_ne_zero (hr' t))
  constructor
  · rw [hm, integrableOn_map_equiv, hs]
    change Integrable (fun x => (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker' ψ θ t P y (e x)) (Y.m'.restrict Y.fd') ↔ _
    simp_rw [hc]
    exact integrable_const_mul_iff hu _
  · change ∫ x in (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').fd', (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker' ψ θ t P y x
        ∂(moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').m' = (r' t)⁻¹ * ∫ x in Y.fd', Y.ker' ψ θ t P (y * h) x ∂Y.m'
    rw [hm, setIntegral_map_equiv, hs]
    simp_rw [hc]
    exact integral_const_mul _ _

end GlobalTheory.BotMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedSeesawTriplePrimeThetaIntegralEqScaledStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedSeesawTriple_primeThetaIntegral_eq_scaled : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    ∀ (g : GA D A), ∀ g' ∈ GfC A', ∀ h ∈ GfC WW, ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r' t ≠ 0) →
    ∀ t P (y : GA D WW),
      (MeasureTheory.IntegrableOn ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker' ψ θ t P y) (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').fd'
          (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').m' ↔ MeasureTheory.IntegrableOn (Y.ker' ψ θ t P (y * h)) Y.fd' Y.m') ∧
      (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').I' ψ θ t P y = (r' t)⁻¹ * Y.I' ψ θ t P (y * h) := by
  first | exact @GlobalTheory.BotMove.int_prime_moveTri | exact GlobalTheory.BotMove.int_prime_moveTri | (intros; apply GlobalTheory.BotMove.int_prime_moveTri <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomLatticeChangeConstantsAwayUnit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove

namespace GlobalTheory.SqTower

theorem bottom_lattices : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} (μ₀ : T), Lc.Is μ₀ → ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ →
  ∀ (i j : Fin D.R.m) {A A' WW : HSp D} (X Y : Tri T A A' WW), IsBottomTri W i j X → GlobalTheory.SqTower.IsStageC W i j 0 0 Y →
  ∃ (Z : Tri T A A' WW) (v : T → ℂ), GlobalTheory.SqTower.IsStageC W i j 0 0 Z ∧
    Z.rA.Λ = X.rA.Λ ∧ Z.rA'.Λ = X.rA'.Λ ∧ Z.rW.Λ = X.rW.Λ ∧ (∀ t, v t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ v t = D.what₂.embLL ζ * v μ₀) ∧
    ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → Z.IsConst W.ψ W.θ (fun t => v t * c t) := by
  intro D T Lc sc G μ₀ hL W S hN i j A A' WW X Y hX hY
  have hYi := hY.2.2.2.2.2.2.2
  obtain ⟨g, hg, hgm⟩ := GlobalTheory.FinPl.BasePoint.exists_base A Y.rA.Λ X.rA.Λ hYi.rigA.1 hX.is.rigA.1
  obtain ⟨g', hg', hgm'⟩ := GlobalTheory.FinPl.BasePoint.exists_base A' Y.rA'.Λ X.rA'.Λ hYi.rigA'.1 hX.is.rigA'.1
  obtain ⟨h, hh, hhm⟩ := GlobalTheory.FinPl.BasePoint.exists_base WW Y.rW.Λ X.rW.Λ hYi.rigW.1 hX.is.rigW.1
  obtain ⟨r, r', hr0, hr, hr', hζ⟩ := GlobalTheory.T.moved_vacua_scalar_multiples_reference_tuple μ₀ hL W S hN i j Y hY g hg g' hg' h hh
  have hZi := GlobalTheory.T.thetaSeesawTriple_moved_to_selfDual_isValid Y _ _ _ _ _ _ hYi X.rA.Λ X.rA'.Λ X.rW.Λ hX.is.rigA.1 hX.is.rigA'.1 hX.is.rigW.1 g hg g' hg' h hh
    (hgm _) (hgm' _) (hhm _) μ₀ r r' hr0 hr hr'
  have hI := GlobalTheory.T.movedSeesawTriple_thetaIntegral_eq_scaled Y _ _ _ _ _ _ hYi X.rA.Λ X.rA'.Λ X.rW.Λ g hg g' h hh μ₀ r r' (fun t => (hr0 t).1)
  have hI' := GlobalTheory.T.movedSeesawTriple_primeThetaIntegral_eq_scaled Y _ _ _ _ _ _ hYi X.rA.Λ X.rA'.Λ X.rW.Λ g g' hg' h hh μ₀ r r' (fun t => (hr0 t).2)
  refine ⟨moveTri Y X.rA.Λ X.rA'.Λ X.rW.Λ g g' h μ₀ r r', fun t => r' t / r t,
    ⟨hY.1, hY.2.1, hY.2.2.1, hY.2.2.2.1, hY.2.2.2.2.1, hY.2.2.2.2.2.1, hY.2.2.2.2.2.2.1, hZi⟩,
    rfl, rfl, rfl, fun t => ⟨div_ne_zero (hr0 t).2 (hr0 t).1, hζ t⟩, ?_⟩
  rintro c ⟨⟨t₁, ht₁⟩, P, P', hc⟩
  refine ⟨⟨t₁, mul_ne_zero (div_ne_zero (hr0 t₁).2 (hr0 t₁).1) ht₁⟩, P, P', fun t =>
    ⟨fun y => ⟨(hI t P y).1.2 ((hc t).1 (y * h)).1, (hI' t P' y).1.2 ((hc t).1 (y * h)).2⟩, ?_, fun y => ?_⟩⟩
  · obtain ⟨y₀, hy₀⟩ := (hc t).2.1
    refine ⟨y₀ * h⁻¹, ?_⟩
    rw [(hI' t P' _).2, inv_mul_cancel_right]
    exact mul_ne_zero (inv_ne_zero (hr0 t).2) hy₀
  · rw [(hI t P y).2, (hI' t P' y).2, (hc t).2.2 (y * h)]
    field_simp [(hr0 t).1, (hr0 t).2]

end GlobalTheory.SqTower
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomLatticeChangeConstantsAwayUnitStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBottom_lattice_change_constants_awayUnit : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} (μ₀ : T), Lc.Is μ₀ → ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ →
  ∀ (i j : Fin D.R.m) {A A' WW : HSp D} (X Y : Tri T A A' WW), IsBottomTri W i j X → GlobalTheory.SqTower.IsStageC W i j 0 0 Y →
  ∃ (Z : Tri T A A' WW) (v : T → ℂ), GlobalTheory.SqTower.IsStageC W i j 0 0 Z ∧
    Z.rA.Λ = X.rA.Λ ∧ Z.rA'.Λ = X.rA'.Λ ∧ Z.rW.Λ = X.rW.Λ ∧ (∀ t, v t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ v t = D.what₂.embLL ζ * v μ₀) ∧
    ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → Z.IsConst W.ψ W.θ (fun t => v t * c t) := by
  first | exact @GlobalTheory.SqTower.bottom_lattices | exact GlobalTheory.SqTower.bottom_lattices | (intros; apply GlobalTheory.SqTower.bottom_lattices <;> assumption)
end
