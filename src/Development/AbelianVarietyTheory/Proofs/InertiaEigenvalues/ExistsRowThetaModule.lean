module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverRowsAndMono
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaFunctionsSpannedHeckeTwistedStandardFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyAgreeRealOfReadGalois

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacteristicFunctionIntegralApply
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

noncomputable section

namespace GlobalTheory.RefTheta

open MeasureTheory Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.principalLevelFrame GlobalTheory.ThetaTri
open scoped TensorProduct

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}

theorem reference_tuple_used (D : D7) : Used0 D D.what₂.mu0 := Or.inl rfl

abbrev t0 (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) : T := Y.tupT D.what₂.mu0

def repY (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) : D.what₂.FT → NG.FinTyp D.host.E D.R.r :=
  fun σ => rowRepR R.θ (Y.eFT σ)

def IsCanonR (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}
    (i : Fin D.R.m) {j : ℕ} (hj : i.1 + 1 = j) (X : GlobalTheory.NPin.RowMod D rep j) : Prop :=
  ∃ (e : X.A →ₗ[ℂ] Mult.MMap (R.MW i (sg0 D A3.A))) (c : ℝ), Function.Injective e ∧ 0 < c ∧
    X.C.map e = Minf R.θ (Y.PW i) (R.MW i (sg0 D A3.A)) ∧
    (∀ h x, e (X.ρ h x) = actM (Y.PW i) (R.MW i (sg0 D A3.A)) h (e x)) ∧
    (∀ x ∈ X.C, ∀ y ∈ X.C, X.B x y = (c : ℂ) * Mult.ipM (R.MW i (sg0 D A3.A)) (R.νW i) (R.fdW i) (e x) (e y)) ∧
    ∀ y : D.what₂.Mj (i.1 + 1), PiTensorProduct.lift (e (X.φ (hj ▸ y))) = (Y.IL.jMj i y).1

variable {Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0}

def eC {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {i : Fin D.R.m} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) : X.A →ₗ[ℂ] Mult.MMap (R.MW i (sg0 D A3.A)) :=
  Classical.choose hc

def cC {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {i : Fin D.R.m} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) : ℝ :=
  Classical.choose (Classical.choose_spec hc)

def yv {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {i : Fin D.R.m} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) :
    ↥X.C →ₗ[ℂ] (Formalism.L2.Theta.GA D (Wc D i) → ℂ) :=
  LinearMap.applyₗ (PiTensorProduct.map (fun τ => (lowT (R.MW i (sg0 D A3.A)) τ).subtype)
      (kUnit (R.MW i (sg0 D A3.A)))) ∘ₗ
    (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).toLinearMap ∘ₗ eC hc ∘ₗ X.C.subtype

variable {M : MtFam D}

def fV (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) :
    ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ) →ₗ[ℂ]
      (Formalism.L2.Theta.GA D (Vc D i) → (R.cV i).W) :=
  (R.cV i).ext ∘ₗ
    { toFun := fun F k => Ad.eW D.what₂.mu0 (reference_tuple_used D) i
        ((F : GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) (preF (Ad.PV i) k))
      map_add' := fun F F' => by funext k; simp
      map_smul' := fun c F => by funext k; simp }

def omStd (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) (t : T) :
    GAf D.host.E D.R.nV × GAf D.host.E D.R.r →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ) :=
  (R.ωP i t).comp ((Ad.PV i).ψ.prodMap (Y.PW i).ψ)

def Om (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) :
    Submodule ℂ ((R.cV i).W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ)) :=
  OmSub (R.ωP i (t0 Y)) (fV Ad i) (yv hc) (R.νV i (t0 Y)) (R.fdV i (t0 Y)) (R.νW i) (R.fdW i) R.ψ (omStd Ad i (t0 Y))

def om (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) :
    GAf D.host.E D.R.nV × GAf D.host.E D.R.r →* Module.End ℂ ↥(Om Ad i hc) :=
  omSub (R.ωP i (t0 Y)) (fV Ad i) (yv hc) (R.νV i (t0 Y)) (R.fdV i (t0 Y)) (R.νW i) (R.fdW i) R.ψ (omStd Ad i (t0 Y))

def lamV (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) (φ : (R.cV i).W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ))
    (Fm : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ)) (y : ↥X.C) : ℂ :=
  GlobalTheory.ThetaTri.lamV (R.ωP i (t0 Y)) (fV Ad i) (yv hc) (R.νV i (t0 Y)) (R.fdV i (t0 Y)) (R.νW i) (R.fdW i) (cC hc : ℂ) φ Fm y

def lamL (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) :
    ↥(Om Ad i hc) →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ) →ₗ[ℂ] ↥X.C →ₗ⋆[ℂ] ℂ :=
  lam (R.ωP i (t0 Y)) (fV Ad i) (yv hc) (R.νV i (t0 Y)) (R.fdV i (t0 Y)) (R.νW i) (R.fdW i) (cC hc : ℂ) R.ψ
    (omStd Ad i (t0 Y))


variable (Y) in
def phi0 (i : Fin D.R.m) : (R.cV i).W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ) :=
  pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A3.A))) (R.BV i)
    (onb (R.MW i (sg0 D A3.A))) (R.vP i (t0 Y)) ∘ₗ R.ioP i (kUnit (R.MW i (sg0 D A3.A)))

end GlobalTheory.RefTheta

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleThetaValuedMapMemThetaData
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleThetaValuedMapMemThetaData
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

noncomputable section

namespace GlobalTheory.RefTheta

open MeasureTheory Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.principalLevelFrame _root_.Formalism.L2.Theta
open Formalism.BasicNotions.TH GlobalTheory.ThetaTri
open scoped Topology

section Forms

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  {Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0} {M : MtFam D}

def fFin (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m)
    (Fm : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ)) :
    Bridge.Gf (Vc D i) → (R.cV i).W :=
  fun k => Ad.eW D.what₂.mu0 (reference_tuple_used D) i
    ((Fm : GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) (preF (Ad.PV i) k))

theorem fV_eq_ext (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m)
    (Fm : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ)) :
    fV Ad i Fm = (R.cV i).ext (fFin Ad i Fm) := rfl

theorem fFin_rat (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m)
    (Fm : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ))
    {γ : GA D (Vc D i)} (hγ : γ ∈ GQ (Vc D i)) (k : Bridge.Gf (Vc D i)) :
    fFin Ad i Fm ((finHom (Vc D i)).rangeRestrict γ * k) = (R.cV i).ρ γ (fFin Ad i Fm k) := by
  set x := preF (Ad.PV i) ((finHom (Vc D i)).rangeRestrict γ) with hxdef
  have hx : finHom (Vc D i) γ = finHom (Vc D i) ((Ad.PV i).ψ x) :=
    (congrArg Subtype.val (GlobalTheory.ThetaFormV.fin_preF (Ad.PV i) ((finHom (Vc D i)).rangeRestrict γ))).symm
  have hrat : x ∈ ReciprocityTheory.Aut.GQ D.host.E D.R.nV := (Ad.rat i x).2 ⟨γ, hγ, hx⟩
  have e1 : preF (Ad.PV i) ((finHom (Vc D i)).rangeRestrict γ * k) = x * preF (Ad.PV i) k := by
    rw [GlobalTheory.ThetaFormV.preF_mul, ← hxdef]
  have hF := Fm.2.1 ⟨x, hrat⟩ (preF (Ad.PV i) k)
  unfold fFin
  rw [e1]
  rw [← Ad.wt D.what₂.mu0 (reference_tuple_used D) i ⟨x, hrat⟩ γ hγ hx]
  exact congrArg _ hF

theorem fV_invariant (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m)
    (Fm : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ)) :
    ∀ γ ∈ GQ (Vc D i), ∀ h, fV Ad i Fm (γ * h) = fV Ad i Fm h := by
  intro γ hγ h
  rw [fV_eq_ext, GlobalTheory.ThetaFormV.ext_apply, GlobalTheory.ThetaFormV.ext_apply, map_mul, fFin_rat Ad i Fm hγ]
  have e : (R.cV i).ρ (γ * h)⁻¹ * (R.cV i).ρ γ = (R.cV i).ρ h⁻¹ := by
    rw [← map_mul]; congr 1; group
  exact congrArg (fun T : Module.End ℂ (R.cV i).W => T _) e

end Forms

end GlobalTheory.RefTheta

noncomputable section

namespace GlobalTheory.RefTheta

open MeasureTheory Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.principalLevelFrame _root_.Formalism.L2.Theta
open Formalism.BasicNotions.TH GlobalTheory.ThetaTri Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Topology

section Cont

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  {Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0} {M : MtFam D}

theorem fV_continuous (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m)
    (hρ : ∀ x, Continuous fun g => (R.cV i).ρ g x)
    (Fm : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ)) :
    Continuous (fV Ad i Fm) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D (Vc D i)) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig (Vc D i).gram))
  obtain ⟨N, hN, hlev⟩ := Fm.2.2
  let J : Subgroup (Bridge.Gf (Vc D i)) :=
    { carrier := {q | ∀ k, fFin Ad i Fm (k * q) = fFin Ad i Fm k}
      mul_mem' := fun {a b} ha hb k => by simp only [Set.mem_setOf_eq] at ha hb ⊢; rw [← mul_assoc, hb, ha]
      one_mem' := fun k => by rw [mul_one]
      inv_mem' := fun {a} ha k => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [← ha (k * a⁻¹), inv_mul_cancel_right] }
  have hfJ : fFin Ad i Fm ∈ Bridge.AdForms ((finHom (Vc D i)).rangeRestrict.comp (GQ (Vc D i)).subtype)
      ((R.cV i).ρ.comp (GQ (Vc D i)).subtype) J 1 :=
    GlobalTheory.ThetaFormV.mem_adForms_one _ _ (fun γ hγ k => fFin_rat Ad i Fm hγ k) J (fun q hq => hq)
  have hJ : ∀ᶠ κ in 𝓝 (1 : GA D (Vc D i)), ∃ h : (finHom (Vc D i)).rangeRestrict κ ∈ J,
      (1 : J →* ℂˣ) ⟨_, h⟩ = 1 := by
    filter_upwards [GlobalTheory.ThetaFormV.eventually_cong_preF (Ad.PV i) Y.hF
      ((GlobalTheory.HeightCounting.Up.StandardFrameAgreement.stdFrame_iff _ _).1 (Ad.std i)) hN] with κ hκ
    refine ⟨fun k => ?_, rfl⟩
    show fFin Ad i Fm (k * (finHom (Vc D i)).rangeRestrict κ) = fFin Ad i Fm k
    unfold fFin
    rw [GlobalTheory.ThetaFormV.preF_mul, hlev _ hκ]
  exact (GlobalTheory.ThetaIntegrand.form_continuous (finHom (Vc D i)).rangeRestrict (GQ (Vc D i)) (R.cV i).ρ
    hρ hJ hfJ).congr fun g => (GlobalTheory.ThetaFormV.ext_apply _ _ _).symm

end Cont

end GlobalTheory.RefTheta

noncomputable section

namespace GlobalTheory.RefTheta

open scoped ComplexOrder


open MeasureTheory Formalism.IndefR.Datum Formalism.IndefR.Links _root_.Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.ThetaTri in
theorem mem_Om_of_theta : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (M : MtFam D) (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) (X : GlobalTheory.NPin.RowMod D (GlobalTheory.RefTheta.repY Y) (i.1 + 1)) (hc : GlobalTheory.RefTheta.IsCanonR Y i rfl X) (φ : (R.cV i).W →ₗ[ℂ] (Formalism.IndefR.Datum.WO (Formalism.IndefR.Links.Vc D i) (Formalism.IndefR.Links.Wc D i) → ℂ)), (∀ v, Formalism.IndefR.Datum.IsThetaFunO R.ψ (Formalism.IndefR.Links.Vc D i) (Formalism.IndefR.Links.Wc D i) (φ v)) → φ ∈ GlobalTheory.RefTheta.Om Ad i hc := by
  intro _ hP D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hPins _ hEx M Ad i X hc φ hφ
  have core := (GlobalTheory.CoreOfWeak.core_of_weak R F hPins.char hEx).1
  have hm := core.models
  have hθ : IsInfFam R.θ := hm.inf
  have hω := core.thP.ωP i (t0 Y)
  have hp : (Vc D i).IsPosDef := hm.vpos i
  have hpd : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ =>
    GlobalTheory.RepsObj.gramAt_posDef hp (D.sp.V_sig ((i : ℕ) + 1)) τ
  have hHV := (hm.νV i (t0 Y)).1.1
  have hfdV := (hm.νV i (t0 Y)).2
  have hHW : (R.νW i).IsHaarMeasure := (hm.νW i).1.1
  have hfdW : IsFundamentalDomain (GQ (Wc D i)) (R.fdW i) (R.νW i) := (hm.νW i).2
  have hρ : ∀ x, Continuous fun g => (R.cV i).ρ g x := (hm.cV i).2.2.1
  intro p
  have hφ' : ∀ v, IsThetaFunO R.ψ (Vc D i) (Wc D i) (valAct1 (omStd Ad i (t0 Y)) p φ v) :=
    fun v => hω.om_pres _ _ (hφ v)
  refine ⟨hφ', fun Fm g => ?_, fun Fm y => ?_⟩
  · have hc1 := fV_continuous Ad i hρ Fm
    have hc2 := fV_invariant Ad i Fm
    exact GlobalTheory.DefiniteQuotient.integrableOn_theta D R.ψ hω.std (Vc D i) (Wc D i) _ _ _ hω hpd _
      (valAct1 (omStd Ad i (t0 Y)) p φ) hφ' _ hc1 hc2 _ _ hHV hfdV g
  · have hc1 := fV_continuous Ad i hρ Fm
    have hc2 := fV_invariant Ad i Fm
    have hmap := (Classical.choose_spec (Classical.choose_spec hc)).2.2.1
    have hey : eC hc (y : X.A) ∈ Formalism.IndefR.principalLevelFrame.Minf R.θ (Y.PW i) (R.MW i (sg0 D A3.A)) := by
      rw [← hmap]; exact ⟨y, y.2, rfl⟩
    have hyv : yv hc y = eC hc (y : X.A) (fun τ => ((Classical.epsilon fun u : ↥(lowT (R.MW i (sg0 D A3.A)) τ) =>
        ‖((u : (R.MW i (sg0 D A3.A)).sm τ) : (R.MW i (sg0 D A3.A)).H τ)‖ = 1 : ↥(lowT (R.MW i (sg0 D A3.A)) τ)) :
          (R.MW i (sg0 D A3.A)).sm τ)) := by
      simp [yv, kUnit, PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod]
    obtain ⟨haut, hcu⟩ := GlobalTheory.T.multiplicitySpaceAllLevels_values_smooth_cuspidal R.θ (Y.PW i) (R.MW i (sg0 D A3.A)) _ hey
      (fun τ => ((Classical.epsilon fun u : ↥(lowT (R.MW i (sg0 D A3.A)) τ) =>
        ‖((u : (R.MW i (sg0 D A3.A)).sm τ) : (R.MW i (sg0 D A3.A)).H τ)‖ = 1 : ↥(lowT (R.MW i (sg0 D A3.A)) τ)) :
          (R.MW i (sg0 D A3.A)).sm τ))
    rw [← hyv] at haut hcu
    have hR := (GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ haut hcu).conj
    have hgr := GlobalTheory.T.moderateGrowth_definiteThetaIntegral_vectorForm R.ψ (Vc D i) (Wc D i) _ _ _ hω hpd _ _ hHV hfdV _
      (valAct1 (omStd Ad i (t0 Y)) p φ) hφ' _ hc1 hc2
    have hct := GlobalTheory.T.continuous_definiteThetaIntegral_vectorForm R.ψ (Vc D i) (Wc D i) _ _ _ hω hpd _ _ hHV hfdV _
      (valAct1 (omStd Ad i (t0 Y)) p φ) hφ' _ hc1 hc2
    have hinv : ∀ γ ∈ GQ (Wc D i), ∀ g, (∫ h in R.fdV i (t0 Y),
        thetaKO (R.ωP i (t0 Y)) h (γ * g)
          (valAct1 (omStd Ad i (t0 Y)) p φ (fV Ad i Fm h)) ∂(R.νV i (t0 Y))) =
        ∫ h in R.fdV i (t0 Y), thetaKO (R.ωP i (t0 Y)) h g
          (valAct1 (omStd Ad i (t0 Y)) p φ (fV Ad i Fm h)) ∂(R.νV i (t0 Y)) := by
      intro γ hγ g
      congr 1
      funext h
      have e : ((h, γ * g) : GA D (Vc D i) × GA D (Wc D i)) = (1, γ) * (h, g) := by simp
      unfold thetaKO
      rw [e, map_mul]
      exact hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ _ (hφ' _))
    have := hR.integrableOn_modGrowth_mul hHW hfdW hgr hinv hct.aestronglyMeasurable
    convert this using 1
    rw [mul_comm]
    rfl

end GlobalTheory.RefTheta
end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleThetaValuedMapMemThetaDataStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.referenceTuple_thetaValued_map_mem_thetaData : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (M : MtFam D) (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) (X : GlobalTheory.NPin.RowMod D (GlobalTheory.RefTheta.repY Y) (i.1 + 1)) (hc : GlobalTheory.RefTheta.IsCanonR Y i rfl X) (φ : (R.cV i).W →ₗ[ℂ] (Formalism.IndefR.Datum.WO (Formalism.IndefR.Links.Vc D i) (Formalism.IndefR.Links.Wc D i) → ℂ)), (∀ v, Formalism.IndefR.Datum.IsThetaFunO R.ψ (Formalism.IndefR.Links.Vc D i) (Formalism.IndefR.Links.Wc D i) (φ v)) → φ ∈ GlobalTheory.RefTheta.Om Ad i hc := by
  first | exact @GlobalTheory.RefTheta.mem_Om_of_theta | exact GlobalTheory.RefTheta.mem_Om_of_theta | (intros; apply GlobalTheory.RefTheta.mem_Om_of_theta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrilinearThetaFormReferenceTupleInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrilinearThetaFormReferenceTupleInvariant
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

noncomputable section
namespace GlobalTheory.RefTheta
open scoped TensorProduct
open MeasureTheory Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.principalLevelFrame GlobalTheory.ThetaTri GlobalTheory.ThetaLoc

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  {Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0} {M : MtFam D}

theorem fV_rt (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) (hcv : (R.cV i).Is) (h : Formalism.AUTREP.GAf D.host.E D.R.nV)
    (Fm Fm' : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ))
    (hF : (Fm' : Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) = NG.rt D.host.E D.R.nV h Fm)
    (x : Formalism.L2.Theta.GA D (Vc D i)) : RefTheta.fV Ad i Fm' x = RefTheta.fV Ad i Fm (x * (Ad.PV i).ψ h) := by
  show (R.cV i).ext _ x = (R.cV i).ext _ (x * (Ad.PV i).ψ h)
  rw [GlobalTheory.DefLiftHecke.ext_mul _ hcv _ ((Ad.PV i).into h) x]
  show (R.cV i).ρ x⁻¹ _ = _
  simp only [LinearMap.coe_mk, AddHom.coe_mk, preF_mul, hF, NG.rt]

theorem fV_rat (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m)
    (Fm : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ))
    (γ : Formalism.L2.Theta.GA D (Vc D i)) (hγ : γ ∈ Formalism.L2.Theta.GQ (Vc D i)) (x : Formalism.L2.Theta.GA D (Vc D i)) :
    RefTheta.fV Ad i Fm (γ * x) = RefTheta.fV Ad i Fm x := by
  obtain ⟨y, hy⟩ := fin_frame_surj (Ad.PV i) ((Formalism.L2.Theta.finHom (Vc D i)).rangeRestrict γ)
  obtain ⟨z, hz⟩ := fin_frame_surj (Ad.PV i) ((Formalism.L2.Theta.finHom (Vc D i)).rangeRestrict x)
  have he : Formalism.L2.Theta.finHom (Vc D i) γ = Formalism.L2.Theta.finHom (Vc D i) ((Ad.PV i).ψ y) :=
    (congrArg Subtype.val hy).symm
  have hh' : y ∈ ReciprocityTheory.Aut.GQ D.host.E D.R.nV := (Ad.rat i _).2 ⟨γ, hγ, he⟩
  show (R.cV i).ρ (γ * x)⁻¹ (Ad.eW D.what₂.mu0 (reference_tuple_used D) i ((Fm : Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W)
      (preF (Ad.PV i) ((Formalism.L2.Theta.finHom (Vc D i)).rangeRestrict (γ * x))))) =
    (R.cV i).ρ x⁻¹ (Ad.eW D.what₂.mu0 (reference_tuple_used D) i ((Fm : Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W)
      (preF (Ad.PV i) ((Formalism.L2.Theta.finHom (Vc D i)).rangeRestrict x))))
  have hprod : (Formalism.L2.Theta.finHom (Vc D i)).rangeRestrict γ * (Formalism.L2.Theta.finHom (Vc D i)).rangeRestrict x =
      (Formalism.L2.Theta.finHom (Vc D i)).rangeRestrict ((Ad.PV i).ψ (y * z)) :=
    (congrArg₂ (· * ·) hy.symm hz.symm).trans
      ((map_mul (Formalism.L2.Theta.finHom (Vc D i)).rangeRestrict _ _).symm.trans
        (congrArg (Formalism.L2.Theta.finHom (Vc D i)).rangeRestrict (map_mul (Ad.PV i).ψ y z).symm))
  have key : preF (Ad.PV i) ((Formalism.L2.Theta.finHom (Vc D i)).rangeRestrict (γ * x)) = y * z :=
    (congrArg (preF (Ad.PV i)) ((map_mul (Formalism.L2.Theta.finHom (Vc D i)).rangeRestrict γ x).trans hprod)).trans (preF_frame _ _)
  have hz' : preF (Ad.PV i) ((Formalism.L2.Theta.finHom (Vc D i)).rangeRestrict x) = z :=
    (congrArg (preF (Ad.PV i)) hz.symm).trans (preF_frame _ _)
  rw [key, hz']
  have e1 := Fm.2.1 ⟨y, hh'⟩ z
  have e2 := Ad.wt D.what₂.mu0 (reference_tuple_used D) i ⟨y, hh'⟩ γ hγ he
    ((Fm : Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) z)
  rw [e1, e2, _root_.mul_inv_rev,
    map_mul, Module.End.mul_apply, ← Module.End.mul_apply ((R.cV i).ρ γ⁻¹), ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply]

theorem yv_apply {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {i : Fin D.R.m} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) (y : ↥X.C) (x : Formalism.L2.Theta.GA D (Wc D i)) :
    RefTheta.yv hc y x = PiTensorProduct.lift (RefTheta.eC hc (y : X.A)) (PiTensorProduct.map
      (fun τ => (lowT (R.MW i (sg0 D A3.A)) τ).subtype) (kUnit (R.MW i (sg0 D A3.A)))) x := rfl

theorem yv_rt {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {i : Fin D.R.m} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X)
    (g : Formalism.AUTREP.GAf D.host.E D.R.r) (y y' : ↥X.C) (hy : (y' : X.A) = X.ρ g y) (x : Formalism.L2.Theta.GA D (Wc D i)) :
    RefTheta.yv hc y' x = RefTheta.yv hc y (x * (Y.PW i).ψ g) := by
  have he : RefTheta.eC hc (y' : X.A) = Formalism.IndefR.principalLevelFrame.actM (Y.PW i) (R.MW i (sg0 D A3.A)) g (RefTheta.eC hc (y : X.A)) := by
    rw [hy]; exact (Classical.choose_spec (Classical.choose_spec hc)).2.2.2.1 g y
  rw [RefTheta.yv_apply, RefTheta.yv_apply, he, lift_actM]

theorem yv_rat {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {i : Fin D.R.m} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X)
    (y : ↥X.C) (γ : Formalism.L2.Theta.GA D (Wc D i)) (hγ : γ ∈ Formalism.L2.Theta.GQ (Wc D i)) (x : Formalism.L2.Theta.GA D (Wc D i)) :
    RefTheta.yv hc y (γ * x) = RefTheta.yv hc y x := by
  have hm : RefTheta.eC hc (y : X.A) ∈ LeftInvM (R.MW i (sg0 D A3.A)) := by
    apply minf_le_leftInv R.θ (Y.PW i)
    rw [← (Classical.choose_spec (Classical.choose_spec hc)).2.2.1]
    exact Submodule.mem_map_of_mem y.2
  rw [RefTheta.yv_apply, RefTheta.yv_apply]
  exact lift_left _ _ hm _ γ hγ x

theorem lamV_inv : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (M : MtFam D) (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) (X : GlobalTheory.NPin.RowMod D (GlobalTheory.RefTheta.repY Y) (i.1 + 1)) (hc : GlobalTheory.RefTheta.IsCanonR Y i rfl X) (h : GAf D.host.E D.R.nV) (g : GAf D.host.E D.R.r) (φ : (R.cV i).W →ₗ[ℂ] (Formalism.IndefR.Datum.WO (Formalism.IndefR.Links.Vc D i) (Formalism.IndefR.Links.Wc D i) → ℂ)), φ ∈ GlobalTheory.RefTheta.Om Ad i hc → ∀ (Fm Fm' : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ)) (y y' : ↥X.C), (Fm' : GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) = NG.rt D.host.E D.R.nV h Fm → (y' : X.A) = X.ρ g y → GlobalTheory.RefTheta.lamV Ad i hc (GlobalTheory.ThetaTri.valAct1 (GlobalTheory.RefTheta.omStd Ad i (GlobalTheory.RefTheta.t0 Y)) (h, g) φ) Fm' y' = GlobalTheory.RefTheta.lamV Ad i hc φ Fm y := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH hEx M Ad i X hc h g φ hφ Fm Fm' y y' hF hy
  have hcore := (GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hEx).1
  have hW := hcore.thP.ωP i (t0 Y)
  have hcv : (R.cV i).Is := hcore.models.cV i
  have hth : ∀ v, IsThetaFunO R.ψ (Vc D i) (Wc D i) (φ v) := by
    intro v
    have := (hφ 1).1 v
    simpa [valAct1_apply] using this
  have hV := hcore.models.νV i (t0 Y)
  have hWm := hcore.models.νW i
  haveI : (R.νV i (t0 Y)).IsHaarMeasure := hV.1.1
  haveI : (R.νV i (t0 Y)).IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D _ _ hV.1.1
  haveI : (R.νW i).IsHaarMeasure := hWm.1.1
  haveI : (R.νW i).IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D _ _ hWm.1.1
  haveI : Countable (Formalism.L2.Theta.GQ (Vc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig (Vc D i).gram
  haveI : Countable (Formalism.L2.Theta.GQ (Wc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig (Wc D i).gram
  have inner : ∀ g₀, thIn (R.ωP i (t0 Y)) (RefTheta.fV Ad i) (R.νV i (t0 Y))
      (R.fdV i (t0 Y)) (valAct1 (RefTheta.omStd Ad i (t0 Y)) (h, g) φ) Fm' g₀ =
      thIn (R.ωP i (t0 Y)) (RefTheta.fV Ad i) (R.νV i (t0 Y))
      (R.fdV i (t0 Y)) φ Fm (g₀ * (Y.PW i).ψ g) := by
    intro g₀
    unfold thIn
    have e1 : ∀ h₀, thetaKO (R.ωP i (t0 Y)) h₀ g₀
        (valAct1 (RefTheta.omStd Ad i (t0 Y)) (h, g) φ (RefTheta.fV Ad i Fm' h₀)) =
        thetaKO (R.ωP i (t0 Y)) (h₀ * (Ad.PV i).ψ h) (g₀ * (Y.PW i).ψ g)
          (φ (RefTheta.fV Ad i Fm (h₀ * (Ad.PV i).ψ h))) := by
      intro h₀
      rw [valAct1_apply, RefTheta.fV_rt Ad i hcv h Fm Fm' hF h₀]
      exact thetaKO_act _ _ _ _ _
    simp only [e1]
    refine (Formalism.IndefR.Eqv.rightInv_holds _ (Formalism.L2.Theta.GQ (Vc D i)) _ _ hV.2
      (fun h₁ => thetaKO (R.ωP i (t0 Y)) h₁ (g₀ * (Y.PW i).ψ g) (φ (RefTheta.fV Ad i Fm h₁))) ?_ _).2
    intro γ hγ h₁
    rw [RefTheta.fV_rat Ad i Fm γ hγ h₁]
    have := (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ _ hW _ (hth (RefTheta.fV Ad i Fm h₁))).1 γ hγ 1
      (one_mem _) h₁ (g₀ * (Y.PW i).ψ g)
    rwa [one_mul] at this
  unfold GlobalTheory.RefTheta.lamV GlobalTheory.ThetaTri.lamV
  congr 1
  have e2 : ∀ g₀, star (RefTheta.yv hc y' g₀) * thIn (R.ωP i (t0 Y)) (RefTheta.fV Ad i)
      (R.νV i (t0 Y)) (R.fdV i (t0 Y))
      (valAct1 (RefTheta.omStd Ad i (t0 Y)) (h, g) φ) Fm' g₀ =
      star (RefTheta.yv hc y (g₀ * (Y.PW i).ψ g)) * thIn (R.ωP i (t0 Y)) (RefTheta.fV Ad i)
      (R.νV i (t0 Y)) (R.fdV i (t0 Y)) φ Fm (g₀ * (Y.PW i).ψ g) := by
    intro g₀
    rw [inner, RefTheta.yv_rt hc g y y' hy]
  simp only [e2]
  refine (Formalism.IndefR.Eqv.rightInv_holds _ (Formalism.L2.Theta.GQ (Wc D i)) _ _ hWm.2
    (fun g₁ => star (RefTheta.yv hc y g₁) * thIn (R.ωP i (t0 Y)) (RefTheta.fV Ad i)
      (R.νV i (t0 Y)) (R.fdV i (t0 Y)) φ Fm g₁) ?_ _).2
  intro γ hγ g₁
  rw [RefTheta.yv_rat hc y γ hγ g₁]
  congr 1
  unfold thIn
  congr 1
  funext h₁
  have := (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ _ hW _ (hth (RefTheta.fV Ad i Fm h₁))).1 1 (one_mem _) γ hγ
    h₁ g₁
  rwa [one_mul] at this

end GlobalTheory.RefTheta

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrilinearThetaFormReferenceTupleInvariantStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trilinearThetaForm_referenceTuple_invariant : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (M : MtFam D) (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) (X : GlobalTheory.NPin.RowMod D (GlobalTheory.RefTheta.repY Y) (i.1 + 1)) (hc : GlobalTheory.RefTheta.IsCanonR Y i rfl X) (h : GAf D.host.E D.R.nV) (g : GAf D.host.E D.R.r) (φ : (R.cV i).W →ₗ[ℂ] (Formalism.IndefR.Datum.WO (Formalism.IndefR.Links.Vc D i) (Formalism.IndefR.Links.Wc D i) → ℂ)), φ ∈ GlobalTheory.RefTheta.Om Ad i hc → ∀ (Fm Fm' : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ)) (y y' : ↥X.C), (Fm' : GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) = NG.rt D.host.E D.R.nV h Fm → (y' : X.A) = X.ρ g y → GlobalTheory.RefTheta.lamV Ad i hc (GlobalTheory.ThetaTri.valAct1 (GlobalTheory.RefTheta.omStd Ad i (GlobalTheory.RefTheta.t0 Y)) (h, g) φ) Fm' y' = GlobalTheory.RefTheta.lamV Ad i hc φ Fm y := by
  first | exact @GlobalTheory.RefTheta.lamV_inv | exact GlobalTheory.RefTheta.lamV_inv | (intros; apply GlobalTheory.RefTheta.lamV_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleWeilDatumCharacters
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleWeilDatumCharacters
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

namespace GlobalTheory.RefTupleChars

theorem ref_chars : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (i : Fin D.R.m), Formalism.IndefR.Links.ChrEq (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu (GlobalTheory.RefTheta.t0 Y)) R.eta (i.1 + 1)).1 (R.C.mu0 i) ∧ Formalism.IndefR.Links.ChrEq (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu (GlobalTheory.RefTheta.t0 Y)) R.eta (i.1 + 1)).2 (R.C.mu0 i * R.C.eta⁻¹) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP _ hEx i
  have hlev := (GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hEx).1.lev
  have ht : GlobalTheory.RefTheta.t0 Y = A3.A.μ0 := by
    show Y.tupT D.what₂.mu0 = A3.A.μ0
    rw [← Y.tup0, Y.tupT_tup]
  rw [ht]
  have hxC := hlev.xi A3.A.μ0
  rw [hlev.xi_base] at hxC
  have hxi : R.toLevCh.xi A3.A.μ0 = 1 := MonoidHom.ext fun x =>
    GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one hxC x
  have e : Formalism.IndefR.Lift.chrTh (R.toLevCh.mu A3.A.μ0) R.eta (i.1 + 1) =
      (R.toLevCh.mu0 (i.1 + 1), R.toLevCh.mu0 (i.1 + 1) * R.eta⁻¹) := by
    simp only [Formalism.IndefR.Lift.chrTh, Formalism.IndefR.Links.LevCh.mu, Formalism.IndefR.Lift.tup, hxi, mul_one]
  rw [e]
  have hm := hlev.mu0 i
  have h2 := GlobalTheory.ClassScalarValue.chrEq_mul_inv hm hxC hlev.eta
  rw [hxi, mul_one, mul_one] at h2
  exact ⟨hm, h2⟩

end GlobalTheory.RefTupleChars
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleWeilDatumCharactersStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.referenceTuple_weilDatum_characters : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (i : Fin D.R.m), Formalism.IndefR.Links.ChrEq (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu (GlobalTheory.RefTheta.t0 Y)) R.eta (i.1 + 1)).1 (R.C.mu0 i) ∧ Formalism.IndefR.Links.ChrEq (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu (GlobalTheory.RefTheta.t0 Y)) R.eta (i.1 + 1)).2 (R.C.mu0 i * R.C.eta⁻¹) := by
  first | exact @GlobalTheory.RefTupleChars.ref_chars | exact GlobalTheory.RefTupleChars.ref_chars | (intros; apply GlobalTheory.RefTupleChars.ref_chars <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleDatumFormReadsThetaLiftInnerProduc
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleDatumFormReadsThetaLiftInnerProduc
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

noncomputable section

namespace GlobalTheory.RefThetaRead

open MeasureTheory Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.principalLevelFrame Formalism.IndefR.Mult
  Formalism.L2.Theta Formalism.L2.DIV GlobalTheory.ThetaTri GlobalTheory.ThetaRead
open scoped TensorProduct InnerProductSpace

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}

theorem fire (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (core : GlobalTheory.Hk3.Core R.toRealDat F.lv2) :
    ThetaFireRow (toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj) Y.IL :=
  ⟨fun μ _ i => GlobalTheory.ThetaPRead.isThetaP_toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj core.thP.thF μ i,
    GlobalTheory.ThetaFireLift.thetaFireL R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj core.lev core.grp core.models
      core.thP R.toRealDat.hv0 Y.IL,
    GlobalTheory.LiftResInj.resInjL_toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj core.models.inf⟩


set_option maxHeartbeats 1000000 in
theorem ipM_theta (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (core : GlobalTheory.Hk3.Core R.toRealDat F.lv2)
    (hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ) {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m)
    (x : D.what₂.Mt μ (j.1 + 1)) (y : D.what₂.Mj (j.1 + 1))
    (T' T'' : MMap (R.MW j (sg0 D A3.A))) (hT : PiTensorProduct.lift T' = (Y.IL.jMj j y).1)
    (hT' : PiTensorProduct.lift T'' = (Y.IL.jMj j (D.what₂.thetaP μ (j.1 + 1) x)).1) :
    ipM (R.MW j (sg0 D A3.A)) (R.νW j) (R.fdW j) T' T'' =
      ∫ g in R.fdW j, star (PiTensorProduct.lift T' (emb _ (kUnit (R.MW j (sg0 D A3.A)))) g) *
        (∫ h in R.fdV j (Y.tupT μ), thetaKO (R.ωP j (Y.tupT μ)) h g
          (R.ptP j (Y.tupT μ) (R.ioP j (kUnit (R.MW j (sg0 D A3.A))) ((Y.IL.jMt μ hμ j x).1 h))) ∂(R.νV j (Y.tupT μ)))
        ∂(R.νW j) := by
  have hM := core.models
  have hF := fire Y core
  obtain ⟨w, hw1, hw2, hw3⟩ := hF.2.1 μ hμ j x
  have hth := Y.tied.lift.theta μ hμ j x w (hF.1 _ hμ j) hw1 hw2 hw3
  obtain ⟨U, hU, hUw⟩ := hw1
  have hUw' : PiTensorProduct.lift U = w := hUw
  obtain ⟨T₀, hT₀, hT₀y⟩ := (Y.IL.jMj j y).2
  have hTT : T₀ = T' := PiTensorProduct.lift.injective (hT₀y.trans hT.symm)
  subst hTT
  obtain ⟨hT1, hT2⟩ := (mem_goodPart _ _ _ _ _ _).1 hT₀
  have hT'U : T'' = postOn (R.MW j (sg0 D A3.A)) (R.eWf j (sg0 D A3.A)) U := by
    apply PiTensorProduct.lift.injective
    rw [hT', hth, ← hUw']
    exact (lift_post (R.MW j (sg0 D A3.A)) _ U).symm
  have hin : ∀ g, (∫ h in R.fdV j (Y.tupT μ), thetaKO (R.ωP j (Y.tupT μ)) h g
      (R.ptP j (Y.tupT μ) (R.ioP j (kUnit (R.MW j (sg0 D A3.A))) ((Y.IL.jMt μ hμ j x).1 h))) ∂(R.νV j (Y.tupT μ))) =
      PiTensorProduct.lift U (emb _ (kUnit (R.MW j (sg0 D A3.A)))) g := by
    intro g
    have e1 := (hF.1 _ hμ j).eq (Y.IL.jMt μ hμ j x) (kUnit (R.MW j (sg0 D A3.A))) g
    rw [← hw2, ← hUw'] at e1
    exact e1.symm
  obtain ⟨p1, p2⟩ := ipM_proj R.toRealDat hM hX j (mult_le_wall R.toRealDat F.lv2 false j hT1)
    (mult_le_wall R.toRealDat F.lv2 false j hU) hT2
  simp only [hin]
  rw [hT'U]
  refine p1.trans ?_
  by_cases hne : ∀ τ, lowT (R.MW j (sg0 D A3.A)) τ ≠ ⊥
  · exact (integral_kUnit _ hne _ _ _ _ p2).symm
  · push Not at hne
    obtain ⟨τ, hτ⟩ := hne
    have h0 := emb_eq_zero _ hτ
    have hw0 : w = 0 := hF.2.2 j w ⟨U, hU, hUw⟩
      ((congrArg (fun e => w ∘ₗ e) h0).trans (LinearMap.comp_zero _))
    have hU0 : U = 0 := PiTensorProduct.lift.injective (by rw [hUw', hw0, map_zero])
    exact integral_zero_right (R.MW j (sg0 D A3.A)) _ _ _ _ hU0 _


set_option maxHeartbeats 1000000 in
theorem fV_eq (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (core : GlobalTheory.Hk3.Core R.toRealDat F.lv2) {M : MtFam D}
    (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) (x : D.what₂.Mt D.what₂.mu0 (i.1 + 1))
    (Fm : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ))
    (hFm : (Fm : GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) =
      (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).real x) :
    GlobalTheory.RefTheta.fV Ad i Fm = (Y.IL.jMt D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i x).1 := by
  have e : (fun k => Ad.eW D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i
      ((Fm : GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) (preF (Ad.PV i) k))) =
      fun k => (Y.IL.jMt D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i x).1 ((Ad.PV i).ψ (preF (Ad.PV i) k)) := by
    funext k
    rw [hFm]
    exact Ad.read _ _ i x _
  change (R.cV i).ext (fun k => Ad.eW D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i
      ((Fm : GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) (preF (Ad.PV i) k))) = _
  rw [e]
  obtain ⟨z, hz⟩ : (Y.IL.jMt D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i x).1 ∈
      LinearMap.range (R.extV i (Y.tupT D.what₂.mu0)) := (Y.IL.jMt D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i x).2.1
  have hz' : (R.cV i).ext ((R.HV i (Y.tupT D.what₂.mu0)).e z) = (Y.IL.jMt D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i x).1 := hz
  generalize (Y.IL.jMt D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i x).1 = φ at hz' ⊢
  subst hz'
  exact ext_pre _ (core.models.cV i).1 _ _


set_option maxHeartbeats 1000000 in
theorem main : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (M : MtFam D) (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) (X : GlobalTheory.NPin.RowMod D (GlobalTheory.RefTheta.repY Y) (i.1 + 1)) (hc : GlobalTheory.RefTheta.IsCanonR Y i rfl X) (x : D.what₂.Mt D.what₂.mu0 (i.1 + 1)) (y : D.what₂.Mj (i.1 + 1)) (Fm : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ)), (Fm : GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) = (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).real x → inner ℂ y (D.what₂.thetaP D.what₂.mu0 (i.1 + 1) x) = GlobalTheory.RefTheta.lamV Ad i hc (GlobalTheory.RefTheta.phi0 Y i) Fm ⟨X.φ y, X.φ_mem y⟩ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH hEx M Ad i X hc x y Fm hFm
  have core := (GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hEx).1
  have hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hH.ok.ok2.irr
  have hf := fV_eq Y core Ad i x Fm hFm
  obtain ⟨-, -, -, -, hB, hφ⟩ := Classical.choose_spec (Classical.choose_spec hc)
  have key : inner ℂ y (D.what₂.thetaP D.what₂.mu0 (i.1 + 1) x) = (GlobalTheory.RefTheta.cC hc : ℂ) *
      ∫ g in R.fdW i, star (GlobalTheory.RefTheta.yv hc ⟨X.φ y, X.φ_mem y⟩ g) *
        (∫ h in R.fdV i (Y.tupT D.what₂.mu0), thetaKO (R.ωP i (Y.tupT D.what₂.mu0)) h g
          (GlobalTheory.RefTheta.phi0 Y i ((Y.IL.jMt D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i x).1 h))
            ∂(R.νV i (Y.tupT D.what₂.mu0))) ∂(R.νW i) := by
    refine (X.φ_inner _ _).trans ((hB _ (X.φ_mem _) _ (X.φ_mem _)).trans (congrArg (fun z => (GlobalTheory.RefTheta.cC hc : ℂ) * z) ?_))
    exact ipM_theta Y core hX (GlobalTheory.RefTheta.reference_tuple_used D) i x y _ _ (hφ y) (hφ _)
  rw [key, ← hf]
  rfl

end GlobalTheory.RefThetaRead

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleDatumFormReadsThetaLiftInnerProducStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.referenceTuple_datumForm_reads_thetaLift_innerProducts : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (M : MtFam D) (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) (X : GlobalTheory.NPin.RowMod D (GlobalTheory.RefTheta.repY Y) (i.1 + 1)) (hc : GlobalTheory.RefTheta.IsCanonR Y i rfl X) (x : D.what₂.Mt D.what₂.mu0 (i.1 + 1)) (y : D.what₂.Mj (i.1 + 1)) (Fm : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ)), (Fm : GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) = (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).real x → inner ℂ y (D.what₂.thetaP D.what₂.mu0 (i.1 + 1) x) = GlobalTheory.RefTheta.lamV Ad i hc (GlobalTheory.RefTheta.phi0 Y i) Fm ⟨X.φ y, X.φ_mem y⟩ := by
  first | exact @GlobalTheory.RefThetaRead.main | exact GlobalTheory.RefThetaRead.main | (intros; apply GlobalTheory.RefThetaRead.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleFormsSmoothAdmissibleUnitaryModule
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleFormsSmoothAdmissibleUnitaryModule
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

noncomputable section

namespace GlobalTheory.RefRowMod

open MeasureTheory Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev
  Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.Mult Formalism.IndefR.PeterssonHilbertSpace


set_option maxHeartbeats 1000000 in
theorem main : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G]
    (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3)
    (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0),
    GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt →
    ∀ (i : Fin D.R.m), ∃ X : GlobalTheory.NPin.RowMod D (GlobalTheory.RefTheta.repY Y) (i.1 + 1), GlobalTheory.RefTheta.IsCanonR Y i rfl X := by
  intro hH hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP _ hEx j
  have hcore := (GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hEx).1
  have hmod := hcore.models
  have hθ := hmod.inf
  have hν := hmod.νW j
  have hHaar : (R.νW j).IsHaarMeasure := hν.1.1
  have hFD := hν.2
  have hSig : (Wc D j).SigOK := D.sp.W_sig _
  have hSA : SchurAll D := fun V _ S θ M J χ μ 𝓕 => (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ μ 𝓕).2
  have hHA : HCAll D := fun V _ S θ M J χ => (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ 0 ∅).1
  have hStd : GlobalTheory.Mem.R3.StdFrame Y.hF (Y.PW j) := Y.stdPsi.2 j
  have hcc := GlobalTheory.T.unitary_congruence_conj_contains_congruence D.host.E D.R.r
  obtain ⟨hlin, hherm, hpos⟩ := GlobalTheory.FinTypesRows.minf_sesq (M := R.MW j (sg0 D A3.A)) (θ := R.θ) (R.νW j) (R.fdW j)
    (Y.PW j) hSA hSig hθ hHaar hFD
  have hT := Y.tied.lift
  have hLev := GlobalTheory.FinTypesRows.levOK_levS (Y.PW j) hStd (R.βW j) (R.datWp j (R.levL F.lv2 false (sg0 D A3.A)))
  set c : ℝ := (∏ ρ, ((Mult.dimK _ _ (kapAt (Wc D j) (sg0 D A3.A) ρ) : ℚ) : ℝ)) * (RealDat.nP F.lv2 false)⁻¹ with hcdef
  have hc : 0 < c := mul_pos (Finset.prod_pos fun ρ _ => by exact_mod_cast GlobalTheory.Mem.EasyInputs.dimOK D j (sg0 D A3.A) ρ)
    (inv_pos.2 (RealDat.nP_pos false))
  have hSm := GlobalTheory.Mem.EasyInputs.smAll D (Wc D j) _ (R.MW j (sg0 D A3.A))
  have hex : ∀ x ∈ principalLevelFrame.Minf R.θ (Y.PW j) (R.MW j (sg0 D A3.A)), ∀ y ∈ principalLevelFrame.Minf R.θ (Y.PW j) (R.MW j (sg0 D A3.A)),
      ∃ b, Mult.IsMultIP (R.MW j (sg0 D A3.A)) (R.νW j) (R.fdW j) x y b := by
    intro x hx y hy
    obtain ⟨N, -, hx', hy'⟩ := GlobalTheory.FinTypesRows.exists_common (Y.PW j) hx hy
    exact hSA _ hSig _ R.θ _ _ _ _ _ hθ hHaar hFD x hx' y hy'
  let φ : D.what₂.Mj (j.1 + 1) →ₗ[ℂ] Mult.MMap (R.MW j (sg0 D A3.A)) :=
    (PiTensorProduct.lift : Mult.MMap (R.MW j (sg0 D A3.A)) ≃ₗ[ℂ] _).symm.toLinearMap ∘ₗ
      (Submodule.subtype ((toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj).Wc j)) ∘ₗ (Y.IL.jMj j).toLinearMap
  have hφ : ∀ y, PiTensorProduct.lift (φ y) = (Y.IL.jMj j y).1 := by
    intro y
    exact LinearEquiv.apply_symm_apply _ _
  have hgood : ∀ y, φ y ∈ Mult.goodPart R.θ (R.MW j (sg0 D A3.A)) (levS _ (R.βW j) (R.datWp j (R.levL F.lv2 false (sg0 D A3.A))))
      (levChi _ (R.βW j) (R.datWp j (R.levL F.lv2 false (sg0 D A3.A)))) (R.eWf j (sg0 D A3.A)) := by
    intro y
    obtain ⟨a, ha, hay⟩ := (Y.IL.jMj j y).2
    have : φ y = a := by
      show PiTensorProduct.lift.symm (Y.IL.jMj j y).1 = a
      rw [← hay]
      exact LinearEquiv.symm_apply_apply _ _
    rw [this]
    exact ha
  have hmem : ∀ y, φ y ∈ principalLevelFrame.Minf R.θ (Y.PW j) (R.MW j (sg0 D A3.A)) := fun y =>
    principalLevelFrame.mult_le_Minf hLev (Mult.goodPart_le _ _ _ _ _ (hgood y))
  refine ⟨{ A := Mult.MMap (R.MW j (sg0 D A3.A))
            ρ := principalLevelFrame.actM (Y.PW j) (R.MW j (sg0 D A3.A))
            C := principalLevelFrame.Minf R.θ (Y.PW j) (R.MW j (sg0 D A3.A))
            B := fun x y => (c : ℂ) * Mult.ipM (R.MW j (sg0 D A3.A)) (R.νW j) (R.fdW j) x y
            lin := fun x hx y hy z hz c' => by
              rw [hlin x hx y hy z hz c']
              ring
            herm := fun x hx y hy => by
              rw [map_mul, Complex.conj_ofReal, ← hherm x hx y hy]
            pos := fun x hx hx0 => by
              rw [Complex.re_ofReal_mul]
              exact mul_pos hc (hpos x hx hx0)
            stab := fun h x hx => GlobalTheory.FinTypesRows.minf_stable (Y.PW j) hcc h hx
            inv := fun h x hx y hy => by
              rw [GlobalTheory.T.schur_pairing_invariant_under_standard_group D (Wc D j) _ R.θ (R.MW j (sg0 D A3.A)) D.R.r (Y.PW j) (R.νW j) (R.fdW j) hSA hSig hθ
                hHaar hFD h x hx y hy]
            smooth := fun x hx => GlobalTheory.FinTypesRows.minf_smooth (Y.PW j) hx
            adm := fun N hN => GlobalTheory.FinTypesRows.minf_adm (Y.PW j) hHA hSig hθ (GlobalTheory.FinTypesRows.levN_open (Y.PW j) hStd) N hN
            φ := φ
            φ_mem := hmem
            φ_inner := fun x y => by
              beta_reduce
              rw [hT.mj j x y]
              change (∏ τ, ((Mult.dimK _ _ (kapAt (Wc D j) (sg0 D A3.A) τ) : ℚ) : ℂ)) *
                Mult.ipM (R.MW j (sg0 D A3.A)) (ENNReal.ofReal (RealDat.nP F.lv2 false)⁻¹ • R.νW j) (R.fdW j) (φ x) (φ y) = _
              rw [GlobalTheory.RowModCanon.ipM_smul_measure _ hSm _ _ (inv_nonneg.2 (RealDat.nP_pos false).le) _ _
                (hex _ (hmem x) _ (hmem y)), hcdef]
              push_cast
              ring
            isot := fun σ y => by
              rw [hT.isot j σ y, Y.prtWE j σ]
              constructor
              · rintro ⟨a, ha, hay⟩
                have e : φ y = a := by
                  show PiTensorProduct.lift.symm (Y.IL.jMj j y).1 = a
                  rw [← hay]
                  exact LinearEquiv.symm_apply_apply _ _
                rw [e]
                exact (Submodule.mem_inf.1 ha).2
              · intro h
                exact ⟨φ y, Submodule.mem_inf.2 ⟨hgood y, h⟩, hφ y⟩ }, LinearMap.id, c, Function.injective_id, hc,
    Submodule.map_id _, fun h x => rfl, fun x _ y _ => rfl, fun y => hφ y⟩

end GlobalTheory.RefRowMod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleFormsSmoothAdmissibleUnitaryModuleStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.referenceTuple_forms_smoothAdmissibleUnitaryModule : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (i : Fin D.R.m), ∃ X : GlobalTheory.NPin.RowMod D (GlobalTheory.RefTheta.repY Y) (i.1 + 1), GlobalTheory.RefTheta.IsCanonR Y i rfl X := by
  first | exact @GlobalTheory.RefRowMod.main | exact GlobalTheory.RefRowMod.main | (intros; apply GlobalTheory.RefRowMod.main <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair


open GlobalTheory.RefTheta GlobalTheory.ThetaTri Formalism.IndefR.Datum Formalism.IndefR.Links in
theorem GlobalTheory.RefTheta.datum_real : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (M : MtFam D), GlobalTheory.HeightCounting.MtAd Y M → ∀ (i : Fin D.R.m), ∃ X : GlobalTheory.NPin.RowMod D (GlobalTheory.RefTheta.repY Y) (i.1 + 1), HasThetaAt D (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)) X (R.C.mu0 i) R.C.eta := by
  intro hHC hCR D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH hEx M Ad i
  have hC := (GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hEx).1
  obtain ⟨X, hc⟩ := GlobalTheory.T.referenceTuple_forms_smoothAdmissibleUnitaryModule hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hEx i
  have hth : ∀ v, IsThetaFunO R.ψ (Vc D i) (Wc D i) (phi0 Y i v) := fun v => hC.thP.pt_theta i _ _
  have h0 : phi0 Y i ∈ Om Ad i hc := GlobalTheory.T.referenceTuple_thetaValued_map_mem_thetaData hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hEx M Ad i X hc _ hth
  refine ⟨X, Om Ad i hc, inferInstance, inferInstance, om Ad i hc, lamL Ad i hc, ⟨_, h0⟩, ?_, ?_, ?_⟩
  · intro h g φ Fm Fm' y y' hF hy
    exact GlobalTheory.T.trilinearThetaForm_referenceTuple_invariant D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hEx M Ad i X hc h g φ.1 φ.2 Fm Fm' y y' hF hy
  · intro x y Fm hF
    exact GlobalTheory.T.referenceTuple_datumForm_reads_thetaLift_innerProducts D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hEx M Ad i X hc x y Fm hF
  intro s μw ηw hμw hηw
  obtain ⟨h1, h2⟩ := GlobalTheory.T.referenceTuple_weilDatum_characters D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hEx i
  have hv : ∀ v, phi0 Y i v ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin D.R.nV) (Fin D.R.r)
      (s.w.adicCompletion D.host.E)) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ))
      (_ : GlobalTheory.NPin.IsLinAt (omStd Ad i (t0 Y)) s μw ηw ι ∧ ∀ Φ, IsThetaFunO R.ψ (Vc D i) (Wc D i) (ι Φ)),
      LinearMap.range ι := fun v =>
    GlobalTheory.T.thetaFunctions_spanned_heckeTwisted_standardFrame D R.ψ (Vc D i) (Wc D i) D.R.nV D.R.r (Ad.PV i) (Y.PW i) Y.hF
      (Ad.std i) (Y.stdPsi.2 i) _ _ (R.ωP i (t0 Y)) (hC.thP.ωP i _) _ _ h1 h2 s μw ηw hμw hηw _ (hth v)
  have hlin := mem_iSup_isLinAt_lin' (omStd Ad i (t0 Y)) (IsThetaFunO R.ψ (Vc D i) (Wc D i)) (· ∈ Om Ad i hc)
    (fun β f hf => GlobalTheory.T.referenceTuple_thetaValued_map_mem_thetaData hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hEx M Ad i X hc _ fun v => by
      simpa [single1] using Formalism.IndefR.Fock.CCR.theta_smul hf (β v))
    s μw ηw _ hv
  exact mem_iSup_isLinAt_omSub _ _ _ _ _ _ _ _ _ s μw ηw h0 hlin
