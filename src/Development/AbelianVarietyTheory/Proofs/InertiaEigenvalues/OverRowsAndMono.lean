module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChoiceSideWithE
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OfFirstStepLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SizeParametersNonempty
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjEqOfNormalises

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverRowsAndMono
noncomputable section

namespace GlobalTheory.LiftRef

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2
  GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up Formalism.AUTREP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def autOf {D : D7} {μt : D.what₂.Tup} {j : ℕ} (Mr : MtReal D μt j) (S : Submodule ℂ (GAf D.host.E D.R.nV → Mr.wt.W))
    (hS : NG.IsIrrRep Mr.wt.ρ S) : NG.AutRep D.host.E D.R.nV :=
  { Mr.wt with S := S, irrS := hS }

theorem evG_and {p q : Ctx → Prop} (hp : EvG p) (hq : EvG q) : EvG fun K => p K ∧ q K := by
  obtain ⟨a, ha, hp⟩ := hp
  obtain ⟨b, hb, hq⟩ := hq
  refine ⟨min a b, lt_min ha hb, fun e C8 C5 c6 Cb he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 C5 c6 Cb he (hle.trans (min_le_left _ _)) h52 h8
  obtain ⟨K', hK'⟩ := hq e C8 C5 c6 Cb he (hle.trans (min_le_right _ _)) h52 h8
  refine ⟨K.sup K', fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 (fc_large_of_sup hL).1
  obtain ⟨b1, hb1⟩ := hK' C hC hC8 (fc_large_of_sup hL).2
  refine ⟨max a1 b1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD (le_trans (le_max_left _ _) hcD)
  obtain ⟨b2, hb2⟩ := hb1 cD (le_trans (le_max_right _ _) hcD)
  refine ⟨max a2 b2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch (le_trans (le_max_left _ _) hch)
  obtain ⟨b3, hb3⟩ := hb2 ch (le_trans (le_max_right _ _) hch)
  exact ⟨max a3 b3, fun X h1 h2 h3 h4 hx hg =>
    ⟨ha3 X h1 h2 h3 h4 (le_trans (le_max_left _ _) hx) hg, hb3 X h1 h2 h3 h4 (le_trans (le_max_right _ _) hx) hg⟩⟩

theorem evG_mono {p q : Ctx → Prop} (h : ∀ K, p K → q K) (hp : EvG p) : EvG q := by
  obtain ⟨a, ha, hp⟩ := hp
  refine ⟨a, ha, fun e C8 C5 c6 Cb he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 C5 c6 Cb he hle h52 h8
  refine ⟨K, fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 hL
  refine ⟨a1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD hcD
  refine ⟨a2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch hch
  exact ⟨a3, fun X h1 h2 h3 h4 hx hg => h X (ha3 X h1 h2 h3 h4 hx hg)⟩

theorem overRows_and_mono {p q r : RowP} (hp : OverRows p) (hq : OverRows q)
    (h : ∀ K B f T w Z Wt hX z p0 Y, p K B f T w Z Wt hX z p0 Y → q K B f T w Z Wt hX z p0 Y → r K B f T w Z Wt hX z p0 Y) :
    OverRows r := by
  unfold OverRows EvLgG at *
  refine evG_mono (fun K hK => ?_) (evG_and hp hq)
  refine large₂.mono (fun B f T _ hpq hKP w hw Z Wt hX z p0 Y h1 h2 h3 h4 h5 => ?_) (large₂.and hK.1 hK.2)
  exact h _ _ _ _ _ _ _ _ _ _ _ (hpq.1 hKP w hw Z Wt hX z p0 Y h1 h2 h3 h4 h5) (hpq.2 hKP w hw Z Wt hX z p0 Y h1 h2 h3 h4 h5)

end GlobalTheory.LiftRef

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.PlaceRead

variable {D : D7}

abbrev Amb (D : D7) (j : Fin D.R.m) : Type := Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank

section Choice

variable (c : NChoice D) (w : D.what₂.places.Pl)

abbrev KE : Type := FractionRing (c.Oe w)

abbrev chr : G D.host.E D.nd.Om →* (D.ntw.Ok (c.twI w) (c.k' w))ˣ := (c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w))

variable {c w}

def viaOk (ι : KE c w →+* ℂ) : D.ntw.Ok (c.twI w) (c.k' w) →+* ℂ := ι.comp (algebraMap _ _)

def ringOf (ι : KE c w →+* ℂ) : Subring ℂ := (ι.comp (algebraMap (c.Oe w) _)).range

def twVia (ρ : Setup D.ntw) (ι : KE c w →+* ℂ) : Twist D Circle :=
  twistOf ρ.rc (viaOk ι) (ρ.ch (c.twI w)) (c.Q w) (chr c w)

def Extends (ρ : Setup D.ntw) (ε : KE c w →+* ℂ) : Prop := viaOk ε = ρ.eOk (c.twI w) (c.sd w) (c.k' w)

theorem Extends.twVia_eq {ρ : Setup D.ntw} {ε : KE c w →+* ℂ} (h : Extends ρ ε) :
    twVia ρ ε = ρ.tw (c.twI w) (c.sd w) (c.k' w) (c.Q w) (chr c w) := by
  rw [twVia, h]; rfl

theorem Extends.apply {ρ : Setup D.ntw} {ε : KE c w →+* ℂ} (h : Extends ρ ε) (a : D.ntw.Ok (c.twI w) (c.k' w)) :
    ε (algebraMap _ _ a) = ρ.eOk (c.twI w) (c.sd w) (c.k' w) a := RingHom.congr_fun h a

variable {ρ : Setup D.ntw} {hρ : ρ.Good} {j : Fin D.R.m} {rd : Rd ρ D.nexp (c.twI w) j (c.sd w)}

def rdE (T : CellTie hρ D.nexp rd) {ε : KE c w →+* ℂ} (hε : Extends ρ ε) : Tgt c w (j.1 + 1) →ₛₗ[ε] Amb D j :=
  let φ : Tgt c w (j.1 + 1) →+ Amb D j := TensorProduct.liftAddHom
    { toFun := fun a => (DistribSMul.toAddMonoidHom _ (ε a)).comp (T.rdV (c.k' w) (c.Q w) (chr c w)).toAddMonoidHom
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp [add_mul] }
    fun s a f => by
      change ε (s • a) • T.rdV _ _ _ f = ε a • T.rdV _ _ _ (s • f)
      rw [← algebraMap_smul (FractionRing (D.ntw.Ok (c.twI w) (c.k' w))) s f, LinearMap.map_smulₛₗ, Algebra.smul_def s a, map_mul, hε.apply,
        smul_smul, mul_comm]
      rfl
  { toFun := φ
    map_add' := φ.map_add
    map_smul' := fun s x => by
      induction x using TensorProduct.inductionOn with
      | tmul a f =>
        change ε (s • a) • T.rdV _ _ _ f = ε s • ε a • T.rdV _ _ _ f
        rw [smul_eq_mul, map_mul, mul_smul]
      | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add] }

theorem rdE_tmul (T : CellTie hρ D.nexp rd) {ε : KE c w →+* ℂ} (hε : Extends ρ ε) (a : KE c w) (f) :
    rdE T hε (a ⊗ₜ f) = ε a • T.rdV (c.k' w) (c.Q w) (chr c w) f := rfl


variable (rd) in
def rdF (hρ : ρ.Good) {ε : KE c w →+* ℂ} (hε : Extends ρ ε) :
    KE c w ⊗[D.ntw.O (c.twI w)] D.nexp.Fm (c.twI w) (j.1 + 1) (c.sd w) →ₛₗ[ε] (GA D (Wc D j) → ℂ) :=
  let φ : KE c w ⊗[D.ntw.O (c.twI w)] D.nexp.Fm (c.twI w) (j.1 + 1) (c.sd w) →+ (GA D (Wc D j) → ℂ) := TensorProduct.liftAddHom
    { toFun := fun a => (DistribSMul.toAddMonoidHom _ (ε a)).comp rd.toAddMonoidHom
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp [add_mul] }
    fun s a f => by
      change ε (s • a) • rd f = ε a • rd (s • f)
      rw [rd_smul, Algebra.smul_def s a, map_mul, IsScalarTower.algebraMap_apply _ (D.ntw.Ok (c.twI w) (c.k' w)) (KE c w), hε.apply,
        hρ.ek_e, smul_smul, mul_comm]
  { toFun := φ
    map_add' := φ.map_add
    map_smul' := fun s x => by
      induction x using TensorProduct.inductionOn with
      | tmul a f =>
        change ε (s • a) • rd f = ε s • ε a • rd f
        rw [smul_eq_mul, map_mul, mul_smul]
      | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add] }

theorem rdF_tmul (hρ : ρ.Good) {ε : KE c w →+* ℂ} (hε : Extends ρ ε) (a : KE c w) (f) :
    rdF rd hρ hε (a ⊗ₜ f) = ε a • rd f := rfl

end Choice

def ConjAt {j : Fin D.R.m} (Φ : VsV D j ℂ →ₗ[ℂ] PolF D (Wc D j).rank (Vc D j).rank) (κ : ℂ) (τ : ℂ ≃+* ℂ) (F F' : Amb D j) : Prop :=
  ∀ h, ∃ x x' : VsV D j ℂ, ConjVec j τ x x' ∧ F h = Φ x ∧ F' h = Φ ((τ κ / κ) • x')

def intLL (D : D7) : Subring ℂ := (D.what₂.embLL.comp (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)).range

theorem used_of_tw {w : D.what₂.places.Pl} (h : D.what₂.muAt w ≠ D.what₂.mu0) : Used0 D (D.what₂.muTw w) :=
  Or.inr ⟨w, ((D.what₂.muAt_or w).resolve_left h).symm⟩

section Rows

variable {X : RealSide D} {X0 : BaseLevelRowSide D} (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0)

def formOf {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) : D.what₂.Mt μ (j.1 + 1) →ₗ[ℂ] (X.R.HV j (Y.tupT μ)).H :=
  (LinearEquiv.ofInjective _ (Y.hinj j (Y.tupT μ))).symm.toLinearMap ∘ₗ Submodule.inclusion inf_le_left ∘ₗ
    (Y.IL.jMt μ hμ j).toLinearMap

theorem extV_formOf {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) (x : D.what₂.Mt μ (j.1 + 1)) :
    X.R.toRealDat.extV j (Y.tupT μ) (formOf Y hμ j x) = (Y.IL.jMt μ hμ j x).1 :=
  congrArg Subtype.val ((LinearEquiv.ofInjective _ (Y.hinj j (Y.tupT μ))).apply_symm_apply _)

def fockOf {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ) :
    D.what₂.Mt μ (j.1 + 1) →ₗ[ℂ] Amb D j :=
  (X.R.ioP j (PiTensorProduct.tprod ℂ u)).compLeft _ ∘ₗ (X.R.HV j (Y.tupT μ)).e ∘ₗ formOf Y hμ j

theorem fockOf_apply {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ) (x h) :
    fockOf Y hμ j u x h = X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j (Y.tupT μ)).e (formOf Y hμ j x) h) := rfl


variable (X) in
def IsLow (j : Fin D.R.m) (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ) : Prop :=
  ∀ τ, (u τ : (X.R.MW j (sg0 D X.A3.A)).sm τ) = X.geo.v₀ j (sg0 D X.A3.A) τ

variable {S : NX.RatDat D.ntw} {YS : NX.NExpRealS X.R X.cG S} (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl)
  (j : Fin D.R.m)

abbrev baseOf : Base (Vc D j) (Wc D j) := Z.ρ.B (c.twI w) j (c.sd w)

structure AtPlace : Prop where
  pins : GlobalTheory.Mem.R3.Pins X.R X.F X.cG
  intersectionNumber_baseChange : GlobalTheory.Mem.R3.Holds X.R X.F
  field : FieldOk X
  tw : D.what₂.muAt w ≠ D.what₂.mu0
  ok : TwOK (c.twI w) (c.k' w) (c.Q w) (chr c w)
  cls : ClsQ (D := D) (c.Q w)
  emb : ∀ ε : KE c w →+* ℂ, Extends Z.ρ ε → ∀ x : D.LL0, ε (c.embW w (x : D.what₂.LL)) = embLL0 D x
  val : ∀ σ, ∃ y : D.what₂.LL, c.embW w y = algebraMap _ (KE c w) ((chr c w σ : (D.ntw.Ok (c.twI w) (c.k' w))ˣ) : D.ntw.Ok (c.twI w) (c.k' w))
  U_eq : ∀ g : X.Γ, X.cG (X.R.eG g) ∈ D.nexp.U ↔ g ∈ X.F.P0
  psi_eq : ∀ i b (g : X.F.P0) (h : X.cG (X.R.eG g) ∈ D.nexp.U),
    Z.ρ.e i b (D.nexp.psiU i b ⟨_, h⟩ : (FractionRing (D.ntw.O i))ˣ) = (D.what₂.embLL (X.F.ψ0 g : D.what₂.LLˣ))⁻¹
  ks : (S.A (j.1 + 1)).IsKsForm
  rat : RatRow YS X.geo.v₀ Z.good (c.twI w) j (c.sd w)
  tup : ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
    IsTupOf X.R.toRealDat (baseOf Z c w j) (twVia Z.ρ ι) (Y.tupT (D.what₂.muTw w))

end Rows

end GlobalTheory.PlaceRead

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarisableOfIsLocS
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowSphSmall

open GlobalTheory.CuspRep.ParLaws GlobalTheory.LocLanglands

end GlobalTheory.RowSphSmall

section FormSec
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open Formalism.IndefR.principalLevelFrame Formalism.IndefR.Mult

namespace GlobalTheory.RowSphSmall


set_option maxHeartbeats 1000000 in
theorem exists_form_rowRepR (hH : GlobalTheory.Published.HarishChandraFinite) (hC : GlobalTheory.Published.CuspRapidDecay) (D : D7) (G : Type) [Group G]
    [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (hP : Pins R F cG) (σ : D.what₂.FT) :
    ∃ B : (principalLevelFrame.rowRepR R.θ (Y.eFT σ)).S → (principalLevelFrame.rowRepR R.θ (Y.eFT σ)).S → ℂ,
      (∀ x y z (c : ℂ), B x (y + c • z) = B x y + c * B x z) ∧ (∀ x y, B x y = starRingEnd ℂ (B y x)) ∧
      (∀ x, x ≠ 0 → 0 < (B x x).re) ∧
      ∀ h (x y x' y' : (principalLevelFrame.rowRepR R.θ (Y.eFT σ)).S), (x' : GAf D.host.E D.R.r → ℂ) = NG.rt D.host.E D.R.r h x →
        (y' : GAf D.host.E D.R.r → ℂ) = NG.rt D.host.E D.R.r h y → B x' y' = B x y := by
  obtain ⟨b, hb⟩ := principalLevelFrame.rowRepR_occ R.θ (Y.eFT σ)
  set π := principalLevelFrame.rowRepR R.θ (Y.eFT σ) with hπ
  have hne : isotIn (D := D) (actM Y.PY (R.MY 0)) (Minf R.θ Y.PY (R.MY 0)) (FinTyp.conjT π) ≠ ⊥ := by
    intro h
    apply hb
    unfold isotE isotL
    rw [h, inf_bot_eq]
  have hM := hP.char.base.models
  have hθ : IsInfFam R.θ := hM.inf
  have hSig : (Yc D 0).SigOK := D.sp.Y_sig 0
  have hcc := GlobalTheory.T.unitary_congruence_conj_contains_congruence D.host.E D.R.r
  have hfd : ∀ j, j < D.R.m → (R.νY A3.A.μ0 j).IsHaarMeasure ∧
      IsFundamentalDomain (GQ (Yc D j)) (R.fdY A3.A.μ0 j) (R.νY A3.A.μ0 j) := by
    intro j hj
    by_cases h : j + 1 < D.R.m
    · have := hM.νY A3.A.μ0 j h
      exact ⟨this.1.1, this.2⟩
    · obtain rfl : j = D.R.m - 1 := by omega
      have := hM.νY' A3.A.μ0
      exact ⟨this.1.1, this.2⟩
  obtain ⟨hHaar, hFD⟩ := hfd 0 Y.hm
  have hSA : SchurAll D := fun V _ S θ M J χ μ 𝓕 =>
    (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ μ 𝓕).2
  obtain ⟨hlin, hherm, hpos⟩ := GlobalTheory.FinTypesRows.minf_sesq (M := R.MY 0) (θ := R.θ) (R.νY A3.A.μ0 0)
    (R.fdY A3.A.μ0 0) Y.PY hSA hSig hθ hHaar hFD
  obtain ⟨B', h1, h2, h3, h4⟩ := GlobalTheory.finTyp_invariant_form_of_isotIn D D.R.r _ (actM Y.PY (R.MY 0))
    (Minf R.θ Y.PY (R.MY 0)) (ipM (R.MY 0) (R.νY A3.A.μ0 0) (R.fdY A3.A.μ0 0)) hlin hherm hpos
    (fun h x hx => GlobalTheory.FinTypesRows.minf_stable Y.PY hcc h hx)
    (fun h x hx y hy => GlobalTheory.T.schur_pairing_invariant_under_standard_group D (Yc D 0) _ R.θ (R.MY 0) D.R.r Y.PY (R.νY A3.A.μ0 0) (R.fdY A3.A.μ0 0) hSA hSig hθ
      hHaar hFD h x hx y hy) (FinTyp.conjT π) hne
  exact GlobalTheory.RowLocalRows.form_of_conjT π B' h1 h2 h3 h4

end GlobalTheory.RowSphSmall
end FormSec

namespace GlobalTheory.RowSphSmall

theorem isUnitarisable_of_isLocS {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (π : NG.FinTyp L n)
    (B : π.S → π.S → ℂ) (hlin : ∀ x y z (c : ℂ), B x (y + c • z) = B x y + c * B x z)
    (hherm : ∀ x y, B x y = starRingEnd ℂ (B y x)) (hpos : ∀ x, x ≠ 0 → 0 < (B x x).re)
    (hinv : ∀ h (x y x' y' : π.S), (x' : Formalism.AUTREP.GAf L n → ℂ) = NG.rt L n h x →
      (y' : Formalism.AUTREP.GAf L n → ℂ) = NG.rt L n h y → B x' y' = B x y)
    (s : ReciprocityTheory.Aut.SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))) (hτ : IsLocS π.S s τ) :
    GlobalTheory.SmGL.IsUnitarisable τ.ρ := by
  obtain ⟨i, T, -, -, hTi, hTm, hTe⟩ := hτ
  obtain ⟨e, he1, he2⟩ := GlobalTheory.SplitEmb.exists_hom_trivOutside_loc L n s
  let t : τ.V → π.S := fun v => ⟨T v, hTm v⟩
  have tadd : ∀ v w, t (v + w) = t v + t w := fun v w => Subtype.ext (map_add T v w)
  have tsmul : ∀ (c : ℂ) v, t (c • v) = c • t v := fun c v => Subtype.ext (map_smul T c v)
  have hlin2 : ∀ y z : π.S, ∀ c : ℂ, B (y + c • z) = fun x => B y x + starRingEnd ℂ c * B z x := by
    intro y z c
    funext x
    rw [hherm, hlin, map_add (f := _), map_mul, ← hherm, ← hherm]
  have hadd1 : ∀ y z x : π.S, B (y + z) x = B y x + B z x := by
    intro y z x
    have := congrFun (hlin2 y z 1) x
    simpa using this
  have hsm1 : ∀ (c : ℂ) (z x : π.S), B (c • z) x = starRingEnd ℂ c * B z x := by
    intro c z x
    have h1 := congrFun (hlin2 0 z c) x
    have h0 : B 0 x = 0 := by
      have := hadd1 0 0 x
      simp only [add_zero] at this
      linear_combination -this
    simpa [h0] using h1
  have hadd2 : ∀ x y z : π.S, B x (y + z) = B x y + B x z := by
    intro x y z
    simpa using hlin x y z 1
  have hsm2 : ∀ (c : ℂ) (x z : π.S), B x (c • z) = c * B x z := by
    intro c x z
    have h1 := hlin x 0 z c
    have h0 : B x 0 = 0 := by
      have := hadd2 x 0 0
      simp only [add_zero] at this
      linear_combination -this
    simpa [h0] using h1
  let Bf : τ.V →ₗ[ℂ] τ.V →ₛₗ[starRingEnd ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => B (t w) (t v))
      (fun v v' w => by rw [tadd, hadd2])
      (fun c v w => by rw [tsmul, hsm2]; rfl)
      (fun v w w' => by rw [tadd, hadd1])
      (fun c v w => by rw [tsmul, hsm1]; rfl)
  refine ⟨Bf, ?_, ?_, ?_⟩
  · intro v w
    show B (t v) (t w) = starRingEnd ℂ (B (t w) (t v))
    exact hherm _ _
  · intro v hv
    show 0 < (B (t v) (t v)).re
    apply hpos
    intro h0
    apply hv
    apply hTi
    rw [map_zero]
    exact congrArg Subtype.val h0
  · intro g v w
    show B (t (τ.ρ g w)) (t (τ.ρ g v)) = B (t w) (t v)
    let g' := Matrix.GeneralLinearGroup.map i.symm.toRingHom g
    have hg : Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n (e g')) = g := by
      rw [he2]
      ext a b
      simp [g']
    have hx : ∀ a, T (τ.ρ g a) = NG.rt L n (e g') (T a) := by
      intro a
      rw [← hg]
      exact hTe (e g') (he1 g') a
    exact hinv (e g') (t w) (t v) (t (τ.ρ g w)) (t (τ.ρ g v)) (hx w) (hx v)

end GlobalTheory.RowSphSmall
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParameterLawsEmpty
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParameterLawsEmpty
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.ParLawsBare

open GlobalTheory.RowTie GlobalTheory.NPin Polynomial

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem heckeCharTie_of_side {D : D7} {cf : CharFrame D} (cs : CharSide D cf) :
    GlobalTheory.HeckeSplitRow.HeckeCharTie D.nd D.naut :=
  ⟨fun π => (cs.e1 π).1, fun _ _ h => cs.e1.injective (Subtype.ext h), cs.unr_iff, cs.frob⟩

theorem heckeSplitOne_of_side {D : D7} {cf : CharFrame D} (cs : CharSide D cf) : GlobalTheory.RowCopy.HeckeSplitOne D :=
  fun ν ν' hw => GlobalTheory.HeckeSplitRow.heckeSplitOne_of_tie D.nd D.naut (heckeCharTie_of_side cs) ν ν' hw

theorem cancel_of_tie {D : D7} (T : WDTie D.nd D.naut) :
    ∀ w (a b c : D.naut.LP w), D.naut.lpSum a c = D.naut.lpSum b c → a = b := by
  intro w a b c h
  apply (T.e w).injective
  refine GlobalTheory.WeilDeligne.WD.lpSum_cancel_right _ _ _ _ _ _ _ (T.e w c) ?_
  rw [← T.sum, ← T.sum, h]


open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil in
theorem locG_rankOne_eq_rcAt {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {cf : CharFrame D} (T : WDTie D.nd D.naut)
    (cg : CGTrue hL D T) (cs : CharSide D cf) (π : D.naut.CG 1) (w : PlE D.host)
    (ξ : (w.adicCompletion D.host.E)ˣ →* ℂˣ) (h : IsComp (cs.e1 π).1 w ξ) :
    T.e w (D.naut.locG π w) = rcAt hL D w 1 (GlobalTheory.SplitRead.Irr.ofDet 1 ξ h.1) := by
  haveI := host_isCMField D.host
  set χ' := (CGu.equivChar D.host.E (cg.e 1 π)).1 with hχ'
  set χ := (cs.e1 π).1 with hχ
  have hloc : ∀ v, T.e v (D.naut.locG π v) = GlobalTheory.CuspRep.ParLaws.locPar hL (CG.ofChar χ') (D.nd.plOm.2 v) := fun v => by
    rw [cg.loc, hχ', CGu.ofChar_equivChar]; rfl
  have unr' : ∀ v, D.naut.unr (D.naut.locG π v) ↔ χ'.UnrAt v := fun v => by
    rw [T.unr, hloc v]; exact GlobalTheory.RankOneComp.locPar_ofChar_unr_iff hL χ' _
  have hchar : χ' = χ := by
    rw [← mul_inv_eq_one]
    apply GlobalTheory.HeckeSplitRow.eq_one_of_split D.host
    filter_upwards [D.naut.locG_unr_ae π] with v hv _
    have u1 := (cs.unr_iff π v).1 hv
    have u2 := (unr' v).1 hv
    refine ⟨fun x hx => ?_, ?_⟩
    · change χ'.loc v x * (χ.loc v x)⁻¹ = 1
      rw [u1 x hx, u2 x hx, inv_one, mul_one]
    · have hf := cs.frob π v u1
      have hf' : D.naut.frobEig (D.naut.locG π v) = {(((χ'.val v)⁻¹ : ℂˣ) : ℂ)} := by
        rw [T.frobEig _ _ hv, hloc v]; exact GlobalTheory.RankOneComp.locPar_ofChar_frob hL χ' _ u2
      rw [hf', Multiset.singleton_inj, Units.val_inj, inv_inj] at hf
      rw [HChar.val_mul, HChar.val_inv, hf, mul_inv_cancel]
  have hcomp : IsComp χ w (χ.loc w) := ⟨GlobalTheory.CuspRep.ParLaws.isSmoothChar_loc χ w, fun x => rfl⟩
  obtain ⟨ξ₀, -, huniq, -⟩ := GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary D.host.E χ w
  have hξ : ξ = χ.loc w := (huniq _ h).trans (huniq _ hcomp).symm
  subst hξ
  rw [hloc, GlobalTheory.CuspRep.ParLaws.locPar_ofChar, rcAt]
  rw [hchar]
  rfl


open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil in
theorem rankOneUnitary {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {cf : CharFrame D} (T : WDTie D.nd D.naut)
    (cg : CGTrue hL D T) (cs : CharSide D cf) : RankOneUnitary T := by
  intro π w σ _ α hα
  obtain ⟨ξ, hξ, -, hξu⟩ := GlobalTheory.HeckeComp.main D.host.E (cs.e1 π).1 w
  have he := locG_rankOne_eq_rcAt T cg cs π w ξ hξ
  rw [WDTie.eig, he] at hα
  unfold WD.inePol at hα
  split_ifs at hα with hσ
  · exact GlobalTheory.LocLanglands.IsRec.recUnit (GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 w)) ξ
      (GlobalTheory.SplitRead.Irr.ofDet 1 ξ hξ.1) (hξu (cs.e1 π).2) ⟨Representation.Equiv.refl _⟩ ⟨σ, hσ⟩ α hα
  · simp at hα


open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LocGL in
theorem rankTwo (hAF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hT : GlobalTheory.Published.CohomologicalCsdTempered)
    (hRP : GlobalTheory.Published.RegularAlgebraicPurity) {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (T : WDTie D.nd D.naut)
    (cg : CGTrue hL D T) (a : ℕ) (π : D.naut.CG a) (ha : 2 ≤ a) (hc : D.naut.csd π) (hr : D.naut.ralg π)
    (w : PlE D.host) : D.naut.tempered (D.naut.locG π w) := by
  have := host_isCMField D.host
  have ha1 : 1 ≤ a := by omega
  obtain ⟨π₀, hπ₀⟩ := Quotient.exists_rep (cg.e a π).1
  have hmk : CG.mk π₀ = (cg.e a π).1 := hπ₀
  have hc₀ : π₀.IsCsd := by
    have h1 := (cg.csd a π).1 hc
    rw [CGu.IsCsd, ← hmk] at h1
    exact h1
  have hinf : ∀ τ, D.naut.infG π τ = (CG.mk π₀).infChar τ := fun τ => by
    rw [cg.inf, CGu.infChar, ← hmk]
  have hr₀ : (CG.mk π₀).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    have := (D.naut.ralg_def π).1 hr τ
    rwa [hinf] at this
  have hcoh := (hRP D.host.E a ha1 π₀ hr₀).2
  obtain ⟨σ₀, hσ₀, -⟩ := LocEx.exists_isLocComp hAF D.host.E a π₀ w
  have htG := hT D.host.E a ha π₀ hc₀ hcoh w σ₀ hσ₀
  rw [T.tempered, cg.loc]
  show (GlobalTheory.CuspRep.ParLaws.locPar hL (cg.e a π).1 (D.nd.plOm.2 w)).tempered
  rw [← hmk, GlobalTheory.CuspRep.ParLaws.locPar_mk hL hσ₀ (D.nd.plOm.2 w)]
  exact GlobalTheory.T.tempered_rep_tempered_parameter D.host.E D.nd.Om _ w (D.nd.plOm.2 w) _ (GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 w)) a
    (GlobalTheory.CuspRep.ParLaws.toRep σ₀) htG

theorem tieAut_of_side {D : D7} {cf : CharFrame D} (cs : CharSide D cf) (hE : IsEmpty D.nd.Loc) :
    Formalism.MainNotions.SumRepresentations.At.TieAut D.nd D.naut := by
  have hcsd : IsCSD D.host cf.eta := GlobalTheory.EtaSelfDual.isCSD_of_isEtaT _ _ _ cf.isEta
  have hE1 : (cs.e1 D.naut.etaT).1.HasInfQ (embPsi D.host) (fun _ => (1 / 2 : ℚ)) :=
    ⟨fun _ => 1, fun _ => by norm_num, by rw [cs.etaT]; exact cf.isEta.inf⟩
  have hE' : (cs.e1 D.naut.etaTinv).1.HasInfQ (embPsi D.host) (fun _ => (-(1 / 2) : ℚ)) :=
    ⟨fun _ => -1, fun _ => by norm_num, by rw [cs.etaTinv]; exact GlobalTheory.AutomorphismSplitting.hasInf_inv cf.isEta.inf⟩
  refine ⟨⟨?_, ?_⟩, fun τ => ?_, fun w => ?_, fun i _ => isEmptyElim i⟩
  · rw [cs.csd, cs.etaT]; exact hcsd
  · rw [cs.csd, cs.etaTinv]; exact GlobalTheory.AutomorphismSplitting.isCSD_inv' hcsd
  · obtain ⟨ρ, hρ⟩ := (GlobalTheory.VolRatioCheck.place_bijective D).2 (InfinitePlace.mk τ)
    rcases InfinitePlace.mk_eq_iff.1 hρ with h | h
    · have ht : τ = embPsi D.host (D.eTau ρ) := h.symm
      rw [ht, (cs.infG _ _ hE1 (D.eTau ρ)).1, (cs.infG _ _ hE' (D.eTau ρ)).1]
      refine ⟨Or.inl (by push_cast; rfl), ?_⟩
      rw [Multiset.map_singleton]; push_cast; rfl
    · have ht : τ = (starRingEnd ℂ).comp (embPsi D.host (D.eTau ρ)) := by
        rw [← h]; ext x; rfl
      rw [ht, (cs.infG _ _ hE1 (D.eTau ρ)).2, (cs.infG _ _ hE' (D.eTau ρ)).2]
      refine ⟨Or.inr (by push_cast; rfl), ?_⟩
      rw [Multiset.map_singleton]; push_cast; ring_nf
  · have hu : D.naut.unr (D.naut.locG D.naut.etaT w) := D.naut.etaT_unr w
    rw [D.naut.tempered_unr _ hu, cs.frob _ w ((cs.unr_iff _ w).1 hu)]
    intro α hα
    rw [Multiset.mem_singleton] at hα
    subst hα
    have h1 : ‖(((cs.e1 D.naut.etaT).1.val w : ℂˣ) : ℂ)‖ = 1 := (cs.e1 D.naut.etaT).2 _
    rw [Units.val_inv_eq_inv_val, norm_inv, h1, inv_one]

theorem tieGal_bare {D : D7} (hE : IsEmpty D.nd.Loc) : Formalism.MainNotions.SumRepresentations.At.TieGal D.nd D.naut :=
  ⟨fun i => isEmptyElim i, fun i => isEmptyElim i, fun i => isEmptyElim i, fun i => isEmptyElim i⟩

theorem tieLab_of_lab {D : D7} (T : WDTie D.nd D.naut) (lab : LabTrue D T) : Formalism.MainNotions.SumRepresentations.tieLab D := by
  let γ : Fin 2 → PlE D.host → Formalism.ConjugateSelfDual.G D.host.E D.nd.Om :=
    fun k => Function.extend (D.naut.plGw k) (D.ntypes.tg k) (fun _ => 1)
  have hγ : ∀ k v, γ k (D.naut.plGw k v) = D.ntypes.tg k v := fun k v => (D.naut.plGw_inj k).extend_apply _ _ v
  have hT : GlobalTheory.LabLaws.LabTie T D.ntypes.teichC γ := by
    intro k v
    rw [hγ k v]
    exact ⟨D.ntypes.teichC_inj k, D.ntypes.tg_gen k v, lab k v⟩
  exact GlobalTheory.LabLaws.tieLab_of_labTie hT

theorem main : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, ∀ (D : D7) (cf : CharFrame D) rep Rw,
    IsEmpty D.nd.Loc → ParIn hL D cf rep Rw → ParLaws D := by
  intro hP hL D cf rep Rw hE X
  have hrig : IsobaricRigid D.nd D.naut := by
    have := GlobalTheory.CuspRep.host_isCMField D.host
    exact GlobalTheory.RowPar.isobaricRigid_of_jacquetShalika hP.what₂.js.1 (GlobalTheory.HeightCounting.Blocks.readsCusp hP.what₂.fin X.cg)
  have han1 := GlobalTheory.RowClose.isobaricCuspidalMultiplicityOne_of_twisted _ _ _ D.nd D.naut hrig
  have han2 := GlobalTheory.SpehRigid.isobaricDiscreteSelfDualMultOne_of_isobaricSumMultOne _ _ _ D.nd D.naut hrig
  have hcheb := GlobalTheory.ChebSplitDense.chebSplit_nd hP.what₂.cheb D
  have ha5 : Formalism.MainNotions.SumRepresentations.adm5 D := (Formalism.MainNotions.SumRepresentations.condition_iff_additive_maps D).2 ⟨han1, han2, fun Sg hSg => by
    have hd := (hcheb hSg.toFinset).closure_eq
    convert hd using 4 with σ
    simp [Set.Finite.mem_toFinset]⟩
  have htie0 : Formalism.MainNotions.SumRepresentations.tie0 D :=
    ⟨GlobalTheory.RowTieLP.main D X.T, tieAut_of_side X.chr hE, tieGal_bare hE⟩
  have ha7 : Formalism.MainNotions.SumRepresentations.adm7 D :=
    GlobalTheory.RowTie.admissible_of_rank_one_unitary D X.T (rankOneUnitary X.T X.cg X.chr)
      (fun a π ha hc hr w => rankTwo hP.what₂.fin hP.what₂.temp hP.what₂.clo X.T X.cg a π ha hc hr w)
  exact ⟨htie0, ha5, ha7, tieLab_of_lab X.T X.lab, heckeSplitOne_of_side X.chr, cancel_of_tie X.T,
    fun k v => GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v⟩

end GlobalTheory.ParLawsBare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParameterLawsEmptyStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parameter_laws_empty : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, ∀ (D : D7) (cf : CharFrame D) rep Rw, IsEmpty D.nd.Loc → ParIn hL D cf rep Rw → ParLaws D := by
  first | exact @GlobalTheory.ParLawsBare.main | exact GlobalTheory.ParLawsBare.main | (intros; apply GlobalTheory.ParLawsBare.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraCentreKeepsTypeSpacesAtLocalisations
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RtMemIsoTyp
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CenKeepsType

theorem rt_mem_isoTyp {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)) (h : GAf L n)
    (f : GAf L n → W) (hf : f ∈ NG.isoTyp ρ S) : NG.rt L n h f ∈ NG.isoTyp ρ S := by
  have hle : NG.isoTyp ρ S ≤ (NG.isoTyp ρ S).comap (NG.rt L n h) := by
    refine sSup_le fun U hU => ?_
    intro a ha
    have hU' : U ≤ NG.isoTyp ρ S := le_sSup hU
    exact hU' (hU.1.1.stable h a ha)
  exact hle hf

end GlobalTheory.CenKeepsType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraCentreKeepsTypeSpacesAtLocalisations
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CenKeepsTypeLoc

theorem main : ∀ (D : D7) (M : MtFam D), AVTied D M → GlobalTheory.HeightCounting.Up.CenLoc D M → OnMtPreservesTypeV D := by
  intro D M A hC i PI z F hF
  by_cases hz : z ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))
  · obtain ⟨L, -, hL⟩ := hC i
    rw [NTypes.onMt, dite_eq_left hz]
    rw [A.typeV, Submodule.mem_comap] at hF ⊢
    have e : (M.loc i).real (D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) ⟨z, hz⟩ F) =
        actSum D L z ((M.loc i).real F) := hL ⟨z, hz⟩ F
    rw [e]
    unfold actSum Finsupp.sum
    exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (GlobalTheory.CenKeepsType.rt_mem_isoTyp _ _ _ _ hF)
  · rw [NTypes.onMt, dite_eq_right hz]
    exact Submodule.zero_mem _

end GlobalTheory.CenKeepsTypeLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraCentreKeepsTypeSpacesAtLocalisationsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupAlgebraCentre_keeps_typeSpaces_at_localisations : ∀ (D : D7) (M : MtFam D), AVTied D M → GlobalTheory.HeightCounting.Up.CenLoc D M → OnMtPreservesTypeV D := by
  first | exact @GlobalTheory.CenKeepsTypeLoc.main | exact GlobalTheory.CenKeepsTypeLoc.main | (intros; apply GlobalTheory.CenKeepsTypeLoc.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSphericalOfHypOutside
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SphHyp

theorem isSpherical_of_hypOutside : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (J : Subgroup (GAf L n)) (χ : J →* ℂˣ), (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → ∀ (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))), NG.HypOutside J χ B → ∀ f ∈ NG.isoTyp a.ρ S, f ∈ NG.TypeSp a.ρ J χ → f ≠ 0 → ∀ (s : SplitPlace L), s.v ∉ B → ∀ (σ : IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → IsSpherical (GlobalTheory.LocLanglands.cls σ).rep := by
  intro L _ _ _ n a S hS J χ hlev B hB f hfiso hfT hf0 s hsB σ hσ
  classical
  obtain ⟨i, T₀, hi, hic, -, -, -⟩ := id hσ
  have hrt : ∀ κ, TrivOutside {s.v} κ → ∀ h : s.loc n κ ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring,
      NG.rt L n κ f = (((1 : (Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) →* ℂˣ) ⟨s.loc n κ, h⟩ : ℂˣ) : ℂ) • f := by
    intro κ hκ h
    have hU := (GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s hκ).1 h
    have hκB : TrivOutside Bᶜ κ := fun w hw => hκ w (by
      intro hm
      rw [Set.mem_singleton_iff] at hm
      rw [hm] at hw
      exact hsB (by simpa using hw))
    obtain ⟨hJ, hχ⟩ := hB κ hκB
    have hκJ := hJ.2 hU
    rw [hfT.2 ⟨κ, hκJ⟩, hχ hκJ]
    simp
  obtain ⟨u, hu0, hu⟩ := GlobalTheory.LocVec.main L n a S hS s σ hσ i hi hic
    (Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) 1 (fun g hg => hg)
    (by simp) f hfiso hf0 hrt
  have key : ∀ y, i y ∈ Formalism.UG.Ov L s.w → Valued.v y ≤ 1 := fun y hy =>
    (GlobalTheory.CuspRep.ParLaws.valuation_le_one_iff s.v y).1 (GlobalTheory.SphLoc.le_one_of_map i.toRingHom hi
      ((GlobalTheory.CuspRep.ParLaws.valuation_le_one_iff s.w _).2 hy))
  have hfix : ∀ g ∈ KO (s.w.adicCompletion L) (Fin n), σ.ρ g u = u := by
    intro g hg
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion s.w n, GlobalTheory.HeckeScalarSph.mem_GLint_iff] at hg
    let g' := Matrix.GeneralLinearGroup.map i.symm.toRingHom g
    have hg' : g' ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := by
      rw [GlobalTheory.HeckeScalarSph.mem_GLint_iff]
      refine ⟨fun p q => ?_, fun p q => ?_⟩
      · show Valued.v (i.symm (g.1 p q)) ≤ 1
        exact key _ (by rw [RingEquiv.apply_symm_apply]; exact hg.1 p q)
      · rw [← map_inv]
        show Valued.v (i.symm ((g⁻¹).1 p q)) ≤ 1
        exact key _ (by rw [RingEquiv.apply_symm_apply]; exact hg.2 p q)
    have e : Matrix.GeneralLinearGroup.map i.toRingHom g' = g :=
      Units.ext (Matrix.ext fun p q => i.apply_symm_apply _)
    have := hu g' hg'
    rw [e] at this
    simpa using this
  have hsph : IsSpherical σ.ρ := by
    intro h
    apply hu0
    have hm : u ∈ fixed σ.ρ (KO (s.w.adicCompletion L) (Fin n)) := fun g => by
      simpa using hfix g.1 g.2
    rw [h] at hm
    exact hm
  exact GlobalTheory.BCOffT.isSpherical_of_equiv (equivRep σ) hsph
end GlobalTheory.SphHyp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivialPartInBaseChange
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.MuBlockLoc

theorem placesOver_finite (D : D7) (k : Fin 2) : (placesOver D.host.E (D.host.g k)).Finite := by
  have hne : Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (D.host.g_prime k).ne_zero
  refine (Ideal.finite_factors hne).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.mpr hv

theorem mem_isoInf (D : D7) (Pa : List (Part D.naut.CG)) (p : Part D.naut.CG) (hp : p ∈ Pa) (hd : 1 ≤ p.d)
    (τ : D.host.E →+* ℂ) :
    (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - (0 : ℂ))) ≤ isoInf D.nd D.naut Pa τ := by
  unfold isoInf
  refine le_trans ?_ (List.single_le_sum (by intro x _; exact Multiset.zero_le x) _ (List.mem_map.2 ⟨p, hp, rfl⟩))
  refine List.single_le_sum (by intro x _; exact Multiset.zero_le x) _ (List.mem_map.2 ⟨(0 : ℂ), ?_, rfl⟩)
  simp
  exact ⟨0, hd, by simp⟩

theorem mu_ralg (D : D7) (Rw : RowSide D) (j : ℕ) (σ : D.what₂.FT) (π : D.nbc.AU j) (μ : D.naut.CG 1)
    (hA : LiftAt D Rw j σ π μ) : D.naut.ralg μ := by
  obtain ⟨a, ha⟩ := GlobalTheory.LocalInv.r_odd D.R
  have hnV : (D.R.nV : ℂ) = 2 * (a : ℂ) + 1 + D.R.t := by
    show ((D.R.r + D.R.t : ℕ) : ℂ) = _
    rw [ha]; push_cast; ring
  have ht1 : 1 ≤ D.R.t := D.R.t_odd.pos
  have hq : ∀ (τ : D.host.E →+* ℂ) (s : ℂ), D.naut.infG D.naut.etaTinv τ = {s} →
      (∀ x ∈ isoInf D.nd D.naut [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] τ, ∃ k : ℤ, x = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2) →
      ∀ z ∈ D.naut.infG μ τ, ∃ k : ℤ, z + s + ((D.R.t : ℂ) - 1) / 2 = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := by
    intro τ s hs hx z hz
    have hle := mem_isoInf D [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] ⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩
      (List.mem_singleton_self _) ht1 τ
    dsimp only at hle
    rw [D.naut.infG_tw _ _ τ s hs, Multiset.map_map] at hle
    obtain ⟨k, hk⟩ := hx _ (Multiset.mem_of_le hle (Multiset.mem_map_of_mem _ hz))
    exact ⟨k, by rw [← hk]; simp⟩
  refine (D.naut.ralg_def _).2 fun φ => ?_
  obtain ⟨z0, hz0⟩ := Multiset.card_eq_one.mp (D.naut.infG_card μ φ)
  refine ⟨by rw [hz0]; exact Multiset.nodup_singleton z0, fun z hz => ?_⟩
  obtain ⟨τ, hτ | hτ⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.emb_cases D φ
  · have e : φ = GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ := hτ
    subst e
    have hx : ∀ x ∈ isoInf D.nd D.naut [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ),
        ∃ k : ℤ, x = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := fun x hx =>
      (D.nbc.infW_alg j (D.nbc.wtAU j π) _).2 x (by rw [(hA.inf τ).1]; exact Multiset.mem_add.2 (Or.inr hx))
    obtain ⟨k, hk⟩ := hq _ _ (hA.eta τ).1 hx z hz
    refine ⟨k + a + 1, ?_⟩
    rw [hnV] at hk
    push_cast
    linear_combination hk
  · have e : φ = GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ := hτ
    subst e
    have hx : ∀ x ∈ isoInf D.nd D.naut [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ),
        ∃ k : ℤ, x = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := fun x hx =>
      (D.nbc.infW_alg j (D.nbc.wtAU j π) _).2 x (by rw [(hA.inf τ).2]; exact Multiset.mem_add.2 (Or.inr hx))
    obtain ⟨k, hk⟩ := hq _ _ (hA.eta τ).2 hx z hz
    refine ⟨k + a, ?_⟩
    rw [hnV] at hk
    push_cast
    linear_combination hk

end GlobalTheory.MuBlockLoc

namespace GlobalTheory.MuBlockLoc

end GlobalTheory.MuBlockLoc
end
end
