module

public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
public import Formalism.LocalToGlobal.IndefiniteReal.RecTie
public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedRowLoc

@[expose] public section

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct nonZeroDivisors

namespace Formalism.IndefR.FWT

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.Datum Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Space

abbrev fin (V : HSp D) (h : GA D V) : Bridge.Gf V := (finHom V).rangeRestrict h

def SplitOffBad (V : HSp D) (bad : ℕ) (h : GA D V) : Prop :=
  h ∈ GfC V ∧ ∃ (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P ∧ (∀ PP ∈ P, ((bad : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) ∧ SuppAt e V h

def uMat (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D)
    (X : Fin S.rank → Fin T.rank → D.host.E) : Matrix (Fin S.rank) (Fin T.rank) (EAf D) :=
  fun b a => toEAf D e * HMul.hMul (HMul.hMul (βS⁻¹).val
    ((HMul.hMul (HMul.hMul S.gram⁻¹ (Matrix.of fun b a => D.sp.cm.sig (X b a))) T.gram).map (eToEAf D))) βT.val b a

end Space

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
  {K' : Type} [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ)


variable (D) in
abbrev lamV : D.what₂.Tau → DomWeight (Vc D i).rank := fun τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ


variable (D) in
abbrev VsV (K : Type) [Field K] : Type := ↥(VV K (lamV D i))


variable (D) in
def embV (τ : D.what₂.Tau) : D.host.E →+* K' := jL.comp (labLL D τ)

theorem embV_spec (h : σ'.comp jL = D.what₂.embLL) (τ : D.what₂.Tau) : σ'.comp (embV D jL τ) = tauE D τ := by
  ext x
  have h1 := RingHom.congr_fun D.embE_φ₀ ((D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E) x)
  have h2 := RingHom.congr_fun h (labLL D τ x)
  exact h2.trans h1

theorem embV_eq_embF {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (j : D.what₂.LL →+* c.F) (h : c.F.val.toRingHom.comp j = D.what₂.embLL) (τ : D.what₂.Tau) :
    embV D j τ = embF c (tauE D τ) := by
  ext x
  exact RingHom.congr_fun (embV_spec j c.F.val.toRingHom h τ) x

abbrev levJ (t : T0) : Subgroup (Bridge.Gf (Vc D i)) := (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J


variable (D) in
def VStd : Prop :=
  (Vc D i).gram = 1 ∧ Bridge.hLat (Vc D i) 1 = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E)

section Tuple

variable (t : T0) {Cl : Type} [Fintype Cl] (h : Cl → GA D (Vc D i))

def RepsR (bad : ℕ) (J' : Subgroup (Bridge.Gf (Vc D i)))
    (Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)) (gam : Cl → ℕ) (vol : K') : Prop :=
  bad ≠ 0 ∧ (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧
    J' ≤ levJ R i t ∧ J'.relIndex (levJ R i t) ≠ 0 ∧ vol = ((J'.relIndex (levJ R i t) : ℕ) : K')⁻¹ ∧
    Bridge.IsReps (Bridge.ratF (Vc D i)) J' (fun k => fin _ (h k)) ∧
    ∀ k, SplitOffBad (Vc D i) bad (h k) ∧ Lh k = Bridge.hLat (Vc D i) (fin _ (h k)) ∧
      gam k = Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) J' (fin _ (h k)))

def CoefficientBaseChange (c0 : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W) (c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W) : Prop :=
  ∀ v : VsV D i D.what₂.LL, ∃ v' : VsV D i K',
    (v' : Pol K' D.what₂.Tau (Vc D i).rank) = MvPolynomial.map jL (v : Pol D.what₂.LL D.what₂.Tau (Vc D i).rank) ∧ c0' v' = c0 v

variable {σ'} (c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W)

def Place (y : (R.HV i t).H) (x : Cl → VsV D i K') : Prop := ∀ k, (R.HV i t).e y (fin _ (h k)) = c0' (x k)

def jVx (x₀ : A.fam.amb.FL i t) : (R.HV i t).H := R.jV i t x₀

def PlaceEx : Prop := ∀ x₀ : A.fam.amb.FL i t, ∃ x, Place R i t h c0' (jVx R i t x₀) x

def ThAdIs (v₀ : (R.MW i (sg0 D A)).Vec) (thAd : (Cl → VsV D i K') → AutQ (Wc D i) → ℂ) : Prop :=
  ∀ y x, Place R i t h c0' y x → thAd x = onQ (Wc D i) (R.thF i t y v₀)

variable (σ')

def BIs (bad : ℕ) (B : Ideal (𝓞 D.host.E) → K') : Prop :=
  ∀ cc : Ideal (𝓞 D.host.E), cc ≠ ⊥ → cc ⊔ Ideal.span {((bad : ℕ) : 𝓞 D.host.E)} = ⊤ →
    σ' (B cc) = (((R.C.mu0 i * R.xiH t * R.C.eta⁻¹).onId (cc : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : ℂˣ) : ℂ) *
      ((Real.sqrt (Ideal.absNorm cc : ℝ) : ℝ) : ℂ)

def XiIs (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) : Prop :=
  ∀ (g : GA D (Wc D i)) (x : (AE D)ˣ), IsDetRoot (Wc D i) g x →
    ((xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g)) : ℂˣ) : ℂ) = ((R.xi t x : Circle) : ℂ)

variable {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E))


open Classical in
def PhiIs (N : Submodule (𝓞 D.host.E) La) (φ : (Fin (Vc D i).rank → La ⧸ N) → K') : Prop :=
  ∃ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) ∧ ∀ x : Fin (Vc D i).rank → La,
    IsIntM (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (x b)) ∧
    σ' (φ fun b => Submodule.Quotient.mk (x b)) =
      omegaK R.Pg (fun PP => redM PP (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (x b))) *
        omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1)
          (fun PP => redM PP (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (x b)))

def HalfIs (Mb I : Ideal (𝓞 D.host.E)) : Prop :=
  Mb = ∏ PP ∈ R.Pg, PP.asIdeal ∧ (∀ PP ∈ R.Q t, I ≤ PP.asIdeal) ∧
    ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal

end Tuple

def LevIs {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E))
    (M : ℕ) (Mh : Ideal (𝓞 D.host.E)) (lev : G → La →ₗ[𝓞 D.host.E] La) : Prop :=
  ∀ g, ∃ κ, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ ∧
    ∀ a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat (Wc D i) 1,
      finVec (Wc D i) (ι (lev g a)) - (finHom (Wc D i) κ).1.mulVec (finVec (Wc D i) (ι a)) = M • w

def ActRho {Rl : Type} [AddCommGroup Rl] [Module Ks Rl] (C : Submodule Ks Rl) (e : C ≃ₗ[Ks] (R.FW i).WK)
    (act : G → Rl →ₗ[Ks] Rl) : Prop :=
  ∀ g (f : C), ∃ hf : act g f ∈ C,
    ((e ⟨act g f, hf⟩ : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) = (R.FW i).ρ g ((e f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL)

def ChiAt (σ : D.what₂.LL →+* ℂ) (χ : (AE D)ˣ →* Circle) : Prop :=
  IsHeckeChar D χ ∧ (∀ a, χ (idF D a) = 1) ∧ (∀ ρ, HasInfExp D χ ρ (-(D.hc (lab σ ρ)).e i)) ∧
    (∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∃ y : Ks, ((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = D.what₂.embLL (algebraMap Ks D.what₂.LL y) ∧
      ((χ x : Circle) : ℂ) = σ (algebraMap Ks D.what₂.LL y)) ∧
    (σ.comp (algebraMap Ks D.what₂.LL) = D.what₂.embLL.comp (algebraMap Ks D.what₂.LL) → χ = R.mu0 ((i : ℕ) + 1))

structure ThPinsT (t : T0) (v₀ : (R.MW i (sg0 D A)).Vec) (c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W)
    {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E))
    (bad : ℕ) (Mb I : Ideal (𝓞 D.host.E)) (N : Submodule (𝓞 D.host.E) La) {Cl : Type} [Fintype Cl]
    (Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)) (gam : Cl → ℕ) (vol : K')
    (B : Ideal (𝓞 D.host.E) → K') (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)
    (φ : (Fin (Vc D i).rank → La ⧸ N) → K') (thAd : (Cl → VsV D i K') → AutQ (Wc D i) → ℂ)
    (Plc : (Cl → VsV D i K') → Prop) : Prop where

  reps : ∃ (h : Cl → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))), RepsR R i t h bad J' Lh gam vol ∧
    PlaceEx R i t h c0' ∧ ThAdIs R i t h c0' v₀ thAd ∧ ∀ x, Plc x ↔ ∃ x₀, Place R i t h c0' (jVx R i t x₀) x
  B : BIs R i σ' t bad B
  xi : XiIs R i t xi
  phi : PhiIs R i σ' t ι N φ
  half : HalfIs R t Mb I

structure ThPinsR (v₀ : (R.MW i (sg0 D A)).Vec) (c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W)
    {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E))
    (M : ℕ) (Mh : Ideal (𝓞 D.host.E)) (lev : G → La →ₗ[𝓞 D.host.E] La) : Prop where
  field : σ'.comp jL = D.what₂.embLL
  std : VStd D i
  v0 : IsChosenExtremalVector R i (sg0 D A) v₀
  c0 : ∃ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
    (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L ∧ CoefficientBaseChange R i jL σ' (c0L i) c0'
  lev : LevIs R i ι M Mh lev

theorem ext_fin {V : HSp D} (c : CoefA V) (hc : c.Is) (f : Bridge.Gf V → c.W) {h : GA D V} (hh : h ∈ GfC V) :
    c.ext f h = f (fin V h) := by
  show c.ρ h⁻¹ (f (fin V h)) = _
  rw [hc.1 _ (inv_mem hh)]
  rfl

def MuR {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    (T : Core D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) : Prop :=
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) →
    ∃ χ, ChiAt R i σ χ ∧ MuVal (T.V ((i : ℕ) + 1) (σ.comp (algebraMap T.Q.c.F D.what₂.LL))) χ
      (T.mu ((i : ℕ) + 1) (σ.comp (algebraMap T.Q.c.F D.what₂.LL)))

def ChiR {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) : Prop :=
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) →
    ChiAt R i σ (T.chiW ((i : ℕ) + 1) (σ.comp (algebraMap T.Q.c.F D.what₂.LL)))

end Formalism.IndefR.FWT
end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.IsMultMapUnivZero
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped TensorProduct InnerProductSpace
open IsDedekindDomain NumberField MeasureTheory

namespace Formalism.IndefR.RecTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Zero

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : Datum.InfFam D) (M : Mult.DSModel V S)

end Zero

section FromLinks

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def TopMultH (R : RealDat D A Ks) : Prop :=
  ∀ t, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) =
    Mult.MultT R.θ R.MX (levS _ R.βX (R.datXt t)) (levChi _ R.βX (R.datXt t))

def datXP (R : RealDat D A Ks) (t : T) (P : Formalism.L2.DIV.LevelP R.Pg D.R.r ℂ) : Formalism.L2.DIV.LevDat D.host.E ℂ D.sp.X'.rank :=
  datY _ D.R.r D.R.t D.R.m r_le_X R.Pg (R.Q t) P R.chi (R.xiR t) Frm.B


open Classical in
def SsetF (R : RealDat D A Ks) (t : T) : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  (R.Sb ∪ R.Q t).image (Formalism.L2.DIV.underPl D.host.F)

def toChainReal (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R) :
    ChainReal D where
  θ := R.θ
  ψ := R.ψ
  η := R.eta
  Ptw := Ptw D
  Y := Yc D
  SY j := Mult.parB (Ptw D) (min j D.R.m)
  MY := R.MY
  X := D.sp.X'
  MX := R.MX
  J _ μ j := if j < D.R.m then levS _ (R.βY j) (R.datYt (tupT μ) j R.triv) else Set.univ
  χ _ μ j := if j < D.R.m then levChi _ (R.βY j) (R.datYt (tupT μ) j R.triv) else 0
  JX _ μ := levS _ R.βX (R.datXt (tupT μ))
  χX _ μ := levChi _ R.βX (R.datXt (tupT μ))
  meas _ μ j := R.νY (tupT μ) j
  fd μ j := R.fdY (tupT μ) j
  measX _ μ := R.νX (tupT μ)
  fdX μ := R.fdX (tupT μ)
  measE b := ENNReal.ofReal (RealDat.nP F b)⁻¹ • R.ν0
  fdE := R.fd0
  chr μ := R.toLevCh.mu (tupT μ)
  Sinf k := PolF D (Yc D (k + 1)).rank (Yc D k).rank
  pt _ μ k := R.ptY (tupT μ) k
  It := R.ItY
  th μ k := thetaKO (R.ωY (tupT μ) k)
  ioC _ μ k := if h : k + 1 < D.R.m then
      (LinearEquiv.ofEq _ _ (by simp only [if_pos (show k < D.R.m by omega)])).toLinearMap ∘ₗ
        R.ioY (tupT μ) k ∘ₗ (LinearEquiv.ofEq _ _ (by simp only [if_pos h])).toLinearMap
    else 0
  SinfX := PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank
  ptX _ μ := R.ptX (tupT μ)
  ItX := R.ItX
  thX μ := thetaKO (R.ωX (tupT μ))
  ioX _ μ := (LinearEquiv.ofEq _ _ (by simp only [if_pos (show D.R.m - 1 < D.R.m by omega)])).toLinearMap ∘ₗ
    R.ioX (tupT μ) ∘ₗ (LinearEquiv.ofEq _ _ (hTop (tupT μ)).symm).toLinearMap
  JE b := levS _ (R.βY 0) (R.dat0 (R.levR F b))
  χE b := levChi _ (R.βY 0) (R.dat0 (R.levR F b))
  eE _ := R.e0
  Sb := SsetF R (tupT D.what₂.mu0)
  volTop := 1
  JP b μ j := if j < D.R.m then levS _ (R.βY j) (R.datYt (tupT μ) j (R.levR F b)) else Set.univ
  χP b μ j := if j < D.R.m then levChi _ (R.βY j) (R.datYt (tupT μ) j (R.levR F b)) else 0
  JXP b μ := levS _ R.βX (datXP R (tupT μ) (R.levR F b))
  χXP b μ := levChi _ R.βX (datXP R (tupT μ) (R.levR F b))
  nrm b := (RealDat.nP F b)⁻¹

def levSubV (V : HSp D) (W : Type) [AddCommGroup W] [Module ℂ W] (J : Set (GA D V)) (χ : GA D V → ℂ) :
    Submodule ℂ (GA D V → W) where
  carrier := {F | ∀ k ∈ J, ∀ g, F (g * k) = χ k • F g}
  add_mem' {F F'} hF hF' k hk g := by simp only [Pi.add_apply, hF k hk g, hF' k hk g, smul_add]
  zero_mem' k _ g := by simp
  smul_mem' c F hF k hk g := by simp only [Pi.smul_apply, hF k hk g, smul_comm c (χ k)]

def datVP (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (P : Formalism.L2.DIV.LevelP R.Pg D.R.r ℂ) :
    Formalism.L2.DIV.LevDat D.host.E ℂ (Vc D i).rank :=
  datY _ D.R.r D.R.t 1 (r_le_V i) R.Pg (R.Q t) P (fun _ => R.chi ((i : ℕ) + 1)) (R.xiR t) Frm.A

def ipVia {H N : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [AddCommGroup N] [Module ℂ N] (e : H →ₗ[ℂ] N)
    (x y : N) : ℂ := by
  classical
  exact if h : x ∈ LinearMap.range e ∧ y ∈ LinearMap.range e then ⟪h.1.choose, h.2.choose⟫_ℂ else 0

def toLiftReal (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R)
    (hinj : ∀ i t, Function.Injective (R.extV i t)) :
    LiftReal D (toChainReal R F tupT hm hTop) where
  V := Vc D
  W := Wc D
  κ i := kapAt (Wc D i) (sg0 D A)
  SW i := parAt (Wc D i) (sg0 D A)
  MW i := R.MW i (sg0 D A)
  JW i := levS _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))
  χW i := levChi _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))
  eW i := R.eWf i (sg0 D A)
  JA i := levS _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))
  χA i := levChi _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))
  measW i := ENNReal.ofReal (RealDat.nP F false)⁻¹ • R.νW i
  fdW i := R.fdW i
  SbW := SsetF R (tupT D.what₂.mu0)
  TauV i := (R.cV i).W
  Amt μ i := LinearMap.range (R.extV i (tupT μ)) ⊓
    levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (datVP R i (tupT μ) (R.levR F false)))
      (levChi _ (R.βV i) (datVP R i (tupT μ) (R.levR F false)))
  ipA μ i := fun x y => (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * ipVia (R.extV i (tupT μ)) x y
  measV μ i := R.νV i (tupT μ)
  fdV μ i := R.fdV i (tupT μ)
  TK i := LowT (R.MW i (sg0 D A))
  embK i := PiTensorProduct.map fun τ => (lowT (R.MW i (sg0 D A)) τ).subtype
  Sinf' i := PolF D (Wc D i).rank (Vc D i).rank
  ioK i := R.ioP i
  ptW μ i := R.ptP i (tupT μ)
  thW μ i := fun g h f => thetaKO (R.ωP i (tupT μ)) h g f
  thC μ i := LinearMap.lcomp ℂ (GA D (Wc D i) → ℂ) (PiTensorProduct.map fun τ => (lowT (R.MW i (sg0 D A)) τ).subtype) ∘ₗ
    (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A)) ≃ₗ[ℂ] _).toLinearMap ∘ₗ R.thF i (tupT μ) ∘ₗ
    (LinearEquiv.ofInjective _ (hinj i (tupT μ))).symm.toLinearMap ∘ₗ Submodule.inclusion inf_le_left

structure RecReal (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t))
    (X0 : BaseLevelRowSide D) (Ish : RowIds (RowSide.sharp D) (toChainReal R F tupT hm hTop) true)
    (I0 : RowIds X0.s (toChainReal R F tupT hm hTop) false)
    (IL : LiftIds (toLiftReal R F tupT hm hTop hinj)) (K : ColReal D) {Xd : DivX D} (E : EigIdx D Xd)
    (labPi : E.Pi → A.fam.base.Ix) {n : ℕ} (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) n)
    (eFT : D.what₂.FT ≃ principalLevelFrame.FTR R.θ PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.levR F b)))
      (fun b => levChi _ (R.βY 0) (R.dat0 (R.levR F b))) (fun _ => R.e0))
    (piOf : E.Pi → HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) (ι : ∀ i, ↥(GfC (Yc D 0)) →* ↥(GfC (Wc D i))) (nch : NChoice D)
    (Tp : Formalism.L2.Host.TupTied D R.C nch) : Prop where

  base : R.BaseW F

  tied : RecTied D X0 (toChainReal R F tupT hm hTop) Ish I0 (toLiftReal R F tupT hm hTop hinj) IL K

  prtE : ∀ π, Ish.prt π = (principalLevelFrame.isotE R.θ PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F true)))
    (levChi _ (R.βY 0) (R.dat0 (R.levR F true))) R.e0 (principalLevelFrame.rowRepR R.θ (eFT π))).map
      (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap

  prtE0 : ∀ π, I0.prt π = (principalLevelFrame.isotE R.θ PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F false)))
    (levChi _ (R.βY 0) (R.dat0 (R.levR F false))) R.e0 (principalLevelFrame.rowRepR R.θ (eFT π))).map
      (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap

  prtWE : ∀ i π, IL.prtW i π = (principalLevelFrame.isotL R.θ (PW i) (R.MW i (sg0 D A))
    (levS _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A))))
    (R.eWf i (sg0 D A)) (principalLevelFrame.rowRepR R.θ (eFT π))).map (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A)) ≃ₗ[ℂ] _).toLinearMap

  xi : ∀ μ, Used0 D μ → K.xi μ = R.toLevCh.xi (tupT μ)

  tupXi : ∀ μ, Used0 D μ → R.toLevCh.xiH (tupT μ) = Tp.xi μ

  tupAt : ∀ w, tupT (D.what₂.muAt w) = R.mu (D.plEq w)

  isomFin : ∀ i, principalLevelFrame.IsIsomFin (ι i)

  frameMatch : ∀ i, principalLevelFrame.FrameMatch PY (PW i) (ι i)

end FromLinks

end Formalism.IndefR.RecTie

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.TensCastR
section -- merged from Formalism.LocalToGlobal.Columns.MtRowFrame
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions

namespace Formalism.L2.Col

def rowFrameOf (D : D7) (Occ : Set (NG.FinTyp D.host.E D.R.r)) (e : D.what₂.FT ≃ FinTypCls Occ) : Formalism.L2.RowFrame D where
  rep σ := finTypRep Occ (e σ)
  inj _ _ h := e.injective (finTypRep_inj h)

end Formalism.L2.Col
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.IndefR.principalLevelFrame

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def tensCastR {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2) :
    FiniteAdeleRing (𝓞 F1) F1 ⊗[F1] E ≃+* E ⊗[F2] FiniteAdeleRing (𝓞 F2) F2 := by
  subst h
  exact (Algebra.TensorProduct.comm F1 (FiniteAdeleRing (𝓞 F1) F1) E).toRingEquiv

variable {D : D7}

def StdPsi {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (P : RowPsi V n) : Prop :=
  (∃ (β : Matrix (Fin V.rank) (Fin n) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E))
      (β' : Matrix (Fin n) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)),
      β * β' = 1 ∧ β' * β = 1 ∧
      ∀ κ, finMat D.sp.cm.sig V.gram (P.ψ κ) =
        β * ((κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map (tensCastR hF).symm) * β') ∧
  ∀ κ, κ ∈ ReciprocityTheory.Aut.Umax D.host.E n ↔ P.ψ κ ∈ KsphC V ∅

def RowRepTie {V : HSp D} {n : ℕ} {Sp : D.what₂.Tau → SPar} (rowRep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E n)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (PY : RowPsi V n) (M : Formalism.IndefR.Mult.DSModel V Sp) (J : Bool → Set (GA D V))
    (χ : Bool → GA D V → ℂ) (e : Bool → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (eFT : D.what₂.FT ≃ FTR θ PY M J χ e) : Prop :=
  ∀ σ, (rowRep σ).Iso (rowRepR θ (eFT σ))

def RowLocPin {V : HSp D} {Sp : D.what₂.Tau → SPar} (lp : Formalism.L2.LPTiedPlaceholder D)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (PY : RowPsi V D.R.r)
    (M : Formalism.IndefR.Mult.DSModel V Sp) (J : Bool → Set (GA D V)) (χ : Bool → GA D V → ℂ)
    (e : Bool → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (eFT : D.what₂.FT ≃ FTR θ PY M J χ e) : Prop :=
  Formalism.L2.RowLocTied D lp (Formalism.L2.Col.rowFrameOf D (OccRows θ PY M J χ e) eFT)

end Formalism.IndefR.principalLevelFrame

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.CompZeroOfOrth
section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FixNLeMulRight
noncomputable section

open NumberField

namespace Formalism.IndefR.principalLevelFrame

section SSP

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
variable {A : Type} [AddCommGroup A] [Module ℂ A]
variable {ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A} {B : A →ₗ⋆[ℂ] A →ₗ[ℂ] ℂ}

def Intw (π π' : Formalism.L2.NG.FinTyp L n) (T : π.S →ₗ[ℂ] π'.S) : Prop :=
  ∀ (h : Formalism.AUTREP.GAf L n) (f : π.S), T ⟨Formalism.L2.NG.rt L n h f, π.stable h f f.2⟩ =
    ⟨Formalism.L2.NG.rt L n h (T f), π'.stable h _ (T f).2⟩

end SSP

end Formalism.IndefR.principalLevelFrame
end
end

noncomputable section

open NumberField IsDedekindDomain
open Formalism.L2.Theta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory
open scoped TensorProduct

namespace Formalism.IndefR.principalLevelFrame

section Dec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance instCMHostD (D : Formalism.BasicNotions.D7) : IsCMField D.host.E := D.host.isCMField_hostE

variable {D : Formalism.BasicNotions.D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} {Sp : D.what₂.Tau → SPar}
variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))

def ActStable (P : RowPsi V n) (M : Mult.DSModel V Sp) : Prop :=
  ∀ h, ∀ T ∈ Minf θ P M, actM P M h T ∈ Minf θ P M

def IpInv (P : RowPsi V n) (M : Mult.DSModel V Sp) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop :=
  ∀ h, ∀ T ∈ Minf θ P M, ∀ T' ∈ Minf θ P M, Mult.ipM M μ 𝓕 (actM P M h T) (actM P M h T') = Mult.ipM M μ 𝓕 T T'

def HermPosLev (P : RowPsi V n) (M : Mult.DSModel V Sp) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop :=
  ∀ N : ℕ, 0 < N → PeterssonHilbertSpace.IsHermPos (Mult.Mult θ M (levN P N) (fun _ => 1)) (Mult.ipM M μ 𝓕)

def IsotDecomp (P : RowPsi V n) (M : Mult.DSModel V Sp) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop :=
  Mult.goodPart θ M J χ e = ⨆ π : Formalism.L2.NG.FinTyp D.host.E n, isotL θ P M J χ e π ∧
    ∀ π π' : Formalism.L2.NG.FinTyp D.host.E n, ¬ π.Iso π' →
      ∀ x ∈ isotL θ P M J χ e π, ∀ y ∈ isotL θ P M J χ e π', Mult.ipM M μ 𝓕 x y = 0

end Dec

section DecProofs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance instCMHostD' (D : Formalism.BasicNotions.D7) : IsCMField D.host.E := D.host.isCMField_hostE

variable {D : Formalism.BasicNotions.D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} {Sp : D.what₂.Tau → SPar}
variable {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
variable {P : RowPsi V n} {M : Mult.DSModel V Sp}

theorem isMultMap_mono {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} (hJ : J' ⊆ J) (hχ : ∀ k ∈ J', χ' k = χ k)
    {T : Mult.MMap M} (h : Mult.IsMultMap θ M J χ T) : Mult.IsMultMap θ M J' χ' T :=
  ⟨h.aut, h.cusp, fun v k hk g => by rw [h.lev v k (hJ hk) g, hχ k hk], h.equiv, h.cont⟩

theorem mult_mono {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} (hJ : J' ⊆ J) (hχ : ∀ k ∈ J', χ' k = χ k) :
    Mult.Mult θ M J χ ≤ Mult.Mult θ M J' χ' :=
  Submodule.span_mono fun _ hT => isMultMap_mono hJ hχ hT

theorem levN_mono (N m : ℕ) : levN P (N * m) ⊆ levN P N := by
  rintro _ ⟨κ, hκ, rfl⟩
  exact ⟨κ, Formalism.L2.NG.Cong.of_mul_left D.host.E n hκ, rfl⟩

abbrev LN (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (P : RowPsi V n) (M : Mult.DSModel V Sp) (N : ℕ) :
    Submodule ℂ (Mult.MMap M) :=
  Mult.Mult θ M (levN P (N + 1)) (fun _ => 1)

theorem LN_directed : Directed (· ≤ ·) (LN θ P M) := by
  intro i j
  have hpos : 1 ≤ (i + 1) * (j + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
  have e : (i + 1) * (j + 1) - 1 + 1 = (i + 1) * (j + 1) := Nat.sub_add_cancel hpos
  refine ⟨(i + 1) * (j + 1) - 1, ?_, ?_⟩
  · apply mult_mono
    · rw [e]
      exact levN_mono _ _
    · intros
      rfl
  · apply mult_mono
    · rw [e, mul_comm]
      exact levN_mono _ _
    · intros
      rfl

theorem mem_Minf {T : Mult.MMap M} : T ∈ Minf θ P M ↔ ∃ N, T ∈ LN θ P M N :=
  Submodule.mem_iSup_of_directed _ LN_directed

theorem LN_le_Minf (N : ℕ) : LN θ P M N ≤ Minf θ P M := le_iSup (LN θ P M) N

theorem common3 {x y z : Mult.MMap M} (hx : x ∈ Minf θ P M) (hy : y ∈ Minf θ P M) (hz : z ∈ Minf θ P M) :
    ∃ N, x ∈ LN θ P M N ∧ y ∈ LN θ P M N ∧ z ∈ LN θ P M N := by
  obtain ⟨a, ha⟩ := mem_Minf.1 hx
  obtain ⟨b, hb⟩ := mem_Minf.1 hy
  obtain ⟨c, hc⟩ := mem_Minf.1 hz
  obtain ⟨d, had, hbd⟩ := LN_directed (θ := θ) (P := P) (M := M) a b
  obtain ⟨k, hdk, hck⟩ := LN_directed (θ := θ) (P := P) (M := M) d c
  exact ⟨k, hdk (had ha), hdk (hbd hb), hck hc⟩

theorem mult_le_Minf {J : Set (GA D V)} {χ : GA D V → ℂ} (hl : LevOK P J χ) : Mult.Mult θ M J χ ≤ Minf θ P M := by
  obtain ⟨N0, hN0, h0⟩ := hl
  have e : N0 - 1 + 1 = N0 := Nat.sub_add_cancel hN0
  refine le_trans ?_ (LN_le_Minf (N0 - 1))
  apply mult_mono
  · rintro _ ⟨κ, hκ, rfl⟩
    rw [e] at hκ
    exact (h0 κ hκ).1
  · rintro _ ⟨κ, hκ, rfl⟩
    rw [e] at hκ
    exact (h0 κ hκ).2.symm

variable (μ : Measure (GA D V)) (𝓕 : Set (GA D V))

theorem hp3 (hHP : HermPosLev θ P M μ 𝓕) (x y z : Minf θ P M) :
    ∃ N, PeterssonHilbertSpace.IsHermPos (LN θ P M N) (Mult.ipM M μ 𝓕) ∧ (x : Mult.MMap M) ∈ LN θ P M N ∧
      (y : Mult.MMap M) ∈ LN θ P M N ∧ (z : Mult.MMap M) ∈ LN θ P M N := by
  obtain ⟨N, hx, hy, hz⟩ := common3 x.2 y.2 z.2
  exact ⟨N, hHP (N + 1) (Nat.succ_pos N), hx, hy, hz⟩

def ipA (hHP : HermPosLev θ P M μ 𝓕) : Minf θ P M →ₗ⋆[ℂ] Minf θ P M →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => Mult.ipM M μ 𝓕 x y)
    (fun x x' y => by
      obtain ⟨N, hp, hx, hx', hy⟩ := hp3 μ 𝓕 hHP x x' y
      exact hp.add ⟨x, hx⟩ ⟨x', hx'⟩ ⟨y, hy⟩)
    (fun s x y => by
      obtain ⟨N, hp, hx, hy, -⟩ := hp3 μ 𝓕 hHP x y y
      exact hp.smul s ⟨x, hx⟩ ⟨y, hy⟩)
    (fun x y y' => by
      obtain ⟨N, hp, hx, hy, hy'⟩ := hp3 μ 𝓕 hHP x y y'
      have h1 := hp.herm ⟨(y : Mult.MMap M) + y', Submodule.add_mem _ hy hy'⟩ ⟨x, hx⟩
      have h2 := hp.herm ⟨y, hy⟩ ⟨x, hx⟩
      have h3 := hp.herm ⟨y', hy'⟩ ⟨x, hx⟩
      have h4 := hp.add ⟨y, hy⟩ ⟨y', hy'⟩ ⟨x, hx⟩
      simp only [Submodule.coe_add] at h1 h2 h3 h4 ⊢
      rw [← h1, ← h2, ← h3, h4, map_add (f := _)])
    (fun s x y => by
      obtain ⟨N, hp, hx, hy, -⟩ := hp3 μ 𝓕 hHP x y y
      have h1 := hp.herm ⟨s • (y : Mult.MMap M), Submodule.smul_mem _ s hy⟩ ⟨x, hx⟩
      have h2 := hp.herm ⟨y, hy⟩ ⟨x, hx⟩
      have h4 := hp.smul s ⟨y, hy⟩ ⟨x, hx⟩
      simp only [Submodule.coe_smul] at h1 h2 h4 ⊢
      rw [← h1, ← h2, h4, map_mul, Complex.conj_conj]
      rfl)

end DecProofs

end Formalism.IndefR.principalLevelFrame
end
end
