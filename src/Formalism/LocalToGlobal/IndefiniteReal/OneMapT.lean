module

public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv

@[expose] public section

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.OneMapT
noncomputable section

open NumberField
open scoped TensorProduct

namespace Formalism.IndefR.FWT

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj
  ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

abbrev inC {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {l : Level H} (c' : Coeff l) : c'.F →+* ℂ := c'.F.val.toRingHom

abbrev sOv (C : Core D) (c' : Coeff C.Q.l) (hle : C.Q.c.F ≤ c'.F) : C.Q.c.F →+* ℂ := (inC c').comp (incF C.Q.c c' hle)

theorem sOv_eq (C : Core D) (c' : Coeff C.Q.l) (hle : C.Q.c.F ≤ c'.F) : sOv C c' hle = C.σ₀ := by
  first
  | rfl
  | (ext x; rfl)
  | (ext x; simp [sOv, inC, incF])


set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 1000000 in
structure OMDat (C : Core D) [Algebra C.Q.c.F D.what₂.LL] (R : RealDat D A C.Q.c.F) (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) : Type 1 where
  c' : Coeff C.Q.l
  hle : C.Q.c.F ≤ c'.F
  jL : D.what₂.LL →+* c'.F
  hV : C.V ((i : ℕ) + 1) (sOv C c' hle) = Wc D i
  c0' : VsV D i c'.F →ₛₗ[inC c'] (R.cV i).W
  lev : G → (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (C.Q.Dw ((i : ℕ) + 1)).La
  dδ : Tp → DeltaDat (C.Q.Xo ((i : ℕ) + 1)) c' (Vc D i).rank
  Cl' : Tp → Type
  [fCl : ∀ t, Fintype (Cl' t)]
  bad : Tp → ℕ
  Lh : ∀ t, Cl' t → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)
  La : ∀ t, Cl' t → GenLat D.host.E (Vc D i).rank
  Nc : ∀ t, Cl' t → ℕ
  gam : ∀ t, Cl' t → ℕ
  vol : Tp → c'.F
  ep : ∀ t, Cl' t → c'.F
  B : Tp → Ideal (𝓞 D.host.E) → c'.F
  epF : Tp → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E) → c'.F
  io : VsV D i c'.F →ₗ[c'.F] MvPolynomial (LtN (C.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c'.F
  hw : VsV D i c'.F
  φ : ∀ t, (Fin (Vc D i).rank → LevQc (C.Q.Dw ((i : ℕ) + 1)) (dδ t).l₂) → c'.F
  w : ∀ t, Cl' t → (Fin (Vc D i).rank → LevQ (C.Q.Dw ((i : ℕ) + 1)) (dδ t).l₂) → c'.F
  U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ ((inC c').comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c'.F)) D.R.r
  dict₂ : ∀ t, GA D (Wc D i) → Σ k, Frame ((U₂ t).X k).Ψ D.R.r
  xi : Tp → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ
  thAd : ∀ t, (Cl' t → VsV D i c'.F) → AutQ (Wc D i) → ℂ
  Plc : ∀ t, (Cl' t → VsV D i c'.F) → Prop

attribute [instance] OMDat.fCl

namespace OMDat

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat C R i Tp tup)

abbrev s0 : C.Q.c.F →+* ℂ := sOv C O.c' O.hle

abbrev lev2 (g : G) := (O.lev g, (LinearMap.id : (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (C.Q.Dw ((i : ℕ) + 1)).La))

abbrev dict := castDict O.hV (C.dict ((i : ℕ) + 1) O.s0)

abbrev mu : GA D (Wc D i) → ℂ := castDict O.hV (C.mu ((i : ℕ) + 1) O.s0)

def phi (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (f : C.R ((i : ℕ) + 1)) : GA D (Wc D i) → ℂ :=
  adel (Wc D i) O.dict (muPin (Wc D i) O.dict O.mu cc) (rdU (C.U ((i : ℕ) + 1) O.s0) f)

variable (κ : WeightFamilies.Wt D ((i : ℕ) + 1))

def EquivAt (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) : Prop :=
  ∀ g k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k →
    ∀ f ∈ C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n, actLev C.Q.c O.lev2 g f ∈ C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n ∧ ∀ h,
      O.phi cc (actLev C.Q.c O.lev2 g f) h =
        (∏ PP : R.Pg, ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g PP)) : ℂˣ) : ℂ)) * O.phi cc f (h * k)

def PhRat (v₀ : (R.MW i (sg0 D A)).Vec) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (ph : ℂ) : Prop :=
  ∀ x : A.fam.amb.FL i A.μ0, ∃ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n), ∀ h,
    ph * (R.HW i (sg0 D A)).e (R.thG i A.μ0 (jVx R i A.μ0 x)) v₀ h =
      ∑ k, D.what₂.embLL (a k) * ((lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * O.phi cc (f k : C.R ((i : ℕ) + 1)) h)

structure Pins (v₀ : (R.MW i (sg0 D A)).Vec)
    (ι : (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ) : Prop where
  lift : ThPinsR R i O.jL (inC O.c') v₀ O.c0' ι C.Q.l.M (Mfr C.Q.l) O.lev
  tuple : ∀ t, ThPinsT R i (inC O.c') (tup t) v₀ O.c0' ι (O.bad t) C.Q.l.Mb (O.dδ t).I (Mfr (O.dδ t).l₂ • ⊤) (O.Lh t) (O.gam t)
    (O.vol t) (O.B t) (O.xi t) (O.φ t) (O.thAd t) (O.Plc t)
  act : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c O.lev2 ∧ ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) O.c' O.lev2
  bad : ∀ t, 0 < O.bad t ∧ BadPin (O.bad t) (D.host.QS * D.host.q) D.host.d (D.host.g 0 * D.host.g 1)
  reps : RepsCov (C.Q.Xo ((i : ℕ) + 1)) O.c' O.Cl' O.dδ O.bad O.Lh O.La O.Nc O.gam
  ep : ∀ t, (∀ k, O.ep t k = O.epF t (O.Lh t k)) ∧ EpIs (Dw := C.Q.Dw ((i : ℕ) + 1)) O.c' (O.bad t) (O.B t) (O.epF t)
  io : IoLFRec O.c' (fun τ => embF O.c' (tauE D τ)) (lamV D i) (wtA κ) O.io O.hw
  w : WPin (C.Q.Xo ((i : ℕ) + 1)) O.c' O.Cl' O.dδ O.φ O.w
  cov : CovPin (C.Q.Xo ((i : ℕ) + 1)) O.c' O.dδ
  cxi : CXiVal (Wc D i) (rank_Wc i) (inC O.c') O.dδ O.U₂ O.dict₂ ι x₀ O.xi
  model₂ : ∀ t k, ModelW (Wc D i) (rank_Wc i) ((O.U₂ t).X k)

def OneMapOf (v₀ : (R.MW i (sg0 D A)).Vec) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (ph : ℂ) : Prop :=
  O.EquivAt κ cc ∧
    OneMapTieC O.hle D.what₂.embLL.toRatAlgHom.fieldRange (C.U ((i : ℕ) + 1)) (inC O.c') (Wc D i) O.dict O.mu (xiR D) (wtA κ)
      (actLev C.Q.c O.lev2) (actLev O.c' O.lev2) O.dδ O.Cl' O.w O.La O.Nc O.gam O.vol O.ep O.io O.thAd O.Plc cc ph ∧
    O.PhRat κ v₀ cc ph

end OMDat

def QHalf {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) : Prop :=
  ∀ t, ∀ PP ∈ R.Q t, ∀ PP' ∈ R.Q t, (∃ p : ℕ, p.Prime ∧ (p : 𝓞 D.host.E) ∈ PP.asIdeal ∧ (p : 𝓞 D.host.E) ∈ PP'.asIdeal) →
    PP.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = PP'.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

def QGuard {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) : Prop :=
  QHalf R ∧ ∀ t, ∀ PP ∈ R.Q t, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal

section Comparison₂

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))

def iotaW (i : Fin D.R.m) : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E) :=
  LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ T.iota ((i : ℕ) + 1)

def OMPins (i : Fin D.R.m) : Prop :=
  (O i).c'.F = D.what₂.embLL.toRatAlgHom.fieldRange ∧ (O i).Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) (O i).s0)

def OneMapRow0 (i : Fin D.R.m) : Prop := ∃ cc ph, (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph

def PhaseTie (ph : Fin D.R.m → ℂ) (i : Fin D.R.m) : Prop :=
  OneMapRow0 T R κ v₀ O i → (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) (ph i)

def OneMapRowR (ph : Fin D.R.m → ℂ) (i : Fin D.R.m) : Prop :=
  OneMapRow0 T R κ v₀ O i ∧
    (QGuard R → ∃ O' : OMDat T.toCore R i T0 id, D.what₂.embLL.toRatAlgHom.fieldRange ≤ O'.c'.F ∧
      O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O'.s0) ∧
        O'.OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) O'.s0) (ph i))

theorem phi_cE (i : Fin D.R.m) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R ((i : ℕ) + 1)) (h : GA D (Wc D i)) :
    (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℂ) * (O i).phi (T.cE ((i : ℕ) + 1) (O i).s0) f h =
      ((O i).hV ▸ T.phiJ ((i : ℕ) + 1) (O i).s0 a f : GA D (Wc D i) → ℂ) h := by
  have key : ∀ (σ : T.Q.c.F →+* ℂ) (W : HSp D) (hV : T.V ((i : ℕ) + 1) σ = W) (g : GA D W),
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℂ) * adel W (castDict hV (T.dict ((i : ℕ) + 1) σ))
        (muPin W (castDict hV (T.dict ((i : ℕ) + 1) σ)) (castDict hV (T.mu ((i : ℕ) + 1) σ)) (T.cE ((i : ℕ) + 1) σ))
        (rdU (T.U ((i : ℕ) + 1) σ) f) g = (hV ▸ T.phiJ ((i : ℕ) + 1) σ a f : GA D W → ℂ) g := by
    intro σ W hV g
    subst hV
    rfl
  exact key _ _ (O i).hV h

end Comparison₂

end Formalism.IndefR.FWT
end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FWTie
noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.IndefR.FWT

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Arith Formalism.IndefR.Mult Formalism.L2.Pj

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}


set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
structure FWTie (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) where

  alg_eq : ∀ x : 𝓞 T.Q.c.F, algebraMap T.Q.c.F D.what₂.LL (x : T.Q.c.F) = D.what₂.OtoLL (T.Q.eO x)

  e : ∀ i : Fin D.R.m, T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n ≃ₗ[T.Q.c.F] (R.FW i).WK

  ks : ∀ i : Fin D.R.m, (R.FW i).IsKsForm

  kap : ∀ (i : Fin D.R.m) (τ : D.what₂.Tau),
    (∀ k : Fin (D.R.sigW ((i : ℕ) + 1)).1, (κ i).aP τ k = aPl D i ((Wc D i).sig (tauE D τ)).1 τ k) ∧
    (∀ k : Fin (D.R.sigW ((i : ℕ) + 1)).2,
      (κ i).aM τ k = aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ k) ∧ (κ i).n = D.R.nV

  pt : ∀ (i : Fin D.R.m) (la : HeightOneSpectrum (𝓞 T.Q.c.F)), (R.FW i).Pt la ≃ T.PtM ((i : ℕ) + 1) la

  nrm_eq : ∀ (i : Fin D.R.m) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : (R.FW i).Pt la) (f : T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n),
    (R.FW i).nrm la y (e i f) = T.nrmM ((i : ℕ) + 1) la (pt i la y) (f : T.R ((i : ℕ) + 1))

  laws : LawsJ T

  chiR : ChiR T R

  hv₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), IsChosenExtremalVector R i σ (v₀ i σ)

  x0 : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) →
    IsModelBaseFrameFamily (R.MW i σ) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) (σ.comp (algebraMap T.Q.c.F D.what₂.LL)))

  ev0 : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) →
    ∀ hV : T.V ((i : ℕ) + 1) (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) = Wc D i,
    (¬ ∃ j' : (Fin (R.nW i) → D.what₂.LL) →ₛₗ[σ] (R.HW i σ).H, ∀ f : T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n,
      ((R.HW i σ).e (j' ((e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL))) (v₀ i σ) =
        hV ▸ T.phiJ ((i : ℕ) + 1) (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) (wtA (κ i)) (f : T.R ((i : ℕ) + 1))) →
    (R.FW i).j σ = 0

  ev : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) →
    ∀ hV : T.V ((i : ℕ) + 1) (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) = Wc D i,
    (∃ j' : (Fin (R.nW i) → D.what₂.LL) →ₛₗ[σ] (R.HW i σ).H, ∀ f : T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n,
      ((R.HW i σ).e (j' ((e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL))) (v₀ i σ) =
        hV ▸ T.phiJ ((i : ℕ) + 1) (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) (wtA (κ i)) (f : T.R ((i : ℕ) + 1))) →
    ∀ f : T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n,
      ((R.HW i σ).e ((R.FW i).j σ ((e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL))) (v₀ i σ) =
        hV ▸ T.phiJ ((i : ℕ) + 1) (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) (wtA (κ i)) (f : T.R ((i : ℕ) + 1))

end Formalism.IndefR.FWT
end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.PartsRow
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped TensorProduct InnerProductSpace
open IsDedekindDomain NumberField MeasureTheory

namespace Formalism.IndefR.RecTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section FromLinks

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure PartsRec (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) {n : ℕ}
    (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) n)
    (eFT : D.what₂.FT ≃ principalLevelFrame.FTR R.θ PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.levR F b)))
      (fun b => levChi _ (R.βY 0) (R.dat0 (R.levR F b))) (fun _ => R.e0))
    {Xd : DivX D} (E : EigIdx D Xd) (labPi : E.Pi → A.fam.base.Ix)
    (piOf : E.Pi → HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ)
    (prtE : D.what₂.FT → Submodule ℂ (AmbT (R.MY 0)))
    (prtWf : ∀ i : Fin D.R.m, D.what₂.FT → Submodule ℂ (AmbT (R.MW i (sg0 D A)))) : Prop where

  cOf : ∀ π, piOf (E.cOf π) = principalLevelFrame.cOfT (PW ⟨0, hm⟩)
    (levS _ (R.βW ⟨0, hm⟩) (R.datWp ⟨0, hm⟩ (R.levL F false (sg0 D A))))
    (levChi _ (R.βW ⟨0, hm⟩) (R.datWp ⟨0, hm⟩ (R.levL F false (sg0 D A)))) (SsetF R (tupT D.what₂.mu0)) (principalLevelFrame.rowRepR R.θ (eFT π))

  piOf_inj : Function.Injective piOf

  prt : ∀ π, prtE π ≤ (hPart (R.MY 0) (levG _ (R.βY 0) (R.dat0 R.triv)) (A.ok A.μ0) R.pl A.q
    (RealDat.polE (A := A) (labPi (E.cOf π)).1)).map (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap

  prtW : ∀ i π, prtWf i π ≤ (hPart (R.MW i (sg0 D A)) (levG _ (R.βW i) (R.datWp i R.triv)) (A.ok A.μ0) R.pl A.q
    (RealDat.polW (A := A) (labPi (E.cOf π)).1)).map (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A)) ≃ₗ[ℂ] _).toLinearMap

end FromLinks

end Formalism.IndefR.RecTie

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.TopMult
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.TopMult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Adelic

variable {D : D7} {V : HSp D}

theorem mem_GfC' (h : GA D V) : h ∈ GfC V ↔ (Eqv.matA D V h).map (infPart D) = 1 := by
  show (infHom V) h = 1 ↔ _
  rw [Units.ext_iff]
  exact Iff.rfl

theorem psiT_of_mem_GfC' {h : GA D V} (hh : h ∈ GfC V) (τ : D.what₂.Tau) : (Eqv.matA D V h).map (Eqv.psiT D τ) = 1 := by
  have h1 := (mem_GfC' h).1 hh
  unfold Eqv.psiT
  rw [RingHom.coe_comp, ← Matrix.map_map, h1]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem inf_GinfC_GfC' : GinfC V ⊓ GfC V = ⊥ := by
  rw [eq_bot_iff]
  rintro a ⟨ha, hb⟩
  rw [Subgroup.mem_bot]
  apply Eqv.matA_inj D V
  rw [Eqv.matA_one]
  apply Eqv.mat_ext D
  · intro τ
    rw [psiT_of_mem_GfC' hb τ, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [(Eqv.mem_GinfC D V a).1 ha, Matrix.map_one _ (map_zero _) (map_one _)]

theorem mem_GfC_of_psiT {h : GA D V} (hh : ∀ τ, (Eqv.matA D V h).map (Eqv.psiT D τ) = 1) : h ∈ GfC V := by
  rw [mem_GfC']
  ext i j
  rw [Matrix.map_apply]
  apply (Eqv.splitEquiv D).injective
  funext τ
  have e := congrFun (congrFun (hh τ) i) j
  rw [Matrix.map_apply] at e
  rw [Eqv.splitEquiv_apply, Eqv.splitEquiv_apply]
  change Eqv.psiT D τ (Eqv.matA D V h i j) = _
  rw [e]
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply_ne hij]

theorem ga_decomp (g : GA D V) : ∃ h ∈ GfC V, ∃ a ∈ GinfC V, g = h * a := by
  refine ⟨g * (Eqv.infOnly D V g)⁻¹, mem_GfC_of_psiT fun τ => ?_, Eqv.infOnly D V g, Eqv.infOnly_mem_GinfC D V g,
    (inv_mul_cancel_right g _).symm⟩
  have h1 : (Eqv.matA D V g).map (Eqv.psiT D τ) = (Eqv.matA D V (Eqv.infOnly D V g)).map (Eqv.psiT D τ) := by
    rw [← Eqv.infMat_thetaC, ← Eqv.infMat_thetaC, Eqv.infMat_infOnly]
  rw [Eqv.matA_mul, Matrix.map_mul, h1, ← Matrix.map_mul, ← Eqv.matA_mul, mul_inv_cancel, Eqv.matA_one,
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem ginf_mem_closure {θ : Datum.InfFam D} (hθ : IsInfFam θ) {a : GA D V} (ha : a ∈ GinfC V) :
    a ∈ Submonoid.closure {x | ∃ τ, ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), x = atTau θ V τ g} := by
  obtain rfl := Eqv.eq_thetaC D hθ
  classical
  set gs : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ => infMat D.sp.cm.sig V.gram (Eqv.thetaC D τ) a
  have hgs : Eqv.IsUnitFam D V gs := Eqv.infMat_unitary' D V a
  have hu : ∀ s : Finset D.what₂.Tau, Eqv.IsUnitFam D V (fun τ => if τ ∈ s then gs τ else 1) := by
    intro s τ
    by_cases hτ : τ ∈ s
    · simp only [hτ, if_true]; exact hgs τ
    · simp only [hτ, if_false]; simp
  have key : ∀ s : Finset D.what₂.Tau, Eqv.famH D V _ (hu s) ∈
      Submonoid.closure {x | ∃ τ, ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), x = atTau (Eqv.thetaC D) V τ g} := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have e : Eqv.famH D V _ (hu ∅) = 1 := by
        apply Eqv.matA_inj D V
        rw [Eqv.matA_famH, Eqv.matA_one]
        convert Eqv.famM_one D V using 2
        funext τ
        simp
      rw [e]
      exact Submonoid.one_mem _
    | insert τ0 s hτ0 ih =>
      have e : Eqv.famH D V _ (hu (insert τ0 s)) = Eqv.atH D V τ0 (gs τ0) (hgs τ0) * Eqv.famH D V _ (hu s) := by
        apply Eqv.matA_inj D V
        rw [Eqv.matA_famH, Eqv.matA_mul, Eqv.matA_atH, Eqv.matA_famH]
        apply Eqv.mat_ext D
        · intro τ
          rw [Matrix.map_mul, Eqv.psi_famM, Eqv.psi_atM, Eqv.psi_famM]
          by_cases h : τ = τ0
          · subst h; simp [hτ0]
          · simp [h]
        · rw [Matrix.map_mul, Eqv.fin_famM, Eqv.fin_atM, Eqv.fin_famM, Matrix.one_mul]
      rw [e]
      refine Submonoid.mul_mem _ (Submonoid.subset_closure ⟨τ0, gs τ0, hgs τ0, ?_⟩) ih
      exact (Eqv.atTau_eq D V τ0 (gs τ0) (hgs τ0)).symm
  have e : a = Eqv.famH D V _ (hu Finset.univ) :=
    Eqv.famH_unique D V _ (hu Finset.univ) a ha (fun τ => by simp [gs])
  rw [e]
  exact key Finset.univ

end Adelic

section GenAd

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} {F : G → W}

end GenAd

section GenHom

variable {G H : Type} [Group G] [Group H] (f : G →* H)

end GenHom

section Generic

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : Datum.InfFam D) (M : DSModel V S) (c : CoefA V)
  (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ)

theorem rr_of_GinfC {a : GA D V} (ha : a ∈ GinfC V) : (finHom V).rangeRestrict a = 1 := Subtype.ext (MonoidHom.mem_ker.mp ha)

theorem atTau_mem_GinfC (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : atTau θ V τ g ∈ GinfC V := by
  unfold atTau
  split_ifs with h
  · exact h.choose_spec.1
  · exact Subgroup.one_mem _

variable {θ M c pr}

variable {J' : Subgroup (Bridge.Gf V)} {χ' : J' →* ℂˣ} {F : Bridge.Gf V → c.W}






theorem exists_lift (y : Bridge.Gf V) : ∃ h, h ∈ GfC V ∧ (finHom V).rangeRestrict h = y := by
  obtain ⟨g, rfl⟩ := (finHom V).rangeRestrict_surjective y
  obtain ⟨h, hh, a, ha, rfl⟩ := ga_decomp g
  exact ⟨h, hh, by rw [map_mul, rr_of_GinfC ha, mul_one]⟩

theorem lift_unique {h h' : GA D V} (hh : h ∈ GfC V) (hh' : h' ∈ GfC V)
    (e : (finHom V).rangeRestrict h = (finHom V).rangeRestrict h') : h = h' := by
  have h1 : h⁻¹ * h' ∈ GinfC V := by
    show h⁻¹ * h' ∈ (finHom V).ker
    have e2 := congrArg Subtype.val e
    simp only [MonoidHom.coe_rangeRestrict] at e2
    rw [MonoidHom.mem_ker, map_mul, map_inv, e2, inv_mul_cancel]
  have h2 : h⁻¹ * h' ∈ GfC V := mul_mem (inv_mem hh) hh'
  have h3 : h⁻¹ * h' ∈ GinfC V ⊓ GfC V := ⟨h1, h2⟩
  rw [inf_GinfC_GfC', Subgroup.mem_bot] at h3
  exact inv_mul_eq_one.mp h3



end Generic

section Real

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


end Real

end Formalism.IndefR.TopMult
end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.ThetaFireRow
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped TensorProduct

namespace Formalism.IndefR.RecTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section FromLinks

open Formalism.IndefR.Links

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def MtRead (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R)
    (hinj : ∀ i t, Function.Injective (R.extV i t)) (IL : LiftIds (toLiftReal R F tupT hm hTop hinj))
    (tw : ∀ μ (i : Fin D.R.m), D.what₂.MtL μ (i + 1) → A.fam.amb.FL i (tupT μ)) : Prop :=
  ∀ μ (hμ : Used0 D μ) (i : Fin D.R.m) (x : D.what₂.MtL μ (i + 1)),
    (IL.jMt μ hμ i (D.what₂.jMt μ (i + 1) x)).1 = R.extV i (tupT μ) (R.jV i (tupT μ) (tw μ i x))

def ThetaFireL {D : D7} {C : ChainReal D} (L : LiftReal D C) (I : LiftIds L) : Prop :=
  ∀ μ (hμ : Used0 D μ) (i : Fin D.R.m) (x : D.what₂.Mt μ (i + 1)), ∃ w : L.AmbW i,
    w ∈ L.MultW i ∧ w ∘ₗ L.embK i = L.thC μ i (I.jMt μ hμ i x) ∧ L.eW i ∘ₗ w ∈ L.Wc i

def ResInjL {D : D7} {C : ChainReal D} (L : LiftReal D C) : Prop :=
  ∀ (i : Fin D.R.m) (w : L.AmbW i), w ∈ L.MultW i → w ∘ₗ L.embK i = 0 → w = 0

def ThetaFireRow {D : D7} {C : ChainReal D} (L : LiftReal D C) (I : LiftIds L) : Prop :=
  (∀ μ, Used0 D μ → ∀ i, Lift.IsThetaP (L.measV μ i) (L.fdV μ i) (L.thW μ i) (L.ptW μ i) (L.ioK i) (L.Amt μ i)
    (L.thC μ i)) ∧ ThetaFireL L I ∧ ResInjL L

def MjRead (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R)
    (hinj : ∀ i t, Function.Injective (R.extV i t)) (IL : LiftIds (toLiftReal R F tupT hm hTop hinj))
    (nj : Fin D.R.m → ℕ) (crd : ∀ i : Fin D.R.m, (Fin (nj i) → D.what₂.LL) → D.what₂.Mj (i + 1))
    (jD : ∀ i : Fin D.R.m, (Fin (nj i) → D.what₂.LL) → (Fin (R.nW i) → D.what₂.LL)) : Prop :=
  ∀ (i : Fin D.R.m) (y : Fin (nj i) → D.what₂.LL),
    ((IL.jMj i (crd i y) : (toLiftReal R F tupT hm hTop hinj).Wc i) : (toLiftReal R F tupT hm hTop hinj).AmbW i) =
      PiTensorProduct.lift (Mult.postOn (R.MW i (sg0 D A)) (R.eWf i (sg0 D A))
        ((R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) (jD i y))))

end FromLinks

end Formalism.IndefR.RecTie

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.IsotInLeOfIntw
noncomputable section

open NumberField IsDedekindDomain
open Formalism.L2.Theta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory
open scoped TensorProduct

namespace Formalism.IndefR.principalLevelFrame

section Indep

variable {A : Type} [AddCommGroup A] [Module ℂ A]

theorem hp_add_right {C : Submodule ℂ A} {ip : A → A → ℂ} (hp : PeterssonHilbertSpace.IsHermPos C ip) (x y z : C) :
    ip x ((y : A) + z) = ip x y + ip x z := by
  have h1 := hp.herm (y + z) x
  have h2 := hp.herm y x
  have h3 := hp.herm z x
  have h4 := hp.add y z x
  simp only [Submodule.coe_add] at h1 h4
  rw [← h1, ← h2, ← h3, h4, map_add (f := _)]

theorem hp_zero_right {C : Submodule ℂ A} {ip : A → A → ℂ} (hp : PeterssonHilbertSpace.IsHermPos C ip) (x : C) : ip x (0 : A) = 0 := by
  have h := hp_add_right hp x 0 0
  simp only [ZeroMemClass.coe_zero, add_zero] at h
  linear_combination -h

theorem hp_sum_right {C : Submodule ℂ A} {ip : A → A → ℂ} (hp : PeterssonHilbertSpace.IsHermPos C ip) (x : C) {ι : Type}
    (s : Finset ι) (w : ι → C) : ip x (∑ i ∈ s, (w i : A)) = ∑ i ∈ s, ip x (w i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact hp_zero_right hp x
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    have h := hp_add_right hp x (w a) (∑ i ∈ s, w i)
    rw [Submodule.coe_sum] at h
    exact h

end Indep

section F

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance instCMHostF (D : Formalism.BasicNotions.D7) : IsCMField D.host.E := D.host.isCMField_hostE

variable {D : Formalism.BasicNotions.D7} {n : ℕ}

theorem isotIn_le_of_intw {A : Type} [AddCommGroup A] [Module ℂ A] (ρ : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ A)
    (C : Submodule ℂ A) {π π' : Formalism.L2.NG.FinTyp D.host.E n} (T : π'.S →ₗ[ℂ] π.S) (hT : Intw π' π T)
    (hsurj : LinearMap.range T = ⊤) : isotIn ρ C π ≤ isotIn ρ C π' := by
  unfold isotIn
  refine iSup₂_le fun Φ hΦ => ?_
  have hr : LinearMap.range (Φ.comp T) = LinearMap.range Φ := by
    rw [LinearMap.range_comp, hsurj, Submodule.map_top]
  rw [← hr]
  refine le_iSup₂ (f := fun (Ψ : π'.S →ₗ[ℂ] A) (_ : IsEqvA ρ π' Ψ ∧ LinearMap.range Ψ ≤ C) => LinearMap.range Ψ)
    (Φ.comp T) ⟨?_, hr ▸ hΦ.2⟩
  intro h f
  simp only [LinearMap.comp_apply]
  rw [hT h f]
  exact hΦ.1 h (T f)

theorem isotIn_iso {A : Type} [AddCommGroup A] [Module ℂ A] (ρ : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ A)
    (C : Submodule ℂ A) {π π' : Formalism.L2.NG.FinTyp D.host.E n} (h : π.Iso π') : isotIn ρ C π = isotIn ρ C π' := by
  unfold Formalism.L2.NG.FinTyp.Iso Formalism.L2.NG.IsoRep at h
  obtain ⟨T, hT⟩ := h
  apply le_antisymm
  · refine isotIn_le_of_intw ρ C (T.symm : π'.S →ₗ[ℂ] π.S) ?_ (LinearMap.range_eq_top.2 T.symm.surjective)
    intro h f
    have key : T ⟨_, π.stable h _ (T.symm f).2⟩ = ⟨_, π'.stable h _ f.2⟩ := by
      apply Subtype.ext
      rw [hT h (T.symm f) ⟨_, π.stable h _ (T.symm f).2⟩ rfl, LinearEquiv.apply_symm_apply]
    exact T.symm_apply_eq.2 key.symm
  · refine isotIn_le_of_intw ρ C (T : π.S →ₗ[ℂ] π'.S) ?_ (LinearMap.range_eq_top.2 T.surjective)
    intro h f
    apply Subtype.ext
    exact hT h f ⟨_, π.stable h _ f.2⟩ rfl

variable {Y W : Formalism.BasicNotions.TH.HSp D} {SpY SpW : D.what₂.Tau → SPar}
variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))

theorem isotL_iso (P : RowPsi W n) (M : Mult.DSModel W SpW) (J : Set (GA D W)) (χ : GA D W → ℂ)
    (e : (GA D W → ℂ) →ₗ[ℂ] (GA D W → ℂ)) {π π' : Formalism.L2.NG.FinTyp D.host.E n} (h : π.Iso π') :
    isotL θ P M J χ e π = isotL θ P M J χ e π' := by
  unfold isotL
  rw [isotIn_iso (actM P M) (Minf θ P M) h]



end F

end Formalism.IndefR.principalLevelFrame
end
end
