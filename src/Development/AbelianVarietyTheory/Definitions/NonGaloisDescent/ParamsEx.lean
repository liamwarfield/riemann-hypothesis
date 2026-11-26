module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DownLift

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev Sys (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

def chiW (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : (AE D)ˣ →* Circle :=
  (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1

def chiV (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : (AE D)ˣ →* Circle :=
  (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2

def valW (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (w : HeightOneSpectrum (𝓞 D.host.E)) : ℂˣ :=
  GlobalTheory.LFun.val (F := D.host.F) (chiW R i t) w

def valV (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (w : HeightOneSpectrum (𝓞 D.host.E)) : ℂˣ :=
  GlobalTheory.LFun.val (F := D.host.F) (chiV R i t) w

def str (q : ℕ) (z : ℂ) (n : ℕ) : Multiset ℂ :=
  (Multiset.range n).map fun k : ℕ => z * (q : ℂ) ^ (((n : ℂ) - 1) / 2 - (k : ℂ))

def IsEigV (R : RealDat D A Ks) (i : Fin D.R.m) (t : T)
    (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV i t).H) (s : Sys D) (y : (R.HV i t).H) : Prop :=
  ∀ P d, GlobalTheory.Hk3.Good R t P → GlobalTheory.Hk3.IsLab (Vc D i) P d → h P (Finsupp.single d 1) y = s P d • y

def HasString (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (s : Sys D) : Prop :=
  ∃ B : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) (Vc D i).rank s B ∧
    ∀ w : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.Hk3.Good R t w →
    ∃ B' : Multiset ℂ, (B w).map (fun a : ℂˣ => (a : ℂ)) =
        B' + str (Ideal.absNorm w.asIdeal) (valV R i t w : ℂ) D.R.t ∧
      ∀ a ∈ B', ‖a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2)

def downInt (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (f : WO (Vc D i) (Wc D i) → ℂ)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)) : ℂ :=
  ∫ h in R.fdV i t, thetaKO (R.ωP i t) h g f * l (R.extV i t y h) ∂(R.νV i t)

def SomeLift (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) : Prop :=
  ∃ f l g, IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ downInt R i t y f l g ≠ 0

def NonVan (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ h, GlobalTheory.Hk3.IsOpsV R i t h → ∀ s, HasString R i t s → ∀ y, IsEigV R i t h s y → y ≠ 0 → SomeLift R i t y

def GoodVt (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) : Prop :=
  ∀ l : (R.cV i).W →ₗ[ℂ] ℂ,
    gaL (Vc D i) (R.βV i) (R.datVt i t) R.eG (RealDat.eC (A := A) (sg0 D A)) (fun h => l (R.extV i t y h)) =
      fun h => l (R.extV i t y h)


open Classical in
def mirC (R : RealDat D A Ks) (i : Fin D.R.m) (PP : R.Pg) (a : Fin D.R.r → kP PP.1) (tr : Bool) (ε : ℤ) (g : G) : ℂ :=
  if (∀ PP', PP' ≠ PP → R.eG g PP' = 1) ∧
      (if tr then ∀ x, ∃ c : kP PP.1, (R.eG g PP : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).mulVec x - x = c • a
        else ∀ x, a ⬝ᵥ x = 0 → (R.eG g PP : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).mulVec x = x) then
    ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g PP)) ^ ε : ℂˣ) : ℂ)
  else 0

def NoChi (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) : Prop :=
  ∀ (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 → ∀ (tr : Bool) (ε : ℤ), ε = 1 ∨ ε = -1 → ∀ l : (R.cV i).W →ₗ[ℂ] ℂ,
    gaL (Vc D i) (R.βV i) (R.datVt i t) R.eG (mirC R i PP a tr ε) (fun h => l (R.extV i t y h)) = 0

def FinLike (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ ∀ c : WO (Vc D i) (Wc D i) →₀ ℂ, (∀ u ∈ c.support, u.map (infPart D) = 0) →
    (c.sum fun u z => z • heisO R.ψ (Vc D i) (Wc D i) u (R.vP i t)) = 0 →
    (c.sum fun u z => z • heisO R.ψ (Vc D i) (Wc D i) u f) = 0

def GenInf (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ y, R.thF i t y = 0 → ∀ f, FinLike R i t f → ∀ l g, downInt R i t y f l g = 0

def GenFin (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ y, NoChi R i t y → (∀ f, FinLike R i t f → ∀ l g, downInt R i t y f l g = 0) → ¬ SomeLift R i t y

def GoodNoChi (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop := ∀ y, GoodVt R i t y → NoChi R i t y

def GoodMem (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ y, GoodVt R i t y → (R.HW i (sg0 D A)).e (R.thG i t y) = R.thF i t y

def TypeNZ (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ h, GlobalTheory.Hk3.IsOpsV R i t h → ∀ s, HasString R i t s → ∀ y, IsEigV R i t h s y → GoodVt R i t y →
    R.thG i t y = 0 → y = 0

def partW (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (c : Sys D) : Submodule ℂ (MMap (R.MW i (sg0 D A))) :=
  partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv))
    (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c

def DownEig (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ h, GlobalTheory.Hk3.IsOpsV R i t h → ∀ s, ∃ c, ∀ y, IsEigV R i t h s y → R.thF i t y ∈ partW R i t c

def UnrCorr (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (ok : Pl D.host.E → Prop) : Prop :=
  ∀ h, GlobalTheory.Hk3.IsOpsV R i t h → ∀ s c y, IsEigV R i t h s y → R.thF i t y ≠ 0 → R.thF i t y ∈ partW R i t c →
    ∀ B B' : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) (Vc D i).rank s B →
      GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) D.R.r c B' → ∀ w : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.Hk3.Good R t w → ok w →
        (B w).map (fun a : ℂˣ => (a : ℂ)) =
          (B' w).map (fun a : ℂˣ => ((a * valV R i t w * (valW R i t w)⁻¹ : ℂˣ) : ℂ)) +
            str (Ideal.absNorm w.asIdeal) (valV R i t w : ℂ) D.R.t

def ParamsEx (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  (∀ h, GlobalTheory.Hk3.IsOpsV R i t h → ∀ s y, IsEigV R i t h s y → y ≠ 0 →
    ∃ B, GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) (Vc D i).rank s B) ∧
  ∀ c, partW R i t c ≠ ⊥ → ∃ B', GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) D.R.r c B' ∧
    ∀ w, GlobalTheory.Hk3.Good R t w → ∀ a ∈ B' w, ‖(a : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2)

def Saturated (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ h, GlobalTheory.Hk3.IsOpsV R i t h → ∀ s, HasString R i t s → ∃ c, ∀ y, IsEigV R i t h s y → GoodVt R i t y →
    ∃ x : (R.HW i (sg0 D A)).H, (R.HW i (sg0 D A)).e x ∈ partW R i t c ⊓ R.Wat i (sg0 D A) R.triv ∧
      LinearMap.adjoint (R.thG i t) x = y

end GlobalTheory.DownLift

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableTrivChar
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC

namespace GlobalTheory.BcSpeh

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n c : ℕ}

structure Parts (π : Submodule ℂ (UA E n → ℂ)) (a d : Fin c → ℕ) (h : ∑ i, d i * a i = n) (P : ∀ i, CuspSub E (a i))
    (ρ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (a i)) (m : Fin c → (E →+* ℂ) → Multiset ℂ) : Prop where

  pos : ∀ i, 1 ≤ a i ∧ 1 ≤ d i

  csd : ∀ i, (P i).IsCsd

  loc : ∀ i w, (P i).IsLocComp w (ρ i w)

  inf : ∀ i τ, (P i).HasInfChar τ (m i τ)

  weight : ∀ τ lam, HasWeightAt π τ lam → ∑ i, spehInf (d i) (m i τ) = infOfWeight lam

  distinct : ∀ i j, d i = d j → (⟨a i, CG.mk (P i)⟩ : Σ b, CG E b) = ⟨a j, CG.mk (P j)⟩ → i = j

  inert : ∀ (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ),
    (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → Formalism.UG.IsUnramInv ϖ s q →
    ∀ α, HasSatAt π w s ϖ q α → ∃ S : Fin c → Multiset ℂˣ, (∀ i, GlobalTheory.LFun.HasSatGL w (ρ i w).ρ (S i)) ∧
      ∑ i, ∑ k : Fin (d i), (S i).map (fun z => (z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((d i : ℂ) - 1) / 2 - (k : ℕ))) =
        (GlobalTheory.LGrp.bcParam n α).map (fun z => (z : ℂ))

def BcSpeh : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π →
      ∃ (c : ℕ) (a d : Fin c → ℕ) (h : ∑ i, d i * a i = n) (P : ∀ i, CuspSub E (a i)) (ρ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (a i))
        (m : Fin c → (E →+* ℂ) → Multiset ℂ) (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (d i * a i)), Parts π a d h P ρ m ∧
        (∀ i w, IsUnitarisable (ρ i w).ρ ∧ IsUnitarisable (σ i w).ρ ∧ GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of (ρ i w).ρ (ρ i w).smooth (ρ i w).irred) (d i) (σ i w).ρ) ∧
        ∀ w, IsSplitAt w → IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd h w (σ · w))

end GlobalTheory.BcSpeh
end
end
