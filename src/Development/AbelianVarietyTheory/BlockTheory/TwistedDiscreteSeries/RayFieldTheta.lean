module

public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RayFieldTheta
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ContainsRayField {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (φ : K →+* L) (M : ℕ) : Prop :=
  ∀ 𝔓 : HeightOneSpectrum (𝓞 L), ((M : ℕ) : 𝓞 L) ∉ 𝔓.asIdeal →
    ∃ (f : ℕ) (α : 𝓞 K),
      Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm (𝔓.asIdeal.comap (RingOfIntegers.mapRingHom φ)) ^ f ∧
      (𝔓.asIdeal.comap (RingOfIntegers.mapRingHom φ)) ^ f = Ideal.span {α} ∧ ((M : ℕ) : 𝓞 K) ∣ α - 1

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Tuple

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)


variable (D) in
def embK : D.host.K →+* D.what₂.LL := D.embE.comp (algebraMap D.host.K D.host.E)

def tupLevel (t : T0) : ℕ :=
  D.host.g 0 * D.host.g 1 * ∏ q ∈ (R.Q t).image (fun PP => Nat.card (kP PP)), q

def RatAt (i : Fin D.R.m) (ph : ℂ) (t : T0) : Prop :=
  ∀ x₀ : A.fam.amb.FL i t, ∃ y : Fin (R.nW i) → D.what₂.LL,
    (R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) y) = ph • R.thF i t (R.jV i t x₀) ∧
    ph • R.thG i t (R.jV i t x₀) =
      (R.FW i).j (sg0 D A) ((R.FW i).eOp (fun g => (idemOf A.X).coeff g) y)

theorem proj_clause (i : Fin D.R.m) (ph : ℂ) (t : T0) (hG : R.thP_thG)
    (hinj : Function.Injective (R.HW i (sg0 D A)).e)
    (hρ : RhoIs (sg0 D A) ((R.FW i).j (sg0 D A)) (R.HW i _).e (actW R i _) (R.FW i).chi (R.FW i).ρ)
    (x : (R.HV i t).H) (y : Fin (R.nW i) → D.what₂.LL)
    (h : (R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) y) = ph • R.thF i t x) :
    ph • R.thG i t x = (R.FW i).j (sg0 D A) ((R.FW i).eOp (fun g => (idemOf A.X).coeff g) y) := by
  apply hinj
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_smul, hG i t x, ← map_smul, ← h, Arith.FormsL.eOp, LinearMap.sum_apply, map_sum, map_sum]
  have key : ∀ g : G, (R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A)
      ((((idemOf A.X).coeff g * (((R.FW i).chi g)⁻¹ : D.what₂.LLˣ)) • (R.FW i).ρ g) y)) =
      RealDat.eC (A := A) (sg0 D A) g • actW R i _ g ((R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) y)) := by
    intro g
    rw [LinearMap.smul_apply, map_smulₛₗ, map_smul, hρ g y, smul_smul, ← map_mul, mul_assoc, Units.inv_mul, mul_one]
    rfl
  rw [Finset.sum_congr rfl fun g _ => key g]
  generalize (R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) y) = Φ
  ext v h
  simp [RealDat.eWf, gaL, actW, postOn, LinearMap.sum_apply, Finset.sum_apply]
  first | rfl | exact Finset.sum_congr rfl fun _ _ => rfl

end Tuple

end GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Doubling
open MeasureTheory Matrix
open scoped TensorProduct ContDiff ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def resL (A B : HSp D) (x : WO (dblSp A) B) : WO A B := Matrix.of fun i j => x i (finSumFinEquiv (Sum.inl j))

def resR (A B : HSp D) (x : WO (dblSp A) B) : WO A B := Matrix.of fun i j => x i (finSumFinEquiv (Sum.inr j))

def lagr (A B : HSp D) (w : WO A B) : WO (dblSp A) B :=
  Matrix.of fun i j => Sum.elim (fun k => w i k) (fun k => -w i k) (finSumFinEquiv.symm j)

def delta (A B : HSp D) (f₁ f₂ : WO A B → ℂ) : WO (dblSp A) B → ℂ :=
  fun x => f₁ (resL A B x) * conj (f₂ (-resR A B x))

def ip (A B : HSp D) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)) (f₁ f₂ : WO A B → ℂ) : ℂ :=
  ∫ w in 𝓕, f₁ w * conj (f₂ w) ∂ν

def evZero (A B : HSp D) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)) (φ : WO (dblSp A) B → ℂ) : ℂ :=
  ∫ w in 𝓕, φ (lagr A B w) ∂ν

def swSec (A B : HSp D) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ))
    (ν : Measure (WO A B)) (𝓕 : Set (WO A B)) (φ : WO (dblSp A) B → ℂ) : GA D (dblSp A) → ℂ :=
  fun g => evZero A B ν 𝓕 (omh (g, 1) φ)

def sZero (A B : HSp D) : ℂ := ((B.rank : ℂ) - (A.rank : ℂ)) / 2

def IsKFinVec {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (K : Subgroup (GA D S))
    (φ : WO S T → ℂ) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ {f : WO S T → ℂ | ∃ k ∈ K, f = om (k, 1) φ})

def IsSmoothOn (V : HSp D) (Φ : GA D V → ℂ) : Prop :=
  Continuous Φ ∧
  (∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → ∀ g, Φ (g * k) = Φ g) ∧
  ∀ θ : InfFam D, IsInfFam θ →
    ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
        ContDiff ℝ ∞ fun t : Fin k → ℝ => Φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)

section Clauses

variable (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle)
  (om : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ))
  (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ))

def ThetaClause : Prop :=
  ∀ f₁ f₂, IsThetaFunO ψ A B f₁ → IsThetaFunO ψ A B f₂ →
    IsThetaFunO ψ (dblSp A) B (delta A B f₁ f₂) ∧
    ∀ (g₁ g₂ : GA D A) (h : GA D B),
      omh (io A (g₁, g₂), h) (delta A B f₁ f₂) =
        (((χB (detA A g₂))⁻¹ : Circle) : ℂ) • delta A B (om (g₁, h) f₁) (om (g₂, h) f₂) ∧
      thetaKO omh (io A (g₁, g₂)) h (delta A B f₁ f₂) =
        thetaKO om g₁ h f₁ * conj (thetaKO om g₂ h f₂) * (((χB (detA A g₂))⁻¹ : Circle) : ℂ)

variable (ν : Measure (WO A B)) (𝓕 : Set (WO A B))

def SectionClause : Prop :=
  ∀ φ, IsThetaFunO ψ (dblSp A) B φ →
    IntegrableOn (fun w => φ (lagr A B w)) 𝓕 ν ∧
    (∀ h : GA D B, evZero A B ν 𝓕 (omh (1, h) φ) = evZero A B ν 𝓕 φ) ∧
    (∀ (p : siegel A) (g : GA D (dblSp A)), swSec A B omh ν 𝓕 φ (p * g) =
      (χB⁻¹ (aP A p) : Circle) * npow (absA D (aP A p)) (sZero A B + (A.rank : ℂ) / 2) * swSec A B omh ν 𝓕 φ g) ∧
    IsSmoothOn (dblSp A) (swSec A B omh ν 𝓕 φ) ∧
    ∀ a : GL (Fin A.rank) (AE D), IsMaj A a → IsKFinVec omh (Khat A a) φ →
      swSec A B omh ν 𝓕 φ ∈ degPS A a χB⁻¹ (sZero A B)

def CoefClause : Prop :=
  ∀ f₁ f₂, IsThetaFunO ψ A B f₁ → IsThetaFunO ψ A B f₂ →
    evZero A B ν 𝓕 (delta A B f₁ f₂) = ip A B ν 𝓕 f₁ f₂ ∧
    ∀ g : GA D A, swSec A B omh ν 𝓕 (delta A B f₁ f₂) (io A (g, 1)) = ip A B ν 𝓕 (om (g, 1) f₁) f₂

end Clauses

def DoublingIso (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle)
    (om : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)), IsWeilDatumO ψ A B χA χB om →
    ∃ omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ),
      IsWeilDatumO ψ (dblSp A) B 1 χB omh ∧ ThetaClause ψ A B χB om omh ∧
      AllSome (fun m : Measure (WO A B) × Set (WO A B) => IsCovolOne (ratL B A) m.1 m.2) fun m =>
        SectionClause ψ A B χB omh m.1 m.2 ∧ CoefClause ψ A B om omh m.1 m.2

section Basic₂

variable (A B : HSp D)

@[simp] theorem resL_lagr (w : WO A B) : resL A B (lagr A B w) = w := by
  ext i j; simp [resL, lagr]

@[simp] theorem resR_lagr (w : WO A B) : resR A B (lagr A B w) = -w := by
  ext i j; simp only [resR, lagr, Matrix.of_apply, Equiv.symm_apply_apply, Sum.elim_inr, Matrix.neg_apply]

theorem delta_lagr (f₁ f₂ : WO A B → ℂ) (w : WO A B) : delta A B f₁ f₂ (lagr A B w) = f₁ w * conj (f₂ w) := by
  simp [delta]

theorem evZero_delta (ν : Measure (WO A B)) (𝓕 : Set (WO A B)) (f₁ f₂ : WO A B → ℂ) :
    evZero A B ν 𝓕 (delta A B f₁ f₂) = ip A B ν 𝓕 f₁ f₂ := by
  simp only [evZero, ip, delta_lagr]

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalHeckeScalars
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.FWT Formalism.L2.Pj

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Local

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def heckeScalar (i : Fin D.R.m) (P : Pl D.host.E) (k : ℕ) : ℂ :=
  (((R.C.mu0 i).val P : ℂˣ) : ℂ) ^ (-(k : ℤ)) * ((Nat.card (kP P) : ℕ) : ℂ) ^ (-((k * (D.R.nV / 2) : ℕ) : ℤ))

def GoodPlace (P : Pl D.host.E) : Prop :=
  Bridge.SplitOff P (R.Sb : Set (Pl D.host.E)) ∧ ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal

def IsCosetSys (i : Fin D.R.m) (P : Pl D.host.E) (k : ℕ) (Rc : Finset (GA D (Wc D i))) : Prop :=
  ∃ α : GA D (Wc D i), IsHeckeAt (Wc D i) P k α ∧ Bridge.IsDC (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc

def ReadAs (i : Fin D.R.m) (P : Pl D.host.E) (k : ℕ) (Rc : Finset (GA D (Wc D i)))
    (hL : (Fin (R.nW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)) : Prop :=
  HeckeJ.IsHkJ (sg0 D A) ((R.FW i).j (sg0 D A)) (R.HW i (sg0 D A)).e (heckeOn (R.MW i (sg0 D A)) Rc) (heckeScalar R i P k) hL

def RationalHeckeAt (i : Fin D.R.m) (P : Pl D.host.E) (k : ℕ) : Prop :=
  ∃ hL : (Fin (R.nW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL),
    (∀ Rc, IsCosetSys R i P k Rc → ReadAs R i P k Rc hL) ∧ ∀ x ∈ (R.FW i).WK, hL x ∈ (R.FW i).WK

def RationalHecke (i : Fin D.R.m) : Prop :=
  ∀ P : Pl D.host.E, GoodPlace R P → ∀ k : ℕ, k ≤ D.R.r → RationalHeckeAt R i P k

theorem readAs_iff (i : Fin D.R.m) (P : Pl D.host.E) (k : ℕ) (Rc : Finset (GA D (Wc D i)))
    (hL : (Fin (R.nW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)) :
    ReadAs R i P k Rc hL ↔ ∀ x, (R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) (hL x)) =
      heckeScalar R i P k • heckeOn (R.MW i (sg0 D A)) Rc ((R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) x)) := Iff.rfl

theorem heckeScalar_zero (i : Fin D.R.m) (P : Pl D.host.E) : heckeScalar R i P 0 = 1 := by
  simp [heckeScalar]

end Local

section Comparison₂

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

end Comparison₂

end GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeSupportLattices
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Arith Formalism.IndefR.Mult
  Formalism.IndefR.FWT Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Forms

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  {G : Type} [Group G] [Fintype G] (Φ : FormsL LL Ks WL W G)

def ball (la : HeightOneSpectrum (𝓞 Ks)) : Set Φ.WK := {f | ∀ y : Φ.Pt la, Φ.nrm la y f ≤ 1}

def resW (hL : WL →ₗ[LL] WL) (hW : ∀ x ∈ Φ.WK, hL x ∈ Φ.WK) : Φ.WK →ₗ[Ks] Φ.WK :=
  (hL.restrictScalars Ks).restrict hW

def LiesOver (la : HeightOneSpectrum (𝓞 Ks)) {K' : Type} [Field K'] [Algebra Ks K'] (O : ValuationSubring K') : Prop :=
  ∀ x : Ks, algebraMap Ks K' x ∈ O ↔ FinitePlace.mk la x ≤ 1

def latK (la : HeightOneSpectrum (𝓞 Ks)) {K' : Type} [Field K'] [Algebra Ks K'] (O : ValuationSubring K') :
    Submodule O (K' ⊗[Ks] Φ.WK) :=
  Submodule.span O ((fun f : Φ.WK => (1 : K') ⊗ₜ[Ks] f) '' ball Φ la)

def latKIn (la : HeightOneSpectrum (𝓞 Ks)) {K' : Type} [Field K'] [Algebra Ks K'] (O : ValuationSubring K')
    (V : Submodule LL WL) : Submodule O (K' ⊗[Ks] Φ.WK) :=
  latK Φ la O ⊓ (((V.restrictScalars Ks).comap Φ.WK.subtype).baseChange K').restrictScalars O

def latL (la : HeightOneSpectrum (𝓞 Ks)) {K' : Type} [Field K'] [Algebra LL K'] (O : ValuationSubring K') :
    Submodule O (K' ⊗[LL] WL) :=
  Submodule.span O ((fun f : Φ.WK => (1 : K') ⊗ₜ[LL] (f : WL)) '' ball Φ la)

def latLIn (la : HeightOneSpectrum (𝓞 Ks)) {K' : Type} [Field K'] [Algebra LL K'] (O : ValuationSubring K')
    (V : Submodule LL WL) : Submodule O (K' ⊗[LL] WL) :=
  latL Φ la O ⊓ (V.baseChange K').restrictScalars O

structure Keeps (la : HeightOneSpectrum (𝓞 Ks)) (hL : WL →ₗ[LL] WL) (hW : ∀ x ∈ Φ.WK, hL x ∈ Φ.WK) : Prop where

  sup : ∀ f : Φ.WK, (∀ y : Φ.Pt la, Φ.nrm la y f ≤ 1) → ∀ y : Φ.Pt la, Φ.nrm la y ⟨hL f, hW f f.2⟩ ≤ 1

  rho : ∀ g : G, hL ∘ₗ Φ.ρ g = Φ.ρ g ∘ₗ hL

  eOp : ∀ eC : G → LL, hL ∘ₗ Φ.eOp eC = Φ.eOp eC ∘ₗ hL

  typeP : ∀ (J : Subgroup G) (lam : J →* LLˣ), ∀ x ∈ Φ.typeP J lam, hL x ∈ Φ.typeP J lam

  good : ∀ eC : G → LL, ∀ x ∈ Φ.good eC, hL x ∈ Φ.good eC

  overK : ∀ (K' : Type) [Field K'] [Algebra Ks K'] (O : ValuationSubring K'), LiesOver la O →
    (∀ x ∈ latK Φ la O, (resW Φ hL hW).baseChange K' x ∈ latK Φ la O) ∧
    ∀ (J : Subgroup G) (lam : J →* LLˣ),
      (∀ x ∈ latKIn Φ la O (Φ.typeP J lam), (resW Φ hL hW).baseChange K' x ∈ latKIn Φ la O (Φ.typeP J lam)) ∧
      ∀ eC : G → LL, ∀ x ∈ latKIn Φ la O (Φ.Wgood J lam eC),
        (resW Φ hL hW).baseChange K' x ∈ latKIn Φ la O (Φ.Wgood J lam eC)

  overL : ∀ (K' : Type) [Field K'] [Algebra LL K'] [Algebra Ks K'] [IsScalarTower Ks LL K'] (O : ValuationSubring K'),
    LiesOver la O →
    (∀ x ∈ latL Φ la O, hL.baseChange K' x ∈ latL Φ la O) ∧
    ∀ (J : Subgroup G) (lam : J →* LLˣ),
      (∀ x ∈ latLIn Φ la O (Φ.typeP J lam), hL.baseChange K' x ∈ latLIn Φ la O (Φ.typeP J lam)) ∧
      ∀ eC : G → LL, ∀ x ∈ latLIn Φ la O (Φ.Wgood J lam eC), hL.baseChange K' x ∈ latLIn Φ la O (Φ.Wgood J lam eC)

end Forms

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

def hkC {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) : ℂ :=
  ((((R.C.mu0 i).val P : ℂˣ) : ℂ) ^ k)⁻¹ * (((Nat.card (kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹

def IsHkData {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))) : Prop :=
  Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) ∧
    ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ k ≤ D.R.r ∧
    IsHeckeAt (Wc D i) P k α ∧ Bridge.IsDC (Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc

def OffChar {Ks : Type} [Field Ks] [NumberField Ks] (P : Formalism.L2.DIV.Pl D.host.E) (la : HeightOneSpectrum (𝓞 Ks)) : Prop :=
  ∀ p : ℕ, p.Prime → (p : 𝓞 D.host.E) ∈ P.asIdeal → (p : 𝓞 Ks) ∉ la.asIdeal

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

def ConstPinned (i : Fin D.R.m) : Prop :=
  ∃ (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : ℂ),
    O.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange ∧
    O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) ∧
    O.OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) O.s0) ph

theorem constPinned_of (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m) (hp : OMPins T R κ v₀ O i)
    (hr : OneMapRow0 T R κ v₀ O i) (hc : CTie T R κ v₀ O i) : ConstPinned T R κ v₀ i :=
  ⟨O i, (hc hr).choose, hp.1, hp.2, (hc hr).choose_spec⟩

structure ReadAt0 (i : Fin D.R.m) : Prop where
  ex : ∀ hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i, JEvAt T R κ v₀ i (sg0 D A) hV
  inj : Function.Injective ((R.FW i).j (sg0 D A))
  rho : RhoIs (sg0 D A) ((R.FW i).j (sg0 D A)) (R.HW i (sg0 D A)).e (actW R i (sg0 D A)) (R.FW i).chi (R.FW i).ρ
  const : ConstPinned T R κ v₀ i

theorem readAt0_of (hj : JEvExists T R κ v₀) (fw : FWTie T R κ v₀) (hu : R.LUnif) (i : Fin D.R.m)
    (hc : ConstPinned T R κ v₀ i) : ReadAt0 T R κ v₀ i := by
  refine ⟨fun hV => hj i _ (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1) hV,
    ?_, (hu i (sg0 D A)).2.2, hc⟩
  refine (injective_iff_map_eq_zero ((R.FW i).j (sg0 D A))).2 fun x hx => ?_
  by_contra h
  have h1 := (hu i (sg0 D A)).1 1 (fun _ => x) (linearIndependent_unique_iff.2 h)
  exact h1.ne_zero 0 hx

def HkSupAt (i : Fin D.R.m) : Prop :=
  ∀ (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))), IsHkData R i P k α Rc →
    ∀ (hL : (Fin (R.nW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)),
      HeckeJ.IsHkJ (sg0 D A) ((R.FW i).j (sg0 D A)) (R.HW i (sg0 D A)).e (heckeOn (R.MW i (sg0 D A)) Rc) (hkC R i P k) hL →
      ∀ (hW : ∀ x ∈ (R.FW i).WK, hL x ∈ (R.FW i).WK) (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OffChar P la →
        Keeps (R.FW i) la hL hW

end GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory GlobalTheory.Doubling
open scoped TensorProduct ENNReal NNReal ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def schwartzA (θ : InfFam D) (m n : ℕ) : Submodule ℂ (Mx D m n → ℂ) :=
  Submodule.span ℂ {φ | ∃ (f : SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ)
    (g : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ),
      g ∈ WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) ∧
      φ = fun x => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))}

variable (A B : HSp D)

def cols (x y : WO A B) : WO (dblSp A) B := (Matrix.fromCols x y).submatrix id finSumFinEquiv.symm

def fstCols (w : WO (dblSp A) B) : WO A B := w.submatrix id fun j => finSumFinEquiv (Sum.inl j)

def sndCols (w : WO (dblSp A) B) : WO A B := w.submatrix id fun j => finSumFinEquiv (Sum.inr j)

def half (D : D7) : AE D := incA D (1 / 2)

def onX (x : WO A B) : WO (dblSp A) B := cols A B (half D • x) (half D • x)

def onY (y : WO A B) : WO (dblSp A) B := cols A B y (-y)

def xOf (w : WO (dblSp A) B) : WO A B := fstCols A B w + sndCols A B w

def yOf (w : WO (dblSp A) B) : WO A B := half D • (fstCols A B w - sndCols A B w)

variable {A B}

def thetaInt (om : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)) (μ : Measure (GA D B)) (𝓕 : Set (GA D B))
    (f₁ f₂ : WO A B → ℂ) (g₁ g₂ : GA D A) : ℝ≥0∞ :=
  ∫⁻ h in 𝓕, ‖thetaKO om g₁ h f₁ * thetaKO om g₂ h f₂‖ₑ ∂μ

abbrev ht (V : HSp D) (g : GA D V) : ℝ≥0 := AdelicU.height D.sp.cm.sig V.gram g

variable (A B)

def InRange : Prop := 1 ≤ A.rank ∧ A.rank < B.rank ∧ (Cusp.wittIndex B = 0 ∨ A.rank + Cusp.wittIndex B < B.rank)

theorem half_add_half : half D + half D = 1 := by
  rw [half, ← map_add (f := _), add_halves, map_one]

theorem fstCols_cols (x y : WO A B) : fstCols A B (cols A B x y) = x := by
  ext i j; simp [fstCols, cols]

theorem sndCols_cols (x y : WO A B) : sndCols A B (cols A B x y) = y := by
  ext i j; simp only [sndCols, cols, Matrix.submatrix_apply, Equiv.symm_apply_apply]; rfl

theorem coords (x y : WO A B) : xOf A B (onX A B x) = x ∧ yOf A B (onX A B x) = 0 ∧
    xOf A B (onY A B y) = 0 ∧ yOf A B (onY A B y) = y := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [xOf, yOf, onX, onY, fstCols_cols, sndCols_cols]
  · rw [← add_smul, half_add_half, one_smul]
  · simp
  · simp
  · rw [sub_neg_eq_add, smul_add, ← add_smul, half_add_half, one_smul]

end GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CommutingRationalGroups
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult NumberField

namespace GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

abbrev levV (i : Fin D.R.m) (t : T) : Bridge.LevDat D (Vc D i) := levEnv (Vc D i) (R.βV i) (R.datVt i t)

def IsLiftV (i : Fin D.R.m) (t : T) (g : G) (κ : (levV R i t).Q) : Prop :=
  rTup (R.βV i) (R.datVt i t) (Formalism.UG.bc (swapAE D) ((κ : Bridge.Gf (Vc D i)) : GL _ _)) = R.eG g

def IsAlgV (i : Fin D.R.m) (t : T) (c : G → ℂ) (κ : G → (levV R i t).Q) (x y : (R.HV i t).H) : Prop :=
  (R.HV i t).e y = ∑ g, c g • Bridge.g0Act (levV R i t).ch (κ g) ((R.HV i t).e x)

def algW (i : Fin D.R.m) (c : G → ℂ) : MMap (R.MW i (sg0 D A)) →ₗ[ℂ] MMap (R.MW i (sg0 D A)) :=
  postOn _ (gaL (Wc D i) (R.βW i) (R.datWp i R.triv) R.eG c)

theorem algW_eC (i : Fin D.R.m) :
    algW R i (RealDat.eC (A := A) (sg0 D A)) = postOn _ (R.eWf i (sg0 D A)) := rfl

end GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups

end
end
