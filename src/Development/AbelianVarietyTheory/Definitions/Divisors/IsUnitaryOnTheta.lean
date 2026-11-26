module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableToGLEntry

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Kronecker

namespace GlobalTheory.WeilParts

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def NonSplitAt (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F) : Prop :=
  IsPlaceIdem D v ε ∧ ¬ ∃ e : AE D, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε

def SuppPl (ε : AF D.host.F) (V : HSp D) (g : GA D V) : Prop :=
  ∀ i j, algebraMap (AF D.host.F) (AE D) ε * (Formalism.L2.Theta.mt V g - 1) i j = (Formalism.L2.Theta.mt V g - 1) i j

def UnramAt (ε : AF D.host.F) (χ : (AE D)ˣ →* Circle) : Prop :=
  ∀ x : (AE D)ˣ, algebraMap (AF D.host.F) (AE D) ε * ((x : AE D) - 1) = (x : AE D) - 1 →
    finPart D (x : AE D) ∈ intAE D → finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → χ x = 1

def FixesVacAt (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F) : Prop :=
  ∀ g h, SuppPl ε S g → SuppPl ε T h →
    (∀ u, u ∈ (latO S T ΛS ΛT fun w => w = v) ↔ actO S T g h u ∈ (latO S T ΛS ΛT fun w => w = v)) →
    ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ (latO S T ΛS ΛT fun w => w = v), heisO ψ S T u f = f) → om (g, h) f = f

def detPlus {m n : ℕ} (sS : Matrix (Fin n) (Fin n) ℂ) (sT : Matrix (Fin m) (Fin m) ℂ) (a' : Matrix (Fin n) (Fin n) ℂ)
    (b : Matrix (Fin m) (Fin m) ℂ) : ℂ :=
  ((1 / 2 : ℂ) • ((1 + sT ⊗ₖ sSᵀ) * (b ⊗ₖ a'ᵀ)) + (1 / 2 : ℂ) • (1 - sT ⊗ₖ sSᵀ)).det

def VacCharPlus (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop :=
  ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ),
    (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) →
    ∀ g ∈ GinfC S, ∀ h ∈ GinfC T,
      (∀ τ, sS τ * compAt θ τ (Formalism.L2.Theta.mt S g) = compAt θ τ (Formalism.L2.Theta.mt S g) * sS τ) →
      (∀ τ, sT τ * compAt θ τ (Formalism.L2.Theta.mt T h) = compAt θ τ (Formalism.L2.Theta.mt T h) * sT τ) →
      ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) →
        om (g, h) f = (∏ τ, detPlus (sS τ) (sT τ) (compAt θ τ (Formalism.L2.Theta.mt S g⁻¹)) (compAt θ τ (Formalism.L2.Theta.mt T h))) • f

structure IsUnitaryOnTheta (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop where
  pres : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (om p f)
  cont : ∀ f, IsThetaFunO ψ S T f → ∀ w, Continuous fun p : GA D S × GA D T => om p f w
  unit : ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ p f, IsThetaFunO ψ S T f →
      ∫⁻ w in 𝓕, ‖om p f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ

structure IsFinWeil (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop extends IsUnitaryOnTheta ψ S T om where
  triv : ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, ∀ f, IsThetaFunO ψ S T f → om (g, h) f = f
  Heisenberg₂ : ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ w₀ f, IsThetaFunO ψ S T f →
    om (g, h) (heisO ψ S T w₀ f) = heisO ψ S T (actO S T g h w₀) (om (g, h) f)
  split : ∀ e, IsSplitIdem D e → ∀ g h, SuppAt e S g → SuppAt e T h → ∀ x y, IsDetAt e S g x → IsDetAt e T h y →
    ∃ r : ℝ, 0 < r ∧ ∀ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) →
      ∀ f, IsThetaFunO ψ S T f → ℓ (om (g, h) f) = (r : ℂ) * (splitFacO χS χT x y : ℂ) * ℓ f
  inert : ∀ v ε, NonSplitAt D v ε → FixesVacAt ψ S T ΛS ΛT om v ε

structure IsInfWeil (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop extends IsUnitaryOnTheta ψ S T om where
  triv : ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ f, IsThetaFunO ψ S T f → om (g, h) f = f
  Heisenberg₂ : ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, ∀ w₀ f, IsThetaFunO ψ S T f →
    om (g, h) (heisO ψ S T w₀ f) = heisO ψ S T (actO S T g h w₀) (om (g, h) f)
  vac : VacCharPlus ψ θ S T om

def IsEtaTilde (D : D7) (η : (AE D)ˣ →* Circle) : Prop :=
  IsHeckeChar D η ∧ UnramEverywhere D η ∧ ResEta D η 1 ∧ ∀ τ, HasInfExp D η τ (1 / 2)

end GlobalTheory.WeilParts

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical

namespace GlobalTheory.AdTh

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {r g : ℕ}

structure IsMod (W : HSp D) (hr : W.rank = r) (X : Data D.host.E r) : Prop where
  model : Formalism.L2.Pj.ModelW W hr X
  psi : ∀ τ : D.host.E →+* ℂ, τ ∈ X.Ψ ↔ ∃ ρ, τ = tauE D ρ
  kap : X.κ0 = -(2 * D.host.xi0)

def realM (θ : InfFam D) {m n : ℕ} (w : Mx D m n) (τ : D.host.E →+* ℂ) : Matrix (Fin m) (Fin n) ℂ :=
  if h : ∃ ρ, τ = tauE D ρ then compAt θ h.choose w else 0

def perC {E : Type} [Field E] [NumberField E] [IsCMField E] (X : Data E r) (x : Frame X.Ψ r) (u : X.Ψ → Fin r → ℂ) :
    X.Ψ × Fin r → ℂ := fun p =>
  if (p.2 : ℕ) < X.p0 then hermC p.1.1 X.Gm (FD.col (mat x p.1) p.2) (u p.1) else ((mat x p.1)⁻¹ *ᵥ u p.1) p.2

def zOf (θ : InfFam D) (V W : HSp D) (hr : W.rank = r) (X : Data D.host.E r) (idx : Fin g ≃ X.Ψ × Fin r)
    (x : Frame X.Ψ r) (w : WO V W) : Fin V.rank → Fin g → ℂ := fun b j =>
  perC X x (fun τ a => realM θ w τ.1 (Fin.cast hr.symm a) b) (idx j)

def Reads (θ : InfFam D) (V W : HSp D) (hr : W.rank = r) (X : Data D.host.E r)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (f : WO V W → ℂ) (φ : TF V.rank g)
    (x : Frame X.Ψ r) : Prop :=
  GlobalTheory.SW.IsSB φ ∧ ∀ w : WO V W, w.map (finPart D) = 0 →
    f w = cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx X bas idx x (zOf θ V W hr X idx x w b) (zOf θ V W hr X idx x w b)) *
      thA X bas idx φ x (zOf θ V W hr X idx x w)

def colsR {E : Type} {m n : ℕ} (hr : m = r) (γ : Matrix (Fin m) (Fin n) E) : Matrix (Fin n) (Fin r) E :=
  fun b a => γ (Fin.cast hr.symm a) b

def IsFinOf (V W : HSp D) (γ : Matrix (Fin W.rank) (Fin V.rank) D.host.E) (u : WO V W) : Prop :=
  u.map (infPart D) = 0 ∧ u.map (finPart D) = (ratW W V γ).map (finPart D)

def IsONFr {E : Type} [Field E] [NumberField E] [IsCMField E] (X : Data E r) (x : Frame X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) = sgnM X

def IsInvOf (W : HSp D) (hr : W.rank = r) (X : Data D.host.E r) (x : Frame X.Ψ r)
    (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) : Prop :=
  ∀ (ρ : D.what₂.Tau) (τ : X.Ψ), τ.1 = tauE D ρ →
    Matrix.reindex (finCongr hr) (finCongr hr) (s ρ) * mat x τ = -(mat x τ * sgnM X)

def frMove (θ : InfFam D) (W : HSp D) (hr : W.rank = r) (X : Data D.host.E r) (h : GA D W) (x : Frame X.Ψ r) :
    Frame X.Ψ r := fun τ =>
  (Matrix.reindex (finCongr hr) (finCongr hr) (realM θ (Formalism.L2.Theta.mt W h) τ.1) * mat x τ : Matrix (Fin r) (Fin r) ℂ)

def latR {E : Type} [Field E] [NumberField E] {m : ℕ} (hr : m = r) (L : Submodule (𝓞 E) (Fin m → E)) : Lt E r :=
  L.map (LinearMap.funLeft (𝓞 E) E (Fin.cast hr.symm))

structure IsLatOf (V W : HSp D) (hr : W.rank = r) (Λ : AddSubgroup (WO V W))
    (A : AddSubgroup (Matrix (Fin V.rank) (Fin r) D.host.E)) : Prop where
  fin : ∀ u ∈ Λ, u.map (infPart D) = 0
  opn : ∃ U : Set (WO V W), IsOpen U ∧ ∀ u : WO V W, u.map (infPart D) = 0 → (u ∈ Λ ↔ u ∈ U)
  rat : ∀ γ u, IsFinOf V W γ u → (u ∈ Λ ↔ colsR hr γ ∈ A)

def IsVarOf (V W : HSp D) (X : Data D.host.E r) (q0 : ℕ)
    (vr : Harm.Var X.Ψ q0 X.p0 (Fin V.rank) ≃ FVar D W.rank V.rank) : Prop :=
  ∀ l, l.1.1 = tauE D (vr l).1 ∧ (vr l).2.2 = l.2.2 ∧
    ((vr l).2.1 : ℕ) = Sum.elim (fun i : Fin q0 => (i : ℕ)) (fun i : Fin X.p0 => q0 + (i : ℕ)) l.2.1

def IsBasOf (W : HSp D) (hr : W.rank = r) (X : Data D.host.E r) {q0 : ℕ} (hq : X.p0 + q0 = r) (x : Frame X.Ψ r)
    (B : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) : Prop :=
  ∀ (ρ : D.what₂.Tau) (τ : X.Ψ), τ.1 = tauE D ρ → ∀ (k : Fin q0 ⊕ Fin X.p0) (i a : Fin W.rank),
    (i : ℕ) = Sum.elim (fun i : Fin q0 => (i : ℕ)) (fun i : Fin X.p0 => q0 + (i : ℕ)) k →
      B ρ a i = x τ (Fin.cast hr a) (rowIdx hq k)

theorem perC_emb {E : Type} [Field E] [NumberField E] [IsCMField E] (X : Data E r) (x : Frame X.Ψ r) (v : Fin r → E) :
    perC X x (fun τ => Data.emb τ.1 v) = per X x v := rfl

end

end GlobalTheory.AdTh
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
open AlgebraicGeometry CategoryTheory Limits MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.LieHt

section Lat

variable {K : Type} [Field K] [NumberField K] {m : ℕ}

def Full (L : Submodule (𝓞 K) (Fin m → K)) : Prop := L.FG ∧ Submodule.span K (L : Set (Fin m → K)) = ⊤

variable (K' : Type) [Field K'] [NumberField K'] [Algebra K K']


end Lat

structure SemiFib (K : Type) [Field K] [NumberField K] : Type 1 where

  P₀ : Out.PolAV (Sp K)

  G : Over (Sp (𝓞 K))
  [grp : GrpObj G]
  semi : IsSemiAbelian G

  φ : P₀.A.left ⟶ G.left
  fib : IsGrpPullback P₀.A G (spMap (algebraMap (𝓞 K) K)) φ

  v : Fin P₀.g → (epsR K ⟶ P₀.A)
  basis : IsLieBasis v

attribute [instance] SemiFib.grp

namespace SemiFib

variable {K : Type} [Field K] [NumberField K] (F : SemiFib K)

def lieLat : Submodule (𝓞 K) (Fin F.P₀.g → K) := Submodule.span (𝓞 K)
  {c | ∃ u : epsR (𝓞 K) ⟶ F.G, IsTangent u ∧ ∃ w, IsVecOver (algebraMap (𝓞 K) K) F.φ u w ∧ IsLieComb c F.v w}

def IsUnif (s : K →+* ℂ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (W : Fin F.P₀.g → Fin g → ℂ) : Prop :=
  ∃ (Q : Out.PolAV (Sp ℂ)) (e : Q.g = g) (ψ : Q.A.left ⟶ F.P₀.A.left) (v' : Fin F.P₀.g → (epsR ℂ ⟶ Q.A))
    (u : HolUnif Q.A Q.L g) (χ : u.Λ → ℂ),
    IsPolFibre s F.P₀ Q ψ ∧ u.Λ = Λ ∧ u.IsAH Hm χ ∧ ∀ i, IsVecOver s ψ (F.v i) (v' i) ∧ u.IsDiff (W i) (v' i)

def IsHerm (h : HermFam K (Fin F.P₀.g → K)) : Prop :=
  ∀ s : K →+* ℂ, ∃ (Λ : Submodule ℤ (Fin F.P₀.g → ℂ)) (Hm : Matrix (Fin F.P₀.g) (Fin F.P₀.g) ℂ)
    (W : Fin F.P₀.g → Fin F.P₀.g → ℂ), F.IsUnif s Λ Hm W ∧
      ∀ i j, h.form s (Pi.single i 1) (Pi.single j 1) = Real.pi * hermForm Hm (W j) (W i)

def IsRho (ρ : (K →+* ℂ) → ℝ) : Prop :=
  ∀ s : K →+* ℂ, ∃ (Λ : Submodule ℤ (Fin F.P₀.g → ℂ)) (Hm : Matrix (Fin F.P₀.g) (Fin F.P₀.g) ℂ)
    (W : Fin F.P₀.g → Fin F.P₀.g → ℂ), F.IsUnif s Λ Hm W ∧
      IsLeast {t | ∃ z ∈ Λ, z ≠ 0 ∧ t = √(hermForm Hm z z).re} (ρ s)

end SemiFib

def SemiFib.ofGenFib {K : Type} [Field K] [NumberField K] {P : Out.PolAV (Sp (𝓞 K))} (hP : IsSemiAbelian P.A)
    (F : GlobalTheory.CM.GenFib P) : SemiFib K := ⟨F.P₀, P.A, hP, F.φ, F.fib.2.1, F.v, F.basis⟩

end GlobalTheory.LieHt
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
noncomputable section

namespace GlobalTheory.DefPt

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl MvPolynomial
open scoped Matrix

section Adelic

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] [DecidableEq ι]

def IntAt (w : HeightOneSpectrum (𝓞 K)) {κ : Type} (M : Matrix ι κ K) : Prop := ∀ i j, w.valuation K (M i j) ≤ 1

def IsAdelic (A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K) : Prop :=
  (∀ w, (A w).det ≠ 0) ∧ {w | ¬ (IntAt w (A w) ∧ IntAt w (A w)⁻¹)}.Finite

def locLat (A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K) : Submodule (𝓞 K) (ι → K) where
  carrier := {x | ∀ (w : HeightOneSpectrum (𝓞 K)) (i : ι), w.valuation K ((A w *ᵥ x) i) ≤ 1}
  zero_mem' := fun w i => by simp
  add_mem' := fun {x y} hx hy w i => by
    rw [Matrix.mulVec_add, Pi.add_apply]
    exact (Valuation.map_add _ _ _).trans (max_le (hx w i) (hy w i))
  smul_mem' := fun a x hx w i => by
    have h : a • x = (a : K) • x := by
      funext j
      simp [Algebra.smul_def]
    rw [h, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul]
    exact mul_le_one' (w.valuation_le_one a) (hx w i)

def matNorm (Y : (K →+* ℂ) → Matrix ι ι ℂ) (σ : K →+* ℂ) (x : ι → K) : ℝ :=
  Real.sqrt (∑ i, ‖(Y σ *ᵥ fun j => σ (x j)) i‖ ^ 2)

def detDeg (A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K) (Y : (K →+* ℂ) → Matrix ι ι ℂ) : ℝ :=
  GlobalTheory.FlatLine.lineDeg (fun σ => ‖(Y σ).det‖) (fun w => (vAdd w (A w).det : ℝ))

end Adelic

section Tensor

variable {T : Type} [Fintype T] [DecidableEq T] {N : T → ℕ} {n : ℕ}

abbrev TIdx (la : ∀ t, Fin (N t) → ℕ) : Type := ∀ t, Idx (la t)

def tval (la : ∀ t, Fin (N t) → ℕ) {S : Type} [CommRing S] (x : TIdx la → S) (y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) S) : S :=
  ∑ I : TIdx la, x I * ∏ t, evalAt (y t) (map (Int.castRingHom S) (intVec (la t) (I t)))

def rhoMat (la : Fin n → ℕ) {K : Type} [Field K] [CharZero K] (g : Matrix (Fin n) (Fin n) K) : Matrix (Idx la) (Idx la) K :=
  LinearMap.toMatrix (basis la K) (basis la K) (rho la K gᵀ)

def kron {J : T → Type} {R : Type} [CommRing R] (M : ∀ t, Matrix (J t) (J t) R) : Matrix (∀ t, J t) (∀ t, J t) R :=
  Matrix.of fun I I' => ∏ t, M t (I t) (I' t)

def onMat (la : Fin n → ℕ) : Matrix (Idx la) (Idx la) ℂ :=
  Matrix.of fun i j => (onBasis la).repr (toSpace la (basis la ℂ j)) i

def fibA (la : ∀ t, Fin (N t) → ℕ) {K : Type} [Field K] [CharZero K] (a : K) (B : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K) :
    Matrix (TIdx la) (TIdx la) K := a • kron fun t => rhoMat (la t) (B t)

def fibY (la : ∀ t, Fin (N t) → ℕ) (s : ℝ) (X : ∀ t, Matrix (Fin (N t)) (Fin (N t)) ℂ) : Matrix (TIdx la) (TIdx la) ℂ :=
  (s : ℂ) • kron fun t => onMat (la t) * rhoMat (la t) (X t)

end Tensor

end GlobalTheory.DefPt

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.MeasurableCompInfGL
noncomputable section

open NumberField IsDedekindDomain MeasureTheory

namespace GlobalTheory.JSW

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def htInf (y : GL (Fin a) (Cinf E)) : ℝ :=
  ∏ w : InfinitePlace E, htGL (Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w) y)

def kerInf {X : Type} [MeasurableSpace X] (ν : Measure X) (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E))
    (F : GA E a → ℂ) (g : GA E a) : ℂ := ∫ x, k x * F (g * infGL E a (γ x)) ∂ν

def rspan (π : CuspSub E a) : Submodule ℂ (GA E a → ℂ) :=
  sInf {S | (∀ φ ∈ π.V, φ.1 ∈ S) ∧ (∀ F ∈ S, ∀ h : GA E a, (fun g => F (g * h)) ∈ S) ∧
    (∀ F ∈ S, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ)
      (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → kerInf ν k γ F ∈ S)}

theorem mem_rspan {π : CuspSub E a} {φ : Sm E a} (h : φ ∈ π.V) : φ.1 ∈ rspan π :=
  Submodule.mem_sInf.2 fun _ hS => hS.1 φ h

theorem rt_mem_rspan {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ rspan π) (h : GA E a) :
    (fun g => F (g * h)) ∈ rspan π :=
  Submodule.mem_sInf.2 fun S hS => hS.2.1 F (Submodule.mem_sInf.1 hF S hS) h

theorem kerInf_mem_rspan {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ rspan π) {X : Type} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) :
    kerInf ν k γ F ∈ rspan π :=
  Submodule.mem_sInf.2 fun S hS => hS.2.2 F (Submodule.mem_sInf.1 hF S hS) X ν k γ hk

theorem rspan_le {π : CuspSub E a} {S : Submodule ℂ (GA E a → ℂ)} (h₁ : ∀ φ ∈ π.V, φ.1 ∈ S)
    (h₂ : ∀ F ∈ S, ∀ h : GA E a, (fun g => F (g * h)) ∈ S)
    (h₃ : ∀ F ∈ S, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ)
      (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → kerInf ν k γ F ∈ S) : rspan π ≤ S :=
  sInf_le ⟨h₁, h₂, h₃⟩

theorem one_le_htInf (y : GL (Fin a) (Cinf E)) : 1 ≤ htInf y := by
  unfold htInf
  calc (1 : ℝ) = ∏ _w : InfinitePlace E, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun w _ => one_le_htGL _

theorem htInf_pos (y : GL (Fin a) (Cinf E)) : 0 < htInf y := lt_of_lt_of_le one_pos (one_le_htInf y)

theorem htGL_le_htInf (y : GL (Fin a) (Cinf E)) (w : InfinitePlace E) :
    htGL (Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w) y) ≤ htInf y := by
  classical
  unfold htInf
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
  refine le_mul_of_one_le_right (htGL_pos _).le ?_
  calc (1 : ℝ) = ∏ _w ∈ Finset.univ.erase w, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun w _ => one_le_htGL _

theorem norm_entry_le_htInf (y : GL (Fin a) (Cinf E)) (i j : Fin a) (w : InfinitePlace E) :
    ‖(y : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ≤ htInf y ∧
      ‖((y⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ≤ htInf y := by
  set p : GL (Fin a) (Cinf E) →* GL (Fin a) ℂ := Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w)
  refine ⟨(norm_entry_le_htGL (p y) i j).trans (htGL_le_htInf y w), ?_⟩
  have e : ((y⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) i j w =
      (((p y)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j := by
    rw [← map_inv]; rfl
  rw [e]
  exact (norm_entry_le_htGL _ i j).trans ((htGL_inv (p y)).le.trans (htGL_le_htInf y w))

theorem height_le_htInf (y : GL (Fin a) (Cinf E)) : height y ≤ 3 * htInf y := by
  have h0 := (htInf_pos y).le
  have h1 : ‖toL y.val‖ ≤ htInf y :=
    pi_norm_le_iff_of_nonneg h0 |>.2 fun i => pi_norm_le_iff_of_nonneg h0 |>.2 fun j =>
      pi_norm_le_iff_of_nonneg h0 |>.2 fun w => (norm_entry_le_htInf y i j w).1
  have h2 : ‖toL (y⁻¹).val‖ ≤ htInf y :=
    pi_norm_le_iff_of_nonneg h0 |>.2 fun i => pi_norm_le_iff_of_nonneg h0 |>.2 fun j =>
      pi_norm_le_iff_of_nonneg h0 |>.2 fun w => (norm_entry_le_htInf y i j w).2
  unfold height
  linarith [one_le_htInf y]

theorem IsRapidInf.of_htInf {X : Type} [MeasurableSpace X] {ν : Measure X} {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)}
    (hk : Measurable k) (hγ : ∀ i j, Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E)) i j)
    (hm : ∀ N : ℕ, Integrable (fun x => ‖k x‖ * htInf (γ x) ^ N) ν) : IsRapidInf ν k γ := by
  refine ⟨hk, Measurable.of_eval fun i => Measurable.of_eval fun j => hγ i j, fun N => ?_⟩
  refine ((hm N).const_mul (3 ^ N)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · refine (hk.norm.mul ?_).aestronglyMeasurable
    have hm' : Measurable fun x => toL (γ x).val :=
      Measurable.of_eval fun i => Measurable.of_eval fun j => hγ i j
    have hi : Measurable fun x => toL ((γ x)⁻¹).val := by
      refine Measurable.of_eval fun i => Measurable.of_eval fun j => Measurable.of_eval fun w => ?_
      set p : GL (Fin a) (Cinf E) →* GL (Fin a) ℂ :=
        Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w)
      have e : (fun x => toL ((γ x)⁻¹).val i j w) =
          fun x => (((p (γ x))⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j := by
        funext x
        rw [← map_inv]; rfl
      rw [e]
      exact measurable_comp_GL (F := fun g : GL (Fin a) ℂ => ((g⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j)
        ((Units.continuous_coe_inv : Continuous fun g : GL (Fin a) ℂ =>
          ((g⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)).matrix_elem i j)
        fun i' j' => (measurable_pi_apply w).comp (hγ i' j')
    unfold height
    exact ((measurable_const.add hm'.norm).add hi.norm).pow_const N
  · have h0 : 0 ≤ height (γ x) := by unfold height; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖k x‖ * height (γ x) ^ N ≤ ‖k x‖ * (3 * htInf (γ x)) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (height_le_htInf _) N) (norm_nonneg _)
      _ = 3 ^ N * (‖k x‖ * htInf (γ x) ^ N) := by rw [mul_pow]; ring

theorem measurable_chart {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) (g : GA E a) : Measurable (chart φ g) := by
  classical
  have e : chart φ g = (invSet E a).piecewise (chart φ g) (fun _ => 0) := by
    funext x
    by_cases hx : x ∈ invSet E a
    · rw [Set.piecewise_eq_of_mem _ _ _ hx]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hx]
      exact dif_neg hx
  rw [e]
  exact (hφ g).continuousOn.measurable_piecewise continuousOn_const isOpen_invSet.measurableSet

theorem measurable_comp_infGL {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) (g : GA E a) {X : Type} [MeasurableSpace X]
    {γ : X → GL (Fin a) (Cinf E)} (hγ : Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E))) :
    Measurable fun x => φ (g * infGL E a (γ x)) := by
  have h : Measurable fun x => toL (γ x).val := hγ
  have e : (fun x => φ (g * infGL E a (γ x))) = fun x => chart φ g (toL (γ x).val) :=
    funext fun x => (chart_val φ g (γ x)).symm
  rw [e]
  exact (measurable_chart hφ g).comp h

theorem IsRapidInf.integrable {X : Type} [MeasurableSpace X] {ν : Measure X} {k : X → ℂ}
    {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) {g : GA E a}
    (hg : ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ (g * infGL E a y)‖ ≤ C * height y ^ N) :
    Integrable (fun x => k x * φ (g * infGL E a (γ x))) ν := by
  obtain ⟨C, N, hC⟩ := hg
  have hC0 : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hC 1)
    have hp : 0 < height (1 : GL (Fin a) (Cinf E)) ^ N := pow_pos (by unfold height; positivity) N
    exact nonneg_of_mul_nonneg_left h hp
  refine ((hk.2.2 N).const_mul C).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (hk.1.mul (measurable_comp_infGL hφ g hk.2.1)).aestronglyMeasurable
  · rw [norm_mul]
    calc ‖k x‖ * ‖φ (g * infGL E a (γ x))‖ ≤ ‖k x‖ * (C * height (γ x) ^ N) :=
          mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
      _ = C * (‖k x‖ * height (γ x) ^ N) := by ring

theorem rspan_ne_bot (π : CuspSub E a) : rspan π ≠ ⊥ := by
  obtain ⟨φ, hφ, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne_bot
  intro hb
  have h := mem_rspan hφ
  rw [hb, Submodule.mem_bot] at h
  exact h0 (Subtype.ext h)

theorem rspan_le_leftInv (π : CuspSub E a) : rspan π ≤ SpanModel.leftInv E a := by
  refine rspan_le (fun φ hφ => (π.cusp φ hφ).1.left) (fun F hF h γ g => ?_) fun F hF X _ ν _ k γ _ γ' g => ?_
  · change F (ratGL E a γ * g * h) = F (g * h)
    rw [mul_assoc]; exact hF γ _
  · change kerInf ν k γ F (ratGL E a γ' * g) = kerInf ν k γ F g
    simp only [kerInf, mul_assoc]
    congr 1
    funext x
    rw [hF γ']

theorem rspan_left (π : CuspSub E a) {F : GA E a → ℂ} (hF : F ∈ rspan π) (γ : GL (Fin a) E) (g : GA E a) :
    F (ratGL E a γ * g) = F g :=
  rspan_le_leftInv π hF γ g

theorem rspan_eq_mspanR (π : CuspSub E a) : rspan π = mspanR π := by
  refine le_antisymm (rspan_le ?_ ?_ ?_) ?_
  · exact fun φ hφ => Submodule.mem_sInf.2 fun _ hS => hS.1 φ hφ
  · exact fun F hF h => Submodule.mem_sInf.2 fun S hS => hS.2.1 F (Submodule.mem_sInf.1 hF S hS) h
  · exact fun F hF X _ ν _ k γ hk => Submodule.mem_sInf.2 fun S hS => hS.2.2 F (Submodule.mem_sInf.1 hF S hS) X _ ν inferInstance k γ hk
  · refine sInf_le ⟨fun φ hφ => mem_rspan hφ, fun F hF h => rt_mem_rspan hF h, fun F hF X _ ν _ k γ hk => ?_⟩
    exact kerInf_mem_rspan hF ν hk


open Classical in
def plS (w : InfinitePlace E) : ℂ →ₙ+* Cinf E where
  toFun z := Pi.single w z
  map_mul' z z' := by ext w'; by_cases h : w' = w <;> simp [Pi.single_apply, h]
  map_zero' := by ext w'; simp [Pi.single_apply]
  map_add' z z' := by ext w'; by_cases h : w' = w <;> simp [Pi.single_apply, h]

def plGL (w : InfinitePlace E) : GL (Fin a) ℂ →* GL (Fin a) (Cinf E) := cornerGL a (plS w)



theorem isRapidInf_dirac (y : GL (Fin a) (Cinf E)) :
    IsRapidInf (Measure.dirac ()) (fun _ : Unit => (1 : ℂ)) (fun _ => y) :=
  ⟨measurable_const, measurable_const, fun _ => integrable_const _⟩

theorem kerInf_dirac (y : GL (Fin a) (Cinf E)) (F : GA E a → ℂ) (g : GA E a) :
    kerInf (Measure.dirac ()) (fun _ : Unit => (1 : ℂ)) (fun _ => y) F g = F (g * infGL E a y) := by
  simp [kerInf]

end GlobalTheory.JSW
end
end
