module

public import Mathlib

@[expose] public section

section -- merged from Formalism.UnipotentAdelicQuotients.ThmBInHecke
noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain

namespace HeckeCharacterZeroLocus.ThmBIn

section Adeles

variable (F : Type) [Field F] [NumberField F]

abbrev AF := AdeleRing (𝓞 F) F

abbrev Ainf := InfiniteAdeleRing F

abbrev Af := FiniteAdeleRing (𝓞 F) F

abbrev Fv (v : HeightOneSpectrum (𝓞 F)) := v.adicCompletion F

def pairA (x : Ainf F) (y : Af F) : AF F := (x, y)

def sndA : AF F →ₐ[F] Af F := AlgHom.snd F (Ainf F) (Af F)

def evalV (v : HeightOneSpectrum (𝓞 F)) : Af F →ₐ[F] Fv F v :=
  { RestrictedProduct.evalRingHom (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v with
    commutes' := fun _ => rfl }

def intAf : Set (Af F) :=
  {a | ∀ v : HeightOneSpectrum (𝓞 F), evalV F v a ∈ v.adicCompletionIntegers F}

end Adeles

section Tens

variable {F E : Type} [Field F] [Field E] [Algebra F E]

scoped instance topTens (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    TopologicalSpace (R ⊗[F] E) := moduleTopology R (R ⊗[F] E)

variable (R : Type) [CommRing R] [Algebra F R]

def sigR (σ : E →ₐ[F] E) : R ⊗[F] E →+* R ⊗[F] E :=
  (Algebra.TensorProduct.map (AlgHom.id F R) σ).toRingHom

def inclR : E →+* R ⊗[F] E := (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).toRingHom

end Tens

def IsCMExt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) : Prop :=
  NumberField.IsTotallyReal F ∧ NumberField.IsTotallyComplex E ∧ Module.finrank F E = 2 ∧
    ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)

section Hecke

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev AE : Type := AF F ⊗[F] E

abbrev incA : E →+* AF F ⊗[F] E := inclR (F := F) (AF F)

def finPart : AE F E →+* Af F ⊗[F] E :=
  (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom

def intAE : AddSubgroup (Af F ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ a ∈ intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}

def idF : (AF F)ˣ →* (AE F E)ˣ :=
  Units.map (algebraMap (AF F) (AE F E)).toMonoidHom


open HeckeCharacterZeroLocus.ThmBIn in
def IsHeckeChar (χ : (AE F E)ˣ →* Circle) : Prop :=
  Continuous χ ∧ ∀ x : Eˣ, χ (Units.map (incA F E).toMonoidHom x) = 1

def IsPlaceIdem (v : HeightOneSpectrum (𝓞 F)) (ε : AF F) : Prop :=
  ∃ α : Af F, ε = pairA F 0 α ∧ evalV F v α = 1 ∧ ∀ v', v' ≠ v → evalV F v' α = 0

variable {F E}

abbrev cA (σ : E →ₐ[F] E) : AE F E →+* AE F E := sigR (AF F) σ

def IsSplitIdem (σ : E →ₐ[F] E) (e : AE F E) : Prop :=
  e * e = e ∧ e * cA σ e = 0 ∧ ∃ v ε, IsPlaceIdem F v ε ∧ e + cA σ e = algebraMap (AF F) (AE F E) ε

def IsIdemAt (σ : E →ₐ[F] E) (e : AE F E) (P : HeightOneSpectrum (𝓞 E)) : Prop :=
  IsSplitIdem σ e ∧ ∀ x : 𝓞 E, x ≠ 0 →
    (x ∈ P.asIdeal ↔ finPart F E (e * incA F E ((x : E)⁻¹)) ∉ intAE F E)

def IsPrimeIdem (σ : E →ₐ[F] E) (P : HeightOneSpectrum (𝓞 E)) (e f : AE F E) : Prop :=
  (IsIdemAt σ e P ∧ f = e + cA σ e) ∨
  (f = e ∧ (∃ v ε, IsPlaceIdem F v ε ∧ e = algebraMap (AF F) (AE F E) ε) ∧
    ∀ x : 𝓞 E, x ≠ 0 →
      (x ∈ P.asIdeal ↔ finPart F E (e * incA F E ((x : E)⁻¹)) ∉ intAE F E))

def IsUnifIdele (σ : E →ₐ[F] E) (P : HeightOneSpectrum (𝓞 E)) (x : (AE F E)ˣ) : Prop :=
  ∃ (e f : AE F E) (ϖ : 𝓞 E), IsPrimeIdem σ P e f ∧ ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 ∧
    (x : AE F E) = e * incA F E (ϖ : E) + (1 - e)

def IsUnramAt (σ : E →ₐ[F] E) (χ : (AE F E)ˣ →* Circle) (P : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∃ e f : AE F E, IsPrimeIdem σ P e f ∧ ∀ x : (AE F E)ˣ, (x : AE F E) = e * (x : AE F E) + (1 - e) →
    finPart F E (x : AE F E) ∈ intAE F E → finPart F E ((x⁻¹ : (AE F E)ˣ) : AE F E) ∈ intAE F E → χ x = 1


open scoped Classical in
open Classical in
def chiAt (σ : E →ₐ[F] E) (χ : (AE F E)ˣ →* Circle) (P : HeightOneSpectrum (𝓞 E)) : ℂ :=
  if h : IsUnramAt σ χ P ∧ ∃ x, IsUnifIdele σ P x then ((χ h.2.choose : Circle) : ℂ) else 0

def normP (P : HeightOneSpectrum (𝓞 E)) : ℕ := Ideal.absNorm P.asIdeal

def lfac (σ : E →ₐ[F] E) (χ : (AE F E)ˣ →* Circle) (P : HeightOneSpectrum (𝓞 E)) (s : ℂ) : ℂ :=
  (1 - chiAt σ χ P * (normP P : ℂ) ^ (-s))⁻¹

end Hecke

end HeckeCharacterZeroLocus.ThmBIn

end
end

section -- merged from Formalism.UnipotentAdelicQuotients.WeylLatDual
open MvPolynomial

noncomputable section

namespace WeylLatticeDuality

def rowGen (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] Polynomial (MvPolynomial (Fin r × Fin n) R) :=
  aeval fun v => Polynomial.C (X v) +
    (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0)

def rowDiv (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) : MvPolynomial (Fin r × Fin n) R :=
  (rowGen R a b f).coeff k

def lpMinor (R : Type*) [CommRing R] {r n : ℕ} (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    MvPolynomial (Fin r × Fin n) R :=
  (Matrix.of fun p q : Fin s =>
    (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin r × Fin n) R)).det

def nuNext {n : ℕ} (ν : Fin n → ℕ) (s : Fin n) : ℕ :=
  if h : s.val + 1 < n then ν ⟨s.val + 1, h⟩ else 0

def hw (R : Type*) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    MvPolynomial (Fin r × Fin n) R :=
  ∏ s : Fin n, (lpMinor R (s.val + 1) (by omega) (by omega)) ^ (ν s - nuNext ν s)

def applyWord (R : Type*) [CommRing R] {r n : ℕ} (w : List (Fin r × Fin r × ℕ))
    (f : MvPolynomial (Fin r × Fin n) R) : MvPolynomial (Fin r × Fin n) R :=
  w.foldr (fun x g => rowDiv R x.1 x.2.1 x.2.2 g) f

def weyl (R : Type*) [CommRing R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) :
    Submodule R (MvPolynomial (Fin r × Fin n) R) :=
  Submodule.span R (Set.range fun w : List (Fin r × Fin r × ℕ) => applyWord R w (hw R hn ν))

def ColChoice {Lt : Type} (N1 : ℕ) (nu : Lt → YoungDiagram) : Type :=
  ∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin N1

def nablaX {Lt : Type} [Fintype Lt] (N0 : ℕ) (nu : Lt → YoungDiagram) (J : ColChoice N0 nu) :
    MvPolynomial (Lt × ℕ × Fin N0) ℤ :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i k : Fin ((nu s).colLen c) =>
    (MvPolynomial.X (s, (i : ℕ), J s c k) : MvPolynomial (Lt × ℕ × Fin N0) ℤ))

def DeX {Lt k : Type} [Fintype Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (y : Lt → Fin N → ℕ → k) :
    MvPolynomial (Lt × ℕ × Fin N) k :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i j : Fin ((nu s).colLen c) =>
    ∑ a : Fin N, MvPolynomial.C (y s a (j : ℕ)) * MvPolynomial.X (s, (i : ℕ), a))

def colsOf {k : Type} [Zero k] {N : ℕ} (Y : Matrix (Fin N) (Fin N) k) : Fin N → ℕ → k :=
  fun a j => if h : j < N then Y a ⟨j, h⟩ else 0

def DelW (p : ℕ) [Fact p.Prime] (T : Type) [Fintype T] (N : ℕ) (ν : T → Fin N → ℕ) :
    AddSubgroup ((T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p]) :=
  AddSubgroup.closure {F | ∃ (r : ℂ_[p]) (f : T → MvPolynomial (Fin N × Fin N) ℤ), ‖r‖ ≤ 1 ∧
    (∀ τ, f τ ∈ weyl ℤ N N le_rfl (ν τ)) ∧
    F = fun y => r * ∏ τ, MvPolynomial.eval (fun k : Fin N × Fin N => y τ k.1 k.2)
      (MvPolynomial.map (Int.castRingHom ℂ_[p]) (f τ))}

def Stmt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Lt T : Type) [Fintype Lt] [Fintype T] (e : Lt → T), Function.Bijective e →
    ∀ (N : ℕ) (nu : Lt → YoungDiagram) (ν : T → Fin N → ℕ),
      (∀ z (r : Fin N), (nu z).rowLen r = ν (e z) r) → (∀ z r, N ≤ r → (nu z).rowLen r = 0) →
      ∀ φ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p]),
        ((∀ J : ColChoice N nu, ‖φ (MvPolynomial.map (Int.castRingHom ℂ_[p]) (nablaX N nu J))‖ ≤ 1) ↔
          (fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] => φ (DeX N nu fun s => colsOf (y (e s)))) ∈ DelW p T N ν)

end WeylLatticeDuality

end
end

section -- merged from Formalism.UnipotentAdelicQuotients.ClassNumberFinite
namespace HeckeCharacterZeroLocus

open NumberField IsDedekindDomain

def zeroLocusGL {F : Type} [Field F] {n : ℕ} (S : Set (MvPolynomial (Fin n × Fin n) F))
    (R : Type) [CommRing R] [Algebra F R] : Set (GL (Fin n) R) :=
  {g | ∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) R) ij.1 ij.2) P = 0}

def IsGroupLocus {F : Type} [Field F] {n : ℕ} (S : Set (MvPolynomial (Fin n × Fin n) F)) : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra F R],
    1 ∈ zeroLocusGL S R ∧ (∀ g ∈ zeroLocusGL S R, ∀ h ∈ zeroLocusGL S R, g * h ∈ zeroLocusGL S R) ∧
      (∀ g ∈ zeroLocusGL S R, g⁻¹ ∈ zeroLocusGL S R)

def locusSubgroup {F : Type} [Field F] {n : ℕ} (S : Set (MvPolynomial (Fin n × Fin n) F))
    (hS : IsGroupLocus S) (R : Type) [CommRing R] [Algebra F R] : Subgroup (GL (Fin n) R) where
  carrier := zeroLocusGL S R
  one_mem' := (hS R).1
  mul_mem' := fun {a b} ha hb => (hS R).2.1 a ha b hb
  inv_mem' := fun {a} ha => (hS R).2.2 a ha

def ClassNumberFinite : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F))
    (hS : IsGroupLocus S) (U : Subgroup (locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))),
    IsOpen (U : Set (locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))) →
    IsCompact (U : Set (locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))) →
    ∃ T : Finset (locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F)),
      ∀ x : locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F), ∃ γ : GL (Fin n) F, γ ∈ zeroLocusGL S F ∧
        ∃ s ∈ T, ∃ u ∈ U,
          (x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) =
            Units.map (RingHom.mapMatrix (algebraMap F (FiniteAdeleRing (𝓞 F) F))).toMonoidHom γ *
              (s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) * ((u : locusSubgroup S hS _) : GL (Fin n) _)

end HeckeCharacterZeroLocus
end

section -- merged from Formalism.UnipotentAdelicQuotients.StdAdditiveCharExists
namespace HeckeCharacterZeroLocus

open NumberField

def StdAdditiveCharExists : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F →
    ∃ ψ : AddChar (AdeleRing (𝓞 F) F) ℂ, Continuous ψ ∧ (∀ x, ‖ψ x‖ = 1) ∧
      (∀ a : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1) ∧ (∃ x, ψ x ≠ 1) ∧
      ∀ x : InfiniteAdeleRing F, ψ (x, 0) =
        Complex.exp (-(2 * Real.pi * Complex.I *
          ((∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ)))

end HeckeCharacterZeroLocus
end

section -- merged from Formalism.UnipotentAdelicQuotients.HaarProductClosedCompact
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.D

def haarProductClosedCompact : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsMulLeftInvariant → IsFiniteMeasureOnCompacts μ →
    μ ≠ 0 → ∀ P K : Subgroup G, IsClosed (P : Set G) → IsCompact (K : Set G) → (∀ g, ∃ p ∈ P, ∃ k ∈ K, g = p * k) →
    ∀ μP μK : Measure G, μP (P : Set G)ᶜ = 0 → (∀ p ∈ P, μP.map (fun x => p * x) = μP) →
      (∀ s : Set G, IsCompact s → μP s ≠ ⊤) → μP ≠ 0 →
      μK Set.univ = 1 → μK (K : Set G)ᶜ = 0 → (∀ k ∈ K, μK.map (fun x => k * x) = μK) →
      ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ Φ : G → ℝ≥0∞, Measurable Φ →
        ∫⁻ x, Φ x ∂μ = c * ∫⁻ p, (∫⁻ k, Φ (p * k) ∂μK) ∂μP

end Formalism.D

end
end

section -- merged from Formalism.UnipotentAdelicQuotients.EllReg
namespace ZetaZeros.D.EllReg

open scoped ContDiff

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable def ev {d : ℕ} (j : Fin d) : E d := EuclideanSpace.single j (1 : ℝ)

noncomputable def dw {d : ℕ} : List (Fin d) → (E d → ℂ) → E d → ℂ
  | [], f => f
  | j :: w, f => fun x => fderiv ℝ (dw w f) x (ev j)

noncomputable def trOp {d : ℕ} (m : ℕ) (b : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (φ : E d → ℂ)
    (x : E d) : ℂ :=
  ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
    (-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => b n w y * φ y) x

structure Sys (d : ℕ) (ι : Type) where
  ord : ι → ℕ
  a : ι → (n : ℕ) → (Fin n → Fin d) → E d → ℂ

noncomputable def Sys.tr {d : ℕ} {ι : Type} (P : Sys d ι) (i : ι) (φ : E d → ℂ) (x : E d) : ℂ :=
  trOp (P.ord i) (P.a i) φ x

noncomputable def Sys.symb {d : ℕ} {ι : Type} (P : Sys d ι) (i : ι) (x ξ : E d) : ℂ :=
  ∑ w : Fin (P.ord i) → Fin d, P.a i (P.ord i) w x * ∏ l, ((ξ (w l) : ℝ) : ℂ)

def WeakSol {d : ℕ} {ι : Type} (P : Sys d ι) (U : Set (E d)) (u : E d → ℂ) : Prop :=
  ∀ (i : ι) (φ : E d → ℂ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
    ∫ x, u x * P.tr i φ x = 0

def Hyp {d : ℕ} {ι : Type} (P : Sys d ι) (U : Set (E d)) (u : E d → ℂ) : Prop :=
  IsOpen U ∧ (∀ i n w, ContDiffOn ℝ ∞ (P.a i n w) U) ∧
    (∀ x ∈ U, ∀ ξ : E d, ξ ≠ 0 → ∃ i, P.symb i x ξ ≠ 0) ∧ ContinuousOn u U ∧ WeakSol P U u

def Internal : Prop :=
  ∀ (d : ℕ) (ι : Type) [Fintype ι] (P : Sys d ι) (U : Set (E d)) (u : E d → ℂ),
    Hyp P U u → ContDiffOn ℝ ∞ u U

end ZetaZeros.D.EllReg
end

section -- merged from Formalism.UnipotentAdelicQuotients.CuspEllipticValues
set_option autoImplicit false

namespace CuspElliptic

def IsChar {G : Type} [Group G] (χ : G → ℂ) : Prop :=
  ∃ (n : ℕ) (ρ : G →* GL (Fin n) ℂ), ∀ x, χ x = Matrix.trace (ρ x : Matrix (Fin n) (Fin n) ℂ)

def IsIrrChar {G : Type} [Group G] [Fintype G] (χ : G → ℂ) : Prop :=
  IsChar χ ∧ (∑ x, χ x * star (χ x)) = (Fintype.card G : ℂ)

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

def unipBlock (d a : ℕ) : Set (GL (Fin d) F) :=
  {u | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)}

def IsCuspChar {d : ℕ} (χ : GL (Fin d) F → ℂ) : Prop :=
  IsIrrChar χ ∧ ∀ a, 0 < a → a < d →
    ∑ u : GL (Fin d) F, (open Classical in if u ∈ (unipBlock d a : Set (GL (Fin d) F)) then χ u else 0) = 0

def Statement : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (d : ℕ) (χ χ' : GL (Fin d) F → ℂ),
    IsCuspChar χ → IsCuspChar χ' →
    (∀ x : GL (Fin d) F, Irreducible (Matrix.charpoly (x : Matrix (Fin d) (Fin d) F)) → χ x = χ' x) →
    χ = χ'

end CuspElliptic
end

section -- merged from Formalism.UnipotentAdelicQuotients.SiegelSetsSL2Adelic
open NumberField

noncomputable section

namespace Formalism.D

def adeleOfParts (F : Type) [Field F] [NumberField F] (x : InfiniteAdeleRing F)
    (y : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) : AdeleRing (𝓞 F) F := (x, y)

def siegelSetsSL2Adelic : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    ∃ (Ω K : Set (Matrix.SpecialLinearGroup (Fin 2) (AdeleRing (𝓞 F) F))) (t₀ : ℝ),
      IsCompact Ω ∧ (∀ p ∈ Ω, (p : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0) ∧ IsCompact K ∧ 0 < t₀ ∧
      ∀ g : Matrix.SpecialLinearGroup (Fin 2) (AdeleRing (𝓞 F) F),
        ∃ γ ∈ (Matrix.SpecialLinearGroup.map (algebraMap F (AdeleRing (𝓞 F) F))).range,
        ∃ p ∈ Ω, ∃ t : ℝ, t₀ ≤ t ∧
        ∃ a a' : InfiniteAdeleRing F,
          (∀ w, a w * a' w = 1 ∧ InfinitePlace.Completion.extensionEmbedding w (a w) = (t : ℂ)) ∧
          ∃ k ∈ K, ((γ * g : Matrix.SpecialLinearGroup (Fin 2) (AdeleRing (𝓞 F) F)) :
              Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
            (p : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) *
              !![adeleOfParts F a 1, 0; 0, adeleOfParts F a' 1] *
              (k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))

end Formalism.D

end
end

section -- merged from Formalism.UnipotentAdelicQuotients.FinOrdValGen
noncomputable section

open NumberField IsDedekindDomain

namespace HeckeValGen

variable (L : Type) [Field L] [NumberField L]

abbrev Ideles : Type := (AdeleRing (𝓞 L) L)ˣ

def diagUnits : Lˣ →* Ideles L :=
  Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom


open Classical in
def finiteSingle (v : HeightOneSpectrum (𝓞 L)) :
    v.adicCompletion L →* FiniteAdeleRing (𝓞 L) L := by
  classical
  exact
    { toFun x := RestrictedProduct.mulSingle
        (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletionIntegers L) v x
      map_one' := RestrictedProduct.mulSingle_one _ _
      map_mul' x y := RestrictedProduct.mulSingle_mul _ _ x y }

def localIdele (v : HeightOneSpectrum (𝓞 L)) : (v.adicCompletion L)ˣ →* Ideles L :=
  Units.map
    { toFun := fun x => ((1 : InfiniteAdeleRing L), finiteSingle L v x)
      map_one' := Prod.ext rfl (map_one (finiteSingle L v))
      map_mul' := fun x y => Prod.ext (mul_one 1).symm (map_mul (finiteSingle L v) x y) }

end HeckeValGen
end
end

section -- merged from Formalism.UnipotentAdelicQuotients.BruhatFunctionExistsVariant
universe u

namespace HeckeCharacterZeroLocus

open MeasureTheory Pointwise

def BruhatFunctionExistsVariant : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) →
    ∀ (μ : Measure H), μ.IsHaarMeasure →
      ∃ β : G → ℝ, Continuous β ∧ (∀ x, 0 ≤ β x) ∧
        (∀ K : Set G, IsCompact K → IsCompact (tsupport β ∩ (K * (H : Set G)))) ∧
        ∀ x : G, ∫ h : H, β (x * (h : G)) ∂μ = 1

end HeckeCharacterZeroLocus
end

section -- merged from Formalism.UnipotentAdelicQuotients.GlobalNormIndexTwo
noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.D.Classical

def GlobalNormIndexTwo : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Module.finrank F E = 2 →
    ∃! η : (AdeleRing (𝓞 F) F)ˣ →* Circle,
      Continuous η ∧
      (∀ a : Fˣ, η (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a) = 1) ∧
      (∀ x : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ,
        η (Units.map (Algebra.norm (AdeleRing (𝓞 F) F) : AdeleRing (𝓞 F) F ⊗[F] E →* AdeleRing (𝓞 F) F) x) = 1) ∧
      η ≠ 1

end Formalism.D.Classical

end
end

section -- merged from Formalism.UnipotentAdelicQuotients.CuspidalCharExists
open Polynomial

noncomputable section

namespace Formalism.D.Classical

section
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

def grUnipBlock (d a : ℕ) : Set (GL (Fin d) F) :=
  {u | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)}

end

variable {g : ℕ} [Fact g.Prime]

end Formalism.D.Classical

namespace Formalism.D.Classical

end Formalism.D.Classical
end
end

section -- merged from Formalism.UnipotentAdelicQuotients.SmComplete
open Filter Topology
open scoped ContDiff

noncomputable section

namespace SmoothVectors

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsClosedMatrixGroup (G : Set (Matrix (Fin n) (Fin n) ℂ)) : Prop :=
  IsClosed G ∧ (1 : Matrix (Fin n) (Fin n) ℂ) ∈ G ∧ (∀ g ∈ G, ∀ h ∈ G, g * h ∈ G) ∧
    ∀ g ∈ G, ∃ h ∈ G, h * g = 1 ∧ g * h = 1

def lieAlg (G : Set (Matrix (Fin n) (Fin n) ℂ)) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {X | ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ G}

end SmoothVectors

end
end

section -- merged from Formalism.UnipotentAdelicQuotients.JetMomFound
set_option autoImplicit false

noncomputable section

open PowerSeries

namespace JetMomFound

section FG

variable {R : Type*} [CommRing R]

def mulN (F : FormalGroup R) : ℕ → PowerSeries R
  | 0 => 0
  | n + 1 => MvPowerSeries.subst (![mulN F n, PowerSeries.X] : Fin 2 → MvPowerSeries Unit R) F.toPowerSeries

def IsIsoGm (F : FormalGroup R) (f : PowerSeries R) : Prop :=
  constantCoeff f = 0 ∧ IsUnit (coeff 1 f) ∧
    PowerSeries.subst F.toPowerSeries f =
      (FormalGroup.𝔾ₘ : FormalGroup R).toPowerSeries.subst
        ![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) f,
          PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) f]

end FG

section Padic

variable {p : ℕ} [Fact p.Prime]

def CoeffFinite (F : FormalGroup 𝓞_ℂ_[p]) : Prop :=
  ∃ L : IntermediateField ℚ_[p] ℂ_[p], FiniteDimensional ℚ_[p] L ∧
    ∀ m : Fin 2 →₀ ℕ, ((MvPowerSeries.coeff m F.toPowerSeries : 𝓞_ℂ_[p]) : ℂ_[p]) ∈ L

def HtOne (F : FormalGroup 𝓞_ℂ_[p]) : Prop :=
  ‖((coeff p (mulN F p) : 𝓞_ℂ_[p]) : ℂ_[p])‖ = 1 ∧ ∀ k < p, ‖((coeff k (mulN F p) : 𝓞_ℂ_[p]) : ℂ_[p])‖ < 1

end Padic

def HtOneIsGm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : FormalGroup 𝓞_ℂ_[p]), CoeffFinite F → HtOne F → ∃ f : PowerSeries 𝓞_ℂ_[p], IsIsoGm F f

end JetMomFound
end
end
