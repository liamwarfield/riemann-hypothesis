module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffClr
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFamilyExponentialLocally
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLineBundleIsoOnOpenOfRestrictionIso

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR
open Polynomial
open scoped Classical

namespace UpperTheory.Gal.W2

def SimDiag : Prop :=
  ∀ (g : ℕ) (I : Type) (M : I → Matrix (Fin g) (Fin g) ℂ), (∀ i j, M i * M j = M j * M i) →
    (∀ i, ∃ p : ℂ[X], p.Separable ∧ aeval (M i) p = 0) → ∃ (Sb : Matrix (Fin g) (Fin g) ℂ) (d : I → Fin g → ℂ),
      Sb.det ≠ 0 ∧ ∀ i, M i * Sb = Sb * Matrix.diagonal (d i)

def ExtendEmb : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (φ : 𝓞 F →+* ℂ), ∃ τ : F →+* ℂ, ∀ c : 𝓞 F, φ c = τ (c : F)

def KillsMat : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (D : PLat O bar) (P₀ : D.La →+ (Fin g → ℂ)), IsPeriod D ρ P₀ → ∀ (ga : D.La →ₗ[O] D.La) (H : Matrix (Fin g) (Fin g) ℂ), (∀ x, P₀ (ga x) = H *ᵥ P₀ x) → ∀ q : (𝓞 F)[X], Kills a ga q ↔ (q.sum fun i b => ρ (a b) * H ^ i) = 0

def HSep : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (H : Matrix (Fin g) (Fin g) ℂ), (∀ c, ρ (a c) * H = H * ρ (a c)) → ∀ χ : F[X], χ.Monic → χ.Separable →
    (∀ q : (𝓞 F)[X], χ ∣ q.map (algebraMap (𝓞 F) F) → (q.sum fun i b => ρ (a b) * H ^ i) = 0) →
    ∃ p : ℂ[X], p.Separable ∧ aeval H p = 0

def DiagExists : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (D : PLat O bar) (P₀ : D.La →+ (Fin g → ℂ)), IsPeriod D ρ P₀ → ∀ (ga : D.La →ₗ[O] D.La) (H : Matrix (Fin g) (Fin g) ℂ), (∀ x, P₀ (ga x) = H *ᵥ P₀ x) → ∀ χ : F[X], IsMinOf a ga χ → χ.Separable → ∃ Sb ty ev, IsDiag a ρ H Sb ty ev

def TypeCount : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (n : ℕ) (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ), IsSig a bar ρ n t₀ ε → ∀ H : Matrix (Fin g) (Fin g) ℂ, ∀ (Sb : Matrix (Fin g) (Fin g) ℂ) (ty : Fin g → (F →+* ℂ)) (ev : Fin g → ℂ), IsDiag a ρ H Sb ty ev → ∀ τ, (evAt ty ev τ).card = typeMult n t₀ ε τ ∧ (evFull ty ev τ).card = n

def TraceLat : Prop :=
  ∀ (L : Type) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L] (g : ℕ) (P : L →+ (Fin g → ℂ)), Function.Injective P →
    DiscreteTopology P.range → Submodule.span ℝ (Set.range P) = ⊤ → ∀ (f : L →ₗ[ℤ] L) (H : Matrix (Fin g) (Fin g) ℂ),
    (∀ x, P (f x) = H *ᵥ P x) → ((LinearMap.trace ℤ L f : ℤ) : ℂ) = H.trace + (starRingEnd ℂ) H.trace

def TraceDual : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (s : (F →+* ℂ) → ℂ),
    (∀ c : 𝓞 F, ∃ m : ℤ, ∑ τ : F →+* ℂ, τ (c : F) * s τ = m) → ∃ b : F, ∀ τ, s τ = τ b

def NewtonPoly : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (m : (F →+* ℂ) → Multiset ℂ), (∀ τ, (m τ).card = n) →
    (∀ j : ℕ, ∃ b : F, ∀ τ, ((m τ).map fun r => r ^ j).sum = τ b) →
    ∃ χ : F[X], χ.Monic ∧ χ.natDegree = n ∧ ∀ τ, χ.map τ = ((m τ).map fun r => X - C r).prod

def PowSumRat : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (D : PLat O bar) (P₀ : D.La →+ (Fin g → ℂ)), IsPeriod D ρ P₀ → ∀ (ga : D.La →ₗ[O] D.La) (H : Matrix (Fin g) (Fin g) ℂ), (∀ x, P₀ (ga x) = H *ᵥ P₀ x) → ∀ (Sb : Matrix (Fin g) (Fin g) ℂ) (ty : Fin g → (F →+* ℂ)) (ev : Fin g → ℂ), IsDiag a ρ H Sb ty ev → ∀ j : ℕ, ∃ b : F, ∀ τ, ((evFull ty ev τ).map fun r => r ^ j).sum = τ b

def RootsFull : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (n : ℕ) (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ), IsSig a bar ρ n t₀ ε → ∀ (D : PLat O bar) (P₀ : D.La →+ (Fin g → ℂ)), IsPeriod D ρ P₀ → ∀ (ga : D.La →ₗ[O] D.La) (H : Matrix (Fin g) (Fin g) ℂ), (∀ x, P₀ (ga x) = H *ᵥ P₀ x) → ∀ (Sb : Matrix (Fin g) (Fin g) ℂ) (ty : Fin g → (F →+* ℂ)) (ev : Fin g → ℂ), IsDiag a ρ H Sb ty ev → ∀ χ : F[X], IsMinOf a ga χ → χ.natDegree = n → ∀ τ, rts χ τ = evFull ty ev τ

def MarkDiag : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (n : ℕ) (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ), IsSig a bar ρ n t₀ ε → ∀ H : Matrix (Fin g) (Fin g) ℂ, ∀ (Sb : Matrix (Fin g) (Fin g) ℂ) (ty : Fin g → (F →+* ℂ)) (ev : Fin g → ℂ), IsDiag a ρ H Sb ty ev → ∀ mu, IsMark a ρ t₀ H mu ↔ evAt ty ev t₀ = {mu}

def TspDiag : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (g : ℕ) (ty : Fin g → (F →+* ℂ)) (t₀ : F →+* ℂ) (i₀ : Fin g), ComplexEmbedding.conjugate t₀ ≠ t₀ →
    (∀ i, ty i = t₀ ↔ i = i₀) → (∀ i j, ty j = ComplexEmbedding.conjugate (ty i) → i = i₀ ∨ j = i₀) →
    ∀ W : Submodule ℂ (Matrix (Fin g) (Fin g) ℂ),
    (∀ S, S ∈ W ↔ Sᵀ = S ∧ ∀ (c : 𝓞 F) i j, S i j * ty j (c : F) = (starRingEnd ℂ) (ty i (c : F)) * S i j) →
    Function.Bijective (fun (S : W) (j : {j // ty j = ComplexEmbedding.conjugate t₀}) => S.1 i₀ j.1)

def BallChar : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (n : ℕ) (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ), IsSig a bar ρ n t₀ ε → ∀ (D : PLat O bar) (P₀ : D.La →+ (Fin g → ℂ)) (M₀ : Matrix (Fin g) (Fin g) ℂ), IsPeriod D ρ P₀ → IsHermOf D P₀ M₀ →
    ∀ H : Matrix (Fin g) (Fin g) ℂ, H.det ≠ 0 → ∀ (Sb : Matrix (Fin g) (Fin g) ℂ) (ty : Fin g → (F →+* ℂ)) (ev : Fin g → ℂ), IsDiag a ρ H Sb ty ev → ∀ mu, evAt ty ev t₀ = {mu} →
    ∀ (d : ℕ) (co : (Fin d → ℂ) →ₗ[ℂ] Matrix (Fin g) (Fin g) ℂ), IsCoordC bar ρ M₀ co →
    ∀ T : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ), (∀ b, co (T b) = H * co b * (H.map star)⁻¹) → d = n - 1 ∧
      ∀ y : ℂ, LinearMap.det (1 - y • T) =
        ((evAt ty ev (ComplexEmbedding.conjugate t₀)).map fun r => 1 - y * (mu / (starRingEnd ℂ) r)).prod

def CspDim : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (n : ℕ) (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ), IsSig a bar ρ n t₀ ε → ∀ (D : PLat O bar) (P₀ : D.La →+ (Fin g → ℂ)) (M₀ : Matrix (Fin g) (Fin g) ℂ), IsPeriod D ρ P₀ → IsHermOf D P₀ M₀ →
    ∃ co : (Fin (n - 1) → ℂ) →ₗ[ℂ] Matrix (Fin g) (Fin g) ℂ, IsCoordC bar ρ M₀ co

def FibDet : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (H : Matrix (Fin g) (Fin g) ℂ), ∀ (Sb : Matrix (Fin g) (Fin g) ℂ) (ty : Fin g → (F →+* ℂ)) (ev : Fin g → ℂ), IsDiag a ρ H Sb ty ev → ∀ (k : ℕ) (α : Fin k → 𝓞 F) (y : ℂ),
    LinearMap.det (1 - y • fibMap H (diagAct a ρ α)) = ∏ s, ∏ i, (1 - ty i (α s : F) * (y * ev i))

def FibW : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (g n : ℕ) (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ) (ty : Fin g → (F →+* ℂ)) (ev : Fin g → ℂ)
    (χ : F[X]) (mu : ℂ), (∀ τ : F →+* ℂ, ComplexEmbedding.conjugate τ ≠ τ) → 1 ≤ n →
    (∀ τ, τ ≠ t₀ → τ ≠ ComplexEmbedding.conjugate t₀ → ε τ + ε (ComplexEmbedding.conjugate τ) = 1) →
    (∀ τ, (evAt ty ev τ).card = typeMult n t₀ ε τ) → (∀ τ, rts χ τ = evFull ty ev τ) → evAt ty ev t₀ = {mu} →
    ∀ (x : F) (y : ℂ), (∏ i, (1 - ty i x * (y * ev i))) * (starRingEnd ℂ) (∏ i, (1 - ty i x * ev i)) = fibW t₀ ε x y χ mu

def EvIntegral : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (D : PLat O bar) (P₀ : D.La →+ (Fin g → ℂ)), IsPeriod D ρ P₀ → ∀ (ga : D.La →ₗ[O] D.La) (H : Matrix (Fin g) (Fin g) ℂ), (∀ x, P₀ (ga x) = H *ᵥ P₀ x) → ∀ (Sb : Matrix (Fin g) (Fin g) ℂ) (ty : Fin g → (F →+* ℂ)) (ev : Fin g → ℂ), IsDiag a ρ H Sb ty ev → ∀ i (x : 𝓞 F), 1 - ty i ((2 * x : 𝓞 F) : F) * ev i ≠ 0

def EigTop : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (n : ℕ) (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ), IsSig a bar ρ n t₀ ε → ∀ (D : PLat O bar) (P₀ : D.La →+ (Fin g → ℂ)) (M₀ : Matrix (Fin g) (Fin g) ℂ), IsPeriod D ρ P₀ → IsHermOf D P₀ M₀ →
    ∀ (ga : D.La →ₗ[O] D.La) (H : Matrix (Fin g) (Fin g) ℂ), FixesPer D P₀ ga H → ∀ χ : F[X], IsMinOf a ga χ → χ.natDegree = n → χ.Separable →
    ∀ (d : ℕ) (co : (Fin d → ℂ) →ₗ[ℂ] Matrix (Fin g) (Fin g) ℂ), IsCoordC bar ρ M₀ co →
    ∀ T : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ), (∀ b, co (T b) = H * co b * (H.map star)⁻¹) →
    ∀ (k : ℕ) (α : Fin k → 𝓞 F), (∀ s, (2 : 𝓞 F) ∣ α s) → (∃ mu, IsMark a ρ t₀ H mu) ∧ ∀ mu, IsMark a ρ t₀ H mu →
      mu ∈ rts χ t₀ ∧ LinearMap.det (1 - T) ≠ 0 ∧ LinearMap.det (1 - fibMap H (diagAct a ρ α)) ≠ 0 ∧
      ∀ t : ℂ, LinearMap.det (1 - t • T) / LinearMap.det (1 - T) * (LinearMap.det (1 - t • fibMap H (diagAct a ρ α)) *
        (starRingEnd ℂ) (LinearMap.det (1 - fibMap H (diagAct a ρ α)))) = locW t₀ ε α t χ mu

def RootSumW : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ) (lam : (F →+* ℂ) → Fin n → ℕ) (m : ℕ),
    ComplexEmbedding.conjugate t₀ ≠ t₀ → (∀ i, lam (ComplexEmbedding.conjugate t₀) i = m) →
    ∃ k₀, ∀ k, k₀ ≤ k → ∃ c : (Fin k → 𝓞 F) →₀ ℂ, (∀ α ∈ c.support, ∀ s, α s ≠ 0 ∧ (2 : 𝓞 F) ∣ α s) ∧
      ∀ (χ : F[X]) (r : (F →+* ℂ) → Fin n → ℂ), χ.Separable → (∀ τ, rts χ τ = Finset.univ.val.map (r τ)) → ∀ y : ℂ,
        (c.sum fun α w => w * ((rts χ t₀).map fun mu => locW t₀ ε α y χ mu).sum) =
          (∏ τ, UpperTheory.Gal.Schur.sch (lam τ) (r τ)) *
            (y ^ ((n - 1) * m + ∑ τ ∈ (Finset.univ.erase t₀).erase (ComplexEmbedding.conjugate t₀), ε τ * ∑ i, lam τ i) *
              ∑ i : Fin n, y ^ (lam t₀ i + (n - 1 - (i : ℕ))))

def RootSumWOff : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ) (lam : (F →+* ℂ) → Fin n → ℕ) (m : ℕ),
    ComplexEmbedding.conjugate t₀ ≠ t₀ → (∀ i, lam t₀ i = m) →
    ∃ k₀, ∀ k, k₀ ≤ k → ∃ c : (Fin k → 𝓞 F) →₀ ℂ, (∀ α ∈ c.support, ∀ s, α s ≠ 0 ∧ (2 : 𝓞 F) ∣ α s) ∧
      ∀ (χ : F[X]) (r : (F →+* ℂ) → Fin n → ℂ), χ.Separable → (∀ τ, rts χ τ = Finset.univ.val.map (r τ)) → χ.coeff 0 ≠ 0 → (∃ q : ℝ, ∀ z ∈ rts χ t₀, z * (starRingEnd ℂ) z = q) → ∀ y : ℂ,
        (c.sum fun α w => w * ((rts χ t₀).map fun mu => locW t₀ ε α y χ mu).sum) =
          (∏ τ, UpperTheory.Gal.Schur.sch (lam τ) (r τ)) *
            (y ^ (m + ∑ τ ∈ (Finset.univ.erase t₀).erase (ComplexEmbedding.conjugate t₀), ε τ * ∑ i, lam τ i) *
              ∑ i : Fin n, y ^ (∑ j ∈ Finset.univ.erase i, lam (ComplexEmbedding.conjugate t₀) j + (i : ℕ)))

end UpperTheory.Gal.W2
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PDetOfCharpoly
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private lemma det_one_sub_smul_matrix {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (y : ℂ) :
    (1 - y • M).det = Polynomial.eval y M.charpoly.reverse := by
  rw [Matrix.reverse_charpoly, Matrix.charpolyRev, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j
  · subst h; simp [Matrix.one_apply]; ring
  · simp [Matrix.one_apply, h]; ring

private lemma det_one_sub_smul_linear {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : V →ₗ[ℂ] V) (y : ℂ) :
    LinearMap.det (1 - y • f) = Polynomial.eval y f.charpoly.reverse := by
  classical
  let b := Module.finBasis ℂ V
  rw [← LinearMap.det_toMatrix b, map_sub, map_smul, LinearMap.toMatrix_one,
    det_one_sub_smul_matrix, LinearMap.charpoly_toMatrix]

theorem UpperTheory.Gal.W2.detOfCharpoly_of :
    UpperTheory.Gal.W2.DetOfCharpoly := by
  intro V W _ _ _ _ _ _ T Θ d A h y
  rw [det_one_sub_smul_linear, det_one_sub_smul_linear, ← Polynomial.eval_mul,
    ← Polynomial.reverse_mul_of_domain, ← h, det_one_sub_smul_matrix]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPtHol
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.ptHol_of :
    UpperTheory.Gal.W2.HolPi → UpperTheory.Gal.W2.PtFibre → UpperTheory.Gal.W2.PtHol := by
  intro hHP hPF O _ bar g ρ D X s A _ S k m B P hB hP
  have hBU : IsOpen (B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ))) := hB.prod isOpen_univ
  have hS := S.hol m B P hB hP
  refine hHP ((Fin m → ℂ) × (Fin k → Fin g → ℂ)) X A k (B ×ˢ Set.univ)
    (fun bz => S.pt k (P bz.1) bz.2) hBU ?_ ?_
  · have hu : IsHolTo (B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ))) (fun bz => S.u (P bz.1)) :=
      GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_precomp hS.1 hBU differentiableOn_fst
        (fun bz hbz => hbz.1)
    refine GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_congr hu ?_
    intro bz hbz
    exact (hPF O bar g ρ D X s A S k (P bz.1) (hP.1 _ hbz.1)).1 bz.2
  · intro j
    let φ : (Fin m → ℂ) × (Fin k → Fin g → ℂ) → (Fin m → ℂ) × (Fin g → ℂ) :=
      fun bz => (bz.1, bz.2 j)
    have hφ : Differentiable ℂ φ := by
      fun_prop
    have hmaps : Set.MapsTo φ (B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ)))
        (B ×ˢ (Set.univ : Set (Fin g → ℂ))) :=
      fun bz hbz => ⟨hbz.1, Set.mem_univ _⟩
    have he := GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_precomp hS.2 hBU hφ.differentiableOn hmaps
    refine GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_congr he ?_
    intro bz hbz
    exact (hPF O bar g ρ D X s A S k (P bz.1) (hP.1 _ hbz.1)).2.1 bz.2 j
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPerNear
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.PerCoordU GlobalTheory.PeriodCoord

namespace UpperTheory.Gal.W2

theorem perNear_of : PerNear := by
  intro O _ bar g ρ D P₀ M₀ hP hM d co hco
  obtain ⟨hHerm, hPos, hIm⟩ := hM
  have hdet : M₀.det ≠ 0 := det_ne_zero_of_pos hPos
  obtain ⟨t, ht, htO, ht0⟩ := eventually_nhds_iff.mp (T.eventually_posDef_hermForm_near_zero_matrix M₀ hPos)
  have hcont : Continuous co := LinearMap.continuous_of_finiteDimensional co
  refine ⟨co ⁻¹' t, htO.preimage hcont, by simpa using ht0, ?_, ?_⟩
  · intro b hb
    obtain ⟨h1, h2, h3⟩ := ht (co b) hb
    have hT : (co b)ᵀ * M₀ ∈ Tsp bar ρ := hco b
    obtain ⟨hH, hF⟩ := T.riemann_relation_converse_conjAffine M₀ (co b) hHerm hdet hT.1 h1
    have hcomm := comm_of_mem_Tsp hP hIm hdet hT
    refine T.isPeriodMap_comp_injective_realLinear D ρ P₀ (realMap 1 (co b)) (M₀ * (1 - (co b).map star * co b)⁻¹) hP
      (realMap_one_injective h2) ?_ hH h3 ?_
    · intro a x
      simp only [realMap_apply, Matrix.one_mulVec, Matrix.mulVec_add, star_mulVec_map,
        Matrix.mulVec_mulVec, hcomm a]
      rw [Matrix.one_mul]
    · intro x y
      simp only [realMap_apply, Matrix.one_mulVec]
      rw [hF, hIm]
  · intro x
    set v := star (P₀ x)
    let f : (Fin d → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
      { toFun := fun b => co b *ᵥ v
        map_add' := by intro a b; simp [Matrix.add_mulVec]
        map_smul' := by intro c b; simp [Matrix.smul_mulVec] }
    have hf : Differentiable ℂ (fun b => co b *ᵥ v) :=
      (LinearMap.toContinuousLinearMap f).differentiable
    have : (fun b => (perC P₀ (co b)) x) = fun b => P₀ x + co b *ᵥ v := by
      funext b; simp [perC_apply, v]
    rw [this]
    exact ((differentiable_const _).add hf).differentiableOn

end UpperTheory.Gal.W2
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PCorrChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem map_star_inv_mul {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (hdet : H.det ≠ 0) :
    (H.map star)⁻¹ * H.map star = 1 := by
  have hu : IsUnit H.det := isUnit_iff_ne_zero.mpr hdet
  have hHi : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H hu
  have hb : H.map star * (H⁻¹).map star = 1 := by
    have h := congrArg (fun M => (starRingEnd ℂ).mapMatrix M) hHi
    simp only [map_mul, map_one] at h
    exact h
  have hi : (H.map star)⁻¹ = (H⁻¹).map star := Matrix.inv_eq_right_inv hb
  rw [hi]
  exact mul_eq_one_comm.mp hb

theorem UpperTheory.Gal.W2.corrChart_of :
    UpperTheory.Gal.W2.AdExists → UpperTheory.Gal.W2.PerLin → UpperTheory.Gal.W2.PtFibre → UpperTheory.Gal.W2.CorrChart := by
  intro hAd hLin hFib O _ bar g ρ D X s A _ S k Z c₁ c₂ P₀ M₀ hP₀ hM₀ ga H hH L hL C hC hC'' z
  obtain ⟨hdet, hcomm, -⟩ := hAd O bar g ρ D P₀ M₀ hP₀ hM₀ ga H hH
  have hu : IsUnit H.det := isUnit_iff_ne_zero.mpr hdet
  have hHi : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H hu
  have hiH : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H hu
  have hbi := map_star_inv_mul H hdet
  set C'' := H * C * (H.map star)⁻¹ with hC''def

  let P'' : D.La →+ (Fin g → ℂ) := (Matrix.toLin' H⁻¹).toAddMonoidHom.comp (perC P₀ C'')
  have hP''apply : ∀ x, P'' x = H⁻¹ *ᵥ perC P₀ C'' x := fun x => by
    show Matrix.toLin' H⁻¹ (perC P₀ C'' x) = _
    rw [Matrix.toLin'_apply]
  have hdetInv : (H⁻¹).det ≠ 0 := by
    intro h0
    have h1 : (H⁻¹ * H).det = 1 := by rw [hiH, Matrix.det_one]
    rw [Matrix.det_mul, h0, zero_mul] at h1
    exact zero_ne_one h1
  have hcommInv : ∀ a, ρ a * H⁻¹ = H⁻¹ * ρ a := fun a => by
    calc ρ a * H⁻¹ = H⁻¹ * (H * ρ a) * H⁻¹ := by
            rw [← Matrix.mul_assoc, hiH, Matrix.one_mul]
      _ = H⁻¹ * (ρ a * H) * H⁻¹ := by rw [hcomm a]
      _ = H⁻¹ * ρ a * (H * H⁻¹) := by simp only [Matrix.mul_assoc]
      _ = H⁻¹ * ρ a := by rw [hHi, Matrix.mul_one]
  have hP'' : IsPeriod D ρ P'' :=
    hLin O bar g ρ D (perC P₀ C'') P'' H⁻¹ hC'' hdetInv hcommInv hP''apply
  have hga : ∀ x, P'' (ga x) = perC P₀ C x := fun x => by
    rw [hP''apply, perC_apply, perC_apply, hH.2 x, GlobalTheory.PerCoordU.star_mulVec_map,
      Matrix.mulVec_mulVec, hC''def]
    have e : H * C * (H.map star)⁻¹ * H.map star = H * C := by
      rw [Matrix.mul_assoc, hbi, Matrix.mul_one]
    rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_add, Matrix.mulVec_mulVec, hiH, Matrix.one_mulVec]
  have hcorr := hL (perC P₀ C) P'' hC hP'' hga z
  let h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearEquiv.ofLinear (Matrix.toLin' H) (Matrix.toLin' H⁻¹)
    (by rw [← Matrix.toLin'_mul, hHi, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, hiH, Matrix.toLin'_one])
  have happ : ∀ v, h v = H *ᵥ v := fun v => by
    show Matrix.toLin' H v = _
    rw [Matrix.toLin'_apply]
  have hfib := (hFib O bar g ρ D X s A S k P'' hP'').2.2.2.2 (perC P₀ C'') h hC''
    (fun x => by rw [happ, hP''apply, Matrix.mulVec_mulVec, hHi, Matrix.one_mulVec]) (L z)
  have hz : fibMap H L z = fun j => h (L z j) := by
    funext j
    rw [happ]
    simp [fibMap, Matrix.toLin'_apply]
  rw [hz, hfib]
  exact hcorr
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPtImm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem flat_of_eventuallyEq {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {Y : Scheme.{0}}
    {s s' : V → (Sp ℂ ⟶ Y)} {v₀ w : V} (h : s =ᶠ[𝓝 v₀] s') (hf : Flat s v₀ w) : Flat s' v₀ w := by
  intro U f hU
  have h0 : s v₀ = s' v₀ := h.eq_of_nhds
  have hfd : fderiv ℂ (fun v => valAt' (s' v) U f) v₀ = fderiv ℂ (fun v => valAt' (s v) U f) v₀ := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [h] with v hv
    rw [hv]
  rw [hfd]
  exact hf U f (h0 ▸ hU)

set_option maxHeartbeats 800000 in
theorem UpperTheory.Gal.W2.ptImm_of :
    UpperTheory.Gal.W2.FlatComp → UpperTheory.Gal.W2.FlatPre → UpperTheory.Gal.W2.PtFibre → UpperTheory.Gal.W2.ExpImm → UpperTheory.Gal.W2.PtImm := by
  intro hComp hPre hPF hExp O _ bar g ρ D X s A _ S k m B P b₀ hB hb₀ hP hu z₀ w hw
  have hBU : IsOpen (B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ))) := hB.prod isOpen_univ
  have hmem : (b₀, z₀) ∈ B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ)) := ⟨hb₀, Set.mem_univ _⟩
  have hnhds : B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ)) ∈ 𝓝 (b₀, z₀) := hBU.mem_nhds hmem
  have hS := S.hol m B P hB hP
  have hw1 : w.1 = 0 := by
    have h1 := hComp ((Fin m → ℂ) × (Fin k → Fin g → ℂ)) (KS.pow A k).left X (KS.pow A k).hom
      (fun bz => S.pt k (P bz.1) bz.2) (b₀, z₀) w hw
    have h2 : Flat (fun bz : (Fin m → ℂ) × (Fin k → Fin g → ℂ) => S.u (P bz.1)) (b₀, z₀) w := by
      refine flat_of_eventuallyEq ?_ h1
      filter_upwards [hnhds] with bz hbz
      exact (hPF O bar g ρ D X s A S k (P bz.1) (hP.1 _ hbz.1)).1 bz.2
    have hfst : HasFDerivAt (fun bz : (Fin m → ℂ) × (Fin k → Fin g → ℂ) => bz.1)
        (ContinuousLinearMap.fst ℂ (Fin m → ℂ) (Fin k → Fin g → ℂ)) (b₀, z₀) := hasFDerivAt_fst
    have h3 : Flat (fun b => S.u (P b)) b₀
        (ContinuousLinearMap.fst ℂ (Fin m → ℂ) (Fin k → Fin g → ℂ) w) :=
      (hPre (Fin m → ℂ) ((Fin m → ℂ) × (Fin k → Fin g → ℂ)) X B (fun b => S.u (P b)) hS.1
        (fun bz => bz.1) (ContinuousLinearMap.fst ℂ (Fin m → ℂ) (Fin k → Fin g → ℂ))
        (b₀, z₀) w hfst hb₀).mp h2
    exact hu _ h3
  have hw2 : ∀ j, w.2 j = 0 := by
    intro j
    have h1 := hComp ((Fin m → ℂ) × (Fin k → Fin g → ℂ)) (KS.pow A k).left A.left
      (Over.Hom.left (KS.pr A j)) (fun bz => S.pt k (P bz.1) bz.2) (b₀, z₀) w hw
    have h2 : Flat (fun bz : (Fin m → ℂ) × (Fin k → Fin g → ℂ) =>
        Over.Hom.left (S.ex (P bz.1) (bz.2 j))) (b₀, z₀) w := by
      refine flat_of_eventuallyEq ?_ h1
      filter_upwards [hnhds] with bz hbz
      exact (hPF O bar g ρ D X s A S k (P bz.1) (hP.1 _ hbz.1)).2.1 bz.2 j
    let L : (Fin m → ℂ) × (Fin k → Fin g → ℂ) →L[ℂ] (Fin m → ℂ) × (Fin g → ℂ) :=
      (ContinuousLinearMap.fst ℂ (Fin m → ℂ) (Fin k → Fin g → ℂ)).prod
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => Fin g → ℂ) j).comp
          (ContinuousLinearMap.snd ℂ (Fin m → ℂ) (Fin k → Fin g → ℂ)))
    have hL : HasFDerivAt (fun bz : (Fin m → ℂ) × (Fin k → Fin g → ℂ) => (bz.1, bz.2 j)) L (b₀, z₀) :=
      L.hasFDerivAt
    have hmem2 : ((b₀, z₀).1, (b₀, z₀).2 j) ∈ B ×ˢ (Set.univ : Set (Fin g → ℂ)) :=
      ⟨hb₀, Set.mem_univ _⟩
    have h3 : Flat (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => Over.Hom.left (S.ex (P bz.1) bz.2))
        (b₀, z₀ j) (L w) :=
      (hPre ((Fin m → ℂ) × (Fin g → ℂ)) ((Fin m → ℂ) × (Fin k → Fin g → ℂ)) A.left
        (B ×ˢ Set.univ) (fun bz => Over.Hom.left (S.ex (P bz.1) bz.2)) hS.2
        (fun bz => (bz.1, bz.2 j)) L (b₀, z₀) w hL hmem2).mp h2
    have hLw : L w = (0, w.2 j) := by
      simp [L, hw1]
    rw [hLw] at h3
    have hι : HasFDerivAt (fun z : Fin g → ℂ => (b₀, z))
        (ContinuousLinearMap.inr ℂ (Fin m → ℂ) (Fin g → ℂ)) (z₀ j) :=
      (hasFDerivAt_const b₀ (z₀ j)).prodMk (hasFDerivAt_id (z₀ j))
    have hmem3 : (fun z : Fin g → ℂ => (b₀, z)) (z₀ j) ∈ B ×ˢ (Set.univ : Set (Fin g → ℂ)) :=
      ⟨hb₀, Set.mem_univ _⟩
    have h4 : Flat (fun z : Fin g → ℂ => Over.Hom.left (S.ex (P b₀) z)) (z₀ j) (w.2 j) :=
      (hPre ((Fin m → ℂ) × (Fin g → ℂ)) (Fin g → ℂ) A.left
        (B ×ˢ Set.univ) (fun bz => Over.Hom.left (S.ex (P bz.1) bz.2)) hS.2
        (fun z => (b₀, z)) (ContinuousLinearMap.inr ℂ (Fin m → ℂ) (Fin g → ℂ))
        (z₀ j) (w.2 j) hι hmem3).mpr h3
    exact hExp X A g (S.u (P b₀)) (S.ex (P b₀)) (S.exp _ (hP.1 _ hb₀)) (z₀ j) (w.2 j) h4
  exact Prod.ext hw1 (_root_.funext hw2)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PLocSum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.locSum_of :
    UpperTheory.Gal.W2.LocTan → UpperTheory.Gal.W2.TorusCount → UpperTheory.Gal.W2.PiLattice → UpperTheory.Gal.W2.PtFibre → UpperTheory.Gal.W2.CorrChart → UpperTheory.Gal.W2.DetOfCharpoly → UpperTheory.Gal.W2.LocSum := by
  intro hTan hCount hPi hFib hChart hDet O _ bar g ρ D X s A _ S d hs k Z sZ c₁ c₂ h₁ h₂ P₀ M₀ hP hM co hco ga H hga T hT L hL hlat hinj hdT hdΘ
  classical
  have hrange : Submodule.span ℝ ((P₀.range : AddSubgroup (Fin g → ℂ)) : Set (Fin g → ℂ)) = ⊤ := by
    rw [AddMonoidHom.coe_range]; exact hP.2.2.2.1
  obtain ⟨hdisc, hspan⟩ := hPi g k P₀.range hP.2.2.1 hrange
  set Λk : AddSubgroup (Fin k → Fin g → ℂ) :=
    AddSubgroup.pi (Set.univ : Set (Fin k)) (fun _ => P₀.range) with hΛk
  have memΛ : ∀ z : Fin k → Fin g → ℂ, z ∈ Λk ↔ ∀ j, z j ∈ P₀.range := by
    intro z; simp [hΛk, AddSubgroup.mem_pi]
  obtain ⟨Fz, hFz1, hFz2, hFzc⟩ := hCount (Fin k → Fin g → ℂ) Λk hdisc hspan (fibMap H L)
    (fun z hz => (memΛ _).2 (hlat z ((memΛ z).1 hz))) hdΘ
  obtain ⟨hf1, hf2, hf3, hf4, hf5⟩ := hFib O bar g ρ D X s A S k P₀ hP
  have e0 : H * 0 * (H.map star)⁻¹ = 0 := by rw [Matrix.mul_zero, Matrix.zero_mul]
  have key : ∀ z, S.pt k P₀ z ≫ c₂ = S.pt k P₀ (fibMap H L z) ≫ c₁ := by
    intro z
    have h := hChart O bar g ρ D X s A S k Z c₁ c₂ P₀ M₀ hP hM ga H hga L hL 0
      (by rw [perC_zero]; exact hP) (by rw [e0, perC_zero]; exact hP) z
    rw [e0, perC_zero] at h
    exact h
  have fixIff : ∀ z, S.pt k P₀ z ≫ c₁ = S.pt k P₀ z ≫ c₂ ↔ fibMap H L z - z ∈ Λk := by
    intro z
    constructor
    · intro h
      have h' : S.pt k P₀ z = S.pt k P₀ (fibMap H L z) := hinj _ _ (h.trans (key z))
      exact (memΛ _).2 ((hf4 _ _).1 h'.symm)
    · intro h
      have h' := (hf4 (fibMap H L z) z).2 ((memΛ _).1 h)
      rw [key z, h']
  let mk : (Fin k → Fin g → ℂ) → CxPts ((GlobalTheory.KS.pow A k).hom ≫ s) (RingHom.id ℂ) :=
    fun z => ⟨S.pt k P₀ z, by rw [← Category.assoc, hf1 z]; exact S.ov P₀ hP⟩
  have mkInj : Set.InjOn mk Fz := by
    intro z hz z' hz' h
    have h1 : S.pt k P₀ z = S.pt k P₀ z' := congrArg Subtype.val h
    have h2 : z - z' ∈ Λk := (memΛ _).2 ((hf4 z z').1 h1)
    obtain ⟨w, _, hw⟩ := hFz2 z (hFz1 z hz)
    have a := hw z ⟨hz, by rw [sub_self]; exact zero_mem _⟩
    have b := hw z' ⟨hz', h2⟩
    exact a.trans b.symm
  refine ⟨Fz.image mk, ?_, ?_⟩
  · intro y
    rw [Finset.mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hf1 z, (fixIff z).2 (hFz1 z hz)⟩
    · rintro ⟨ho, hfx⟩
      obtain ⟨z, hz⟩ := hf3 y.1 ho
      have hz1 : fibMap H L z - z ∈ Λk := (fixIff z).1 (by rw [← hz]; exact hfx)
      obtain ⟨z', ⟨hz'F, hz'⟩, _⟩ := hFz2 z hz1
      refine ⟨z', hz'F, Subtype.ext ?_⟩
      show S.pt k P₀ z' = y.1
      rw [hz]; exact ((hf4 z z').2 ((memΛ _).1 hz')).symm
  · intro At hAt
    have hdet : ∀ y ∈ Fz.image mk, ∀ t : ℂ, (1 - t • At y).det =
        LinearMap.det (1 - t • T) * LinearMap.det (1 - t • fibMap H L) := by
      intro y hy t
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
      have hcp := hTan O bar g ρ D X s A S d hs k Z sZ c₁ c₂ h₁ h₂ P₀ M₀ hP hM co hco ga H hga T hT L hL z
        ((memΛ _).1 (hFz1 z hz)) (mk z) rfl (At (mk z)) (hAt _ hy)
      exact hDet _ _ T (fibMap H L) _ _ hcp t
    have hdet1 : ∀ y ∈ Fz.image mk, (1 - At y).det =
        LinearMap.det (1 - T) * LinearMap.det (1 - fibMap H L) := by
      intro y hy
      have h := hdet y hy 1
      simpa only [one_smul] using h
    refine ⟨fun y hy => by rw [hdet1 y hy]; exact mul_ne_zero hdT hdΘ, fun t => ?_⟩
    have hterm : ∀ y ∈ Fz.image mk, lefTerm (At y) t =
        LinearMap.det (1 - t • T) * LinearMap.det (1 - t • fibMap H L) /
          (LinearMap.det (1 - T) * LinearMap.det (1 - fibMap H L)) := by
      intro y hy
      unfold lefTerm
      rw [hdet y hy t, hdet1 y hy]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_image_of_injOn mkInj, nsmul_eq_mul, hFzc]
    field_simp
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPerCoordLoc
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR
open GlobalTheory.PeriodCoord (realMap realMap_apply realMap_inj colMat)

namespace UpperTheory.Gal.W2

theorem perCoordLoc_of : PerCoordLoc := by
  intro O _ bar g ρ D P₀ M₀ hP₀ hM₀ d co hco m B P b₀ hB hb₀ hHol hPb₀
  obtain ⟨α, β, hαβ⟩ := PerCoordU.exists_colMat_per hP₀
  obtain ⟨A, hA⟩ : ∃ A : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ, ∀ b, A b = colMat α ⇑(P b) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Bm, hBm⟩ : ∃ Bm : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ, ∀ b, Bm b = colMat β ⇑(P b) :=
    ⟨_, fun _ => rfl⟩
  have hrep : ∀ b ∈ B, ∀ x, P b x = realMap (A b) (Bm b) (P₀ x) := by
    intro b hb x
    rw [hA, hBm]
    exact hαβ _ (hHol.1 b hb) x
  have hPd : ∀ (x : D.La) (i : Fin g), DifferentiableOn ℂ (fun b => P b x i) B :=
    fun x i => differentiableOn_pi.1 (hHol.2 x) i
  have hAd : ∀ i j, DifferentiableOn ℂ (fun b => A b i j) B := by
    intro i j
    simp only [hA, colMat, Matrix.of_apply]
    exact DifferentiableOn.fun_sum fun x _ => (hPd x i).const_mul _
  have hBd : ∀ i j, DifferentiableOn ℂ (fun b => Bm b i j) B := by
    intro i j
    simp only [hBm, colMat, Matrix.of_apply]
    exact DifferentiableOn.fun_sum fun x _ => (hPd x i).const_mul _
  have hAc : ContinuousOn A B :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hAd i j).continuousOn
  have hdet : ContinuousOn (fun b => (A b).det) B :=
    (continuous_id.matrix_det).comp_continuousOn hAc
  have hSo : IsOpen (B ∩ (fun b => (A b).det) ⁻¹' {0}ᶜ) :=
    hdet.isOpen_inter_preimage hB isOpen_compl_singleton
  have hAB0 : A b₀ = 1 ∧ Bm b₀ = 0 := by
    apply realMap_inj
    apply PerCoordU.ext_per hP₀
    intro x
    have h1 := hrep b₀ hb₀ x
    rw [hPb₀] at h1
    rw [← h1, realMap_apply]
    simp
  have hb₀S : b₀ ∈ B ∩ (fun b => (A b).det) ⁻¹' {0}ᶜ := by
    refine ⟨hb₀, ?_⟩
    simp [hAB0.1]
  have hnhds : B ∩ (fun b => (A b).det) ⁻¹' {0}ᶜ ∈ 𝓝 b₀ := hSo.mem_nhds hb₀S
  have hinvd : ∀ i j, DifferentiableOn ℂ (fun b => (A b)⁻¹ i j) (B ∩ (fun b => (A b).det) ⁻¹' {0}ᶜ) :=
    RiemannRel.differentiableOn_left_inverse A (fun b => (A b)⁻¹)
      (fun i j => (hAd i j).mono Set.inter_subset_left)
      (fun b hb => Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (by simpa using hb.2)))
  obtain ⟨gL, hgL⟩ := LinearMap.exists_leftInverse_of_injective co (LinearMap.ker_eq_bot.mpr hco.1)
  refine ⟨fun b => gL ((A b)⁻¹ * Bm b), ?_, ?_, ?_⟩
  · rw [differentiableAt_pi]
    intro k
    have e : (fun b => gL ((A b)⁻¹ * Bm b) k) =
        fun b => ∑ i, ∑ j, ((A b)⁻¹ * Bm b) i j * gL (Matrix.single i j 1) k :=
      funext fun b => PerCoordU.coords_sum gL _ k
    rw [e]
    refine DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_sum fun j _ => ?_
    refine DifferentiableAt.mul_const ?_ _
    simp only [Matrix.mul_apply]
    refine DifferentiableAt.fun_sum fun l _ => DifferentiableAt.fun_mul ?_ ?_
    · exact (hinvd i l).differentiableAt hnhds
    · exact (hBd l j).differentiableAt (hB.mem_nhds hb₀)
  · simp only
    rw [hAB0.1, hAB0.2, Matrix.mul_zero, map_zero]
  · filter_upwards [hnhds] with b hb
    have hdetb : IsUnit (A b).det := isUnit_iff_ne_zero.mpr (by simpa using hb.2)
    have hCmem : (A b)⁻¹ * Bm b ∈ LinearMap.range co := by
      rw [hco.2]
      exact PerCoordU.mem_Tsp_of_period hP₀ (hHol.1 b hb.1) hM₀.2.2 (hrep b hb.1) hdetb.ne_zero
    obtain ⟨y, hy⟩ := hCmem
    have hcy : co (gL ((A b)⁻¹ * Bm b)) = (A b)⁻¹ * Bm b := by
      rw [← hy, ← LinearMap.comp_apply gL co, hgL, LinearMap.id_apply]
    letI := Matrix.invertibleOfIsUnitDet (A b) hdetb
    refine ⟨Matrix.toLinearEquiv' (A b) this, fun x => ?_⟩
    simp only [hcy, perC_apply]
    rw [hrep b hb.1 x, realMap_apply]
    show A b *ᵥ P₀ x + Bm b *ᵥ star (P₀ x) = A b *ᵥ (P₀ x + ((A b)⁻¹ * Bm b) *ᵥ star (P₀ x))
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv_cancel_left _ _ hdetb]

end UpperTheory.Gal.W2
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTanChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.tanChart_of :
    UpperTheory.Gal.W2.TanDeriv → UpperTheory.Gal.W2.FlatAffine → UpperTheory.Gal.W2.ConjCharpoly → UpperTheory.Gal.W2.TanChart := by
  intro hTD hFA hCC E _ _ _ d hd Z Y sZ s' c₁ c₂ h₁ h₂ B s v₀ hB hv hs hs' hflat G G' hG hGv hev y hy0 A hT
  obtain ⟨U, W, hW1, hW2, t, hy, hU, hW, φ, hφ1, hφ2, hφ3, hφ4⟩ := hT
  obtain ⟨ψ, hψ1, hψ2⟩ := hTD E Y s' B s v₀ hB hv hs hs' y hy0 W hy
  let e₁ : Fin d → Sec s' W := fun l => Sec.res s' hW1 (appSec sZ s' c₁ U (t l))
  let e₂ : Fin d → Sec s' W := fun l => Sec.res s' hW2 (appSec sZ s' c₂ U (t l))
  have hφ2' : ∀ l, φ (KaehlerDifferential.D ℂ (Sec s' W) (e₁ l)) = Pi.single l 1 := hφ2
  have hφ3' : ∀ j, φ (KaehlerDifferential.D ℂ (Sec s' W) (e₂ j)) = fun l => A j l := hφ3
  let N : Set E := {v | v ∈ B ∧ ⊤ ≤ s v ⁻¹ᵁ W}
  have hNo : IsOpen N := (hs W 0).1
  have hv₀N : v₀ ∈ N := by
    refine ⟨hv, ?_⟩
    have := hy
    simp only [CxPts.ptsIn, Set.mem_setOf_eq] at this
    rw [hy0] at this
    exact this
  have hNn : N ∈ 𝓝 v₀ := hNo.mem_nhds hv₀N
  have hK : ∀ ω, ψ ω = ∑ l, (φ ω) l • ψ (KaehlerDifferential.D ℂ (Sec s' W) (e₁ l)) := by
    intro ω
    set ω' := ω - ∑ l, (φ ω) l • KaehlerDifferential.D ℂ (Sec s' W) (e₁ l) with hω'
    have hφω' : φ ω' = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hω', map_sub, map_sum]
      simp only [map_smul, hφ2']
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    obtain ⟨m, b, ω'', hb0, hωeq⟩ := hφ4 ω' hφω'
    have hψω' : ψ ω' = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hωeq, map_sum]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [hψ1, hb0 i, zero_smul]
    have hω : ω = ω' + ∑ l, (φ ω) l • KaehlerDifferential.D ℂ (Sec s' W) (e₁ l) := by
      rw [hω']
      abel
    conv_lhs => rw [hω]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), hψω', zero_add, map_sum]
    simp only [map_smul]
  let τ : E →ₗ[ℂ] Fin d → ℂ :=
    LinearMap.pi (fun l => ((ψ (KaehlerDifferential.D ℂ (Sec s' W) (e₁ l)) : E →L[ℂ] ℂ) : E →ₗ[ℂ] ℂ))
  have hτ : ∀ w l, τ w l = ψ (KaehlerDifferential.D ℂ (Sec s' W) (e₁ l)) w := fun w l => rfl
  have hinj : Function.Injective τ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro w hw
    apply hflat
    refine hFA E Y B s v₀ w hB hv hs W hW hv₀N.2 (fun f => ?_)
    have hf : fderiv ℂ (fun v => valAt' (s v) W f) v₀ = ψ (KaehlerDifferential.D ℂ (Sec s' W) f) :=
      (hψ2 f).symm
    rw [hf, hK, ContinuousLinearMap.sum_apply]
    refine Finset.sum_eq_zero (fun l _ => ?_)
    rw [ContinuousLinearMap.smul_apply, ← hτ, hw]
    simp
  have hval : ∀ (c : Y ⟶ Z) (hc : W ≤ c ⁻¹ᵁ U) (f : Sec sZ U) (v : E), ⊤ ≤ s v ⁻¹ᵁ W →
      valAt' (s v) W (Sec.res s' hc (appSec sZ s' c U f)) = valAt' (s v ≫ c) U f := by
    intro c hc f v hvW
    exact (valAt'_res (s v) hc _ hvW).trans (valAt'_comp (s v) c U f)
  have hrel : ∀ w, τ (G' w) = A *ᵥ τ w := by
    intro w
    funext j
    have hd1 : DifferentiableAt ℂ (fun v => valAt' (s v) W (e₁ j)) v₀ :=
      ((hs W (e₁ j)).2).differentiableAt hNn
    have hGN : ∀ᶠ v in 𝓝 v₀, G v ∈ N := by
      have hNn' : N ∈ 𝓝 (G v₀) := by rw [hGv]; exact hNn
      exact hG.continuousAt.preimage_mem_nhds hNn'
    have heq : (fun v => valAt' (s v) W (e₂ j)) =ᶠ[𝓝 v₀]
        (fun v => valAt' (s v) W (e₁ j)) ∘ G := by
      filter_upwards [hNn, hGN, hev] with v hvN hGvN hevv
      simp only [Function.comp_apply]
      rw [hval c₂ hW2 (t j) v hvN.2, hval c₁ hW1 (t j) (G v) hGvN.2, hevv]
    have hd1' : HasFDerivAt (fun v => valAt' (s v) W (e₁ j))
        (fderiv ℂ (fun v => valAt' (s v) W (e₁ j)) v₀) (G v₀) := by
      rw [hGv]; exact hd1.hasFDerivAt
    have hcomp := hd1'.comp v₀ hG
    have hfd : fderiv ℂ (fun v => valAt' (s v) W (e₂ j)) v₀ =
        (fderiv ℂ (fun v => valAt' (s v) W (e₁ j)) v₀).comp G' := by
      rw [heq.fderiv_eq]
      exact hcomp.fderiv
    have h2 : ψ (KaehlerDifferential.D ℂ (Sec s' W) (e₂ j)) w = ∑ l, A j l * τ w l := by
      rw [hK, hφ3', ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [ContinuousLinearMap.smul_apply, smul_eq_mul, hτ]
    rw [Matrix.mulVec, dotProduct, ← h2, hψ2, hfd, hτ, hψ2]
    rfl
  exact hCC E d hd τ (G' : E →ₗ[ℂ] E) A hinj hrel
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTorusCount
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem det_lattice_restrict_eq_det {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Lz : Submodule ℤ E) [DiscreteTopology Lz] [IsZLattice ℝ Lz]
    (f : E →ₗ[ℝ] E) (fL : Lz →ₗ[ℤ] Lz) (hfL : ∀ x, (fL x : E) = f x) :
    ((LinearMap.det fL : ℤ) : ℝ) = LinearMap.det f := by
  haveI := ZLattice.module_free ℝ Lz
  haveI := ZLattice.module_finite ℝ Lz
  let b := Module.Free.chooseBasis ℤ Lz
  let bR := Module.Basis.ofZLatticeBasis ℝ Lz b
  rw [← LinearMap.det_toMatrix b, ← LinearMap.det_toMatrix bR, ← eq_intCast (Int.castRingHom ℝ),
    RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
    Module.Basis.ofZLatticeBasis_apply, ← hfL, Module.Basis.ofZLatticeBasis_repr_apply]
  rfl

private theorem exists_lattice_reps {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : AddSubgroup E) (hd : DiscreteTopology L)
    (hs : Submodule.span ℝ (L : Set E) = ⊤) (f : E →ₗ[ℝ] E) (hf : ∀ z ∈ L, f z ∈ L)
    (hdet : LinearMap.det f ≠ 0) :
    ∃ Fz : Finset E, (∀ z ∈ Fz, f z ∈ L) ∧ (∀ z, f z ∈ L → ∃! z', z' ∈ Fz ∧ z - z' ∈ L) ∧
      (Fz.card : ℝ) = |LinearMap.det f| := by
  classical
  let Lz : Submodule ℤ E := AddSubgroup.toIntSubmodule L
  haveI : DiscreteTopology Lz := hd
  haveI : IsZLattice ℝ Lz := ⟨hs⟩
  haveI := ZLattice.module_free ℝ Lz
  haveI := ZLattice.module_finite ℝ Lz
  let fL : Lz →ₗ[ℤ] Lz :=
    { toFun := fun x => ⟨f x, hf x x.2⟩
      map_add' := by intro x y; ext; simp
      map_smul' := by intro c x; ext; simp }
  have hfL : ∀ x, (fL x : E) = f x := fun x => rfl
  have hdetZ := det_lattice_restrict_eq_det Lz f fL hfL
  have hdetL : LinearMap.det fL ≠ 0 := by
    intro h; apply hdet; rw [← hdetZ, h]; simp
  let fe := LinearMap.equivOfDetNeZero f hdet
  have hfe : ∀ z, fe z = f z := fun z => rfl
  have finj : Function.Injective f := by
    intro x y h; apply fe.injective; rw [hfe, hfe, h]
  have hinj : Function.Injective fL := fun x y h => Subtype.ext (finj (congrArg Subtype.val h))
  let N := LinearMap.range fL
  let e := LinearEquiv.ofInjective fL hinj
  have hcard := Submodule.natAbs_det_equiv N e
  have hcomp : N.subtype ∘ₗ (e : Lz →+ N).toIntLinearMap = fL := by ext x; rfl
  rw [hcomp] at hcard
  haveI : Finite (Lz ⧸ N) :=
    Nat.finite_of_card_ne_zero (by rw [← hcard]; exact Int.natAbs_ne_zero.mpr hdetL)
  letI := Fintype.ofFinite (Lz ⧸ N)
  let s : (Lz ⧸ N) → E := fun q => fe.symm ((Quotient.out q : Lz) : E)
  have hs_f : ∀ q, f (s q) = ((Quotient.out q : Lz) : E) := fun q => by
    rw [← hfe]; exact fe.apply_symm_apply _
  have hsinj : Function.Injective s := by
    intro q q' h
    have h1 : (Quotient.out q : Lz) = Quotient.out q' := Subtype.ext (by rw [← hs_f, ← hs_f, h])
    rw [← Submodule.Quotient.mk_out q, ← Submodule.Quotient.mk_out q', h1]
  have key : ∀ z (hz : f z ∈ L) (q' : Lz ⧸ N),
      z - s q' ∈ L ↔ q' = Submodule.Quotient.mk (⟨f z, hz⟩ : Lz) := by
    intro z hz q'
    constructor
    · intro h
      have hm : (⟨f z, hz⟩ : Lz) - Quotient.out q' ∈ N :=
        ⟨⟨z - s q', h⟩, by ext; simp [fL, hs_f]⟩
      rw [← Submodule.Quotient.eq, Submodule.Quotient.mk_out] at hm
      exact hm.symm
    · intro h
      have hm : (⟨f z, hz⟩ : Lz) - Quotient.out q' ∈ N := by
        rw [← Submodule.Quotient.eq, Submodule.Quotient.mk_out, h]
      obtain ⟨l, hl⟩ := hm
      have : f (l : E) = f (z - s q') := by
        rw [← hfL, hl, map_sub, hs_f]; rfl
      rw [← finj this]; exact l.2
  refine ⟨Finset.univ.image s, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hz
    rw [hs_f]; exact (Quotient.out q).2
  · intro z hz
    refine ⟨s (Submodule.Quotient.mk (⟨f z, hz⟩ : Lz)), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _),
      (key z hz _).mpr rfl⟩, ?_⟩
    rintro z' ⟨hz', hzz'⟩
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hz'
    rw [(key z hz q).mp hzz']
  · rw [Finset.card_image_of_injective _ hsinj, Finset.card_univ, ← Nat.card_eq_fintype_card, ← hcard,
      ← hdetZ, Nat.cast_natAbs, Int.cast_abs]

theorem UpperTheory.Gal.W2.torusCount_of :
    UpperTheory.Gal.W2.DetReal → UpperTheory.Gal.W2.TorusCount := by
  intro hDR W _ _ _ Λ hd hs Θ hΘ hdet
  let f : W →ₗ[ℝ] W := (1 - Θ).restrictScalars ℝ
  have hR : ((LinearMap.det f : ℝ) : ℂ) = _ := hDR W (1 - Θ)
  have hdf : LinearMap.det f = Complex.normSq (LinearMap.det (1 - Θ)) := by
    apply Complex.ofReal_injective
    rw [hR, Complex.mul_conj]
  have hfz : ∀ z, f z ∈ Λ ↔ Θ z - z ∈ Λ := by
    intro z
    show (1 - Θ) z ∈ Λ ↔ _
    rw [LinearMap.sub_apply, Module.End.one_apply, ← neg_sub, neg_mem_iff]
  have hfL : ∀ z ∈ Λ, f z ∈ Λ := fun z hz => (hfz z).mpr (sub_mem (hΘ z hz) hz)
  have hpos : 0 < LinearMap.det f := by rw [hdf]; exact Complex.normSq_pos.mpr hdet
  obtain ⟨Fz, h1, h2, h3⟩ := exists_lattice_reps Λ hd hs f hfL hpos.ne'
  refine ⟨Fz, fun z hz => (hfz z).mp (h1 z hz), fun z hz => h2 z ((hfz z).mpr hz), ?_⟩
  rw [Complex.mul_conj, ← hdf, ← abs_of_pos hpos, ← h3]
  norm_cast
end
