module

public import Mathlib

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnimodGenus
open NumberField

noncomputable section

namespace PI.UG

section Defs

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

def isom (h : V →ₗ⋆[K] V →ₗ[K] K) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∀ x y, h (g x) (g y) = h x y}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro a b ha hb x y
    change h (a (b x)) (a (b y)) = h x y
    rw [ha, hb]
  inv_mem' := by
    intro a ha x y
    have := ha (a.symm x) (a.symm y)
    change h (a.symm x) (a.symm y) = h x y
    simpa using this.symm

def gmap (g : V ≃ₗ[K] V) (L : Submodule R V) : Submodule R V :=
  L.map ((g : V →ₗ[K] V).restrictScalars R)

def dual (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) : Submodule R V :=
  ⨅ y ∈ L, (1 : Submodule R K).comap ((h y).restrictScalars R)

def IsUnimodular (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) : Prop :=
  dual h L = L

def locS {W : Type*} [AddCommGroup W] [Module R W] (S : Submonoid R) (L : Submodule R W) :
    Submodule R W where
  carrier := {x | ∃ s ∈ S, s • x ∈ L}
  zero_mem' := ⟨1, S.one_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
    refine ⟨s * t, S.mul_mem hs ht, ?_⟩
    have e : (s * t) • (x + y) = t • (s • x) + s • (t • y) := by
      rw [smul_add, mul_smul, smul_comm s t x, mul_smul]
    rw [e]
    exact L.add_mem (L.smul_mem t hx) (L.smul_mem s hy)
  smul_mem' := by
    rintro r x ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    rw [smul_comm]
    exact L.smul_mem r hx

def hcompl (p : Ideal R) : Submonoid R :=
  Submonoid.closure {s | s ∉ p ∧ ∀ t : R, algebraMap R K t = star (algebraMap R K s) → t ∉ p}

def loc {W : Type*} [AddCommGroup W] [Module R W] (p : Ideal R) (L : Submodule R W) :
    Submodule R W :=
  locS (hcompl (K := K) p) L

def SameGenus (h : V →ₗ⋆[K] V →ₗ[K] K) (L M : Submodule R V) : Prop :=
  ∀ p : Ideal R, p.IsMaximal → ∃ g ∈ isom h, gmap g (loc (K := K) p L) = loc (K := K) p M

end Defs

abbrev Sp (E : Type) (n : ℕ) : Type := Fin n → E

def hStd (E : Type) [Field E] [StarRing E] (n : ℕ) : Sp E n →ₗ⋆[E] Sp E n →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ (starRingEnd E) (RingHom.id E) (fun x y => ∑ i, star (x i) * y i)
    (by intro x y z; simp [add_mul, Finset.sum_add_distrib])
    (by intro c x y; simp [Finset.mul_sum, mul_assoc, starRingEnd_apply])
    (by intro x y z; simp [mul_add, Finset.sum_add_distrib])
    (by intro c x y; simp [Finset.mul_sum, mul_left_comm])

def stdLat (E : Type) [Field E] [NumberField E] (n : ℕ) : Submodule (𝓞 E) (Sp E n) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)

def IsCMUnram (K : Type*) [Field K] [NumberField K] [StarRing K] : Prop :=
  IsTotallyComplex K ∧ (∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a)) ∧
    ∀ P : Ideal (RingOfIntegers K), P.IsMaximal →
      ∃ θ t : RingOfIntegers K, algebraMap (RingOfIntegers K) K t =
        star (algebraMap (RingOfIntegers K) K θ) ∧ θ - t ∉ P

end PI.UG

namespace PI

open PI.UG

def UnimodGenus : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ), IsCMUnram E →
    ∀ N : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E N → IsUnimodular (hStd E n) N →
      SameGenus (hStd E n) (stdLat E n) N

end PI
end
end

section -- merged from Formalism.PeriodIntegrals.LocalEnd
open NumberField IsDedekindDomain

namespace PI

def LocalEndHomeo : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (τ : v.adicCompletion F →+* v.adicCompletion F),
    Continuous τ ∧ ∃ τ' : v.adicCompletion F →+* v.adicCompletion F, Continuous τ' ∧ ∀ a, τ (τ' a) = a

end PI
end

section -- merged from Formalism.PeriodIntegrals.PowBddInt
namespace PI

open Matrix

def PowBddInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (k : ℕ) (γ : Matrix (Fin k) (Fin k) E) (N : ℕ), 0 < N →
    (∀ (n : ℕ) (i j : Fin k), IsIntegral ℤ ((N : E) * (γ ^ n) i j)) →
    ∀ i, IsIntegral ℤ (γ.charpoly.coeff i)

end PI
end

section -- merged from Formalism.PeriodIntegrals.Minkowski
namespace PI

def minkowskiExp (N p : ℕ) : ℕ := ∑ i ∈ Finset.range (N + 1), N / (p ^ i * (p - 1))

def minkowskiM (N : ℕ) : ℕ := ∏ p ∈ (Finset.range (N + 2)).filter Nat.Prime, p ^ minkowskiExp N p

def MinkowskiBound : Prop :=
  ∀ (N : ℕ) (G : Subgroup (Matrix.GeneralLinearGroup (Fin N) ℤ)), Finite G →
    Nat.card G ∣ minkowskiM N

end PI
end

section -- merged from Formalism.PeriodIntegrals.PrimeSums
namespace PI

def PrimeLogOverP : Prop :=
  ∀ Y : ℝ, 1 < Y → ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ Y) →
    ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ≤ Real.log Y

def PrimeLogOverPSqTail : Prop :=
  ∀ X : ℝ, 0 < X → ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ X < (p : ℝ)) →
    ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 2.04 / X

end PI
end

section -- merged from Formalism.PeriodIntegrals.HeisDefs
namespace PI

section Heis

variable {T I J : Type} [Fintype T] [Fintype I] [Fintype J]

noncomputable def HfG (A : ℝ) (z w : T → I → J → ℂ) : ℂ :=
  (∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j)) / (A : ℂ)

noncomputable def UG (A : ℝ) (x : T → I → J → ℂ) (G : (T → I → J → ℂ) → ℂ) : (T → I → J → ℂ) → ℂ :=
  fun z => G (z + x) * Complex.exp (-(Real.pi : ℂ) * HfG A z x - (Real.pi : ℂ) * HfG A x x / 2)

end Heis

end PI
end

section -- merged from Formalism.PeriodIntegrals.OkpInert
open NumberField

noncomputable section

namespace PI

def W2pair (p : ℕ) [Fact p.Prime] : Set (ℂ_[p] × ℂ_[p]) :=
  closure (Subring.closure {x : ℂ_[p] × ℂ_[p] | ∃ ζ : ℂ_[p], ζ ^ (p ^ 2 - 1) = 1 ∧ x = (ζ, ζ ^ p)} :
    Set (ℂ_[p] × ℂ_[p]))

def OkpInert : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ) [Fact p.Prime] (τ : K →+* ℂ_[p]),
    Module.finrank ℚ K = 2 → (∃ x, c x ≠ x) → p ≠ 2 → (Ideal.span {(p : 𝓞 K)}).IsPrime →
    closure (Set.range fun a : 𝓞 K => (τ (a : K), τ (c (a : K)))) = W2pair p

end PI
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryDense
open Matrix
open scoped ComplexOrder

namespace PI

def UnitaryDense : Prop :=
  ∀ (n : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ),
    (∀ u : Matrix (Fin n) (Fin n) ℂ, uᴴ * u = 1 →
      MvPolynomial.eval (fun x : Fin n × Fin n => u x.1 x.2) P = 0) → P = 0

def FramesDense : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ℕ) (G : ι → Matrix (Fin n) (Fin n) ℂ), (∀ τ, (G τ).PosDef) →
    ∀ P : MvPolynomial (ι × Fin n × Fin n) ℂ,
      (∀ y : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (y τ)ᴴ * G τ * y τ = 1) →
        MvPolynomial.eval (fun x : ι × Fin n × Fin n => y x.1 x.2.1 x.2.2) P = 0) → P = 0

end PI
end

section -- merged from Formalism.PeriodIntegrals.UnimodIdx
open MeasureTheory Topology

noncomputable section

namespace PI

def UnimodIdx : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [SigmaFinite μ], μ.IsHaarMeasure →
    ∀ (U : ℕ → Subgroup G), (∀ n, IsOpen (U n : Set G)) → (∀ V ∈ 𝓝 (1 : G), ∃ n, (U n : Set G) ⊆ V) →
    ∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) →
    (∀ x : G, (K.map (MulAut.conj x).toMonoidHom).relIndex K = (K.map (MulAut.conj x⁻¹).toMonoidHom).relIndex K) →
    μ.IsMulRightInvariant

end PI

end
end

section -- merged from Formalism.PeriodIntegrals.DiscIn
namespace PI

def DiscFactor : Prop :=
  ∀ (f : ℂ → ℂ) (z₀ : ℂ) (r R₁ : ℝ), 0 < R₁ → R₁ < r →
    DifferentiableOn ℂ f (Metric.closedBall z₀ r) → f z₀ ≠ 0 →
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ) (h : ℂ → ℂ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall z₀ R₁ ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      DifferentiableOn ℂ h (Metric.closedBall z₀ r) ∧
      (∀ z ∈ Metric.closedBall z₀ R₁, h z ≠ 0) ∧
      ∀ z ∈ Metric.closedBall z₀ r, f z = (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z

def DiscLog : Prop :=
  ∀ (f : ℂ → ℂ) (z₀ : ℂ) (R : ℝ), DifferentiableOn ℂ f (Metric.ball z₀ R) →
    (∀ z ∈ Metric.ball z₀ R, f z ≠ 0) →
    ∃ g : ℂ → ℂ, g z₀ = 0 ∧ (∀ z ∈ Metric.ball z₀ R, HasDerivAt g (deriv f z / f z) z) ∧
      ∀ z ∈ Metric.ball z₀ R, f z = f z₀ * Complex.exp (g z)

end PI
end

section -- merged from Formalism.PeriodIntegrals.WittUnram
noncomputable section

namespace PI

abbrev WF (p f : ℕ) [Fact p.Prime] := WittVector p (GaloisField p f)

def IsWittIdent {p f : ℕ} [Fact p.Prime] {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] (σ : Qq ≃+* Qq)
    (φ : WF p f ≃+* W) : Prop :=
  ∀ x : WF p f, σ (algebraMap W Qq (φ x)) = algebraMap W Qq (φ (WittVector.frobenius x))

def WittUnram : Prop :=
  ∀ (p f : ℕ) [Fact p.Prime] (W Qq : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] (σ : Qq ≃+* Qq),
    IsFractionRing W Qq → Irreducible (p : W) → Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ f →
    IsAdicComplete (Ideal.span {(p : W)}) W →
    (∀ x : W, ∃ y : W, σ (algebraMap W Qq x) = algebraMap W Qq (x ^ p + (p : W) * y)) →
    ∃ φ : WF p f ≃+* W, IsWittIdent σ φ

end PI
end
end

section -- merged from Formalism.PeriodIntegrals.FglPhSplit
noncomputable section

namespace PI.FglPhSplit

open Classical

def expMv {K : Type*} [Field K] {σ : Type*} (F : MvPowerSeries σ K) : MvPowerSeries σ K :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α (F ^ n) / (n.factorial : K)

structure Dat (K : Type*) [Field K] where
  l : PowerSeries K
  ex : PowerSeries K
  ph : PowerSeries K

namespace Dat

variable {K : Type*} [Field K] (g : Dat K) {σ : Type*}

end Dat

end PI.FglPhSplit

end
end

section -- merged from Formalism.PeriodIntegrals.HermLatFin
open NumberField Matrix
open scoped ComplexOrder

noncomputable section

namespace PI.HermLatFin

def herm {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : E :=
  ∑ i, ∑ j, σ (x i) * J i j * y j

def IsLat {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin n → E)) = ⊤

def admitted {E : Type} [Field E] [NumberField E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (T : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  IsLat L ∧ (∀ x ∈ L, ∀ y ∈ L, IsIntegral ℤ (herm σ J x y)) ∧
    ∀ y : Fin n → E, (∀ x ∈ L, IsIntegral ℤ (herm σ J x y)) → (T : E) • y ∈ L

def IsUJ {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J g : Matrix (Fin n) (Fin n) E) : Prop :=
  (g.map σ)ᵀ * J * g = J

def HermLatFin : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (T : ℕ),
    (∀ τ : E →+* ℂ, ∀ a : E, τ (σ a) = starRingEnd ℂ (τ a)) →
    (∀ τ : E →+* ℂ, (J.map τ).PosDef) →
    0 < T →
    ∃ S : Set (Submodule (𝓞 E) (Fin n → E)), S.Finite ∧
      ∀ L, admitted σ J T L → ∃ L' ∈ S, ∃ g : Matrix (Fin n) (Fin n) E, IsUJ σ J g ∧
        (fun x => g *ᵥ x) '' (L' : Set (Fin n → E)) = (L : Set (Fin n → E))

end PI.HermLatFin
end
end

section -- merged from Formalism.PeriodIntegrals.SplitIntLoc
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.SplitIntLoc

section Defs

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

end Defs

section Points

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]

def tensInt (R : Type) [CommRing R] [Algebra F R] (S₁ : Subring E) (S₂ : Subring R) :
    Subring (E ⊗[F] R) :=
  Subring.closure (Set.range (fun x : S₁ => (x : E) ⊗ₜ[F] (1 : R)) ∪
    Set.range (fun y : S₂ => (1 : E) ⊗ₜ[F] (y : R)))

end Points

def intOE (E : Type) [Field E] [NumberField E] : Subring E := (algebraMap (𝓞 E) E).range

end PI.SplitIntLoc

namespace PI

open PI.SplitIntLoc in
def SplitIntLoc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F))
    (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F),
    (∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a)) →
    ∀ x, x ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring ↔
      (spl x).1 ∈ v.adicCompletionIntegers F ∧ (spl x).2 ∈ v.adicCompletionIntegers F

end PI
end
end

section -- merged from Formalism.PeriodIntegrals.WwInjective
noncomputable section

namespace PI.WwInjective

namespace KM

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ)

abbrev XZ (Lt : Type) (N0 N1 : ℕ) : Type := (Lt × ℕ × Fin N0) ⊕ (Lt × Fin N0 × Fin N1)

def ColChoice (nu : Lt → YoungDiagram) : Type :=
  ∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin N1

def applyAt0 (l : ℕ) [Fact l.Prime] (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (XZ Lt N0 N1) ℤ) : MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l] :=
  ∑ μ ∈ P.support, MvPolynomial.monomial (Finsupp.sumFinsuppEquivProdFinsupp μ).1
    (((AddMonoidAlgebra.coeff P μ : ℤ) : ℂ_[l]) *
      ((Finsupp.sumFinsuppEquivProdFinsupp μ).2.prod fun _ n => (n.factorial : ℂ_[l])) *
      MvPowerSeries.coeff (Finsupp.sumFinsuppEquivProdFinsupp μ).2 Th)

def nablaX (nu : Lt → YoungDiagram) (J : ColChoice N0 nu) : MvPolynomial (Lt × ℕ × Fin N0) ℤ :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i k : Fin ((nu s).colLen c) =>
    (MvPolynomial.X (s, (i : ℕ), J s c k) : MvPolynomial (Lt × ℕ × Fin N0) ℤ))

end KM

def DeX {Lt k : Type} [Fintype Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (y : Lt → Fin N → ℕ → k) :
    MvPolynomial (Lt × ℕ × Fin N) k :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i j : Fin ((nu s).colLen c) =>
    ∑ a : Fin N, MvPolynomial.C (y s a (j : ℕ)) * MvPolynomial.X (s, (i : ℕ), a))

def minY {Lt k : Type} [Fintype Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (J : KM.ColChoice N nu)
    (y : Lt → Fin N → ℕ → k) : k :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i j : Fin ((nu s).colLen c) => y s (J s c i) (j : ℕ))

def WwInjective : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N : ℕ) (nu : Lt → YoungDiagram)
    (ph : Module.Dual ℂ_[l] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[l])),
    (∀ y, ph (DeX N nu y) = 0) → ∀ J, ph (MvPolynomial.map (Int.castRingHom _) (KM.nablaX N nu J)) = 0

end PI.WwInjective
end
end

section -- merged from Formalism.PeriodIntegrals.BiaddOfCube
noncomputable section

open Classical

namespace PI.BiaddOfCube

def IsIntP {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ‖x‖ ≤ 1

def IntegralMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, IsIntP (MvPowerSeries.coeff n F)

def expMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α (F ^ n) / (n.factorial : ℂ_[p])

def Simeq {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralMv (expMv (f - g))

abbrev Xv {p : ℕ} [Fact p.Prime] {σ : Type*} (i : σ) : MvPowerSeries σ ℂ_[p] := MvPowerSeries.X i

variable {p : ℕ} [Fact p.Prime] {σ : Type*} (l ex ph : PowerSeries ℂ_[p])

def add (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l) ex

def phAt (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst a ph

def be (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  phAt ph (add l ex a b) - phAt ph a - phAt ph b

def Target : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X →
    Simeq (phAt ph (add l ex (add l ex (Xv 0) (Xv 1)) (Xv 2)) - phAt ph (add l ex (Xv 0) (Xv 1)) -
        phAt ph (add l ex (Xv 1) (Xv 2)) - phAt ph (add l ex (Xv 2) (Xv 0)) +
        phAt ph (Xv 0) + phAt ph (Xv 1) + phAt ph (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) 0 →
    Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2)) ∧
    Simeq (be l ex ph (Xv 0) (add l ex (Xv 1) (Xv 2)) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 1) + be l ex ph (Xv 0) (Xv 2))

end PI.BiaddOfCube
end
end

section -- merged from Formalism.PeriodIntegrals.FglTriFactor
noncomputable section

open Classical

namespace PI.FglTriFactor

def IsIntP {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ‖x‖ ≤ 1

def IntegralMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, IsIntP (MvPowerSeries.coeff n F)

abbrev Xv {p : ℕ} [Fact p.Prime] {σ : Type*} (i : σ) : MvPowerSeries σ ℂ_[p] := MvPowerSeries.X i

section

variable {p : ℕ} [Fact p.Prime] (l ex : PowerSeries ℂ_[p]) {σ : Type*}

def lg (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst a l

def pt (x : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst x ex

def add (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := pt ex (lg l a + lg l b)

def sub (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := pt ex (lg l a - lg l b)

end

def IsWq {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : Prop :=
  let c := algebraMap ℂ_[p] (PowerSeries ℂ_[p])
  let X := (PowerSeries.X : PowerSeries ℂ_[p])
  wq = 1 + c W.a₁ * X * wq + c W.a₂ * X ^ 2 * wq + c W.a₃ * X ^ 3 * wq ^ 2 +
    c W.a₄ * X ^ 4 * wq ^ 2 + c W.a₆ * X ^ 6 * wq ^ 3

def dX {A : Type*} [CommRing A] (f : PowerSeries A) : PowerSeries A :=
  PowerSeries.mk fun n => ((n : A) + 1) * PowerSeries.coeff (n + 1) f

def omegaW {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries ℂ_[p] :=
  let c := algebraMap ℂ_[p] (PowerSeries ℂ_[p])
  let X := (PowerSeries.X : PowerSeries ℂ_[p])
  (-(2 : PowerSeries ℂ_[p]) * wq - X * dX wq) * (wq * (c W.a₁ * X + c W.a₃ * X ^ 3 * wq - 2))⁻¹

def flog {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries ℂ_[p] :=
  PowerSeries.mk fun n => if n = 0 then 0 else PowerSeries.coeff (n - 1) (omegaW W wq) / n

def T {p : ℕ} [Fact p.Prime] (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 3) ℂ_[p] :=
  (Xv 0) ^ 3 * PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (Xv 2 - Xv 1) +
    (Xv 1) ^ 3 * PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (Xv 0 - Xv 2) +
    (Xv 2) ^ 3 * PowerSeries.subst (Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (Xv 1 - Xv 0)

def Lemma : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq ex : PowerSeries ℂ_[p]),
    IsIntP W.a₁ → IsIntP W.a₂ → IsIntP W.a₃ → IsIntP W.a₄ → IsIntP W.a₆ → ‖W.Δ‖ = 1 →
    IsWq W wq → PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex (flog W wq) = PowerSeries.X →
    IntegralMv (add (flog W wq) ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    ∃ n : MvPowerSeries (Fin 3) ℂ_[p], IntegralMv n ∧ MvPowerSeries.constantCoeff n = 1 ∧
      T wq = add (flog W wq) ex (add (flog W wq) ex (Xv 0) (Xv 1)) (Xv 2) *
        sub (flog W wq) ex (Xv 0) (Xv 1) * sub (flog W wq) ex (Xv 1) (Xv 2) *
        sub (flog W wq) ex (Xv 2) (Xv 0) * n

end PI.FglTriFactor
end
end

section -- merged from Formalism.PeriodIntegrals.OddDualWeyl
open MvPolynomial Matrix

noncomputable section

namespace PI.OddDualWeyl

def rowAct (R : Type*) [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] MvPolynomial (Fin r × Fin n) R :=
  aeval fun v => ∑ b : Fin r, C (g v.1 b) * X (b, v.2)

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

def colSpan (R : Type*) {K : Type*} [CommRing R] [Field K] [Algebra R K] {k : ℕ}
    (g : Matrix (Fin k) (Fin k) K) : Submodule R (Fin k → K) :=
  Submodule.span R (Set.range fun c : Fin k => fun i => g i c)

def nuOf {m : ℕ} (lam : Fin (m + 1) → ℤ) : Fin (m + 1) → ℕ :=
  fun t => (lam t - lam (Fin.last m)).toNat

def deltaL (R K : Type*) [CommRing R] [Field K] [Algebra R K] (k : ℕ) (ν : Fin k → ℕ)
    (g : Matrix (Fin k) (Fin k) K) : Submodule R (MvPolynomial (Fin k × Fin k) K) :=
  Submodule.comap ((rowAct K (n := k) g).toLinearMap.restrictScalars R)
    (Submodule.map (mapAlgHom (Algebra.ofId R K)).toLinearMap (weyl R k k le_rfl ν))

def deltaLTw (R K : Type*) [CommRing R] [Field K] [Algebra R K] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) : Submodule R (MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) :=
  Submodule.map ((LinearMap.lsmul K (MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)
      (g.det ^ (-(lam (Fin.last m))))).restrictScalars R)
    (deltaL R K (m + 1) (nuOf lam) g)

def Dl0 (O : Type*) {Kf : Type*} [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (Λ : Submodule O (Fin (m + 1) → Kf)) : Submodule O (MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) :=
  if Antitone lam then
    ⨅ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (_ : IsUnit g.det ∧ Λ = colSpan O g), deltaLTw O Kf m lam g
  else ⊥

section GlobalTheory

variable {K : Type} [Field K]

def lamStar {m : ℕ} (lam : Fin (m + 1) → ℤ) : Fin (m + 1) → ℤ := fun i => -lam i.rev

def revCol {m : ℕ} (z : Matrix (Fin (m + 1)) (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  z.submatrix id Fin.rev

def OddFact (O : Type) [CommRing O] [Algebra O K] (m : ℕ) (lam : Fin (m + 1) → ℤ) : Prop :=
  ∀ g : Matrix (Fin (m + 1)) (Fin (m + 1)) K, IsUnit g.det →
    (∀ F ∈ Dl0 O m lam (colSpan O g), ∃ F' ∈ Dl0 O m (lamStar lam) (colSpan O (g⁻¹)ᵀ),
      ∀ z : Matrix (Fin (m + 1)) (Fin (m + 1)) K, IsUnit z.det →
        z.det ^ lam (Fin.last m) * eval (fun x => z x.1 x.2) F =
          (revCol (z⁻¹)ᵀ).det ^ lamStar lam (Fin.last m) * eval (fun x => revCol (z⁻¹)ᵀ x.1 x.2) F') ∧
    (∀ F' ∈ Dl0 O m (lamStar lam) (colSpan O (g⁻¹)ᵀ), ∃ F ∈ Dl0 O m lam (colSpan O g),
      ∀ z : Matrix (Fin (m + 1)) (Fin (m + 1)) K, IsUnit z.det →
        z.det ^ lam (Fin.last m) * eval (fun x => z x.1 x.2) F =
          (revCol (z⁻¹)ᵀ).det ^ lamStar lam (Fin.last m) * eval (fun x => revCol (z⁻¹)ᵀ x.1 x.2) F')

end GlobalTheory

end PI.OddDualWeyl
end
end

section -- merged from Formalism.PeriodIntegrals.LocFramePrim
noncomputable section

namespace PI.LocFramePrim

open NumberField IsDedekindDomain
open scoped TensorProduct Classical

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def inclR : E →+* R ⊗[F] E := (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).toRingHom

def ratTup {M n : ℕ} (X : Fin n → Fin M → E) : Fin n → Fin M → R ⊗[F] E :=
  fun a i => inclR R (X a i)

def ratV {n : ℕ} (x : Fin n → E) : Fin n → R ⊗[F] E := fun i => inclR R (x i)

end Alg

abbrev Fv (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) := v.adicCompletion F

section Level

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

def latLoc (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E)) :
    Submodule (v.adicCompletionIntegers F) (Fin n → Fv F v ⊗[F] E) :=
  Submodule.span (v.adicCompletionIntegers F) (ratV (F := F) (Fv F v) '' Λ)

end Level

section Frames

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

abbrev TupV (n a : ℕ) : Type := Fin a → Fin n → Fv F v ⊗[F] E

def OEv : Set (Fv F v ⊗[F] E) :=
  SetLike.coe (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ))

def sc (x : Fv F v) : Fv F v ⊗[F] E := x ⊗ₜ[F] (1 : E)

variable {n : ℕ} (Λ : Set (Fin n → E))

def IsPrim {a : ℕ} (X : TupV (E := E) v n a) : Prop :=
  (∀ i, X i ∈ latLoc (E := E) v Λ) ∧
  ∀ c : Fin a → Fv F v ⊗[F] E, (∑ i, c i • X i) ∈ latLoc (E := E) v Λ → ∀ i, c i ∈ OEv (E := E) v

def IsDiffVal (d : Fv F v) : Prop :=
  d ≠ 0 ∧ (∀ x ∈ differentIdeal ℤ (𝓞 F), Valued.v (algebraMap F (Fv F v) (x : F)) ≤ Valued.v d) ∧
    ∃ x ∈ differentIdeal ℤ (𝓞 F), Valued.v (algebraMap F (Fv F v) (x : F)) = Valued.v d

def dV : Fv F v := if h : ∃ d, IsDiffVal v d then h.choose else 1

def alp (r : ℕ) (a : Fin (r + 1)) : Fv F v := if (a : ℕ) < r then (dV v)⁻¹ ^ (r - (a : ℕ)) else 1

def locF {r : ℕ} (X : TupV (E := E) v n (r + 1)) : TupV (E := E) v n (r + 1) :=
  fun a => sc (E := E) v (alp v r a) • X a

end Frames

section Split

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def ddE : FractionalIdeal (nonZeroDivisors (𝓞 E)) E :=
  ((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (differentIdeal ℤ (𝓞 F)) : Ideal (𝓞 E)) :
    FractionalIdeal (nonZeroDivisors (𝓞 E)) E)

variable {F}

def latSpan {n r : ℕ} (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (w : Fin r → Fin n → E) :
    Submodule (𝓞 E) (Fin n → E) :=
  Submodule.span (𝓞 E) {y | ∃ (a : Fin r) (x : E), x ∈ aa a ∧ y = x • w a}

end Split

def Statement : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (n r : ℕ) (Λ Lb : Submodule (𝓞 E) (Fin n → E))
    (e f : Fin r → Fin n → E) (z : Fin n → E),
    Λ.FG →
    Λ = latSpan (fun a : Fin r => ddE F ^ (-((r : ℤ) - (a : ℕ)))) e ⊔ Lb ⊔
      latSpan (fun a : Fin r => (ddE F ^ (-((r : ℤ) - (a : ℕ))))⁻¹) f →
    LinearIndependent E (Fin.append e f) →
    (∀ y ∈ Lb, y ∈ Submodule.span E (Set.range e ∪ Set.range f) → y = 0) →
    z ∈ Lb →
    (∀ c : E, c • z ∈ Lb → ∃ o : 𝓞 E, (o : E) = c) →
    IsPrim v (Λ : Set (Fin n → E))
      (locF v (ratTup (Fv F v) (Fin.snoc e z : Fin (r + 1) → Fin n → E)))

end PI.LocFramePrim
end
end

section -- merged from Formalism.PeriodIntegrals.FockRBlock
open MvPolynomial

noncomputable section

namespace PI.TO

def colW (r n : ℕ) : Fin r × Fin n → (Fin n → ℕ) := fun v => Pi.single v.2 1

def colAddGen (R : Type*) [CommRing R] {r n : ℕ} (l j : Fin n) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] MvPolynomial (Option (Fin r × Fin n)) R :=
  aeval fun v => if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v)

def dualWeyl (R : Type*) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) :
    Submodule R (MvPolynomial (Fin r × Fin n) R) :=
  weightedHomogeneousSubmodule R (colW r n) ν ⊓
    ⨅ (l : Fin n) (j : Fin n) (_ : l < j),
      LinearMap.ker ((colAddGen R (r := r) l j).toLinearMap -
        (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))).toLinearMap)

def genM (R : Type) [CommRing R] (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) (MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) :=
  Matrix.of fun a s => X (a, s)

def Nv (R : Type) [CommRing R] (m : ℕ) (vec : Bool) (c : Fin (m + 1)) :
    MvPolynomial (Fin (m + 1) × Fin (m + 1)) R :=
  if vec then X (c, 0) else (genM R m).adjugate (Fin.last m) c

def theta (R : Type) [CommRing R] (m : ℕ) (vec : Bool) :
    MvPolynomial (Fin (m + 1)) R →ₐ[R] MvPolynomial (Fin (m + 1) × Fin (m + 1)) R :=
  aeval (Nv R m vec)

def Hd (R : Type) [CommRing R] (k d : ℕ) : Submodule R (MvPolynomial (Fin k) R) :=
  restrictSupport R {μ | ∑ c, μ c = d}

def fockR {σ R : Type*} [CommRing R] (f g : MvPolynomial σ R) : R :=
  ∑ m ∈ f.support, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : R)

def word1 {K : Type} [CommRing K] {k : ℕ} (l : List (Fin k × Fin k)) (f : MvPolynomial (Fin k) K) : MvPolynomial (Fin k) K :=
  l.foldr (fun y f => X y.1 * pderiv y.2 f) f

def blockEmb (K : Type*) [CommRing K] {S : Type*} {k n : ℕ} (s : S) :
    MvPolynomial (Fin k × Fin n) K →ₐ[K] MvPolynomial (S × (Fin k × Fin n)) K :=
  rename fun v => (s, v)

def tensorLat (R K : Type*) [CommRing R] [CommRing K] [Algebra R K] {S : Type*} [Fintype S] {k n : ℕ}
    (M : S → Submodule R (MvPolynomial (Fin k × Fin n) K)) : Submodule R (MvPolynomial (S × (Fin k × Fin n)) K) :=
  Submodule.span R {P | ∃ F : S → MvPolynomial (Fin k × Fin n) K, (∀ s, F s ∈ M s) ∧ P = ∏ s, blockEmb K s (F s)}

def multideg {ι : Type*} {n : ℕ} (m : ι × Fin n →₀ ℕ) (i : ι) : ℕ := ∑ c : Fin n, m (i, c)

def Pol (R : Type*) [CommSemiring R] {ι : Type*} (n : ℕ) (d : ι → ℕ) :
    Submodule R (MvPolynomial (ι × Fin n) R) :=
  MvPolynomial.restrictSupport R {m | ∀ i, multideg m i = d i}

section Multi

variable {S : Type} [Fintype S] [DecidableEq S]

def Th0 (R : Type) [CommRing R] (m : ℕ) (vec : S → Bool) :
    MvPolynomial (S × Fin (m + 1)) R →ₐ[R] MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) R :=
  aeval fun v => blockEmb R v.1 (Nv R m (vec v.1) v.2)

end Multi

def opWord {R : Type} [CommRing R] {n' k : ℕ} (l : List (Fin n' × (Fin k × Fin k))) (f : MvPolynomial (Fin n' × Fin k) R) :
    MvPolynomial (Fin n' × Fin k) R :=
  l.foldr (fun y f => X (y.1, y.2.1) * pderiv (y.1, y.2.2) f) f

def FockRBlock : Prop :=
  ∀ (K S : Type) [CommRing K] [Fintype S] (k n : ℕ) (F G : S → MvPolynomial (Fin k × Fin n) K),
    fockR (∏ s, blockEmb K s (F s)) (∏ s, blockEmb K s (G s)) = ∏ s, fockR (F s) (G s)

def OnePos : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (m : ℕ), 1 ≤ m → ∀ (vec : Bool) (d c : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν → ν 0 ≤ c →
    ∀ β ∈ dualWeyl K (m + 1) (m + 1) ν, ∀ s ∈ dualWeyl K (m + 1) (m + 1) ν,
      ∃ (L : Finset (List (Fin (m + 1) × Fin (m + 1)))) (a : List (Fin (m + 1) × Fin (m + 1)) → K),
        (∀ l ∈ L, l.length ≤ c) ∧
        ∀ P ∈ Hd K (m + 1) d, ∀ Q ∈ Hd K (m + 1) d,
          fockR (theta K m vec P * s) (theta K m vec Q * β) =
            fockR (theta K m vec (∑ l ∈ L, a l • word1 l P)) (theta K m vec Q)

def TenOp : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (n' m : ℕ), 1 ≤ m → ∀ (vec : Fin n' → Bool) (TT : Finset (Fin n')) (d : Fin n' → ℕ)
    (c : ℕ) (ν : Fin n' → Fin (m + 1) → ℕ), (∀ t, Antitone (ν t)) → (∀ t ∈ TT, ν t 0 ≤ c) → (∀ t, t ∉ TT → ν t = 0) →
    ∀ β ∈ tensorLat K K (fun t => dualWeyl K (m + 1) (m + 1) (ν t)),
    ∀ s ∈ tensorLat K K (fun t => dualWeyl K (m + 1) (m + 1) (ν t)),
      ∃ (L : Finset (List (Fin n' × (Fin (m + 1) × Fin (m + 1))))) (a : List (Fin n' × (Fin (m + 1) × Fin (m + 1))) → K),
        (∀ l ∈ L, (∀ z ∈ l, z.1 ∈ TT) ∧ ∀ t, (l.filter fun z => z.1 = t).length ≤ c) ∧
        ∀ G ∈ Pol K (ι := Fin n') (m + 1) d, (∑ l ∈ L, a l • opWord l G) ∈ Pol K (ι := Fin n') (m + 1) d ∧
          ∀ H ∈ Pol K (ι := Fin n') (m + 1) d,
            fockR (Th0 K m vec G * s) (Th0 K m vec H * β) = fockR (Th0 K m vec (∑ l ∈ L, a l • opWord l G)) (Th0 K m vec H)

end PI.TO

namespace PI

def TenOp : Prop := PI.TO.FockRBlock → PI.TO.OnePos → PI.TO.TenOp

end PI
end
end
