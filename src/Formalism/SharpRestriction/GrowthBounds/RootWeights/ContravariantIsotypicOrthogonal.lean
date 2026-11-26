module

public import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees
public import Formalism.GrowthSums.LemmaATwoFactList

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.ContravariantIsotypicOrthogonal
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def restrictStableOperators {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (W : Submodule K V)
    (h : ∀ a b, ∀ x ∈ W, E a b x ∈ W) : GLOps n K W := fun a b => (E a b).restrict (h a b)

def CompleteReducibilityIsotypic : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (n : ℕ) (E : GLOps n K V),
    IsGLRep E → (⨆ mu : Fin n → ℤ, isoSub E mu) = ⊤

def ContravariantIsotypicOrthogonal : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (n : ℕ) (E : GLOps n K V),
    IsGLRep E → ∀ B : V →ₗ[K] V →ₗ[K] K, (∀ a b x y, B (E a b x) y = B x (E b a y)) →
      ∀ lam mu : Fin n → ℤ, lam ≠ mu → ∀ x ∈ isoSub E lam, ∀ y ∈ isoSub E mu, B x y = 0

def HighestWeightDominant : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ)
    (E : GLOps n K V), IsGLRep E → ∀ lam v, IsHWV E lam v → Dominant lam

def SubrepRestrictionRep : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (n : ℕ) (E : GLOps n K V),
    IsGLRep E → ∀ (W : Submodule K V) (h : ∀ a b, ∀ x ∈ W, E a b x ∈ W),
      IsGLRep (restrictStableOperators E W h) ∧
      (∀ (mu : Fin n → ℤ) (x : W), x ∈ weightSp (restrictStableOperators E W h) mu ↔ (x : V) ∈ weightSp E mu) ∧
      (∀ a b k (x : W), ((divPowE (restrictStableOperators E W h) a b k x : W) : V) = divPowE E a b k x) ∧
      (∀ a k (x : W), ((binomE (restrictStableOperators E W h) a k x : W) : V) = binomE E a k x) ∧
      (∀ lam (e : Module.End K V), IsIsoProj E lam e →
        ∃ e' : Module.End K W, IsIsoProj (restrictStableOperators E W h) lam e' ∧ ∀ x : W, ((e' x : W) : V) = e x) ∧
      (∀ lam (e : Module.End K V), IsIsoProj E lam e → (¬ ∃ v : W, IsHWV (restrictStableOperators E W h) lam v) →
        ∀ x ∈ W, e x = 0)

def PolynomialGLRepresentation : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (n : ℕ) (LL : Letters ι),
    (∀ S, IsGLRep (glOps K n LL S)) ∧
    (∀ S S' : Set ι, Disjoint S S' → ∀ a b c d,
      glOps K n LL S a b * glOps K n LL S' c d = glOps K n LL S' c d * glOps K n LL S a b) ∧
    (∀ S S' : Set ι, S ⊆ S' → ∀ a b, glOps K n LL S' a b = glOps K n LL S a b + glOps K n LL (S' \ S) a b) ∧
    (∀ S d a b, ∀ F ∈ Pol K n d, glOps K n LL S a b F ∈ Pol K n d) ∧
    (∀ d : ι → ℕ, FiniteDimensional K (Pol K n d)) ∧
    (∀ S mu F, F ∈ weightSp (glOps K n LL S) mu → ∀ m ∈ F.support, wtS LL S m = mu) ∧
    (∃ B : MvPolynomial (ι × Fin n) K →ₗ[K] MvPolynomial (ι × Fin n) K →ₗ[K] K,
      (∀ F G, B F G = fock F G) ∧ ∀ S a b F G, B (glOps K n LL S a b F) G = B F (glOps K n LL S b a G))

def latticeMultidegreePart {O : Type} [CommRing O] [IsDomain O] {ι : Type} {n : ℕ}
    (L : Submodule O (MvPolynomial (ι × Fin n) (KK O))) (d : ι → ℕ) : Submodule O (Pol (KK O) n d) :=
  L.comap (((Pol (KK O) n d).subtype).restrictScalars O)

def AdmissibleDVRIntegralFormLatticesStable : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O → CharZero (KK O) ∧
    ∀ (n : ℕ) (ι : Type) [Fintype ι] (LL : Letters ι),
      (∀ S : Set ι, PolUZStable LL S (IntPol O (ι × Fin n)) ∧
        ∀ u ∈ polUZgens (KK O) LL S, ∀ F : MvPolynomial (ι × Fin n) (KK O),
          InBB (O := O) p F → InBB (O := O) p (u F)) ∧
      (∀ S : Set ι, ∀ u ∈ UZgens (glOps (KK O) n LL S),
        (∀ F ∈ IntPol O (ι × Fin n), u F ∈ IntPol O (ι × Fin n)) ∧
        ∀ F : MvPolynomial (ι × Fin n) (KK O), InBB (O := O) p F → InBB (O := O) p (u F)) ∧
      ∃ BBs : Submodule O (MvPolynomial (ι × Fin n) (KK O)), (∀ F, F ∈ BBs ↔ InBB (O := O) p F) ∧
        ∀ d : ι → ℕ, (latticeMultidegreePart (IntPol O (ι × Fin n)) d).FG ∧ MQ (K := KK O) (latticeMultidegreePart (IntPol O (ι × Fin n)) d) = ⊤ ∧
          (latticeMultidegreePart BBs d).FG ∧ MQ (K := KK O) (latticeMultidegreePart BBs d) = ⊤

end Formalism.MainNotions.G.GLWeightTheory
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.PadicGeMulNat
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def mah (f : ℕ → ℚ) (j : ℕ) : ℚ := (fwdDiff 1)^[j] f 0

def DecLe (p : ℕ) (θ s : ℝ) (K : ℕ) (f : ℕ → ℚ) : Prop := ∀ j ≤ K, PadicGe p (mah f j) (θ * j + s)

def Dec (p : ℕ) (θ s : ℝ) (f : ℕ → ℚ) : Prop := ∀ j, PadicGe p (mah f j) (θ * j + s)

def HdU (p : ℕ) : Prop := ∀ t rho : ℕ, rho < p ^ (t + 1) → ∃ a : ℕ → ℤ,
  (∀ n : ℕ, dUnit (p ^ (t + 1)) n rho = ∑ l ∈ range (rho + 1), (a l : ℚ) * (n.choose l : ℚ)) ∧
  ∀ l, (p : ℤ) ^ l ∣ a l

def HDec (p : ℕ) : Prop := ∀ u : UnitFn, u.rho < p ^ (u.t + 1) → Dec p (1 / 4) 0 (unitFn p u)

def HUnit (p : ℕ) : Prop := ∀ u : UnitFn, u.rho < p ^ (u.t + 1) → ∀ m : ℕ,
  unitFn p u m ≠ 0 ∧ padicValRat p (unitFn p u m) = 0

def HMul (p : ℕ) : Prop := ∀ (θ s s' : ℝ) (f g : ℕ → ℚ), 0 ≤ θ → Dec p θ s f → Dec p θ s' g →
  Dec p θ (s + s') (fun n => f n * g n)

theorem padicGe_add {p : ℕ} [Fact p.Prime] {x y : ℚ} {r : ℝ} (hx : PadicGe p x r) (hy : PadicGe p y r) :
    PadicGe p (x + y) r := by
  rcases hx with hx | hx
  · subst hx; simpa using hy
  rcases hy with hy | hy
  · subst hy; rw [add_zero]; exact Or.inr hx
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  right
  have hm := padicValRat.min_le_padicValRat_add (p := p) hxy
  have hm' : ((min (padicValRat p x) (padicValRat p y) : ℤ) : ℝ) ≤ (padicValRat p (x + y) : ℝ) := by
    exact_mod_cast hm
  rw [Int.cast_min] at hm'
  exact le_trans (le_min hx hy) hm'

theorem padicGe_mul {p : ℕ} [Fact p.Prime] {x y : ℚ} {r s : ℝ} (hx : PadicGe p x r) (hy : PadicGe p y s) :
    PadicGe p (x * y) (r + s) := by
  rcases hx with hx | hx
  · left; simp [hx]
  rcases hy with hy | hy
  · left; simp [hy]
  by_cases h0 : x * y = 0
  · exact Or.inl h0
  right
  have hx0 : x ≠ 0 := left_ne_zero_of_mul h0
  have hy0 : y ≠ 0 := right_ne_zero_of_mul h0
  rw [padicValRat.mul hx0 hy0]
  push_cast
  linarith

theorem padicGe_mono {p : ℕ} {x : ℚ} {r s : ℝ} (hx : PadicGe p x r) (h : s ≤ r) : PadicGe p x s := by
  rcases hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr (le_trans h hx)

theorem padicGe_neg {p : ℕ} {x : ℚ} {r : ℝ} (hx : PadicGe p x r) : PadicGe p (-x) r := by
  rcases hx with hx | hx
  · left; simp [hx]
  · right; rw [padicValRat.neg]; exact hx

theorem padicGe_int {p : ℕ} [Fact p.Prime] (k : ℤ) : PadicGe p (k : ℚ) 0 := by
  by_cases hk : (k : ℚ) = 0
  · exact Or.inl hk
  right
  rw [padicValRat.of_int]
  exact_mod_cast (Nat.cast_nonneg _ : (0 : ℤ) ≤ (padicValInt p k : ℤ))

theorem padicGe_mul_nat {p : ℕ} [Fact p.Prime] {x : ℚ} {r : ℝ} (hx : PadicGe p x r) (k : ℕ) :
    PadicGe p (x * (k : ℚ)) r := by
  have h := padicGe_mul hx (padicGe_int (p := p) (k : ℤ))
  simpa using h

theorem padicGe_sum {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι) (f : ι → ℚ) {r : ℝ}
    (h : ∀ i ∈ s, PadicGe p (f i) r) : PadicGe p (∑ i ∈ s, f i) r := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Or.inl (by simp)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact padicGe_add (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

end Formalism.MainNotions.G.GLWeightTheory
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantDenominatorLinftyBound
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def linf {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (W : Submodule K V) : ℕ :=
  sSup {k | ∃ nu ∈ wtsOf E W, (∑ a, nu a = 0) ∧ ∃ a, k = (nu a).natAbs}

def InvariantDenominatorLinftyBound : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O →
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
      [FiniteDimensional (KK O) V] (E : GLOps n (KK O) V), IsGLRep E →
      ∀ M : Submodule O V, UZLattice E M → MQ (K := KK O) M = ⊤ →
      ∀ Inv : Module.End (KK O) V, IsInvProj E Inv →
        ∀ x ∈ M, ((p : O) ^ (N0 n * deF p n (linf E (MQ M)))) • Inv x ∈ M

def InvariantProjectionDenominator : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O →
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
      [FiniteDimensional (KK O) V] (E : GLOps n (KK O) V), IsGLRep E →
      ∀ M : Submodule O V, UZLattice E M → MQ (K := KK O) M = ⊤ →
      ∀ Inv : Module.End (KK O) V, IsInvProj E Inv →
        ∀ x ∈ M, ((p : O) ^ (N0 n * deF p n (ellOf E (MQ M)))) • Inv x ∈ M

end Formalism.MainNotions.G.GLWeightTheory
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.EBeta
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees


open Classical in
def eBeta {R : Type} [CommRing R] {ι : Type} {r : ℕ} (LL : Letters ι) (S : Set ι) {k1 : Type} [CommRing k1]
    (j : R →+* k1) (g0 g0inv : Matrix (Fin r) (Fin r) k1) :
    MvPolynomial (ι × Fin r) R →+* MvPolynomial (ι × Fin r) k1 :=
  eval₂Hom (C.comp j) fun v =>
    if v.1 ∈ S then
      (if LL.vec v.1 then ∑ a : Fin r, C (g0inv a v.2) * X (v.1, a)
       else ∑ a : Fin r, C (g0 v.2 a) * X (v.1, a))
    else X v


open Classical in
def eWt {ι : Type} {r : ℕ} [NeZero r] (LL : Letters ι) (S : Set ι) (m : ι × Fin r →₀ ℕ) : ℤ :=
  m.sum fun v k => if v.2 = lastIdx r ∧ v.1 ∈ S then (if LL.vec v.1 then (k : ℤ) else -(k : ℤ)) else 0

def HSupp : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (r : ℕ) [NeZero r] (S : Set ι)
    (k1 : Type) [CommRing k1] (j : R →+* k1) (g0 g0inv : Matrix (Fin r) (Fin r) k1), g0 * g0inv = 1 →
    ∀ (G : MvPolynomial (ι × Fin r) R) (th : ℤ), (th : WithTop ℤ) ≤ valS LL S G →
      ∀ m ∈ (eBeta LL S j g0 g0inv G).support, th ≤ eWt LL S m

def matA (R : Type) [CommRing R] {ι : Type} {r : ℕ} (A : Fin r → ι) :
    Matrix (Fin r) (Fin r) (MvPolynomial (ι × Fin r) R) :=
  Matrix.of fun i j : Fin r => (X (A i, j) : MvPolynomial (ι × Fin r) R)

def HCop : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) (r : ℕ) [NeZero r] (A : Fin r → ι), Function.Injective A →
    (matA R A).adjugate (lastIdx r) (lastIdx r) ≠ 0 ∧
    IsRelPrime (detA (R := R) A) ((matA R A).adjugate (lastIdx r) (lastIdx r))

def E1 : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (r : ℕ) [NeZero r] (S : Set ι)
    (A : Fin r → ι), Function.Injective A → (∀ l, A l ∈ S ∧ LL.vec (A l) = true) →
    (∀ (d : ι → ℕ) (G : MvPolynomial (ι × Fin r) R), G ∈ Pol R r d →
      ∀ th : ℤ, (th : WithTop ℤ) ≤ valS LL S G → (degOther LL S A d : ℤ) < th →
        (detA (R := R) A) ^ (th - degOther LL S A d).toNat ∣ G)

end Formalism.MainNotions.G.GLWeightTheory
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.StableSubspaceCompleteReducibility
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def SatisfiesGLRelations {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) : Prop :=
  ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0)

def IsStableUnderOperators {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V)
    (W : Submodule K V) : Prop := ∀ a b, ∀ x ∈ W, E a b x ∈ W

def isotypicPartIn {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V)
    (W : Submodule K V) (mu : Fin n → ℤ) : Submodule K V :=
  Submodule.span K {x | ∃ u ∈ Umon E, ∃ v ∈ W, IsHWV E mu v ∧ x = u v}

def StableSubspaceCompleteReducibility : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (n : ℕ) (E : GLOps n K V), SatisfiesGLRelations E →
    ∀ W : Submodule K V, FiniteDimensional K W → IsStableUnderOperators E W → W ≤ ⨆ mu, weightSp E mu →
      W ≤ ⨆ mu, isotypicPartIn E W mu

def HighestWeightModuleWeightBounds : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (n : ℕ) [NeZero n] (E : GLOps n K V),
    SatisfiesGLRelations E → ∀ (mu : Fin n → ℤ) (v : V), IsHWV E mu v → ∀ u ∈ Umon E,
      u v ∈ ⨆ ν ∈ {ν : Fin n → ℤ | mu (lastIdx n) ≤ ν (lastIdx n) ∧ ν 0 ≤ mu 0}, weightSp E ν

def PolynomialOperatorsGLRelations : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι), SatisfiesGLRelations (glOps R n LL S)

def MonomialsAreWeightVectors : Prop :=
  ∀ (R : Type) [Field R] [CharZero R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι),
    (∀ (m : ι × Fin n →₀ ℕ) (c : R), monomial m c ∈ weightSp (glOps R n LL S) (wtS LL S m)) ∧
    (∀ (ν : Fin n → ℤ) (x : MvPolynomial (ι × Fin n) R), x ∈ weightSp (glOps R n LL S) ν →
      ∀ m ∈ x.support, wtS LL S m = ν)

def PolynomialLocallyFinite : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι)
    (x : MvPolynomial (ι × Fin n) R), ∃ T : Submodule R (MvPolynomial (ι × Fin n) R),
      FiniteDimensional R T ∧ x ∈ T ∧ IsStableUnderOperators (glOps R n LL S) T

def DividedPowerFormulaCharZero : Prop :=
  ∀ (R : Type) [Field R] [CharZero R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι)
    (a b : Fin n) (k : ℕ), a ≠ b → divPowE (glOps R n LL S) a b k = divPow R LL S a b k

def BinomialFormulaCharZero : Prop :=
  ∀ (R : Type) [Field R] [CharZero R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι)
    (a : Fin n) (k : ℕ), binomE (glOps R n LL S) a k = binomPol R LL S a k

end Formalism.MainNotions.G.GLWeightTheory
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicProjectorFixedMem
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def highestWeightVectors {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (lam : Fin n → ℤ) :
    Submodule K V :=
  weightSp E lam ⊓ ⨅ a : Fin n, ⨅ b : Fin n, ⨅ (_ : a < b), LinearMap.ker (E a b)

def generatedSubrep {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (h : V) :
    Submodule K V :=
  Submodule.span K {x | ∃ u ∈ Umon E, x = u h}

def IsotypicProjectorFixedMem : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ)
    (E : GLOps n K V), IsGLRep E → ∀ (lam : Fin n → ℤ) (e : Module.End K V), IsIsoProj E lam e →
      ∀ Y : V, e Y = Y → Y ∈ isoSub E lam

def GeneratedMultipleOfHWV : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (n : ℕ)
    (E : GLOps n K V), IsGLRep E → ∀ (lam : Fin n → ℤ) (h : V), h ∈ highestWeightVectors E lam →
      generatedSubrep E h ≤ Submodule.span K {h} ⊔ ⨆ mu ∈ {mu : Fin n → ℤ | mu ≠ lam}, (weightSp E mu ⊓ generatedSubrep E h)

def DualLatticeDivisibility : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
    [FiniteDimensional (KK O) V] (M : Submodule O V), M.FG → MQ (K := KK O) M = ⊤ →
    ∀ (t : KK O) (z : V),
      (∀ f : V →ₗ[KK O] KK O, (∀ x ∈ M, ∃ o : O, f x = algebraMap O (KK O) o) →
        ∃ o : O, f z = t * algebraMap O (KK O) o) →
      ∃ m ∈ M, z = t • m

def LatticeSubspaceBasis : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
    [FiniteDimensional (KK O) V] (M : Submodule O V), M.FG → MQ (K := KK O) M = ⊤ →
    ∀ H : Submodule (KK O) V, ∃ (k : ℕ) (h : Fin k → V), (∀ j, h j ∈ M ∧ h j ∈ H) ∧
      LinearIndependent (KK O) h ∧ H ≤ Submodule.span (KK O) (Set.range h) ∧
      ∀ x ∈ M, x ∈ H → ∃ o : Fin k → O, x = ∑ j, o j • h j

def GeneratedLatticeCorollary : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O →
    ∀ (n : ℕ) [NeZero n] (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
      [IsScalarTower O (KK O) V] [FiniteDimensional (KK O) V] (E : GLOps n (KK O) V), IsGLRep E →
      ∀ M : Submodule O V, UZLattice E M →
      ∀ lam : Fin n → ℤ, Dominant lam →
      ∀ π : Module.End (KK O) V, IsWtProj E lam π →
      ∀ h : V, h ∈ M → h ∈ highestWeightVectors E lam → h ≠ 0 →
      ∀ (c : ℤ) (y : V), y ∈ generatedSubrep E h →
        (∀ u ∈ UZmon E, ∃ o : O, π (u y) = ((p : KK O) ^ c * algebraMap O (KK O) o) • h) →
        ∃ m ∈ M, y = ((p : KK O) ^ (c - ((N0 n * deF p n (ellWt lam) : ℕ) : ℤ))) • m

end Formalism.MainNotions.G.GLWeightTheory
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.MulLaurentSup
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

private theorem laurent_mul_coeff_of_unique_decomp {B : Type*} [CommRing B] (f g : LaurentPolynomial B) (a b : ℤ)
    (h : ∀ k₁ ∈ f.coeff.support, ∀ k₂ ∈ g.coeff.support, k₁ + k₂ = a + b → k₁ = a ∧ k₂ = b) :
    (f * g).coeff (a + b) = f.coeff a * g.coeff b := by
  classical
  rw [AddMonoidAlgebra.coeff_mul, Finsupp.sum, Finset.sum_eq_single a]
  · rw [Finsupp.sum, Finset.sum_eq_single b]
    · simp
    · intro k₂ hk₂ hne
      by_cases ha : a ∈ f.coeff.support
      · rw [if_neg]; intro he; exact hne (h a ha k₂ hk₂ he).2
      · have : f.coeff a = 0 := by simpa using ha
        simp [this]
    · intro hb
      have : g.coeff b = 0 := by simpa using hb
      simp [this]
  · intro k₁ hk₁ hne
    apply Finset.sum_eq_zero
    intro k₂ hk₂
    dsimp only; rw [if_neg]; intro he; exact hne (h k₁ hk₁ k₂ hk₂ he).1
  · intro ha
    have : f.coeff a = 0 := by simpa using ha
    simp [this]

theorem mul_laurent_inf {B : Type*} [CommRing B] [IsDomain B] (f g : LaurentPolynomial B) :
    ((f * g).coeff.support.inf fun k => (k : WithTop ℤ)) =
      (f.coeff.support.inf fun k => (k : WithTop ℤ)) + (g.coeff.support.inf fun k => (k : WithTop ℤ)) := by
  classical
  apply le_antisymm
  · rcases f.coeff.support.eq_empty_or_nonempty with hf | hf
    · rw [hf, Finset.inf_empty, top_add]; exact le_top
    rcases g.coeff.support.eq_empty_or_nonempty with hg | hg
    · rw [hg, Finset.inf_empty, add_top]; exact le_top
    have hc := laurent_mul_coeff_of_unique_decomp f g (f.coeff.support.min' hf) (g.coeff.support.min' hg) (by
      intro k₁ hk₁ k₂ hk₂ he
      have h1 := Finset.min'_le _ _ hk₁
      have h2 := Finset.min'_le _ _ hk₂
      omega)
    have hmem : f.coeff.support.min' hf + g.coeff.support.min' hg ∈ (f * g).coeff.support := by
      rw [Finsupp.mem_support_iff, hc]
      exact mul_ne_zero (Finsupp.mem_support_iff.mp (Finset.min'_mem _ hf))
        (Finsupp.mem_support_iff.mp (Finset.min'_mem _ hg))
    calc _ ≤ (((f.coeff.support.min' hf + g.coeff.support.min' hg : ℤ)) : WithTop ℤ) := Finset.inf_le hmem
      _ = ((f.coeff.support.min' hf : ℤ) : WithTop ℤ) + ((g.coeff.support.min' hg : ℤ) : WithTop ℤ) :=
        WithTop.coe_add _ _
      _ = _ := by simp only [Finset.min'_eq_inf', Finset.coe_inf']; rfl
  · exact AddMonoidAlgebra.le_infDegree_mul { toFun := fun k : ℤ => (k : WithTop ℤ), map_add' := fun a b => WithTop.coe_add a b } f g

theorem mul_laurent_sup {B : Type*} [CommRing B] [IsDomain B] (f g : LaurentPolynomial B) :
    ((f * g).coeff.support.sup fun k => (k : WithBot ℤ)) =
      (f.coeff.support.sup fun k => (k : WithBot ℤ)) + (g.coeff.support.sup fun k => (k : WithBot ℤ)) := by
  classical
  apply le_antisymm
  · exact AddMonoidAlgebra.supDegree_mul_le (D := fun k : ℤ => (k : WithBot ℤ)) (fun a b => WithBot.coe_add a b) (p := f) (q := g)
  · rcases f.coeff.support.eq_empty_or_nonempty with hf | hf
    · rw [hf, Finset.sup_empty, WithBot.bot_add]; exact bot_le
    rcases g.coeff.support.eq_empty_or_nonempty with hg | hg
    · rw [hg, Finset.sup_empty, WithBot.add_bot]; exact bot_le
    have hc := laurent_mul_coeff_of_unique_decomp f g (f.coeff.support.max' hf) (g.coeff.support.max' hg) (by
      intro k₁ hk₁ k₂ hk₂ he
      have h1 := Finset.le_max' _ _ hk₁
      have h2 := Finset.le_max' _ _ hk₂
      omega)
    have hmem : f.coeff.support.max' hf + g.coeff.support.max' hg ∈ (f * g).coeff.support := by
      rw [Finsupp.mem_support_iff, hc]
      exact mul_ne_zero (Finsupp.mem_support_iff.mp (Finset.max'_mem _ hf))
        (Finsupp.mem_support_iff.mp (Finset.max'_mem _ hg))
    calc _ = ((f.coeff.support.max' hf : ℤ) : WithBot ℤ) + ((g.coeff.support.max' hg : ℤ) : WithBot ℤ) := by
          simp only [Finset.max'_eq_sup', Finset.coe_sup']; rfl
      _ = (((f.coeff.support.max' hf + g.coeff.support.max' hg : ℤ)) : WithBot ℤ) := (WithBot.coe_add _ _).symm
      _ ≤ _ := Finset.le_sup (f := fun k : ℤ => ((k : ℤ) : WithBot ℤ)) (b := f.coeff.support.max' hf + g.coeff.support.max' hg) hmem

def mul_Phi (σ A : Type*) [CommRing A] :
    MvPolynomial σ (LaurentPolynomial A) →+* LaurentPolynomial (MvPolynomial σ A) :=
  MvPolynomial.eval₂Hom (AddMonoidAlgebra.mapRingHom ℤ (C : A →+* MvPolynomial σ A))
    (fun i => LaurentPolynomial.C (X i))

private theorem laurent_mul_C_coeff {B : Type*} [CommRing B] (y : LaurentPolynomial B) (q : B) (k : ℤ) :
    (y * LaurentPolynomial.C q).coeff k = y.coeff k * q := by
  have hCc : ∀ j : ℤ, (LaurentPolynomial.C q).coeff j = if j = 0 then q else 0 := by
    intro j
    simp [LaurentPolynomial.C_apply, Finsupp.single_apply, eq_comm]
  have h := laurent_mul_coeff_of_unique_decomp y (LaurentPolynomial.C q) k 0 (by
    intro k₁ _ k₂ hk₂ he
    have : k₂ = 0 := by
      by_contra hne
      rw [Finsupp.mem_support_iff, hCc, if_neg hne] at hk₂
      exact hk₂ rfl
    omega)
  rw [add_zero] at h
  rw [h, hCc, if_pos rfl]

theorem mul_Phi_coeff {σ A : Type*} [CommRing A] (P : MvPolynomial σ (LaurentPolynomial A)) (m : σ →₀ ℕ) (k : ℤ) :
    AddMonoidAlgebra.coeff ((mul_Phi σ A P).coeff k) m = (AddMonoidAlgebra.coeff P m).coeff k := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial m' c =>
    simp only [mul_Phi, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial]
    have hprod : (m'.prod fun i e => (LaurentPolynomial.C (X i) : LaurentPolynomial (MvPolynomial σ A)) ^ e) =
        LaurentPolynomial.C (monomial m' 1) := by
      rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, map_finsuppProd]
      simp [map_pow]
    rw [hprod, laurent_mul_C_coeff]
    have hmap : (AddMonoidAlgebra.mapRingHom ℤ (C : A →+* MvPolynomial σ A) c).coeff k = C (c.coeff k) := by
      simp [AddMonoidAlgebra.mapRingHom]
    rw [hmap, MvPolynomial.C_mul_monomial, mul_one, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    split_ifs <;> simp
  | add p q hp hq => simp [map_add (f := _), hp, hq]

def mul_degs {σ A : Type*} [CommRing A] (P : MvPolynomial σ (LaurentPolynomial A)) : Finset ℤ :=
  P.support.biUnion fun m => (P.coeff m).coeff.support

theorem mul_degs_eq {σ A : Type*} [CommRing A] (P : MvPolynomial σ (LaurentPolynomial A)) :
    mul_degs P = (mul_Phi σ A P).coeff.support := by
  classical
  ext k
  simp only [mul_degs, Finset.mem_biUnion, MvPolynomial.mem_support_iff, Finsupp.mem_support_iff]
  constructor
  · rintro ⟨m, -, hm⟩ h
    apply hm
    rw [← mul_Phi_coeff, h]
    simp
  · intro h
    obtain ⟨m, hm⟩ : ∃ m, AddMonoidAlgebra.coeff ((mul_Phi σ A P).coeff k) m ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact h (by ext m; simpa using hc m)
    rw [mul_Phi_coeff] at hm
    exact ⟨m, fun h0 => hm (by rw [h0]; simp), hm⟩

instance mul_domGL (R : Type*) [Field R] (n : ℕ) : IsDomain (GLCoord R n) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors
    (Matrix.det_mvPolynomialX_ne_zero (Fin n) R))

theorem mul_valS_mul {R : Type*} [Field R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F G : MvPolynomial (ι × Fin n) R) : valS LL S (F * G) = valS LL S F + valS LL S G := by
  have key : ∀ H : MvPolynomial (ι × Fin n) R, valS LL S H =
      ((mul_Phi _ _ (twistSub LL S (lastIdx n) H)).coeff.support.inf fun k => (k : WithTop ℤ)) := by
    intro H; rw [← mul_degs_eq]; rfl
  rw [key, key, key, map_mul, map_mul, mul_laurent_inf]

theorem mul_lam1S_mul {R : Type*} [Field R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F G : MvPolynomial (ι × Fin n) R) : lam1S LL S (F * G) = lam1S LL S F + lam1S LL S G := by
  have key : ∀ H : MvPolynomial (ι × Fin n) R, lam1S LL S H =
      ((mul_Phi _ _ (twistSub LL S (0 : Fin n) H)).coeff.support.sup fun k => (k : WithBot ℤ)) := by
    intro H; rw [← mul_degs_eq]; rfl
  rw [key, key, key, map_mul, map_mul, mul_laurent_sup]

end Formalism.MainNotions.G.GLWeightTheory
end
end
