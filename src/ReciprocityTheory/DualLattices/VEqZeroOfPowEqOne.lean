module

public import Mathlib

@[expose] public section

section -- merged from ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
namespace ReciprocityTheory.PGsh

open MvPowerSeries

noncomputable section

variable {C : Type*} [Field C]

def IsIntV (v : AddValuation C (WithTop ℝ)) (x : C) : Prop := 0 ≤ v x

def MvIsInt (v : AddValuation C (WithTop ℝ)) {σ : Type*} (f : MvPowerSeries σ C) : Prop :=
  ∀ α, IsIntV v (coeff α f)

def PsIsInt (v : AddValuation C (WithTop ℝ)) (f : PowerSeries C) : Prop :=
  ∀ n, IsIntV v (PowerSeries.coeff n f)

theorem v_eq_zero_of_pow_eq_one {v : AddValuation C (WithTop ℝ)} {z : C} {N : ℕ} (hN : N ≠ 0)
    (hz : z ^ N = 1) : v z = 0 := by
  have h1 : N • v z = 0 := by rw [← AddValuation.map_pow, hz, AddValuation.map_one]
  generalize v z = x at h1 ⊢
  induction x using WithTop.recTopCoe with
  | top =>
    exfalso
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN
    rw [succ_nsmul, WithTop.add_top] at h1
    exact WithTop.top_ne_zero h1
  | coe r =>
    rw [← WithTop.coe_nsmul] at h1
    have h2 : N • r = 0 := WithTop.coe_eq_zero.mp h1
    rw [nsmul_eq_mul] at h2
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (Nat.cast_eq_zero.mp h) hN
    · rw [h]; rfl

structure LogFGL (v : AddValuation C (WithTop ℝ)) (d : ℕ) where
  lg : Fin d → MvPowerSeries (Fin d) C
  lg_const : ∀ a, constantCoeff (lg a) = 0
  lg_lin : ∀ a b, coeff (Finsupp.single b 1) (lg a) = if a = b then 1 else 0
  F : Fin d → MvPowerSeries (Fin d ⊕ Fin d) C
  F_int : ∀ a, MvIsInt v (F a)
  F_const : ∀ a, constantCoeff (F a) = 0
  lg_F : ∀ a, subst F (lg a) =
    subst (fun b => X (Sum.inl b)) (lg a) + subst (fun b => X (Sum.inr b)) (lg a)

def IsCurve (v : AddValuation C (WithTop ℝ)) {d : ℕ} (ga : Fin d → PowerSeries C) : Prop :=
  ∀ a, PowerSeries.constantCoeff (ga a) = 0 ∧ PsIsInt v (ga a)

def tangent {d : ℕ} (ga : Fin d → PowerSeries C) : Fin d → C :=
  fun a => PowerSeries.coeff 1 (ga a)

def rescaleCurve {d : ℕ} (x : C) (ga : Fin d → PowerSeries C) : Fin d → PowerSeries C :=
  fun a => PowerSeries.rescale x (ga a)

namespace LogFGL

variable {v : AddValuation C (WithTop ℝ)} {d : ℕ} (G : LogFGL v d)

def lgCurve (ga : Fin d → PowerSeries C) : Fin d → PowerSeries C :=
  fun a => subst ga (G.lg a)

def add (ga gb : Fin d → PowerSeries C) : Fin d → PowerSeries C :=
  fun a => subst (Sum.elim ga gb) (G.F a)

def sumList (G : LogFGL v d) : List (Fin d → PowerSeries C) → (Fin d → PowerSeries C)
  | [] => 0
  | g :: l => G.add g (sumList G l)

def sumF {m : ℕ} (g : Fin m → Fin d → PowerSeries C) : Fin d → PowerSeries C :=
  G.sumList (List.ofFn g)

def nsmulF (G : LogFGL v d) : ℕ → (Fin d → PowerSeries C) → (Fin d → PowerSeries C)
  | 0, _ => 0
  | n + 1, ga => G.add ga (nsmulF G n ga)

def lc (p : ℕ) (ga : Fin d → PowerSeries C) (n : ℕ) : Fin d → C :=
  fun a => PowerSeries.coeff (p ^ n) (G.lgCurve ga a)

def IsPTypical (p : ℕ) (ga : Fin d → PowerSeries C) : Prop :=
  ∀ a m, (∀ n, m ≠ p ^ n) → PowerSeries.coeff m (G.lgCurve ga a) = 0

def IsOfType (p : ℕ) {h : ℕ} (ty : Fin d → ZMod h) (i : ZMod h)
    (ga : Fin d → PowerSeries C) : Prop :=
  G.IsPTypical p ga ∧ ∀ (n : ℕ) a, ty a ≠ i + (n : ZMod h) → G.lc p ga n a = 0

end LogFGL

structure MuAction {v : AddValuation C (WithTop ℝ)} {d : ℕ} (G : LogFGL v d) (p h : ℕ)
    (ty : Fin d → ZMod h) where
  mul : C → Fin d → MvPowerSeries (Fin d) C
  mul_int : ∀ z, z ^ (p ^ h - 1) = 1 → ∀ a, MvIsInt v (mul z a)
  mul_const : ∀ z a, constantCoeff (mul z a) = 0
  lg_mul : ∀ z, z ^ (p ^ h - 1) = 1 → ∀ a,
    subst (mul z) (G.lg a) = (z ^ (p ^ (ty a).val)) • G.lg a

def expComp [CharZero C] (Ω : C) (lg : PowerSeries C) : PowerSeries C :=
  PowerSeries.mk fun m => ∑ n ∈ Finset.range (m + 1),
    Ω ^ n / (n.factorial : C) * PowerSeries.coeff m (lg ^ n)

def lgSum {d M : ℕ} (p : ℕ) (c : Fin d → ℕ → Fin d → C)
    (t : Fin d → MvPowerSeries (Fin M) C) (b : Fin d) : MvPowerSeries (Fin M) C :=
  fun α => ∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a, c a n b * coeff α (t a ^ (p ^ n))

def OrdGe (v : AddValuation C (WithTop ℝ)) {M : ℕ} (ρ : Fin M → ℝ) (g : MvPowerSeries (Fin M) C)
    (r : ℝ) : Prop :=
  ∀ α : Fin M →₀ ℕ, (((r - ∑ m, ρ m * α m : ℝ)) : WithTop ℝ) ≤ v (coeff α g)

def radius (p : ℕ) (k : ℤ) : ℝ := (1 + (p : ℝ) ^ (-(2 * k + 1))) / ((p : ℝ) ^ 2 - 1)

end

end ReciprocityTheory.PGsh
end

section -- merged from ReciprocityTheory.DualLattices.TensorSpan
noncomputable section

open Finset

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] (R : Type) [CommRing R] [Algebra R C]

def intFun (X : Type) : Submodule R (X → C) where
  carrier := {f | ∀ x, ∃ r : R, algebraMap R C r = f x}
  add_mem' := by
    rintro f g hf hg x
    obtain ⟨r, hr⟩ := hf x
    obtain ⟨s, hs⟩ := hg x
    exact ⟨r + s, by simp [hr, hs]⟩
  zero_mem' := fun _ => ⟨0, by simp⟩
  smul_mem' := by
    rintro c f hf x
    obtain ⟨r, hr⟩ := hf x
    exact ⟨c * r, by simp [hr, Algebra.smul_def]⟩

def tensorSpan {X : Type} (M : Submodule R (X → C)) : Submodule R (X × X → C) :=
  Submodule.span R {F | ∃ g ∈ M, ∃ h ∈ M, F = fun p => g p.1 * h p.2}

def IsLat {X : Type} [Fintype X] [DecidableEq X] (M : Submodule R (X → C)) : Prop :=
  ∃ B : Matrix X X C, IsUnit B.det ∧ M = Submodule.span R (Set.range fun j x => B x j)

def HasColen (v : Valuation C NNReal) {X : Type} [Fintype X] [DecidableEq X]
    (M : Submodule R (X → C)) (c : NNReal) : Prop :=
  ∃ B : Matrix X X C, M = Submodule.span R (Set.range fun j x => B x j) ∧ v B.det = c

def addPull (N : Type) [AddCommGroup N] : (N → C) →ₗ[R] (N × N → C) :=
  LinearMap.funLeft R C (fun p : N × N => p.1 + p.2)

structure HopfOrder (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] where
  carrier : Submodule R (N → C)
  lat : IsLat R carrier
  le_int : carrier ≤ intFun R N
  one_mem : (1 : N → C) ∈ carrier
  mul_mem : ∀ f g, f ∈ carrier → g ∈ carrier → f * g ∈ carrier
  comul : ∀ f ∈ carrier, addPull R N f ∈ tensorSpan R carrier
  antipode : ∀ f ∈ carrier, (fun x => f (-x)) ∈ carrier

variable {R}

def dualLat {X : Type} [Fintype X] (M : Submodule R (X → C)) : Submodule R (X → C) where
  carrier := {u | ∀ f ∈ M, ∃ r : R, algebraMap R C r = ∑ a, u a * f a}
  add_mem' := by
    rintro u w hu hw f hf
    obtain ⟨r, hr⟩ := hu f hf
    obtain ⟨s, hs⟩ := hw f hf
    exact ⟨r + s, by simp [hr, hs, add_mul, Finset.sum_add_distrib]⟩
  zero_mem' := fun _ _ => ⟨0, by simp⟩
  smul_mem' := by
    rintro c u hu f hf
    obtain ⟨r, hr⟩ := hu f hf
    refine ⟨c * r, ?_⟩
    simp only [map_mul, hr, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum, mul_assoc]

def fourier {N H : Type} [Fintype N] (e : H → N → C) :
    (N → C) →ₗ[R] (H → C) where
  toFun u h := ∑ a, u a * e h a
  map_add' u w := by ext h; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c u := by ext h; simp [Algebra.smul_def, Finset.mul_sum, mul_assoc]

def augIdeal {X : Type} [AddCommGroup X] (M : Submodule R (X → C)) : Submodule R (X → C) :=
  M ⊓ LinearMap.ker (LinearMap.proj (R := R) (φ := fun _ : X => C) 0)

def resK {N : Type} [AddCommGroup N] (K : AddSubgroup N) : (N → C) →ₗ[R] (K → C) :=
  LinearMap.funLeft R C (fun k : K => (k : N))

def pullQ {N : Type} [AddCommGroup N] (K : AddSubgroup N) : (N ⧸ K → C) →ₗ[R] (N → C) :=
  LinearMap.funLeft R C (QuotientAddGroup.mk : N → N ⧸ K)

def extK {N : Type} [AddCommGroup N] (K : AddSubgroup N) [DecidablePred (· ∈ K)] :
    (K → C) →ₗ[R] (N → C) where
  toFun u a := if h : a ∈ K then u ⟨a, h⟩ else 0
  map_add' u w := by ext a; by_cases h : a ∈ K <;> simp [h]
  map_smul' c u := by ext a; by_cases h : a ∈ K <;> simp [h]

def pushQ {N : Type} [AddCommGroup N] [Fintype N] (K : AddSubgroup N)
    [DecidableEq (N ⧸ K)] : (N → C) →ₗ[R] (N ⧸ K → C) where
  toFun u c := ∑ a ∈ Finset.univ.filter (fun a : N => (a : N ⧸ K) = c), u a
  map_add' u w := by ext c; simp [Finset.sum_add_distrib]
  map_smul' c u := by ext d; simp [Finset.smul_sum]

end ReciprocityTheory.PGsh.L2
end
end

section -- merged from ReciprocityTheory.DualLattices.SmallLevelClassSet
noncomputable section

open Polynomial Matrix
open scoped TensorProduct

namespace ReciprocityTheory.PGsh

def stdJ (D : Type*) [CommRing D] (g : ℕ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D :=
  Matrix.fromBlocks 0 (-1) 1 0

def ExistsPointLeviLogNormSqPos : Prop :=
  ∀ (D : Type) [CommRing D] [IsDomain D] (g : ℕ)
    (E Φ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D) (c : D),
    Eᵀ = -E → (∀ i, E i i = 0) → IsUnit E.det → c ≠ 0 →
    Φᵀ * stdJ D g * Φ = c • E →
    let Ht : Matrix (Fin g) (Fin g ⊕ Fin g) D := Φ.submatrix Sum.inl id
    let Bt : Matrix (Fin g) (Fin g ⊕ Fin g) D := Φ.submatrix Sum.inr id
    let hb : Matrix (Fin g ⊕ Fin g) (Fin g) D := (Eᵀ)⁻¹ * Htᵀ
    let ι := algebraMap D (FractionRing D)
    (∀ f : Fin g → D, ∃ t : Fin g ⊕ Fin g → D, Ht *ᵥ t = c • f) ∧
    Ht * hb = 0 ∧ Bt * hb = c • (1 : Matrix (Fin g) (Fin g) D) ∧ hbᵀ * E * hb = 0 ∧
    (∀ t : Fin g ⊕ Fin g → FractionRing D, Ht.map ι *ᵥ t = 0 →
      ∃ x : Fin g → FractionRing D, hb.map ι *ᵥ x = t) ∧
    (∀ x : Fin g → FractionRing D, (∃ w : Fin g ⊕ Fin g → D, hb.map ι *ᵥ x = ι ∘ w) →
      ∃ y : Fin g → D, c • x = ι ∘ y)

abbrev extModR (R K V : Type*) [CommRing R] [Field K] [Algebra R K] [AddCommGroup V]
    [Module K V] : Module R (ExteriorAlgebra K V) :=
  Module.compHom _ (algebraMap R K)

attribute [local instance] extModR

def TruncatedPolynomialStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k H : Type) [Field k] [CharP k p] [CommRing H] [HopfAlgebra k H]
    [FiniteDimensional k H] (d : ℕ) (x : Fin d → H),
    (∀ f ∈ RingHom.ker (Bialgebra.counitAlgHom k H), f ^ p = 0) →
    (∀ i, x i ∈ RingHom.ker (Bialgebra.counitAlgHom k H)) →
    (∀ y ∈ RingHom.ker (Bialgebra.counitAlgHom k H), ∃ l : Fin d → k,
      y - ∑ i, l i • x i ∈ RingHom.ker (Bialgebra.counitAlgHom k H) ^ 2) →
    (∀ l : Fin d → k, ∑ i, l i • x i ∈ RingHom.ker (Bialgebra.counitAlgHom k H) ^ 2 → l = 0) →
    Function.Surjective (MvPolynomial.aeval (R := k) x) ∧
      RingHom.ker (MvPolynomial.aeval (R := k) x) =
        Ideal.span (Set.range fun i => (MvPolynomial.X i : MvPolynomial (Fin d) k) ^ p)

end ReciprocityTheory.PGsh
end
end

section -- merged from ReciprocityTheory.DualLattices.CyclicRecursionStatement
noncomputable section

open WittVector Ideal

namespace ReciprocityTheory.PGsh

section Ainf

variable (p : ℕ) [Fact p.Prime] (C : Type) [Field C] (v : Valuation C NNReal)
  (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

def KerThetaStatement : Prop :=
  ∀ pflat : PreTilt O p, pflat.untilt = (p : O) →
    RingHom.ker (fontaineTheta O p) =
        span {(p : WittVector p (PreTilt O p)) - teichmuller p pflat} ∧
      ((p : WittVector p (PreTilt O p)) - teichmuller p pflat) ∈
        nonZeroDivisors (WittVector p (PreTilt O p)) ∧
      RingHom.ker ((Ideal.Quotient.mk (span {(p : O)})).comp (fontaineTheta O p)) =
        span {(p : WittVector p (PreTilt O p)), teichmuller p pflat}

def XiNuStatement : Prop :=
  ∀ ε : PreTilt O p, v.Integers O →
    IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p →
      teichmuller p ε - 1 =
          (∑ i ∈ Finset.range p, teichmuller p ((frobeniusEquiv (PreTilt O p) p).symm ε) ^ i) *
            (teichmuller p ((frobeniusEquiv (PreTilt O p) p).symm ε) - 1) ∧
        fontaineTheta O p (teichmuller p ((frobeniusEquiv (PreTilt O p) p).symm ε) - 1) =
          ((frobeniusEquiv (PreTilt O p) p).symm ε).untilt - 1 ∧
        v (algebraMap O C (fontaineTheta O p
            (teichmuller p ((frobeniusEquiv (PreTilt O p) p).symm ε) - 1))) ^ (p - 1) =
          v (p : C) ∧
        ∀ pflat : PreTilt O p, pflat.untilt = (p : O) →
          RingHom.ker (fontaineTheta O p) =
              span {∑ i ∈ Finset.range p,
                teichmuller p ((frobeniusEquiv (PreTilt O p) p).symm ε) ^ i} ∧
            ∃ u : (WittVector p (PreTilt O p))ˣ,
              ∑ i ∈ Finset.range p, teichmuller p ((frobeniusEquiv (PreTilt O p) p).symm ε) ^ i =
                u * ((p : WittVector p (PreTilt O p)) - teichmuller p pflat)

def RegularStatement : Prop :=
  ∀ pflat : PreTilt O p, pflat.untilt = (p : O) →
    (p : WittVector p (PreTilt O p)) ∈ nonZeroDivisors (WittVector p (PreTilt O p)) ∧
      (∀ x : WittVector p (PreTilt O p),
          teichmuller p pflat * x ∈ span {(p : WittVector p (PreTilt O p))} →
            x ∈ span {(p : WittVector p (PreTilt O p))}) ∧
      span {(p : WittVector p (PreTilt O p)), teichmuller p pflat} ≠ ⊤

def FlatW'Statement : Prop :=
  ∀ pflat : PreTilt O p, pflat.untilt = (p : O) →
    span {(p : WittVector p (PreTilt O p)) ^ 2, teichmuller p pflat} =
        span {((p : WittVector p (PreTilt O p)) - teichmuller p pflat) ^ 2, teichmuller p pflat} ∧
      ((p : WittVector p (PreTilt O p) ⧸
          span {(p : WittVector p (PreTilt O p)) ^ 2, teichmuller p pflat}) ^ 2 = 0) ∧
      (∀ x : WittVector p (PreTilt O p) ⧸
            span {(p : WittVector p (PreTilt O p)) ^ 2, teichmuller p pflat},
          (p : WittVector p (PreTilt O p) ⧸
              span {(p : WittVector p (PreTilt O p)) ^ 2, teichmuller p pflat}) * x = 0 →
            ∃ y, x = (p : WittVector p (PreTilt O p) ⧸
              span {(p : WittVector p (PreTilt O p)) ^ 2, teichmuller p pflat}) * y) ∧
      ∀ [Algebra (ZMod (p ^ 2)) (WittVector p (PreTilt O p) ⧸
          span {(p : WittVector p (PreTilt O p)) ^ 2, teichmuller p pflat})],
        Module.Flat (ZMod (p ^ 2)) (WittVector p (PreTilt O p) ⧸
          span {(p : WittVector p (PreTilt O p)) ^ 2, teichmuller p pflat})

end Ainf

def TiltStructureStatement (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O],
      (∃ pflat : PreTilt O p, pflat.untilt = (p : O)) ∧
      (∃ ε : PreTilt O p, IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) ∧
      KerThetaStatement p O ∧ XiNuStatement p C v O ∧ RegularStatement p O ∧
      FlatW'Statement p O

def TeichSumStatement (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (ι : Type) (s : Finset ι),
    (∃ S : MvPolynomial ι ℤ, (p : MvPolynomial ι ℤ) * S =
      ∑ i ∈ s, MvPolynomial.X i ^ p - (∑ i ∈ s, MvPolynomial.X i) ^ p) ∧
    ∀ (K : Type) [CommRing K] [CharP K p] [PerfectRing K p] (X : ι → K) (S : MvPolynomial ι ℤ),
      (p : MvPolynomial ι ℤ) * S =
          ∑ i ∈ s, MvPolynomial.X i ^ p - (∑ i ∈ s, MvPolynomial.X i) ^ p →
        (∃ w : WittVector p K,
          ∑ i ∈ s, teichmuller p (X i) =
            teichmuller p (∑ i ∈ s, X i) + (p : WittVector p K) *
              teichmuller p (MvPolynomial.aeval (fun i => (frobeniusEquiv K p).symm (X i)) S) +
              (p : WittVector p K) ^ 2 * w) ∧
        ∀ (y : K) (t : WittVector p K), ∃ w : WittVector p K,
          (teichmuller p y + (p : WittVector p K) * t) ^ p =
            teichmuller p (y ^ p) + (p : WittVector p K) ^ 2 * w

end ReciprocityTheory.PGsh
end
end

section -- merged from ReciprocityTheory.DualLattices.IsUnitDetOfSpanEq
noncomputable section

open Matrix Finset

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}

theorem det_map_algebraMap {X : Type} [Fintype X] [DecidableEq X] (M : Matrix X X R) :
    (M.map (algebraMap R C)).det = algebraMap R C M.det := by
  rw [RingHom.map_det]
  rfl

theorem eq_one_of_le_one_of_mul_eq_one {a b : NNReal} (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) :
    a = 1 := by
  have h1 := mul_le_of_le_one_right (zero_le : (0 : NNReal) ≤ a) hb
  rw [h] at h1
  exact le_antisymm ha h1

private lemma cols_mul_lemma {X : Type} [Fintype X] [DecidableEq X] {P Q : Matrix X X C}
    (h : Submodule.span R (Set.range fun j x => Q x j) ≤
      Submodule.span R (Set.range fun j x => P x j)) :
    ∃ A : Matrix X X R, Q = P * A.map (algebraMap R C) := by
  have hc : ∀ j, ∃ c : X → R, ∑ i, c i • (fun x => P x i) = fun x => Q x j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun R).1 (h (Submodule.subset_span ⟨j, rfl⟩))
  choose c hc using hc
  refine ⟨Matrix.of fun i j => c j i, ?_⟩
  ext x j
  have hx := congrFun (hc j) x
  simp only [Finset.sum_apply, Pi.smul_apply] at hx
  rw [Matrix.mul_apply, ← hx]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Algebra.smul_def, mul_comm]

theorem valuation_det_eq_of_span_eq_alt (hv : v.Integers R) {X : Type} [Fintype X] [DecidableEq X]
    {P Q : Matrix X X C} (hP : IsUnit P.det)
    (h : Submodule.span R (Set.range fun j x => P x j) =
      Submodule.span R (Set.range fun j x => Q x j)) :
    v Q.det = v P.det := by
  obtain ⟨A, hA⟩ := cols_mul_lemma (R := R) h.ge
  obtain ⟨B, hB⟩ := cols_mul_lemma (R := R) h.le
  have hdQ : Q.det = P.det * algebraMap R C A.det := by
    rw [hA, Matrix.det_mul, det_map_algebraMap]
  have hdP : P.det = Q.det * algebraMap R C B.det := by
    rw [hB, Matrix.det_mul, det_map_algebraMap]
  have hAB : algebraMap R C A.det * algebraMap R C B.det = 1 := by
    refine mul_left_cancel₀ hP.ne_zero ?_
    calc P.det * (algebraMap R C A.det * algebraMap R C B.det)
        = P.det * algebraMap R C A.det * algebraMap R C B.det := (mul_assoc _ _ _).symm
      _ = P.det := by rw [← hdQ, ← hdP]
      _ = P.det * 1 := (mul_one _).symm
  have hvA : v (algebraMap R C A.det) = 1 :=
    eq_one_of_le_one_of_mul_eq_one (hv.map_le_one _) (hv.map_le_one _)
      (by rw [← map_mul v, hAB, map_one])
  rw [hdQ, map_mul, hvA, mul_one]

theorem exists_matrix_span_eq (hv : v.Integers R) {X : Type} [Fintype X] [DecidableEq X]
    (M : Submodule R (X → C)) (hfg : M.FG)
    (hsp : Submodule.span C (M : Set (X → C)) = ⊤) :
    ∃ β : Matrix X X C, IsUnit β.det ∧ M = Submodule.span R (Set.range fun j x => β x j) := by
  classical
  obtain ⟨S, rfl⟩ := hfg
  rw [Submodule.span_span_of_tower] at hsp
  suffices key : ∀ (n : ℕ) (S : Finset (X → C)), S.card = n →
      Submodule.span C (↑S : Set (X → C)) = ⊤ →
      ∃ β : Matrix X X C, IsUnit β.det ∧
        Submodule.span R (↑S : Set (X → C)) = Submodule.span R (Set.range fun j x => β x j) from
    key _ S rfl hsp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hn hspC
  by_cases hli : LinearIndependent C (fun i : S => (i : X → C))
  · have hb := Module.Basis.mk hli (by simpa using hspC.ge)
    let e : X ≃ S := (hb.indexEquiv (Pi.basisFun C X)).symm
    refine ⟨Matrix.of fun x j => ((e j : S) : X → C) x, ?_, ?_⟩
    · refine (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 ?_)
      exact hli.comp e e.injective
    · congr 1
      ext f
      constructor
      · intro hf
        exact ⟨e.symm ⟨f, hf⟩, by ext x; simp⟩
      · rintro ⟨j, rfl⟩
        exact (e j).2
  · obtain ⟨g, hg, i1, hi1⟩ := Fintype.not_linearIndependent_iff.1 hli
    obtain ⟨i0, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => v (g i))
      ⟨i1, Finset.mem_univ _⟩
    have hg0 : g i0 ≠ 0 := by
      intro h0
      have h2 := hmax i1 (Finset.mem_univ _)
      rw [h0, map_zero] at h2
      exact hi1 ((Valuation.zero_iff v).1 (le_antisymm h2 zero_le))
    have key : (i0 : X → C) =
        ∑ i ∈ Finset.univ.erase i0, (-(g i * (g i0)⁻¹)) • (i : X → C) := by
      have h1 := Finset.add_sum_erase Finset.univ (fun i => g i • (i : X → C)) (Finset.mem_univ i0)
      rw [hg] at h1
      have h2 : g i0 • (i0 : X → C) = -∑ i ∈ Finset.univ.erase i0, g i • (i : X → C) :=
        eq_neg_of_add_eq_zero_left h1
      calc (i0 : X → C) = (g i0)⁻¹ • (g i0 • (i0 : X → C)) := by
            rw [smul_smul, inv_mul_cancel₀ hg0, one_smul]
        _ = _ := by
          rw [h2, smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_smul, neg_smul, mul_comm]
    have hle1 : ∀ i, v (-(g i * (g i0)⁻¹)) ≤ 1 := by
      intro i
      rw [Valuation.map_neg, map_mul, map_inv₀]
      calc v (g i) * (v (g i0))⁻¹ ≤ v (g i0) * (v (g i0))⁻¹ :=
            mul_le_mul_of_nonneg_right (hmax i (Finset.mem_univ _)) zero_le
        _ = 1 := mul_inv_cancel₀ ((Valuation.ne_zero_iff v).2 hg0)
    choose r hr using fun i => hv.exists_of_le_one (hle1 i)
    have hx0R : (i0 : X → C) ∈ Submodule.span R (↑(S.erase (i0 : X → C)) : Set (X → C)) := by
      have hsum : (∑ i ∈ Finset.univ.erase i0, (-(g i * (g i0)⁻¹)) • (i : X → C)) ∈
          Submodule.span R (↑(S.erase (i0 : X → C)) : Set (X → C)) := by
        refine Submodule.sum_mem _ fun i hi => ?_
        rw [← hr i, algebraMap_smul]
        refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
        exact Finset.mem_coe.2 (Finset.mem_erase.2
          ⟨fun h => (Finset.mem_erase.1 hi).1 (Subtype.ext h), i.2⟩)
      rw [← key] at hsum
      exact hsum
    have hx0C : (i0 : X → C) ∈ Submodule.span C (↑(S.erase (i0 : X → C)) : Set (X → C)) :=
      Submodule.span_le_restrictScalars R C _ hx0R
    have hS : (↑S : Set (X → C)) = insert (i0 : X → C) ↑(S.erase (i0 : X → C)) := by
      rw [← Finset.coe_insert, Finset.insert_erase i0.2]
    have hspR : Submodule.span R (↑S : Set (X → C)) =
        Submodule.span R (↑(S.erase (i0 : X → C)) : Set (X → C)) := by
      rw [hS, Submodule.span_insert_eq_span hx0R]
    have hspC' : Submodule.span C (↑(S.erase (i0 : X → C)) : Set (X → C)) = ⊤ := by
      rw [← hspC, hS, Submodule.span_insert_eq_span hx0C]
    obtain ⟨β, hβ, hβS⟩ := ih _ (by rw [← hn]; exact Finset.card_erase_lt_of_mem i0.2)
      (S.erase (i0 : X → C)) rfl hspC'
    exact ⟨β, hβ, hspR.trans hβS⟩

private lemma cols_le_lemma_2 {X : Type} [Fintype X] [DecidableEq X] {P Q : Matrix X X C}
    (A : Matrix X X R) (hA : Q = P * A.map (algebraMap R C)) :
    Submodule.span R (Set.range fun j x => Q x j) ≤
      Submodule.span R (Set.range fun j x => P x j) := by
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have hcol : (fun x => Q x j) = ∑ i, A i j • fun x => P x i := by
    ext x
    simp [hA, Matrix.mul_apply, Finset.sum_apply, Algebra.smul_def, mul_comm]
  show (fun x => Q x j) ∈ Submodule.span R _
  rw [hcol]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem inv_mem_of_valuation_eq_one (hv : v.Integers R) {X : Type} [Fintype X] [DecidableEq X]
    (A : Submodule R (X → C)) (P : Matrix X X C) (hP : IsUnit P.det)
    (hA : A = Submodule.span R (Set.range fun j x => P x j))
    (one : (1 : X → C) ∈ A) (mul : ∀ f g, f ∈ A → g ∈ A → f * g ∈ A)
    (u : X → C) (hu : u ∈ A) (hunit : ∀ x, v (u x) = 1) : u⁻¹ ∈ A := by
  have hu0 : ∀ x, u x ≠ 0 := fun x h0 => by simpa [h0] using hunit x
  have hPA : ∀ j, (fun x => P x j) ∈ A := fun j => by
    rw [hA]; exact Submodule.subset_span ⟨j, rfl⟩
  have hcolD : ∀ j, (fun x => (Matrix.diagonal u * P) x j) = u * fun x => P x j := by
    intro j; ext x; simp [Matrix.diagonal_mul]
  have hDle : Submodule.span R (Set.range fun j x => (Matrix.diagonal u * P) x j) ≤
      Submodule.span R (Set.range fun j x => P x j) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    show (fun x => (Matrix.diagonal u * P) x j) ∈ Submodule.span R _
    rw [hcolD, ← hA]
    exact mul u _ hu (hPA j)
  obtain ⟨T, hT⟩ := cols_mul_lemma hDle
  have hdT : algebraMap R C T.det = ∏ x, u x := by
    have e := congrArg Matrix.det hT
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, det_map_algebraMap] at e
    exact mul_left_cancel₀ hP.ne_zero (by rw [← e]; ring)
  have hvT : v (algebraMap R C T.det) = 1 := by
    rw [hdT, map_prod]
    exact Finset.prod_eq_one fun x _ => hunit x
  have hy : algebraMap R C T.det ≠ 0 := by
    rw [hdT]; exact Finset.prod_ne_zero_iff.2 fun x _ => hu0 x
  obtain ⟨s, hs⟩ := hv.exists_of_le_one
    (show v (algebraMap R C T.det)⁻¹ ≤ 1 from le_of_eq (by rw [map_inv₀, hvT, inv_one]))
  have hTs : T.det * s = 1 := hv.hom_inj (by rw [map_mul, hs, mul_inv_cancel₀ hy, map_one])
  have hTu : IsUnit T.det := ⟨⟨T.det, s, hTs, by rw [mul_comm]; exact hTs⟩, rfl⟩
  have hPD : P = (Matrix.diagonal u * P) * (T⁻¹).map (algebraMap R C) := by
    rw [hT, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv T hTu]
    simp
  have hPle := cols_le_lemma_2 _ hPD
  have hmem : (1 : X → C) ∈
      Submodule.span R (Set.range fun j x => (Matrix.diagonal u * P) x j) :=
    hPle (by rw [← hA]; exact one)
  have hle : Submodule.span R (Set.range fun j x => (Matrix.diagonal u * P) x j) ≤
      A.comap (LinearMap.mulLeft R u⁻¹) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    convert hPA j using 1
    ext x
    simp [Matrix.diagonal_mul, hu0 x]
  simpa using hle hmem

end ReciprocityTheory.PGsh.L2
end
end

section -- merged from ReciprocityTheory.DualLattices.VIntCastLtOneOfDvd
noncomputable section

open Finset

namespace ReciprocityTheory.PGsh.Up.U3

variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]

theorem v_natCast_le_one (hv : v.Integers R) (n : ℕ) : v (n : C) ≤ 1 := by
  rw [← map_natCast (algebraMap R C) n]
  exact hv.map_le_one _

theorem v_intCast_le_one (hv : v.Integers R) (n : ℤ) : v (n : C) ≤ 1 := by
  rw [← map_intCast (algebraMap R C) n]
  exact hv.map_le_one _

theorem v_intCast_lt_one_of_dvd (hv : v.Integers R) (hpv : v (p : C) < 1) {n : ℤ}
    (h : (p : ℤ) ∣ n) : v (n : C) < 1 := by
  obtain ⟨m, rfl⟩ := h
  push_cast
  rw [map_mul]
  calc v (p : C) * v (m : C) ≤ v (p : C) * 1 :=
        mul_le_mul_of_nonneg_left (v_intCast_le_one hv m) zero_le'
    _ < 1 := by rw [mul_one]; exact hpv

theorem v_intCast_eq_one (hv : v.Integers R) (hpv : v (p : C) < 1) {n : ℤ}
    (h : ¬ (p : ℤ) ∣ n) : v (n : C) = 1 := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  obtain ⟨a, b, hab⟩ := (Prime.coprime_iff_not_dvd hpz).mpr h
  have h1 : (a : C) * (p : C) + (b : C) * (n : C) = 1 := by
    have := congrArg (Int.cast : ℤ → C) hab
    push_cast at this
    exact this
  have ha : v ((a : C) * (p : C)) < 1 := by
    rw [map_mul]
    calc v (a : C) * v (p : C) ≤ 1 * v (p : C) :=
          mul_le_mul_of_nonneg_right (v_intCast_le_one hv a) zero_le'
      _ < 1 := by rw [one_mul]; exact hpv
  have hb : 1 ≤ v ((b : C) * (n : C)) := by
    by_contra hlt
    push_neg at hlt
    have := v.map_add_lt ha hlt
    rw [h1, map_one] at this
    exact lt_irrefl _ this
  refine le_antisymm (v_intCast_le_one hv n) ?_
  rw [map_mul] at hb
  calc 1 ≤ v (b : C) * v (n : C) := hb
    _ ≤ 1 * v (n : C) := mul_le_mul_of_nonneg_right (v_intCast_le_one hv b) zero_le'
    _ = v (n : C) := one_mul _

theorem v_le_one_of_pow_eq {r : C} (hr : r ^ p = r) : v r ≤ 1 := by
  by_contra h
  push_neg at h
  have h2 : 2 ≤ p := hp.out.two_le
  have key : v r ^ 1 < v r ^ p := pow_lt_pow_right₀ h (by omega)
  rw [pow_one, ← map_pow, hr] at key
  exact lt_irrefl _ key

theorem v_pow_sub_le {r s : C} (hr : v r ≤ 1) (hs : v s ≤ 1) (i : ℕ) :
    v (r ^ i - s ^ i) ≤ v (r - s) := by
  rw [← geom_sum₂_mul, map_mul]
  have hS : v (∑ j ∈ range i, r ^ j * s ^ (i - 1 - j)) ≤ 1 := by
    apply v.map_sum_le
    intro j _
    rw [map_mul, map_pow, map_pow]
    exact mul_le_one₀ (pow_le_one₀ zero_le' hr) zero_le' (pow_le_one₀ zero_le' hs)
  calc _ ≤ 1 * v (r - s) := mul_le_mul_of_nonneg_right hS zero_le'
    _ = _ := one_mul _

theorem teich_unique (hv : v.Integers R) (hpv : v (p : C) < 1) {r s : C} (hr : r ^ p = r)
    (hs : s ^ p = s) (h : v (r - s) < 1) : r = s := by
  by_contra hne
  have hd : r - s ≠ 0 := sub_ne_zero.mpr hne
  have hr1 : v r ≤ 1 := v_le_one_of_pow_eq hr
  have hs1 : v s ≤ 1 := v_le_one_of_pow_eq hs
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ k ∈ range p, r ^ k * s ^ (p - 1 - k) := ⟨_, rfl⟩
  have hSd : S * (r - s) = r - s := by rw [hS, geom_sum₂_mul, hr, hs]
  have hS1 : S = 1 := mul_right_cancel₀ hd (by rw [hSd, one_mul])
  have hconst : ∑ k ∈ range p, s ^ k * s ^ (p - 1 - k) = (p : C) * s ^ (p - 1) := by
    rw [Finset.sum_congr rfl (g := fun _ => s ^ (p - 1)) (fun k hk => by
      rw [← pow_add]
      congr 1
      have := Finset.mem_range.mp hk
      omega)]
    simp
  have hdiff : S - (p : C) * s ^ (p - 1) = ∑ k ∈ range p, (r ^ k - s ^ k) * s ^ (p - 1 - k) := by
    rw [← hconst, hS, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hlt1 : v (S - (p : C) * s ^ (p - 1)) < 1 := by
    rw [hdiff]
    apply v.map_sum_lt one_ne_zero
    intro k _
    rw [map_mul]
    calc v (r ^ k - s ^ k) * v (s ^ (p - 1 - k)) ≤ v (r ^ k - s ^ k) * 1 :=
          mul_le_mul_of_nonneg_left (by rw [map_pow]; exact pow_le_one₀ zero_le' hs1) zero_le'
      _ ≤ v (r - s) := by rw [mul_one]; exact v_pow_sub_le hr1 hs1 k
      _ < 1 := h
  have hlt2 : v ((p : C) * s ^ (p - 1)) < 1 := by
    rw [map_mul, map_pow]
    calc v (p : C) * v s ^ (p - 1) ≤ v (p : C) * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ zero_le' hs1) zero_le'
      _ < 1 := by rw [mul_one]; exact hpv
  have hv : v S < 1 := by
    have := v.map_add_lt hlt1 hlt2
    rwa [sub_add_cancel] at this
  rw [hS1, map_one] at hv
  exact lt_irrefl _ hv

theorem exists_teich [IsAlgClosed C] (hv : v.Integers R) (hpv : v (p : C) < 1) (n : ℕ) :
    ∃ r : C, r ^ p = r ∧ v (r - n) < 1 := by
  have hdvd : (p : ℤ) ∣ ((n : ℤ) ^ p - n) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.pow_card, sub_self]
  have hv1 : v ((n : C) ^ p - n) < 1 := by
    have := v_intCast_lt_one_of_dvd hv hpv hdvd
    push_cast at this
    exact this
  have hmon : (Polynomial.X ^ p - Polynomial.X : Polynomial C).Monic :=
    Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast hp.out.one_lt)
  have heq : (Polynomial.X ^ p - Polynomial.X : Polynomial C) =
      ((Polynomial.X ^ p - Polynomial.X : Polynomial C).roots.map (fun a => Polynomial.X - Polynomial.C a)).prod := by
    first
    | exact Polynomial.eq_prod_roots_of_monic_of_splits_id hmon (IsAlgClosed.splits _)
    | exact (Polynomial.Monic.eq_prod_roots_of_splits_id hmon (IsAlgClosed.splits _))
    | (have hc := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
          (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits (Polynomial.X ^ p - Polynomial.X : Polynomial C)))
       rw [hmon.leadingCoeff, map_one, one_mul] at hc
       exact hc.symm)
    | (have hc := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
          (IsAlgClosed.card_roots_eq_natDegree (k := C) (p := Polynomial.X ^ p - Polynomial.X))
       rw [hmon.leadingCoeff, map_one, one_mul] at hc
       exact hc.symm)
  have heval : (n : C) ^ p - n =
      ((Polynomial.X ^ p - Polynomial.X : Polynomial C).roots.map (fun a => (n : C) - a)).prod := by
    have := congrArg (Polynomial.eval (n : C)) heq
    rw [Polynomial.eval_multiset_prod, Multiset.map_map] at this
    simpa [Function.comp_def] using this
  by_contra hno
  push_neg at hno
  have hge : 1 ≤ v ((n : C) ^ p - n) := by
    rw [heval, map_multiset_prod, Multiset.map_map]
    apply Multiset.one_le_prod_of_one_le
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
    have h2 := (Polynomial.mem_roots hmon.ne_zero).mp ha
    rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X] at h2
    have h3 := hno a (sub_eq_zero.mp h2)
    simp only [Function.comp_apply]
    rwa [Valuation.map_sub_swap]
  exact absurd hv1 (not_lt.mpr hge)

theorem exists_teichChar [IsAlgClosed C] (hv : v.Integers R) (hpv : v (p : C) < 1) :
    ∃ ω : ZMod p → C, (∀ a, ω a ^ p = ω a) ∧ (∀ a, v (ω a - (a.val : C)) < 1) ∧
      ω 0 = 0 ∧ ω 1 = 1 ∧ (∀ a b, ω (a * b) = ω a * ω b) ∧
      (∀ a b, a ≠ b → v (ω a - ω b) = 1) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  choose ω hω1 hω2 using fun a : ZMod p => exists_teich hv hpv (p := p) a.val
  have hω1' : ∀ a, v (ω a) ≤ 1 := fun a => v_le_one_of_pow_eq (hω1 a)
  refine ⟨ω, hω1, hω2, ?_, ?_, ?_, ?_⟩
  · refine teich_unique hv hpv (hω1 0) (zero_pow hp.out.ne_zero) ?_
    simpa using hω2 0
  · refine teich_unique hv hpv (hω1 1) (one_pow _) ?_
    have := hω2 1
    rwa [ZMod.val_one, Nat.cast_one] at this
  · intro a b
    refine teich_unique hv hpv (hω1 (a * b)) (by rw [mul_pow, hω1, hω1]) ?_
    have e4 : v (((a * b).val : C) - (a.val : C) * (b.val : C)) < 1 := by
      have hd : (p : ℤ) ∣ (((a * b).val : ℤ) - (a.val : ℤ) * (b.val : ℤ)) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        simp [ZMod.natCast_zmod_val]
      have := v_intCast_lt_one_of_dvd hv hpv hd
      push_cast at this
      exact this
    have e5 : v ((a.val : C) * (b.val : C) - ω a * ω b) < 1 := by
      have hx : (a.val : C) * b.val - ω a * ω b = -((ω a - a.val) * b.val + ω a * (ω b - b.val)) := by ring
      rw [hx, Valuation.map_neg]
      apply v.map_add_lt
      · rw [map_mul]
        calc _ ≤ v (ω a - a.val) * 1 := mul_le_mul_of_nonneg_left (v_natCast_le_one hv _) zero_le'
          _ < 1 := by rw [mul_one]; exact hω2 a
      · rw [map_mul]
        calc _ ≤ 1 * v (ω b - b.val) := mul_le_mul_of_nonneg_right (hω1' a) zero_le'
          _ < 1 := by rw [one_mul]; exact hω2 b
    have hx : ω (a * b) - ω a * ω b = (ω (a * b) - ((a * b).val : C)) +
        ((((a * b).val : C) - (a.val : C) * (b.val : C)) + ((a.val : C) * (b.val : C) - ω a * ω b)) := by ring
    rw [hx]
    exact v.map_add_lt (hω2 (a * b)) (v.map_add_lt e4 e5)
  · intro a b hab
    refine le_antisymm ((v.map_sub (ω a) (ω b)).trans (max_le (hω1' a) (hω1' b))) ?_
    by_contra hlt
    push_neg at hlt
    have h1 : v ((a.val : C) - (b.val : C)) < 1 := by
      have hx : (a.val : C) - b.val = -(ω a - a.val) + (ω a - ω b) + (ω b - b.val) := by ring
      rw [hx]
      exact v.map_add_lt (v.map_add_lt (by rw [Valuation.map_neg]; exact hω2 a) hlt) (hω2 b)
    have hnd : ¬ (p : ℤ) ∣ ((a.val : ℤ) - (b.val : ℤ)) := by
      intro hd
      apply hab
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hd
      push_cast at hd
      simpa [sub_eq_zero, ZMod.natCast_zmod_val] using hd
    have := v_intCast_eq_one hv hpv hnd
    push_cast at this
    rw [this] at h1
    exact lt_irrefl _ h1

theorem exists_primRoot [IsAlgClosed C] [CharZero C] : ∃ ζ : C, IsPrimitiveRoot ζ p := by
  haveI : NeZero (p : C) := ⟨Nat.cast_ne_zero.mpr hp.out.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic p C) (by
    rw [Polynomial.degree_cyclotomic, Nat.totient_prime hp.out]
    have := hp.out.two_le
    norm_cast
    omega)
  exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζ⟩

theorem val_sub_one_le {α β : C} (hα : IsPrimitiveRoot α p) (hβ : IsPrimitiveRoot β p) :
    v (α - 1) ≤ v (β - 1) := by
  obtain ⟨i, -, hi⟩ := hβ.eq_pow_of_pow_eq_one hα.pow_eq_one
  have hβ1 : v β = 1 :=
    (pow_eq_one_iff_of_nonneg zero_le' hp.out.ne_zero).mp (by rw [← map_pow, hβ.pow_eq_one, map_one])
  rw [← hi]
  have := v_pow_sub_le (v := v) (r := β) (s := 1) hβ1.le (by rw [map_one]) i
  rwa [one_pow] at this

theorem val_prim_root {z : C} (hz : IsPrimitiveRoot z p) : v (z - 1) ^ (p - 1) = v (p : C) := by
  have hcyc := Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hz
  have h1 : (p : C) = ∏ μ ∈ primitiveRoots p C, (1 - μ) := by
    have := congrArg (Polynomial.eval 1) hcyc
    rw [Polynomial.eval_one_cyclotomic_prime, Polynomial.eval_prod] at this
    simpa using this
  have hc : ∀ μ ∈ primitiveRoots p C, v (1 - μ) = v (z - 1) := by
    intro μ hμ
    have hμ' : IsPrimitiveRoot μ p := (mem_primitiveRoots hp.out.pos).mp hμ
    rw [Valuation.map_sub_swap]
    exact le_antisymm (val_sub_one_le hμ' hz) (val_sub_one_le hz hμ')
  rw [h1, map_prod, Finset.prod_congr rfl hc, Finset.prod_const, hz.card_primitiveRoots,
    Nat.totient_prime hp.out]

end ReciprocityTheory.PGsh.Up.U3
end
end

section -- merged from ReciprocityTheory.DualLattices.NearIdentityColengthStatement
namespace ReciprocityTheory.PGsh

open Matrix

def CharTableStatement : Prop :=
  ∀ (K : Type) [Field K] (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (e : G ≃ AddChar G K),
    (Matrix.of fun g h : G => e h g).det ^ 2 = (Fintype.card G : K) ^ Fintype.card G ∨
    (Matrix.of fun g h : G => e h g).det ^ 2 = -(Fintype.card G : K) ^ Fintype.card G

def GaussCongruenceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F] [CharP F p]
    (O : Type) [CommRing O] [IsDomain O] (m : Ideal O) [m.IsPrime]
    (ι : F →+* O ⧸ m) (ω : MulChar F O) (ζ : O),
    Fintype.card F ≠ 2 → ζ ^ p = 1 → (∀ a, Ideal.Quotient.mk m (ω a) = ι a) →
    letI : Algebra (ZMod p) F := ZMod.algebra F p
    ∃ y ∈ m, (∑ a : F, ω⁻¹ a * ζ ^ (Algebra.trace (ZMod p) F a).val) = (ζ - 1) * (y - 1)

end ReciprocityTheory.PGsh
end

section -- merged from ReciprocityTheory.DualLattices.FrobEqOfLe
noncomputable section

open Finset Filter Topology

namespace ReciprocityTheory.PGsh.Up.Det2

theorem v_det_scaled {C : Type} [Field C] (v : Valuation C NNReal) {ι : Type} [Fintype ι]
    [DecidableEq ι] (c : Matrix ι ι C) (y z : ι → C) :
    v (Matrix.of fun j k => c j k * (y j / z k)).det =
      v c.det * (∏ j, v (y j)) / ∏ k, v (z k) := by
  have hM : (Matrix.of fun j k => c j k * (y j / z k)) =
      Matrix.diagonal y * c * Matrix.diagonal fun k => (z k)⁻¹ := by
    ext j k
    simp only [Matrix.of_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, div_eq_mul_inv]
    ring
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, map_mul, map_mul,
    map_prod, map_prod]
  simp only [map_inv₀, Finset.prod_inv_distrib, div_eq_mul_inv]
  ring

end ReciprocityTheory.PGsh.Up.Det2
end
end
