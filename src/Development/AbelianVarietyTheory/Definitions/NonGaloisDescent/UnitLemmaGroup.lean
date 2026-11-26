module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
noncomputable section

namespace GlobalTheory.UnitLemma

open Polynomial

section Orbits

variable (O : Type) [CommRing O] {A : Type} [CommRing A] [Algebra O A]

def mulLat (t : A) (L : Submodule O A) : Submodule O A := L.map (LinearMap.mulLeft O t)

def stabLat (L : Submodule O A) : Subgroup Aˣ where
  carrier := {t | ∀ y, y ∈ L ↔ (t : A) * y ∈ L}
  one_mem' := by intro y; simp
  mul_mem' := by
    intro a b ha hb y
    rw [hb y, ha ((b : A) * y), Units.val_mul, mul_assoc]
  inv_mem' := by
    intro a ha y
    have := ha (((a⁻¹ : Aˣ) : A) * y)
    rw [← mul_assoc, Units.mul_inv, one_mul] at this
    exact this.symm

def intUnits (A : Type) [CommRing A] [Algebra O A] : Subgroup Aˣ where
  carrier := {t | IsIntegral O (t : A) ∧ IsIntegral O ((t⁻¹ : Aˣ) : A)}
  one_mem' := by simpa using isIntegral_one
  mul_mem' := by
    intro a b ha hb
    refine ⟨by simpa using ha.1.mul hb.1, ?_⟩
    rw [mul_inv_rev, Units.val_mul]
    exact hb.2.mul ha.2
  inv_mem' := by
    intro a ha
    exact ⟨ha.2, by simpa using ha.1⟩

def Orb (G : Subgroup Aˣ) (X : Set (Submodule O A)) : Type :=
  Quot fun L M : X => ∃ t ∈ G, (M : Submodule O A) = mulLat O (t : A) (L : Submodule O A)

def orbSum (G : Subgroup Aˣ) (X : Set (Submodule O A)) (w : Submodule O A → ℚ) : ℚ :=
  ∑ᶠ o : Orb O G X, w (Quot.out o).1 *
    (((stabLat O (Quot.out o).1 ⊓ G).relIndex (intUnits O A ⊓ G) : ℕ) : ℚ)

def IsLat (E : Type) [Field E] [Algebra E A] (L : Submodule O A) : Prop :=
  L.FG ∧ Submodule.span E (L : Set A) = ⊤

def countGL (E : Type) [Field E] [Algebra E A] (g : A) : ℚ :=
  orbSum O ⊤ {L | IsLat O E L ∧ ∀ y ∈ L, g * y ∈ L} fun _ => 1

end Orbits

def val (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {E : Type} [Field E]
    [Algebra O E] [IsFractionRing O E] (x : E) : ℤ :=
  -WithZero.log ((IsDiscreteValuationRing.maximalIdeal O).valuation E x)

structure UQ : Type 1 where
  O : Type
  E : Type
  [cO : CommRing O]
  [dO : IsDomain O]
  [dvr : IsDiscreteValuationRing O]
  [cpl : IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  [fin : Finite (IsLocalRing.ResidueField O)]
  [fE : Field E]
  [aOE : Algebra O E]
  [frac : IsFractionRing O E]
  [c0 : CharZero E]
  c : E ≃+* E
  c_c : ∀ x, c (c x) = x
  c_int : ∀ x : O, ∃ y : O, c (algebraMap O E x) = algebraMap O E y
  c_res : ∃ x y : O, c (algebraMap O E x) = algebraMap O E y ∧ x - y ∉ IsLocalRing.maximalIdeal O
  q : ℕ
  card_res : Nat.card (IsLocalRing.ResidueField O) = q ^ 2

attribute [instance] UQ.cO UQ.dO UQ.dvr UQ.cpl UQ.fin UQ.fE UQ.aOE UQ.frac UQ.c0

def UQ.Odd (K : UQ) : Prop := IsUnit (2 : K.O)

def UQ.eta (K : UQ) (x : K.E) : ℚ := (-1 : ℚ) ^ val K.O x

structure InvAlg (K : UQ) : Type 1 where
  A : Type
  [cA : CommRing A]
  [aE : Algebra K.E A]
  [aO : Algebra K.O A]
  [tow : IsScalarTower K.O K.E A]
  [fd : Module.Finite K.E A]
  σ : A ≃+* A
  σ_σ : ∀ y, σ (σ y) = y
  σ_alg : ∀ e : K.E, σ (algebraMap K.E A e) = algebraMap K.E A (K.c e)
  g : A

attribute [instance] InvAlg.cA InvAlg.aE InvAlg.aO InvAlg.tow InvAlg.fd

namespace InvAlg

variable {K : UQ} (B : InvAlg K)

def P : K.E[X] := (LinearMap.mulLeft K.E B.g).charpoly

def prod (B₁ B₂ : InvAlg K) : InvAlg K where
  A := B₁.A × B₂.A
  σ := RingEquiv.prodCongr B₁.σ B₂.σ
  σ_σ := fun y => Prod.ext (B₁.σ_σ y.1) (B₂.σ_σ y.2)
  σ_alg := fun e => Prod.ext (B₁.σ_alg e) (B₂.σ_alg e)
  g := (B₁.g, B₂.g)

def herm (x y z : B.A) : K.E := Algebra.trace K.E B.A (x * y * B.σ z)

def X (x : B.A) : Set (Submodule K.O B.A) :=
  {L | IsLat K.O K.E L ∧ (∀ y ∈ L, B.g * y ∈ L) ∧
    ∀ y, y ∈ L ↔ ∀ z ∈ L, B.herm x y z ∈ (algebraMap K.O K.E).range}

def T : Subgroup B.Aˣ where
  carrier := {t | (t : B.A) * B.σ (t : B.A) = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, map_mul] at ha hb ⊢
    calc (a : B.A) * b * (B.σ a * B.σ b) = ((a : B.A) * B.σ a) * ((b : B.A) * B.σ b) := by ring
      _ = 1 := by rw [ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have h1 : B.σ (a : B.A) * B.σ ((a⁻¹ : B.Aˣ) : B.A) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    calc ((a⁻¹ : B.Aˣ) : B.A) * B.σ ((a⁻¹ : B.Aˣ) : B.A)
        = ((a⁻¹ : B.Aˣ) : B.A) * B.σ ((a⁻¹ : B.Aˣ) : B.A) * ((a : B.A) * B.σ a) := by rw [ha, mul_one]
      _ = (((a⁻¹ : B.Aˣ) : B.A) * a) * (B.σ (a : B.A) * B.σ ((a⁻¹ : B.Aˣ) : B.A)) := by ring
      _ = 1 := by rw [h1, Units.inv_mul, one_mul]

def N (x : B.A) : ℚ := orbSum K.O B.T (B.X x) fun _ => 1

def gramDet (x : B.A) : K.E :=
  (Matrix.of fun i j => B.herm x (Module.finBasis K.E B.A i) (Module.finBasis K.E B.A j)).det

def Cl : Type :=
  Quot fun x y : {x : B.Aˣ // B.σ (x : B.A) = x} => ∃ u : B.Aˣ, (y.1 : B.A) = x.1 * (u * B.σ (u : B.A))

def Cl.rep {B : InvAlg K} (k : B.Cl) : B.A := ((Quot.out k).1 : B.Aˣ)

def stSum : ℚ := ∑ᶠ k : B.Cl, B.N k.rep

def kapSum (B₁ B₂ : InvAlg K) : ℚ :=
  ∑ᶠ k : (B₁.prod B₂).Cl, K.eta (B₁.gramDet (Cl.rep k).1) * (B₁.prod B₂).N k.rep

def Identity (B₁ B₂ : InvAlg K) : Prop :=
  (-(K.q : ℚ)) ^ (-val K.O (resultant B₁.P B₂.P)) * kapSum B₁ B₂ = B₁.stSum * B₂.stSum

end InvAlg

def UnitLemmaGroup : Prop :=
  ∀ (K : UQ), K.Odd → ∀ B₁ B₂ : InvAlg K, B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 →
    (B₁.P * B₂.P).Separable → InvAlg.Identity B₁ B₂

def UnitLemmaLie : Prop :=
  ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.σ B₁.g = B₁.g → B₂.σ B₂.g = B₂.g →
    (B₁.P * B₂.P).Separable → InvAlg.Identity B₁ B₂

end GlobalTheory.UnitLemma
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
open Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.JR

class Unram (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] : Prop where
  charZero : CharZero F
  ultraF : IsUltrametricDist F
  ultraE : IsUltrametricDist E
  lcF : LocallyCompactSpace F
  lcE : LocallyCompactSpace E
  finrank_eq : Module.finrank F E = 2
  star_fix : ∀ x : F, star (algebraMap F E x) = algebraMap F E x
  star_ne : ∃ y : E, star y ≠ y
  norm_star : ∀ y : E, ‖star y‖ = ‖y‖
  unram : ∀ y : E, ∃ x : F, ‖y‖ = ‖x‖

def eta {F : Type} [NormedField F] (x : F) : ℂ := by
  classical exact if ∃ y : F, ‖x‖ = ‖y‖ ^ 2 then 1 else -1

def IsStdChar {F : Type} [NormedField F] (ψ : AddChar F ℂ) : Prop :=
  (∀ x : F, ‖x‖ ≤ 1 → ψ x = 1) ∧ ∃ x : F, ψ x ≠ 1 ∧ ∀ y : F, ‖y‖ < 1 → ‖x * y‖ ≤ 1

def IsTest {X : Type} [TopologicalSpace X] (f : X → ℂ) : Prop := IsLocallyConstant f ∧ HasCompactSupport f

abbrev Gl (r : ℕ) (k : Type) : Type := Matrix (Fin r) (Fin r) k × (Fin r → k) × (Fin r → k) × k

abbrev Inv (r : ℕ) (k : Type) : Type := (Fin r → k) × (Fin r → k) × k

section Alg
variable {r : ℕ} {k : Type} [CommRing k]

def act (g : GL (Fin r) k) (Y : Gl r k) : Gl r k :=
  ((g : Matrix (Fin r) (Fin r) k) * Y.1 * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k),
    (g : Matrix (Fin r) (Fin r) k) *ᵥ Y.2.1,
    Y.2.2.1 ᵥ* ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k), Y.2.2.2)

def mom (Y : Gl r k) (i : ℕ) : k := Y.2.2.1 ⬝ᵥ ((Y.1 ^ i) *ᵥ Y.2.1)

def inv (Y : Gl r k) : Inv r k := (fun i => Y.1.charpoly.coeff i, fun i => mom Y i, Y.2.2.2)

def Bm (Y : Gl r k) : Matrix (Fin r) (Fin r) k := Matrix.of fun i j => ((Y.1 ^ (j : ℕ)) *ᵥ Y.2.1) i

def Cm (Y : Gl r k) : Matrix (Fin r) (Fin r) k := Matrix.of fun i j => (Y.2.2.1 ᵥ* (Y.1 ^ (i : ℕ))) j

def companion (p : Fin r → k) : Matrix (Fin r) (Fin r) k :=
  Matrix.of fun i j => if (j : ℕ) + 1 = r then - p i else if (i : ℕ) = (j : ℕ) + 1 then 1 else 0

def sec (a : Inv r k) : Gl r k := (companion a.1, fun i => if (i : ℕ) = 0 then 1 else 0, a.2.1, a.2.2)

def hankel (a : Inv r k) : Matrix (Fin r) (Fin r) k := Matrix.of fun i j => mom (sec a) ((i : ℕ) + (j : ℕ))

def Delta (a : Inv r k) : k := (hankel a).det

def full (Y : Gl r k) : Matrix (Fin (r + 1)) (Fin (r + 1)) k :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks Y.1 (Matrix.of fun i (_ : Fin 1) => Y.2.1 i) (Matrix.of fun (_ : Fin 1) j => Y.2.2.1 j)
      (Matrix.of fun _ _ => Y.2.2.2))

def lastDet (Y : Gl r k) : k :=
  (Matrix.of fun (i j : Fin (r + 1)) => (Pi.single (Fin.last r) (1 : k) ᵥ* (full Y ^ (i : ℕ))) j).det

def Inv.map {k' : Type} [CommRing k'] (φ : k →+* k') (a : Inv r k) : Inv r k' :=
  (fun i => φ (a.1 i), fun i => φ (a.2.1 i), φ a.2.2)

end Alg

abbrev Hn (r : ℕ) (F E : Type) [CommRing E] [StarRing E] : Type :=
  selfAdjoint (Matrix (Fin r) (Fin r) E) × (Fin r → E) × F

section Herm
variable {r : ℕ} {F E : Type} [CommRing F] [CommRing E] [StarRing E] [Algebra F E]

def Hn.toGl (X : Hn r F E) : Gl r E := (X.1.1, X.2.1, star X.2.1, algebraMap F E X.2.2)

def actU (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) : Hn r F E :=
  (⟨g.1 * X.1.1 * star g.1, IsSelfAdjoint.conjugate X.1.2 g.1⟩, g.1 *ᵥ X.2.1, X.2.2)

def HasInv (X : Hn r F E) (a : Inv r F) : Prop := inv X.toGl = a.map (algebraMap F E)

end Herm

section Orb
variable {r : ℕ} {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def omega (Y : Gl r F) : ℂ := eta (lastDet Y)

def glO (r : ℕ) (F : Type) [NormedField F] : Set (GL (Fin r) F) :=
  {g | ∀ i j, ‖(g : Matrix (Fin r) (Fin r) F) i j‖ ≤ 1 ∧ ‖((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j‖ ≤ 1}

def uO (r : ℕ) (E : Type) [NormedField E] [StarRing E] : Set (Matrix.unitaryGroup (Fin r) E) :=
  {g | ∀ i j, ‖g.1 i j‖ ≤ 1}

structure Meas (r : ℕ) (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [StarRing E] where
  [mG : MeasurableSpace (GL (Fin r) F)]
  [bG : BorelSpace (GL (Fin r) F)]
  [mU : MeasurableSpace (Matrix.unitaryGroup (Fin r) E)]
  [bU : BorelSpace (Matrix.unitaryGroup (Fin r) E)]
  [mF : MeasurableSpace F]
  [bF : BorelSpace F]
  [mE : MeasurableSpace E]
  [bE : BorelSpace E]
  μG : Measure (GL (Fin r) F)
  μU : Measure (Matrix.unitaryGroup (Fin r) E)
  μF : Measure F
  μE : Measure E
  haarG : μG.IsHaarMeasure
  haarU : μU.IsHaarMeasure
  haarF : μF.IsAddHaarMeasure
  haarE : μE.IsAddHaarMeasure
  volG : μG (glO r F) = 1
  volU : μU (uO r E) = 1
  volF : μF (Metric.closedBall 0 1) = 1
  volE : μE (Metric.closedBall 0 1) = 1

def orbG (M : Meas r F E) (f' : Gl r F → ℂ) (Y : Gl r F) : ℂ :=
  letI := M.mG
  ∫ g, f' (act g Y) * omega (act g Y) ∂M.μG

def orbU (M : Meas r F E) (f : Hn r F E → ℂ) (X : Hn r F E) : ℂ :=
  letI := M.mU
  ∫ g, f (actU g X) ∂M.μU

def MatchAt (M : Meas r F E) (f' : Gl r F → ℂ) (f : Hn r F E → ℂ) (a : Inv r F) : Prop :=
  (∀ X : Hn r F E, HasInv X a → orbG M f' (sec a) = orbU M f X) ∧
    ((¬ ∃ X : Hn r F E, HasInv X a) → orbG M f' (sec a) = 0)

def Match (M : Meas r F E) (f' : Gl r F → ℂ) (f : Hn r F E → ℂ) : Prop :=
  ∀ a : Inv r F, Delta a ≠ 0 → MatchAt M f' f a

def fourG (M : Meas r F E) (ψ : AddChar F ℂ) (f' : Gl r F → ℂ) (Y : Gl r F) : ℂ :=
  letI := M.mF
  ∫ b', ∫ c', f' (Y.1, b', c', Y.2.2.2) * ψ (c' ⬝ᵥ Y.2.1 + Y.2.2.1 ⬝ᵥ b')
    ∂(Measure.pi fun _ : Fin r => M.μF) ∂(Measure.pi fun _ : Fin r => M.μF)

def fourU (M : Meas r F E) (ψ : AddChar F ℂ) (f : Hn r F E → ℂ) (X : Hn r F E) : ℂ :=
  letI := M.mE
  ∫ c, f (X.1, c, X.2.2) * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1)) ∂(Measure.pi fun _ : Fin r => M.μE)

def unitG (r : ℕ) (F : Type) [NormedField F] : Gl r F → ℂ :=
  Set.indicator {Y | (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧ ‖Y.2.2.2‖ ≤ 1} 1

def unitU (r : ℕ) (F E : Type) [NormedField F] [NormedField E] [StarRing E] : Hn r F E → ℂ :=
  Set.indicator {X | (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1} 1

end Orb

def FourierMatch (r : ℕ) : Prop :=
  ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E]
    (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ →
    ∀ (f' : Gl r F → ℂ) (f : Hn r F E → ℂ), IsTest f' → IsTest f → Match M f' f →
      Match M (fourG M ψ f') (fourU M ψ f)

def UnitMatch (r : ℕ) : Prop :=
  ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E]
    (M : Meas r F E), Match M (unitG r F) (unitU r F E)

end GlobalTheory.JR
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne
namespace GlobalTheory.PsChar

variable {M A : Type*} [Monoid M] [CommRing A]

noncomputable def alt (T : M → A) : (n : ℕ) → (Fin n → M) → A
  | 0, _ => 1
  | n + 1, x => T (x 0) * alt T n (Fin.tail x) - ∑ i : Fin n, alt T n (Function.update (Fin.tail x) i (x 0 * Fin.tail x i))

structure IsPsChar (d : ℕ) (T : M → A) : Prop where
  one : T 1 = d
  comm : ∀ x y, T (x * y) = T (y * x)
  alt_eq_zero : ∀ x : Fin (d + 1) → M, alt T (d + 1) x = 0

theorem map_alt {B : Type*} [CommRing B] (f : A →+* B) (T : M → A) :
    ∀ (n : ℕ) (x : Fin n → M), f (alt T n x) = alt (fun g => f (T g)) n x
  | 0, _ => by simp [alt]
  | n + 1, x => by simp [alt, map_alt f T n]

end GlobalTheory.PsChar
end

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MapCSmulMulVec
noncomputable section

open PowerSeries

namespace GlobalTheory.NB

structure Fr (l : ℕ) (O : Type) [CommRing O] where
  prime : l.Prime
  odd : l ≠ 2
  l_nonunit : ¬ IsUnit (l : O)

  root : ∃ x : O, Associated (x ^ (l - 1)) (l : O)
  e : ℕ
  s : ℕ
  es : e * s = l - 1
  ϖ : Fin e → O
  ϖ_val : ∀ τ, Associated (ϖ τ ^ e) (l : O)
  ϖ_sub : ∀ τ τ', τ ≠ τ' → Associated (ϖ τ - ϖ τ') (ϖ τ)
  E : O⟦X⟧
  E_def : E = ∏ τ, (X - C (ϖ τ))
  φ : O⟦X⟧ →ₐ[O] O⟦X⟧
  γ : O⟦X⟧ →ₐ[O] O⟦X⟧
  comm : ∀ a, φ (γ a) = γ (φ a)
  u : (O⟦X⟧)ˣ
  φ_X : φ X = (u : O⟦X⟧) * X * E ^ s
  κ : (O⟦X⟧)ˣ
  γ_X : γ X = X * (1 + (κ : O⟦X⟧) * E)
  χ : Oˣ
  χ_gen : Associated ((χ : O) - 1) (l : O)
  χ_zero : constantCoeff (1 + (κ : O⟦X⟧) * E) = (χ : O) ^ s

  lev : Fin e → (O⟦X⟧ ≃ₐ[O] O⟦X⟧)
  lev_X : ∀ τ, lev τ X = X + C (ϖ τ)

  χ_lev : ∀ τ, ∃ w : O⟦X⟧, γ (X - C (ϖ τ)) = (X - C (ϖ τ)) * w ∧ constantCoeff (lev τ w) = (χ : O)

  lvl_red : ∀ (k : ℕ) (a : O⟦X⟧), (φ ^ k) E ∣ a ^ 2 → (φ ^ k) E ∣ a

  lvl_triv : ∀ (k : ℕ) (a : O⟦X⟧), (φ ^ k) E ∣ (γ ^ (l ^ k)) a - a

  lvl_inv : e = 1 → ∀ (k : ℕ) (a : O⟦X⟧), (φ ^ k) E ∣ γ a - a → ∃ c : O, (φ ^ k) E ∣ a - C c

  EE : Type
  [eeRing : CommRing EE]
  [eeAlgA : Algebra O⟦X⟧ EE]
  [eeAlgO : Algebra O EE]
  [eeTow : IsScalarTower O O⟦X⟧ EE]
  EE_inj : Function.Injective (algebraMap O⟦X⟧ EE)
  EE_X : IsUnit (algebraMap O⟦X⟧ EE X)
  EE_complete : IsAdicComplete (Ideal.span {(l : EE)}) EE
  EE_dense : ∀ (x : EE) (k : ℕ), ∃ (a : O⟦X⟧) (m : ℕ),
    (l : EE) ^ k ∣ x * algebraMap O⟦X⟧ EE (X ^ m) - algebraMap O⟦X⟧ EE a
  EE_sat : ∀ (a : O⟦X⟧) (k : ℕ), (l : EE) ^ k ∣ algebraMap O⟦X⟧ EE a → (l : O⟦X⟧) ^ k ∣ a
  φE : EE →ₐ[O] EE
  φE_ext : ∀ a, φE (algebraMap O⟦X⟧ EE a) = algebraMap O⟦X⟧ EE (φ a)
  γE : EE →ₐ[O] EE
  γE_ext : ∀ a, γE (algebraMap O⟦X⟧ EE a) = algebraMap O⟦X⟧ EE (γ a)

  coeffRing : ∃ (_ : IsDomain O) (_ : IsDiscreteValuationRing O),
      IsAdicComplete (IsLocalRing.maximalIdeal O) O ∧ CharZero O := by
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

attribute [instance] Fr.eeRing Fr.eeAlgA Fr.eeAlgO Fr.eeTow

open Classical

namespace Fr

variable {l : ℕ} {O : Type} [CommRing O] (R : Fr l O)

abbrev ι : O⟦X⟧ →+* R.EE := algebraMap O⟦X⟧ R.EE

def N0 (r : ℕ) : Submodule O⟦X⟧ (Fin r → R.EE) :=
  Submodule.pi Set.univ fun _ => LinearMap.range (Algebra.linearMap O⟦X⟧ R.EE)

variable [IsDomain O]

end Fr

structure Sys {l : ℕ} {O : Type} [CommRing O] (R : Fr l O) (n r : ℕ) where
  M : ℕ
  Φ : ZMod n → Matrix (Fin r) (Fin r) O⟦X⟧
  G : ZMod n → Matrix (Fin r) (Fin r) O⟦X⟧
  G_one : ∀ i, ∃ B : Matrix (Fin r) (Fin r) O⟦X⟧, G i = 1 + (X : O⟦X⟧) • B
  Φ_inv : ∀ i, ∃ (k : ℕ) (Ψ : Matrix (Fin r) (Fin r) O⟦X⟧), Φ i * Ψ = R.E ^ k • (1 : Matrix _ _ _)
  comm : ∀ i, R.E ^ M • (G i * (Φ i).map R.γ) = R.γ R.E ^ M • (Φ i * (G (i - 1)).map R.φ)

abbrev DD {l : ℕ} {O : Type} [CommRing O] (R : Fr l O) (n r : ℕ) : Type := ZMod n → Fin r → R.EE

namespace Sys

variable {l : ℕ} {O : Type} [CommRing O] {R : Fr l O} {n r : ℕ} (S : Sys R n r)

def φl (i : ZMod n) : (Fin r → R.EE) →ₗ[O] (Fin r → R.EE) :=
  ((Ring.inverse (R.ι R.E) ^ S.M • (S.Φ i).map R.ι).mulVecLin.restrictScalars O).comp
    (R.φE.toLinearMap.compLeft (Fin r))

def γl (i : ZMod n) : (Fin r → R.EE) →ₗ[O] (Fin r → R.EE) :=
  (((S.G i).map R.ι).mulVecLin.restrictScalars O).comp (R.γE.toLinearMap.compLeft (Fin r))

def φD : DD R n r →ₗ[O] DD R n r := LinearMap.pi fun i => (S.φl i).comp (LinearMap.proj (i - 1))

def γD : DD R n r →ₗ[O] DD R n r := LinearMap.pi fun i => (S.γl i).comp (LinearMap.proj i)

def Z1 : Submodule O (DD R n r × DD R n r) :=
  LinearMap.ker ((S.γD - LinearMap.id).coprod (-(S.φD - LinearMap.id)))

def B1 : Submodule O (DD R n r × DD R n r) :=
  LinearMap.range ((S.φD - LinearMap.id).prod (S.γD - LinearMap.id))

variable [IsDomain O]

end Sys

structure Hom {l : ℕ} {O : Type} [CommRing O] {R : Fr l O} {n r r' : ℕ} (S : Sys R n r)
    (S' : Sys R n r') where
  F : ZMod n → Matrix (Fin r') (Fin r) O⟦X⟧
  φ_comm : ∀ i x, ((F i).map R.ι).mulVec (S.φl i x) = S'.φl i (((F (i - 1)).map R.ι).mulVec x)
  γ_comm : ∀ i x, ((F i).map R.ι).mulVec (S.γl i x) = S'.γl i (((F i).map R.ι).mulVec x)

namespace Hom

variable {l : ℕ} {O : Type} [CommRing O] {R : Fr l O} {n r r' r'' : ℕ} {S : Sys R n r} {S' : Sys R n r'}
  {S'' : Sys R n r''} (F : Hom S S')

def comp (F' : Hom S' S'') (F : Hom S S') : Hom S S'' where
  F := fun i => F'.F i * F.F i
  φ_comm := fun i x => by
    rw [Matrix.map_mul, Matrix.map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, F.φ_comm,
      F'.φ_comm]
  γ_comm := fun i x => by
    rw [Matrix.map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, F.γ_comm, F'.γ_comm]

end Hom

end GlobalTheory.NB
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwConj
open Matrix

noncomputable section

namespace GlobalTheory.Tw

variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]

def Phi (n : ℕ) (R : Type) [CommRing R] : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if (i : ℕ) + (j : ℕ) + 1 = n then (-1) ^ (i : ℕ) else 0

def theta (g : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := Phi n R * (g⁻¹)ᴴ * (Phi n R)ᵀ

def nrm (δ : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := δ * theta δ

def twConj (x δ : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := x⁻¹ * δ * theta x

def Reg (δ : Matrix (Fin n) (Fin n) R) : Prop := IsUnit δ ∧ (nrm δ).charpoly.Separable

def cent (δ : Matrix (Fin n) (Fin n) R) : Set (Matrix (Fin n) (Fin n) R) := {g | IsUnit g ∧ g * δ = δ * theta g}

def adj (δ g : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := δ * Phi n R * gᴴ * (Phi n R)ᵀ * δ⁻¹

end GlobalTheory.Tw
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
noncomputable section

namespace GlobalTheory.PMonE

open Finset

section Basic

variable {F : Type*} [NormedField F] {m : Type*} [Fintype m]

def Integral (x : m → F) : Prop := ∀ i, ‖x i‖ ≤ 1

def gsum (q D : ℕ) (M : ℕ → Matrix m m F) (x : m → F) : m → F :=
  ∑ n ∈ range (D + 1), (M n).mulVec (fun i => x i ^ q ^ n)

variable [DecidableEq m]

structure Normal (N : ℕ) (M : ℕ → Matrix m m F) : Prop where
  int : ∀ n i j, ‖M n i j‖ ≤ 1
  top : M N = 1
  small : ∀ n, N < n → ∀ i j, ‖M n i j‖ < 1

end Basic

def GLOnto (N : ℕ) : Prop :=
  ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] [IsAlgClosed F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e D : ℕ), 0 < e → N ≤ D →
    ∀ M : ℕ → Matrix m m F, Normal N M → ∀ b : m → F, Integral b →
      ∃ x : m → F, Integral x ∧ gsum (p ^ e) D M x = b

def GLCount (N : ℕ) : Prop :=
  ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] [IsAlgClosed F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e D : ℕ), 0 < e → N ≤ D →
    ∀ M : ℕ → Matrix m m F, Normal N M → (M 0).det ≠ 0 →
      Nat.card {x : m → F // Integral x ∧ gsum (p ^ e) D M x = 0} = (p ^ e) ^ (Fintype.card m * N)

section Win

variable {F : Type*} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]

def pw (k : ℤ) (x : F) : F :=
  if 0 ≤ k then x ^ p ^ k.toNat else ((frobeniusEquiv F p).symm)^[(-k).toNat] x

def Orth {h : ℕ} (lam : Fin h → F) : Prop :=
  ∀ (c : Fin h → ℤ) (j : Fin h), ¬ (p : ℤ) ∣ c j → ‖lam j‖ ≤ ‖∑ i, (c i : F) * lam i‖

def term {h : ℕ} (ϖ : F) (lam : Fin h → F) (x : Fin h → F) (r j : Fin h) (n : ℤ) : F :=
  lam j * ϖ ^ (-n) * pw p ((r : ℤ) + n * h) (x j)

def rowT {h : ℕ} (ϖ : F) (lam : Fin h → F) (K : ℕ) (x : Fin h → F) (r : Fin h) : F :=
  ∑ j, ∑ n ∈ Icc (-(K : ℤ)) K, term p ϖ lam x r j n

end Win

def MooreNorm : Prop :=
  ∀ (F : Type) [NormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ)
    (lam : Fin h → F), Antitone (fun j => ‖lam j‖) → Orth p lam →
    ‖(Matrix.of fun r j : Fin h => lam j ^ p ^ (r : ℕ)).det‖ = ∏ j : Fin h, ‖lam j‖ ^ p ^ (h - 1 - (j : ℕ))

def WinThm : Prop :=
  ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] [IsAlgClosed F] (p : ℕ) [Fact p.Prime]
    [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F), 0 < h → ‖ϖ‖ = (p : ℝ)⁻¹ → ∀ lam : Fin h → F, (∀ j, lam j ≠ 0) →
    Antitone (fun j => ‖lam j‖) → Orth p lam → (∀ i j, ‖lam i‖ < p * ‖lam j‖) →
    ∃ (ρ τ : Fin h → ℝ) (K : ℕ), (∀ j, 0 < ρ j ∧ ρ j < 1) ∧ (∀ r, 0 < τ r) ∧
      (∀ x : Fin h → F, (∀ j, ‖x j‖ ≤ ρ j) → ∀ (r j : Fin h) (n : ℤ),
        ‖term p ϖ lam x r j n‖ ≤ τ r ∧ ((K : ℤ) < |n| → ‖term p ϖ lam x r j n‖ ≤ τ r / p)) ∧
      (∀ b : Fin h → F, (∀ r, ‖b r‖ ≤ τ r) → ∃ x : Fin h → F, (∀ j, ‖x j‖ ≤ ρ j) ∧ ∀ r, rowT p ϖ lam K x r = b r) ∧
      (∃ x : Fin h → F, (∀ j, ‖x j‖ ≤ ρ j) ∧ (∃ j, ρ j ^ p ^ h < ‖x j‖) ∧ ∀ r, rowT p ϖ lam K x r = 0)

end GlobalTheory.PMonE

end
end
