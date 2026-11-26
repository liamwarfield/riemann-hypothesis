module

public import Development.EtaleCohomology.DivisorCycles.OpenCoset

@[expose] public section

section -- merged from Development.EtaleCohomology.DivisorCycles.CycleCount
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb

def Proj : Prop := ∀ (C : Type) [Field C] (N n : ℕ) (X : Mat C N) (e : Fin n → C), Function.Injective e → Deg n X →
  (∀ i, X.charpoly.IsRoot (e i)) →
  ∃ p : Fin n → Mat C N, Sys p ∧ X = ∑ i, e i • p i ∧ ∀ i, p i ∈ Algebra.adjoin C ({X} : Set (Mat C N))

def Grade : Prop := ∀ (C : Type) [Field C] [CharZero C] (N n : ℕ) (p : Fin n → Mat C N) (e : Fin n → C)
  (g : Submodule C (Mat C N)), Sys p → IsLac e →
  (∀ Y ∈ g, (∑ i, e i • p i) * Y - Y * (∑ i, e i • p i) ∈ g) → ∀ Y ∈ g, ∀ i j, i ≠ j → p i * Y * p j ∈ g

def CycleCount : Prop := ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (N n : ℕ) (p : Fin n → Mat C N)
  (y : Mat C N) (π : Equiv.Perm (Fin n)), Sys p → IsUnit y → (∀ j, y * p j = p (π j) * y) → Deg n y → Disj y π p →
  HasEig n y ∧ ∀ i, π i = i → ∃ c : C, y * p i = c • p i

def DiagScalar : Prop := ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (N n : ℕ) (p : Fin n → Mat C N)
  (e : Fin n → C) (Y : Mat C N), Sys p → Function.Injective e → (∀ i, Y * p i = p i * Y) →
  (∀ s : C, Deg n (s • Y + ∑ i, e i • p i)) → ∀ i, ∃ c : C, Y * p i = c • p i

def AlgStruct : Prop := ∀ (C : Type) [Field C] (N n : ℕ) (p : Fin n → Mat C N) (g : Submodule C (Mat C N)), Sys p →
  (∀ Y ∈ g, ∀ Z ∈ g, Y * Z - Z * Y ∈ g) → (∀ Y ∈ g, ∀ i j, i ≠ j → p i * Y * p j ∈ g) →
  (∀ Y ∈ g, (∀ i, Y * p i = p i * Y) → ∀ i, ∃ c : C, Y * p i = c • p i) →
  ∀ a ∈ Algebra.adjoin C (g : Set (Mat C N)),
    (∀ i j, i ≠ j → p i * a * p j ∈ g) ∧ ∀ i, ∃ c : C, p i * a * p i = c • p i

def Semis : Prop := ∀ (Γ C : Type) [Group Γ] [Field C] (N : ℕ) (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)),
  IsSSMat ρ → Normd ρ A → Keeps ρ A → NoNil A

def MatrixUnits₂ : Prop := ∀ (C : Type) [Field C] (N n : ℕ) (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N),
  Sys p → Corner A p → NoNil A → ∃ E, MUnits A p E

def IdemConj : Prop := ∀ (C : Type) [Field C] [CharZero C] (N n : ℕ) (A : Subalgebra C (Mat C N))
  (p q : Fin n → Mat C N), Sys p → Corner A p → Sys q → Corner A q → NoNil A →
  ∃ v ∈ A, IsUnit v ∧ ∃ π : Equiv.Perm (Fin n), (∀ j, v * p j = q (π j) * v) ∧
    ∀ i, (∃ a ∈ A, q i * a * p i ≠ 0) → π i = i

def UnitFactorization : Prop := ∀ (C : Type) [Field C] (N n : ℕ) (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N)
  (E : Fin n → Fin n → Mat C N), Sys p → MUnits A p E → ∀ v ∈ A, IsUnit v →
  ∃ u ∈ Tv A p, ∃ d : Fin n → C, (∀ j, d j ≠ 0) ∧ v = u * ∑ j, d j • p j

def GenSpec : Prop := ∀ (C : Type) [Field C] (N n : ℕ) (p : Fin n → Mat C N) (x : Mat C N) (π : Equiv.Perm (Fin n)),
  Sys p → IsUnit x → (∀ j, x * p j = p (π j) * x) → ∃ B : Set C, B.Finite ∧ ∀ τ : Fin n → C, (∀ j, τ j ≠ 0) →
    MulLac τ B → Disj (x * ∑ j, τ j • p j) π p

def Struct : Prop := ∀ (Γ C : Type) [Group Γ] [Field C] [IsAlgClosed C] [CharZero C] (N n : ℕ)
  (ρ : Γ →* GL (Fin N) C) (X : Mat C N) (e : Fin n → C), IsSSMat ρ → (∀ g, Deg n (ρ g : Mat C N)) → X ∈ lie ρ →
  IsLac e → (∀ i, X.charpoly.IsRoot (e i)) → ∃ p, Good ρ e p

def Key : Prop := ∀ (Γ C : Type) [Group Γ] [Field C] [IsAlgClosed C] [CharZero C] (N n : ℕ)
  (ρ : Γ →* GL (Fin N) C) (e : Fin n → C) (p : Fin n → Mat C N), (∀ g, Deg n (ρ g : Mat C N)) → IsLac e → Good ρ e p →
  ∀ U : Subgroup Γ, U.Normal → U.FiniteIndex → ∀ g,
    (∃ m ∈ Zcl (img ρ U : Set (Mat C N)), HasEig n ((ρ g : Mat C N) * m)) ∧
    ∀ i, (∃ a ∈ env ρ, p i * a * (ρ g : Mat C N) * p i ≠ 0) → ∃ w ∈ env ρ, p i * (ρ g : Mat C N) = p i * w

def BigCorner : Prop := ∀ (Γ C : Type) [Group Γ] [Field C] (N n : ℕ) (ρ : Γ →* GL (Fin N) C)
  (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N), Corner A p → Normd ρ A → Keeps ρ A →
  (∀ g i, (∃ a ∈ A, p i * a * (ρ g : Mat C N) * p i ≠ 0) → ∃ w ∈ A, p i * (ρ g : Mat C N) = p i * w) →
  ∃ R : Subalgebra C (Mat C N), (∀ g, (ρ g : Mat C N) ∈ R) ∧ Corner R p ∧ Normd ρ R ∧ Keeps ρ R

def Rep : Prop := ∀ (Γ C : Type) [Group Γ] [Field C] (N n : ℕ) (ρ : Γ →* GL (Fin N) C) (R : Subalgebra C (Mat C N))
  (p : Fin n → Mat C N) (E : Fin n → Fin n → Mat C N), Sys p → MUnits R p E → (∀ g, (ρ g : Mat C N) ∈ R) →
  ∃ r A B, Sub (n := n) ρ r A B

def DenseAlg : Prop := ∀ (Γ C : Type) [Group Γ] [Field C] [CharZero C] (N n : ℕ) (ρ : Γ →* GL (Fin N) C)
  (r : Γ →* GL (Fin n) C) A B, Sub ρ r A B → ∀ (U : Subgroup Γ) (g : Γ), ∀ m ∈ Zcl (img ρ U : Set (Mat C N)),
  HasEig n ((ρ g : Mat C N) * m) → ∃ u ∈ U, (r (g * u) : Mat C n).charpoly.Separable

def DegAll : Prop := ∀ (Γ K : Type) [Group Γ] [TopologicalSpace Γ] [Field K] [TopologicalSpace K]
  [IsTopologicalRing K] [T2Space K] (N n : ℕ) (ρ : Γ →* GL (Fin N) K), Continuous (fun g => (ρ g : Mat K N)) →
  ∀ S : Set Γ, Dense S → (∀ s ∈ S, Deg n (ρ s : Mat K N)) → ∀ g, Deg n (ρ g : Mat K N)

def FinSub : Prop := ∀ (Γ K : Type) [Group Γ] [Field K] (N n : ℕ) (ρ : Γ →* GL (Fin N) K) (r : Γ →* GL (Fin n) K) A B,
  Sub ρ r A B → IsSSMat ρ → IsSSMat r ∧ A.rank = n ∧ (∀ g, (r g : Mat K n) = B * (ρ g : Mat K N) * A) ∧
  ∀ g (q : Polynomial K), Polynomial.aeval (ρ g : Mat K N) q = 0 ↔ Polynomial.aeval (r g : Mat K n) q = 0

def FinEmbed : Prop := ∀ (Γ K : Type) [Group Γ] [Field K] (N n : ℕ) (ρ : Γ →* GL (Fin N) K) (r : Γ →* GL (Fin n) K) A B,
  Sub ρ r A B → IsSSMat ρ → IsSSMat r →
  ∃ (k : ℕ) (T : Fin k → Matrix (Fin n) (Fin N) K) (T' : Fin k → Matrix (Fin N) (Fin n) K),
    (∀ j g, T j * (ρ g : Mat K N) = (r g : Mat K n) * T j) ∧ (∀ j g, (ρ g : Mat K N) * T' j = T' j * (r g : Mat K n)) ∧
    ∑ j, T' j * T j = 1

def FinDense : Prop := ∀ (Γ K : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K] (n : ℕ) (r : Γ →* GL (Fin n) K),
  Continuous (fun g => (r g : Mat K n)) →
  (∀ U : Subgroup Γ, U.Normal → U.FiniteIndex → ∀ g, ∃ u ∈ U, (r (g * u) : Mat K n).charpoly.Separable) →
  IsOpen {g | (r g : Mat K n).charpoly.Separable} ∧ Dense {g | (r g : Mat K n).charpoly.Separable}

def FinPoly : Prop := ∀ (K : Type) [Field K] [IsAlgClosed K] (n : ℕ) (x : Mat K n) (P : Polynomial K), P.Monic →
  P.natDegree = n → Polynomial.aeval x P = 0 → (x.charpoly.Separable → x.charpoly = P) ∧
  (ProdGen n P → x.det = (-1) ^ n * P.coeff 0 → x.charpoly = P)

end LateralTheory.DivDb
end

section -- merged from Development.EtaleCohomology.DivisorCycles.SpecPtPf
namespace LateralTheory.DivDb.SpecPtPf

theorem SpecPt_of : LateralTheory.DivDb.SpecPt := by
  intro C R σ _ _ _ _ _ _ x G hG hx
  classical
  let I : Ideal (MvPolynomial σ C) := RingHom.ker (MvPolynomial.aeval (R := C) x)
  have hI : I.IsPrime := RingHom.ker_isPrime _
  let P : MvPolynomial σ C := ∏ g ∈ hG.toFinset, g
  have hP : MvPolynomial.aeval x P ≠ 0 := by
    simp only [P, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun g hg => hx g (hG.mem_toFinset.mp hg)
  have hPI : P ∉ I.radical := by
    rw [hI.radical]; exact hP
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := C), MvPolynomial.mem_vanishingIdeal_iff] at hPI
  push Not at hPI
  obtain ⟨y, hy, hyP⟩ := hPI
  rw [MvPolynomial.mem_zeroLocus_iff] at hy
  refine ⟨y, fun f hf => ?_, fun g hg => ?_⟩
  · have := hy f (RingHom.mem_ker.mpr hf)
    simpa [MvPolynomial.coe_aeval_eq_eval] using this
  · simp only [P, map_prod] at hyP
    exact (Finset.prod_ne_zero_iff.mp hyP) g (hG.mem_toFinset.mpr hg)

end LateralTheory.DivDb.SpecPtPf
end

section -- merged from Development.EtaleCohomology.DivisorCycles.TangentFieldExtension
open Matrix

namespace LateralTheory.DivDb.TangentFieldExtension
open LateralTheory.DivDb

variable {C : Type} [Field C] {N : ℕ}

theorem ev_DX (Y x : Mat C N) (f : MP C N) : ev x (DX Y f) = dAt f x (Y * x) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [dAt, ev, DX, MvPolynomial.derivation_C]
  | add f g hf hg =>
    rw [map_add (f := _), ev, map_add (f := _), ← ev, ← ev, hf, hg]
    simp only [dAt, map_add (f := _), ev, add_mul, Finset.sum_add_distrib]
  | mul_X f q hf =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    simp only [ev, map_add (f := _), map_mul] at hf ⊢
    rw [hf]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [DX, MvPolynomial.mkDerivation_X, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      dAt, ev, Derivation.leibniz, smul_eq_mul, map_add, map_mul, MvPolynomial.pderiv_X, add_mul,
      Finset.sum_add_distrib, Matrix.mul_apply]
    congr 1
    · simp [Pi.single_apply, apply_ite (MvPolynomial.eval _)]
    · rw [Finset.mul_sum]; simp only [mul_assoc]

theorem TanField_of (hChain : Chain) : TanField := by
  intro C _ N S Y
  constructor
  · intro hY f hf s hs
    obtain ⟨f', hev, hd⟩ := hChain C N N (LinearMap.mulRight C s) f
    have hf' : f' ∈ Van (S : Set (Mat C N)) := fun x hx => by
      rw [hev, LinearMap.mulRight_apply]; exact hf _ (S.mul_mem hx hs)
    have h1 : dAt f' 1 Y = 0 := hY f' hf'
    rw [hd] at h1
    simp only [LinearMap.mulRight_apply, one_mul] at h1
    show ev s (DX Y f) = 0
    rw [ev_DX]; exact h1
  · intro h f hf
    have h1 : ev 1 (DX Y f) = 0 := h f hf 1 S.one_mem
    rw [ev_DX, mul_one] at h1
    exact h1

end LateralTheory.DivDb.TangentFieldExtension
end

section -- merged from Development.EtaleCohomology.DivisorCycles.SepPolyProof
open Matrix Polynomial
namespace LateralTheory.DivDb.SepPolyProof

noncomputable def disc (C : Type) [Field C] (n : ℕ) : MvPolynomial (Fin n × Fin n) C :=
  resultant (charpoly.univ C (Fin n)) (derivative (charpoly.univ C (Fin n))) n (n - 1)

theorem univ_map_ev {C : Type} [Field C] {n : ℕ} (x : Mat C n) :
    (charpoly.univ C (Fin n)).map (MvPolynomial.eval (fun p : Fin n × Fin n => x p.1 p.2)) = x.charpoly := by
  have h := charpoly.univ_map_eval₂Hom (Fin n) (RingHom.id C) (fun p : Fin n × Fin n => x p.1 p.2)
  have hx : (Matrix.of (fun p : Fin n × Fin n => x p.1 p.2).curry) = x := by ext i j; rfl
  rw [hx] at h
  exact h

theorem ev_disc {C : Type} [Field C] [CharZero C] {n : ℕ} (x : Mat C n) :
    ev x (disc C n) = resultant x.charpoly (derivative x.charpoly) := by
  unfold ev disc
  rw [← resultant_map_map, ← derivative_map, univ_map_ev]
  have h1 : x.charpoly.natDegree = n := by simpa using charpoly_natDegree_eq_dim x
  rw [natDegree_derivative, h1]

end LateralTheory.DivDb.SepPolyProof

namespace LateralTheory.DivDb
open LateralTheory.DivDb.SepPolyProof in
theorem SepPoly_of : SepPoly := by
  intro C _ _ n
  refine ⟨disc C n, fun x => ?_⟩
  rw [ev_disc, Ne, resultant_eq_zero_iff]
  have h0 : x.charpoly ≠ 0 := (charpoly_monic x).ne_zero
  simp only [ne_eq, h0, not_false_eq_true, true_or, true_and, not_not]
  rfl
end LateralTheory.DivDb
end
