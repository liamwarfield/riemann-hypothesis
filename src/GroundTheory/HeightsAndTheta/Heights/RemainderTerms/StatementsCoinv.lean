module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.CoinvReduction
public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

namespace Coinv

def IsUnderStaircase {f n : ℕ} (e : Fin f × Fin n →₀ ℕ) : Prop := ∀ v, e v ≤ (v.2 : ℕ)

def staircase (f n : ℕ) : Fin f × Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => (v.2 : ℕ)

def underStaircaseSpan (K : Type*) [Field K] (f n : ℕ) :
    Submodule K (MvPolynomial (Fin f × Fin n) K) :=
  Submodule.span K {P | ∃ e : Fin f × Fin n →₀ ℕ, IsUnderStaircase e ∧ P = monomial e 1}

def coinvTop (f n : ℕ) : ℕ := f * (n * (n - 1) / 2)

end Coinv

open Coinv

def CoinvStepReduction.Statement : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (f n : ℕ) (b : Fin f) (k : Fin n)
    (e : Fin f × Fin n →₀ ℕ), (k : ℕ) + 1 ≤ e (b, k) →
    ∃ (T : Finset (Fin f × Fin n →₀ ℕ)) (c : (Fin f × Fin n →₀ ℕ) → K),
      (∀ e' ∈ T, (∀ u : Fin f × Fin n, (u.1 < b ∨ (u.1 = b ∧ u.2 < k)) → e' u = e u) ∧
        e' (b, k) < e (b, k)) ∧
      monomial e (1 : K) - ∑ e' ∈ T, c e' • monomial e' (1 : K) ∈ psumIdeal K f n

def CoinvMonomialReduction.Statement : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (f n : ℕ) (e : Fin f × Fin n →₀ ℕ),
    ∃ v ∈ underStaircaseSpan K f n, monomial e (1 : K) - v ∈ psumIdeal K f n

def CoinvPolynomialReduction.Statement : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (f n : ℕ) (H : MvPolynomial (Fin f × Fin n) K),
    ∃ v ∈ underStaircaseSpan K f n, H - v ∈ psumIdeal K f n

def HomogeneousComponentMul.Statement : Prop :=
  ∀ (σ R : Type) [CommSemiring R] (p a : MvPolynomial σ R) (m d : ℕ), p.IsHomogeneous m →
    homogeneousComponent d (p * a) = if m ≤ d then p * homogeneousComponent (d - m) a else 0

def CoinvIdealRepresentation.Statement : Prop :=
  ∀ (K : Type) [Field K] (f n : ℕ) (J : MvPolynomial (Fin f × Fin n) K),
    J ∈ psumIdeal K f n →
    ∃ a : ℕ → Fin f → MvPolynomial (Fin f × Fin n) K,
      J = ∑ m ∈ Finset.Icc 1 n, ∑ b : Fin f, bps K f n m b * a m b

def CoinvIdealComponent.Statement : Prop :=
  ∀ (K : Type) [Field K] (f n : ℕ) (J : MvPolynomial (Fin f × Fin n) K),
    J ∈ psumIdeal K f n → ∀ d : ℕ,
    ∃ Q : ℕ → Fin f → MvPolynomial (Fin f × Fin n) K,
      (∀ m b, (Q m b).IsHomogeneous (d - m)) ∧
      homogeneousComponent d J = ∑ m ∈ Finset.Icc 1 n, ∑ b : Fin f, bps K f n m b * Q m b

def CoinvStaircaseDegree.Statement : Prop :=
  ∀ (f n : ℕ) (e : Fin f × Fin n →₀ ℕ), IsUnderStaircase e →
    e.degree ≤ coinvTop f n ∧ (e.degree = coinvTop f n → e = staircase f n)

def CoinvStaircaseComponent.Statement : Prop :=
  ∀ (K : Type) [Field K] (f n : ℕ) (v : MvPolynomial (Fin f × Fin n) K),
    v ∈ underStaircaseSpan K f n →
    (∀ d, coinvTop f n < d → homogeneousComponent d v = 0) ∧
    ∃ c : K, homogeneousComponent (coinvTop f n) v = C c * monomial (staircase f n) 1

def CoinvAboveTop.Statement : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (f n d : ℕ) (H : MvPolynomial (Fin f × Fin n) K),
    H.IsHomogeneous d → coinvTop f n < d →
    ∃ Q : ℕ → Fin f → MvPolynomial (Fin f × Fin n) K,
      (∀ m b, (Q m b).IsHomogeneous (d - m)) ∧
      H = ∑ m ∈ Finset.Icc 1 n, ∑ b : Fin f, bps K f n m b * Q m b

def CoinvAtTop.Statement : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (f n : ℕ) (H : MvPolynomial (Fin f × Fin n) K),
    H.IsHomogeneous (coinvTop f n) →
    ∃ c : K, H - C c * monomial (staircase f n) 1 ∈ psumIdeal K f n

def CoinvAboveTopGeneral.Statement : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (β ι : Type) [Fintype β] [DecidableEq β] [Fintype ι]
    [DecidableEq ι] (d : ℕ) (H : MvPolynomial (β × ι) K), H.IsHomogeneous d →
    Fintype.card β * (Fintype.card ι * (Fintype.card ι - 1) / 2) < d →
    ∃ Q : ℕ → β → MvPolynomial (β × ι) K, (∀ m b, (Q m b).IsHomogeneous (d - m)) ∧
      H = ∑ m ∈ Finset.Icc 1 (Fintype.card ι), ∑ b : β, (∑ i : ι, X (b, i) ^ m) * Q m b

def VandermondeOfHomogeneous.Statement : Prop :=
  ∀ (σ R : Type) [CommRing R] (m : ℕ) (v : Fin m → MvPolynomial σ R),
    (∀ i, (v i).IsHomogeneous 1) → (vandermondeOf v).IsHomogeneous (m * (m - 1) / 2)

def RestPolynomialHomogeneous.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock),
    (restPolynomial f r a c).IsHomogeneous (topDegree f (r + a) + 1)

def RestPolynomialHomogeneousDecomposition.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock), ∃ Q : ℕ → Fin f → RootRing f (r + a),
    IsPowerSumDecomposition f (r + a) (restPolynomial f r a c) Q ∧
    ∀ k τ, (Q k τ).IsHomogeneous (topDegree f (r + a) + 1 - k)

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Inhabitants
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

noncomputable section

open MvPolynomial

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagBasic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

namespace Flag

open MvPolynomial Finset

noncomputable section

theorem vandermondeOf_eq_det {R : Type*} [CommRing R] {m : ℕ} (v : Fin m → R) :
    vandermondeOf v = (Matrix.vandermonde (fun i => -v i)).det := by
  rw [Matrix.det_vandermonde, vandermondeOf]
  refine Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun j _ => ?_))
  ring

theorem vandermondeOf_perm {R : Type*} [CommRing R] {m : ℕ} (v : Fin m → R)
    (σ : Equiv.Perm (Fin m)) :
    vandermondeOf (fun i => v (σ i)) = (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) * vandermondeOf v := by
  rw [vandermondeOf_eq_det, vandermondeOf_eq_det]
  have : Matrix.vandermonde (fun i => -v (σ i)) =
      (Matrix.vandermonde (fun i => -v i)).submatrix σ id := by
    ext i j; rfl
  rw [this, Matrix.det_permute]

theorem blockPermute_blockPermute (f N : ℕ) (v w : Fin f → Equiv.Perm (Fin N)) (H : RootRing f N) :
    blockPermute f N v (blockPermute f N w H) = blockPermute f N (v * w) H := by
  simp only [blockPermute, rename_rename]
  rfl

theorem blockSign_mul (f N : ℕ) (v w : Fin f → Equiv.Perm (Fin N)) :
    blockSign f N (v * w) = blockSign f N v * blockSign f N w := by
  simp only [blockSign, ← Finset.prod_mul_distrib, Pi.mul_apply, Equiv.Perm.sign_mul, Units.val_mul,
    Int.cast_mul]

theorem blockSign_mul_self (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) :
    blockSign f N w * blockSign f N w = 1 := by
  simp only [blockSign, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one (fun τ _ => ?_)
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

theorem blockPermute_X (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) (τ : Fin f) (i : Fin N) :
    blockPermute f N w (X (τ, i)) = X (τ, w τ i) := by
  simp [blockPermute]

theorem blockPermute_blockVandermonde (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) :
    blockPermute f N w (blockVandermonde f N) = blockSign f N w • blockVandermonde f N := by
  simp only [blockVandermonde, map_prod]
  have h1 : ∀ τ : Fin f, blockPermute f N w (vandermondeOf fun i : Fin N => (X (τ, i) : RootRing f N)) =
      (((Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : RootRing f N) *
        vandermondeOf fun i : Fin N => (X (τ, i) : RootRing f N) := by
    intro τ
    have : blockPermute f N w (vandermondeOf fun i : Fin N => (X (τ, i) : RootRing f N)) =
        vandermondeOf fun i : Fin N => (X (τ, w τ i) : RootRing f N) := by
      simp only [vandermondeOf, map_prod, map_sub, blockPermute_X]
    rw [this]
    exact vandermondeOf_perm (fun i : Fin N => (X (τ, i) : RootRing f N)) (w τ)
  rw [Finset.prod_congr rfl (fun τ _ => h1 τ), Finset.prod_mul_distrib, Algebra.smul_def,
    blockSign, map_prod]
  simp

theorem blockVandermonde_ne_zero (f N : ℕ) : blockVandermonde f N ≠ 0 := by
  simp only [blockVandermonde, vandermondeOf]
  refine Finset.prod_ne_zero_iff.mpr (fun τ _ => Finset.prod_ne_zero_iff.mpr
    (fun i _ => Finset.prod_ne_zero_iff.mpr (fun j hj => ?_)))
  rw [sub_ne_zero]
  intro h
  have := X_injective h
  simp only [Prod.mk.injEq, true_and] at this
  rw [Finset.mem_Ioi] at hj
  exact (ne_of_lt hj) this

theorem blockPermute_antisymmetrize (f N : ℕ) (v : Fin f → Equiv.Perm (Fin N)) (H : RootRing f N) :
    blockPermute f N v (antisymmetrize f N H) = blockSign f N v • antisymmetrize f N H := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [antisymmetrize, map_sum, map_smul, blockPermute_blockPermute, Finset.smul_sum, smul_smul]
  refine Fintype.sum_equiv (Equiv.mulLeft v) _ _ (fun w => ?_)
  simp only [Equiv.coe_mulLeft]
  congr 1
  rw [blockSign_mul, ← mul_assoc, blockSign_mul_self, one_mul]

theorem card_blockPerm (f N : ℕ) : Fintype.card (Fin f → Equiv.Perm (Fin N)) = N.factorial ^ f := by
  simp [Fintype.card_perm]

end

end Flag

namespace Flag

open MvPolynomial Finset

noncomputable section

section Deriv

variable {σ ι : Type*}

end Deriv

section Indices

variable {f r a : ℕ}

end Indices

section Rest

variable (f r a : ℕ) (c : SmallBlock)

theorem flagIntegral_C_mul (f N : ℕ) (x : ℚ) (Φ : RootRing f N) :
    flagIntegral f N (C x * Φ) = x * flagIntegral f N Φ := by
  simp only [flagIntegral, coeff_C_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun _ _ => ?_)
  ring

theorem flagIntegral_add (f N : ℕ) (Φ Ψ : RootRing f N) :
    flagIntegral f N (Φ + Ψ) = flagIntegral f N Φ + flagIntegral f N Ψ := by
  simp only [flagIntegral, MvPolynomial.coeff_add, add_mul, Finset.sum_add_distrib]

theorem flagIntegral_zero (f N : ℕ) : flagIntegral f N 0 = 0 := by
  simp [flagIntegral]

end Rest

end

end Flag

open MvPolynomial

namespace Flag

open MvPolynomial Finset

end Flag

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.IsFlagIntegralOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.RestTerms

open MvPolynomial Matrix Real Finset

noncomputable section

def IsPart {r : ℕ} (la : Fin r → ℕ) : Prop := ∀ a b : Fin r, a ≤ b → la b ≤ la a

def shapeCells {r : ℕ} (la : Fin r → ℕ) : Finset (ℕ × ℕ) :=
  Finset.univ.biUnion fun a : Fin r => (Finset.range (la a)).image fun b => ((a : ℕ), b)

def numSYT {r : ℕ} (la : Fin r → ℕ) : ℕ :=
  Nat.card {T : shapeCells la ≃ Fin (shapeCells la).card // Monotone T}

def hookShape (k b : ℕ) : Fin (b + 1) → ℕ := fun a => if (a : ℕ) = 0 then k - b else 1

abbrev Roots (f j k : ℕ) : Type := MvPolynomial (Fin f × Fin (j + k)) ℝ

variable (f j k : ℕ)

def dimFl : ℕ := f * ((j + k) * (j + k - 1) / 2)

def nDim : ℕ := f * j * k

def psumAt (m : ℕ) (τ : Fin f) : Roots f j k := ∑ i, X (τ, i) ^ m

def lieClass (m : ℕ) (σ : Fin f × Bool) : Roots f j k :=
  if σ.2 then (-1) ^ m * ∑ b : Fin k, X (σ.1, Fin.natAdd j b) ^ m
  else ∑ a : Fin j, X (σ.1, Fin.castAdd k a) ^ m

def IsSmallBlock (bot : Bool) : Prop := (bot = true → k ≤ j) ∧ (bot = false → j ≤ k)

def smallPsum (bot : Bool) (m : ℕ) (τ : Fin f) : Roots f j k :=
  if bot then ∑ b : Fin k, X (τ, Fin.natAdd j b) ^ m
  else ∑ a : Fin j, (-X (τ, Fin.castAdd k a)) ^ m

def muClass (bot : Bool) : Roots f j k := ∑ τ, smallPsum f j k bot 1 τ

def fibClass (bot : Bool) : Roots f j k :=
  ∏ τ : Fin f, if bot then
      vandermonde (fun b : Fin k => (X (τ, Fin.natAdd j b) : Roots f j k)) *
        vandermonde (fun a : Fin j => (X (τ, Fin.castAdd k a) : Roots f j k))
    else
      vandermonde (fun a : Fin j => -(X (τ, Fin.castAdd k a) : Roots f j k)) *
        vandermonde (fun b : Fin k => (X (τ, Fin.natAdd j b) : Roots f j k))

def restPoly (bot : Bool) : Roots f j k := muClass f j k bot ^ (nDim f j k + 1) * fibClass f j k bot

def degPoly (bot : Bool) : Roots f j k := muClass f j k bot ^ nDim f j k * fibClass f j k bot

structure IsFlagIntegral (I : Roots f j k →ₗ[ℝ] ℝ) : Prop where
  kills : ∀ (m : ℕ) (τ : Fin f) (G : Roots f j k), 1 ≤ m → m ≤ dimFl f j k →
    G.IsHomogeneous (dimFl f j k - m) → I (psumAt f j k m τ * G) = 0
  ne_zero : ∃ G : Roots f j k, G.IsHomogeneous (dimFl f j k) ∧ I G ≠ 0

def IsPsumDecomp (F : Roots f j k) (Q : Fin f → ℕ → Roots f j k) : Prop :=
  (∀ τ m, 1 ≤ m → m ≤ j + k → (Q τ m).IsHomogeneous (dimFl f j k + 1 - m)) ∧
    F = ∑ τ : Fin f, ∑ m ∈ Finset.Icc 1 (j + k), psumAt f j k m τ * Q τ m

def blockAntisym : Roots f j k →ₗ[ℝ] Roots f j k :=
  ∑ w : Fin f → Equiv.Perm (Fin (j + k)),
    (((∏ τ, (Equiv.Perm.sign (w τ) : ℤ) : ℤ) : ℝ)) •
      (rename (Equiv.prodCongrRight w)).toLinearMap

def rhoMon : (Fin f × Fin (j + k)) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => j + k - 1 - (v.2 : ℕ)

def ddConst : Roots f j k →ₗ[ℝ] ℝ := (lcoeff ℝ (rhoMon f j k)).comp (blockAntisym f j k)

def primesOver (P : Set ℕ) (B₀ : ℝ) : Type := {p : ℕ // p ∈ P ∧ p.Prime ∧ B₀ < p}

def restTerm (I : Roots f j k →ₗ[ℝ] ℝ) (σ : ℕ → ℕ → Fin f → Fin f × Bool)
    (Q : Fin f → ℕ → Roots f j k) (p : ℕ) (τ : Fin f) (m n : ℕ) : ℝ :=
  ((p : ℝ) ^ ((n + 1) * m))⁻¹ * m * I (lieClass f j k (m - 1) (σ p (n + 1) τ) * Q τ m)

def restAt (I : Roots f j k →ₗ[ℝ] ℝ) (vol : ℝ) (σ : ℕ → ℕ → Fin f → Fin f × Bool)
    (Q : Fin f → ℕ → Roots f j k) (p : ℕ) : ℝ :=
  Real.log p * vol * ∑ τ : Fin f, ∑ m ∈ Finset.Icc 2 (j + k), ∑' n : ℕ, restTerm f j k I σ Q p τ m n

def FlagIntegralProportional.Statement : Prop :=
  ∀ f j k : ℕ, 1 ≤ f → 1 ≤ j → 1 ≤ k → ∀ I : Roots f j k →ₗ[ℝ] ℝ, IsFlagIntegral f j k I →
    ∃ c : ℝ, c ≠ 0 ∧ ∀ G : Roots f j k, G.IsHomogeneous (dimFl f j k) → I G = c * ddConst f j k G

def PrimeTail.Statement : Prop :=
  ∀ B : ℝ, 0 < B →
    Summable (fun p : {p : ℕ // p.Prime ∧ B < p} => Real.log p.1 / (p.1 : ℝ) ^ 2) ∧
      ∑' p : {p : ℕ // p.Prime ∧ B < p}, Real.log p.1 / (p.1 : ℝ) ^ 2 ≤ 2 * Real.log 4 / B

def RestBound.Statement : Prop :=
  ∀ f j k : ℕ, 1 ≤ f → 1 ≤ j → 1 ≤ k → ∀ bot : Bool, IsSmallBlock j k bot →
    ∀ I : Roots f j k →ₗ[ℝ] ℝ, IsFlagIntegral f j k I →
    ∀ vol : ℝ, 0 < vol → ∀ P : Set ℕ, (∀ p ∈ P, p.Prime) →
    ∀ B₀ : ℝ, 4 * f * ((j + k : ℕ) : ℝ) ^ 2 ≤ B₀ →
    ∀ σ : ℕ → ℕ → Fin f → Fin f × Bool,
    ∀ Q : Fin f → ℕ → Roots f j k, IsPsumDecomp f j k (restPoly f j k bot) Q →
      Summable (fun p : primesOver P B₀ => restAt f j k I vol σ Q p.1) ∧
        |∑' p : primesOver P B₀, restAt f j k I vol σ Q p.1| ≤
          1.6 * ((nDim f j k : ℝ) + 1) * vol * |I (degPoly f j k bot)|

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PowerSums
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

namespace Flag

open MvPolynomial Finset

noncomputable section

theorem injective_of_surjective_endo {R : Type*} [CommRing R] [IsNoetherianRing R]
    (φ : R →+* R) (hφ : Function.Surjective φ) : Function.Injective φ := by
  let K : ℕ →o Ideal R := ⟨fun n => RingHom.ker (φ ^ n), fun m n hmn x hx => by
    simp only [RingHom.mem_ker, RingHom.coe_pow] at hx ⊢
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [add_comm, Function.iterate_add_apply, hx, iterate_map_zero]⟩
  have hsurj : ∀ n, Function.Surjective (φ^[n]) := fun n => hφ.iterate n
  obtain ⟨n, hn⟩ := (monotone_stabilizes_iff_noetherian (R := R) (M := R)).mpr
    (isNoetherianRing_iff.mp inferInstance) K
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hsurj n x
  have hy : y ∈ K (n + 1) := by
    show (φ ^ (n + 1)) y = 0
    rw [RingHom.coe_pow, Function.iterate_succ_apply', hx]
  rw [← hn (n + 1) (Nat.le_succ n)] at hy
  have h' : (φ ^ n) y = 0 := hy
  simpa [RingHom.coe_pow] using h'

theorem psum_mem_range (N j : ℕ) (hj1 : 1 ≤ j) (hjN : j ≤ N) :
    psum (Fin N) ℚ j ∈ (powerSumHom N).range := by
  refine ⟨X ⟨j - 1, by omega⟩, ?_⟩
  change powerSumHom N (X ⟨j - 1, by omega⟩) = _
  simp only [powerSumHom, aeval_X]
  congr 1
  show j - 1 + 1 = j
  omega

theorem esymm_mem_range (N k : ℕ) (hk : k ≤ N) :
    esymm (Fin N) ℚ k ∈ (powerSumHom N).range := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [esymm_zero]; exact Subalgebra.one_mem _
    have hN := mul_esymm_eq_sum (Fin N) ℚ k
    have hmem : (k : MvPolynomial (Fin N) ℚ) * esymm (Fin N) ℚ k ∈ (powerSumHom N).range := by
      rw [hN]
      refine Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _) ?_
      refine Subalgebra.sum_mem _ (fun a ha => ?_)
      obtain ⟨ha1', ha2⟩ := Finset.mem_filter.mp ha
      have ha1 := Finset.HasAntidiagonal.mem_antidiagonal.mp ha1'
      refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _
        (Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _)
        (ih a.1 ha2 (by omega))) (psum_mem_range N a.2 (by omega) (by omega))
    have hinv : esymm (Fin N) ℚ k = C ((k : ℚ)⁻¹) * ((k : MvPolynomial (Fin N) ℚ) * esymm (Fin N) ℚ k) := by
      rw [← mul_assoc, show (k : MvPolynomial (Fin N) ℚ) = C (k : ℚ) by simp, ← C_mul,
        inv_mul_cancel₀ (by exact_mod_cast hk0.ne'), C_1, one_mul]
    rw [hinv]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hmem

theorem exists_powerSumHom_eq {N : ℕ} {P : MvPolynomial (Fin N) ℚ} (hP : P.IsSymmetric) :
    ∃ S, powerSumHom N S = P := by
  obtain ⟨Q, hQ⟩ := esymmAlgHom_fin_surjective ℚ (le_refl N) ⟨P, hP⟩
  have h1 : P = aeval (fun i : Fin N => esymm (Fin N) ℚ (i + 1)) Q := by
    rw [← esymmAlgHom_apply, hQ]
  have h2 : aeval (fun i : Fin N => esymm (Fin N) ℚ (i + 1)) Q ∈ (powerSumHom N).range := by
    have hsub : Algebra.adjoin ℚ (Set.range fun i : Fin N => esymm (Fin N) ℚ (i + 1)) ≤
        (powerSumHom N).range := by
      rw [Algebra.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      exact esymm_mem_range N _ (by omega)
    exact hsub (by rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨Q, rfl⟩)
  rw [h1]
  exact h2

theorem powerSumHom_isSymmetric (N : ℕ) (S : MvPolynomial (Fin N) ℚ) :
    (powerSumHom N S).IsSymmetric := by
  have : powerSumHom N S ∈ symmetricSubalgebra (Fin N) ℚ := by
    have hsub : (powerSumHom N).range ≤ symmetricSubalgebra (Fin N) ℚ := by
      rintro _ ⟨T, rfl⟩
      simp only [powerSumHom]
      have : Algebra.adjoin ℚ (Set.range fun i : Fin N => psum (Fin N) ℚ (i.val + 1)) ≤
          symmetricSubalgebra (Fin N) ℚ := by
        rw [Algebra.adjoin_le_iff]
        rintro _ ⟨i, rfl⟩
        exact psum_isSymmetric (Fin N) ℚ _
      exact this (by rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨T, rfl⟩)
    exact hsub ⟨S, rfl⟩
  exact this

theorem powerSumHom_injective (N : ℕ) : Function.Injective (powerSumHom N) := by

  let e := esymmAlgEquiv (Fin N) ℚ (n := N) (by simp)
  let π : MvPolynomial (Fin N) ℚ →ₐ[ℚ] symmetricSubalgebra (Fin N) ℚ :=
    (powerSumHom N).codRestrict _ (fun S => powerSumHom_isSymmetric N S)
  let φ : MvPolynomial (Fin N) ℚ →ₐ[ℚ] MvPolynomial (Fin N) ℚ := e.symm.toAlgHom.comp π
  have hsurj : Function.Surjective φ := by
    intro T
    obtain ⟨S, hS⟩ := exists_powerSumHom_eq (e T).2
    refine ⟨S, ?_⟩
    apply e.injective
    simp only [φ, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
    exact Subtype.ext hS
  have hinj : Function.Injective φ := injective_of_surjective_endo φ.toRingHom hsurj
  intro S T hST
  apply hinj
  simp only [φ, AlgHom.comp_apply]
  congr 1
  exact Subtype.ext hST

theorem constantCoeff_powerSumHom (N : ℕ) (S : MvPolynomial (Fin N) ℚ) :
    constantCoeff (powerSumHom N S) = constantCoeff S := by
  induction S using MvPolynomial.induction_on with
  | C a => simp [powerSumHom]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, powerSumHom, aeval_X, constantCoeff_X, mul_zero]
    simp [psum, constantCoeff_X]

end

end Flag

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Elementary
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open Finset

noncomputable section

theorem XBound.intersectionNumber_baseChange : XBound.Statement := by
  intro r a hN
  have hN' : (2 : ℝ) ≤ ((r + a : ℕ) : ℝ) := by exact_mod_cast hN
  refine ⟨?_, ?_⟩
  · simp only [restX]
    push_cast
    push_cast at hN'
    nlinarith [sq_nonneg ((r : ℝ) - a)]
  · nlinarith

theorem XOverPrime.intersectionNumber_baseChange : XOverPrime.Statement := by
  intro f r a B₀ p hf hN hB hp
  have hN' : (2 : ℝ) ≤ ((r + a : ℕ) : ℝ) := by exact_mod_cast hN
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hX := (XBound.intersectionNumber_baseChange r a hN)
  have hX2 : (restX r a : ℝ) ≤ 3 / 2 * ((r + a : ℕ) : ℝ) ^ 2 := hX.1.trans hX.2
  have hN2 : 0 < ((r + a : ℕ) : ℝ) ^ 2 := by positivity
  have hp4 : 4 * ((r + a : ℕ) : ℝ) ^ 2 < p := by nlinarith
  have hp0 : 0 < p := lt_trans (by positivity) hp4
  rw [div_le_iff₀ hp0]
  nlinarith

theorem two_log_four_le : 2 * Real.log 4 ≤ 2.78 := by
  have := Real.log_two_lt_d9
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  nlinarith

theorem RestConstants.intersectionNumber_baseChange : RestConstants.Statement := by
  refine ⟨two_log_four_le, ?_⟩
  intro f N hf hN
  have hf' : (0 : ℝ) < f := by exact_mod_cast hf
  have hN' : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
  have : (1.5 : ℝ) * f * (3 / 2 * (N : ℝ) ^ 2) * (2.78 / (4 * f * (N : ℝ) ^ 2)) =
      1.5 * (3 / 2) * 2.78 / 4 := by
    field_simp
  rw [this]
  norm_num

theorem GeometricTail.intersectionNumber_baseChange : GeometricTail.Statement := by
  intro p k hp hk
  set x : ℝ := (p ^ k)⁻¹ with hx
  have hpk : (2 : ℝ) ≤ p ^ k := by
    calc (2 : ℝ) ≤ p := hp
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ k := pow_le_pow_right₀ (by linarith) hk
  have hx0 : 0 ≤ x := by positivity
  have hx2 : x ≤ 1 / 2 := by
    rw [hx]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    linarith
  have hterm : ∀ n : ℕ, (p ^ ((n + 1) * k))⁻¹ = x * x ^ n := by
    intro n
    rw [hx, ← pow_succ', inv_pow, ← pow_mul, mul_comm k]
  have hs : Summable (fun n : ℕ => x ^ n) :=
    summable_geometric_of_lt_one hx0 (by linarith)
  refine ⟨?_, ?_⟩
  · simp_rw [hterm]
    exact hs.mul_left x
  · simp_rw [hterm]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hx0 (by linarith)]
    have h1 : (1 - x)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    calc x * (1 - x)⁻¹ ≤ x * 2 := mul_le_mul_of_nonneg_left h1 hx0
      _ = 2 * x := by ring

theorem exp_three_eighths_le : Real.exp (3 / 8) ≤ 1.5 := by
  have he := Real.exp_one_lt_d9
  have h8 : Real.exp (3 / 8) ^ 8 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    norm_num
  by_contra hlt
  push Not at hlt
  have h1 : (1.5 : ℝ) ^ 8 < Real.exp (3 / 8) ^ 8 :=
    pow_lt_pow_left₀ hlt (by norm_num) (by norm_num)
  have h2 : Real.exp 1 ^ 3 < (2.7182818286 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ he (Real.exp_pos 1).le (by norm_num)
  rw [h8] at h1
  norm_num at h1 h2
  linarith

theorem ExponentialTail.intersectionNumber_baseChange : ExponentialTail.Statement := by
  intro p X hp hX hXp
  set u : ℝ := X / p with hu
  have hu0 : 0 ≤ u := by positivity
  have hu38 : u ≤ 3 / 8 := by rw [hu, div_le_iff₀ hp]; linarith
  have hA : 0 ≤ X / p ^ 2 := by positivity
  have hterm : ∀ k : ℕ, 2 * (p ^ (k + 2))⁻¹ * X ^ (k + 1) / ((k + 2).factorial : ℝ) =
      X / p ^ 2 * (u ^ k * (2 / ((k + 2).factorial : ℝ))) := by
    intro k
    rw [hu, div_pow]
    field_simp
    ring
  have hfac : ∀ k : ℕ, 2 / ((k + 2).factorial : ℝ) ≤ 1 / (k.factorial : ℝ) := by
    intro k
    have h1 : (2 : ℝ) * k.factorial ≤ (k + 2).factorial := by
      have : 2 * k.factorial ≤ (k + 2).factorial := by
        rw [Nat.factorial_succ, Nat.factorial_succ]
        exact Nat.mul_le_mul (by omega) (Nat.le_mul_of_pos_left _ (by omega))
      exact_mod_cast this
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hbound : ∀ k : ℕ, 2 * (p ^ (k + 2))⁻¹ * X ^ (k + 1) / ((k + 2).factorial : ℝ) ≤
      X / p ^ 2 * (u ^ k / (k.factorial : ℝ)) := by
    intro k
    rw [hterm]
    apply mul_le_mul_of_nonneg_left _ hA
    rw [div_eq_mul_one_div (u ^ k)]
    exact mul_le_mul_of_nonneg_left (hfac k) (by positivity)
  have hnn : ∀ k : ℕ, 0 ≤ 2 * (p ^ (k + 2))⁻¹ * X ^ (k + 1) / ((k + 2).factorial : ℝ) := by
    intro k; positivity
  have hexp : Summable (fun k : ℕ => u ^ k / (k.factorial : ℝ)) := Real.summable_pow_div_factorial u
  have hsum : Summable (fun k : ℕ => X / p ^ 2 * (u ^ k / (k.factorial : ℝ))) := hexp.mul_left _
  have hS : Summable (fun k : ℕ => 2 * (p ^ (k + 2))⁻¹ * X ^ (k + 1) / ((k + 2).factorial : ℝ)) :=
    Summable.of_nonneg_of_le hnn hbound hsum
  refine ⟨hS, ?_, ?_⟩
  · calc ∑' k : ℕ, 2 * (p ^ (k + 2))⁻¹ * X ^ (k + 1) / ((k + 2).factorial : ℝ)
        ≤ ∑' k : ℕ, X / p ^ 2 * (u ^ k / (k.factorial : ℝ)) := hS.tsum_le_tsum hbound hsum
      _ = X / p ^ 2 * Real.exp u := by
        rw [tsum_mul_left, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
      _ ≤ X / p ^ 2 * Real.exp (3 / 8) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hu38) hA
      _ = Real.exp (3 / 8) * X / p ^ 2 := by ring
  · have := exp_three_eighths_le
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right this hA

theorem ChebyshevThetaBound.intersectionNumber_baseChange : ChebyshevThetaBound.Statement := by
  intro x hx
  set n := ⌊x⌋₊
  have hprod : ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p =
      Real.log (primorial n) := by
    rw [primorial, Nat.cast_prod, Real.log_prod]
    intro p hp
    have := (Finset.mem_filter.mp hp).2.pos
    exact_mod_cast this.ne'
  rw [hprod]
  have hpos : (0 : ℝ) < primorial n := by exact_mod_cast primorial_pos n
  calc Real.log (primorial n) ≤ Real.log ((4 : ℝ) ^ n) := by
        apply Real.log_le_log hpos
        exact_mod_cast primorial_le_four_pow n
    _ = n * Real.log 4 := by rw [Real.log_pow]
    _ ≤ x * Real.log 4 := by
        apply mul_le_mul_of_nonneg_right (Nat.floor_le hx)
        exact Real.log_nonneg (by norm_num)

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsElem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open Finset

noncomputable section

def RestInnerTsumBound.Statement : Prop :=
  ∀ (p : ℝ) (k : ℕ) (c : ℕ → ℝ) (M : ℝ), 2 ≤ p → 1 ≤ k → (∀ n, |c n| ≤ M) →
    Summable (fun n : ℕ => (p ^ ((n + 1) * k))⁻¹ * c n) ∧
      |∑' n : ℕ, (p ^ ((n + 1) * k))⁻¹ * c n| ≤ M * (2 * (p ^ k)⁻¹)

def RestKSumBound.Statement : Prop :=
  ∀ (p X : ℝ) (N : ℕ), 0 < p → 0 ≤ X → X ≤ 3 / 8 * p →
    ∑ k ∈ Finset.Icc 2 N, 2 * (p ^ k)⁻¹ * X ^ (k - 1) / (k.factorial : ℝ) ≤ 1.5 * X / p ^ 2

def RestPrimeBoundOfFactor.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock) (B₀ : ℝ), 1 ≤ f → 1 ≤ r → 1 ≤ a →
    4 * (f : ℝ) * ((r + a : ℕ) : ℝ) ^ 2 ≤ B₀ →
    ∀ Q : ℕ → Fin f → RootRing f (r + a),
      (∀ k : ℕ, 2 ≤ k → k ≤ r + a → ∀ τ τ' : Fin f,
        |restTerm f (r + a) Q k τ (smallPowerSum f r a c (k - 1) τ')| ≤
          ((f * (r * a) + 1 : ℕ) : ℚ) * |fibreDegree f r a c| * restX r a ^ (k - 1) /
            (k.factorial : ℚ)) →
    ∀ (s : ℕ → ℕ → Fin f → Fin f) (e : ℕ → ℕ → Fin f → ℕ → ℚ),
      (∀ p n τ k, e p n τ k = 1 ∨ e p n τ k = -1) →
    ∀ p : ℕ, p.Prime → B₀ < p →
      |restPrimeModel f r a c Q s e p| ≤
        1.5 * f * (restX r a : ℝ) * (Real.log p / (p : ℝ) ^ 2) *
          ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)|

def RestBoundOfPrimeBound.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock) (B₀ : ℝ), 1 ≤ f → 1 ≤ r → 1 ≤ a →
    4 * (f : ℝ) * ((r + a : ℕ) : ℝ) ^ 2 ≤ B₀ →
    ∀ (Q : ℕ → Fin f → RootRing f (r + a)) (s : ℕ → ℕ → Fin f → Fin f)
      (e : ℕ → ℕ → Fin f → ℕ → ℚ),
    (∀ p : ℕ, p.Prime → B₀ < p →
      |restPrimeModel f r a c Q s e p| ≤
        1.5 * f * (restX r a : ℝ) * (Real.log p / (p : ℝ) ^ 2) *
          ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)|) →
    ∀ P : Set ℕ,
      Summable (fun p : {p : ℕ // p ∈ P ∧ p.Prime ∧ B₀ < p} =>
        |restPrimeModel f r a c Q s e p|) ∧
      |∑' p : {p : ℕ // p ∈ P ∧ p.Prime ∧ B₀ < p}, restPrimeModel f r a c Q s e p| ≤
        1.6 * ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)|

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsTop
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

def OtherFactorFormula.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock), 2 ≤ f → 1 ≤ r → 1 ≤ a →
    ∃ C₀ : ℚ, C₀ ≠ 0 ∧
      fibreDegree f r a c =
        C₀ * (f * (r * a)).factorial / ((r * a).factorial : ℚ) ^ f *
          (numStandardTable (rectangle r a) : ℚ) ^ f ∧
      ∀ Q : ℕ → Fin f → RootRing f (r + a),
        IsPowerSumDecomposition f (r + a) (restPolynomial f r a c) Q →
        ∀ (k : ℕ) (hk2 : 2 ≤ k) (hkN : k ≤ r + a) (τ τ' : Fin f), τ' ≠ τ →
          ∃ S : MvPolynomial (Fin (r + a)) ℚ,
            powerSumHom (r + a) S =
              ∑ nu ∈ partitionsOf r k,
                C ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) *
                  aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu) ∧
            restTerm f (r + a) Q k τ (smallPowerSum f r a c (k - 1) τ') =
              C₀ * k * (f * (r * a) + 1).factorial /
                  (((r * a + k).factorial : ℚ) * ((r * a - (k - 1)).factorial : ℚ) *
                    ((r * a).factorial : ℚ) ^ (f - 2)) *
                (numStandardTable (rectangle r a) : ℚ) ^ (f - 2) *
                symmetricGroupCharacter (rectangle r a)
                  ((k - 1) :: List.replicate (r * a - (k - 1)) 1) *
                AddMonoidAlgebra.coeff S (Finsupp.single (⟨k - 1, by omega⟩ : Fin (r + a)) 1)

def SchurSignCoefficient.Statement : Prop :=
  ∀ (N r k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) (nu : Fin r → ℕ) (s : ℚ), (s = 1 ∨ s = -1) →
    Antitone nu → ∑ i, nu i = k →
    ∃ S : MvPolynomial (Fin N) ℚ,
      powerSumHom N S = aeval (fun i : Fin N => C s * X i) (schur (Fin N) nu) ∧
      AddMonoidAlgebra.coeff S (Finsupp.single (⟨k - 1, by omega⟩ : Fin N) 1) =
        s ^ k * if ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1 then
          (-1 : ℚ) ^ ((Finset.univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ nu i = 1).card) / k
        else 0

def HookTableauCount.Statement : Prop :=
  ∀ r k l : ℕ, l < k → l < r → numStandardTable (hookShape r k l) = Nat.choose (k - 1) l

def RectangleTablePos.Statement : Prop :=
  ∀ r a : ℕ, 0 < numStandardTable (rectangle r a)

def HookSumBound.Statement : Prop :=
  ∀ (r a k : ℕ) (b : (Fin r → ℕ) → ℚ), 1 ≤ k →
    (∀ nu ∈ partitionsOf r k, |b nu| ≤ numStandardTable (fun i => a + nu i)) →
    ∑ nu ∈ (partitionsOf r k).filter (fun nu => ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1), |b nu| ≤
      (Nat.choose (r * a + k) k : ℚ) * 2 ^ (k - 1) * numStandardTable (rectangle r a)

end

end RestTerms

end GroundTheory.Heights₂.Heights
end
