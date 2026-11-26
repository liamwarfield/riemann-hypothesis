module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.JacobiTrudi
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.AltCoeff

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

def IsBlockAlternating (f N : ℕ) (P : RootRing f N) : Prop :=
  ∀ w : Fin f → Equiv.Perm (Fin N), blockPermute f N w P = blockSign f N w • P

def IsBlockSymmetric (f N : ℕ) (P : RootRing f N) : Prop :=
  ∀ w : Fin f → Equiv.Perm (Fin N), blockPermute f N w P = P

theorem isBlockAlternating_blockVandermonde (f N : ℕ) :
    IsBlockAlternating f N (blockVandermonde f N) :=
  fun w => Flag.blockPermute_blockVandermonde f N w

theorem isBlockAlternating_antisymmetrize (f N : ℕ) (H : RootRing f N) :
    IsBlockAlternating f N (antisymmetrize f N H) :=
  fun w => Flag.blockPermute_antisymmetrize f N w H

def FlagCoeffBlockPermute.Statement : Prop :=
  ∀ (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) (P : RootRing f N) (α : Fin f × Fin N →₀ ℕ),
    AddMonoidAlgebra.coeff (blockPermute f N w P) α =
      AddMonoidAlgebra.coeff P (Finsupp.equivFunOnFinite.symm fun p : Fin f × Fin N => α (p.1, w p.1 p.2))

def FlagAltCoeffInjective.Statement : Prop :=
  ∀ (f N : ℕ) (P : RootRing f N) (α : Fin f × Fin N →₀ ℕ),
    IsBlockAlternating f N P → AddMonoidAlgebra.coeff P α ≠ 0 → ∀ τ : Fin f, Function.Injective fun i : Fin N => α (τ, i)

def FlagInjSumBound.Statement : Prop :=
  ∀ (N : ℕ) (g : Fin N → ℕ), Function.Injective g →
    N * (N - 1) / 2 ≤ ∑ i, g i ∧ (∑ i, g i = N * (N - 1) / 2 → ∀ i, g i < N)

def FlagStaircaseOrbit.Statement : Prop :=
  ∀ (f N : ℕ) (α β : Fin f × Fin N →₀ ℕ), (∀ τ i, α (τ, i) < N) → (∀ τ i, β (τ, i) < N) →
    (∀ τ, Function.Injective fun i : Fin N => α (τ, i)) →
    (∀ τ, Function.Injective fun i : Fin N => β (τ, i)) →
    ∃ w : Fin f → Equiv.Perm (Fin N), ∀ τ i, α (τ, w τ i) = β (τ, i)

def FlagVandermondeHomogeneous.Statement : Prop :=
  ∀ f N : ℕ, (blockVandermonde f N).IsHomogeneous (topDegree f N)

def FlagAltTopDegree.Statement : Prop :=
  ∀ (f N : ℕ) (P : RootRing f N), IsBlockAlternating f N P → P.IsHomogeneous (topDegree f N) →
    ∃ e : ℚ, P = C e * blockVandermonde f N

def FlagIntegralPermute.Statement : Prop :=
  ∀ (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) (H : RootRing f N),
    flagIntegral f N (blockPermute f N w H) = blockSign f N w * flagIntegral f N H

def FlagIntegralAntisymmetrize.Statement : Prop :=
  ∀ (f N : ℕ) (H : RootRing f N),
    flagIntegral f N (antisymmetrize f N H) = (N.factorial : ℚ) ^ f * flagIntegral f N H

def FlagIntegralVandermondePos.Statement : Prop :=
  ∀ f N : ℕ, 0 < flagIntegral f N (blockVandermonde f N)

def FlagAntisymHomogeneous.Statement : Prop :=
  ∀ (f N : ℕ) (H : RootRing f N) (d : ℕ), H.IsHomogeneous d → (antisymmetrize f N H).IsHomogeneous d

def FlagHomogeneousComponentMul.Statement : Prop :=
  ∀ (σ : Type) (P G : MvPolynomial σ ℚ) (k n : ℕ), P.IsHomogeneous k →
    homogeneousComponent n (P * G) = if k ≤ n then P * homogeneousComponent (n - k) G else 0

def FlagIntegralTopComponent.Statement : Prop :=
  ∀ (f N : ℕ) (Φ : RootRing f N),
    flagIntegral f N Φ = flagIntegral f N (homogeneousComponent (topDegree f N) Φ)

def FlagIntegralVandermondeMul.Statement : Prop :=
  ∀ (f N : ℕ) (R : RootRing f N),
    flagIntegral f N (blockVandermonde f N * R) = constantCoeff R * flagIntegral f N (blockVandermonde f N)

def FlagIntegralViaQuotient.Statement : Prop :=
  ∀ (f N : ℕ) (H R : RootRing f N), antisymmetrize f N H = blockVandermonde f N * R →
    flagIntegral f N H =
      flagIntegral f N (blockVandermonde f N) / (N.factorial : ℚ) ^ f * constantCoeff R

def FlagIntegralTopDegree.Statement : Prop :=
  ∀ (f N : ℕ) (H : RootRing f N), H.IsHomogeneous (topDegree f N) →
    algebraMap ℚ (FractionRing (RootRing f N)) (flagIntegral f N H) =
      algebraMap ℚ (FractionRing (RootRing f N))
          (flagIntegral f N (blockVandermonde f N) / (N.factorial : ℚ) ^ f) *
        dividedDifference f N H

def FlagSymmetricMulAntisym.Statement : Prop :=
  ∀ (f N : ℕ) (P H : RootRing f N), IsBlockSymmetric f N P →
    antisymmetrize f N (P * H) = P * antisymmetrize f N H

def FlagPowerSumSymmetric.Statement : Prop :=
  ∀ (f N k : ℕ) (τ : Fin f), IsBlockSymmetric f N (blockPowerSum f N k τ)

def FlagSwapDivisible.Statement : Prop :=
  ∀ (σ : Type) [DecidableEq σ] (P : MvPolynomial σ ℚ) (a b : σ), a ≠ b →
    rename (Equiv.swap a b) P = -P → (X a - X b : MvPolynomial σ ℚ) ∣ P

def FlagDiffPrime.Statement : Prop :=
  ∀ (σ : Type) [DecidableEq σ] (a b : σ), a ≠ b → Prime (X a - X b : MvPolynomial σ ℚ)

def FlagDiffNotDvd.Statement : Prop :=
  ∀ (σ : Type) [DecidableEq σ] (a b c d : σ), a ≠ b → c ≠ d → ¬ (a = c ∧ b = d) →
    ¬ (a = d ∧ b = c) → ¬ (X a - X b : MvPolynomial σ ℚ) ∣ (X c - X d)

def FlagProdPrimesDvd.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (ι : Type) (s : Finset ι) (p : ι → R) (x : R),
    (∀ i ∈ s, Prime (p i)) → (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ p i ∣ p j) → (∀ i ∈ s, p i ∣ x) →
      (∏ i ∈ s, p i) ∣ x

def FlagVandermondeDvd.Statement : Prop :=
  ∀ (f N : ℕ) (P : RootRing f N), IsBlockAlternating f N P → blockVandermonde f N ∣ P

def FlagDividedDifferencePoly.Statement : Prop :=
  ∀ (f N : ℕ) (H : RootRing f N), ∃ R : RootRing f N,
    antisymmetrize f N H = blockVandermonde f N * R ∧ IsBlockSymmetric f N R

def FlagQuotientHomogeneous.Statement : Prop :=
  ∀ (σ : Type) (A R : MvPolynomial σ ℚ) (m k : ℕ), A ≠ 0 → A.IsHomogeneous m →
    (A * R).IsHomogeneous (m + k) → R.IsHomogeneous k

def FlagRestrictSymmetric.Statement : Prop :=
  ∀ (f N : ℕ) (τ : Fin f) (R : RootRing f N), IsBlockSymmetric f N R →
    (restrictToBlock f N τ R).IsSymmetric

def FlagRestrictPowerSum.Statement : Prop :=
  ∀ (f N k : ℕ) (τ σ : Fin f), 1 ≤ k →
    restrictToBlock f N τ (blockPowerSum f N k σ) = if σ = τ then psum (Fin N) ℚ k else 0

def FlagRestrictConstantCoeff.Statement : Prop :=
  ∀ (f N : ℕ) (τ : Fin f) (R : RootRing f N),
    constantCoeff (restrictToBlock f N τ R) = constantCoeff R

def FlagRestrictHomogeneous.Statement : Prop :=
  ∀ (f N : ℕ) (τ : Fin f) (R : RootRing f N) (k : ℕ), R.IsHomogeneous k →
    (restrictToBlock f N τ R).IsHomogeneous k

def FlagRestrictDecomposition.Statement : Prop :=
  ∀ (f N : ℕ) (τ : Fin f) (R : ℕ → Fin f → RootRing f N),
    restrictToBlock f N τ (∑ l ∈ Finset.Icc 1 N, ∑ σ : Fin f, blockPowerSum f N l σ * R l σ) =
      ∑ l ∈ Finset.Icc 1 N, psum (Fin N) ℚ l * restrictToBlock f N τ (R l τ)

def FlagPowerSumPreimage.Statement : Prop :=
  ∀ (N : ℕ) (T : ℕ → MvPolynomial (Fin N) ℚ), (∀ l, (T l).IsSymmetric) →
    ∃ S : MvPolynomial (Fin N) ℚ,
      powerSumHom N S = ∑ l ∈ Finset.Icc 1 N, psum (Fin N) ℚ l * T l ∧
      ∀ (k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N),
        AddMonoidAlgebra.coeff S (Finsupp.single (⟨k - 1, by omega⟩ : Fin N) 1) = constantCoeff (T k)

def FlagAntisymDecomposition.Statement : Prop :=
  ∀ (f N : ℕ) (F G : RootRing f N) (Q R : ℕ → Fin f → RootRing f N),
    IsPowerSumDecomposition f N F Q →
    (∀ l σ, antisymmetrize f N (G * Q l σ) = blockVandermonde f N * R l σ) →
    antisymmetrize f N (G * F) =
      blockVandermonde f N * ∑ l ∈ Finset.Icc 1 N, ∑ σ : Fin f, blockPowerSum f N l σ * R l σ

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

def SchStrictAntiSplit.Statement : Prop :=
  ∀ (r n : ℕ) (d : Fin r → ℕ), StrictAnti d → ∑ i, d i = r * (r - 1) / 2 + n →
    (∀ i : Fin r, r - 1 - (i : ℕ) ≤ d i) ∧
      (fun i : Fin r => d i - (r - 1 - (i : ℕ))) ∈ partitionsOf r n

def SchAltPartitionExpansion.Statement : Prop :=
  ∀ (r n : ℕ) (P : MvPolynomial (Fin r) ℚ), Comb.IsAlt P →
    P.IsHomogeneous (r * (r - 1) / 2 + n) →
    P = ∑ lam ∈ partitionsOf r n,
      C (AddMonoidAlgebra.coeff P (Finsupp.equivFunOnFinite.symm fun i : Fin r => lam i + (r - 1 - (i : ℕ)))) *
        (vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ)) * schur (Fin r) lam)

def rootOfUnity (k : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / k)

def rootOfUnityPoint (N k : ℕ) : Fin N → ℂ :=
  fun i => if (i : ℕ) < k then rootOfUnity k ^ (i : ℕ) else 0

def rootOfUnityJTMatrix (k : ℕ) {r : ℕ} (nu : Fin r → ℕ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i j =>
    if 0 ≤ (nu i : ℤ) - ((i : ℕ) : ℤ) + ((j : ℕ) : ℤ) ∧
        (k : ℤ) ∣ (nu i : ℤ) - ((i : ℕ) : ℤ) + ((j : ℕ) : ℤ) then 1 else 0

def SchProdOneSubRootsOfUnity.Statement : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ∏ i ∈ range k, (1 - Polynomial.C (rootOfUnity k ^ i) * Polynomial.X) =
      (1 - Polynomial.X ^ k : Polynomial ℂ)

def SchCompleteGenerating.Statement : Prop :=
  ∀ (N : ℕ) (y : Fin N → ℂ) (d : ℕ),
    ∑ c ∈ range (d + 1), (∏ i : Fin N, (1 - Polynomial.C (y i) * Polynomial.X)).coeff c *
      aeval y (hsymm (Fin N) ℚ (d - c)) = if d = 0 then 1 else 0

def SchCompleteAtRootsOfUnity.Statement : Prop :=
  ∀ N k d : ℕ, 1 ≤ k → k ≤ N →
    aeval (rootOfUnityPoint N k) (hsymm (Fin N) ℚ d) = if k ∣ d then 1 else 0

def SchPowerSumAtRootsOfUnity.Statement : Prop :=
  ∀ N k j : ℕ, 1 ≤ k → k ≤ N → 1 ≤ j →
    aeval (rootOfUnityPoint N k) (psum (Fin N) ℚ j) = if k ∣ j then (k : ℂ) else 0

def SchPowerSumHomWeighted.Statement : Prop :=
  ∀ (N d : ℕ) (S : MvPolynomial (Fin N) ℚ),
    S.IsWeightedHomogeneous (fun i : Fin N => (i : ℕ) + 1) d → (powerSumHom N S).IsHomogeneous d

def SchWeightedPreimage.Statement : Prop :=
  ∀ (N k : ℕ) (P : MvPolynomial (Fin N) ℚ), P.IsSymmetric → P.IsHomogeneous k →
    ∃ S, powerSumHom N S = P ∧ S.IsWeightedHomogeneous (fun i : Fin N => (i : ℕ) + 1) k

def SchEvalPowerSumHom.Statement : Prop :=
  ∀ (N k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) (S : MvPolynomial (Fin N) ℚ),
    S.IsWeightedHomogeneous (fun i : Fin N => (i : ℕ) + 1) k →
      aeval (rootOfUnityPoint N k) (powerSumHom N S) =
        (k : ℂ) * ((AddMonoidAlgebra.coeff S (Finsupp.single (⟨k - 1, by omega⟩ : Fin N) 1) : ℚ) : ℂ)

def SchSchurHomogeneous.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (r : ℕ) (lam : Fin r → ℕ),
    (schur σ lam).IsHomogeneous (∑ i, lam i)

def SchSchurRowsToK.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (r k : ℕ) (nu : Fin r → ℕ), Antitone nu →
    ∑ i, nu i = k →
    schur σ nu = schur σ (fun i : Fin k => if h : (i : ℕ) < r then nu ⟨i, h⟩ else 0)

def SchSchurEvalMatrix.Statement : Prop :=
  ∀ (N k r : ℕ) (nu : Fin r → ℕ), 1 ≤ k → k ≤ N →
    aeval (rootOfUnityPoint N k) (schur (Fin N) nu) = (rootOfUnityJTMatrix k nu).det

def SchRootOfUnityBialternant.Statement : Prop :=
  ∀ (k : ℕ) (nu : Fin k → ℕ), 1 ≤ k →
    (Matrix.of fun i j : Fin k => rootOfUnity k ^ ((j : ℕ) * (nu i + (k - 1 - (i : ℕ))))).det =
      (rootOfUnityJTMatrix k nu).det * vandermondeOf (fun i : Fin k => rootOfUnity k ^ (i : ℕ))

def SchRootOfUnityRowsPerm.Statement : Prop :=
  ∀ (k : ℕ) (l : Fin k → ℕ) (π : Equiv.Perm (Fin k)), 1 ≤ k →
    (∀ i, l i % k = k - 1 - (π i : ℕ)) →
      (Matrix.of fun i j : Fin k => rootOfUnity k ^ ((j : ℕ) * l i)).det =
        (((Equiv.Perm.sign π : ℤ) : ℂ)) *
          (Matrix.of fun i j : Fin k => rootOfUnity k ^ ((j : ℕ) * (k - 1 - (i : ℕ)))).det

def SchRootOfUnityRowsEq.Statement : Prop :=
  ∀ (k : ℕ) (l : Fin k → ℕ) (i i' : Fin k), i ≠ i' → l i % k = l i' % k →
    (Matrix.of fun i j : Fin k => rootOfUnity k ^ ((j : ℕ) * l i)).det = 0

def SchHookResidues.Statement : Prop :=
  ∀ (k : ℕ) (nu : Fin k → ℕ), 1 ≤ k → Antitone nu → ∑ i, nu i = k →
    (∀ i : Fin k, (i : ℕ) ≠ 0 → nu i ≤ 1) →
    ∃ π : Equiv.Perm (Fin k), (∀ i, (nu i + (k - 1 - (i : ℕ))) % k = k - 1 - (π i : ℕ)) ∧
      ((Equiv.Perm.sign π : ℤ)) =
        (-1) ^ (univ.filter fun i : Fin k => (i : ℕ) ≠ 0 ∧ nu i = 1).card

def SchResidueCount.Statement : Prop :=
  ∀ (k : ℕ) (l : Fin k → ℕ), (∀ i, l i < 2 * k) → Function.Injective (fun i => l i % k) →
    ∑ i, l i = k * (k - 1) / 2 + k * (univ.filter fun i => k ≤ l i).card

def SchNonHookResidues.Statement : Prop :=
  ∀ (k : ℕ) (nu : Fin k → ℕ), 1 ≤ k → Antitone nu → ∑ i, nu i = k →
    ¬ (∀ i : Fin k, (i : ℕ) ≠ 0 → nu i ≤ 1) →
    ∃ i i' : Fin k, i ≠ i' ∧ (nu i + (k - 1 - (i : ℕ))) % k = (nu i' + (k - 1 - (i' : ℕ))) % k

def SchRootOfUnityVandermondeNe.Statement : Prop :=
  ∀ k : ℕ, 1 ≤ k → vandermondeOf (fun i : Fin k => rootOfUnity k ^ (i : ℕ)) ≠ 0

def SchJTMatrixDetAtRoots.Statement : Prop :=
  ∀ (k : ℕ) (nu : Fin k → ℕ), 1 ≤ k → Antitone nu → ∑ i, nu i = k →
    (rootOfUnityJTMatrix k nu).det =
      if ∀ i : Fin k, (i : ℕ) ≠ 0 → nu i ≤ 1 then
        (-1) ^ (univ.filter fun i : Fin k => (i : ℕ) ≠ 0 ∧ nu i = 1).card else 0

def SchSchurAtRootsOfUnity.Statement : Prop :=
  ∀ (N r k : ℕ) (nu : Fin r → ℕ), 1 ≤ k → k ≤ N → Antitone nu → ∑ i, nu i = k →
    aeval (rootOfUnityPoint N k) (schur (Fin N) nu) =
      if ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1 then
        (-1) ^ (univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ nu i = 1).card else 0

def smallBlockPlace (r a : ℕ) (c : SmallBlock) : Fin r ⊕ Fin a → Fin 1 × Fin (r + a) :=
  Sum.elim (yIndex 1 r a c 0) (zIndex 1 r a c 0)

def smallBlockOf (r a : ℕ) : SmallBlock → Fin (r + a) → Fin r ⊕ Fin a
  | .last, p =>
    if h : (p : ℕ) < a then Sum.inr ⟨p, h⟩ else Sum.inl ⟨(p : ℕ) - a, by have := p.isLt; omega⟩
  | .first, p =>
    if h : (p : ℕ) < r then Sum.inl ⟨p, h⟩ else Sum.inr ⟨(p : ℕ) - r, by have := p.isLt; omega⟩

def SchAevalSignedRename.Statement : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (s : ℚ) (g : ι → κ)
    (d : ℕ) (P : MvPolynomial ι ℚ), P.IsHomogeneous d →
    aeval (fun i => C s * (X (g i) : MvPolynomial κ ℚ)) P = C (s ^ d) * rename g P

def SchAntisymmetrizePlace.Statement : Prop :=
  ∀ (r a : ℕ) (c : SmallBlock) (Q : MvPolynomial (Fin r ⊕ Fin a) ℚ),
    antisymmetrize 1 (r + a) (rename (smallBlockPlace r a c) Q) =
      rename (smallBlockPlace r a c) (antisym Q)

def SchSmallBlockProduct.Statement : Prop :=
  ∀ (r a : ℕ) (c : SmallBlock) (lam : Fin r → ℕ),
    aeval (yRoot 1 r a c 0) (schur (Fin r) lam) * vandermondeOf (yRoot 1 r a c 0) *
        vandermondeOf (zRoot 1 r a c 0) =
      C (c.sign ^ (∑ i, lam i + r * (r - 1) / 2)) *
        rename (smallBlockPlace r a c)
          (rename Sum.inl (alternant fun i : Fin r => lam i + (r - 1 - (i : ℕ))) *
            rename Sum.inr (alternant fun j : Fin a => a - 1 - (j : ℕ)))

def SchAlternantRenamePlace.Statement : Prop :=
  ∀ (r a : ℕ) (c : SmallBlock) (v : Fin r ⊕ Fin a → ℕ),
    rename (smallBlockPlace r a c) (alternant v) =
      rename (fun p : Fin (r + a) => ((0 : Fin 1), p)) (alternant (v ∘ smallBlockOf r a c))

def SchConcatExponent.Statement : Prop :=
  ∀ (r a : ℕ) (c : SmallBlock), ∃ τ : Equiv.Perm (Fin (r + a)),
    ∀ lam : Fin r → ℕ, (∀ i, a ≤ lam i) →
      (Sum.elim (fun i : Fin r => lam i + (r - 1 - (i : ℕ))) (fun j : Fin a => a - 1 - (j : ℕ)))
          ∘ smallBlockOf r a c =
        (fun p : Fin (r + a) =>
          Schur.padPartition (r + a) (fun i : Fin r => lam i - a) p + (r + a - 1 - (p : ℕ))) ∘ τ

def SchConcatAlternant.Statement : Prop :=
  ∀ (r a : ℕ) (c : SmallBlock), ∃ s : ℚ, (s = 1 ∨ s = -1) ∧
    ∀ lam : Fin r → ℕ, (∀ i, a ≤ lam i) →
      rename (smallBlockPlace r a c)
          (alternant (Sum.elim (fun i : Fin r => lam i + (r - 1 - (i : ℕ)))
            (fun j : Fin a => a - 1 - (j : ℕ)))) =
        C s * rename (fun p : Fin (r + a) => ((0 : Fin 1), p))
          (vandermondeOf (fun p : Fin (r + a) => (X p : MvPolynomial (Fin (r + a)) ℚ)) *
            schur (Fin (r + a)) (fun i : Fin r => lam i - a))

def SchConcatAlternantZero.Statement : Prop :=
  ∀ (r a : ℕ) (lam : Fin r → ℕ), Antitone lam → ¬ (∀ i, a ≤ lam i) →
    alternant (Sum.elim (fun i : Fin r => lam i + (r - 1 - (i : ℕ)))
      (fun j : Fin a => a - 1 - (j : ℕ))) = 0

def SchBlockVandermondeOne.Statement : Prop :=
  ∀ N : ℕ, blockVandermonde 1 N =
    rename (fun p : Fin N => ((0 : Fin 1), p))
      (vandermondeOf (fun p : Fin N => (X p : MvPolynomial (Fin N) ℚ)))

def SchAlternantHomogeneous.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (e : ι → ℕ), (alternant e).IsHomogeneous (∑ i, e i)

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PHomogeneousComponentMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem HomogeneousComponentMul.proof : HomogeneousComponentMul.Statement := by
  intro σ R _ p a m d hp
  have hterm : ∀ i, homogeneousComponent d (p * homogeneousComponent i a) =
      if d = m + i then p * homogeneousComponent i a else 0 := fun i =>
    homogeneousComponent_of_mem
      ((mem_homogeneousSubmodule _ _).mpr (hp.mul (homogeneousComponent_isHomogeneous i a)))
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [← sum_homogeneousComponent a, Finset.mul_sum, map_sum]
  simp_rw [hterm]
  split_ifs with hmd
  · have hcongr : ∀ i ∈ range (a.totalDegree + 1),
        (if d = m + i then p * homogeneousComponent i a else 0) =
          if d - m = i then p * homogeneousComponent i a else 0 := by
      intro i _
      congr 1
      exact propext ⟨fun h => by omega, fun h => by omega⟩
    rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq]
    split_ifs with hmem
    · rfl
    · rw [Finset.mem_range, not_lt] at hmem
      rw [homogeneousComponent_eq_zero (d - m) a (by omega), mul_zero]
  · exact Finset.sum_eq_zero fun i _ => if_neg (by omega)

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PVandermondeOfHomogeneous
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem VandermondeOfHomogeneous.sum_card_Ioi (m : ℕ) :
    (∑ i : Fin m, ∑ _j ∈ Finset.Ioi i, (1 : ℕ)) = m * (m - 1) / 2 := by
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun i => m - 1 - i) m]
  have h := Finset.sum_range_reflect (fun i => i) m
  rw [h, Finset.sum_range_id]

theorem VandermondeOfHomogeneous.proof : VandermondeOfHomogeneous.Statement := by
  intro σ R _ m v hv
  rw [← VandermondeOfHomogeneous.sum_card_Ioi m]
  unfold vandermondeOf
  refine IsHomogeneous.prod _ _ _ fun i _ => ?_
  refine IsHomogeneous.prod _ _ _ fun j _ => ?_
  exact (hv i).sub (hv j)

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvStaircaseDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

theorem Coinv.sum_staircase_exponents (f n : ℕ) :
    ∑ v : Fin f × Fin n, (v.2 : ℕ) = coinvTop f n := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]
  rfl

theorem CoinvStaircaseDegree.proof : CoinvStaircaseDegree.Statement := by
  intro f n e he
  have hle : ∀ v ∈ (Finset.univ : Finset (Fin f × Fin n)), e v ≤ (v.2 : ℕ) := fun v _ => he v
  rw [Finsupp.degree_eq_sum, ← Coinv.sum_staircase_exponents f n]
  refine ⟨Finset.sum_le_sum hle, fun hEq => ?_⟩
  have hall := (Finset.sum_eq_sum_iff_of_le hle).1 hEq
  ext v
  simp [staircase, hall v (Finset.mem_univ v)]

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvPolynomialReduction
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

noncomputable section

theorem CoinvPolynomialReduction.proof (h1 : CoinvMonomialReduction.Statement) :
    CoinvPolynomialReduction.Statement := by
  intro K _ _ f n H
  choose v hv hvI using fun d => h1 K f n d
  refine ⟨∑ d ∈ H.support, AddMonoidAlgebra.coeff H d • v d, ?_, ?_⟩
  · exact Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _ (hv d)
  · have e1 : H - ∑ d ∈ H.support, AddMonoidAlgebra.coeff H d • v d =
        (∑ d ∈ H.support, monomial d (AddMonoidAlgebra.coeff H d)) - ∑ d ∈ H.support, AddMonoidAlgebra.coeff H d • v d := by
      rw [← H.as_sum]
    have e2 : (∑ d ∈ H.support, monomial d (AddMonoidAlgebra.coeff H d)) - ∑ d ∈ H.support, AddMonoidAlgebra.coeff H d • v d =
        ∑ d ∈ H.support, C (AddMonoidAlgebra.coeff H d) * (monomial d (1 : K) - v d) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [mul_sub, C_mul_monomial, mul_one, smul_eq_C_mul]
    rw [e1, e2]
    exact Ideal.sum_mem _ fun d _ => Ideal.mul_mem_left _ _ (hvI d)

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvIdealComponent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

noncomputable section

theorem Coinv.bps_isHomogeneous (K : Type) [Field K] (f n m : ℕ) (b : Fin f) :
    (bps K f n m b).IsHomogeneous m :=
  IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_X_pow _ _

theorem CoinvIdealComponent.proof (h1 : CoinvIdealRepresentation.Statement)
    (h2 : HomogeneousComponentMul.Statement) : CoinvIdealComponent.Statement := by
  intro K _ f n J hJ d
  obtain ⟨a, rfl⟩ := h1 K f n J hJ
  refine ⟨fun m b => if m ≤ d then homogeneousComponent (d - m) (a m b) else 0, ?_, ?_⟩
  · intro m b
    dsimp only
    split_ifs
    · exact homogeneousComponent_isHomogeneous _ _
    · exact isHomogeneous_zero _ _ _
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [h2 (Fin f × Fin n) K (bps K f n m b) (a m b) m d (bps_isHomogeneous K f n m b)]
    by_cases hmd : m ≤ d <;> simp [hmd]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvAboveTopGeneral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

noncomputable section

theorem CoinvAboveTopGeneral.proof (h1 : CoinvAboveTop.Statement) :
    CoinvAboveTopGeneral.Statement := by
  intro K _ _ β ι _ _ _ _ d H hH hd
  set eβ := Fintype.equivFin β
  set eι := Fintype.equivFin ι
  set ψ : β × ι ≃ Fin (Fintype.card β) × Fin (Fintype.card ι) := eβ.prodCongr eι with hψ
  obtain ⟨Q', hQ'h, hQ'⟩ := h1 K (Fintype.card β) (Fintype.card ι) d (rename ψ H)
    hH.rename_isHomogeneous hd
  refine ⟨fun m b => rename ψ.symm (Q' m (eβ b)),
    fun m b => (hQ'h m (eβ b)).rename_isHomogeneous, ?_⟩
  have hback : H = rename ψ.symm (rename ψ H) := by
    rw [rename_rename, Equiv.symm_comp_self, rename_id_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hback, hQ', map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← Equiv.sum_comp eβ.symm]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [map_mul]
  simp only [Equiv.apply_symm_apply]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [bps, map_sum, ← Equiv.sum_comp eι.symm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [hψ]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvStaircaseComponent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Coinv

noncomputable section

theorem CoinvStaircaseComponent.proof (h1 : CoinvStaircaseDegree.Statement) :
    CoinvStaircaseComponent.Statement := by
  intro K _ f n v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, he, rfl⟩ := hx
    have hhom : monomial e (1 : K) ∈ homogeneousSubmodule (Fin f × Fin n) K e.degree :=
      (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_monomial 1 rfl)
    obtain ⟨hle, heq⟩ := h1 f n e he
    refine ⟨fun d hd => ?_, ?_⟩
    · rw [homogeneousComponent_of_mem hhom, if_neg (by omega)]
    · rw [homogeneousComponent_of_mem hhom]
      by_cases h : coinvTop f n = e.degree
      · refine ⟨1, ?_⟩
        rw [if_pos h, heq h.symm, C_1, one_mul]
      · exact ⟨0, by rw [if_neg h, C_0, zero_mul]⟩
  | zero => exact ⟨fun d _ => map_zero _, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨hx1, cx, hx2⟩ := hx
    obtain ⟨hy1, cy, hy2⟩ := hy
    refine ⟨fun d hd => by rw [map_add (f := _), hx1 d hd, hy1 d hd, add_zero], cx + cy, ?_⟩
    rw [map_add (f := _), hx2, hy2, C_add, add_mul]
  | smul a x _ hx =>
    obtain ⟨hx1, cx, hx2⟩ := hx
    refine ⟨fun d hd => by rw [map_smul, hx1 d hd, smul_zero], a * cx, ?_⟩
    rw [map_smul, hx2, smul_eq_C_mul, C_mul, mul_assoc]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvMonomialReduction
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

noncomputable section

theorem CoinvMonomialReduction.proof (h1 : CoinvStepReduction.Statement) :
    CoinvMonomialReduction.Statement := by
  intro K _ _ f n e
  classical
  let r : Fin f × Fin n → Fin f × Fin n → Prop := fun u v => toLex u < toLex v
  have : IsStrictTotalOrder (Fin f × Fin n) r :=
    inferInstanceAs (IsStrictTotalOrder (Lex (Fin f × Fin n)) (· < ·))
  have wf : WellFounded
      (Finsupp.Lex r (· < ·) : (Fin f × Fin n →₀ ℕ) → (Fin f × Fin n →₀ ℕ) → Prop) :=
    Finsupp.Lex.wellFounded_of_finite r wellFounded_lt
  induction e using wf.induction with
  | _ e ih =>
  by_cases hu : IsUnderStaircase e
  · exact ⟨monomial e 1, Submodule.subset_span ⟨e, hu, rfl⟩, by simp⟩
  · simp only [IsUnderStaircase, not_forall, not_le] at hu
    obtain ⟨⟨b, k⟩, hbk⟩ := hu
    obtain ⟨T, c, hT, hmem⟩ := h1 K f n b k e (by simpa using hbk)
    have hlt : ∀ e' ∈ T, Finsupp.Lex r (· < ·) e' e := by
      intro e' he'
      refine Finsupp.lex_def.mpr ⟨(b, k), fun j hj => (hT e' he').1 j ?_, (hT e' he').2⟩
      exact Prod.Lex.toLex_lt_toLex.mp hj
    choose! w hw hwm using fun e' (he' : e' ∈ T) => ih e' (hlt e' he')
    refine ⟨∑ e' ∈ T, c e' • w e',
      Submodule.sum_mem _ fun e' he' => Submodule.smul_mem _ _ (hw e' he'), ?_⟩
    have hsplit : monomial e (1 : K) - ∑ e' ∈ T, c e' • w e' =
        (monomial e 1 - ∑ e' ∈ T, c e' • monomial e' 1) +
          ∑ e' ∈ T, C (c e') * (monomial e' 1 - w e') := by
      simp only [smul_eq_C_mul, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [hsplit]
    exact Ideal.add_mem _ hmem (Ideal.sum_mem _ fun e' he' => Ideal.mul_mem_left _ _ (hwm e' he'))

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvIdealRepresentation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section


open Coinv in
theorem CoinvIdealRepresentation.proof : CoinvIdealRepresentation.Statement := by
  intro K _ f n J hJ
  induction hJ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m₀, b₀, h1, h2, rfl⟩ := hx
    refine ⟨fun m b => if m = m₀ ∧ b = b₀ then 1 else 0, ?_⟩
    have hm₀ : m₀ ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨h1, h2⟩
    symm
    rw [Finset.sum_eq_single m₀]
    · rw [Finset.sum_eq_single b₀]
      · simp
      · intro b _ hb
        simp [hb]
      · intro h
        exact absurd (Finset.mem_univ b₀) h
    · intro m _ hm
      apply Finset.sum_eq_zero
      intro b _
      simp [hm]
    · intro h
      exact absurd hm₀ h
  | zero =>
    exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨a', rfl⟩ := hy
    refine ⟨a + a', ?_⟩
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  | smul r x _ hx =>
    obtain ⟨a, rfl⟩ := hx
    refine ⟨fun m b => r * a m b, ?_⟩
    simp only [smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun b _ => ?_
    ring

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvStepReduction
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

open Coinv

theorem CoinvStepReduction.proof : CoinvStepReduction.Statement := by
  classical
  intro K _ _ f n b k e he
  obtain ⟨c, hc⟩ := Coinv.exists_reduction (K := K) (f := f) (n := n) b k
  set φ : ↥(Finset.Ioi k) → Fin f × Fin n := fun s => (b, (s : Fin n)) with hφ
  have hinj : Function.Injective φ := fun s t h => Subtype.ext (Prod.ext_iff.mp h).2
  obtain ⟨e₀, rfl⟩ : ∃ e₀ : Fin f × Fin n →₀ ℕ, e = e₀ + Finsupp.single (b, k) ((k : ℕ) + 1) := by
    refine ⟨e - Finsupp.single (b, k) ((k : ℕ) + 1), ?_⟩
    ext u
    simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
    by_cases hu : u = (b, k)
    · subst hu; simp only [Finsupp.single_eq_same]; omega
    · simp [Ne.symm hu]
  set P : MvPolynomial (Fin f × Fin n) K := ∑ j ∈ range ((k : ℕ) + 1),
      monomial e₀ 1 * (rename φ (-c j) * X (b, k) ^ j) with hP
  refine ⟨P.support, fun e' => P.coeff e', ?_, ?_⟩
  · intro e' he'
    have h1 := support_sum he'
    rw [Finset.mem_biUnion] at h1
    obtain ⟨j, hj, hj'⟩ := h1
    have h2 := support_mul _ _ hj'
    rw [Finset.mem_add] at h2
    obtain ⟨a, ha, d', hd', rfl⟩ := h2
    have ha' : a = e₀ := Finset.mem_singleton.mp (support_monomial_subset ha)
    have h3 := support_mul _ _ hd'
    rw [Finset.mem_add] at h3
    obtain ⟨d, hd, s, hs, rfl⟩ := h3
    rw [X_pow_eq_monomial] at hs
    have hs' : s = Finsupp.single (b, k) j := Finset.mem_singleton.mp (support_monomial_subset hs)
    rw [support_rename_of_injective hinj, Finset.mem_image] at hd
    obtain ⟨d₀, -, rfl⟩ := hd
    subst ha' hs'
    have hoff : ∀ u : Fin f × Fin n, (u.1 ≠ b ∨ u.2 ≤ k) → Finsupp.mapDomain φ d₀ u = 0 := by
      intro u hu
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨s, rfl⟩
      have hks : k < (s : Fin n) := Finset.mem_Ioi.mp s.2
      rcases hu with hu | hu
      · exact hu rfl
      · exact absurd hu (not_le.mpr hks)
    rw [Finset.mem_range] at hj
    refine ⟨fun u hu => ?_, ?_⟩
    · have hne : u ≠ (b, k) := by
        rintro rfl
        rcases hu with h | ⟨-, h⟩ <;> exact lt_irrefl _ h
      have h0 := hoff u (by
        rcases hu with h | ⟨-, h⟩
        · exact Or.inl (ne_of_lt h)
        · exact Or.inr (le_of_lt h))
      simp [h0, Ne.symm hne]
    · have h0 := hoff (b, k) (Or.inr le_rfl)
      simp only [Finsupp.add_apply, h0, Finsupp.single_eq_same]
      omega
  · have hsum : ∑ e' ∈ P.support, P.coeff e' • monomial e' (1 : K) = P := by
      conv_rhs => rw [P.as_sum]
      refine Finset.sum_congr rfl fun e' _ => ?_
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hsum]
    have hm : monomial (e₀ + Finsupp.single (b, k) ((k : ℕ) + 1)) (1 : K) =
        monomial e₀ 1 * X (b, k) ^ ((k : ℕ) + 1) := by
      rw [X_pow_eq_monomial, monomial_mul, one_mul]
    have hdiff : monomial (e₀ + Finsupp.single (b, k) ((k : ℕ) + 1)) (1 : K) - P =
        monomial e₀ 1 * (X (b, k) ^ ((k : ℕ) + 1) +
          ∑ j ∈ range ((k : ℕ) + 1), rename φ (c j) * X (b, k) ^ j) := by
      rw [hm, hP, mul_add, Finset.mul_sum]
      simp only [map_neg, neg_mul, mul_neg, Finset.sum_neg_distrib, sub_neg_eq_add]
    rw [hdiff]
    exact Ideal.mul_mem_left _ _ hc

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvAboveTop
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

theorem CoinvAboveTop.proof (h1 : CoinvPolynomialReduction.Statement)
    (h2 : CoinvIdealComponent.Statement) (h3 : CoinvStaircaseComponent.Statement) :
    CoinvAboveTop.Statement := by
  intro K _ _ f n d H hH hd
  obtain ⟨v, hv, hJ⟩ := h1 K f n H
  obtain ⟨Q, hQ, hcomp⟩ := h2 K f n (H - v) hJ d
  refine ⟨Q, hQ, ?_⟩
  have h0 : homogeneousComponent d v = 0 := (h3 K f n v hv).1 d hd
  have hHd : homogeneousComponent d H = H := by
    rw [homogeneousComponent_of_mem (mem_homogeneousSubmodule d H |>.mpr hH), if_pos rfl]
  rw [← hcomp, map_sub, h0, sub_zero, hHd]

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvAtTop
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

noncomputable section

theorem CoinvAtTop.proof (h1 : CoinvPolynomialReduction.Statement)
    (h2 : CoinvIdealComponent.Statement) (h3 : CoinvStaircaseComponent.Statement) :
    CoinvAtTop.Statement := by
  intro K _ _ f n H hH
  obtain ⟨v, hv, hJ⟩ := h1 K f n H
  obtain ⟨Q, -, hQ⟩ := h2 K f n (H - v) hJ (coinvTop f n)
  obtain ⟨-, c, hc⟩ := h3 K f n v hv
  refine ⟨c, ?_⟩
  have hcomp : H - C c * monomial (staircase f n) 1 =
      homogeneousComponent (coinvTop f n) (H - v) := by
    rw [map_sub, homogeneousComponent_eq_self hH, hc]
  rw [hcomp, hQ]
  refine Ideal.sum_mem _ fun m hm => Ideal.sum_mem _ fun b _ => ?_
  rw [Finset.mem_Icc] at hm
  exact Ideal.mul_mem_right _ _ (bps_mem_psumIdeal b hm.1 hm.2)

end

end GroundTheory.Heights₂.Heights.RestTerms
end
