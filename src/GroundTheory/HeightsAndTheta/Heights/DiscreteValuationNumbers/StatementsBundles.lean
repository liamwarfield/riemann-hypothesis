module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsMultiHomogIdealSpanSingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PCutByForm

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def NumericalSegre.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (e : ℕ),
    IsMultiProjPrime (pointIdeal F y) →
    ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (N : ℕ), 0 < N → ∀ (E : Type) [AddCommGroup E] [Module Ω E]
      (B : ChartBundle F (segreVec y) N E) (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ),
      IsFlagFrame y B w b →
    ∀ (M : ℕ) (a : K → ℤ) (φ : Fin M → Module.Dual Ω E), IsTwistedDualGens y B a φ →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ (n : ℕ) (Y : List (K → ℤ)), n + Y.length = N - 1 + e →
      intNumL F (projIdeal F y w φ t) (List.replicate n zetaDeg ++ Y.map liftDeg) =
        if N - 1 ≤ n then
          ∑ α ∈ Finset.Nat.antidiagonalTuple N (n - (N - 1)),
            intNumL F (pointIdeal F y) (rootList (fun i => a - b i) α ++ Y)
        else 0

def FlagIndependence.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (B B' : ChartBundle O (segreVec y) N E),
      SameGenericFibre ϖ B B' →
    ∀ (w w' v v' : Module.Basis (Fin N) Ω E) (x x' u u' : Fin N → K → ℤ)
      (f g f₂ g₂ : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g → IsFlagPair ϖ y B B' v v' u u' f₂ g₂ →
    ∀ (m : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsHomogeneous m → G.IsSymmetric →
    ∀ (Gs Hs : Fin N → MvPolynomial (Fin N ⊕ Fin N) ℤ), IsPairExpansion m G Gs →
      IsPairExpansion m G Hs →
    ∀ Q : List (K → ℤ), Q.length + m = d + 1 →
      pairNum (pointIdeal O y) x x' f g Gs Q = pairNum (pointIdeal O y) u u' f₂ g₂ Hs Q

def PairNumberPullback.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (d r : ℕ),
      IsModelOver (pointIdeal O y) d → IsModelOver (pointIdeal O (joinCoords y y')) (d + r) →
    ∀ (N : ℕ) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      (∀ i, IsVerticalDivisor (pointIdeal O y) ϖ (x i - x' i) (f i) (g i)) →
    ∀ (m : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsHomogeneous m →
    ∀ Gs : Fin N → MvPolynomial (Fin N ⊕ Fin N) ℤ, IsPairExpansion m G Gs →
    ∀ Q : List (K → ℤ), Q.length + m = d + r + 1 →
      (0 < r → pairNum (pointIdeal O (joinCoords y y')) (fun i => joinDeg (x i))
        (fun i => joinDeg (x' i)) (fun i => joinForm (f i)) (fun i => joinForm (g i)) Gs
        (Q.map joinDeg) = 0) ∧
      (IsBirationalJoin O y y' → pairNum (pointIdeal O (joinCoords y y')) (fun i => joinDeg (x i))
        (fun i => joinDeg (x' i)) (fun i => joinForm (f i)) (fun i => joinForm (g i)) Gs
        (Q.map joinDeg) = pairNum (pointIdeal O y) x x' f g Gs Q)

def PairCocycle.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (B B' B'' : ChartBundle O (segreVec y) N E),
      SameGenericFibre ϖ B B' → SameGenericFibre ϖ B' B'' →
    ∀ (w w' w'' : Module.Basis (Fin N) Ω E) (x x' x'' : Fin N → K → ℤ)
      (f g f' g' f'' g'' : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g → IsFlagPair ϖ y B' B'' w' w'' x' x'' f' g' →
      IsFlagPair ϖ y B B'' w w'' x x'' f'' g'' →
    ∀ (k : ℕ) (Gs Gs' Gs'' : Fin N → MvPolynomial (Fin N ⊕ Fin N) ℤ),
      IsPairExpansion k (psum (Fin N) ℤ k) Gs → IsPairExpansion k (psum (Fin N) ℤ k) Gs' →
      IsPairExpansion k (psum (Fin N) ℤ k) Gs'' →
    ∀ Q : List (K → ℤ), Q.length + k = d + 1 →
      pairNum (pointIdeal O y) x x'' f'' g'' Gs'' Q =
          pairNum (pointIdeal O y) x x' f g Gs Q + pairNum (pointIdeal O y) x' x'' f' g' Gs' Q ∧
        ∀ (fr gr : Fin N → MRing ι O) (Gr : Fin N → MvPolynomial (Fin N ⊕ Fin N) ℤ),
          IsFlagPair ϖ y B' B w' w x' x fr gr → IsPairExpansion k (psum (Fin N) ℤ k) Gr →
          pairNum (pointIdeal O y) x' x fr gr Gr Q = -pairNum (pointIdeal O y) x x' f g Gs Q

def SubQuotient.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N r : ℕ) (E U V : Type) [AddCommGroup E] [Module Ω E] [AddCommGroup U] [Module Ω U]
      [AddCommGroup V] [Module Ω V]
      (B B' : ChartBundle O (segreVec y) N E) (BU BU' : ChartBundle O (segreVec y) r U)
      (BV BV' : ChartBundle O (segreVec y) (N - r) V) (j : U →ₗ[Ω] E) (π : E →ₗ[Ω] V),
      Function.Injective j → Function.Surjective π → LinearMap.range j = LinearMap.ker π →
      SameGenericFibre ϖ B B' →
      (∀ c, segreVec y c ≠ 0 →
        (∀ z, z ∈ BU.lat c ↔ j z ∈ B.lat c) ∧ (∀ z, z ∈ BU'.lat c ↔ j z ∈ B'.lat c) ∧
        (∀ q, q ∈ BV.lat c ↔ ∃ z ∈ B.lat c, π z = q) ∧
        (∀ q, q ∈ BV'.lat c ↔ ∃ z ∈ B'.lat c, π z = q)) →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (wU wU' : Module.Basis (Fin r) Ω U) (xU xU' : Fin r → K → ℤ) (fU gU : Fin r → MRing ι O),
      IsFlagPair ϖ y BU BU' wU wU' xU xU' fU gU →
    ∀ (wV wV' : Module.Basis (Fin (N - r)) Ω V) (xV xV' : Fin (N - r) → K → ℤ)
      (fV gV : Fin (N - r) → MRing ι O),
      IsFlagPair ϖ y BV BV' wV wV' xV xV' fV gV →
    ∀ (k : ℕ) (Gs : Fin N → MvPolynomial (Fin N ⊕ Fin N) ℤ)
      (GsU : Fin r → MvPolynomial (Fin r ⊕ Fin r) ℤ)
      (GsV : Fin (N - r) → MvPolynomial (Fin (N - r) ⊕ Fin (N - r)) ℤ),
      IsPairExpansion k (psum (Fin N) ℤ k) Gs → IsPairExpansion k (psum (Fin r) ℤ k) GsU →
      IsPairExpansion k (psum (Fin (N - r)) ℤ k) GsV →
    ∀ Q : List (K → ℤ), Q.length + k = d + 1 →
      pairNum (pointIdeal O y) x x' f g Gs Q =
        pairNum (pointIdeal O y) xU xU' fU gU GsU Q + pairNum (pointIdeal O y) xV xV' fV gV GsV Q

def ScalarQuotient.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (B B' : ChartBundle O (segreVec y) N E)
      (n : ℕ) (u : Oˣ),
      (∀ c, segreVec y c ≠ 0 → ∀ z, z ∈ B'.lat c ↔
        ∃ z₀ ∈ B.lat c, z = algebraMap O Ω ((u : O) * ϖ ^ n) • z₀) →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (k : ℕ) (Gs : Fin N → MvPolynomial (Fin N ⊕ Fin N) ℤ),
      IsPairExpansion k (psum (Fin N) ℤ k) Gs →
    ∀ Q : List (K → ℤ), Q.length + k = d + 1 →
      pairNum (pointIdeal O y) x x' f g Gs Q =
        (k : ℤ) * n * cycEval (fun W => classNum x (psum (Fin N) ℤ (k - 1)) Q W)
          (divCycle (pointIdeal O y) (C ϖ))

section Examples

theorem isVerticalDivisor_one {K : Type*} [DecidableEq K] {ι : K → Type*} {O : Type*} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (H : Ideal (MRing ι O)) [H.IsPrime] :
    IsVerticalDivisor H ϖ 0 1 1 := by
  have hHom : IsMultiHomog (1 : MRing ι O) 0 := isWeightedHomogeneous_one O (blockWeight ι)
  have hOne : (1 : MRing ι O) ∉ H := (Ideal.ne_top_iff_one H).mp Ideal.IsPrime.ne_top'
  refine ⟨⟨0, 0, hHom, hHom, ?_⟩, hOne, hOne, ?_, ?_⟩
  · funext k
    simp
  · simp [ratDiv]
  · intro W hW _ _ _
    have hOneW : (1 : MRing ι O) ∉ W := (Ideal.ne_top_iff_one W).mp hW.ne_top
    exact ⟨1, 1, hOneW, hOneW, by simp⟩

def psumExpansion (N k : ℕ) : Fin N → MvPolynomial (Fin N ⊕ Fin N) ℤ :=
  fun i => ∑ j ∈ Finset.range k, X (Sum.inl i) ^ j * X (Sum.inr i) ^ (k - 1 - j)

theorem isHomogeneous_psumExpansion (N k : ℕ) (i : Fin N) :
    (psumExpansion N k i).IsHomogeneous (k - 1) := by
  unfold psumExpansion
  refine IsHomogeneous.sum _ _ _ fun j hj => ?_
  have hj' : j + (k - 1 - j) = k - 1 := by
    have := Finset.mem_range.mp hj
    omega
  have h := ((isHomogeneous_X ℤ (Sum.inl i : Fin N ⊕ Fin N)).pow j).mul
    ((isHomogeneous_X ℤ (Sum.inr i : Fin N ⊕ Fin N)).pow (k - 1 - j))
  simpa [hj'] using h

theorem isPairExpansion_psum (N k : ℕ) :
    IsPairExpansion k (psum (Fin N) ℤ k) (psumExpansion N k) := by
  refine ⟨?_, isHomogeneous_psumExpansion N k⟩
  unfold psumExpansion
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [psum, map_sum, map_pow, rename_X, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm, (Commute.all _ _).geom_sum₂_mul]

end Examples

section ExamplesDVR

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {Ω : Type*} [Field Ω]
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω]

instance pointIdeal_isPrime (y : (Σ k, ι k) → Ω) : (pointIdeal O y).IsPrime :=
  RingHom.ker_isPrime _

theorem isFlagPair_self (ϖ : O) (y : (Σ k, ι k) → Ω) (r : ℕ) {s : Ω} (hs : s ≠ 0) :
    IsFlagPair ϖ y (scaledTrivBundle O (segreVec y) r hs) (scaledTrivBundle O (segreVec y) r hs)
      (scaledBasis r hs) (scaledBasis r hs) 0 0 (fun _ => 1) (fun _ => 1) := by
  have hFlag := isFlagFrame_scaledTriv O y r hs
  refine ⟨hFlag, hFlag, ?_, ?_, ?_⟩
  · intro i j hij
    rw [Module.Basis.repr_self, Finsupp.single_apply, ite_eq_right hij.ne]
  · intro i
    rw [sub_self]
    exact isVerticalDivisor_one ϖ _
  · intro i
    simp [Module.Basis.repr_self]

end ExamplesDVR

section ExamplesZ2

theorem isHomogeneous_psum (N k : ℕ) : (psum (Fin N) ℤ k).IsHomogeneous k := by
  unfold psum
  refine IsHomogeneous.sum _ _ _ fun i _ => ?_
  simpa using (isHomogeneous_X ℤ i).pow k

end ExamplesZ2

section ExamplesEuler

variable {Ω : Type*} [Field Ω] {R : Type*} [CommRing R] [Algebra R Ω]

section Pair
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω]

end Pair

end ExamplesEuler

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

section Regrading

variable {σ R M M' : Type*} [CommRing R] [AddCommMonoid M] [AddCommMonoid M']

theorem weight_comp_addMonoidHom (φ : M →+ M') (w : σ → M) (d : σ →₀ ℕ) :
    Finsupp.weight (fun v => φ (w v)) d = φ (Finsupp.weight w d) := by
  simp [Finsupp.weight_apply, map_finsuppSum, map_nsmul]

theorem weightedHomogeneousComponent_comp_addMonoidHom (φ : M →+ M') (hφ : Function.Injective φ)
    (w : σ → M) (b : M) (f : MvPolynomial σ R) :
    weightedHomogeneousComponent (fun v => φ (w v)) (φ b) f = weightedHomogeneousComponent w b f := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent,
    weight_comp_addMonoidHom, hφ.eq_iff]

end Regrading

section Lex

variable {K : Type} [Fintype K] {ι : K → Type} {R : Type*} [CommRing R]

def lexRelabel (e : K ≃ Fin (Fintype.card K)) : (K → ℕ) →+ Lex (Fin (Fintype.card K) → ℕ) where
  toFun b := toLex (fun j => b (e.symm j))
  map_zero' := rfl
  map_add' _ _ := rfl

theorem lexRelabel_surjective (e : K ≃ Fin (Fintype.card K)) : Function.Surjective (lexRelabel e) :=
  fun i => ⟨fun k => ofLex i (e k), by
    change toLex (fun j => ofLex i (e (e.symm j))) = i
    simp only [Equiv.apply_symm_apply]
    rfl⟩

theorem lexRelabel_injective (e : K ≃ Fin (Fintype.card K)) : Function.Injective (lexRelabel e) := by
  intro a b h
  have h' : (fun j => a (e.symm j)) = fun j => b (e.symm j) := toLex.injective h
  funext k
  simpa using congrFun h' (e k)

variable [DecidableEq K] [DecidableEq (Lex (Fin (Fintype.card K) → ℕ))]

theorem isHomogeneous_lex_of_isMultiHomogIdeal (e : K ≃ Fin (Fintype.card K))
    {I : Ideal (MRing ι R)} (hI : IsMultiHomogIdeal I) :
    letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v));
    I.IsHomogeneous (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v))) := by
  letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v))
  intro i r hr
  change ((weightedDecomposition R (fun v => lexRelabel e (blockWeight ι v))).decompose' r i :
    MRing ι R) ∈ I
  rw [weightedDecomposition.decompose'_apply]
  obtain ⟨b, rfl⟩ := lexRelabel_surjective e i
  rw [weightedHomogeneousComponent_comp_addMonoidHom _ (lexRelabel_injective e)]
  exact hI r hr b

theorem isMultiHomogIdeal_of_isHomogeneous_lex (e : K ≃ Fin (Fintype.card K))
    {I : Ideal (MRing ι R)}
    (hI : letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v));
      I.IsHomogeneous (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))) :
    IsMultiHomogIdeal I := by
  letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v))
  intro f hf b
  rw [← weightedHomogeneousComponent_comp_addMonoidHom _ (lexRelabel_injective e)]
  exact weightedHomogeneousComponent_mem_of_mem R _ hI hf _

end Lex

theorem MinimalPrimeMultiHomog.proof : MinimalPrimeMultiHomog.Statement := by
  intro R _ K _ _ ι J W hJ hW
  let e : K ≃ Fin (Fintype.card K) := Fintype.equivFin K
  letI : DecidableEq (Lex (Fin (Fintype.card K) → ℕ)) := LinearOrder.toDecidableEq
  letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v))
  have hJh : J.IsHomogeneous (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v))) := isHomogeneous_lex_of_isMultiHomogIdeal e hJ
  have hWp : W.IsPrime := hW.1.1
  have hcore : (W.homogeneousCore (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).toIdeal.IsPrime := hWp.homogeneousCore
  have hJle : J ≤ (W.homogeneousCore (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).toIdeal := by
    rw [← hJh.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v))) hW.1.2
  have hle : (W.homogeneousCore (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).toIdeal ≤ W := Ideal.toIdeal_homogeneousCore_le (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v))) W
  have heq : (W.homogeneousCore (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).toIdeal = W := le_antisymm hle (hW.2 ⟨hcore, hJle⟩ hle)
  apply isMultiHomogIdeal_of_isHomogeneous_lex e
  rw [← heq]
  exact (W.homogeneousCore (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).isHomogeneous

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

section General

variable {A : Type*} [CommRing A]

theorem localizedQuot_subsingleton_of_not_le (Q W : Ideal A) [W.IsPrime] (h : ¬ Q ≤ W) :
    Subsingleton (LocalizedModule W.primeCompl (A ⧸ Q)) := by
  obtain ⟨q, hqQ, hqW⟩ := Set.not_subset.mp h
  rw [LocalizedModule.subsingleton_iff]
  intro m
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective m
  refine ⟨q, hqW, ?_⟩
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Q.mul_mem_right a hqQ

theorem length_localizedQuot_sup_span_mul (P W : Ideal A) [P.IsPrime] [W.IsPrime] {x : A} (y : A)
    (hx : x ∉ P) :
    Module.length (Localization.AtPrime W)
        (LocalizedModule W.primeCompl (A ⧸ (P ⊔ Ideal.span {x * y}))) =
      Module.length (Localization.AtPrime W)
          (LocalizedModule W.primeCompl (A ⧸ (P ⊔ Ideal.span {y}))) +
        Module.length (Localization.AtPrime W)
          (LocalizedModule W.primeCompl (A ⧸ (P ⊔ Ideal.span {x}))) := by
  have hle : P ⊔ Ideal.span {x * y} ≤ P ⊔ Ideal.span {x} :=
    sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr
      (Ideal.mul_mem_right y _ (Ideal.mem_span_singleton_self x))) P
  let g₁ : (A ⧸ (P ⊔ Ideal.span {y})) →ₗ[A] A ⧸ (P ⊔ Ideal.span {x * y}) :=
    Submodule.mapQ _ _ (LinearMap.mulLeft A x) (fun a ha => by
      obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.mp ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      show x * (p + c * y) ∈ P ⊔ Ideal.span {x * y}
      have e : x * (p + c * y) = x * p + c * (x * y) := by ring
      rw [e]
      exact Submodule.add_mem_sup (P.mul_mem_left _ hp) (Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩))
  let g₂ : (A ⧸ (P ⊔ Ideal.span {x * y})) →ₗ[A] A ⧸ (P ⊔ Ideal.span {x}) :=
    Submodule.mapQ _ _ LinearMap.id (fun a ha => hle ha)
  have hinj : Function.Injective g₁ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro z hz
    induction z using Submodule.Quotient.induction_on with | _ a => ?_
    rw [LinearMap.mem_ker] at hz
    simp only [g₁, Submodule.mapQ_apply, LinearMap.mulLeft_apply,
      Submodule.Quotient.mk_eq_zero] at hz
    simp only [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    obtain ⟨p, hp, r, hr, hpr⟩ := Submodule.mem_sup.mp hz
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    have hm : x * (a - c * y) ∈ P := by
      have e : x * (a - c * y) = p := by linear_combination hpr.symm
      rw [e]; exact hp
    have ha : a - c * y ∈ P := (‹P.IsPrime›.mem_or_mem hm).resolve_left hx
    have e : a = (a - c * y) + c * y := by ring
    rw [e]
    exact Submodule.add_mem_sup ha (Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩)
  have hsurj : Function.Surjective g₂ := by
    intro z
    induction z using Submodule.Quotient.induction_on with | _ a => ?_
    exact ⟨Submodule.Quotient.mk a, rfl⟩
  have hex : Function.Exact g₁ g₂ := by
    intro z
    induction z using Submodule.Quotient.induction_on with | _ a => ?_
    simp only [g₂, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero,
      Set.mem_range]
    constructor
    · intro ha
      obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.mp ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      refine ⟨Submodule.Quotient.mk c, ?_⟩
      simp only [g₁, Submodule.mapQ_apply, LinearMap.mulLeft_apply]
      rw [Submodule.Quotient.eq]
      have e : x * c - (p + c * x) = -p := by ring
      rw [e]
      exact Submodule.mem_sup_left (P.neg_mem hp)
    · rintro ⟨z, hz⟩
      induction z using Submodule.Quotient.induction_on with | _ c => ?_
      simp only [g₁, Submodule.mapQ_apply, LinearMap.mulLeft_apply] at hz
      rw [Submodule.Quotient.eq] at hz
      have e : a = -(x * c - a) + c * x := by ring
      rw [e]
      exact Submodule.add_mem _ (Submodule.neg_mem _ (hle hz))
        (Submodule.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩))
  exact Module.length_eq_add_of_exact (R := Localization.AtPrime W)
    (LocalizedModule.map W.primeCompl g₁) (LocalizedModule.map W.primeCompl g₂)
    (LocalizedModule.map_injective _ _ hinj) (LocalizedModule.map_surjective _ _ hsurj)
    (LocalizedModule.map_exact _ _ _ hex)

theorem length_localizedQuot_ne_top [IsNoetherianRing A] (J W : Ideal A) [W.IsPrime]
    (hW : W ∈ J.minimalPrimes) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J)) ≠ ⊤ := by
  have : IsNoetherianRing (Localization.AtPrime W) :=
    IsLocalization.isNoetherianRing W.primeCompl _ inferInstance
  have hI : IsLocalRing.maximalIdeal (Localization.AtPrime W) ∈
      (J.map (algebraMap A (Localization.AtPrime W))).minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map W.primeCompl (Localization.AtPrime W) J,
      Set.mem_preimage, Localization.AtPrime.under_maximalIdeal]
    exact hW
  have : IsArtinianRing (Localization.AtPrime W ⧸ J.map (algebraMap A (Localization.AtPrime W))) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hI
  have : IsArtinian (Localization.AtPrime W)
      (Localization.AtPrime W ⧸ J.map (algebraMap A (Localization.AtPrime W))) :=
    isArtinian_of_surjective_algebraMap
      (Ideal.Quotient.mk_surjective (I := J.map (algebraMap A (Localization.AtPrime W))))
  have : IsNoetherian (Localization.AtPrime W)
      (Localization.AtPrime W ⧸ J.map (algebraMap A (Localization.AtPrime W))) :=
    isNoetherian_quotient _
  have := IsLocalization.linearMap_compatibleSMul W.primeCompl
  let e := (IsLocalizedModule.linearEquiv W.primeCompl
    (J.toLocalizedQuotient' (Localization.AtPrime W) W.primeCompl
      (Algebra.linearMap A (Localization.AtPrime W)))
    (LocalizedModule.mkLinearMap W.primeCompl (A ⧸ J))).restrictScalars (Localization.AtPrime W)
  rw [← e.length_eq, Ideal.localized'_eq_map]
  exact Module.length_ne_top

theorem mem_minimalPrimes_sup_span_mul [IsNoetherianRing A] {P W : Ideal A} [P.IsPrime] {x y : A}
    (hy : y ∉ P) (hW : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes) :
    W ∈ (P ⊔ Ideal.span {x * y}).minimalPrimes := by
  have hWp : W.IsPrime := hW.1.1
  have hxW : x ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  refine ⟨⟨hWp, sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr (W.mul_mem_right y hxW))⟩, ?_⟩
  rintro Q ⟨hQp, hQ⟩ hQW
  have hPQ : P ≤ Q := le_sup_left.trans hQ
  rcases hQp.mem_or_mem (hQ (Ideal.mem_sup_right (Ideal.subset_span rfl))) with hxQ | hyQ
  · exact hW.2 ⟨hQp, sup_le hPQ ((Ideal.span_singleton_le_iff_mem _).mpr hxQ)⟩ hQW
  by_contra hWQ
  have hlt : Q < W := lt_of_le_of_ne hQW (fun h => hWQ h.ge)
  have hPQlt : P < Q := lt_of_le_of_ne hPQ (fun h => hy (h ▸ hyQ))
  have hker : RingHom.ker (Ideal.Quotient.mk P) = P := Ideal.mk_ker
  have hQ' : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (hker.le.trans hPQ)
  have hW' : (W.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (hker.le.trans hPW)
  have h0 : (⊥ : Ideal (A ⧸ P)).IsPrime := Ideal.isPrime_bot
  have hcQ : (Q.map (Ideal.Quotient.mk P)).comap (Ideal.Quotient.mk P) = Q := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      hker, sup_eq_left.mpr hPQ]
  have hcW : (W.map (Ideal.Quotient.mk P)).comap (Ideal.Quotient.mk P) = W := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      hker, sup_eq_left.mpr hPW]
  have hcP : (⊥ : Ideal (A ⧸ P)).comap (Ideal.Quotient.mk P) = P := by
    rw [← RingHom.ker_eq_comap_bot, hker]
  have h1 : (⊥ : Ideal (A ⧸ P)) < Q.map (Ideal.Quotient.mk P) :=
    lt_of_le_of_ne bot_le (fun h => hPQlt.ne
      (hcP.symm.trans ((congrArg (Ideal.comap (Ideal.Quotient.mk P)) h).trans hcQ)))
  have h2 : Q.map (Ideal.Quotient.mk P) < W.map (Ideal.Quotient.mk P) :=
    lt_of_le_of_ne (Ideal.map_mono hQW) (fun h => hlt.ne
      (hcQ.symm.trans ((congrArg (Ideal.comap (Ideal.Quotient.mk P)) h).trans hcW)))
  have hb := Ideal.height_add_one_le_of_lt_of_isPrime h1
  have hc := Ideal.height_add_one_le_of_lt_of_isPrime h2
  have hk := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  have h2le : (2 : ℕ∞) ≤ 1 :=
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ (⊥ : Ideal (A ⧸ P)).height + 1 + 1 := by gcongr; positivity
      _ ≤ (Q.map (Ideal.Quotient.mk P)).height + 1 := by gcongr
      _ ≤ 1 := hc.trans hk
  exact absurd h2le (by norm_num)

end General

section Forms

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem divCycle_eq_toNat_multAt {P : Ideal (MRing ι R)} (f g : MRing ι R)
    {W : Ideal (MRing ι R)} [W.IsPrime] (hW : W ∈ (P ⊔ Ideal.span {g}).minimalPrimes)
    (hrel : IsRelevant W) (hle : P ⊔ Ideal.span {g} ≤ P ⊔ Ideal.span {f}) :
    divCycle P f W = ((multAt (P ⊔ Ideal.span {f}) W).toNat : ℤ) := by
  unfold divCycle
  by_cases hfW : P ⊔ Ideal.span {f} ≤ W
  · have hm : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes :=
      ⟨⟨hW.1.1, hfW⟩, fun Q hQ hQW => hW.2 ⟨hQ.1, hle.trans hQ.2⟩ hQW⟩
    rw [dite_eq_left ⟨hm, hrel⟩]
  · rw [dite_eq_right (fun h => hfW h.1.1.2)]
    unfold multAt
    rw [Module.length_eq_zero_iff.mpr (localizedQuot_subsingleton_of_not_le _ W hfW)]
    rfl

end Forms

theorem DivCycleMul.proof : DivCycleMul.Statement := by
  intro R _ _ K _ ι _ P x y hP hx hy
  funext W
  have hxy : x * y ∉ P := fun h => (hP.mem_or_mem h).elim hx hy
  by_cases hrel : IsRelevant W
  swap
  · simp only [Pi.add_apply]
    unfold divCycle
    rw [dite_eq_right (fun h => hrel h.2), dite_eq_right (fun h => hrel h.2), dite_eq_right (fun h => hrel h.2),
      add_zero]
  by_cases hm : W ∈ (P ⊔ Ideal.span {x * y}).minimalPrimes
  · have hW : W.IsPrime := hm.1.1
    have hxle : P ⊔ Ideal.span {x * y} ≤ P ⊔ Ideal.span {x} :=
      sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr
        (Ideal.mul_mem_right y _ (Ideal.mem_span_singleton_self x))) P
    have hyle : P ⊔ Ideal.span {x * y} ≤ P ⊔ Ideal.span {y} :=
      sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr
        (Ideal.mul_mem_left _ x (Ideal.mem_span_singleton_self y))) P
    simp only [Pi.add_apply]
    rw [divCycle_eq_toNat_multAt (x * y) (x * y) hm hrel le_rfl,
      divCycle_eq_toNat_multAt x (x * y) hm hrel hxle,
      divCycle_eq_toNat_multAt y (x * y) hm hrel hyle]
    have htop := length_localizedQuot_ne_top _ W hm
    have hadd := length_localizedQuot_sup_span_mul P W y hx
    unfold multAt
    rw [hadd] at htop ⊢
    rw [ENat.toNat_add (WithTop.add_ne_top.mp htop).1 (WithTop.add_ne_top.mp htop).2]
    push_cast
    ring
  · simp only [Pi.add_apply]
    unfold divCycle
    have hnx : ¬ W ∈ (P ⊔ Ideal.span {x}).minimalPrimes :=
      fun h => hm (mem_minimalPrimes_sup_span_mul hy h)
    have hny : ¬ W ∈ (P ⊔ Ideal.span {y}).minimalPrimes :=
      fun h => hm (mul_comm y x ▸ mem_minimalPrimes_sup_span_mul hx h)
    rw [dite_eq_right (fun h => hm h.1), dite_eq_right (fun h => hnx h.1), dite_eq_right (fun h => hny h.1), add_zero]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSupSpanMultiHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

attribute [local instance] MvPolynomial.weightedGradedAlgebra


open scoped Classical in
theorem isHomogeneous_of_isMultiHomogIdeal' {K : Type*} [DecidableEq K] {ι : K → Type*}
    {R : Type*} [CommRing R] {I : Ideal (MRing ι R)} (hI : IsMultiHomogIdeal I) :
    (by
      classical
      exact I.IsHomogeneous (weightedHomogeneousSubmodule R (blockWeight ι))) := by
  classical
  have e : I = Ideal.span
      {g | ∃ f ∈ I, ∃ b, g = weightedHomogeneousComponent (blockWeight ι) b f} := by
    apply le_antisymm
    · intro f hf
      rw [← sum_weightedHomogeneousComponent (blockWeight ι) f,
        finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
      exact Ideal.sum_mem _ fun b _ => Ideal.subset_span ⟨f, hf, b, rfl⟩
    · rw [Ideal.span_le]
      rintro g ⟨f, hf, b, rfl⟩
      exact hI f hf b
  rw [e]
  refine Ideal.homogeneous_span _ _ fun x hx => ?_
  obtain ⟨f, -, b, rfl⟩ := hx
  exact ⟨b, weightedHomogeneousComponent_isWeightedHomogeneous b f⟩

theorem SupSpanMultiHomog.proof : SupSpanMultiHomog.Statement := by
  classical
  intro R _ K _ ι I x e hI hx
  have h1 := isHomogeneous_of_isMultiHomogIdeal' hI
  have h2 : (Ideal.span {x}).IsHomogeneous (weightedHomogeneousSubmodule R (blockWeight ι)) :=
    Ideal.homogeneous_span _ _ (by
      rintro y rfl
      exact ⟨e, hx⟩)
  have h := h1.sup h2
  intro f hf b
  exact weightedHomogeneousComponent_mem_of_mem R (blockWeight ι) h hf b

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleFiniteSupport
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem DivCycleFiniteSupport.proof : DivCycleFiniteSupport.Statement.{u} := by
  intro R _ _ K _ ι _ P f
  apply Set.Finite.subset (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {f}))
  intro W hW
  by_contra hmin
  apply hW
  unfold divCycle
  rw [dite_eq_right]
  exact fun h => hmin h.1

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialQuotDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem SpecialQuotDim.proof : SpecialQuotDim.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ W hW
  let π : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O)
  have hsurj : Function.Surjective π :=
    MvPolynomial.map_surjective _ IsLocalRing.residue_surjective
  have hker : RingHom.ker π ≤ W := by
    change RingHom.ker (MvPolynomial.map (IsLocalRing.residue O)) ≤ W
    rw [MvPolynomial.ker_map, IsLocalRing.ker_residue,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.map_span,
      Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
    exact hW
  have hcomap : (specialIdeal W).comap π = W := by
    change (W.map π).comap π = W
    rw [Ideal.comap_map_of_surjective' _ hsurj, sup_eq_left.2 hker]
  let f := (Ideal.Quotient.mk (specialIdeal W)).comp π
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective.comp hsurj
  have hkf : RingHom.ker f = W := by
    ext x
    change Ideal.Quotient.mk _ (π x) = 0 ↔ x ∈ W
    rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hcomap]
  exact (ringKrullDim_eq_of_ringEquiv
    ((Ideal.quotEquivOfEq hkf.symm).trans (RingHom.quotientKerEquivOfSurjective hf))).symm

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBridge
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

def VocabMultiHomog.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (s : MRing ι R) (a : K → ℕ),
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a ↔ IsMultiHomog s a

def VocabMultiHomogIdeal.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι R)),
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal P ↔ IsMultiHomogIdeal P

def VocabDivCycle.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι R)) (s : MRing ι R) (W : Ideal (MRing ι R)),
    ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W : ℕ) : ℤ) = divCycle P s W

def IntNumPoint.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (V : Ideal (MRing ι F)) (i : ∀ k, ι k), IsMultiProjPrime V →
    ringKrullDim (MRing ι F ⧸ V) = ((0 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    (∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ V) →
    intNum F V (![] : Fin 0 → K → ℤ) = ReciprocityTheory.ChartRestriction.G.AI.I1.ptDeg V i

def IntNumRatSection.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (n : ℕ) (V : Ideal (MRing ι F)), IsMultiProjPrime V →
    ringKrullDim (MRing ι F ⧸ V) = ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (L : Fin n → K → ℤ) (A : K → ℤ) (f g : MRing ι F) (α β : K → ℕ),
      IsMultiHomog f α → IsMultiHomog g β → f ∉ V → g ∉ V → (∀ k, (α k : ℤ) - β k = A k) →
      intNum F V (Fin.snoc (α := fun _ => K → ℤ) L A) =
        cycEval (fun W => intNum F W L) (ratDiv V f g)

def IntNumIsFieldIntersection.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)],
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection (F := F) (ι := ι) (fun V _ L => intNum F V L)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.MemOfMemSupportDivCycle
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR

open MvPolynomial Module ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

section Lengths

end Lengths

section Models

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def redMap : MRingOver O ι →+* MRingOver (IsLocalRing.ResidueField O) ι :=
  MvPolynomial.map (IsLocalRing.residue O)

def IsModelOver (P : Ideal (MRingOver O ι)) (d : ℕ) : Prop :=
  IsMultiProjPrime P ∧ P.comap (C : O →+* MRingOver O ι) = ⊥ ∧
    ringKrullDim (MRingOver O ι ⧸ P) = ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞)

def intCyc {R : Type*} [CommRing R] (Z : Ideal (MRingOver R ι) →₀ ℕ) : Ideal (MRingOver R ι) →₀ ℤ :=
  Finsupp.mapRange (fun m : ℕ => (m : ℤ)) Nat.cast_zero Z

def specCyc (ϖ : O) (P : Ideal (MRingOver O ι)) : Ideal (MRingOver O ι) →₀ ℕ :=
  divCycle P (C ϖ)

def divO (P : Ideal (MRingOver O ι)) (f g : MRingOver O ι) : Ideal (MRingOver O ι) →₀ ℤ :=
  intCyc (divCycle P f) - intCyc (divCycle P g)

def redEval (J : Ideal (MRingOver (IsLocalRing.ResidueField O) ι) → ℤ)
    (Z : Ideal (MRingOver O ι) →₀ ℤ) : ℤ :=
  Z.sum fun W m => m * J (W.map redMap)

end Models


section Inhabitants

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]


omit [Fintype K] [IsDomain O] [IsDiscreteValuationRing O] in
theorem isMultiHomog_C (a : O) : IsMultiHomog (C a : MRingOver O ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hm
  split_ifs at hm with h0
  · subst h0; simp
  · exact absurd rfl hm


end Inhabitants

section LengthInhabitants

open IsLocalRing

end LengthInhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsVerticalComponentFibre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

def VerticalComponentFibre.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d →
    ∀ (f : MRing ι O) (b : K → ℕ), IsMultiHomog f b → f ∉ P →
    ∀ W ∈ (P ⊔ Ideal.span {f}).minimalPrimes, IsRelevant W → (C ϖ : MRing ι O) ∈ W →
      IsMultiProjPrime (specialIdeal W) ∧
        ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) =
          ((d + Fintype.card K : ℕ) : WithBot ℕ∞)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMultAtOfSaturated
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

section General

variable {A : Type*} [CommRing A]

theorem mem_minimalPrimes_of_saturated (J Q : Ideal A) [Q.IsPrime] (hJQ : J ≤ Q)
    (hsat : ∀ q ∈ Q, ∃ s ∉ Q, s * q ∈ J) : Q ∈ J.minimalPrimes := by
  refine ⟨⟨‹Q.IsPrime›, hJQ⟩, fun W hW hWQ q hq => ?_⟩
  obtain ⟨s, hs, hsq⟩ := hsat q hq
  exact (hW.1.mem_or_mem (hW.2 hsq)).resolve_left (fun h => hs (hWQ h))

theorem localizedQuot_map_bijective_of_saturated (J Q : Ideal A) [Q.IsPrime] (hJQ : J ≤ Q)
    (hsat : ∀ q ∈ Q, ∃ s ∉ Q, s * q ∈ J) :
    Function.Bijective (LocalizedModule.map Q.primeCompl
      (Submodule.mapQ J Q LinearMap.id (fun _ ha => hJQ ha) : (A ⧸ J) →ₗ[A] A ⧸ Q)) := by
  refine ⟨?_, LocalizedModule.map_surjective _ _ ?_⟩
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    induction x using LocalizedModule.induction_on with | h m s => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective m
    rw [LinearMap.mem_ker, LocalizedModule.map_mk] at hx
    have haQ : a ∈ Q := localizedQuotient_mk_eq_zero Q a s hx
    obtain ⟨t, ht, hta⟩ := hsat a haQ
    rw [Submodule.mem_bot, ← LocalizedModule.zero_mk (1 : Q.primeCompl), LocalizedModule.mk_eq]
    refine ⟨⟨t, ht⟩, ?_⟩
    rw [smul_zero, smul_zero, one_smul, Submonoid.smul_def, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hta
  · intro z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨Ideal.Quotient.mk J a, rfl⟩

end General

universe u

theorem MultAtOfSaturated.proof : MultAtOfSaturated.Statement.{u} := by
  intro R _ K ι J Q _ hJQ hsat
  refine ⟨mem_minimalPrimes_of_saturated J Q hJQ hsat, ?_⟩
  unfold multAt
  rw [(LinearEquiv.ofBijective _ (localizedQuot_map_bijective_of_saturated J Q hJQ hsat)).length_eq,
    Module.length_eq_one_iff]
  exact localizedQuotient_isSimpleModule Q

end GroundTheory.Heights₂.Heights.NumbersDVR
end
