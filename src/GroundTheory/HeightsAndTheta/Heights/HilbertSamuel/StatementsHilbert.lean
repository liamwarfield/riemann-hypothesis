module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsUnitApprox
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsMoreRest

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Classical

noncomputable section

universe u v

section Objects

variable {K : Type*} [DecidableEq K]

def unitDeg (k : K) : K → ℤ := Pi.single k 1

variable [Fintype K] {ι : K → Type*} {F : Type*} [Field F]

structure IsMultigrading (ι : K → Type*) (M : Type*) [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
    (piece : (K → ℤ) → Submodule F M) : Prop where
  internal : DirectSum.IsInternal piece
  smul_mem : ∀ (v : Σ k, ι k) (m : K → ℤ) (x : M), x ∈ piece m →
    (X v : MRing ι F) • x ∈ piece (m + unitDeg v.1)

def modMultAt {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M] [Module (MRing ι R) M]
    (W : Ideal (MRing ι R)) [W.IsPrime] : ℕ∞ :=
  Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl M)


open Classical in
def topCycleNum (F : Type*) [Field F] (ι : K → Type*) (M : Type*) [AddCommGroup M] [Module (MRing ι F) M] (d : ℕ) (bs : Fin d → K → ℤ) :
    ℤ :=
  ∑ᶠ W : Ideal (MRing ι F),
    if h : IsMultiProjPrime W ∧ Module.annihilator (MRing ι F) M ≤ W ∧
        ringKrullDim (MRing ι F ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) then
      haveI : W.IsPrime := h.1.isPrime
      ((modMultAt M W).toNat : ℤ) * intNum F W bs
    else 0

end Objects

def MultigradedFiltration.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (M : Type v) [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
    [IsScalarTower F (MRing ι F) M] [Module.Finite (MRing ι F) M]
    (piece : (K → ℤ) → Submodule F M), IsMultigrading ι M piece →
    ∃ (n : ℕ) (N : Fin (n + 1) → Submodule (MRing ι F) M) (x : Fin n → M) (c : Fin n → K → ℤ)
      (q : Fin n → Ideal (MRing ι F)),
      N 0 = ⊥ ∧ N (Fin.last n) = ⊤ ∧
      (∀ j : Fin n, x j ∈ piece (c j) ∧
        N j.succ = N j.castSucc ⊔ Submodule.span (MRing ι F) {x j} ∧
        (q j).IsPrime ∧ IsMultiHomogIdeal (q j) ∧
        ∀ s : MRing ι F, s • x j ∈ N j.castSucc ↔ s ∈ q j) ∧
      ∀ (W : Ideal (MRing ι F)) (hW : W ∈ (Module.annihilator (MRing ι F) M).minimalPrimes),
        (((Finset.univ.filter fun j => q j = W).card : ℕ) : ℕ∞) =
          haveI : W.IsPrime := hW.1.1
          modMultAt M W

def HilbertDimZero.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)), IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∃ a₀ : ℕ, ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      hilbFn q (fun k => (a k : ℤ)) = intNum F q (![] : Fin 0 → K → ℤ)

def HilbertPrime.AtDim (d : ℕ) : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)), IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∃ (a₀ : ℕ) (C : ℝ), ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |(hilbFn q (fun k => (a k : ℤ)) : ℝ) -
          (intNum F q (fun _ : Fin d => fun k => (a k : ℤ)) : ℝ) / d.factorial| ≤
        C * ((∑ k, (a k : ℝ)) + 1) ^ ((d : ℝ) - 1)

def HilbertPrime.Statement : Prop := ∀ d : ℕ, HilbertPrime.AtDim.{u} d

def HilbertModule.AtDim (d : ℕ) : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (M : Type v) [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
    [IsScalarTower F (MRing ι F) M] [Module.Finite (MRing ι F) M]
    (piece : (K → ℤ) → Submodule F M), IsMultigrading ι M piece →
    (∀ W : Ideal (MRing ι F), IsMultiProjPrime W → Module.annihilator (MRing ι F) M ≤ W →
      ringKrullDim (MRing ι F ⧸ W) ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞)) →
    ∃ (a₀ : ℕ) (C : ℝ), ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |(Module.finrank F (piece fun k => (a k : ℤ)) : ℝ) -
          (topCycleNum F ι M d (fun _ : Fin d => fun k => (a k : ℤ)) : ℝ) / d.factorial| ≤
        C * ((∑ k, (a k : ℝ)) + 1) ^ ((d : ℝ) - 1)

def ModulesFromPrimes.Statement : Prop :=
  ∀ d : ℕ, (∀ e ≤ d, HilbertPrime.AtDim.{u} e) → HilbertModule.AtDim.{u, v} d

def HilbertIncrement.Statement : Prop :=
  ∀ d : ℕ, HilbertModule.AtDim.{u, u} d →
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)), IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ b : K, ∃ (a₀ : ℕ) (C : ℝ), ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |((hilbFn q (fun k => (a k : ℤ)) - hilbFn q ((fun k => (a k : ℤ)) - unitDeg b) : ℤ) : ℝ) -
          (intNum F q (Matrix.vecCons (unitDeg b) fun _ : Fin d => fun k => (a k : ℤ)) : ℝ) /
            d.factorial| ≤
        C * ((∑ k, (a k : ℝ)) + 1) ^ ((d : ℝ) - 1)


open Classical in
def IntersectionRecursion.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)) (d : ℕ), IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (b : K) (i : ι b), (X ⟨b, i⟩ : MRing ι F) ∉ q → ∀ bs : Fin d → K → ℤ,
      intNum F q (Matrix.vecCons (unitDeg b) bs) =
        ∑ᶠ W : Ideal (MRing ι F),
          if h : IsMultiProjPrime W ∧ q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)} ≤ W ∧
              ringKrullDim (MRing ι F ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) then
            haveI : W.IsPrime := h.1.isPrime
            ((multAt (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)}) W).toNat : ℤ) * intNum F W bs
          else 0

def MixedNumberPolynomial.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)) (d : ℕ), IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
    (∀ (σ : Equiv.Perm (Fin d)) (bs : Fin d → K → ℤ), intNum F q (bs ∘ σ) = intNum F q bs) ∧
    ∀ (bs : Fin d → K → ℤ) (j : Fin d) (x y : K → ℤ),
      intNum F q (Function.update bs j (x + y)) =
        intNum F q (Function.update bs j x) + intNum F q (Function.update bs j y)

def MultigradedHilbertPolynomial.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)) (d : ℕ), IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∃ (p : MvPolynomial K ℚ) (a₀ : ℕ), p.totalDegree ≤ d ∧
      ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
        (hilbFn q (fun k => (a k : ℤ)) : ℚ) = MvPolynomial.eval (fun k => (a k : ℚ)) p

def RankOfSections.Statement : Prop :=
  ∀ (ι₀ : Type) [Fintype ι₀] (q : Ideal (MRing (fun _ : Unit => ι₀) ℚ)) (D : ℕ),
    IsMultiProjPrime q →
    ringKrullDim (MRing (fun _ : Unit => ι₀) ℚ ⧸ q) = ((D + 1 : ℕ) : WithBot ℕ∞) →
    ∃ C : ℝ, ∀ n : ℕ,
      |(hilbFn q (fun _ => (n : ℤ)) : ℝ) -
          (intNum ℚ q (fun _ : Fin D => fun _ => (1 : ℤ)) : ℝ) * (n : ℝ) ^ D / D.factorial| ≤
        C * ((n : ℝ) + 1) ^ ((D : ℝ) - 1)

section Examples

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {F : Type u} [Field F]

def intWeight : (Σ k, ι k) → K → ℤ := fun v => unitDeg v.1

def ringPiece (m : K → ℤ) : Submodule F (MRing ι F) :=
  weightedHomogeneousSubmodule F (intWeight (ι := ι)) m


omit [∀ k, Fintype (ι k)] in
theorem isMultigrading_ring : IsMultigrading ι (MRing ι F) (ringPiece (F := F) (ι := ι)) := by
  refine ⟨(weightedDecomposition F (intWeight (ι := ι))).isInternal, ?_⟩
  intro v m x hx
  change IsWeightedHomogeneous (intWeight (ι := ι)) x m at hx
  rw [smul_eq_mul]
  change IsWeightedHomogeneous (intWeight (ι := ι)) (X v * x) (m + unitDeg v.1)
  rw [add_comm m (unitDeg v.1)]
  exact (isWeightedHomogeneous_X F (intWeight (ι := ι)) v).mul hx

end Examples

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPrimeComplexRadical
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial TensorProduct

noncomputable section

theorem isReduced_tensor_domain_of_formallyEtale (E L D : Type*) [Field E] [Field L] [Algebra E L]
    [Algebra.FormallyEtale E L] [Algebra.EssFiniteType E L] [CommRing D] [IsDomain D]
    [Algebra E D] : IsReduced (L ⊗[E] D) := by
  have : IsReduced (FractionRing D ⊗[E] L) :=
    Algebra.FormallyUnramified.isReduced_of_field (FractionRing D) (FractionRing D ⊗[E] L)
  have : IsReduced (L ⊗[E] FractionRing D) :=
    isReduced_of_injective (Algebra.TensorProduct.comm E L (FractionRing D))
      (AlgEquiv.injective _)
  exact isReduced_of_injective
    (Algebra.TensorProduct.map (AlgHom.id E L) (IsScalarTower.toAlgHom E D (FractionRing D)))
    (Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective D _))


open scoped IntermediateField.algebraAdjoinAdjoin in
theorem isReduced_tensor_field_of_perfectField (K L F : Type*) [Field K] [PerfectField K]
    [Field L] [Algebra K L] [Algebra.EssFiniteType K L] [Field F] [Algebra K F] :
    IsReduced (L ⊗[K] F) := by
  classical
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K L
  let R := Algebra.adjoin K (s : Set L)
  let E := IntermediateField.adjoin K (s : Set L)
  letI : Algebra R E :=
    (Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin K (s : Set L))).toAlgebra
  have : IsScalarTower K R E := IsScalarTower.of_algebraMap_eq' rfl
  have : FaithfulSMul R E :=
    Subalgebra.inclusion.faithfulSMul (IntermediateField.algebra_adjoin_le_adjoin K (s : Set L))
  have : IsFractionRing R E := IsFractionRing.of_field _ _ fun ⟨_, h⟩ => by
    obtain ⟨x, hx, y, hy, eq⟩ := IntermediateField.mem_adjoin_iff_div.mp h
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, Subtype.ext eq⟩

  have eR : R ≃ₐ[K] MvPolynomial s K :=
    (Subalgebra.equivOfEq R (Algebra.adjoin K (Set.range ((↑) : s → L))) (by simp [R])).trans hs.1.aevalEquiv.symm
  have hRF : IsDomain (R ⊗[K] F) :=
    ((Algebra.TensorProduct.comm K R F).toRingEquiv.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[K] F) eR).toRingEquiv.trans
        (MvPolynomial.algebraTensorAlgEquiv (σ := s) K F).toRingEquiv)).toMulEquiv.isDomain

  have hT : IsDomain (E ⊗[R] (R ⊗[K] F)) := by
    letI : Algebra (R ⊗[K] F) (E ⊗[R] (R ⊗[K] F)) := Algebra.TensorProduct.rightAlgebra
    have := IsLocalization.tensorRight (R := R) (S := R ⊗[K] F) (A := E) (nonZeroDivisors R)
    refine IsLocalization.isDomain_of_le_nonZeroDivisors (R := R ⊗[K] F)
      (M := Algebra.algebraMapSubmonoid (R ⊗[K] F) (nonZeroDivisors R)) (E ⊗[R] (R ⊗[K] F)) ?_
    rintro _ ⟨r, hr, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro h0
    have hinj : Function.Injective (algebraMap R (R ⊗[K] F)) :=
      Algebra.TensorProduct.includeLeft_injective (S := R) (RingHom.injective (algebraMap K F))
    exact nonZeroDivisors.ne_zero hr (hinj (by simpa using h0))

  have : IsDomain (E ⊗[K] F) :=
    (Algebra.TensorProduct.cancelBaseChange K R R E F).symm.toMulEquiv.isDomain

  have : Algebra.FormallyEtale E L := Algebra.FormallyEtale.of_isSeparable E L
  have : Algebra.EssFiniteType E L := Algebra.EssFiniteType.of_comp K E L
  have := isReduced_tensor_domain_of_formallyEtale E L (E ⊗[K] F)
  exact isReduced_of_injective (Algebra.TensorProduct.cancelBaseChange K E E L F).symm
    (AlgEquiv.injective _)

theorem isReduced_tensor_domain_of_perfectField (K A F : Type*) [Field K] [PerfectField K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] [Field F] [Algebra K F] :
    IsReduced (F ⊗[K] A) := by
  have : Algebra.EssFiniteType A (FractionRing A) :=
    .of_isLocalization _ (nonZeroDivisors A)
  have : Algebra.EssFiniteType K (FractionRing A) := .comp K A _
  have := isReduced_tensor_field_of_perfectField K (FractionRing A) F
  have : IsReduced (F ⊗[K] FractionRing A) :=
    isReduced_of_injective (Algebra.TensorProduct.comm K F (FractionRing A)) (AlgEquiv.injective _)
  exact isReduced_of_injective
    (Algebra.TensorProduct.map (AlgHom.id K F) (IsScalarTower.toAlgHom K A (FractionRing A)))
    (Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective A _))

theorem isRadical_map_of_isPrime_of_perfectField (K F : Type*) [Field K] [PerfectField K]
    [Field F] [Algebra K F] (σ : Type*) [Fintype σ] (Q : Ideal (MvPolynomial σ K))
    [Q.IsPrime] : (Q.map (MvPolynomial.map (algebraMap K F))).IsRadical := by
  rw [Ideal.isRadical_iff_quotient_reduced]
  let e₀ := MvPolynomial.algebraTensorAlgEquiv (σ := σ) K F
  have hJ : Q.map (MvPolynomial.map (algebraMap K F)) =
      (Q.map (Algebra.TensorProduct.includeRight (R := K) (A := F)).toRingHom).map
        e₀.toRingEquiv.toRingHom := by
    rw [Ideal.map_map]
    congr 1
    refine RingHom.ext fun p => ?_
    simp [e₀, MvPolynomial.algebraTensorAlgEquiv_tmul]
  let e : F ⊗[K] (MvPolynomial σ K ⧸ Q) ≃+*
      MvPolynomial σ F ⧸ Q.map (MvPolynomial.map (algebraMap K F)) :=
    (Algebra.TensorProduct.tensorQuotientEquiv (R := K) K (MvPolynomial σ K) F Q).toRingEquiv.trans
      (Ideal.quotientEquiv _ _ e₀.toRingEquiv (hJ.trans rfl))
  have := isReduced_tensor_domain_of_perfectField K (MvPolynomial σ K ⧸ Q) F
  exact isReduced_of_injective e.symm e.symm.injective

theorem PrimeComplexRadical.proof : PrimeComplexRadical.Statement := by
  intro σ _ P hP
  by_cases hZ : ∃ n : ℤ, n ≠ 0 ∧ C n ∈ P
  · obtain ⟨n, hn, hnP⟩ := hZ
    have htop : P.map (MvPolynomial.map (Int.castRingHom ℂ)) = ⊤ := by
      apply Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hnP)
      rw [MvPolynomial.map_C]
      exact (isUnit_iff_ne_zero.mpr (by simpa using hn)).map C
    rw [htop]
    exact fun x _ => Submodule.mem_top
  · push Not at hZ
    let _ := MvPolynomial.algebraMvPolynomial (σ := σ) (R := ℤ) (S := ℚ)
    let M := (nonZeroDivisors ℤ).map (C (σ := σ) (R := ℤ))
    have : IsLocalization M (MvPolynomial σ ℚ) := MvPolynomial.isLocalization _ _
    let Q := P.map (algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℚ))
    have hQ : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M _ P hP (by
      rw [Set.disjoint_left]
      rintro _ ⟨n, hn, rfl⟩ hnP
      exact hZ n (nonZeroDivisors.ne_zero hn) hnP)
    have hmap : P.map (MvPolynomial.map (Int.castRingHom ℂ)) =
        Q.map (MvPolynomial.map (algebraMap ℚ ℂ)) := by
      rw [Ideal.map_map]
      congr 1
      refine RingHom.ext fun p => ?_
      change _ = MvPolynomial.map (algebraMap ℚ ℂ) (MvPolynomial.map (algebraMap ℤ ℚ) p)
      rw [MvPolynomial.map_map,
        show (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ) = Int.castRingHom ℂ from RingHom.ext_int _ _]
    rw [hmap]
    exact isRadical_map_of_isPrime_of_perfectField ℚ ℂ σ Q

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionNormSqLevi
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def LeviLogFlat.Statement : Prop :=
  ∀ (J : Type) [Fintype J] (P u : (J → ℂ) → ℝ) (z w : J → ℂ),
    ContDiffAt ℝ 2 P z → ContDiffAt ℝ 2 u z → 0 < P z → u z = 0 → fderiv ℝ u z w = 0 →
    fderiv ℝ u z (Complex.I • w) = 0 → leviForm u z w = 0 →
    leviForm (fun x => Real.log (P x + u x)) z w = leviForm (fun x => Real.log (P x)) z w

def LeviHolPerturb.Statement : Prop :=
  ∀ (J : Type) [Fintype J] (ξ : (J → ℂ) → ℝ) (a φ : (J → ℂ) → ℂ) (z w : J → ℂ),
    ContDiffAt ℝ 2 ξ z → AnalyticAt ℂ a z → AnalyticAt ℂ φ z → φ z = 0 → fderiv ℂ φ z w = 0 →
    ContDiffAt ℝ 2 (fun x => ξ x * (‖a x + φ x‖ ^ 2 - ‖a x‖ ^ 2)) z ∧
      ξ z * (‖a z + φ z‖ ^ 2 - ‖a z‖ ^ 2) = 0 ∧
      fderiv ℝ (fun x => ξ x * (‖a x + φ x‖ ^ 2 - ‖a x‖ ^ 2)) z w = 0 ∧
      fderiv ℝ (fun x => ξ x * (‖a x + φ x‖ ^ 2 - ‖a x‖ ^ 2)) z (Complex.I • w) = 0 ∧
      leviForm (fun x => ξ x * (‖a x + φ x‖ ^ 2 - ‖a x‖ ^ 2)) z w = 0

def LeviCompHol.Statement : Prop :=
  ∀ (E F : Type) [Fintype E] [Fintype F] (g : (E → ℂ) → (F → ℂ)) (φ : (F → ℂ) → ℝ) (x w : E → ℂ),
    AnalyticAt ℂ g x → ContDiffAt ℝ 2 φ (g x) →
    leviForm (fun y => φ (g y)) x w = leviForm φ (g x) (fderiv ℂ g x w)

def LeviFSInvariant.Statement : Prop :=
  ∀ (M : Type) [Fintype M] (a b : M → ℂ) (c μ : ℂ), a ≠ 0 → c ≠ 0 →
    leviForm (fun u : M → ℂ => Real.log (∑ j, ‖u j‖ ^ 2) / 2) (c • a) (c • b + μ • a) =
      leviForm (fun u : M → ℂ => Real.log (∑ j, ‖u j‖ ^ 2) / 2) a b

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComplexMinimalPrimesContract
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem mvPolynomial_int_complex_flat (σ : Type) :
    Module.Flat (MvPolynomial σ ℤ) (MvPolynomial σ ℂ) :=
  Module.Flat.isBaseChange ℤ (MvPolynomial σ ℤ) ℂ (MvPolynomial σ ℂ)
    (Algebra.IsPushout.out (R := ℤ) (S := MvPolynomial σ ℤ) (R' := ℂ) (S' := MvPolynomial σ ℂ))

theorem algebraMap_mvPolynomial_int_complex (σ : Type) :
    algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℂ) = MvPolynomial.map (Int.castRingHom ℂ) := by
  rw [MvPolynomial.algebraMap_def]
  congr 1

theorem ComplexMinimalPrimesContract.proof : ComplexMinimalPrimesContract.Statement := by
  intro σ _ P hP Q hQ
  have := hP
  have hflat := mvPolynomial_int_complex_flat σ
  have hAlg := algebraMap_mvPolynomial_int_complex σ
  have : Q.IsPrime := hQ.1.1
  have hPQ : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ Q := hQ.1.2
  have hle : P ≤ Q.comap (MvPolynomial.map (Int.castRingHom ℂ)) :=
    Ideal.map_le_iff_le_comap.mp hPQ
  have : (Q.comap (MvPolynomial.map (Int.castRingHom ℂ))).IsPrime := Ideal.comap_isPrime _ Q
  have : Q.LiesOver (Q.comap (MvPolynomial.map (Int.castRingHom ℂ))) :=
    ⟨by rw [Ideal.under, Ideal.comap, hAlg]; rfl⟩
  obtain ⟨Q', hQ'Q, hQ'prime, hQ'over⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (R := MvPolynomial σ ℤ) (p := P)
      (q := Q.comap (MvPolynomial.map (Int.castRingHom ℂ))) Q hle
  have hQ'P : Q'.comap (MvPolynomial.map (Int.castRingHom ℂ)) = P := by
    have := hQ'over.over
    rw [Ideal.under, hAlg] at this
    exact this.symm
  have hmapQ' : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ Q' :=
    Ideal.map_le_iff_le_comap.mpr hQ'P.ge
  have hQQ' : Q ≤ Q' := hQ.2 ⟨hQ'prime, hmapQ'⟩ hQ'Q
  rw [← le_antisymm hQ'Q hQQ']
  exact hQ'P

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootGridLower
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Finset

theorem RootGridLower.sum_fin_pow {M : ℕ} (hM : 0 < M) {ω : ℂ} (hω : IsPrimitiveRoot ω M)
    {a b : ℕ} (ha : a < M) (hb : b < M) :
    ∑ t : Fin M, (ω ^ a * (ω ^ b)⁻¹) ^ (t : ℕ) = if a = b then (M : ℂ) else 0 := by
  have hω0 : ω ≠ 0 := hω.ne_zero hM.ne'
  rw [Fin.sum_univ_eq_sum_range (fun t => (ω ^ a * (ω ^ b)⁻¹) ^ t)]
  split_ifs with hab
  · subst hab
    simp [mul_inv_cancel₀ (pow_ne_zero _ hω0)]
  · have hz : ω ^ a * (ω ^ b)⁻¹ ≠ 1 := by
      intro h
      apply hab
      apply hω.pow_inj ha hb
      have := congrArg (· * ω ^ b) h
      simpa [mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hω0)] using this
    rw [geom_sum_eq hz]
    have h1 : (ω ^ a * (ω ^ b)⁻¹) ^ M = 1 := by
      rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm a, mul_comm b, pow_mul, pow_mul,
        hω.pow_eq_one]
      simp
    simp [h1]

theorem RootGridLower.average {e M : ℕ} (hM : 0 < M) {ω : ℂ} (hω : IsPrimitiveRoot ω M)
    (Q : MvPolynomial (Fin e) ℤ) (hdeg : ∀ i, Q.degreeOf i < M) (j : Fin e →₀ ℕ)
    (hj : ∀ i, j i < M) :
    ∑ k : Fin e → Fin M, eval (fun i => ω ^ (k i : ℕ)) (map (Int.castRingHom ℂ) Q) *
        ∏ i, ((ω ^ j i)⁻¹) ^ (k i : ℕ) = (M : ℂ) ^ e * ((Q.coeff j : ℤ) : ℂ) := by
  classical
  simp_rw [eval_map, eval₂_eq', Finset.sum_mul]
  rw [Finset.sum_comm]
  have key : ∀ d ∈ Q.support, ∑ k : Fin e → Fin M,
      (Int.castRingHom ℂ) (Q.coeff d) * (∏ i, (ω ^ (k i : ℕ)) ^ d i) *
        ∏ i, ((ω ^ j i)⁻¹) ^ (k i : ℕ) =
      ((Q.coeff d : ℤ) : ℂ) * if d = j then (M : ℂ) ^ e else 0 := by
    intro d hd
    have hdM : ∀ i, d i < M := fun i => lt_of_le_of_lt (monomial_le_degreeOf i hd) (hdeg i)
    have hprod : ∀ k : Fin e → Fin M, (∏ i, (ω ^ (k i : ℕ)) ^ d i) * ∏ i, ((ω ^ j i)⁻¹) ^ (k i : ℕ)
        = ∏ i, (ω ^ d i * (ω ^ j i)⁻¹) ^ (k i : ℕ) := by
      intro k
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (k i : ℕ)]
    simp_rw [mul_assoc, hprod, ← Finset.mul_sum]
    congr 1
    rw [← Fintype.prod_sum (fun i (t : Fin M) => (ω ^ d i * (ω ^ j i)⁻¹) ^ (t : ℕ))]
    simp_rw [RootGridLower.sum_fin_pow hM hω (hdM _) (hj _)]
    split_ifs with hdj
    · subst hdj; simp
    · obtain ⟨i, hi⟩ : ∃ i, d i ≠ j i := by
        by_contra h
        push Not at h
        exact hdj (Finsupp.ext h)
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  rw [Finset.sum_congr rfl key]
  simp_rw [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with hjs
  · simp [mul_comm]
  · rw [MvPolynomial.notMem_support_iff.mp hjs]; simp

theorem RootGridLower.of_pos {e M : ℕ} (hM : 0 < M) (Q : MvPolynomial (Fin e) ℤ) (hQ : Q ≠ 0)
    (hdeg : ∀ i, Q.degreeOf i < M) :
    ∃ ζ : Fin e → ℂ, (∀ i, ζ i ^ M = 1) ∧ 1 ≤ ‖eval ζ (map (Int.castRingHom ℂ) Q)‖ := by
  classical
  have hω := Complex.isPrimitiveRoot_exp M hM.ne'
  set ω := Complex.exp (2 * Real.pi * Complex.I / M)
  obtain ⟨j, hj⟩ : Q.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]; exact hQ
  have hjM : ∀ i, j i < M := fun i => lt_of_le_of_lt (monomial_le_degreeOf i hj) (hdeg i)
  have hc : (1 : ℝ) ≤ ‖((Q.coeff j : ℤ) : ℂ)‖ := by
    rw [Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs (MvPolynomial.mem_support_iff.mp hj)
  have hω1 : ‖ω‖ = 1 := hω.norm'_eq_one hM.ne'
  by_contra hne
  push Not at hne
  have hlt : ∀ k : Fin e → Fin M,
      ‖eval (fun i => ω ^ (k i : ℕ)) (map (Int.castRingHom ℂ) Q)‖ < 1 := by
    intro k
    refine hne _ fun i => ?_
    rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  have hne' : (Finset.univ : Finset (Fin e → Fin M)).Nonempty :=
    ⟨fun i => ⟨j i, hjM i⟩, Finset.mem_univ _⟩
  have hupper : ‖(M : ℂ) ^ e * ((Q.coeff j : ℤ) : ℂ)‖ < (M : ℝ) ^ e := by
    rw [← RootGridLower.average hM hω Q hdeg j hjM]
    calc ‖∑ k : Fin e → Fin M, eval (fun i => ω ^ (k i : ℕ)) (map (Int.castRingHom ℂ) Q) *
            ∏ i, ((ω ^ j i)⁻¹) ^ (k i : ℕ)‖
        ≤ ∑ k : Fin e → Fin M, ‖eval (fun i => ω ^ (k i : ℕ)) (map (Int.castRingHom ℂ) Q) *
            ∏ i, ((ω ^ j i)⁻¹) ^ (k i : ℕ)‖ := norm_sum_le _ _
      _ = ∑ k : Fin e → Fin M, ‖eval (fun i => ω ^ (k i : ℕ)) (map (Int.castRingHom ℂ) Q)‖ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          simp [norm_prod, hω1]
      _ < ∑ _k : Fin e → Fin M, (1 : ℝ) := Finset.sum_lt_sum_of_nonempty hne' fun k _ => hlt k
      _ = (M : ℝ) ^ e := by simp
  have hlower : (M : ℝ) ^ e ≤ ‖(M : ℂ) ^ e * ((Q.coeff j : ℤ) : ℂ)‖ := by
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    exact le_mul_of_one_le_right (by positivity) hc
  linarith

theorem RootGridLower.proof : RootGridLower.Statement := by
  intro e m Q hQ hdeg
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain ⟨ζ, -, hζ⟩ := RootGridLower.of_pos Nat.one_pos Q hQ
      (fun i => lt_trans (hdeg i) Nat.one_pos)
    exact ⟨ζ, fun i => pow_zero _, hζ⟩
  · exact RootGridLower.of_pos hm Q hQ hdeg

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPolyNonvanishDense
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

theorem PolyNonvanishDense.proof : PolyNonvanishDense.Statement := by
  intro e D hD
  rw [dense_iff_inter_open]
  rintro U hU ⟨y₀, hy₀⟩
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU y₀ hy₀
  have hzero : map (algebraMap ℚ ℂ) D = 0 := by
    refine funext_set (fun j => Metric.ball (y₀ j) ε)
      (fun j => infinite_of_mem_nhds (y₀ j) (Metric.ball_mem_nhds _ hε)) fun y hy => ?_
    rw [← ball_pi y₀ hε] at hy
    have hyU := hball hy
    rw [map_zero, eval_map, ← aeval_def]
    by_contra hyD
    exact (Set.eq_empty_iff_forall_notMem.mp hne) y ⟨hyU, hyD⟩
  exact hD (map_injective _ (algebraMap ℚ ℂ).injective (by rw [hzero, map_zero]))

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNoetherProjection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

theorem NoetherProjection.proof : NoetherProjection.Statement := by
  intro σ _ P hP
  have : Nontrivial (MvPolynomial σ ℚ ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr hP
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg ℚ (MvPolynomial σ ℚ ⧸ P)
  choose ℓ hℓ using fun j => Ideal.Quotient.mk_surjective (g (X j))
  have hcomp : (Ideal.Quotient.mkₐ ℚ P).comp (aeval ℓ) = g := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [hℓ]
  have hcompR : (Ideal.Quotient.mk P).comp (aeval ℓ).toRingHom = g.toRingHom := by
    rw [← hcomp]
    rfl
  refine ⟨s, ℓ, ?_, ?_⟩
  · intro q hq
    apply hinj
    rw [map_zero, ← hcomp, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr hq]
  · intro f
    obtain ⟨p, hpm, hp⟩ := hint (Ideal.Quotient.mk P f)
    refine ⟨p, hpm, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, Polynomial.hom_eval₂, hcompR]
    exact hp

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootsBounded
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Filter Topology NNReal

theorem RootsBounded.continuous_aeval {e : ℕ} (g : MvPolynomial (Fin e) ℚ) :
    Continuous fun y : Fin e → ℂ => aeval y g := by
  have h := MvPolynomial.continuous_eval (p := MvPolynomial.map (algebraMap ℚ ℂ) g)
  refine h.congr fun y => ?_
  rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]

theorem RootsBounded.proof : RootsBounded.Statement := by
  intro e G hG y₀
  set m := G.natDegree
  let a : ℕ → (Fin e → ℂ) → ℂ := fun k y => aeval y (G.coeff k)
  refine ⟨((1 + ∑ k ∈ Finset.range m, (‖a k y₀‖₊ + 1) : ℝ≥0) : ℝ), ?_⟩
  have hev : ∀ᶠ y in 𝓝 y₀, ∀ k ∈ Finset.range m, ‖a k y‖₊ ≤ ‖a k y₀‖₊ + 1 := by
    rw [eventually_all_finset]
    intro k _
    have hc : Continuous fun y => ‖a k y‖₊ :=
      (RootsBounded.continuous_aeval (G.coeff k)).nnnorm
    exact hc.continuousAt.eventually (gt_mem_nhds (lt_add_one _)) |>.mono fun _ h => h.le
  filter_upwards [hev] with y hy t ht
  set P : Polynomial ℂ := G.map (aeval y).toRingHom
  have hPm : P.Monic := hG.map _
  have hdeg : P.natDegree = m := hG.natDegree_map _
  have hroot : P.IsRoot t := by
    rw [Polynomial.IsRoot, Polynomial.eval_map]; exact ht
  have hlt := Polynomial.IsRoot.norm_lt_cauchyBound hPm.ne_zero hroot
  have hcb : Polynomial.cauchyBound P ≤ 1 + ∑ k ∈ Finset.range m, (‖a k y₀‖₊ + 1) := by
    rw [Polynomial.cauchyBound, hPm.leadingCoeff, nnnorm_one, div_one, add_comm]
    gcongr
    rw [hdeg]
    refine Finset.sup_le fun k hk => ?_
    have hcoeff : P.coeff k = a k y := by
      simp [P, a, Polynomial.coeff_map]
    rw [hcoeff]
    exact (hy k hk).trans (Finset.single_le_sum (f := fun k => ‖a k y₀‖₊ + 1)
      (fun _ _ => bot_le) hk)
  have : ‖t‖₊ ≤ 1 + ∑ k ∈ Finset.range m, (‖a k y₀‖₊ + 1) := (hlt.trans_le hcb).le
  exact_mod_cast this

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootsNear
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Filter Topology

theorem RootsNear.pow_card_le_norm_prod (s : Multiset ℂ) (t₀ : ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ a ∈ s, ε ≤ dist a t₀) :
    ε ^ Multiset.card s ≤ ‖(s.map fun a => t₀ - a).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ, mul_comm]
    have h1 : ε ≤ ‖t₀ - a‖ := by
      rw [← dist_eq_norm, dist_comm]; exact h a (Multiset.mem_cons_self _ _)
    have h2 := ih (fun b hb => h b (Multiset.mem_cons_of_mem hb))
    exact mul_le_mul h1 h2 (pow_nonneg hε _) (norm_nonneg _)

theorem RootsNear.continuous_eval₂ {e : ℕ} (G : Polynomial (MvPolynomial (Fin e) ℚ)) (t : ℂ) :
    Continuous fun y : Fin e → ℂ => G.eval₂ (aeval y).toRingHom t := by
  simp only [Polynomial.eval₂_eq_sum_range]
  refine continuous_finsetSum _ fun i _ => Continuous.mul ?_ continuous_const
  have : (fun y : Fin e → ℂ => (aeval y).toRingHom (G.coeff i)) =
      fun y => eval y (MvPolynomial.map (algebraMap ℚ ℂ) (G.coeff i)) := by
    funext y
    simp [MvPolynomial.eval_map, MvPolynomial.aeval_def]
  rw [this]
  exact MvPolynomial.continuous_eval _

theorem RootsNear.proof : RootsNear.Statement := by
  intro e G hG y₀ t₀ h0 ε hε
  have hpos : (0 : ℝ) < ε ^ G.natDegree := pow_pos hε _
  have ht := (RootsNear.continuous_eval₂ G t₀).tendsto y₀
  rw [h0] at ht
  filter_upwards [ht (Metric.ball_mem_nhds 0 hpos)] with y hy
  rw [Set.mem_preimage, mem_ball_zero_iff] at hy
  by_contra hno
  push Not at hno
  set p := G.map (aeval y).toRingHom with hp
  have hpm : p.Monic := hG.map _
  have hdeg : p.natDegree = G.natDegree := hG.natDegree_map _
  have hcard : Multiset.card p.roots = p.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hprod := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hpm hcard
  have hev : G.eval₂ (aeval y).toRingHom t₀ = (p.roots.map fun a => t₀ - a).prod := by
    rw [← Polynomial.eval_map, ← hp]
    conv_lhs => rw [← hprod]
    rw [Polynomial.eval_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    simp
  have hle := RootsNear.pow_card_le_norm_prod p.roots t₀ hε.le (fun a ha => by
    have ha' : p.eval₂ (RingHom.id ℂ) a = 0 := by
      rw [Polynomial.eval₂_id]; exact (Polynomial.mem_roots hpm.ne_zero).1 ha
    have := hno a (by rw [hp, Polynomial.eval₂_map] at ha'; simpa using ha')
    exact this)
  rw [hcard, hdeg, ← hev] at hle
  exact absurd hy (not_lt.2 hle)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootsLiftToZeros
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

theorem RootsLiftToZeros.exists_extend {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.IsIntegral R A] (ev : R →+* ℂ) (hker : RingHom.ker (algebraMap R A) ≤ RingHom.ker ev) :
    ∃ χ : A →+* ℂ, χ.comp (algebraMap R A) = ev :=
  _root_.UpperTheory.Reformulated.B.Qi28.exists_extend ev hker

theorem RootsLiftToZeros.proof : RootsLiftToZeros.Statement := by
  intro σ P e ℓ u G hint hG y t ht
  classical
  let A := MvPolynomial σ ℚ ⧸ P
  let α : Polynomial (MvPolynomial (Fin e) ℚ) →+* A :=
    (Ideal.Quotient.mk P).comp (Polynomial.eval₂RingHom (aeval ℓ).toRingHom u)
  letI : Algebra (Polynomial (MvPolynomial (Fin e) ℚ)) A := α.toAlgebra
  have hα : ∀ Q, algebraMap (Polynomial (MvPolynomial (Fin e) ℚ)) A Q =
      Ideal.Quotient.mk P (Q.eval₂ (aeval ℓ).toRingHom u) := fun _ => rfl
  have _ : Algebra.IsIntegral (Polynomial (MvPolynomial (Fin e) ℚ)) A := by
    constructor
    intro a
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨p, hpm, hp⟩ := hint g
    refine ⟨p.map Polynomial.C, hpm.map _, ?_⟩
    have hc : (algebraMap (Polynomial (MvPolynomial (Fin e) ℚ)) A).comp Polynomial.C =
        (Ideal.Quotient.mk P).comp (aeval ℓ).toRingHom :=
      RingHom.ext fun r => by simp [hα]
    rw [Polynomial.eval₂_map, hc, ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem]
    exact hp
  let ev : Polynomial (MvPolynomial (Fin e) ℚ) →+* ℂ := Polynomial.eval₂RingHom (aeval y).toRingHom t
  have hker : RingHom.ker (algebraMap (Polynomial (MvPolynomial (Fin e) ℚ)) A) ≤ RingHom.ker ev := by
    intro Q hQ
    rw [RingHom.mem_ker, hα, Ideal.Quotient.eq_zero_iff_mem] at hQ
    obtain ⟨H, rfl⟩ := hG Q hQ
    rw [RingHom.mem_ker, map_mul]
    change Polynomial.eval₂ (aeval y).toRingHom t G * ev H = 0
    rw [ht, zero_mul]
  obtain ⟨ψ, hψ⟩ := RootsLiftToZeros.exists_extend ev hker
  let χ : MvPolynomial σ ℚ →+* ℂ := ψ.comp (Ideal.Quotient.mk P)
  have hχ : χ = (aeval fun i => χ (X i)).toRingHom :=
    MvPolynomial.ringHom_ext
      (fun r => RingHom.congr_fun (Subsingleton.elim (χ.comp C) ((aeval fun i => χ (X i)).toRingHom.comp C)) r)
      (fun i => by simp)
  have key : ∀ Q, χ (Q.eval₂ (aeval ℓ).toRingHom u) = ev Q := fun Q => RingHom.congr_fun hψ Q
  have hz : ∀ g, aeval (fun i => χ (X i)) g = χ g := fun g => (RingHom.congr_fun hχ g).symm
  refine ⟨fun i => χ (X i), fun g hg => ?_, funext fun j => ?_, ?_⟩
  · rw [hz]
    change ψ (Ideal.Quotient.mk P g) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hg, map_zero]
  · have := key (Polynomial.C (X j))
    simp only [Polynomial.eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X] at this
    rw [hz, this]
    simp [ev]
  · have := key Polynomial.X
    simp only [Polynomial.eval₂_X] at this
    rw [hz, this]
    simp [ev]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRatPrimeDense
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Filter Topology

theorem RatPrimeDense.continuous_aeval {σ : Type} (g : MvPolynomial σ ℚ) :
    Continuous fun z : σ → ℂ => aeval z g := by
  simp_rw [aeval_def, ← eval_map]
  exact MvPolynomial.continuous_eval _

theorem RatPrimeDense.proof (h₁ : FiniteSeparatingModel.Statement) (h₂ : RootsNear.Statement)
    (h₃ : RootsBounded.Statement) (h₄ : PolyNonvanishDense.Statement) : RatPrimeDense.Statement := by
  intro σ _ P f hP hf x hx
  obtain ⟨e, ℓ, u, G, c, D, hG, hc, hD, hint, hGz, hcf, hlift, hsep⟩ := h₁ σ P f x hP hf hx
  set L : (σ → ℂ) → Fin e → ℂ := fun z j => aeval z (ℓ j) with hL
  have hLc : Continuous L := continuous_pi fun j => RatPrimeDense.continuous_aeval (ℓ j)
  have huc : Continuous fun z : σ → ℂ => aeval z u := RatPrimeDense.continuous_aeval u
  have hZ : IsClosed {z : σ → ℂ | ∀ g ∈ P, aeval z g = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun g => isClosed_iInter fun _ =>
      isClosed_eq (RatPrimeDense.continuous_aeval g) continuous_const

  choose p hp hpz using hint
  choose R hR using fun i => h₃ e (p i) (hp i) (L x)
  set Rb : ℝ := ∑ i, max (R i) 0
  have hRb : 0 ≤ Rb := Finset.sum_nonneg fun i _ => le_max_right _ _
  rw [Metric.mem_closure_iff]
  intro ε hε
  set C := ({z : σ → ℂ | ∀ g ∈ P, aeval z g = 0} ∩ Metric.closedBall 0 Rb) ∩ {z | ε ≤ dist z x}
  have hCc : IsCompact C := ((isCompact_closedBall 0 Rb).inter_left hZ).inter_right
    (isClosed_le continuous_const (continuous_id.dist continuous_const))
  set φ : (σ → ℂ) → ℝ := fun z => dist (L z) (L x) + dist (aeval z u) (aeval x u)
  have hφc : Continuous φ :=
    (hLc.dist continuous_const).add (huc.dist continuous_const)
  obtain ⟨δ, hδ, hδC⟩ : ∃ δ > 0, ∀ z ∈ C, δ ≤ φ z := by
    rcases C.eq_empty_or_nonempty with hC | hC
    · exact ⟨1, one_pos, by simp [hC]⟩
    obtain ⟨z₀, hz₀, hmin⟩ := hCc.exists_isMinOn hC hφc.continuousOn
    refine ⟨φ z₀, ?_, fun z hz => hmin hz⟩
    refine lt_of_le_of_ne (add_nonneg dist_nonneg dist_nonneg) fun h0 => ?_
    have h1 := (add_eq_zero_iff_of_nonneg dist_nonneg dist_nonneg).mp h0.symm
    have := hsep z₀ hz₀.1.1 (dist_eq_zero.mp h1.1) (dist_eq_zero.mp h1.2)
    have h2 := hz₀.2
    simp only [Set.mem_ofPred_eq, this, dist_self] at h2
    exact absurd h2 (not_le.mpr hε)

  have hE : ∀ᶠ y in 𝓝 (L x), (∃ t : ℂ, G.eval₂ (aeval y).toRingHom t = 0 ∧
      dist t (aeval x u) < δ / 2) ∧ (∀ i, ∀ t : ℂ, (p i).eval₂ (aeval y).toRingHom t = 0 → ‖t‖ ≤ R i) ∧
      dist y (L x) < δ / 2 :=
    (h₂ e G hG (L x) (aeval x u) (hGz x hx) (δ / 2) (half_pos hδ)).and
      ((eventually_all.mpr hR).and (Metric.ball_mem_nhds _ (half_pos hδ)))
  obtain ⟨y, ⟨⟨t, ht, htd⟩, hyR, hyd⟩, hyB⟩ := (mem_closure_iff_nhds.mp
    (h₄ e (D * c) (mul_ne_zero hD hc) (L x)) _ hE)
  simp only [Set.mem_ofPred_eq, map_mul, mul_ne_zero_iff] at hyB
  obtain ⟨z, hz, hzy, hzt⟩ := hlift y t hyB.1 ht
  have hzL : L z = y := hzy
  refine ⟨z, ⟨hz, hcf z hz (by rw [hzy]; exact hyB.2)⟩, ?_⟩
  have hzR : z ∈ Metric.closedBall 0 Rb := by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hRb]
    intro i
    have := hyR i (z i) (by rw [← hzL]; exact hpz i z hz)
    exact this.trans ((le_max_left _ _).trans
      (Finset.single_le_sum (fun j _ => le_max_right (R j) 0) (Finset.mem_univ i)))
  by_contra hfar
  have hφz : φ z < δ := by
    change dist (L z) (L x) + dist (aeval z u) (aeval x u) < δ
    rw [hzL, hzt]
    linarith
  exact absurd (hδC z ⟨⟨hz, hzR⟩, by show ε ≤ dist z x; rw [dist_comm]; exact not_lt.mp hfar⟩) (not_le.mpr hφz)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComplexTaylor
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Filter Topology Asymptotics ReciprocityTheory.AnForm Matrix

noncomputable section

def ComplexTaylorTwo.Statement : Prop :=
  ∀ (D : ℕ) (ψ : (Fin D → ℂ) → ℝ) (y₀ : Fin D → ℂ), ContDiffAt ℝ 2 ψ y₀ →
    ∃ (a : Fin D → ℂ) (b : Matrix (Fin D) (Fin D) ℂ),
      (fun z : Fin D → ℂ => ψ (y₀ + z) - ψ y₀ - (a ⬝ᵥ z + z ⬝ᵥ (b *ᵥ z)).re -
          (z ⬝ᵥ (hessC ψ y₀ *ᵥ star z)).re) =o[𝓝 0] fun z => ‖z‖ ^ 2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
