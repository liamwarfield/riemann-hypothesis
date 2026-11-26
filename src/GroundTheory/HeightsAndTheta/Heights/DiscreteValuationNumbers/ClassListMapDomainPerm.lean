module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisor
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PNumericalSegre
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundlePullbackVanish

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)

set_option linter.unusedSectionVars false

universe u

section Coord

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem mcIdeal_eq_pointIdeal (R : Type*) [CommRing R] {Ω : Type*} [Field Ω] [Algebra R Ω]
    (y : (Σ k, ι k) → Ω) : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal R y = pointIdeal R y := rfl

end Coord

section Model

variable (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiProjPrime_iff (P : Ideal (MRing ι O)) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime P ↔ IsMultiProjPrime P := by
  have hI := VocabMultiHomogIdeal.proof VocabMultiHomog.proof O K ι P
  constructor
  · rintro ⟨hp, hh, hr⟩
    exact ⟨hp, hI.1 hh, hr⟩
  · rintro ⟨hp, hh, hr⟩
    exact ⟨hp, hI.2 hh, hr⟩

theorem isModelOver_iff (P : Ideal (MRing ι O)) (d : ℕ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O P d ↔ Nonempty K ∧ IsModelOver P d := by
  rw [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver, isMultiProjPrime_iff]
  constructor
  · rintro ⟨hK, hP, ht, hd⟩
    exact ⟨hK, hP, ht, hd⟩
  · rintro ⟨hK, hP, ht, hd⟩
    exact ⟨hK, hP, ht, hd⟩

end Model

section Generic

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {N : ℕ} {V : Type*} [AddCommGroup V] [Module Ω V]

theorem exists_const_iff {ϖ : O} (hϖ : Irreducible ϖ) {x : (Σ k, ι k) → Ω}
    (B : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V) (s : ∀ k, ι k) (v : V) :
    (∃ c : O, c ≠ 0 ∧ algebraMap O Ω c • v ∈ B.lat s) ↔
      ∃ n : ℕ, algebraMap O Ω ϖ ^ n • v ∈ B.lat s := by
  constructor
  · rintro ⟨c, hc, hv⟩
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
    refine ⟨n, ?_⟩
    have h := B.stable s (algebraMap O Ω ↑u⁻¹) (Subalgebra.algebraMap_mem _ _) _ hv
    rwa [smul_smul, ← map_mul, ← mul_assoc, Units.inv_mul, one_mul, map_pow] at h
  · rintro ⟨n, hn⟩
    exact ⟨ϖ ^ n, pow_ne_zero _ hϖ.ne_zero, by rwa [map_pow]⟩

theorem sameGeneric_iff {ϖ : O} (hϖ : Irreducible ϖ) (x : (Σ k, ι k) → Ω)
    (E E' : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SameGeneric O x E E' ↔ SameGenericFibre ϖ E E' := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SameGeneric SameGenericFibre
  refine forall_congr' fun s => imp_congr_right fun _ => and_congr ?_ ?_
  · exact forall₂_congr fun v _ => exists_const_iff hϖ E' s v
  · exact forall₂_congr fun v _ => exists_const_iff hϖ E s v

end Generic

section Cycles

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ratCyc_eq (P : Ideal (MRing ι O)) (f g : MRing ι O) :
    ⇑(IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O P f g) = ratDiv P f g := by
  funext W
  simp [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc, ratDiv, FlagTypings.divCycle_eq]

theorem redIdeal_eq (W : Ideal (MRing ι O)) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W = specialIdeal W := rfl

theorem vEval_eq (J : Ideal (MRing ι (IsLocalRing.ResidueField O)) → ℤ)
    (Z : Ideal (MRing ι O) →₀ ℤ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O J Z = cycEval (fun W => J (specialIdeal W)) ⇑Z := by
  rw [FlagTypings.cycEval_finsupp]
  rfl

end Cycles

section PairNumbers

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem monoList_eq {r : ℕ} {A : Type*} (deg : Fin r → A) (μ : Fin r →₀ ℕ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList deg μ = (IndefiniteRowSideFullHecke.NumbersDVR.monoList μ).map deg := by
  simp [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList, IndefiniteRowSideFullHecke.NumbersDVR.monoList, List.map_flatMap,
    List.map_replicate]

theorem intNum_get_cast (F : Type*) [Field F] (V : Ideal (MRing ι F)) (L : List (K → ℤ)) (n : ℕ)
    (h : L.length = n) : intNum F V (fun j => L.get (Fin.cast h.symm j)) = intNumL F V L := by
  subst h
  rfl

theorem classList_mapDomain_perm {σ τ : Type*} (e : σ → τ) (cls : τ → K → ℤ) (μ : σ →₀ ℕ) :
    (classList cls (μ.mapDomain e)).Perm (classList (cls ∘ e) μ) := by
  rw [← Multiset.coe_eq_coe, classList, classList, Multiset.coe_toList, Multiset.coe_toList,
    ← Finsupp.toMultiset_map, Multiset.map_map]

theorem polyNum_eq_classNum {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {m : ℕ} (deg : Fin m → K → ℤ) {τ : Type*} [DecidableEq τ] (e : Fin m ≃ τ) (cls : τ → K → ℤ)
    (hcls : cls ∘ e = deg) {H : MvPolynomial (Fin m) ℤ} {d : ℕ} (hH : H.IsHomogeneous d)
    (W : Ideal (MRing ι O)) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum (fun V _ L => intNum (IsLocalRing.ResidueField O) V L)
                              (specialIdeal W) d deg H = classNum cls (rename e H) [] W := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum classNum
  rw [support_rename_of_injective e.injective,
    Finset.sum_image fun a _ b _ h => Finsupp.mapDomain_injective e.injective h]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [coeff_rename_mapDomain _ e.injective]
  congr 1
  have hlen : (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList deg μ).length = d := by
    rw [monoList_eq, List.length_map, FlagTypings.length_monoList hH hμ]
  rw [dite_eq_left hlen]
  refine (intNum_get_cast _ _ _ _ hlen).trans ?_
  rw [List.append_nil]
  refine FlagTypings.intNumL_perm _ _ ?_
  rw [monoList_eq]
  refine ((FlagTypings.monoList_perm deg μ).trans ?_)
  rw [← hcls]
  exact (classList_mapDomain_perm e cls μ).symm

theorem sum_split {r : ℕ} (l : Fin r) (f : Fin r → ℕ) :
    ∑ j, f j = (∑ j ∈ Finset.univ.filter (fun j => j < l), f j) + f l +
      ∑ j ∈ Finset.univ.filter (fun j => l < j), f j := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j < l),
    ← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter fun j => ¬ j < l) (fun j => j = l),
    Finset.filter_filter, Finset.filter_filter, add_assoc]
  congr 2
  · rw [Finset.sum_eq_single l]
    · intro b hb hbl
      simp only [Finset.mem_filter] at hb
      exact absurd hb.2.2 hbl
    · intro h
      exact absurd (by simp) h
  · congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      exact lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
    · intro h
      exact ⟨not_lt.mpr h.le, ne_of_gt h⟩

theorem isHomogeneous_divDiff {r : ℕ} (l : Fin r) {G : MvPolynomial (Fin r) ℤ} {d : ℕ}
    (hG : G.IsHomogeneous (d + 1)) : (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l G).IsHomogeneous d := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff
  apply IsHomogeneous.sum
  intro μ hμ
  have hdeg : ∑ j, μ j = d + 1 := by
    have h := hG (mem_support_iff.mp hμ)
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
    simpa using h
  by_cases h0 : μ l = 0
  · simp only [h0, Finset.range_zero, Finset.sum_empty, mul_zero, zero_mul]
    exact isHomogeneous_zero _ _ _
  · have hA := IsHomogeneous.prod (Finset.univ.filter fun j => j < l)
      (fun j => (X (Fin.natAdd r j) : MvPolynomial (Fin (r + r)) ℤ) ^ μ j) (fun j => μ j)
      fun j _ => isHomogeneous_X_pow _ _
    have hB := IsHomogeneous.prod (Finset.univ.filter fun j => l < j)
      (fun j => (X (Fin.castAdd r j) : MvPolynomial (Fin (r + r)) ℤ) ^ μ j) (fun j => μ j)
      fun j _ => isHomogeneous_X_pow _ _
    have hM : (∑ a ∈ Finset.range (μ l), (X (Fin.castAdd r l) : MvPolynomial (Fin (r + r)) ℤ) ^ a *
        X (Fin.natAdd r l) ^ (μ l - 1 - a)).IsHomogeneous (μ l - 1) := by
      apply IsHomogeneous.sum
      intro a ha
      have h := (isHomogeneous_X_pow (R := ℤ) (Fin.castAdd r l) a).mul
        (isHomogeneous_X_pow (R := ℤ) (Fin.natAdd r l) (μ l - 1 - a))
      have ha' := Finset.mem_range.mp ha
      rwa [show a + (μ l - 1 - a) = μ l - 1 by omega] at h
    have h := (((isHomogeneous_C _ (G.coeff μ)).mul hA).mul hM).mul hB
    have hs := sum_split l μ
    rw [hdeg] at hs
    convert h using 1
    omega

theorem pairNum_eq {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (P : Ideal (MRing ι O)) (d : ℕ) {r : ℕ} (y y' : Fin r → K → ℤ) (f g : Fin r → MRing ι O)
    {G : MvPolynomial (Fin r) ℤ} (hG : G.IsHomogeneous (d + 1)) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O (fun V _ L => intNum (IsLocalRing.ResidueField O) V L) P d
                              y y' f g G =
      pairNum P y y' f g
        (fun l => rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l G)) [] := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum pairNum
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [vEval_eq, ratCyc_eq]
  congr 1
  funext W
  refine polyNum_eq_classNum (Fin.append y y') finSumFinEquiv.symm (Sum.elim y y') ?_
    (isHomogeneous_divDiff l hG) W
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [Function.comp_apply, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl, Fin.append_left]
  · simp only [Function.comp_apply, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr, Fin.append_right]

end PairNumbers

section DualGens

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

end DualGens

section ProjBundle

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

end ProjBundle

section Joins

variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
variable [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]

theorem joinCoords_eq {Ω : Type*} [Field Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) :
    joinCoords y y' = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y y' := by
  funext p
  obtain ⟨k | k, i⟩ := p <;> rfl

theorem joinForm_eq {R : Type*} [CommRing R] (f : MRing ι R) :
    joinForm (ι' := ι') f = rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ι') f := rfl

end Joins

section Degenerate

variable (O : Type*) [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]

end Degenerate

end GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreClosureNumber
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SegreClosureNumber.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ), 0 < N → ∀ (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
      IsModelOver (pointIdeal O (pairProjCoord y e φ φ' t)) (d + (N - 1)) →
    ∀ f₀ g₀ : MRing (bundleIdx (bundleIdx ι M) M') O,
      IsVerticalDivisor (pointIdeal O (pairProjCoord y e φ φ' t)) ϖ
        (zetaFirst a₀ - zetaSecond a₀') f₀ g₀ →
      aeval (pairProjCoord y e φ φ' t) f₀ = aeval (pairProjCoord y e φ φ' t) g₀ →
    ∀ (n : ℕ) (z z' : Fin n → K → ℤ) (fz gz : Fin n → MRing ι O),
      (∀ j, IsVerticalDivisor (pointIdeal O y) ϖ (z j - z' j) (fz j) (gz j)) →
    ∀ (a r : ℕ) (R : MvPolynomial (Fin n) ℤ), R.IsHomogeneous r →
    ∀ As : Fin (N + n) → MvPolynomial (Fin (N + n) ⊕ Fin (N + n)) ℤ,
      IsPairExpansion (a + r) (hsymmTimes N n a R) As →
    ∀ Cs : Fin (1 + n) → MvPolynomial (Fin (1 + n) ⊕ Fin (1 + n)) ℤ,
      IsPairExpansion (N - 1 + a + r) (zetaPowTimes n (N - 1 + a) R) Cs →
    ∀ Q : List (K → ℤ), Q.length + (a + r) = d + 1 →
      pairNum (pointIdeal O y) (Fin.append x z) (Fin.append x' z') (Fin.append f fz)
          (Fin.append g gz) As Q =
        (-1) ^ a * pairNum (pointIdeal O (pairProjCoord y e φ φ' t))
          (Fin.append (fun _ : Fin 1 => zetaFirst a₀) (fun j => liftPairDeg (z j)))
          (Fin.append (fun _ : Fin 1 => zetaSecond a₀') (fun j => liftPairDeg (z' j)))
          (Fin.append (fun _ : Fin 1 => f₀) (fun j => liftPairForm M M' (fz j)))
          (Fin.append (fun _ : Fin 1 => g₀) (fun j => liftPairForm M M' (gz j))) Cs
          (Q.map liftPairDeg)

section Examples

theorem mem_of_divCycle_ne_zero {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    {P : Ideal (MRing ι R)} {f : MRing ι R} {W : Ideal (MRing ι R)} (h : divCycle P f W ≠ 0) :
    f ∈ W ∧ W.IsPrime ∧ IsRelevant W := by
  unfold divCycle at h
  by_cases hW : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W
  · exact ⟨hW.1.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl)), hW.1.1.1, hW.2⟩
  · exact False.elim (h (dif_neg hW))

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerTail
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal joinCoord pullDeg liftVar ptCoord)

def JoinVerticalDivisor.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω) (b : K → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι),
    IsVertDiv O (mcIdeal O x) b f g →
    IsVertDiv O (mcIdeal O (joinCoord x z)) (pullDeg (K' := K') b) (rename (liftVar ι') f)
      (rename (liftVar ι') g)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsLocalCoeffRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Defs

variable {R : Type*} [CommRing R]

abbrev localQuot (P U : Ideal R) [U.IsPrime] : Type _ :=
  Localization.AtPrime U ⧸ P.map (algebraMap R (Localization.AtPrime U))

def localQuotMap (P U : Ideal R) [U.IsPrime] : R →+* localQuot P U :=
  (Ideal.Quotient.mk _).comp (algebraMap R (Localization.AtPrime U))

end Defs

section Lemmas

def LocalQuotRing.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (P U : Ideal R) [U.IsPrime], P.IsPrime → P ≤ U →
    IsDomain (localQuot P U) ∧ IsLocalRing (localQuot P U) ∧
      (∀ y : localQuot P U, IsUnit y ↔ y ∉ U.map (localQuotMap P U)) ∧
      ∀ x : R, localQuotMap P U x = 0 ↔ x ∈ P

def LocalQuotPrimes.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (P U : Ideal R) [U.IsPrime], P ≤ U →
    (∀ W : Ideal R, W.IsPrime → P ≤ W → W ≤ U →
      (W.map (localQuotMap P U)).IsPrime ∧ (W.map (localQuotMap P U)).comap (localQuotMap P U) = W) ∧
    ∀ p : Ideal (localQuot P U), p.IsPrime →
      P ≤ p.comap (localQuotMap P U) ∧ p.comap (localQuotMap P U) ≤ U ∧
        (p.comap (localQuotMap P U)).map (localQuotMap P U) = p

def LocCycleLocalQuot.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (P U : Ideal R) [U.IsPrime] (J W : Ideal R), P ≤ J → W.IsPrime → P ≤ W →
    W ≤ U → locCycle J W = locCycle (J.map (localQuotMap P U)) (W.map (localQuotMap P U))

def LocalQuotColon.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (P U : Ideal R) [U.IsPrime] (f g : R),
    ((P ⊔ Ideal.span {f}).colon {g}).map (localQuotMap P U) =
      (Ideal.span {localQuotMap P U f}).colon {localQuotMap P U g}

def LocalQuotFinsum.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (P U : Ideal R) [U.IsPrime], P ≤ U →
    ∀ (F : Ideal R → ℤ) (F' : Ideal (localQuot P U) → ℤ),
      (∀ G, F G ≠ 0 → G.IsPrime ∧ P ≤ G ∧ G ≤ U) → (∀ p, F' p ≠ 0 → p.IsPrime) →
      (∀ G : Ideal R, G.IsPrime → P ≤ G → G ≤ U → F G = F' (G.map (localQuotMap P U))) →
      ∑ᶠ G, F G = ∑ᶠ p, F' p

def LocalCoeffLocal.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A],
    (∀ Q₁ Q₂ : Ideal A, Q₁.IsPrime → Q₂.IsPrime → ⊥ < Q₁ → Q₁ < Q₂ → Q₂ < IsLocalRing.maximalIdeal A →
      False) →
    ∀ f g s u v : A, f ≠ 0 → g ≠ 0 → s ≠ 0 → IsUnit u → u * f = v * g →
    (∀ W : Ideal A, locCycle (Ideal.span {s}) W ≠ 0 →
      locCycle (Ideal.span {f}) W = locCycle (Ideal.span {g}) W) →
    ∑ᶠ G, (locCycle (Ideal.span {f}) G - locCycle (Ideal.span {g}) G) *
        locCycle (G ⊔ Ideal.span {s}) (IsLocalRing.maximalIdeal A) =
      ∑ᶠ W, locCycle (Ideal.span {s}) W *
        locCycle (W ⊔ (Ideal.span {f}).colon {g}) (IsLocalRing.maximalIdeal A)

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AevalChartSubstMemOfMemBlowUpOf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

section Chart

variable {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

def chartSubst (a : J → MRing ι R) : (Σ o, extIdx ι J o) → Polynomial (MRing ι R)
  | ⟨none, j⟩ => Polynomial.C (a j) * Polynomial.X
  | ⟨some k, i⟩ => Polynomial.C (X ⟨k, i⟩)

theorem aeval_chartSubst_liftForm (a : J → MRing ι R) (p : MRing ι R) :
    aeval (chartSubst a) (liftForm p) = Polynomial.C p := by
  have e : (aeval (chartSubst a)).comp (liftForm : MRing ι R →ₐ[R] MRing (extIdx ι J) R) =
      Polynomial.CAlgHom := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [liftForm, chartSubst]
  exact DFunLike.congr_fun e p

theorem aeval_chartSubst_mem_of_mem_blowUpOf {P : Ideal (MRing ι R)} (hP : P.IsPrime)
    {u a : J → MRing ι R} {u₀ g : MRing ι R} (hg : g ∉ P) (h : ∀ j, u₀ * u j - g * a j ∈ P)
    {F : MRing (extIdx ι J) R} (hF : F ∈ blowUpOf P u) :
    aeval (chartSubst a) F ∈ Ideal.map (Polynomial.C : MRing ι R →+* Polynomial (MRing ι R)) P := by
  let π := Polynomial.mapRingHom (Ideal.Quotient.mk P)
  have key : (Polynomial.compRingHom (Polynomial.C (Ideal.Quotient.mk P g) * Polynomial.X)).comp
        (π.comp (aeval (R := R) (chartSubst a)).toRingHom) =
      (Polynomial.compRingHom (Polynomial.C (Ideal.Quotient.mk P u₀) * Polynomial.X)).comp
        (aeval (R := R) (blowUpSubst P u)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [π, Polynomial.compRingHom]
      rfl
    · rintro ⟨_ | k, i⟩
      · have e : Ideal.Quotient.mk P (u₀ * u i) = Ideal.Quotient.mk P (g * a i) :=
          Ideal.Quotient.eq.mpr (h i)
        simp only [map_mul] at e
        simp [π, chartSubst, blowUpSubst, Polynomial.compRingHom]
        have e' : Polynomial.C (Ideal.Quotient.mk P (a i)) * Polynomial.C (Ideal.Quotient.mk P g) =
            Polynomial.C (Ideal.Quotient.mk P (u i)) * Polynomial.C (Ideal.Quotient.mk P u₀) := by
          rw [← Polynomial.C_mul, ← Polynomial.C_mul, mul_comm (Ideal.Quotient.mk P (u i)), e, mul_comm]
        rw [← mul_assoc, ← mul_assoc, e']
      · simp [π, chartSubst, blowUpSubst, Polynomial.compRingHom]
  have hF' : π (aeval (chartSubst a) F) = 0 := by
    have e := DFunLike.congr_fun key F
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at e
    rw [show aeval (blowUpSubst P u) F = 0 from RingHom.mem_ker.mp hF, map_zero] at e
    have hg' : Ideal.Quotient.mk P g ∈ nonZeroDivisors (MRing ι R ⧸ P) :=
      mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
    exact (Polynomial.comp_C_mul_X_eq_zero_iff hg').mp e
  have hk : aeval (chartSubst a) F ∈ RingHom.ker π := hF'
  rwa [Polynomial.ker_mapRingHom, Ideal.mk_ker] at hk

theorem mem_of_aeval_chartSubst_mem {a : J → MRing ι R} {H : Ideal (MRing (extIdx ι J) R)}
    (hH : H.IsPrime) {P' : Ideal (MRing ι R)} (hP'H : P' ≤ H.comap (liftForm (J := J))) (j₀ : J)
    (ha : liftForm (a j₀) ∉ H)
    (hrel : ∀ j, newVar j * liftForm (a j₀) - newVar j₀ * liftForm (a j) ∈ H)
    {F : MRing (extIdx ι J) R}
    (hF : aeval (chartSubst a) F ∈ Ideal.map (Polynomial.C : MRing ι R →+* Polynomial (MRing ι R)) P') :
    F ∈ H := by
  let L := FractionRing (MRing (extIdx ι J) R ⧸ H)
  let q : MRing (extIdx ι J) R →+* L := (algebraMap _ L).comp (Ideal.Quotient.mk H)
  have hq : ∀ y, q y = 0 ↔ y ∈ H := by
    intro y
    simp only [q, RingHom.comp_apply]
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ L), Ideal.Quotient.eq_zero_iff_mem]
  have ha' : q (liftForm (a j₀)) ≠ 0 := fun h0 => ha ((hq _).mp h0)
  let ε : Polynomial (MRing ι R) →+* L :=
    Polynomial.eval₂RingHom (q.comp (liftForm (J := J) : MRing ι R →ₐ[R] _).toRingHom)
      (q (newVar j₀) / q (liftForm (a j₀)))
  have key : ε.comp (aeval (R := R) (chartSubst a)).toRingHom = q := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ε, liftForm_C]
    · rintro ⟨_ | k, i⟩
      · have h1 := (hq _).mpr (hrel i)
        rw [map_sub, map_mul, map_mul, sub_eq_zero] at h1
        simp only [ε, chartSubst, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
          aeval_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_C,
          Polynomial.eval₂_X]
        rw [← mul_div_assoc, div_eq_iff ha', mul_comm]
        exact h1.symm
      · simp [ε, chartSubst, liftForm]
  have hε : Ideal.map (Polynomial.C : MRing ι R →+* Polynomial (MRing ι R)) P' ≤ RingHom.ker ε := by
    rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, RingHom.mem_ker]
    simp only [ε, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    exact (hq _).mpr (hP'H hp)
  have h2 := RingHom.mem_ker.mp (hε hF)
  have h3 := DFunLike.congr_fun key F
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at h3
  rw [h3] at h2
  exact (hq F).mp h2

end Chart

theorem BlowUpStrictTransform.proof : BlowUpStrictTransform.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD s hsP e m H hϖH hH
  set Q := blowUpOf P (blowUpGens s g f m e) with hQ
  have hPp : P.IsPrime := hP.multiProj.isPrime

  obtain ⟨x, hx, hHmin⟩ : ∃ x : MRing (extIdx ι (BlowUpIdx ι)) O,
      (x = liftForm s ∨ x = newVar none) ∧ H ∈ (Q ⊔ Ideal.span {x}).minimalPrimes := by
    have hm : ∀ {F}, divCycle Q F H ≠ 0 → H ∈ (Q ⊔ Ideal.span {F}).minimalPrimes := by
      intro F hF
      unfold divCycle at hF
      split_ifs at hF with hW
      · exact hW.1
      · exact absurd rfl hF
    rcases hH with hH | hH
    · exact ⟨_, Or.inl rfl, hm hH⟩
    · exact ⟨_, Or.inr rfl, hm hH⟩
  obtain ⟨hHp, hQH, hHrel⟩ : H.IsPrime ∧ Q ≤ H ∧ IsRelevant H := by
    rcases hH with hH | hH
    · exact le_and_isRelevant_of_divCycle_ne_zero hH
    · exact le_and_isRelevant_of_divCycle_ne_zero hH
  have mnm : ∀ {y z}, y ∉ H → z ∉ H → y * z ∉ H := fun hy hz hyz => (hHp.mem_or_mem hyz).elim hy hz
  have hxH : x ∈ H := hHmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
  set H₀ := H.comap (liftForm (J := BlowUpIdx ι)) with hH₀
  obtain ⟨hH₀p, hPH₀, hrel₀, -⟩ := comap_liftForm_facts hHp hQH hHrel
  have hϖH₀ : (C ϖ : MRing ι O) ∉ H₀ := by rw [Ideal.mem_comap, liftForm_C]; exact hϖH

  obtain ⟨u₀, v₀, hu, hv, h⟩ := hD.unit_off_special H₀ hH₀p hPH₀ hrel₀ hϖH₀
  obtain ⟨i, hpm, hYi, -⟩ := blowUp_offSpecial hPp e hD.den_not_mem hHp hQH hHrel (u₀ := u₀) hv h
  set a := blowUpCof s m e u₀ v₀ with ha_def
  have haS : liftForm (a (some (some i))) ∉ H := by
    show liftForm (v₀ * powMonomial e i) ∉ H
    rw [map_mul]; exact mnm hv hpm
  have hrelH : ∀ j, newVar j * liftForm (a (some (some i))) -
      newVar (some (some i)) * liftForm (a j) ∈ H :=
    fun j => hQH (blowUpCof_relation hPp e hD.den_not_mem h j _)

  have hsH₀ : s ∈ H₀ := by
    rcases hx with rfl | rfl
    · exact hxH
    · have h3 := H.sub_mem (H.mul_mem_right (liftForm (a (some (some i)))) hxH) (hrelH none)
      rw [sub_sub_cancel] at h3
      have h4 : liftForm (u₀ * s) ∈ H := (hHp.mem_or_mem h3).resolve_left hYi
      rw [map_mul] at h4
      exact (hHp.mem_or_mem h4).resolve_left hu

  have hmin₀ : H₀ ∈ (P ⊔ Ideal.span {s}).minimalPrimes := by
    refine ⟨⟨hH₀p, sup_le hPH₀ ((Ideal.span_singleton_le_iff_mem _).mpr hsH₀)⟩,
      fun P' hP' hP'H₀ => ?_⟩
    have := hP'.1
    have hsP' : s ∈ P' := hP'.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
    let Q' := (Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) P').comap
      (aeval (R := O) (chartSubst a))
    have hQ'p : Q'.IsPrime := Ideal.comap_isPrime _ _
    have hQQ' : Q ⊔ Ideal.span {x} ≤ Q' := by
      refine sup_le (fun F hF => ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      · exact Ideal.map_mono (le_sup_left.trans hP'.2)
          (aeval_chartSubst_mem_of_mem_blowUpOf hPp hD.den_not_mem (fun j => blowUpCof_spec e h j) hF)
      · rw [Ideal.mem_comap]
        rcases hx with rfl | rfl
        · rw [aeval_chartSubst_liftForm]
          exact Ideal.mem_map_of_mem _ hsP'
        · simp only [newVar, aeval_X, chartSubst]
          exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (P'.mul_mem_left _ hsP'))
    have hQ'H : Q' ≤ H := fun F hF => mem_of_aeval_chartSubst_mem hHp hP'H₀ _ haS hrelH hF
    have hHQ' := hHmin.2 ⟨hQ'p, hQQ'⟩ hQ'H
    intro p hp
    have h5 : Polynomial.C p ∈ Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) P' := by
      rw [← aeval_chartSubst_liftForm a p]
      exact hHQ' hp
    simpa using Ideal.mem_map_C_iff.mp h5 0

  have := hH₀p
  unfold divCycle
  rw [dite_eq_left ⟨hmin₀, hrel₀⟩]
  have hne := length_localizedQuot_ne_top (P ⊔ Ideal.span {s}) H₀ hmin₀
  have hnz : multAt (P ⊔ Ideal.span {s}) H₀ ≠ 0 := by
    unfold multAt
    rw [Ne, Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
    intro hs
    obtain ⟨r, hr, hr0⟩ := hs (Ideal.Quotient.mk _ 1)
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mul_one,
      Ideal.Quotient.eq_zero_iff_mem] at hr0
    exact hr (hmin₀.1.2 hr0)
  have htn : (multAt (P ⊔ Ideal.span {s}) H₀).toNat ≠ 0 :=
    fun h0 => (ENat.toNat_eq_zero.mp h0).elim hnz hne
  exact_mod_cast htn

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ComapLiftFormConstChartPrimeExample
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpOrderLe.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (J : Type) [Fintype J] (P : Ideal (MRing ι R)), P.IsPrime →
    ∀ (u : J → MRing ι R) (G' : Ideal (MRing (extIdx ι J) R)) (y : MRing (extIdx ι J) R),
      y ∉ blowUpOf P u → G' ∈ (blowUpOf P u ⊔ Ideal.span {y}).minimalPrimes → IsRelevant G' →
    ∀ x : MRing ι R, x ∉ P → G'.comap (liftForm (J := J)) ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
    ∀ z : MRing ι R, z ∉ P →
      divCycle (blowUpOf P u) (liftForm z) G' ≤ divCycle P z (G'.comap (liftForm (J := J)))

def ExceptionalContraction.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    ∀ e : K → ℕ, (∀ k, (c k : ℤ) = b k + e k) →
    ∀ m : MRing ι O, IsMultiHomog m e → m ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → m ∉ H) →
    ∀ G' : Ideal (MRing (extIdx ι (BlowUpIdx ι)) O),
      (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ G' →
      0 < divCycle (blowUpOf P (blowUpGens s g f m e)) (newVar none) G' →
      0 < ratDiv (blowUpOf P (blowUpGens s g f m e)) (liftForm (f * m))
        (liftForm g * newVar (some none)) G' →
      G'.comap (liftForm (J := BlowUpIdx ι)) ∈ (P ⊔ Ideal.span {s}).minimalPrimes

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpHorizontal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpHorizontalSat.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : MRing ι O) ∉ W →
      ∃ j, ∀ j', ∃ v w : MRing ι O, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing (extIdx ι J) O), divCycle (blowUpOf P u) (liftForm x) W ≠ 0 →
      (C ϖ : MRing (extIdx ι J) O) ∉ W →
      ∀ F : MRing (extIdx ι J) O, F ∈ W ↔ ∃ s : MRing ι O, s ∉ W.comap (liftForm (ι := ι) (J := J) (R := O)) ∧
        (liftForm (ι := ι) (J := J) (R := O)) s * F ∈ blowUpOf P u ⊔ Ideal.map (liftForm (ι := ι) (J := J) (R := O)) (W.comap (liftForm (ι := ι) (J := J) (R := O)))

def BlowUpHorizontalMult.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : MRing ι O) ∉ W →
      ∃ j, ∀ j', ∃ v w : MRing ι O, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing (extIdx ι J) O), divCycle (blowUpOf P u) (liftForm x) W ≠ 0 →
      (C ϖ : MRing (extIdx ι J) O) ∉ W →
      divCycle P x (W.comap (liftForm (ι := ι) (J := J) (R := O))) = divCycle (blowUpOf P u) (liftForm x) W

def BlowUpHorizontalLift.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : MRing ι O) ∉ W →
      ∃ j, ∀ j', ∃ v w : MRing ι O, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), divCycle P x W ≠ 0 → (C ϖ : MRing ι O) ∉ W →
      ∃ W' : Ideal (MRing (extIdx ι J) O), divCycle (blowUpOf P u) (liftForm x) W' ≠ 0 ∧
        (C ϖ : MRing (extIdx ι J) O) ∉ W' ∧ W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W

def BlowUpHorizontalStrict.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : MRing ι O) ∉ W →
      ∃ j, ∀ j', ∃ v w : MRing ι O, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing (extIdx ι J) O), divCycle (blowUpOf P u) (liftForm x) W ≠ 0 →
      (C ϖ : MRing (extIdx ι J) O) ∉ W →
      (∃ j, u j ∉ W.comap (liftForm (ι := ι) (J := J) (R := O))) → W = blowUpOf (W.comap (liftForm (ι := ι) (J := J) (R := O))) u

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerMore
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord)

def JoinPointModel.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω)))) d

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsJoinVariety
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx)

def JoinVariety.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (V : Ideal (MRing ι F)) (n : ℕ), ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF V n →
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF
      (V.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx))) n

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMoreExtra
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsProjVarF)

def VerticalDivisorSupportFibre.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRingOver O ι)) (d : ℕ),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O P d →
    ∀ (b : K → ℤ) (f g : MRingOver O ι), IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O P b f g →
    ∀ W : Ideal (MRingOver O ι), IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O P f g W ≠ 0 →
      IsProjVarF (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W) d

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSpanBundleTrdegGe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

def SpanBundleTrdegGe.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) (ι : K → Type) (y : (Σ k, ι k) → Ω) (M i : ℕ) (G : Fin M → Fin i → Ω),
    LinearIndependent Ω (fun j l => G l j) →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (s : Fin i → Φ), AlgebraicIndependent Ω s →
      Algebra.trdeg F (MRing ι F ⧸ pointIdeal F y) + i ≤
        Algebra.trdeg F (MRing (bundleIdx ι M) F ⧸ projIdeal F y (Pi.basisFun Ω (Fin i))
          (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsProjIdealFormValue
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def ProjIdealFormValue.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [DecidableEq K] (ι : K → Type) (y : (Σ k, ι k) → Ω)
    (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (w : Module.Basis (Fin N) Ω E)
    (M : ℕ) (φ : Fin M → Module.Dual Ω E) (Φ : Type) [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ)
    (d : Option K → ℕ) (x : MRing (bundleIdx ι M) F), IsMultiHomog x d →
      (x ∈ projIdeal F y w φ t ↔
        eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ t) x = 0)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
