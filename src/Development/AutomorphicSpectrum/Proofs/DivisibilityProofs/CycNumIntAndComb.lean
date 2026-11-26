module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
public import Development.WeilBound.CoreStatements.IdealCycleValues.ProdMapToMultiset
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PScalarQuotient
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyCN

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycNumIntAndComb
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem cycEval_eq_sum {K : Type} {ι : K → Type} {R : Type} [CommRing R]
    (n Z : Ideal (MRing ι R) → ℤ) (T : Finset (Ideal (MRing ι R)))
    (hT : Function.support Z ⊆ (T : Set (Ideal (MRing ι R)))) :
    cycEval n Z = ∑ W ∈ T, Z W * n W := by
  unfold cycEval
  refine finsum_eq_sum_of_support_subset _ ?_
  intro W hW
  apply hT
  intro h0
  apply hW
  simp [h0]

theorem cycEval_comb {K : Type} {ι : K → Type} {R : Type} [CommRing R]
    (n : Ideal (MRing ι R) → ℤ) {α : Type} (s : Finset α) (c : α → ℤ)
    (Z : α → Ideal (MRing ι R) → ℤ) (hZ : ∀ a, (Function.support (Z a)).Finite) :
    cycEval n (fun W => ∑ a ∈ s, c a * Z a W) = ∑ a ∈ s, c a * cycEval n (Z a) := by
  classical
  set T : Finset (Ideal (MRing ι R)) := s.biUnion fun a => (hZ a).toFinset with hTdef
  have hsum : Function.support (fun W => ∑ a ∈ s, c a * Z a W) ⊆
      (T : Set (Ideal (MRing ι R))) := by
    intro W hW
    by_contra hWT
    apply hW
    refine Finset.sum_eq_zero fun a ha => ?_
    have : Z a W = 0 := by
      by_contra hne
      exact hWT (by
        simp only [hTdef, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe,
          Set.Finite.coe_toFinset]
        exact ⟨a, ha, hne⟩)
    simp [this]
  have hone : ∀ a ∈ s, cycEval n (Z a) = ∑ W ∈ T, Z a W * n W := by
    intro a ha
    refine cycEval_eq_sum n (Z a) T ?_
    intro W hW
    simp only [hTdef, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe,
      Set.Finite.coe_toFinset]
    exact ⟨a, ha, hW⟩
  have hrhs : ∑ a ∈ s, c a * cycEval n (Z a) = ∑ a ∈ s, c a * ∑ W ∈ T, Z a W * n W :=
    Finset.sum_congr rfl fun a ha => by rw [hone a ha]
  rw [cycEval_eq_sum n _ T hsum, hrhs]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun W _ => ?_
  ring

theorem cycNum_int_and_comb : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) (cls : σ → K → ℤ) (Q : List (K → ℤ)), (∀ (Z : Ideal (MRing ι O) → ℤ), (Function.support Z).Finite → ∀ H : MvPolynomial σ ℤ, cycNum Z cls (MvPolynomial.map (Int.castRingHom ℝ) H) Q = ((cycEval (fun W => classNum cls H Q W) Z : ℤ) : ℝ)) ∧ (∀ (α : Type) (s : Finset α) (c : α → ℤ) (Z : α → Ideal (MRing ι O) → ℤ), (∀ a, (Function.support (Z a)).Finite) → ∀ H : MvPolynomial σ ℝ, cycNum (fun W => ∑ a ∈ s, c a * Z a W) cls H Q = ∑ a ∈ s, (c a : ℝ) * cycNum (Z a) cls H Q) := by
  intro O _ _ _ K _ _ ι _ σ cls Q
  refine ⟨?_, ?_⟩
  · intro Z hZ H
    have hinj : Function.Injective (Int.castRingHom ℝ) := Int.cast_injective
    have hT : Function.support Z ⊆ (hZ.toFinset : Set (Ideal (MRing ι O))) := by simp
    have key : cycEval (fun W => classNum cls H Q W) Z =
        ∑ μ ∈ H.support, H.coeff μ * cycList Z (classList cls μ ++ Q) := by
      unfold cycList
      rw [cycEval_eq_sum _ Z _ hT]
      simp only [cycEval_eq_sum _ Z _ hT, classNum, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun W _ => ?_
      ring
    unfold cycNum
    rw [MvPolynomial.support_map_of_injective _ hinj, key]
    push_cast
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [MvPolynomial.coeff_map]
    simp
  · intro α s c Z hZ H
    unfold cycNum
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have : cycList (fun W => ∑ a ∈ s, c a * Z a W) (classList cls μ ++ Q) =
        ∑ a ∈ s, c a * cycList (Z a) (classList cls μ ++ Q) :=
      cycEval_comb _ s c Z hZ
    rw [this]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycleNumberRename
section -- merged from Development.WeilBound.CoreStatements.IdealCycleValues.CycNumRenameVariables
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem BaseChangeColon.cycNum_rename_variables : (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ σ' : Type) (e : σ → σ') (Z : Ideal (MRing ι O) → ℤ) (cls : σ' → K → ℤ) (H : MvPolynomial σ ℝ) (Q : List (K → ℤ)), cycNum Z cls (rename e H) Q = cycNum Z (cls ∘ e) H Q) ∧ (∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ σ' : Type) (e : σ → σ') (V : Ideal (MRing ι F)) (cls : σ' → K → ℤ) (H : MvPolynomial σ ℝ) (Q : List (K → ℤ)), genNum F V cls (rename e H) Q = genNum F V (cls ∘ e) H Q) := by
  refine ⟨?_, ?_⟩
  · intro O _ _ _ K _ _ ι _ σ σ' e Z cls H Q
    unfold cycNum classList
    rw [BaseChangeColon.evL_eq, BaseChangeColon.evL_eq, BaseChangeColon.evL_rename]
    simp only [BaseChangeColon.classes_mapDomain]
  · intro F _ K _ _ ι _ σ σ' e V cls H Q
    unfold genNum classList
    rw [BaseChangeColon.evL_eq, BaseChangeColon.evL_eq, BaseChangeColon.evL_rename]
    simp only [BaseChangeColon.classes_mapDomain]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycleNumberRename
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem numbers_rename : (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ σ' : Type) (e : σ → σ') (Z : Ideal (MRing ι O) → ℤ) (cls : σ' → K → ℤ) (H : MvPolynomial σ ℝ) (Q : List (K → ℤ)), cycNum Z cls (rename e H) Q = cycNum Z (cls ∘ e) H Q) ∧ (∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ σ' : Type) (e : σ → σ') (V : Ideal (MRing ι F)) (cls : σ' → K → ℤ) (H : MvPolynomial σ ℝ) (Q : List (K → ℤ)), genNum F V cls (rename e H) Q = genNum F V (cls ∘ e) H Q) :=
  BaseChangeColon.cycNum_rename_variables

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycleNumberRenameStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cycle_number_rename : (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ σ' : Type) (e : σ → σ') (Z : Ideal (MRing ι O) → ℤ) (cls : σ' → K → ℤ) (H : MvPolynomial σ ℝ) (Q : List (K → ℤ)), cycNum Z cls (rename e H) Q = cycNum Z (cls ∘ e) H Q) ∧ (∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ σ' : Type) (e : σ → σ') (V : Ideal (MRing ι F)) (cls : σ' → K → ℤ) (H : MvPolynomial σ ℝ) (Q : List (K → ℤ)), genNum F V cls (rename e H) Q = genNum F V (cls ∘ e) H Q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.numbers_rename | exact GlobalTheory.CompanionTheory.Ar.Num.numbers_rename | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.numbers_rename <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycleListPermInvariant
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycleListPermInvariant
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem intNumL_perm_of_perm (F : Type) [Field F] (K : Type) [DecidableEq K] (ι : K → Type)
    (V : Ideal (MRing ι F)) (l l' : List (K → ℤ)) (h : l.Perm l') :
    intNumL F V l = intNumL F V l' := by
  haveI : LeftCommutative (diffStep : (K → ℤ) → ((K → ℤ) → ℤ) → ((K → ℤ) → ℤ)) := by
    constructor
    intro a b g
    funext m
    simp only [diffStep]
    rw [sub_right_comm m a b]
    ring
  unfold intNumL intNum GroundTheory.Heights₂.Heights.NumbersDVR.mixedDiff
  rw [List.ofFn_get, List.ofFn_get, h.foldr_eq]

theorem numbers_list_perm : (∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (V : Ideal (MRing ι F)) (l l' : List (K → ℤ)), l.Perm l' → intNumL F V l = intNumL F V l') ∧ (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Z : Ideal (MRing ι O) → ℤ) (l l' : List (K → ℤ)), l.Perm l' → cycList Z l = cycList Z l') := by
  refine ⟨fun F _ K _ _ ι _ V l l' h => intNumL_perm_of_perm F K ι V l l' h, ?_⟩
  intro O _ _ _ K _ _ ι _ Z l l' h
  unfold cycList
  congr 1
  funext W
  exact intNumL_perm_of_perm _ K ι (specialIdeal W) l l' h

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycleListPermInvariantStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cycle_list_perm_invariant : (∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (V : Ideal (MRing ι F)) (l l' : List (K → ℤ)), l.Perm l' → intNumL F V l = intNumL F V l') ∧ (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Z : Ideal (MRing ι O) → ℤ) (l l' : List (K → ℤ)), l.Perm l' → cycList Z l = cycList Z l') := by
  exact GlobalTheory.CompanionTheory.Ar.Num.numbers_list_perm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycleNumberLinear
section -- merged from Development.WeilBound.CoreStatements.IdealCycleValues.CycNumLinearInPolynomial
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem BaseChangeColon.cycNum_linear_in_polynomial : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) (Z : Ideal (MRing ι O) → ℤ) (cls : σ → K → ℤ) (Q : List (K → ℤ)), (∀ H H' : MvPolynomial σ ℝ, cycNum Z cls (H + H') Q = cycNum Z cls H Q + cycNum Z cls H' Q) ∧ (∀ (c : ℝ) (H : MvPolynomial σ ℝ), cycNum Z cls (C c * H) Q = c * cycNum Z cls H Q) ∧ (∀ (α : Type) (s : Finset α) (H : α → MvPolynomial σ ℝ), cycNum Z cls (∑ a ∈ s, H a) Q = ∑ a ∈ s, cycNum Z cls (H a) Q) ∧ ∀ (μ : σ →₀ ℕ) (c : ℝ), cycNum Z cls (monomial μ c) Q = c * (cycList Z (classList cls μ ++ Q) : ℝ) := by
  intro O _ _ _ K _ _ ι _ σ Z cls Q
  classical
  set g : (σ →₀ ℕ) → ℝ := fun μ => (cycList Z (classList cls μ ++ Q) : ℝ) with hg
  have key : ∀ (H : MvPolynomial σ ℝ) (s : Finset (σ →₀ ℕ)), H.support ⊆ s →
      cycNum Z cls H Q = ∑ μ ∈ s, AddMonoidAlgebra.coeff H μ * g μ := by
    intro H s hs
    show ∑ μ ∈ H.support, AddMonoidAlgebra.coeff H μ * g μ = _
    refine Finset.sum_subset hs (fun μ _ hμ => ?_)
    rw [MvPolynomial.notMem_support_iff.mp hμ, zero_mul]
  have hadd : ∀ H H' : MvPolynomial σ ℝ, cycNum Z cls (H + H') Q = cycNum Z cls H Q + cycNum Z cls H' Q := by
    intro H H'
    rw [key (H + H') (H.support ∪ H'.support) MvPolynomial.support_add,
      key H (H.support ∪ H'.support) Finset.subset_union_left,
      key H' (H.support ∪ H'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun _ _ => ?_)
    rw [MvPolynomial.coeff_add, add_mul]
  have hzero : cycNum Z cls (0 : MvPolynomial σ ℝ) Q = 0 := by
    rw [key 0 ∅ (by simp)]
    simp
  refine ⟨hadd, ?_, ?_, ?_⟩
  · intro c H
    have hs : (MvPolynomial.C c * H).support ⊆ H.support := by
      intro μ hμ
      rw [MvPolynomial.mem_support_iff] at hμ ⊢
      rw [MvPolynomial.coeff_C_mul] at hμ
      exact right_ne_zero_of_mul hμ
    rw [key _ H.support hs, key H H.support subset_rfl, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun _ _ => ?_)
    rw [MvPolynomial.coeff_C_mul, mul_assoc]
  · intro α s H
    induction s using Finset.induction_on with
    | empty => simp [hzero]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]
  · intro μ c
    rw [key _ {μ} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycleNumberLinear
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem cycNum_linear : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) (Z : Ideal (MRing ι O) → ℤ) (cls : σ → K → ℤ) (Q : List (K → ℤ)), (∀ H H' : MvPolynomial σ ℝ, cycNum Z cls (H + H') Q = cycNum Z cls H Q + cycNum Z cls H' Q) ∧ (∀ (c : ℝ) (H : MvPolynomial σ ℝ), cycNum Z cls (C c * H) Q = c * cycNum Z cls H Q) ∧ (∀ (α : Type) (s : Finset α) (H : α → MvPolynomial σ ℝ), cycNum Z cls (∑ a ∈ s, H a) Q = ∑ a ∈ s, cycNum Z cls (H a) Q) ∧ ∀ (μ : σ →₀ ℕ) (c : ℝ), cycNum Z cls (monomial μ c) Q = c * (cycList Z (classList cls μ ++ Q) : ℝ) :=
  @BaseChangeColon.cycNum_linear_in_polynomial

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycleNumberLinearStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cycle_number_linear : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) (Z : Ideal (MRing ι O) → ℤ) (cls : σ → K → ℤ) (Q : List (K → ℤ)), (∀ H H' : MvPolynomial σ ℝ, cycNum Z cls (H + H') Q = cycNum Z cls H Q + cycNum Z cls H' Q) ∧ (∀ (c : ℝ) (H : MvPolynomial σ ℝ), cycNum Z cls (C c * H) Q = c * cycNum Z cls H Q) ∧ (∀ (α : Type) (s : Finset α) (H : α → MvPolynomial σ ℝ), cycNum Z cls (∑ a ∈ s, H a) Q = ∑ a ∈ s, cycNum Z cls (H a) Q) ∧ ∀ (μ : σ →₀ ℕ) (c : ℝ), cycNum Z cls (monomial μ c) Q = c * (cycList Z (classList cls μ ++ Q) : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.cycNum_linear | exact GlobalTheory.CompanionTheory.Ar.Num.cycNum_linear | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.cycNum_linear <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.UniformizerDivisorCycleNumber
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.UniformizerDivisorCycleNumber
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.ConsPoly

theorem length_classList {K σ : Type} (cls : σ → K → ℤ) {H : MvPolynomial σ ℝ} {m : ℕ}
    (hH : H.IsHomogeneous m) {μ : σ →₀ ℕ} (hμ : μ ∈ H.support) :
    (classList cls μ).length = m := by
  have h := hH (mem_support_iff.mp hμ)
  rw [← h]
  simp [classList, Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset,
    Finsupp.weight_apply, Finsupp.sum]

theorem cycList_const {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P : Ideal (MRing ι O)} (l : List (K → ℤ))
    (hM : IsModelOver P l.length) (u : Oˣ) (e : ℕ) :
    cycList (divCycle P (C ((u : O) * ϖ ^ e))) l =
      (e : ℤ) * intNumL (FractionRing O) (genFib P) l := by
  haveI : P.IsPrime := hM.multiProj.isPrime
  have hC : ∀ a : O, a ≠ 0 → (C a : MRing ι O) ∉ P := by
    intro a ha hmem
    apply ha
    have ha' : a ∈ P.comap (C : O →+* MRing ι O) := Ideal.mem_comap.2 hmem
    rw [hM.noTorsion] at ha'
    exact Ideal.mem_bot.1 ha'
  have hfin := ScalarQuotient.divCycle_support_finite P (C ϖ)
  have key : cycEval (fun W => vNumL W l) (divCycle P (C ϖ)) =
      intNumL (FractionRing O) (genFib P) l :=
    ConservationOfNumber.full O ϖ hϖ K ι P l.length hM l.get
  unfold cycList
  rw [ScalarQuotient.divCycle_const P hC hϖ.ne_zero u e, ← key]
  unfold cycEval
  show ∑ᶠ W, ((e : ℤ) * divCycle P (C ϖ) W) * vNumL W l =
    (e : ℤ) * ∑ᶠ W, divCycle P (C ϖ) W * vNumL W l
  rw [mul_finsum]
  · exact finsum_congr fun W => by ring
  all_goals exact hfin.subset (Function.support_mul_subset_left _ _)

end GlobalTheory.CompanionTheory.Ar.Num.ConsPoly


open GlobalTheory.CompanionTheory.Ar.Num.ConsPoly in
theorem GlobalTheory.CompanionTheory.Ar.Num.cycNum_divCycle_const : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (u : Oˣ) (e : ℕ) (σ : Type) (cls : σ → K → ℤ) (H : MvPolynomial σ ℝ) (m : ℕ), H.IsHomogeneous m → ∀ Q : List (K → ℤ), m + Q.length = d → cycNum (divCycle P (C ((u : O) * ϖ ^ e))) cls H Q = (e : ℝ) * genNum (FractionRing O) (genFib P) cls H Q := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hM u e σ cls H m hH Q hd
  unfold cycNum genNum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hlen : (classList cls μ ++ Q).length = d := by
    rw [List.length_append, GlobalTheory.CompanionTheory.Ar.Num.ConsPoly.length_classList cls hH hμ, hd]
  have hM' : IsModelOver P (classList cls μ ++ Q).length := by
    rw [hlen]
    exact hM
  rw [GlobalTheory.CompanionTheory.Ar.Num.ConsPoly.cycList_const hϖ _ hM' u e]
  push_cast
  ring
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.UniformizerDivisorCycleNumberStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformizer_divisor_cycle_number : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (u : Oˣ) (e : ℕ) (σ : Type) (cls : σ → K → ℤ) (H : MvPolynomial σ ℝ) (m : ℕ), H.IsHomogeneous m → ∀ Q : List (K → ℤ), m + Q.length = d → cycNum (divCycle P (C ((u : O) * ϖ ^ e))) cls H Q = (e : ℝ) * genNum (FractionRing O) (genFib P) cls H Q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.cycNum_divCycle_const | exact GlobalTheory.CompanionTheory.Ar.Num.cycNum_divCycle_const | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.cycNum_divCycle_const <;> assumption)
end
end
