module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
public import Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionRingAll
public import Formalism.SharpRestriction.LevelLetterCocycles.ExportBoundOfAdmissible

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmittedStatementsOfLocalBoundsConclusion
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesSizeConditionFive
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesSizeConditionFive
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem adm5_tab : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L),
    Concl L P X C → TwistedPlaces.adm5 L (tab L X tf C) C := by
  classical
  intro D L P X C tf h i hi hl
  obtain ⟨h2, hq, hd, hg⟩ := hl
  have hqd : ¬ (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) := by tauto
  have hR0 : 0 ≤ C * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * (TwistedPlaces.large₂ L) ^ 2 := by
    have := h.pos
    positivity
  show (if D.nd.l i ∈ D.host.small then TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i
    else if D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d then TwistedPlaces.midG L C (D.nd.l i)
    else if KillingConditions.RangeAD L X.exc (D.nd.l i) then KillingConditions.supZ i (X.errorBoundHub i) else 0) ≤ _
  rw [if_neg h2, if_neg hqd]
  split_ifs with hR
  · unfold KillingConditions.supZ
    split_ifs with hne
    · exact Finset.sup'_le hne _ (fun π hπ => h.bb i hi hg hR π hπ)
    · exact hR0
  · exact hR0

end GlobalTheory.NLink
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesSizeConditionFiveStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localBoundTableAllPrimes_sizeConditionFive : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.adm5 L (tab L X tf C) C := by
  first | exact @GlobalTheory.NLink.adm5_tab | exact GlobalTheory.NLink.adm5_tab | (intros; apply GlobalTheory.NLink.adm5_tab <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesRamifiedTypePrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesRamifiedTypePrimes
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem localBoundTableAllPrimes_ramified_typePrimes : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L),
    Concl L P X C → TwistedPlaces.RamifiedPrimeLengthBound L (tab L X tf C) C ∧ TwistedPlaces.GeneratorPrimeEtaBound L (tab L X tf C) C := by
  intro D L P X C tf hC
  refine ⟨⟨?_, hC.small.2.2.2.2.1⟩, ?_⟩
  · intro i _ hl
    obtain ⟨hq, hd, hq8, hd16, -⟩ := D.host.hyp
    have h3q := D.host.q_ne_three
    have h2 : D.nd.l i ∉ D.host.small := UpperTheory.Small.not_mem_of_qd D.host hl
    have h3 : D.nd.l i ≠ 3 := by rcases hl with h | h <;> rw [h] <;> omega
    have hR : ¬ KillingConditions.RangeAD L X.exc (D.nd.l i) := fun h => h.2.1 hl
    have hlen : (tab L X tf C).len i = fun _ => 0 := by
      funext lam
      simp only [tab, h2, h3, hR, if_false]
    have hBB : (tab L X tf C).BB i = TwistedPlaces.midG L C (D.nd.l i) := by
      simp only [tab, h2, hl, if_false, if_true]
    rw [hlen, hBB]
    simp [TwistedPlaces.sumOver]
  · intro j hj l hl
    exact ⟨hC.typ j hj l hl, le_rfl⟩

end GlobalTheory.NLink
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesRamifiedTypePrimesStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramifiedPrimeLengthBound_and_generatorPrimeEtaBound_tab : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.RamifiedPrimeLengthBound L (tab L X tf C) C ∧ TwistedPlaces.GeneratorPrimeEtaBound L (tab L X tf C) C := by
  first | exact @GlobalTheory.NLink.localBoundTableAllPrimes_ramified_typePrimes | exact GlobalTheory.NLink.localBoundTableAllPrimes_ramified_typePrimes | (intros; apply GlobalTheory.NLink.localBoundTableAllPrimes_ramified_typePrimes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesSizeConditionSix
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesSizeConditionSix
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem adm6_tab : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L),
    Concl L P X C → TwistedPlaces.adm6 L (tab L X tf C) := by
  intro D L P X C tf hC
  refine ⟨?_, ?_⟩
  · intro i hi π hπ
    have hk := ((hC.kill i hi).1 π hπ).2
    show (Br.sPi D.loc D.nbr i (X.ρ i) π : ℝ) + TwistedPlaces.epsL (D.nd.l i) ≤ _
    unfold TwistedPlaces.epsL at hk ⊢
    have : (2 : ℝ) / (D.nd.l i : ℝ) ^ 2 = 1 / (D.nd.l i : ℝ) ^ 2 + 1 / (D.nd.l i : ℝ) ^ 2 := by ring
    rw [this]
    linarith
  · intro j _ l _
    show TwistedPlaces.epsL l + TwistedPlaces.epsL l ≤ 2 / (l : ℝ) ^ 2
    unfold TwistedPlaces.epsL
    apply le_of_eq
    ring

end GlobalTheory.NLink
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesSizeConditionSixStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localBoundTableAllPrimes_sizeConditionSix : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.adm6 L (tab L X tf C) := by
  first | exact @GlobalTheory.NLink.adm6_tab | exact GlobalTheory.NLink.adm6_tab | (intros; apply GlobalTheory.NLink.adm6_tab <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesConditionTwoThree
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesConditionTwoThree
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLinkAdmF

theorem placesOver_three_nonempty (D : D7) : (placesOver D.host.E 3).Nonempty := by
  have hl : Nat.Prime 3 := Nat.prime_three
  have hne : ((3 : ℕ) : 𝓞 D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hnu : ¬ IsUnit ((3 : ℕ) : 𝓞 D.host.E) := by
    intro h
    have h1 := h.map (Algebra.norm ℤ)
    have h2 : Algebra.norm ℤ ((3 : ℕ) : 𝓞 D.host.E) = ((3 : ℕ) : ℤ) ^ Module.finrank ℤ (𝓞 D.host.E) := by
      rw [← Algebra.norm_algebraMap (R := ℤ) (S := 𝓞 D.host.E) ((3 : ℕ) : ℤ)]; simp
    rw [h2, isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at h1
    exact hl.one_lt.ne' h1
  obtain ⟨M, hM, hlM⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hnu)
  exact ⟨⟨M, hM.isPrime, fun h => hne (by simp [h] at hlM)⟩, hlM⟩

theorem sumOver_three_even (D : D7) (c : ℝ) :
    TwistedPlaces.sumOver D 3 (fun _ => c / ((placesOver D.host.E 3).ncard : ℝ)) = c := by
  have hfin : (placesOver D.host.E 3).Finite := FamilyRepresentationConstants.placesOver_finite D.host.E 3 (by norm_num)
  have hpos : 0 < (placesOver D.host.E 3).ncard :=
    (Set.ncard_pos hfin).2 (placesOver_three_nonempty D)
  unfold TwistedPlaces.sumOver
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_const, nsmul_eq_mul,
    ← Set.ncard_eq_toFinset_card _ hfin]
  have : ((placesOver D.host.E 3).ncard : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  field_simp

theorem localBoundTableAllPrimes_conditionTwoThree : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.SmallPrimeLengthBound L tf C → TwistedPlaces.SmallPrimeLengthBound L (tab L X tf C) C := by
  intro D L P X C tf _ hF i hi hl
  have hFi := hF i hi hl
  by_cases h2 : D.nd.l i ∈ D.host.small
  · have hlen : (tab L X tf C).len i = fun _ => 0 := by
      funext lam
      simp only [tab, if_pos h2]
    have hBB : (tab L X tf C).BB i = TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i := by
      simp only [tab, if_pos h2]
    show TwistedPlaces.sumOver D _ ((tab L X tf C).len i) + (tab L X tf C).BB i ≤ _
    rw [hlen, hBB]
    have h0 : TwistedPlaces.sumOver D (D.nd.l i) (fun _ => (0 : ℝ)) = 0 := by simp [TwistedPlaces.sumOver]
    rw [h0, zero_add]
    exact hFi
  · have h3 : D.nd.l i = 3 := hl.resolve_left h2
    have hq : D.host.q ≠ 3 := D.host.q_ne_three
    have hd : D.host.d ≠ 3 := by
      have := D.host.hyp.2.2.2.1
      omega
    have hlen : (tab L X tf C).len i =
        fun _ => (TwistedPlaces.sumOver D 3 (tf.len i) + tf.BB i) / ((placesOver D.host.E 3).ncard : ℝ) := by
      funext lam
      simp only [tab, if_neg h2, if_pos h3]
    have hBB : (tab L X tf C).BB i = 0 := by
      have h1 : ¬ (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) := by omega
      have hR : ¬ KillingConditions.RangeAD L X.exc (D.nd.l i) := fun hr => hr.1 (Or.inr h3)
      simp only [tab, if_neg h2, if_neg h1, if_neg hR]
    show TwistedPlaces.sumOver D (D.nd.l i) ((tab L X tf C).len i) + (tab L X tf C).BB i ≤ _
    have hFi' : TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i ≤ _ := hFi
    rw [h3] at hFi'
    rw [hlen, hBB, h3, sumOver_three_even, add_zero]
    exact hFi'

end GlobalTheory.NLinkAdmF

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesConditionTwoThreeStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallPrimeLengthBound_tab : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.SmallPrimeLengthBound L tf C → TwistedPlaces.SmallPrimeLengthBound L (tab L X tf C) C := by
  first | exact @GlobalTheory.NLinkAdmF.localBoundTableAllPrimes_conditionTwoThree | exact GlobalTheory.NLinkAdmF.localBoundTableAllPrimes_conditionTwoThree | (intros; apply GlobalTheory.NLinkAdmF.localBoundTableAllPrimes_conditionTwoThree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesVanishingExcluded
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesVanishingExcluded
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem largePrimeLengthVanishing_and_exceptionalBounded_tab : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ)
    (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.LargePrimeLengthVanishing L (tab L X tf C) ∧ TwistedPlaces.ExceptionalPrimesBounded L (tab L X tf C) := by
  intro D L P X C tf h
  obtain ⟨h3, hq, hd, -, -, hsl⟩ := h.small
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i _ hl
    obtain ⟨hlt, -, hexc⟩ := hl
    have hexc' : D.nd.l i ∉ X.exc := hexc
    have h2 : D.nd.l i ∉ D.host.small := fun he => by linarith [hsl _ he]
    have h3' : D.nd.l i ≠ 3 := by
      rintro he; rw [he] at hlt; push_cast at hlt; linarith
    have hq' : D.nd.l i ≠ D.host.q := by
      rintro he; rw [he] at hlt; linarith
    have hd' : D.nd.l i ≠ D.host.d := by
      rintro he; rw [he] at hlt; linarith
    have hR : ¬ KillingConditions.RangeAD L X.exc (D.nd.l i) := fun hr => hr.2.2 ⟨hlt, hexc'⟩
    refine ⟨fun lam _ => ?_, ?_⟩
    · simp only [tab, h2, h3', hR, if_false]
    · simp only [tab, h2, hR, if_false]
      rw [if_neg (by rintro (he | he) <;> contradiction)]
  · exact h.exc.1
  · exact h.exc.2

end GlobalTheory.NLink
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesVanishingExcludedStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localBoundTableAllPrimes_vanishing_excluded : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.LargePrimeLengthVanishing L (tab L X tf C) ∧ TwistedPlaces.ExceptionalPrimesBounded L (tab L X tf C) := by
  first | exact @GlobalTheory.NLink.largePrimeLengthVanishing_and_exceptionalBounded_tab | exact GlobalTheory.NLink.largePrimeLengthVanishing_and_exceptionalBounded_tab | (intros; apply GlobalTheory.NLink.largePrimeLengthVanishing_and_exceptionalBounded_tab <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesRowsAndBand
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesRowsAndBand
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

open Classical

namespace GlobalTheory.NLink

theorem localBoundTableAllPrimes_rowsAndBand : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.admA L (tab L X tf C) C ∧ TwistedPlaces.admB L (tab L X tf C) C ∧ TwistedPlaces.MediumInertPrimeLengthBound L (tab L X tf C) C ∧ TwistedPlaces.SmallInertPrimeSmallOrderLengthBound L (tab L X tf C) C ∧ TwistedPlaces.BandPlaceWeightApproximation L (tab L X tf C) C := by
  intro D L P X C tf h
  have hC := h.pos
  obtain ⟨nA, nB, nC, nD, nBand⟩ := h.num
  have h3 : ¬ TwistedPlaces.InertK D 3 := h.small.2.2.2.1
  have hR : ∀ i, D.nd.l i ≠ 3 → KillingConditions.RangeAD L X.exc (D.nd.l i) →
      (tab L X tf C).len i = (tabX L X).len i := by
    intro i h3 hr; funext lam
    have hs : D.nd.l i ∉ D.host.small := fun e => hr.1 (Or.inl e)
    show (if D.nd.l i ∈ D.host.small then (0 : ℝ) else if D.nd.l i = 3 then _
      else if KillingConditions.RangeAD L X.exc (D.nd.l i) then _ else 0) = _
    rw [if_neg hs, if_neg h3, if_pos hr]; rfl
  have hN : ∀ i, D.nd.l i ≠ 3 → ¬ KillingConditions.RangeAD L X.exc (D.nd.l i) →
      (tab L X tf C).len i = fun _ => 0 := by
    intro i h3 hr; funext lam
    show (if D.nd.l i ∈ D.host.small then (0 : ℝ) else if D.nd.l i = 3 then _
      else if KillingConditions.RangeAD L X.exc (D.nd.l i) then _ else 0) = _
    rw [if_neg h3, if_neg hr, ite_self]
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hb : 1 ≤ L.sc.b := Real.one_le_exp (Real.rpow_nonneg hx.le _)
  have hSc := L.Sc_pos
  have hEta := L.etaSz_pos
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hLg : 0 ≤ TwistedPlaces.large₂ L := Real.rpow_nonneg hx.le _
  have hB1 : 1 ≤ TwistedPlaces.hB L := by unfold TwistedPlaces.hB; linarith
  have hwB : 0 ≤ TwistedPlaces.wB L := by
    have hb' : 0 < L.sc.b' := by
      unfold Scale.b' Scale.a Scale.X'
      positivity
    have h0 : 0 ≤ L.sc.w'' D.R.n := by unfold Scale.w''; positivity
    unfold TwistedPlaces.wB
    exact le_trans (by linarith) (le_max_left _ _)
  have hetaP : 0 ≤ TwistedPlaces.eta₃ L := by unfold TwistedPlaces.eta₃; linarith
  have hwP : 0 ≤ TwistedPlaces.wP L := by unfold TwistedPlaces.wP; linarith
  have hGP : 0 ≤ TwistedPlaces.GP L := by unfold TwistedPlaces.GP; linarith
  have heP : ∀ l : ℕ, l.Prime → 0 ≤ TwistedPlaces.eP L C l := by
    intro l hl
    unfold TwistedPlaces.eP
    have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
    have h1 : 0 ≤ Real.logb l (TwistedPlaces.hB L) := Real.logb_nonneg hl1 hB1
    have h2 : 0 ≤ TwistedPlaces.hB L / l := div_nonneg (by linarith) (by linarith)
    exact mul_nonneg hC (by linarith)
  have hflat : ∀ (tb : TwistedPlaces.Tab L) i lam (l : ℕ), 0 ≤ TwistedPlaces.flatCD L tb i lam l := by
    intro tb i lam l
    unfold TwistedPlaces.flatCD
    have h1 : 0 ≤ (TwistedPlaces.wP L + TwistedPlaces.eta₃ L) / l := div_nonneg (by linarith) (Nat.cast_nonneg _)
    have h2 : 0 ≤ TwistedPlaces.eta₃ L * (if tb.band i lam then 1 else 0) :=
      mul_nonneg hetaP (by split_ifs <;> norm_num)
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi hP
    have h5 := hP.1
    have h3' : D.nd.l i ≠ 3 := by omega
    by_cases hr : KillingConditions.RangeAD L X.exc (D.nd.l i)
    · rw [hR i h3' hr]; exact nA i hi hP
    · rw [hN i h3' hr]
      have hl := (D.nd.lPrime i).out
      have h0 : TwistedPlaces.sumOver D (D.nd.l i) (fun _ => (0 : ℝ)) = 0 := by
        unfold TwistedPlaces.sumOver; simp
      rw [h0, mul_zero]
      unfold TwistedPlaces.sumOver
      apply finsum_nonneg; intro lam; apply finsum_nonneg; intro _
      exact mul_nonneg (by positivity) (heP _ hl)
  · intro i hi hP
    have hI := hP.1
    have h3' : D.nd.l i ≠ 3 := fun e => h3 (by rw [e] at hI; exact hI)
    by_cases hr : KillingConditions.RangeAD L X.exc (D.nd.l i)
    · rw [hR i h3' hr]; exact nB i hi hP
    · rw [hN i h3' hr]
      intro lam _
      have hl1 : (1 : ℝ) ≤ D.nd.l i := by exact_mod_cast (D.nd.lPrime i).out.one_lt.le
      have h1 : 0 ≤ TwistedPlaces.hB L / ((D.nd.l i : ℝ) - 1) ^ (TwistedPlaces.jA L (D.nd.l i) + 1) :=
        div_nonneg (by linarith) (pow_nonneg (by linarith) _)
      have h2 : 0 ≤ (TwistedPlaces.GP L + 1) * ((TwistedPlaces.jA L (D.nd.l i) : ℝ) + 1) :=
        mul_nonneg (by linarith) (by positivity)
      exact mul_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (Nat.cast_nonneg _)) (by linarith)
  · intro i hi hP
    have hI := hP.1
    have h3' : D.nd.l i ≠ 3 := fun e => h3 (by rw [e] at hI; exact hI)
    by_cases hr : KillingConditions.RangeAD L X.exc (D.nd.l i)
    · rw [hR i h3' hr]; exact nC i hi hP
    · rw [hN i h3' hr]
      intro lam _
      have hl := (D.nd.lPrime i).out
      have h1 : 0 ≤ TwistedPlaces.hB L / (D.nd.l i : ℝ) ^ 2 := div_nonneg (by linarith) (by positivity)
      have h2 := hflat (tab L X tf C) i lam (D.nd.l i)
      have h4 := heP _ hl
      exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (Nat.cast_nonneg _)) (by linarith))
        (mul_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (Nat.cast_nonneg _)) h4)
  · intro i hi hP
    have hI := hP.1
    have h3' : D.nd.l i ≠ 3 := fun e => h3 (by rw [e] at hI; exact hI)
    by_cases hr : KillingConditions.RangeAD L X.exc (D.nd.l i)
    · rw [hR i h3' hr]; exact nD i hi hP
    · rw [hN i h3' hr]
      intro lam _
      have hl := (D.nd.lPrime i).out
      have h1 : 0 ≤ TwistedPlaces.hB L / (D.nd.l i : ℝ) ^ 2 := div_nonneg (by linarith) (by positivity)
      have h2 := hflat (tab L X tf C) i lam (D.nd.l i)
      have h4 := heP _ hl
      exact add_nonneg (add_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (Nat.cast_nonneg _)) h1)
        (mul_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (Nat.cast_nonneg _)) h2))
        (mul_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (Nat.cast_nonneg _)) h4)
  · exact nBand

end GlobalTheory.NLink
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesRowsAndBandStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admA_admB_inert_band_tab : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.admA L (tab L X tf C) C ∧ TwistedPlaces.admB L (tab L X tf C) C ∧ TwistedPlaces.MediumInertPrimeLengthBound L (tab L X tf C) C ∧ TwistedPlaces.SmallInertPrimeSmallOrderLengthBound L (tab L X tf C) C ∧ TwistedPlaces.BandPlaceWeightApproximation L (tab L X tf C) C := by
  first | exact @GlobalTheory.NLink.localBoundTableAllPrimes_rowsAndBand | exact GlobalTheory.NLink.localBoundTableAllPrimes_rowsAndBand | (intros; apply GlobalTheory.NLink.localBoundTableAllPrimes_rowsAndBand <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTableOfLocalBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTableOfLocalBounds
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLink.Adm4Tab

theorem placesOver_nonempty (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime) :
    (placesOver E p).Nonempty :=
  by apply _root_.UpperTheory.Reformulated.B.Qk8.exists_place <;> assumption

theorem sumOver_const (D : D7) (l : ℕ) (hl : l ≠ 0) (k : ℝ) :
    TwistedPlaces.sumOver D l (fun _ => k) = ((placesOver D.host.E l).ncard : ℝ) * k := by
  have hf := FamilyRepresentationConstants.placesOver_finite D.host.E l hl
  rw [TwistedPlaces.sumOver, finsum_mem_eq_finite_toFinset_sum _ hf, Finset.sum_const, Set.ncard_eq_toFinset_card _ hf,
    nsmul_eq_mul]

theorem sumOver_mono (D : D7) (l : ℕ) (hl : l ≠ 0) {f g : HeightOneSpectrum (𝓞 D.host.E) → ℝ}
    (h : ∀ lam, f lam ≤ g lam) : TwistedPlaces.sumOver D l f ≤ TwistedPlaces.sumOver D l g := by
  have hf := FamilyRepresentationConstants.placesOver_finite D.host.E l hl
  rw [TwistedPlaces.sumOver, TwistedPlaces.sumOver, finsum_mem_eq_finite_toFinset_sum _ hf, finsum_mem_eq_finite_toFinset_sum _ hf]
  exact Finset.sum_le_sum fun lam _ => h lam

theorem le_supZ {D : D7} (i : D.nd.Loc) (f : D.nd.X i → ℝ) {π : D.nd.X i} (hπ : π ∈ D.nd.Zgood i) :
    f π ≤ KillingConditions.supZ i f := by
  unfold KillingConditions.supZ
  rw [dite_eq_left ⟨π, hπ⟩]
  exact Finset.le_sup' f hπ

end GlobalTheory.NLink.Adm4Tab


open GlobalTheory.NLink.Adm4Tab in
theorem GlobalTheory.NLink.admissible_table_of_conclusion : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L),
    Concl L P X C → (∀ i, TwistedPlaces.TwLoc D i → (D.nd.l i ∈ D.host.small ∨ D.nd.l i = 3) → ∀ π ∈ D.nd.Zgood i,
      Bd X.ρ i π (TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i)) → TwistedPlaces.ArchimedeanSignatureMatching L (tab L X tf C) := by
  intro D L P X C tf hC h23 i hi hg π hπ
  have key : ∀ b, Bd X.ρ i π b → b ≤ TwistedPlaces.sumOver D (D.nd.l i) ((tab L X tf C).len i) + (tab L X tf C).BB i →
      (D.nd.vcc i π : ℝ) ≤ (tab L X tf C).s i π + TwistedPlaces.sumOver D (D.nd.l i) ((tab L X tf C).len i) +
        TwistedPlaces.VVr D (D.nd.l i) + TwistedPlaces.vhE D (D.nd.l i) + (tab L X tf C).BB i + TwistedPlaces.epsL (D.nd.l i) := by
    intro b hb hle
    unfold Bd at hb
    have hs : (tab L X tf C).s i π = (Br.sPi D.loc D.nbr i (X.ρ i) π : ℝ) := rfl
    rw [hs]
    linarith
  have hl0 : D.nd.l i ≠ 0 := (D.nd.lPrime i).out.ne_zero
  have hq3 : D.host.q ≠ 3 := D.host.q_ne_three
  have hd3 : D.host.d ≠ 3 := by have := D.host.hyp.2.2.2.1; omega
  have hzero : TwistedPlaces.sumOver D (D.nd.l i) (fun _ => (0 : ℝ)) = 0 := by
    rw [sumOver_const D _ hl0, mul_zero]
  by_cases h2 : D.nd.l i ∈ D.host.small
  · apply key _ (h23 i hi (Or.inl h2) π hπ)
    have hlen : (tab L X tf C).len i = fun _ => 0 := by
      funext lam
      simp only [tab, if_pos h2]
    have hBB : (tab L X tf C).BB i = TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i := by
      simp only [tab, if_pos h2]
    rw [hlen, hzero, hBB, zero_add]
  by_cases h3 : D.nd.l i = 3
  · apply key _ (h23 i hi (Or.inr h3) π hπ)
    have hBB : (tab L X tf C).BB i = 0 := by
      have hq : ¬ (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) := by
        rw [h3]; rintro (h | h) <;> [exact hq3 h.symm; exact hd3 h.symm]
      have hR : ¬ KillingConditions.RangeAD L X.exc (D.nd.l i) := fun h => h.1 (Or.inr h3)
      simp only [tab, if_neg h2, if_neg hq, if_neg hR]
    have hlen : (tab L X tf C).len i =
        fun _ => (TwistedPlaces.sumOver D 3 (tf.len i) + tf.BB i) / ((placesOver D.host.E 3).ncard : ℝ) := by
      funext lam
      simp only [tab, if_neg h2, if_pos h3]
    rw [hBB, hlen, h3, sumOver_const D 3 (by norm_num)]
    have hf3 := FamilyRepresentationConstants.placesOver_finite D.host.E 3 (by norm_num)
    have hpos : 0 < (placesOver D.host.E 3).ncard :=
      (Set.ncard_pos hf3).2 (placesOver_nonempty D.host.E 3 Nat.prime_three)
    have hpos' : ((placesOver D.host.E 3).ncard : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [mul_div_cancel₀ _ hpos', add_zero]
  by_cases hqd : D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d
  · apply key _ (hC.ram i hi hqd π hπ)
    have hR : ¬ KillingConditions.RangeAD L X.exc (D.nd.l i) := fun h => h.2.1 hqd
    have hlen : (tab L X tf C).len i = fun _ => 0 := by
      funext lam
      simp only [tab, if_neg h2, if_neg h3, if_neg hR]
    have hBB : (tab L X tf C).BB i = TwistedPlaces.midG L C (D.nd.l i) := by
      simp only [tab, if_neg h2, if_pos hqd]
    rw [hlen, hzero, hBB, zero_add]
  by_cases hR : KillingConditions.RangeAD L X.exc (D.nd.l i)
  · have hm := hC.mid i hi hg hR π hπ
    have hb : Bd X.ρ i π (TwistedPlaces.sumOver D (D.nd.l i) (X.len0 i π) + X.errorBoundHub i π) := by
      unfold Bd
      linarith
    apply key _ hb
    have hlen : (tab L X tf C).len i = KillingConditions.lenR X.len0 i := by
      funext lam
      simp only [tab, if_neg h2, if_neg h3, if_pos hR]
    have hBB : (tab L X tf C).BB i = KillingConditions.supZ i (X.errorBoundHub i) := by
      simp only [tab, if_neg h2, if_neg hqd, if_pos hR]
    rw [hlen, hBB]
    have h1 : TwistedPlaces.sumOver D (D.nd.l i) (X.len0 i π) ≤ TwistedPlaces.sumOver D (D.nd.l i) (KillingConditions.lenR X.len0 i) :=
      sumOver_mono D _ hl0 fun lam => le_supZ i (fun π => X.len0 i π lam) hπ
    have h2' : X.errorBoundHub i π ≤ KillingConditions.supZ i (X.errorBoundHub i) := le_supZ i (X.errorBoundHub i) hπ
    linarith
  · have hlt : TwistedPlaces.lStar L < (D.nd.l i : ℝ) ∧ D.nd.l i ∉ X.exc := by
      by_contra hc
      exact hR ⟨fun h => h.elim h2 h3, hqd, hc⟩
    apply key _ (hC.large i hi hlt.1 hg hlt.2 π hπ)
    have hlen : (tab L X tf C).len i = fun _ => 0 := by
      funext lam
      simp only [tab, if_neg h2, if_neg h3, if_neg hR]
    have hBB : (tab L X tf C).BB i = 0 := by
      simp only [tab, if_neg h2, if_neg hqd, if_neg hR]
    rw [hlen, hzero, hBB, add_zero]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTableOfLocalBoundsStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_table_of_local_bounds : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → (∀ i, TwistedPlaces.TwLoc D i → (D.nd.l i ∈ D.host.small ∨ D.nd.l i = 3) → ∀ π ∈ D.nd.Zgood i, Bd X.ρ i π (TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i)) → TwistedPlaces.ArchimedeanSignatureMatching L (tab L X tf C) := by
  first | exact @GlobalTheory.NLink.admissible_table_of_conclusion | exact GlobalTheory.NLink.admissible_table_of_conclusion | (intros; apply GlobalTheory.NLink.admissible_table_of_conclusion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmittedStatementsOfLocalBoundsConclusion
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem admittedStatements_of_localBoundsConclusion : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ),
    Concl L P X C → ∃ tb : TwistedPlaces.Tab L, TwistedPlaces.AdmT L tb C P := by
  intro D L P X C h
  obtain ⟨tf, hF, h23⟩ := h.two
  refine ⟨tab L X tf C, ?_⟩
  have h2 : TwistedPlaces.adm2 L := fun j hj w hw _ => h.mult j hj w hw
  obtain ⟨hA, hB, hC, hD, hBand⟩ := GlobalTheory.T.admA_admB_inert_band_tab D L P X C tf h
  obtain ⟨hE, hExc⟩ := GlobalTheory.T.localBoundTableAllPrimes_vanishing_excluded D L P X C tf h
  obtain ⟨hG, hH⟩ := GlobalTheory.T.ramifiedPrimeLengthBound_and_generatorPrimeEtaBound_tab D L P X C tf h
  exact ⟨h.pass, h2, h.rank, GlobalTheory.T.admissible_table_of_local_bounds D L P X C tf h h23, GlobalTheory.T.localBoundTableAllPrimes_sizeConditionFive D L P X C tf h,
    GlobalTheory.T.localBoundTableAllPrimes_sizeConditionSix D L P X C tf h, hA, hB, hC, hD, hBand, hE, hExc,
    GlobalTheory.T.smallPrimeLengthBound_tab D L P X C tf h hF, hG, hH, h.par⟩

end GlobalTheory.NLink
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmittedStatementsOfLocalBoundsConclusionStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admittedStatements_of_localBoundsConclusion_alt : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ), Concl L P X C → ∃ tb : TwistedPlaces.Tab L, TwistedPlaces.AdmT L tb C P := by
  first | exact @GlobalTheory.NLink.admittedStatements_of_localBoundsConclusion | exact GlobalTheory.NLink.admittedStatements_of_localBoundsConclusion | (intros; apply GlobalTheory.NLink.admittedStatements_of_localBoundsConclusion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinkNAlongFamilyOfLocalBounds
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.LinkFam

theorem main : ∀ {eps : ℝ} (Fm : FamP eps), ConclF Fm → Formalism.MainNotions.LinkN Fm := by
  intro eps Fm hC
  obtain ⟨C, x0, h⟩ := hC
  have hA : Formalism.MainNotions.TwistedPlaces.AdmF Fm := ⟨C, x0, fun x hx hx1 i hS => by
    obtain ⟨X, hX⟩ := h x hx hx1 i hS
    exact GlobalTheory.T.admittedStatements_of_localBoundsConclusion_alt _ _ _ X C hX⟩
  exact Formalism.MainNotions.N.linkN_of Fm hA (Formalism.MainNotions.TwistedPlaces.stmtF_holds Fm)

end GlobalTheory.LinkFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinkNAlongFamilyOfLocalBoundsStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linkN_along_family_of_localBounds : ∀ {eps : ℝ} (Fm : FamP eps), ConclF Fm → Formalism.MainNotions.LinkN Fm := by
  first | exact @GlobalTheory.LinkFam.main | exact GlobalTheory.LinkFam.main | (intros; apply GlobalTheory.LinkFam.main <;> assumption)
end
