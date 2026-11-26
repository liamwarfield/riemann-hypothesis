module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycNumIntAndComb
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumSectionCut
public import Development.WeilBound.CoreStatements.IdealCycleValues.IntNumLCons
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.VerticalNumberZeroOfHorizontal

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.IdealCycleValues.CycListAdditiveFirstClass
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem BaseChangeColon.cycList_additive_first_class : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (a : K → ℕ) (f : MRing ι O), IsMultiHomog f a → f ∉ P → ∀ (b b' : K → ℤ) (l : List (K → ℤ)), l.length + 1 = d → cycList (divCycle P f) ((b + b') :: l) = cycList (divCycle P f) (b :: l) + cycList (divCycle P f) (b' :: l) := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP a f hf hfP b b' l hl
  have hPp : P.IsPrime := hP.multiProj.isPrime
  unfold cycList
  refine AdditivityInDivisor.cycEval_add_fn (DivCycleFiniteSupport.full O K ι P f) fun W hW => ?_
  by_cases hϖW : (C ϖ : MRing ι O) ∈ W
  · have hWmin : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes := by
      unfold divCycle at hW
      split_ifs at hW with h
      · exact h.1
      · exact absurd rfl hW
    have hWp : W.IsPrime := hWmin.1.1
    have hPW : P ≤ W := le_sup_left.trans hWmin.1.2
    have hWh : IsMultiHomogIdeal W := MinimalPrimeMultiHomog.full O K ι _ W
      (SupSpanMultiHomog.full O K ι P f a hP.multiProj.multiHomog hf) hWmin
    have hfW : f ∈ W := hWmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
    have hlt : P < W := lt_of_le_of_ne hPW fun h => hfP (h ▸ hfW)
    have hdim := DimStrictDrop.full (MRing ι O) P W hlt
    rw [hP.dim, ← SpecialQuotDim.full O ϖ hϖ K ι W hϖW,
      show d + 1 + Fintype.card K = l.length + 2 + Fintype.card K by omega] at hdim
    have key := IntNumAddFirst.full _ K ι l.length (specialIdeal W)
      (SpecialIdealCorresp.full O ϖ hϖ K ι P W hWp hϖW).1 (SpecialIdealMultiHomog.full O K ι W hWh)
      (AdditivityInDivisor.withBot_lt_of_add_one_le hdim) b b' l.get
    rw [← BaseChangeColon.intNumL_cons, ← BaseChangeColon.intNumL_cons, ← BaseChangeColon.intNumL_cons] at key
    exact key
  · have h0 := GlobalTheory.T.vertical_number_zero_of_horizontal O ϖ hϖ K ι P d hP a f hf hfP W hW hϖW
    show vNumL W _ = vNumL W _ + vNumL W _
    rw [h0 _ (by simpa using hl), h0 _ (by simpa using hl), h0 _ (by simpa using hl), add_zero]
end

section -- merged from Development.WeilBound.CoreStatements.IdealCycleValues.HomogeneousSumLinearChangeClasses
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem BaseChangeColon.homogeneous_sum_linear_change_classes : ∀ (G : Type) [AddCommGroup G] (d : ℕ) (n : List G → ℝ), (∀ l l', l.Perm l' → n l = n l') → (∀ b b' l, l.length + 1 = d → n ((b + b') :: l) = n (b :: l) + n (b' :: l)) → ∀ (σ σ' : Type) [Fintype σ] (cls : σ → G) (M : σ' → σ → ℤ) (H : MvPolynomial σ' ℝ) (m : ℕ), H.IsHomogeneous m → ∀ Q : List G, m + Q.length = d → (∑ μ ∈ H.support, H.coeff μ * n ((μ.toMultiset.map fun t => ∑ i, M t i • cls i).toList ++ Q)) = ∑ μ ∈ (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H).support, (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H).coeff μ * n ((μ.toMultiset.map cls).toList ++ Q) := by
  intro G _ d n hperm hadd σ σ' _ cls M H m hH Q hQ
  exact (BaseChangeColon.subst_abs d n hperm hadd cls M H m hH Q hQ).trans
    (BaseChangeColon.evL_eq _ _).symm
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DivisorCycleSubstitution
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DivisorCycleListAdditive
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DivisorCycleListAdditive
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem cycList_divCycle_add_first : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (a : K → ℕ) (f : MRing ι O), IsMultiHomog f a → f ∉ P → ∀ (b b' : K → ℤ) (l : List (K → ℤ)), l.length + 1 = d → cycList (divCycle P f) ((b + b') :: l) = cycList (divCycle P f) (b :: l) + cycList (divCycle P f) (b' :: l) := by
  exact @BaseChangeColon.cycList_additive_first_class

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DivisorCycleListAdditiveStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisor_cycle_list_additive : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (a : K → ℕ) (f : MRing ι O), IsMultiHomog f a → f ∉ P → ∀ (b b' : K → ℤ) (l : List (K → ℤ)), l.length + 1 = d → cycList (divCycle P f) ((b + b') :: l) = cycList (divCycle P f) (b :: l) + cycList (divCycle P f) (b' :: l) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.cycList_divCycle_add_first | exact GlobalTheory.CompanionTheory.Ar.Num.cycList_divCycle_add_first | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.cycList_divCycle_add_first <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HomogeneousClassSubstitution
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HomogeneousClassSubstitution
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem subst_abs_list : ∀ (G : Type) [AddCommGroup G] (d : ℕ) (n : List G → ℝ), (∀ l l', l.Perm l' → n l = n l') → (∀ b b' l, l.length + 1 = d → n ((b + b') :: l) = n (b :: l) + n (b' :: l)) → ∀ (σ σ' : Type) [Fintype σ] (cls : σ → G) (M : σ' → σ → ℤ) (H : MvPolynomial σ' ℝ) (m : ℕ), H.IsHomogeneous m → ∀ Q : List G, m + Q.length = d → (∑ μ ∈ H.support, H.coeff μ * n ((μ.toMultiset.map fun t => ∑ i, M t i • cls i).toList ++ Q)) = ∑ μ ∈ (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H).support, (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H).coeff μ * n ((μ.toMultiset.map cls).toList ++ Q) := by
  exact @BaseChangeColon.homogeneous_sum_linear_change_classes

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HomogeneousClassSubstitutionStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_class_substitution : ∀ (G : Type) [AddCommGroup G] (d : ℕ) (n : List G → ℝ), (∀ l l', l.Perm l' → n l = n l') → (∀ b b' l, l.length + 1 = d → n ((b + b') :: l) = n (b :: l) + n (b' :: l)) → ∀ (σ σ' : Type) [Fintype σ] (cls : σ → G) (M : σ' → σ → ℤ) (H : MvPolynomial σ' ℝ) (m : ℕ), H.IsHomogeneous m → ∀ Q : List G, m + Q.length = d → (∑ μ ∈ H.support, H.coeff μ * n ((μ.toMultiset.map fun t => ∑ i, M t i • cls i).toList ++ Q)) = ∑ μ ∈ (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H).support, (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H).coeff μ * n ((μ.toMultiset.map cls).toList ++ Q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.subst_abs_list | exact GlobalTheory.CompanionTheory.Ar.Num.subst_abs_list | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.subst_abs_list <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DivisorCycleSubstitution
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem divCycle_support_finite {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι O)) (f : MRing ι O) : (Function.support (divCycle P f)).Finite := by
  haveI : IsNoetherianRing (MRing ι O) := by
    unfold MRing
    infer_instance
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing (MRing ι O) (P ⊔ Ideal.span {f})).subset ?_
  intro W hW
  by_contra hn
  apply hW
  unfold divCycle
  rw [dite_eq_right]
  exact fun h => hn h.1

theorem cycList_ratDiv {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι O)) (f g : MRing ι O) (l : List (K → ℤ)) :
    cycList (ratDiv P f g) l = cycList (divCycle P f) l - cycList (divCycle P g) l := by
  have e : ratDiv P f g = divCycle P f - divCycle P g := rfl
  unfold cycList
  rw [e]
  exact (cycEval_sub_cycle _ _ _ (divCycle_support_finite P f) (divCycle_support_finite P g)).symm

theorem cycNum_subst_of_add {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (Z : Ideal (MRing ι O) → ℤ) (d : ℕ)
    (hadd : ∀ (b b' : K → ℤ) (l : List (K → ℤ)), l.length + 1 = d →
      cycList Z ((b + b') :: l) = cycList Z (b :: l) + cycList Z (b' :: l))
    {σ σ' : Type} [Fintype σ] (cls : σ → K → ℤ) (M : σ' → σ → ℤ) (H : MvPolynomial σ' ℝ) (m : ℕ)
    (hH : H.IsHomogeneous m) (Q : List (K → ℤ)) (hQ : m + Q.length = d) :
    cycNum Z (fun t => ∑ i, M t i • cls i) H Q =
      cycNum Z cls (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H) Q :=
  GlobalTheory.T.homogeneous_class_substitution (K → ℤ) d (fun l => (cycList Z l : ℝ))
    (fun l l' h => by rw [GlobalTheory.T.cycle_list_perm_invariant.2 O K ι Z l l' h])
    (fun b b' l h => by rw [hadd b b' l h]; push_cast; rfl)
    σ σ' cls M H m hH Q hQ

theorem cycNum_linear_subst : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (a a' : K → ℕ) (f g : MRing ι O), IsMultiHomog f a → IsMultiHomog g a' → f ∉ P → g ∉ P → ∀ (σ σ' : Type) [Fintype σ] (cls : σ → K → ℤ) (M : σ' → σ → ℤ) (H : MvPolynomial σ' ℝ) (m : ℕ), H.IsHomogeneous m → ∀ Q : List (K → ℤ), m + Q.length = d → cycNum (ratDiv P f g) (fun t => ∑ i, M t i • cls i) H Q = cycNum (ratDiv P f g) cls (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H) Q ∧ cycNum (divCycle P f) (fun t => ∑ i, M t i • cls i) H Q = cycNum (divCycle P f) cls (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H) Q := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP a a' f g hf hg hfP hgP σ σ' _ cls M H m hH Q hQ
  have af := GlobalTheory.T.divisor_cycle_list_additive O ϖ hϖ K ι P d hP a f hf hfP
  have ag := GlobalTheory.T.divisor_cycle_list_additive O ϖ hϖ K ι P d hP a' g hg hgP
  refine ⟨cycNum_subst_of_add _ d (fun b b' l h => ?_) cls M H m hH Q hQ,
    cycNum_subst_of_add _ d (af · · · ·) cls M H m hH Q hQ⟩
  rw [cycList_ratDiv, cycList_ratDiv, cycList_ratDiv, af b b' l h, ag b b' l h]
  ring

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DivisorCycleSubstitutionStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisor_cycle_substitution : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (a a' : K → ℕ) (f g : MRing ι O), IsMultiHomog f a → IsMultiHomog g a' → f ∉ P → g ∉ P → ∀ (σ σ' : Type) [Fintype σ] (cls : σ → K → ℤ) (M : σ' → σ → ℤ) (H : MvPolynomial σ' ℝ) (m : ℕ), H.IsHomogeneous m → ∀ Q : List (K → ℤ), m + Q.length = d → cycNum (ratDiv P f g) (fun t => ∑ i, M t i • cls i) H Q = cycNum (ratDiv P f g) cls (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H) Q ∧ cycNum (divCycle P f) (fun t => ∑ i, M t i • cls i) H Q = cycNum (divCycle P f) cls (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H) Q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.cycNum_linear_subst | exact GlobalTheory.CompanionTheory.Ar.Num.cycNum_linear_subst | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.cycNum_linear_subst <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LocalPairSplitSum
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LocalPairSplitSum
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.CkAppend

theorem classList_mapDomain_eq {K σ τ : Type} (cls : τ → K → ℤ) (e : σ → τ) (μ : σ →₀ ℕ) :
    classList cls (Finsupp.mapDomain e μ) = classList (cls ∘ e) μ := by
  unfold classList
  rw [← Finsupp.toMultiset_map, Multiset.map_map]

theorem classNum_rename_eq {K : Type} [DecidableEq K] {ι : K → Type} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {σ τ : Type} (cls : τ → K → ℤ) (e : σ → τ) (he : Function.Injective e)
    (H : MvPolynomial σ ℤ) (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (rename e H) Q W = classNum (cls ∘ e) H Q W := by
  classical
  unfold classNum
  rw [support_rename_of_injective he,
    Finset.sum_image fun a _ b _ h => Finsupp.mapDomain_injective he h]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [coeff_rename_mapDomain e he, classList_mapDomain_eq]

theorem psumExpansion_rename (N k : ℕ) (i : Fin N) :
    psumExpansion N k i =
      rename (Sum.map (fun _ : Fin 1 => i) (fun _ : Fin 1 => i)) (psumExpansion 1 k 0) := by
  simp [psumExpansion]

theorem pairNum_psumExpansion {K : Type} [DecidableEq K] {ι : K → Type} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {N : ℕ} (P : Ideal (MRing ι O)) (x x' : Fin N → K → ℤ)
    (f g : Fin N → MRing ι O) (k : ℕ) (Q : List (K → ℤ)) :
    pairNum P x x' f g (psumExpansion N k) Q =
      ∑ i, pairNum P (fun _ : Fin 1 => x i) (fun _ => x' i) (fun _ => f i) (fun _ => g i)
        (psumExpansion 1 k) Q := by
  unfold pairNum
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_one]
  have he : Function.Injective (Sum.map (fun _ : Fin 1 => i) (fun _ : Fin 1 => i)) :=
    Sum.map_injective.mpr ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ _ _ => Subsingleton.elim _ _⟩
  have hc : Sum.elim x x' ∘ Sum.map (fun _ : Fin 1 => i) (fun _ : Fin 1 => i) =
      Sum.elim (fun _ : Fin 1 => x i) (fun _ : Fin 1 => x' i) := by
    funext s
    rcases s with s | s <;> rfl
  simp only [psumExpansion_rename N k i, classNum_rename_eq _ _ he, hc]

theorem ck_append : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (j j' : ℕ) (T : LocPair ι O (Fin (j + j')))
    (P : Ideal (MRing ι O)) (k : ℕ) (Q : List (K → ℤ)),
    T.ck P k Q = (T.comp (Fin.castAdd j')).ck P k Q + (T.comp (Fin.natAdd j)).ck P k Q := by
  intro O _ _ _ K _ _ ι _ j j' T P k Q
  unfold LocPair.ck
  rw [pairNum_psumExpansion, pairNum_psumExpansion, pairNum_psumExpansion, Fin.sum_univ_add]
  rfl

end GlobalTheory.CompanionTheory.Ar.Num.CkAppend
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LocalPairSplitSumStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_pair_split_sum : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (j j' : ℕ) (T : LocPair ι O (Fin (j + j'))) (P : Ideal (MRing ι O)) (k : ℕ) (Q : List (K → ℤ)), T.ck P k Q = (T.comp (Fin.castAdd j')).ck P k Q + (T.comp (Fin.natAdd j)).ck P k Q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.CkAppend.ck_append | exact GlobalTheory.CompanionTheory.Ar.Num.CkAppend.ck_append | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.CkAppend.ck_append <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagM3FromLocal
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.FlagLocalM3

noncomputable section

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem divCycle_support_finite (P : Ideal (MRing ι O)) (f : MRing ι O) :
    (Function.support (divCycle P f)).Finite := by
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {f})).subset ?_
  intro W hW
  by_contra h
  apply hW
  simp [divCycle, h]

theorem C_not_mem {P : Ideal (MRing ι O)} {d : ℕ} (hP : IsModelOver P d) {a : O} (ha : a ≠ 0) :
    (C a : MRing ι O) ∉ P := by
  intro h
  have h' : a ∈ P.comap (C : O →+* MRing ι O) := h
  rw [hP.noTorsion] at h'
  exact ha (by simpa using h')

theorem laNum_eq (P : Ideal (MRing ι O)) (a : O) {r : ℕ} (x : Fin r → K → ℤ) (k : ℕ)
    (Q : List (K → ℤ)) :
    ((laNum P a x k Q : ℤ) : ℝ) =
      (k : ℝ) * cycNum (divCycle P (C a)) x (∑ i : Fin r, (X i : MvPolynomial (Fin r) ℝ) ^ (k - 1)) Q := by
  have h := (cycNum_int_and_comb O K ι (Fin r) x Q).1 (divCycle P (C a))
    (divCycle_support_finite P (C a)) (psum (Fin r) ℤ (k - 1))
  have e : MvPolynomial.map (Int.castRingHom ℝ) (psum (Fin r) ℤ (k - 1)) =
      ∑ i : Fin r, (X i : MvPolynomial (Fin r) ℝ) ^ (k - 1) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [psum, map_sum]
  rw [e] at h
  rw [h, laNum]
  push_cast
  rfl

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ]

theorem liePs_inl (j j' m : ℕ) (τ : Ψ) :
    (liePs (N := j + j') j m (Sum.inl τ) : MvPolynomial (Ψ × Fin (j + j')) ℝ) =
      rename (fun i : Fin j => (τ, Fin.castAdd j' i))
        (∑ i : Fin j, (X i : MvPolynomial (Fin j) ℝ) ^ m) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [liePs, map_sum, map_pow, rename_X, Finset.sum_filter, Fin.sum_univ_add]
  simp

theorem liePs_inr (j j' m : ℕ) (τ : Ψ) :
    (liePs (N := j + j') j m (Sum.inr τ) : MvPolynomial (Ψ × Fin (j + j')) ℝ) =
      rename (fun i : Fin j' => (τ, Fin.natAdd j i))
        (∑ i : Fin j', (-(X i : MvPolynomial (Fin j') ℝ)) ^ m) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [liePs, map_sum, map_pow, map_neg, rename_X, Finset.sum_filter, Fin.sum_univ_add]
  have h0 : ∀ x : Fin j, ¬ j ≤ (x : ℕ) := fun x => not_le.2 x.2
  simp [h0]

theorem cycNum_neg {ϖ : O} (hϖ : Irreducible ϖ) {P : Ideal (MRing ι O)} {d : ℕ} (hP : IsModelOver P d)
    {a : O} (ha : a ≠ 0) {r : ℕ} (cls : Fin r → K → ℤ) (m : ℕ) (Q : List (K → ℤ))
    (hQ : m + Q.length = d) :
    cycNum (divCycle P (C a)) (fun i => -cls i) (∑ i : Fin r, (X i : MvPolynomial (Fin r) ℝ) ^ m) Q =
      cycNum (divCycle P (C a)) cls (∑ i : Fin r, (-(X i : MvPolynomial (Fin r) ℝ)) ^ m) Q := by
  have hC : IsMultiHomog (C a : MRing ι O) (0 : K → ℕ) := isWeightedHomogeneous_C _ a
  have hH : (∑ i : Fin r, (X i : MvPolynomial (Fin r) ℝ) ^ m).IsHomogeneous m :=
    IsHomogeneous.sum _ _ _ fun i _ => by
      simpa using (isHomogeneous_X ℝ i).pow m
  have h := (GlobalTheory.T.divisor_cycle_substitution O ϖ hϖ K ι P d hP 0 0 (C a) (C a) hC hC (C_not_mem hP ha) (C_not_mem hP ha)
    (Fin r) (Fin r) cls (fun t i => if t = i then -1 else 0) _ m hH Q hQ).2
  have e1 : (fun t : Fin r => ∑ i, (if t = i then (-1 : ℤ) else 0) • cls i) = fun i => -cls i := by
    funext t
    simp
  have e2 : aeval (fun t : Fin r => ∑ i, (C (((if t = i then (-1 : ℤ) else 0 : ℤ)) : ℝ) * X i :
      MvPolynomial (Fin r) ℝ)) (∑ i : Fin r, (X i : MvPolynomial (Fin r) ℝ) ^ m) =
      ∑ i : Fin r, (-(X i : MvPolynomial (Fin r) ℝ)) ^ m := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, apply_ite]
  rw [e1, e2] at h
  exact h

end

end GlobalTheory.CompanionTheory.Ar.Num.FlagLocalM3

namespace GlobalTheory.CompanionTheory.Ar.Num


open GlobalTheory.CompanionTheory.Ar.Num.FlagLocalM3 in
theorem flag_m3_of_local_m3 : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (p : ℕ), (p : O) ≠ 0 → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (j j' : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (T : LocPair ι O (Ψ × Fin (j + j'))) (lie : ∀ σ, LocPair ι O (Fin ((Sum.elim (fun _ : Ψ => j) (fun _ : Ψ => j')) σ))) (om : ∀ σ, LocPair ι O (Fin ((Sum.elim (fun _ : Ψ => j') (fun _ : Ψ => j)) σ))), (∀ τ, lie (Sum.inl τ) = T.comp fun i : Fin j => (τ, Fin.castAdd j' i)) → (∀ τ, om (Sum.inl τ) = T.comp fun i : Fin j' => (τ, Fin.natAdd j i)) → (∀ τ k Q, Q.length + k = d + 1 → laNum P (p : O) (lie (Sum.inr τ)).x k Q = laNum P (p : O) (fun i : Fin j' => -T.x (τ, Fin.natAdd j i)) k Q) → LabelChernComparison P d p φ lie om → FlagChernComparison P d p j φ T := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP p hp Ψ _ _ j j' φ T lie om hl ho hr hM τ k hk Q hQ
  set Z := divCycle P (C (p : O)) with hZ
  have hm : k - 1 + Q.length = d := by omega

  have hlab : ∀ τ' : Ψ ⊕ Ψ, ((laNum P (p : O) (lie τ').x k Q : ℤ) : ℝ) =
      (k : ℝ) * cycNum Z T.x (liePs j (k - 1) τ') Q := by
    rintro (t | t)
    · have e : (lie (Sum.inl t)).x = fun i : Fin j => T.x (t, Fin.castAdd j' i) := by
        rw [hl t]; rfl
      have e' : ((laNum P (p : O) (lie (Sum.inl t)).x k Q : ℤ) : ℝ) =
          ((laNum P (p : O) (fun i : Fin j => T.x (t, Fin.castAdd j' i)) k Q : ℤ) : ℝ) :=
        congrArg (fun y : Fin j → K → ℤ => ((laNum P (p : O) y k Q : ℤ) : ℝ)) e
      rw [e', laNum_eq, liePs_inl, (GlobalTheory.T.cycle_number_rename).1 O K ι _ _ _ Z T.x]
      rfl
    · rw [hr t k Q hQ, laNum_eq, cycNum_neg hϖ hP hp _ _ Q hm, liePs_inr,
        (GlobalTheory.T.cycle_number_rename).1 O K ι _ _ _ Z T.x]
      rfl
  have hL := hM k hk Q hQ (Sum.inl τ)
  have e1 : (lie (Sum.inl τ)).ck P k Q = (T.comp fun i : Fin j => (τ, Fin.castAdd j' i)).ck P k Q :=
    congrArg (fun L : LocPair ι O (Fin j) => L.ck P k Q) (hl τ)
  have e2 : (om (Sum.inl τ)).ck P k Q = (T.comp fun i : Fin j' => (τ, Fin.natAdd j i)).ck P k Q :=
    congrArg (fun L : LocPair ι O (Fin j') => L.ck P k Q) (ho τ)
  have hadd := GlobalTheory.T.local_pair_split_sum O K ι j j' (T.comp fun i : Fin (j + j') => (τ, i)) P k Q
  have hlin := GlobalTheory.T.cycle_number_linear O K ι (Ψ × Fin (j + j')) Z T.x Q
  rw [e1, e2] at hL
  have hleft : (((T.comp fun i : Fin (j + j') => (τ, i)).ck P k Q : ℤ) : ℝ) =
      (((T.comp fun i : Fin j => (τ, Fin.castAdd j' i)).ck P k Q : ℤ) : ℝ) +
      (((T.comp fun i : Fin j' => (τ, Fin.natAdd j i)).ck P k Q : ℤ) : ℝ) := by
    rw [hadd]
    push_cast
    rfl
  rw [hleft, hL, bracket]
  rw [hlin.2.1, hlin.2.2.1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ' _ => ?_
  rw [hlin.2.1, hlab τ']
  ring

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagM3FromLocalStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_m3_from_local : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (p : ℕ), (p : O) ≠ 0 → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (j j' : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (T : LocPair ι O (Ψ × Fin (j + j'))) (lie : ∀ σ, LocPair ι O (Fin ((Sum.elim (fun _ : Ψ => j) (fun _ : Ψ => j')) σ))) (om : ∀ σ, LocPair ι O (Fin ((Sum.elim (fun _ : Ψ => j') (fun _ : Ψ => j)) σ))), (∀ τ, lie (Sum.inl τ) = T.comp fun i : Fin j => (τ, Fin.castAdd j' i)) → (∀ τ, om (Sum.inl τ) = T.comp fun i : Fin j' => (τ, Fin.natAdd j i)) → (∀ τ k Q, Q.length + k = d + 1 → laNum P (p : O) (lie (Sum.inr τ)).x k Q = laNum P (p : O) (fun i : Fin j' => -T.x (τ, Fin.natAdd j i)) k Q) → LabelChernComparison P d p φ lie om → FlagChernComparison P d p j φ T := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.flag_m3_of_local_m3 | exact GlobalTheory.CompanionTheory.Ar.Num.flag_m3_of_local_m3 | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.flag_m3_of_local_m3 <;> assumption)
end
