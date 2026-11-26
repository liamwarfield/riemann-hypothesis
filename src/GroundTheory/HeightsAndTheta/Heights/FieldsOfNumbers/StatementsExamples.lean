module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.NoetherCharP

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsExamples
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem relDim_bot {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {F : Type*} [Field F] :
    relDim (⊥ : Ideal (MRing ι F)) =
      (((Fintype.card (Σ k, ι k) : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) := by
  unfold relDim
  rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field, zero_add,
    Nat.card_eq_fintype_card]
  rfl

abbrev ProjIdx (N : ℕ) : Unit → Type := fun _ => Fin (N + 1)

theorem relDim_projectiveSpace {F : Type*} [Field F] (N : ℕ) :
    relDim (⊥ : Ideal (MRing (ProjIdx N) F)) = (N : WithBot (WithTop ℤ)) := by
  rw [relDim_bot]
  simp [Fintype.card_sigma]
  rfl

def binomFn (N : ℕ) (t : ℤ) : ℤ := if 0 ≤ t then ((t.toNat + N).choose N : ℤ) else 0

theorem binomFn_sub (N : ℕ) (t : ℤ) :
    binomFn (N + 1) t - binomFn (N + 1) (t - 1) = binomFn N t := by
  unfold binomFn
  rcases lt_trichotomy t 0 with h | rfl | h
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp
  · simp
  · obtain ⟨u, rfl⟩ : ∃ u : ℕ, t = u + 1 := ⟨(t - 1).toNat, by omega⟩
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
    have h1 : ((u : ℤ) + 1).toNat = u + 1 := by omega
    have h2 : ((u : ℤ) + 1 - 1).toNat = u := by omega
    have h3 := Nat.choose_succ_succ (u + N + 1) N
    rw [h1, h2, show u + 1 + (N + 1) = u + N + 1 + 1 by omega, h3,
      show u + (N + 1) = u + N + 1 by omega, show u + 1 + N = u + N + 1 by omega]
    push_cast
    ring

theorem weight_projIdx (N : ℕ) (d : (Σ _ : Unit, ProjIdx N ()) →₀ ℕ) :
    Finsupp.weight (blockWeight (ProjIdx N)) d () = ∑ x, d x := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply]
  simp [blockWeight]

theorem finrank_gradedPiece_projectiveSpace (F : Type*) [Field F] (N a : ℕ) :
    Module.finrank F (gradedPiece (⊥ : Ideal (MRing (ProjIdx N) F)) (fun _ => a)) =
      (a + N).choose N := by
  have hinj : Function.Injective
      (Ideal.Quotient.mkₐ F (⊥ : Ideal (MRing (ProjIdx N) F))).toLinearMap := by
    intro x y h
    simpa [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq, sub_eq_zero] using h
  unfold gradedPiece
  rw [← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _),
    weightedHomogeneousSubmodule_eq_finsupp_supported]
  let s : Set ((Σ _ : Unit, ProjIdx N ()) →₀ ℕ) :=
    {d | Finsupp.weight (blockWeight (ProjIdx N)) d = fun _ => a}
  let e : s ≃ (Finset.univ.finsuppAntidiag a : Finset ((Σ _ : Unit, ProjIdx N ()) →₀ ℕ)) :=
    Equiv.subtypeEquivRight fun d => by
      rw [Finset.mem_finsuppAntidiag]
      simp only [s, Set.mem_ofPred_eq, Finset.subset_univ, and_true]
      constructor
      · intro h
        rw [← weight_projIdx]
        exact congrFun h ()
      · intro h
        funext u
        rw [weight_projIdx]
        exact h
  have : Fintype s := Fintype.ofEquiv _ e.symm
  rw [LinearEquiv.finrank_eq (AddMonoidAlgebra.supportedEquivFinsupp (R := F) (S := F) s), Module.finrank_finsupp_self,
    Fintype.card_congr e, Fintype.card_coe, Finset.card_finsuppAntidiag_nat_eq_choose]
  simp [Fintype.card_sigma]
  rw [add_comm, Nat.choose_symm_add]

theorem hilbFn_projectiveSpace (F : Type*) [Field F] (N : ℕ) (m : Unit → ℤ) :
    hilbFn (⊥ : Ideal (MRing (ProjIdx N) F)) m = binomFn N (m ()) := by
  unfold hilbFn binomFn
  by_cases hm : 0 ≤ m ()
  · rw [if_pos (fun k => hm), if_pos hm]
    have : (fun k => (m k).toNat) = fun _ : Unit => (m ()).toNat := rfl
    rw [this, finrank_gradedPiece_projectiveSpace]
  · rw [if_neg (fun h => hm (h ())), if_neg hm]

theorem foldr_diffStep_binomFn (j N : ℕ) :
    (List.replicate j (1 : Unit → ℤ)).foldr diffStep (fun m => binomFn (N + j) (m ())) =
      fun m => binomFn N (m ()) := by
  induction j generalizing N with
  | zero => simp
  | succ j ih =>
    rw [List.replicate_succ, List.foldr_cons, show N + (j + 1) = (N + 1) + j by omega, ih]
    funext m
    simp only [diffStep, Pi.sub_apply, Pi.one_apply]
    exact binomFn_sub N (m ())

theorem intNum_projectiveSpace (F : Type*) [Field F] (N : ℕ) :
    intNum F (⊥ : Ideal (MRing (ProjIdx N) F)) (fun _ : Fin N => (1 : Unit → ℤ)) = 1 := by
  have hh : hilbFn (⊥ : Ideal (MRing (ProjIdx N) F)) = fun m => binomFn (0 + N) (m ()) := by
    funext m
    rw [zero_add, hilbFn_projectiveSpace]
  unfold intNum mixedDiff
  rw [List.ofFn_const, hh, foldr_diffStep_binomFn]
  have hev : ∀ᶠ m : Unit → ℤ in Filter.atTop, binomFn 0 (m ()) = 1 :=
    (Filter.eventually_ge_atTop 0).mono fun m hm => by
      have : (0 : ℤ) ≤ m () := hm ()
      simp [binomFn, this]
  have hex : ∃ c, ∀ᶠ m : Unit → ℤ in Filter.atTop, binomFn 0 (m ()) = c := ⟨1, hev⟩
  unfold eventualValue
  rw [dite_eq_left hex]
  obtain ⟨m, h1, h2⟩ := (hex.choose_spec.and hev).exists
  exact h1.symm.trans h2

theorem blockIncl_injective {K K' : Type*} (j : K ↪ K') (ι' : K' → Type*) :
    Function.Injective (blockIncl j ι') := by
  rintro ⟨a, x⟩ ⟨b, y⟩ h
  simp only [blockIncl, Sigma.mk.inj_iff] at h
  obtain ⟨h1, h2⟩ := h
  cases j.injective h1
  rw [eq_of_heq h2]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsRename
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Split

variable {K K' : Type}

end Split

def RenameMultiHomog.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K K' : Type) [DecidableEq K] [DecidableEq K'] (j : K ↪ K')
    (ι : K → Type) (ι' : K' → Type) (g : (Σ k, ι k) → (Σ k', ι' k')), (∀ v, (g v).1 = j v.1) →
    ∀ (f : MRing ι R) (d : K → ℕ), IsMultiHomog f d →
      IsMultiHomog (rename g f) (Function.extend j d 0)

def RenameHilbFn.Statement : Prop :=
  ∀ (F : Type u) [Field F] (S K' : Type) [DecidableEq S] [DecidableEq K'] (κ : S → Type)
    (ι' : K' → Type) (E : S ≃ K') (σ : (Σ s, κ s) ≃ (Σ k', ι' k')), (∀ v, (σ v).1 = E v.1) →
    ∀ (P : Ideal (MRing ι' F)) (m : S → ℤ),
      hilbFn (P.comap (rename σ)) m = hilbFn P (m ∘ E.symm)

def RenameIntNum.Statement : Prop :=
  ∀ (F : Type u) [Field F] (S K' : Type) [DecidableEq S] [DecidableEq K'] (κ : S → Type)
    (ι' : K' → Type) (E : S ≃ K') (σ : (Σ s, κ s) ≃ (Σ k', ι' k')), (∀ v, (σ v).1 = E v.1) →
    ∀ (P : Ideal (MRing ι' F)) (n : ℕ) (bs : Fin n → S → ℤ),
      intNum F (P.comap (rename σ)) bs = intNum F P (fun i => bs i ∘ E.symm)

def RenameMultiProjPrime.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (S K' : Type) [DecidableEq S] [DecidableEq K'] (κ : S → Type)
    (ι' : K' → Type) (E : S ≃ K') (σ : (Σ s, κ s) ≃ (Σ k', ι' k')), (∀ v, (σ v).1 = E v.1) →
    ∀ P : Ideal (MRing ι' R), IsMultiProjPrime P → IsMultiProjPrime (P.comap (rename σ))

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PGradedFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

section

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem finite_monomials_of_multidegree (m : K → ℕ) :
    {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m}.Finite := by
  apply (Finsupp.finite_of_degree_eq (∑ k, m k)).subset
  intro d hd
  simp only [Set.mem_ofPred_eq] at hd ⊢
  rw [← hd, Finsupp.weight_eq_sum, Finsupp.degree_eq_sum, Finset.sum_fn, Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [blockWeight, Pi.single_apply]

theorem finiteDimensional_multiHomogForms (F : Type*) [Field F] (m : K → ℕ) :
    FiniteDimensional F (weightedHomogeneousSubmodule F (blockWeight ι) m) := by
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
  have := (finite_monomials_of_multidegree (ι := ι) m).to_subtype
  exact Module.Finite.of_basis
    (basisRestrictSupport F {d | Finsupp.weight (blockWeight ι) d = m})

end

theorem GradedFinite.proof : GradedFinite.Statement := by
  intro F _ K _ _ ι _ I m
  have hfin := finiteDimensional_multiHomogForms (ι := ι) F m
  have hP : FiniteDimensional F (gradedPiece I m) := by
    unfold gradedPiece
    exact Module.Finite.iff_fg.mpr
      ((Module.Finite.iff_fg.mp hfin).map (Ideal.Quotient.mkₐ F I).toLinearMap)
  refine ⟨hP, ?_⟩
  unfold hilbFn
  rw [if_pos fun k => Int.natCast_nonneg (m k)]
  simp only [Int.toNat_natCast]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumSymm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open GroundTheory.Heights₂.Heights.NumbersDVR

section

variable {K : Type*}

theorem diffStep_comm (a b : K → ℤ) (h : (K → ℤ) → ℤ) :
    diffStep a (diffStep b h) = diffStep b (diffStep a h) := by
  funext m
  simp only [diffStep, sub_sub, add_comm a b]
  ring

instance diffStep_leftCommutative :
    LeftCommutative (diffStep : (K → ℤ) → ((K → ℤ) → ℤ) → (K → ℤ) → ℤ) :=
  ⟨diffStep_comm⟩

theorem mixedDiff_comp_perm {n : ℕ} (bs : Fin n → K → ℤ) (σ : Equiv.Perm (Fin n))
    (h : (K → ℤ) → ℤ) : mixedDiff (bs ∘ σ) h = mixedDiff bs h := by
  unfold mixedDiff
  exact (σ.ofFn_comp_perm bs).foldr_eq h

end

theorem IntNumSymm.proof : IntNumSymm.Statement := by
  intro F _ K _ _ ι _ I n bs σ
  unfold intNum
  rw [mixedDiff_comp_perm]

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFContractedDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

namespace PFContracted

section Drop

variable {K : Type*} {ι : K → Type*} {F : Type*} [Field F]

theorem ringKrullDim_add_one_le {P Q : Ideal (MRing ι F)} [P.IsPrime] (hPQ : P ≤ Q)
    {f : MRing ι F} (hfP : f ∉ P) (hfQ : f ∈ Q) :
    ringKrullDim (MRing ι F ⧸ Q) + 1 ≤ ringKrullDim (MRing ι F ⧸ P) := by
  refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hPQ)
    (Ideal.Quotient.factor_surjective hPQ) (r := Ideal.Quotient.mk P f) ?_ ?_
  · exact mem_nonZeroDivisors_of_ne_zero (by rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem])
  · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hfQ

theorem ringKrullDim_lt_top [Finite K] [∀ k, Finite (ι k)] (Q : Ideal (MRing ι F)) :
    ringKrullDim (MRing ι F ⧸ Q) < ⊤ := by
  refine lt_of_le_of_lt (ringKrullDim_quotient_le Q) ?_
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field, zero_add]
  exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _)

end Drop

section Kill

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

def killBlocks (T : Finset K) : MRing ι F →ₐ[F] MRing ι F :=
  aeval fun v => if v.1 ∈ T then 0 else X v

theorem killBlocks_X (T : Finset K) (v : Σ k, ι k) :
    killBlocks (F := F) T (X v) = if v.1 ∈ T then 0 else X v := by
  simp [killBlocks]

theorem killBlocks_empty : killBlocks (ι := ι) (F := F) (∅ : Finset K) = AlgHom.id F _ := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [killBlocks_X]

theorem killBlocks_comp {T T' : Finset K} (h : T ⊆ T') :
    (killBlocks (ι := ι) (F := F) T').comp (killBlocks T) = killBlocks T' := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, killBlocks_X]
  by_cases hv : v.1 ∈ T
  · simp [hv, h hv]
  · simp [hv, killBlocks_X]

theorem killBlocks_monomial (T : Finset K) (d : (Σ k, ι k) →₀ ℕ) (c : F) :
    killBlocks T (monomial d c) =
      if ∀ v ∈ d.support, v.1 ∉ T then monomial d c else 0 := by
  rw [killBlocks, aeval_monomial]
  split_ifs with h
  · rw [monomial_eq, algebraMap_eq]
    congr 1
    exact Finsupp.prod_congr fun v hv => by rw [if_neg (h v hv)]
  · simp only [not_forall, not_not] at h
    obtain ⟨v, hv, hT⟩ := h
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero hv ?_)
    dsimp only
    rw [if_pos hT, zero_pow (Finsupp.mem_support_iff.mp hv)]

theorem coeff_killBlocks (T : Finset K) (q : MRing ι F) (d : (Σ k, ι k) →₀ ℕ) :
    AddMonoidAlgebra.coeff (killBlocks T q) d = if ∀ v ∈ d.support, v.1 ∉ T then AddMonoidAlgebra.coeff q d else 0 := by
  classical
  induction q using MvPolynomial.induction_on' with
  | monomial d' c =>
    rw [killBlocks_monomial, apply_ite (AddMonoidAlgebra.coeff · d), AddMonoidAlgebra.coeff_zero, coeff_monomial]
    by_cases hd : d' = d
    · subst hd
      simp
    · simp [hd]
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add]
    change AddMonoidAlgebra.coeff (killBlocks T p) d + AddMonoidAlgebra.coeff (killBlocks T q) d = _
    rw [hp, hq]
    split_ifs <;> simp

theorem weight_apply_eq_zero_iff (d : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blockWeight ι) d k = 0 ↔ ∀ v ∈ d.support, v.1 ≠ k := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Finset.sum_eq_zero_iff]
  refine forall₂_congr fun v hv => ?_
  simp only [Pi.smul_apply, smul_eq_mul, blockWeight, Pi.single_apply, mul_ite, mul_one, mul_zero]
  have := Finsupp.mem_support_iff.mp hv
  constructor
  · intro h hk
    rw [if_pos hk.symm] at h
    exact this h
  · intro h
    rw [if_neg (fun hk => h hk.symm)]

theorem killBlocks_of_isMultiHomog (T : Finset K) {p : MRing ι F} {b : K → ℕ}
    (hp : IsMultiHomog p b) : killBlocks T p = if ∀ k ∈ T, b k = 0 then p else 0 := by
  ext d
  rw [coeff_killBlocks]
  by_cases hd : AddMonoidAlgebra.coeff p d = 0
  · split_ifs <;> simp [hd]
  · have hw : Finsupp.weight (blockWeight ι) d = b := hp hd
    have key : (∀ v ∈ d.support, v.1 ∉ T) ↔ ∀ k ∈ T, b k = 0 := by
      constructor
      · intro h k hk
        rw [← hw, weight_apply_eq_zero_iff]
        intro v hv hvk
        exact h v hv (hvk ▸ hk)
      · intro h v hv hvT
        have := h v.1 hvT
        rw [← hw, weight_apply_eq_zero_iff] at this
        exact this v hv rfl
    by_cases hb : ∀ k ∈ T, b k = 0
    · rw [if_pos (key.mpr hb), if_pos hb]
    · rw [if_neg (fun h => hb (key.mp h)), if_neg hb, AddMonoidAlgebra.coeff_zero]
      rfl

theorem killBlocks_mem_of_isMultiHomogIdeal {Q : Ideal (MRing ι F)} (hQ : IsMultiHomogIdeal Q)
    (T : Finset K) {q : MRing ι F} (hq : q ∈ Q) : killBlocks T q ∈ Q := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← sum_weightedHomogeneousComponent (blockWeight ι) q,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp q), map_sum]
  refine Ideal.sum_mem _ fun b _ => ?_
  rw [killBlocks_of_isMultiHomog T (weightedHomogeneousComponent_isWeightedHomogeneous b q)]
  split_ifs
  · exact hQ q hq b
  · exact Q.zero_mem

def killIdeal (Q : Ideal (MRing ι F)) (T : Finset K) : Ideal (MRing ι F) :=
  Q.comap (killBlocks T)

theorem card_le_ringKrullDim [Fintype K] {Q : Ideal (MRing ι F)} [hQp : Q.IsPrime]
    (hQ : ∀ (T : Finset K) (q : MRing ι F), q ∈ Q → killBlocks T q ∈ Q) (hrel : IsRelevant Q) :
    (Fintype.card K : WithBot ℕ∞) ≤ ringKrullDim (MRing ι F ⧸ Q) := by
  choose i hi using hrel
  have hmono : ∀ {T T' : Finset K}, T ⊆ T' → killIdeal Q T ≤ killIdeal Q T' := by
    intro T T' h q hq
    change killBlocks T' q ∈ Q
    rw [← killBlocks_comp h]
    exact hQ T' _ hq
  have hprime : ∀ T, (killIdeal Q T).IsPrime := fun T => Ideal.comap_isPrime _ _
  have hchain : ∀ T : Finset K,
      ringKrullDim (MRing ι F ⧸ killIdeal Q T) + (T.card : WithBot ℕ∞) ≤
        ringKrullDim (MRing ι F ⧸ Q) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      have : killIdeal Q (∅ : Finset K) = Q := by
        ext q
        simp [killIdeal, killBlocks_empty]
      rw [this, Finset.card_empty, Nat.cast_zero, add_zero]
    | insert k T hk ih =>
      have := hprime T
      have hstep := ringKrullDim_add_one_le (P := killIdeal Q T) (Q := killIdeal Q (insert k T))
        (hmono (Finset.subset_insert k T)) (f := X ⟨k, i k⟩)
        (by
          change killBlocks T (X ⟨k, i k⟩) ∉ Q
          rw [killBlocks_X, if_neg hk]
          exact hi k)
        (by
          change killBlocks (insert k T) (X ⟨k, i k⟩) ∈ Q
          rw [killBlocks_X, if_pos (Finset.mem_insert_self k T)]
          exact Q.zero_mem)
      calc ringKrullDim (MRing ι F ⧸ killIdeal Q (insert k T)) + ((insert k T).card : WithBot ℕ∞)
          = (ringKrullDim (MRing ι F ⧸ killIdeal Q (insert k T)) + 1) + (T.card : WithBot ℕ∞) := by
            rw [Finset.card_insert_of_notMem hk, Nat.cast_add, Nat.cast_one, add_assoc,
              add_comm (1 : WithBot ℕ∞)]
        _ ≤ ringKrullDim (MRing ι F ⧸ killIdeal Q T) + (T.card : WithBot ℕ∞) := by gcongr
        _ ≤ _ := ih
  have := hprime Finset.univ
  have h0 := ringKrullDim_nonneg_of_nontrivial (R := MRing ι F ⧸ killIdeal Q Finset.univ)
  have := hchain Finset.univ
  rw [Finset.card_univ] at this
  calc (Fintype.card K : WithBot ℕ∞) = 0 + (Fintype.card K : WithBot ℕ∞) := (zero_add _).symm
    _ ≤ ringKrullDim (MRing ι F ⧸ killIdeal Q Finset.univ) + (Fintype.card K : WithBot ℕ∞) := by
        gcongr
    _ ≤ _ := this

end Kill

end PFContracted

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PNoetherIntegralClosure
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

theorem NoetherIntegralClosureFinite.proof : NoetherIntegralClosureFinite.Statement := by
  intro k A _ _ _ _ _ K _ _ _ L _ _ _ _ _
  refine finite_integralClosure_of_forall_mvPolynomial k A K L fun s L' _ _ _ _ _ => ?_
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with hp' | rfl
  · have : Fact p.Prime := ⟨hp'⟩
    exact finite_integralClosure_mvPolynomial_of_charP k p s L'
  · have : CharZero k := CharP.charP_to_charZero k
    exact finite_integralClosure_mvPolynomial_of_charZero k s L'

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PExistsForm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

theorem isMultiHomog_prod_pow {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {R : Type*}
    [CommRing R] (i : ∀ k, ι k) (n : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, i k⟩ : MRing ι R) ^ n k) n := by
  have h := IsWeightedHomogeneous.prod (R := R) Finset.univ
    (fun k => (X ⟨k, i k⟩ : MRing ι R) ^ n k) (fun k => n k • blockWeight ι ⟨k, i k⟩)
    (w := blockWeight ι) (fun k _ => (isWeightedHomogeneous_X R _ _).pow _)
  have hs : (∑ k, n k • blockWeight ι ⟨k, i k⟩) = n := by
    funext j
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [hs] at h
  exact h

theorem prod_pow_not_mem {K : Type} [Fintype K] {ι : K → Type} {R : Type*} [CommRing R]
    (P : Ideal (MRing ι R)) [hP : P.IsPrime] (i : ∀ k, ι k)
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι R) ∉ P) (n : K → ℕ) :
    (∏ k, (X ⟨k, i k⟩ : MRing ι R) ^ n k) ∉ P := by
  intro h
  obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
  exact hi k (hP.mem_of_pow_mem _ hk)

theorem ExistsForm.proof : ExistsForm.Statement := by
  intro F _ K _ _ ι _ P hP b
  have := hP.isPrime
  choose i hi using hP.relevant
  refine ⟨fun k => (b k).toNat, fun k => (-b k).toNat,
    ∏ k, (X ⟨k, i k⟩ : MRing ι F) ^ (b k).toNat, ∏ k, (X ⟨k, i k⟩ : MRing ι F) ^ (-b k).toNat,
    isMultiHomog_prod_pow i _, isMultiHomog_prod_pow i _, prod_pow_not_mem P i hi _,
    prod_pow_not_mem P i hi _, ?_⟩
  funext k
  simp only
  omega

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRational
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem divCycle_support_finite {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (f : MRing ι F) :
    (Function.support (divCycle P f)).Finite := by
  apply (Ideal.finite_minimalPrimes_of_isNoetherianRing (MRing ι F)
    (P ⊔ Ideal.span {f})).subset
  intro W hW
  by_contra h
  apply hW
  simp only [divCycle]
  rw [dite_eq_right (fun h' => h h'.1)]

theorem cycEval_ratDiv {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} [∀ k, Fintype (ι k)] (N : Ideal (MRing ι F) → ℤ) (P : Ideal (MRing ι F))
    (f g : MRing ι F) :
    cycEval N (ratDiv P f g) = cycEval N (divCycle P f) - cycEval N (divCycle P g) := by
  simp only [cycEval, ratDiv, sub_mul]
  apply finsum_sub_distrib
  · exact (divCycle_support_finite P f).subset (Function.support_mul_subset_left _ _)
  · exact (divCycle_support_finite P g).subset (Function.support_mul_subset_left _ _)

theorem CutRational.proof (h1 : CutRegular.Statement.{u}) (h2 : IntNumAdd.Statement.{u}) :
    CutRational.Statement.{u} := by
  intro F _ K _ _ ι _ P hP n hn bf bg f g hf hg hfP hgP bs
  have hadd := h2 F K ι P hP.multiHomog hP.relevant (n + 1) hn
    (Fin.snoc (α := fun _ => K → ℤ) bs 0) (Fin.last n)
    (fun k => (bf k : ℤ) - bg k) (fun k => (bg k : ℤ))
  simp only [Fin.update_snoc_last] at hadd
  have hsum : ((fun k => (bf k : ℤ) - bg k) + fun k => (bg k : ℤ)) = fun k => (bf k : ℤ) := by
    funext k; simp
  rw [hsum, h1 F K ι P hP n hn bf f hf hfP bs, h1 F K ι P hP n hn bg g hg hgP bs] at hadd
  rw [cycEval_ratDiv]
  linarith

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumAdd
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open GroundTheory.Heights₂.Heights.NumbersDVR

universe u

section

variable {K : Type*}

theorem diffStep_add (b b' : K → ℤ) (h : (K → ℤ) → ℤ) (m : K → ℤ) :
    diffStep (b + b') h m = diffStep b h m + diffStep b' h (m - b) := by
  simp only [diffStep, sub_add_eq_sub_sub]
  ring

theorem foldr_diffStep_set_add (h : (K → ℤ) → ℤ) (b b' : K → ℤ) :
    ∀ (L : List (K → ℤ)) (i : ℕ), i < L.length → ∀ m : K → ℤ,
      (L.set i (b + b')).foldr diffStep h m =
        (L.set i b).foldr diffStep h m + (L.set i b').foldr diffStep h (m - b)
  | [], i, hi, _ => absurd hi (Nat.not_lt_zero _)
  | a :: L, 0, _, m => by
      simp only [List.set_cons_zero, List.foldr_cons]
      exact diffStep_add b b' _ m
  | a :: L, i + 1, hi, m => by
      simp only [List.set_cons_succ, List.foldr_cons, diffStep]
      have hi' : i < L.length := by simpa using hi
      rw [foldr_diffStep_set_add h b b' L i hi' m, foldr_diffStep_set_add h b b' L i hi' (m - a),
        ← sub_right_comm m a b]
      ring

theorem ofFn_update {α : Type*} {n : ℕ} (bs : Fin n → α) (i : Fin n) (x : α) :
    List.ofFn (Function.update bs i x) = (List.ofFn bs).set i x := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [List.getElem_ofFn, List.getElem_set, Function.update_apply, Fin.ext_iff]
    split_ifs with h h' h'
    · rfl
    · exact absurd h.symm h'
    · exact absurd h'.symm h
    · rfl

theorem mixedDiff_update_add {n : ℕ} (bs : Fin n → K → ℤ) (i : Fin n) (b b' : K → ℤ)
    (h : (K → ℤ) → ℤ) (m : K → ℤ) :
    mixedDiff (Function.update bs i (b + b')) h m =
      mixedDiff (Function.update bs i b) h m + mixedDiff (Function.update bs i b') h (m - b) := by
  simp only [mixedDiff, ofFn_update]
  exact foldr_diffStep_set_add h b b' _ i (by simp) m

theorem tendsto_sub_const_atTop (b : K → ℤ) :
    Filter.Tendsto (fun m : K → ℤ => m - b) Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_atTop.2 fun c => ⟨c + b, fun _ hm => le_sub_iff_add_le.mpr hm⟩

theorem IntNumAdd.proof (h1 : MixedDiffConst.Statement.{u}) : IntNumAdd.Statement.{u} := by
  intro F _ K _ _ ι _ I hI hrel n hn bs i b b'
  have e := fun x : K → ℤ => (h1 F K ι I hI hrel n hn).1 (Function.update bs i x)
  have e' := (tendsto_sub_const_atTop b).eventually (e b')
  obtain ⟨m, h0, hb, hb'⟩ := ((e (b + b')).and ((e b).and e')).exists
  rw [← h0, ← hb, ← hb']
  exact mixedDiff_update_add bs i b b' _ m

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.HomFracDegZeroEqFunField
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

section

variable {F : Type*} [Field F] {K : Type*} {ι : K → Type*}

theorem relDim_eq_iff_hasRelDim [Fintype K] (I : Ideal (MRing ι F)) (n : ℕ) :
    relDim I = (n : WithBot (WithTop ℤ)) ↔ IndefiniteRowSideFullHecke.FieldNumbers.HasRelDim I n := by
  unfold relDim IndefiniteRowSideFullHecke.FieldNumbers.HasRelDim
  generalize ringKrullDim (MRing ι F ⧸ I) = x
  have e1 : ((n : ℕ) : WithBot (WithTop ℤ)) = some (some (n : ℤ)) := rfl
  have e2 : ((n + Fintype.card K : ℕ) : WithBot ℕ∞) = some (some (n + Fintype.card K)) := rfl
  rw [e1, e2]
  rcases x with _ | _ | e
  · simp [WithBot.map]
  · simp only [WithBot.map, WithTop.map, Option.map]
    exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  · simp only [WithBot.map, WithTop.map, Option.map]
    constructor
    · intro h
      have h1 : (e : ℤ) - Fintype.card K = n := Option.some.inj (Option.some.inj h)
      have h2 : e = n + Fintype.card K := by omega
      rw [h2]
      exact rfl
    · intro h
      have h1 : e = n + Fintype.card K := Option.some.inj (Option.some.inj h)
      subst h1
      congr 2
      push_cast
      ring

variable [DecidableEq K]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end
