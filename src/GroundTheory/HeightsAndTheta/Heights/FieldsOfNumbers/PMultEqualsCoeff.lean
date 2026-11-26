module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegreeBound
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyCN

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMultEqualsCoeff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter

universe u

namespace MultEqualsCoeff

variable {K : Type*}

theorem tendsto_sub (c : K → ℤ) : Tendsto (fun m : K → ℤ => m - c) atTop atTop :=
  tendsto_atTop_atTop.2 fun a => ⟨a + c, fun _ hm => le_sub_iff_add_le.mpr hm⟩

theorem foldr_diffStep_sum {J : Type*} (s : Finset J) (f : J → (K → ℤ) → ℤ) :
    ∀ L : List (K → ℤ), L.foldr diffStep (∑ j ∈ s, f j) = ∑ j ∈ s, L.foldr diffStep (f j)
  | [] => rfl
  | b :: L => by
      simp only [List.foldr_cons]
      rw [foldr_diffStep_sum s f L]
      funext m
      simp only [diffStep, Finset.sum_apply, Finset.sum_sub_distrib]

theorem foldr_diffStep_zero : ∀ L : List (K → ℤ), L.foldr diffStep (0 : (K → ℤ) → ℤ) = 0
  | [] => rfl
  | b :: L => by
      simp only [List.foldr_cons, foldr_diffStep_zero L]
      funext m
      simp [diffStep]

theorem foldr_diffStep_shift (h : (K → ℤ) → ℤ) (c : K → ℤ) :
    ∀ L : List (K → ℤ),
      L.foldr diffStep (fun m => h (m - c)) = fun m => L.foldr diffStep h (m - c)
  | [] => rfl
  | b :: L => by
      simp only [List.foldr_cons]
      rw [foldr_diffStep_shift h c L]
      funext m
      simp only [diffStep, sub_right_comm m b c]

theorem foldr_diffStep_eventuallyEq {h g : (K → ℤ) → ℤ} (e : h =ᶠ[atTop] g) :
    ∀ L : List (K → ℤ), L.foldr diffStep h =ᶠ[atTop] L.foldr diffStep g
  | [] => e
  | b :: L => by
      have e' := foldr_diffStep_eventuallyEq e L
      filter_upwards [e', (tendsto_sub b).eventually e'] with m h1 h2
      simp only [List.foldr_cons, diffStep]
      rw [h1, h2]

theorem exists_nat_of_nonneg_of_lt {x : WithBot (WithTop ℤ)} {n : ℕ} (h0 : 0 ≤ x)
    (h : x < n) : ∃ d : ℕ, x = d ∧ d < n := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h0 (not_le.mpr (WithBot.bot_lt_coe _))
  | coe y =>
    induction y using WithTop.recTopCoe with
    | top => exact absurd h (not_lt.mpr (by simp))
    | coe z =>
      have hz0 : 0 ≤ z := by exact_mod_cast h0
      obtain ⟨d, rfl⟩ := Int.eq_ofNat_of_zero_le hz0
      have hdn : (d : ℤ) < n := by exact_mod_cast h
      exact ⟨d, by norm_cast, by omega⟩

variable [Fintype K] [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]


omit [DecidableEq K] in
theorem relDim_nonneg_of_card_le (I : Ideal (MRing ι F))
    (h : ((Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι F ⧸ I)) : 0 ≤ relDim I := by
  unfold relDim
  generalize ringKrullDim (MRing ι F ⧸ I) = x at h ⊢
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h (not_le.mpr (WithBot.bot_lt_coe _))
  | coe y =>
    induction y using ENat.recTopCoe with
    | top => exact WithBot.coe_le_coe.mpr le_top
    | coe e =>
      have he : Fintype.card K ≤ e := by exact_mod_cast h
      have : (0 : WithTop ℤ) ≤ WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) (e : ℕ∞) := by
        change (0 : WithTop ℤ) ≤ (((e : ℤ) - Fintype.card K : ℤ) : WithTop ℤ)
        exact_mod_cast (by omega : (0 : ℤ) ≤ (e : ℤ) - Fintype.card K)
      exact WithBot.coe_le_coe.mpr this

theorem hilbFn_eventually_zero_of_not_relevant (I : Ideal (MRing ι F)) (hI : ¬ IsRelevant I) :
    ∀ᶠ m in atTop, hilbFn I m = 0 := by
  simp only [IsRelevant, not_forall, not_exists, not_not] at hI
  obtain ⟨k, hk⟩ := hI
  filter_upwards [eventually_ge_atTop (1 : K → ℤ)] with m hm
  unfold hilbFn
  split_ifs with h0
  · have hbot : gradedPiece I (fun k => (m k).toNat) = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨f, hf, rfl⟩
      rw [Submodule.mem_bot, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem, MvPolynomial.as_sum f]
      refine Ideal.sum_mem _ fun s hs => ?_
      have hw := (mem_weightedHomogeneousSubmodule _ _ _ _).mp hf (mem_support_iff.mp hs)
      obtain ⟨v, hv, hvk⟩ : ∃ v ∈ s.support, v.1 = k := by
        by_contra hne
        simp only [not_exists, not_and] at hne
        have h1 := congrFun hw k
        rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply,
          Finset.sum_eq_zero fun v hv => by
            simp [blockWeight, Ne.symm (hne v hv)]] at h1
        have := hm k
        simp only [Pi.one_apply] at this
        omega
      have hle : Finsupp.single v 1 ≤ s := by
        rw [Finsupp.single_le_iff]
        exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)
      have hX : (X v : MRing ι F) ∈ I := by
        obtain ⟨k', i⟩ := v
        subst hvk
        exact hk i
      have e : monomial s (AddMonoidAlgebra.coeff f s) = X v * monomial (s - Finsupp.single v 1) (AddMonoidAlgebra.coeff f s) := by
        rw [show (X v : MRing ι F) = monomial (Finsupp.single v 1) 1 from rfl, monomial_mul,
          one_mul, add_tsub_cancel_of_le hle]
      rw [e]
      exact I.mul_mem_right _ hX
    rw [hbot]
    simp
  · rfl

end MultEqualsCoeff


open MultEqualsCoeff in
theorem MultEqualsCoeff.proof (h1 : PrimeFiltration.Statement.{u})
    (h2 : MixedDiffConst.Statement.{u}) (h3 : RelevantPrimeDimGe.Statement.{u}) :
    MultEqualsCoeff.Statement.{u} := by
  intro F _ K _ _ ι _ I hI hrel n hn bs
  classical
  obtain ⟨r, Q, c, hQ, hsum, hmult, hcase⟩ := h1 F K ι I hI
  let top : Ideal (MRing ι F) → Prop := fun W => W ∈ I.minimalPrimes ∧ IsRelevant W ∧ relDim W = n
  let val : Ideal (MRing ι F) → ℤ := fun W => if top W then intNum F W bs else 0
  have hpiece : ∀ j, ∀ᶠ m in atTop,
      mixedDiff bs (hilbFn (Q j)) (m - fun k => (c j k : ℤ)) = val (Q j) := by
    intro j
    refine (tendsto_sub fun k => (c j k : ℤ)).eventually
      (p := fun x => mixedDiff bs (hilbFn (Q j)) x = val (Q j)) ?_
    obtain ⟨hpr, hhom, -⟩ := hQ j
    by_cases hr : IsRelevant (Q j)
    · rcases (hcase j).resolve_left (not_not.mpr hr) with hlt | ⟨hmin, heq⟩
      · rw [hn] at hlt
        have hnt : ¬ top (Q j) := fun ht => lt_irrefl _ (ht.2.2 ▸ hlt)
        simp only [val, if_neg hnt]
        obtain ⟨d, hd, hdn⟩ := exists_nat_of_nonneg_of_lt
          (relDim_nonneg_of_card_le (Q j) (h3 F K ι (Q j) ⟨hpr, hhom, hr⟩)) hlt
        exact (h2 F K ι (Q j) hhom hr d hd).2 n hdn bs
      · have ht : top (Q j) := ⟨hmin, hr, heq.trans hn⟩
        simp only [val, if_pos ht]
        exact (h2 F K ι (Q j) hhom hr n (heq.trans hn)).1 bs
    · have hnt : ¬ top (Q j) := fun ht => hr ht.2.1
      simp only [val, if_neg hnt]
      filter_upwards [foldr_diffStep_eventuallyEq
        (hilbFn_eventually_zero_of_not_relevant (Q j) hr) (List.ofFn bs)] with m hm
      unfold mixedDiff
      rw [hm]
      exact congrFun (foldr_diffStep_zero _) m
  have hI' : ∀ᶠ m in atTop, mixedDiff bs (hilbFn I) m = ∑ j, val (Q j) := by
    have e1 : mixedDiff bs (hilbFn I) =ᶠ[atTop]
        mixedDiff bs (∑ j, fun m => hilbFn (Q j) (m - fun k => (c j k : ℤ))) := by
      apply foldr_diffStep_eventuallyEq
      filter_upwards [hsum] with m hm
      rw [hm, Finset.sum_apply]
    filter_upwards [e1, eventually_all.2 hpiece] with m hm hall
    rw [hm, mixedDiff, foldr_diffStep_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [foldr_diffStep_shift]
    exact hall j
  have hval : intNum F I bs = ∑ j, val (Q j) := by
    obtain ⟨m, ha, hb⟩ := (((h2 F K ι I hI hrel n hn).1 bs).and hI').exists
    rw [← ha, hb]
  have hsupp : (Function.support fun W => topCycle I n W * intNum F W bs) ⊆
      (Finset.univ.image Q : Set (Ideal (MRing ι F))) := by
    intro W hW
    by_contra hWQ
    apply hW
    simp only [topCycle]
    split_ifs with h
    · have hm := hmult W h.1 h.2.1 (h.2.2.trans hn.symm)
      have h0 : (Finset.univ.filter fun j => Q j = W) = ∅ := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        rintro rfl
        exact hWQ (by simp)
      rw [h0, Finset.card_empty] at hm
      rw [← hm]
      simp
    · simp
  rw [hval, cycEval, finsum_eq_sum_of_support_subset _ hsupp,
    ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image Q) (g := Q)
      (fun j _ => Finset.mem_image_of_mem Q (Finset.mem_univ j)) (fun j => val (Q j))]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Finset.sum_congr rfl fun j hj => by rw [(Finset.mem_filter.1 hj).2], Finset.sum_const,
    nsmul_eq_mul]
  simp only [topCycle, val, top]
  split_ifs with h
  · rw [← hmult W h.1 h.2.1 (h.2.2.trans hn.symm)]
    simp
  · simp

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PHilbDegreeBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Lemmas

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isHomogeneous_of_isMultiHomogIdeal {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I) :
    I.IsHomogeneous (weightedHomogeneousSubmodule F (blockWeight ι)) := _root_.GroundTheory.Heights₂.Heights.NumbersDVR.HilbDegBound.isHomogeneous_of_isMultiHomogIdeal (I := I) hI

theorem isMultiHomogIdeal_sup_span {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I)
    {s : MRing ι F} {c : K → ℕ} (hs : IsMultiHomog s c) :
    IsMultiHomogIdeal (I ⊔ Ideal.span {s}) := by
  classical
  have h2 : (Ideal.span {s}).IsHomogeneous (weightedHomogeneousSubmodule F (blockWeight ι)) :=
    Ideal.homogeneous_span _ _ fun x hx => ⟨c, (Set.mem_singleton_iff.mp hx) ▸ hs⟩
  intro f hf b
  exact weightedHomogeneousComponent_mem_of_mem
    (h := (isHomogeneous_of_isMultiHomogIdeal hI).sup h2) (hp := hf) (m := b)


omit [Fintype K] [DecidableEq K] in
theorem colon_span_eq_of_isPrime {P : Ideal (MRing ι F)} (hP : P.IsPrime) {s : MRing ι F}
    (hs : s ∉ P) : P.colon (Ideal.span {s}) = P := by
  ext x
  rw [Ideal.mem_colon_span_singleton]
  exact ⟨fun h => (hP.mem_or_mem h).resolve_right hs, fun h => P.mul_mem_right s h⟩


omit [Fintype K] [DecidableEq K] in
theorem ringKrullDim_sup_span_add_one_le {P : Ideal (MRing ι F)} [P.IsPrime] {s : MRing ι F}
    (hs : s ∉ P) :
    ringKrullDim (MRing ι F ⧸ (P ⊔ Ideal.span {s})) + 1 ≤ ringKrullDim (MRing ι F ⧸ P) := by
  refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor le_sup_left)
    (Ideal.Quotient.factor_surjective le_sup_left) (r := Ideal.Quotient.mk P s) ?_ ?_
  · exact mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.subset_span rfl)

theorem lt_of_add_one_le_natCast {x : WithBot ℕ∞} {n : ℕ} (h : x + 1 ≤ n) : x < n := by
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have e : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]
      rw [e, ← WithBot.coe_natCast, WithBot.coe_le_coe] at h
      exact absurd h (not_le.mpr (ENat.natCast_lt_top n))
    | coe a =>
      have : a + 1 ≤ n := by exact_mod_cast h
      exact_mod_cast (show a < n by omega)

end Lemmas

theorem totalDegree_add_card_le_ringKrullDim (h1 : HilbEventuallyPoly.Statement.{u})
    (h2 : HilbExactDivide.Statement.{u}) (h3 : PolyOfDiffs.Statement)
    (h4 : PrimeFiltration.Statement.{u}) (hU : EventuallyPolyUnique.Statement)
    (hS : EventuallyPolyShift.Statement) (hZ : HilbIrrelevantZero.Statement.{u})
    (hD : RelevantPrimeDimGe.Statement.{u})
    (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (n : ℕ) :
    ∀ I : Ideal (MRing ι F), IsMultiHomogIdeal I → ringKrullDim (MRing ι F ⧸ I) < n →
      ∀ p : MvPolynomial K ℚ, EventuallyPoly (hilbFn I) p → p ≠ 0 →
      ((p.totalDegree + Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι F ⧸ I) := by
  induction n with
  | zero =>
    intro I _ hlt p hp hp0
    exfalso
    have hsub : Subsingleton (MRing ι F ⧸ I) := by
      by_contra hn
      rw [not_subsingleton_iff_nontrivial] at hn
      have h0 := ringKrullDim_nonneg_of_nontrivial (R := MRing ι F ⧸ I)
      exact absurd hlt (not_lt.mpr (by simpa using h0))
    have hz : ∀ m, hilbFn I m = 0 := by
      intro m
      unfold hilbFn
      split_ifs
      · rw [Module.finrank_zero_of_subsingleton, Nat.cast_zero]
      · rfl
    have : EventuallyPoly (hilbFn I) 0 := Filter.Eventually.of_forall fun m => by simp [hz]
    exact hp0 (hU K _ p 0 hp this)
  | succ n ih =>
    have prime : ∀ P : Ideal (MRing ι F), P.IsPrime → IsMultiHomogIdeal P →
        ringKrullDim (MRing ι F ⧸ P) < (n + 1 : ℕ) → ∀ p : MvPolynomial K ℚ,
        EventuallyPoly (hilbFn P) p → p ≠ 0 →
        ((p.totalDegree + Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι F ⧸ P) := by
      intro P hPp hPh hlt p hp hp0
      by_cases hrel : IsRelevant P
      swap
      · exfalso
        have : EventuallyPoly (hilbFn P) 0 := (hZ F K ι P hrel).mono fun m hm => by simp [hm]
        exact hp0 (hU K _ p 0 hp this)
      have hge := hD F K ι P ⟨hPp, hPh, hrel⟩
      choose i hi using hrel
      obtain ⟨N, hN⟩ : ∃ N : ℕ, ringKrullDim (MRing ι F ⧸ P) = N := by
        generalize ringKrullDim (MRing ι F ⧸ P) = x at hge hlt
        induction x using WithBot.recBotCoe with
        | bot => exact absurd hge (not_le.mpr (WithBot.bot_lt_coe _))
        | coe a =>
          induction a using ENat.recTopCoe with
          | top => exact absurd hlt (by simp)
          | coe a => exact ⟨a, rfl⟩
      have hKN : Fintype.card K ≤ N := by rw [hN] at hge; exact_mod_cast hge
      have hdiff : ∀ k, ∃ q : MvPolynomial K ℚ, (q = 0 ∨ q.totalDegree < N - Fintype.card K) ∧
          EventuallyPoly (diffStep (Pi.single k 1) (hilbFn P)) q := by
        intro k
        have hs : IsMultiHomog (X ⟨k, i k⟩ : MRing ι F) (Pi.single k 1) :=
          isWeightedHomogeneous_X _ _ _
        have hJ := isMultiHomogIdeal_sup_span hPh hs
        obtain ⟨q, hq⟩ := h1 F K ι _ hJ
        refine ⟨q, ?_, ?_⟩
        · by_cases hq0 : q = 0
          · exact Or.inl hq0
          right
          have hdrop := ringKrullDim_sup_span_add_one_le (P := P) (hi k)
          rw [hN] at hdrop
          have hNn : N ≤ n := by
            rw [hN] at hlt
            have : N < n + 1 := by exact_mod_cast hlt
            omega
          have hltJ := lt_of_add_one_le_natCast (hdrop.trans (by exact_mod_cast hNn))
          have hb := ih _ hJ hltJ q hq hq0
          have h' : ((q.totalDegree + Fintype.card K : ℕ) : WithBot ℕ∞) + 1 ≤ N := by
            refine le_trans ?_ hdrop
            gcongr
          have h'' : q.totalDegree + Fintype.card K + 1 ≤ N := by exact_mod_cast h'
          omega
        · refine hq.mono fun m hm => ?_
          have e := h2 F K ι P hPh (Pi.single k 1) _ hs m
          rw [colon_span_eq_of_isPrime hPp (hi k)] at e
          have ec : (fun k' => ((Pi.single k 1 : K → ℕ) k' : ℤ)) = (Pi.single k 1 : K → ℤ) := by
            funext k'
            by_cases h : k' = k <;> simp [h]
          rw [ec] at e
          simp only [diffStep]
          rw [e]
          exact hm
      obtain ⟨p', hp'deg, hp'⟩ := h3 K (hilbFn P) (N - Fintype.card K) hdiff
      have hpp' := hU K _ p p' hp hp'
      subst hpp'
      rw [hN]
      exact_mod_cast (show p.totalDegree + Fintype.card K ≤ N by omega)
    intro I hI hlt p hp hp0
    obtain ⟨r, Q, c, hQ, hsum, -, -⟩ := h4 F K ι I hI
    choose pj hpj using fun j => h1 F K ι (Q j) (hQ j).2.1
    choose q hq hqdeg hq0 using fun j => hS K _ (pj j) (fun k => (c j k : ℤ)) (hpj j)
    have hsumP : EventuallyPoly (hilbFn I) (∑ j, q j) := by
      have hall : ∀ᶠ m in Filter.atTop, ∀ j, (hilbFn (Q j) (m - fun k => (c j k : ℤ)) : ℚ) =
          eval (fun k => (m k : ℚ)) (q j) := Filter.eventually_all.mpr hq
      filter_upwards [hall, hsum] with m hm hm'
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hm', map_sum]
      push_cast
      exact Finset.sum_congr rfl fun j _ => hm j
    have hpq := hU K _ p _ hp hsumP
    have hDQ : ∀ j, q j ≠ 0 → (((q j).totalDegree + Fintype.card K : ℕ) : WithBot ℕ∞) ≤
        ringKrullDim (MRing ι F ⧸ I) := by
      intro j hj
      have hpj0 : pj j ≠ 0 := fun h => hj (hq0 j h)
      have hle : ringKrullDim (MRing ι F ⧸ Q j) ≤ ringKrullDim (MRing ι F ⧸ I) :=
        ringKrullDim_le_of_surjective (Ideal.Quotient.factor (hQ j).2.2)
          (Ideal.Quotient.factor_surjective _)
      have hb := prime (Q j) (hQ j).1 (hQ j).2.1 (hle.trans_lt hlt) (pj j) (hpj j) hpj0
      refine le_trans ?_ (hb.trans hle)
      have := hqdeg j
      exact_mod_cast (show (q j).totalDegree + Fintype.card K ≤
        (pj j).totalDegree + Fintype.card K by omega)
    classical
    set T := Finset.univ.filter fun j => q j ≠ 0 with hT
    have hpT : p = ∑ j ∈ T, q j := by rw [hpq, hT, Finset.sum_filter_ne_zero]
    have hTne : T.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h0
      rw [h0, Finset.sum_empty] at hpT
      exact hp0 hpT
    obtain ⟨j, hjT, hjmax⟩ := Finset.exists_max_image T (fun j => (q j).totalDegree) hTne
    have hdeg : p.totalDegree ≤ (q j).totalDegree := by
      rw [hpT]
      exact totalDegree_finsetSum_le hjmax
    refine le_trans ?_ (hDQ j (Finset.mem_filter.mp hjT).2)
    exact_mod_cast (show p.totalDegree + Fintype.card K ≤ (q j).totalDegree + Fintype.card K by
      omega)

theorem HilbDegreeBound.proof (h1 : HilbEventuallyPoly.Statement.{u})
    (h2 : HilbExactDivide.Statement.{u}) (h3 : PolyOfDiffs.Statement)
    (h4 : PrimeFiltration.Statement.{u}) (hU : EventuallyPolyUnique.Statement)
    (hS : EventuallyPolyShift.Statement) (hZ : HilbIrrelevantZero.Statement.{u})
    (hD : RelevantPrimeDimGe.Statement.{u}) : HilbDegreeBound.Statement.{u} := by
  intro F _ K _ _ ι _ I hI
  refine ⟨fun _ p hp hp0 => ?_, fun hrel => hZ F K ι I hrel⟩
  have key := fun n => totalDegree_add_card_le_ringKrullDim h1 h2 h3 h4 hU hS hZ hD F K ι n I hI
  unfold relDim
  generalize hx : ringKrullDim (MRing ι F ⧸ I) = x at key
  induction x using WithBot.recBotCoe with
  | bot =>
    have := key 0 (WithBot.bot_lt_coe _) p hp hp0
    exact absurd this (not_le.mpr (WithBot.bot_lt_coe _))
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact WithBot.coe_le_coe.mpr le_top
    | coe N =>
      have := key (N + 1) (by exact_mod_cast Nat.lt_succ_self N) p hp hp0
      have hle : p.totalDegree + Fintype.card K ≤ N := by exact_mod_cast this
      show ((p.totalDegree : ℕ) : WithBot (WithTop ℤ)) ≤
        (((N : ℤ) - Fintype.card K : ℤ) : WithTop ℤ)
      have : (p.totalDegree : ℤ) ≤ (N : ℤ) - Fintype.card K := by omega
      exact_mod_cast this

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end
