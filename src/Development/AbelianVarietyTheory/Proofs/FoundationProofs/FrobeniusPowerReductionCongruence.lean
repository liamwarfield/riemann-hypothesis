module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Formalism.CyclotomicNorms.StatementI

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusPowerReductionCongruence
open GlobalTheory.K5 Polynomial
open scoped NNReal

namespace GlobalTheory

theorem aeval_qq_pow_sub_lt_one : ∀ (p : ℕ) [Fact p.Prime] (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ (v : Valuation Ωl ℝ≥0), (∀ x : Ωl, v x ≤ 1 ↔ IsInt (p := p) x) → v (p : Ωl) < 1 → ∀ (T : Tower p Ωl) (n : ℕ) (f : (O0 p)[X]), f.natDegree < p ^ n → v (aeval (T.qq n) f ^ (p ^ n) - algebraMap (O0 p) Ωl (∑ i ∈ Finset.range (p ^ n), f.coeff i ^ (p ^ n) * qO p ^ i)) < 1 := by
  intro p hp Ωl _ _ _ v hv hvp T n f hf
  classical
  have hpr : p.Prime := hp.out
  have hq : IsIntegral (O0 p) (T.qq n) :=
    IsIntegral.of_pow (pow_pos hpr.pos n) (by rw [GlobalTheory.K5.Basic.qq_pow]; exact isIntegral_algebraMap)
  let t : ℕ → integralClosure (O0 p) Ωl := fun i =>
    ⟨algebraMap (O0 p) Ωl (f.coeff i) * T.qq n ^ i, isIntegral_algebraMap.mul (hq.pow i)⟩
  have key : ∀ s : Finset ℕ, ∃ r : integralClosure (O0 p) Ωl,
      (∑ i ∈ s, t i) ^ p ^ n = ∑ i ∈ s, t i ^ p ^ n + p * r := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simp [zero_pow (pow_ne_zero _ hpr.ne_zero)]⟩
    | insert a s ha ih =>
      obtain ⟨r, hr⟩ := ih
      obtain ⟨r', hr'⟩ := exists_add_pow_prime_pow_eq hpr (t a) (∑ i ∈ s, t i) n
      exact ⟨r + t a * (∑ i ∈ s, t i) * r', by rw [Finset.sum_insert ha, Finset.sum_insert ha, hr', hr]; ring⟩
  obtain ⟨r, hr⟩ := key (Finset.range (p ^ n))
  have term : ∀ i, ((t i ^ p ^ n : integralClosure (O0 p) Ωl) : Ωl) =
      algebraMap (O0 p) Ωl (f.coeff i ^ p ^ n * qO p ^ i) := by
    intro i
    rw [SubmonoidClass.coe_pow, map_mul, map_pow, map_pow]
    show (algebraMap (O0 p) Ωl (f.coeff i) * T.qq n ^ i) ^ p ^ n = _
    rw [mul_pow, ← pow_mul, mul_comm i, pow_mul, GlobalTheory.K5.Basic.qq_pow]
  have e1 : aeval (T.qq n) f = ((∑ i ∈ Finset.range (p ^ n), t i : integralClosure (O0 p) Ωl) : Ωl) := by
    rw [aeval_eq_sum_range' hf]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def]
  have e2 : algebraMap (O0 p) Ωl (∑ i ∈ Finset.range (p ^ n), f.coeff i ^ p ^ n * qO p ^ i) =
      ((∑ i ∈ Finset.range (p ^ n), t i ^ p ^ n : integralClosure (O0 p) Ωl) : Ωl) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun i _ => (term i).symm
  have e3 : aeval (T.qq n) f ^ p ^ n - algebraMap (O0 p) Ωl
      (∑ i ∈ Finset.range (p ^ n), f.coeff i ^ p ^ n * qO p ^ i) = (p : Ωl) * (r : Ωl) := by
    rw [e1, e2, ← SubmonoidClass.coe_pow, hr]
    push_cast
    ring
  rw [e3, map_mul]
  have hr1 : v (r : Ωl) ≤ 1 := (hv _).2 r.2
  calc v (p : Ωl) * v (r : Ωl) ≤ v (p : Ωl) * 1 := by gcongr
    _ = v (p : Ωl) := mul_one _
    _ < 1 := hvp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffEqZeroOfSumPlusMinusRepsEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffEqZeroOfSumPlusMinusRepsEqZero
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

theorem coeff_eq_zero_of_sum_reps_eq_zero : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ))
    (b : SL(2, ℤ) → ℕ → ℂ), 0 < M → IsReps Γ s →
    (∀ (x : SL(2, ℤ)) (n : ℕ), b (x * ModularGroup.T) n = Complex.exp (2 * Real.pi * Complex.I / M) ^ n * b x n) →
    (∀ γ ∈ Γ, ∀ (x : SL(2, ℤ)) (n : ℕ), b (γ * x) n = b x n) → (∀ (x : SL(2, ℤ)) (n : ℕ), b (-x) n = -b x n) →
    (∀ i, ∑ n ∈ Finset.range M, b (s i) n = 0) → ∀ (x : SL(2, ℤ)) (n : ℕ), n < M → b x n = 0 := by
  intro M Γ r s b hM hs hT hΓ hneg hsum x n hn
  have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / M)) M :=
    Complex.isPrimitiveRoot_exp M hM.ne'
  set ζ := Complex.exp (2 * Real.pi * Complex.I / M) with hζ
  have hB : ∀ y : SL(2, ℤ), ∑ k ∈ Finset.range M, b y k = 0 := by
    intro y
    obtain ⟨i, γ, hγ, rfl | rfl⟩ := hs.1 y
    · simp only [hΓ γ hγ]; exact hsum i
    · simp only [hneg, hΓ γ hγ, Finset.sum_neg_distrib, hsum i, neg_zero]
  have hTm : ∀ (m : ℕ) (y : SL(2, ℤ)) (k : ℕ), b (y * ModularGroup.T ^ m) k = (ζ ^ k) ^ m * b y k := by
    intro m
    induction m with
    | zero => intro y k; simp
    | succ m ih => intro y k; rw [pow_succ, ← mul_assoc, hT, ih, pow_succ]; ring
  have hinj : Function.Injective (fun j : Fin M => ζ ^ (j : ℕ)) := by
    intro i j h
    exact Fin.ext (hprim.pow_inj i.2 j.2 h)
  have hv := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero (R := ℂ)
    (f := fun j : Fin M => ζ ^ (j : ℕ)) (v := fun j : Fin M => b x j) hinj (by
      intro i
      have h0 := hB (x * ModularGroup.T ^ (i : ℕ))
      rw [← Fin.sum_univ_eq_sum_range] at h0
      rw [← h0]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hTm, mul_comm])
  have := congrFun hv ⟨n, hn⟩
  simpa using this

end GlobalTheory.OddFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffEqZeroOfSumPlusMinusRepsEqZeroStatement
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_eq_zero_of_sum_plusMinusReps_eq_zero : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (b : SL(2, ℤ) → ℕ → ℂ), 0 < M → IsReps Γ s → (∀ (x : SL(2, ℤ)) (n : ℕ), b (x * ModularGroup.T) n = Complex.exp (2 * Real.pi * Complex.I / M) ^ n * b x n) → (∀ γ ∈ Γ, ∀ (x : SL(2, ℤ)) (n : ℕ), b (γ * x) n = b x n) → (∀ (x : SL(2, ℤ)) (n : ℕ), b (-x) n = -b x n) → (∀ i, ∑ n ∈ Finset.range M, b (s i) n = 0) → ∀ (x : SL(2, ℤ)) (n : ℕ), n < M → b x n = 0 := by
  first | exact @GlobalTheory.OddFrame.coeff_eq_zero_of_sum_reps_eq_zero | exact GlobalTheory.OddFrame.coeff_eq_zero_of_sum_reps_eq_zero | (intros; apply GlobalTheory.OddFrame.coeff_eq_zero_of_sum_reps_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubOnePowEqPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubOnePowEqPrime
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem valuation_one_sub_pow_le {L : Type} [Field L] (v : Valuation L ℝ≥0) (η : L)
    (hη : v η ≤ 1) (n : ℕ) : v (1 - η ^ n) ≤ v (1 - η) := by
  rw [← mul_neg_geom_sum, v.map_mul]
  have hs : v (∑ i ∈ Finset.range n, η ^ i) ≤ 1 := by
    apply Valuation.map_sum_le
    intro i _
    rw [v.map_pow]
    exact pow_le_one₀ (zero_le') hη
  calc v (1 - η) * v (∑ i ∈ Finset.range n, η ^ i) ≤ v (1 - η) * 1 := by gcongr
    _ = v (1 - η) := mul_one _

theorem valuation_sub_one_pow_eq_prime :
    ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ ζ : L,
      IsPrimitiveRoot ζ p → v (ζ - 1) ^ (p - 1) = v (p : L) := by
  intro L _ v p hp ζ hζ
  have hone : ∀ η : L, η ^ p = 1 → v η ≤ 1 := by
    intro η hη
    have h1 : v η ^ p = 1 := by rw [← v.map_pow, hη, v.map_one]
    exact le_of_eq ((pow_eq_one_iff_of_nonneg (zero_le') hp.ne_zero).mp h1)
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩
  have hprod := hζ.prod_one_sub_pow_eq_order
  have hterm : ∀ k ∈ Finset.range n, v (1 - ζ ^ (k + 1)) = v (ζ - 1) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [Valuation.map_sub_swap v ζ 1]
    have hc : (k + 1).Coprime (n + 1) := by
      have h := Nat.coprime_of_lt_prime (Nat.succ_ne_zero k) (by omega : k + 1 < n + 1) hp
      first | exact h | exact h.symm
    have hprim : IsPrimitiveRoot (ζ ^ (k + 1)) (n + 1) := hζ.pow_of_coprime _ hc
    apply le_antisymm
    · exact valuation_one_sub_pow_le v ζ (hone ζ hζ.pow_eq_one) (k + 1)
    · obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hζ.pow_eq_one
      calc v (1 - ζ) = v (1 - (ζ ^ (k + 1)) ^ i) := by rw [hi]
        _ ≤ v (1 - ζ ^ (k + 1)) :=
          valuation_one_sub_pow_le v _ (hone _ hprim.pow_eq_one) i
  rw [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, ← hprod, map_prod, Finset.prod_congr rfl hterm, Finset.prod_const,
    Finset.card_range]

end GlobalTheory.AlmostEt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubOnePowEqPrimeStatement
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_primitiveRoot_sub_one_pow_pred_eq : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ ζ : L, IsPrimitiveRoot ζ p → v (ζ - 1) ^ (p - 1) = v (p : L) := by
  first | exact @GlobalTheory.AlmostEt.valuation_sub_one_pow_eq_prime | exact GlobalTheory.AlmostEt.valuation_sub_one_pow_eq_prime | (intros; apply GlobalTheory.AlmostEt.valuation_sub_one_pow_eq_prime <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusPowerBasisIndependent
open GlobalTheory.K5 Polynomial
open scoped NNReal

namespace GlobalTheory

theorem laurent_terms_eq_zero_of_order_injOn {K ι : Type*} [Field K] (s : Finset ι)
    (f : ι → LaurentSeries K)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, f i ≠ 0 → f j ≠ 0 → (f i).order = (f j).order → i = j)
    (hsum : ∑ i ∈ s, f i = 0) : ∀ i ∈ s, f i = 0 := by
  classical
  by_contra hne
  push Not at hne
  have hnon : (s.filter fun i => f i ≠ 0).Nonempty := by
    obtain ⟨i, hi, hfi⟩ := hne
    exact ⟨i, Finset.mem_filter.2 ⟨hi, hfi⟩⟩
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image _ (fun i => (f i).order) hnon
  obtain ⟨his, hfi⟩ := Finset.mem_filter.1 hi
  have h1 : (∑ j ∈ s, f j).coeff (f i).order = (f i).coeff (f i).order := by
    rw [HahnSeries.coeff_sum]
    refine Finset.sum_eq_single_of_mem i his ?_
    intro j hj hji
    by_cases hfj : f j = 0
    · simp [hfj]
    · apply HahnSeries.coeff_eq_zero_of_lt_order
      exact lt_of_le_of_ne (hmin j (Finset.mem_filter.2 ⟨hj, hfj⟩))
        (fun h => hji (hinj i his j hj hfi hfj h).symm)
  rw [hsum] at h1
  exact hfi (HahnSeries.coeff_order_eq_zero.1 (by simpa using h1.symm))

theorem laurent_pow_indep_over_prime_pow_powers :
    ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (c : ℕ → LaurentSeries (ZMod p)), ∑ i ∈ Finset.range (p ^ n), c i ^ (p ^ n) * (HahnSeries.single (1 : ℤ) (1 : ZMod p)) ^ i = 0 → ∀ i < p ^ n, c i = 0 := by
  intro p _ n c hsum i hi
  have hX : ∀ j : ℕ, (HahnSeries.single (1 : ℤ) (1 : ZMod p) : LaurentSeries (ZMod p)) ^ j ≠ 0 :=
    fun j => pow_ne_zero _ (HahnSeries.single_ne_zero one_ne_zero)
  have hord : ∀ j : ℕ, c j ^ (p ^ n) * (HahnSeries.single (1 : ℤ) (1 : ZMod p)) ^ j ≠ 0 →
      (c j ^ (p ^ n) * (HahnSeries.single (1 : ℤ) (1 : ZMod p)) ^ j).order
        = ((p ^ n : ℕ) : ℤ) * (c j).order + j := by
    intro j hj
    rw [HahnSeries.order_mul (left_ne_zero_of_mul hj) (hX j), HahnSeries.order_pow,
      HahnSeries.order_pow, HahnSeries.order_single one_ne_zero]
    simp
  have key := laurent_terms_eq_zero_of_order_injOn (Finset.range (p ^ n))
    (fun j => c j ^ (p ^ n) * (HahnSeries.single (1 : ℤ) (1 : ZMod p)) ^ j) ?_ hsum i
    (Finset.mem_range.2 hi)
  · exact pow_eq_zero_iff (by omega) |>.1 ((mul_eq_zero.1 key).resolve_right (hX i))
  · intro a ha b hb hfa hfb h
    have h' := (hord a hfa).symm.trans (h.trans (hord b hfb))
    have ha' := Finset.mem_range.1 ha
    have hb' := Finset.mem_range.1 hb
    have hm := congrArg (fun z : ℤ => z % ((p ^ n : ℕ) : ℤ)) h'
    simp only [Int.mul_add_emod_self_left] at hm
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast ha'),
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hb')] at hm
    exact_mod_cast hm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AutomorphismOnExtensionPointwise
open GlobalTheory.K5 Polynomial
open scoped NNReal

namespace GlobalTheory

theorem exists_algEquiv_apply_eq_of_fixes_preimage_base :
    ∀ (Ω L K : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [Field L] [IsAlgClosed L] [Field K] [CharZero K] [Algebra K L] [Algebra.IsAlgebraic K L] (j : Ω →+* L) (s : Ω ≃ₐ[ℚ] Ω), (∀ a : Ω, j a ∈ Set.range (algebraMap K L) → s a = a) → ∀ x : Ω, ∃ g : L ≃ₐ[K] L, g (j x) = j (s x) := by
  intro Ω L K _ _ _ _ _ _ _ _ _ j s hs x
  classical
  haveI : IsAlgClosure K L := ⟨‹_›, ‹_›⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hint : IsIntegral K (j x) := Algebra.IsIntegral.isIntegral _
  have hxint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral _
  have hcomp : j.comp (algebraMap ℚ Ω) = (algebraMap K L).comp (algebraMap ℚ K) :=
    RingHom.ext_rat _ _
  set Q : Polynomial Ω := (minpoly ℚ x).map (algebraMap ℚ Ω) with hQ
  have hQ0 : Q ≠ 0 := Polynomial.map_ne_zero (minpoly.ne_zero hxint)
  have hQj : Q.map j = ((minpoly ℚ x).map (algebraMap ℚ K)).map (algebraMap K L) := by
    rw [hQ, Polynomial.map_map, Polynomial.map_map, hcomp]
  have hdvd : minpoly K (j x) ∣ (minpoly ℚ x).map (algebraMap ℚ K) := by
    apply minpoly.dvd
    rw [aeval_def, ← eval_map, ← hQj, eval_map, eval₂_at_apply, hQ, eval_map, ← aeval_def,
      minpoly.aeval, map_zero]
  set P : L[X] := (minpoly K (j x)).map (algebraMap K L) with hP
  have hPm : P.Monic := (minpoly.monic hint).map _
  have hPQ : P ∣ Q.map j := by
    rw [hQj]; exact Polynomial.map_dvd _ hdvd
  have hroots : ∀ r ∈ P.roots, r ∈ Set.range j := by
    intro r hr
    have h1 : r ∈ (Q.map j).roots :=
      Multiset.mem_of_le (roots.le_of_dvd (Polynomial.map_ne_zero hQ0) hPQ) hr
    rw [(IsAlgClosed.splits Q).roots_map j] at h1
    obtain ⟨a, -, ha⟩ := Multiset.mem_map.1 h1
    exact ⟨a, ha⟩
  have hlift : P ∈ lifts j := by
    rw [(IsAlgClosed.splits P).eq_prod_roots_of_monic hPm]
    refine Subsemiring.multiset_prod_mem _ _ ?_
    intro q hq
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hq
    obtain ⟨a, rfl⟩ := hroots r hr
    exact (mem_lifts _).2 ⟨X - C a, by simp⟩
  obtain ⟨M, hM⟩ := (mem_lifts _).1 hlift
  have hMs : M.map (s : Ω →+* Ω) = M := by
    ext n
    rw [coeff_map]
    refine hs _ ⟨(minpoly K (j x)).coeff n, ?_⟩
    rw [← coeff_map, ← coeff_map, hM]
  have hMx : M.eval x = 0 := by
    apply j.injective
    rw [← eval₂_at_apply, ← eval_map, hM, hP, eval_map, ← aeval_def, minpoly.aeval, map_zero]
  have hMsx : M.eval (s x) = 0 := by
    have h := eval₂_at_apply (p := M) (s : Ω →+* Ω) x
    rw [← eval_map, hMs, hMx, map_zero] at h
    exact h
  have hroot : aeval (j (s x)) (minpoly K (j x)) = 0 := by
    rw [aeval_def, ← eval_map, ← hP, ← hM, eval_map, eval₂_at_apply, hMsx, map_zero]
  exact (isConjRoot_of_aeval_eq_zero hint hroot).symm.exists_algEquiv

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormalFiniteIndexFixing
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormalFiniteIndexFixing
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem exists_normal_finiteIndex_fixing (L : Type) [Field L] (G : Type) [Group G]
    [MulSemiringAction G L] (S : Finset L) (hS : ∀ s ∈ S, (MulAction.orbit G s).Finite) :
    ∃ U : Subgroup G, U.Normal ∧ U.FiniteIndex ∧ (∀ s ∈ S, s ∈ Fix L U) ∧
      ∀ h : G, h ∉ U → ∃ x ∈ Fix L U, h • x ≠ x := by
  classical
  set T : Set L := ⋃ s ∈ S, MulAction.orbit G s with hT
  have hTfin : T.Finite := Set.Finite.biUnion S.finite_toSet (fun s hs => hS s hs)
  have hTstab : ∀ g : G, ∀ x ∈ T, g • x ∈ T := by
    intro g x hx
    simp only [hT, Set.mem_iUnion] at hx ⊢
    obtain ⟨s, hs, hx⟩ := hx
    exact ⟨s, hs, MulAction.mem_orbit_of_mem_orbit g hx⟩
  set F : Finset L := hTfin.toFinset
  have hF : ∀ x, x ∈ F ↔ x ∈ T := fun x => hTfin.mem_toFinset
  let U : Subgroup G := ⨅ x ∈ F, MulAction.stabilizer G x
  have hU : ∀ g : G, g ∈ U ↔ ∀ x ∈ T, g • x = x := by
    intro g
    simp only [U, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff, hF]
  have hST : ∀ s ∈ S, s ∈ T := by
    intro s hs
    simp only [hT, Set.mem_iUnion]
    exact ⟨s, hs, MulAction.mem_orbit_self s⟩
  have hFix : ∀ x ∈ T, x ∈ Fix L U := by
    intro x hx
    change ∀ m : U, m • x = x
    rintro ⟨g, hg⟩
    exact (hU g).1 hg x hx
  refine ⟨U, ?_, ?_, fun s hs => hFix s (hST s hs), ?_⟩
  · refine ⟨fun n hn g => ?_⟩
    rw [hU] at hn ⊢
    intro x hx
    have := hn (g⁻¹ • x) (hTstab g⁻¹ x hx)
    rw [mul_smul, mul_smul, this, smul_inv_smul]
  · refine Subgroup.finiteIndex_iInf' _ (fun x hx => ?_)
    refine ⟨?_⟩
    rw [MulAction.index_stabilizer]
    have hx' := (hF x).1 hx
    simp only [hT, Set.mem_iUnion] at hx'
    obtain ⟨s, hs, hxs⟩ := hx'
    rw [MulAction.orbit_eq_iff.mpr hxs]
    exact (Set.ncard_pos (hS s hs)).mpr ⟨s, MulAction.mem_orbit_self s⟩ |>.ne'
  · intro h hh
    rw [hU] at hh
    push_neg at hh
    obtain ⟨x, hx, hne⟩ := hh
    exact ⟨x, hFix x hx, hne⟩

end GlobalTheory.AlmostEt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormalFiniteIndexFixingStatement
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_finiteIndex_fixing_finite_orbits : ∀ (L : Type) [Field L] (G : Type) [Group G] [MulSemiringAction G L] (S : Finset L), (∀ s ∈ S, (MulAction.orbit G s).Finite) → ∃ U : Subgroup G, U.Normal ∧ U.FiniteIndex ∧ (∀ s ∈ S, s ∈ Fix L U) ∧ ∀ h : G, h ∉ U → ∃ x ∈ Fix L U, h • x ≠ x := by
  first | exact @GlobalTheory.AlmostEt.exists_normal_finiteIndex_fixing | exact GlobalTheory.AlmostEt.exists_normal_finiteIndex_fixing | (intros; apply GlobalTheory.AlmostEt.exists_normal_finiteIndex_fixing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AutomorphismExtensionUniform
open GlobalTheory.K5 Polynomial
open scoped NNReal

namespace GlobalTheory

theorem isClosed_setOf_algEquiv_apply_eq {K L : Type} [Field K] [Field L] [Algebra K L]
    [Algebra.IsIntegral K L] (a b : L) : IsClosed {g : L ≃ₐ[K] L | g a = b} := by
  by_cases h : ∃ g₀ : L ≃ₐ[K] L, g₀ a = b
  · obtain ⟨g₀, hg₀⟩ := h
    have hc : IsClosed ((MulAction.stabilizer (L ≃ₐ[K] L) a : Subgroup _) : Set (L ≃ₐ[K] L)) :=
      Subgroup.isClosed_of_isOpen _ (stabilizer_isOpen_of_isIntegral a)
    have hp := hc.preimage (continuous_const_mul g₀⁻¹)
    convert hp using 1
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe, MulAction.mem_stabilizer_iff,
      mul_smul, inv_smul_eq_iff]
    simp only [AlgEquiv.smul_def, hg₀]
  · have : {g : L ≃ₐ[K] L | g a = b} = ∅ := by
      ext g
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hg => h ⟨g, hg⟩
    rw [this]
    exact isClosed_empty

theorem exists_primitive_for_finset (k : Type) {Ω : Type} [Field k] [CharZero k] [Field Ω]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
    (u : Finset Ω) : ∃ x : Ω, ∀ {L : Type} [Field L] (φ ψ : Ω →+* L),
      φ.comp (algebraMap k Ω) = ψ.comp (algebraMap k Ω) → φ x = ψ x →
      ∀ y ∈ u, φ y = ψ y := by
  let F : IntermediateField k Ω := IntermediateField.adjoin k (u : Set Ω)
  haveI : FiniteDimensional k F :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨α, hα⟩ := Field.exists_primitive_element k F
  refine ⟨α, fun {L} _ φ ψ hk hx y hy => ?_⟩
  have key : ∀ z : F, z ∈ IntermediateField.adjoin k {α} → φ z = ψ z := by
    intro z hz
    induction hz using IntermediateField.adjoin_induction with
    | mem x hx' =>
      rw [Set.mem_singleton_iff.mp hx']
      exact hx
    | algebraMap q =>
      exact DFunLike.congr_fun hk q
    | add x y _ _ hx hy => simp [hx, hy]
    | inv x _ hx => simp [hx]
    | mul x y _ _ hx hy => simp [hx, hy]
  exact key ⟨y, IntermediateField.subset_adjoin k _ hy⟩ (by rw [hα]; trivial)

theorem exists_algEquiv_inducing_of_forall_conj :
    ∀ (Ω L K : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [Field L] [IsAlgClosed L]
      [Field K] [CharZero K] [Algebra K L] [Algebra.IsAlgebraic K L] (j : Ω →+* L)
      (s : Ω ≃ₐ[ℚ] Ω), (∀ x : Ω, ∃ g : L ≃ₐ[K] L, g (j x) = j (s x)) →
      ∃ g : L ≃ₐ[K] L, ∀ x : Ω, g (j x) = j (s x) := by
  intro Ω L K _ _ _ _ _ _ _ _ _ j s h
  haveI : IsAlgClosure K L := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois K L := {}
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hne := (isCompact_univ (X := L ≃ₐ[K] L)).inter_iInter_nonempty
    (fun x : Ω => {g : L ≃ₐ[K] L | g (j x) = j (s x)})
    (fun x => isClosed_setOf_algEquiv_apply_eq _ _)
    (fun u => by
      obtain ⟨x, hx⟩ := exists_primitive_for_finset ℚ u
      obtain ⟨g, hg⟩ := h x
      refine ⟨g, Set.mem_univ _, ?_⟩
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      intro y hy
      exact hx ((g : L →+* L).comp j) (j.comp (s : Ω →+* Ω)) (RingHom.ext_rat _ _) hg y hy)
  obtain ⟨g, -, hg⟩ := hne
  simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hg
  exact ⟨g, hg⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixModularFormGamma1InterGam
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixModularFormGamma1InterGam
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

open ConjAct Pointwise

namespace GlobalTheory.Hk

theorem conj_entries (σ y : SL(2, ℤ)) :
   ((σ * y * σ⁻¹ : SL(2, ℤ)) 0 0 = (σ 0 0 * y 0 0 + σ 0 1 * y 1 0) * σ 1 1 - (σ 0 0 * y 0 1 + σ 0 1 * y 1 1) * σ 1 0) ∧
   ((σ * y * σ⁻¹ : SL(2, ℤ)) 1 0 = (σ 1 0 * y 0 0 + σ 1 1 * y 1 0) * σ 1 1 - (σ 1 0 * y 0 1 + σ 1 1 * y 1 1) * σ 1 0) ∧
   ((σ * y * σ⁻¹ : SL(2, ℤ)) 1 1 = -(σ 1 0 * y 0 0 + σ 1 1 * y 1 0) * σ 0 1 + (σ 1 0 * y 0 1 + σ 1 1 * y 1 1) * σ 0 0) := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
  refine ⟨by ring, by ring, by ring⟩

theorem dia_conj_mem {N l : ℕ} {d : ℤ} {σ : SL(2, ℤ)} (hσ : IsDia N l d σ) {y : SL(2, ℤ)}
    (hy : y ∈ lev N l) : σ * y * σ⁻¹ ∈ lev N l := by
  obtain ⟨hy1, hy0⟩ := Subgroup.mem_inf.1 hy
  obtain ⟨hc, -⟩ := hσ
  rw [Gamma1_mem] at hy1
  rw [Gamma0_mem] at hy0
  obtain ⟨hp, hs, hr⟩ := hy1
  obtain ⟨e00, e10, e11⟩ := conj_entries σ y
  have hdvd : ((N * l : ℕ) : ℤ) ∣ (σ 1 0 : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hc
  have hcN : ((σ 1 0 : ℤ) : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (by push_cast; exact dvd_mul_right _ _) hdvd)
  have hcl : ((σ 1 0 : ℤ) : ZMod l) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (by push_cast; exact dvd_mul_left _ _) hdvd)
  have hdet : (σ 0 0 : ℤ) * σ 1 1 - σ 0 1 * σ 1 0 = 1 := by
    have := σ.2; rw [Matrix.det_fin_two] at this; exact this
  have hdetN : ((σ 0 0 : ℤ) : ZMod N) * (σ 1 1 : ℤ) - ((σ 0 1 : ℤ) : ZMod N) * (σ 1 0 : ℤ) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod N) hdet
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Gamma1_mem, e00, e10, e11]
    push_cast
    rw [hp, hs, hr, hcN]
    rw [hcN] at hdetN
    refine ⟨?_, ?_, ?_⟩ <;> first | ring1 | linear_combination hdetN
  · rw [Gamma0_mem, e10]
    push_cast
    rw [hy0, hcl]
    ring

theorem lev_le_conj {N l : ℕ} {d : ℤ} {σ : SL(2, ℤ)} (hσ : IsDia N l d σ) :
    (lev N l : Subgroup (GL (Fin 2) ℝ)) ≤
      toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ σ)⁻¹ • (lev N l : Subgroup (GL (Fin 2) ℝ)) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, map_inv, inv_inv, ConjAct.toConjAct_smul]
  exact Subgroup.mem_map.2 ⟨σ * y * σ⁻¹, dia_conj_mem hσ hy, by simp [map_mul, map_inv]⟩

theorem dia_modularForm : ∀ (N l : ℕ) (k d : ℤ) (σ : SL(2, ℤ)), 0 < N → IsDia N l d σ →
    ∀ f : ModularForm (lev N l) k, ∃ g : ModularForm (lev N l) k, ⇑g = dia k σ ⇑f := by
  intro N l k d σ _ hσ f
  let F := ModularForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ σ)
  have hle := lev_le_conj hσ
  refine ⟨{ toFun := ⇑F
            slash_action_eq' := fun γ hγ => F.slash_action_eq' γ (hle hγ)
            holo' := F.holo'
            bdd_at_cusps' := fun hc => F.bdd_at_cusps' (hc.mono hle) }, ?_⟩
  show ⇑F = _
  rw [ModularForm.coe_translate, dia, ModularForm.SL_slash]
  rfl

end GlobalTheory.Hk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixModularFormGamma1InterGamStatement
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diamondOperatorOfMatrix_modularForm_gamma1InterGamma0 : ∀ (N l : ℕ) (k d : ℤ) (σ : SL(2, ℤ)), 0 < N → GlobalTheory.Hk.IsDia N l d σ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k, ∃ g : ModularForm (GlobalTheory.Hk.lev N l) k, ⇑g = GlobalTheory.Hk.dia k σ ⇑f := by
  first | exact @GlobalTheory.Hk.dia_modularForm | exact GlobalTheory.Hk.dia_modularForm | (intros; apply GlobalTheory.Hk.dia_modularForm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationEqOneOfPowEqSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationEqOneOfPowEqSpan
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem valuation_eq_one_of_pow_eq_span :
    ∀ (E Ω R : Type) [Field E] [Field Ω] [Algebra E Ω] [CommRing R] [Algebra R E] (B : ValuationSubring Ω)
      (J : Submodule R E) (N : ℕ), 0 < N → (∀ x : R, algebraMap E Ω (algebraMap R E x) ∈ B) → ∀ w : E, w ≠ 0 →
      (J ^ N = Submodule.span R {w}) → ∃ c : E, c ≠ 0 ∧ B.valuation (algebraMap E Ω (w / c ^ N)) = 1 := by
  intro E Ω R _ _ _ _ _ B J N hN hRB w hw hJ
  set v := B.valuation.comap (algebraMap E Ω) with hv
  have hva : ∀ x, v x = B.valuation (algebraMap E Ω x) := fun x => rfl
  have hR : ∀ r : R, v (algebraMap R E r) ≤ 1 := fun r => by
    rw [hva]; exact (B.valuation_le_one_iff _).mpr (hRB r)
  have hsm : ∀ (r : R) (z : E), v (r • z) ≤ v z := fun r z => by
    rw [Algebra.smul_def, v.map_mul]
    calc v (algebraMap R E r) * v z ≤ 1 * v z := mul_le_mul' (hR r) le_rfl
      _ = v z := one_mul _
  let S : ℕ → Submodule R E := fun n =>
    { carrier := {z | ∃ c ∈ J, v z ≤ v c ^ (n + 1)}
      zero_mem' := ⟨0, J.zero_mem, by simp⟩
      add_mem' := by
        rintro z₁ z₂ ⟨c₁, hc₁, h₁⟩ ⟨c₂, hc₂, h₂⟩
        rcases le_total (v c₁) (v c₂) with h | h
        · refine ⟨c₂, hc₂, (v.map_add z₁ z₂).trans (max_le ?_ h₂)⟩
          exact h₁.trans (pow_le_pow_left₀ zero_le' h _)
        · refine ⟨c₁, hc₁, (v.map_add z₁ z₂).trans (max_le h₁ ?_)⟩
          exact h₂.trans (pow_le_pow_left₀ zero_le' h _)
      smul_mem' := by
        rintro r z ⟨c, hc, h⟩
        exact ⟨c, hc, (hsm r z).trans h⟩ }
  have key : ∀ n : ℕ, J ^ (n + 1) ≤ S n := by
    intro n
    induction n with
    | zero =>
      intro z hz
      rw [pow_one] at hz
      exact ⟨z, hz, by simp⟩
    | succ n ih =>
      rw [pow_succ]
      refine Submodule.mul_le.mpr ?_
      intro y hy z' hz'
      obtain ⟨c, hc, h⟩ := ih hy
      show ∃ c ∈ J, v (y * z') ≤ v c ^ (n + 1 + 1)
      rw [v.map_mul]
      rcases le_total (v c) (v z') with h' | h'
      · refine ⟨z', hz', ?_⟩
        rw [pow_succ]
        exact mul_le_mul' (h.trans (pow_le_pow_left₀ zero_le' h' _)) le_rfl
      · refine ⟨c, hc, ?_⟩
        rw [pow_succ]
        exact mul_le_mul' h h'
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hwmem : w ∈ J ^ (n + 1) := by rw [hJ]; exact Submodule.mem_span_singleton_self w
  obtain ⟨c, hc, hle⟩ := key n hwmem
  have hcN : c ^ (n + 1) ∈ Submodule.span R {w} := hJ ▸ Submodule.pow_mem_pow J hc (n + 1)
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hcN
  have hge : v (c ^ (n + 1)) ≤ v w := by
    rw [← hr]; exact hsm r w
  have heq : v (c ^ (n + 1)) = v w := le_antisymm hge (by rw [v.map_pow]; exact hle)
  have hw0 : v w ≠ 0 := by
    rw [hva]; exact (Valuation.ne_zero_iff _).mpr ((_root_.map_ne_zero _).mpr hw)
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hw0
    rw [← heq]; simp
  refine ⟨c, hc0, ?_⟩
  have : v (w / c ^ (n + 1)) = 1 := by
    rw [map_div₀, heq, div_self hw0]
  simpa [hva] using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationEqOneOfPowEqSpanStatement
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuation_div_pow_eq_one_of_pow_eq_span : ∀ (E Ω R : Type) [Field E] [Field Ω] [Algebra E Ω] [CommRing R] [Algebra R E] (B : ValuationSubring Ω) (J : Submodule R E) (N : ℕ), 0 < N → (∀ x : R, algebraMap E Ω (algebraMap R E x) ∈ B) → ∀ w : E, w ≠ 0 → (J ^ N = Submodule.span R {w}) → ∃ c : E, c ≠ 0 ∧ B.valuation (algebraMap E Ω (w / c ^ N)) = 1 := by
  first | exact @GlobalTheory.valuation_eq_one_of_pow_eq_span | exact GlobalTheory.valuation_eq_one_of_pow_eq_span | (intros; apply GlobalTheory.valuation_eq_one_of_pow_eq_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteGaloisApproximation
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteGaloisApproximation
open GlobalTheory.K5

namespace GlobalTheory.K5

theorem gal_finite_subcover : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ S : Gal p Ω → Finset Ω, ∃ F : Finset (Gal p Ω), ∀ h : Gal p Ω, ∃ g ∈ F, ∀ x ∈ S g, h x = g x := by
  intro p _ Ω _ _ hΩ S
  classical
  letI : TopologicalSpace Ω := ⊥
  haveI : DiscreteTopology Ω := ⟨rfl⟩
  haveI : IsDomain (O0 p) := hΩ.inj.isDomain (algebraMap (O0 p) Ω)
  haveI : Module.IsTorsionFree (O0 p) Ω := Module.isTorsionFree_iff_algebraMap_injective.mpr hΩ.inj
  haveI := hΩ.alg
  choose P hP0 hP using fun x : Ω => (Algebra.IsAlgebraic.isAlgebraic (R := O0 p) x)
  have hmap : ∀ x, (P x).map (algebraMap (O0 p) Ω) ≠ 0 := fun x =>
    (Polynomial.map_ne_zero_iff hΩ.inj).mpr (hP0 x)
  let R : Ω → Set Ω := fun x => (((P x).map (algebraMap (O0 p) Ω)).roots.toFinset : Set Ω)
  have hR : ∀ (φ : Ω →ₐ[O0 p] Ω) x, φ x ∈ R x := by
    intro φ x
    simp only [R, Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_roots (hmap x), Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def,
      Polynomial.aeval_algHom_apply, hP x, map_zero]
  let K : Set (Ω → Ω) := Set.pi Set.univ R
  have hK : IsCompact K := isCompact_univ_pi (fun x => (Finset.finite_toSet _).isCompact)
  let C : Set (Ω → Ω) := (⋂ a, ⋂ b, {f | f (a + b) = f a + f b}) ∩ (⋂ a, ⋂ b, {f | f (a * b) = f a * f b})
      ∩ {f | f 1 = 1} ∩ ⋂ r : O0 p, {f | f (algebraMap (O0 p) Ω r) = algebraMap (O0 p) Ω r}
  have hC : IsClosed C := by
    have key : ∀ (u : (Ω → Ω) → Ω × Ω × Ω), Continuous u → ∀ T : Set (Ω × Ω × Ω),
        IsClosed (u ⁻¹' T) := fun u hu T => (isClosed_discrete T).preimage hu
    refine IsClosed.inter (IsClosed.inter (IsClosed.inter ?_ ?_) ?_) ?_
    · refine isClosed_iInter fun a => isClosed_iInter fun b => ?_
      exact key (fun f => (f (a + b), f a, f b)) (by fun_prop) {t | t.1 = t.2.1 + t.2.2}
    · refine isClosed_iInter fun a => isClosed_iInter fun b => ?_
      exact key (fun f => (f (a * b), f a, f b)) (by fun_prop) {t | t.1 = t.2.1 * t.2.2}
    · exact key (fun f => (f 1, f 1, f 1)) (by fun_prop) {t | t.1 = 1}
    · refine isClosed_iInter fun r => ?_
      exact key (fun f => (f (algebraMap (O0 p) Ω r), f 1, f 1)) (by fun_prop)
        {t | t.1 = algebraMap (O0 p) Ω r}
  let U : Gal p Ω → Set (Ω → Ω) := fun g => ⋂ x ∈ S g, (fun f => f x) ⁻¹' {g x}
  have hU : ∀ g, IsOpen (U g) := fun g =>
    isOpen_biInter_finset (fun x _ => (isOpen_discrete {g x}).preimage (continuous_apply x))
  have hcov : K ∩ C ⊆ ⋃ g, U g := by
    rintro f ⟨-, ⟨⟨hadd, hmul⟩, h1⟩, halg⟩
    simp only [Set.mem_iInter, Set.mem_setOf_eq] at hadd hmul h1 halg
    have h0 : f 0 = 0 := by
      have := hadd 0 0
      simp only [add_zero] at this
      exact left_eq_add.mp this
    let φ : Ω →ₐ[O0 p] Ω :=
      { toFun := f, map_one' := h1, map_mul' := hmul, map_zero' := h0, map_add' := hadd,
        commutes' := halg }
    let e : Gal p Ω := AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ)
    refine Set.mem_iUnion.mpr ⟨e, ?_⟩
    simp only [U, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
    intro x _
    rfl
  have hmem : ∀ h : Gal p Ω, (⇑h : Ω → Ω) ∈ K ∩ C := by
    intro h
    refine ⟨fun x _ => hR (h : Ω →ₐ[O0 p] Ω) x, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · simp only [Set.mem_iInter, Set.mem_setOf_eq]; intro a b; exact map_add h a b
    · simp only [Set.mem_iInter, Set.mem_setOf_eq]; intro a b; exact map_mul h a b
    · exact map_one h
    · simp only [Set.mem_iInter, Set.mem_setOf_eq]; intro r; exact h.commutes r
  obtain ⟨F, hF⟩ := (hK.inter_right hC).elim_finite_subcover U hU hcov
  refine ⟨F, fun h => ?_⟩
  obtain ⟨g, hg, hgh⟩ := Set.mem_iUnion₂.mp (hF (hmem h))
  refine ⟨g, hg, fun x hx => ?_⟩
  have := Set.mem_iInter₂.mp hgh x hx
  simpa using this

end GlobalTheory.K5
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteGaloisApproximationStatement
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_galois_approximation : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ S : Gal p Ω → Finset Ω, ∃ F : Finset (Gal p Ω), ∀ h : Gal p Ω, ∃ g ∈ F, ∀ x ∈ S g, h x = g x := by
  first | exact @GlobalTheory.K5.gal_finite_subcover | exact GlobalTheory.K5.gal_finite_subcover | (intros; apply GlobalTheory.K5.gal_finite_subcover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardPowEqOneLeOfIsCyclicUnits
namespace GlobalTheory

private lemma card_pow_eq_one_le_of_isCyclic {α : Type*} [Group α] [Finite α] [IsCyclic α] {n : ℕ}
    (hn : 0 < n) : Nat.card {a : α // a ^ n = 1} ≤ n := by
  classical
  let _ := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  convert IsCyclic.card_pow_eq_one_le (α := α) hn

theorem card_pow_eq_one_le_index_mul {G : Type*} [CommGroup G] [Finite G] (H : Subgroup G)
    [IsCyclic H] {d : ℕ} (hd : 0 < d) : Nat.card {x : G // x ^ d = 1} ≤ H.index * d := by
  classical

  set K : Subgroup G := (powMonoidHom d : G →* G).ker with hKdef
  have hK : Nat.card {x : G // x ^ d = 1} = Nat.card K :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => by simp [hKdef]))
  have hsplit := (H.subgroupOf K).card_mul_index
  have hidx : (H.subgroupOf K).index ≤ H.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite))
      (Subgroup.relIndex_dvd_index_of_normal (H := H) (K := K))
  have hsmall : Nat.card (H.subgroupOf K) ≤ d := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun x : H.subgroupOf K => (⟨⟨(x.1 : G), Subgroup.mem_subgroupOf.mp x.2⟩, ?_⟩ :
        {h : H // h ^ d = 1})) ?_) (card_pow_eq_one_le_of_isCyclic hd)
    · apply Subtype.ext
      have hx : (x.1 : G) ^ d = 1 := x.1.2
      simpa using hx
    · intro x y hxy
      apply Subtype.ext; apply Subtype.ext
      simpa using congrArg (fun z : {h : H // h ^ d = 1} => ((z.1 : H) : G)) hxy
  rw [hK, ← hsplit]
  calc Nat.card (H.subgroupOf K) * (H.subgroupOf K).index ≤ d * H.index :=
        Nat.mul_le_mul hsmall hidx
    _ = H.index * d := Nat.mul_comm _ _

theorem card_pow_eq_one_le_units {M : Type*} [Monoid M] [Finite M] {d : ℕ} (hd : 0 < d) :
    Nat.card {x : M // x ^ d = 1} ≤ Nat.card {x : Mˣ // x ^ d = 1} := by
  refine Nat.card_le_card_of_injective
    (fun x => ⟨Units.ofPowEqOne x.1 d x.2 hd.ne', Units.pow_ofPowEqOne _ _⟩) ?_
  intro x y hxy
  apply Subtype.ext
  have := congrArg (fun z : {u : Mˣ // u ^ d = 1} => ((z.1 : Mˣ) : M)) hxy
  simpa using this

theorem card_pow_eq_one_le_of_isCyclic_units (n : ℕ) [NeZero n] [IsCyclic (ZMod n)ˣ] {d : ℕ}
    (hd : 0 < d) : Nat.card {x : ZMod n // x ^ d = 1} ≤ d :=
  (card_pow_eq_one_le_units hd).trans (card_pow_eq_one_le_of_isCyclic hd)

theorem card_pow_eq_one_two_pow_le (w : ℕ) (hw : 1 ≤ w) {d : ℕ} (hd : 0 < d) :
    Nat.card {x : ZMod (2 ^ w) // x ^ d = 1} ≤ 2 * d := by
  have : NeZero (2 ^ w) := ⟨by positivity⟩
  obtain _ | _ | n := w
  · omega
  ·
    have : IsCyclic (ZMod (2 ^ 1))ˣ := (ZMod.isCyclic_units_two_pow_iff 1).mpr (by norm_num)
    exact (card_pow_eq_one_le_of_isCyclic_units _ hd).trans (by omega)
  ·
    let u : (ZMod (2 ^ (n + 2)))ˣ :=
      ZMod.unitOfCoprime 5 (Nat.Coprime.pow_right _ (by norm_num))
    have hu : orderOf u = 2 ^ n := by
      rw [← orderOf_units, ZMod.coe_unitOfCoprime, Nat.cast_ofNat, ZMod.orderOf_five]
    have hG : Nat.card (ZMod (2 ^ (n + 2)))ˣ = 2 ^ n * 2 := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime_pow Nat.prime_two (by omega)]
      simp [pow_succ]
    have hidx : (Subgroup.zpowers u).index = 2 := by
      have h := (Subgroup.zpowers u).card_mul_index
      rw [Nat.card_zpowers, hu, hG] at h
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h
    calc Nat.card {x : ZMod (2 ^ (n + 2)) // x ^ d = 1}
        ≤ Nat.card {x : (ZMod (2 ^ (n + 2)))ˣ // x ^ d = 1} := card_pow_eq_one_le_units hd
      _ ≤ (Subgroup.zpowers u).index * d := card_pow_eq_one_le_index_mul _ hd
      _ = 2 * d := by rw [hidx]

theorem rootsOfUnityCount : Formalism.CyclotomicNorms.RootsOfUnityCount := by
  intro ℓ w d hℓ hw hd
  have : NeZero (ℓ ^ w) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  by_cases h2 : ℓ = 2
  · subst h2
    exact ⟨fun h => absurd rfl h, card_pow_eq_one_two_pow_le w hw hd⟩
  ·
    have := ZMod.isCyclic_units_of_prime_pow ℓ hℓ h2 w
    have h := card_pow_eq_one_le_of_isCyclic_units (ℓ ^ w) (d := d) hd
    exact ⟨fun _ => h.trans (Nat.le_mul_of_pos_right _ (pow_pos hℓ.pos _)), h.trans (by omega)⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TendstoSmulInvOfMulTendstoInvertibleMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TendstoSmulInvOfMulTendstoInvertibleMatrix
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

theorem tendsto_smul_inv_of_mul_tendsto_invertible (r : ℕ) (A U : ℍ → Matrix (Fin r) (Fin r) ℂ)
    (L : Matrix (Fin r) (Fin r) ℂ) (d : ℍ → ℂ) (hL : L.det ≠ 0)
    (hAU : Tendsto (fun τ => A τ * U τ) atImInfty (𝓝 L))
    (hdU : Tendsto (fun τ => d τ • U τ) atImInfty (𝓝 0)) :
    Tendsto (fun τ => d τ • (A τ)⁻¹) atImInfty (𝓝 0) := by
  have hdet : Tendsto (fun τ => (A τ * U τ).det) atImInfty (𝓝 L.det) :=
    ((continuous_id.matrix_det).tendsto L).comp hAU
  have hev : ∀ᶠ τ in atImInfty, (A τ * U τ).det ≠ 0 := hdet.eventually_ne hL

  have hinvdet : Tendsto (fun τ => Ring.inverse (A τ * U τ).det) atImInfty (𝓝 (Ring.inverse L.det)) := by
    simp only [Ring.inverse_eq_inv']
    exact hdet.inv₀ hL
  have hadj : Tendsto (fun τ => (A τ * U τ).adjugate) atImInfty (𝓝 L.adjugate) :=
    ((continuous_id.matrix_adjugate).tendsto L).comp hAU
  have hinv : Tendsto (fun τ => (A τ * U τ)⁻¹) atImInfty (𝓝 L⁻¹) := by
    simp only [Matrix.inv_def]
    exact hinvdet.smul hadj
  have hlim : Tendsto (fun τ => (d τ • U τ) * (A τ * U τ)⁻¹) atImInfty (𝓝 0) := by
    have := hdU.mul hinv
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [hev] with τ hτ
  have hu : IsUnit (A τ * U τ).det := isUnit_iff_ne_zero.mpr hτ
  have h1 : A τ * (U τ * (A τ * U τ)⁻¹) = 1 := by
    rw [← mul_assoc]; exact Matrix.mul_nonsing_inv _ hu
  rw [Matrix.inv_eq_right_inv h1, Matrix.smul_mul]

end GlobalTheory.OddFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TendstoSmulInvOfMulTendstoInvertibleMatrixStatement
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_smul_inv_of_mul_tendsto_invertible_matrix : ∀ (r : ℕ) (A U : ℍ → Matrix (Fin r) (Fin r) ℂ) (L : Matrix (Fin r) (Fin r) ℂ) (d : ℍ → ℂ), L.det ≠ 0 → Tendsto (fun τ => A τ * U τ) atImInfty (𝓝 L) → Tendsto (fun τ => d τ • U τ) atImInfty (𝓝 0) → Tendsto (fun τ => d τ • (A τ)⁻¹) atImInfty (𝓝 0) := by
  first | exact @GlobalTheory.OddFrame.tendsto_smul_inv_of_mul_tendsto_invertible | exact GlobalTheory.OddFrame.tendsto_smul_inv_of_mul_tendsto_invertible | (intros; apply GlobalTheory.OddFrame.tendsto_smul_inv_of_mul_tendsto_invertible <;> assumption)
end
end
