module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Point2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.AbelianFieldHasMuIffExistsPrimitiveRoot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IsAlgClosureRat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ABoundOfIsTower

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Vvat
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.vvat :
    ∀ (l t : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] (T b B : ℝ), 0 ≤ b → (t : ℝ) ≤ T → T * b ≤ B →
      (∀ e : ℕ, 1 ≤ e → e < t → shaInv E l e ≠ ⊤ ∧ ((shaInv E l e).toNat : ℝ) ≤ b) → VVat l E t B := by
  intro l t _ E _ _ T b B hb htT hTB h Ω _ _ _ D
  refine ⟨fun e he het => by rw [shaLen_eq_shaInv]; exact (h e he het).1, ?_⟩
  calc ∑ e ∈ Finset.Ico 1 t, ((shaLen D e).toNat : ℝ) ≤ ∑ _e ∈ Finset.Ico 1 t, b := by
        apply Finset.sum_le_sum
        intro e he
        rw [Finset.mem_Ico] at he
        rw [shaLen_eq_shaInv]
        exact (h e he.1 he.2).2
    _ = ((t - 1 : ℕ) : ℝ) * b := by rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    _ ≤ T * b := mul_le_mul_of_nonneg_right (le_trans (by exact_mod_cast Nat.sub_le t 1) htT) hb
    _ ≤ B := hTB
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Exc
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Near1
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.near1 :
    ∀ (l : ℕ) [Fact l.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[l] K] [IsUltrametricDist K] (s : K) (Z a b : ℕ),
      1 ≤ a → a ≤ Z → 1 ≤ b → b ≤ Z → ‖s - (a : K)‖ < (l : ℝ) ^ (-(Nat.log l Z : ℤ)) →
        ‖s - (b : K)‖ < (l : ℝ) ^ (-(Nat.log l Z : ℤ)) → a = b := by
  intro l _ K _ _ _ s Z a b ha1 haZ hb1 hbZ hsa hsb
  by_contra hab
  have hlp : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hlp.one_lt
  set k := Nat.log l Z with hk
  set d : ℤ := (a : ℤ) - b with hd
  have hd0 : d ≠ 0 := by omega
  have hK : ‖(d : ℚ_[l])‖ < (l : ℝ) ^ (-(k : ℤ)) := by
    have h1 : algebraMap ℚ_[l] K (d : ℚ_[l]) = (s - b) + -(s - a) := by
      rw [map_intCast, hd]
      push_cast
      ring
    rw [← norm_algebraMap' K, h1]
    calc ‖(s - b) + -(s - a)‖ ≤ max ‖s - b‖ ‖-(s - a)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ < _ := by
        rw [norm_neg]
        exact max_lt hsb hsa
  have hdq : (d : ℚ_[l]) ≠ 0 := by exact_mod_cast hd0
  rw [Padic.norm_eq_zpow_neg_valuation hdq] at hK
  have hlt := (zpow_lt_zpow_iff_right₀ hl1).mp hK
  have hle : ‖(d : ℚ_[l])‖ ≤ (l : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) := by
    rw [Padic.norm_eq_zpow_neg_valuation hdq]
    apply zpow_le_zpow_right₀ hl1.le
    push_cast
    omega
  have hdvd := (Padic.norm_int_le_pow_iff_dvd d (k + 1)).mp hle
  have hZ := Nat.lt_pow_succ_log_self hlp.one_lt Z
  have habs : d.natAbs ≤ Z := by
    rw [hd]
    omega
  have h0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd (by
    simp only [Int.natAbs_pow, Int.natAbs_natCast]
    exact lt_of_le_of_lt habs hZ)
  exact hd0 h0
end

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.exc :
    ∀ (l R : ℕ) [Fact l.Prime] (L₀ : Type) [Field L₀], ABound l R L₀ →
      ∃ c : ℕ, (∃ ζ : L₀, IsPrimitiveRoot ζ (l ^ c)) ∧ ∀ Z : ℕ, ∃ Exc : Finset ℕ, FirstBound l R c L₀ Z Exc := by
  intro l R _ L₀ _ h
  classical
  obtain ⟨⟨K, _, _, hU, c, R', s, hR', hζ, hb⟩, -⟩ := h
  refine ⟨c, hζ, fun Z => ?_⟩
  obtain ⟨near, hnear⟩ : ∃ near : Fin R' → Finset ℕ, near = fun i =>
      (Finset.Icc 1 Z : Finset ℕ).filter
        (fun e : ℕ => ‖s i - (e : K)‖ < (l : ℝ) ^ (-(Nat.log l Z : ℤ))) :=
    ⟨_, rfl⟩
  refine ⟨Finset.univ.biUnion near, ?_⟩
  unfold FirstBound
  refine ⟨?_, ?_⟩
  · have hone : ∀ i : Fin R', (near i).card ≤ 1 := by
      intro i
      rw [Finset.card_le_one]
      intro a ha b hb'
      rw [hnear] at ha hb'
      simp only [Finset.mem_filter, Finset.mem_Icc] at ha hb'
      exact near1 l K (s i) Z a b ha.1.1 ha.1.2 hb'.1.1 hb'.1.2 ha.2 hb'.2
    calc (Finset.univ.biUnion near).card ≤ ∑ i : Fin R', (near i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin R', 1 := Finset.sum_le_sum (fun i _ => hone i)
      _ = R' := by simp
      _ ≤ R := hR'
  · intro e he1 heZ hne m L₁ _ _ _ hL
    have hfar : ∀ i : Fin R', (l : ℝ) ^ (-(Nat.log l Z : ℤ)) ≤ ‖s i - (e : K)‖ := by
      intro i
      by_contra hlt
      push_neg at hlt
      apply hne
      rw [hnear]
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨i, ⟨he1, heZ⟩, hlt⟩
    have h1 := hb e he1 m L₁ hL (Nat.log l Z) hfar
    exact h1.trans (by gcongr)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Layerex
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win
open Polynomial

private theorem winlx_up {K : Type} [Field K] {l m : ℕ} (hl : l.Prime) {b : K}
    (h : IsPrimitiveRoot (b ^ l) (l ^ (m + 1))) : IsPrimitiveRoot b (l ^ (m + 2)) := by
  haveI : Fact l.Prime := ⟨hl⟩
  have h1 : ¬ b ^ (l ^ (m + 1)) = 1 := by
    intro e
    have : (b ^ l) ^ (l ^ m) = 1 := by rw [← pow_mul, ← pow_succ']; exact e
    exact h.pow_ne_one_of_pos_of_lt (pow_ne_zero _ hl.ne_zero)
      (Nat.pow_lt_pow_right hl.one_lt (Nat.lt_succ_self m)) this
  have h2 : b ^ (l ^ (m + 1 + 1)) = 1 := by
    rw [pow_succ' l (m + 1), pow_mul]; exact h.pow_eq_one
  have h3 := orderOf_eq_prime_pow h1 h2
  have := IsPrimitiveRoot.orderOf b
  rwa [h3] at this

private theorem winlx_max (K : Type) [Field K] [NumberField K] {l k : ℕ} (hl : l.Prime)
    (h : ∃ z : K, IsPrimitiveRoot z (l ^ (k + 1))) :
    ∃ m, k ≤ m ∧ (∃ z : K, IsPrimitiveRoot z (l ^ (m + 1))) ∧
      ¬ ∃ z : K, IsPrimitiveRoot z (l ^ (m + 2)) := by
  by_contra hc
  push Not at hc
  have key : ∀ n, ∃ z : K, IsPrimitiveRoot z (l ^ (k + n + 1)) := by
    intro n
    induction n with
    | zero => exact h
    | succ n ih => exact hc (k + n) (by omega) ih
  obtain ⟨z, hz⟩ := key (Module.finrank ℚ K)
  have hpos : 0 < Nat.lcm (l ^ (k + Module.finrank ℚ K + 1)) (l ^ (k + Module.finrank ℚ K + 1)) := by
    rw [Nat.lcm_self]; exact pow_pos hl.pos _
  have h1 := IsPrimitiveRoot.lcm_totient_le_finrank (K := ℚ) hz hz (Polynomial.cyclotomic.irreducible_rat hpos)
  rw [Nat.lcm_self, Nat.totient_prime_pow_succ hl] at h1
  have h2 : k + Module.finrank ℚ K < l ^ (k + Module.finrank ℚ K) := Nat.lt_pow_self hl.one_lt
  have h3 : 1 ≤ l - 1 := by have := hl.two_le; omega
  have h4 := Nat.mul_le_mul_left (l ^ (k + Module.finrank ℚ K)) h3
  omega

private theorem winlx_step (K : Type) [Field K] [NumberField K] {l m : ℕ} (hl : l.Prime)
    {z : K} (hz : IsPrimitiveRoot z (l ^ (m + 1))) (hn : ¬ ∃ z : K, IsPrimitiveRoot z (l ^ (m + 2))) :
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K'),
      IsCyclotomicExtension {l ^ (m + 2)} K K' ∧ Module.finrank K K' = l := by
  have hirr : Irreducible (X ^ l - C z : K[X]) :=
    X_pow_sub_C_irreducible_of_prime hl (fun b hb => hn ⟨b, winlx_up hl (hb ▸ hz)⟩)
  haveI : Fact (Irreducible (X ^ l - C z : K[X])) := ⟨hirr⟩
  let pb := AdjoinRoot.powerBasis hirr.ne_zero
  haveI : Module.Finite K (AdjoinRoot (X ^ l - C z : K[X])) := pb.finite
  haveI : NeZero (l ^ (m + 2)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hr : IsPrimitiveRoot (AdjoinRoot.root (X ^ l - C z : K[X])) (l ^ (m + 2)) := by
    apply winlx_up hl
    rw [root_X_pow_sub_C_pow]
    exact hz.map_of_injective (AdjoinRoot.of (X ^ l - C z : K[X])).injective
  refine ⟨AdjoinRoot (X ^ l - C z : K[X]), inferInstance, NumberField.of_module_finite K _, inferInstance, ?_, ?_⟩
  · rw [IsCyclotomicExtension.iff_singleton]
    refine ⟨⟨_, hr⟩, fun x => ?_⟩
    have : x ∈ Algebra.adjoin K {AdjoinRoot.root (X ^ l - C z : K[X])} := by
      rw [AdjoinRoot.adjoinRoot_eq_top]; trivial
    refine Algebra.adjoin_mono ?_ this
    rintro _ rfl
    exact hr.pow_eq_one
  · rw [pb.finrank, AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C _]

theorem UpperTheory.V.Win.layerex :
    ∀ (l j : ℕ), l.Prime → ∀ (L : Type) [Field L] [NumberField L], HasMuQ l L →
      ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L'), IsLayer l j L L' := by
  intro l j hl L _ _ hq
  have hz : ∃ z : L, IsPrimitiveRoot z l := by
    obtain ⟨ζ, hζ⟩ := hq
    by_cases h2 : l = 2
    · subst h2
      rw [if_pos rfl] at hζ
      exact ⟨ζ ^ 2, hζ.pow (by norm_num) (by norm_num)⟩
    · rw [if_neg h2] at hζ
      exact ⟨ζ, hζ⟩
  have key : ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L'),
      (∃ k : ℕ, IsCyclotomicExtension {l ^ (k + 1)} L L') ∧ Module.finrank L L' = l ^ j := by
    induction j with
    | zero =>
      refine ⟨L, inferInstance, inferInstance, inferInstance, ⟨0, ?_⟩, by simp⟩
      haveI : NeZero (l ^ (0 + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
      rw [IsCyclotomicExtension.iff_singleton]
      exact ⟨by simpa using hz, fun x => Subalgebra.algebraMap_mem _ x⟩
    | succ j ih =>
      obtain ⟨K, _, _, _, ⟨k, hk⟩, hd⟩ := ih
      obtain ⟨m, hkm, ⟨z, hz⟩, hn⟩ := winlx_max K (k := k) hl
        (hk.exists_isPrimitiveRoot (Set.mem_singleton _) (pow_ne_zero _ hl.ne_zero))
      obtain ⟨K', _, _, _, hc, hd'⟩ := winlx_step K hl hz hn
      letI : Algebra L K' := ((algebraMap K K').comp (algebraMap L K)).toAlgebra
      haveI : IsScalarTower L K K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      refine ⟨K', inferInstance, inferInstance, inferInstance, ⟨m + 1, ?_⟩, ?_⟩
      · haveI : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
        have h1 := IsCyclotomicExtension.trans {l ^ (k + 1)} {l ^ (m + 2)} L K K' (algebraMap K K').injective
        rw [Set.union_comm] at h1
        exact (IsCyclotomicExtension.iff_union_of_dvd L K'
          ⟨l ^ (m + 2), Set.mem_singleton _, pow_ne_zero _ hl.ne_zero, pow_dvd_pow _ (by omega)⟩).2 h1
      · rw [← Module.finrank_mul_finrank L K K', hd, hd', pow_succ]
  obtain ⟨L', _, _, _, ⟨k, hk⟩, hd⟩ := key
  exact ⟨L', inferInstance, inferInstance, inferInstance, ⟨k + 1, hk⟩, hd⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Final
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.final :
    ∀ Ct eps C : ℝ, 0 < eps → ∃ x0 : ℝ, 2 ≤ x0 ∧ ∀ x ≥ x0, x ^ Ct * ptBound C eps x ≤ Real.exp (x ^ (4 * eps / 5)) := by
  intro Ct eps C heps
  have hba : 0 < 4 * eps / 5 - 3 * eps / 4 := by linarith
  have hb : 0 < 4 * eps / 5 := by linarith
  have E1 := ((isLittleO_log_rpow_atTop hb).const_mul_left (|Ct| + |C|)).bound
    (by norm_num : (0:ℝ) < 1 / 4)
  have E2 := (tendsto_rpow_atTop hba).eventually_ge_atTop (4 * |C|)
  have E3 := (tendsto_rpow_atTop hb).eventually_ge_atTop (4 * (Real.log 3 + |C|))
  have E4 := Filter.eventually_ge_atTop (2:ℝ)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (E1.and (E2.and (E3.and E4)))
  refine ⟨max N 2, le_max_right _ _, fun x hx => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hN x (le_trans (le_max_left _ _) hx)
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hxa : 0 ≤ x ^ (3 * eps / 4) := Real.rpow_nonneg hx0.le _
  have hxb : 0 ≤ x ^ (4 * eps / 5) := Real.rpow_nonneg hx0.le _
  have hsplit : x ^ (4 * eps / 5) = x ^ (3 * eps / 4) * x ^ (4 * eps / 5 - 3 * eps / 4) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (add_nonneg (abs_nonneg Ct) (abs_nonneg C)) hlog),
    abs_of_nonneg hxb] at h1
  have hC2 : |C| * x ^ (3 * eps / 4) ≤ 1 / 4 * x ^ (4 * eps / 5) := by
    rw [hsplit]
    nlinarith [mul_le_mul_of_nonneg_left h2 hxa]
  have hS : Real.log 3 + (|Ct| + |C|) * Real.log x + |C| + |C| * x ^ (3 * eps / 4)
      ≤ x ^ (4 * eps / 5) := by linarith
  have hp1 : C * (1 + Real.log x)
      ≤ Real.exp (|C| * (1 + Real.log x) + |C| * x ^ (3 * eps / 4)) := by
    have q1 : C * (1 + Real.log x) ≤ |C| * (1 + Real.log x) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
    have q2 : 0 ≤ |C| * x ^ (3 * eps / 4) := mul_nonneg (abs_nonneg C) hxa
    linarith [Real.add_one_le_exp (|C| * (1 + Real.log x) + |C| * x ^ (3 * eps / 4))]
  have hp2 : Real.exp (C * x ^ (3 * eps / 4))
      ≤ Real.exp (|C| * (1 + Real.log x) + |C| * x ^ (3 * eps / 4)) := by
    apply Real.exp_le_exp.mpr
    have q1 : C * x ^ (3 * eps / 4) ≤ |C| * x ^ (3 * eps / 4) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) hxa
    have q2 : 0 ≤ |C| * (1 + Real.log x) := mul_nonneg (abs_nonneg C) (by linarith)
    linarith
  have hpt : ptBound C eps x
      ≤ 3 * Real.exp (|C| * (1 + Real.log x) + |C| * x ^ (3 * eps / 4)) := by
    show C * (1 + Real.log x) + 2 * Real.exp (C * x ^ (3 * eps / 4)) ≤ _
    linarith
  have hxc : x ^ Ct ≤ Real.exp (|Ct| * Real.log x) := by
    rw [Real.rpow_def_of_pos hx0]
    apply Real.exp_le_exp.mpr
    have q := mul_le_mul_of_nonneg_right (le_abs_self Ct) hlog
    linarith
  calc x ^ Ct * ptBound C eps x
      ≤ x ^ Ct * (3 * Real.exp (|C| * (1 + Real.log x) + |C| * x ^ (3 * eps / 4))) :=
        mul_le_mul_of_nonneg_left hpt (Real.rpow_nonneg hx0.le _)
    _ ≤ Real.exp (|Ct| * Real.log x)
          * (3 * Real.exp (|C| * (1 + Real.log x) + |C| * x ^ (3 * eps / 4))) :=
        mul_le_mul_of_nonneg_right hxc (by positivity)
    _ = Real.exp (|Ct| * Real.log x + Real.log 3
          + (|C| * (1 + Real.log x) + |C| * x ^ (3 * eps / 4))) := by
        rw [Real.exp_add (|Ct| * Real.log x + Real.log 3), Real.exp_add (|Ct| * Real.log x),
          Real.exp_log (by norm_num : (0:ℝ) < 3)]
        ring
    _ ≤ Real.exp (x ^ (4 * eps / 5)) := Real.exp_le_exp.mpr (by linarith)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.ThmBabOf
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.PartA
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Layerdisc
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Layeremb
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.layeremb :
    ∀ (l j N : ℕ), l.Prime → 0 < N → ∀ (L₀ L₁ : Type) [Field L₀] [NumberField L₀] [Field L₁] [NumberField L₁]
      [Algebra L₀ L₁], Nonempty (L₀ →ₐ[ℚ] CyclotomicField N ℚ) → IsLayer l j L₀ L₁ →
        ∃ N' : ℕ, 0 < N' ∧ N' ≤ 2 * Module.finrank ℚ L₁ * N ∧ Nonempty (L₁ →ₐ[ℚ] CyclotomicField N' ℚ) := by
  intro l j N hl hN L₀ L₁ _ _ _ _ _ ⟨f⟩ ⟨⟨k, hk⟩, _⟩
  have hlk : 0 < l ^ k := pow_pos hl.pos k
  have hM : 0 < l ^ k * N := Nat.mul_pos hlk hN
  haveI : NeZero (l ^ k) := ⟨hlk.ne'⟩
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast hN.ne'⟩
  haveI : NeZero ((l ^ k * N : ℕ) : ℚ) := ⟨by exact_mod_cast hM.ne'⟩
  refine ⟨l ^ k * N, hM, ?_, ?_⟩
  · exact Nat.mul_le_mul_right N (rootdeg L₁ l k hl ⟨_, IsCyclotomicExtension.zeta_spec (l ^ k) L₀ L₁⟩)
  · obtain ⟨ζ, hζ⟩ := @IsCyclotomicExtension.exists_isPrimitiveRoot _ ℚ (CyclotomicField (l ^ k * N) ℚ) _ _ _
      (CyclotomicField.isCyclotomicExtension _ ℚ) _ (Set.mem_singleton _) hM.ne'
    have hN' := hζ.pow hM rfl
    have hl' := hζ.pow hM (Nat.mul_comm _ _)
    have i2 := @IsCyclotomicExtension.isSplittingField_X_pow_sub_one N _ ℚ (CyclotomicField N ℚ) _ _ _
      (CyclotomicField.isCyclotomicExtension N ℚ)
    let e : CyclotomicField N ℚ →+* CyclotomicField (l ^ k * N) ℚ :=
      (@Polynomial.IsSplittingField.lift (CyclotomicField (l ^ k * N) ℚ) ℚ (CyclotomicField N ℚ) _ _ _ _ _
        (Polynomial.X ^ N - 1) i2 (by simpa using Polynomial.X_pow_sub_one_splits hN')).toRingHom
    letI : Algebra L₀ (CyclotomicField (l ^ k * N) ℚ) := (e.comp f.toRingHom).toAlgebra
    haveI := IsCyclotomicExtension.isSplittingField_X_pow_sub_one (l ^ k) L₀ L₁
    let h : L₁ →ₐ[L₀] CyclotomicField (l ^ k * N) ℚ :=
      Polynomial.IsSplittingField.lift _ (Polynomial.X ^ (l ^ k) - 1)
        (by simpa using Polynomial.X_pow_sub_one_splits hl')
    exact ⟨h.toRingHom.toRatAlgHom⟩
end

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.layerdisc :
    ∀ (l j n1 N0 : ℕ), l.Prime → 0 < N0 → ∃ (n0 : ℕ) (c0 : ℝ), 0 ≤ c0 ∧
      ∀ (P : ℕ) (w : ℝ), 0 < P → 1 ≤ w → Real.log (P : ℝ) ≤ w →
        ∀ (L₀ L₁ : Type) [Field L₀] [NumberField L₀] [Field L₁] [NumberField L₁] [Algebra L₀ L₁],
          Module.finrank ℚ L₀ ≤ n1 → Nonempty (L₀ →ₐ[ℚ] CyclotomicField (N0 * P) ℚ) → IsLayer l j L₀ L₁ →
            Module.finrank ℚ L₁ ≤ n0 ∧ Real.log (2 * ((discr L₁).natAbs : ℝ)) ≤ c0 * w := by
  intro l j n1 N0 hl hN0
  have hlj : 1 ≤ l ^ j := Nat.one_le_pow _ _ hl.pos
  set n0 : ℕ := (n1 + 1) * l ^ j with hn0
  have hn0pos : 1 ≤ n0 := by
    rw [hn0]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hn0R : (1:ℝ) ≤ (n0:ℝ) := by exact_mod_cast hn0pos
  have hN0R : (1:ℝ) ≤ (N0:ℝ) := by exact_mod_cast hN0
  have hC1 : (1:ℝ) ≤ 2 * (n0:ℝ) * (N0:ℝ) := by nlinarith
  have hlogC : 0 ≤ Real.log (2 * (n0:ℝ) * (N0:ℝ)) := Real.log_nonneg hC1
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  set A : ℝ := Real.log 2 + (n0:ℝ) * Real.log (2 * (n0:ℝ) * (N0:ℝ)) with hA
  have hA0 : 0 ≤ A := by
    have : 0 ≤ (n0:ℝ) * Real.log (2 * (n0:ℝ) * (N0:ℝ)) := mul_nonneg (by linarith) hlogC
    linarith
  refine ⟨n0, A + n0, by linarith, ?_⟩
  intro P w hP hw hlogP L₀ L₁ _ _ _ _ _ hdeg hemb hlay
  have hdim : Module.finrank ℚ L₀ * Module.finrank L₀ L₁ = Module.finrank ℚ L₁ :=
    Module.finrank_mul_finrank ℚ L₀ L₁
  have hrel : Module.finrank L₀ L₁ = l ^ j := by
    unfold IsLayer at hlay
    exact hlay.2
  have hd1 : Module.finrank ℚ L₁ ≤ n0 := by
    rw [← hdim, hrel, hn0]
    exact Nat.mul_le_mul_right _ (by omega)
  refine ⟨hd1, ?_⟩
  have hNP : 0 < N0 * P := Nat.mul_pos hN0 hP
  obtain ⟨N', hN'pos, hN'le, hN'emb⟩ := layeremb l j (N0 * P) hl hNP L₀ L₁ hemb hlay
  have hdisc := disc L₁ N' hN'pos hN'emb
  have hd1R : ((Module.finrank ℚ L₁ : ℕ) : ℝ) ≤ (n0:ℝ) := by exact_mod_cast hd1
  have hPR : (1:ℝ) ≤ (P:ℝ) := by exact_mod_cast hP
  have hN'R : (1:ℝ) ≤ (N':ℝ) := by exact_mod_cast hN'pos
  have hlogN' : 0 ≤ Real.log (N':ℝ) := Real.log_nonneg hN'R
  have hN'le' : (N':ℝ) ≤ 2 * (n0:ℝ) * (N0:ℝ) * (P:ℝ) := by
    have h1 : (N':ℝ) ≤ ((2 * Module.finrank ℚ L₁ * (N0 * P) : ℕ) : ℝ) := by exact_mod_cast hN'le
    have h2 : ((2 * Module.finrank ℚ L₁ * (N0 * P) : ℕ) : ℝ) ≤ 2 * (n0:ℝ) * (N0:ℝ) * (P:ℝ) := by
      push_cast
      have : (0:ℝ) ≤ (N0:ℝ) * (P:ℝ) := by positivity
      nlinarith
    linarith
  have hlogle : Real.log (N':ℝ) ≤ Real.log (2 * (n0:ℝ) * (N0:ℝ)) + Real.log (P:ℝ) := by
    rw [← Real.log_mul (by linarith) (by linarith)]
    exact Real.log_le_log (by linarith) hN'le'
  have hLP0 : 0 ≤ Real.log (P:ℝ) := Real.log_nonneg hPR
  have hlog2D : Real.log (2 * ((discr L₁).natAbs : ℝ)) ≤ Real.log 2 + Real.log ((discr L₁).natAbs : ℝ) := by
    rcases Nat.eq_zero_or_pos (discr L₁).natAbs with h | h
    · rw [h]
      simpa using hlog2
    · have hD : ((discr L₁).natAbs : ℝ) ≠ 0 := by positivity
      rw [Real.log_mul (by norm_num) hD]
  have k1 : ((Module.finrank ℚ L₁ : ℕ) : ℝ) * Real.log (N':ℝ) ≤ (n0:ℝ) * Real.log (N':ℝ) :=
    mul_le_mul_of_nonneg_right hd1R hlogN'
  have k2 : (n0:ℝ) * Real.log (N':ℝ) ≤ (n0:ℝ) * (Real.log (2 * (n0:ℝ) * (N0:ℝ)) + Real.log (P:ℝ)) :=
    mul_le_mul_of_nonneg_left hlogle (by linarith)
  have k3 : (n0:ℝ) * Real.log (P:ℝ) ≤ (n0:ℝ) * w := mul_le_mul_of_nonneg_left hlogP (by linarith)
  have k4 : A ≤ A * w := by nlinarith
  nlinarith
end

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

private theorem ne_top_and_toNat_le_of_le_one_add (a b : ℕ∞) (hb : b ≠ ⊤) (h : a ≤ 1 + b) :
    a ≠ ⊤ ∧ a.toNat ≤ 1 + b.toNat := by
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hb
  have h' : a ≤ ((1 + n : ℕ) : ℕ∞) := by push_cast; exact h
  have ha : a ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) h'
  obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp ha
  refine ⟨ha, ?_⟩
  simp only [ENat.toNat_coe]
  exact_mod_cast h'

theorem UpperTheory.V.Win.partA :
    ∀ CK : ℝ, 0 < CK → LemmaK CK → ∀ (M : AbF) (R : ℕ) (J Ct eps A1 : ℝ), 0 < J → 0 ≤ Ct → 0 < eps →
      ∃ x0 : ℝ, ∀ e t : ℝ → ℕ, admitted A1 Ct e t → ∀ (X : ℝ) (q d : ℕ), PrimePair M.m q d →
        Real.log ((q : ℝ) * d) ≤ X ^ (eps / (4 * J)) →
        ∀ (L₀ : Type) [Field L₀] [NumberField L₀], TwoBase M q d L₀ → ABound 2 R L₀ →
          ∃ Exc : Finset ℕ, Exc.card ≤ R ∧ ∀ x ≥ x0, X ^ (1 / J) ≤ x → x ≤ X → Good (eps / (2 * CK)) Ct Exc x →
            BaAt M eps e t q d x := by
  intro CK hCK hK M R J Ct eps A1 hJ hCt heps
  obtain ⟨n0, c0, hc0, hLD⟩ := layerdisc 2 (jZero 2 R) (8 * M.deg) (4 * M.m) Nat.prime_two
    (by have := M.pos; omega)
  obtain ⟨C, hC0, hC⟩ := point2 CK hCK hK 2 R (16 * M.deg) n0 c0 J Ct eps (2 * |A1| + 2)
    hc0 hJ hCt heps (by positivity)
  obtain ⟨x0, hx02, hx0⟩ := final Ct eps C heps
  refine ⟨x0, fun e t hAdm X q d hPP hlogqd L₀ _ _ hTB hAB => ?_⟩
  obtain ⟨hmu, hfin, hcyc, hE⟩ := hTB
  have hSB : SecondBound 2 R L₀ := hAB.2
  obtain ⟨c, hζ, hZ⟩ := exc 2 R L₀ hAB
  have hc : c ≤ 16 * M.deg := by
    have h1 := rootdeg L₀ 2 c Nat.prime_two hζ
    have h2 : c < 2 ^ c := Nat.lt_two_pow_self
    omega
  obtain ⟨L₂, i1, i2, i3, hL₂⟩ := layerex 2 (jZero 2 R) Nat.prime_two L₀ hmu
  obtain ⟨Exc, hExc⟩ := hZ ⌊X ^ Ct⌋₊
  refine ⟨Exc, hExc.1, fun x hx hXx hxX hG E _ _ hEc => ?_⟩
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  obtain ⟨he2, h2e, -, htx⟩ := hAdm x (by linarith)
  have hw : (1 : ℝ) ≤ x ^ (eps / 4) := Real.one_le_rpow hx1 (by positivity)
  have hP : 0 < q * d := Nat.mul_pos hPP.1.pos hPP.2.2.1.pos
  have hlogP : Real.log ((q * d : ℕ) : ℝ) ≤ x ^ (eps / 4) := by
    push_cast
    exact hlogqd.trans (logs.2.1 J eps X x hJ heps hX1 hXx)
  have hcyc' : Nonempty (L₀ →ₐ[ℚ] CyclotomicField (4 * M.m * (q * d)) ℚ) := by
    rw [← mul_assoc]; exact hcyc
  obtain ⟨hn0, hdisc⟩ := hLD (q * d) (x ^ (eps / 4)) hP hw hlogP L₀ L₂ hfin hcyc' hL₂
  obtain ⟨m, L₁, j1, j2, j3, hL₁, hme, hsha⟩ := hE (e x) he2 E hEc
  have hm : (m : ℝ) ≤ (2 * |A1| + 2) * (1 + Real.log x) := by
    have h3 := logs.2.2 (e x) A1 x hx1 h2e
    have h4 : (m : ℝ) ≤ (e x : ℝ) + 2 := by exact_mod_cast hme
    linarith
  have hpb : 0 ≤ ptBound C eps x := by
    show 0 ≤ C * (1 + Real.log x) + 2 * Real.exp (C * x ^ (3 * eps / 4))
    exact add_nonneg (mul_nonneg hC0 (by linarith)) (by positivity)
  show VVat 2 E (t x) (Real.exp (x ^ (4 * eps / 5)))
  refine vvat 2 (t x) E (x ^ Ct) (ptBound C eps x) _ hpb htx (hx0 x hx) ?_
  intro k hk1 hkt
  have hkx : (k : ℝ) ≤ x ^ Ct := le_trans (by exact_mod_cast hkt.le) htx
  have hk := hC L₀ hmu hSB c X Exc hc hExc L₂ hL₂ hn0 x hx1 hXx hxX hG hdisc k hk1 hkx
    m L₁ hL₁ hm
  obtain ⟨hne, hle⟩ := ne_top_and_toNat_le_of_le_one_add _ _ hk.1 (hsha k hk1)
  refine ⟨hne, ?_⟩
  have h5 : ((shaInv E 2 k).toNat : ℝ) ≤ 1 + ((shaInv L₁ 2 k).toNat : ℝ) := by
    exact_mod_cast hle
  linarith [hk.2]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.PartB
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.EquivOfRange
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

private theorem act_root {K : Type} [Field K] {N : ℕ} [NeZero N] {ζ x : K} (hζ : IsPrimitiveRoot ζ N)
    (σ : K →+* K) {a : ℕ} (hσ : σ ζ = ζ ^ a) (hx : x ^ N = 1) : σ x = x ^ a := by
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
  rw [map_pow, hσ, pow_right_comm]

private theorem exists_pow {N : ℕ} [NeZero N] {ζ : CyclotomicField N ℚ} (hζ : IsPrimitiveRoot ζ N)
    (τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) : ∃ a : ℕ, τ ζ = ζ ^ a := by
  obtain ⟨i, -, h⟩ := hζ.eq_pow_of_pow_eq_one (ξ := τ ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
  exact ⟨i, h.symm⟩

private theorem mem_fix {E K : Type} [Field E] [Field K] [Algebra ℚ E] [Algebra ℚ K] (j : E →ₐ[ℚ] K)
    (τ : K ≃ₐ[ℚ] K) : τ ∈ j.fieldRange.fixingSubgroup ↔ ∀ x : E, τ (j x) = j x := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  exact ⟨fun h x => h _ ⟨x, rfl⟩, fun h _ ⟨x, hx⟩ => hx ▸ h x⟩

private theorem ker_congr (A : AbF) {a b : ℕ} (h : a ≡ b [MOD A.m]) (hb : A.ker b) : A.ker a := by
  obtain ⟨u, hu, e⟩ := hb
  exact ⟨u, hu, e.trans ((ZMod.natCast_eq_natCast_iff _ _ _).2 h).symm⟩

private theorem exists_res {K L : Type} [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] [Normal ℚ K]
    (f : K →ₐ[ℚ] L) (σ : L ≃ₐ[ℚ] L) : ∃ τ : K ≃ₐ[ℚ] K, ∀ x : K, σ (f x) = f (τ x) := by
  letI : Algebra K L := f.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  exact ⟨σ.restrictNormal K, fun x => (σ.restrictNormal_commutes K x).symm⟩

private theorem equiv_of_range {F L L' Ω : Type} [Field F] [Field L] [Field L'] [Field Ω] [Algebra F L]
    [Algebra F L'] [Algebra F Ω] (g : L →ₐ[F] Ω) (g' : L' →ₐ[F] Ω) (e : g.fieldRange = g'.fieldRange) :
    Nonempty (L ≃+* L') :=
  ⟨((g.equivFieldRange.trans (IntermediateField.equivOfEq e)).trans g'.equivFieldRange.symm).toRingEquiv⟩

private theorem equiv_of_fix {L L' Ω : Type} [Field L] [Field L'] [Field Ω] [Algebra ℚ L] [Algebra ℚ L']
    [Algebra ℚ Ω] [IsGalois ℚ Ω] (g : L →ₐ[ℚ] Ω) (g' : L' →ₐ[ℚ] Ω)
    (h : ∀ σ : Ω ≃ₐ[ℚ] Ω, (∀ x, σ (g x) = g x) ↔ ∀ x, σ (g' x) = g' x) : Nonempty (L ≃+* L') := by
  have e : g.fieldRange = g'.fieldRange := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup g.fieldRange,
      ← InfiniteGalois.fixedField_fixingSubgroup g'.fieldRange]
    congr 1
    ext σ
    rw [mem_fix, mem_fix, h]
  exact equiv_of_range g g' e

theorem UpperTheory.V.Win.abiso :
    ∀ (A : AbF) (L L' : Type) [Field L] [NumberField L] [Field L'] [NumberField L'],
      IsAbField A L → IsAbField A L' → Nonempty (L ≃+* L') := by
  intro A L L' _ _ _ _ hL hL'
  obtain ⟨N, hN, i, ζ, hm, hζ, H0⟩ := hL
  obtain ⟨N', hN', j, ζ', hm', hζ', H⟩ := hL'
  haveI : NeZero A.m := ⟨A.pos.ne'⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension _ ℚ
  haveI : IsCyclotomicExtension {N'} ℚ (CyclotomicField N' ℚ) := CyclotomicField.isCyclotomicExtension _ ℚ
  haveI : IsAbelianGalois ℚ (CyclotomicField N ℚ) := IsCyclotomicExtension.isAbelianGalois {N} ℚ _
  haveI : IsAbelianGalois ℚ (CyclotomicField N' ℚ) := IsCyclotomicExtension.isAbelianGalois {N'} ℚ _
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := by
    first
      | exact @IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) _ _
      | convert @IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) _ _
  let f : CyclotomicField N ℚ →ₐ[ℚ] AlgebraicClosure ℚ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let f' : CyclotomicField N' ℚ →ₐ[ℚ] AlgebraicClosure ℚ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine equiv_of_fix (f.comp i) (f'.comp j) fun σ => ?_
  obtain ⟨τ, hσ⟩ := exists_res f σ
  obtain ⟨τ', hσ'⟩ := exists_res f' σ
  obtain ⟨a, hτ⟩ := exists_pow hζ τ
  obtain ⟨b, hb⟩ := exists_pow hζ' τ'
  obtain ⟨k, hk⟩ := id hm
  obtain ⟨k', hk'⟩ := id hm'
  have hω : IsPrimitiveRoot (f (ζ ^ k)) A.m :=
    (hζ.pow (NeZero.pos N) (by rw [hk, mul_comm])).map_of_injective f.injective
  have hω' : IsPrimitiveRoot (f' (ζ' ^ k')) A.m :=
    (hζ'.pow (NeZero.pos N') (by rw [hk', mul_comm])).map_of_injective f'.injective
  have h1 : σ (f (ζ ^ k)) = f (ζ ^ k) ^ a := by
    rw [hσ, map_pow τ, hτ, pow_right_comm, map_pow f]
  have h2 : σ (f' (ζ' ^ k')) = f' (ζ' ^ k') ^ b := by
    rw [hσ', map_pow τ', hb, pow_right_comm, map_pow f']
  have h3 : σ (f (ζ ^ k)) = f (ζ ^ k) ^ b :=
    act_root hω' (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) h2 hω.pow_eq_one
  have hab : a ≡ b [MOD A.m] := by
    have := ((hω.isOfFinOrder A.pos.ne').pow_eq_pow_iff_modEq).1 (h1.symm.trans h3)
    rwa [← hω.eq_orderOf] at this
  have h4 : A.ker a ↔ A.ker b := ⟨ker_congr A hab.symm, ker_congr A hab⟩
  have e1 : (∀ x, σ ((f.comp i) x) = (f.comp i) x) ↔ ∀ x, τ (i x) = i x := by
    refine forall_congr' fun x => ?_
    show σ (f (i x)) = f (i x) ↔ _
    rw [hσ]
    exact f.injective.eq_iff
  have e2 : (∀ x, σ ((f'.comp j) x) = (f'.comp j) x) ↔ ∀ x, τ' (j x) = j x := by
    refine forall_congr' fun x => ?_
    show σ (f' (j x)) = f' (j x) ↔ _
    rw [hσ']
    exact f'.injective.eq_iff
  rw [e1, e2, H0 τ a hτ, H τ' b hb, h4]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Layeriso
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

private theorem nonempty_ringEquiv_of_isCyclotomic_finrank_eq (l j k k' : ℕ) (hl : l.Prime) (hk : k ≤ k') (L₀ L₀' L₁ L₁' : Type)
    [Field L₀] [Field L₀'] [Field L₁] [Field L₁'] [Algebra L₀ L₁] [Algebra L₀' L₁']
    (e : L₀ ≃+* L₀') (h₁ : IsCyclotomicExtension {l ^ k} L₀ L₁)
    (h₁' : IsCyclotomicExtension {l ^ k'} L₀' L₁')
    (d₁ : Module.finrank L₀ L₁ = l ^ j) (d₁' : Module.finrank L₀' L₁' = l ^ j) :
    Nonempty (L₁ ≃+* L₁') := by
  haveI : NeZero (l ^ k') := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta (l ^ k') L₀' L₁' ^ (l ^ (k' - k))) (l ^ k) :=
    (IsCyclotomicExtension.zeta_spec (l ^ k') L₀' L₁').pow (pow_pos hl.pos _)
      (by rw [← pow_add, Nat.sub_add_cancel hk])
  letI : Algebra L₀ L₀' := e.toRingHom.toAlgebra
  letI : Algebra L₀ L₁' := ((algebraMap L₀' L₁').comp e.toRingHom).toAlgebra
  haveI : IsScalarTower L₀ L₀' L₁' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have h1 : Module.finrank L₀ L₀' = 1 := by
    rw [← (AlgEquiv.ofRingEquiv (R := L₀) (A₁ := L₀) (A₂ := L₀') (f := e)
      (fun _ => rfl)).toLinearEquiv.finrank_eq, Module.finrank_self]
  have h2 : Module.finrank L₀ L₁' = l ^ j := by
    rw [← Module.finrank_mul_finrank L₀ L₀' L₁', h1, one_mul, d₁']
  haveI : FiniteDimensional L₀ L₁' :=
    Module.finite_of_finrank_pos (by rw [h2]; exact pow_pos hl.pos _)
  haveI : Algebra.IsIntegral L₀ L₁' := Algebra.IsIntegral.of_finite L₀ L₁'
  haveI := hζ.intermediateField_adjoin_isCyclotomicExtension L₀
  let φ := IsCyclotomicExtension.algEquiv {l ^ k} L₀ L₁
    (IntermediateField.adjoin L₀ {IsCyclotomicExtension.zeta (l ^ k') L₀' L₁' ^ (l ^ (k' - k))})
  have htop : IntermediateField.adjoin L₀
      {IsCyclotomicExtension.zeta (l ^ k') L₀' L₁' ^ (l ^ (k' - k))} = ⊤ :=
    IntermediateField.eq_of_le_of_finrank_eq le_top
      (by rw [IntermediateField.finrank_top', ← φ.toLinearEquiv.finrank_eq, d₁, h2])
  exact ⟨φ.toRingEquiv.trans ((IntermediateField.equivOfEq htop).toRingEquiv.trans
    IntermediateField.topEquiv.toRingEquiv)⟩

theorem UpperTheory.V.Win.layeriso :
    ∀ (l j : ℕ), l.Prime → ∀ (L₀ L₀' L₁ L₁' : Type) [Field L₀] [NumberField L₀] [Field L₀'] [NumberField L₀']
      [Field L₁] [NumberField L₁] [Field L₁'] [NumberField L₁'] [Algebra L₀ L₁] [Algebra L₀' L₁'],
        Nonempty (L₀ ≃+* L₀') → IsLayer l j L₀ L₁ → IsLayer l j L₀' L₁' → Nonempty (L₁ ≃+* L₁') := by
  intro l j hl L₀ L₀' L₁ L₁' _ _ _ _ _ _ _ _ _ _ ⟨e⟩ ⟨⟨k, hk⟩, d⟩ ⟨⟨k', hk'⟩, d'⟩
  rcases le_total k k' with h | h
  · exact nonempty_ringEquiv_of_isCyclotomic_finrank_eq l j k k' hl h L₀ L₀' L₁ L₁' e hk hk' d d'
  · obtain ⟨f⟩ := nonempty_ringEquiv_of_isCyclotomic_finrank_eq l j k' k hl h L₀' L₀ L₁' L₁ e.symm hk' hk d' d
    exact ⟨f.symm⟩
end

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

private theorem exists_isPrimitiveRoot_of_hasMu_of_isAbField (A : AbF) (l : ℕ) [Fact l.Prime] (hA : A.HasMu l) (L : Type) [Field L]
    [NumberField L] (hL : IsAbField A L) : ∃ ζ : L, IsPrimitiveRoot ζ l := by
  obtain ⟨N, hN, j, ζ, h1, h2, h3⟩ := hL
  obtain ⟨k, hk⟩ := hA.1.trans h1
  have hz : IsPrimitiveRoot (ζ ^ k) l := h2.pow (NeZero.pos N) (by rw [hk, mul_comm])
  have key : ζ ^ k ∈ IntermediateField.fixedField (IntermediateField.fixingSubgroup j.fieldRange) := by
    rintro ⟨τ, hτ⟩
    rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
    obtain ⟨a, -, ha⟩ := h2.eq_pow_of_pow_eq_one
      (show (τ ζ) ^ N = 1 by rw [← map_pow, h2.pow_eq_one, map_one])
    have hker := (h3 τ a ha.symm).mp (fun x => hτ (j x) ⟨x, rfl⟩)
    have hmod := hA.2 a hker
    show τ (ζ ^ k) = ζ ^ k
    rw [map_pow, ← ha, ← pow_mul]
    have ha1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with h | h
      · subst h
        have hl1 : l ∣ 1 := Nat.modEq_zero_iff_dvd.mp hmod.symm
        exact absurd (Nat.le_of_dvd one_pos hl1) (not_le.mpr (Fact.out : l.Prime).one_lt)
      · exact h
    obtain ⟨q, hq⟩ := (Nat.modEq_iff_dvd' ha1).mp hmod.symm
    have ha' : a = l * q + 1 := (Nat.sub_eq_iff_eq_add ha1).mp hq
    calc ζ ^ (a * k) = ζ ^ (k + N * q) := by
          congr 1
          rw [ha', hk]
          ring
      _ = ζ ^ k := by rw [pow_add, pow_mul, h2.pow_eq_one, one_pow, mul_one]
  haveI : IsGalois ℚ (CyclotomicField N ℚ) :=
    IsCyclotomicExtension.isGalois (S := {N}) (K := ℚ) (L := CyclotomicField N ℚ)
  rw [IsGalois.fixedField_fixingSubgroup] at key
  obtain ⟨y, hy⟩ := key
  refine ⟨y, ?_⟩
  rw [← hy] at hz
  exact (IsPrimitiveRoot.map_iff_of_injective j.toRingHom.injective).mp hz

theorem UpperTheory.V.Win.partB :
    ∀ CK : ℝ, 0 < CK → LemmaK CK → ∀ (l R : ℕ) [Fact l.Prime], l ≠ 2 → ∀ A : AbF, A.HasMu l →
      ∀ (L₀ : Type) [Field L₀] [NumberField L₀], IsAbField A L₀ → ABound l R L₀ →
        ∀ J Ct eps A1 : ℝ, 0 < J → 0 ≤ Ct → 0 < eps → ∃ x0 : ℝ, ∀ e t : ℝ → ℕ, admitted A1 Ct e t → ∀ X : ℝ,
          ∃ Exc : Finset ℕ, Exc.card ≤ R ∧ ∀ x ≥ x0, X ^ (1 / J) ≤ x → x ≤ X → Good (eps / (2 * CK)) Ct Exc x →
            ∀ (L₀' : Type) [Field L₀'] [NumberField L₀'], IsAbField A L₀' →
              ∀ (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀' L₁], IsLayer l (jZero l R) L₀' L₁ →
                VVat l L₁ (t x) (Real.exp (x ^ (4 * eps / 5))) := by
  intro CK hCK hK l R _ hl2 A hA L₀ _ _ hL₀ hAB J Ct eps A1 hJ hCt heps
  have hmu0 : HasMuQ l L₀ := by
    obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_hasMu_of_isAbField A l hA L₀ hL₀
    exact ⟨ζ, by rw [if_neg hl2]; exact hζ⟩
  obtain ⟨c, -, hc⟩ := exc l R L₀ hAB
  obtain ⟨L₂, i1, i2, i3, hL₂⟩ := layerex l (jZero l R) Fact.out L₀ hmu0
  have hc0 : 0 ≤ Real.log (2 * ((NumberField.discr L₂).natAbs : ℝ)) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ ((NumberField.discr L₂).natAbs : ℝ) :=
      Nat.one_le_cast.mpr (Int.natAbs_pos.mpr (NumberField.discr_ne_zero L₂))
    linarith
  obtain ⟨C, -, hP⟩ := point2 CK hCK hK l R c (Module.finrank ℚ L₂)
    (Real.log (2 * ((NumberField.discr L₂).natAbs : ℝ))) J Ct eps (jZero l R : ℝ) hc0 hJ hCt heps
    (Nat.cast_nonneg _)
  obtain ⟨x1, hx1two, hx1⟩ := final Ct eps C heps
  refine ⟨x1, fun e t hAdm X => ?_⟩
  obtain ⟨Exc, hExc⟩ := hc ⌊X ^ Ct⌋₊
  refine ⟨Exc, hExc.1, fun x hx hXx hxX hgood L₀' _ _ hL₀' L₁ _ _ _ hL₁ => ?_⟩
  obtain ⟨f0⟩ := abiso A L₀ L₀' hL₀ hL₀'
  obtain ⟨f1⟩ := layeriso l (jZero l R) Fact.out L₀ L₀' L₂ L₁ ⟨f0⟩ hL₂ hL₁
  have hx1' : (1 : ℝ) ≤ x := by linarith
  have hadm := hAdm x (by linarith)
  have hQ : ∀ e' : ℕ, 1 ≤ e' → (e' : ℝ) ≤ x ^ Ct →
      shaInv L₂ l e' ≠ ⊤ ∧ ((shaInv L₂ l e').toNat : ℝ) + 1 ≤ ptBound C eps x := by
    intro e' he1 he2
    refine hP L₀ hmu0 hAB.2 c X Exc le_rfl hExc L₂ hL₂ le_rfl x hx1' hXx hxX hgood ?_ e' he1 he2
      (jZero l R) L₂ hL₂ ?_
    · exact le_mul_of_one_le_right hc0 (Real.one_le_rpow hx1' (by positivity))
    · exact le_mul_of_one_le_right (Nat.cast_nonneg _) (by linarith [Real.log_nonneg hx1'])
  have hb : 0 ≤ ptBound C eps x := by
    have := (hQ 1 le_rfl (by simpa using Real.one_le_rpow hx1' hCt)).2
    have : (0 : ℝ) ≤ ((shaInv L₂ l 1).toNat : ℝ) := Nat.cast_nonneg _
    linarith
  refine vvat l (t x) L₁ (x ^ Ct) (ptBound C eps x) _ hb hadm.2.2.2 (hx1 x hx) ?_
  intro e' he1 he2
  rw [← shaInv_congr f1]
  have h := hQ e' he1 (le_trans (by exact_mod_cast he2.le) hadm.2.2.2)
  exact ⟨h.1, by linarith [h.2]⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Window
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Window1
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.window1 :
    ∀ (R : ℕ) (B U : ℝ) (T : Finset ℝ), 1 ≤ B → 0 < U → T.card ≤ R →
      ∃ y : ℝ, U / (2 ^ (R + 2) * B ^ R) ≤ y ∧ 2 * y ≤ U ∧ ∀ a ∈ T, ∀ u : ℝ, y ≤ u → u ≤ 2 * y → a ≤ u → B * a ≤ u := by
  intro R
  induction R with
  | zero =>
    intro B U T hB hU hT
    have hT0 : T = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hT0
    refine ⟨U / 2, ?_, by linarith, ?_⟩
    · apply div_le_div_of_nonneg_left hU.le (by norm_num)
      norm_num
    · intro a ha
      simp at ha
  | succ n ih =>
    intro B U T hB hU hT
    have hB0 : 0 < B := by linarith
    by_cases h : ∃ a ∈ T, U / (2 * B) < a ∧ a ≤ U
    · obtain ⟨a0, ha0, h1, h2⟩ := h
      obtain ⟨y, hy1, hy2, hy3⟩ := ih B (U / (2 * B)) (T.erase a0) hB (by positivity)
        (by rw [Finset.card_erase_of_mem ha0]; omega)
      refine ⟨y, ?_, ?_, ?_⟩
      · calc U / (2 ^ (n + 1 + 2) * B ^ (n + 1))
            = U / (2 * B) / (2 ^ (n + 2) * B ^ n) := by
              rw [div_div]
              congr 1
              ring
          _ ≤ y := hy1
      · have : U / (2 * B) ≤ U := div_le_self hU.le (by linarith)
        linarith
      · intro a ha u hu1 hu2 hau
        by_cases hae : a = a0
        · subst hae
          exfalso
          have : U / (2 * B) < u := lt_of_lt_of_le h1 hau
          linarith
        · exact hy3 a (Finset.mem_erase.mpr ⟨hae, ha⟩) u hu1 hu2 hau
    · push_neg at h
      refine ⟨U / 2, ?_, by linarith, ?_⟩
      · apply div_le_div_of_nonneg_left hU.le (by norm_num)
        have h2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
        have h3 : (1 : ℝ) ≤ B ^ (n + 1) := one_le_pow₀ hB
        have h4 : (2 : ℝ) ^ (n + 1 + 2) = 8 * 2 ^ n := by ring
        rw [h4]
        nlinarith
      · intro a ha u hu1 hu2 hau
        by_contra hc
        push_neg at hc
        have ha1 : U / (2 * B) < a := by
          rw [div_lt_iff₀ (by positivity)]
          nlinarith
        have := h a ha ha1
        linarith
end

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.window :
    ∀ (R : ℕ) (eta Ct X : ℝ) (Exc : Finset ℕ), 0 < eta → eta ≤ Ct → 1 < X → Exc.card ≤ R →
      ∃ Y : ℝ, InRange (2 ^ (R + 2) * (Ct / eta) ^ R) X Y ∧ ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (2 : ℝ) → Good eta Ct Exc x := by
  intro R eta Ct X Exc heta hle hX hcard
  classical
  have hCt : 0 < Ct := lt_of_lt_of_le heta hle
  have hX0 : 0 < X := by linarith
  have hB : 1 ≤ Ct / eta := (one_le_div heta).mpr hle
  obtain ⟨y, hy1, hy2, hy3⟩ := UpperTheory.V.Win.window1 R (Ct / eta) (Real.log X)
    (Exc.image fun e : ℕ => Real.log (e : ℝ) / Ct) hB (Real.log_pos hX)
    (le_trans Finset.card_image_le hcard)
  have hsq : Real.exp y ^ (2 : ℝ) = Real.exp (2 * y) := by
    rw [← Real.exp_mul, mul_comm]
  refine ⟨Real.exp y, ⟨?_, ?_⟩, ?_⟩
  · rw [Real.rpow_def_of_pos hX0, Real.exp_le_exp, mul_one_div]
    exact hy1
  · rw [hsq, ← Real.le_log_iff_exp_le hX0]
    exact hy2
  · intro x hx1 hx2 e he hex
    have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos y) hx1
    rcases Nat.eq_zero_or_pos e with h0 | hpos
    · subst h0
      simpa using (Real.rpow_pos_of_pos hx0 eta).le
    have he0 : (0 : ℝ) < e := by exact_mod_cast hpos
    have hu1 : y ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx1
    have hu2 : Real.log x ≤ 2 * y := by
      rw [Real.log_le_iff_le_exp hx0, ← hsq]
      exact hx2
    have hu3 : Real.log (e : ℝ) / Ct ≤ Real.log x := by
      rw [div_le_iff₀ hCt, mul_comm, ← Real.log_rpow hx0]
      exact Real.log_le_log he0 hex
    have h := hy3 _ (Finset.mem_image_of_mem _ he) (Real.log x) hu1 hu2 hu3
    have h' : Ct / eta * (Real.log (e : ℝ) / Ct) = Real.log (e : ℝ) / eta := by
      field_simp
    rw [h', div_le_iff₀ heta] at h
    rw [Real.rpow_def_of_pos hx0, ← Real.log_le_iff_le_exp he0]
    exact h
end

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.thmBab_of :
    (∃ CK : ℝ, LemmaK CK) → FixedIn → TwoIn → ∃ K : BConst, ∀ Ct : ℝ, 1 ≤ Ct → ThmBab K Ct := by
  rintro ⟨CK0, hK0⟩ hF hT
  classical
  have hCK1 : (1 : ℝ) ≤ max CK0 1 := le_max_right _ _
  have hCKpos : (0 : ℝ) < max CK0 1 := lt_of_lt_of_le one_pos hCK1
  have hK : LemmaK (max CK0 1) := kmono CK0 _ (le_max_left _ _) hK0
  let P : ℕ → AbF → ℕ → Prop := fun l A R =>
    ∃ (_ : Fact l.Prime) (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀), IsAbField A L₀ ∧ ABound l R L₀
  let R0 : AbF → ℕ := fun M => Classical.choose (hT M)
  let Rl : ℕ → AbF → ℕ := fun l A => if h : ∃ R, P l A R then Classical.choose h else 0
  refine ⟨BConst.mk R0 Rl (max CK0 1) hCKpos, fun Ct hCt => ?_⟩
  unfold ThmBab BShape IsBWindow
  intro M B' L hAux eps A1 heps heps'
  unfold OddPrimesWithRootsOfUnity at hAux
  have hCt0 : 0 < Ct := lt_of_lt_of_le one_pos hCt
  set CK : ℝ := max CK0 1 with hCKdef
  set R : ℕ := R0 M + ∑ l ∈ B', Rl l (L l) with hRdef
  set J : ℝ := 2 ^ (R + 2) * (2 * CK * Ct / eps) ^ R with hJdef
  have hJpos : 0 < J := by
    have : 0 < 2 * CK * Ct / eps := by positivity
    positivity
  obtain ⟨x0A, hA⟩ := partA CK hCKpos hK M (R0 M) J Ct eps A1 hJpos hCt0.le heps
  have hB : ∀ l ∈ B', ∃ x0 : ℝ, ∀ e t, admitted A1 Ct e t → ∀ X : ℝ, ∃ Exc : Finset ℕ,
      Exc.card ≤ Rl l (L l) ∧ ∀ x ≥ x0, X ^ (1 / J) ≤ x → x ≤ X → Good (eps / (2 * CK)) Ct Exc x →
        ∀ (_ : Fact l.Prime) (L₀' : Type) [Field L₀'] [NumberField L₀'], IsAbField (L l) L₀' →
          ∀ (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀' L₁],
            IsLayer l (Nat.log l (Rl l (L l)) + 3) L₀' L₁ → VVat l L₁ (t x) (Real.exp (x ^ (4 * eps / 5))) := by
    intro l hl
    obtain ⟨hp, hl2, hmu⟩ := hAux l hl
    haveI : Fact l.Prime := ⟨hp⟩
    by_cases hex : ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀), IsAbField (L l) L₀
    · obtain ⟨L₀, _, _, hab⟩ := hex
      have hP : ∃ R, P l (L l) R := by
        obtain ⟨R', hR'⟩ := hF l hl2 (L l) hmu L₀ hab
        exact ⟨R', ⟨_, L₀, _, _, hab, hR'⟩⟩
      have hRl : Rl l (L l) = Classical.choose hP := by
        show (if h : ∃ R, P l (L l) R then Classical.choose h else 0) = _
        rw [dite_eq_left hP]
      obtain ⟨_, L₀₀, _, _, hab0, hR0⟩ := Classical.choose_spec hP
      obtain ⟨x0, hx0⟩ := partB CK hCKpos hK l (Classical.choose hP) hl2 (L l) hmu L₀₀ hab0 hR0
        J Ct eps A1 hJpos hCt0.le heps
      refine ⟨x0, fun e t hAdm X => ?_⟩
      obtain ⟨Exc, hcard, hx⟩ := hx0 e t hAdm X
      refine ⟨Exc, hRl ▸ hcard, fun x hxx hlo hhi hg _ L₀' _ _ hab' L₁ _ _ _ hlay => ?_⟩
      rw [hRl] at hlay
      exact hx x hxx hlo hhi hg L₀' hab' L₁ hlay
    · refine ⟨0, fun e t _ X => ⟨∅, by simp, ?_⟩⟩
      intro x _ _ _ _ _ L₀' _ _ hab' _ _ _ _ _
      exact absurd ⟨L₀', _, _, hab'⟩ hex
  choose! f hf using hB
  set x1 : ℝ := max 1 (max x0A (∑ l ∈ B', |f l|)) with hx1def
  have hfle : ∀ l ∈ B', f l ≤ x1 := fun l hl =>
    (le_abs_self _).trans ((Finset.single_le_sum (fun i _ => abs_nonneg (f i)) hl).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  have hx0A : x0A ≤ x1 := (le_max_left _ _).trans (le_max_right _ _)
  have hx1pos : 0 ≤ x1 := zero_le_one.trans (le_max_left _ _)
  refine ⟨max 2 (x1 ^ J), fun e t hAdm X hX q d hqd hlog => ?_⟩
  have hX2 : 2 ≤ X := (le_max_left _ _).trans hX
  have hXJ : x1 ^ J ≤ X := (le_max_right _ _).trans hX
  have hlow : x1 ≤ X ^ (1 / J) := by
    calc x1 = (x1 ^ J) ^ (1 / J) := by
          rw [← Real.rpow_mul hx1pos, mul_one_div_cancel hJpos.ne', Real.rpow_one]
      _ ≤ X ^ (1 / J) := Real.rpow_le_rpow (Real.rpow_nonneg hx1pos _) hXJ (by positivity)
  obtain ⟨L₀, _, _, hTB, hAB⟩ := Classical.choose_spec (hT M) q d hqd
  obtain ⟨ExcA, hcardA, hxA⟩ := hA e t hAdm X q d hqd hlog L₀ hTB hAB
  have hB2 := fun l hl => hf l hl e t hAdm X
  choose! g hg using hB2
  have hcard : (ExcA ∪ B'.biUnion g).card ≤ R :=
    (Finset.card_union_le _ _).trans (add_le_add hcardA
      (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun l hl => (hg l hl).1)))
  have heta : 0 < eps / (2 * CK) := by positivity
  have hetaCt : eps / (2 * CK) ≤ Ct := by
    have h1 : eps / (2 * CK) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    linarith
  obtain ⟨Y, hY, hgood⟩ := window R (eps / (2 * CK)) Ct X (ExcA ∪ B'.biUnion g) heta hetaCt
    (by linarith) hcard
  have hJeq : (2 : ℝ) ^ (R + 2) * (Ct / (eps / (2 * CK))) ^ R = J := by
    rw [hJdef, show Ct / (eps / (2 * CK)) = 2 * CK * Ct / eps by rw [div_div_eq_mul_div]; ring]
  rw [hJeq] at hY
  refine ⟨Y, hY, fun x hYx hxY => ?_⟩
  have hG := hgood x hYx hxY
  have hXlo : X ^ (1 / J) ≤ x := hY.1.trans hYx
  have hXhi : x ≤ X := hxY.trans hY.2
  have hGsub : ∀ S ⊆ ExcA ∪ B'.biUnion g, Good (eps / (2 * CK)) Ct S x :=
    fun S hS n hn => hG n (hS hn)
  refine ⟨hxA x (hx0A.trans (hlow.trans hXlo)) hXlo hXhi (hGsub _ Finset.subset_union_left), ?_⟩
  unfold BbAt
  intro l hl _ L₀' _ _ hab L₁ _ _ _ hlay
  exact (hg l hl).2 x ((hfle l hl).trans (hlow.trans hXlo)) hXlo hXhi
    (hGsub _ ((Finset.subset_biUnion_of_mem g hl).trans Finset.subset_union_right)) _ L₀' hab L₁ hlay
end

open Formalism.GaloisCohomology

namespace UpperTheory.V.Win

theorem thmBab_of_lemmaK (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK)
    (hFW : Published.FerreroWashington) (hK : ∃ CK : ℝ, LemmaK CK) : ∃ K : BConst, ∀ Ct : ℝ, 1 ≤ Ct → ThmBab K Ct :=
  have hA : Two.TowerBound := fun l _ L _ _ R h => PropA.aBound_of_isTower hP hF hT l L R h
  thmBab_of hK (Two.fixedIn hFW hA) (Two.twoIn hFW hA)

end UpperTheory.V.Win
