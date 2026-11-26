module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.SignHolds

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ChartLeadingWeightTwo
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

namespace UpperTheory.V.Alg.M

section Comb

variable {τ : Type}

private theorem sp_peel (w : τ → ℕ) (ν : τ →₀ ℕ) (h : Finsupp.weight w ν ≠ 0) :
    ∃ i ν', w i ≠ 0 ∧ ν = Finsupp.single i 1 + ν' := by
  rw [Finsupp.weight_apply, Finsupp.sum] at h
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [smul_eq_mul] at hne
  refine ⟨i, ν - Finsupp.single i 1, right_ne_zero_of_mul hne, ?_⟩
  rw [add_tsub_cancel_of_le]
  rw [Finsupp.single_le_iff]
  exact Nat.one_le_iff_ne_zero.mpr (left_ne_zero_of_mul hne)

private theorem sp_ws (w : τ → ℕ) (i : τ) : Finsupp.weight w (Finsupp.single i 1) = w i := by
  simp [Finsupp.weight_apply, Finsupp.sum_single_index]

private theorem sp_zero (w : τ → ℕ) (hw : ∀ i, w i ≠ 0) (ν : τ →₀ ℕ) (h : Finsupp.weight w ν = 0) : ν = 0 := by
  rw [← Finsupp.support_eq_empty]
  by_contra hne
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_zero_iff] at h
  have h1 := h i hi
  rw [smul_eq_mul, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact (Finsupp.mem_support_iff.mp hi) h1
  · exact hw i h1

private theorem sp_one (w : τ → ℕ) (hw : ∀ i, w i ≠ 0) (ν : τ →₀ ℕ) (h : Finsupp.weight w ν = 1) :
    ∃ i, ν = Finsupp.single i 1 := by
  obtain ⟨i, ν', hi, rfl⟩ := sp_peel w ν (by rw [h]; exact one_ne_zero)
  rw [map_add (f := _), sp_ws] at h
  have h0 : Finsupp.weight w ν' = 0 := by omega
  exact ⟨i, by rw [sp_zero w hw ν' h0, add_zero]⟩

private theorem sp_two (w : τ → ℕ) (hw : ∀ i, w i ≠ 0) (ν : τ →₀ ℕ) (h : Finsupp.weight w ν = 2) :
    (∃ i, ν = Finsupp.single i 1) ∨
      ∃ i k, w i = 1 ∧ w k = 1 ∧ ν = Finsupp.single i 1 + Finsupp.single k 1 := by
  obtain ⟨i, ν', hi, rfl⟩ := sp_peel w ν (by rw [h]; exact two_ne_zero)
  rw [map_add (f := _), sp_ws] at h
  rcases (by omega : w i = 2 ∨ w i = 1) with h2 | h1
  · left
    exact ⟨i, by rw [sp_zero w hw ν' (by omega), add_zero]⟩
  · right
    obtain ⟨k, rfl⟩ := sp_one w hw ν' (by omega)
    rw [sp_ws] at h
    exact ⟨i, k, h1, by omega, rfl⟩

private theorem sp_split (w w' : τ → ℕ) (hw : ∀ i, w i ≤ 2) (hw' : ∀ i, w i ≠ 0 → w' i = 0) (a : ℕ) (ν : τ →₀ ℕ)
    (h : Finsupp.weight w ν = 2 * (a + 1)) :
    ∃ μ ν', ν = μ + ν' ∧ Finsupp.weight w μ = 2 ∧ Finsupp.weight w' μ = 0 := by
  obtain ⟨i, ν1, hi, rfl⟩ := sp_peel w ν (by rw [h]; omega)
  rw [map_add (f := _), sp_ws] at h
  have hi2 := hw i
  rcases (by omega : w i = 2 ∨ w i = 1) with h2 | h1
  · exact ⟨Finsupp.single i 1, ν1, rfl, by rw [sp_ws]; exact h2, by rw [sp_ws]; exact hw' i hi⟩
  · obtain ⟨k, ν2, hk, rfl⟩ := sp_peel w ν1 (by omega)
    rw [map_add (f := _), sp_ws] at h
    have hk2 := hw k
    rcases (by omega : w k = 2 ∨ w k = 1) with h2 | h1'
    · exact ⟨Finsupp.single k 1, Finsupp.single i 1 + ν2, add_left_comm _ _ _, by rw [sp_ws]; exact h2,
        by rw [sp_ws]; exact hw' k hk⟩
    · refine ⟨Finsupp.single i 1 + Finsupp.single k 1, ν2, by rw [add_assoc], ?_, ?_⟩
      · rw [map_add (f := _), sp_ws, sp_ws]
        omega
      · rw [map_add (f := _), sp_ws, sp_ws, hw' i hi, hw' k hk]

private theorem sp_wt (wt : τ → ℤ) (ν : τ →₀ ℕ) :
    Finsupp.weight wt ν = (Finsupp.weight (posW wt) ν : ℕ) - (Finsupp.weight (negW wt) ν : ℕ) ∧
    Finsupp.weight (fun i => (wt i).natAbs) ν = Finsupp.weight (posW wt) ν + Finsupp.weight (negW wt) ν := by
  constructor
  · simp only [Finsupp.weight_apply, Finsupp.sum, posW, negW, smul_eq_mul, nsmul_eq_mul]
    push_cast
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_sub, Int.toNat_sub_toNat_neg]
  · simp only [Finsupp.weight_apply, Finsupp.sum, posW, negW, smul_eq_mul]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_add, Int.toNat_add_toNat_neg_eq_natAbs]

private def Lead {E : Type} [CommRing E] (wt : τ → ℤ) (g : MvPowerSeries τ E) (ν : τ →₀ ℕ) : Prop :=
  g ∈ fil E wt (Finsupp.weight (negW wt) ν) ∧ MvPowerSeries.coeff ν g ≠ 0 ∧
    ∀ ν', Finsupp.weight (negW wt) ν' = Finsupp.weight (negW wt) ν → ν' ≠ ν → MvPowerSeries.coeff ν' g = 0

private theorem Lead.coeff_mul_of_lead_add_and_vanishing {E : Type} [Field E] {wt : τ → ℤ} {g h : MvPowerSeries τ E} {ν μ : τ →₀ ℕ}
    (hg : Lead wt g ν) (hh : Lead wt h μ) :
    MvPowerSeries.coeff (ν + μ) (g * h) = MvPowerSeries.coeff ν g * MvPowerSeries.coeff μ h ∧
      ∀ ν', Finsupp.weight (negW wt) ν' = Finsupp.weight (negW wt) ν + Finsupp.weight (negW wt) μ →
        ν' ≠ ν + μ → MvPowerSeries.coeff ν' (g * h) = 0 := by
  classical
  obtain ⟨hg1, -, hg3⟩ := hg
  obtain ⟨hh1, -, hh3⟩ := hh
  have key : ∀ ν', Finsupp.weight (negW wt) ν' = Finsupp.weight (negW wt) ν + Finsupp.weight (negW wt) μ →
      ∀ p ∈ Finset.HasAntidiagonal.antidiagonal ν', p ≠ (ν, μ) →
        MvPowerSeries.coeff p.1 g * MvPowerSeries.coeff p.2 h = 0 := by
    intro ν' hν' p hp hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hs : Finsupp.weight (negW wt) p.1 + Finsupp.weight (negW wt) p.2 =
        Finsupp.weight (negW wt) ν + Finsupp.weight (negW wt) μ := by
      rw [← map_add (f := _), hp, hν']
    by_cases h1 : Finsupp.weight (negW wt) p.1 < Finsupp.weight (negW wt) ν
    · rw [hg1 p.1 h1, zero_mul]
    by_cases h2 : Finsupp.weight (negW wt) p.2 < Finsupp.weight (negW wt) μ
    · rw [hh1 p.2 h2, mul_zero]
    have e1 : Finsupp.weight (negW wt) p.1 = Finsupp.weight (negW wt) ν := by omega
    have e2 : Finsupp.weight (negW wt) p.2 = Finsupp.weight (negW wt) μ := by omega
    by_cases q1 : p.1 = ν
    · have q2 : p.2 ≠ μ := fun q2 => hne (Prod.ext q1 q2)
      rw [hh3 p.2 e2 q2, mul_zero]
    · rw [hg3 p.1 e1 q1, zero_mul]
  constructor
  · rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single_of_mem (ν, μ)
      (Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl) (key (ν + μ) (map_add _ _ _))]
  · intro ν' hν' hne
    rw [MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => key ν' hν' p hp ?_
    rintro rfl
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    exact hne hp.symm

private theorem Lead.mul {E : Type} [Field E] {wt : τ → ℤ} {g h : MvPowerSeries τ E} {ν μ : τ →₀ ℕ}
    (hg : Lead wt g ν) (hh : Lead wt h μ) : Lead wt (g * h) (ν + μ) := by
  have hc := Lead.coeff_mul_of_lead_add_and_vanishing hg hh
  obtain ⟨hg1, hg2, -⟩ := hg
  obtain ⟨hh1, hh2, -⟩ := hh
  unfold Lead
  refine ⟨?_, ?_, ?_⟩
  · rw [map_add (f := _)]
    exact (fil_holds E τ wt _ _ g h hg1 hh1).1
  · rw [hc.1]
    exact mul_ne_zero hg2 hh2
  · intro ν' hν' hne
    exact hc.2 ν' (by rw [hν', map_add (f := _)]) hne

private theorem Lead.one {E : Type} [Field E] (wt : τ → ℤ) : Lead wt (1 : MvPowerSeries τ E) 0 := by
  classical
  refine ⟨fun ν hν => by simp at hν, by simp, fun ν' _ h => ?_⟩
  rw [MvPowerSeries.coeff_one, if_neg h]

end Comb

section Chart

variable {O A τ : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] {𝒜 : ℤ → Submodule O A}
  [GradedAlgebra 𝒜] {x : A →ₐ[O] O} {wt : τ → ℤ} {φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)}

private theorem finsupp_weight_single_one (w : τ → ℤ) (i : τ) : Finsupp.weight w (Finsupp.single i 1) = w i := by
  simp [Finsupp.weight_apply, Finsupp.sum_single_index]

private theorem sp_comp (H : IsChart0 𝒜 x wt φ) (ν : τ →₀ ℕ) (f : A) :
    MvPowerSeries.coeff ν (φ (DirectSum.decompose 𝒜 f (Finsupp.weight wt ν))) = MvPowerSeries.coeff ν (φ f) := by
  classical
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝒜 f]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.sum_eq_single (Finsupp.weight wt ν)]
  · intro j _ hj
    exact H.graded j _ (SetLike.coe_mem _) ν (Ne.symm hj)
  · intro hnot
    simp only [DFinsupp.mem_support_iff, not_not] at hnot
    rw [hnot]
    simp

private theorem sp_lin (H : IsChart0 𝒜 x wt φ) (i : τ) :
    ∃ f ∈ 𝒜 (wt i), MvPowerSeries.coeff (Finsupp.single i 1) (φ f) ≠ 0 ∧
      ∀ i', i' ≠ i → MvPowerSeries.coeff (Finsupp.single i' 1) (φ f) = 0 := by
  obtain ⟨f, hf1, hf2⟩ := H.onto i
  refine ⟨(DirectSum.decompose 𝒜 f (wt i) : A), SetLike.coe_mem _, ?_, ?_⟩
  · have h1 := sp_comp H (Finsupp.single i 1) f
    rw [finsupp_weight_single_one] at h1
    rw [h1]
    exact hf1
  · intro i' hi'
    by_cases hw : wt i' = wt i
    · have h1 := sp_comp H (Finsupp.single i' 1) f
      rw [finsupp_weight_single_one, hw] at h1
      rw [h1]
      exact hf2 i' hi'
    · exact H.graded (wt i) _ (SetLike.coe_mem _) (Finsupp.single i' 1) (by rw [finsupp_weight_single_one]; exact hw)

omit [GradedAlgebra 𝒜] in
private theorem sp_elim (M : Submodule O A) (ν : τ →₀ ℕ) (S : Finset (τ →₀ ℕ)) (hν : ν ∉ S)
    (hS : ∀ μ ∈ S, Finsupp.weight (negW wt) μ = Finsupp.weight (negW wt) ν → ∃ g ∈ M, Lead wt (φ g) μ) :
    ∀ f ∈ M, MvPowerSeries.coeff ν (φ f) ≠ 0 →
      (∀ ν', Finsupp.weight (negW wt) ν' = Finsupp.weight (negW wt) ν → ν' ≠ ν → ν' ∉ S →
        MvPowerSeries.coeff ν' (φ f) = 0) →
      ∃ f ∈ M, MvPowerSeries.coeff ν (φ f) ≠ 0 ∧
      (∀ ν', Finsupp.weight (negW wt) ν' = Finsupp.weight (negW wt) ν → ν' ≠ ν →
        MvPowerSeries.coeff ν' (φ f) = 0) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro f hf h1 h2
    exact ⟨f, hf, h1, fun ν' e hne => h2 ν' e hne (by simp)⟩
  | @insert μ S hμ ih =>
    intro f hf h1 h2
    have hνS : ν ∉ S := fun h => hν (Finset.mem_insert_of_mem h)
    have hνμ : ν ≠ μ := fun h => hν (h ▸ Finset.mem_insert_self μ S)
    have hS' : ∀ μ' ∈ S, Finsupp.weight (negW wt) μ' = Finsupp.weight (negW wt) ν → ∃ g ∈ M, Lead wt (φ g) μ' :=
      fun μ' hm => hS μ' (Finset.mem_insert_of_mem hm)
    by_cases hl : Finsupp.weight (negW wt) μ = Finsupp.weight (negW wt) ν
    · obtain ⟨g, hg, -, hg2, hg3⟩ := hS μ (Finset.mem_insert_self μ S) hl
      obtain ⟨⟨p, d⟩, hpd⟩ := IsLocalization.surj (nonZeroDivisors O) (MvPowerSeries.coeff μ (φ g))
      obtain ⟨⟨q, e⟩, hqe⟩ := IsLocalization.surj (nonZeroDivisors O) (MvPowerSeries.coeff μ (φ f))
      dsimp only at hpd hqe
      have hc : ∀ n, MvPowerSeries.coeff n (φ ((p * e) • f - (q * d) • g)) =
          algebraMap O (FractionRing O) (p * e) * MvPowerSeries.coeff n (φ f) -
            algebraMap O (FractionRing O) (q * d) * MvPowerSeries.coeff n (φ g) := by
        intro n
        rw [map_sub, map_smul, map_smul, map_sub, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower,
          Algebra.smul_def, Algebra.smul_def]
      have hd : algebraMap O (FractionRing O) d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
      have he : algebraMap O (FractionRing O) e ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors e.2
      have hp : algebraMap O (FractionRing O) p ≠ 0 := by
        rw [← hpd]
        exact mul_ne_zero hg2 hd
      apply ih hνS hS' _ (M.sub_mem (M.smul_mem _ hf) (M.smul_mem _ hg))
      · rw [hc, hg3 ν hl.symm hνμ, mul_zero, sub_zero, map_mul]
        exact mul_ne_zero (mul_ne_zero hp he) h1
      · intro ν' e' hne hnS
        by_cases hm : ν' = μ
        · subst hm
          rw [hc, map_mul, map_mul, ← hpd, ← hqe]
          ring
        · rw [hc, h2 ν' e' hne (by simp [hm, hnS]), hg3 ν' (e'.trans hl.symm) hm]
          ring
    · apply ih hνS hS' f hf h1
      intro ν' e' hne hnS
      apply h2 ν' e' hne
      intro hmem
      rcases Finset.mem_insert.mp hmem with rfl | h
      · exact hl e'
      · exact hnS h

omit [GradedAlgebra 𝒜] in
private theorem sp_fil (H : IsChart0 𝒜 x wt φ) (i : τ) (f : A) (hf : f ∈ 𝒜 (wt i)) :
    φ f ∈ fil (FractionRing O) wt (Finsupp.weight (negW wt) (Finsupp.single i 1)) := by
  have h0 : φ f ∈ fil (FractionRing O) wt 0 := fun ν hν => absurd hν (Nat.not_lt_zero _)
  have h1 := (fil_holds (FractionRing O) τ wt 0 0 (φ f) 0 h0 (Submodule.zero_mem _)).2 (wt i) (H.graded (wt i) f hf)
  rw [sp_ws]
  exact h1

omit [GradedAlgebra 𝒜] in
private theorem sp_abs (H : IsChart0 𝒜 x wt φ) (i : τ) : (wt i).natAbs ≠ 0 := by
  rcases H.wts i with h | h | h | h <;> rw [h] <;> decide

private theorem chart_leading_weight_one (H : IsChart0 𝒜 x wt φ) (i : τ) (hi : (wt i).natAbs = 1) :
    ∃ f ∈ 𝒜 (wt i), Lead wt (φ f) (Finsupp.single i 1) := by
  obtain ⟨f, hf, h1, h2⟩ := sp_lin H i
  refine ⟨f, hf, sp_fil H i f hf, h1, fun ν' a b => ?_⟩
  by_cases hw : Finsupp.weight wt ν' = wt i
  · have := sp_wt wt ν'
    rw [sp_ws, negW] at a
    obtain ⟨k, rfl⟩ := sp_one _ (sp_abs H) ν' (by omega)
    exact h2 k fun h => b (by rw [h])
  · exact H.graded _ _ hf _ hw

private theorem chart_leading_weight_sum (H : IsChart0 𝒜 x wt φ) (i k : τ) (hi : (wt i).natAbs = 1) (hk : (wt k).natAbs = 1) :
    ∃ f ∈ 𝒜 (wt i + wt k), Lead wt (φ f) (Finsupp.single i 1 + Finsupp.single k 1) := by
  obtain ⟨f, hf, hfl⟩ := chart_leading_weight_one H i hi
  obtain ⟨g, hg, hgl⟩ := chart_leading_weight_one H k hk
  refine ⟨f * g, SetLike.mul_mem_graded hf hg, ?_⟩
  rw [map_mul]
  exact Lead.mul hfl hgl

private theorem chart_leading_weight_two [Fintype τ] (H : IsChart0 𝒜 x wt φ) (i : τ) (hi : (wt i).natAbs = 2) :
    ∃ f ∈ 𝒜 (wt i), Lead wt (φ f) (Finsupp.single i 1) := by
  classical
  obtain ⟨f, hf, hf1, hf2⟩ := sp_lin H i
  let S : Finset (τ →₀ ℕ) := ((Finset.univ ×ˢ Finset.univ).filter (fun kl : τ × τ =>
      (wt kl.1).natAbs = 1 ∧ (wt kl.2).natAbs = 1 ∧ wt kl.1 + wt kl.2 = wt i)).image
      (fun kl => Finsupp.single kl.1 1 + Finsupp.single kl.2 1)
  have hnS : Finsupp.single i 1 ∉ S := by
    intro hmem
    obtain ⟨⟨k, l⟩, -, heq⟩ := Finset.mem_image.mp hmem
    have h3 := congrArg (Finsupp.weight (fun _ : τ => (1 : ℕ))) heq
    simp [sp_ws] at h3
  obtain ⟨f', hf', hf'1, hf'2⟩ := sp_elim (wt := wt) (φ := φ) (𝒜 (wt i)) (Finsupp.single i 1) S hnS (by
      intro μ hμ _
      obtain ⟨⟨k, l⟩, hkl, rfl⟩ := Finset.mem_image.mp hμ
      obtain ⟨-, hk, hl, hsum⟩ := Finset.mem_filter.mp hkl
      obtain ⟨g, hg, hgl⟩ := chart_leading_weight_sum H k l hk hl
      exact ⟨g, hsum ▸ hg, hgl⟩) f hf hf1 (by
      intro ν' e hne hnot
      by_cases hw : Finsupp.weight wt ν' = wt i
      · have hwt := sp_wt wt ν'
        rw [sp_ws] at e
        have hn : Finsupp.weight (negW wt) ν' = (-wt i).toNat := e
        have hsgn : wt i = 2 ∨ wt i = -2 := by
          rcases Int.natAbs_eq (wt i) with h | h <;> rw [hi] at h <;> simp [h]
        have hw' := hw
        rw [hwt.1] at hw'
        rcases sp_two (fun k => (wt k).natAbs) (sp_abs H) ν' (by
          rw [hwt.2]
          rcases hsgn with h | h <;> rw [h] at hn hw' <;>
            simp only [show (-(2:ℤ)).toNat = 0 from rfl, show (-(-2:ℤ)).toNat = 2 from rfl] at hn <;> omega)
          with ⟨k, rfl⟩ | ⟨k, l, hk, hl, rfl⟩
        · exact hf2 k (fun h => hne (by rw [h]))
        · exfalso
          apply hnot
          rw [map_add (f := _), finsupp_weight_single_one, finsupp_weight_single_one] at hw
          exact Finset.mem_image.mpr ⟨(k, l), Finset.mem_filter.mpr ⟨by simp, hk, hl, hw⟩, rfl⟩
      · exact H.graded (wt i) f hf ν' hw)
  refine ⟨f', hf', ?_⟩
  unfold Lead
  exact ⟨sp_fil H i f' hf', hf'1, hf'2⟩

private theorem sp_l [Fintype τ] (H : IsChart0 𝒜 x wt φ) (μ : τ →₀ ℕ) (j : ℤ) (hj : j.natAbs = 2)
    (h1 : Finsupp.weight (negW wt) μ = (-j).toNat) (h2 : Finsupp.weight (posW wt) μ = j.toNat) :
    ∃ f ∈ 𝒜 j, Lead wt (φ f) μ := by
  have hwt := sp_wt wt μ
  have hj' : j = 2 ∨ j = -2 := by
    rcases Int.natAbs_eq j with h | h <;> rw [hj] at h <;> simp [h]
  have habs : Finsupp.weight (fun k => (wt k).natAbs) μ = 2 := by
    rw [hwt.2, h1, h2]
    rcases hj' with h | h <;> subst h <;> decide
  have hwj : Finsupp.weight wt μ = j := by
    rw [hwt.1, h1, h2]
    rcases hj' with h | h <;> subst h <;> decide
  rcases sp_two (fun k => (wt k).natAbs) (sp_abs H) μ habs with ⟨k, rfl⟩ | ⟨k, l, hk, hl, rfl⟩
  · rw [finsupp_weight_single_one] at hwj
    obtain ⟨f, hf, hfl⟩ := chart_leading_weight_two H k (by rw [hwj]; exact hj)
    exact ⟨f, hwj ▸ hf, hfl⟩
  · rw [map_add (f := _), finsupp_weight_single_one, finsupp_weight_single_one] at hwj
    obtain ⟨f, hf, hfl⟩ := chart_leading_weight_sum H k l hk hl
    exact ⟨f, hwj ▸ hf, hfl⟩

private theorem posW_negW_le_two_and_disjoint_of_isChart0 (H : IsChart0 𝒜 x wt φ) (k : τ) :
    posW wt k ≤ 2 ∧ negW wt k ≤ 2 ∧ (negW wt k ≠ 0 → posW wt k = 0) ∧ (posW wt k ≠ 0 → negW wt k = 0) := by
  unfold posW negW
  rcases H.wts k with h | h | h | h <;> rw [h] <;> decide

private theorem sp_main [Fintype τ] (H : IsChart0 𝒜 x wt φ) (a b : ℕ) :
    ∀ ν : τ →₀ ℕ, Finsupp.weight (negW wt) ν = 2 * a → Finsupp.weight (posW wt) ν = 2 * b →
      ∃ f ∈ oz 𝒜 (-2) ^ a * oz 𝒜 2 ^ b, Lead wt (φ f) ν := by
  intro ν hn hp
  induction a generalizing ν with
  | zero =>
    induction b generalizing ν with
    | zero =>
      have h0 : ν = 0 := sp_zero (fun k => (wt k).natAbs) (sp_abs H) ν (by rw [(sp_wt wt ν).2, hn, hp])
      subst h0
      refine ⟨1, ?_, ?_⟩
      · simp only [pow_zero, mul_one]
        exact Submodule.mem_one.mpr ⟨1, map_one _⟩
      · rw [map_one]
        exact Lead.one wt
    | succ b ih =>
      obtain ⟨μ, ν', rfl, hμ1, hμ2⟩ := sp_split (posW wt) (negW wt) (fun k => (posW_negW_le_two_and_disjoint_of_isChart0 H k).1)
        (fun k hk => (posW_negW_le_two_and_disjoint_of_isChart0 H k).2.2.2 hk) b ν hp
      rw [map_add (f := _)] at hn hp
      obtain ⟨g, hg, hgl⟩ := ih ν' (by omega) (by omega)
      obtain ⟨f1, hf1, hf1l⟩ := sp_l H μ 2 rfl (by rw [hμ2]; rfl) (by rw [hμ1]; rfl)
      refine ⟨f1 * g, ?_, ?_⟩
      · rw [pow_succ', mul_left_comm]
        exact Submodule.mul_mem_mul (show f1 ∈ oz 𝒜 2 from hf1) hg
      · rw [map_mul]
        exact Lead.mul hf1l hgl
  | succ a ih =>
    obtain ⟨μ, ν', rfl, hμ1, hμ2⟩ := sp_split (negW wt) (posW wt) (fun k => (posW_negW_le_two_and_disjoint_of_isChart0 H k).2.1)
      (fun k hk => (posW_negW_le_two_and_disjoint_of_isChart0 H k).2.2.1 hk) a ν hn
    rw [map_add (f := _)] at hn hp
    obtain ⟨g, hg, hgl⟩ := ih ν' (by omega) (by omega)
    obtain ⟨f1, hf1, hf1l⟩ := sp_l H μ (-2) rfl (by rw [hμ1]; rfl) (by rw [hμ2]; rfl)
    refine ⟨f1 * g, ?_, ?_⟩
    · rw [pow_succ', mul_assoc]
      exact Submodule.mul_mem_mul (show f1 ∈ oz 𝒜 (-2) from hf1) hg
    · rw [map_mul]
      exact Lead.mul hf1l hgl

end Chart

end UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.exists_mem_oz_pow_coeff_ne_zero_unique :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (τ : Type) [Fintype τ] (wt : τ → ℤ) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart0 𝒜 x wt φ →
    ∀ (a b : ℕ) (ν : τ →₀ ℕ), Finsupp.weight (negW wt) ν = 2 * a → Finsupp.weight (posW wt) ν = 2 * b →
      ∃ f ∈ oz 𝒜 (-2) ^ a * oz 𝒜 2 ^ b, MvPowerSeries.coeff ν (φ f) ≠ 0 ∧
        ∀ ν', Finsupp.weight (negW wt) ν' = 2 * a → ν' ≠ ν → MvPowerSeries.coeff ν' (φ f) = 0 := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x _ τ _ wt φ H a b ν h1 h2
  obtain ⟨f, hf, hfl⟩ := UpperTheory.V.Alg.M.sp_main H a b ν h1 h2
  obtain ⟨-, hc, hz⟩ := hfl
  exact ⟨f, hf, hc, fun ν' e hne => hz ν' (e.trans h1.symm) hne⟩
end

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem length_localization_bound {O B L P I : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing B]
    [Algebra O B] (x : B →ₐ[O] O) [AddCommGroup L] [Module B L] [Module O L] [IsScalarTower O B L]
    [Module.Finite B L] [AddCommGroup P] [Module B P] [Finite I] (lc : L →ₗ[O] (I → FractionRing O))
    (hlc : ∀ (b : B) (f : L), lc (b • f) = x b • lc f)
    (hsp : ∀ i, ∃ f, lc f i ≠ 0 ∧ ∀ j, j ≠ i → lc f j = 0)
    (ϖ : O) (hϖ : Irreducible ϖ) (π : L →ₗ[B] P) (hπ : Function.Surjective π)
    (hk : ∀ f, π f = 0 ↔ ∃ g, lc f = ϖ • lc g) : Module.length B P = Nat.card I := by
  classical
  have := Fintype.ofFinite I
  have hfin : Module.Finite O (LinearMap.range lc) := by
    obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := B) (M := L)
    rw [Module.Finite.iff_fg]
    refine ⟨S.image lc, le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le, Finset.coe_image]
      rintro _ ⟨f, -, rfl⟩
      exact ⟨f, rfl⟩
    · rintro _ ⟨f, rfl⟩
      have hf : f ∈ Submodule.span B (S : Set L) := hS ▸ Submodule.mem_top
      induction hf using Submodule.span_induction with
      | mem f hf => exact Submodule.subset_span (by rw [Finset.coe_image]; exact ⟨f, hf, rfl⟩)
      | zero => rw [map_zero]; exact zero_mem _
      | add f g _ _ hf hg => rw [map_add]; exact add_mem hf hg
      | smul b f _ hf => rw [hlc]; exact Submodule.smul_mem _ _ hf
  have hfree : Module.Free O (LinearMap.range lc) := inferInstance
  have hrk : Module.finrank O (LinearMap.range lc) = Fintype.card I := by
    apply le_antisymm
    · have h1 : Module.rank O (LinearMap.range lc) ≤ Module.rank O (I → FractionRing O) := Submodule.rank_le _
      rw [← IsLocalization.rank_eq (FractionRing O) (nonZeroDivisors O) le_rfl (N := I → FractionRing O),
        rank_fun'] at h1
      exact Module.finrank_le_of_rank_le h1
    · choose f hf hf' using hsp
      have h2 : LinearIndependent O fun i => lc.rangeRestrict (f i) := by
        rw [Fintype.linearIndependent_iff]
        intro c hc i
        have h3 := congrArg (fun z : LinearMap.range lc => z.1 i) hc
        simp only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, SetLike.val_smul, Pi.smul_apply,
          LinearMap.codRestrict_apply, LinearMap.rangeRestrict, ZeroMemClass.coe_zero, Pi.zero_apply] at h3
        rw [Finset.sum_eq_single i (fun j _ hj => by rw [hf' j i (Ne.symm hj), smul_zero]) (by simp)] at h3
        exact (smul_eq_zero.1 h3).resolve_right (hf i)
      exact h2.fintype_card_le_finrank
  let e : LinearMap.range lc ≃ₗ[O] (I → O) := LinearEquiv.ofFinrankEq _ _ (by rw [hrk, Module.finrank_fintype_fun_eq_card])
  let ρ : L →ₗ[O] (I → O ⧸ Ideal.span {ϖ}) :=
    ((Ideal.span {ϖ}).mkQ.compLeft I) ∘ₗ e.toLinearMap ∘ₗ lc.rangeRestrict
  have hρ : Function.Surjective ρ := by
    intro y
    choose z hz using fun i => Submodule.mkQ_surjective (Ideal.span {ϖ}) (y i)
    obtain ⟨f, hf⟩ := lc.surjective_rangeRestrict (e.symm z)
    refine ⟨f, funext fun i => ?_⟩
    show (Ideal.span {ϖ}).mkQ (e (lc.rangeRestrict f) i) = y i
    rw [hf, e.apply_symm_apply, hz]
  have hρk : ∀ f, ρ f = 0 ↔ ∃ g, lc f = ϖ • lc g := by
    intro f
    constructor
    · intro h
      have h1 : ∀ i, ∃ c, c * ϖ = e (lc.rangeRestrict f) i := fun i =>
        Ideal.mem_span_singleton'.1 ((Submodule.Quotient.mk_eq_zero _).1 (congrFun h i))
      choose c hc using h1
      obtain ⟨g, hg⟩ := lc.surjective_rangeRestrict (e.symm c)
      refine ⟨g, ?_⟩
      have h2 : lc.rangeRestrict f = ϖ • lc.rangeRestrict g := by
        apply e.injective
        rw [map_smul, hg, e.apply_symm_apply]
        funext i
        rw [← hc, Pi.smul_apply, smul_eq_mul, mul_comm]
      exact congrArg Subtype.val h2
    · rintro ⟨g, hg⟩
      have h2 : lc.rangeRestrict f = ϖ • lc.rangeRestrict g := Subtype.ext hg
      funext i
      show (Ideal.span {ϖ}).mkQ (e (lc.rangeRestrict f) i) = 0
      rw [h2, map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ϖ)
  letI : Module O P := Module.compHom P (algebraMap O B)
  haveI : IsScalarTower O B P := ⟨fun a b p => by
    show _ = algebraMap O B a • b • p
    rw [Algebra.smul_def, mul_smul]⟩
  have hact : ∀ (b : B) (p : P), b • p = x b • p := by
    intro b p
    obtain ⟨f, rfl⟩ := hπ p
    show _ = algebraMap O B (x b) • π f
    rw [← sub_eq_zero, ← map_smul, ← map_smul, ← map_sub, hk]
    exact ⟨0, by rw [map_sub, hlc, hlc, AlgHom.commutes, map_zero, smul_zero]; exact sub_self _⟩
  have h1 : Module.length B P = Module.length O P := by
    letI : Algebra B O := x.toRingHom.toAlgebra
    haveI : IsScalarTower B O P := ⟨fun b a p => by
      rw [hact]
      exact mul_smul (x b) a p⟩
    exact Module.length_eq_of_surjective fun a => ⟨algebraMap O B a, x.commutes a⟩
  have hker : LinearMap.ker (π.restrictScalars O) = LinearMap.ker ρ := by
    ext f
    exact (hk f).trans (hρk f).symm
  have e2 : P ≃ₗ[O] (I → O ⧸ Ideal.span {ϖ}) :=
    (((π.restrictScalars O).quotKerEquivOfSurjective hπ).symm.trans (Submodule.quotEquivOfEq _ _ hker)).trans
      (ρ.quotKerEquivOfSurjective hρ)
  haveI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  haveI : IsSimpleModule O (O ⧸ Ideal.span {ϖ}) := isSimpleModule_iff_isCoatom.2 (Ideal.isMaximal_def.1 inferInstance)
  rw [h1, e2.length_eq, Module.length_pi_of_fintype]
  simp [Module.length_eq_one]

private theorem weight_eq {τ : Type} (wt : τ → ℤ) (ν : τ →₀ ℕ) :
    Finsupp.weight wt ν = (Finsupp.weight (posW wt) ν : ℤ) - (Finsupp.weight (negW wt) ν : ℤ) := by
  simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, Nat.cast_sum, Nat.cast_mul, ← Finset.sum_sub_distrib,
    nsmul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_sub, posW, negW, Int.toNat_sub_toNat_neg]

private theorem pullback_fin_relation {τ : Type} [Fintype τ] (wt : τ → ℤ) (h : ∀ i, wt i ≠ 0) (a b : ℕ) :
    Finite {ν : τ →₀ ℕ // Finsupp.weight (negW wt) ν = a ∧ Finsupp.weight (posW wt) ν = b} := by
  have h1 := Finsupp.finite_of_nat_weight_le (fun i => negW wt i + posW wt i)
    (fun i => by have := h i; simp only [negW, posW]; omega) (a + b)
  refine Set.Finite.to_subtype (s := {ν | Finsupp.weight (negW wt) ν = a ∧ Finsupp.weight (posW wt) ν = b})
    (h1.subset ?_)
  rintro ν ⟨h2, h3⟩
  show Finsupp.weight (fun i => negW wt i + posW wt i) ν ≤ a + b
  rw [← h2, ← h3]
  simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, mul_add, Finset.sum_add_distrib, le_refl]

private noncomputable def monoL {B A : Type} [CommRing B] [CommRing A] [Algebra B A] {k : ℕ}
    (N : Fin k → Submodule B A) (m : Fin k →₀ ℕ) : lat N m →ₗ[B] rees N where
  toFun f := mono N m f.1 f.2
  map_add' f g := Subtype.ext (by
    show MvPolynomial.monomial m (f.1 + g.1) = MvPolynomial.monomial m f.1 + MvPolynomial.monomial m g.1
    rw [map_add (f := _)])
  map_smul' c f := Subtype.ext (by
    show MvPolynomial.monomial m (c • f.1) = c • MvPolynomial.monomial m f.1
    rw [MvPolynomial.smul_monomial])

private theorem gr_eq_range {B A : Type} [CommRing B] [CommRing A] [Algebra B A] {k : ℕ}
    (N : Fin k → Submodule B A) (m : Fin k →₀ ℕ) : reesGr N (toDeg m) = LinearMap.range (monoL N m) := by
  classical
  apply le_antisymm
  · intro p hp
    refine ⟨⟨_, p.2 m⟩, Subtype.ext ?_⟩
    ext n
    show AddMonoidAlgebra.coeff (MvPolynomial.monomial m _) n = _
    rw [MvPolynomial.coeff_monomial]
    split_ifs with h
    · rw [← h]
    · exact (hp n fun h' => h (toDeg_injective h').symm).symm
  · rintro _ ⟨f, rfl⟩
    exact mono_mem N m f.1 f.2

private theorem piece_gen {B R L : Type} [CommRing B] [CommRing R] [Algebra B R] [AddCommGroup L] [Module B L]
    {k : ℕ} (𝒢 : Deg k → Submodule B R) (d : Deg k) (ι : L →ₗ[B] R) (hι : 𝒢 d = LinearMap.range ι) (𝔮 : Ideal R)
    (β : B) : ∃ π : L →ₗ[B] ((((GMod.self 𝒢).quo 𝔮).quot (algebraMap B R β)).gr d),
      Function.Surjective π ∧ ∀ f, π f = 0 ↔ ∃ p : R, ι f - β • p ∈ 𝔮 := by
  let M := LinearMap.range (LinearMap.lsmul R (R ⧸ 𝔮) (algebraMap B R β))
  let π0 : L →ₗ[B] (R ⧸ 𝔮) ⧸ M := M.mkQ.restrictScalars B ∘ₗ (Submodule.mkQ 𝔮).restrictScalars B ∘ₗ ι
  have hgr : (((GMod.self 𝒢).quo 𝔮).quot (algebraMap B R β)).gr d = LinearMap.range π0 := by
    rw [LinearMap.range_comp, LinearMap.range_comp, ← hι]
    rfl
  refine ⟨π0.codRestrict _ fun f => hgr ▸ LinearMap.mem_range_self π0 f, fun y => ?_, fun f => ?_⟩
  · obtain ⟨f, hf⟩ : y.1 ∈ LinearMap.range π0 := hgr ▸ y.2
    exact ⟨f, Subtype.ext hf⟩
  · rw [Subtype.ext_iff]
    show M.mkQ (Submodule.mkQ 𝔮 (ι f)) = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective 𝔮 y
      rw [LinearMap.lsmul_apply, ← map_smul, algebraMap_smul, eq_comm, Submodule.mkQ_apply, Submodule.mkQ_apply,
        Submodule.Quotient.eq] at hy
      exact ⟨p, hy⟩
    · rintro ⟨p, hp⟩
      refine ⟨Submodule.mkQ 𝔮 p, ?_⟩
      rwa [LinearMap.lsmul_apply, ← map_smul, algebraMap_smul, eq_comm, Submodule.mkQ_apply, Submodule.mkQ_apply,
        Submodule.Quotient.eq]

private theorem rees_graded_piece_surjection {B A : Type} [CommRing B] [CommRing A] [Algebra B A] {k : ℕ}
    (N : Fin k → Submodule B A) (μ : Fin k →₀ ℕ) (𝔮 : Ideal (rees N)) (β : B) (T : (Fin k →₀ ℕ) → AddSubgroup A)
    (hq : ∀ p, p ∈ 𝔮 ↔ ∀ m, AddMonoidAlgebra.coeff p.1 m ∈ T m) :
    ∃ π : lat N μ →ₗ[B] ((((GMod.self (reesGr N)).quo 𝔮).quot (algebraMap B (rees N) β)).gr (toDeg μ)),
      Function.Surjective π ∧ ∀ f, π f = 0 ↔ ∃ g : lat N μ, (f - β • g).1 ∈ T μ := by
  classical
  obtain ⟨π, hπ, hk⟩ := piece_gen (reesGr N) (toDeg μ) (monoL N μ) (gr_eq_range N μ) 𝔮 β
  refine ⟨π, hπ, fun f => (hk f).trans ⟨?_, ?_⟩⟩
  · rintro ⟨p, hp⟩
    refine ⟨⟨_, p.2 μ⟩, ?_⟩
    have h1 : AddMonoidAlgebra.coeff (MvPolynomial.monomial μ f.1 - β • p.1) μ ∈ T μ := (hq _).1 hp μ
    rwa [MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial, if_pos rfl, MvPolynomial.coeff_smul] at h1
  · rintro ⟨g, hg⟩
    refine ⟨monoL N μ g, ?_⟩
    rw [← map_smul, ← map_sub, hq]
    intro m
    show AddMonoidAlgebra.coeff (MvPolynomial.monomial μ (f - β • g).1) m ∈ _
    rw [MvPolynomial.coeff_monomial]
    split_ifs with h
    · exact h ▸ hg
    · exact zero_mem _

theorem UpperTheory.V.Alg.M.hf_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    ∀ (τ : Type) [Fintype τ] (wt : τ → ℤ) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart0 𝒜 x wt φ →
    Q.F (Fin.last r) ∈ satSq x → ∀ 𝔮 : Ideal (mR Q), (𝔮 : Set (mR Q)) = leadKer Q wt φ → ∀ ϖ : O, Irreducible ϖ →
      ∀ d : Deg 3, 0 ≤ d → hilb ((mQ Q 𝔮).quot (algebraMap (𝒜 0) (mR Q) (algebraMap O (𝒜 0) ϖ))) d =
        cnt wt (2 * d 0 + 4 * d 2) (2 * d 1 + 2 * d 2) := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hW r s r' s' m Q τ _ wt φ hφ hF 𝔮 h𝔮 ϖ hϖ d hd
  classical
  obtain ⟨μ, rfl⟩ : ∃ μ : Fin 3 →₀ ℕ, toDeg μ = d :=
    ⟨Finsupp.equivFunOnFinite.symm fun j => (d j).toNat, funext fun j => by simpa [toDeg] using hd j⟩
  set F := Q.F (Fin.last r) with hFd
  obtain ⟨π, hπ, hk⟩ := rees_graded_piece_surjection (mN 𝒜 F) μ 𝔮 (algebraMap O (𝒜 0) ϖ)
    (fun ν => ((fil (FractionRing O) wt (2 * ν 0 + 4 * ν 2 + 1)).toAddSubgroup).comap φ.toRingHom.toAddMonoidHom)
    (fun p => by rw [← SetLike.mem_coe, h𝔮]; rfl)
  let I := {ν : τ →₀ ℕ // Finsupp.weight (negW wt) ν = 2 * μ 0 + 4 * μ 2 ∧ Finsupp.weight (posW wt) ν = 2 * μ 1 + 2 * μ 2}
  haveI : Finite I := pullback_fin_relation wt (fun i => by have := hφ.wts i; omega) _ _
  let lc : lat (mN 𝒜 F) μ →ₗ[O] (I → FractionRing O) :=
    { toFun := fun f ν => MvPowerSeries.coeff ν.1 (φ f.1)
      map_add' := fun f g => funext fun ν => by simp
      map_smul' := fun c f => funext fun ν => by
        show MvPowerSeries.coeff ν.1 (φ (c • f.1)) = c • MvPowerSeries.coeff ν.1 (φ f.1)
        rw [map_smul, LinearMap.map_smul_of_tower] }
  have hlat := latfil_holds O A 𝒜 x hW τ wt φ hφ F (Q.hF _) hF μ
  have hz : ∀ f : lat (mN 𝒜 F) μ, φ f.1 ∈ fil (FractionRing O) wt (2 * μ 0 + 4 * μ 2 + 1) ↔ lc f = 0 := by
    intro f
    refine ⟨fun h => funext fun ν => h ν.1 (by rw [ν.2.1]; omega), fun h ν hν => ?_⟩
    obtain ⟨h1, h2⟩ := hlat f.1 f.2
    by_cases h3 : Finsupp.weight (negW wt) ν < 2 * μ 0 + 4 * μ 2
    · exact h2 ν h3
    by_cases h4 : Finsupp.weight (posW wt) ν = 2 * μ 1 + 2 * μ 2
    · exact congrFun h ⟨ν, by omega, h4⟩
    · exact hφ.graded _ _ h1 ν (by rw [weight_eq]; omega)
  have hfg : ∀ i, (mN 𝒜 F i).FG := by
    have h := fg_holds O A 𝒜 x hW
    intro i
    fin_cases i
    · exact h _
    · exact h _
    · exact (Submodule.fg_span_singleton _).sup (((h _).mul (h _)).mul (h _))
  have hl : lat (mN 𝒜 F) μ = mN 𝒜 F 0 ^ μ 0 * mN 𝒜 F 1 ^ μ 1 * mN 𝒜 F 2 ^ μ 2 := Fin.prod_univ_three _
  haveI : Module.Finite (𝒜 0) (lat (mN 𝒜 F) μ) := by
    rw [Module.Finite.iff_fg, hl]
    exact (((hfg _).pow _).mul ((hfg _).pow _)).mul ((hfg _).pow _)
  have key := length_localization_bound (res0 𝒜 x) lc (fun b f => ?_) (fun i => ?_) ϖ hϖ π hπ (fun f => ?_)
  · show ((Module.length _ _).toNat : ℤ) = (Nat.card _ : ℕ)
    rw [key, ENat.toNat_coe]
    congr 1
    refine Nat.card_congr (Equiv.subtypeEquivRight fun ν => ?_)
    simp only [toDeg]
    omega
  · rw [← sub_eq_zero, ← map_smul, ← map_sub, ← hz, ← algebraMap_smul (𝒜 0) (res0 𝒜 x b) f, ← sub_smul]
    show φ (((b - algebraMap O (𝒜 0) (res0 𝒜 x b) : 𝒜 0) : A) * f.1) ∈ _
    rw [map_mul, add_comm _ 1]
    refine (fil_holds _ _ wt _ _ _ _ ((satfil_holds O A 𝒜 x hW τ wt φ hφ).2 _ (Subtype.property _) ?_)
      (hlat f.1 f.2).2).1
    show res0 𝒜 x (b - algebraMap O (𝒜 0) (res0 𝒜 x b)) = 0
    rw [map_sub, AlgHom.commutes]
    exact sub_self _
  · obtain ⟨f, hf, h1, h2⟩ := exists_mem_oz_pow_coeff_ne_zero_unique O A 𝒜 x hW τ wt φ hφ (μ 0 + 2 * μ 2) (μ 1 + μ 2) i.1 (by rw [i.2.1]; ring)
      (by rw [i.2.2]; ring)
    have hle : oz 𝒜 (-2) ^ (μ 0 + 2 * μ 2) * oz 𝒜 2 ^ (μ 1 + μ 2) ≤ lat (mN 𝒜 F) μ := by
      have h3 : oz 𝒜 (-2) ^ (μ 0 + 2 * μ 2) * oz 𝒜 2 ^ (μ 1 + μ 2) =
          oz 𝒜 (-2) ^ μ 0 * oz 𝒜 2 ^ μ 1 * (oz 𝒜 (-2) * oz 𝒜 (-2) * oz 𝒜 2) ^ μ 2 := by ring
      rw [h3, hl]
      exact mul_le_mul' le_rfl (pow_le_pow_left' (le_sup_right : _ ≤ mN 𝒜 F 2) _)
    exact ⟨⟨f, hle hf⟩, h1, fun j hj => h2 j.1 (by rw [j.2.1]; ring) fun h => hj (Subtype.ext h)⟩
  · rw [hk]
    refine exists_congr fun g => ?_
    rw [← sub_eq_zero, ← map_smul, ← map_sub, ← hz, algebraMap_smul]
    rfl
