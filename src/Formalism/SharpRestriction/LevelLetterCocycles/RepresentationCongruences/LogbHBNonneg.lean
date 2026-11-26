module

public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcPropositionAlternative
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthBoundTheorem
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcStructuresThreeHold

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.JumpsOfSurjectiveLatticeMap
noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Module

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 in
theorem jumps_of_surjective_lattice_map : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (hJ : UsedJ D HW F) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL),
    (∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (f : LatHom T₁.L T₂.L),
      Formalism.MainNotions.LiftingTheory.Sur ((HW l).W K 1 LL hG) f →
      ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), IsJumpV ((D.loc l).PD K) T₂.ρ τ a →
        IsJumpV ((D.loc l).PD K) T₁.ρ τ a) ∧
    (∀ (T₂ Y : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T₂.L Y.L)
      (π : LatHom Y.L ((HW l).W K 1 LL hG).one.L) (cc : ↥(GK K) → T₂.V),
      cc ∈ latticeCocycles T₂.L → IsCrys ((D.loc l).PD K) T₂.ρ → IsCrys ((D.loc l).PD K) Y.ρ →
      Formalism.MainNotions.LiftingTheory.IsExtOf ((HW l).W K 1 LL hG) ι π cc →
      ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), IsJumpV ((D.loc l).PD K) Y.ρ τ a →
        a = 0 ∨ IsJumpV ((D.loc l).PD K) T₂.ρ τ a) := by
  intro D HW F hJ l _ K LL hG
  refine ⟨?_, ?_⟩
  · intro T₁ T₂ f hS τ a ha
    obtain ⟨c1, c2, hO⟩ := hS
    obtain ⟨T₀, ι, hses, c0⟩ := Formalism.MainNotions.LiftingTheory.lker_HKer_D D HW F hJ.a22 l K 1 LL hG T₁ T₂ f ⟨c1, c2, hO⟩
    exact (hJ.a23 l K LL T₀ T₁ T₂ ι f hses c0 c1 c2 τ a).2 (Or.inr ha)
  · intro T₂ Y ι π cc _ c2 cY hext τ a ha
    obtain ⟨cone, hone0⟩ := Formalism.MainNotions.LiftingTheory.lone_HOne0_holds D HW F l K 1 LL hG
    rcases (hJ.a23 l K LL T₂ Y _ ι π hext.1 c2 cY cone τ a).1 ha with h | h
    · exact Or.inr h
    · exact Or.inl (hone0 τ a h)

end Formalism.MainNotions.N.Ln17
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.SumPadicValIntWindowLe
noncomputable section

open Classical Finset

namespace Formalism.MainNotions.N.Ln17

theorem padicValNat_eq_card_dvd_pows (l : ℕ) (hl : 2 ≤ l) (N b : ℕ) (hN : N ≠ 0) (hb : N < l ^ b) :
    padicValNat l N = ((Ico 1 b).filter (fun i => l ^ i ∣ N)).card := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero hN
  have key : ∀ i, l ^ i ∣ N ↔ i ≤ padicValNat l N := by
    intro i
    have hfin : FiniteMultiplicity l N := Nat.finiteMultiplicity_iff.2 ⟨by omega, hN0⟩
    rw [padicValNat_def']
    exact hfin.pow_dvd_iff_le_multiplicity
  have hv : padicValNat l N < b := by
    have h1 : l ^ padicValNat l N ≤ N := Nat.le_of_dvd hN0 ((key _).2 le_rfl)
    by_contra hc
    push_neg at hc
    have : l ^ b ≤ l ^ padicValNat l N := Nat.pow_le_pow_right (by omega) hc
    omega
  have hset : (Ico 1 b).filter (fun i => l ^ i ∣ N) = Icc 1 (padicValNat l N) := by
    ext i
    simp only [mem_filter, mem_Ico, mem_Icc, key]
    omega
  rw [hset, Nat.card_Icc]
  omega

theorem sum_padicVal_window_split (l : ℕ) (hl : 2 ≤ l) (m b : ℕ) :
    ∀ S : ℕ, m + S < l ^ b →
      (∑ j ∈ range S, padicValNat l (m + 1 + j)) + ∑ i ∈ Ico 1 b, m / l ^ i =
        ∑ i ∈ Ico 1 b, (m + S) / l ^ i := by
  intro S
  induction S with
  | zero => intro _; simp
  | succ S ih =>
    intro hS
    have ih' := ih (by omega)
    rw [sum_range_succ]
    have hv := padicValNat_eq_card_dvd_pows l hl (m + 1 + S) b (by omega) (by omega)
    have hdiv : ∀ i, (m + (S + 1)) / l ^ i =
        (m + S) / l ^ i + if l ^ i ∣ m + 1 + S then 1 else 0 := by
      intro i
      rw [show m + (S + 1) = m + S + 1 by omega, Nat.succ_div, show m + S + 1 = m + 1 + S by omega]
    rw [Finset.sum_congr rfl (fun i _ => hdiv i), sum_add_distrib, sum_boole, Nat.cast_id]
    omega

theorem sum_padicVal_window_le (l : ℕ) (hl : 2 ≤ l) (m S : ℕ) :
    ((∑ j ∈ range S, padicValNat l (m + 1 + j) : ℕ) : ℝ) ≤
      S / ((l : ℝ) - 1) + Real.logb l ((m + S : ℕ) : ℝ) := by
  have hl1 : (1:ℝ) < l := by exact_mod_cast (show 1 < l by omega)
  have hlpos : (0:ℝ) < (l:ℝ) - 1 := by linarith
  rcases Nat.eq_zero_or_pos S with hS | hS
  · subst hS
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_div, zero_add, add_zero]
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · simp [h0]
    · exact Real.logb_nonneg hl1 (by exact_mod_cast h0)
  obtain ⟨b, hb⟩ : ∃ b, b = Nat.log l (m + S) + 1 := ⟨_, rfl⟩
  have hlt : m + S < l ^ b := by rw [hb]; exact Nat.lt_pow_succ_log_self (by omega) _
  have E := sum_padicVal_window_split l hl m b S hlt
  have hT : ∑ i ∈ Ico 1 b, (m + S) / l ^ i ≤ ∑ i ∈ Ico 1 b, (m / l ^ i + (S / l ^ i + 1)) := by
    apply Finset.sum_le_sum
    intro i _
    have hq : 0 < l ^ i := by positivity
    rw [Nat.add_div hq]
    split_ifs <;> omega
  simp only [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, smul_eq_mul, mul_one] at hT
  have hN : ∑ j ∈ range S, padicValNat l (m + 1 + j) ≤ ∑ i ∈ Ico 1 b, S / l ^ i + (b - 1) := by omega
  have hgeo : ((∑ i ∈ Ico 1 b, S / l ^ i : ℕ) : ℝ) ≤ S / ((l:ℝ) - 1) := by
    rw [Nat.cast_sum]
    calc ∑ i ∈ Ico 1 b, ((S / l ^ i : ℕ) : ℝ) ≤ ∑ i ∈ Ico 1 b, (S:ℝ) * (1 / (l:ℝ)) ^ i := by
          apply Finset.sum_le_sum
          intro i _
          rw [one_div, inv_pow, ← div_eq_mul_inv]
          calc ((S / l ^ i : ℕ) : ℝ) ≤ (S:ℝ) / ((l ^ i : ℕ) : ℝ) := Nat.cast_div_le
            _ = (S:ℝ) / (l:ℝ) ^ i := by push_cast; rfl
      _ = S * ∑ i ∈ Ico 1 b, (1 / (l:ℝ)) ^ i := by rw [Finset.mul_sum]
      _ ≤ S * ((1 / (l:ℝ)) ^ 1 / (1 - 1 / (l:ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply geom_sum_Ico_le_of_lt_one (by positivity)
          rw [div_lt_one (by linarith)]
          exact hl1
      _ = S / ((l:ℝ) - 1) := by
          have hl0 : (l:ℝ) ≠ 0 := by positivity
          have hl1' : (l:ℝ) - 1 ≠ 0 := hlpos.ne'
          rw [pow_one, one_sub_div hl0, div_div_div_cancel_right₀ hl0, one_div, div_eq_mul_inv]
  have hlog : ((b - 1 : ℕ) : ℝ) ≤ Real.logb l ((m + S : ℕ) : ℝ) := by
    have e : b - 1 = Nat.log l (m + S) := by omega
    rw [e, Real.le_logb_iff_rpow_le hl1 (by exact_mod_cast (show 0 < m + S by omega)), Real.rpow_natCast]
    exact_mod_cast Nat.pow_log_le_self l (show m + S ≠ 0 by omega)
  calc ((∑ j ∈ range S, padicValNat l (m + 1 + j) : ℕ) : ℝ)
      ≤ ((∑ i ∈ Ico 1 b, S / l ^ i + (b - 1) : ℕ) : ℝ) := by exact_mod_cast hN
    _ = ((∑ i ∈ Ico 1 b, S / l ^ i : ℕ) : ℝ) + ((b - 1 : ℕ) : ℝ) := by rw [Nat.cast_add]
    _ ≤ S / ((l:ℝ) - 1) + Real.logb l ((m + S : ℕ) : ℝ) := add_le_add hgeo hlog

theorem logb_natCast_nonneg (l : ℕ) (hl : (1 : ℝ) < l) (N : ℕ) : 0 ≤ Real.logb l (N : ℝ) := by
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · simp [h0]
  · exact Real.logb_nonneg hl (by exact_mod_cast h0)

theorem sum_padicValInt_Ico_le_div_sub_one_add_logb (l : ℕ) (hl2 : 2 ≤ l) (a : ℤ) (S N : ℕ)
    (ha : ∀ i ∈ Finset.Ico a (a + S), i ≠ 0 ∧ |i| ≤ (N : ℤ)) :
    ((∑ i ∈ Finset.Ico a (a + S), padicValInt l i : ℕ) : ℝ) ≤
      S / ((l : ℝ) - 1) + Real.logb l N := by
  have hl1 : (1:ℝ) < l := by exact_mod_cast (show 1 < l by omega)
  have hLN : 0 ≤ Real.logb l (N:ℝ) := logb_natCast_nonneg l hl1 N
  have hre : ∑ i ∈ Finset.Ico a (a + S), padicValInt l i = ∑ k ∈ range S, padicValInt l (a + (k:ℤ)) := by
    have himg : (range S).image (fun k : ℕ => a + (k:ℤ)) = Finset.Ico a (a + S) := by
      ext i
      simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Ico]
      constructor
      · rintro ⟨k, hk, rfl⟩
        omega
      · intro h
        exact ⟨(i - a).toNat, by omega, by omega⟩
    rw [← himg, Finset.sum_image]
    intro x _ y _ h
    simpa using h
  rw [hre]
  rcases Nat.eq_zero_or_pos S with hS | hS
  · subst hS
    simp [hLN]
  have hfirst := ha a (by simp only [Finset.mem_Ico]; omega)
  have hlast := ha (a + S - 1) (by simp only [Finset.mem_Ico]; omega)
  rw [abs_le] at hfirst hlast
  by_cases hpos : 0 < a
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = a - 1 := ⟨(a - 1).toNat, by omega⟩
    have hr : ∑ k ∈ range S, padicValInt l (a + (k:ℤ)) = ∑ k ∈ range S, padicValNat l (m + 1 + k) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have e : a + (k:ℤ) = ((m + 1 + k : ℕ) : ℤ) := by push_cast; omega
      rw [show padicValInt l (a + (k:ℤ)) = padicValNat l (a + (k:ℤ)).natAbs by simp [padicValInt, padicValNat_def'], e, Int.natAbs_cast]
    rw [hr]
    refine (sum_padicVal_window_le l hl2 m S).trans (add_le_add le_rfl ?_)
    exact Real.logb_le_logb_of_le hl1 (by exact_mod_cast (show 0 < m + S by omega))
      (by exact_mod_cast (show m + S ≤ N by omega))
  · have hneg : a + S ≤ 0 := by
      by_contra hc
      have := ha 0 (by simp only [Finset.mem_Ico]; omega)
      exact this.1 rfl
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = -a - S := ⟨(-a - S).toNat, by omega⟩
    have hr : ∑ k ∈ range S, padicValInt l (a + (k:ℤ)) = ∑ k ∈ range S, padicValNat l (m + 1 + k) := by
      refine (Finset.sum_range_reflect (fun k : ℕ => padicValInt l (a + (k:ℤ))) S).symm.trans ?_
      refine Finset.sum_congr rfl (fun k hk => ?_)
      simp only [Finset.mem_range] at hk
      have e : a + (((S - 1 - k : ℕ)) : ℤ) = -((m + 1 + k : ℕ) : ℤ) := by omega
      show padicValInt l (a + ((S - 1 - k : ℕ) : ℤ)) = _
      rw [e, show padicValInt l (-((m + 1 + k : ℕ) : ℤ)) = padicValNat l (-((m + 1 + k : ℕ) : ℤ)).natAbs by simp [padicValInt, padicValNat_def'],
        Int.natAbs_neg, Int.natAbs_cast]
    rw [hr]
    refine (sum_padicVal_window_le l hl2 m S).trans (add_le_add le_rfl ?_)
    exact Real.logb_le_logb_of_le hl1 (by exact_mod_cast (show 0 < m + S by omega))
      (by exact_mod_cast (show m + S ≤ N by omega))

private theorem sum_biUnion_le_sum_sum' {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (t : ι → Finset ℤ) (f : ℤ → ℕ) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hj]
    have h2 := Finset.sum_union_inter (s₁ := t j) (s₂ := s.biUnion t) (f := f)
    omega

theorem kappa_bound_window_sum (l : ℕ) (hl : 11 ≤ l) (ell S h : ℕ) (a : Fin ell → ℤ)
    (ha : ∀ k, ∀ i ∈ Finset.Ico (a k) (a k + S), i ≠ 0 ∧ |i| ≤ (h : ℤ))
    (JS : Finset ℤ) (hJS : JS ⊆ Finset.univ.biUnion fun k => Finset.Ico (a k) (a k + S)) :
    (ell ≤ 3 → (((ell + ∑ i ∈ JS.erase 0, (ell + 1 + padicValInt l i) : ℕ) : ℝ)) ≤
      13 * S + 3 * Real.logb l (2 * (h : ℝ)) + 3) ∧
    (∀ R : ℕ, 1 ≤ R → ell ≤ R → (((ell + ∑ i ∈ JS.erase 0, (ell + 1 + padicValInt l i) : ℕ) : ℝ)) ≤
      3 * (R : ℝ) ^ 2 * (S + 1 + Real.logb l (2 * (h : ℝ)))) := by
  have hl1 : (1:ℝ) < l := by exact_mod_cast (show 1 < l by omega)
  have hl11 : (11:ℝ) ≤ l := by exact_mod_cast hl
  have hlm : (10:ℝ) ≤ (l:ℝ) - 1 := by linarith
  have hL0 : 0 ≤ Real.logb l (h:ℝ) := logb_natCast_nonneg l hl1 h
  have hL2 : Real.logb l (h:ℝ) ≤ Real.logb l (2 * (h:ℝ)) := by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · simp [h0]
    · have : (0:ℝ) < h := by exact_mod_cast h0
      exact Real.logb_le_logb_of_le hl1 this (by linarith)
  have hsub : JS.erase 0 ⊆ Finset.univ.biUnion fun k => Finset.Ico (a k) (a k + S) :=
    (Finset.erase_subset _ _).trans hJS
  have hC : (JS.erase 0).card ≤ ell * S := by
    calc (JS.erase 0).card ≤ (Finset.univ.biUnion fun k => Finset.Ico (a k) (a k + S)).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ k, (Finset.Ico (a k) (a k + S)).card := Finset.card_biUnion_le
      _ = ell * S := by simp
  have h1 : ∑ i ∈ JS.erase 0, padicValInt l i ≤ ∑ k, ∑ i ∈ Finset.Ico (a k) (a k + S), padicValInt l i :=
    (Finset.sum_le_sum_of_subset hsub).trans (sum_biUnion_le_sum_sum' _ _ _)
  have hV : ((∑ i ∈ JS.erase 0, padicValInt l i : ℕ) : ℝ) ≤ ell * (S / ((l:ℝ) - 1) + Real.logb l (h:ℝ)) := by
    calc ((∑ i ∈ JS.erase 0, padicValInt l i : ℕ) : ℝ)
        ≤ ((∑ k, ∑ i ∈ Finset.Ico (a k) (a k + S), padicValInt l i : ℕ) : ℝ) := by exact_mod_cast h1
      _ = ∑ k, ((∑ i ∈ Finset.Ico (a k) (a k + S), padicValInt l i : ℕ) : ℝ) := by rw [Nat.cast_sum]
      _ ≤ ∑ _k : Fin ell, (S / ((l:ℝ) - 1) + Real.logb l (h:ℝ)) :=
          Finset.sum_le_sum fun k _ => sum_padicValInt_Ico_le_div_sub_one_add_logb l (by omega) (a k) S h (ha k)
      _ = ell * (S / ((l:ℝ) - 1) + Real.logb l (h:ℝ)) := by simp [mul_add]
  have hQ : (((ell + ∑ i ∈ JS.erase 0, (ell + 1 + padicValInt l i)) : ℕ) : ℝ) =
      ell + (ell + 1) * ((JS.erase 0).card : ℝ) + ((∑ i ∈ JS.erase 0, padicValInt l i : ℕ) : ℝ) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
    push_cast
    ring
  have hCr : ((JS.erase 0).card : ℝ) ≤ ell * S := by exact_mod_cast hC
  have hS0 : (0:ℝ) ≤ S := by positivity
  have hX0 : 0 ≤ S / ((l:ℝ) - 1) := by positivity
  have hX : S / ((l:ℝ) - 1) ≤ S / 10 := div_le_div_of_nonneg_left hS0 (by norm_num) hlm
  have he0 : (0:ℝ) ≤ ell := by positivity
  have hC0 : (0:ℝ) ≤ ((JS.erase 0).card : ℝ) := by positivity
  have g1 : ((ell:ℝ) + 1) * ((JS.erase 0).card : ℝ) ≤ ((ell:ℝ) + 1) * (ell * S) :=
    mul_le_mul_of_nonneg_left hCr (by positivity)
  rw [hQ]
  refine ⟨fun h3 => ?_, fun R hR hR' => ?_⟩
  · have he3 : (ell:ℝ) ≤ 3 := by exact_mod_cast h3
    have g2 : ((ell:ℝ) + 1) * (ell * S) ≤ 12 * S := by
      have : ((ell:ℝ) + 1) * ell ≤ 12 := by nlinarith
      nlinarith
    have g3 : (ell:ℝ) * (S / ((l:ℝ) - 1) + Real.logb l (h:ℝ)) ≤ 3 * (S / ((l:ℝ) - 1) + Real.logb l (h:ℝ)) :=
      mul_le_mul_of_nonneg_right he3 (by positivity)
    linarith
  · have hr1 : (1:ℝ) ≤ R := by exact_mod_cast hR
    have her : (ell:ℝ) ≤ R := by exact_mod_cast hR'
    have g2 : ((ell:ℝ) + 1) * (ell * S) ≤ 2 * (R:ℝ) ^ 2 * S := by
      have : ((ell:ℝ) + 1) * ell ≤ 2 * (R:ℝ) ^ 2 := by nlinarith
      nlinarith
    have her2 : (ell:ℝ) ≤ (R:ℝ) ^ 2 := by nlinarith
    have g3 : (ell:ℝ) * (S / ((l:ℝ) - 1) + Real.logb l (h:ℝ)) ≤ (R:ℝ) ^ 2 * (S + Real.logb l (2 * (h:ℝ))) :=
      mul_le_mul her2 (by linarith) (by positivity) (by positivity)
    have g4 : 0 ≤ (R:ℝ) ^ 2 * Real.logb l (2 * (h:ℝ)) := mul_nonneg (by positivity) (by linarith)
    nlinarith

theorem letter_size_add_le_height {n : ℕ} (b w S η : ℕ) (size : ZMod n → ℕ) (h20w : 20 * w ≤ b)
    (hnt : ∀ i, ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i → size i ≤ w) (x : ZMod n) :
    size x + S ≤ Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size := by
  unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.hB
  split_ifs with hT
  · by_cases hx : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size x
    · unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick at hx
      omega
    · have := hnt x hx
      omega
  · have hx : ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size x := fun hh => hT ⟨x, hh⟩
    have := hnt x hx
    omega

theorem kappa_bound_of_length {n : ℕ} [NeZero n] (l : ℕ) (hl : 11 ≤ l) (b w S η : ℕ) (up : ZMod n → Bool)
    (size : ZMod n → ℕ) (h20w : 20 * w ≤ b)
    (hnt : ∀ i, ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i → size i ≤ w) (hsz : ∀ i, η < size i) (c : ZMod n) :
    ((arcOf b w S η up size).len c ≤ 3 → (kapC l (arcOf b w S η up size) c : ℝ) ≤
      13 * S + 3 * Real.logb l (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) + 3) ∧
    (∀ R : ℕ, 1 ≤ R → (arcOf b w S η up size).len c ≤ R → (kapC l (arcOf b w S η up size) c : ℝ) ≤
      3 * (R : ℝ) ^ 2 * ((S : ℝ) + 1 + Real.logb l (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ)))) := by
  let a : Fin ((arcOf b w S η up size).len c) → ℤ := fun k =>
    if up (c - ((k : ℕ) : ZMod n)) then -((size (c - ((k : ℕ) : ZMod n)) : ℕ) : ℤ) - S
    else ((size (c - ((k : ℕ) : ZMod n)) : ℕ) : ℤ)
  have hwin : ∀ k, ∀ i ∈ Finset.Ico (a k) (a k + S),
      i ≠ 0 ∧ |i| ≤ ((Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℕ) : ℤ) := by
    intro k i hi
    have h1 := letter_size_add_le_height b w S η size h20w hnt (c - ((k : ℕ) : ZMod n))
    have h2 := hsz (c - ((k : ℕ) : ZMod n))
    simp only [Finset.mem_Ico, a] at hi
    split_ifs at hi <;> exact ⟨by omega, abs_le.2 ⟨by omega, by omega⟩⟩
  have hty : ∀ x, (arcOf b w S η up size).ty x =
      if up x then Formalism.MainNotions.LocalTheoryWindows.LT.up (size x) else Formalism.MainNotions.LocalTheoryWindows.LT.down (size x) := fun _ => rfl
  have hSS : (arcOf b w S η up size).S = S := rfl
  have hJS : (arcOf b w S η up size).JS c ⊆ Finset.univ.biUnion fun k => Finset.Ico (a k) (a k + S) := by
    intro i hi
    simp only [Formalism.MainNotions.ArcLiftingSetup.ArcP.JS, Finset.mem_union] at hi
    rcases hi with hi | hi
    · rw [if_neg] at hi
      · simp at hi
      rintro ⟨s, -, hs⟩
      rw [hty] at hs
      split_ifs at hs
    · rw [Finset.mem_biUnion] at hi
      obtain ⟨s, hs, hi⟩ := hi
      rw [Finset.mem_range] at hs
      rw [Finset.mem_biUnion]
      refine ⟨⟨s, hs⟩, Finset.mem_univ _, ?_⟩
      rw [hty, hSS] at hi
      by_cases hu : up (c - (s : ZMod n)) <;> simp [a, hu] at hi ⊢ <;> omega
  exact kappa_bound_window_sum l hl ((arcOf b w S η up size).len c) S (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size) a hwin
    ((arcOf b w S η up size).JS c) hJS

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 in
theorem kappa_le_of_alternating : ∀ {n : ℕ} [NeZero n] (l : ℕ) (hl : 11 ≤ l) (b w S η : ℕ) (up : ZMod n → Bool)
    (size : ZMod n → ℕ) (h20 : 20 * S ≤ b) (h20w : 20 * w ≤ b)
    (hnt : ∀ i, ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i → size i ≤ w) (hAlt : Alt b η up size)
    (hsz : ∀ i, η < size i) (c : ZMod n) (hc : c ∈ (arcOf b w S η up size).cuts)
    (hlen : (arcOf b w S η up size).len c ≤ 3),
    (kapC l (arcOf b w S η up size) c : ℝ) ≤
      13 * S + 3 * Real.logb l (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) + 3 := by
  intro n _ l hl b w S η up size h20 h20w hnt hAlt hsz c hc hlen
  exact (kappa_bound_of_length l hl b w S η up size h20w hnt hsz c).1 hlen

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 in
theorem kappa_le_of_single_thick : ∀ {n : ℕ} [NeZero n] (l : ℕ) (hl : 11 ≤ l) (b w S η : ℕ) (up : ZMod n → Bool)
    (size : ZMod n → ℕ) (h20 : 20 * S ≤ b) (h20w : 20 * w ≤ b)
    (hnt : ∀ i, ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i → size i ≤ w) (R : ℕ) (hR : 1 ≤ R) (hOne : One b η R up size)
    (hsz : ∀ i, η < size i) (c : ZMod n) (hc : c ∈ (arcOf b w S η up size).cuts)
    (hlen : (arcOf b w S η up size).len c ≤ R),
    (kapC l (arcOf b w S η up size) c : ℝ) ≤
      3 * (R : ℝ) ^ 2 * ((S : ℝ) + 1 + Real.logb l (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ))) := by
  intro n _ l hl b w S η up size h20 h20w hnt R hR hOne hsz c hc hlen
  exact (kappa_bound_of_length l hl b w S η up size h20w hnt hsz c).2 R hR hlen

end Formalism.MainNotions.N.Ln17
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcSetupTheorem
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem arc_setup_theorem [NeZero n] [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (CR : ℝ) (hWR : Formalism.MainNotions.LiftingTheory.coreWR W CR) (hDc : Formalism.MainNotions.TruncatedSeriesCountingBounds.DcrisExactStrict PD LL)
    (hJ21 : ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD T₂.ρ τ a → IsJumpV PD T₁.ρ τ a)
    (hJmp : Formalism.MainNotions.CrystallineLiftingBounds.coreJumps PD LL O) :
    let A := arcOf b w S η up size
    A.OK ∧ Win W A T₁ ∧ Win W A T₂ ∧ (∑ c ∈ A.cuts, A.len c) = n ∧
    (Alt b η up size → ∀ c ∈ A.cuts, A.len c ≤ 3) ∧
    (∀ R : ℕ, 1 ≤ R → One b η R up size → ∀ c ∈ A.cuts, A.len c ≤ R) ∧
    (A.σ PD.p : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ∧
    ∃ rr : ℕ, (rr : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ∧
      (∀ c ∈ A.cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c (Formalism.MainNotions.LiftingTheory.lp W rr)) ∧
      ∀ (Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L) (cc : G → T₂.V),
        cc ∈ latticeCocycles T₂.L → IsCrys PD Y.ρ → Formalism.MainNotions.LiftingTheory.IsExtOf W ι π cc →
          Win W A Y ∧ ∀ c ∈ A.cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W π c (Formalism.MainNotions.LiftingTheory.lp W rr) :=
  SetupA.arcSetup_of W hcase F hB CR hWR hJmp hJ21

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.CocycleClassesExponent
noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Module

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {PD : PeriodData G Qp K₀ K B BdR}

theorem cocycle_classes_exponent {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (e : ℕ)
    (Zc : Finset (LatticeCohomology T₂.L))
    (hZc : ∀ z ∈ Zc, z ∈ latticeFiniteCohomology PD T₂.L)
    (h : ∀ x ∈ latticeFiniteCohomology PD T₂.L, (((PD.p : ℕ) : O) ^ e) • x ∈
      (latticeFiniteCohomology PD T₁.L).map F.H1map ⊔ Submodule.span O (Zc : Set (LatticeCohomology T₂.L))) :
    ∃ Z : Finset (G → T₂.V), Z.card ≤ Zc.card ∧ (∀ z ∈ Z, z ∈ latticeFiniteCocycles PD T₂.L) ∧ ExpIn PD F Z e := by
  classical
  have hrep : ∀ z ∈ Zc, ∃ a : ↥(latticeCocycles T₂.L), (a : G → T₂.V) ∈ latticeFiniteCocycles PD T₂.L ∧ Submodule.mkQ _ a = z := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp (hZc z hz)
    exact ⟨a, ha, rfl⟩
  choose! r hr1 hr2 using hrep
  refine ⟨Zc.image (fun z => (r z : G → T₂.V)), Finset.card_image_le, ?_, ?_⟩
  · intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    exact hr1 z hz
  · intro c hc
    have hc' : c ∈ latticeCocycles T₂.L ⊓ _ := hc
    have hcZ : c ∈ latticeCocycles T₂.L := (Submodule.mem_inf.mp hc').1
    have hx : Submodule.mkQ _ (⟨c, hcZ⟩ : ↥(latticeCocycles T₂.L)) ∈ latticeFiniteCohomology PD T₂.L :=
      Submodule.mem_map_of_mem (p := (latticeFiniteCocycles PD T₂.L).comap (latticeCocycles T₂.L).subtype) hc
    obtain ⟨y, hy, w, hw, hyw⟩ := Submodule.mem_sup.mp (h _ hx)
    obtain ⟨y0, hy0, rfl⟩ := Submodule.mem_map.mp hy
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hy0
    have ha' : (a : G → T₁.V) ∈ latticeFiniteCocycles PD T₁.L := ha
    have hspan : Submodule.span O (Zc : Set (LatticeCohomology T₂.L)) =
        (Submodule.span O (r '' (Zc : Set (LatticeCohomology T₂.L)))).map (Submodule.mkQ _) := by
      rw [Submodule.map_span, Set.image_image, Set.image_congr (g := fun z => z) (fun z hz => hr2 z hz),
        Set.image_id']
    rw [hspan] at hw
    obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp hw
    have e1 : F.H1map (Submodule.mkQ _ a) =
        Submodule.mkQ _ (⟨F.post a, F.post_Z1T _ a.2⟩ : ↥(latticeCocycles T₂.L)) := rfl
    have hker : ((PD.p : ℕ) : O) ^ e • (⟨c, hcZ⟩ : ↥(latticeCocycles T₂.L)) -
        ⟨F.post a, F.post_Z1T _ a.2⟩ - s ∈ (latticeCoboundaries T₂.L).comap (latticeCocycles T₂.L).subtype := by
      rw [← Submodule.ker_mkQ ((latticeCoboundaries T₂.L).comap (latticeCocycles T₂.L).subtype), LinearMap.mem_ker, map_sub, map_sub,
        map_smul, ← hyw, e1]
      abel
    have hb : ((PD.p : ℕ) : O) ^ e • c - F.post a - (s : G → T₂.V) ∈ latticeCoboundaries T₂.L := hker
    have hs' : (s : G → T₂.V) ∈
        Submodule.span O ((Zc.image fun z => (r z : G → T₂.V) : Finset (G → T₂.V)) : Set (G → T₂.V)) := by
      have hm := Submodule.mem_map_of_mem (f := (latticeCocycles T₂.L).subtype) hs
      rw [Submodule.map_span] at hm
      refine Submodule.span_mono ?_ hm
      rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hz)
    have hpa : F.post a ∈ F.ImF PD := Submodule.mem_sup_left (Submodule.mem_map_of_mem ha')
    have hbI : ((PD.p : ℕ) : O) ^ e • c - F.post a - (s : G → T₂.V) ∈ F.ImF PD := Submodule.mem_sup_right hb
    have key : ((PD.p : ℕ) : O) ^ e • c =
        (F.post a + (((PD.p : ℕ) : O) ^ e • c - F.post a - (s : G → T₂.V))) + s := by abel
    rw [key]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.add_mem _ hpa hbI)) (Submodule.mem_sup_right hs')

end Core

end Formalism.MainNotions.N.Ln17
end
end

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Module
open Formalism.MainNotions.N.FrobeniusPowerSeries (LiftsAt InFF InLpp)

section Assembly

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem split_sum [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hl : 5 ≤ PD.p) (hsplit : SplitCore W) (hext : ExtYCore PD W)
    (A : ArcP n) (hA : A.OK) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (hcr : IsCrys PD T₂.ρ) (hW₂ : Win W A T₂) (rr : ℕ)
    (hY : ∀ (Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L) (cc : G → T₂.V),
      cc ∈ latticeCocycles T₂.L → IsCrys PD Y.ρ → Formalism.MainNotions.LiftingTheory.IsExtOf W ι π cc →
        Win W A Y ∧ ∀ c ∈ A.cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W π c (Formalism.MainNotions.LiftingTheory.lp W rr))
    (E : ℕ) (Zc : ZMod n → Finset (LatticeCohomology T₂.L))
    (hcut : ∀ c ∈ A.cuts, ∀ (w : W.DD T₂) (x : LatticeCohomology T₂.L), InI W T₂ c w →
        InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) 1 (abelian₂ W A c (A.len c) • w) →
        (∀ (d : ℕ) (bb : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL),
          IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) bb sol → PoleOK W A T₂ c bb sol w) →
        IsRho W A T₂ c w x →
        (((PD.p : ℕ) : O) ^ E) • x ∈
          (latticeFiniteCohomology PD T₁.L).map F.H1map ⊔ Submodule.span O ((A.cuts.biUnion Zc : Finset _) : Set (LatticeCohomology T₂.L))) :
    ∀ x ∈ latticeFiniteCohomology PD T₂.L, (((PD.p : ℕ) : O) ^ (rr + 2 * A.σ PD.p + E)) • x ∈
      (latticeFiniteCohomology PD T₁.L).map F.H1map ⊔ Submodule.span O ((A.cuts.biUnion Zc : Finset _) : Set (LatticeCohomology T₂.L)) := by
  intro x hx
  obtain ⟨⟨cc, hcc⟩, hyf, rfl⟩ := Submodule.mem_map.mp hx
  have hccf : cc ∈ latticeFiniteCocycles PD T₂.L := hyf
  obtain ⟨Y, ι, π, hYc, hE⟩ := hext T₂ hcr cc hccf
  obtain ⟨-, hkill⟩ := hY Y ι π cc hcc hYc hE
  obtain ⟨w, xx, hw, hsum⟩ := hsplit hcase hl A hA T₂ Y ι π hW₂ hYc cc hcc hE rr hkill
  have hmem : ∀ c ∈ A.cuts, (((PD.p : ℕ) : O) ^ E) • xx c ∈
      (latticeFiniteCohomology PD T₁.L).map F.H1map ⊔ Submodule.span O ((A.cuts.biUnion Zc : Finset _) : Set (LatticeCohomology T₂.L)) :=
    fun c hc => hcut c hc (w c) (xx c) (hw c hc).1 (hw c hc).2.1 (hw c hc).2.2.2 (hw c hc).2.2.1
  rw [Submodule.mkQ_apply, show rr + 2 * A.σ PD.p + E = E + (rr + 2 * A.σ PD.p) by ring, pow_add,
    mul_smul]
  rcases hsum with h | h
  · rw [h, Finset.smul_sum]
    exact Submodule.sum_mem _ hmem
  · rw [h, smul_neg, Finset.smul_sum]
    exact Submodule.neg_mem _ (Submodule.sum_mem _ hmem)

private lemma logb_two_mul_hB_nonneg {n : ℕ} (l b w S η : ℕ) (size : ZMod n → ℕ) (hl : 2 ≤ l) :
    0 ≤ Real.logb l (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) := by
  rcases Nat.eq_zero_or_pos (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size) with h | h
  · simp [h]
  · apply Real.logb_nonneg
    · exact_mod_cast (by omega : 1 < l)
    · have : (1 : ℝ) ≤ (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ) := by exact_mod_cast h
      linarith

theorem one_le_Sg {n : ℕ} (l b w S η : ℕ) (size : ZMod n → ℕ) (hl : 2 ≤ l) : 1 ≤ Sg l b w S η size := by
  have h1 := logb_two_mul_hB_nonneg l b w S η size hl
  unfold Sg
  have a : (0 : ℝ) ≤ (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ) / (l : ℝ) ^ 2 := by positivity
  have c : (0 : ℝ) ≤ ((w : ℝ) + S + η) / l := by positivity
  linarith

theorem logb_hB_nonneg {n : ℕ} (l b w S η : ℕ) (size : ZMod n → ℕ) (hl : 2 ≤ l) :
    0 ≤ Real.logb l (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) := by
  exact logb_two_mul_hB_nonneg l b w S η size hl

theorem logb_le_Sg {n : ℕ} (l b w S η : ℕ) (size : ZMod n → ℕ) :
    3 * Real.logb l (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) + 3 ≤ 3 * Sg l b w S η size := by
  unfold Sg
  have a : (0 : ℝ) ≤ (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ) / (l : ℝ) ^ 2 := by positivity
  have c : (0 : ℝ) ≤ ((w : ℝ) + S + η) / l := by positivity
  linarith

theorem bandI_nonneg {n : ℕ} (l b w S η : ℕ) (size : ZMod n → ℕ) (Cb : ℝ) :
    0 ≤ bandI l b w S η size Cb := by
  unfold bandI
  split_ifs <;> norm_num

theorem sumAltW [Fintype (K →ₐ[Qp] LL)] [NeZero n] [FiniteDimensional Qp LL] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) {CR : ℝ}
    {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (co : CoresW W CR Pt)
    {T₁ T₂ : LocLat G Qp LL O} (f : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ f b w S η m up size Mi hi)
    (hAlt : Alt b η up size) (Cb : ℝ) (hCb : 2 ≤ Cb)
    (hsm : (¬ ∃ i, Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i) ∨ 40 * Sg PD.p b w S η size ≤ (b : ℝ) / 4) :
    ∃ (e : ℕ) (Z : Finset (G → T₂.V)),
      (e : ℝ) ≤ 55 * Sg PD.p b w S η size + 13 * S + η * bandI PD.p b w S η size Cb ∧
      Z.card ≤ 4 * n * m ∧ (∀ z ∈ Z, z ∈ latticeFiniteCocycles PD T₂.L) ∧ ExpIn PD f Z e := by
  have hl : 11 ≤ PD.p := hB.1
  have hS := hB.2.1
  have hcase := hS.1
  obtain ⟨hOK, hW₁, hW₂, hsumlen, hlen3, -, hσ, rr, hrr, hkF, hY⟩ :=
    Formalism.MainNotions.N.FrobeniusPowerSeries.arc_setup_theorem W hcase f hB CR co.wr co.dc (co.jq T₁ T₂ f hS.2.1) co.cj
  have hsg1 := one_le_Sg PD.p b w S η size (by omega)
  have hbd0 := bandI_nonneg PD.p b w S η size Cb
  obtain ⟨E₁, hE₁def⟩ : ∃ E₁ : ℕ,
      E₁ = ⌊40 * Sg PD.p b w S η size + η * bandI PD.p b w S η size Cb⌋₊ := ⟨_, rfl⟩
  have hη0 : (0 : ℝ) ≤ η * bandI PD.p b w S η size Cb := mul_nonneg (Nat.cast_nonneg η) hbd0
  have hE₁le : (E₁ : ℝ) ≤ 40 * Sg PD.p b w S η size + η * bandI PD.p b w S η size Cb := by
    rw [hE₁def]; exact Nat.floor_le (by linarith)
  have hσE : (arcOf b w S η up size).σ PD.p ≤ E₁ := by
    rw [hE₁def]; apply Nat.le_floor; linarith
  have hscope : ∀ c ∈ (arcOf b w S η up size).cuts, (arcOf b w S η up size).len c ≤ 2 ∨
      40 * Sg PD.p b w S η size ≤ (b : ℝ) / 4 := by
    intro c _
    rcases hsm with h | h
    · left; exact (arc_len_le_one_of_no_thick b w S η up size h c).trans (by norm_num)
    · right; exact h
  have hARC : ∀ c ∈ (arcOf b w S η up size).cuts, ∀ (d : ℕ) (bb : Fin d → W.DD T₂)
      (sol : Fin d → ℕ → Fin d → LL),
      IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol → ∀ k₀,
      InLpp W (arcOf b w S η up size) T₂ c bb k₀ → ∀ f', InFF W (arcOf b w S η up size) c f' →
      LiftsAt W (arcOf b w S η up size) f c bb sol k₀ f' E₁ := by
    intro c hc d bb sol hbb k₀ hk₀ f' hf'
    obtain ⟨e₁, he₁, hL⟩ := Formalism.MainNotions.N.FrobeniusPowerSeries.arc_proposition_alternative W hcase f hB CR co.wr hW₁ hW₂ co.H co.Tr co.relay co.arc
      co.arcL co.nn co.sat co.satP co.kLev co.r2 co.hO co.hOv co.inj co.P2 co.P9 co.pi0 co.sec co.gl co.hf co.fl rr hrr hkF c hc bb sol
      hbb k₀ hk₀ f' hf' Pt co.P3 co.P4 co.ptEx co.c4 co.P5 Cb hCb hAlt (hscope c hc)
    exact Formalism.MainNotions.N.FrobeniusPowerSeries.LiftsAt.liftsAt_mono _ _ _ _ _ _ _ (hE₁def ▸ Nat.le_floor he₁) hL
  have hm : ∀ i, ((arcOf b w S η up size).ty i).thick →
      Formalism.MainNotions.TruncatedSeriesCountingBounds.lowCount W T₂ i (arcOf b w S η up size).η ≤ m := fun i _ => hS.2.2.2.2.1 i
  have hcut := fun c (hc : c ∈ (arcOf b w S η up size).cuts) => arc_length_bound_theorem W hcase co.l5 co.hO co.hOv
    co.inj co.relay co.arc co.nn co.univ co.kLev co.kMod co.P2 co.P9 co.pi0 (arcOf b w S η up size) hOK
    f hS.2.1 hW₁ hW₂ m hm c hc E₁ hσE (hARC c hc)
  choose! Zc hZcard hZH1 hZmain using hcut
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℕ, κ = (arcOf b w S η up size).cuts.sup
      (kapC PD.p (arcOf b w S η up size)) := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ E : ℕ, E = (arcOf b w S η up size).σ PD.p + κ + E₁ := ⟨_, rfl⟩
  have hcutE : ∀ c ∈ (arcOf b w S η up size).cuts, ∀ (w' : W.DD T₂) (x : LatticeCohomology T₂.L),
      InI W T₂ c w' →
      InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) ((arcOf b w S η up size).len c) 1
        (abelian₂ W (arcOf b w S η up size) c ((arcOf b w S η up size).len c) • w') →
      (∀ (d : ℕ) (bb : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL),
        IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol →
        PoleOK W (arcOf b w S η up size) T₂ c bb sol w') →
      IsRho W (arcOf b w S η up size) T₂ c w' x →
      (((PD.p : ℕ) : O) ^ E) • x ∈ (latticeFiniteCohomology PD T₁.L).map f.H1map ⊔
        Submodule.span O (((arcOf b w S η up size).cuts.biUnion Zc : Finset _) : Set (LatticeCohomology T₂.L)) := by
    intro c hc w' x h1 h2 h3 h4
    have h := hZmain c hc w' x h1 h2 h3 h4
    have hk : kapC PD.p (arcOf b w S η up size) c ≤ κ :=
      hκdef ▸ Finset.le_sup (f := kapC PD.p (arcOf b w S η up size)) hc
    have hE : E = ((arcOf b w S η up size).σ PD.p + kapC PD.p (arcOf b w S η up size) c + E₁) +
        (κ - kapC PD.p (arcOf b w S η up size) c) := by rw [hEdef]; omega
    have hsub : ((Zc c : Finset _) : Set (LatticeCohomology T₂.L)) ⊆
        (((arcOf b w S η up size).cuts.biUnion Zc : Finset _) : Set (LatticeCohomology T₂.L)) := fun z hz =>
      Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨c, hc, Finset.mem_coe.1 hz⟩)
    rw [hE, pow_add, mul_comm, mul_smul]
    refine Submodule.smul_mem _ _ ?_
    exact SetLike.le_def.1 (sup_le_sup_left (Submodule.span_mono hsub) ((latticeFiniteCohomology PD T₁.L).map f.H1map)) h
  have hsp := split_sum W hcase co.l5 co.split co.ext (arcOf b w S η up size) hOK f hS.2.1.2.1 hW₂ rr
    hY E Zc hcutE
  have hZH1' : ∀ z ∈ (arcOf b w S η up size).cuts.biUnion Zc, z ∈ latticeFiniteCohomology PD T₂.L := by
    intro z hz
    obtain ⟨c, hc, hz'⟩ := Finset.mem_biUnion.1 hz
    exact hZH1 c hc z hz'
  obtain ⟨Z, hZc, hZf, hZe⟩ := cocycle_classes_exponent f (rr + 2 * (arcOf b w S η up size).σ PD.p + E) _ hZH1' hsp
  refine ⟨rr + 2 * (arcOf b w S η up size).σ PD.p + E, Z, ?_, ?_, hZf, hZe⟩
  ·
    have hlg := logb_le_Sg PD.p b w S η size
    have hlg0 := logb_hB_nonneg PD.p b w S η size (by omega)
    have hκ : (κ : ℝ) ≤ 13 * S + 3 * Real.logb PD.p (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) + 3 := by
      have h0 : 0 ≤ 13 * (S : ℝ) + 3 * Real.logb PD.p (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) + 3 := by
        have := Nat.cast_nonneg (α := ℝ) S; linarith
      have : κ ≤ ⌊13 * (S : ℝ) + 3 * Real.logb PD.p (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) + 3⌋₊ := by
        rw [hκdef]
        apply Finset.sup_le
        intro c hc
        apply Nat.le_floor
        exact kappa_le_of_alternating PD.p hl b w S η up size hB.2.2.2.2.1 hB.2.2.1 hS.2.2.2.2.2.1 hAlt hS.2.2.1 c hc (hlen3 hAlt c hc)
      exact (Nat.cast_le.2 this).trans (Nat.floor_le h0)
    rw [hEdef]
    push_cast
    linarith
  ·
    refine hZc.trans ((Finset.card_biUnion_le).trans ?_)
    calc ∑ c ∈ (arcOf b w S η up size).cuts, (Zc c).card
        ≤ ∑ c ∈ (arcOf b w S η up size).cuts, 4 * m * (arcOf b w S η up size).len c := by
          apply Finset.sum_le_sum
          intro c hc
          refine (hZcard c hc).trans ?_
          have h1 := ro_le_arc_len (arcOf b w S η up size) c
          have h2 := hlen3 hAlt c hc
          have : Formalism.MainNotions.LocalTheoryWindows.ro (arcOf b w S η up size).ty (arcOf b w S η up size).len c *
              ((arcOf b w S η up size).len c + 1) ≤ 4 * (arcOf b w S η up size).len c := by nlinarith
          calc m * Formalism.MainNotions.LocalTheoryWindows.ro (arcOf b w S η up size).ty (arcOf b w S η up size).len c *
                ((arcOf b w S η up size).len c + 1)
              = m * (Formalism.MainNotions.LocalTheoryWindows.ro (arcOf b w S η up size).ty (arcOf b w S η up size).len c *
                ((arcOf b w S η up size).len c + 1)) := by ring
            _ ≤ m * (4 * (arcOf b w S η up size).len c) := Nat.mul_le_mul_left m this
            _ = 4 * m * (arcOf b w S η up size).len c := by ring
      _ = 4 * m * ∑ c ∈ (arcOf b w S η up size).cuts, (arcOf b w S η up size).len c := by
          rw [Finset.mul_sum]
      _ = 4 * n * m := by rw [hsumlen]; ring

theorem sumOneW [Fintype (K →ₐ[Qp] LL)] [NeZero n] [FiniteDimensional Qp LL] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) {CR : ℝ}
    {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (co : CoresW W CR Pt)
    {T₁ T₂ : LocLat G Qp LL O} (f : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ f b w S η m up size Mi hi)
    (R : ℕ) (hR : 1 ≤ R) (hOne : One b η R up size) :
    ∃ (e : ℕ) (Z : Finset (G → T₂.V)),
      (e : ℝ) ≤ 18 * Sg PD.p b w S η size + 3 * (R : ℝ) ^ 2 * ((S : ℝ) + 1 +
        Real.logb PD.p (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ))) + 1 ∧
      Z.card ≤ (R + 1) * n * m ∧ (∀ z ∈ Z, z ∈ latticeFiniteCocycles PD T₂.L) ∧ ExpIn PD f Z e := by
  have hl : 11 ≤ PD.p := hB.1
  have hS := hB.2.1
  have hcase := hS.1
  obtain ⟨hOK, hW₁, hW₂, hsumlen, -, hlenR, hσ, rr, hrr, hkF, hY⟩ :=
    Formalism.MainNotions.N.FrobeniusPowerSeries.arc_setup_theorem W hcase f hB CR co.wr co.dc (co.jq T₁ T₂ f hS.2.1) co.cj
  have hsg1 := one_le_Sg PD.p b w S η size (by omega)
  obtain ⟨E₁, hE₁def⟩ : ∃ E₁ : ℕ, E₁ = ⌊6 * Sg PD.p b w S η size + 1⌋₊ := ⟨_, rfl⟩
  have hE₁le : (E₁ : ℝ) ≤ 6 * Sg PD.p b w S η size + 1 := by
    rw [hE₁def]; exact Nat.floor_le (by linarith)
  have hσE : (arcOf b w S η up size).σ PD.p ≤ E₁ := by
    rw [hE₁def]; apply Nat.le_floor; linarith
  have hARC : ∀ c ∈ (arcOf b w S η up size).cuts, ∀ (d : ℕ) (bb : Fin d → W.DD T₂)
      (sol : Fin d → ℕ → Fin d → LL),
      IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol → ∀ k₀,
      InLpp W (arcOf b w S η up size) T₂ c bb k₀ → ∀ f', InFF W (arcOf b w S η up size) c f' →
      LiftsAt W (arcOf b w S η up size) f c bb sol k₀ f' E₁ := by
    intro c hc d bb sol hbb k₀ hk₀ f' hf'
    obtain ⟨e₁, he₁, hL⟩ := Formalism.MainNotions.N.FrobeniusPowerSeries.arc_single_type_bound W hcase f hB CR co.wr hW₁ hW₂ co.H co.Tr co.relay co.arc
      co.arcL co.nn co.sat co.satP co.kLev co.r2 co.hO co.hOv co.inj co.P2 co.P9 co.pi0 co.sec co.gl co.hf co.fl rr hrr hkF c hc bb
      sol hbb k₀ hk₀ f' hf' (fun s _ => (hOne.1 _).trans (hOne.1 c).symm)
    exact Formalism.MainNotions.N.FrobeniusPowerSeries.LiftsAt.liftsAt_mono _ _ _ _ _ _ _ (hE₁def ▸ Nat.le_floor he₁) hL
  have hm : ∀ i, ((arcOf b w S η up size).ty i).thick →
      Formalism.MainNotions.TruncatedSeriesCountingBounds.lowCount W T₂ i (arcOf b w S η up size).η ≤ m := fun i _ => hS.2.2.2.2.1 i
  have hcut := fun c (hc : c ∈ (arcOf b w S η up size).cuts) => arc_length_bound_theorem W hcase co.l5 co.hO co.hOv
    co.inj co.relay co.arc co.nn co.univ co.kLev co.kMod co.P2 co.P9 co.pi0 (arcOf b w S η up size) hOK
    f hS.2.1 hW₁ hW₂ m hm c hc E₁ hσE (hARC c hc)
  choose! Zc hZcard hZH1 hZmain using hcut
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℕ, κ = (arcOf b w S η up size).cuts.sup
      (kapC PD.p (arcOf b w S η up size)) := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ E : ℕ, E = (arcOf b w S η up size).σ PD.p + κ + E₁ := ⟨_, rfl⟩
  have hcutE : ∀ c ∈ (arcOf b w S η up size).cuts, ∀ (w' : W.DD T₂) (x : LatticeCohomology T₂.L),
      InI W T₂ c w' →
      InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) ((arcOf b w S η up size).len c) 1
        (abelian₂ W (arcOf b w S η up size) c ((arcOf b w S η up size).len c) • w') →
      (∀ (d : ℕ) (bb : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL),
        IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol →
        PoleOK W (arcOf b w S η up size) T₂ c bb sol w') →
      IsRho W (arcOf b w S η up size) T₂ c w' x →
      (((PD.p : ℕ) : O) ^ E) • x ∈ (latticeFiniteCohomology PD T₁.L).map f.H1map ⊔
        Submodule.span O (((arcOf b w S η up size).cuts.biUnion Zc : Finset _) : Set (LatticeCohomology T₂.L)) := by
    intro c hc w' x h1 h2 h3 h4
    have h := hZmain c hc w' x h1 h2 h3 h4
    have hk : kapC PD.p (arcOf b w S η up size) c ≤ κ :=
      hκdef ▸ Finset.le_sup (f := kapC PD.p (arcOf b w S η up size)) hc
    have hE : E = ((arcOf b w S η up size).σ PD.p + kapC PD.p (arcOf b w S η up size) c + E₁) +
        (κ - kapC PD.p (arcOf b w S η up size) c) := by rw [hEdef]; omega
    have hsub : ((Zc c : Finset _) : Set (LatticeCohomology T₂.L)) ⊆
        (((arcOf b w S η up size).cuts.biUnion Zc : Finset _) : Set (LatticeCohomology T₂.L)) := fun z hz =>
      Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨c, hc, Finset.mem_coe.1 hz⟩)
    rw [hE, pow_add, mul_comm, mul_smul]
    refine Submodule.smul_mem _ _ ?_
    exact SetLike.le_def.1 (sup_le_sup_left (Submodule.span_mono hsub) ((latticeFiniteCohomology PD T₁.L).map f.H1map)) h
  have hsp := split_sum W hcase co.l5 co.split co.ext (arcOf b w S η up size) hOK f hS.2.1.2.1 hW₂ rr
    hY E Zc hcutE
  have hZH1' : ∀ z ∈ (arcOf b w S η up size).cuts.biUnion Zc, z ∈ latticeFiniteCohomology PD T₂.L := by
    intro z hz
    obtain ⟨c, hc, hz'⟩ := Finset.mem_biUnion.1 hz
    exact hZH1 c hc z hz'
  obtain ⟨Z, hZc, hZf, hZe⟩ := cocycle_classes_exponent f (rr + 2 * (arcOf b w S η up size).σ PD.p + E) _ hZH1' hsp
  refine ⟨rr + 2 * (arcOf b w S η up size).σ PD.p + E, Z, ?_, ?_, hZf, hZe⟩
  ·
    have hlg0 := logb_hB_nonneg PD.p b w S η size (by omega)
    have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
    have hκ : (κ : ℝ) ≤ 3 * (R : ℝ) ^ 2 * ((S : ℝ) + 1 +
        Real.logb PD.p (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ))) := by
      have h0 : 0 ≤ 3 * (R : ℝ) ^ 2 * ((S : ℝ) + 1 +
          Real.logb PD.p (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ))) := by
        have := Nat.cast_nonneg (α := ℝ) S; positivity
      have : κ ≤ ⌊3 * (R : ℝ) ^ 2 * ((S : ℝ) + 1 +
          Real.logb PD.p (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ)))⌋₊ := by
        rw [hκdef]
        apply Finset.sup_le
        intro c hc
        apply Nat.le_floor
        exact kappa_le_of_single_thick PD.p hl b w S η up size hB.2.2.2.2.1 hB.2.2.1 hS.2.2.2.2.2.1 R hR hOne hS.2.2.1 c hc
          (hlenR R hR hOne c hc)
      exact (Nat.cast_le.2 this).trans (Nat.floor_le h0)
    rw [hEdef]
    push_cast
    linarith
  ·
    refine hZc.trans ((Finset.card_biUnion_le).trans ?_)
    calc ∑ c ∈ (arcOf b w S η up size).cuts, (Zc c).card
        ≤ ∑ c ∈ (arcOf b w S η up size).cuts, (R + 1) * m * (arcOf b w S η up size).len c := by
          apply Finset.sum_le_sum
          intro c hc
          refine (hZcard c hc).trans ?_
          have h1 := ro_le_arc_len (arcOf b w S η up size) c
          have h2 := hlenR R hR hOne c hc
          have : Formalism.MainNotions.LocalTheoryWindows.ro (arcOf b w S η up size).ty (arcOf b w S η up size).len c *
              ((arcOf b w S η up size).len c + 1) ≤ (R + 1) * (arcOf b w S η up size).len c := by
            nlinarith
          calc m * Formalism.MainNotions.LocalTheoryWindows.ro (arcOf b w S η up size).ty (arcOf b w S η up size).len c *
                ((arcOf b w S η up size).len c + 1)
              = m * (Formalism.MainNotions.LocalTheoryWindows.ro (arcOf b w S η up size).ty (arcOf b w S η up size).len c *
                ((arcOf b w S η up size).len c + 1)) := by ring
            _ ≤ m * ((R + 1) * (arcOf b w S η up size).len c) := Nat.mul_le_mul_left m this
            _ = (R + 1) * m * (arcOf b w S η up size).len c := by ring
      _ = (R + 1) * m * ∑ c ∈ (arcOf b w S η up size).cuts, (arcOf b w S η up size).len c := by
          rw [Finset.mul_sum]
      _ = (R + 1) * n * m := by rw [hsumlen]; ring

end Assembly

section Record

variable (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)

theorem coresAt {CR CA CB CK : ℝ} (hU : AdmBoundsB D HW F Cm CR CA CB CK) (hJ : UsedJ D HW F)
    (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL) (hK : CaseA K LL) (hl : 11 ≤ l)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))] [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)] :
    CoresW ((HW l).W K 1 LL hG) CR (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) := by
  have h5 : 5 ≤ l := by omega
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hFD : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F := hU.p9
  refine
    { l5 := by rw [hpl]; exact h5
      hO := fun x => ((D.loc l).v_O LL (x : ↥LL.1)).2 x.2
      hOv := fun x hx => ⟨⟨x, ((D.loc l).v_O LL x).1 hx⟩, rfl⟩
      inj := Subtype.val_injective
      wr := hU.a2.2.2.2.2.1 l K 1 LL hG
      H := hU.a2.2.2.2.2.2.1 l K 1 LL hG
      Tr := hU.a2.2.2.2.2.2.2.1 l K 1 LL hG
      dc := hU.a15 l K LL
      relay := hU.a11 l K LL hG hK h5
      arc := (hU.a12 l K LL hG hK h5).1
      arcL := (hU.a12 l K LL hG hK h5).2
      split := hU.a13 l K LL hG hK h5
      nn := (hU.a14 l K LL hG hK h5).1
      univ := (hU.a14 l K LL hG hK h5).2
      sat := hU.a5 l K LL hG hK h5
      satP := hU.sP l K LL hG hK h5
      kLev := hU.kLev l K LL hG hK h5
      kMod := hU.kMod l K LL hG hK h5
      r2 := hU.a9
      P2 := hU.p2 l K 1 LL hG
      P3 := hU.p3 l K 1 LL hG
      P4 := hU.p4 l K 1 LL hG
      P9 := hU.p9 l K 1 LL hG
      pi0 := (Formalism.MainNotions.UnusedSlot80.gamma_uniformizer_divisible_statement D HW F h9 l K LL hK h5) ((HW l).W K 1 LL hG).gam
      ptEx := ptEx_at D HW l K LL hG hK
      P5 := hU.p5 l K 1 LL hG
      ext := fun T hT cc hcc => Formalism.MainNotions.LiftingTheory.lext_HExt_D D HW F l K 1 LL hG
        (Formalism.MainNotions.LiftingTheory.gen_one_crys _) T cc hT hcc
      cj := hJ.a23 l K LL
      c4 := hJ.c4 l K 1 LL hG
      sec := (arc_structures_hold_at D HW F Cm hU hJ l K LL hG hK).1
      gl := (arc_structures_hold_at D HW F Cm hU hJ l K LL hG hK).2.1
      hf := (arc_structures_hold_at D HW F Cm hU hJ l K LL hG hK).2.2.1
      fl := (arc_structures_hold_at D HW F Cm hU hJ l K LL hG hK).2.2.2
      jq := (jumps_of_surjective_lattice_map D HW F hJ l K LL hG).1
      jy := (jumps_of_surjective_lattice_map D HW F hJ l K LL hG).2 }

end Record

section Record2

variable (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)

theorem sum_alt {CR CA CB CK : ℝ} (hU : AdmBoundsB D HW F Cm CR CA CB CK) (hJ : UsedJ D HW F)
    (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL) (hK : CaseA K LL)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))] [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)]
    (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (f : LatHom T₁.L T₂.L) (b w S η m : ℕ)
    (up : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Bool) (size Mi hi : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ)
    (hB : HypB ((D.loc l).PD K) ((HW l).W K 1 LL hG) T₁ T₂ f b w S η m up size Mi hi)
    (hAlt : Alt b η up size) (Cb : ℝ) (hCb : 2 ≤ Cb)
    (hsm : (¬ ∃ i, Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i) ∨ 40 * Sg l b w S η size ≤ (b : ℝ) / 4) :
    ∃ (e : ℕ) (Z : Finset (↥(GK K) → T₂.V)),
      (e : ℝ) ≤ 55 * Sg l b w S η size + 13 * S + η * bandI l b w S η size Cb ∧
      Z.card ≤ 4 * Module.finrank ℚ_[l] ↥(K0 K) * m ∧ (∀ z ∈ Z, z ∈ latticeFiniteCocycles ((D.loc l).PD K) T₂.L) ∧
      ExpIn ((D.loc l).PD K) f Z e := by
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hl : 11 ≤ l := by
    have h11 := hB.1
    rwa [hp] at h11
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := isAdicComplete_integers_local l LL
  have h := sumAltW ((HW l).W K 1 LL hG) (coresAt D HW F Cm hU hJ l K LL hG hK hl) f hB hAlt Cb hCb
    (by rw [hp]; exact hsm)
  rw [hp] at h
  exact h

theorem sum_one {CR CA CB CK : ℝ} (hU : AdmBoundsB D HW F Cm CR CA CB CK) (hJ : UsedJ D HW F)
    (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL) (hK : CaseA K LL)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))] [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)]
    (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (f : LatHom T₁.L T₂.L) (b w S η m : ℕ)
    (up : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Bool) (size Mi hi : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ)
    (hB : HypB ((D.loc l).PD K) ((HW l).W K 1 LL hG) T₁ T₂ f b w S η m up size Mi hi)
    (R : ℕ) (hR : 1 ≤ R) (hOne : One b η R up size) :
    ∃ (e : ℕ) (Z : Finset (↥(GK K) → T₂.V)),
      (e : ℝ) ≤ 18 * Sg l b w S η size + 3 * (R : ℝ) ^ 2 * ((S : ℝ) + 1 +
        Real.logb l (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ))) + 1 ∧
      Z.card ≤ (R + 1) * Module.finrank ℚ_[l] ↥(K0 K) * m ∧ (∀ z ∈ Z, z ∈ latticeFiniteCocycles ((D.loc l).PD K) T₂.L) ∧
      ExpIn ((D.loc l).PD K) f Z e := by
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hl : 11 ≤ l := by
    have h11 := hB.1
    rwa [hp] at h11
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := isAdicComplete_integers_local l LL
  have h := sumOneW ((HW l).W K 1 LL hG) (coresAt D HW F Cm hU hJ l K LL hG hK hl) f hB R hR hOne
  rw [hp] at h
  exact h

end Record2

end Formalism.MainNotions.N.Ln17
