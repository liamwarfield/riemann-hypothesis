module

public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.SumCMulImHermCEqSignMulTrace
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitR
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitOA

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.DivSqLeOfForallDivAddSqLe
namespace GlobalTheory

open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2
open scoped InnerProductSpace

noncomputable section

theorem _root_.GlobalTheory.greedy_splitting_thin :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ (n : ℕ) (ω : Fin n → 𝓞 E), (∀ j (σ : E →+* ℂ), ‖σ (ω j)‖ ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E)) ∧ ∀ α : 𝓞 E, (α : E) ∈ Submodule.span ℚ (Set.range fun j => (ω j : E))) →
    (∀ (E : Type) [Field E] [NumberField E] (X : _root_.ReciprocityTheory.ChartRestriction.G.I2.PT E) (I : Submodule ℤ (_root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp X.dim)), I ≤ X.L → (∀ x ∈ X.L, x ∈ _root_.ReciprocityTheory.ChartRestriction.G.I2.IR I → x ∈ I) → 0 < X.la1 → ∃ x u : Fin (Module.finrank ℝ (_root_.ReciprocityTheory.ChartRestriction.G.I2.IR I)) → _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp X.dim, (∀ j, x j ∈ X.L ∧ _root_.ReciprocityTheory.ChartRestriction.G.I2.IsU I (x j) (u j)) ∧ LinearIndependent ℝ u ∧ ∀ j, ‖u j‖ ≤ (Module.finrank ℝ (_root_.ReciprocityTheory.ChartRestriction.G.I2.IR I) : ℝ) ^ 2 / X.la1) →
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : _root_.ReciprocityTheory.ChartRestriction.G.I2.PT E) (DF : ℕ) (P : _root_.ReciprocityTheory.ChartRestriction.G.I2.Par X DF), X.la1 < P.th → ∃ I, _root_.ReciprocityTheory.ChartRestriction.G.I2.IsSplit P I) := by
  intro hω hshort E _ _ _ X DF P hthin
  obtain ⟨n, ω, hωb, hωs⟩ := hω E
  have hf1 : 1 ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E := le_trans (Nat.one_le_pow _ _ P.hm1) P.hmf
  have hfpos : (0 : ℝ) < _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E := by exact_mod_cast hf1
  have hf1' : (1 : ℝ) ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E := by exact_mod_cast hf1
  have hrd : (16 : ℝ) ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E := P.hrd
  have hrdpos : 0 < _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E := by linarith
  have hf2 : (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 2 ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E := P.hf2
  have hr : 1 ≤ X.r := by
    rcases Nat.eq_zero_or_pos X.r with h | h
    · have := P.hfr
      rw [h, mul_zero] at this
      omega
    · exact h
  obtain ⟨τ, hτ⟩ := P.hm
  obtain ⟨x₀, hx₀L, hx₀⟩ := _root_.ReciprocityTheory.ChartRestriction.G.I2.L_ne_zero X hr τ
  have hne : ∃ x ∈ X.L, x ≠ 0 := ⟨x₀, hx₀L, hx₀⟩
  have hla : 0 < X.la1 := _root_.ReciprocityTheory.ChartRestriction.G.I2.first_minimum_pos X hne
  have hth : 0 < P.th := hla.trans hthin
  have hthdef : P.th = _root_.ReciprocityTheory.ChartRestriction.G.I2.th (E := E) P.q P.R0 := rfl
  have hΩ : 0 < _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar
    exact mul_pos (mul_pos two_pos (by positivity)) hrdpos
  have hd1 : (1 : ℝ) ≤ (_root_.ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) P.m : ℝ) := by
    have : 0 < _root_.ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) P.m := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.dstar
      exact Nat.mul_pos (Nat.mul_pos two_pos hf1) P.hm1
    exact_mod_cast this
  have hΩth : _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) * P.th ^ 2 ≤ 1 := by
    have h1 : (1 : ℝ) ≤ (_root_.ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) P.m : ℝ) ^ 2 := one_le_pow₀ hd1
    have hnn : 0 ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) * P.th ^ 2 := mul_nonneg hΩ.le (sq_nonneg _)
    calc _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) * P.th ^ 2 = 1 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) * P.th ^ 2) := by ring
      _ ≤ (_root_.ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) P.m : ℝ) ^ 2 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) * P.th ^ 2) :=
        mul_le_mul_of_nonneg_right h1 hnn
      _ = (_root_.ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) P.m : ℝ) ^ 2 * _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) * _root_.ReciprocityTheory.ChartRestriction.G.I2.th (E := E) P.q P.R0 ^ 2 := by
        rw [hthdef]; ring
      _ ≤ 1 := P.C1.le
  obtain ⟨I, hG, hthick⟩ := _root_.ReciprocityTheory.ChartRestriction.G.I2.exists_maximal X ω hΩ hth hΩth hωb hωs
  have hshortI : ∀ t, X.la1 < t → t ≤ P.th → ∃ ξ ∈ I, ξ ≠ 0 ∧ ‖ξ‖ < t := by
    intro t ht ht'
    obtain ⟨ξ, hξL, hξ0, hξt⟩ := _root_.ReciprocityTheory.ChartRestriction.G.I2.exists_short X hne ht
    refine ⟨ξ, ?_, hξ0, hξt⟩
    by_contra hξI
    have h1 := hthick ξ hξL hξI
    have h2 : Metric.infDist ξ (_root_.ReciprocityTheory.ChartRestriction.G.I2.IR I : Set (_root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp X.dim)) ≤ ‖ξ‖ := by
      have := Metric.infDist_le_dist_of_mem (x := ξ) (Submodule.zero_mem (_root_.ReciprocityTheory.ChartRestriction.G.I2.IR I))
      rwa [dist_zero_right] at this
    linarith
  have hph : P.ph = 2 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) / (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 * X.la1 ^ 2) := by
    show X.ph P.th = _
    unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.ph
    rw [if_pos hthin]
  obtain ⟨ρ, hρ, hrk⟩ := _root_.ReciprocityTheory.ChartRestriction.G.I2.rank_iso X I hG.le hG.stable hG.iso
  have hρm : ρ ≤ P.m := (hρ τ).trans hτ
  refine ⟨I, _root_.ReciprocityTheory.ChartRestriction.G.I2.IsSplit.mk hG.le (_root_.ReciprocityTheory.ChartRestriction.G.I2.sat_of_IR hG.sat) hG.stable hG.iso ?_ ⟨ρ, hρm, hrk⟩ ?_
    (fun x hx _ hxI => hthick x hx hxI) ?_ ?_ ?_⟩
  · intro x hx
    exact X.eps_iso x (hG.le hx) (fun α => hG.iso _ (hG.stable α x hx) x hx)
  · refine ⟨fun _ => hthin, fun _ hbot => ?_⟩
    obtain ⟨ξ, hξ, hξ0, -⟩ := hshortI P.th hthin le_rfl
    rw [hbot] at hξ
    exact hξ0 ((Submodule.mem_bot ℤ).mp hξ)
  · intro x hx u hu hu0
    have h := hG.sep x hx u hu hu0
    have hq : (1 : ℝ) ≤ P.q := by exact_mod_cast P.hq
    have hR : P.R0 ^ 2 ≠ 0 := by have := P.hR0.1; positivity
    have hM : _root_.ReciprocityTheory.ChartRestriction.G.I2.RR (E := E) = _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 7 := by unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.RR; rfl
    have hth2 : P.th ^ 2 = (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * P.R0 ^ 2 * _root_.ReciprocityTheory.ChartRestriction.G.I2.RR (E := E) ^ 3 / P.q := by
      rw [hthdef]
      unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.th
      rw [Real.sq_sqrt]
      rw [hM]
      have : 0 ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 7 := by positivity
      positivity
    have hΩ2 : _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) ^ 2 = 4 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 3 * _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar
      rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast hfpos.le]
      norm_num
    have hb0 : _root_.ReciprocityTheory.ChartRestriction.G.I2.b0 (E := E) P.q P.R0 = P.q / (P.R0 ^ 2 * _root_.ReciprocityTheory.ChartRestriction.G.I2.RR (E := E) ^ 4) := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.b0; rfl
    have hfr : (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E := by nlinarith
    have hf3 : (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 3 ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 := by
      calc (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 3 = _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 2 := by ring
        _ ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E * _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E := mul_le_mul hfr hf2 (by positivity) hrdpos.le
        _ = _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 := by ring
    have hkey : (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) ^ 2 ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 7 := by
      rw [hΩ2]
      have h4 : (4 : ℝ) ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num) hrd 3]
      have h5 : (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 3 ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 := by
        calc (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 3 = ((_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 2) ^ 2 := by ring
          _ ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hf2 2
      calc (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * (4 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 3 * _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2)
          = 4 * ((_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 3) * _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 := by ring
        _ ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 3 * _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 * _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul h4 h5 (by positivity) (by positivity)) (by positivity)
        _ = _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 7 := by ring
    have hle : _root_.ReciprocityTheory.ChartRestriction.G.I2.b0 (E := E) P.q P.R0 ≤ (1 / (_root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) * P.th)) ^ 2 := by
      rw [div_pow, one_pow, le_div_iff₀ (by positivity), mul_pow, hth2, hb0, hM]
      have hq0 : (P.q : ℝ) ≠ 0 := by positivity
      have hr7 : (0 : ℝ) < _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 7 := by positivity
      have hr7' : _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 7 ≠ 0 := hr7.ne'
      have hrd0 : _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ≠ 0 := hrdpos.ne'
      have hR0 : P.R0 ≠ 0 := fun h0 => hR (by rw [h0]; ring)
      rw [show (P.q : ℝ) / (P.R0 ^ 2 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 7) ^ 4) *
          (_root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) ^ 2 * ((_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * P.R0 ^ 2 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 7) ^ 3 / P.q))
          = (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) ^ 2 / _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 7 by
        field_simp]
      rw [div_le_one hr7]
      exact hkey
    exact hle.trans (pow_le_pow_left₀ (by positivity) h.le 2)
  · have hrd0 : _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ≠ 0 := hrdpos.ne'
    have hf0 : (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ≠ 0 := hfpos.ne'
    have hla0 : X.la1 ≠ 0 := hla.ne'
    obtain ⟨x, u, hxu, hli, hb⟩ := hshort E X I hG.le hG.sat hla
    refine ⟨x, u, hxu, hli, fun j => ?_⟩
    have hdd : (Module.finrank ℝ (_root_.ReciprocityTheory.ChartRestriction.G.I2.IR I) : ℝ) ≤ (_root_.ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) P.m : ℝ) := by
      have : Module.finrank ℝ (_root_.ReciprocityTheory.ChartRestriction.G.I2.IR I) ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) P.m := by
        rw [hrk]
        unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.dstar
        exact Nat.mul_le_mul_left _ hρm
      exact_mod_cast this
    calc ‖u j‖ ^ 2 ≤ ((Module.finrank ℝ (_root_.ReciprocityTheory.ChartRestriction.G.I2.IR I) : ℝ) ^ 2 / X.la1) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hb j) 2
      _ ≤ ((_root_.ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) P.m : ℝ) ^ 2 / X.la1) ^ 2 :=
          pow_le_pow_left₀ (div_nonneg (by positivity) hla.le)
            (div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hdd 2) hla.le) 2
      _ = _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ)) := by
          rw [hph]
          field_simp
  · intro k x u hxu hspan
    have hrd0 : _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ≠ 0 := hrdpos.ne'
    have hla0 : X.la1 ≠ 0 := hla.ne'
    rw [hph]
    have hbound : ∀ t, X.la1 < t → t ≤ P.th →
        2 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) / (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 * t ^ 2) ≤ ∑ j, ‖u j‖ ^ 2 / 2 := by
      intro t ht ht'
      obtain ⟨ξ, hξI, hξ0, hξt⟩ := hshortI t ht ht'
      refine le_trans ?_ (_root_.ReciprocityTheory.ChartRestriction.G.I2.sum_sq_norm_ge_of_span X I hG.le hG.stable hξI hξ0 k x u hxu hspan)
      exact div_le_div_of_nonneg_left (by positivity)
        (mul_pos (pow_pos hrdpos 2) (pow_pos (norm_pos_iff.mpr hξ0) 2))
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hξt.le 2) (sq_nonneg _))
    have hlim : Filter.Tendsto (fun t : ℝ => 2 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) / (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 * t ^ 2))
        (nhdsWithin X.la1 (Set.Ioi X.la1))
        (nhds (2 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) / (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 * X.la1 ^ 2))) := by
      refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
      refine ContinuousAt.tendsto ?_
      exact ContinuousAt.div₀ continuousAt_const (by fun_prop)
        (mul_ne_zero (pow_ne_zero 2 hrd0) (pow_ne_zero 2 hla0))
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT hthin] with t ht
    exact hbound t ht.1 ht.2.le

end

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ThickSplitRealSpanBot
namespace GlobalTheory

open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2
open scoped InnerProductSpace

noncomputable section

theorem thickSplit_realSpan_bot {E : Type} [Field E] [NumberField E] [IsCMField E]
    {dim : (E →+* ℂ) → ℕ} : IR (⊥ : Submodule ℤ (Vsp dim)) = ⊥ := by simp [IR]

theorem thickSplit_bot :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E) (DF : ℕ) (P : Par X DF),
      ¬ X.la1 < P.th → IsSplit P ⊥ := by
  intro E _ _ _ X DF P h
  have h' : ¬ X.la1 < th (E := E) P.q P.R0 := h
  have hph : P.ph = 0 := by rw [Par.ph, PT.ph, if_neg h']
  have hG := Good.bot X 0
  have hfr0 : Module.finrank ℝ (IR (⊥ : Submodule ℤ (Vsp X.dim))) = 0 := by
    rw [thickSplit_realSpan_bot]; exact finrank_bot ℝ _
  refine ⟨bot_le, ?_, hG.stable, hG.iso, ?_, ⟨0, Nat.zero_le _, by rw [hfr0]; ring⟩, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro x _ k hk hkx
    rw [Submodule.mem_bot] at hkx ⊢
    have : (k : ℝ) • x = 0 := by rw [Int.cast_smul_eq_zsmul]; exact hkx
    exact (smul_eq_zero.1 this).resolve_left (by exact_mod_cast hk)
  · intro x hx
    rw [Submodule.mem_bot] at hx
    subst hx
    exact X.eps_iso 0 (Submodule.zero_mem _)
      (fun α => by rw [act_eq_actE, actE_zero_right]; exact Hf_im_zero_left _)
  · simp only [ne_eq, not_true_eq_false, false_iff]
    exact h
  · intro x hx _ hxI
    rw [thickSplit_realSpan_bot, Submodule.bot_coe, Metric.infDist_singleton, dist_zero_right]
    rw [Submodule.mem_bot] at hxI
    exact (le_of_not_gt h).trans (sq_le_Qy_of_le_firstMinimum X hx hxI)
  · intro x _ u hu hne
    exfalso
    have := hu.1
    rw [thickSplit_realSpan_bot, Submodule.mem_bot] at this
    exact hne this
  · haveI : IsEmpty (Fin (Module.finrank ℝ (IR (⊥ : Submodule ℤ (Vsp X.dim))))) := by
      rw [hfr0]; infer_instance
    exact ⟨fun _ => 0, fun _ => 0, fun j => isEmptyElim j, linearIndependent_empty_type,
      fun j => isEmptyElim j⟩
  · intro k x u _ _
    rw [hph]
    exact Finset.sum_nonneg (fun j _ => by positivity)

end

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsShortIndependentIsU
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2
open scoped InnerProductSpace

namespace GlobalTheory

noncomputable section

section lin

variable {E : Type} [Field E] [NumberField E]

variable {dim : (E →+* ℂ) → ℕ}

theorem isU_add_shortIndep {I : Submodule ℤ (Vsp dim)} {x y u v : Vsp dim} (hu : IsU I x u)
    (hv : IsU I y v) : IsU I (x + y) (u + v) :=
  ⟨(IR I).add_mem hu.1 hv.1, fun a ha => by
    rw [inner_add_left, hu.2 a ha, hv.2 a ha, Hf_im_add_left]⟩

theorem isU_zero_shortIndep (I : Submodule ℤ (Vsp dim)) : IsU I 0 0 :=
  ⟨(IR I).zero_mem, fun a _ => by rw [inner_zero_left, Hf_im_zero_left]⟩

theorem isU_zsmul_shortIndep {I : Submodule ℤ (Vsp dim)} {x u : Vsp dim} (k : ℤ) (hu : IsU I x u) :
    IsU I (k • x) (k • u) := by
  rw [← Int.cast_smul_eq_zsmul ℝ k x, ← Int.cast_smul_eq_zsmul ℝ k u]
  exact ⟨(IR I).smul_mem _ hu.1, fun a ha => by
    rw [real_inner_smul_left, hu.2 a ha, Hf_im_smul_left]⟩

end lin

theorem exists_short_independent_isU :
    (∀ (N : ℕ) (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))), DiscreteTopology M → Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin N))) = ⊤ → ∀ lam : ℝ, 0 < lam → (∀ z : EuclideanSpace ℝ (Fin N), (∀ y ∈ M, ∃ k : ℤ, inner ℝ z y = (k : ℝ)) → z ≠ 0 → lam ≤ ‖z‖) → ∃ v : Fin N → EuclideanSpace ℝ (Fin N), (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ (N : ℝ) ^ 2 / lam) → (∀ (E : Type) [Field E] [NumberField E] (X : PT E) (a : Vsp X.dim), ((∀ y ∈ X.L, (Hf y a).im = 0) → a = 0) ∧ ((∀ y ∈ X.L, ∃ k : ℤ, (Hf y a).im = k) → a ∈ X.L)) → (∀ (E : Type) [Field E] [NumberField E] (X : PT E) (I : Submodule ℤ (Vsp X.dim)), I ≤ X.L → (∀ x ∈ X.L, x ∈ IR I → x ∈ I) → 0 < X.la1 → ∃ x u : Fin (Module.finrank ℝ (IR I)) → Vsp X.dim, (∀ j, x j ∈ X.L ∧ IsU I (x j) (u j)) ∧ LinearIndependent ℝ u ∧ ∀ j, ‖u j‖ ≤ (Module.finrank ℝ (IR I) : ℝ) ^ 2 / X.la1) := by
  intro htrans hpair E _ _ X I hle hsat hla
  set K := IR I with hK
  set N := Module.finrank ℝ K with hNdef
  let e : K ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N) := (stdOrthonormalBasis ℝ K).repr
  let M : Submodule ℤ (EuclideanSpace ℝ (Fin N)) :=
    { carrier := {z | ∃ y ∈ X.L, IsU I y ((e.symm z : K) : Vsp X.dim)}
      add_mem' := by
        rintro z z' ⟨y, hy, hu⟩ ⟨y', hy', hu'⟩
        exact ⟨y + y', X.L.add_mem hy hy', by simpa using isU_add_shortIndep hu hu'⟩
      zero_mem' := ⟨0, X.L.zero_mem, by simpa using isU_zero_shortIndep I⟩
      smul_mem' := by
        rintro k z ⟨y, hy, hu⟩
        exact ⟨k • y, X.L.smul_mem k hy, by simpa using isU_zsmul_shortIndep k hu⟩ }
  have hmemM : ∀ y ∈ X.L, ∀ u, IsU I y u → ∃ z ∈ M, ((e.symm z : K) : Vsp X.dim) = u :=
    fun y hy u hu => ⟨e ⟨u, hu.1⟩, ⟨y, hy, by simpa using hu⟩, by simp⟩
  have hinner : ∀ z z' : EuclideanSpace ℝ (Fin N),
      ⟪z, z'⟫_ℝ = ⟪((e.symm z : K) : Vsp X.dim), ((e.symm z' : K) : Vsp X.dim)⟫_ℝ := by
    intro z z'
    rw [← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map]
  have hnormE : ∀ z, ‖((e.symm z : K) : Vsp X.dim)‖ = ‖z‖ := by
    intro z
    rw [← e.symm.norm_map z]
    rfl
  have hdual : ∀ z : EuclideanSpace ℝ (Fin N), (∀ y ∈ M, ∃ k : ℤ, inner ℝ z y = (k : ℝ)) → ((e.symm z : K) : Vsp X.dim) ∈ I := by
    intro z hz
    apply hsat _ ?_ (e.symm z).2
    apply (hpair E X _).2
    intro y hy
    obtain ⟨u, hu⟩ := exists_isU I y
    obtain ⟨z', hz'M, hz'⟩ := hmemM y hy u hu
    obtain ⟨k, hk⟩ := hz z' hz'M
    refine ⟨k, ?_⟩
    rw [← hu.2 _ (e.symm z).2, ← hk, hinner, hz', real_inner_comm]
  have hspan : Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin N))) = ⊤ := by
    rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
    intro z hz
    have h0 : ∀ z' ∈ M, ⟪z', z⟫_ℝ = 0 := fun z' hz' =>
      (Submodule.mem_orthogonal _ _).1 hz z' (Submodule.subset_span hz')
    have ha : ((e.symm z : K) : Vsp X.dim) = 0 := by
      apply (hpair E X _).1
      intro y hy
      obtain ⟨u, hu⟩ := exists_isU I y
      obtain ⟨z', hz'M, hz'⟩ := hmemM y hy u hu
      rw [← hu.2 _ (e.symm z).2, ← hz', ← hinner]
      exact h0 z' hz'M
    have : e.symm z = 0 := Subtype.ext ha
    simpa using congrArg e this

  obtain ⟨s, hsI, hsspan, hsli⟩ := exists_linearIndependent ℝ (I : Set (Vsp X.dim))
  have hsfin : s.Finite := hsli.setFinite
  set A := ∑ a ∈ hsfin.toFinset, ‖a‖ + 1 with hA
  have hApos : 0 < A := by
    have : 0 ≤ ∑ a ∈ hsfin.toFinset, ‖a‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    linarith
  have hlow : ∀ z ∈ M, z ≠ 0 → 1 / A ≤ ‖z‖ := by
    intro z hzM hz0
    obtain ⟨y, hy, hu⟩ := hzM
    set u := ((e.symm z : K) : Vsp X.dim)
    have hu0 : u ≠ 0 := by
      intro h0
      apply hz0
      have : e.symm z = 0 := Subtype.ext h0
      simpa using congrArg e this
    obtain ⟨a, has, ha⟩ : ∃ a ∈ s, ⟪u, a⟫_ℝ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have : ∀ w ∈ Submodule.span ℝ s, ⟪u, w⟫_ℝ = 0 := by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem x hx => exact hcon x hx
        | zero => exact inner_zero_right _
        | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
        | smul r x _ hx => rw [real_inner_smul_right, hx, mul_zero]
      have h1 := this u (by rw [hsspan]; exact hu.1)
      exact hu0 (inner_self_eq_zero.1 h1)
    have h1 : 1 ≤ |⟪u, a⟫_ℝ| := by
      rw [hu.2 a (mem_IR (hsI has))]
      rw [hu.2 a (mem_IR (hsI has))] at ha
      exact one_le_abs_im X hy (hle (hsI has)) ha
    have h2 : |⟪u, a⟫_ℝ| ≤ ‖u‖ * ‖a‖ := abs_real_inner_le_norm _ _
    have h3 : ‖a‖ ≤ A := by
      have := Finset.single_le_sum (f := fun a => ‖a‖) (fun _ _ => norm_nonneg _)
        ((Set.Finite.mem_toFinset hsfin).2 has)
      linarith
    rw [← hnormE z, div_le_iff₀ hApos]
    nlinarith [norm_nonneg u]
  have hdisc : DiscreteTopology M := by
    rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff]
    refine ⟨1 / A, by positivity, fun z hz => ?_⟩
    by_contra hz0
    have h1 := hlow z z.2 (fun h => hz0 (Subtype.ext h))
    rw [dist_zero_right] at hz
    have : ‖(z : EuclideanSpace ℝ (Fin N))‖ = ‖z‖ := rfl
    linarith
  obtain ⟨v, hvM, hvli, hvt⟩ := htrans N M hdisc hspan X.la1 hla (by
    intro z hz hz0
    have ha := hdual z hz
    have hne : ((e.symm z : K) : Vsp X.dim) ≠ 0 := by
      intro h0
      apply hz0
      have : e.symm z = 0 := Subtype.ext h0
      simpa using congrArg e this
    calc X.la1 ≤ ‖((e.symm z : K) : Vsp X.dim)‖ := sq_le_Qy_of_le_firstMinimum X (hle ha) hne
      _ = ‖z‖ := hnormE _)
  choose y hy hyU using hvM
  refine ⟨y, fun j => ((e.symm (v j) : K) : Vsp X.dim), fun j => ⟨hy j, hyU j⟩, ?_, ?_⟩
  · exact (hvli.map' e.symm.toLinearEquiv.toLinearMap (LinearEquiv.ker _)).map' K.subtype
      K.ker_subtype
  · intro j
    rw [hnormE]
    exact hvt j

end

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.PrincipalTorusEqZeroOfImLattice
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2
open scoped InnerProductSpace

namespace GlobalTheory

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem principalTorus_eq_zero_of_im_lattice (X : PT E) {a : Vsp X.dim} (h : ∀ y ∈ X.L, (Hf y a).im = 0) : a = 0 := by
  have hspan : ∀ v, (Hf v a).im = 0 := by
    intro v
    have hv : v ∈ Submodule.span ℝ (X.L : Set (Vsp X.dim)) := by
      have h1 : Submodule.span ℝ (Set.range X.b) ≤ Submodule.span ℝ (X.L : Set (Vsp X.dim)) :=
        Submodule.span_mono (fun z hz => Submodule.subset_span hz)
      rw [X.b.span_eq] at h1
      exact h1 Submodule.mem_top
    exact Hf_im_span_left _ a h v hv
  have h1 := hspan (Complex.I • a)
  have e : -(Complex.I • (Complex.I • a)) = a := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul, neg_neg]
  rw [Hf_im_eq', e] at h1
  exact inner_self_eq_zero.1 h1

theorem principalTorus_mem_lattice_of_int (X : PT E) {a : Vsp X.dim} (h : ∀ y ∈ X.L, ∃ k : ℤ, (Hf y a).im = k) :
    a ∈ X.L := by
  have hfl : ∀ y ∈ X.L, ((⌊(Hf y a).im⌋ : ℤ) : ℝ) = (Hf y a).im := by
    intro y hy
    obtain ⟨k, hk⟩ := h y hy
    rw [hk, Int.floor_intCast]
  let φ : X.L →+ ℤ :=
    { toFun := fun y => ⌊(Hf (y : Vsp X.dim) a).im⌋
      map_zero' := by simp [Hf_im_zero_left]
      map_add' := by
        intro y y'
        apply Int.cast_injective (α := ℝ)
        push_cast
        rw [hfl _ (X.L.add_mem y.2 y'.2), hfl _ y.2, hfl _ y'.2]
        simp only [Hf_im_add_left] }
  obtain ⟨x0, hx0, hφ⟩ := X.perfect φ
  have h0 : a + x0 = 0 := by
    apply principalTorus_eq_zero_of_im_lattice X
    intro y hy
    have := hφ ⟨y, hy⟩
    simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
    rw [hfl y hy] at this
    rw [Hf_im_add_right, this, Hf_im_antisymm x0 y]
    ring
  have : a = -x0 := eq_neg_of_add_eq_zero_left h0
  rw [this]
  exact X.L.neg_mem hx0

theorem principalTorus_im_perfect :
    (∀ (E : Type) [Field E] [NumberField E] (X : PT E) (a : Vsp X.dim),
      ((∀ y ∈ X.L, (Hf y a).im = 0) → a = 0) ∧
        ((∀ y ∈ X.L, ∃ k : ℤ, (Hf y a).im = k) → a ∈ X.L)) :=
  fun _ _ _ X _ => ⟨principalTorus_eq_zero_of_im_lattice X, principalTorus_mem_lattice_of_int X⟩

end

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsBasisSpanEqOfDiscrete
open Module Submodule

namespace GlobalTheory

theorem exists_basis_span_eq_of_discrete {N : ℕ} (M : Submodule ℤ (EuclideanSpace ℝ (Fin N)))
    [DiscreteTopology M] (hM : span ℝ (M : Set (EuclideanSpace ℝ (Fin N))) = ⊤) :
    ∃ b : Basis (Fin N) ℝ (EuclideanSpace ℝ (Fin N)), span ℤ (Set.range b) = M := by
  have : IsZLattice ℝ M := ⟨hM⟩
  have := ZLattice.module_free ℝ M
  have := ZLattice.module_finite ℝ M
  let b1 := (Module.Free.chooseBasis ℤ M).ofZLatticeBasis ℝ M
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ M) = N := by
    rw [← finrank_eq_card_basis b1]
    simp
  refine ⟨b1.reindex (Fintype.equivFinOfCardEq hcard), ?_⟩
  rw [Basis.range_reindex]
  exact Basis.ofZLatticeBasis_span ℝ M _

theorem exists_inner_dual_basis {N : ℕ} (b : Basis (Fin N) ℝ (EuclideanSpace ℝ (Fin N))) :
    ∃ d : Basis (Fin N) ℝ (EuclideanSpace ℝ (Fin N)), ∀ j y, inner ℝ (d j) y = b.repr y j := by
  let w : Fin N → EuclideanSpace ℝ (Fin N) := fun j =>
    (InnerProductSpace.toDual ℝ _).symm (LinearMap.toContinuousLinearMap (b.coord j))
  have hw : ∀ j y, inner ℝ (w j) y = b.repr y j := fun j y => by
    simp [w, InnerProductSpace.toDual_symm_apply]
  have hli : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := congrArg (fun x => inner ℝ x (b i)) hg
    simpa [sum_inner, real_inner_smul_left, hw, Finsupp.single_apply] using this
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' _ hli (by simp), fun j y => ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank', hw]

theorem transference_discrete_lattice :
    ∀ (N : ℕ) (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))), DiscreteTopology M →
      Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin N))) = ⊤ → ∀ lam : ℝ, 0 < lam →
      (∀ z : EuclideanSpace ℝ (Fin N), (∀ y ∈ M, ∃ k : ℤ, inner ℝ z y = (k : ℝ)) → z ≠ 0 →
        lam ≤ ‖z‖) →
      ∃ v : Fin N → EuclideanSpace ℝ (Fin N), (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧
        ∀ j, ‖v j‖ ≤ (N : ℝ) ^ 2 / lam := by
  intro N M _ hM lam hlam hmin
  obtain ⟨b, rfl⟩ := exists_basis_span_eq_of_discrete M hM
  obtain ⟨d, hd⟩ := exists_inner_dual_basis b
  obtain ⟨y, hli, hint, hy⟩ := ReciprocityTheory.ChartRestriction.G.T0.transference_dual d lam hlam (by
    intro x hx hx0
    refine hmin x (fun y hy => ?_) hx0
    obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hx
    obtain ⟨e, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hy
    refine ⟨∑ j, c j * e j, ?_⟩
    simp [sum_inner, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hd,
      Finsupp.single_apply])
  refine ⟨y, fun i => ?_, hli, hy⟩
  rw [b.mem_span_iff_repr_mem ℤ]
  intro j
  obtain ⟨m, hm⟩ := hint i j
  exact ⟨m, by rw [← hd, real_inner_comm, hm]; simp⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.GreedySplittingPrincipalTorusExists
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory

theorem greedy_splitting_exists : SplitStatement := by
  intro E _ _ _ X DF P
  by_cases h : X.la1 < P.th
  · exact greedy_splitting_thin exists_short_integers_span
      (exists_short_independent_isU transference_discrete_lattice principalTorus_im_perfect)
      E X DF P h
  · exact ⟨⊥, thickSplit_bot E X DF P h⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.GreedySplittingPrincipalTorusExistsStatement
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.GlobalTheory.T.greedy_splitting_principal_torus_exists : SplitStatement := by
  first | exact @GlobalTheory.greedy_splitting_exists | exact GlobalTheory.greedy_splitting_exists | (intros; apply GlobalTheory.greedy_splitting_exists <;> assumption)
end
