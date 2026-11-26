module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.GoodHeightExists

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LStructB
noncomputable section

namespace PI.EF

open Complex Filter Topology Set DirichletCharacter

section prim
variable {N : ℕ}

lemma factorsThrough_inv {χ : DirichletCharacter ℂ N} {d : ℕ} (h : χ.FactorsThrough d) :
    (χ⁻¹).FactorsThrough d := by
  obtain ⟨hd, χ₀, hχ⟩ := h
  exact ⟨hd, χ₀⁻¹, by rw [hχ, map_inv]⟩

lemma conductor_inv (χ : DirichletCharacter ℂ N) : (χ⁻¹).conductor = χ.conductor := by
  unfold DirichletCharacter.conductor
  congr 1
  ext d
  simp only [DirichletCharacter.conductorSet, Set.mem_setOf_eq]
  exact ⟨fun h => by simpa using factorsThrough_inv h, factorsThrough_inv⟩

lemma isPrimitive_inv {χ : DirichletCharacter ℂ N} (h : χ.IsPrimitive) : (χ⁻¹).IsPrimitive := by
  have h' : χ.conductor = N := h
  show (χ⁻¹).conductor = N
  rw [conductor_inv, h']

lemma level_eq_one_of_primitive_one [NeZero N] {χ : DirichletCharacter ℂ N} (h : χ.IsPrimitive)
    (h1 : χ = 1) : N = 1 := by
  have h' : χ.conductor = N := h
  rw [h1, DirichletCharacter.conductor_one] at h'
  exact h'.symm

end prim

variable {N : ℕ} [NeZero N]

lemma completed_ne_zero_right (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 ≤ s.re)
    (h1 : χ ≠ 1 ∨ s ≠ 1) : completedLFunction χ s ≠ 0 := by
  intro h0
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have h2 := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)
  rw [h0, zero_div] at h2
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ h1 hs h2

lemma completed_ne_zero_left {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {s : ℂ}
    (hs : s.re ≤ 0) (h1 : χ ≠ 1 ∨ s ≠ 0) : completedLFunction χ s ≠ 0 := by
  intro h0
  have hp := (isPrimitive_inv hχ).completedLFunction_one_sub s
  rw [inv_inv, h0, mul_zero] at hp
  refine completed_ne_zero_right χ⁻¹ (s := 1 - s) (by simp; linarith) ?_ hp
  rcases h1 with h | h
  · left
    exact fun h' => h (inv_eq_one.mp h')
  · right
    intro h'
    apply h
    linear_combination -h'

theorem zeroLocus : ZeroLocus := by
  intro N _ χ hχ s hs hs1 hL
  by_cases hre1 : 1 ≤ s.re
  · exact absurd hL (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hs1) hre1)
  by_cases hre0 : 0 < s.re
  · left
    exact ⟨hre0, by linarith⟩
  push_neg at hre1 hre0
  right
  by_cases hc : s = 0 ∧ χ = 1
  · exfalso
    obtain ⟨rfl, rfl⟩ := hc
    have hN := level_eq_one_of_primitive_one hχ rfl
    subst hN
    rw [DirichletCharacter.LFunction_modOne_eq, riemannZeta_zero] at hL
    norm_num at hL
  have hc' : χ ≠ 1 ∨ s ≠ 0 := by tauto
  have hne := completed_ne_zero_left hχ hre0 hc'
  have hsN : s ≠ 0 ∨ N ≠ 1 := by
    rcases hc' with h | h
    · right
      intro hN
      subst hN
      exact h (DirichletCharacter.level_one χ)
    · left
      exact h
  have hdiv := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s hsN
  rw [hL, eq_comm, div_eq_zero_iff] at hdiv
  rcases hdiv with h | hg
  · exact absurd h hne
  rcases DirichletCharacter.even_or_odd χ with he | ho
  · rw [he.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff] at hg
    obtain ⟨n, hn⟩ := hg
    have hre := congrArg Complex.re hn
    simp at hre
    have hn1 : (n : ℝ) < 1 := by linarith
    have hn0 : n = 0 := by exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast hn1)
    subst hn0
    simp at hn
    refine Or.inl ⟨hn, he, ?_⟩
    intro h1
    exact hc ⟨hn, h1⟩
  · rw [ho.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff] at hg
    obtain ⟨n, hn⟩ := hg
    have hre := congrArg Complex.re hn
    simp at hre
    have hn1 : (n : ℝ) < 1 := by linarith
    have hn0 : n = 0 := by exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast hn1)
    subst hn0
    refine Or.inr ⟨?_, ho⟩
    simp at hn
    linear_combination hn

private lemma exists_differentiable_Gammaℝ_inv_eq_mul : ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ g 0 ≠ 0 ∧
    ∀ z : ℂ, (Gammaℝ z)⁻¹ = z * g z := by
  refine ⟨fun s => (Real.pi : ℂ) ^ (s / 2) * (1 / 2 * (Complex.Gamma (s / 2 + 1))⁻¹), ?_, ?_, ?_⟩
  · refine Differentiable.mul ?_ ?_
    · exact (differentiable_id.div_const (2 : ℂ)).const_cpow
        (Or.inl (by exact_mod_cast Real.pi_ne_zero))
    · exact (differentiable_const _).mul
        (Complex.differentiable_one_div_Gamma.comp ((differentiable_id.div_const (2 : ℂ)).add_const 1))
  · simp [Complex.Gamma_one]
  · intro z
    rw [Complex.Gammaℝ_def, neg_div, Complex.cpow_neg, mul_inv, inv_inv]
    by_cases hz : z = 0
    · subst hz
      simp [Complex.Gamma_zero]
    · have key : (Complex.Gamma (z / 2))⁻¹ = z * (1 / 2 * (Complex.Gamma (z / 2 + 1))⁻¹) := by
        rw [Complex.Gamma_add_one _ (div_ne_zero hz two_ne_zero), mul_inv]
        have h2 : z * (1 / 2) * (z / 2)⁻¹ = 1 := by field_simp
        calc (Complex.Gamma (z / 2))⁻¹
            = (z * (1 / 2) * (z / 2)⁻¹) * (Complex.Gamma (z / 2))⁻¹ := by rw [h2, one_mul]
          _ = _ := by ring
      rw [key]
      ring

theorem mult_zero_of_even {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (he : χ.Even)
    (h1 : χ ≠ 1) : LFunction χ 0 = 0 ∧ analyticOrderNatAt (LFunction χ) 0 = 1 := by
  obtain ⟨g, hgd, hg0, hgz⟩ := exists_differentiable_Gammaℝ_inv_eq_mul
  have hN1 : N ≠ 1 := by
    intro hN
    subst hN
    exact h1 (DirichletCharacter.level_one χ)
  have hLeq : ∀ s, LFunction χ s = completedLFunction χ s * (s * g s) := by
    intro s
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr hN1),
      he.gammaFactor_def, div_eq_mul_inv, hgz]
  have hc0 : completedLFunction χ 0 ≠ 0 := completed_ne_zero_left hχ (by simp) (Or.inl h1)
  have hcd : Differentiable ℂ (completedLFunction χ) :=
    DirichletCharacter.differentiable_completedLFunction h1
  refine ⟨by rw [hLeq]; simp, ?_⟩
  have hLa : AnalyticAt ℂ (LFunction χ) 0 := (DirichletCharacter.differentiable_LFunction h1).analyticAt 0
  have hord : analyticOrderAt (LFunction χ) 0 = ((1 : ℕ) : ℕ∞) := by
    rw [hLa.analyticOrderAt_eq_natCast]
    refine ⟨fun s => completedLFunction χ s * g s, (hcd.mul hgd).analyticAt 0, mul_ne_zero hc0 hg0, ?_⟩
    filter_upwards with z
    rw [hLeq]
    simp only [sub_zero, pow_one, smul_eq_mul]
    ring
  simp [analyticOrderNatAt, hord]

end PI.EF
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LStructA
noncomputable section

namespace PI.EF

open Complex Filter Topology Set

lemma logDeriv_local {f : ℂ → ℂ} {ρ : ℂ} (hf : AnalyticAt ℂ f ρ)
    (hfin : analyticOrderAt f ρ ≠ ⊤) :
    ∃ k : ℂ → ℂ, AnalyticAt ℂ k ρ ∧ ∀ᶠ s in 𝓝[≠] ρ, f s ≠ 0 ∧
      logDeriv f s = (analyticOrderNatAt f ρ : ℂ) / (s - ρ) + k s := by
  have hn : analyticOrderAt f ρ = (analyticOrderNatAt f ρ : ℕ∞) := (Nat.cast_analyticOrderNatAt hfin).symm
  obtain ⟨g, hg, hg0, hfg⟩ := (hf.analyticOrderAt_eq_natCast).1 hn
  refine ⟨fun s => deriv g s / g s, hg.deriv.div hg hg0, ?_⟩
  have hU : ∀ᶠ z in 𝓝 ρ, (∀ᶠ w in 𝓝 z, f w = (w - ρ) ^ analyticOrderNatAt f ρ • g w) ∧
      g z ≠ 0 ∧ AnalyticAt ℂ g z :=
    hfg.eventually_nhds.and ((hg.continuousAt.eventually_ne hg0).and hg.eventually_analyticAt)
  filter_upwards [nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with s hs hsne
  obtain ⟨hfs, hgs, hga⟩ := hs
  have hsr : s - ρ ≠ 0 := sub_ne_zero.2 hsne
  have hpow : (s - ρ) ^ analyticOrderNatAt f ρ ≠ 0 := pow_ne_zero _ hsr
  have hfs' : f s = (s - ρ) ^ analyticOrderNatAt f ρ * g s := by rw [hfs.self_of_nhds, smul_eq_mul]
  refine ⟨by rw [hfs']; exact mul_ne_zero hpow hgs, ?_⟩
  have hd : DifferentiableAt ℂ (fun w : ℂ => w - ρ) s := differentiableAt_id.sub_const ρ
  have hld : logDeriv f s = logDeriv (fun w => (w - ρ) ^ analyticOrderNatAt f ρ * g w) s := by
    rw [logDeriv_apply, logDeriv_apply,
      Filter.EventuallyEq.deriv_eq (hfs.mono fun w hw => by rw [hw, smul_eq_mul]), hfs']
  have hl : logDeriv (fun w : ℂ => w - ρ) s = 1 / (s - ρ) := by
    rw [logDeriv_apply, deriv_sub_const, deriv_id'']
  rw [hld, logDeriv_fun_mul (f := fun w => (w - ρ) ^ analyticOrderNatAt f ρ) s hpow hgs (hd.pow _)
    hga.differentiableAt, logDeriv_fun_pow hd, hl, logDeriv_apply]
  beta_reduce
  ring

theorem exists_regular_part {f : ℂ → ℂ} {K : Set ℂ} (hf : AnalyticOnNhd ℂ f K) (Z : Finset ℂ)
    (hZ0 : ∀ ρ ∈ Z, f ρ = 0) (hK : ∀ s ∈ K, f s = 0 → s ∈ Z)
    (hfin : ∀ ρ ∈ K, analyticOrderAt f ρ ≠ ⊤) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H K ∧ ∀ s ∈ K, f s ≠ 0 →
      logDeriv f s = H s + ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ) := by
  classical
  have hloc : ∀ ρ, ρ ∈ K → ∃ k : ℂ → ℂ, AnalyticAt ℂ k ρ ∧ ∀ᶠ s in 𝓝[≠] ρ, f s ≠ 0 ∧
      logDeriv f s = (analyticOrderNatAt f ρ : ℂ) / (s - ρ) + k s :=
    fun ρ hρ => logDeriv_local (hf ρ hρ) (hfin ρ hρ)
  choose! k hk hkev using hloc
  have hsumA : ∀ (W : Finset ℂ) (s0 : ℂ), s0 ∉ W →
      AnalyticAt ℂ (fun s => ∑ ρ ∈ W, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)) s0 := by
    intro W s0 hW
    have h := Finset.analyticAt_sum (𝕜 := ℂ) (c := s0) W
      (f := fun ρ (s : ℂ) => (analyticOrderNatAt f ρ : ℂ) / (s - ρ))
      (fun ρ hρ => analyticAt_const.div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.2 fun h => hW (h ▸ hρ)))
    convert h using 1
    ext s
    simp [Finset.sum_apply]
  let H : ℂ → ℂ := fun s => if s ∈ Z ∧ s ∈ K then
      k s s - ∑ ρ ∈ Z.erase s, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)
    else logDeriv f s - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)
  refine ⟨H, ?_, ?_⟩
  · intro s0 hs0
    by_cases hz : s0 ∈ Z
    · have hRa : AnalyticAt ℂ
          (fun s => k s0 s - ∑ ρ ∈ Z.erase s0, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)) s0 :=
        (hk s0 hs0).sub (hsumA _ s0 (by simp))
      have h1 := hkev s0 hs0
      rw [eventually_nhdsWithin_iff] at h1
      have h2 : ∀ᶠ s in 𝓝 s0, s ∉ Z.erase s0 :=
        (Z.erase s0).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
      refine hRa.congr ?_
      filter_upwards [h1, h2] with s hs1 hs2
      by_cases hss : s = s0
      · subst hss
        simp only [H, if_pos (And.intro hz hs0)]
      · have hsZ : s ∉ Z := fun h => hs2 (Finset.mem_erase.2 ⟨hss, h⟩)
        obtain ⟨_, hl⟩ := hs1 hss
        simp only [H, hsZ, false_and, if_false]
        rw [hl, ← Finset.add_sum_erase Z _ hz]
        ring
    · have hf0 : f s0 ≠ 0 := fun h => hz (hK s0 hs0 h)
      have h2 : ∀ᶠ s in 𝓝 s0, s ∉ Z :=
        Z.finite_toSet.isClosed.isOpen_compl.mem_nhds (by simpa using hz)
      have hA : AnalyticAt ℂ (fun s => logDeriv f s - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)) s0 := by
        refine AnalyticAt.sub ?_ (hsumA Z s0 hz)
        have e : logDeriv f = fun s => deriv f s / f s := funext fun s => logDeriv_apply f s
        rw [e]
        exact (hf s0 hs0).deriv.div (hf s0 hs0) hf0
      refine hA.congr ?_
      filter_upwards [h2] with s hs
      simp only [H, hs, false_and, if_false]
  · intro s _ hfs
    have hsZ : s ∉ Z := fun h => hfs (hZ0 s h)
    simp only [H, hsZ, false_and, if_false]
    ring

lemma finite_zeros_of_compact {f : ℂ → ℂ} (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0)
    {K : Set ℂ} (hK : IsCompact K) : (K ∩ f ⁻¹' {0}).Finite := by
  by_contra hinf
  obtain ⟨z, _, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf hK Set.inter_subset_left
  have hfr : ∃ᶠ w in 𝓝[≠] z, f w = 0 := by
    rw [accPt_iff_frequently] at hacc
    rw [Filter.Frequently, eventually_nhdsWithin_iff]
    intro h
    apply hacc
    filter_upwards [h] with w hw
    rintro ⟨hne, hw'⟩
    exact hw hne hw'.2
  have h0 := AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (fun w _ => hf.analyticAt w) isPreconnected_univ (Set.mem_univ z) hfr
  exact hx (h0 (Set.mem_univ x))

lemma order_ne_top_of_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0)
    (y : ℂ) : analyticOrderAt f y ≠ ⊤ := by
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  have h0 := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (fun w _ => hf.analyticAt w) isPreconnected_univ (Set.mem_univ y) htop
  exact hx (h0 (Set.mem_univ x))

end PI.EF
end
end

noncomputable section

namespace PI.EF

open Complex Filter Topology Set DirichletCharacter

lemma isCompact_rect (x₀ x₁ y₀ y₁ : ℝ) : IsCompact (rect x₀ x₁ y₀ y₁) :=
  isCompact_Icc.reProdIm isCompact_Icc

lemma mem_rect {x₀ x₁ y₀ y₁ : ℝ} {s : ℂ} :
    s ∈ rect x₀ x₁ y₀ y₁ ↔ (x₀ ≤ s.re ∧ s.re ≤ x₁) ∧ (y₀ ≤ s.im ∧ s.im ≤ y₁) := by
  simp only [rect, Complex.mem_reProdIm, Set.mem_Icc]

variable {N : ℕ} [NeZero N]

def Lent (χ : DirichletCharacter ℂ N) : ℂ → ℂ :=
  open Classical in if χ = 1 then LFunctionTrivChar₁ N else LFunction χ

lemma differentiable_Lent (χ : DirichletCharacter ℂ N) : Differentiable ℂ (Lent χ) := by
  unfold Lent
  split_ifs with h
  · exact differentiable_LFunctionTrivChar₁ N
  · exact differentiable_LFunction h

lemma Lent_of_ne {χ : DirichletCharacter ℂ N} (h : χ ≠ 1) : Lent χ = LFunction χ := by
  unfold Lent
  rw [if_neg h]

lemma Lent_one_apply {χ : DirichletCharacter ℂ N} (h : χ = 1) {s : ℂ} (hs : s ≠ 1) :
    Lent χ s = (s - 1) * LFunction χ s := by
  subst h
  unfold Lent
  rw [if_pos rfl]
  first
    | (rw [LFunctionTrivChar₁, Function.update_of_ne hs]; rfl)
    | (simp [LFunctionTrivChar₁, Function.update_of_ne hs])
    | (simp [LFunctionTrivChar₁, hs])

lemma Lent_two_ne_zero (χ : DirichletCharacter ℂ N) : Lent χ 2 ≠ 0 := by
  have h2 : (2 : ℂ) ≠ 1 := by norm_num
  have hL : LFunction χ 2 ≠ 0 := LFunction_ne_zero_of_one_le_re χ (Or.inr h2) (by norm_num)
  by_cases h : χ = 1
  · rw [Lent_one_apply h h2]
    exact mul_ne_zero (sub_ne_zero.mpr h2) hL
  · rw [Lent_of_ne h]
    exact hL

lemma Lent_one_ne_zero (χ : DirichletCharacter ℂ N) : Lent χ 1 ≠ 0 := by
  by_cases h : χ = 1
  · unfold Lent
    rw [if_pos h]
    exact LFunctionTrivChar₁_apply_one_ne_zero N
  · rw [Lent_of_ne h]
    exact LFunction_ne_zero_of_one_le_re χ (Or.inl h) (by simp)

lemma Lent_eq_zero_iff (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s ≠ 1) :
    Lent χ s = 0 ↔ LFunction χ s = 0 := by
  by_cases h : χ = 1
  · rw [Lent_one_apply h hs, mul_eq_zero]
    simp [sub_eq_zero, hs]
  · rw [Lent_of_ne h]

lemma Lent_eventuallyEq {χ : DirichletCharacter ℂ N} (h : χ = 1) {s : ℂ} (hs : s ≠ 1) :
    Lent χ =ᶠ[𝓝 s] (fun z => z - 1) * LFunction χ := by
  filter_upwards [isOpen_ne.mem_nhds hs] with z hz
  rw [Lent_one_apply h hz]
  rfl

lemma order_Lent (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s ≠ 1) :
    analyticOrderNatAt (Lent χ) s = analyticOrderNatAt (LFunction χ) s := by
  by_cases h : χ = 1
  · have hL : AnalyticAt ℂ (LFunction χ) s := by
      apply DifferentiableOn.analyticAt (s := {z | z ≠ 1})
      · intro z hz
        exact (differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt
      · exact isOpen_ne.mem_nhds hs
    have h1 : AnalyticAt ℂ (fun z : ℂ => z - 1) s := analyticAt_id.sub analyticAt_const
    have h0 : analyticOrderAt (fun z : ℂ => z - 1) s = 0 :=
      h1.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hs)
    unfold analyticOrderNatAt
    rw [analyticOrderAt_congr (Lent_eventuallyEq h hs), analyticOrderAt_mul h1 hL, h0, zero_add]
  · rw [Lent_of_ne h]

lemma logDeriv_Lent (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s ≠ 1) (h0 : LFunction χ s ≠ 0) :
    logDeriv (LFunction χ) s = logDeriv (Lent χ) s - del1 χ / (s - 1) := by
  by_cases h : χ = 1
  · have hd : DifferentiableAt ℂ (LFunction χ) s := differentiableAt_LFunction χ s (Or.inl hs)
    have he := Lent_eventuallyEq h hs
    have h1 : logDeriv (Lent χ) s = logDeriv (fun z => (z - 1) * LFunction χ z) s := by
      unfold logDeriv
      simp only [Pi.div_apply]
      rw [he.deriv_eq, he.eq_of_nhds]
      rfl
    have h2 : logDeriv (fun z : ℂ => z - 1) s = 1 / (s - 1) := by
      simp [logDeriv_apply]
    have hdz : DifferentiableAt ℂ (fun z : ℂ => z - 1) s := differentiableAt_id.sub_const (1 : ℂ)
    rw [h1, logDeriv_fun_mul (f := fun z : ℂ => z - 1) (g := LFunction χ) s
      (sub_ne_zero.mpr hs) h0 hdz hd, h2]
    simp only [del1, if_pos h]
    ring
  · rw [Lent_of_ne h]
    simp [del1, h]

theorem zerosFinite : ZerosFinite := by
  intro N _ χ hχ T
  have h := finite_zeros_of_compact (differentiable_Lent χ) (Lent_two_ne_zero χ)
    (isCompact_rect 0 1 (-T) T)
  refine h.subset ?_
  intro ρ hρ
  obtain ⟨hre0, hre1, him, hL⟩ := hρ
  have h1 : ρ ≠ 1 := fun e => by rw [e] at hre1; simp at hre1
  refine ⟨mem_rect.mpr ⟨⟨hre0.le, hre1.le⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · linarith [neg_abs_le ρ.im]
  · linarith [le_abs_self ρ.im]
  · exact (Lent_eq_zero_iff χ h1).mpr hL

theorem regularPart : RegularPart := by
  intro N _ χ hχ x₁ T' hx₁ hT' hNO
  classical
  have hSfin : (ZerosBelow χ T').Finite := zerosFinite N χ hχ T'

  obtain ⟨E0, hE0⟩ : ∃ E0 : Finset ℂ, E0 = if χ.Even ∧ χ ≠ 1 then {0} else ∅ := ⟨_, rfl⟩
  have hE0mem : ∀ ρ, ρ ∈ E0 ↔ ρ = 0 ∧ χ.Even ∧ χ ≠ 1 := by
    intro ρ
    rw [hE0]
    by_cases he : χ.Even ∧ χ ≠ 1
    · rw [if_pos he, Finset.mem_singleton]
      exact ⟨fun h => ⟨h, he⟩, fun h => h.1⟩
    · rw [if_neg he]
      simp only [Finset.notMem_empty, false_iff]
      exact fun h => he h.2
  have hre1 : ∀ ρ ∈ ZerosBelow χ T', ρ ≠ 1 := by
    intro ρ hρ e
    have h := hρ.2.1
    rw [e] at h
    simp at h
  have hZ0 : ∀ ρ ∈ hSfin.toFinset ∪ E0, Lent χ ρ = 0 := by
    intro ρ hρ
    rcases Finset.mem_union.mp hρ with h | h
    · have h' := hSfin.mem_toFinset.mp h
      exact (Lent_eq_zero_iff χ (hre1 ρ h')).mpr h'.2.2.2
    · obtain ⟨rfl, he, h1⟩ := (hE0mem ρ).mp h
      exact (Lent_eq_zero_iff χ zero_ne_one).mpr (mult_zero_of_even hχ he h1).1
  have hK : ∀ s ∈ rect (-1 / 2) x₁ (-T') T', Lent χ s = 0 → s ∈ hSfin.toFinset ∪ E0 := by
    intro s hs hz
    have hs1 : s ≠ 1 := fun e => Lent_one_ne_zero χ (e ▸ hz)
    have hL : LFunction χ s = 0 := (Lent_eq_zero_iff χ hs1).mp hz
    obtain ⟨⟨hsre0, hsre1⟩, him0, him1⟩ := mem_rect.mp hs
    rcases zeroLocus N χ hχ s (by linarith) hs1 hL with h | h | h
    · apply Finset.mem_union_left
      rw [hSfin.mem_toFinset]
      refine ⟨h.1, h.2, ?_, hL⟩
      have hle : |s.im| ≤ T' := abs_le.mpr ⟨him0, him1⟩
      exact lt_of_le_of_ne hle (hNO s h.1 h.2 hL)
    · exact Finset.mem_union_right _ ((hE0mem s).mpr h)
    · exfalso
      rw [h.1] at hsre0
      norm_num at hsre0
  have hf : AnalyticOnNhd ℂ (Lent χ) (rect (-1 / 2) x₁ (-T') T') := fun x _ =>
    (differentiable_Lent χ).analyticAt x
  have hfin : ∀ ρ ∈ rect (-1 / 2) x₁ (-T') T', analyticOrderAt (Lent χ) ρ ≠ ⊤ := fun ρ _ =>
    order_ne_top_of_entire (differentiable_Lent χ) (Lent_two_ne_zero χ) ρ
  obtain ⟨H, hH, hHeq⟩ := exists_regular_part hf (hSfin.toFinset ∪ E0) hZ0 hK hfin
  refine ⟨H, hH.differentiableOn, ?_⟩
  intro s hs hL0 hs1
  have hLe : Lent χ s ≠ 0 := fun e => hL0 ((Lent_eq_zero_iff χ hs1).mp e)
  have hdisj : Disjoint hSfin.toFinset E0 := by
    rw [Finset.disjoint_left]
    intro ρ h1 h2
    have h1' := (hSfin.mem_toFinset.mp h1).1
    rw [((hE0mem ρ).mp h2).1] at h1'
    simp at h1'
  have hS : ∑ ρ ∈ hSfin.toFinset, (analyticOrderNatAt (Lent χ) ρ : ℂ) / (s - ρ) =
      ∑ ρ ∈ hSfin.toFinset, (mult χ ρ : ℂ) / (s - ρ) := by
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [order_Lent χ (hre1 ρ (hSfin.mem_toFinset.mp hρ))]
  have hE : ∑ ρ ∈ E0, (analyticOrderNatAt (Lent χ) ρ : ℂ) / (s - ρ) = eps0 χ / s := by
    rw [hE0]
    by_cases he : χ.Even ∧ χ ≠ 1
    · rw [if_pos he, Finset.sum_singleton, order_Lent χ zero_ne_one,
        (mult_zero_of_even hχ he.1 he.2).2]
      simp only [eps0, if_pos he]
      simp
    · rw [if_neg he]
      simp only [eps0, if_neg he]
      simp
  rw [logDeriv_Lent χ hs1 hL0, hHeq s hs hLe, Finset.sum_union hdisj,
    finsum_mem_eq_finite_toFinset_sum _ hSfin, hS, hE]
  ring

end PI.EF
