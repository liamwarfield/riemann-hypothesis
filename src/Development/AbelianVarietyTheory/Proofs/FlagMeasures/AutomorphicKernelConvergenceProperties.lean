module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ShellSumMajorant
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

private lemma exp_mul_exp_neg_eq_shell (a : ℝ) (r : ℕ) :
    Real.exp (2 * a * (r + 1)) * Real.exp (-(4 * a * r)) =
      Real.exp (2 * a) * Real.exp (-(2 * a)) ^ r := by
  rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem shell_sum_majorant : ∀ (n q : ℕ) (h : ℝ), 1 ≤ n → 1 ≤ q → 32 * (n : ℝ) ^ 2 * Real.sqrt q ≤ h → AntitoneOn (decE q h) (Set.Ici 0) ∧ (∀ r : ℕ, decE q h r ≤ Real.exp (-(4 * (n : ℝ) ^ 2 * r))) ∧ Summable (fun r : ℕ => Real.exp (2 * (n : ℝ) ^ 2 * (r + 1)) * Real.exp (-(4 * (n : ℝ) ^ 2 * r))) ∧ ∑' r : ℕ, Real.exp (2 * (n : ℝ) ^ 2 * (r + 1)) * Real.exp (-(4 * (n : ℝ) ^ 2 * r)) ≤ 2 * Real.exp (2 * (n : ℝ) ^ 2) := by
  intro n q h hn hq hh
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hsq : 1 ≤ Real.sqrt (q : ℝ) := Real.one_le_sqrt.mpr hq1
  have hsqpos : 0 < Real.sqrt (q : ℝ) := by linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hh0 : 0 ≤ h := by
    have : 0 ≤ 32 * (n : ℝ) ^ 2 * Real.sqrt q := by positivity
    linarith
  have hgeo := fun r : ℕ => exp_mul_exp_neg_eq_shell ((n : ℝ) ^ 2) r
  have h3 : 3 ≤ Real.exp (2 * (n : ℝ) ^ 2) := by
    linarith [Real.add_one_le_exp (2 * (n : ℝ) ^ 2)]
  have he0 : 0 ≤ Real.exp (-(2 * (n : ℝ) ^ 2)) := (Real.exp_pos _).le
  have he : Real.exp (-(2 * (n : ℝ) ^ 2)) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro x hx y hy hxy
    simp only [Set.mem_Ici] at hx hy
    unfold GlobalTheory.Count.decE
    apply Real.exp_le_exp.mpr
    have hm : min (2 * x ^ 2) (x / Real.sqrt q) ≤ min (2 * y ^ 2) (y / Real.sqrt q) := by
      apply min_le_min
      · nlinarith
      · exact div_le_div_of_nonneg_right hxy hsqpos.le
    rw [neg_mul, neg_mul, neg_le_neg_iff]
    exact mul_le_mul_of_nonneg_left hm (by positivity)
  ·
    intro r
    unfold GlobalTheory.Count.decE
    apply Real.exp_le_exp.mpr
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      simp
    · have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
      have hmin : min (2 * (r : ℝ) ^ 2) (r / Real.sqrt q) = r / Real.sqrt q := by
        apply min_eq_right
        have : (r : ℝ) / Real.sqrt q ≤ r := div_le_self (by linarith) hsq
        nlinarith
      rw [hmin, neg_mul]
      apply neg_le_neg
      have hd : 32 * (n : ℝ) ^ 2 ≤ h / Real.sqrt q := by
        rw [le_div_iff₀ hsqpos]
        exact hh
      have := mul_le_mul_of_nonneg_right hd (by linarith : (0 : ℝ) ≤ r)
      have hdiv : h / 8 * (r / Real.sqrt q) = h / Real.sqrt q * r / 8 := by ring
      rw [hdiv]
      linarith
  · rw [funext hgeo]
    exact (summable_geometric_of_lt_one he0 (by linarith)).mul_left _
  ·
    rw [funext hgeo, tsum_mul_left, tsum_geometric_of_lt_one he0 (by linarith)]
    have hinv : (1 - Real.exp (-(2 * (n : ℝ) ^ 2)))⁻¹ ≤ 2 := by
      rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
      linarith
    have := mul_le_mul_of_nonneg_left hinv (Real.exp_pos (2 * (n : ℝ) ^ 2)).le
    linarith

end GlobalTheory.Dec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SummableAndTsumLeOfBoxCount
open Finset

namespace GlobalTheory

theorem summable_and_tsum_le_of_box_count (ι Γ : Type) [Fintype ι] (D : Γ → ι → ℝ) (t : Γ → ℝ)
    (a A c : ℝ) (hA : 0 ≤ A) (hc : 0 ≤ c) (ha : Real.exp (-a) ≤ 1 / 2) (_hD : ∀ γ v, 0 ≤ D γ v)
    (ht : ∀ γ, 0 ≤ t γ ∧ t γ ≤ c * ∏ v, Real.exp (-(2 * a * (⌊D γ v⌋₊ : ℝ))))
    (hN : ∀ r : ι → ℝ, (∀ v, 0 ≤ r v) → {γ | t γ ≠ 0 ∧ ∀ v, D γ v ≤ r v}.Finite ∧
      (({γ | t γ ≠ 0 ∧ ∀ v, D γ v ≤ r v}.ncard : ℕ) : ℝ) ≤ A * Real.exp (a * ∑ v, r v)) :
    Summable t ∧ ∑' γ, t γ ≤ c * A * (2 * Real.exp a) ^ Fintype.card ι := by
  classical
  set q := Real.exp (-a) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by linarith
  have hgeom : ∀ M : ℕ, ∑ k ∈ Finset.range M, q ^ k ≤ 2 := by
    intro M
    calc ∑ k ∈ Finset.range M, q ^ k ≤ ∑' k, q ^ k :=
          (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum _ (fun k _ => pow_nonneg hq0 k)
      _ = (1 - q)⁻¹ := tsum_geometric_of_lt_one hq0 hq1
      _ ≤ 2 := by
          rw [inv_le_comm₀ (by linarith) (by norm_num)]
          linarith
  have hprod : ∀ F : Finset (ι → ℕ), ∑ n ∈ F, ∏ v, q ^ (n v) ≤ 2 ^ Fintype.card ι := by
    intro F
    set M := F.sup (fun n => ∑ v, n v) + 1 with hM
    have hsub : F ⊆ Fintype.piFinset (fun _ : ι => Finset.range M) := by
      intro n hn
      rw [Fintype.mem_piFinset]
      intro v
      rw [Finset.mem_range]
      have h1 : n v ≤ ∑ w, n w :=
        Finset.single_le_sum (fun w _ => Nat.zero_le (n w)) (Finset.mem_univ v)
      have h2 : ∑ w, n w ≤ F.sup (fun n => ∑ v, n v) := Finset.le_sup (f := fun n => ∑ v, n v) hn
      omega
    calc ∑ n ∈ F, ∏ v, q ^ (n v)
        ≤ ∑ n ∈ Fintype.piFinset (fun _ : ι => Finset.range M), ∏ v, q ^ (n v) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun n _ _ => Finset.prod_nonneg (fun v _ => pow_nonneg hq0 _))
      _ = ∏ _v : ι, ∑ k ∈ Finset.range M, q ^ k :=
          (Finset.prod_univ_sum (fun _ => Finset.range M) (fun _ k => q ^ k)).symm
      _ ≤ ∏ _v : ι, (2 : ℝ) :=
          Finset.prod_le_prod₀ (fun v _ => Finset.sum_nonneg (fun k _ => pow_nonneg hq0 k))
            (fun v _ => hgeom M)
      _ = 2 ^ Fintype.card ι := by simp
  have hB : 0 ≤ c * A * (2 * Real.exp a) ^ Fintype.card ι := by positivity
  have hfin : ∀ s : Finset Γ, ∑ γ ∈ s, t γ ≤ c * A * (2 * Real.exp a) ^ Fintype.card ι := by
    intro s
    set φ : Γ → ι → ℕ := fun γ v => ⌊D γ v⌋₊ with hφ
    set s' := s.filter (fun γ => t γ ≠ 0) with hs'
    rw [← Finset.sum_filter_ne_zero]
    rw [← Finset.sum_fiberwise_of_maps_to (t := s'.image φ) (g := φ)
      (fun γ hγ => Finset.mem_image_of_mem φ hγ)]
    have hfib : ∀ n : ι → ℕ, ∑ γ ∈ s'.filter (fun γ => φ γ = n), t γ ≤
        c * A * Real.exp (a * Fintype.card ι) * ∏ v, q ^ (n v) := by
      intro n
      set Fn := s'.filter (fun γ => φ γ = n) with hFn
      set e : ℝ := c * ∏ v, Real.exp (-(2 * a * (n v : ℝ))) with he_def
      have he : 0 ≤ e := by positivity
      have h1 : ∑ γ ∈ Fn, t γ ≤ Fn.card * e := by
        calc ∑ γ ∈ Fn, t γ ≤ ∑ _γ ∈ Fn, e := by
              apply Finset.sum_le_sum
              intro γ hγ
              have hn : φ γ = n := (Finset.mem_filter.1 hγ).2
              have hfl : ∀ v, ⌊D γ v⌋₊ = n v := fun v => congrFun hn v
              have h := (ht γ).2
              simp only [hfl] at h
              exact h
          _ = Fn.card * e := by rw [Finset.sum_const, nsmul_eq_mul]
      set r : ι → ℝ := fun v => (n v : ℝ) + 1 with hr_def
      have hr : ∀ v, 0 ≤ r v := fun v => by positivity
      obtain ⟨hSf, hSc⟩ := hN r hr
      have hsub : (↑Fn : Set Γ) ⊆ {γ | t γ ≠ 0 ∧ ∀ v, D γ v ≤ r v} := by
        intro γ hγ
        have hm := Finset.mem_filter.1 (Finset.mem_coe.1 hγ)
        have hm' := Finset.mem_filter.1 hm.1
        refine ⟨hm'.2, fun v => ?_⟩
        have hfl : ⌊D γ v⌋₊ = n v := congrFun hm.2 v
        have hl := Nat.lt_floor_add_one (D γ v)
        rw [hfl] at hl
        exact hl.le
      have hcard : (Fn.card : ℝ) ≤ A * Real.exp (a * ∑ v, r v) := by
        have hc' := Set.ncard_le_ncard hsub hSf
        rw [Set.ncard_coe_finset] at hc'
        exact le_trans (by exact_mod_cast hc') hSc
      have hS2 : ∑ v, 2 * a * (n v : ℝ) = 2 * a * ∑ v, (n v : ℝ) := by rw [Finset.mul_sum]
      have hS3 : ∑ v, (n v : ℝ) * -a = (∑ v, (n v : ℝ)) * -a := by rw [Finset.sum_mul]
      have hS1 : ∑ v, r v = ∑ v, (n v : ℝ) + Fintype.card ι := by
        simp only [hr_def, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, mul_one]
      calc ∑ γ ∈ Fn, t γ ≤ Fn.card * e := h1
        _ ≤ A * Real.exp (a * ∑ v, r v) * e := mul_le_mul_of_nonneg_right hcard he
        _ = c * A * Real.exp (a * Fintype.card ι) * ∏ v, q ^ (n v) := by
            rw [he_def, hq]
            simp_rw [← Real.exp_nat_mul]
            rw [← Real.exp_sum, ← Real.exp_sum, Finset.sum_neg_distrib, hS2, hS3, hS1]
            rw [show A * Real.exp (a * (∑ v, (n v : ℝ) + Fintype.card ι)) *
                  (c * Real.exp (-(2 * a * ∑ v, (n v : ℝ)))) =
                c * A * (Real.exp (a * (∑ v, (n v : ℝ) + Fintype.card ι)) *
                  Real.exp (-(2 * a * ∑ v, (n v : ℝ)))) by ring,
              show c * A * Real.exp (a * Fintype.card ι) * Real.exp ((∑ v, (n v : ℝ)) * -a) =
                c * A * (Real.exp (a * Fintype.card ι) * Real.exp ((∑ v, (n v : ℝ)) * -a)) by ring,
              ← Real.exp_add, ← Real.exp_add]
            congr 2
            ring
    calc ∑ n ∈ s'.image φ, ∑ γ ∈ s'.filter (fun γ => φ γ = n), t γ
        ≤ ∑ n ∈ s'.image φ, c * A * Real.exp (a * Fintype.card ι) * ∏ v, q ^ (n v) :=
          Finset.sum_le_sum (fun n _ => hfib n)
      _ = c * A * Real.exp (a * Fintype.card ι) * ∑ n ∈ s'.image φ, ∏ v, q ^ (n v) := by
          rw [Finset.mul_sum]
      _ ≤ c * A * Real.exp (a * Fintype.card ι) * 2 ^ Fintype.card ι :=
          mul_le_mul_of_nonneg_left (hprod _) (by positivity)
      _ = c * A * (2 * Real.exp a) ^ Fintype.card ι := by
          rw [mul_pow, ← Real.exp_nat_mul, mul_comm (Fintype.card ι : ℝ) a]
          ring
  exact ⟨summable_of_sum_le (fun γ => (ht γ).1) hfin, tsum_le_of_sum_le' hB hfin⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesKernelSummableWithBound
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesKernelSummableWithBound
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

theorem decE_dOp_le_floor {n : ℕ} (hn : 1 ≤ n) (ε : Fin n → Bool) (h : ℝ)
    (hh : 32 * (n : ℝ) ^ 2 * Real.sqrt (rkR ε) ≤ h) (g : UJ ε) :
    decE (rkR ε) h (dOp (uMat g)) ≤ Real.exp (-(2 * (2 * (n : ℝ) ^ 2) * (⌊dOp (uMat g)⌋₊ : ℝ))) := by
  rcases Nat.eq_zero_or_pos (rkR ε) with h0 | hq
  · simp [GlobalTheory.Count.Majorant.dOp_eq_zero ε h0 g, decE]
  · obtain ⟨ha, hb, -⟩ := shell_sum_majorant n (rkR ε) h hn hq hh
    have hp : 0 ≤ dOp (uMat g) := ((GlobalTheory.Count.Cartan.cartan_distances n ε).2.1 g g hn).1
    refine (ha (Set.mem_Ici.2 (Nat.cast_nonneg _)) (Set.mem_Ici.2 hp) (Nat.floor_le hp)).trans ?_
    refine (hb _).trans (le_of_eq ?_)
    congr 2
    ring

theorem norm_phe_le_floor (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ) (hd : IsDSData B d)
    (hn : 1 ≤ B.I.n) (hl : LocDec B h) (hb : HBig B 32 h) (g : B.I.GA) :
    ‖phe B d g‖ ≤ ((∏ v, d v) * (B.e 1).re) *
      ∏ v, Real.exp (-(2 * (2 * (B.I.n : ℝ) ^ 2) * (⌊dOp (uMat (g.1 v))⌋₊ : ℝ))) := by
  obtain ⟨-, he0, he, -⟩ := GlobalTheory.rowsAut_idem_elementary B
  have hd0 : 0 ≤ ∏ v, d v := Finset.prod_nonneg fun v _ => (hd v).2.2.2.1.le
  have h1 : ‖∏ v, ⟪B.w v, B.σ v (uMat (g.1 v)) (B.w v)⟫_ℂ‖ ≤
      ∏ v, Real.exp (-(2 * (2 * (B.I.n : ℝ) ^ 2) * (⌊dOp (uMat (g.1 v))⌋₊ : ℝ))) := by
    rw [norm_prod]
    exact Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) fun v _ =>
      (hl v _).trans (decE_dOp_le_floor hn _ h (hb v) _)
  unfold phe ph
  rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_of_nonneg hd0, mul_assoc, mul_assoc,
    mul_comm (B.e 1).re]
  exact mul_le_mul_of_nonneg_left (mul_le_mul h1 (he _) (norm_nonneg _) ((norm_nonneg _).trans h1)) hd0

theorem kernel_abs_bound : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n → LocDec B h → HBig B 32 h → ∀ x y : B.I.GA, Summable (fun γ : B.I.GFset => ‖phe B d (x⁻¹ * γ.1 * y)‖) ∧ ∑' γ : B.I.GFset, ‖phe B d (x⁻¹ * γ.1 * y)‖ ≤ kerC B d * (tau1 B.I x * tau1 B.I y)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) := by
  intro B d h hd hn hl hb x y
  obtain ⟨-, he0, -, -⟩ := GlobalTheory.rowsAut_idem_elementary B
  have hd0 : 0 ≤ ∏ v, d v := Finset.prod_nonneg fun v _ => (hd v).2.2.2.1.le
  have ht := (GlobalTheory.T.truncatedLeastLatticeSize_lipschitz_properties B.I hn).1
  have hx := ht x
  have hy := ht y
  have hn' : (1 : ℝ) ≤ B.I.n := by exact_mod_cast hn
  have ha : (1 : ℝ) ≤ 2 * (B.I.n : ℝ) ^ 2 := by nlinarith
  have hexp : (2 : ℝ) ≤ Real.exp (2 * (B.I.n : ℝ) ^ 2) := by
    have := Real.add_one_le_exp (2 * (B.I.n : ℝ) ^ 2)
    linarith
  have hA : 0 ≤ (3 * Real.sqrt B.I.n / (tau1 B.I x * tau1 B.I y)) ^ (2 * B.I.n ^ 2 * B.I.f) := by positivity
  have hc : 0 ≤ (∏ v, d v) * (B.e 1).re := mul_nonneg hd0 he0
  obtain ⟨hs, hle⟩ := GlobalTheory.summable_and_tsum_le_of_box_count (InfinitePlace B.I.F) B.I.GFset
    (fun γ v => dOp (uMat ((x⁻¹ * γ.1 * y).1 v))) (fun γ => ‖phe B d (x⁻¹ * γ.1 * y)‖)
    (2 * (B.I.n : ℝ) ^ 2) _ _ hA hc
    (by rw [Real.exp_neg, one_div]; exact inv_anti₀ two_pos hexp)
    (fun γ v => ((GlobalTheory.Count.Cartan.cartan_distances B.I.n _).2.1 _ 1 hn).1)
    (fun γ => ⟨norm_nonneg _, norm_phe_le_floor B d h hd hn hl hb _⟩)
    (by
      intro r hr
      obtain ⟨hf, hcnt⟩ := GlobalTheory.T.count_rational_elements_bounded_distance B.I x y r hn hr
      have hsub : Subtype.val '' {γ : B.I.GFset | ‖phe B d (x⁻¹ * γ.1 * y)‖ ≠ 0 ∧
            ∀ v, dOp (uMat ((x⁻¹ * γ.1 * y).1 v)) ≤ r v} ⊆
          {γ ∈ B.I.GFset | (x⁻¹ * γ * y).2 ∈ B.I.Kset ∧ ∀ v, dOp (uMat ((x⁻¹ * γ * y).1 v)) ≤ r v} := by
        rintro _ ⟨γ, ⟨h1, h2⟩, rfl⟩
        refine ⟨γ.2, B.e_adm.2.2.2.2.1 _ fun h0 => h1 ?_, h2⟩
        unfold phe
        rw [h0, mul_zero, norm_zero]
      refine ⟨Set.Finite.of_finite_image (hf.subset hsub) Subtype.val_injective.injOn, le_trans ?_ hcnt⟩
      rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
      exact_mod_cast Set.ncard_le_ncard hsub hf)
  refine ⟨hs, hle.trans ?_⟩
  have hcard : Fintype.card (InfinitePlace B.I.F) ≤ B.I.f := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank B.I.F
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces B.I.F
    unfold AutInst.f
    omega
  refine (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) hcard) (mul_nonneg hc hA)).trans
    (le_of_eq ?_)
  unfold kerC
  rw [div_eq_mul_inv, mul_pow (3 * Real.sqrt B.I.n)]
  ring

end GlobalTheory.Dec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesKernelSummableWithBoundStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeriesKernel_summable_with_bound : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n → LocDec B h → HBig B 32 h → ∀ x y : B.I.GA, Summable (fun γ : B.I.GFset => ‖phe B d (x⁻¹ * γ.1 * y)‖) ∧ ∑' γ : B.I.GFset, ‖phe B d (x⁻¹ * γ.1 * y)‖ ≤ kerC B d * (tau1 B.I x * tau1 B.I y)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) := by
  first | exact @GlobalTheory.Dec.kernel_abs_bound | exact GlobalTheory.Dec.kernel_abs_bound | (intros; apply GlobalTheory.Dec.kernel_abs_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousAutomorphicKernelDiscreteSeriesTest
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousAutomorphicKernelDiscreteSeriesTest
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

theorem decE_dOp_le_exp_floor {n : ℕ} (ε : Fin n → Bool) (h : ℝ) (hn : 1 ≤ n)
    (hh : 32 * (n : ℝ) ^ 2 * Real.sqrt (rkR ε) ≤ h) (g : Formalism.REAL.UJ ε) :
    decE (rkR ε) h (dOp (uMat g)) ≤ Real.exp (-(4 * (n : ℝ) ^ 2 * (⌊dOp (uMat g)⌋₊ : ℝ))) := by
  obtain ⟨-, hHS, -, -, -⟩ := GlobalTheory.Count.Cartan.cartan_distances n ε
  obtain ⟨hd0, -, -, hle, hge⟩ := hHS g g hn
  set d := dOp (uMat g) with hd
  rcases Nat.eq_zero_or_pos (rkR ε) with h0 | hq
  ·
    have hz : d = 0 := by
      have h1 : dHS (uMat g) ≤ 0 := by simpa [h0] using hge
      have h2 : Real.sqrt 2 * d ≤ 0 := hle.trans h1
      have h3 : d ≤ 0 := by
        by_contra hc
        have : 0 < Real.sqrt 2 * d := mul_pos (by positivity) (lt_of_not_ge hc)
        linarith
      exact le_antisymm h3 hd0
    simp [decE, hz, h0]
  · obtain ⟨hanti, hint, -, -⟩ := shell_sum_majorant n (rkR ε) h hn hq hh
    have hfl : ((⌊d⌋₊ : ℕ) : ℝ) ≤ d := Nat.floor_le hd0
    calc decE (rkR ε) h d ≤ decE (rkR ε) h (⌊d⌋₊ : ℕ) :=
          hanti (Set.mem_Ici.mpr (Nat.cast_nonneg _)) (Set.mem_Ici.mpr hd0) hfl
      _ ≤ _ := hint _

theorem continuous_kern_phe : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n →
    LocDec B h → HBig B 32 h → Continuous (fun p : B.I.GA × B.I.GA => kern B.I (phe B d) p.1 p.2) := by
  intro B d h hd hn hl hb
  classical
  obtain ⟨-, he1, he, hec⟩ := GlobalTheory.rowsAut_idem_elementary B
  obtain ⟨hphc, hphm, -⟩ := GlobalTheory.T.discrete_series_coefficient_integrable_majorant B d h hd hl
  obtain ⟨-, -, -, -, hsupp, -, -⟩ := B.e_adm
  have hC := fun v => GlobalTheory.Count.Cartan.cartan_distances B.I.n (B.I.ε v)

  have hKmul : ∀ a w b : B.I.Gf, a ∈ B.I.Kset → w ∈ B.I.Kset → b ∈ B.I.Kset →
      a * w * b⁻¹ ∈ B.I.Kset := by
    intro a w b ha hw hbm
    simp only [AutInst.Kset, Set.mem_ofPred_eq] at ha hw hbm ⊢
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using mul_mem (mul_mem ha hw) (inv_mem hbm)

  obtain ⟨K1, hK1o, hK1one, hK1K⟩ : ∃ K1 : Set B.I.Gf, IsOpen K1 ∧ (1 : B.I.Gf) ∈ K1 ∧ K1 ⊆ B.I.Kset := by
    refine ⟨_, B.I.topf_open 1 le_rfl, ?_, ?_⟩
    · refine ⟨one_mem _, fun y _ => ⟨0, zero_mem _, ?_⟩⟩
      simp
    · intro x hx
      exact hx.1
  obtain ⟨Mv, hMv⟩ : ∃ Mv : InfinitePlace B.I.F → ℝ,
      ∀ v, Mv v = dOp (uMat (1 : Formalism.REAL.UJ (B.I.ε v))) + 1 := ⟨_, fun v => rfl⟩
  rw [continuous_iff_continuousAt]
  rintro ⟨x0, y0⟩

  have c1 : Continuous fun p : B.I.GA × B.I.GA => x0⁻¹ * p.1 := continuous_const.mul continuous_fst
  have c2 : Continuous fun p : B.I.GA × B.I.GA => y0⁻¹ * p.2 := continuous_const.mul continuous_snd
  have hNn : {p : B.I.GA × B.I.GA | (∀ v, dOp (uMat ((x0⁻¹ * p.1).1 v)) < Mv v) ∧ (x0⁻¹ * p.1).2 ∈ K1 ∧
      (∀ v, dOp (uMat ((y0⁻¹ * p.2).1 v)) < Mv v) ∧ (y0⁻¹ * p.2).2 ∈ K1} ∈ nhds (x0, y0) := by
    have e1 : ∀ᶠ p in nhds (x0, y0), ∀ v, dOp (uMat (((x0⁻¹ * p.1) : B.I.GA).1 v)) < Mv v := by
      rw [Filter.eventually_all]
      intro v
      have hc : Continuous fun p : B.I.GA × B.I.GA => dOp (uMat ((x0⁻¹ * p.1).1 v)) :=
        (hC v).2.2.2.2.comp ((continuous_apply v).comp (continuous_fst.comp c1))
      have h0 : dOp (uMat ((x0⁻¹ * (x0, y0).1).1 v)) < Mv v := by simp [hMv]
      exact (hc.tendsto (x0, y0)).eventually (eventually_lt_nhds h0)
    have e2 : ∀ᶠ p in nhds (x0, y0), (x0⁻¹ * p.1).2 ∈ K1 :=
      ((continuous_snd.comp c1).tendsto (x0, y0)).eventually (hK1o.mem_nhds (by simpa using hK1one))
    have e3 : ∀ᶠ p in nhds (x0, y0), ∀ v, dOp (uMat (((y0⁻¹ * p.2) : B.I.GA).1 v)) < Mv v := by
      rw [Filter.eventually_all]
      intro v
      have hc : Continuous fun p : B.I.GA × B.I.GA => dOp (uMat ((y0⁻¹ * p.2).1 v)) :=
        (hC v).2.2.2.2.comp ((continuous_apply v).comp (continuous_fst.comp c2))
      have h0 : dOp (uMat ((y0⁻¹ * (x0, y0).2).1 v)) < Mv v := by simp [hMv]
      exact (hc.tendsto (x0, y0)).eventually (eventually_lt_nhds h0)
    have e4 : ∀ᶠ p in nhds (x0, y0), (y0⁻¹ * p.2).2 ∈ K1 :=
      ((continuous_snd.comp c2).tendsto (x0, y0)).eventually (hK1o.mem_nhds (by simpa using hK1one))
    filter_upwards [e1, e2, e3, e4] with p h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩

  set n := B.I.n with hnn
  set C' : ℝ := |∏ v, d v| * (B.e 1).re * ∏ v, Real.exp (4 * (n : ℝ) ^ 2 * (1 + 2 * Mv v)) with hC'
  have hC'0 : 0 ≤ C' :=
    mul_nonneg (mul_nonneg (abs_nonneg _) he1) (Finset.prod_nonneg fun v _ => (Real.exp_pos _).le)
  set D : B.I.GFset → InfinitePlace B.I.F → ℝ := fun γ v => dOp (uMat ((x0⁻¹ * γ.1 * y0).1 v)) with hD
  set t : B.I.GFset → ℝ := fun γ => if (x0⁻¹ * γ.1 * y0).2 ∈ B.I.Kset then
      C' * ∏ v, Real.exp (-(2 * (2 * (n : ℝ) ^ 2) * (⌊D γ v⌋₊ : ℝ))) else 0 with ht
  have ht0 : ∀ γ, 0 ≤ t γ ∧ t γ ≤ C' * ∏ v, Real.exp (-(2 * (2 * (n : ℝ) ^ 2) * (⌊D γ v⌋₊ : ℝ))) := by
    intro γ
    have hp : 0 ≤ C' * ∏ v, Real.exp (-(2 * (2 * (n : ℝ) ^ 2) * (⌊D γ v⌋₊ : ℝ))) :=
      mul_nonneg hC'0 (Finset.prod_nonneg fun v _ => (Real.exp_pos _).le)
    by_cases hK : (x0⁻¹ * γ.1 * y0).2 ∈ B.I.Kset
    · simp only [ht, if_pos hK]
      exact ⟨hp, le_rfl⟩
    · simp only [ht, if_neg hK]
      exact ⟨le_rfl, hp⟩
  have hDnn : ∀ γ v, 0 ≤ D γ v := fun γ v => ((hC v).2.1 ((x0⁻¹ * γ.1 * y0).1 v) 1 hn).1
  have ha : Real.exp (-(2 * (n : ℝ) ^ 2)) ≤ 1 / 2 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : Real.exp (-(2 * (n : ℝ) ^ 2)) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by nlinarith)
    have h2 : (1 + 1 : ℝ) ≤ Real.exp 1 := Real.add_one_le_exp 1
    have h3 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
    have h4 := Real.exp_pos (-1)
    nlinarith
  have hA : 0 ≤ (3 * Real.sqrt n / (tau1 B.I x0 * tau1 B.I y0)) ^ (2 * n ^ 2 * B.I.f) :=
    Even.pow_nonneg ⟨n ^ 2 * B.I.f, by ring⟩ _
  have hcount : ∀ r : InfinitePlace B.I.F → ℝ, (∀ v, 0 ≤ r v) →
      {γ | t γ ≠ 0 ∧ ∀ v, D γ v ≤ r v}.Finite ∧
      (({γ | t γ ≠ 0 ∧ ∀ v, D γ v ≤ r v}.ncard : ℕ) : ℝ) ≤
        (3 * Real.sqrt n / (tau1 B.I x0 * tau1 B.I y0)) ^ (2 * n ^ 2 * B.I.f) *
          Real.exp (2 * (n : ℝ) ^ 2 * ∑ v, r v) := by
    intro r hr
    obtain ⟨hfin, hcard⟩ := GlobalTheory.T.count_rational_elements_bounded_distance B.I x0 y0 r hn hr
    have hsub : {γ | t γ ≠ 0 ∧ ∀ v, D γ v ≤ r v} ⊆ Subtype.val ⁻¹'
        {γ ∈ B.I.GFset | (x0⁻¹ * γ * y0).2 ∈ B.I.Kset ∧ ∀ v, dOp (uMat ((x0⁻¹ * γ * y0).1 v)) ≤ r v} := by
      rintro γ ⟨htγ, hrγ⟩
      refine ⟨γ.2, ?_, hrγ⟩
      by_contra hK
      exact htγ (by simp only [ht, if_neg hK])
    have hpre := Set.Finite.preimage (f := (Subtype.val : B.I.GFset → B.I.GA)) Subtype.val_injective.injOn hfin
    refine ⟨hpre.subset hsub, ?_⟩
    calc (({γ | t γ ≠ 0 ∧ ∀ v, D γ v ≤ r v}.ncard : ℕ) : ℝ)
        ≤ ((Subtype.val ⁻¹' {γ ∈ B.I.GFset | (x0⁻¹ * γ * y0).2 ∈ B.I.Kset ∧
            ∀ v, dOp (uMat ((x0⁻¹ * γ * y0).1 v)) ≤ r v}).ncard : ℝ) :=
          Nat.cast_le.mpr (Set.ncard_le_ncard hsub hpre)
      _ = (({γ ∈ B.I.GFset | (x0⁻¹ * γ * y0).2 ∈ B.I.Kset ∧
            ∀ v, dOp (uMat ((x0⁻¹ * γ * y0).1 v)) ≤ r v}.ncard : ℕ) : ℝ) := by
          apply congrArg (fun k : ℕ => (k : ℝ))
          apply Set.ncard_preimage_of_injective_subset_range Subtype.val_injective
          intro γ hγ
          exact ⟨⟨γ, hγ.1⟩, rfl⟩
      _ ≤ _ := hcard
  obtain ⟨hsum, -⟩ := GlobalTheory.summable_and_tsum_le_of_box_count (InfinitePlace B.I.F) B.I.GFset D t
    (2 * (n : ℝ) ^ 2) _ C' hA hC'0 ha hDnn ht0 hcount

  have hcγ : ∀ γ : B.I.GFset, Continuous fun p : B.I.GA × B.I.GA => phe B d (p.1⁻¹ * γ.1 * p.2) := by
    intro γ
    have hm : Continuous fun p : B.I.GA × B.I.GA => p.1⁻¹ * γ.1 * p.2 :=
      (continuous_fst.inv.mul continuous_const).mul continuous_snd
    exact (hphc.comp (continuous_fst.comp hm)).mul (hec.comp (continuous_snd.comp hm))

  have hbound : ∀ γ : B.I.GFset, ∀ p ∈ {p : B.I.GA × B.I.GA | (∀ v, dOp (uMat ((x0⁻¹ * p.1).1 v)) < Mv v) ∧
      (x0⁻¹ * p.1).2 ∈ K1 ∧ (∀ v, dOp (uMat ((y0⁻¹ * p.2).1 v)) < Mv v) ∧ (y0⁻¹ * p.2).2 ∈ K1},
      ‖phe B d (p.1⁻¹ * γ.1 * p.2)‖ ≤ t γ := by
    rintro γ ⟨x, y⟩ ⟨hax, hKx, hby, hKy⟩
    simp only at hax hKx hby hKy ⊢
    set a := x0⁻¹ * x with ha'
    set b := y0⁻¹ * y with hb'
    set w := x⁻¹ * γ.1 * y with hw
    have hz : x0⁻¹ * γ.1 * y0 = a * w * b⁻¹ := by rw [ha', hb', hw]; group
    have hphe : ‖phe B d w‖ = ‖ph B d w.1‖ * ‖B.e w.2‖ := norm_mul _ _
    rw [hphe]
    by_cases hew : B.e w.2 = 0
    · rw [hew, norm_zero, mul_zero]
      exact (ht0 γ).1
    have hzK : (x0⁻¹ * γ.1 * y0).2 ∈ B.I.Kset := by
      rw [hz]
      exact hKmul a.2 w.2 b.2 (hK1K hKx) (hsupp _ hew) (hK1K hKy)
    simp only [ht, if_pos hzK]

    have hmaj : ‖ph B d w.1‖ ≤ |∏ v, d v| *
        ∏ v, Real.exp (-(4 * (n : ℝ) ^ 2 * (⌊dOp (uMat (w.1 v))⌋₊ : ℝ))) := by
      refine (hphm w.1).trans ?_
      simp only [majPh]
      refine mul_le_mul (le_abs_self _) ?_ (Finset.prod_nonneg fun v _ => (Real.exp_pos _).le)
        (abs_nonneg _)
      refine Finset.prod_le_prod₀ (fun v _ => (Real.exp_pos _).le) fun v _ => ?_
      exact decE_dOp_le_exp_floor (B.I.ε v) h hn (hb v) (w.1 v)
    have hshift : ∀ v, Real.exp (-(4 * (n : ℝ) ^ 2 * (⌊dOp (uMat (w.1 v))⌋₊ : ℝ))) ≤
        Real.exp (4 * (n : ℝ) ^ 2 * (1 + 2 * Mv v)) *
          Real.exp (-(2 * (2 * (n : ℝ) ^ 2) * (⌊D γ v⌋₊ : ℝ))) := by
      intro v
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      obtain ⟨hnn0, hinv, -⟩ := (hC v).2.1 (b.1 v) (b.1 v) hn
      have htri1 := ((hC v).2.1 (a.1 v * w.1 v) (b.1 v)⁻¹ hn).2.2.1
      have htri2 := ((hC v).2.1 (a.1 v) (w.1 v) hn).2.2.1
      have hzv : (x0⁻¹ * γ.1 * y0).1 v = a.1 v * w.1 v * (b.1 v)⁻¹ := by rw [hz]; rfl
      have hDz : D γ v ≤ dOp (uMat (a.1 v)) + dOp (uMat (w.1 v)) + dOp (uMat (b.1 v)) := by
        simp only [hD, hzv]
        linarith
      have hwnn : 0 ≤ dOp (uMat (w.1 v)) := ((hC v).2.1 (w.1 v) (w.1 v) hn).1
      have hfz : ((⌊D γ v⌋₊ : ℕ) : ℝ) ≤ D γ v := Nat.floor_le (hDnn γ v)
      have hfw : dOp (uMat (w.1 v)) < (⌊dOp (uMat (w.1 v))⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      have hav := hax v
      have hbv := hby v
      have hkey : ((⌊D γ v⌋₊ : ℕ) : ℝ) ≤ (⌊dOp (uMat (w.1 v))⌋₊ : ℝ) + 1 + 2 * Mv v := by linarith
      have hn2 : (0 : ℝ) ≤ 4 * (n : ℝ) ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hkey hn2]
    have hprod : ∏ v, Real.exp (-(4 * (n : ℝ) ^ 2 * (⌊dOp (uMat (w.1 v))⌋₊ : ℝ))) ≤
        (∏ v, Real.exp (4 * (n : ℝ) ^ 2 * (1 + 2 * Mv v))) *
          ∏ v, Real.exp (-(2 * (2 * (n : ℝ) ^ 2) * (⌊D γ v⌋₊ : ℝ))) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod₀ (fun v _ => (Real.exp_pos _).le) fun v _ => hshift v
    calc ‖ph B d w.1‖ * ‖B.e w.2‖
        ≤ (|∏ v, d v| * ((∏ v, Real.exp (4 * (n : ℝ) ^ 2 * (1 + 2 * Mv v))) *
            ∏ v, Real.exp (-(2 * (2 * (n : ℝ) ^ 2) * (⌊D γ v⌋₊ : ℝ))))) * (B.e 1).re := by
          refine mul_le_mul ?_ (he _) (norm_nonneg _) ?_
          · exact hmaj.trans (mul_le_mul_of_nonneg_left hprod (abs_nonneg _))
          · exact mul_nonneg (abs_nonneg _) (mul_nonneg
              (Finset.prod_nonneg fun v _ => (Real.exp_pos _).le)
              (Finset.prod_nonneg fun v _ => (Real.exp_pos _).le))
      _ = C' * ∏ v, Real.exp (-(2 * (2 * (n : ℝ) ^ 2) * (⌊D γ v⌋₊ : ℝ))) := by
          rw [hC']; ring
  have key := continuousOn_tsum (fun γ => (hcγ γ).continuousOn) hsum hbound
  exact key.continuousAt hNn

end GlobalTheory.Dec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousAutomorphicKernelDiscreteSeriesTestStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_automorphicKernel_discreteSeriesTest : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n → LocDec B h → HBig B 32 h → Continuous (fun p : B.I.GA × B.I.GA => kern B.I (phe B d) p.1 p.2) := by
  first | exact @GlobalTheory.Dec.continuous_kern_phe | exact GlobalTheory.Dec.continuous_kern_phe | (intros; apply GlobalTheory.Dec.continuous_kern_phe <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutomorphicKernelConvergenceProperties
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.KernelConv

theorem coef_inv {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (w : H) (g : UJ ε) :
    ⟪w, σ (uMat g⁻¹) w⟫_ℂ = star ⟪w, σ (uMat g) w⟫_ℂ := by
  obtain ⟨⟨h1, hmul⟩, hnorm, -⟩ := hσ
  have hg : uMat g ∈ UJset ε := g.2
  have hgi : uMat g⁻¹ ∈ UJset ε := (g⁻¹).2
  have hone : uMat g * uMat g⁻¹ = 1 := by
    show ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
      (((g⁻¹ : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1
    simp
  have hback : σ (uMat g) (σ (uMat g⁻¹) w) = w := by
    have := congrArg (fun T : H →L[ℂ] H => T w) (hmul _ hg _ hgi)
    simp only [hone, h1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at this
    exact this.symm
  let L : H →ₗᵢ[ℂ] H := { toLinearMap := (σ (uMat g) : H →ₗ[ℂ] H), norm_map' := hnorm _ hg }
  have key : ⟪w, σ (uMat g⁻¹) w⟫_ℂ = ⟪σ (uMat g) w, w⟫_ℂ := by
    rw [← L.inner_map_map w (σ (uMat g⁻¹) w)]
    show ⟪σ (uMat g) w, σ (uMat g) (σ (uMat g⁻¹) w)⟫_ℂ = _
    rw [hback]
  rw [key, ← inner_conj_symm]
  rfl

theorem phe_inv (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (hd : IsDSData B d) (x : B.I.GA) :
    phe B d x⁻¹ = star (phe B d x) := by
  have he : B.e x⁻¹.2 = star (B.e x.2) := B.e_adm.2.2.1 x.2
  have hp : ∏ v, ⟪B.w v, B.σ v (uMat (x⁻¹.1 v)) (B.w v)⟫_ℂ =
      star (∏ v, ⟪B.w v, B.σ v (uMat (x.1 v)) (B.w v)⟫_ℂ) := by
    rw [star_prod]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    show ⟪B.w v, B.σ v (uMat (x.1 v)⁻¹) (B.w v)⟫_ℂ = _
    exact coef_inv (hd v).2.1.2.2.1 (B.w v) (x.1 v)
  unfold phe ph
  rw [he, hp]
  simp only [star_mul', star_star]
  rw [show star ((∏ v, d v : ℝ) : ℂ) = ((∏ v, d v : ℝ) : ℂ) from Complex.conj_ofReal _]

theorem kern_eq (I : AutInst) (Γ : Subgroup I.GA) (hΓ : (Γ : Set I.GA) = I.GFset) (φ : I.GA → ℂ) (x y : I.GA) :
    kern I φ x y = ∑' γ : Γ, φ (x⁻¹ * γ.1 * y) := by
  unfold kern
  exact ((Equiv.subtypeEquivRight (fun a => by rw [← hΓ, SetLike.mem_coe]) : Γ ≃ I.GFset).tsum_eq
    (fun γ : I.GFset => φ (x⁻¹ * γ.1 * y))).symm

theorem kern_invariant (I : AutInst) (φ : I.GA → ℂ) (γ : I.GA) (hγ : γ ∈ I.GFset) (x y : I.GA) :
    kern I φ (γ * x) y = kern I φ x y ∧ kern I φ x (γ * y) = kern I φ x y := by
  have hΓ : ((GlobalTheory.RatDiscrete.ratSub I : Subgroup I.GA) : Set I.GA) = I.GFset := rfl
  have hγΓ : γ ∈ GlobalTheory.RatDiscrete.ratSub I := hγ
  rw [kern_eq I _ hΓ, kern_eq I _ hΓ, kern_eq I _ hΓ]
  constructor
  · refine ((Equiv.mulLeft (⟨γ, hγΓ⟩ : GlobalTheory.RatDiscrete.ratSub I)).tsum_eq
      (fun δ : GlobalTheory.RatDiscrete.ratSub I => φ ((γ * x)⁻¹ * δ.1 * y))).symm.trans ?_
    congr 1; funext δ; simp [mul_assoc]
  · refine ((Equiv.mulRight (⟨γ, hγΓ⟩ : GlobalTheory.RatDiscrete.ratSub I)⁻¹).tsum_eq
      (fun δ : GlobalTheory.RatDiscrete.ratSub I => φ (x⁻¹ * δ.1 * (γ * y)))).symm.trans ?_
    congr 1; funext δ; simp [mul_assoc]

theorem kern_symm (I : AutInst) (φ : I.GA → ℂ) (hφ : ∀ x, φ x⁻¹ = star (φ x)) (x y : I.GA) :
    kern I φ y x = star (kern I φ x y) := by
  have hΓ : ((GlobalTheory.RatDiscrete.ratSub I : Subgroup I.GA) : Set I.GA) = I.GFset := rfl
  rw [kern_eq I _ hΓ, kern_eq I _ hΓ, tsum_star]
  refine ((Equiv.inv (GlobalTheory.RatDiscrete.ratSub I)).tsum_eq
    (fun δ : GlobalTheory.RatDiscrete.ratSub I => φ (y⁻¹ * δ.1 * x))).symm.trans ?_
  congr 1; funext δ
  rw [← hφ]
  simp [mul_assoc]

theorem kernelA : KernelA := by
  unfold KernelA
  intro B d h hd hn hL hH
  refine ⟨GlobalTheory.T.discreteSeriesKernel_summable_with_bound B d h hd hn hL hH, GlobalTheory.T.continuous_automorphicKernel_discreteSeriesTest B d h hd hn hL hH, ?_, ?_⟩
  · intro γ hγ x y
    exact kern_invariant B.I (phe B d) γ hγ x y
  · intro x y
    exact kern_symm B.I (phe B d) (phe_inv B d hd) x y

end GlobalTheory.KernelConv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutomorphicKernelConvergencePropertiesStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphicKernel_convergence_properties : KernelA := by
  first | exact @GlobalTheory.KernelConv.kernelA | exact GlobalTheory.KernelConv.kernelA | (intros; apply GlobalTheory.KernelConv.kernelA <;> assumption)
end
