module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapTwoSidedMulHaarMatrixQuadraticExt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DixmierMalliavinFactorisationBasisStep
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedDerivFunctionalContDiffExpLine
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedDerivFunctionalContDiffExpLine
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.HCA

theorem smFn_contDiff_line :
    ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ Λ : List (Fin d) → (G → ℂ) → ℂ, SmFn h b μ S K Λ → ∀ l i, ∀ f ∈ S, ContDiff ℝ ∞ (fun t : ℝ => Λ l fun y => f (h.expG (t • b i) * y)) ∧ ∀ (p : ℕ) (s : ℝ), iteratedDeriv p (fun t : ℝ => Λ l fun y => f (h.expG (t • b i) * y)) s = Λ (List.replicate p i ++ l) fun y => f (h.expG (s • b i) * y) := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b _ _ μ _ S _ hS K _ Λ hΛ l i f hf
  have hd : ∀ (l : List (Fin d)) (s : ℝ), HasDerivAt (fun t : ℝ => Λ l fun y => f (h.expG (t • b i) * y))
      (Λ (i :: l) fun y => f (h.expG (s • b i) * y)) s := by
    intro l s
    have h1 := hΛ.der l i _ (hS f hf (h.expG (s • b i)))
    have h2 : HasDerivAt (fun t : ℝ => Λ l fun y => f (h.expG ((s + t) • b i) * y))
        (Λ (i :: l) fun y => f (h.expG (s • b i) * y)) (s - s) := by
      rw [sub_self]
      simpa only [h.expG_add_smul, mul_assoc] using h1
    have h3 := h2.comp_sub_const s s
    simpa only [add_sub_cancel] using h3
  have hi : ∀ p : ℕ, iteratedDeriv p (fun t : ℝ => Λ l fun y => f (h.expG (t • b i) * y))
      = fun s : ℝ => Λ (List.replicate p i ++ l) fun y => f (h.expG (s • b i) * y) := by
    intro p
    induction p with
    | zero => simp
    | succ p ih =>
      rw [iteratedDeriv_succ, ih]
      funext s
      rw [(hd _ s).deriv, List.replicate_succ, List.cons_append]
  refine ⟨contDiff_of_differentiable_iteratedDeriv fun m _ => ?_, fun p s => by rw [hi p]⟩
  rw [hi m]
  exact fun s => (hd _ s).differentiableAt

end GlobalTheory.HCA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedDerivFunctionalContDiffExpLineStatement
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundedDerivFunctional_contDiff_expLine : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ Λ : List (Fin d) → (G → ℂ) → ℂ, SmFn h b μ S K Λ → ∀ l i, ∀ f ∈ S, ContDiff ℝ ∞ (fun t : ℝ => Λ l fun y => f (h.expG (t • b i) * y)) ∧ ∀ (p : ℕ) (s : ℝ), iteratedDeriv p (fun t : ℝ => Λ l fun y => f (h.expG (t • b i) * y)) s = Λ (List.replicate p i ++ l) fun y => f (h.expG (s • b i) * y) := by
  first | exact @GlobalTheory.HCA.smFn_contDiff_line | exact GlobalTheory.HCA.smFn_contDiff_line | (intros; apply GlobalTheory.HCA.smFn_contDiff_line <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedDerivFunctionalTsumReplicate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedDerivFunctionalTsumReplicate
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.HCA

theorem smFn_tsum_replicate : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ Λ : List (Fin d) → (G → ℂ) → ℂ, SmFn h b μ S K Λ → ∀ i, ∃ M : ℕ → ℝ, (∀ p, 0 ≤ M p) ∧ (∀ p, ∀ f ∈ S, ‖Λ (List.replicate p i) f‖ ≤ M p * ∫ x in K, ‖f x‖ ∂μ) ∧ ∀ c : ℕ → ℝ, Summable (fun p => |c p| * M p) → SmFn h b μ S K fun l f => ∑' p, (c p : ℂ) * Λ (l ++ List.replicate p i) f := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b _ _ μ hμ S hSc hSL K hK Λ hΛ i
  classical
  haveI := hμ
  choose C0 hC0 using hΛ.bdd
  let C : List (Fin d) → ℝ := fun l => max 0 (C0 l)
  have hC0' : ∀ l, 0 ≤ C l := fun l => le_max_left _ _
  have hC : ∀ l, ∀ f ∈ S, ‖Λ l f‖ ≤ C l * ∫ x in K, ‖f x‖ ∂μ := by
    intro l f hf
    have hI : 0 ≤ ∫ x in K, ‖f x‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
    exact (hC0 l f hf).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hI)
  let D : ℕ → ℕ → ℝ := fun p k =>
    C (((Encodable.decode k : Option (List (Fin d))).getD []) ++ List.replicate p i)
  let M : ℕ → ℝ := fun p => C (List.replicate p i) + ∑ k ∈ Finset.range (p + 1), D p k
  have hD0 : ∀ p k, 0 ≤ D p k := fun p k => hC0' _
  have hM0 : ∀ p, 0 ≤ M p := fun p => add_nonneg (hC0' _) (Finset.sum_nonneg fun k _ => hD0 p k)
  have hMl : ∀ l : List (Fin d), ∀ p, Encodable.encode l ≤ p → C (l ++ List.replicate p i) ≤ M p := by
    intro l p hp
    have h1 : D p (Encodable.encode l) ≤ ∑ k ∈ Finset.range (p + 1), D p k :=
      Finset.single_le_sum (f := D p) (fun k _ => hD0 p k) (Finset.mem_range.2 (Nat.lt_succ_of_le hp))
    have h2 : D p (Encodable.encode l) = C (l ++ List.replicate p i) := by
      simp only [D, Encodable.encodek, Option.getD_some]
    have h3 := hC0' (List.replicate p i)
    simp only [M]
    linarith
  refine ⟨M, hM0, ?_, ?_⟩
  · intro p f hf
    refine (hC _ f hf).trans (mul_le_mul_of_nonneg_right ?_ (integral_nonneg fun _ => norm_nonneg _))
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => hD0 p k)
  intro c hc
  have hsum : ∀ l, Summable (fun p => |c p| * C (l ++ List.replicate p i)) := by
    intro l
    refine Summable.of_norm_bounded_eventually_nat hc ?_
    filter_upwards [Filter.eventually_ge_atTop (Encodable.encode l)] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (hC0' _))]
    exact mul_le_mul_of_nonneg_left (hMl l p hp) (abs_nonneg _)
  have hterm : ∀ l, ∀ f ∈ S, ∀ p, ‖(c p : ℂ) * Λ (l ++ List.replicate p i) f‖ ≤
      |c p| * C (l ++ List.replicate p i) * ∫ x in K, ‖f x‖ ∂μ := by
    intro l f hf p
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC _ f hf) (abs_nonneg _)
  have hsumm : ∀ l, ∀ f ∈ S, Summable (fun p => (c p : ℂ) * Λ (l ++ List.replicate p i) f) :=
    fun l f hf => Summable.of_norm_bounded ((hsum l).mul_right _) (hterm l f hf)
  have hexp0 : h.expG 0 = 1 := by
    apply Subtype.ext; apply Units.ext; simp
  refine ⟨?_, ?_, ?_⟩
  · intro l f hf f' hf' a
    have e : ∀ p, (c p : ℂ) * Λ (l ++ List.replicate p i) (a • f + f') =
        a * ((c p : ℂ) * Λ (l ++ List.replicate p i) f) + (c p : ℂ) * Λ (l ++ List.replicate p i) f' := by
      intro p; rw [hΛ.lin _ f hf f' hf' a]; ring
    simp_rw [e]
    rw [Summable.tsum_add ((hsumm l f hf).mul_left a) (hsumm l f' hf'), tsum_mul_left]
  · intro l
    refine ⟨∑' p, |c p| * C (l ++ List.replicate p i), fun f hf => ?_⟩
    rw [← tsum_mul_right]
    exact tsum_of_norm_bounded ((hsum l).mul_right _).hasSum (hterm l f hf)
  · intro l j f hf
    have hft : ∀ t : ℝ, (fun y => f (h.expG (t • b j) * y)) ∈ S := fun t => hSL f hf _
    have hcont : Continuous fun q : ℝ × G => f (h.expG (q.1 • b j) * q.2) :=
      (hSc f hf).comp ((h.continuous_expG.comp (continuous_fst.smul continuous_const)).mul continuous_snd)
    obtain ⟨A, hA⟩ := ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).prod hK).exists_bound_of_continuousOn
      hcont.continuousOn
    have hB : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ∫ x in K, ‖f (h.expG (t • b j) * x)‖ ∂μ ≤ max 0 A * μ.real K := by
      intro t ht
      have h1 := norm_setIntegral_le_of_norm_le_const (μ := μ) (C := max 0 A)
        (f := fun x => ‖f (h.expG (t • b j) * x)‖) hK.measure_lt_top (fun x hx => by
          rw [norm_norm]; exact (hA (t, x) ⟨ht, hx⟩).trans (le_max_right _ _))
      exact (Real.le_norm_self _).trans h1
    have hderiv : ∀ (m : List (Fin d)) (t : ℝ), HasDerivAt (fun s : ℝ => Λ m fun y => f (h.expG (s • b j) * y))
        (Λ (j :: m) fun y => f (h.expG (t • b j) * y)) t := by
      intro m t
      have h0 := hΛ.der m j _ (hft t)
      have e1 : (fun s : ℝ => Λ m fun y => f (h.expG (t • b j) * (h.expG (s • b j) * y))) =
          fun s => Λ m fun y => f (h.expG ((t + s) • b j) * y) := by
        funext s; congr 1; funext y; rw [h.expG_add_smul, mul_assoc]
      rw [e1] at h0
      have h1 : HasDerivAt (fun s : ℝ => Λ m fun y => f (h.expG ((t + s) • b j) * y))
          (Λ (j :: m) fun y => f (h.expG (t • b j) * y)) (t - t) := by rw [sub_self]; exact h0
      have h2 := h1.comp_sub_const t t
      have e2 : ∀ u : ℝ, t + (u - t) = u := fun u => by ring
      simp only [e2] at h2
      exact h2
    have key := hasDerivAt_tsum_of_isPreconnected (t := Set.Ioo (-1 : ℝ) 1) (y₀ := 0) (y := 0)
      (g := fun p s => (c p : ℂ) * Λ (l ++ List.replicate p i) fun y => f (h.expG (s • b j) * y))
      (g' := fun p s => (c p : ℂ) * Λ (j :: (l ++ List.replicate p i)) fun y => f (h.expG (s • b j) * y))
      (u := fun p => |c p| * C ((j :: l) ++ List.replicate p i) * (max 0 A * μ.real K))
      ((hsum (j :: l)).mul_right _) isOpen_Ioo isPreconnected_Ioo
      (fun p s _ => (hderiv _ s).const_mul _)
      (fun p s hs => (hterm (j :: l) _ (hft s) p).trans
        (mul_le_mul_of_nonneg_left (hB s (Set.Ioo_subset_Icc_self hs)) (mul_nonneg (abs_nonneg _) (hC0' _))))
      (by norm_num) (hsumm l _ (hft 0)) (by norm_num)
    simp only [zero_smul, hexp0, one_mul] at key
    exact key

end GlobalTheory.HCA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedDerivFunctionalTsumReplicateStatement
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundedDerivFunctional_tsum_replicate : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ Λ : List (Fin d) → (G → ℂ) → ℂ, SmFn h b μ S K Λ → ∀ i, ∃ M : ℕ → ℝ, (∀ p, 0 ≤ M p) ∧ (∀ p, ∀ f ∈ S, ‖Λ (List.replicate p i) f‖ ≤ M p * ∫ x in K, ‖f x‖ ∂μ) ∧ ∀ c : ℕ → ℝ, Summable (fun p => |c p| * M p) → SmFn h b μ S K fun l f => ∑' p, (c p : ℂ) * Λ (l ++ List.replicate p i) f := by
  first | exact @GlobalTheory.HCA.smFn_tsum_replicate | exact GlobalTheory.HCA.smFn_tsum_replicate | (intros; apply GlobalTheory.HCA.smFn_tsum_replicate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DixmierMalliavinFactorisationBasisStep
noncomputable section

open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic Set
open scoped ContDiff

namespace GlobalTheory.HCA

theorem smFn_dixmierMalliavin_step : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ Λ : List (Fin d) → (G → ℂ) → ℂ, SmFn h b μ S K Λ → ∀ (i : Fin d) (ε : ℝ), 0 < ε → ∃ (Λ' : List (Fin d) → (G → ℂ) → ℂ) (u v : ℝ → ℂ), SmFn h b μ S K Λ' ∧ ContDiff ℝ ∞ u ∧ ContDiff ℝ ∞ v ∧ tsupport u ⊆ Set.Icc (-ε) ε ∧ tsupport v ⊆ Set.Icc (-ε) ε ∧ ∀ f ∈ S, Λ [] f = (∫ t, u t * Λ' [] fun y => f (h.expG (t • b i) * y)) + ∫ t, v t * Λ [] fun y => f (h.expG (t • b i) * y) := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b _ _ μ hμ S hcont hinv K hK Λ hΛ i ε hε
  obtain ⟨M, hM0, hMb, hser⟩ := GlobalTheory.T.boundedDerivFunctional_tsum_replicate 𝔸 G 𝔤 h d b μ hμ S hcont hinv K hK Λ hΛ i
  obtain ⟨c, u, v, hu, hv, hus, hvs, hc, hid⟩ := exists_dixmierMalliavin_line M hε
  refine ⟨fun l f => ∑' p, (c p : ℂ) * Λ (l ++ List.replicate p i) f, u, v,
    hser c hc, hu, hv, hus, hvs, fun f hf => ?_⟩
  have hmem : ∀ t : ℝ, (fun y => f (h.expG (t • b i) * y)) ∈ S := fun t => hinv f hf _
  set F : ℝ → ℂ := fun t => Λ [] fun y => f (h.expG (t • b i) * y) with hFdef
  obtain ⟨hF, hD'⟩ := GlobalTheory.T.boundedDerivFunctional_contDiff_expLine 𝔸 G 𝔤 h d b μ hμ S hcont hinv K hK Λ hΛ [] i f hf
  have hD : ∀ p t, iteratedDeriv p F t = Λ (List.replicate p i) fun y => f (h.expG (t • b i) * y) := by
    intro p t; rw [hD' p t, List.append_nil]

  have hfc : Continuous f := hcont f hf
  have hjc : Continuous fun q : ℝ × G => f (h.expG (q.1 • b i) * q.2) :=
    hfc.comp ((h.continuous_expG.comp (continuous_fst.smul continuous_const)).mul continuous_snd)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hjc.continuousOn
  set B : ℝ := max C 0 * μ.real K with hB
  have hB0 : 0 ≤ B := mul_nonneg (le_max_right _ _) measureReal_nonneg
  have hKint : ∀ t ∈ Icc (-ε) ε, (∫ x in K, ‖f (h.expG (t • b i) * x)‖ ∂μ) ≤ B := by
    intro t ht
    have := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := K) (C := max C 0)
      (f := fun x => ‖f (h.expG (t • b i) * x)‖) hK.measure_lt_top (fun x hx => by
        rw [norm_norm]; exact (hC (t, x) ⟨ht, hx⟩).trans (le_max_left _ _))
    rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _)] at this
    exact this
  have hDb : ∀ p, ∀ t ∈ Icc (-ε) ε, ‖iteratedDeriv p F t‖ ≤ M p * B := by
    intro p t ht
    rw [hD]
    exact (hMb p _ (hmem t)).trans (mul_le_mul_of_nonneg_left (hKint t ht) (hM0 p))

  set a : ℂ := ((B + 1 : ℝ) : ℂ)⁻¹ with ha
  have hB1 : (0 : ℝ) < B + 1 := by linarith
  have ha0 : a ≠ 0 := inv_ne_zero (by exact_mod_cast hB1.ne')
  have hFa : ContDiff ℝ ∞ fun t => a * F t := contDiff_const.mul hF
  have hDa : ∀ p t, iteratedDeriv p (fun t => a * F t) t = a * iteratedDeriv p F t := by
    intro p t
    exact iteratedDeriv_const_mul a (hF.contDiffAt.of_le (by exact_mod_cast le_top))
  have key := hid (fun t => a * F t) hFa (fun p t ht => by
    rw [hDa, norm_mul, ha, norm_inv, Complex.norm_real, Real.norm_of_nonneg hB1.le]
    rw [inv_mul_le_iff₀ hB1]
    calc ‖iteratedDeriv p F t‖ ≤ M p * B := hDb p t ht
      _ ≤ (B + 1) * M p := by nlinarith [hM0 p])
  simp_rw [hDa] at key
  have e1 : ∀ p, (c p : ℂ) * ∫ t, a * iteratedDeriv p F t * u t = a * ((c p : ℂ) * ∫ t, iteratedDeriv p F t * u t) := by
    intro p
    simp_rw [mul_assoc a, integral_const_mul]; ring
  have e2 : ∫ t, a * F t * v t = a * ∫ t, F t * v t := by
    rw [← integral_const_mul a]; simp_rw [mul_assoc]
  simp_rw [e1] at key
  rw [e2, tsum_mul_left, ← mul_add] at key
  have key' := mul_left_cancel₀ ha0 key
  have hF0 : F 0 = Λ [] f := by
    simp only [hFdef, zero_smul]; rw [h.expG_zero]; simp only [one_mul]
  rw [← hF0, key']
  congr 1
  · have hugc : HasCompactSupport u := isCompact_Icc.of_isClosed_subset (isClosed_tsupport u) hus
    have hcD : ∀ p, Continuous (fun t => iteratedDeriv p F t) := fun p =>
      hF.continuous_iteratedDeriv p (by exact_mod_cast le_top)
    let T : ℕ → ℝ → ℂ := fun p t => (c p : ℂ) * (iteratedDeriv p F t * u t)
    have hTi : ∀ p, Integrable (T p) := fun p =>
      (((hcD p).mul hu.continuous).integrable_of_hasCompactSupport hugc.mul_left).const_mul _
    have hTb : ∀ p t, ‖T p t‖ ≤ |c p| * M p * (B * ‖u t‖) := by
      intro p t
      by_cases ht : t ∈ tsupport u
      · simp only [T, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have := hDb p t (hus ht)
        calc |c p| * (‖iteratedDeriv p F t‖ * ‖u t‖) ≤ |c p| * ((M p * B) * ‖u t‖) := by gcongr
          _ = |c p| * M p * (B * ‖u t‖) := by ring
      · have hu0 : u t = 0 := image_eq_zero_of_notMem_tsupport ht
        simp only [T, hu0, mul_zero, norm_zero, le_refl]
    have hgi : Integrable (fun t => B * ‖u t‖) :=
      (hu.continuous.integrable_of_hasCompactSupport hugc).norm.const_mul _
    have hsum : Summable fun p => ∫ t, ‖T p t‖ := by
      refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun t => norm_nonneg _)
        (fun p => ?_) (hc.mul_right (∫ t, B * ‖u t‖))
      rw [← integral_const_mul]
      exact integral_mono (hTi p).norm (hgi.const_mul _) (fun t => hTb p t)
    have e3 : ∀ p, (c p : ℂ) * ∫ t, iteratedDeriv p F t * u t = ∫ t, T p t := fun p =>
      (integral_const_mul _ _).symm
    simp_rw [e3]
    rw [integral_tsum_of_summable_integral_norm hTi hsum]
    congr 1
    funext t
    rw [← tsum_mul_left]
    congr 1
    funext p
    dsimp only [T, List.nil_append]
    rw [hD]
    ring
  · congr 1; funext t; rw [mul_comm]

end GlobalTheory.HCA

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DixmierMalliavinFactorisationBasisStepStatement
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dixmierMalliavin_factorisation_basis_step : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ Λ : List (Fin d) → (G → ℂ) → ℂ, SmFn h b μ S K Λ → ∀ (i : Fin d) (ε : ℝ), 0 < ε → ∃ (Λ' : List (Fin d) → (G → ℂ) → ℂ) (u v : ℝ → ℂ), SmFn h b μ S K Λ' ∧ ContDiff ℝ ∞ u ∧ ContDiff ℝ ∞ v ∧ tsupport u ⊆ Set.Icc (-ε) ε ∧ tsupport v ⊆ Set.Icc (-ε) ε ∧ ∀ f ∈ S, Λ [] f = (∫ t, u t * Λ' [] fun y => f (h.expG (t • b i) * y)) + ∫ t, v t * Λ [] fun y => f (h.expG (t • b i) * y) := by
  first | exact @GlobalTheory.HCA.smFn_dixmierMalliavin_step | exact GlobalTheory.HCA.smFn_dixmierMalliavin_step | (intros; apply GlobalTheory.HCA.smFn_dixmierMalliavin_step <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDixmierMalliavinDecompProdExp
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.HCA

theorem integrable_integral_fin_cons {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    {F : (Fin (n + 1) → ℝ) → E} (hF : Integrable F) :
    Integrable (fun s : ℝ => ∫ t', F (Fin.cons s t')) := by
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hint : Integrable (fun p : ℝ × (Fin n → ℝ) =>
      F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm p))
      ((volume : Measure ℝ).prod (Measure.pi fun _ : Fin n => (volume : Measure ℝ))) :=
    (hmp.symm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hF
  refine hint.integral_prod_left.congr (ae_of_all _ fun s => ?_)
  simp only
  congr 1; funext t'
  congr 1
  simp [MeasurableEquiv.piFinSuccAbove]

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

theorem prodExp_fin_succ (h : IsExpLieAlgebra G 𝔤) {n : ℕ} (X : Fin (n + 1) → 𝔤) (t : Fin (n + 1) → ℝ) :
    h.prodExp X t = h.expG (t 0 • X 0) * h.prodExp (Fin.tail X) (Fin.tail t) := by
  simp [IsExpLieAlgebra.prodExp, List.ofFn_succ, Fin.tail]

theorem integral_mul_sum_cons_kernel (h : IsExpLieAlgebra G 𝔤) {n N : ℕ} (X : Fin (n + 1) → 𝔤) {ε : ℝ}
    (hε : 0 ≤ ε) {u : ℝ → ℂ} (hu : Continuous u) (hus : tsupport u ⊆ Set.Icc (-ε) ε)
    {κ : Fin N → (Fin n → ℝ) → ℂ} (hκ : ∀ m, Continuous (κ m))
    (hκs : ∀ m, tsupport (κ m) ⊆ Metric.closedBall 0 ε) {Φ : Fin N → G → ℂ}
    (hΦ : ∀ m, Continuous (Φ m)) (Ψ : ℝ → ℂ)
    (hΨ : ∀ s, Ψ s = ∑ m, ∫ t', κ m t' * Φ m (h.expG (s • X 0) * h.prodExp (Fin.tail X) t')) :
    ∫ s, u s * Ψ s = ∑ m, ∫ t, u (t 0) * κ m (Fin.tail t) * Φ m (h.prodExp X t) := by
  have hF : ∀ m, Integrable (fun t : Fin (n + 1) → ℝ => u (t 0) * κ m (Fin.tail t) * Φ m (h.prodExp X t)) := by
    intro m
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((hu.comp (continuous_apply 0)).mul
        ((hκ m).comp (continuous_pi fun j => continuous_apply j.succ))).mul
        ((hΦ m).comp (h.continuous_prodExp X))
    · exact HasCompactSupport.mul_right (f := fun t : Fin (n + 1) → ℝ => u (t 0) * κ m (Fin.tail t))
        ((isCompact_closedBall 0 ε).of_isClosed_subset (isClosed_tsupport _)
          (tsupport_cons_kernel hε hus (hκs m)))
  have heq : ∀ m s, u s * ∫ t', κ m t' * Φ m (h.expG (s • X 0) * h.prodExp (Fin.tail X) t') =
      ∫ t', u ((Fin.cons s t' : Fin (n + 1) → ℝ) 0) * κ m (Fin.tail (Fin.cons s t' : Fin (n + 1) → ℝ)) *
        Φ m (h.prodExp X (Fin.cons s t')) := by
    intro m s
    rw [← integral_const_mul]
    congr 1; funext t'
    simp only [Fin.cons_zero, Fin.tail_cons, prodExp_fin_succ h X, mul_assoc]
  simp_rw [hΨ, Finset.mul_sum]
  rw [integral_finsetSum _ (fun m _ => by
    simp_rw [heq m]; exact integrable_integral_fin_cons (hF m))]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp_rw [heq m]
  exact (integral_fin_succ_cons (hF m)).symm

end GlobalTheory.HCA

namespace GlobalTheory.HCA

theorem SmFn.exists_decomp_prodExp : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ ε : ℝ, 0 < ε → ∀ (n : ℕ) (j : Fin n → Fin d) (Λ : List (Fin d) → (G → ℂ) → ℂ), SmFn h b μ S K Λ → ∃ (N : ℕ) (Λ' : Fin N → List (Fin d) → (G → ℂ) → ℂ) (κ : Fin N → (Fin n → ℝ) → ℂ), (∀ m, SmFn h b μ S K (Λ' m) ∧ ContDiff ℝ ∞ (κ m) ∧ tsupport (κ m) ⊆ Metric.closedBall 0 ε) ∧ ∀ f ∈ S, Λ [] f = ∑ m, ∫ t, κ m t * Λ' m [] fun y => f (h.prodExp (fun k => b (j k)) t * y) := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b _ _ μ hμ S hS hL K hK ε hε n
  induction n with
  | zero =>
    intro j Λ hΛ
    refine ⟨1, fun _ => Λ, fun _ _ => 1, fun _ => ⟨hΛ, contDiff_const, ?_⟩, fun f hf => ?_⟩
    · intro t _
      rw [Subsingleton.elim t 0]; exact Metric.mem_closedBall_self hε.le
    · have hv : (volume : Measure (Fin 0 → ℝ)).real Set.univ = 1 := by
        simp [Measure.real, MeasureTheory.volume_pi]
      have hP : ∀ t : Fin 0 → ℝ, h.prodExp (fun k => b (j k)) t = 1 := fun t => by
        simp [IsExpLieAlgebra.prodExp]
      simp [hP, hv]
  | succ n ih =>
    intro j Λ hΛ
    obtain ⟨Λ', u, v, hΛ', hu, hv, hus, hvs, hdec⟩ :=
      GlobalTheory.T.dixmierMalliavin_factorisation_basis_step 𝔸 G 𝔤 h d b μ hμ S hS hL K hK Λ hΛ (j 0) ε hε
    obtain ⟨N₁, Λ₁, κ₁, h₁, hd₁⟩ := ih (Fin.tail j) Λ' hΛ'
    obtain ⟨N₂, Λ₂, κ₂, h₂, hd₂⟩ := ih (Fin.tail j) Λ hΛ
    refine ⟨N₁ + N₂, Fin.append Λ₁ Λ₂,
      Fin.append (fun m t => u (t 0) * κ₁ m (Fin.tail t)) (fun m t => v (t 0) * κ₂ m (Fin.tail t)),
      ?_, ?_⟩
    · intro m
      refine Fin.addCases (fun m => ?_) (fun m => ?_) m
      · simp only [Fin.append_left]
        exact ⟨(h₁ m).1, contDiff_cons_kernel hu (h₁ m).2.1, tsupport_cons_kernel hε.le hus (h₁ m).2.2⟩
      · simp only [Fin.append_right]
        exact ⟨(h₂ m).1, contDiff_cons_kernel hv (h₂ m).2.1, tsupport_cons_kernel hε.le hvs (h₂ m).2.2⟩
    · intro f hf
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [hdec f hf]
      have hc : ∀ (Λ₀ : List (Fin d) → (G → ℂ) → ℂ), SmFn h b μ S K Λ₀ →
          Continuous fun x : G => Λ₀ [] fun y => f (x * y) := fun Λ₀ hΛ₀ =>
        SmFn.continuous_leftTranslate 𝔸 G 𝔤 h d b μ hμ S hS hL K hK Λ₀ hΛ₀ [] f hf
      congr 1
      · exact integral_mul_sum_cons_kernel h (fun k => b (j k)) hε.le hu.continuous hus
          (fun m => (h₁ m).2.1.continuous) (fun m => (h₁ m).2.2)
          (Φ := fun m x => Λ₁ m [] fun y => f (x * y)) (fun m => hc _ (h₁ m).1) _
          (fun s => by
            rw [hd₁ _ (hL f hf _)]
            simp only [mul_assoc]
            rfl)
      · exact integral_mul_sum_cons_kernel h (fun k => b (j k)) hε.le hv.continuous hvs
          (fun m => (h₂ m).2.1.continuous) (fun m => (h₂ m).2.2)
          (Φ := fun m x => Λ₂ m [] fun y => f (x * y)) (fun m => hc _ (h₂ m).1) _
          (fun s => by
            rw [hd₂ _ (hL f hf _)]
            simp only [mul_assoc]
            rfl)

end GlobalTheory.HCA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDixmierMalliavinDecompProdExpStatement
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dixmierMalliavin_decomp_prodExp : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ ε : ℝ, 0 < ε → ∀ (n : ℕ) (j : Fin n → Fin d) (Λ : List (Fin d) → (G → ℂ) → ℂ), SmFn h b μ S K Λ → ∃ (N : ℕ) (Λ' : Fin N → List (Fin d) → (G → ℂ) → ℂ) (κ : Fin N → (Fin n → ℝ) → ℂ), (∀ m, SmFn h b μ S K (Λ' m) ∧ ContDiff ℝ ∞ (κ m) ∧ tsupport (κ m) ⊆ Metric.closedBall 0 ε) ∧ ∀ f ∈ S, Λ [] f = ∑ m, ∫ t, κ m t * Λ' m [] fun y => f (h.prodExp (fun k => b (j k)) t * y) := by
  first | exact @GlobalTheory.HCA.SmFn.exists_decomp_prodExp | exact GlobalTheory.HCA.SmFn.exists_decomp_prodExp | (intros; apply GlobalTheory.HCA.SmFn.exists_decomp_prodExp <;> assumption)
end
