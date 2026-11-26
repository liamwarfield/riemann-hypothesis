module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashUnnormalizedConstMul

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.QExpansionMulFiniteConvolution
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.TotallyPositiveSummandsWithDenominatorFinite
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem reAt_abs_eq_place {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (v : InfinitePlace F) (x : F) :
    |reAt v x| = v x := by
  have hw : v.IsReal := IsTotallyReal.isReal v
  rw [← InfinitePlace.norm_embedding_of_isReal hw x]
  unfold reAt
  rw [← InfinitePlace.embedding_of_isReal_apply hw x, Complex.ofReal_re, Real.norm_eq_abs]

theorem reAt_sub_place {F : Type} [Field F] [NumberField F] (v : InfinitePlace F) (x y : F) :
    reAt v (x - y) = reAt v x - reAt v y := by
  unfold reAt
  simp [map_sub]

theorem reAt_zero_place {F : Type} [Field F] [NumberField F] (v : InfinitePlace F) :
    reAt v 0 = 0 := by
  unfold reAt; simp

private theorem infinitePlace_le_of_totally_positive_gap {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (ξ η : F)
    (h1 : η = 0 ∨ TP η) (h2 : ξ - η = 0 ∨ TP (ξ - η)) (w : InfinitePlace F) : w η ≤ w ξ := by
  have key : 0 ≤ reAt w η ∧ reAt w η ≤ reAt w ξ := by
    rcases h1 with h1 | h1
    · subst h1
      refine ⟨by simp [reAt_zero_place], ?_⟩
      rcases h2 with h2 | h2
      · rw [sub_zero] at h2
        simp [h2, reAt_zero_place]
      · have := h2 w
        rw [sub_zero] at this
        simpa [reAt_zero_place] using this.le
    · refine ⟨(h1 w).le, ?_⟩
      rcases h2 with h2 | h2
      · rw [sub_eq_zero] at h2
        simp [h2]
      · have := h2 w
        rw [reAt_sub_place] at this
        linarith
  rw [← reAt_abs_eq_place w η, ← reAt_abs_eq_place w ξ, abs_of_nonneg key.1,
    abs_of_nonneg (key.1.trans key.2)]
  exact key.2

theorem finite_tp_box : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (D : ℕ), 0 < D → ∀ ξ : F, {η : F | (η = 0 ∨ TP η) ∧ (ξ - η = 0 ∨ TP (ξ - η)) ∧ IsIntegral ℤ ((D : F) * η)}.Finite := by
  intro F _ _ _ D hD ξ
  have hfin := NumberField.Embeddings.finite_of_norm_le F ℂ ((D : ℝ) * ∑ w : InfinitePlace F, w ξ)
  have hD' : (D : F) ≠ 0 := by exact_mod_cast hD.ne'
  refine (Set.Finite.preimage (f := fun η : F => (D : F) * η)
    (fun a _ b _ h => mul_left_cancel₀ hD' h) hfin).subset ?_
  rintro η ⟨h1, h2, h3⟩
  refine ⟨h3, fun φ => ?_⟩
  have hle : (InfinitePlace.mk φ) η ≤ (InfinitePlace.mk φ) ξ := infinitePlace_le_of_totally_positive_gap ξ η h1 h2 _
  have hsum : (InfinitePlace.mk φ) ξ ≤ ∑ w : InfinitePlace F, w ξ :=
    Finset.single_le_sum (f := fun w : InfinitePlace F => w ξ) (fun w _ => apply_nonneg w ξ)
      (Finset.mem_univ _)
  rw [InfinitePlace.apply] at hle
  show ‖φ ((D : F) * η)‖ ≤ (D : ℝ) * ∑ w : InfinitePlace F, w ξ
  rw [map_mul, norm_mul, map_natCast, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (hle.trans hsum) (Nat.cast_nonneg _)

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totallyPositive_summands_with_denominator_finite : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (D : ℕ), 0 < D → ∀ ξ : F, {η : F | (η = 0 ∨ TP η) ∧ (ξ - η = 0 ∨ TP (ξ - η)) ∧ IsIntegral ℤ ((D : F) * η)}.Finite := by
  first | exact @GlobalTheory.HilbertThetaSeries.finite_tp_box | exact GlobalTheory.HilbertThetaSeries.finite_tp_box | (intros; apply GlobalTheory.HilbertThetaSeries.finite_tp_box <;> assumption)
end

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem reAt_add_qm {F : Type} [Field F] [NumberField F] (v : InfinitePlace F) (x y : F) :
    reAt v (x + y) = reAt v x + reAt v y := by
  simp [reAt, map_add (f := _)]

theorem ez_add_qm {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (x y : F) (z : Hn F) :
    ez (x + y) z = ez x z * ez y z := by
  simp only [ez, ← Complex.exp_add, reAt_add_qm, Complex.ofReal_add, add_mul, Finset.sum_add_distrib, mul_add]

theorem TP_add {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {x y : F} (hx : TP x) (hy : TP y) :
    TP (x + y) := fun v => by rw [reAt_add_qm]; exact add_pos (hx v) (hy v)

theorem hasQ_mul : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (f g : Hn F → ℂ) (a b : F → ℂ),
    HasQ f a → HasQ g b → ∃ c, HasQ (f * g) c ∧ ∀ ξ, ∃ s : Finset F, c ξ = ∑ η ∈ s, a η * b (ξ - η) := by
  intro F _ _ _ f g a b ⟨⟨D, hD, ha⟩, hf⟩ ⟨⟨E, hE, hb⟩, hg⟩
  have hfin : ∀ ξ, (Function.support fun η => a η * b (ξ - η)).Finite := by
    intro ξ
    refine (GlobalTheory.T.totallyPositive_summands_with_denominator_finite F D hD ξ).subset ?_
    intro η hη
    have h1 : a η ≠ 0 := left_ne_zero_of_mul hη
    have h2 : b (ξ - η) ≠ 0 := right_ne_zero_of_mul hη
    exact ⟨(ha η h1).1, (hb _ h2).1, (ha η h1).2⟩
  refine ⟨fun ξ => ∑ η ∈ (hfin ξ).toFinset, a η * b (ξ - η), ⟨⟨D * E, Nat.mul_pos hD hE, ?_⟩, ?_⟩,
    fun ξ => ⟨_, rfl⟩⟩
  · intro ξ hξ
    obtain ⟨η, -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hξ
    have h1 : a η ≠ 0 := left_ne_zero_of_mul hne
    have h2 : b (ξ - η) ≠ 0 := right_ne_zero_of_mul hne
    obtain ⟨p1, i1⟩ := ha η h1
    obtain ⟨p2, i2⟩ := hb _ h2
    have hsum : ξ = η + (ξ - η) := by ring
    refine ⟨?_, ?_⟩
    · rcases p1 with e1 | t1 <;> rcases p2 with e2 | t2
      · left; rw [e1, sub_zero] at e2; exact e2
      · right; rw [e1, sub_zero] at t2; exact t2
      · right; rw [sub_eq_zero] at e2; rw [e2]; exact t1
      · right; rw [hsum]; exact TP_add t1 t2
    · have hE' : IsIntegral ℤ (E : F) := by
        have := isIntegral_algebraMap (R := ℤ) (A := F) (x := (E : ℤ))
        simpa using this
      have hD' : IsIntegral ℤ (D : F) := by
        have := isIntegral_algebraMap (R := ℤ) (A := F) (x := (D : ℤ))
        simpa using this
      have : ((D * E : ℕ) : F) * ξ = (E : F) * ((D : F) * η) + (D : F) * ((E : F) * (ξ - η)) := by
        push_cast; ring
      rw [this]
      exact (hE'.mul i1).add (hD'.mul i2)
  · intro z
    have hu := summable_norm_iff.mpr (hf z).summable
    have hw := summable_norm_iff.mpr (hg z).summable
    have H : HasSum (fun p : F × F => (a p.1 * ez p.1 z) * (b p.2 * ez p.2 z)) (f z * g z) := by
      have hs := summable_mul_of_summable_norm hu hw
      have ht := tsum_mul_tsum_of_summable_norm hu hw
      rw [(hf z).tsum_eq, (hg z).tsum_eq] at ht
      rw [ht]; exact hs.hasSum
    let e : F × F ≃ F × F :=
      { toFun := fun p => (p.2, p.1 - p.2), invFun := fun q => (q.1 + q.2, q.1),
        left_inv := fun p => by simp, right_inv := fun q => by simp }
    have H2 := (e.hasSum_iff).mpr H
    refine H2.prod_fiberwise fun ξ => ?_
    have hx : (fun η => ((fun p : F × F => (a p.1 * ez p.1 z) * (b p.2 * ez p.2 z)) ∘ e) (ξ, η)) =
        fun η => a η * b (ξ - η) * ez ξ z := by
      funext η
      simp only [Function.comp, e, Equiv.coe_fn_mk]
      have : ez ξ z = ez η z * ez (ξ - η) z := by rw [← ez_add_qm, add_sub_cancel]
      rw [this]; ring
    rw [hx, Finset.sum_mul]
    apply hasSum_sum_of_ne_finset_zero
    intro η hη
    have : a η * b (ξ - η) = 0 := by
      by_contra h
      exact hη ((hfin ξ).mem_toFinset.mpr h)
    rw [this, zero_mul]

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qExpansion_mul_finite_convolution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (f g : Hn F → ℂ) (a b : F → ℂ), HasQ f a → HasQ g b → ∃ c, HasQ (f * g) c ∧ ∀ ξ, ∃ s : Finset F, c ξ = ∑ η ∈ s, a η * b (ξ - η) := by
  first | exact @GlobalTheory.HilbertThetaSeries.hasQ_mul | exact GlobalTheory.HilbertThetaSeries.hasQ_mul | (intros; apply GlobalTheory.HilbertThetaSeries.hasQ_mul <;> assumption)
end

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem small_filtration : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (r s : ℝ) (f g : Hn F → ℂ) (c : ℂ), Small ι r f → Small ι s g → Small ι (max r s) (f + g) ∧ Small ι (r * s) (f * g) ∧ Small ι (‖ι.symm c‖ * r) (c • f) ∧ (r ≤ s → Small ι s f) ∧ 0 ≤ r ∧ Small ι ‖ι.symm c‖ (fun _ : Hn F => c) := by
  intro F _ _ _ p _ ι r s f g c hf hg
  obtain ⟨a, ha, har⟩ := hf
  obtain ⟨b, hb, hbs⟩ := hg
  have hr : 0 ≤ r := (norm_nonneg _).trans (har 0)
  have hs : 0 ≤ s := (norm_nonneg _).trans (hbs 0)
  obtain ⟨h1, h2, -, h4⟩ := GlobalTheory.T.qExpansion_linear_combination F f g a b c ha hb
  refine ⟨⟨a + b, h1, fun ξ => ?_⟩, ?_, ⟨c • a, h2, fun ξ => ?_⟩, fun hrs => ⟨a, ha, fun ξ => (har ξ).trans hrs⟩, hr,
    ⟨_, h4, fun ξ => ?_⟩⟩
  · rw [Pi.add_apply, map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (har ξ) (hbs ξ))
  · obtain ⟨d, hd, hds⟩ := GlobalTheory.T.qExpansion_mul_finite_convolution F f g a b ha hb
    refine ⟨d, hd, fun ξ => ?_⟩
    obtain ⟨t, ht⟩ := hds ξ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ht, map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hr hs) fun η _ => ?_
    rw [map_mul, norm_mul]
    exact mul_le_mul (har η) (hbs _) (norm_nonneg _) hr
  · rw [Pi.smul_apply, smul_eq_mul, map_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (har ξ) (norm_nonneg _)
  · split_ifs
    · exact le_rfl
    · rw [map_zero, norm_zero]; exact norm_nonneg _

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertQExp_padicBound_algebra_properties : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (r s : ℝ) (f g : Hn F → ℂ) (c : ℂ), Small ι r f → Small ι s g → Small ι (max r s) (f + g) ∧ Small ι (r * s) (f * g) ∧ Small ι (‖ι.symm c‖ * r) (c • f) ∧ (r ≤ s → Small ι s f) ∧ 0 ≤ r ∧ Small ι ‖ι.symm c‖ (fun _ : Hn F => c) := by
  first | exact @GlobalTheory.HilbertThetaSeries.small_filtration | exact GlobalTheory.HilbertThetaSeries.small_filtration | (intros; apply GlobalTheory.HilbertThetaSeries.small_filtration <;> assumption)
