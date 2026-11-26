module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.Generators
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.ChebClosed

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.SepNodeQuad
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.TwoNode
open MvPolynomial Filter Topology

private theorem UpperTheory.ConvolutionTheory.FX.two_node_sep (a b a' b' : ℂ) (h : (a, b) ≠ (a', b')) :
    ∃ Q : MvPolynomial (Fin 2) ℂ, eval ![a, b] Q = 1 ∧ eval ![a', b'] Q = 0 := by
  by_cases ha : a = a'
  · have hb : b - b' ≠ 0 := by
      intro hb
      exact h (by rw [ha, sub_eq_zero.mp hb])
    refine ⟨C (b - b')⁻¹ * (X 1 - C b'), ?_, ?_⟩
    · simp [inv_mul_cancel₀ hb]
    · simp
  · have ha' : a - a' ≠ 0 := sub_ne_zero.mpr ha
    refine ⟨C (a - a')⁻¹ * (X 0 - C a'), ?_, ?_⟩
    · simp [inv_mul_cancel₀ ha']
    · simp

private theorem UpperTheory.ConvolutionTheory.FX.two_node_poly (J : Type) [Fintype J] [DecidableEq J] (x z : J → ℂ)
    (h : Function.Injective (fun i => (x i, z i))) (i : J) :
    ∃ P : MvPolynomial (Fin 2) ℂ, ∀ j, eval ![x j, z j] P = if j = i then 1 else 0 := by
  have : ∀ j, ∃ Q : MvPolynomial (Fin 2) ℂ, j ≠ i →
      eval ![x i, z i] Q = 1 ∧ eval ![x j, z j] Q = 0 := by
    intro j
    by_cases hj : j = i
    · exact ⟨0, fun h => absurd hj h⟩
    · obtain ⟨Q, hQ⟩ := UpperTheory.ConvolutionTheory.FX.two_node_sep (x i) (z i) (x j) (z j)
        (fun e => hj (h e).symm)
      exact ⟨Q, fun _ => hQ⟩
  choose Q hQ using this
  refine ⟨∏ j ∈ Finset.univ.erase i, Q j, fun j => ?_⟩
  rw [map_prod]
  split_ifs with hj
  · subst hj
    exact Finset.prod_eq_one fun k hk => (hQ k (Finset.ne_of_mem_erase hk)).1
  · exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩) (hQ j hj).2

theorem UpperTheory.ConvolutionTheory.FX.two_node :
    ∀ (J : Type) [Fintype J] (x z : J → ℂ), Function.Injective (fun i => (x i, z i)) → ∃ (s₀ : ℕ) (K : ℝ), ∀ (c : J → ℂ) (ε : ℝ), (∀ s ≤ s₀, ∀ s' ≤ s₀, ‖∑ i, c i * x i ^ s * z i ^ s'‖ ≤ ε) → ∀ i, ‖c i‖ ≤ K * ε := by
  intro J _ x z h
  classical
  choose P hP using UpperTheory.ConvolutionTheory.FX.two_node_poly J x z h
  refine ⟨Finset.univ.sup fun i => (P i).totalDegree,
    ∑ i, ∑ m ∈ (P i).support, ‖(P i).coeff m‖, fun c ε hε i => ?_⟩
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hε 0 (Nat.zero_le _) 0 (Nat.zero_le _))
  have h1 : c i = ∑ m ∈ (P i).support, (P i).coeff m * ∑ j, c j * x j ^ m 0 * z j ^ m 1 := by
    have : c i = ∑ j, c j * eval ![x j, z j] (P i) := by
      simp [hP]
    rw [this]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [eval_eq', Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hdeg : ∀ m ∈ (P i).support, ∀ k, m k ≤ Finset.univ.sup fun i => (P i).totalDegree := by
    intro m hm k
    exact ((monomial_le_degreeOf k hm).trans (degreeOf_le_totalDegree _ _)).trans
      (Finset.le_sup (f := fun i => (P i).totalDegree) (Finset.mem_univ i))
  calc ‖c i‖ ≤ ∑ m ∈ (P i).support, ‖(P i).coeff m‖ * ε := by
        rw [h1]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hε _ (hdeg m hm 0) _ (hdeg m hm 1)) (norm_nonneg _)
    _ = (∑ m ∈ (P i).support, ‖(P i).coeff m‖) * ε := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right ?_ hε0
        exact Finset.single_le_sum (f := fun i => ∑ m ∈ (P i).support, ‖(P i).coeff m‖)
          (fun i _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
end

open MvPolynomial Filter Topology

private noncomputable def UpperTheory.ConvolutionTheory.FX.sepNode (y : ℝ) (b : Bool) : ℝ :=
  if b then y + Real.sqrt (y ^ 2 - 1) else y - Real.sqrt (y ^ 2 - 1)

private theorem UpperTheory.ConvolutionTheory.FX.sepNode_quad (y : ℝ) (hy : 1 < y) (b : Bool) :
    UpperTheory.ConvolutionTheory.FX.sepNode y b ^ 2 + 1 = 2 * y * UpperTheory.ConvolutionTheory.FX.sepNode y b := by
  have hs : Real.sqrt (y ^ 2 - 1) ^ 2 = y ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  cases b <;> simp only [UpperTheory.ConvolutionTheory.FX.sepNode, if_true, Bool.false_eq_true, if_false] <;>
    linear_combination hs

private theorem UpperTheory.ConvolutionTheory.FX.sepNode_inj (y y' : ℝ) (hy : 1 < y) (hy' : 1 < y') (b b' : Bool)
    (h : UpperTheory.ConvolutionTheory.FX.sepNode y b = UpperTheory.ConvolutionTheory.FX.sepNode y' b') : y = y' ∧ b = b' := by
  have q := UpperTheory.ConvolutionTheory.FX.sepNode_quad y hy b
  have q' := UpperTheory.ConvolutionTheory.FX.sepNode_quad y' hy' b'
  rw [← h] at q'
  have ht : UpperTheory.ConvolutionTheory.FX.sepNode y b ≠ 0 := by
    intro h0
    rw [h0] at q
    norm_num at q
  have hyy : y = y' := by
    apply mul_right_cancel₀ ht
    linarith
  subst hyy
  refine ⟨rfl, ?_⟩
  have hs : 0 < Real.sqrt (y ^ 2 - 1) := Real.sqrt_pos.mpr (by nlinarith)
  cases b <;> cases b' <;>
    simp only [UpperTheory.ConvolutionTheory.FX.sepNode, if_true, Bool.false_eq_true, if_false] at h <;>
    first | rfl | (exfalso; linarith)

theorem UpperTheory.ConvolutionTheory.FX.separate0 :
    ∀ (η : ℝ), 0 < η → ∀ (I : Type) [Fintype I] (a : I → ℝ) (ζ : I → ℂ), (∀ i, η < a i) → (∀ i, ζ i ≠ 0) →
    Function.Injective (fun i => (a i, ζ i)) → ∃ (s₀ : ℕ) (K : ℝ), ∀ (m j : ℕ) (c : I → ℂ) (ε : ℝ),
    (∀ s ≤ s₀, ∀ s' ≤ s₀, ‖∑ i, c i * (((Polynomial.Chebyshev.T ℝ ((m + s : ℕ) : ℤ)).eval (2 * a i / η - 1) : ℝ) : ℂ) * ζ i ^ (j + s')‖ ≤ ε) →
    ∀ i, ‖c i‖ * (2 * a i / η - 1) ^ m * ‖ζ i‖ ^ j ≤ K * ε := by
  intro η hη I _ a ζ ha _ hinj
  have hy : ∀ i, 1 < 2 * a i / η - 1 := fun i => by
    have : 2 < 2 * a i / η := by
      rw [lt_div_iff₀ hη]
      linarith [ha i]
    linarith
  obtain ⟨s₀, K, hK⟩ := UpperTheory.ConvolutionTheory.FX.two_node (I × Bool)
    (fun p => ((UpperTheory.ConvolutionTheory.FX.sepNode (2 * a p.1 / η - 1) p.2 : ℝ) : ℂ)) (fun p => ζ p.1) (by
      rintro ⟨i, b⟩ ⟨i', b'⟩ h
      simp only [Prod.mk.injEq, Complex.ofReal_inj] at h
      obtain ⟨h1, h2⟩ := UpperTheory.ConvolutionTheory.FX.sepNode_inj _ _ (hy i) (hy i') _ _ h.1
      have h3 : a i = a i' := by
        field_simp at h1
        linarith
      have h4 : i = i' := hinj (Prod.ext h3 h.2)
      rw [h4, h2])
  refine ⟨s₀, 2 * K, fun m j c ε hε i => ?_⟩
  have key := hK (fun p => c p.1 *
      ((UpperTheory.ConvolutionTheory.FX.sepNode (2 * a p.1 / η - 1) p.2 : ℝ) : ℂ) ^ m * ζ p.1 ^ j / 2) ε (by
    intro s hs s' hs'
    refine le_of_eq_of_le ?_ (hε s hs s' hs')
    congr 1
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [((UpperTheory.ConvolutionTheory.FX.cheb_facts (m + s) _).2 (hy i).le).1, Fintype.sum_bool]
    simp only [UpperTheory.ConvolutionTheory.FX.sepNode, if_true, Bool.false_eq_true, if_false]
    generalize Real.sqrt ((2 * a i / η - 1) ^ 2 - 1) = r
    generalize 2 * a i / η - 1 = y
    push_cast
    ring) (i, true)
  simp only [UpperTheory.ConvolutionTheory.FX.sepNode, if_true] at key
  have hyi := hy i
  have hr := Real.sqrt_nonneg ((2 * a i / η - 1) ^ 2 - 1)
  generalize Real.sqrt ((2 * a i / η - 1) ^ 2 - 1) = r at key hr
  generalize 2 * a i / η - 1 = y at key hyi
  rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ y + r), Complex.norm_two] at key
  have h5 : ‖c i‖ * y ^ m * ‖ζ i‖ ^ j ≤ ‖c i‖ * (y + r) ^ m * ‖ζ i‖ ^ j := by
    have : y ≤ y + r := by linarith
    have : 0 ≤ y := by linarith
    gcongr
  linarith
end

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

private lemma pow_le_exp_eventually (d : ℕ → ℕ) (hd : Tendsto (fun j : ℕ => (d j : ℝ) / j) atTop (𝓝 0))
    (L : ℝ) (hL : 0 < L) : ∀ᶠ j : ℕ in atTop, L ^ (d j + 1) ≤ Real.exp j := by
  have h1 : Tendsto (fun j : ℕ => Real.log L * ((d j : ℝ) / j + 1 / j)) atTop
      (𝓝 (Real.log L * (0 + 0))) :=
    (hd.add tendsto_one_div_atTop_nhds_zero_nat).const_mul _
  have h2 := h1.eventually (gt_mem_nhds (show Real.log L * (0 + 0) < 1 by simp))
  filter_upwards [h2, eventually_gt_atTop 0] with j hj hj0
  have hjp : (0 : ℝ) < j := by exact_mod_cast hj0
  have h3 : Real.log L * ((d j : ℝ) + 1) ≤ j := by
    have : Real.log L * ((d j : ℝ) / j + 1 / j) = Real.log L * ((d j : ℝ) + 1) / j := by ring
    rw [this, div_lt_one hjp] at hj
    exact hj.le
  calc L ^ (d j + 1) = Real.exp (Real.log L * ((d j : ℝ) + 1)) := by
        rw [← Real.rpow_def_of_pos hL]
        rw [← Real.rpow_natCast]; push_cast; rfl
    _ ≤ _ := Real.exp_le_exp.2 h3

private lemma err_bound2 (p : ℕ) (hp : 0 < p) (c₁ cq a₀ : ℝ) (h0 : 0 < a₀) (h1 : a₀ ≤ 1)
    (A η : ℝ) (hA : A = |c₁ + cq + 1| + 1) (hηp : 0 < η) (hη : η ≤ a₀ * Real.exp (-(p * A))) (j : ℕ) (F : ℝ)
    (hF : Real.exp ((c₁ + cq + 2 + Real.log (4 / a₀)) * j) ≤ F) :
    Real.exp ((cq + 1) * j) * (η / a₀) ^ (j / p) *
      (Real.exp (c₁ * j) * (1 + (4 / η) ^ (j / p) / F) +
        (4 / η) ^ (j / p) * Real.exp (-(cq + 2 + Real.log (4 / a₀)) * j)) ≤
      (Real.exp (p * A) + 2) * Real.exp (-j) := by
  have hFp : 0 < F := (Real.exp_pos _).trans_le hF
  set m := j / p with hm
  set g := Real.log (4 / a₀) with hg
  have hq : (η / a₀) ^ m * (4 / η) ^ m = (4 / a₀) ^ m := by
    rw [← mul_pow]; congr 1; field_simp
  have h4 : (4 / a₀) ^ m ≤ Real.exp (g * j) := by
    have : (1 : ℝ) ≤ 4 / a₀ := by rw [le_div_iff₀ h0]; linarith
    calc (4 / a₀) ^ m ≤ (4 / a₀) ^ j := pow_le_pow_right₀ this (Nat.div_le_self _ _)
      _ = Real.exp (g * j) := by
        rw [mul_comm, Real.exp_nat_mul, hg, Real.exp_log (by positivity)]
  have h5 : (η / a₀) ^ m ≤ Real.exp (-(m * p * A)) := by
    have : η / a₀ ≤ Real.exp (-(p * A)) := by rw [div_le_iff₀ h0, mul_comm]; exact hη
    calc _ ≤ Real.exp (-(p * A)) ^ m := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hmp : (j : ℝ) ≤ m * p + p := by
    have := Nat.lt_div_mul_add (a := j) hp
    rw [← hm] at this
    exact_mod_cast this.le
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hA1 : c₁ + cq + 2 ≤ A := by have := le_abs_self (c₁ + cq + 1); linarith
  have t1 : Real.exp ((cq + 1) * j) * (η / a₀) ^ m * Real.exp (c₁ * j) ≤
      Real.exp (p * A) * Real.exp (-j) := by
    refine le_trans (b := Real.exp ((cq + 1) * j) * Real.exp (-(m * p * A)) * Real.exp (c₁ * j))
      (by gcongr) ?_
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith [mul_le_mul_of_nonneg_right hmp hA0, mul_le_mul_of_nonneg_right hA1 hj]
  have t2 : Real.exp ((cq + 1) * j) * Real.exp (c₁ * j) * (4 / a₀) ^ m / F ≤ Real.exp (-j) := by
    rw [div_le_iff₀ hFp]
    calc _ ≤ Real.exp ((cq + 1) * j) * Real.exp (c₁ * j) * Real.exp (g * j) := by gcongr
      _ = Real.exp (-j) * Real.exp ((c₁ + cq + 2 + g) * j) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := by gcongr
  have t3 : Real.exp ((cq + 1) * j) * (4 / a₀) ^ m * Real.exp (-(cq + 2 + g) * j) ≤
      Real.exp (-j) := by
    calc _ ≤ Real.exp ((cq + 1) * j) * Real.exp (g * j) * Real.exp (-(cq + 2 + g) * j) := by gcongr
      _ = Real.exp (-j) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [← hq] at t2 t3
  calc _ = Real.exp ((cq + 1) * j) * (η / a₀) ^ m * Real.exp (c₁ * j) +
        Real.exp ((cq + 1) * j) * Real.exp (c₁ * j) * ((η / a₀) ^ m * (4 / η) ^ m) / F +
        Real.exp ((cq + 1) * j) * ((η / a₀) ^ m * (4 / η) ^ m) * Real.exp (-(cq + 2 + g) * j) := by
        ring
    _ ≤ _ := by linarith

private lemma solve_bound2 (x a z η a₀ cq K₁ K E : ℝ) (d m j : ℕ) (hx : 0 ≤ x) (hη : 0 < η)
    (hηa : η < a₀) (h1 : a₀ ≤ 1) (ha : a₀ ≤ a) (hz : Real.exp (-cq) ≤ z) (hE : 0 ≤ E)
    (hL : ((|K₁| + 1) * |K| / a₀ + 1) ^ (d + 1) ≤ Real.exp j)
    (h : x * a ^ d * (2 * a / η - 1) ^ m * z ^ j ≤ K₁ * (K ^ (d + 1) * E)) :
    x ≤ Real.exp ((cq + 1) * j) * (η / a₀) ^ m * E := by
  have h0 : 0 < a₀ := hη.trans hηa
  have hb : a₀ / η ≤ 2 * a / η - 1 := by
    rw [div_sub_one hη.ne', div_le_div_iff_of_pos_right hη]; linarith
  have hb0 : 0 < a₀ / η := by positivity
  have hl : x * a₀ ^ (d + 1) * (a₀ / η) ^ m * Real.exp (-cq) ^ j ≤
      x * a ^ d * (2 * a / η - 1) ^ m * z ^ j := by
    have : a₀ ^ (d + 1) ≤ a ^ d :=
      (pow_le_pow_of_le_one h0.le h1 (Nat.le_succ d)).trans (pow_le_pow_left₀ h0.le ha d)
    have h2 : 0 ≤ a := by linarith
    have h3 : 0 ≤ 2 * a / η - 1 := by linarith
    gcongr
  have hr : K₁ * (K ^ (d + 1) * E) ≤ a₀ ^ (d + 1) * Real.exp j * E := by
    have e1 : |K₁| ≤ (|K₁| + 1) ^ (d + 1) :=
      (by linarith : |K₁| ≤ |K₁| + 1).trans
        (le_self_pow₀ (by linarith [abs_nonneg K₁]) (Nat.succ_ne_zero d))
    calc K₁ * (K ^ (d + 1) * E) ≤ |K₁ * (K ^ (d + 1) * E)| := le_abs_self _
      _ = |K₁| * |K| ^ (d + 1) * E := by
        rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hE, mul_assoc]
      _ ≤ (|K₁| + 1) ^ (d + 1) * |K| ^ (d + 1) * E := by gcongr
      _ = a₀ ^ (d + 1) * ((|K₁| + 1) * |K| / a₀) ^ (d + 1) * E := by
        rw [← mul_pow, ← mul_pow]; congr 2; field_simp
      _ ≤ a₀ ^ (d + 1) * ((|K₁| + 1) * |K| / a₀ + 1) ^ (d + 1) * E := by
        gcongr; linarith
      _ ≤ _ := by gcongr
  have h6 := (hl.trans h).trans hr
  have hpos : 0 < a₀ ^ (d + 1) * (a₀ / η) ^ m * Real.exp (-cq) ^ j := by positivity
  have e2 : (η / a₀) ^ m * (a₀ / η) ^ m = 1 := by
    rw [← mul_pow]
    have : η / a₀ * (a₀ / η) = 1 := by field_simp
    rw [this, one_pow]
  have e3 : Real.exp ((cq + 1) * j) * Real.exp (-cq) ^ j = Real.exp j := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  refine le_of_mul_le_mul_right ?_ hpos
  calc _ = x * a₀ ^ (d + 1) * (a₀ / η) ^ m * Real.exp (-cq) ^ j := by ring
    _ ≤ a₀ ^ (d + 1) * Real.exp j * E := h6
    _ = a₀ ^ (d + 1) * (Real.exp ((cq + 1) * j) * Real.exp (-cq) ^ j) *
        ((η / a₀) ^ m * (a₀ / η) ^ m) * E := by rw [e2, e3, mul_one]
    _ = _ := by ring

theorem UpperTheory.ConvolutionTheory.FX.exponents2 :
    ∀ (d : ℕ → ℕ), Tendsto (fun j : ℕ => (d j : ℝ) / j) atTop (𝓝 0) →
    (∀ B : ℝ, ∀ᶠ j : ℕ in atTop, Real.exp (B * j) ≤ (d j).factorial) →
    ∀ (p : ℕ), 0 < p → ∀ (c₁ cq a₀ : ℝ), 0 < a₀ → a₀ ≤ 1 → ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < a₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → ∃ N : ℝ,
    ∀ (I : Type) [Fintype I] (a : I → ℝ) (ζ : I → ℂ), (∀ i, η < a i) → (∀ i, ζ i ≠ 0) →
    Function.Injective (fun i => (a i, ζ i)) → ∀ (c : ℕ → I → ℂ) (c' : I → ℂ),
    (∀ i, Tendsto (fun j => c j i) atTop (𝓝 (c' i))) →
    (∀ s₀ : ℕ, ∃ K : ℝ, ∀ᶠ j : ℕ in atTop, ∀ s ≤ s₀, ∀ s' ≤ s₀,
    ‖∑ i, c j i * (a i : ℂ) ^ d j * (cheb η (j / p + s) (a i) : ℂ) * ζ i ^ (j + s')‖ ≤
    K ^ (d j + 1) * (Real.exp (c₁ * j) * (1 + (4 / η) ^ (j / p) / (d j).factorial) + (4 / η) ^ (j / p) * Real.exp (-N * j))) →
    ∀ i, a₀ ≤ a i → Real.exp (-cq) ≤ ‖ζ i‖ → c' i = 0 := by
  intro d hd hfac p hp c₁ cq a₀ h0 h1
  obtain ⟨A, hA⟩ : ∃ A, A = |c₁ + cq + 1| + 1 := ⟨_, rfl⟩
  have hη₀a : a₀ * Real.exp (-(p * A)) < a₀ := by
    have hA0 : 0 < A := by rw [hA]; positivity
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    have : Real.exp (-(p * A)) < 1 := Real.exp_lt_one_iff.2 (by nlinarith [mul_pos hp' hA0])
    nlinarith
  refine ⟨a₀ * Real.exp (-(p * A)), by positivity, hη₀a, ?_⟩
  intro η hηp hη
  have hηa : η < a₀ := hη.trans_lt hη₀a
  refine ⟨cq + 2 + Real.log (4 / a₀), ?_⟩
  intro I _ a ζ ha hζ0 hinj c c' hc hbd i hi hζ
  obtain ⟨s₀, K₁, hsep⟩ := UpperTheory.ConvolutionTheory.FX.separate0 η hηp I a ζ ha hζ0 hinj
  obtain ⟨K, hK⟩ := hbd s₀
  have hev : ∀ᶠ j : ℕ in atTop, ‖c j i‖ ≤ (Real.exp (p * A) + 2) * Real.exp (-j) := by
    filter_upwards [hK, hfac (c₁ + cq + 2 + Real.log (4 / a₀)),
      pow_le_exp_eventually d hd ((|K₁| + 1) * |K| / a₀ + 1) (by positivity)] with j hj hF hL
    have h := hsep (j / p) j (fun i => c j i * (a i : ℂ) ^ d j) _ hj i
    have hai : 0 ≤ a i := by linarith
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hai] at h
    exact (solve_bound2 _ _ _ η a₀ cq K₁ K _ _ _ _ (norm_nonneg _) hηp hηa h1 hi hζ
      (by positivity) hL h).trans (err_bound2 p hp c₁ cq a₀ h0 h1 A η hA hηp hη j _ hF)
  have hlim : Tendsto (fun j : ℕ => (Real.exp (p * A) + 2) * Real.exp (-j)) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul
      (Real.exp (p * A) + 2)
    simpa using this
  exact tendsto_nhds_unique (hc i) (squeeze_zero_norm' hev hlim)
