module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CarLaws

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.BandTC
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Imports
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.flip :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (X : H →L[ℂ] H) (a b : ℝ), (∀ t h, X (M.F.U t h) = M.F.U (-t) (X h)) →
      IsHilbertSchmidt (M.P (Ioc a b) ∘L X) → IsHilbertSchmidt (X ∘L M.P (Ioc a b)) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M X a b hX hs
  obtain ⟨-, -, -, -, pl, p0, -, -⟩ := projLaws M
  rcases le_or_gt b a with hab | hab
  · rw [Ioc_eq_empty_of_le hab, p0, ContinuousLinearMap.comp_zero]
    show hsNormSq _ < _
    rw [hsNormSq_zero]; exact ENNReal.zero_lt_top
  set d := b - a with hd
  have d0 : 0 < d := sub_pos.2 hab
  let I : ℤ → Set ℝ := fun n => Ioc (a + n * d) (a + (n + 1) * d)
  have hI : ∀ n, MeasurableSet (I n) := fun _ => measurableSet_Ioc
  have sa : ∀ s, MeasurableSet s → ContinuousLinearMap.adjoint (M.P s) = M.P s := fun s hs => (pl s s hs hs).2.1.adjoint_eq
  have pyth : ∀ x : H, ‖x‖ₑ ^ 2 = ∑' n, ‖M.P (I n) x‖ₑ ^ 2 := fun x => by
    have h1 : HasSum (fun n => M.P (I n) x) x := by
      have h0 : HasSum (fun n => M.P (I n) x) (M.J (M.J.symm x)) :=
        ((cutLim (M.J.symm x)).2 a d d0).mapL (M.J.toContinuousLinearEquiv : L V →L[ℂ] H)
      rwa [M.J.apply_symm_apply] at h0
    have h2 := (h1.mapL (innerSL ℂ x)).mapL Complex.reCLM
    have e : ∀ n, (⟪x, M.P (I n) x⟫_ℂ).re = ‖M.P (I n) x‖ ^ 2 := fun n => by
      have i1 := DFunLike.congr_fun (pl _ _ (hI n) (hI n)).1 x
      rw [inter_self, ContinuousLinearMap.comp_apply] at i1
      rw [← i1, ← ContinuousLinearMap.adjoint_inner_left, sa _ (hI n), i1, inner_self_eq_norm_sq_to_K]
      simp [← Complex.ofReal_pow]
    simp only [innerSL_apply_apply, Complex.reCLM_apply, e] at h2
    rw [inner_self_eq_norm_sq_to_K] at h2
    have h3 : HasSum (fun n => ‖M.P (I n) x‖ ^ 2) (‖x‖ ^ 2) := by simpa [← Complex.ofReal_pow] using h2
    have h4 := ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg ‖M.P (I n) x‖) h3.summable
    rw [h3.tsum_eq] at h4
    simpa [ENNReal.ofReal_pow] using h4
  have dec : ∀ Y : H →L[ℂ] H, hsNormSq Y = ∑' n, hsNormSq (M.P (I n) ∘L Y) := fun Y => by
    simp only [hsNormSq]
    rw [ENNReal.tsum_comm]
    exact tsum_congr fun m => pyth _
  have un : ∀ t, ‖M.F.U t‖ₑ ≤ 1 := fun t => by
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_le_one]
    exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun h => by rw [M.F.norm, one_mul]
  have step : ∀ n : ℤ, hsNormSq (M.P (I n) ∘L X ∘L M.P (Ioc a b)) ≤ hsNormSq (M.P (I n) ∘L ContinuousLinearMap.adjoint (M.P (Ioc a b) ∘L X)) := fun n => by
    have t1 := ((pl (Ioc a b) _ measurableSet_Ioc (measurableSet_Ioc (a := a) (b := b))).2.2.2.2 (-(n * d))).1
    have pre : (fun x => x + -(n * d)) ⁻¹' Ioc a b = I n := by
      ext x
      simp only [I, mem_preimage, mem_Ioc]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    rw [pre] at t1
    have t2 : ∀ h, M.F.U (-(n * d)) (M.P (Ioc a b) h) = M.P (I n) (M.F.U (-(n * d)) h) := fun h => DFunLike.congr_fun t1 h
    have e : M.P (I n) ∘L X ∘L M.P (Ioc a b) = M.F.U (-(n * d)) ∘L (M.P (Ioc a b) ∘L X ∘L M.P (I n)) ∘L M.F.U (-(n * d)) := by
      ext h
      simp only [ContinuousLinearMap.comp_apply]
      rw [← t2, hX, t2, ← M.F.add, add_neg_cancel, M.F.zero]
    have e2 : M.P (I n) ∘L ContinuousLinearMap.adjoint (M.P (Ioc a b) ∘L X) =
        ContinuousLinearMap.adjoint (M.P (Ioc a b) ∘L X ∘L M.P (I n)) := by
      simp only [ContinuousLinearMap.adjoint_comp, sa _ (hI n), ContinuousLinearMap.comp_assoc]
    rw [e, e2, hsNormSq_adjoint]
    refine (hsNormSq_comp_left_le _ _).trans ((mul_le_of_le_one_left' (pow_le_one' (un _) _)).trans ?_)
    exact (hsNormSq_comp_right_le _ _).trans (mul_le_of_le_one_left' (pow_le_one' (un _) _))
  show hsNormSq _ < _
  rw [dec]
  refine (ENNReal.tsum_le_tsum step).trans_lt ?_
  rw [← dec]
  exact hs.adjoint
end

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W]

private theorem widen (M : Sc H V W) (φ : ℝ → ℂ) (hi : Integrable φ) (ρ a b : ℝ) (hρ : ∀ t, ρ < |t| → φ t = 0) :
    M.P (Ioc (a - ρ) (b + ρ)) * (M.F.av φ * M.P (Ioc a b)) = M.F.av φ * M.P (Ioc a b) := by
  ext h
  obtain ⟨i1, i2⟩ := ((avSpec M.F).2.2.2 φ hi).1 (M.P (Ioc a b) h)
  simp only [ContinuousLinearMap.mul_apply]
  rw [i2, ← ContinuousLinearMap.integral_comp_comm _ i1]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  by_cases ht : ρ < |t|
  · simp [hρ t ht]
  have pl := (projLaws M).2.2.2.2.1
  have m : MeasurableSet ((fun x => x + t) ⁻¹' Ioc a b) := measurableSet_Ioc.preimage (measurable_add_const t)
  have e1 : M.F.U t (M.P (Ioc a b) h) = _ :=
    DFunLike.congr_fun ((pl (Ioc a b) (Ioc a b) measurableSet_Ioc measurableSet_Ioc).2.2.2.2 t).1 h
  have e2 := (pl (Ioc (a - ρ) (b + ρ)) _ measurableSet_Ioc m).1
  rw [inter_eq_right.2 (by
    rintro x ⟨h1, h2⟩
    have := abs_le.1 (not_lt.1 ht)
    constructor <;> linarith [this.1, this.2])] at e2
  simp only [map_smul]
  rw [e1]
  exact congrArg _ (DFunLike.congr_fun e2 _)
end

theorem UpperTheory.V.Z.IntegralApplyAeEq.bandTC :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (X : H →L[ℂ] H) (κ : ℝ → V →L[ℂ] W), Ker κ → M.Carries X κ → ∀ (ψ : ℝ → ℝ) (δ a b : ℝ), Bump ψ (-δ) 0 → a ≤ b →
      IsTraceClass ((M.F.av (fun t => (ψ t : ℂ)) ∘L X) ∘L M.P (Ioc a b)) ∧ IsTraceClass (M.P' (Ioc a b) ∘L (M.F.av (fun t => (ψ t : ℂ)) ∘L X)) ∧
      IsTraceClass ((M.F.av (fun t => (ψ t : ℂ)) ∘L X) ∘L M.P' (Ioc a b)) ∧
      trace ((M.F.av (fun t => (ψ t : ℂ)) ∘L X) ∘L M.P (Ioc a b)) = ∫ y in a..b, ∑ i, M.cor (fun x => (ψ x : ℂ)) (stdOrthonormalBasis ℂ V i) (kv κ (stdOrthonormalBasis ℂ V i)) (2 * y) ∧
      trace (M.P' (Ioc a b) ∘L (M.F.av (fun t => (ψ t : ℂ)) ∘L X)) =
        conj (∫ y in a..b, ∑ j, M.swap.cor (fun x => (ψ (-x) : ℂ)) (stdOrthonormalBasis ℂ W j) (kv (sharp κ) (stdOrthonormalBasis ℂ W j)) (2 * y)) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M X κ hk hX ψ δ a b hψ hab
  obtain ⟨c1, c2, -⟩ := carLaws M X κ hk hX
  have hk' := (convAdj κ hk).1
  obtain ⟨s0, hi, -⟩ := avApprox.2.1 ψ _ _ hψ
  have cc : Continuous fun t => (ψ t : ℂ) := Complex.continuous_ofReal.comp hψ.cont
  have sc : HasCompactSupport fun t => (ψ t : ℂ) := s0.comp_left Complex.ofReal_zero
  have cn : Continuous fun t => (ψ (-t) : ℂ) := cc.comp continuous_neg
  have sn : HasCompactSupport fun t => (ψ (-t) : ℂ) := sc.comp_homeomorph (Homeomorph.neg ℝ)
  have z : ∀ t, |δ| < |t| → ψ t = 0 := fun t ht => hψ.supp t fun h => by
    have : |t| ≤ |δ| := abs_le.2 ⟨by linarith [h.1, le_abs_self δ], h.2.trans (abs_nonneg δ)⟩
    linarith
  obtain ⟨-, -, a1, a2, -⟩ := (avSpec M.F).2.2.2 _ hi
  simp only [Complex.conj_ofReal] at a1
  set Ψ := M.F.av fun t => (ψ t : ℂ) with hΨ
  set Ψn := M.F.av fun t => (ψ (-t) : ℂ) with hΨn
  have a3 : M.swap.F.av (fun t => (ψ t : ℂ)) = Ψn := a2
  have cm : Ψ * X = X * Ψn := by
    have := ((avSpec M.F.rev).2.2.2 _ hi).2.2.2.2 M.F X fun t h => by
      show X (M.F.U (-t) h) = _
      rw [c1, neg_neg]
    rw [a2] at this
    exact this.symm
  have hab' : a - |δ| ≤ b + |δ| := by linarith [abs_nonneg δ]
  have w1 := widen M (fun t => (ψ (-t) : ℂ)) hi.comp_neg |δ| a b fun t ht => by rw [z (-t) (by rwa [abs_neg])]; simp
  have w2 := widen M.swap (fun t => (ψ t : ℂ)) hi |δ| a b fun t ht => by rw [z t ht]; simp
  rw [a3] at w2
  obtain ⟨b1, -, b2, -, b3⟩ := bandHS M X κ hk hX _ a b cn sn hab
  obtain ⟨b4, -⟩ := bandHS M X κ hk hX _ _ _ cn sn hab'
  obtain ⟨d1, -, d2, -, d3⟩ := bandHS M.swap _ _ hk' c2 _ a b cc sc hab
  obtain ⟨d4, -⟩ := bandHS M.swap _ _ hk' c2 _ _ _ cc sc hab'
  rw [a3] at d2 d3
  obtain ⟨p1, p2, -⟩ := (projLaws M).2.2.2.2.1 (Ioc a b) (Ioc a b) measurableSet_Ioc measurableSet_Ioc
  obtain ⟨q1, q2, -⟩ := (projLaws M.swap).2.2.2.2.1 (Ioc a b) (Ioc a b) measurableSet_Ioc measurableSet_Ioc
  obtain ⟨-, q3, -⟩ := (projLaws M.swap).2.2.2.2.1 (Ioc (a - |δ|) (b + |δ|)) (Ioc a b) measurableSet_Ioc measurableSet_Ioc
  rw [inter_self] at p1 q1
  have d5 : IsHilbertSchmidt (X ∘L M.swap.P (Ioc (a - |δ|) (b + |δ|))) := by
    refine flip M.swap X _ _ (fun t h => c1 (-t) h) ?_
    have := d4.adjoint
    rwa [ContinuousLinearMap.adjoint_comp, q3.adjoint_eq, ContinuousLinearMap.adjoint_adjoint] at this
  simp only [Sc.P']
  set P := M.P (Ioc a b)
  set Q := M.swap.P (Ioc a b)
  set P₁ := M.P (Ioc (a - |δ|) (b + |δ|))
  set Q₁ := M.swap.P (Ioc (a - |δ|) (b + |δ|))
  have a1' : star Ψ = Ψn := a1
  have a4 : star Ψn = Ψ := by rw [← a1', star_star]
  have t1 : IsTraceClass (Ψ * X * P) := by
    rw [cm, mul_assoc, ← w1, ← mul_assoc]
    exact isTraceClass_comp b4 b2
  have t3 : IsTraceClass (Ψ * X * Q) := by
    rw [cm, mul_assoc, ← w2, ← mul_assoc]
    exact isTraceClass_comp d5 d2
  have t2 : IsTraceClass (Q * (Ψ * X)) := by
    have h : IsTraceClass (star X * Q₁ * (Ψn * Q)) := isTraceClass_comp d4 d2
    rw [mul_assoc, w2] at h
    have h' : IsTraceClass (star (star X * (Ψn * Q))) := h.adjoint
    rwa [star_mul, star_mul, star_star, q2.star_eq, a4, mul_assoc] at h'
  refine ⟨t1, t2, t3, ?_, ?_⟩
  · simp only [neg_neg] at b3
    rw [← b3]
    have h := trace_comp_comm t1 P
    change trace (P * (Ψ * X * P)) = trace (Ψ * X * P * P) at h
    change P * P = P at p1
    rw [mul_assoc (Ψ * X), p1] at h
    change trace (Ψ * X * P) = trace (star (Ψn * P) * (X * P))
    rw [← h, star_mul, p2.star_eq, a4]
    simp only [mul_assoc]
  · rw [← d3, ← trace_adjoint (isTraceClass_comp d2.adjoint d1)]
    have h := trace_comp_comm t2 Q
    change trace (Q * (Q * (Ψ * X))) = trace (Q * (Ψ * X) * Q) at h
    change Q * Q = Q at q1
    rw [← mul_assoc, q1] at h
    change trace (Q * (Ψ * X)) = trace (star (star (Ψn * Q) * (star X * Q)))
    rw [h, star_mul, star_star, star_mul, star_star, q2.star_eq, cm]
    simp only [mul_assoc]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.TraceId
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.TwoProj
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.twoProj :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Λ E Λ' E' Y : H →L[ℂ] H), Λ + E = Λ' + E' → Λ ∘L Λ = Λ → E ∘L E = E → Λ' ∘L Λ' = Λ' → E' ∘L E' = E' →
      Λ ∘L E = 0 → E ∘L Λ = 0 → Λ' ∘L E' = 0 → E' ∘L Λ' = 0 → IsTraceClass (Λ ∘L Y ∘L Λ) → IsTraceClass (E ∘L Y) →
      IsTraceClass (Y ∘L E) → IsTraceClass (Y ∘L E') →
      IsTraceClass (Λ' ∘L Y ∘L Λ') ∧ trace (Λ ∘L Y ∘L Λ) + trace (E ∘L Y) = trace (Λ' ∘L Y ∘L Λ') + trace (Y ∘L E') := by
  intro H _ _ _ Λ E Λ' E' Y hs h1 h2 h3 h4 h5 h6 h7 h8 t1 t2 t3 t4
  have key : ∀ A B Z : H →L[ℂ] H, A * A = A → B * B = B → A * B = 0 → B * A = 0 → IsTraceClass ((A + B) * Z * (A + B)) →
      IsTraceClass (A * Z * A) ∧ trace ((A + B) * Z * (A + B)) = trace (A * Z * A) + trace (B * Z * B) := by
    intro A B Z a b ab ba h
    have e1 : A * ((A + B) * Z * (A + B)) * A = A * Z * A := by
      rw [← mul_assoc, ← mul_assoc, mul_add A A, a, ab, add_zero, mul_assoc, add_mul, a, ba, add_zero]
    have e2 : B * ((A + B) * Z * (A + B)) * B = B * Z * B := by
      rw [← mul_assoc, ← mul_assoc, mul_add B A, b, ba, zero_add, mul_assoc, add_mul, b, ab, zero_add]
    set Q := (A + B) * Z * (A + B) with hQ
    have e3 : Q = A * Q + B * Q := by
      rw [← add_mul, hQ, ← mul_assoc, ← mul_assoc, add_mul A B (A + B), mul_add A, mul_add B, a, b, ab, ba, add_zero, zero_add]
    have c : ∀ P : H →L[ℂ] H, P * P = P → trace (P * Q) = trace (P * Q * P) := fun P hP => by
      have := trace_comp_comm (h.comp_left P) P
      change trace (P * (P * Q)) = trace (P * Q * P) at this
      rwa [← mul_assoc, hP] at this
    refine ⟨e1 ▸ (h.comp_left A).comp_right A, ?_⟩
    rw [← e1, ← e2, ← c A a, ← c B b]
    conv_lhs => rw [e3]
    exact trace_add (h.comp_left A) (h.comp_left B)
  have hT : IsTraceClass ((Λ + E) * Y * (Λ + E)) := by
    have : (Λ + E) * Y * (Λ + E) = Λ * (Y * Λ) + (Λ * (Y * E) + E * Y * (Λ + E)) := by noncomm_ring
    rw [this]
    exact t1.add ((t3.comp_left Λ).add (t2.comp_right (Λ + E)))
  obtain ⟨-, k1⟩ := key Λ E Y h1 h2 h5 h6 hT
  rw [hs] at hT k1
  obtain ⟨k2, k3⟩ := key Λ' E' Y h3 h4 h7 h8 hT
  have c1 : trace (E * Y * E) = trace (E * Y) := by
    have := trace_comp_comm t2 E
    change trace (E * (E * Y)) = trace (E * Y * E) at this
    rw [← this, ← mul_assoc]; exact congrArg (fun Z => trace (Z * Y)) h2
  have c2 : trace (E' * Y * E') = trace (Y * E') := by
    have := trace_comp_comm t4 E'
    change trace (E' * (Y * E')) = trace (Y * E' * E') at this
    rw [mul_assoc, this, mul_assoc]; exact congrArg (fun Z => trace (Y * Z)) h4
  refine ⟨k2, ?_⟩
  change trace (Λ * (Y * Λ)) + trace (E * Y) = trace (Λ' * (Y * Λ')) + trace (Y * E')
  rw [← mul_assoc, ← mul_assoc, ← c1, ← c2, ← k1, k3]
end

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.traceId :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (X : H →L[ℂ] H) (κ : ℝ → V →L[ℂ] W), Ker κ → M.Carries X κ → ∀ (ψ : ℝ → ℝ) (δ T a : ℝ), Bump ψ (-δ) 0 → M.T₀ ≤ T → 0 ≤ a →
      IsTraceClass (M.abelian₂ T T ∘L (M.F.av (fun t => (ψ t : ℂ)) ∘L X) ∘L M.abelian₂ T T) →
      trace (M.abelian₂ T T ∘L (M.F.av (fun t => (ψ t : ℂ)) ∘L X) ∘L M.abelian₂ T T) + trace (M.P' (Ioc T (T + a)) ∘L (M.F.av (fun t => (ψ t : ℂ)) ∘L X)) =
        trace (M.abelian₂ T T ∘L M.F.U (-(2 * a)) ∘L (M.F.av (fun t => (ψ t : ℂ)) ∘L X) ∘L M.abelian₂ T T) + trace ((M.F.av (fun t => (ψ t : ℂ)) ∘L X) ∘L M.P (Ioc (T - a) T)) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M X κ hk hX ψ δ T a hψ hT ha htc
  obtain ⟨-, -, -, -, hP, -, -, hL⟩ := projLaws M
  have hP' := (projLaws M.swap).2.2.2.2.1
  obtain ⟨t1, -, -, -, -⟩ := bandTC M X κ hk hX ψ δ (T - a) T hψ (by linarith)
  obtain ⟨-, t2, t3, -, -⟩ := bandTC M X κ hk hX ψ δ T (T + a) hψ (by linarith)
  have hcomm := ((avSpec M.F).2.2.2 _ (avApprox.2.1 ψ _ _ hψ).2.1).2.2.2.2 M.F (M.F.U (-a))
    (fun t h => by rw [← M.F.add, ← M.F.add, add_comm])
  set Ψ := M.F.av (fun t => (ψ t : ℂ)) with hΨ
  set Y := Ψ ∘L X with hY
  have mI : ∀ x : ℝ, MeasurableSet (Ioi x) := fun _ => measurableSet_Ioi
  have mc : ∀ x y : ℝ, MeasurableSet (Ioc x y) := fun _ _ => measurableSet_Ioc
  have s1 : M.P' (Ioi T) = M.P' (Ioc T (T + a)) + M.P' (Ioi (T + a)) := by
    have := (hP' _ _ (mc T (T + a)) (mI (T + a))).2.2.2.1 (Ioc_disjoint_Ioi le_rfl)
    rwa [Ioc_union_Ioi_eq_Ioi (by linarith)] at this
  have s2 : M.P (Ioi (T - a)) = M.P (Ioc (T - a) T) + M.P (Ioi T) := by
    have := (hP _ _ (mc (T - a) T) (mI T)).2.2.2.1 (Ioc_disjoint_Ioi le_rfl)
    rwa [Ioc_union_Ioi_eq_Ioi (by linarith)] at this
  obtain ⟨-, -, l0, -, -, -, -, l3, l4⟩ := hL T T (by linarith)
  obtain ⟨-, -, m0, -, -, m1, m2, -, -⟩ := hL (T - a) (T + a) (by linarith)
  have e0 : M.P' (Ioc T (T + a)) ∘L M.P' (Ioc T (T + a)) = M.P' (Ioc T (T + a)) := by
    have := (hP' _ _ (mc T (T + a)) (mc T (T + a))).1
    rwa [inter_self] at this
  have e1 : M.P' (Ioi T) ∘L M.P' (Ioc T (T + a)) = M.P' (Ioc T (T + a)) := by
    have := (hP' _ _ (mI T) (mc T (T + a))).1
    rwa [inter_eq_right.2 Ioc_subset_Ioi_self] at this
  have e2 : M.P' (Ioc T (T + a)) ∘L M.P' (Ioi T) = M.P' (Ioc T (T + a)) := by
    have := (hP' _ _ (mc T (T + a)) (mI T)).1
    rwa [inter_eq_left.2 Ioc_subset_Ioi_self] at this
  have e3 : M.P (Ioi (T - a)) ∘L M.P (Ioc (T - a) T) = M.P (Ioc (T - a) T) := by
    have := (hP _ _ (mI (T - a)) (mc (T - a) T)).1
    rwa [inter_eq_right.2 Ioc_subset_Ioi_self] at this
  have e4 : M.P (Ioc (T - a) T) ∘L M.P (Ioi (T - a)) = M.P (Ioc (T - a) T) := by
    have := (hP _ _ (mc (T - a) T) (mI (T - a))).1
    rwa [inter_eq_left.2 Ioc_subset_Ioi_self] at this
  obtain ⟨tc, key⟩ := twoProj (M.abelian₂ T T) (M.P' (Ioc T (T + a))) (M.abelian₂ (T - a) (T + a)) (M.P (Ioc (T - a) T)) Y
    (by simp only [Sc.abelian₂, s1, s2]; abel) l0 e0 m0 (by simpa using (hP _ _ (mc (T - a) T) (mc (T - a) T)).1)
    (by rw [← e1, ← ContinuousLinearMap.comp_assoc, l3, ContinuousLinearMap.zero_comp])
    (by rw [← e2, ContinuousLinearMap.comp_assoc, l4, ContinuousLinearMap.comp_zero])
    (by rw [← e3, ← ContinuousLinearMap.comp_assoc, m1, ContinuousLinearMap.zero_comp])
    (by rw [← e4, ContinuousLinearMap.comp_assoc, m2, ContinuousLinearMap.comp_zero]) htc t2 t3 t1
  rw [key]
  congr 1
  have u1 : ∀ h, M.F.U a (M.abelian₂ T T h) = M.abelian₂ (T - a) (T + a) (M.F.U a h) := fun h => by
    obtain ⟨x1, x2⟩ := (hP _ _ (mI T) (mI T)).2.2.2.2 a
    have y1 : (fun x : ℝ => x + a) ⁻¹' Ioi T = Ioi (T - a) := by ext x; simp [sub_lt_iff_lt_add]
    have y2 : (fun x : ℝ => x - a) ⁻¹' Ioi T = Ioi (T + a) := by ext x; simp [lt_sub_iff_add_lt]
    rw [y1] at x1; rw [y2] at x2
    have z1 := DFunLike.congr_fun x1 h
    have z2 := DFunLike.congr_fun x2 h
    simp only [ContinuousLinearMap.comp_apply] at z1 z2
    simp only [Sc.abelian₂, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, map_sub, z1, z2]
  have inv1 : ∀ h, M.F.U (-a) (M.F.U a h) = h := fun h => by rw [← M.F.add, neg_add_cancel, M.F.zero]
  have inv2 : ∀ h, M.F.U a (M.F.U (-a) h) = h := fun h => by rw [← M.F.add, add_neg_cancel, M.F.zero]
  have u2 : ∀ h, M.F.U (-a) (M.abelian₂ (T - a) (T + a) h) = M.abelian₂ T T (M.F.U (-a) h) := fun h => by
    conv_lhs => rw [← inv2 h, ← u1, inv1]
  have hYU : ∀ h, Y (M.F.U a h) = M.F.U (-a) (Y h) := fun h => by
    show Ψ (X (M.F.U a h)) = M.F.U (-a) (Ψ (X h))
    rw [(carLaws M X κ hk hX).1]
    exact (DFunLike.congr_fun hcomm _).symm
  have := trace_comp_comm (tc.comp_left (M.F.U (-a))) (M.F.U a)
  have f1 : M.F.U a ∘L (M.F.U (-a) ∘L (M.abelian₂ (T - a) (T + a) ∘L Y ∘L M.abelian₂ (T - a) (T + a))) =
      M.abelian₂ (T - a) (T + a) ∘L Y ∘L M.abelian₂ (T - a) (T + a) := by
    ext h; simp only [ContinuousLinearMap.comp_apply, inv2]
  have f2 : (M.F.U (-a) ∘L (M.abelian₂ (T - a) (T + a) ∘L Y ∘L M.abelian₂ (T - a) (T + a))) ∘L M.F.U a =
      M.abelian₂ T T ∘L M.F.U (-(2 * a)) ∘L Y ∘L M.abelian₂ T T := by
    ext h
    show M.F.U (-a) (M.abelian₂ (T - a) (T + a) (Y (M.abelian₂ (T - a) (T + a) (M.F.U a h)))) = M.abelian₂ T T (M.F.U (-(2 * a)) (Y (M.abelian₂ T T h)))
    rw [← u1, hYU, u2, ← M.F.add]
    congr 3; ring
  rwa [f1, f2] at this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.TraceFar
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W)

private theorem k1 {T : ℝ} (hT : M.T₀ ≤ T) {r : ℝ} (hr : r ≤ 0) (h : H) : M.abelian₂ T T (M.F.U r (M.P (Ioi T) h)) = 0 := by
  obtain ⟨-, -, -, -, hP, -, -, hL⟩ := projLaws M
  have x1 := DFunLike.congr_fun ((hP _ _ (measurableSet_Ioi (a := T)) (measurableSet_Ioi (a := T))).2.2.2.2 r).1 h
  have y1 : (fun x : ℝ => x + r) ⁻¹' Ioi T = Ioi (T - r) := by ext x; simp [sub_lt_iff_lt_add]
  have x2 := (hP _ _ (measurableSet_Ioi (a := T)) (measurableSet_Ioi (a := T - r))).1
  rw [inter_eq_right.2 (Ioi_subset_Ioi (by linarith))] at x2
  rw [y1, ← x2] at x1
  simp only [ContinuousLinearMap.comp_apply] at x1
  rw [x1]
  exact DFunLike.congr_fun (hL T T (by linarith)).2.2.2.2.2.1 _

private theorem k2 {T δ : ℝ} (hT : M.T₀ ≤ T) {r : ℝ} (hr : -δ ≤ r) (h : H) : M.abelian₂ T T (M.F.U r (M.P' (Ioi (T + δ)) h)) = 0 := by
  obtain ⟨-, -, -, -, hP, -, -, hL⟩ := projLaws M
  have x1 := DFunLike.congr_fun ((hP _ _ (measurableSet_Ioi (a := T + δ)) (measurableSet_Ioi (a := T))).2.2.2.2 r).2 h
  have y1 : (fun x : ℝ => x - r) ⁻¹' Ioi (T + δ) = Ioi (T + δ + r) := by ext x; simp [lt_sub_iff_add_lt]
  have x2 : M.P' (Ioi T) ∘L M.P' (Ioi (T + δ + r)) = M.P' (Ioi T ∩ Ioi (T + δ + r)) :=
    ((projLaws M.swap).2.2.2.2.1 _ _ (measurableSet_Ioi (a := T)) (measurableSet_Ioi (a := T + δ + r))).1
  rw [inter_eq_right.2 (Ioi_subset_Ioi (by linarith))] at x2
  rw [y1, ← x2] at x1
  simp only [ContinuousLinearMap.comp_apply] at x1
  rw [x1]
  exact DFunLike.congr_fun (hL T T (by linarith)).2.2.2.2.2.2.2.1 _

private theorem k3 {ψ : ℝ → ℝ} {δ : ℝ} (hψ : Bump ψ (-δ) 0) (A : H →L[ℂ] H) (h : H)
    (hA : ∀ r, -δ ≤ r → r ≤ 0 → A (M.F.U r h) = 0) : A (M.F.av (fun t => (ψ t : ℂ)) h) = 0 := by
  obtain ⟨i, e⟩ := ((avSpec M.F).2.2.2 _ (avApprox.2.1 ψ _ _ hψ).2.1).1 h
  rw [e, ← A.integral_comp_comm i]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun r => ?_)
  by_cases hr : r ∈ Icc (-δ) 0
  · simp [hA r hr.1 hr.2]
  · simp [hψ.supp r hr]

private theorem k4 {T ρ : ℝ} (hρ : 0 ≤ ρ) : M.P' (Ioi T) = M.P' (Ioc T (T + ρ)) + M.P' (Ioi (T + ρ)) := by
  have := ((projLaws M.swap).2.2.2.2.1 _ _ (measurableSet_Ioc (a := T) (b := T + ρ)) (measurableSet_Ioi (a := T + ρ))).2.2.2.1
    (Ioc_disjoint_Ioi le_rfl)
  rwa [Ioc_union_Ioi_eq_Ioi (by linarith)] at this

private theorem k5 (T : ℝ) (h : H) : h = M.abelian₂ T T h + M.P (Ioi T) h + M.P' (Ioi T) h := by
  show h = h - M.P (Ioi T) h - M.P' (Ioi T) h + _ + _
  abel

private theorem k6 {X : H →L[ℂ] H} {κ : ℝ → V →L[ℂ] W} (hk : Ker κ) (hX : M.Carries X κ) {ψ : ℝ → ℝ} {δ : ℝ} (hψ : Bump ψ (-δ) 0)
    {a b : ℝ} (hab : a ≤ b) :
    IsHilbertSchmidt (M.F.av (fun t => (ψ t : ℂ)) ∘L M.P' (Ioc a b)) ∧ IsHilbertSchmidt (M.P' (Ioc a b) ∘L X) ∧
    hsNorm (M.F.av (fun t => (ψ t : ℂ)) ∘L M.P' (Ioc a b)) ^ 2 = (b - a) * (Module.finrank ℂ W * ∫ x, ψ x ^ 2) ∧
    hsNorm (M.P' (Ioc a b) ∘L X) ^ 2 = (b - a) * ∑ i, ‖kv (sharp κ) (stdOrthonormalBasis ℂ W i)‖ ^ 2 ∧
    M.P' (Ioc a b) ∘L M.P' (Ioc a b) = M.P' (Ioc a b) := by
  obtain ⟨hs, hi, -⟩ := avApprox.2.1 ψ _ _ hψ
  obtain ⟨b1, b2, b3, b4, -⟩ := bandHS M.swap _ _ (convAdj κ hk).1 (carLaws M X κ hk hX).2.1 (fun t => (ψ (-t) : ℂ)) a b
    (Complex.continuous_ofReal.comp (hψ.cont.comp continuous_neg))
    ((hs.comp_homeomorph (Homeomorph.neg ℝ)).comp_left (g := fun x : ℝ => (x : ℂ)) rfl) hab
  have e : M.swap.F.av (fun t => (ψ (-t) : ℂ)) = M.F.av fun t => (ψ t : ℂ) := by
    have := ((avSpec M.F).2.2.2 _ hi.comp_neg).2.2.2.1
    simp only [neg_neg] at this
    exact this
  rw [e] at b3 b4
  obtain ⟨p1, p2, -⟩ := (projLaws M.swap).2.2.2.2.1 _ _ (measurableSet_Ioc (a := a) (b := b)) (measurableSet_Ioc (a := a) (b := b))
  rw [inter_self] at p1
  have e2 : M.P' (Ioc a b) ∘L X = ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint X ∘L M.swap.P (Ioc a b)) := by
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint, p2.adjoint_eq]; rfl
  refine ⟨b3, e2 ▸ b1.adjoint, b4.trans ?_, by rw [e2, hsNorm_adjoint, b2], p1⟩
  have := integral_neg_eq_self (fun x => ψ x ^ 2) volume
  simp [this]
end

theorem UpperTheory.V.Z.IntegralApplyAeEq.traceFar :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (X : H →L[ℂ] H) (κ : ℝ → V →L[ℂ] W), Ker κ → M.Carries X κ → ∀ (ψ : ℝ → ℝ) (δ T : ℝ), Bump ψ (-δ) 0 → M.T₀ ≤ T → IsTraceClass (M.abelian₂ T T ∘L X ∘L M.abelian₂ T T) →
      IsTraceClass (M.abelian₂ T T ∘L (M.F.av (fun t => (ψ t : ℂ)) ∘L X) ∘L M.abelian₂ T T) ∧
      Tendsto (fun a : ℝ => trace (M.abelian₂ T T ∘L M.F.U (-(2 * a)) ∘L (M.F.av (fun t => (ψ t : ℂ)) ∘L X) ∘L M.abelian₂ T T)) atTop (𝓝 0) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M X κ hk hX ψ δ T hψ hT htc
  obtain ⟨ρ₀, hρ₀⟩ := hk.2.isCompact.isBounded.subset_closedBall 0
  have hρ : ∀ t, max ρ₀ 0 < |t| → κ t = 0 := fun t ht => image_eq_zero_of_notMem_tsupport fun h => by
    have := hρ₀ h
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs] at this
    linarith [le_max_left ρ₀ 0]
  set ρ := max ρ₀ 0
  have r0 : 0 ≤ ρ := le_max_right _ _
  obtain ⟨h1, h2, -, -, h3⟩ := k6 M hk hX hψ (a := T) (b := T + ρ) (by linarith)
  obtain ⟨-, -, l0, -, ln, -, l2, -⟩ := (projLaws M).2.2.2.2.2.2.2 T T (by linarith)
  set Λ := M.abelian₂ T T
  set Ψ := M.F.av (fun t => (ψ t : ℂ))
  set E := M.P' (Ioc T (T + ρ))
  let Z : H →L[ℂ] H := Ψ ∘L (Λ ∘L X ∘L Λ) + ((Ψ ∘L E) ∘L (E ∘L X)) ∘L Λ
  have hZ : IsTraceClass Z := (htc.comp_left Ψ).add ((isTraceClass_comp h1 h2).comp_right Λ)
  have key : ∀ t, 0 ≤ t → Λ ∘L M.F.U (-t) ∘L (Ψ ∘L X) ∘L Λ = (Λ ∘L M.F.U (-t)) ∘L Z := fun t ht => by
    ext h
    have a1 : (Λ ∘L M.F.U (-t)) (Ψ (M.P (Ioi T) (X (Λ h)))) = 0 := k3 M hψ _ _ fun r _ hr => by
      rw [ContinuousLinearMap.comp_apply, ← M.F.add]; exact k1 M hT (by linarith) _
    have a2 : M.P' (Ioi (T + ρ)) (X (Λ h)) = 0 := by
      have := DFunLike.congr_fun ((carLaws M X κ hk hX).2.2 ρ T hρ) (Λ h)
      have l : M.P (Ioi T) (Λ h) = 0 := DFunLike.congr_fun l2 h
      simpa [l] using this
    have a3 : E (E (X (Λ h))) = E (X (Λ h)) := DFunLike.congr_fun h3 _
    show (Λ ∘L M.F.U (-t)) (Ψ (X (Λ h))) = (Λ ∘L M.F.U (-t)) (Ψ (Λ (X (Λ h))) + Ψ (E (E (X (Λ h)))))
    conv_lhs => rw [k5 M T (X (Λ h)), k4 M r0, ContinuousLinearMap.add_apply, a2, add_zero, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), a1, add_zero]
    rw [a3, map_add (f := _)]
  constructor
  · have := key 0 le_rfl
    have e : M.F.U (-0) = 1 := by ext h; simpa using M.F.zero h
    rw [e] at this
    exact this ▸ hZ.comp_left _
  · have t := trWeak atTop (fun a : ℝ => Λ ∘L M.F.U (-(2 * a))) 0 Z hZ (fun a =>
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun h => by
        rw [ContinuousLinearMap.comp_apply]
        exact (Λ.le_opNorm _).trans (by rw [M.F.norm]; gcongr)) (fun x y => by
      have sa := ((projLaws M).2.2.2.2.2.2.2 T T (by linarith)).2.2.2.1
      have := ((projLaws M).1 y (Λ x)).2.comp (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop two_pos))
      simp only [ContinuousLinearMap.zero_apply, inner_zero_right]
      exact this.congr fun a => sa.isSymmetric.apply_clm _ _)
    have z : trace ((0 : H →L[ℂ] H) ∘L Z) = 0 := by
      have := trace_smul 0 hZ
      simpa using this
    rw [z] at t
    refine t.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
    rw [key _ (by linarith)]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CorLim
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CorOne
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.corOne :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (φ : ℝ → ℂ) (e n : V) (c : ℝ), Continuous φ → HasCompactSupport φ →
      Tendsto (fun a => ∫ s in (c - a)..(c + a), ⟪sv V φ e, sh V s (one V n)⟫_ℂ) atTop (𝓝 (conj (∫ x, φ x) * ⟪e, n⟫_ℂ)) := by
  intro V _ _ _ _ φ e n c h1 h2
  have iφ : Integrable φ := h1.integrable_of_hasCompactSupport h2
  have hf : Integrable fun x => conj (φ (-x)) := (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp iφ.comp_neg
  have hg : Integrable ((Ioc (0 : ℝ) 1).indicator fun _ => ⟪e, n⟫_ℂ) := (integrable_indicator_iff measurableSet_Ioc).2 (by simp)
  have e1 : ∀ s, ⟪sv V φ e, sh V s (one V n)⟫_ℂ = convolution (fun x => conj (φ (-x)))
      ((Ioc (0 : ℝ) 1).indicator fun _ => ⟪e, n⟫_ℂ) (ContinuousLinearMap.mul ℂ ℂ) volume s := fun s => by
    rw [convolution_def, L2.inner_def, ← integral_neg_eq_self _ volume]
    rw [← integral_neg_eq_self (fun t => ContinuousLinearMap.mul ℂ ℂ (conj (φ (-t)))
      ((Ioc (0 : ℝ) 1).indicator (fun _ => ⟪e, n⟫_ℂ) (s - t))) volume, integral_neg_eq_self (fun a => ⟪sv V φ e a, sh V s (one V n) a⟫_ℂ) volume]
    refine integral_congr_ae ?_
    filter_upwards [((svSpec (V := V)).1 φ (h1.memLp_of_hasCompactSupport h2) e).1, sh_ae V s (one V n),
      (measurePreserving_add_right volume s).quasiMeasurePreserving.ae ((svSpec (V := V)).2 n).1] with x a1 a2 a3
    rw [a1, a2, a3, sub_neg_eq_add, add_comm s x, inner_smul_left]
    by_cases b : x + s ∈ Ioc (0 : ℝ) 1 <;> simp [b]
  simp only [e1]
  have t := intervalIntegral_tendsto_integral (hf.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hg)
    (a := fun a : ℝ => c - a) (b := fun a : ℝ => c + a) (l := atTop)
    (tendsto_atBot_add_const_left _ c tendsto_neg_atTop_atBot) (tendsto_atTop_add_const_left _ c tendsto_id)
  rw [integral_convolution _ hf hg, integral_indicator measurableSet_Ioc, integral_conj, integral_neg_eq_self] at t
  simpa using t
end

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.corLim :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (N : W →ₗ[ℂ] V), M.IsN N → ∀ (φ : ℝ → ℂ) (e : V) (p : L W) (c : ℝ), Continuous φ → HasCompactSupport φ → Bdd p →
      Continuous (M.cor φ e p) ∧ Tendsto (fun a => ∫ s in (c - a)..(c + a), M.cor φ e p s) atTop (𝓝 (conj (∫ x, φ x) * ⟪e, N (∫ x, p x)⟫_ℂ)) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M N hN φ e p c h1 h2 hp
  have hc : ∀ a b : H, Continuous fun s => ⟪a, M.F.U s b⟫_ℂ := fun a b => continuous_const.inner (M.F.cont b)
  refine ⟨hc _ _, ?_⟩
  have t1 := (cobLaws M.F).2.2.2.2.2.2.1 (projLaws M).1 _ (M.J (sv V φ e)) c (nAll M N hN p hp)
  have t2 := corOne φ e (N (∫ x, p x)) c h1 h2
  have t3 := t1.add t2
  rw [zero_add] at t3
  refine t3.congr fun a => ?_
  have e1 : ∀ s, ⟪sv V φ e, sh V s (one V (N (∫ x, p x)))⟫_ℂ = ⟪M.J (sv V φ e), M.F.U s (M.J (one V (N (∫ x, p x))))⟫_ℂ :=
    fun s => by rw [M.hJ, M.J.inner_map_map]
  simp only [e1]
  rw [← intervalIntegral.integral_add ((hc _ _).intervalIntegrable _ _) ((hc _ _).intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [Sc.cor, map_sub, inner_sub_right, sub_add_cancel]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.TailB
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.WBound
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

private theorem layer (f : ℝ → ℝ) (hf : Measurable f) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (2 * x) * f x) =
      ∫⁻ a, ENNReal.ofReal (2 * Real.exp (2 * a)) * ∫⁻ x in Ioi a, ENNReal.ofReal (f x) := by
  have e1 : ∀ x : ℝ, ENNReal.ofReal (Real.exp (2 * x)) = ∫⁻ a in Iio x, ENNReal.ofReal (2 * Real.exp (2 * a)) := fun x => by
    rw [setLIntegral_congr Iio_ae_eq_Iic, ← ofReal_integral_eq_lintegral_ofReal
      ((integrableOn_exp_mul_Iic two_pos x).const_mul 2) (Eventually.of_forall fun _ => by positivity), integral_const_mul,
      integral_exp_mul_Iic two_pos]
    congr 1; ring
  have m : Measurable fun z : ℝ × ℝ => {z : ℝ × ℝ | z.2 < z.1}.indicator
      (fun z => ENNReal.ofReal (2 * Real.exp (2 * z.2)) * ENNReal.ofReal (f z.1)) z :=
    Measurable.indicator (by fun_prop) (measurableSet_lt measurable_snd measurable_fst)
  have := lintegral_lintegral_swap (μ := volume) (ν := volume) (f := fun x a : ℝ => {z : ℝ × ℝ | z.2 < z.1}.indicator
      (fun z => ENNReal.ofReal (2 * Real.exp (2 * z.2)) * ENNReal.ofReal (f z.1)) (x, a)) m.aemeasurable
  refine (lintegral_congr fun x => ?_).trans (this.trans (lintegral_congr fun a => ?_))
  · rw [ENNReal.ofReal_mul (Real.exp_pos _).le, e1, ← lintegral_mul_const _ (by fun_prop), ← lintegral_indicator measurableSet_Iio]
    rfl
  · rw [← lintegral_const_mul _ (by fun_prop), ← lintegral_indicator measurableSet_Ioi]
    rfl

theorem UpperTheory.V.Z.IntegralApplyAeEq.wBound :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (g : L V) (p : L W) (c Q : ℝ), (∀ a : ℝ, ‖cut V (Ioi a) g‖ ≤ ‖cut W (Iic (c - a)) p‖) → WLe (-2) p Q → WLe 2 g (Real.exp c * Q) := by
  intro V _ _ _ _ W _ _ _ _ g p c Q h ⟨hp1, hp2⟩
  have ig : Integrable fun x => ‖g x‖ ^ 2 := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).1 (Lp.memLp g)
  have ip : Integrable fun x => ‖p x‖ ^ 2 := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable p)).1 (Lp.memLp p)
  have mg : Measurable fun x => ‖g x‖ ^ 2 := (Lp.stronglyMeasurable g).norm.measurable.pow_const 2
  have mp : Measurable fun x => ‖p x‖ ^ 2 := (Lp.stronglyMeasurable p).norm.measurable.pow_const 2
  have ip' : Integrable fun x => ‖p (c - x)‖ ^ 2 := ip.comp_sub_left c
  have h1 : ∀ a, ∫⁻ x in Ioi a, ENNReal.ofReal (‖g x‖ ^ 2) ≤ ∫⁻ x in Ioi a, ENNReal.ofReal (‖p (c - x)‖ ^ 2) := fun a => by
    rw [← ofReal_integral_eq_lintegral_ofReal ig.integrableOn (Eventually.of_forall fun _ => by positivity),
      ← ofReal_integral_eq_lintegral_ofReal ip'.integrableOn (Eventually.of_forall fun _ => by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : ∫ x in Ioi a, ‖p (c - x)‖ ^ 2 = ∫ x in Iic (c - a), ‖p x‖ ^ 2 := by
      rw [← integral_Ici_eq_integral_Ioi, ← integral_indicator measurableSet_Ici, ← integral_indicator measurableSet_Iic,
        ← integral_sub_left_eq_self _ volume c]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      by_cases b : x ≤ c - a
      · simp [indicator, b, show a ≤ c - x by linarith]
      · simp [indicator, b, show ¬ a ≤ c - x from fun k => b (by linarith)]
    rw [e, ← (cutLaws (V := V) _ univ measurableSet_Ioi .univ).2.2.2.2.2.2.2.2,
      ← (cutLaws (V := W) _ univ measurableSet_Iic .univ).2.2.2.2.2.2.2.2]
    exact pow_le_pow_left₀ (norm_nonneg _) (h a) 2
  have i2 : Integrable fun x => Real.exp (2 * x) * ‖p (c - x)‖ ^ 2 := by
    refine ((hp1.comp_sub_left c).const_mul (Real.exp (2 * c))).congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [← mul_assoc, ← Real.exp_add]; ring_nf
  have v2 : ∫ x, Real.exp (2 * x) * ‖p (c - x)‖ ^ 2 ≤ (Real.exp c * Q) ^ 2 := by
    have e : ∫ x, Real.exp (2 * x) * ‖p (c - x)‖ ^ 2 = Real.exp (2 * c) * ∫ x, Real.exp (-2 * x) * ‖p x‖ ^ 2 := by
      rw [← integral_sub_left_eq_self (fun x => Real.exp (-2 * x) * ‖p x‖ ^ 2) volume c, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [← mul_assoc, ← Real.exp_add]; ring_nf
    rw [e, mul_pow, ← Real.exp_nat_mul]
    exact mul_le_mul_of_nonneg_left hp2 (Real.exp_pos _).le
  have mp' : Measurable fun x => ‖p (c - x)‖ ^ 2 := mp.comp (measurable_const.sub measurable_id)
  have h2 : ∫⁻ x, ENNReal.ofReal (Real.exp (2 * x) * ‖g x‖ ^ 2) ≤ ENNReal.ofReal ((Real.exp c * Q) ^ 2) := by
    refine le_trans ?_ (ENNReal.ofReal_le_ofReal v2)
    rw [ofReal_integral_eq_lintegral_ofReal i2 (Eventually.of_forall fun _ => by positivity), layer _ mg, layer _ mp']
    exact lintegral_mono fun a => mul_le_mul' le_rfl (h1 a)
  have m2 : Measurable fun x => Real.exp (2 * x) * ‖g x‖ ^ 2 := (by fun_prop : Measurable fun x : ℝ => Real.exp (2 * x)).mul mg
  have i3 : Integrable fun x => Real.exp (2 * x) * ‖g x‖ ^ 2 :=
    ⟨m2.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => by positivity)).2
      (h2.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨i3, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal i3 (Eventually.of_forall fun _ => by positivity)] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2
end

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

private theorem half {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (g : L V) (q a : ℝ) (hq : 0 < q) (h : WLe 2 g q) :
    ∫⁻ y in Ioi a, ‖g y‖ₑ ≤ ENNReal.ofReal (99 / 140 * Real.exp (-a) * q) := by
  set l := 5 / 7 * Real.exp (-a) / q with hl
  have l0 : 0 < l := by positivity
  have i1 : IntegrableOn (fun y => Real.exp (-2 * y)) (Ioi a) := integrableOn_exp_mul_Ioi (by norm_num) a
  have i2 : IntegrableOn (fun y => l / 2 * (Real.exp (2 * y) * ‖g y‖ ^ 2) + (2 * l)⁻¹ * Real.exp (-2 * y)) (Ioi a) :=
    (h.1.integrableOn.const_mul _).add (i1.const_mul _)
  have pt : ∀ y, ‖g y‖ ≤ l / 2 * (Real.exp (2 * y) * ‖g y‖ ^ 2) + (2 * l)⁻¹ * Real.exp (-2 * y) := fun y => by
    have e1 : Real.exp (-2 * y) = (Real.exp (2 * y))⁻¹ := by rw [← Real.exp_neg]; ring_nf
    have e0 := Real.exp_pos (2 * y)
    rw [e1]
    set E := Real.exp (2 * y)
    rw [← sub_nonneg]
    have : l / 2 * (E * ‖g y‖ ^ 2) + (2 * l)⁻¹ * E⁻¹ - ‖g y‖ = (l * E * ‖g y‖ - 1) ^ 2 / (2 * l * E) := by
      field_simp; ring
    rw [this]; positivity
  calc _ ≤ ∫⁻ y in Ioi a, ENNReal.ofReal (l / 2 * (Real.exp (2 * y) * ‖g y‖ ^ 2) + (2 * l)⁻¹ * Real.exp (-2 * y)) :=
        lintegral_mono fun y => by rw [← ofReal_norm_eq_enorm]; exact ENNReal.ofReal_le_ofReal (pt y)
    _ = ENNReal.ofReal (∫ y in Ioi a, l / 2 * (Real.exp (2 * y) * ‖g y‖ ^ 2) + (2 * l)⁻¹ * Real.exp (-2 * y)) :=
        (ofReal_integral_eq_lintegral_ofReal i2 (Eventually.of_forall fun y => (norm_nonneg _).trans (pt y))).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_add (h.1.integrableOn.const_mul _) (i1.const_mul _), integral_const_mul, integral_const_mul,
          integral_exp_mul_Ioi (by norm_num)]
        have h1 : ∫ y in Ioi a, Real.exp (2 * y) * ‖g y‖ ^ 2 ≤ q ^ 2 :=
          (setIntegral_le_integral h.1 (Eventually.of_forall fun y => by positivity)).trans h.2
        refine (add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity)) le_rfl).trans_eq ?_
        have e1 : Real.exp (-2 * a) = Real.exp (-a) ^ 2 := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
        have e0 := Real.exp_pos (-a)
        rw [e1, hl]
        field_simp; ring

theorem UpperTheory.V.Z.IntegralApplyAeEq.tailB :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (φ : ℝ → ℂ) (e : V) (p : L W) (Q α β : ℝ), Continuous φ → (∀ x, 1 / 2 < |x| → φ x = 0) → ∫ x, ‖φ x‖ ≤ 1 → 0 ≤ Q →
      WLe (-2) p Q → α ≤ β → ‖∫ s in α..β, M.cor φ e p s‖ ≤ 6 / 5 * ‖e‖ * Real.exp (2 * M.T₀) * Q * Real.exp (-α) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M φ e p Q α β φc φs φi hQ hp hαβ
  set g : L V := M.J.symm (M.J' p) with hg
  have hcut : ∀ a : ℝ, ‖cut V (Ioi a) g‖ ≤ ‖cut W (Iic (2 * M.T₀ - a)) p‖ := fun a => by
    have h1 := cutLaws (V := W) (Iic (2 * M.T₀ - a)) (Ioi (2 * M.T₀ - a)) measurableSet_Iic measurableSet_Ioi
    have h2 := h1.2.2.1 (Iic_disjoint_Ioi le_rfl)
    rw [Iic_union_Ioi, h1.2.2.2.1] at h2
    have h3 : p = cut W (Iic (2 * M.T₀ - a)) p + cut W (Ioi (2 * M.T₀ - a)) p := DFunLike.congr_fun h2 p
    have h4 := DFunLike.congr_fun ((projLaws M).2.2.2.2.2.2.2 a (2 * M.T₀ - a) (by linarith)).1 (M.J' p)
    change M.J (cut V (Ioi a) (M.J.symm (M.J' (cut W (Ioi (2 * M.T₀ - a)) (M.J'.symm (M.J' p)))))) = 0 at h4
    rw [M.J'.symm_apply_apply, M.J.map_eq_zero_iff] at h4
    have h5 : cut V (Ioi a) g = cut V (Ioi a) (M.J.symm (M.J' (cut W (Iic (2 * M.T₀ - a)) p))) := by
      rw [hg]
      conv_lhs => rw [h3]
      rw [map_add (f := _), map_add (f := _), map_add (f := _), h4, add_zero]
    rw [h5]
    refine ((cutLaws (V := V) (Ioi a) (Ioi a) measurableSet_Ioi measurableSet_Ioi).2.2.2.2.2.1 _).trans_eq ?_
    rw [M.J.symm.norm_map, M.J'.norm_map]
  have hw := wBound g p (2 * M.T₀) Q hcut hp
  have φcs : HasCompactSupport φ := HasCompactSupport.intro (isCompact_Icc (a := -(1 / 2)) (b := 1 / 2)) fun x hx =>
    φs x (by rw [mem_Icc, ← abs_le, not_le] at hx; exact hx)
  have φI : Integrable φ := φc.integrable_of_hasCompactSupport φcs
  have hsv := ((svSpec (V := V)).1 φ (φc.memLp_of_hasCompactSupport φcs) e).1
  have gm : Measurable fun y => ‖g y‖ₑ := (Lp.stronglyMeasurable g).enorm
  have hcor : ∀ s, ‖M.cor φ e p s‖ₑ ≤ ∫⁻ x, ‖φ x‖ₑ * ‖e‖ₑ * ‖g (x + s)‖ₑ := fun s => by
    have e1 : M.J' p = M.J g := by rw [hg, M.J.apply_symm_apply]
    rw [Sc.cor, e1, M.hJ, M.J.inner_map_map, L2.inner_def]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae ?_)
    filter_upwards [hsv, sh_ae V s g] with x h1 h2
    rw [h1, h2, ← enorm_smul]
    exact enorm_inner_le _ _
  have main : ∀ q, Real.exp (2 * M.T₀) * Q < q → ‖∫ s in α..β, M.cor φ e p s‖ ≤ 6 / 5 * ‖e‖ * Real.exp (-α) * q := by
    intro q hq
    have q0 : 0 ≤ Real.exp (2 * M.T₀) * Q := by positivity
    have q1 : 0 < q := q0.trans_lt hq
    have hB := half g q (α - 1 / 2) q1 ⟨hw.1, hw.2.trans (pow_le_pow_left₀ q0 hq.le 2)⟩
    set B := 99 / 140 * Real.exp (-(α - 1 / 2)) * q with hBd
    have B0 : 0 ≤ B := by positivity
    have h1 : ‖∫ s in α..β, M.cor φ e p s‖ₑ ≤ ENNReal.ofReal (‖e‖ * B) := by
      rw [intervalIntegral.integral_of_le hαβ]
      calc _ ≤ ∫⁻ s in Ioc α β, ∫⁻ x, ‖φ x‖ₑ * ‖e‖ₑ * ‖g (x + s)‖ₑ :=
            (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono hcor)
        _ = ∫⁻ x, ∫⁻ s in Ioc α β, ‖φ x‖ₑ * ‖e‖ₑ * ‖g (x + s)‖ₑ :=
            lintegral_lintegral_swap (((φc.measurable.enorm.comp measurable_snd).mul_const _).mul
              (gm.comp (measurable_snd.add measurable_fst))).aemeasurable
        _ ≤ ∫⁻ x, ‖φ x‖ₑ * (‖e‖ₑ * ENNReal.ofReal B) := by
            refine lintegral_mono fun x => ?_
            by_cases hx : 1 / 2 < |x|
            · simp [φs x hx]
            have gx : Measurable fun s => ‖g (x + s)‖ₑ := gm.comp (measurable_const.add measurable_id)
            rw [lintegral_const_mul _ gx, mul_assoc]
            gcongr
            refine le_trans ?_ hB
            rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Ioi,
              ← lintegral_add_left_eq_self (fun y => (Ioi (α - 1 / 2)).indicator (fun y => ‖g y‖ₑ) y) x]
            refine lintegral_mono fun s => ?_
            by_cases hs : s ∈ Ioc α β
            · have h7 : x + s ∈ Ioi (α - 1 / 2) := by
                have h5 := (abs_le.1 (not_lt.1 hx)).1
                have h6 := hs.1
                rw [mem_Ioi]
                linarith
              rw [indicator_of_mem hs]
              exact (indicator_of_mem h7 fun y => ‖g y‖ₑ).ge
            · rw [indicator_of_notMem hs]
              exact bot_le
        _ = (∫⁻ x, ‖φ x‖ₑ) * (‖e‖ₑ * ENNReal.ofReal B) := lintegral_mul_const _ φc.measurable.enorm
        _ ≤ 1 * (‖e‖ₑ * ENNReal.ofReal B) := by
            gcongr
            rw [← ofReal_integral_norm_eq_lintegral_enorm φI]
            exact ENNReal.ofReal_le_one.2 φi
        _ = _ := by rw [one_mul, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm_eq_enorm]
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
    refine h1.trans ?_
    have h2 : Real.exp (1 / 2) ≤ 169 / 100 := by
      refine (pow_le_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) two_ne_zero).1 ?_
      rw [← Real.exp_nat_mul]
      norm_num
      linarith [Real.exp_one_lt_d9]
    have h3 : Real.exp (-(α - 1 / 2)) = Real.exp (-α) * Real.exp (1 / 2) := by rw [← Real.exp_add]; ring_nf
    rw [hBd, h3]
    have h4 : 0 ≤ ‖e‖ * Real.exp (-α) * q := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 h4]
  have := ge_of_tendsto (x := 𝓝[>] (Real.exp (2 * M.T₀) * Q))
    (((continuous_const (y := 6 / 5 * ‖e‖ * Real.exp (-α))).mul continuous_id).tendsto _ |>.mono_left nhdsWithin_le_nhds)
    (eventually_mem_nhdsWithin.mono fun q hq => main q hq)
  refine this.trans_eq ?_
  simp only [Pi.mul_apply, id]; ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Planch
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

private theorem r_int : Integrable (fun y : ℝ => ((1 + |y|) ^ 2)⁻¹) ∧ ∫ y : ℝ, ((1 + |y|) ^ 2)⁻¹ = 2 := by
  constructor
  · refine integrable_inv_one_add_sq.mono' (Continuous.aestronglyMeasurable (Continuous.fun_inv₀ (by fun_prop) fun y => by positivity))
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    refine inv_anti₀ (by positivity) ?_
    nlinarith [abs_nonneg y, sq_abs y]
  · rw [integral_comp_abs (f := fun y => ((1 + y) ^ 2)⁻¹)]
    have h := integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0) (g := fun y : ℝ => -(1 + y)⁻¹) (g' := fun y => ((1 + y) ^ 2)⁻¹) (l := 0)
      (fun y hy => by
        have h0 : (1 + y) ≠ 0 := by have : 0 ≤ y := hy; positivity
        have := (((hasDerivAt_id y).const_add 1).inv h0).neg
        exact this.congr_deriv (by simp only [id]; rw [neg_div, neg_neg, one_div]))
      (fun y _ => by positivity)
      (by simpa using (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ (1 : ℝ) tendsto_id)).neg)
    rw [h]; norm_num

private theorem symb_app {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [CompleteSpace W] (κ : ℝ → V →L[ℂ] W) (hk : Ker κ) (z : ℂ) (e : V) :
    symb κ z e = ∫ t : ℝ, Complex.exp (z * t) • κ t e := by
  have c1 : Continuous fun t : ℝ => Complex.exp (z * t) • κ t :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).smul hk.1
  have s1 : HasCompactSupport fun t : ℝ => Complex.exp (z * t) • κ t := hk.2.mono fun t ht h => ht (by simp [h])
  exact ContinuousLinearMap.integral_apply (c1.integrable_of_hasCompactSupport s1) e

theorem UpperTheory.V.Z.IntegralApplyAeEq.planch :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (κ : ℝ → V →L[ℂ] W) (K : ℝ), Ker κ → (∀ y : ℝ, ‖symb κ (1 + y * Complex.I)‖ ≤ K / (1 + |y|)) →
      ∀ e, WLe (-2) (kv κ e) (K / √3 * ‖e‖) := by
  intro V _ _ _ _ W _ _ _ _ κ K hk hb e
  let f : ℝ → W := fun t => (Real.exp t : ℂ) • κ t e
  have fc : Continuous f := (Complex.continuous_ofReal.comp Real.continuous_exp).smul (hk.1.clm_apply continuous_const)
  have fs : HasCompactSupport f := hk.2.mono fun t ht h => ht (by simp [f, h])
  have fm : MemLp f 2 volume := fc.memLp_of_hasCompactSupport fs
  have fi : Integrable f := fc.integrable_of_hasCompactSupport fs
  have e1 : ∀ᵐ x : ℝ, ‖f (-x)‖ ^ 2 = Real.exp (-2 * x) * ‖kv κ e x‖ ^ 2 := by
    filter_upwards [((kvSpec κ hk).1 e).1] with x hx
    rw [hx, norm_smul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_nat_mul]
    congr 2; push_cast; ring
  have i2 : Integrable fun x => ‖f x‖ ^ 2 := (memLp_two_iff_integrable_sq_norm fc.aestronglyMeasurable).1 fm
  refine ⟨i2.comp_neg.congr e1, ?_⟩
  rw [← integral_congr_ae e1, integral_neg_eq_self fun x => ‖f x‖ ^ 2]
  have nn : ∀ u : L W, ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 := fun u => by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), L2.inner_def, ← integral_re (L2.integrable_inner u u)]
    simp only [inner_self_eq_norm_sq]
  have e2 : ∫ x, ‖f x‖ ^ 2 = ‖Lp.fourierTransformₗᵢ ℝ W (fm.toLp f)‖ ^ 2 := by
    rw [LinearIsometryEquiv.norm_map, nn]
    exact integral_congr_ae (fm.coeFn_toLp.mono fun x hx => by simp only [hx])
  have hF : ∀ ξ : ℝ, 𝓕 f ξ = symb κ (1 + ((-(2 * Real.pi * ξ) : ℝ) : ℂ) * Complex.I) e := fun ξ => by
    rw [Real.fourier_real_eq_integral_exp_smul, symb_app κ hk]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [f, smul_smul, Complex.ofReal_exp, ← Complex.exp_add]
    congr 2; push_cast; ring
  obtain ⟨ri, rv⟩ := r_int
  rw [e2, nn]
  calc _ ≤ ∫ ξ, (K * ‖e‖) ^ 2 * ((1 + |2 * Real.pi * ξ|) ^ 2)⁻¹ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
          ((ri.comp_mul_left' (R := 2 * Real.pi) (by positivity)).const_mul _) ?_
        filter_upwards [fourAe (fm.toLp f) (fi.congr fm.coeFn_toLp.symm)] with ξ hξ
        rw [hξ, Real.fourier_congr_ae fm.coeFn_toLp, hF]
        have h1 := (symb κ _).le_of_opNorm_le (hb (-(2 * Real.pi * ξ))) e
        rw [abs_neg] at h1
        refine (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans_eq ?_
        field_simp
    _ = (K * ‖e‖) ^ 2 * (|(2 * Real.pi)⁻¹| * 2) := by
        rw [integral_const_mul, Measure.integral_comp_mul_left (fun y : ℝ => ((1 + |y|) ^ 2)⁻¹), smul_eq_mul, rv]
    _ ≤ _ := by
        rw [div_mul_eq_mul_div, div_pow, Real.sq_sqrt (by norm_num), div_eq_mul_inv, abs_of_pos (by positivity)]
        gcongr
        rw [mul_inv, mul_right_comm, inv_mul_cancel₀ two_ne_zero, one_mul]
        exact inv_anti₀ (by norm_num) Real.pi_gt_three.le
end

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.traceSm :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (N : W ≃ₗᵢ[ℂ] V), M.IsN (N.toLinearEquiv : W →ₗ[ℂ] V) → ∀ (X : H →L[ℂ] H) (κ : ℝ → V →L[ℂ] W), Ker κ → M.Carries X κ → ∀ (ψ : ℝ → ℝ) (δ T K : ℝ), δ ≤ 1 / 2 → Bump ψ (-δ) 0 → M.T₀ ≤ T →
      IsTraceClass (M.abelian₂ T T ∘L X ∘L M.abelian₂ T T) → (∀ z : ℂ, |z.re| ≤ 1 → ‖symb κ z‖ ≤ K / (1 + |z.im|)) →
      ‖trace (M.abelian₂ T T ∘L (M.F.av (fun t => (ψ t : ℂ)) ∘L X) ∘L M.abelian₂ T T) -
          (1 / 2 : ℂ) * LinearMap.trace ℂ V ((N.toLinearEquiv : W →ₗ[ℂ] V) ∘ₗ (symb κ 0 : V →ₗ[ℂ] W))‖ ≤
        Module.finrank ℂ V * Real.exp (2 * M.T₀) * K * Real.exp (-2 * T) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M N hN X κ hk hX ψ δ T K hδ hψ hT htc hb
  obtain ⟨hk', -, hs'⟩ := convAdj κ hk
  obtain ⟨s0, hi, -⟩ := avApprox.2.1 ψ _ _ hψ
  have cc : Continuous fun t => (ψ t : ℂ) := Complex.continuous_ofReal.comp hψ.cont
  have sc : HasCompactSupport fun t => (ψ t : ℂ) := s0.comp_left Complex.ofReal_zero
  have cn : Continuous fun t => (ψ (-t) : ℂ) := cc.comp continuous_neg
  have z : ∀ t, 1 / 2 < |t| → ψ t = 0 := fun t ht => hψ.supp t fun h => by
    have : |t| ≤ 1 / 2 := abs_le.2 ⟨by linarith [h.1], h.2.trans (by norm_num)⟩
    linarith
  have n1 : ∫ x, ‖(ψ x : ℂ)‖ = 1 := by
    simp only [Complex.norm_real, Real.norm_of_nonneg (hψ.nonneg _)]; exact hψ.total
  have n2 : ∫ x, ‖(ψ (-x) : ℂ)‖ = 1 := (integral_neg_eq_self (fun x => ‖(ψ x : ℂ)‖) _).trans n1
  have n3 : ∫ x, (ψ x : ℂ) = 1 := by rw [integral_complex_ofReal, hψ.total]; simp
  have K0 : 0 ≤ K := by simpa using (norm_nonneg _).trans (hb 0 (by simp))
  have Q0 : 0 ≤ K / √3 := by positivity
  have w1 := planch κ K hk fun y => by simpa using hb (1 + y * Complex.I) (by simp)
  have w2 := planch (sharp κ) K hk' fun y => by
    rw [hs', LinearIsometryEquiv.norm_map]
    simpa using hb (-conj (1 + y * Complex.I)) (by simp)
  obtain ⟨f1, f2⟩ := traceFar M X κ hk hX ψ δ T hψ hT htc
  set e := stdOrthonormalBasis ℂ V
  set f := stdOrthonormalBasis ℂ W
  set c : _ → ℝ → ℂ := fun i => M.cor (fun x => (ψ x : ℂ)) (e i) (kv κ (e i)) with hc
  set d : _ → ℝ → ℂ := fun j => M.swap.cor (fun x => (ψ (-x) : ℂ)) (f j) (kv (sharp κ) (f j)) with hd
  have c0 : ∀ i, Continuous (c i) := fun i => continuous_const.inner (M.F.cont _)
  have d0 : ∀ j, Continuous (d j) := fun j => continuous_const.inner (M.swap.F.cont _)
  have sub : ∀ {ι : Type} [Fintype ι] (g : ι → ℝ → ℂ), (∀ i, Continuous (g i)) → ∀ a b : ℝ,
      ∫ y in a..b, ∑ i, g i (2 * y) = (1 / 2 : ℂ) * ∑ i, ∫ s in (2 * a)..(2 * b), g i s := by
    intro ι _ g hg a b
    rw [intervalIntegral.integral_finsetSum fun i _ =>
      (show Continuous fun y => g i (2 * y) from (hg i).comp (continuous_const.mul continuous_id)).intervalIntegrable _ _, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_comp_mul_left _ two_ne_zero]
    simp
  set B : ℝ := 6 / 5 * Real.exp (2 * M.T₀) * (K / √3) * Real.exp (-(2 * T)) with hB
  have tc : ∀ i β, 2 * T ≤ β → ‖∫ s in (2 * T)..β, c i s‖ ≤ B := fun i β hβ => by
    have := tailB M _ (e i) _ _ _ β cc (fun x hx => by rw [z x hx]; simp) n1.le (mul_nonneg Q0 (norm_nonneg _)) (w1 (e i)) hβ
    simpa [e.orthonormal.1 i, hB] using this
  have td : ∀ j β, 2 * T ≤ β → ‖∫ s in (2 * T)..β, d j s‖ ≤ B := fun j β hβ => by
    have := tailB M.swap _ (f j) _ _ _ β cn (fun x hx => by rw [z (-x) (by rwa [abs_neg])]; simp) n2.le
      (mul_nonneg Q0 (norm_nonneg _)) (w2 (f j)) hβ
    simp only [f.orthonormal.1 j, mul_one] at this
    exact this
  have lim : ∀ i, Tendsto (fun a : ℝ => ∫ s in (2 * T - 2 * a)..(2 * T + 2 * a), c i s) atTop (𝓝 ⟪e i, N (symb κ 0 (e i))⟫_ℂ) := fun i => by
    obtain ⟨-, k1, k2⟩ := (kvSpec κ hk).1 (e i)
    have := (corLim M _ hN _ (e i) _ (2 * T) cc sc k1).2
    rw [n3, map_one, one_mul, k2] at this
    exact this.comp (tendsto_id.const_mul_atTop two_pos)
  have tot := f2.add ((tendsto_finsetSum Finset.univ fun i _ => lim i).const_mul (1 / 2 : ℂ))
  rw [zero_add] at tot
  rw [LinearMap.trace_eq_sum_inner _ e]
  refine le_of_tendsto ((tendsto_const_nhds.sub tot).norm) ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
  have id1 := traceId M X κ hk hX ψ δ T a hψ hT ha f1
  rw [(bandTC M X κ hk hX ψ δ T (T + a) hψ (by linarith)).2.2.2.2, (bandTC M X κ hk hX ψ δ (T - a) T hψ (by linarith)).2.2.2.1,
    sub c c0, sub d d0] at id1
  have sp : ∀ i, ∫ s in (2 * T - 2 * a)..(2 * T + 2 * a), c i s =
      (∫ s in (2 * (T - a))..(2 * T), c i s) + ∫ s in (2 * T)..(2 * T + 2 * a), c i s := fun i => by
    rw [intervalIntegral.integral_add_adjacent_intervals ((c0 i).intervalIntegrable _ _) ((c0 i).intervalIntegrable _ _), mul_sub]
  simp only [sp, Finset.sum_add_distrib]
  rw [eq_sub_of_add_eq id1]
  have hd' : Module.finrank ℂ W = Module.finrank ℂ V := N.toLinearEquiv.finrank_eq
  have b1 : ‖∑ i, ∫ s in (2 * T)..(2 * T + 2 * a), c i s‖ ≤ Module.finrank ℂ V * B := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ B fun i _ => tc i _ (by linarith)).trans_eq ?_)
    simp
  have b2 : ‖∑ j, ∫ s in (2 * T)..(2 * (T + a)), d j s‖ ≤ Module.finrank ℂ V * B := by
    rw [← hd']
    refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ B fun j _ => td j _ (by linarith)).trans_eq ?_)
    simp
  have alg : ∀ R x y w : ℂ, R + 1 / 2 * x - conj (1 / 2 * w) - (R + 1 / 2 * (x + y)) = -(conj (1 / 2 * w) + 1 / 2 * y) := by
    intros; ring
  rw [alg, norm_neg]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_conj, norm_mul, norm_mul]
  have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  have h3 : 6 / 5 * (K / √3) ≤ K := by
    have : (6 / 5 : ℝ) ≤ √3 := Real.le_sqrt_of_sq_le (by norm_num)
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  have h4 : B ≤ Real.exp (2 * M.T₀) * K * Real.exp (-2 * T) := by
    rw [hB, neg_mul, show 6 / 5 * Real.exp (2 * M.T₀) * (K / √3) = Real.exp (2 * M.T₀) * (6 / 5 * (K / √3)) by ring]
    gcongr
  have h5 : (Module.finrank ℂ V : ℝ) * B ≤ Module.finrank ℂ V * (Real.exp (2 * M.T₀) * K * Real.exp (-2 * T)) := by gcongr
  rw [h2]
  linarith
