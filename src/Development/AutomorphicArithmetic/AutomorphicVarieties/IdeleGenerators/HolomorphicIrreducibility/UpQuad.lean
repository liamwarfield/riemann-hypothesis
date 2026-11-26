module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcPolar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeOperatorsCommuteOnAutomorphicForms
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolCap

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.UpQuad
open UpperTheory.V.Af UpperTheory.V.Af.Bc in
theorem UpperTheory.V.Sd.upQuad :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Sd.UpQuad := by
  intro hP F E Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι hE n _ hn r hr ⟨π, hreg, hatt⟩ hirr
  obtain ⟨P, hBC⟩ := (UpperTheory.V.Br.quadBCw hP F E hE n hn π hreg).resolve_left
    fun ⟨η, hη, ht⟩ => Bc.noTwist hP F E Ω l ι hE n r π hr hatt hirr η hη ht
  have h := UpperTheory.V.Br.bcAtt0 F E Ω l ι n r π P hBC.toIsBC0
  exact ⟨P, h.1 hreg, h.2 hatt ((Bc.irrBasic.1 _ Unit _ n _).2.1 hirr)⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolLin
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PrincipalCongruenceAntitone
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsOpenStabilizerAddSmul
theorem UpperTheory.isOpen_stabilizer_add_smul :
    ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ G V) (a b : V) (z : ℂ),
        IsOpen {g : G | ρ g a = a} → IsOpen {g : G | ρ g b = b} → IsOpen {g : G | ρ g (a + z • b) = a + z • b} := by
  intro G V _ _ _ _ _ ρ a b z ha hb
  rw [isOpen_iff_mem_nhds]
  intro g hg
  have hg' : ρ g (a + z • b) = a + z • b := hg
  have hc : Continuous fun x : G => g⁻¹ * x := continuous_const.mul continuous_id
  have hU : IsOpen ((fun x : G => g⁻¹ * x) ⁻¹' ({g : G | ρ g a = a} ∩ {g : G | ρ g b = b})) :=
    (ha.inter hb).preimage hc
  refine Filter.mem_of_superset (hU.mem_nhds ?_) ?_
  · simp
  · intro x hx
    have h1 : ρ (g⁻¹ * x) a = a := hx.1
    have h2 : ρ (g⁻¹ * x) b = b := hx.2
    have h3 : ρ (g⁻¹ * x) (a + z • b) = a + z • b := by
      rw [map_add (f := _), map_smul, h1, h2]
    have h4 : x = g * (g⁻¹ * x) := by group
    show ρ x (a + z • b) = a + z • b
    rw [h4, map_mul, Module.End.mul_apply, h3, hg']
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MirabolicRowCongruence
theorem UpperTheory.mirabolic_row_congruence :
    ∀ {R : Type} [CommRing R] (I J : Ideal R) (g : GL (Fin 2) R), I ≤ J →
        Matrix.vecMul ![0, 1] ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) g : GL (Fin 2) (R ⧸ I)) : Matrix (Fin 2) (Fin 2) (R ⧸ I)) = ![0, 1] →
        Matrix.vecMul ![0, 1] ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk J) g : GL (Fin 2) (R ⧸ J)) : Matrix (Fin 2) (Fin 2) (R ⧸ J)) = ![0, 1] := by
  intro R _ I J g hIJ h
  have key : ∀ (K : Ideal R) (j : Fin 2),
      Matrix.vecMul ![0, 1] ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk K) g :
        GL (Fin 2) (R ⧸ K)) : Matrix (Fin 2) (Fin 2) (R ⧸ K)) j
        = Ideal.Quotient.mk K ((g : Matrix (Fin 2) (Fin 2) R) 1 j) := by
    intro K j
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.GeneralLinearGroup.map]
  funext j
  have hj := congrArg (Ideal.Quotient.factor hIJ) ((key I j).symm.trans (congrFun h j))
  rw [Ideal.Quotient.factor_mk] at hj
  rw [key J j, hj]
  fin_cases j <;> simp
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ModerateGrowthAddSmul
theorem UpperTheory.moderate_growth_add_smul :
    ∀ {Y : Type} (h : Y → ℝ) (f g : Y → ℂ) (z : ℂ), (∀ y, 1 ≤ h y) →
        (∃ (C : ℝ) (N : ℕ), ∀ y, ‖f y‖ ≤ C * h y ^ N) → (∃ (C : ℝ) (N : ℕ), ∀ y, ‖g y‖ ≤ C * h y ^ N) →
        ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f y + z * g y‖ ≤ C * h y ^ N := by
  intro Y h f g z hh ⟨C, N, hf⟩ ⟨D, M, hg⟩
  refine ⟨|C| + ‖z‖ * |D|, N + M, fun y => ?_⟩
  have h0 : 0 ≤ h y := zero_le_one.trans (hh y)
  have h1 : ‖f y‖ ≤ |C| * h y ^ (N + M) :=
    (hf y).trans (mul_le_mul (le_abs_self C)
      (pow_le_pow_right₀ (hh y) (Nat.le_add_right N M)) (pow_nonneg h0 _) (abs_nonneg C))
  have h2 : ‖g y‖ ≤ |D| * h y ^ (N + M) :=
    (hg y).trans (mul_le_mul (le_abs_self D)
      (pow_le_pow_right₀ (hh y) (Nat.le_add_left M N)) (pow_nonneg h0 _) (abs_nonneg D))
  calc ‖f y + z * g y‖ ≤ ‖f y‖ + ‖z * g y‖ := norm_add_le _ _
    _ = ‖f y‖ + ‖z‖ * ‖g y‖ := by rw [norm_mul]
    _ ≤ |C| * h y ^ (N + M) + ‖z‖ * (|D| * h y ^ (N + M)) :=
        add_le_add h1 (mul_le_mul_of_nonneg_left h2 (norm_nonneg z))
    _ = (|C| + ‖z‖ * |D|) * h y ^ (N + M) := by ring
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FiniteSpanAddSmul
theorem UpperTheory.finite_span_add_smul :
    ∀ {ι V : Type} [AddCommGroup V] [Module ℂ V] (T : ι → V →ₗ[ℂ] V) (S : Set ι) (a b : V) (z : ℂ),
        FiniteDimensional ℂ (Submodule.span ℂ ((fun i => T i a) '' S)) →
        FiniteDimensional ℂ (Submodule.span ℂ ((fun i => T i b) '' S)) →
        FiniteDimensional ℂ (Submodule.span ℂ ((fun i => T i (a + z • b)) '' S)) := by
  intro ι V _ _ T S a b z ha hb
  have hle : Submodule.span ℂ ((fun i => T i (a + z • b)) '' S) ≤
      Submodule.span ℂ ((fun i => T i a) '' S) ⊔ Submodule.span ℂ ((fun i => T i b) '' S) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    simp only [map_add (f := _), map_smul, SetLike.mem_coe]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨i, hi, rfl⟩)
      (Submodule.smul_mem _ z (Submodule.subset_span ⟨i, hi, rfl⟩))
  exact Submodule.finiteDimensional_of_le hle
end

open UpperTheory.V.Sd UpperTheory.V.TR in
private theorem UpperTheory.Reformulated.B.Gr32.aut_zero {F : Type} [Field F] [NumberField F] [NumberField.IsTotallyReal F] :
    IsAutForm (0 : Sm F 2) := by
  refine ⟨fun _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · simp only [map_zero, Set.setOf_true, isOpen_univ]
  · refine Submodule.finiteDimensional_of_le (S₂ := ⊥) ?_
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    simp
  · refine Submodule.finiteDimensional_of_le (S₂ := ⊥) ?_
    rw [Submodule.span_le]
    rintro _ ⟨k, _, rfl⟩
    simp
  · intro g
    exact ⟨0, 0, fun y => by simp⟩

open UpperTheory.V.Sd UpperTheory.V.TR in
private theorem UpperTheory.Reformulated.B.Gr32.aut_lin {F : Type} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    {φ ψ : Sm F 2} (z : ℂ) (hφ : IsAutForm φ) (hψ : IsAutForm ψ) : IsAutForm (φ + z • ψ) := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := hφ
  obtain ⟨b1, b2, b3, b4, b5⟩ := hψ
  refine ⟨fun γ g => ?_, UpperTheory.isOpen_stabilizer_add_smul _ φ ψ z a2 b2, ?_, UpperTheory.finite_span_add_smul (fun x => x) _ φ ψ z a4 b4, fun g => ?_⟩
  · change φ.1 _ + z * ψ.1 _ = φ.1 _ + z * ψ.1 _
    rw [a1, b1]
  · rw [← Set.image_univ] at a3 b3 ⊢
    exact UpperTheory.finite_span_add_smul (fun k => cptRep F 2 k) _ φ ψ z a3 b3
  · refine UpperTheory.moderate_growth_add_smul (fun y : GL (Fin 2) (Rinf F) => height y) (fun y => φ.1 (g * infGL F 2 y))
      (fun y => ψ.1 (g * infGL F 2 y)) z (fun y => ?_) (a5 g) (b5 g)
    unfold height
    have h1 := norm_nonneg (toL (y : Matrix (Fin 2) (Fin 2) (Rinf F)))
    have h2 := norm_nonneg (toL ((y⁻¹ : GL (Fin 2) (Rinf F)) : Matrix (Fin 2) (Fin 2) (Rinf F)))
    linarith

open UpperTheory.V.Sd in
private theorem UpperTheory.Reformulated.B.Gr32.principal_congruence_antitone {F : Type} [Field F] [NumberField F]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) {m n : ℕ} (h : m ≤ n) :
    K1 w n ≤ K1 w m := by
  unfold K1
  refine Subgroup.map_mono fun g hg => ?_
  exact UpperTheory.mirabolic_row_congruence _ _ g (Ideal.pow_le_pow_right h) hg

open UpperTheory.V.Sd in
private theorem UpperTheory.Reformulated.B.Gr32.coefAt_lin {F : Type} [Field F] [NumberField F]
    (a b : Ideal (NumberField.RingOfIntegers F) → ℂ) (z : ℂ) (y : GlobalTheory.CuspRep.Af F) :
    coefAt (a + z • b) y = coefAt a y + z * coefAt b y := by
  unfold coefAt
  split_ifs <;> simp

open UpperTheory.V.Sd in
private theorem UpperTheory.Reformulated.B.Gr32.coefAt_zero {F : Type} [Field F] [NumberField F]
    (y : GlobalTheory.CuspRep.Af F) : coefAt (0 : Ideal (NumberField.RingOfIntegers F) → ℂ) y = 0 := by
  unfold coefAt
  split_ifs <;> simp

theorem UpperTheory.Reformulated.B.Gr32.holLin :
    UpperTheory.V.Sd.HolLin := by
  intro F _ _ _ k c ω
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨UpperTheory.Reformulated.B.Gr32.aut_zero, fun w => Submodule.zero_mem _, fun z g => ?_, fun v => ?_, fun v => ?_⟩
    · simp
    · simp
    · simp
  · intro x y _ yf
    simp only [UpperTheory.Reformulated.B.Gr32.coefAt_zero, zero_mul, Pi.zero_apply, zero_div, sub_zero]
    exact hasSum_zero
  · rintro φ ψ z ⟨a1, a2, a3, a4, a5⟩ ⟨b1, b2, b3, b4, b5⟩
    refine ⟨UpperTheory.Reformulated.B.Gr32.aut_lin z a1 b1,
      fun w => Submodule.add_mem _ (a2 w) (Submodule.smul_mem _ z (b2 w)), fun u g => ?_, fun v => ?_, fun v => ?_⟩
    · change φ.1 _ + z * ψ.1 _ = _ * (φ.1 _ + z * ψ.1 _)
      rw [a3, b3]
      ring
    · simp only [map_add (f := _), map_smul]
      linear_combination (norm := module) a4 v + z • b4 v
    · simp only [map_add (f := _), map_smul]
      linear_combination (norm := module) a5 v + z • b5 v
  · intro φ ψ z c₀ a d₀ b h1 h2 x y hy yf
    have h := (h1 x y hy yf).add ((h2 x y hy yf).mul_left z)
    convert (preTransparency := .reducible) h using 1
    · funext ξ
      rw [UpperTheory.Reformulated.B.Gr32.coefAt_lin]
      ring
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  · rintro φ c' hc ⟨a1, a2, a3, a4, a5⟩
    refine ⟨a1, fun w => ?_, a3, a4, a5⟩
    have h : φ ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd (UpperTheory.V.Sd.locSm F w) (UpperTheory.V.Sd.K1 w (c w)) := a2 w
    show φ ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd (UpperTheory.V.Sd.locSm F w) (UpperTheory.V.Sd.K1 w (c' w))
    exact fun g hg => h g (UpperTheory.Reformulated.B.Gr32.principal_congruence_antitone w (hc w) hg)
end

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V.Af

namespace UpperTheory.V.Sd

end UpperTheory.V.Sd

open UpperTheory.V UpperTheory.V.Sd in
theorem UpperTheory.V.Sd.holLin :
    UpperTheory.V.Sd.HolLin :=
  _root_.UpperTheory.Reformulated.B.Gr32.holLin
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ExpInj
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep Filter Topology
open scoped Matrix

namespace UpperTheory.V.Sd

variable {F : Type} [Field F] [NumberField F]

private def rotA (θ : TR.Rinf F) : GL (Fin 2) (TR.Rinf F) where
  val := !![fun v => Real.cos (θ v), fun v => Real.sin (θ v); fun v => -Real.sin (θ v), fun v => Real.cos (θ v)]
  inv := !![fun v => Real.cos (θ v), fun v => -Real.sin (θ v); fun v => Real.sin (θ v), fun v => Real.cos (θ v)]
  val_inv := by
    ext i j v
    have := Real.sin_sq_add_cos_sq (θ v)
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> nlinarith
  inv_val := by
    ext i j v
    have := Real.sin_sq_add_cos_sq (θ v)
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> nlinarith

omit [NumberField F] in
private theorem rotA_add (θ η : TR.Rinf F) : rotA (θ + η) = rotA θ * rotA η := by
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rotA, Matrix.mul_apply, Fin.sum_univ_succ, Real.cos_add, Real.sin_add] <;> ring

omit [NumberField F] in
private theorem rotA_zero : rotA (0 : TR.Rinf F) = 1 := by
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rotA]

private theorem rotA_deriv (θ : TR.Rinf F) :
    HasDerivAt (fun t : ℝ => TR.toL (rotA (t • θ)).val) (TR.toL !![0, θ; -θ, 0]) 0 := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
  have h : HasDerivAt (fun t : ℝ => t * θ v) (θ v) 0 := by simpa using (hasDerivAt_id (0 : ℝ)).mul_const (θ v)
  fin_cases i <;> fin_cases j
  · simpa [rotA] using h.cos
  · simpa [rotA] using h.sin
  · simpa [rotA] using h.sin.fun_neg
  · simpa [rotA] using h.cos

variable [IsTotallyReal F]

private theorem lie_rot {k : ℕ} {φ : TR.Sm F 2} (hw : ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * k) • φ)
    (θ : TR.Rinf F) : TR.lie F 2 (TR.toL !![0, θ; -θ, 0]) φ = (Complex.I * k * ((∑ v, θ v : ℝ) : ℂ)) • φ := by
  classical
  have e : (TR.toL !![0, θ; -θ, 0] : TR.Lie F 2) = ∑ v, θ v • ((TR.toL (Matrix.single 0 1 (Pi.single v 1)) : TR.Lie F 2) -
      TR.toL (Matrix.single 1 0 (Pi.single v 1))) := by
    ext i j w
    fin_cases i <;> fin_cases j <;> simp [Finset.sum_apply, Matrix.single, Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum, LinearMap.sum_apply, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_smul, map_sub, LinearMap.smul_apply, LinearMap.sub_apply, mul_comm, mul_smul, ← hw v]
  simp only [TR.Eop]
  congr!

private theorem norm_rot {k : ℕ} {φ : TR.Sm F 2} (hw : ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * k) • φ)
    (θ : TR.Rinf F) (g : GA F 2) : ‖φ.1 (g * TR.infGL F 2 (rotA θ))‖ = ‖φ.1 g‖ := by
  set s : ℂ := Complex.I * k * ((∑ v, θ v : ℝ) : ℂ) with hs
  set f : ℝ → ℂ := fun t => φ.1 (g * TR.infGL F 2 (rotA (t • θ))) with hf
  have hd : ∀ t, HasDerivAt f (s * f t) t := fun t => by
    have h1 := TR.hasDerivAt_curve φ (g * TR.infGL F 2 (rotA (t • θ))) (fun u : ℝ => rotA (u • θ)) _
      (by simp [rotA_zero]) (rotA_deriv θ)
    rw [← TR.lie_apply, lie_rot hw] at h1
    have h2 : HasDerivAt (fun u : ℝ => f (t + u)) (s * f t) 0 := by
      convert h1 using 2
      · simp only [hf, add_smul, rotA_add, map_mul, mul_assoc]
    have h3 := HasDerivAt.comp_add_const t (-t) (f := fun u : ℝ => f (t + u)) (by simpa using h2)
    simpa using h3
  have he : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-s * t)) (Complex.exp (-s * t) * -s) t := fun t => by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-s)).cexp
  have hz : ∀ t, HasDerivAt (fun t : ℝ => f t * Complex.exp (-s * t)) 0 t := fun t => by
    have := (hd t).fun_mul (he t)
    rwa [show s * f t * Complex.exp (-s * t) + f t * (Complex.exp (-s * t) * -s) = 0 by ring] at this
  have hc := is_const_of_deriv_eq_zero (fun t => (hz t).differentiableAt) (fun t => (hz t).deriv) 1 0
  have hn : ‖Complex.exp (-s)‖ = 1 := by
    rw [Complex.norm_exp, hs]
    simp
  have := congrArg norm hc
  simpa [hf, hn, rotA_zero] using this

omit [NumberField F] [IsTotallyReal F] in
private theorem iwasawa (h : GL (Fin 2) (TR.Rinf F)) (hd : ∀ v, 0 < (h : Matrix (Fin 2) (Fin 2) (TR.Rinf F)).det v) :
    ∃ (ρ y : (TR.Rinf F)ˣ) (x θ : TR.Rinf F), h = Matrix.GeneralLinearGroup.scalar (Fin 2) ρ * (aff y x * rotA θ) ∧
      (∀ v, 0 < y.val v) ∧ ∀ v, y.val v = (h : Matrix (Fin 2) (Fin 2) (TR.Rinf F)).det v / (h 1 0 v ^ 2 + h 1 1 v ^ 2) := by
  let z : InfinitePlace F → ℂ := fun v => ⟨h 1 1 v, -h 1 0 v⟩
  have hdet : ∀ v, (h : Matrix (Fin 2) (Fin 2) (TR.Rinf F)).det v = h 0 0 v * h 1 1 v - h 0 1 v * h 1 0 v := fun v => by
    rw [Matrix.det_fin_two]; rfl
  have hz : ∀ v, z v ≠ 0 := fun v h0 => by
    have h1 : h 1 1 v = 0 := congrArg Complex.re h0
    have h2 : -h 1 0 v = 0 := congrArg Complex.im h0
    have := hd v
    rw [hdet, h1, neg_eq_zero.1 h2] at this
    simp at this
  have hr : ∀ v, 0 < ‖z v‖ := fun v => norm_pos_iff.2 (hz v)
  have hsq : ∀ v, h 1 0 v ^ 2 + h 1 1 v ^ 2 = ‖z v‖ ^ 2 := fun v => by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp only [z]; ring
  have hy : ∀ v, 0 < (h : Matrix (Fin 2) (Fin 2) (TR.Rinf F)).det v / (h 1 0 v ^ 2 + h 1 1 v ^ 2) := fun v =>
    div_pos (hd v) (by rw [hsq]; exact pow_pos (hr v) 2)
  let U : (f : TR.Rinf F) → (∀ v, 0 < f v) → (TR.Rinf F)ˣ := fun f hf =>
    ⟨f, fun v => (f v)⁻¹, funext fun v => mul_inv_cancel₀ (hf v).ne', funext fun v => inv_mul_cancel₀ (hf v).ne'⟩
  refine ⟨U _ hr, U _ hy, fun v => (h 0 0 v * h 1 0 v + h 0 1 v * h 1 1 v) / (h 1 0 v ^ 2 + h 1 1 v ^ 2),
    fun v => Complex.arg (z v), ?_, hy, fun v => rfl⟩
  ext i j v
  have hc : Real.cos (Complex.arg (z v)) = h 1 1 v / ‖z v‖ := Complex.cos_arg (hz v)
  have hs : Real.sin (Complex.arg (z v)) = -h 1 0 v / ‖z v‖ := Complex.sin_arg _
  have h0 := (hr v).ne'
  have h1 := hsq v
  fin_cases i <;> fin_cases j <;>
    simp [U, rotA, aff, Matrix.mul_apply, Fin.sum_univ_succ, hc, hs, hdet, h1, Matrix.GeneralLinearGroup.scalar] <;>
    field_simp
  · linear_combination (-(h.val 0 0 v)) * h1
  · linear_combination (-(h.val 0 1 v)) * h1

omit [IsTotallyReal F] in
private theorem absF_pos (y : (Af F)ˣ) : 0 < absF y := by
  refine finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun w => norm_pos_iff.2 ?_
  exact (y.isUnit.map (pLoc F w)).ne_zero

private theorem infGL_scalar (ρ : (TR.Rinf F)ˣ) :
    TR.infGL F 2 (Matrix.GeneralLinearGroup.scalar (Fin 2) ρ) = Matrix.GeneralLinearGroup.scalar (Fin 2) (TR.infId F ρ) := by
  have h1 : TR.pInf F (TR.infId F ρ).val = ρ.val := by
    change TR.pInf F (1 - TR.sInf F 1 + TR.sInf F _) = _
    have h : ∀ x, TR.pInf F (TR.sInf F x) = x := fun x => (TR.infEq F).symm_apply_apply x
    simp [h]
  have h2 : pFin F (TR.infId F ρ).val = 1 := by
    change (1 : Af F) - 0 + 0 = 1
    simp
  refine TR.ga_ext ?_ ?_
  · rw [TR.pInf_infGL]
    refine Units.ext (Matrix.ext fun i j => ?_)
    fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.map, h1]
  · rw [TR.pFin_infGL]
    refine Units.ext (Matrix.ext fun i j => ?_)
    fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.map, h2]

private theorem norm_inf {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} (hω : IsOfFinOrder ω) {φ : TR.Sm F 2} (hφ : IsHol k c ω φ)
    {c₀ a} (he : HasExp φ.1 k c₀ a) (ha : ∀ 𝔪, 𝔪 ≠ ⊥ → a 𝔪 = 0) (yf : (Af F)ˣ) (h : GL (Fin 2) (TR.Rinf F))
    (hd : ∀ v, 0 < (h : Matrix (Fin 2) (Fin 2) (TR.Rinf F)).det v) :
    ‖φ.1 (TR.infGL F 2 h * finGL F 2 (aff yf 0))‖ =
      ((∏ v, (h : Matrix (Fin 2) (Fin 2) (TR.Rinf F)).det v / (h 1 0 v ^ 2 + h 1 1 v ^ 2)) * absF yf) ^ ((k : ℝ) / 2) *
        ‖c₀ yf‖ := by
  obtain ⟨ρ, y, x, θ, e, hy, hy'⟩ := iwasawa h hd
  have hc : ∀ t, coefAt a t = 0 := fun t => by
    unfold coefAt
    split_ifs with h
    · exact ha _ h.choose_spec.1
    · rfl
  have h1 := he x y hy yf
  simp only [hc, zero_mul] at h1
  have h2 := sub_eq_zero.1 (h1.unique hasSum_zero)
  have hp : 0 < ((∏ v, y.val v) * absF yf) ^ ((k : ℝ) / 2) :=
    Real.rpow_pos_of_pos (mul_pos (Finset.prod_pos fun v _ => hy v) (absF_pos yf)) _
  rw [div_eq_iff (by exact_mod_cast hp.ne')] at h2
  have hn : ‖((ω.1 (TR.infId F ρ) : ℂˣ) : ℂ)‖ = 1 := by
    obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 hω
    have : (ω.1 (TR.infId F ρ)) ^ n = 1 := congrArg (fun χ : HChar F => χ.1 (TR.infId F ρ)) e
    have h3 : ((ω.1 (TR.infId F ρ) : ℂˣ) : ℂ) ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
    exact Complex.norm_eq_one_of_pow_eq_one h3 hn.ne'
  simp only [← hy']
  rw [e, map_mul, map_mul, infGL_scalar, mul_assoc, hφ.cent, mul_assoc, TR.infGL_comm (rotA θ), ← mul_assoc, norm_mul, hn,
    one_mul, norm_rot hφ.wt, h2, norm_mul, Complex.norm_real, Real.norm_of_nonneg hp.le, mul_comm]

private def lowA {R : Type} [CommRing R] (x : R) : GL (Fin 2) R where
  val := !![1, 0; x, 1]
  inv := !![1, 0; -x, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

private theorem map_lowA {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (x : R) :
    Matrix.GeneralLinearGroup.map p (lowA x) = lowA (p x) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [lowA, Matrix.GeneralLinearGroup.map]

private theorem continuous_lowA {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (lowA : R → GL (Fin 2) R) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [lowA] <;> fun_prop
  · change Continuous fun x : R => (!![1, 0; -x, 1] : Matrix (Fin 2) (Fin 2) R)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem const_zero {k : ℕ} (hk : 1 ≤ k) {c : Pl F → ℕ} {ω : HChar F} (hω : IsOfFinOrder ω) {φ : TR.Sm F 2}
    (hφ : IsHol k c ω φ) {c₀ a} (he : HasExp φ.1 k c₀ a) (ha : ∀ 𝔪, 𝔪 ≠ ⊥ → a 𝔪 = 0) (yf : (Af F)ˣ) : c₀ yf = 0 := by
  set t : GL (Fin 2) (Af F) := aff yf 0 with ht
  have hc : Continuous fun x : Af F => t⁻¹ * lowA x * t := (continuous_const.mul continuous_lowA).mul continuous_const
  have h0 : t⁻¹ * lowA (0 : Af F) * t ∈ {u | TR.finRep F 2 u φ = φ} := by
    have : lowA (0 : Af F) = 1 := by
      refine Units.ext (Matrix.ext fun i j => ?_)
      fin_cases i <;> fin_cases j <;> simp [lowA]
    simp [this]
  obtain ⟨n, hn⟩ := (((hc.tendsto 0).comp (GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele F)).eventually
    (hφ.aut.level.mem_nhds h0)).exists
  set N : ℕ := n.factorial with hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast n.factorial_pos
  have hn' : ∀ g, φ.1 (g * finGL F 2 (t⁻¹ * lowA (N : Af F) * t)) = φ.1 g := fun g => congrFun (congrArg Subtype.val hn) g
  have e : ratGL F 2 (lowA (N : F)) = TR.infGL F 2 (lowA (N : TR.Rinf F)) * finGL F 2 (lowA (N : Af F)) := by
    rw [← TR.infGL_mul_finGL (ratGL F 2 (lowA (N : F))), ratGL, map_lowA, map_lowA, map_lowA]
    simp only [map_natCast]
  have e2 : φ.1 (TR.infGL F 2 (lowA (N : TR.Rinf F)) * finGL F 2 t) = φ.1 (TR.infGL F 2 1 * finGL F 2 t) := by
    rw [← hφ.aut.left (lowA (N : F)) (TR.infGL F 2 1 * finGL F 2 t), e, ← hn', map_one, one_mul, mul_assoc, mul_assoc,
      ← map_mul, mul_inv_cancel_left, map_mul, mul_assoc]
  have d1 : ∀ v, ((lowA (N : TR.Rinf F) : GL (Fin 2) (TR.Rinf F)) : Matrix (Fin 2) (Fin 2) (TR.Rinf F)).det v = 1 := fun v => by
    simp [lowA, Matrix.det_fin_two]
  have n1 := norm_inf hω hφ he ha yf (lowA (N : TR.Rinf F)) fun v => by rw [d1]; exact one_pos
  have n2 := norm_inf hω hφ he ha yf 1 fun v => by simp
  rw [e2, n2] at n1
  by_contra hne
  have n3 := mul_right_cancel₀ (norm_ne_zero_iff.2 hne) n1
  have hlt : (∏ v : InfinitePlace F, (1 : ℝ) / ((N : ℝ) ^ 2 + 1)) < 1 := by
    rw [Finset.prod_const]
    refine pow_lt_one₀ (by positivity) ?_ (Finset.card_ne_zero_of_mem (Finset.mem_univ (Classical.arbitrary _)))
    rw [div_lt_one (by positivity)]
    nlinarith
  have hpos : 0 ≤ (∏ v : InfinitePlace F, (1 : ℝ) / ((N : ℝ) ^ 2 + 1)) := by positivity
  have hA := absF_pos yf
  have hk' : (0 : ℝ) < (k : ℝ) / 2 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have := Real.rpow_lt_rpow (mul_nonneg hpos hA.le) (mul_lt_mul_of_pos_right hlt hA) hk'
  simp only [d1] at n3
  refine this.ne ?_
  convert n3.symm using 4 <;> simp [lowA]

end UpperTheory.V.Sd

theorem UpperTheory.V.Sd.expInj :
    UpperTheory.V.Sd.ExpInj := by
  intro F _ _ _ k hk c ω hω φ hφ c₀ a he ha
  refine Subtype.ext (funext fun g => ?_)
  obtain ⟨γ, h, y, u, hu, hd, rfl⟩ := UpperTheory.V.Sd.strongApp F
    { carrier := {u | UpperTheory.V.TR.finRep F 2 u φ = φ}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at *
        rw [map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] } hφ.aut.level g
  have hu' : ∀ g, φ.1 (g * finGL F 2 u) = φ.1 g := fun g => congrFun (congrArg Subtype.val hu) g
  rw [hφ.aut.left, map_mul, ← mul_assoc, hu']
  have := UpperTheory.V.Sd.norm_inf hω hφ he ha y h hd
  rw [UpperTheory.V.Sd.const_zero hk hω hφ he ha y, norm_zero, mul_zero] at this
  exact norm_eq_zero.1 this
end
end
