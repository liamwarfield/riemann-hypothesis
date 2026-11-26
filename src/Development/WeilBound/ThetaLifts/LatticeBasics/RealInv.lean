module

public import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
public import Development.WeilBound.ThetaLifts.LatticeBasics.ExistsRealStructure
public import Development.WeilBound.ThetaLifts.SchwartzMoments.SchwartzDqTendsto

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.TwistedProofs.EqZeroOfForallNhds
open Filter Topology

namespace GlobalTheory.CompanionTheory.Twist.FockLogDeriv

theorem eq_zero_of_forall_nhds {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hT : ∀ b, (∀ y, T y b = 0) → b = 0)
    (y₀ : V) (U : Set V) (hU : U ∈ 𝓝 y₀) (b : V) (hb : ∀ y ∈ U, T y b = 0) : b = 0 := by
  apply hT
  intro z
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  have h0 : T y₀ b = 0 := hb y₀ (hball (Metric.mem_ball_self hε))
  have hz1 : 0 < ‖z‖ + 1 := by positivity
  set t : ℝ := ε / (2 * (‖z‖ + 1)) with ht
  have htpos : 0 < t := by positivity
  have htz : t * (‖z‖ + 1) = ε / 2 := by
    rw [ht]; field_simp
  have hmem : y₀ + t • z ∈ U := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg htpos.le]
    nlinarith [norm_nonneg z]
  have h1 := hb _ hmem
  rw [map_add (f := _), LinearMap.add_apply, map_smul, LinearMap.smul_apply, h0, zero_add, smul_eq_mul] at h1
  exact (mul_eq_zero.mp h1).resolve_left htpos.ne'

theorem main {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hT : ∀ b, (∀ y, T y b = 0) → b = 0)
    (Jm : V × V →ₗ[ℝ] V × V) (f₀ : SchwartzMap V ℂ) (hf : f₀ ≠ 0)
    (hE : ∀ (p : V × V) (y : V), fderiv ℝ f₀ y (Jm p).1
        + (-(2 * Real.pi * Complex.I)) * ((T y (Jm p).2 : ℝ) : ℂ) * f₀ y
      = Complex.I * (fderiv ℝ f₀ y p.1
        + (-(2 * Real.pi * Complex.I)) * ((T y p.2 : ℝ) : ℂ) * f₀ y)) :
    ∃ m : V →ₗ[ℝ] V →ₗ[ℝ] ℂ, ∀ a y, fderiv ℝ f₀ y a = m a y * f₀ y := by
  let Φ : V × V →ₗ[ℝ] (V → ℂ) :=
    { toFun := fun p y => fderiv ℝ f₀ y p.1 + (-(2 * Real.pi * Complex.I)) * ((T y p.2 : ℝ) : ℂ) * f₀ y
      map_add' := by
        intro p q
        funext y
        simp only [Prod.fst_add, Prod.snd_add, map_add (f := _), Complex.ofReal_add, Pi.add_apply]
        ring
      map_smul' := by
        intro s p
        funext y
        simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply,
          Pi.smul_apply, Complex.real_smul]
        ring }
  have hΦ : ∀ p y, Φ p y = fderiv ℝ f₀ y p.1 + (-(2 * Real.pi * Complex.I)) * ((T y p.2 : ℝ) : ℂ) * f₀ y :=
    fun p y => rfl
  have hEΦ : ∀ p y, Φ (Jm p) y = Complex.I * Φ p y := fun p y => by rw [hΦ, hΦ]; exact hE p y
  have hΦ0 : ∀ w y, Φ (0, w) y = (-(2 * Real.pi * Complex.I)) * ((T y w : ℝ) : ℂ) * f₀ y := by
    intro w y
    rw [hΦ]
    simp only [map_zero, zero_add]
  let Q : V × V →ₗ[ℝ] V × V :=
    (LinearMap.inr ℝ V V) ∘ₗ (LinearMap.fst ℝ V V) + Jm ∘ₗ (LinearMap.inr ℝ V V) ∘ₗ (LinearMap.snd ℝ V V)
  let Θ : V × V →ₗ[ℝ] (V → ℂ) := Φ ∘ₗ Q
  have hΘ : ∀ w₁ w₂ y, Θ (w₁, w₂) y = (-(2 * Real.pi * Complex.I)) * ((T y w₁ : ℝ) : ℂ) * f₀ y +
      Complex.I * ((-(2 * Real.pi * Complex.I)) * ((T y w₂ : ℝ) : ℂ) * f₀ y) := by
    intro w₁ w₂ y
    have e : Θ (w₁, w₂) = Φ (0, w₁) + Φ (Jm (0, w₂)) := map_add Φ _ _
    rw [e, Pi.add_apply, hEΦ, hΦ0, hΦ0]
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, f₀ y₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (SchwartzMap.ext fun y => by simp [h y])
  have hU : {y | f₀ y ≠ 0} ∈ 𝓝 y₀ := (isOpen_compl_singleton.preimage f₀.continuous).mem_nhds hy₀
  have hc : (-(2 * Real.pi * Complex.I) : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hinj : Function.Injective Θ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨w₁, w₂⟩ h
    have hsplit : ∀ y ∈ {y | f₀ y ≠ 0}, T y w₁ = 0 ∧ T y w₂ = 0 := by
      intro y hy
      have h0 : Θ (w₁, w₂) y = 0 := by rw [h]; rfl
      rw [hΘ] at h0
      have h3 : ((T y w₁ : ℝ) : ℂ) + Complex.I * ((T y w₂ : ℝ) : ℂ) = 0 := by
        have h4 : (-(2 * Real.pi * Complex.I)) * f₀ y *
            (((T y w₁ : ℝ) : ℂ) + Complex.I * ((T y w₂ : ℝ) : ℂ)) = 0 := by
          rw [← h0]; ring
        rcases mul_eq_zero.mp h4 with h5 | h5
        · rcases mul_eq_zero.mp h5 with h6 | h6
          · exact absurd h6 hc
          · exact absurd h6 hy
        · exact h5
      have hre := congrArg Complex.re h3
      have him := congrArg Complex.im h3
      simp at hre him
      exact ⟨hre, him⟩
    have e1 := eq_zero_of_forall_nhds T hT y₀ _ hU w₁ fun y hy => (hsplit y hy).1
    have e2 := eq_zero_of_forall_nhds T hT y₀ _ hU w₂ fun y hy => (hsplit y hy).2
    rw [e1, e2]; rfl
  have hle : LinearMap.range Θ ≤ LinearMap.range Φ := LinearMap.range_comp_le_range Q Φ
  have hrange : LinearMap.range Θ = LinearMap.range Φ := by
    apply Submodule.eq_of_le_of_finrank_le hle
    rw [LinearMap.finrank_range_of_inj hinj]
    exact LinearMap.finrank_range_le Φ
  have hmem : ∀ a, (Φ ∘ₗ LinearMap.inl ℝ V V) a ∈ LinearMap.range Θ := fun a => by
    rw [hrange]; exact LinearMap.mem_range_self Φ _
  let e := LinearEquiv.ofInjective Θ hinj
  let W : V →ₗ[ℝ] V × V :=
    e.symm.toLinearMap ∘ₗ LinearMap.codRestrict (LinearMap.range Θ) (Φ ∘ₗ LinearMap.inl ℝ V V) hmem
  have hW : ∀ a, Θ (W a) = Φ (a, 0) := by
    intro a
    have h := congrArg Subtype.val (e.apply_symm_apply ⟨Φ (a, 0), hmem a⟩)
    exact h
  let m : V →ₗ[ℝ] V →ₗ[ℝ] ℂ := LinearMap.mk₂ ℝ
    (fun a y => (-(2 * Real.pi * Complex.I)) * ((T y (W a).1 : ℝ) : ℂ) +
      Complex.I * ((-(2 * Real.pi * Complex.I)) * ((T y (W a).2 : ℝ) : ℂ)))
    (by intro a₁ a₂ y; simp only [map_add (f := _), Prod.fst_add, Prod.snd_add, Complex.ofReal_add]; ring)
    (by intro s a y; simp only [map_smul, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Complex.ofReal_mul,
      Complex.real_smul]; ring)
    (by intro a y₁ y₂; simp only [map_add (f := _), LinearMap.add_apply, Complex.ofReal_add]; ring)
    (by intro s a y; simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Complex.ofReal_mul,
      Complex.real_smul]; ring)
  refine ⟨m, fun a y => ?_⟩
  have h1 : Φ (a, 0) y = fderiv ℝ f₀ y a := by
    rw [hΦ]; simp only [map_zero, Complex.ofReal_zero, mul_zero, zero_mul, add_zero]
  have h2 := hΘ (W a).1 (W a).2 y
  rw [Prod.mk.eta, hW, h1] at h2
  rw [h2]
  show _ = ((-(2 * Real.pi * Complex.I)) * ((T y (W a).1 : ℝ) : ℂ) +
      Complex.I * ((-(2 * Real.pi * Complex.I)) * ((T y (W a).2 : ℝ) : ℂ))) * f₀ y
  ring

end GlobalTheory.CompanionTheory.Twist.FockLogDeriv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.TwistedProofs.SchwartzLogDerivLinearGaussian
namespace GlobalTheory.CompanionTheory.Twist

theorem schwartz_logDeriv_linear_formula {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f₀ : SchwartzMap V ℂ) (m : V →ₗ[ℝ] V →ₗ[ℝ] ℂ)
    (hm : ∀ a y, fderiv ℝ f₀ y a = m a y * f₀ y) (y : V) :
    f₀ y = f₀ 0 * Complex.exp (m y y / 2) := by
  have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f₀ (s • y)) ((t : ℂ) * m y y * f₀ (t • y)) t := by
    intro t
    have h1 : HasFDerivAt f₀ (fderiv ℝ f₀ (t • y)) (t • y) := f₀.differentiableAt.hasFDerivAt
    have h2 : HasDerivAt (fun s : ℝ => s • y) y t := by
      simpa using (hasDerivAt_id t).smul_const y
    have h3 : HasDerivAt (fun s : ℝ => f₀ (s • y)) (fderiv ℝ f₀ (t • y) y) t :=
      h1.comp_hasDerivAt t h2
    rw [hm, map_smul, Complex.real_smul] at h3
    exact h3
  have hE : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-((s : ℂ) ^ 2 * m y y / 2)))
      (Complex.exp (-((t : ℂ) ^ 2 * m y y / 2)) * (-((t : ℂ) * m y y))) t := by
    intro t
    have h5 : HasDerivAt (fun z : ℂ => -(z ^ 2 * m y y / 2)) (-((t : ℂ) * m y y)) (t : ℂ) := by
      have h6 := (((hasDerivAt_pow 2 (t : ℂ)).mul_const (m y y)).div_const 2).neg
      refine h6.congr_deriv ?_
      rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
      push_cast
      ring
    exact h5.cexp.comp_ofReal
  have hH : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => f₀ (s • y) * Complex.exp (-((s : ℂ) ^ 2 * m y y / 2))) 0 t := by
    intro t
    refine ((hg t).mul (hE t)).congr_deriv ?_
    ring
  have h10 := is_const_of_deriv_eq_zero (fun t => (hH t).differentiableAt) (fun t => (hH t).deriv) 1 0
  simp only [one_smul, zero_smul, Complex.ofReal_one, Complex.ofReal_zero, one_pow, one_mul,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, zero_div, neg_zero,
    Complex.exp_zero, mul_one] at h10
  calc f₀ y = f₀ y * Complex.exp (-(m y y / 2)) * Complex.exp (m y y / 2) := by
        rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = f₀ 0 * Complex.exp (m y y / 2) := by rw [h10]

theorem schwartz_logDeriv_linear_gaussian {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (f₀ : SchwartzMap V ℂ) (hf : f₀ ≠ 0)
    (m : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (hm : ∀ a y, fderiv ℝ f₀ y a = m a y * f₀ y) :
    ∃ (c₀ : ℂ) (Q Q' : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), c₀ ≠ 0 ∧ (∀ x, x ≠ 0 → 0 < Q x x) ∧
      ∀ x, f₀ x = c₀ * Complex.exp (-(Q x x : ℂ) - Complex.I * (Q' x x : ℂ)) := by
  have hform := fun y => schwartz_logDeriv_linear_formula f₀ m hm y
  have hc0 : f₀ 0 ≠ 0 := by
    intro h0
    apply hf
    ext x
    simp [hform x, h0]
  refine ⟨f₀ 0, (-(1 / 2 : ℝ)) • m.compr₂ Complex.reLm, (-(1 / 2 : ℝ)) • m.compr₂ Complex.imLm,
    hc0, ?_, ?_⟩
  · intro x hx
    simp only [LinearMap.smul_apply, LinearMap.compr₂_apply, Complex.reLm_coe, smul_eq_mul]
    by_contra hle
    push Not at hle
    have hre : 0 ≤ (m x x).re := by linarith
    obtain ⟨C, hCpos, hC⟩ := f₀.decay 1 0
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hcpos : 0 < ‖f₀ 0‖ := norm_pos_iff.mpr hc0
    set t : ℝ := C / (‖f₀ 0‖ * ‖x‖) + 1 with ht
    have htpos : 0 < t := by positivity
    have hlow : ‖f₀ 0‖ ≤ ‖f₀ (t • x)‖ := by
      rw [hform (t • x), norm_mul, Complex.norm_exp]
      apply le_mul_of_one_le_right (norm_nonneg _)
      apply Real.one_le_exp
      simp only [map_smul, LinearMap.smul_apply, smul_smul, Complex.div_ofNat_re, Complex.smul_re,
        smul_eq_mul]
      have h6 := mul_nonneg (mul_self_nonneg t) hre
      linarith
    have hdec := hC (t • x)
    rw [pow_one, norm_iteratedFDeriv_zero, norm_smul, Real.norm_eq_abs, abs_of_pos htpos] at hdec
    have hbig : C < t * ‖x‖ * ‖f₀ 0‖ := by
      have hne : ‖f₀ 0‖ * ‖x‖ ≠ 0 := by positivity
      have heq : t * ‖x‖ * ‖f₀ 0‖ = C + ‖x‖ * ‖f₀ 0‖ := by
        rw [ht]
        field_simp
      rw [heq]
      linarith [mul_pos hxpos hcpos]
    have h7 : t * ‖x‖ * ‖f₀ 0‖ ≤ t * ‖x‖ * ‖f₀ (t • x)‖ :=
      mul_le_mul_of_nonneg_left hlow (by positivity)
    linarith
  · intro x
    rw [hform x]
    congr 1
    congr 1
    simp only [LinearMap.smul_apply, LinearMap.compr₂_apply, Complex.reLm_coe, Complex.imLm_coe,
      smul_eq_mul]
    apply Complex.ext <;> simp <;> ring

end GlobalTheory.CompanionTheory.Twist
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.RealInvL
noncomputable section

namespace GlobalTheory.ThK.Dbl.Dense

open scoped TensorProduct NNReal ENNReal Matrix SchwartzMap LineDeriv
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

section Line
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def hl (a : V) (L : V →L[ℝ] ℝ) (t : ℝ) (f : V → ℂ) (x : V) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * (L a / 2) : ℝ) : ℂ)) * f (x + t • a)

def dop (a : V) (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  ∂_{a} f + (-(2 * Real.pi * Complex.I)) • SchwartzMap.smulLeftCLM ℂ L f

theorem dop_apply (a : V) (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    dop a L f x = fderiv ℝ f x a + (-(2 * Real.pi * Complex.I) * (L x : ℂ)) * f x := by
  have hT := L.hasTemperateGrowth
  simp only [dop, SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hT,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  simp only [Complex.real_smul, smul_eq_mul]
  ring

theorem dop_add (a b : V) (L M : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) :
    dop (a + b) (L + M) f = dop a L f + dop b M f := by
  ext x
  simp only [SchwartzMap.add_apply, dop_apply, map_add (f := _), ContinuousLinearMap.add_apply]
  push_cast
  ring

theorem dop_subsingleton [Subsingleton V] (a : V) (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) : dop a L f = 0 := by
  ext x
  have ha : a = 0 := Subsingleton.elim _ _
  have hx : x = 0 := Subsingleton.elim _ _
  simp [dop_apply, ha, hx]

theorem hasDerivAt_hl (a : V) (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    HasDerivAt (fun t : ℝ => hl a L t f x) (dop a L f x) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => t * L x + t ^ 2 * (L a / 2)) (L x) 0 := by
    have a1 : HasDerivAt (fun t : ℝ => t * L x) (L x) 0 := by simpa using (hasDerivAt_id (0 : ℝ)).mul_const (L x)
    have a2 : HasDerivAt (fun t : ℝ => t ^ 2 * (L a / 2)) 0 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (L a / 2)
    simpa using a1.fun_add a2
  have h2 : HasDerivAt (fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * (L a / 2) : ℝ) : ℂ)))
      (-(2 * Real.pi * Complex.I) * (L x : ℂ)) 0 := by
    have := ((h1.ofReal_comp).const_mul (-(2 * Real.pi * Complex.I))).cexp
    simpa using this
  have h3 : HasDerivAt (fun t : ℝ => x + t • a) a 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add x
  have h4 : HasDerivAt (fun t : ℝ => f (x + t • a)) (fderiv ℝ f x a) 0 := by
    have hf : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • a) := by
      simpa using f.hasFDerivAt x
    exact hf.comp_hasDerivAt (0 : ℝ) h3
  refine (h2.fun_mul h4).congr_deriv ?_
  rw [dop_apply]
  simp
  ring
end Line


open Complex in
theorem temperate_exp : Function.HasTemperateGrowth (fun t : ℝ => cexp (I * t)) := by
  have hd : ∀ n : ℕ, iteratedDeriv n (fun t : ℝ => cexp (I * t)) = fun t : ℝ => I ^ n * cexp (I * t) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      funext t
      rw [iteratedDeriv_succ, ih]
      have : HasDerivAt (fun t : ℝ => I ^ n * cexp (I * t)) (I ^ n * (cexp (I * t) * (I * 1))) t :=
        (((hasDerivAt_id (t : ℂ)).const_mul I).cexp.const_mul _).comp_ofReal
      rw [this.deriv]; ring
  refine ⟨Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff),
    fun n => ⟨0, 1, fun t => ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hd, norm_mul, norm_pow,
    Complex.norm_I, one_pow, one_mul, Complex.norm_exp_I_mul_ofReal]
  simp

variable {κ : Type} [Fintype κ]

section LineProof
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def chirp (c : ℝ) (q : V → ℝ) (x : V) : ℂ := Complex.exp (Complex.I * ((-(2 * Real.pi) * c * q x : ℝ) : ℂ))

theorem chirp_tg (c : ℝ) {q : V → ℝ} (hq : q.HasTemperateGrowth) : (chirp c q).HasTemperateGrowth := by
  have h1 : (fun x => -(2 * Real.pi) * c * q x).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const _).mul hq
  exact temperate_exp.comp h1

theorem chirp_mul (q : V → ℝ) (x y : V) :
    chirp 1 q y * chirp (-1) q x =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((q y - q x : ℝ) : ℂ)) := by
  rw [chirp, chirp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem chirp_one (q : V → ℝ) (x : V) : chirp (-1) q x * chirp 1 q x = 1 := by
  rw [mul_comm, chirp_mul]
  simp

theorem hl_schwartz (a : V) (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) (t : ℝ) : ∃ G : 𝓢(V, ℂ), ∀ x, G x = hl a L t f x := by
  have hq : (fun x => t * L x + t ^ 2 * (L a / 2)).HasTemperateGrowth :=
    ((Function.HasTemperateGrowth.const t).mul L.hasTemperateGrowth).add (Function.HasTemperateGrowth.const _)
  refine ⟨SchwartzMap.smulLeftCLM ℂ (chirp 1 fun x => t * L x + t ^ 2 * (L a / 2))
    (SchwartzMap.compSubConstCLM ℂ (-(t • a)) f), fun x => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply (chirp_tg 1 hq), SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, hl, chirp]
  simp only [smul_eq_mul]
  congr 2
  push_cast
  ring

theorem hl_line_deriv (a : V) (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) :
    ∃ G : ℝ → 𝓢(V, ℂ), (∀ t x, G t x = hl a L t f x) ∧
      (a ≠ 0 → ∀ T : 𝓢(V, ℂ) →L[ℂ] ℂ, HasDerivAt (fun t => T (G t)) (T (dop a L f)) 0) := by
  choose G hG using hl_schwartz a L f
  refine ⟨G, hG, fun ha T => ?_⟩
  have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.2 ha
  obtain ⟨g₀, -, hg₀⟩ := exists_dual_vector ℝ a hna
  set lam : V →L[ℝ] ℝ := ‖a‖⁻¹ • g₀ with hlam
  have hla : lam a = 1 := by
    simp only [hlam, ContinuousLinearMap.smul_apply, hg₀, smul_eq_mul]
    simpa using inv_mul_cancel₀ hna
  set q : V → ℝ := fun x => lam x * L x + (-(L a / 2)) * (lam x * lam x) with hq
  have hqt : q.HasTemperateGrowth :=
    (lam.hasTemperateGrowth.mul L.hasTemperateGrowth).add
      ((Function.HasTemperateGrowth.const _).mul (lam.hasTemperateGrowth.mul lam.hasTemperateGrowth))
  have hdiff : ∀ (x : V) (t : ℝ), q (x + t • a) - q x = t * L x + t ^ 2 * (L a / 2) := fun x t => by
    simp only [hq, map_add (f := _), map_smul, hla, smul_eq_mul]
    ring
  have t1 := chirp_tg 1 hqt
  have t2 := chirp_tg (-1) hqt
  set P := SchwartzMap.smulLeftCLM ℂ (chirp 1 q) with hP
  set Pi := SchwartzMap.smulLeftCLM ℂ (chirp (-1) q) with hPi
  set g : 𝓢(V, ℂ) := P f with hg
  have hGe : ∀ t, G t = Pi (SchwartzMap.compSubConstCLM ℂ (-(t • a)) g) := fun t => by
    ext x
    rw [hG, hPi, SchwartzMap.smulLeftCLM_apply_apply t2, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, hg, hP,
      SchwartzMap.smulLeftCLM_apply_apply t1, hl, ← hdiff]
    simp only [smul_eq_mul]
    rw [← mul_assoc, mul_comm (chirp (-1) q x), chirp_mul]
  have hf : Pi g = f := by
    ext x
    rw [hPi, SchwartzMap.smulLeftCLM_apply_apply t2, hg, hP, SchwartzMap.smulLeftCLM_apply_apply t1]
    simp only [smul_eq_mul]
    rw [← mul_assoc, chirp_one, one_mul]
  have hG0 : G 0 = f := by
    ext x
    rw [hG]
    simp [hl]
  have hder : ∀ T₁ : 𝓢(V, ℂ) →L[ℂ] ℂ, HasDerivAt (fun t => T₁ (G t)) (T₁ (Pi (∂_{a} g))) 0 := fun T₁ => by
    rw [hasDerivAt_iff_tendsto_slope_zero]
    have h := PositivityTheory.ThKOwn.schwartz_dq_tendsto g a
    have h2 := (((T₁.comp Pi).restrictScalars ℝ).continuous.tendsto _).comp h
    refine h2.congr fun t => ?_
    simp only [Function.comp, map_smul, map_sub, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.comp_apply,
      zero_add, hG0, hGe, hf]
  have hid : Pi (∂_{a} g) = dop a L f := by
    ext x
    have h1 := hder (BoundedContinuousFunction.evalCLM ℂ x ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ V ℂ)
    have e : (fun t => (BoundedContinuousFunction.evalCLM ℂ x ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ V ℂ) (G t)) =
        fun t => hl a L t f x := by
      funext t
      exact hG t x
    rw [e] at h1
    exact h1.unique (hasDerivAt_hl a L f x)
  rw [← hid]
  exact hder T
end LineProof

variable {F : Type} [Field F] [NumberField F]

theorem exists_sb_one {κ : Type} [Fintype κ] : ∃ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), g 0 = 1 :=
  ⟨_, pf_mem good_std, by rw [pf_eq_prod ∅ 0 fun u _ => ⟨rfl, fun i => by simp⟩, Finset.prod_empty]⟩

section Coord
variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def aOf (M : Model σ X W) (u : Matrix (Fin n) (Fin d) (AE F E)) : Fin n × Fin d → mixedEmbedding.mixedSpace F :=
  fun i => evI F ((M.co.e u).1 i)

def lOf (M : Model σ X W) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  linForm fun i => evI F ((M.co.e u).2 i)

end Coord

section Coord2
variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem aOf_add (M : Model σ X W) (u v : Matrix (Fin n) (Fin d) (AE F E)) :
    aOf M (u + v) = aOf M u + aOf M v := by
  funext i
  simp [aOf, map_add (f := _), evI_add]

theorem lOf_add (M : Model σ X W) (u v : Matrix (Fin n) (Fin d) (AE F E)) :
    lOf M (u + v) = lOf M u + lOf M v := by
  ext y
  simp only [lOf, ContinuousLinearMap.add_apply, linForm_apply, ← map_add (f := _), ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [map_add (f := _), evI_add, mul_add]

theorem evI_half_trace (S : mixedEmbedding.mixedSpace F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F ⅟(2 : AF F) * S) =
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) S / 2 := by
  have h1 : evI F ⅟(2 : AF F) + evI F ⅟(2 : AF F) = 1 := by
    rw [← evI_add, invOf_two_add_invOf_two]
    exact map_one (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have h2 : S = evI F ⅟(2 : AF F) * S + evI F ⅟(2 : AF F) * S := by
    rw [← add_mul, h1, one_mul]
  have h3 := congrArg (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)) h2
  rw [map_add (f := _)] at h3
  linarith

open scoped Classical in
theorem heisLine_tens (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) (f : SInf F (Fin n × Fin d))
    {r : (Fin n × Fin d → AF F) → ℂ} (hr : ∀ x z, At (evI F) z → r (x + z) = r x) (t : ℝ) :
    M.heisLine ψ u t (tens (evI F) f r) = tens (evI F) (hl (aOf M u) (lOf M u) t f) r := by
  have hab : ∀ s, evI F s = 0 → s • M.co.e u = 0 := fun s hs => by
    rw [← map_smul, hu s hs, map_zero]
  have ha : At (evI F) (M.co.e u).1 := fun s hs => congrArg Prod.fst (hab s hs)
  have hb : At (evI F) (M.co.e u).2 := fun s hs => congrArg Prod.snd (hab s hs)
  have hat : At (evI F) (realAd F t • (M.co.e u).1) := fun s hs => by
    rw [smul_comm, ha s hs, smul_zero]
  funext x
  show schr ψ (M.co.e (realAd F t • u)) _ x = _
  rw [map_smul]
  show schr ψ (realAd F t • (M.co.e u).1, realAd F t • (M.co.e u).2) _ x = _
  have e : (fun i => evI F ((x + realAd F t • (M.co.e u).1) i)) =
      (fun i => evI F (x i)) + t • fun i => evI F ((M.co.e u).1 i) := by
    funext i
    simp [evI_add, evI_mul, evI_realAd, Algebra.smul_def]
  simp only [schr, tens]
  rw [phase_line ψ hψ _ _ x hb t, e, hr x _ hat, evI_half_trace]
  simp only [hl, aOf, lOf, linForm_apply, mul_assoc]
  rfl

open scoped Classical in
theorem actsD_dop (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) (f : SInf F (Fin n × Fin d)) :
    ActsD (evI F) (M.heisLine ψ u) f (dop (aOf M u) (lOf M u) f) := by
  intro r hr x
  have e : (fun t => M.heisLine ψ u t (tens (evI F) f r) x) =
      fun t => hl (aOf M u) (lOf M u) t f (fun i => evI F (x i)) * r x := by
    funext t
    rw [heisLine_tens M hψ hu f hr.1 t]
    rfl
  rw [e]
  exact (hasDerivAt_hl _ _ f _).mul_const (r x)

open scoped Classical in
theorem actsD_unique' (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) {f f₁ : SInf F (Fin n × Fin d)}
    (h : ActsD (evI F) (M.heisLine ψ u) f f₁) : f₁ = dop (aOf M u) (lOf M u) f := by
  obtain ⟨g, hg, h0⟩ := exists_sb_one (F := F) (κ := Fin n × Fin d)
  ext x
  have hr : Rest (evI F) f (rOf g) := ⟨fun x z hz => rOf_add g x z hz, Submodule.subset_span ⟨f, g, hg, rfl⟩⟩
  have h1 := h _ hr (pt x 0)
  have h2 := actsD_dop M hψ hu f _ hr (pt x 0)
  have := h1.unique h2
  simpa [tens_rOf, pureA_pt, h0] using this

end Coord2

section Inter
variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}
variable {M : Model σ Y W} {ψ : AddChar (AF F) ℂ} {om : Rep σ Y W} {k : UA σ Y.J × UA σ W.J}

theorem at_act (k : UA σ Y.J × UA σ W.J) {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) :
    At (evI F) (actAB (cA σ) k u) := fun s hs => by
  rw [actAB, ← Matrix.smul_mul, ← Matrix.mul_smul, hu s hs, Matrix.mul_zero, Matrix.zero_mul]

theorem act_add (k : UA σ Y.J × UA σ W.J) (u v : Matrix (Fin n) (Fin d) (AE F E)) :
    actAB (cA σ) k (u + v) = actAB (cA σ) k u + actAB (cA σ) k v := by
  rw [actAB, Matrix.mul_add, Matrix.add_mul]; rfl


open scoped Classical in
def Impl (om : Rep σ Y W) (k : UA σ Y.J × UA σ W.J) (A : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d)) : Prop :=
  ∀ f : SInf F (Fin n × Fin d), ∀ g ∈ SB (Fin n × Fin d → Af F), om k (pureA F f g) = pureA F (A f) g

open scoped Classical in
theorem line_hl (hψ : IsStd ψ) (hs : IsSplitting (adeleClass F) ψ M.co (actAB (cA σ)) om)
    {A : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d)} (hA : Impl om k A)
    {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) (f G : SInf F (Fin n × Fin d)) (t : ℝ)
    (hG : ∀ x, G x = hl (aOf M u) (lOf M u) t f x) (x : Fin n × Fin d → mixedEmbedding.mixedSpace F) :
    A G x = hl (aOf M (actAB (cA σ) k u)) (lOf M (actAB (cA σ) k u)) t (A f) x := by
  obtain ⟨g, hg, h0⟩ := exists_sb_one (F := F) (κ := Fin n × Fin d)
  have hr : ∀ x z, At (evI F) z → rOf g (x + z) = rOf g x := fun x z hz => rOf_add g x z hz
  have hΦ : pureA F f g ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, g, hg, rfl⟩
  have e1 : M.heisLine ψ u t (pureA F f g) = pureA F G g := by
    rw [← tens_rOf, heisLine_tens M hψ hu f hr t, tens_rOf]
    congr 1
    funext x
    exact (hG x).symm
  have e2 : om k (M.heisLine ψ u t (pureA F f g)) =
      M.heisLine ψ (actAB (cA σ) k u) t (om k (pureA F f g)) := by
    have := hs.impl k (realAd F t • u) _ hΦ
    rw [actAB, Matrix.mul_smul, Matrix.smul_mul] at this
    exact this
  rw [e1, hA G g hg, hA f g hg, ← tens_rOf, ← tens_rOf, heisLine_tens M hψ (at_act k hu) (A f) hr t] at e2
  have := congrFun e2 (pt x 0)
  simpa [tens_rOf, pureA_pt, h0] using this

open scoped Classical in
theorem inter_of_ne (hψ : IsStd ψ) (hs : IsSplitting (adeleClass F) ψ M.co (actAB (cA σ)) om)
    {A : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d)} (hA : Impl om k A)
    {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) (ha : aOf M u ≠ 0) (f : SInf F (Fin n × Fin d)) :
    A (dop (aOf M u) (lOf M u) f) = dop (aOf M (actAB (cA σ) k u)) (lOf M (actAB (cA σ) k u)) (A f) := by
  obtain ⟨G, hG, hD⟩ := hl_line_deriv (aOf M u) (lOf M u) f
  ext x
  let T := (BoundedContinuousFunction.evalCLM ℂ x ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ) ∘L A
  have hT : ∀ f, A f x = T f := fun _ => rfl
  have h1 := hD ha T
  have e : (fun t => T (G t)) = fun t => hl (aOf M (actAB (cA σ) k u)) (lOf M (actAB (cA σ) k u)) t (A f) x := by
    funext t
    rw [← hT]
    exact line_hl hψ hs hA hu f (G t) t (hG t) x
  rw [e] at h1
  rw [hT]
  exact h1.unique (hasDerivAt_hl _ _ (A f) x)

open scoped Classical in
theorem exists_at (M : Model σ Y W) (ξ : Fin n × Fin d → mixedEmbedding.mixedSpace F) :
    ∃ v : Matrix (Fin n) (Fin d) (AE F E), At (evI F) v ∧ aOf M v = ξ := by
  refine ⟨M.co.e.symm (pt ξ 0, 0), fun s hs => ?_, ?_⟩
  · have h1 : s.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hs
    rw [← map_smul, LinearEquiv.map_eq_zero_iff]
    refine Prod.ext ?_ (by simp)
    funext i
    refine Prod.ext ?_ ?_
    · show s.1 * _ = 0
      rw [h1, zero_mul]
    · show s.2 * 0 = 0
      rw [mul_zero]
  · have : M.co.e (M.co.e.symm (pt ξ 0, 0)) = (pt ξ 0, 0) := LinearEquiv.apply_symm_apply _ _
    show (fun i => evI F ((M.co.e (M.co.e.symm (pt ξ 0, 0))).1 i)) = ξ
    rw [this]
    exact evI_pt ξ 0

open scoped Classical in
theorem inter (hψ : IsStd ψ) (hs : IsSplitting (adeleClass F) ψ M.co (actAB (cA σ)) om)
    {A : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d)} (hA : Impl om k A)
    {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) (f : SInf F (Fin n × Fin d)) :
    A (dop (aOf M u) (lOf M u) f) = dop (aOf M (actAB (cA σ) k u)) (lOf M (actAB (cA σ) k u)) (A f) := by
  by_cases ha : aOf M u = 0
  · rcases subsingleton_or_nontrivial (Fin n × Fin d → mixedEmbedding.mixedSpace F) with hV | hV
    · rw [dop_subsingleton, dop_subsingleton, map_zero]
    · obtain ⟨ξ, hξ⟩ := exists_ne (0 : Fin n × Fin d → mixedEmbedding.mixedSpace F)
      obtain ⟨v, hv, rfl⟩ := exists_at M ξ
      have huv : At (evI F) (u + v) := fun s hs => by rw [smul_add, hu s hs, hv s hs, add_zero]
      have h1 := inter_of_ne hψ hs hA huv (by rw [aOf_add, ha, zero_add]; exact hξ) f
      have h2 := inter_of_ne hψ hs hA hv hξ f
      rw [aOf_add, lOf_add, dop_add, map_add (f := _), act_add, aOf_add, lOf_add, dop_add, h2] at h1
      exact add_right_cancel h1
  · exact inter_of_ne hψ hs hA hu ha f

end Inter

section Unit

theorem cont_mixS : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

variable (F) (κ : Type)

def splitE : ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃+ (κ → AdeleRing (𝓞 F) F) where
  toFun p := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)
  invFun x := (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2)
  left_inv p := Prod.ext (funext fun i => RingEquiv.apply_symm_apply _ _) (funext fun i => rfl)
  right_inv x := funext fun i => Prod.ext (RingEquiv.symm_apply_apply _ _) rfl
  map_add' p q := funext fun i => Prod.ext (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i) (q.1 i)) rfl

theorem splitE_apply (p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) :
    splitE F κ p = fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i) := rfl

theorem continuous_splitE : Continuous (splitE F κ) := by
  rw [show ⇑(splitE F κ) = fun p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) =>
    fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i) from rfl]
  exact continuous_pi fun i => (cont_mixS.comp
    ((continuous_apply i).comp continuous_fst)).prodMk ((continuous_apply i).comp continuous_snd)

variable {F} in
theorem cont_evI : Continuous (evI F) :=
  (continuous_pi fun w => (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).continuous.comp
    ((continuous_apply w.1).comp continuous_fst)).prodMk
  (continuous_pi fun w => (InfinitePlace.Completion.isometry_extensionEmbedding w.1).continuous.comp
    ((continuous_apply w.1).comp continuous_fst))

theorem continuous_splitE_symm : Continuous (splitE F κ).symm := by
  rw [show ⇑(splitE F κ).symm = fun x : κ → AdeleRing (𝓞 F) F =>
    ((fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2) :
      (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) from rfl]
  exact (continuous_pi fun i => cont_evI.comp (continuous_apply i)).prodMk (continuous_pi fun i => continuous_snd.comp (continuous_apply i))

theorem pureA_splitE (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) :
    GlobalTheory.WeilM.pureA F f g (splitE F κ p) = f p.1 * g p.2 := by
  simp only [GlobalTheory.WeilM.pureA, splitE_apply, RingEquiv.apply_symm_apply]

open scoped Classical in
theorem volume_isAddHaar [Fintype κ] : (volume : Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure := by
  haveI : MeasurableAdd (mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  exact Measure.pi.isAddHaarMeasure _

variable {F κ} [Fintype κ]

open scoped Classical in
theorem lintegral_eq {S : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ}
    (hU : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ φ ∈ schA F κ, ∫⁻ x, ‖S φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) {f f' : SInf F κ}
    (h : ∀ g ∈ SB (κ → Af F), S (pureA F f g) = pureA F f' g) : ∫⁻ x, ‖f' x‖ₑ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  obtain ⟨g, hg, h₁⟩ := exists_sb_one (F := F) (κ := κ)
  haveI := volume_isAddHaar F κ
  haveI : OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  haveI : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  letI mY : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  letI mA : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI : SigmaCompactSpace (κ → FiniteAdeleRing (𝓞 F) F) := sigmaCompactSpace_of_locallyCompact_secondCountable
  set ν : Measure (κ → FiniteAdeleRing (𝓞 F) F) := Measure.addHaar with hν
  haveI : SFinite ν := inferInstance
  haveI : MeasurableAdd (κ → mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  haveI : MeasurableAdd (κ → FiniteAdeleRing (𝓞 F) F) := ContinuousAdd.measurableAdd
  haveI : ν.IsAddHaarMeasure := by rw [hν]; infer_instance
  haveI : ((volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (κ → mixedEmbedding.mixedSpace F)) ν
  have hμH : Measure.IsAddHaarMeasure ((volume.prod ν).map (splitE F κ)) :=
    (splitE F κ).isAddHaarMeasure_map _ (continuous_splitE F κ) (continuous_splitE_symm F κ)
  let em : ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃ᵐ (κ → AdeleRing (𝓞 F) F) :=
    (Homeomorph.mk (splitE F κ).toEquiv (continuous_splitE F κ)
      (continuous_splitE_symm F κ)).toMeasurableEquiv
  have hint : ∀ h : (κ → AdeleRing (𝓞 F) F) → ℝ≥0∞,
      ∫⁻ x, h x ∂((volume.prod ν).map (splitE F κ)) = ∫⁻ p, h (splitE F κ p) ∂(volume.prod ν) :=
    fun h => lintegral_map_equiv h em
  have hgc : Continuous g := hg.1.continuous
  have hC : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν ≠ ⊤ := by
    have h1 : ∫⁻ y, ‖g y * g y‖ₑ ∂ν < ⊤ :=
      ((hgc.mul hgc).integrable_of_hasCompactSupport (hg.2.mul_left (f := g))).2
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq (lintegral_congr fun y => ?_)) h1)
    rw [enorm_mul, sq]
  have hC0 : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν ≠ 0 := fun h0 => by
    rw [lintegral_eq_zero_iff (hgc.measurable.enorm.pow_const 2)] at h0
    have h2 : g =ᵐ[ν] 0 := h0.mono fun y hy => by simpa using hy
    have := congrFun ((hgc.ae_eq_iff_eq ν continuous_zero).1 h2) 0
    simp [h₁] at this
  have hp : ∀ a : SInf F κ, ∫⁻ x, ‖pureA F a g x‖ₑ ^ 2 ∂((volume.prod ν).map (splitE F κ)) =
      (∫⁻ x, ‖a x‖ₑ ^ 2) * ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν := fun a => by
    rw [hint]
    have e1 : ∀ p, ‖pureA F a g (splitE F κ p)‖ₑ ^ 2 = ‖a p.1‖ₑ ^ 2 * ‖g p.2‖ₑ ^ 2 := by
      intro p
      rw [pureA_splitE, enorm_mul, mul_pow]
    simp_rw [e1]
    rw [lintegral_prod_mul (a.continuous.measurable.enorm.pow_const 2).aemeasurable
      (hgc.measurable.enorm.pow_const 2).aemeasurable]
  have := hU _ hμH _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)
  rw [h g hg, hp, hp] at this
  exact (ENNReal.mul_left_inj hC0 hC).1 this

end Unit

end GlobalTheory.ThK.Dbl.Dense

end
end

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal ENNReal Matrix Classical SchwartzMap
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace Dense

theorem exists_fixed {S H P : Type} [AddCommGroup S] [Module ℂ S] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [AddCommGroup P] [Module ℂ P] (ι : S →ₗ[ℂ] H) (hι : Function.Injective ι) (p : S →ₗ[ℂ] P) (N : Submodule ℂ S)
    [FiniteDimensional ℂ N] {f : S} (hf : f ∈ N) (hp : p f ≠ 0) :
    ∃ f₀ ∈ N, f₀ ≠ 0 ∧ ∀ g ∈ N, p g = p f₀ → ‖ι g‖ = ‖ι f₀‖ → g = f₀ := by
  let Z := (N ⊓ LinearMap.ker p).map ι
  haveI : FiniteDimensional ℂ (N ⊓ LinearMap.ker p : Submodule ℂ S) := Submodule.finiteDimensional_of_le inf_le_left
  haveI : CompleteSpace Z := FiniteDimensional.complete ℂ Z
  obtain ⟨_, ⟨z, hz, rfl⟩, y, hy, e⟩ := Z.exists_add_mem_mem_orthogonal (ι f)
  have e' : ι (f - z) = y := by rw [map_sub, e, add_sub_cancel_left]
  refine ⟨f - z, sub_mem hf hz.1, fun h => hp ?_, fun g hg h1 h2 => ?_⟩
  · rw [sub_eq_zero.1 h]
    exact hz.2
  · have hm : ι (g - (f - z)) ∈ Z := ⟨_, ⟨sub_mem hg (sub_mem hf hz.1), by simp [h1]⟩, rfl⟩
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ (hy _ hm)
    rw [← e', ← map_add (f := _), sub_add_cancel, h2, right_eq_add, mul_self_eq_zero, norm_eq_zero] at this
    exact sub_eq_zero.1 (hι (this.trans (map_zero ι).symm))

def dopL {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V) (L : V →L[ℝ] ℝ) : 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ) where
  toFun := dop a L
  map_add' f g := by
    ext x
    simp only [dop_apply, SchwartzMap.add_apply]
    rw [show ⇑(f + g) = ⇑f + ⇑g from rfl, fderiv_add f.differentiableAt g.differentiableAt, ContinuousLinearMap.add_apply]
    ring
  map_smul' c f := by
    ext x
    simp only [dop_apply, SchwartzMap.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [show ⇑(c • f) = c • ⇑f from rfl, fderiv_const_smul f.differentiableAt, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring

theorem exists_dop_fin {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (N : Submodule ℂ 𝓢(V, ℂ))
    [FiniteDimensional ℂ N] : ∃ N' : Submodule ℂ 𝓢(V, ℂ), FiniteDimensional ℂ N' ∧ ∀ a L, ∀ f ∈ N, dop a L f ∈ N' := by
  let b := Module.finBasis ℝ (V × (V →L[ℝ] ℝ))
  refine ⟨⨆ i, N.map (dopL (b i).1 (b i).2), inferInstance, fun a L f hf => ?_⟩
  have : ∀ q ∈ Submodule.span ℝ (Set.range b), dop q.1 q.2 f ∈ ⨆ i, N.map (dopL (b i).1 (b i).2) := fun q hq => by
    induction hq using Submodule.span_induction with
    | mem q h => obtain ⟨i, rfl⟩ := h; exact Submodule.mem_iSup_of_mem i ⟨f, hf, rfl⟩
    | zero => convert Submodule.zero_mem _; ext x; simp [dop_apply]
    | add x y _ _ hx hy => rw [Prod.fst_add, Prod.snd_add, dop_add]; exact add_mem hx hy
    | smul t q _ h =>
      convert Submodule.smul_mem _ (t : ℂ) h
      ext x
      simp only [dop_apply, Prod.smul_fst, Prod.smul_snd, map_smul, ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply,
        smul_eq_mul, Complex.real_smul]
      push_cast
      ring
  exact this (a, L) (b.span_eq ▸ trivial)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def vacSp (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w) (ε : InfinitePlace F → ℤˣ) :
    Submodule ℂ (SInf F (Fin n × Fin d)) where
  carrier := {f | ∀ u u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → At (evI F) u' →
    (∀ w, u'.map (piInf (τ w)) = (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (τ w)) * (W.θ w)ᵀ)) →
    dopL (aOf M u') (lOf M u') f = Complex.I • dopL (aOf M u) (lOf M u) f}
  zero_mem' _ _ _ _ _ := by simp
  add_mem' hf hg u u' h1 h2 h3 := by rw [map_add (f := _), map_add (f := _), hf u u' h1 h2 h3, hg u u' h1 h2 h3, smul_add]
  smul_mem' c f hf u u' h1 h2 h3 := by rw [map_smul, map_smul, hf u u' h1 h2 h3, smul_comm]

theorem vacSp_fin (h : IsCMExt F E σ) (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w) (ε : InfinitePlace F → ℤˣ) :
    FiniteDimensional ℂ (vacSp M τ ε) := by
  let ev : SInf F (Fin n × Fin d) →L[ℂ] ℂ :=
    BoundedContinuousFunction.evalCLM ℂ 0 ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ
  refine FiniteDimensional.of_injective (ev.toLinearMap ∘ₗ (vacSp M τ ε).subtype)
    ((injective_iff_map_eq_zero _).2 fun f h0 => Subtype.ext ?_)
  by_contra hf
  let C : InfinitePlace F → Matrix (Fin n) (Fin d) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin d) ℂ := fun w =>
    { toFun := fun x => (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * x * (W.θ w)ᵀ)
      map_add' := fun x y => by rw [Matrix.mul_add, Matrix.add_mul, smul_add]
      map_smul' := fun t x => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]
        rw [smul_comm] }
  obtain ⟨S, J, sAt, sev, sJ⟩ := exists_real_structure σ h τ M.co.e C
  let T : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (Fin n × Fin d → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun y b => linForm b y) (fun y y' b => map_add _ y y') (fun t y b => map_smul _ t y)
      (fun y b b' => by simp only [linForm_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)])
      (fun t y b => by simp only [linForm_apply, Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul])
  obtain ⟨m, hm⟩ := GlobalTheory.CompanionTheory.Twist.FockLogDeriv.main T (fun b hb => funext fun i => trace_mul_eq_zero _ fun y => by
      have : linForm b (Pi.single i y) = 0 := hb _
      rw [linForm_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same, mul_comm] at this
      exact this) J f.1 hf fun p y => by
    have := congrArg (fun g : SInf F (Fin n × Fin d) => g y) (f.2 (S p) (S (J p)) (sAt _) (sAt _) fun w => sJ p w)
    simp only [dopL, LinearMap.coe_mk, AddHom.coe_mk, SchwartzMap.smul_apply, smul_eq_mul, dop_apply, aOf, lOf] at this
    rw [show aOf M (S p) = p.1 from (sev _).1, show aOf M (S (J p)) = (J p).1 from (sev _).1, (sev _).2, (sev _).2] at this
    exact this
  obtain ⟨c, Q, Q', hc, -, e⟩ := GlobalTheory.CompanionTheory.Twist.schwartz_logDeriv_linear_gaussian f.1 hf m hm
  have : f.1 0 = 0 := h0
  rw [e] at this
  exact mul_ne_zero hc (Complex.exp_ne_zero _) this

variable {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W}

theorem vacSp_map (hψ : IsStd ψ) (hs : IsSplitting (adeleClass F) ψ M.co (actAB (cA σ)) om)
    {τ : ∀ w : InfinitePlace F, EmbOver E w} {k : UA σ X.J} (hk : k ∈ KInf σ X τ) {A} (hA : Impl om (k, 1) A) {ε f}
    (hf : f ∈ vacSp M τ ε) : A f ∈ vacSp M τ ε := by
  intro u u' hu hu' hrel
  have e0 : ∀ g v, actAB (cA σ) ((g, 1) : UA σ X.J × UA σ W.J) v = mat g * v := fun g v => by simp [actAB, mat]
  have e1 : mat k * mat k⁻¹ = 1 := by show k.1.1 * ((k⁻¹ : UA σ X.J).1.1) = 1; simp
  have e2 : mat k⁻¹ * mat k = 1 := by show ((k⁻¹ : UA σ X.J).1.1) * k.1.1 = 1; simp
  have a1 := at_act (W := W) (k⁻¹, 1) hu
  have a2 := at_act (W := W) (k⁻¹, 1) hu'
  have i1 := inter hψ hs hA a1 f
  have i2 := inter hψ hs hA a2 f
  simp only [e0, ← Matrix.mul_assoc, e1, Matrix.one_mul] at i1 i2 a1 a2
  have := hf _ _ a1 a2 fun w => by
    have h1 : (mat k⁻¹).map (piInf (τ w)) * (mat k).map (piInf (τ w)) = 1 := by
      rw [← Matrix.map_mul, e2, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 : (mat k).map (piInf (τ w)) * (mat k⁻¹).map (piInf (τ w)) = 1 := by
      rw [← Matrix.map_mul, e1, Matrix.map_one _ (map_zero _) (map_one _)]
    have hc : (mat k⁻¹).map (piInf (τ w)) * X.θ w = X.θ w * (mat k⁻¹).map (piInf (τ w)) := by
      rw [← Matrix.one_mul (X.θ w * _), ← h1, Matrix.mul_assoc, ← Matrix.mul_assoc _ (X.θ w), (hk.2 w).eq, Matrix.mul_assoc,
        h2, Matrix.mul_one]
    rw [Matrix.map_mul, Matrix.map_mul, hrel w, Matrix.mul_smul]
    simp only [← Matrix.mul_assoc, hc]
  change dop _ _ _ = Complex.I • dop _ _ _ at this ⊢
  rw [← i1, ← i2, this, map_smul]

theorem pol_finite (h : IsCMExt F E σ) (hψ : IsStd ψ) (hs : IsSplitting (adeleClass F) ψ M.co (actAB (cA σ)) om)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) {f} (hf : f ∈ M.Pol ψ τ) :
    ∃ N : Submodule ℂ (SInf F (Fin n × Fin d)), FiniteDimensional ℂ N ∧ f ∈ N ∧
      ∀ k ∈ KInf σ X τ, ∀ A, Impl om (k, 1) A → ∀ g ∈ N, A g ∈ N := by
  let S : Submodule ℂ (SInf F (Fin n × Fin d)) :=
    { carrier := {f | ∃ N : Submodule ℂ (SInf F (Fin n × Fin d)), FiniteDimensional ℂ N ∧ f ∈ N ∧
        ∀ k ∈ KInf σ X τ, ∀ A, Impl om (k, 1) A → ∀ g ∈ N, A g ∈ N}
      zero_mem' := ⟨⊥, inferInstance, zero_mem _, fun k _ A _ g hg => by rw [(Submodule.mem_bot ℂ).1 hg, map_zero]; exact zero_mem _⟩
      add_mem' := by
        rintro f g ⟨N, _, h1, h2⟩ ⟨N', _, h1', h2'⟩
        refine ⟨N ⊔ N', inferInstance, Submodule.add_mem_sup h1 h1', fun k hk A hA g hg => ?_⟩
        obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hg
        rw [map_add (f := _)]
        exact Submodule.add_mem_sup (h2 k hk A hA x hx) (h2' k hk A hA y hy)
      smul_mem' := fun c f ⟨N, h0, h1, h2⟩ => ⟨N, h0, N.smul_mem c h1, h2⟩ }
  refine (sInf_le (a := S) ⟨fun f₀ ⟨ε, hε⟩ => ?_, fun u hu g ⟨N, h0, h1, h2⟩ g₁ hg => ?_⟩ : M.Pol ψ τ ≤ S) hf
  · exact ⟨vacSp M τ ε, vacSp_fin h M τ ε, fun u u' hu hu' e => hε u u' hu hu' e _ _ (actsD_dop M hψ hu f₀)
      (actsD_dop M hψ hu' f₀), fun k hk A hA g hg => vacSp_map hψ hs hk hA hg⟩
  · obtain ⟨N', h3, h4⟩ := exists_dop_fin N
    refine ⟨Submodule.span ℂ {z | ∃ v, At (evI F) v ∧ ∃ x ∈ N, z = dop (aOf M v) (lOf M v) x},
      Submodule.finiteDimensional_of_le (S₂ := N') (Submodule.span_le.2 ?_),
      Submodule.subset_span ⟨u, hu, g, h1, actsD_unique' M hψ hu hg⟩, fun k hk A hA z hz => ?_⟩
    · rintro _ ⟨v, -, x, hx, rfl⟩
      exact h4 _ _ x hx
    · refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap A.toLinearMap (Submodule.span ℂ
        {z | ∃ v, At (evI F) v ∧ ∃ x ∈ N, z = dop (aOf M v) (lOf M v) x}))).2 ?_ hz)
      rintro _ ⟨v, hv, x, hx, rfl⟩
      exact Submodule.subset_span ⟨_, at_act _ hv, _, h2 k hk A hA x hx, inter hψ hs hA hv x⟩

end Dense

theorem realInv_of (hA : PositivityTheory.ThKF.ArchOp) : RealInv := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp _ P _ _ _ p hq
  obtain ⟨f, hf, h0⟩ : ∃ f ∈ M.Pol B.ψ B.emb, p f ≠ 0 := by
    obtain ⟨y, hy⟩ := exists_ne (0 : P)
    obtain ⟨f, hf, rfl⟩ : y ∈ (M.Pol B.ψ B.emb).map p := hq.onto ▸ trivial
    exact ⟨f, hf, hy⟩
  have hs := hp.weil.isUSplitting
  obtain ⟨N, _, h1, h2⟩ := Dense.pol_finite hp.base.cm hp.base.std hs.toIsSplitting B.emb hf
  haveI : FiniteDimensional ℂ (N ⊓ M.Pol B.ψ B.emb : Submodule ℂ _) := Submodule.finiteDimensional_of_le inf_le_left
  haveI := Dense.volume_isAddHaar F (Fin n × Fin d)
  haveI : BorelSpace (Fin n × Fin d → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  obtain ⟨f₀, hf₀, hne, hfix⟩ := Dense.exists_fixed
    (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F))).toLinearMap
    (SchwartzMap.injective_toLp 2 _) p (N ⊓ M.Pol B.ψ B.emb) ⟨h1, hf⟩ h0
  refine ⟨f₀, hf₀.2, hne, fun k hk => ?_⟩
  have h1W : (1 : UA σ W.J) ∈ UAt σ W (evI F) := fun u _ => by simp [mat]
  obtain ⟨T, hT, hP⟩ := hA F E σ B n d X W M χX χW om r s r' s' hp k hk.1 1 h1W
  have hP' := hP hk ⟨h1W, fun w => by simp [mat]⟩
  have hn := Dense.lintegral_eq (S := om (k, 1)) (fun μ hμ => hs.unit μ hμ (k, 1)) (hT.1 f₀)
  have := hfix (T f₀) ⟨h2 k hk T hT.1 _ hf₀.1, hP' _ hf₀.2⟩ (hq.cpt k hk f₀ hf₀.2 _ (hT.2 f₀)) (by
    change ‖(T f₀).toLp 2 _‖ = ‖f₀.toLp 2 _‖
    simp only [SchwartzMap.norm_toLp, eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top (T f₀).continuous.aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top f₀.continuous.aestronglyMeasurable,
      ENNReal.toReal_ofNat, ENNReal.rpow_two, hn])
  simpa only [this] using hT.2 f₀

end GlobalTheory.ThK.Dbl

end
