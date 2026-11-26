module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinWronskianNeZero
public import GroundTheory.GlobalFields.ComplexMultiplication.JInvariantSurjective
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.JInvariantEqualSl2Orbit
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.JInvariantEqualSl2Orbit
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.JOrbit

open GroundTheory.Global.Elliptic

theorem exists_smul_of_homothetic (τ σ : ℍ) {c : ℂ} (hc : c ≠ 0)
    (h : ((latticeOfTau τ).lattice : Set ℂ) = (c * ·) '' (latticeOfTau σ).lattice) :
    ∃ γ : SL(2, ℤ), τ = γ • σ := by
  have m1 : (τ : ℂ) ∈ (c * ·) '' ((latticeOfTau σ).lattice : Set ℂ) := by
    rw [← h]; exact (latticeOfTau τ).ω₁_mem_lattice
  have m2 : (1 : ℂ) ∈ (c * ·) '' ((latticeOfTau σ).lattice : Set ℂ) := by
    rw [← h]; exact (latticeOfTau τ).ω₂_mem_lattice
  have m3 : c * σ ∈ ((latticeOfTau τ).lattice : Set ℂ) := by
    rw [h]; exact ⟨σ, (latticeOfTau σ).ω₁_mem_lattice, rfl⟩
  have m4 : c * 1 ∈ ((latticeOfTau τ).lattice : Set ℂ) := by
    rw [h]; exact ⟨1, (latticeOfTau σ).ω₂_mem_lattice, rfl⟩
  obtain ⟨z, hz, h1⟩ := m1
  obtain ⟨w, hw, h2⟩ := m2
  obtain ⟨a, b, rfl⟩ := PeriodPair.mem_lattice.1 hz
  obtain ⟨e, f, rfl⟩ := PeriodPair.mem_lattice.1 hw
  obtain ⟨p, q, h3⟩ := PeriodPair.mem_lattice.1 m3
  obtain ⟨r, s, h4⟩ := PeriodPair.mem_lattice.1 m4
  simp only [latticeOfTau_ω₁, latticeOfTau_ω₂, mul_one] at h1 h2 h3 h4
  have k1 : (σ : ℂ) = p * (a * σ + b) + q * (e * σ + f) := by
    apply mul_left_cancel₀ hc
    linear_combination -h3 - p * h1 - q * h2
  have k2 : (1 : ℂ) = r * (a * σ + b) + s * (e * σ + f) := by
    apply mul_left_cancel₀ hc
    linear_combination -h4 - r * h1 - s * h2
  have k3 : (τ : ℂ) * (e * σ + f) = a * σ + b := by
    apply mul_left_cancel₀ hc
    linear_combination (τ : ℂ) * h2 - h1
  have hy : 0 < σ.im := σ.im_pos
  have hv : 0 < τ.im := τ.im_pos
  have k1i := congrArg Complex.im k1
  have k1r := congrArg Complex.re k1
  have k2i := congrArg Complex.im k2
  have k2r := congrArg Complex.re k2
  have k3i := congrArg Complex.im k3
  have k3r := congrArg Complex.re k3
  simp at k1i k1r k2i k2r k3i k3r
  have e1 : ((p * a + q * e : ℤ) : ℝ) = (1 : ℤ) := by
    apply mul_right_cancel₀ hy.ne'
    push_cast; linear_combination -k1i
  have e3 : ((r * a + s * e : ℤ) : ℝ) = (0 : ℤ) := by
    apply mul_right_cancel₀ hy.ne'
    push_cast; linear_combination -k2i
  have e2 : ((p * b + q * f : ℤ) : ℝ) = (0 : ℤ) := by
    push_cast at e1 ⊢; linear_combination -k1r - σ.re * e1
  have e4 : ((r * b + s * f : ℤ) : ℝ) = (1 : ℤ) := by
    push_cast at e3 ⊢; linear_combination -k2r - σ.re * e3
  have e1' : p * a + q * e = 1 := by exact_mod_cast e1
  have e2' : p * b + q * f = 0 := by exact_mod_cast e2
  have e3' : r * a + s * e = 0 := by exact_mod_cast e3
  have e4' : r * b + s * f = 1 := by exact_mod_cast e4
  have hdet : (a * f - b * e) * (p * s - q * r) = 1 := by
    linear_combination (r * b + s * f) * e1' + e4' - (r * a + s * e) * e2'
  have him : τ.im * ((e * σ.re + f) ^ 2 + (e * σ.im) ^ 2) = σ.im * ((a * f - b * e : ℤ) : ℝ) := by
    push_cast
    linear_combination (e * σ.re + f) * k3i - (e * σ.im) * k3r
  have hnn : (0 : ℝ) ≤ ((a * f - b * e : ℤ) : ℝ) := by
    have : 0 ≤ σ.im * ((a * f - b * e : ℤ) : ℝ) := by rw [← him]; positivity
    exact (mul_nonneg_iff_of_pos_left hy).1 this
  have hnn' : 0 ≤ a * f - b * e := by exact_mod_cast hnn
  have hD : a * f - b * e = 1 := Int.eq_one_of_mul_eq_one_right hnn' hdet
  have hne : (e : ℂ) * σ + f ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h2
    exact zero_ne_one h2
  let γ : SL(2, ℤ) := ⟨!![a, b; e, f], by rw [Matrix.det_fin_two_of]; exact hD⟩
  refine ⟨γ, ?_⟩
  ext
  rw [coe_specialLinearGroup_apply γ σ]
  simp [γ]
  rw [eq_div_iff hne, k3]

theorem exists_smul_of_E₄_E₆ :
    ∀ τ σ : ℍ, E₄ τ ^ 3 * E₆ σ ^ 2 = E₆ τ ^ 2 * E₄ σ ^ 3 → ∃ γ : SL(2, ℤ), τ = γ • σ := by
  intro τ σ h
  have hj : modularJ σ = modularJ τ := by
    have h1 := ModularForm.discriminant_ne_zero τ
    have h2 := ModularForm.discriminant_ne_zero σ
    rw [modularJ, modularJ, div_eq_div_iff h2 h1,
      ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ,
      ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq σ]
    linear_combination h / 1728
  obtain ⟨c, hc, hl⟩ := (modularJ_eq_iff σ τ).1 hj
  exact exists_smul_of_homothetic τ σ hc hl

end GlobalTheory.JOrbit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.JInvariantEqualSl2OrbitStatement
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.j_invariant_equal_sl2_orbit : ∀ τ σ : ℍ, E₄ τ ^ 3 * E₆ σ ^ 2 = E₆ τ ^ 2 * E₄ σ ^ 3 → ∃ γ : SL(2, ℤ), τ = γ • σ := by
  first | exact @GlobalTheory.JOrbit.exists_smul_of_E₄_E₆ | exact GlobalTheory.JOrbit.exists_smul_of_E₄_E₆ | (intros; apply GlobalTheory.JOrbit.exists_smul_of_E₄_E₆ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelOneSimpleZeroFormAtPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EllipticPointsStabilizer
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EllipticPointsStabilizer
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.EllipticZero

lemma denom_mul_SL (g h : SL(2, ℤ)) (z : ℍ) :
    denom ((g * h : SL(2, ℤ)) : GL (Fin 2) ℝ) z
      = denom (g : GL (Fin 2) ℝ) ((h • z : ℍ) : ℂ) * denom (h : GL (Fin 2) ℝ) z := by
  have hd : 0 < ((h : GL (Fin 2) ℝ)).det.val := by simp
  have := denom_cocycle (g : GL (Fin 2) ℝ) (h : GL (Fin 2) ℝ) z.im_ne_zero
  rw [← coe_smul_of_det_pos hd, ← ModularGroup.sl_moeb] at this
  rw [← this, map_mul, map_mul]

lemma conj_fix (γ u : SL(2, ℤ)) (σ : ℍ) (hu : u • σ = σ) :
    (γ * u * γ⁻¹) • (γ • σ) = γ • σ ∧
      denom ((γ * u * γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) ((γ • σ : ℍ) : ℂ)
        = denom (u : GL (Fin 2) ℝ) σ := by
  refine ⟨by rw [mul_smul, mul_smul, inv_smul_smul, hu], ?_⟩
  have h1 := denom_mul_SL (γ * u * γ⁻¹) γ σ
  have h2 := denom_mul_SL γ u σ
  rw [inv_mul_cancel_right, h2, hu, mul_comm] at h1
  exact (mul_right_cancel₀ (denom_ne_zero _ _) h1).symm

lemma eq_zero_of_fix {k : ℤ} (f : ModularForm 𝒮ℒ k) (u : SL(2, ℤ)) (σ : ℍ) (hu : u • σ = σ)
    (hk : denom (u : GL (Fin 2) ℝ) σ ^ k ≠ 1) : f σ = 0 := by
  have h : f (u • σ) = denom u σ ^ k * f σ :=
    SlashInvariantForm.slash_action_eqn'' f (by simp) σ
  rw [hu] at h
  have : (denom (u : GL (Fin 2) ℝ) σ ^ k - 1) * f σ = 0 := by linear_combination -h
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hk)

lemma exists_four : ∃ (σ : ℍ) (u : SL(2, ℤ)), u • σ = σ ∧
    IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) σ) 4 := by
  refine ⟨UpperHalfPlane.I, ModularGroup.S, ?_, ?_⟩
  · rw [modular_S_smul]; ext1; simp
  · rw [ModularGroup.denom_S]; exact Complex.isPrimitiveRoot_I

lemma exists_six : ∃ (σ : ℍ) (u : SL(2, ℤ)), u • σ = σ ∧
    IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) σ) 6 := by
  have hp := Complex.isPrimitiveRoot_exp 6 (by norm_num)
  set μ := Complex.exp (2 * Real.pi * Complex.I / (6 : ℕ)) with hμ
  have him : 0 < μ.im := by
    have : μ = Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * Complex.I) := by
      rw [hμ]; congr 1; push_cast; ring
    rw [this, Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_three]
    positivity
  have h6 : μ ^ 6 = 1 := hp.pow_eq_one
  have h3 : μ ^ 3 - 1 ≠ 0 := sub_ne_zero.2 (hp.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num))
  have h1 : μ + 1 ≠ 0 := fun h => by
    have := congrArg Complex.im h
    simp at this
    exact him.ne' this
  have hq : μ ^ 2 - μ + 1 = 0 := by
    have : (μ ^ 3 - 1) * ((μ + 1) * (μ ^ 2 - μ + 1)) = 0 := by linear_combination h6
    exact (mul_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h3)).resolve_left h1
  have h0 : μ ≠ 0 := hp.ne_zero (by norm_num)
  refine ⟨⟨μ, him⟩, ModularGroup.T * ModularGroup.S, ?_, ?_⟩
  · rw [mul_smul, modular_S_smul, modular_T_smul]
    ext1
    simp only [coe_vadd]
    push_cast
    field_simp
    linear_combination -hq
  · rw [denom_mul_SL, ModularGroup.denom_S]
    have : ∀ z : ℍ, denom ((ModularGroup.T : SL(2, ℤ)) : GL (Fin 2) ℝ) z = 1 := fun z => by
      rw [ModularGroup.denom_apply]; simp [ModularGroup.T]
    rw [this, one_mul]
    exact hp

theorem elliptic_of_zero : ∀ τ₀ : ℍ,
    (E₆ τ₀ = 0 → ∃ u : SL(2, ℤ), u • τ₀ = τ₀ ∧ IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) τ₀) 4) ∧
    (E₄ τ₀ = 0 → ∃ u : SL(2, ℤ), u • τ₀ = τ₀ ∧
      IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) τ₀) 6) := by
  intro τ₀
  constructor
  · intro h
    obtain ⟨σ, u, hu, hp⟩ := exists_four
    have h0 : E₆ σ = 0 := eq_zero_of_fix E₆ u σ hu (by
      rw [Ne, hp.zpow_eq_one_iff_dvd]; norm_num)
    obtain ⟨γ, rfl⟩ := GlobalTheory.T.j_invariant_equal_sl2_orbit τ₀ σ (by rw [h, h0]; ring)
    obtain ⟨h1, h2⟩ := conj_fix γ u σ hu
    exact ⟨_, h1, h2 ▸ hp⟩
  · intro h
    obtain ⟨σ, u, hu, hp⟩ := exists_six
    have h0 : E₄ σ = 0 := eq_zero_of_fix E₄ u σ hu (by
      rw [Ne, hp.zpow_eq_one_iff_dvd]; norm_num)
    obtain ⟨γ, rfl⟩ := GlobalTheory.T.j_invariant_equal_sl2_orbit τ₀ σ (by rw [h, h0]; ring)
    obtain ⟨h1, h2⟩ := conj_fix γ u σ hu
    exact ⟨_, h1, h2 ▸ hp⟩

end GlobalTheory.EllipticZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EllipticPointsStabilizerStatement
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elliptic_points_stabilizer : ∀ τ₀ : ℍ, (E₆ τ₀ = 0 → ∃ u : SL(2, ℤ), u • τ₀ = τ₀ ∧ IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) τ₀) 4) ∧ (E₄ τ₀ = 0 → ∃ u : SL(2, ℤ), u • τ₀ = τ₀ ∧ IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) τ₀) 6) := by
  first | exact @GlobalTheory.EllipticZero.elliptic_of_zero | exact GlobalTheory.EllipticZero.elliptic_of_zero | (intros; apply GlobalTheory.EllipticZero.elliptic_of_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinWronskianNeZeroStatement
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_wronskian_ne_zero : ∀ τ : ℍ, 2 * E₄ τ * deriv (⇑E₆ ∘ ofComplex) τ - 3 * E₆ τ * deriv (⇑E₄ ∘ ofComplex) τ ≠ 0 := by
  first | exact @GlobalTheory.EisWronskian.wronskian_E₄_E₆_ne_zero | exact GlobalTheory.EisWronskian.wronskian_E₄_E₆_ne_zero | (intros; apply GlobalTheory.EisWronskian.wronskian_E₄_E₆_ne_zero <;> assumption)
end

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.LevelOneLocal

theorem tendsto_E {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    Tendsto (ModularForm.E hk : ℍ → ℂ) atImInfty (𝓝 1) := by
  have h0 : valueAtInfty (ModularForm.E hk : ℍ → ℂ) = 1 := by
    rw [← qExpansion_coeff_zero one_pos
      (ModularFormClass.analyticAt_cuspFunction_zero (ModularForm.E hk) one_pos one_mem_strictPeriods_SL)
      (SlashInvariantFormClass.periodic_comp_ofComplex (ModularForm.E hk) one_mem_strictPeriods_SL)]
    exact EisensteinSeries.E_qExpansion_coeff_zero hk hk2
  obtain ⟨c, hc, h⟩ := ModularFormClass.exp_decay_sub_atImInfty' (ModularForm.E hk)
  rw [h0] at h
  have h2 : Tendsto (fun τ : ℍ ↦ Real.exp (-c * τ.im)) atImInfty (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    exact Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_comap
  simpa using (h.trans_tendsto h2).add_const 1

theorem tendsto_E₄ : Tendsto (E₄ : ℍ → ℂ) atImInfty (𝓝 1) := tendsto_E _ ⟨2, rfl⟩

theorem tendsto_E₆ : Tendsto (E₆ : ℍ → ℂ) atImInfty (𝓝 1) := tendsto_E _ ⟨3, rfl⟩

theorem cube_sub_sq_ne_zero (τ : ℍ) : E₄ τ ^ 3 - E₆ τ ^ 2 ≠ 0 := by
  intro h
  apply ModularForm.discriminant_ne_zero τ
  rw [ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq, h, zero_div]

theorem isMF_E₄ : IsMF ⊤ 4 (E₄ : ℍ → ℂ) := isMF_coe_top E₄

theorem isMF_E₆ : IsMF ⊤ 6 (E₆ : ℍ → ℂ) := isMF_coe_top E₆

theorem differentiableAt_comp {f : ℍ → ℂ} (hf : MDiff f) (τ : ℍ) :
    DifferentiableAt ℂ (f ∘ ofComplex) τ :=
  mdifferentiableAt_iff.mp (hf τ)

theorem deriv_comb (α β : ℂ) (τ : ℍ) :
    deriv ((α • (E₄ : ℍ → ℂ) ^ 3 - β • (E₆ : ℍ → ℂ) ^ 2) ∘ ofComplex) τ =
      α * (3 * E₄ τ ^ 2 * deriv (⇑E₄ ∘ ofComplex) τ) - β * (2 * E₆ τ * deriv (⇑E₆ ∘ ofComplex) τ) := by
  have h4 := (differentiableAt_comp isMF_E₄.2.1 τ).hasDerivAt
  have h6 := (differentiableAt_comp isMF_E₆.2.1 τ).hasDerivAt
  have h := ((h4.fun_pow 3).const_mul α).fun_sub ((h6.fun_pow 2).const_mul β)
  have e : (α • (E₄ : ℍ → ℂ) ^ 3 - β • (E₆ : ℍ → ℂ) ^ 2) ∘ ofComplex =
      fun x => α * (⇑E₄ ∘ ofComplex) x ^ 3 - β * (⇑E₆ ∘ ofComplex) x ^ 2 := by
    ext x; simp
  rw [e, h.deriv]
  simp

theorem exists_local_data : ∀ τ₀ : ℍ, ∃ (n : ℕ) (a b : ℤ) (E : ℍ → ℂ) (u : SL(2, ℤ)), u • τ₀ = τ₀ ∧ 0 < n ∧ IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) τ₀) n ∧ a < b ∧ Even (b - a) ∧ IsMF ⊤ b E ∧ (∀ τ : ℍ, E τ = 0 → deriv (E ∘ ofComplex) τ ≠ 0 ∧ ∃ γ : SL(2, ℤ), τ = γ • τ₀) ∧ (∃ c : ℂ, c ≠ 0 ∧ Tendsto E atImInfty (𝓝 c)) ∧ ∀ d : ℤ, 0 ≤ d → (n : ℤ) ∣ d → ∃ e : ℍ → ℂ, IsMF ⊤ (d + a) e ∧ e τ₀ ≠ 0 := by
  intro τ₀
  have hD := cube_sub_sq_ne_zero τ₀
  by_cases h6 : E₆ τ₀ = 0
  · obtain ⟨u, hu, hp⟩ := (GlobalTheory.T.elliptic_points_stabilizer τ₀).1 h6
    have h4 : E₄ τ₀ ≠ 0 := fun h => hD (by simp [h, h6])
    refine ⟨4, 0, 6, E₆, u, hu, by norm_num, hp, by norm_num, by decide, isMF_E₆, fun τ hτ => ⟨?_, ?_⟩,
      ⟨1, one_ne_zero, tendsto_E₆⟩, ?_⟩
    · intro h
      exact GlobalTheory.T.eisenstein_wronskian_ne_zero τ (by simp [h, hτ])
    · exact GlobalTheory.T.j_invariant_equal_sl2_orbit τ τ₀ (by simp [h6, hτ])
    · rintro d hd ⟨m, rfl⟩
      obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ m by push_cast at hd; omega)
      refine ⟨(E₄ : ℍ → ℂ) ^ m, ?_, by simpa using fun h => absurd h h4⟩
      have := isMF_E₄.pow m
      convert this using 1
      push_cast; ring
  by_cases h4 : E₄ τ₀ = 0
  · obtain ⟨u, hu, hp⟩ := (GlobalTheory.T.elliptic_points_stabilizer τ₀).2 h4
    refine ⟨6, 0, 4, E₄, u, hu, by norm_num, hp, by norm_num, by decide, isMF_E₄, fun τ hτ => ⟨?_, ?_⟩,
      ⟨1, one_ne_zero, tendsto_E₄⟩, ?_⟩
    · intro h
      exact GlobalTheory.T.eisenstein_wronskian_ne_zero τ (by simp [h, hτ])
    · exact GlobalTheory.T.j_invariant_equal_sl2_orbit τ τ₀ (by simp [h4, hτ])
    · rintro d hd ⟨m, rfl⟩
      obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ m by push_cast at hd; omega)
      refine ⟨(E₆ : ℍ → ℂ) ^ m, ?_, by simpa using fun h => absurd h h6⟩
      have := isMF_E₆.pow m
      convert this using 1
      push_cast; ring
  refine ⟨2, 4, 12, (E₆ τ₀ ^ 2) • (E₄ : ℍ → ℂ) ^ 3 - (E₄ τ₀ ^ 3) • (E₆ : ℍ → ℂ) ^ 2, -1, ?_, by norm_num, ?_,
    by norm_num, by decide, ?_, fun τ hτ => ?_, ⟨E₆ τ₀ ^ 2 - E₄ τ₀ ^ 3, fun h => hD (by linear_combination -h), ?_⟩,
    ?_⟩
  · rw [ModularGroup.SL_neg_smul, one_smul]
  · have : denom ((-1 : SL(2, ℤ)) : GL (Fin 2) ℝ) τ₀ = -1 := by simp [denom]
    rw [this]
    exact IsPrimitiveRoot.neg_one 0 (by norm_num)
  · exact ((isMF_E₄.pow 3).smul _).sub ((isMF_E₆.pow 2).smul _)
  · have hz : E₆ τ₀ ^ 2 * E₄ τ ^ 3 - E₄ τ₀ ^ 3 * E₆ τ ^ 2 = 0 := by simpa using hτ
    refine ⟨?_, GlobalTheory.T.j_invariant_equal_sl2_orbit τ τ₀ (by linear_combination hz)⟩
    have hDτ := cube_sub_sq_ne_zero τ
    have k4 : E₄ τ ≠ 0 := by
      intro h
      have : E₆ τ = 0 := by simpa [h, h4] using hz
      exact hDτ (by simp [h, this])
    rw [deriv_comb]
    intro h
    have hW := GlobalTheory.T.eisenstein_wronskian_ne_zero τ
    apply mul_ne_zero (mul_ne_zero (pow_ne_zero 2 h6) (pow_ne_zero 3 k4)) hW
    linear_combination (2 * E₄ τ * deriv (⇑E₆ ∘ ofComplex) τ) * hz - (E₄ τ * E₆ τ) * h
  · have := ((tendsto_E₄.pow 3).const_mul (E₆ τ₀ ^ 2)).sub ((tendsto_E₆.pow 2).const_mul (E₄ τ₀ ^ 3))
    simp only [one_pow, mul_one] at this
    exact this
  · rintro d hd ⟨m, rfl⟩
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ m by push_cast at hd; omega)
    rcases Nat.even_or_odd' m with ⟨p, rfl | rfl⟩
    · refine ⟨(E₄ : ℍ → ℂ) ^ (p + 1), ?_, by simpa using h4⟩
      have := isMF_E₄.pow (p + 1)
      convert this using 1
      push_cast; ring
    · refine ⟨(E₄ : ℍ → ℂ) ^ p * E₆, (isMF_E₄.pow p).mul isMF_E₆ (by push_cast; ring), ?_⟩
      exact mul_ne_zero (pow_ne_zero p h4) h6

end GlobalTheory.LevelOneLocal
end

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

open ModularForm (E₄ E₆) in
private lemma sum_range_zpow_primitiveRoot_pow {ζ : ℂ} {n : ℕ} (hζ : IsPrimitiveRoot ζ n) (t : ℤ) :
    ∑ m ∈ Finset.range n, (ζ ^ t) ^ m = if (n : ℤ) ∣ t then (n : ℂ) else 0 := by
  split_ifs with hdvd
  · rw [(hζ.zpow_eq_one_iff_dvd t).2 hdvd]
    simp
  · have hne : ζ ^ t ≠ 1 := fun h1 => hdvd ((hζ.zpow_eq_one_iff_dvd t).1 h1)
    rw [geom_sum_eq hne]
    have : (ζ ^ t) ^ n = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow]
    rw [this, sub_self, zero_div]

open ModularForm (E₄ E₆) in
private lemma eventually_ne_zero_nhdsNE_of_simple_zero {E : ℍ → ℂ} (hE : MDiff E) {z : ℂ}
    (hz : 0 < z.im) (he : (E ∘ ofComplex) z = 0) (hd : deriv (E ∘ ofComplex) z ≠ 0) :
    ∀ᶠ w in 𝓝[≠] z, (E ∘ ofComplex) w ≠ 0 := by
  have hU : {w : ℂ | 0 < w.im} ∈ 𝓝 z :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz
  have hdiff : DifferentiableAt ℂ (E ∘ ofComplex) z :=
    (UpperHalfPlane.mdifferentiable_iff.1 hE).differentiableAt hU
  have hc : ContinuousAt (dslope (E ∘ ofComplex) z) z := continuousAt_dslope_same.2 hdiff
  have h1 : ∀ᶠ w in 𝓝 z, dslope (E ∘ ofComplex) z w ≠ 0 :=
    hc.eventually_ne (by rwa [dslope_same])
  filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with w hw hwz
  have hs := sub_smul_dslope (E ∘ ofComplex) z w
  rw [he, sub_zero, smul_eq_mul] at hs
  rw [← hs]
  exact mul_ne_zero (sub_ne_zero.2 hwz) hw

open ModularForm (E₄ E₆) in
private lemma eq_of_eq_off_simple_zeros' {E A B : ℍ → ℂ} (hE : MDiff E)
    (hzero : ∀ τ : ℍ, E τ = 0 → deriv (E ∘ ofComplex) τ ≠ 0) (hA : MDiff A) (hB : MDiff B)
    (h : ∀ τ, E τ ≠ 0 → A τ = B τ) : A = B := by
  funext τ
  by_cases hτ : E τ = 0
  swap
  · exact h τ hτ
  have hU : {w : ℂ | 0 < w.im} ∈ 𝓝 (τ : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds τ.im_pos
  have hAc : ContinuousAt (A ∘ ofComplex) τ :=
    ((UpperHalfPlane.mdifferentiable_iff.1 hA).differentiableAt hU).continuousAt
  have hBc : ContinuousAt (B ∘ ofComplex) τ :=
    ((UpperHalfPlane.mdifferentiable_iff.1 hB).differentiableAt hU).continuousAt
  have hev := eventually_ne_zero_nhdsNE_of_simple_zero hE τ.im_pos (by simpa using hτ) (hzero τ hτ)
  have heq : A ∘ ofComplex =ᶠ[𝓝[≠] (τ : ℂ)] B ∘ ofComplex := by
    filter_upwards [hev] with w hw
    exact h _ hw
  have := tendsto_nhds_unique ((hAc.tendsto.mono_left nhdsWithin_le_nhds).congr' heq)
    (hBc.tendsto.mono_left nhdsWithin_le_nhds)
  simpa using this

open ModularForm (E₄ E₆) in
private lemma exists_isMF_mul_eq_of_vanishes_on_orbit {Γ : Subgroup SL(2, ℤ)} {N b : ℤ}
    {E H : ℍ → ℂ} {τ₀ : ℍ} (hE : _root_.GlobalTheory.OddFrame.IsMF ⊤ b E)
    (hzero : ∀ τ : ℍ, E τ = 0 → deriv (E ∘ ofComplex) τ ≠ 0 ∧ ∃ γ : SL(2, ℤ), τ = γ • τ₀)
    (hlim : ∃ c, c ≠ 0 ∧ Tendsto E atImInfty (𝓝 c)) (hH : _root_.GlobalTheory.OddFrame.IsMF Γ N H)
    (hHz : ∀ γ : SL(2, ℤ), H (γ • τ₀) = 0) :
    ∃ G, _root_.GlobalTheory.OddFrame.IsMF Γ (N - b) G ∧ ∀ τ, E τ * G τ = H τ := by
  set e := E ∘ ofComplex with he_def
  set h := H ∘ ofComplex with hh_def
  let g : ℂ → ℂ := fun w => if e w = 0 then deriv h w / deriv e w else h w / e w
  have hEe : ∀ τ : ℍ, e τ = E τ := fun τ => by simp [he_def]
  have hHh : ∀ τ : ℍ, h τ = H τ := fun τ => by simp [hh_def]
  have hprod : ∀ τ : ℍ, E τ * g τ = H τ := by
    intro τ
    by_cases h0 : E τ = 0
    · obtain ⟨γ, hγ⟩ := (hzero τ h0).2
      rw [h0, zero_mul, hγ, hHz γ]
    · have h0' : e τ ≠ 0 := by rwa [hEe]
      show E τ * (if e τ = 0 then _ else _) = H τ
      rw [if_neg h0', hEe, hHh, mul_div_cancel₀ _ h0]
  set G : ℍ → ℂ := fun τ => g τ with hG_def
  have hGdiv : ∀ τ, E τ ≠ 0 → G τ = H τ / E τ := fun τ hτ =>
    eq_div_of_mul_eq hτ (by rw [mul_comm]; exact hprod τ)
  have hU' : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hed : DifferentiableOn ℂ e {w : ℂ | 0 < w.im} :=
    UpperHalfPlane.mdifferentiable_iff.1 hE.2.1
  have hhd : DifferentiableOn ℂ h {w : ℂ | 0 < w.im} :=
    UpperHalfPlane.mdifferentiable_iff.1 hH.2.1
  have hgd : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ g z := by
    intro z hz
    have hU := hU'.mem_nhds hz
    have hcoe : ((ofComplex z : ℍ) : ℂ) = z := by rw [ofComplex_apply_of_im_pos hz]
    by_cases hez : e z = 0
    · have hz' : E (ofComplex z) = 0 := hez
      have hdz : deriv e z ≠ 0 := by have := (hzero _ hz').1; rwa [hcoe] at this
      obtain ⟨γ, hγ⟩ := (hzero _ hz').2
      have hhz : h z = 0 := by show H (ofComplex z) = 0; rw [hγ]; exact hHz γ
      have hds : DifferentiableAt ℂ (fun w => dslope h z w / dslope e z w) z :=
        (((Complex.differentiableOn_dslope hU).2 hhd).differentiableAt hU).div
          (((Complex.differentiableOn_dslope hU).2 hed).differentiableAt hU) (by rwa [dslope_same])
      apply hds.congr_of_eventuallyEq
      have hc : ContinuousAt (dslope e z) z := continuousAt_dslope_same.2 (hed.differentiableAt hU)
      filter_upwards [hc.eventually_ne (by rwa [dslope_same] : dslope e z z ≠ 0)] with w hw
      by_cases hwz : w = z
      · rw [hwz]
        show (if e z = 0 then _ else _) = _
        rw [if_pos hez, dslope_same, dslope_same]
      · have he' : e w = (w - z) * dslope e z w := by
          have := sub_smul_dslope e z w
          rw [hez, sub_zero, smul_eq_mul] at this
          exact this.symm
        have hh' : h w = (w - z) * dslope h z w := by
          have := sub_smul_dslope h z w
          rw [hhz, sub_zero, smul_eq_mul] at this
          exact this.symm
        have hew : e w ≠ 0 := by rw [he']; exact mul_ne_zero (sub_ne_zero.2 hwz) hw
        show (if e w = 0 then _ else _) = _
        rw [if_neg hew, he', hh', mul_div_mul_left _ _ (sub_ne_zero.2 hwz)]
    · have hq : DifferentiableAt ℂ (fun w => h w / e w) z :=
        (hhd.differentiableAt hU).div (hed.differentiableAt hU) hez
      apply hq.congr_of_eventuallyEq
      filter_upwards [(hed.differentiableAt hU).continuousAt.eventually_ne hez] with w hw
      show (if e w = 0 then _ else _) = _
      rw [if_neg hw]
  have hGm : MDiff G := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    intro z hz
    have hU := hU'.mem_nhds hz
    have heq : G ∘ ofComplex =ᶠ[𝓝 z] g := by
      filter_upwards [hU] with w hw
      simp only [Function.comp_apply, hG_def]
      rw [ofComplex_apply_of_im_pos hw]
    exact ((hgd z hz).congr_of_eventuallyEq heq).differentiableWithinAt
  have hkey : ∀ (x : SL(2, ℤ)) (τ : ℍ), E τ ≠ 0 →
      (G ∣[N - b] x) τ = (H ∣[N] x) τ / E τ := by
    intro x τ hτ
    have hEx := congrFun (hE.slash_top x) τ
    rw [ModularForm.SL_slash_apply] at hEx
    rw [ModularForm.SL_slash_apply, ModularForm.SL_slash_apply]
    set D := denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) x)) (τ : ℂ) with hD
    have hD0 : D ≠ 0 := denom_ne_zero _ _
    have hEx' : E (x • τ) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hEx
      exact hτ hEx.symm
    rw [hGdiv _ hEx', ← hEx, show -(N - b) = -N - -b by ring, zpow_sub₀ hD0]
    have hb0 : D ^ (-b) ≠ 0 := zpow_ne_zero _ hD0
    field_simp
  refine ⟨G, ⟨fun γ hγ => ?_, hGm, fun x => ?_⟩, hprod⟩
  · apply eq_of_eq_off_simple_zeros' hE.2.1 (fun τ hτ => (hzero τ hτ).1)
      (_root_.GlobalTheory.OddFrame.mdiff_slash hGm _ _) hGm
    intro τ hτ
    rw [hkey γ τ hτ, hH.1 γ hγ, hGdiv τ hτ]
  · obtain ⟨c, hc, hEc⟩ := hlim
    have hinv : BoundedAtFilter atImInfty (fun τ => (E τ)⁻¹) := by
      unfold BoundedAtFilter
      exact (hEc.inv₀ hc).isBigO_one ℝ
    have hbd := (hH.2.2 x).mul hinv
    unfold IsBoundedAtImInfty BoundedAtFilter at hbd ⊢
    refine hbd.congr' ?_ EventuallyEq.rfl
    filter_upwards [hEc.eventually_ne hc] with τ hτ
    rw [Pi.mul_apply, hkey x τ hτ, div_eq_mul_inv]

open ModularForm (E₄ E₆) in
theorem _root_.GlobalTheory.OddFrame.reduces_of_det_evM_eq_zero : ∀ (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ)
    (F : Fin r → ℍ → ℂ) (τ₀ : ℍ), _root_.GlobalTheory.OddFrame.IsReps Γ s → (∀ j, Odd (w j) ∧ _root_.GlobalTheory.OddFrame.IsMF Γ (w j) (F j)) →
    (_root_.GlobalTheory.OddFrame.evM s w F τ₀).det = 0 → _root_.GlobalTheory.OddFrame.Reduces Γ w F := by
  intro Γ r s w F τ₀ hs hF hdet
  classical
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hrow : ∀ i, ∑ j, v j * (F j ∣[w j] s i) τ₀ = 0 := by
    intro i
    have := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, _root_.GlobalTheory.OddFrame.evM, Matrix.of_apply,
      Pi.zero_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hrel : ∀ x : SL(2, ℤ), ∑ j, v j * (F j ∣[w j] x) τ₀ = 0 :=
    fun x => hs.sum_eq_zero hF v τ₀ hrow x
  obtain ⟨n, a, b, E, u, hu, hn, hζ, hab, hba, hE, hzero, hlim, hforms⟩ :=
    _root_.GlobalTheory.LevelOneLocal.exists_local_data τ₀
  set ζ := denom (Matrix.SpecialLinearGroup.toGL
    ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) u)) (τ₀ : ℂ) with hζdef
  have hζ0 : ζ ≠ 0 := denom_ne_zero _ _
  have hpow : ∀ (m : ℕ) (x : SL(2, ℤ)) (j : Fin r),
      (F j ∣[w j] (x * u ^ m)) τ₀ = (F j ∣[w j] x) τ₀ * ζ ^ (-((m : ℤ) * w j)) := by
    intro m
    induction m with
    | zero => intro x j; simp
    | succ m ih =>
      intro x j
      rw [pow_succ, ← mul_assoc, _root_.GlobalTheory.OddFrame.slash_mul_apply, hu, ih, mul_assoc,
        ← zpow_add₀ hζ0]
      congr 2
      push_cast
      ring
  have hrelm : ∀ (m : ℕ) (x : SL(2, ℤ)),
      ∑ j, v j * (F j ∣[w j] x) τ₀ * ζ ^ (-((m : ℤ) * w j)) = 0 := by
    intro m x
    rw [← hrel (x * u ^ m)]
    exact Finset.sum_congr rfl fun j _ => by rw [hpow, mul_assoc]
  obtain ⟨j₁, hj₁⟩ : ∃ j, v j ≠ 0 := by simpa using Function.ne_iff.1 hv0
  have hclass : ∀ x : SL(2, ℤ),
      ∑ j, (if (n : ℤ) ∣ w j - w j₁ then v j else 0) * (F j ∣[w j] x) τ₀ = 0 := by
    intro x
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hsum : ∑ m ∈ Finset.range n, ζ ^ ((m : ℤ) * w j₁) *
        ∑ j, v j * (F j ∣[w j] x) τ₀ * ζ ^ (-((m : ℤ) * w j)) = 0 :=
      Finset.sum_eq_zero fun m _ => by rw [hrelm, mul_zero]
    have hswap : ∑ m ∈ Finset.range n, ζ ^ ((m : ℤ) * w j₁) *
        ∑ j, v j * (F j ∣[w j] x) τ₀ * ζ ^ (-((m : ℤ) * w j)) =
        ∑ j, v j * (F j ∣[w j] x) τ₀ * ∑ m ∈ Finset.range n, (ζ ^ (w j₁ - w j)) ^ m := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => ?_
      rw [← zpow_natCast, ← zpow_mul,
        show (w j₁ - w j) * (m : ℤ) = (m : ℤ) * w j₁ + -((m : ℤ) * w j) by ring, zpow_add₀ hζ0]
      ring
    rw [hswap] at hsum
    simp_rw [sum_range_zpow_primitiveRoot_pow hζ] at hsum
    have hmul : (n : ℂ) * ∑ j, (if (n : ℤ) ∣ w j - w j₁ then v j else 0) *
        (F j ∣[w j] x) τ₀ = 0 := by
      refine Eq.trans ?_ hsum
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hd : (n : ℤ) ∣ w j - w j₁
      · rw [if_pos hd, if_pos (dvd_sub_comm.1 hd)]
        ring
      · have hd' : ¬ (n : ℤ) ∣ w j₁ - w j := fun h' => hd (dvd_sub_comm.1 h')
        simp [hd, hd']
    exact (mul_eq_zero.1 hmul).resolve_left hn0
  set P : Fin r → Prop := fun j => v j ≠ 0 ∧ (n : ℤ) ∣ w j - w j₁ with hP
  have hne : (Finset.univ.filter P).Nonempty :=
    ⟨j₁, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj₁, by simp⟩⟩
  obtain ⟨j₀, hj₀S, hj₀max⟩ := (Finset.univ.filter P).exists_max_image w hne
  have hj₀ : P j₀ := (Finset.mem_filter.1 hj₀S).2
  have hforms' : ∀ j, ∃ f : ℍ → ℂ,
      _root_.GlobalTheory.OddFrame.IsMF ⊤ (w j₀ - w j + a) f ∧ (P j → f τ₀ ≠ 0) := by
    intro j
    by_cases hj : P j
    · obtain ⟨f, hf, hf0⟩ := hforms (w j₀ - w j)
        (sub_nonneg.2 (hj₀max j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)))
        (by have := dvd_sub hj₀.2 hj.2; rwa [sub_sub_sub_cancel_right] at this)
      exact ⟨f, hf, fun _ => hf0⟩
    · exact ⟨0, _root_.GlobalTheory.OddFrame.IsMF.zero _ _, fun h' => absurd h' hj⟩
  choose f hfmf hfne using hforms'
  set e : Fin r → ℍ → ℂ := fun j => (if P j then v j / f j τ₀ else 0) • f j with he_def
  have he_mf : ∀ j, _root_.GlobalTheory.OddFrame.IsMF ⊤ (w j₀ - w j + a) (e j) :=
    fun j => (hfmf j).smul _
  have he0 : ∀ j, e j τ₀ = if (n : ℤ) ∣ w j - w j₁ then v j else 0 := by
    intro j
    simp only [he_def, Pi.smul_apply, smul_eq_mul]
    by_cases hj : P j
    · rw [if_pos hj, if_pos hj.2, div_mul_cancel₀ _ (hfne j hj)]
    · rw [if_neg hj, zero_mul]
      by_cases hd : (n : ℤ) ∣ w j - w j₁
      · rw [if_pos hd]
        exact (not_not.1 fun hv' => hj ⟨hv', hd⟩).symm
      · rw [if_neg hd]
  set H : ℍ → ℂ := ∑ j, e j * F j with hH_def
  have hHmf : _root_.GlobalTheory.OddFrame.IsMF Γ (w j₀ + a) H :=
    _root_.GlobalTheory.OddFrame.IsMF.sum _ fun j _ =>
      ((he_mf j).mono le_top).mul (hF j).2 (by ring)
  have hHslash : ∀ (x : SL(2, ℤ)) (τ : ℍ),
      (H ∣[w j₀ + a] x) τ = ∑ j, e j τ * (F j ∣[w j] x) τ := by
    intro x τ
    rw [ModularForm.SL_slash_apply, hH_def, Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hex := congrFun ((he_mf j).slash_top x) τ
    rw [ModularForm.SL_slash_apply] at hex
    rw [ModularForm.SL_slash_apply, ← hex, Pi.mul_apply, mul_mul_mul_comm,
      ← zpow_add₀ (denom_ne_zero _ _)]
    congr 2
    ring
  have hHz : ∀ γ : SL(2, ℤ), H (γ • τ₀) = 0 := by
    intro γ
    have h1 : (H ∣[w j₀ + a] γ) τ₀ = 0 := by
      rw [hHslash]
      simp_rw [he0]
      exact hclass γ
    rw [ModularForm.SL_slash_apply] at h1
    exact (mul_eq_zero.1 h1).resolve_right (zpow_ne_zero _ (denom_ne_zero _ _))
  obtain ⟨G, hG, hEG⟩ := exists_isMF_mul_eq_of_vanishes_on_orbit hE hzero hlim hHmf hHz
  refine ⟨j₀, w j₀ + a - b, G, E, e, by linarith, ?_, hG, fun j => (he_mf j).2.1, ?_, ?_⟩
  · rw [show w j₀ + a - b = w j₀ - (b - a) by ring]
    exact (hF j₀).1.sub_even hba
  · intro h0
    have := congrFun h0 τ₀
    rw [he0, if_pos hj₀.2, Pi.zero_apply] at this
    exact hj₀.1 this
  · intro x τ
    rw [← hHslash]
    have hEGf : H = E * G := funext fun τ => (hEG τ).symm
    have hm := ModularForm.mul_slash_SL2 b (w j₀ + a - b) x E G
    rw [show b + (w j₀ + a - b) = w j₀ + a by ring, hE.slash_top] at hm
    rw [hEGf, hm]
    rfl

end GlobalTheory.OddFrame
