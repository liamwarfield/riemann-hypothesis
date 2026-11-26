module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.FamExp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.GoodConst

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.SideEstX
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem pw_mul {a b M R b' : ℝ} {d : ℕ} (ha : a ≤ M ^ (d + 1)) (hb0 : 0 ≤ b) (hb : b ≤ b') (h1 : 1 ≤ b')
    (hM : |M| ≤ R) : a * b ≤ (R * b') ^ (d + 1) := by
  have hR : 0 ≤ R := (abs_nonneg _).trans hM
  have h2 : a ≤ R ^ (d + 1) :=
    ha.trans ((le_abs_self _).trans (by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hM _))
  rw [mul_pow]
  exact mul_le_mul h2 (hb.trans (le_self_pow₀ h1 (Nat.succ_ne_zero d))) hb0 (by positivity)

private theorem exp_grow {B c₁ : ℝ} {j m' s₀ : ℕ} (hB0 : 0 ≤ B) (hB : B ≤ Real.exp c₁) (hc : 0 ≤ c₁) (hm : m' ≤ s₀) :
    B ^ (j + m') ≤ Real.exp (c₁ * s₀) * Real.exp (c₁ * j) := by
  refine (pow_le_pow_left₀ hB0 hB _).trans ?_
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have : (m' : ℝ) ≤ s₀ := by exact_mod_cast hm
  push_cast
  nlinarith

private theorem main_est {C₁ cU M₁ C₂ N c₁ η e1 e2 W D : ℝ} {N₀ j k m m' s₀ : ℕ} (hcU : 1 ≤ cU) (hM₁ : 4 ≤ M₁)
    (hη : 0 < η) (hη1 : η ≤ 1) (hk : k ≤ j) (hm : m ≤ s₀) (hm' : m' ≤ s₀) (h10 : 0 ≤ e1) (h1 : e1 ≤ W) (h20 : 0 ≤ e2)
    (h2 : e2 ≤ W / D) (hD : 0 < D) (hc : 0 ≤ c₁) (hA : cU * Real.exp (N₀ * C₂) ≤ Real.exp c₁)
    (hB : cU * (M₁ / 4) * Real.exp (-2 * C₂) ≤ Real.exp (-|N|)) :
    C₁ * cU ^ (j + m') * (Real.exp (N₀ * (C₂ * ((j + m' : ℕ) : ℝ))) * (e1 + (4 / η) ^ (k + m) * e2) +
        (4 / η) ^ (k + m) * Real.exp (-(((2 : ℕ) : ℝ) * (C₂ * ((j + m' : ℕ) : ℝ)))) * e1 +
        (M₁ / η) ^ (k + m) * W * Real.exp (-2 * (C₂ * ((j + m' : ℕ) : ℝ)))) ≤
      (2 * |C₁| * Real.exp (c₁ * s₀) * (M₁ / η) ^ s₀) * W *
        (Real.exp (c₁ * j) * (1 + (4 / η) ^ k / D) + (4 / η) ^ k * Real.exp (-N * j)) := by
  have hW : 0 ≤ W := h10.trans h1
  have hq : 1 ≤ 4 / η := by rw [le_div_iff₀ hη]; linarith
  have hr : 1 ≤ M₁ / 4 := by linarith
  have hrq : M₁ / η = M₁ / 4 * (4 / η) := by field_simp
  rw [hrq]
  generalize 4 / η = q at *
  generalize M₁ / 4 = r at *
  have hrq1 : 1 ≤ r * q := one_le_mul_of_one_le_of_one_le hr hq
  have hR1 : (r * q) ^ m ≤ (r * q) ^ s₀ := pow_le_pow_right₀ hrq1 hm
  have hR2 : q ^ m ≤ (r * q) ^ s₀ := (pow_le_pow_left₀ (by linarith) (by nlinarith) m).trans hR1
  have hR3 : 1 ≤ (r * q) ^ s₀ := one_le_pow₀ hrq1
  have a1 : cU ^ (j + m') * Real.exp (N₀ * (C₂ * ((j + m' : ℕ) : ℝ))) ≤ Real.exp (c₁ * s₀) * Real.exp (c₁ * j) := by
    refine le_trans (le_of_eq ?_) (exp_grow (by positivity) hA hc hm')
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  have a2 : cU ^ (j + m') * r ^ k * Real.exp (-2 * (C₂ * ((j + m' : ℕ) : ℝ))) ≤ Real.exp (-N * j) := by
    have b1 : r ^ k ≤ r ^ (j + m') := pow_le_pow_right₀ hr (by omega)
    have b2 : (cU * r * Real.exp (-2 * C₂)) ^ (j + m') ≤ Real.exp (-|N|) ^ (j + m') :=
      pow_le_pow_left₀ (by positivity) hB _
    have b3 : Real.exp (-|N|) ^ (j + m') ≤ Real.exp (-N * j) := by
      rw [← Real.exp_nat_mul]
      refine Real.exp_le_exp.mpr ?_
      have := le_abs_self N
      have := abs_nonneg N
      have : (0 : ℝ) ≤ j := by positivity
      have : (0 : ℝ) ≤ m' := by positivity
      push_cast
      nlinarith
    refine le_trans ?_ (b2.trans b3)
    rw [mul_pow, mul_pow, ← Real.exp_nat_mul]
    have : ((j + m' : ℕ) : ℝ) * (-2 * C₂) = -2 * (C₂ * ((j + m' : ℕ) : ℝ)) := by ring
    rw [this]
    gcongr
  have hE : 1 ≤ Real.exp (c₁ * s₀) := Real.one_le_exp (by positivity)
  have e : -(((2 : ℕ) : ℝ) * (C₂ * ((j + m' : ℕ) : ℝ))) = -2 * (C₂ * ((j + m' : ℕ) : ℝ)) := by push_cast; ring
  rw [e]
  have p1 := Real.exp_pos (N₀ * (C₂ * ((j + m' : ℕ) : ℝ)))
  have p2 := Real.exp_pos (-2 * (C₂ * ((j + m' : ℕ) : ℝ)))
  have p3 := Real.exp_pos (c₁ * j)
  have p4 := Real.exp_pos (-N * j)
  generalize Real.exp (N₀ * (C₂ * ((j + m' : ℕ) : ℝ))) = x1 at *
  generalize Real.exp (-2 * (C₂ * ((j + m' : ℕ) : ℝ))) = x2 at *
  generalize Real.exp (c₁ * j) = x3 at *
  generalize Real.exp (-N * j) = x4 at *
  generalize Real.exp (c₁ * s₀) = E at *
  have hu : 0 ≤ cU ^ (j + m') := by positivity
  generalize cU ^ (j + m') = u at *
  have hrk : 1 ≤ r ^ k := one_le_pow₀ hr
  have hrqm : 0 ≤ (r * q) ^ m := by positivity
  rw [pow_add q, pow_add (r * q), mul_pow r q k]
  have hqk : 0 ≤ q ^ k := by positivity
  have hqm : 0 ≤ q ^ m := by positivity
  generalize q ^ k = qk at *
  generalize q ^ m = qm at *
  generalize r ^ k = rk at *
  generalize (r * q) ^ m = Rm at *
  generalize (r * q) ^ s₀ = R at *
  have a3 : u * x2 ≤ x4 := le_trans (by nlinarith [mul_nonneg hu p2.le]) a2
  have t1 : u * x1 * (e1 + qk * qm * e2) ≤ E * x3 * (R * W + qk * R * (W / D)) := by
    have : e1 ≤ R * W := h1.trans (le_mul_of_one_le_left hW hR3)
    gcongr
  have t2 : u * x2 * (qk * qm * e1) ≤ x4 * (qk * R * W) := by gcongr
  have t3 : u * rk * x2 * (qk * Rm * W) ≤ x4 * (qk * R * W) := by gcongr
  have t4 : x4 * (qk * R * W) ≤ E * (x4 * (qk * R * W)) := le_mul_of_one_le_left (by positivity) hE
  have t5 : 0 ≤ E * x3 * (R * W + qk * R * (W / D)) := by positivity
  calc _ = C₁ * (u * x1 * (e1 + qk * qm * e2) + u * x2 * (qk * qm * e1) + u * rk * x2 * (qk * Rm * W)) := by ring
    _ ≤ |C₁| * (u * x1 * (e1 + qk * qm * e2) + u * x2 * (qk * qm * e1) + u * rk * x2 * (qk * Rm * W)) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ ≤ |C₁| * (2 * (E * x3 * (R * W + qk * R * (W / D))) + 2 * (E * (x4 * (qk * R * W)))) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    _ = _ := by ring

private theorem tr_bd {E : Type} [Field E] [NumberField E] {μ : Measure (normOneGL (K := E) (n := (2 + 2)))} [μ.IsHaarMeasure] {θ : Twist μ}
    {𝔢 : Side θ 2} (𝔣 : Fam 𝔢) (N : Eu 𝔣.d' ≃ₗᵢ[ℂ] Eu 𝔣.d) (x : ℝ) :
    ∃ Ct : ℝ, 0 ≤ Ct ∧ ∀ j, ‖𝔣.tr N x j‖ ≤ Ct * (‖𝔣.u 0 0‖ + 1) ^ j := by
  let Ψ : (Eu 𝔣.d' →L[ℂ] Eu 𝔣.d') →ₗ[ℂ] ℂ :=
    { toFun := fun a => LinearMap.trace ℂ (Eu 𝔣.d) ((N.toLinearEquiv : Eu 𝔣.d' →ₗ[ℂ] Eu 𝔣.d) ∘ₗ
        ((eigP 𝔣.a₀ x ∘L a ∘L symb 𝔣.βg 0 : Eu 𝔣.d' →L[ℂ] Eu 𝔣.d') : Eu 𝔣.d' →ₗ[ℂ] Eu 𝔣.d') ∘ₗ
        (𝔣.s.toLinearEquiv : Eu 𝔣.d →ₗ[ℂ] Eu 𝔣.d'))
      map_add' := fun a b => by
        rw [← map_add (f := _)]; congr 1; ext v; simp
      map_smul' := fun c a => by
        rw [RingHom.id_apply, ← map_smul]; congr 1; ext v; simp }
  refine ⟨‖LinearMap.toContinuousLinearMap Ψ‖, norm_nonneg _, fun j => ?_⟩
  refine ((LinearMap.toContinuousLinearMap Ψ).le_opNorm (𝔣.u 0 0 ^ j)).trans
    (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  induction j with
  | zero => rw [pow_zero, pow_zero]; exact ContinuousLinearMap.norm_id_le
  | succ j ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul ih (by linarith) (norm_nonneg _) (by positivity))

set_option maxHeartbeats 6000000 in
theorem sideEstX :
    OneSideX → Ci.EvVal → Ci.TruncSpec → ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
      (μ : Measure (normOneGL (K := K) (n := (2 + 2)))) [μ.IsHaarMeasure] (θ : Twist μ) (𝔰 : Side θ 2) (𝔵 : Fam 𝔰)
      (ev : PR K (2 + 2) →+* (LL μ →L[ℂ] LL μ)) (evz : ℂ → PR K (2 + 2) →+* (Eu 𝔵.d' →L[ℂ] Eu 𝔵.d'))
      (Nn : Eu 𝔵.d' ≃ₗᵢ[ℂ] Eu 𝔵.d) (Cf : ℝ), 𝔰.toAmp.IsEv ev → (∀ P, Inner μ (ev P)) → 𝔵.IsEvz ev evz →
      Family μ 𝔵.A 𝔵.A' 0 𝔵.P Nn Cf → ∀ sp : Finset ℝ,
      (∀ x, x ∈ sp ↔ 0 < x ∧ Module.End.eigenspace (𝔵.a₀ : Eu 𝔵.d' →ₗ[ℂ] Eu 𝔵.d') (x : ℂ) ≠ ⊥) →
      ∀ C₀ N : ℝ, ∃ c₁ : ℝ, ∀ η : ℝ, 0 < η → η ≤ 1 →
      ∀ χ : ℝ → ℝ, Continuous χ → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) → (∀ x ≥ η, χ x = 1) →
      ∃ s : Finset (ℝ × Submodule ℂ (LL μ)),
        (∀ y, y ∈ s ↔ η < y.1 ∧ IsSummand μ y.2 ∧ y.2.map (θ.U : LL μ →ₗ[ℂ] LL μ) = y.2 ∧ eigIn y.2 𝔰.toAmp.A y.1 ≠ ⊥) ∧
        (∀ y ∈ s, FiniteDimensional ℂ (eigIn y.2 𝔰.toAmp.A y.1)) ∧
        ∀ Φ G, UpperTheory.ConvolutionTheory.admitted 𝔰.S Φ → IsGen Φ G →
          (∃ C : ℝ, ∀ d : ℕ, ‖ev (trunc d G) ∘L fcalc χ 𝔰.toAmp.A ∘L (1 - Pc μ - 𝔵.P)‖ ≤ C ^ (d + 1) / d.factorial) →
          ∀ P : PR K (2 + 2), (∀ y ∈ P.vars, y.1 ∉ 𝔰.S) → ∃ (u : ℝ × Submodule ℂ (LL μ) → ℕ → ℂ) (w : ℝ → ℕ → ℂ),
            (∀ y ∈ s, ∀ (L : Ix K (2 + 2) → ℂ) t, At μ 𝔰.S y.2 (msOf L) t →
              Tendsto (u y) atTop (𝓝 (y.1 * val y.1 (msOf L) t P * evK L (hval t) Φ))) ∧
            (∀ (x : ℝ) (L : Ix K (2 + 2) → ℂ), msOf L = 𝔵.Λ → Tendsto (w x) atTop (𝓝 (x * val x 𝔵.Λ 𝔵.t P * evK L (hval 𝔵.t) Φ))) ∧
            ∀ p : ℕ, 0 < p → ∀ s₀ : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ j : ℕ in atTop, ∀ d : ℕ, ∀ m ≤ s₀, ∀ m' ≤ s₀, ∀ f : TG K (2 + 2),
              𝔰.Rep (ev (chebP η (j / p + m) * (trunc d G * P))) (j + m') (Real.exp (C₀ * ((j + m' : ℕ) : ℝ))) f →
              ‖twInt θ f - ∑ y ∈ s, u y d * (y.1 : ℂ) ^ d * (cheb η (j / p + m) y.1 : ℂ) *
                  trOn (eigIn y.2 𝔰.toAmp.A y.1) ((𝔰.Uq 0 ^ (j + m')) ∘L Rop μ 𝔰.g ∘L θ.U) -
                ∑ x ∈ sp.filter (η < ·), w x d * (x : ℂ) ^ d * (cheb η (j / p + m) x : ℂ) * ((1 / 2 : ℂ) * 𝔵.tr Nn x (j + m'))‖ ≤
                M ^ (d + 1) * (Real.exp (c₁ * j) * (1 + (4 / η) ^ (j / p) / d.factorial) + (4 / η) ^ (j / p) * Real.exp (-N * j)) := by
  intro h1 hV hT K _ _ _ μ _ θ 𝔰 𝔵 ev evz Nn Cf hev hin hz hF sp hsp C₀ N
  classical
  obtain ⟨c, cU, M₁, N₀, hc, hcU, hM₁, H⟩ := h1 K μ θ 𝔰 𝔵 ev evz Nn Cf hev hin hz hF sp hsp
  obtain ⟨C₂, hC1, hC2, hC3⟩ : ∃ C₂ : ℝ, 1 ≤ C₂ ∧ C₀ ≤ c * C₂ ∧
      cU * (M₁ / 4) * Real.exp (-2 * C₂) ≤ Real.exp (-|N|) := by
    have hpos : 0 < cU * (M₁ / 4) := by positivity
    have q1 : 0 ≤ |C₀| / c := by positivity
    have q2 := abs_nonneg N
    refine ⟨1 + |C₀| / c + |N| + cU * (M₁ / 4), by linarith, ?_, ?_⟩
    · have : c * (|C₀| / c) = |C₀| := by field_simp
      have := le_abs_self C₀
      nlinarith
    · have q3 : cU * (M₁ / 4) ≤ Real.exp (cU * (M₁ / 4)) := by linarith [Real.add_one_le_exp (cU * (M₁ / 4))]
      refine (mul_le_mul_of_nonneg_right q3 (Real.exp_pos _).le).trans ?_
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
  obtain ⟨c₁, hc0, hcA, hcB⟩ : ∃ c₁ : ℝ, 0 ≤ c₁ ∧ cU * Real.exp (N₀ * C₂) ≤ Real.exp c₁ ∧
      ‖𝔵.u 0 0‖ + 1 ≤ Real.exp c₁ := by
    have q1 : 0 ≤ cU * Real.exp (N₀ * C₂) := by positivity
    have q2 := norm_nonneg (𝔵.u 0 0)
    have q3 := Real.add_one_le_exp (cU * Real.exp (N₀ * C₂) + ‖𝔵.u 0 0‖)
    exact ⟨cU * Real.exp (N₀ * C₂) + ‖𝔵.u 0 0‖, by linarith, by linarith, by linarith⟩
  refine ⟨c₁, fun η hη hη1 χ hχ hχ1 hχ2 => ?_⟩
  obtain ⟨s, hs, hfin, H⟩ := H η hη hη1 χ hχ hχ1 hχ2
  obtain ⟨C₁, T₁, H⟩ := H 2
  refine ⟨s, hs, hfin, fun Φ G hΦ hG hC P hP => ?_⟩
  obtain ⟨Ck, hC⟩ := hC
  obtain ⟨⟨κ, D, hκ, hBd⟩, hval', hnorm⟩ := (hT K (2 + 2) 𝔰.S Φ hΦ).2 G hG
  obtain ⟨Me, hMe⟩ := hnorm (LL μ) ev hev.const
  have hSB : ∀ R : PR K (2 + 2), (∀ y ∈ R.vars, y.1 ∉ 𝔰.S) → ∃ M, SB (fun z => evz z R) M := fun R hR =>
    ((actLaws 𝔵.A'.J).2.2.1 _ _ (hz.act R hR)).1
  obtain ⟨Mt, hMt⟩ := truncSB evz hz.const 𝔰.S hSB Φ G hΦ hG
  obtain ⟨KP, hKP⟩ := hSB P hP
  have htv : ∀ d, ∀ y ∈ (trunc d G).vars, y.1 ∉ 𝔰.S := fun d y hy => hκ _ ((hBd d).1 y hy)
  have hQv : ∀ d, ∀ y ∈ (trunc d G * P).vars, y.1 ∉ 𝔰.S := fun d y hy => by
    rcases Finset.mem_union.mp (vars_mul _ _ hy) with h | h
    · exact htv d y h
    · exact hP y h
  have hV' := fun y (hy : y ∈ s) =>
    hV K (2 + 2) (by norm_num) μ 𝔰.toAmp y.2 y.1 (hη.trans ((hs y).1 hy).1) ((hs y).1 hy).2.1
  have hex : ∀ y : ℝ × Submodule ℂ (LL μ), ∃ Λ t, y ∈ s → At μ 𝔰.S y.2 Λ t := fun y => by
    by_cases hy : y ∈ s
    · obtain ⟨Λ, t, h⟩ := (hV' y hy).1 ((hs y).1 hy).2.2.2
      exact ⟨Λ, t, fun _ => h⟩
    · exact ⟨fun _ => 0, fun _ => 0, fun h => absurd h hy⟩
  choose Λ t hΛ using hex
  have huniq : ∀ y ∈ s, ∀ Λ' t', At μ 𝔰.S y.2 Λ' t' → ∀ R : PR K (2 + 2), (∀ y ∈ R.vars, y.1 ∉ 𝔰.S) →
      val y.1 (Λ y) (t y) R = val y.1 Λ' t' R := fun y hy Λ' t' h R hR => by
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ((hs y).1 hy).2.2.2
    have e1 := (hV' y hy).2.2 ev hev _ _ (hΛ y hy) R hR v hv
    have e2 := (hV' y hy).2.2 ev hev _ _ h R hR v hv
    exact smul_left_injective ℂ hv0 (e1.symm.trans e2)
  refine ⟨fun y d => y.1 * val y.1 (Λ y) (t y) P * (val y.1 (Λ y) (t y) (trunc d G) / (y.1 : ℂ) ^ d),
    fun x d => x * val x 𝔵.Λ 𝔵.t P * (val x 𝔵.Λ 𝔵.t (trunc d G) / (x : ℂ) ^ d), ?_, ?_, ?_⟩
  · intro y hy L t' h
    obtain ⟨u, hu, hu'⟩ := hval' L t'
    have hy0 : (y.1 : ℂ) ≠ 0 := by exact_mod_cast (hη.trans ((hs y).1 hy).1).ne'
    refine (hu.const_mul _).congr fun d => ?_
    beta_reduce
    rw [huniq y hy _ _ h P hP, huniq y hy _ _ h _ (htv d), hu', mul_div_cancel_left₀ _ (pow_ne_zero d hy0)]
  · intro x L hL
    obtain ⟨u, hu, hu'⟩ := hval' L 𝔵.t
    rw [hL] at hu'
    refine (hu.const_mul _).congr fun d => ?_
    beta_reduce
    by_cases hx : (x : ℂ) = 0
    · simp [hx]
    · rw [hu', mul_div_cancel_left₀ _ (pow_ne_zero d hx)]
  intro p hp s₀
  choose Ct hCt0 hCt using fun x => tr_bd 𝔵 Nn x
  obtain ⟨M₀, hM₀0, hM₀⟩ : ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ {a b M : ℝ} {d : ℕ}, a ≤ M ^ (d + 1) → 0 ≤ b → b ≤ ‖ev P‖ + |KP| + 1 →
      |M| ≤ |Me| + |Ck| + |Mt| + 1 → a * b ≤ M₀ ^ (d + 1) :=
    ⟨(|Me| + |Ck| + |Mt| + 1) * (‖ev P‖ + |KP| + 1), by positivity, fun ha hb hb' hM =>
      pw_mul ha hb hb' (by linarith [norm_nonneg (ev P), abs_nonneg KP]) hM⟩
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ, K₁ = 2 * |C₁| * Real.exp (c₁ * s₀) * (M₁ / η) ^ s₀ := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : ℝ, K₂ = (∑ x ∈ sp, Ct x) * Real.exp (c₁ * s₀) := ⟨_, rfl⟩
  have hK₁0 : 0 ≤ K₁ := by
    have : 0 ≤ M₁ := by linarith
    rw [hK₁]; positivity
  have hS0 : 0 ≤ ∑ x ∈ sp, Ct x := Finset.sum_nonneg fun x _ => hCt0 x
  have hK₂0 : 0 ≤ K₂ := by rw [hK₂]; positivity
  refine ⟨(K₁ + K₂ + 1) * M₀, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop ⌈T₁⌉₊] with j hj d m hm m' hm' f hf
  have n1 := abs_nonneg Me
  have n2 := abs_nonneg Ck
  have n3 := abs_nonneg Mt
  have n4 := abs_nonneg KP
  have n5 := norm_nonneg (ev P)
  have hW0 : 0 ≤ M₀ ^ (d + 1) := by positivity
  have hfac : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
  have b1 : ‖ev (trunc d G * P)‖ ≤ M₀ ^ (d + 1) := by
    rw [map_mul]
    exact (norm_mul_le _ _).trans (hM₀ (hMe d) n5 (by linarith) (by linarith))
  have b2 : ‖ev (trunc d G * P) ∘L fcalc χ 𝔰.toAmp.A ∘L (1 - Pc μ - 𝔵.P)‖ ≤ M₀ ^ (d + 1) / d.factorial := by
    rw [mul_comm, map_mul, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc, le_div_iff₀ hfac]
    have := (le_div_iff₀ hfac).mp (hC d)
    refine le_trans ?_ (hM₀ this n5 (by linarith) (by linarith))
    rw [mul_right_comm, mul_comm _ ‖ev P‖]
    exact mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) hfac.le
  have b3 : SB (fun z => evz z (trunc d G * P)) (M₀ ^ (d + 1)) := fun z hz' => by
    simp only [map_mul]
    exact (norm_mul_le _ _).trans (hM₀ (hMt d z hz') (norm_nonneg _)
      ((hKP z hz').trans (by linarith [le_abs_self KP])) (by linarith))
  have hj0 : (0 : ℝ) ≤ ((j + m' : ℕ) : ℝ) := by positivity
  have hT₁ : T₁ ≤ C₂ * ((j + m' : ℕ) : ℝ) := by
    have q1 : T₁ ≤ ((j + m' : ℕ) : ℝ) := (Nat.le_ceil T₁).trans (by exact_mod_cast hj.trans (Nat.le_add_right _ _))
    nlinarith
  have hf' : 𝔰.Rep (ev (chebP η (j / p + m) * (trunc d G * P))) (j + m') (Real.exp (c * (C₂ * ((j + m' : ℕ) : ℝ)))) f :=
    ⟨hf.1, fun x hx => hf.2 x (lt_of_le_of_lt (Real.exp_le_exp.mpr (by nlinarith)) hx)⟩
  have E1 := (H (trunc d G * P) (fun y => val y.1 (Λ y) (t y) (trunc d G * P)) _ (hQv d) b3
    (fun y hy v hv => (hV' y hy).2.2 ev hev _ _ (hΛ y hy) _ (hQv d) v hv) (j / p + m) (j + m') _ f hT₁ hf').trans
    (main_est hcU hM₁ hη hη1 (Nat.div_le_self j p) hm hm' (norm_nonneg _) b1 (norm_nonneg _) b2 hfac hc0 hcA hC3)
  have E2 : ‖(1 / 2 : ℂ) * ∑ x ∈ sp.filter (fun x => ¬ η < x), (cheb η (j / p + m) x : ℂ) *
      (x * val x 𝔵.Λ 𝔵.t (trunc d G * P) * 𝔵.tr Nn x (j + m'))‖ ≤ K₂ * M₀ ^ (d + 1) * Real.exp (c₁ * j) := by
    have g1 : ∀ x ∈ sp.filter (fun x => ¬ η < x), ‖(cheb η (j / p + m) x : ℂ) *
        (x * val x 𝔵.Λ 𝔵.t (trunc d G * P) * 𝔵.tr Nn x (j + m'))‖ ≤
        Ct x * (M₀ ^ (d + 1) * (Real.exp (c₁ * s₀) * Real.exp (c₁ * j))) := by
      intro x hx
      obtain ⟨hx, hxη⟩ := Finset.mem_filter.mp hx
      obtain ⟨hx0, hx⟩ := (hsp x).1 hx
      have hxη : x ≤ η := not_lt.mp hxη
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hx
      have r1 : ‖(cheb η (j / p + m) x : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real]; exact (UpperTheory.ConvolutionTheory.FX.cheb_bound η _ hη hη1).1 x ⟨hx0.le, hxη⟩
      have r2 : ‖(x : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_of_nonneg hx0.le]; linarith
      have r3 : ‖val x 𝔵.Λ 𝔵.t (trunc d G * P)‖ ≤ M₀ ^ (d + 1) := by
        have q1 := (evz 0 (trunc d G * P)).le_of_opNorm_le (b3 0 (by simp)) v
        rw [hz.zero _ (hQv d) x hx0 v hv, norm_smul] at q1
        exact le_of_mul_le_mul_right q1 (norm_pos_iff.mpr hv0)
      have r4 : ‖𝔵.tr Nn x (j + m')‖ ≤ Ct x * (Real.exp (c₁ * s₀) * Real.exp (c₁ * j)) :=
        (hCt x _).trans (mul_le_mul_of_nonneg_left (exp_grow (by positivity) hcB hc0 hm') (hCt0 x))
      have := hCt0 x
      rw [norm_mul, norm_mul, norm_mul]
      calc _ ≤ 1 * (1 * M₀ ^ (d + 1) * (Ct x * (Real.exp (c₁ * s₀) * Real.exp (c₁ * j)))) := by gcongr
        _ = _ := by ring
    have g2 := (norm_sum_le _ _).trans (Finset.sum_le_sum g1)
    rw [← Finset.sum_mul] at g2
    have g3 : ∑ x ∈ sp.filter (fun x => ¬ η < x), Ct x ≤ ∑ x ∈ sp, Ct x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun x _ _ => hCt0 x
    rw [norm_mul]
    have g4 : ‖(1 / 2 : ℂ)‖ ≤ 1 := by norm_num
    calc _ ≤ 1 * ((∑ x ∈ sp, Ct x) * (M₀ ^ (d + 1) * (Real.exp (c₁ * s₀) * Real.exp (c₁ * j)))) :=
          mul_le_mul g4 (g2.trans (by gcongr)) (norm_nonneg _) zero_le_one
      _ = _ := by rw [hK₂]; ring
  have s1 : ∑ y ∈ s, y.1 * val y.1 (Λ y) (t y) P * (val y.1 (Λ y) (t y) (trunc d G) / (y.1 : ℂ) ^ d) * (y.1 : ℂ) ^ d *
        (cheb η (j / p + m) y.1 : ℂ) * trOn (eigIn y.2 𝔰.toAmp.A y.1) ((𝔰.Uq 0 ^ (j + m')) ∘L Rop μ 𝔰.g ∘L θ.U) =
      ∑ y ∈ s, (cheb η (j / p + m) y.1 : ℂ) * (y.1 * val y.1 (Λ y) (t y) (trunc d G * P) *
        trOn (eigIn y.2 𝔰.toAmp.A y.1) ((𝔰.Uq 0 ^ (j + m')) ∘L Rop μ 𝔰.g ∘L θ.U)) := by
    refine Finset.sum_congr rfl fun y hy => ?_
    have hy0 : (y.1 : ℂ) ≠ 0 := by exact_mod_cast (hη.trans ((hs y).1 hy).1).ne'
    rw [map_mul]
    field_simp
  have s2 : ∑ x ∈ sp.filter (η < ·), x * val x 𝔵.Λ 𝔵.t P * (val x 𝔵.Λ 𝔵.t (trunc d G) / (x : ℂ) ^ d) * (x : ℂ) ^ d *
        (cheb η (j / p + m) x : ℂ) * ((1 / 2 : ℂ) * 𝔵.tr Nn x (j + m')) =
      (1 / 2 : ℂ) * ∑ x ∈ sp.filter (η < ·), (cheb η (j / p + m) x : ℂ) *
        (x * val x 𝔵.Λ 𝔵.t (trunc d G * P) * 𝔵.tr Nn x (j + m')) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (hη.trans (Finset.mem_filter.mp hx).2).ne'
    rw [map_mul]
    field_simp
  rw [← Finset.sum_filter_add_sum_filter_not sp (η < ·), mul_add, ← sub_sub, ← hK₁] at E1
  beta_reduce
  rw [s1, s2]
  have hq : 0 ≤ (4 / η) ^ (j / p) := by positivity
  have x3 := Real.exp_pos (c₁ * j)
  have x4 := Real.exp_pos (-N * j)
  have F0 : Real.exp (c₁ * j) ≤
      Real.exp (c₁ * j) * (1 + (4 / η) ^ (j / p) / d.factorial) + (4 / η) ^ (j / p) * Real.exp (-N * j) := by
    have : 0 ≤ Real.exp (c₁ * j) * ((4 / η) ^ (j / p) / d.factorial) := by positivity
    have : 0 ≤ (4 / η) ^ (j / p) * Real.exp (-N * j) := by positivity
    linarith
  have F1 := x3.le.trans F0
  refine (norm_le_norm_sub_add _ _).trans ((add_le_add E1 (E2.trans (mul_le_mul_of_nonneg_left F0 (by positivity)))).trans ?_)
  rw [← add_mul, ← add_mul, mul_pow]
  have F2 : K₁ + K₂ ≤ (K₁ + K₂ + 1) ^ (d + 1) := le_trans (by linarith) (le_self_pow₀ (by linarith) (Nat.succ_ne_zero d))
  gcongr

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.Regroup
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

open Classical in
private lemma regroup {T : Type} (s : Finset T) (a : T → ℝ) (S : T → Finset ℂ) (c : T → ℂ → ℂ) (w : T → ℂ) (P : Finset (ℝ × ℂ))
    (hP : ∀ i ∈ s, ∀ ζ ∈ S i, (a i, ζ) ∈ P) (f : ℝ × ℂ → ℂ) :
    ∑ q ∈ P, (∑ i ∈ s, if a i = q.1 ∧ q.2 ∈ S i then w i * c i q.2 else 0) * f q =
      ∑ i ∈ s, w i * ∑ ζ ∈ S i, c i ζ * f (a i, ζ) := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mul_sum]
  symm
  have hinj : Set.InjOn (fun ζ : ℂ => (a i, ζ)) (S i) := fun z _ z' _ h => (Prod.ext_iff.1 h).2
  calc ∑ ζ ∈ S i, w i * (c i ζ * f (a i, ζ))
      = ∑ q ∈ (S i).image (fun ζ : ℂ => (a i, ζ)), (if a i = q.1 ∧ q.2 ∈ S i then w i * c i q.2 else 0) * f q := by
        rw [Finset.sum_image hinj]
        refine Finset.sum_congr rfl fun ζ hζ => ?_
        rw [if_pos ⟨rfl, hζ⟩, mul_assoc]
    _ = _ := by
        refine Finset.sum_subset ?_ ?_
        · intro q hq
          obtain ⟨ζ, hζ, rfl⟩ := Finset.mem_image.1 hq
          exact hP i hi ζ hζ
        · intro q _ hq
          rw [if_neg, zero_mul]
          rintro ⟨h1, h2⟩
          exact hq (Finset.mem_image.2 ⟨q.2, h2, Prod.ext h1 rfl⟩)

private lemma d_top (d : ℕ → ℕ) (h : ∀ B : ℝ, ∀ᶠ j : ℕ in atTop, Real.exp (B * j) ≤ (d j).factorial) :
    Tendsto d atTop atTop := by
  refine tendsto_atTop.2 fun M => ?_
  filter_upwards [h 1, eventually_ge_atTop M.factorial] with j hj hM
  by_contra hlt
  have h1 : (d j).factorial ≤ M.factorial := Nat.factorial_le (not_le.1 hlt).le
  have h2 : ((d j).factorial : ℝ) ≤ j := by exact_mod_cast h1.trans hM
  have h3 := Real.add_one_le_exp (1 * (j : ℝ))
  linarith

private lemma low_bd (Z : Finset ℂ) (hZ : ∀ ζ ∈ Z, ζ ≠ 0) : ∃ cq : ℝ, ∀ ζ ∈ Z, Real.exp (-cq) ≤ ‖ζ‖ := by
  obtain ⟨M, hM⟩ := (Z.image fun ζ => -Real.log ‖ζ‖).bddAbove
  refine ⟨M, fun ζ hζ => ?_⟩
  have h1 : -Real.log ‖ζ‖ ≤ M := hM (by simpa using ⟨ζ, hζ, rfl⟩)
  calc Real.exp (-M) ≤ Real.exp (Real.log ‖ζ‖) := Real.exp_le_exp.2 (by linarith)
    _ = ‖ζ‖ := Real.exp_log (norm_pos_iff.2 (hZ ζ hζ))

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.absX :
    ∀ (T : Type) (a : T → ℝ) (τ : T → ℕ → ℂ) (act good : T → Prop) (x : ℝ), 0 < x → x ≤ 1 → ∀ (p : ℕ), 0 < p → ∀ (d : ℕ → ℕ),
      Tendsto (fun j : ℕ => (d j : ℝ) / j) atTop (𝓝 0) → (∀ B : ℝ, ∀ᶠ j : ℕ in atTop, Real.exp (B * j) ≤ (d j).factorial) →
      (∀ i, act i → 0 < a i → ∃ (s : Finset ℂ) (c : ℂ → ℂ), 0 ∉ s ∧ ∀ᶠ j : ℕ in atTop, τ i j = ∑ ζ ∈ s, c ζ * ζ ^ j) →
      {i | act i ∧ a i = x}.Finite →
      (∀ N : ℝ, ∃ c₁ : ℝ, ∀ η : ℝ, 0 < η → η < x → ∃ (s : Finset T) (u : T → ℕ → ℂ) (u' : T → ℂ) (k : ℂ), k ≠ 0 ∧ (∀ i, i ∈ s ↔ η < a i ∧ act i) ∧
        (∀ i ∈ s, Tendsto (u i) atTop (𝓝 (u' i))) ∧ (∀ i ∈ s, good i → a i = x → u' i = k) ∧ (∀ i ∈ s, ¬ good i → u' i = 0) ∧
        ∀ s₀ : ℕ, ∃ K : ℝ, ∀ᶠ j : ℕ in atTop, ∀ m ≤ s₀, ∀ m' ≤ s₀,
          ‖∑ i ∈ s, u i (d j) * (a i : ℂ) ^ d j * (cheb η (j / p + m) (a i) : ℂ) * τ i (j + m')‖ ≤
            K ^ (d j + 1) * (Real.exp (c₁ * j) * (1 + (4 / η) ^ (j / p) / (d j).factorial) + (4 / η) ^ (j / p) * Real.exp (-N * j))) →
      ∀ᶠ j : ℕ in atTop, ∑ᶠ i ∈ {i | act i ∧ good i ∧ a i = x}, τ i j = 0 := by
  classical
  intro T a τ act good x hx hx1 p hp d hd hfac hexp hfin H
  choose! S c hS0 hτ using hexp
  obtain ⟨cq, hcq⟩ := low_bd (hfin.toFinset.biUnion S) (by
    intro ζ hζ h0
    obtain ⟨i, hi, hζ⟩ := Finset.mem_biUnion.1 hζ
    have hi' := hfin.mem_toFinset.1 hi
    exact hS0 i hi'.1 (hi'.2 ▸ hx) (h0 ▸ hζ))
  obtain ⟨N, hN⟩ := exponents3 d hd hfac p hp cq x hx hx1
  obtain ⟨c₁, H⟩ := H N
  obtain ⟨η, hη, hηx, hE⟩ := hN c₁
  obtain ⟨s, u, u', k, hk, hs, hu, hgood, hbad, hest⟩ := H η hη hηx
  have hsp : ∀ i ∈ s, act i ∧ 0 < a i := fun i hi => ⟨((hs i).1 hi).2, hη.trans ((hs i).1 hi).1⟩
  set P : Finset (ℝ × ℂ) := s.biUnion fun i => (S i).image fun ζ => (a i, ζ) with hPdef
  have hP : ∀ i ∈ s, ∀ ζ ∈ S i, (a i, ζ) ∈ P := fun i hi ζ hζ =>
    Finset.mem_biUnion.2 ⟨i, hi, Finset.mem_image.2 ⟨ζ, hζ, rfl⟩⟩
  have hP' : ∀ q ∈ P, ∃ i ∈ s, a i = q.1 ∧ q.2 ∈ S i := by
    intro q hq
    obtain ⟨i, hi, hq⟩ := Finset.mem_biUnion.1 hq
    obtain ⟨ζ, hζ, rfl⟩ := Finset.mem_image.1 hq
    exact ⟨i, hi, rfl, hζ⟩
  have hall : ∀ᶠ j : ℕ in atTop, ∀ i ∈ s, τ i j = ∑ ζ ∈ S i, c i ζ * ζ ^ j :=
    (Filter.eventually_all_finset s).2 fun i hi => hτ i (hsp i hi).1 (hsp i hi).2
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hall
  let C : (T → ℂ) → ℝ × ℂ → ℂ := fun w q => ∑ i ∈ s, if a i = q.1 ∧ q.2 ∈ S i then w i * c i q.2 else 0
  have key := hE η hη le_rfl P (fun q => q.1.1) (fun q => q.1.2)
    (fun q => by
      obtain ⟨i, hi, h1, -⟩ := hP' q.1 q.2
      exact h1 ▸ ((hs i).1 hi).1)
    (fun q h0 => by
      obtain ⟨i, hi, -, h2⟩ := hP' q.1 q.2
      exact hS0 i (hsp i hi).1 (hsp i hi).2 (h0 ▸ h2))
    (fun q q' h => Subtype.ext h)
    (fun j q => C (fun i => u i (d j)) q.1) (fun q => C u' q.1)
    (fun q => by
      refine tendsto_finsetSum _ fun i hi => ?_
      split_ifs
      · exact ((hu i hi).comp (d_top d hfac)).mul_const _
      · exact tendsto_const_nhds)
    (fun s₀ => by
      obtain ⟨K, hK⟩ := hest s₀
      refine ⟨K, ?_⟩
      filter_upwards [hK, eventually_ge_atTop J] with j hj hjJ m hm m' hm'
      refine le_of_eq_of_le ?_ (hj m hm m' hm')
      congr 1
      have h1 := regroup s a S c (fun i => u i (d j)) P hP
        (fun q => (q.1 : ℂ) ^ d j * (cheb η (j / p + m) q.1 : ℂ) * q.2 ^ (j + m'))
      rw [← Finset.sum_coe_sort P] at h1
      refine Eq.trans (Finset.sum_congr rfl fun q _ => by simp only [C, mul_assoc]) (h1.trans ?_)
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hJ (j + m') (by omega) i hi, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ζ _ => ?_
      ring)
  filter_upwards [hall] with j hj
  have h1 := regroup s a S c u' P hP (fun q => if q.1 = x then q.2 ^ j else 0)
  have h2 : ∑ q ∈ P, C u' q * (if q.1 = x then q.2 ^ j else 0) = 0 := by
    refine Finset.sum_eq_zero fun q hq => ?_
    split_ifs with hqx
    · obtain ⟨i, hi, h1, h2⟩ := hP' q hq
      have := key ⟨q, hq⟩ hqx.ge (hcq _ (Finset.mem_biUnion.2
        ⟨i, hfin.mem_toFinset.2 ⟨(hsp i hi).1, h1.trans hqx⟩, h2⟩))
      rw [this, zero_mul]
    · exact mul_zero _
  have h3 : k * ∑ i ∈ s.filter (fun i => good i ∧ a i = x), τ i j = 0 := by
    rw [← h2]
    refine Eq.trans ?_ h1.symm
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i hi => ?_
    by_cases hg : good i
    · by_cases ha : a i = x
      · simp only [hg, ha, and_self, if_true, hgood i hi hg ha, hj i hi]
      · simp [ha]
    · simp [hg, hbad i hi hg]
  have h4 : {i | act i ∧ good i ∧ a i = x} = ↑(s.filter (fun i => good i ∧ a i = x)) := by
    ext i
    simp only [Set.mem_setOf_eq, Finset.coe_filter]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨(hs i).2 ⟨h3 ▸ hηx, h1⟩, h2, h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(hsp i h1).1, h2⟩
  show ∑ᶠ i ∈ {i | act i ∧ good i ∧ a i = x}, τ i j = 0
  rw [h4, finsum_mem_coe_finset]
  exact (mul_eq_zero.1 h3).resolve_left hk
end

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem chi_ex (η : ℝ) (hη : 0 < η) : ∃ χ : ℝ → ℝ, Continuous χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ (∀ x ≥ η, χ x = 1) ∧
    (∀ x ≤ η / 2, χ x = 0) ∧ ∀ x, |χ x| ≤ 1 := by
  have h01 : ∀ x : ℝ, 0 ≤ max 0 (min 1 (2 * x / η - 1)) ∧ max 0 (min 1 (2 * x / η - 1)) ≤ 1 :=
    fun x => ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  refine ⟨fun x => max 0 (min 1 (2 * x / η - 1)), by fun_prop, h01, ?_, ?_, ?_⟩
  · intro x hx
    have : 2 ≤ 2 * x / η := by rw [le_div_iff₀ hη]; linarith
    show max 0 (min 1 (2 * x / η - 1)) = 1
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  · intro x hx
    have : 2 * x / η ≤ 1 := by rw [div_le_iff₀ hη]; linarith
    exact max_eq_left ((min_le_right _ _).trans (by linarith))
  · intro x
    rw [abs_of_nonneg (h01 x).1]; exact (h01 x).2

private theorem trOn_bot {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) :
    trOn (⊥ : Submodule ℂ H) T = 0 := by
  have : prj (⊥ : Submodule ℂ H) = 0 := by
    ext v
    have h := Submodule.starProjection_apply_mem (⊥ : Submodule ℂ H).topologicalClosure v
    have h0 : (⊥ : Submodule ℂ H).topologicalClosure = ⊥ := IsClosed.submodule_topologicalClosure_eq (by simp)
    exact (Submodule.mem_bot ℂ).mp (h0.le h)
  simp [trOn, this, trace]

private theorem eig_bot {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (V : Submodule ℂ H)
    (A : H →L[ℂ] H) (hA : ‖A‖ ≤ 1) (x : ℝ) (hx : 1 < x) : eigIn V A x = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  have h1 : A v = (x : ℂ) • v := Module.End.mem_eigenspace_iff.mp hv.2
  have h2 : ‖A v‖ ≤ 1 * ‖v‖ := (A.le_opNorm v).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  rw [h1, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at h2
  have : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
  simpa using this

private theorem deg_ev (d : ℕ → ℕ) (hd : Tendsto (fun j : ℕ => (d j : ℝ) / j) atTop (𝓝 0)) (p : ℕ) (hp : 0 < p) (A : ℕ) :
    ∀ᶠ j : ℕ in atTop, ∀ m' : ℕ, j / (2 * p) + (d j + A) ≤ (j + m') / p := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  filter_upwards [hd.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (4 * p) by positivity)), eventually_ge_atTop (4 * p * A),
    eventually_gt_atTop 0] with j h1 h2 h3 m'
  have hj : (0 : ℝ) < j := by exact_mod_cast h3
  rw [div_lt_div_iff₀ hj (by positivity)] at h1
  have h4 : d j * (4 * p) < j := by
    have : ((d j * (4 * p) : ℕ) : ℝ) < (j : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have h5 := Nat.div_mul_le_self j (2 * p)
  rw [Nat.le_div_iff_mul_le hp]
  nlinarith

private theorem comb_bd (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (n : ℕ) (c₁ c₂ j X Y u v : ℝ) (hj : 0 ≤ j) (hX : 0 ≤ X)
    (hY : 0 ≤ Y) (hu : u ≤ a ^ (n + 1) * (Real.exp (c₁ * j) * X + Y)) (hv : v ≤ b ^ (n + 1) * (Real.exp (c₂ * j) * X + Y)) :
    u + c * v ≤ (a + (c + 1) * b) ^ (n + 1) * (Real.exp (max c₁ c₂ * j) * X + Y) := by
  have e1 : Real.exp (c₁ * j) * X + Y ≤ Real.exp (max c₁ c₂ * j) * X + Y := by
    gcongr; exact le_max_left _ _
  have e2 : Real.exp (c₂ * j) * X + Y ≤ Real.exp (max c₁ c₂ * j) * X + Y := by
    gcongr; exact le_max_right _ _
  set Z := Real.exp (max c₁ c₂ * j) * X + Y
  have hZ : 0 ≤ Z := by positivity
  have hu' : u ≤ a ^ (n + 1) * Z := hu.trans (by gcongr)
  have hv' : v ≤ b ^ (n + 1) * Z := hv.trans (by gcongr)
  have h3 : c ≤ (c + 1) ^ (n + 1) := (by linarith : c ≤ c + 1).trans (le_self_pow₀ (by linarith) (Nat.succ_ne_zero n))
  have h4 : a ^ (n + 1) + ((c + 1) * b) ^ (n + 1) ≤ (a + (c + 1) * b) ^ (n + 1) :=
    pow_add_pow_le ha (by positivity) (Nat.succ_ne_zero n)
  have h5 : c * b ^ (n + 1) ≤ ((c + 1) * b) ^ (n + 1) := by rw [mul_pow]; gcongr
  calc u + c * v ≤ a ^ (n + 1) * Z + c * (b ^ (n + 1) * Z) := by gcongr
    _ = (a ^ (n + 1) + c * b ^ (n + 1)) * Z := by ring
    _ ≤ _ := by gcongr; linarith

section
variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem val_congr (x : ℝ) (Λ : (K →+* ℂ) → Multiset ℂ) (t t' : Pl K → Multiset ℂ) (S : Set (Pl K)) (h : ∀ w ∉ S, t w = t' w)
    (P : PR K n) (hP : ∀ y ∈ P.vars, y.1 ∉ S) : val x Λ t P = val x Λ t' P := by
  unfold val
  refine hom_congr_vars (by ext <;> simp) ?_ rfl
  intro i hi _
  simp [hval, h _ (hP i hi)]

private theorem val_gam (x : ℝ) (Λ : (K →+* ℂ) → Multiset ℂ) (t : Pl K → Multiset ℂ) (γ : MvPolynomial (Pl K × Fin n) ℂ) :
    val x Λ t (map C γ : PR K n) = eval (hval t) γ := by
  unfold val
  induction γ using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp => simp only [map_mul, hp]; simp

private theorem evK_congr (hT : TruncSpec) (S : Set (Pl K)) (Φ : KF (Ix K n) (Pl K × Fin n)) (hΦ : admitted S Φ) (L L' : Ix K n → ℂ)
    (t t' : Pl K → Multiset ℂ) (hL : msOf L = msOf L') (h : ∀ w ∉ S, t w = t' w) : evK L (hval t) Φ = evK L' (hval t') Φ := by
  obtain ⟨⟨G, hG⟩, h2⟩ := hT K n S Φ hΦ
  obtain ⟨⟨κ, D, hκ, hB⟩, h3, -⟩ := h2 G hG
  obtain ⟨u, hu, hu'⟩ := h3 L t
  obtain ⟨v, hv, hv'⟩ := h3 L' t'
  have : u = v := by
    funext d
    have a1 := hu' 1 d
    have a2 := hv' 1 d
    rw [hL, val_congr 1 _ t t' S h _ (fun y hy => hκ _ ((hB d).1 y hy)), a2] at a1
    simpa using a1.symm
  subst this
  exact tendsto_nhds_unique hu hv

private theorem pt_card (b : Datum K n) (S : Set (Pl K)) (Λ : (K →+* ℂ) → Multiset ℂ) (t : Pl K → Multiset ℂ) (h : b.Pt S Λ t) :
    ∀ w ∉ S, (t w).card = n := by
  obtain ⟨lam, m, B, h1, -, h3⟩ := h
  intro w hw
  rw [h3 w hw, Multiset.card_sum]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) b.sum
  rw [Multiset.card_map]
  exact ((h1 i).2 w hw).1

private theorem tr_eq {l : ℕ} {μ : Measure (normOneGL (K := K) (n := n))} [μ.IsHaarMeasure] {θ : Twist μ} (𝔰 : Side θ l)
    (p : Submodule ℂ (LL μ) → Prop) (x : ℝ) (j : ℕ) :
    𝔰.tr p x j = ∑ᶠ y ∈ {y : ℝ × Submodule ℂ (LL μ) | (IsSummand μ y.2 ∧ y.2.map (θ.U : LL μ →ₗ[ℂ] LL μ) = y.2 ∧
      eigIn y.2 𝔰.toAmp.A y.1 ≠ ⊥) ∧ p y.2 ∧ y.1 = x}, trOn (eigIn y.2 𝔰.toAmp.A y.1) ((𝔰.Uq 0 ^ j) ∘L Rop μ 𝔰.g ∘L θ.U) := by
  unfold Side.tr
  symm
  rw [finsum_mem_eq_of_bijOn (t := {V : Submodule ℂ (LL μ) | (IsSummand μ V ∧ V.map (θ.U : LL μ →ₗ[ℂ] LL μ) = V ∧ p V) ∧ eigIn V 𝔰.toAmp.A x ≠ ⊥})
    (g := fun V => trOn (eigIn V 𝔰.toAmp.A x) ((𝔰.Uq 0 ^ j) ∘L Rop μ 𝔰.g ∘L θ.U)) Prod.snd]
  · apply finsum_mem_inter_support_eq'
    intro V hV
    refine ⟨fun h => h.1, fun h => ⟨h, fun h0 => hV ?_⟩⟩
    simp only [h0, trOn_bot]
  · refine ⟨?_, ?_, ?_⟩
    · rintro ⟨a, V⟩ ⟨⟨h1, h2, h3⟩, h4, rfl⟩
      exact ⟨⟨h1, h2, h4⟩, h3⟩
    · rintro ⟨a, V⟩ ⟨-, -, h⟩ ⟨a', V'⟩ ⟨-, -, h'⟩ h''
      exact Prod.ext (h.trans h'.symm) h''
    · rintro V ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨(x, V), ⟨⟨h1, h2, h4⟩, h3, rfl⟩, rfl⟩
  · rintro ⟨a, V⟩ ⟨-, -, rfl⟩
    rfl

end

private theorem finsum_sum {α β : Type} (S : Set (α ⊕ β)) (hS : S.Finite) (f : α ⊕ β → ℂ) :
    ∑ᶠ i ∈ S, f i = ∑ᶠ i ∈ Sum.inl ⁻¹' S, f (Sum.inl i) + ∑ᶠ i ∈ Sum.inr ⁻¹' S, f (Sum.inr i) := by
  conv_lhs => rw [← Set.image_preimage_inl_union_image_preimage_inr S]
  rw [finsum_mem_union Set.disjoint_image_inl_image_inr ((hS.preimage Sum.inl_injective.injOn).image _)
    ((hS.preimage Sum.inr_injective.injOn).image _), finsum_mem_image Sum.inl_injective.injOn,
    finsum_mem_image Sum.inr_injective.injOn]

private def ExpF (τ : ℕ → ℂ) : Prop := ∃ (s : Finset ℂ) (c : ℂ → ℂ), 0 ∉ s ∧ ∀ᶠ j : ℕ in atTop, τ j = ∑ ζ ∈ s, c ζ * ζ ^ j

private def Lim (u : ℕ → ℂ) (g e : Prop) (k : ℂ) : Prop := ∃ z, Tendsto u atTop (𝓝 z) ∧ (g → e → z = k) ∧ (¬ g → z = 0)

private theorem ExpF.mul {τ : ℕ → ℂ} (h : ExpF τ) (c : ℂ) : ExpF fun j => c * τ j := by
  obtain ⟨s, c', h0, h1⟩ := h
  refine ⟨s, fun ζ => c * c' ζ, h0, ?_⟩
  filter_upwards [h1] with j hj
  rw [hj, Finset.mul_sum]
  simp only [mul_assoc]

private theorem abs3 (T₁ T₂ T₃ : Type) (a₁ : T₁ → ℝ) (a₂ : T₂ → ℝ) (a₃ : T₃ → ℝ) (τ₁ : T₁ → ℕ → ℂ) (τ₂ : T₂ → ℕ → ℂ) (τ₃ : T₃ → ℕ → ℂ)
    (act₁ good₁ : T₁ → Prop) (act₂ good₂ : T₂ → Prop) (act₃ good₃ : T₃ → Prop) (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) (p : ℕ) (hp : 0 < p)
    (d : ℕ → ℕ) (hd : Tendsto (fun j : ℕ => (d j : ℝ) / j) atTop (𝓝 0))
    (hd' : ∀ B : ℝ, ∀ᶠ j : ℕ in atTop, Real.exp (B * j) ≤ (d j).factorial)
    (e₁ : ∀ i, act₁ i → 0 < a₁ i → ExpF (τ₁ i)) (e₂ : ∀ i, act₂ i → 0 < a₂ i → ExpF (τ₂ i)) (e₃ : ∀ i, act₃ i → 0 < a₃ i → ExpF (τ₃ i))
    (f₁ : {i | act₁ i ∧ a₁ i = x}.Finite) (f₂ : {i | act₂ i ∧ a₂ i = x}.Finite) (f₃ : {i | act₃ i ∧ a₃ i = x}.Finite)
    (h : ∀ N : ℝ, ∃ c₁ : ℝ, ∀ η : ℝ, 0 < η → η < x → ∃ (s₁ : Finset T₁) (s₂ : Finset T₂) (s₃ : Finset T₃)
      (u₁ : T₁ → ℕ → ℂ) (u₂ : T₂ → ℕ → ℂ) (u₃ : T₃ → ℕ → ℂ) (k : ℂ), k ≠ 0 ∧
      (∀ i, i ∈ s₁ ↔ η < a₁ i ∧ act₁ i) ∧ (∀ i, i ∈ s₂ ↔ η < a₂ i ∧ act₂ i) ∧ (∀ i, i ∈ s₃ ↔ η < a₃ i ∧ act₃ i) ∧
      (∀ i ∈ s₁, Lim (u₁ i) (good₁ i) (a₁ i = x) k) ∧ (∀ i ∈ s₂, Lim (u₂ i) (good₂ i) (a₂ i = x) k) ∧
      (∀ i ∈ s₃, Lim (u₃ i) (good₃ i) (a₃ i = x) k) ∧
      ∀ s₀ : ℕ, ∃ K : ℝ, ∀ᶠ j : ℕ in atTop, ∀ m ≤ s₀, ∀ m' ≤ s₀,
        ‖∑ i ∈ s₁, u₁ i (d j) * (a₁ i : ℂ) ^ d j * (cheb η (j / p + m) (a₁ i) : ℂ) * τ₁ i (j + m') +
          (∑ i ∈ s₂, u₂ i (d j) * (a₂ i : ℂ) ^ d j * (cheb η (j / p + m) (a₂ i) : ℂ) * τ₂ i (j + m') +
          ∑ i ∈ s₃, u₃ i (d j) * (a₃ i : ℂ) ^ d j * (cheb η (j / p + m) (a₃ i) : ℂ) * τ₃ i (j + m'))‖ ≤
            K ^ (d j + 1) * (Real.exp (c₁ * j) * (1 + (4 / η) ^ (j / p) / (d j).factorial) + (4 / η) ^ (j / p) * Real.exp (-N * j))) :
    ∀ᶠ j : ℕ in atTop, ∑ᶠ i ∈ {i | act₁ i ∧ good₁ i ∧ a₁ i = x}, τ₁ i j + (∑ᶠ i ∈ {i | act₂ i ∧ good₂ i ∧ a₂ i = x}, τ₂ i j +
      ∑ᶠ i ∈ {i | act₃ i ∧ good₃ i ∧ a₃ i = x}, τ₃ i j) = 0 := by
  have hfin : {i : T₁ ⊕ T₂ ⊕ T₃ | Sum.elim act₁ (Sum.elim act₂ act₃) i ∧ Sum.elim a₁ (Sum.elim a₂ a₃) i = x}.Finite := by
    refine Set.finite_preimage_inl_and_inr.mp ⟨f₁, Set.finite_preimage_inl_and_inr.mp ⟨f₂, f₃⟩⟩
  have key := absX (T₁ ⊕ T₂ ⊕ T₃) (Sum.elim a₁ (Sum.elim a₂ a₃)) (Sum.elim τ₁ (Sum.elim τ₂ τ₃)) (Sum.elim act₁ (Sum.elim act₂ act₃))
    (Sum.elim good₁ (Sum.elim good₂ good₃)) x hx hx1 p hp d hd hd' ?_ hfin ?_
  · refine key.mono fun j hj => ?_
    have hf2 : {i : T₁ ⊕ T₂ ⊕ T₃ | Sum.elim act₁ (Sum.elim act₂ act₃) i ∧ Sum.elim good₁ (Sum.elim good₂ good₃) i ∧
        Sum.elim a₁ (Sum.elim a₂ a₃) i = x}.Finite := hfin.subset fun i hi => ⟨hi.1, hi.2.2⟩
    rw [finsum_sum _ hf2, finsum_sum _ (hf2.preimage Sum.inr_injective.injOn)] at hj
    exact hj
  · rintro (i | i | i)
    exacts [e₁ i, e₂ i, e₃ i]
  · intro N
    obtain ⟨c₁, h⟩ := h N
    refine ⟨c₁, fun η hη hη' => ?_⟩
    obtain ⟨s₁, s₂, s₃, u₁, u₂, u₃, k, hk, m₁, m₂, m₃, l₁, l₂, l₃, hb⟩ := h η hη hη'
    have hl : ∀ i ∈ s₁.disjSum (s₂.disjSum s₃), Lim (Sum.elim u₁ (Sum.elim u₂ u₃) i) (Sum.elim good₁ (Sum.elim good₂ good₃) i)
        (Sum.elim a₁ (Sum.elim a₂ a₃) i = x) k := by
      rintro (i | i | i) hi
      · exact l₁ i (by simpa using hi)
      · exact l₂ i (by simpa using hi)
      · exact l₃ i (by simpa using hi)
    choose! z hz1 hz2 hz3 using hl
    refine ⟨s₁.disjSum (s₂.disjSum s₃), Sum.elim u₁ (Sum.elim u₂ u₃), z, k, hk, ?_, hz1, hz2, hz3, fun s₀ => ?_⟩
    · rintro (i | i | i)
      · simpa using m₁ i
      · simpa using m₂ i
      · simpa using m₃ i
    · obtain ⟨K, hK⟩ := hb s₀
      refine ⟨K, ?_⟩
      filter_upwards [hK] with j hj m hm m' hm'
      rw [Finset.sum_disjSum, Finset.sum_disjSum]
      exact hj m hm m' hm'

private theorem side_fin (hTr : TrExp) (hEV : EvVal) (hTS : TruncSpec) (hOS : OneSide) (hEv : EvEx) {K : Type} [Field K] [NumberField K]
    [_root_.NumberField.IsTotallyComplex K] {μ : Measure (normOneGL (K := K) (n := (2 + 2)))} [μ.IsHaarMeasure] {θ : Twist μ} (𝔰 : Side θ 2) :
    (∀ y : ℝ × Submodule ℂ (LL μ), (IsSummand μ y.2 ∧ y.2.map (θ.U : LL μ →ₗ[ℂ] LL μ) = y.2 ∧ eigIn y.2 𝔰.toAmp.A y.1 ≠ ⊥) → 0 < y.1 →
      ExpF fun j => trOn (eigIn y.2 𝔰.toAmp.A y.1) ((𝔰.Uq 0 ^ j) ∘L Rop μ 𝔰.g ∘L θ.U)) ∧
    ∀ x : ℝ, 0 < x → {y : ℝ × Submodule ℂ (LL μ) |
      (IsSummand μ y.2 ∧ y.2.map (θ.U : LL μ →ₗ[ℂ] LL μ) = y.2 ∧ eigIn y.2 𝔰.toAmp.A y.1 ≠ ⊥) ∧ y.1 = x}.Finite := by
  obtain ⟨hA0, -, -, ev, hev, hin⟩ := hEv K (2 + 2) (by norm_num) μ 𝔰.toAmp
  obtain ⟨c₁, h⟩ := sideEst hOS hEV hTS K (2 + 2) 2 (by norm_num) μ θ 𝔰 ev hev hin 0
  have key : ∀ x : ℝ, 0 < x → ∃ (η : ℝ) (s : Finset (ℝ × Submodule ℂ (LL μ))), η < x ∧
      (∀ y, y ∈ s ↔ η < y.1 ∧ IsSummand μ y.2 ∧ y.2.map (θ.U : LL μ →ₗ[ℂ] LL μ) = y.2 ∧ eigIn y.2 𝔰.toAmp.A y.1 ≠ ⊥) ∧
        (∀ y ∈ s, FiniteDimensional ℂ (eigIn y.2 𝔰.toAmp.A y.1)) := by
    intro x hx
    have hη : 0 < min (x / 2) 1 := lt_min (by linarith) one_pos
    obtain ⟨χ, h1, h2, h3, -⟩ := chi_ex _ hη
    obtain ⟨s, hs, hs', -⟩ := h _ hη (min_le_right _ _) χ h1 h2 h3
    exact ⟨_, s, (min_le_left _ _).trans_lt (by linarith), hs, hs'⟩
  refine ⟨fun y hy hy0 => ?_, fun x hx => ?_⟩
  · obtain ⟨η, s, h1, h2, h3⟩ := key _ hy0
    exact hTr K (2 + 2) 2 (by norm_num) μ θ 𝔰 y.2 y.1 hA0 hy.1 (h3 y ((h2 y).mpr ⟨h1, hy⟩))
  · obtain ⟨η, s, h1, h2, h3⟩ := key _ hx
    exact s.finite_toSet.subset fun y hy => (h2 y).mpr ⟨hy.2 ▸ h1, hy.1⟩

private theorem fam_card (hPar : ParEx) {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    {μ : Measure (normOneGL (K := E) (n := (2 + 2)))} [μ.IsHaarMeasure] {θ : Twist μ} {𝔢 : Side θ 2} (𝔵 : UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.Fam 𝔢) :
    (∀ τ, (𝔵.Λ τ).card = 2 + 2) ∧ ∀ w ∉ 𝔢.S, (𝔵.t w).card = 2 + 2 ∧ 0 ∉ 𝔵.t w := by
  have h1 : IsSummand (BW.mu1 E 2) 𝔵.τ₁ :=
    ⟨𝔵.pair.irr₁.le, 𝔵.pair.irr₁.closed, 𝔵.pair.irr₁.inv, 𝔵.pair.irr₁.ne, fun V a b c => 𝔵.pair.irr₁.irr V a b c⟩
  have h2 : IsSummand (BW.mu1 E 2) 𝔵.τ₂ :=
    ⟨𝔵.pair.irr₂.le, 𝔵.pair.irr₂.closed, 𝔵.pair.irr₂.inv, 𝔵.pair.irr₂.ne, fun V a b c => 𝔵.pair.irr₂.irr V a b c⟩
  refine ⟨fun τ => ?_, fun w hw => ⟨?_, ?_⟩⟩
  · rw [UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.Fam.Λ, Multiset.card_add, (𝔵.at₁.1 τ).1, (𝔵.at₂.1 τ).1]
  · rw [UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.Fam.t, Multiset.card_add, (𝔵.at₁.2 w hw).1, (𝔵.at₂.2 w hw).1]
  · rw [UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.Fam.t, Multiset.mem_add, not_or]
    exact ⟨(hPar E 2 (by norm_num) _ _ h1).2.2 w _ (𝔵.at₁.2 w hw), (hPar E 2 (by norm_num) _ _ h2).2.2 w _ (𝔵.at₂.2 w hw)⟩

private theorem sep (hEV : EvVal) (hVB : ValBc) (hSep : SepPoly) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [_root_.NumberField.IsTotallyComplex F] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (hn : 0 < n)
    {μE : Measure (normOneGL (K := E) (n := n))} [μE.IsHaarMeasure] {μF : Measure (normOneGL (K := F) (n := n))} [μF.IsHaarMeasure] (𝔞 : Amp μE) (𝔟 : Amp μF)
    (hS : ∀ w : Pl E, w ∈ 𝔞.S ↔ w.under (𝓞 F) ∈ 𝔟.S) (Λ : (E →+* ℂ) → Multiset ℂ) (t : Pl E → Multiset ℂ)
    (hΛ : ∀ τ, (Λ τ).card = n) (ht : ∀ w ∉ 𝔞.S, (t w).card = n)
    (sE : Finset (ℝ × Submodule ℂ (LL μE))) (sF : Finset (ℝ × Submodule ℂ (LL μF)))
    (hE : ∀ y ∈ sE, 0 < y.1 ∧ IsSummand μE y.2 ∧ eigIn y.2 𝔞.A y.1 ≠ ⊥) (hF : ∀ y ∈ sF, 0 < y.1 ∧ IsSummand μF y.2 ∧ eigIn y.2 𝔟.A y.1 ≠ ⊥) :
    ∃ (P : PR E n) (κ : Finset (Pl E)) (D : ℕ), (∀ w ∈ κ, w ∉ 𝔞.S) ∧ Bd κ D D P ∧ (∀ x : ℝ, x ≠ 0 → val x Λ t P ≠ 0) ∧
      (∀ y ∈ sE, ¬ At μE 𝔞.S y.2 Λ t → ∃ (L : Ix E n → ℂ) (t' : Pl E → Multiset ℂ), At μE 𝔞.S y.2 (msOf L) t' ∧ val y.1 (msOf L) t' P = 0) ∧
      (∀ y ∈ sF, ¬ (∃ Λ' t', At μF 𝔟.S y.2 Λ' t' ∧ Λ = bcInf Λ' ∧ ∀ w ∉ 𝔞.S, t w = bcSat t' w) →
        ∃ (L : Ix F n → ℂ) (t' : Pl F → Multiset ℂ), At μF 𝔟.S y.2 (msOf L) t' ∧ val y.1 (msOf L) t' (bcPR F P) = 0) := by
  classical
  have pE : ∀ y ∈ sE, ∃ (L : Ix E n → ℂ) (t' : Pl E → Multiset ℂ), At μE 𝔞.S y.2 (msOf L) t' := by
    intro y hy
    obtain ⟨Λ', t', h⟩ := (hEV E n hn μE 𝔞 y.2 y.1 (hE y hy).1 (hE y hy).2.1).1 (hE y hy).2.2
    obtain ⟨L, rfl⟩ := (bdLem E n ∅ ∅ 0 0 0 0 0 0).2.2.2 Λ' fun τ => (h.1 τ).1
    exact ⟨L, t', h⟩
  have pF : ∀ y ∈ sF, ∃ (L : Ix F n → ℂ) (t' : Pl F → Multiset ℂ), At μF 𝔟.S y.2 (msOf L) t' := by
    intro y hy
    obtain ⟨Λ', t', h⟩ := (hEV F n hn μF 𝔟 y.2 y.1 (hF y hy).1 (hF y hy).2.1).1 (hF y hy).2.2
    obtain ⟨L, rfl⟩ := (bdLem F n ∅ ∅ 0 0 0 0 0 0).2.2.2 Λ' fun τ => (h.1 τ).1
    exact ⟨L, t', h⟩
  choose! LE tE hLE using pE
  choose! LF tF hLF using pF
  let I₁ := {y // y ∈ sE.filter fun y => ¬ At μE 𝔞.S y.2 Λ t}
  let I₂ := {y // y ∈ sF.filter fun y => ¬ (∃ Λ' t', At μF 𝔟.S y.2 Λ' t' ∧ Λ = bcInf Λ' ∧ ∀ w ∉ 𝔞.S, t w = bcSat t' w)}
  letI : Fintype I₁ := Finset.Subtype.fintype _
  letI : Fintype I₂ := Finset.Subtype.fintype _
  obtain ⟨P, κ, D, h1, h2, h3, h4⟩ := hSep E n 𝔞.S Λ t (I₁ ⊕ I₂)
    (Sum.elim (fun y => msOf (LE y.1)) fun y => bcInf (msOf (LF y.1))) (Sum.elim (fun y => tE y.1) fun y => bcSat (tF y.1)) hΛ ht
    (by
      rintro (y | y) τ
      · exact ((hLE y.1 (Finset.mem_filter.mp y.2).1).1 τ).1
      · exact ((hLF y.1 (Finset.mem_filter.mp y.2).1).1 _).1)
    (by
      rintro (y | y) w hw
      · exact ((hLE y.1 (Finset.mem_filter.mp y.2).1).2 w hw).1
      · exact (Multiset.card_map _ _).trans ((hLF y.1 (Finset.mem_filter.mp y.2).1).2 _ fun h => hw ((hS w).mpr h)).1)
    (by
      rintro (y | y) ⟨ha, hb⟩
      · have h := hLE y.1 (Finset.mem_filter.mp y.2).1
        refine (Finset.mem_filter.mp y.2).2 ⟨fun τ => ?_, fun w hw => ?_⟩
        · rw [congrFun ha τ]; exact h.1 τ
        · rw [hb w hw]; exact h.2 w hw
      · exact (Finset.mem_filter.mp y.2).2 ⟨_, _, hLF y.1 (Finset.mem_filter.mp y.2).1, ha, hb⟩)
  refine ⟨P, κ, D, h1, h2, h3, fun y hy hy' => ⟨LE y, tE y, hLE y hy, ?_⟩, fun y hy hy' => ⟨LF y, tF y, hLF y hy, ?_⟩⟩
  · exact h4 (Sum.inl ⟨y, Finset.mem_filter.mpr ⟨hy, hy'⟩⟩) y.1
  · rw [(hVB F E n y.1 _ (tF y) P fun z hz => ((hLF y hy).2 _ fun h => h1 _ (h2.1 z hz) ((hS _).mpr h)).1).1]
    exact h4 (Sum.inr ⟨y, Finset.mem_filter.mpr ⟨hy, hy'⟩⟩) y.1

set_option maxHeartbeats 16000000 in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.cixOf :
    ParEx → TrExp → EvVal → ValBc → KillEx2 → KfBc → TruncSpec → SepPoly → OneSide → OneSideX → EvEx → Kill → KillExempt → FamEx → CIx := by
  set_option maxHeartbeats 4000000 in
    intro hPar hTr hEV hVB hK2 hKf hTS hSep hOS hOSX hEv hKill hKX hFam F E _ _ _ _ _ _ _ μE _ μF _ θ 𝔢 𝔣 c hG 𝔵 hoff
    classical
    obtain ⟨hAE0, hAE1, -, evE, hevE, hinE⟩ := hEv E (2 + 2) (by norm_num) μE 𝔢.toAmp
    obtain ⟨hAF0, hAF1, -, evF, hevF, hinF⟩ := hEv F (2 + 2) (by norm_num) μF 𝔣.toAmp
    obtain ⟨Nn, Cf, hN⟩ := hFam E μE _ 𝔵.τ₁ 𝔵.τ₂ 𝔵.pair 𝔵.D 𝔵.d 𝔵.d' 𝔵.A 𝔵.A' 𝔵.P 𝔵.isP
    obtain ⟨evz, hevz⟩ := evzEx 𝔵 evE hevE
    obtain ⟨⟨sp, hsp, hsp1, hsp0⟩, hexp⟩ := famExp 𝔵 Nn Cf hN hAE0 hAE1
    refine ⟨Nn, hN.2, fun x hx => ?_⟩
    by_cases hx1 : 1 < x
    · refine Eventually.of_forall fun j => ?_
      rw [hsp0 x hx (fun h => absurd (hsp1 x h) (not_le.mpr hx1)) j]
      simp only [Side.tr, eig_bot _ _ hAE1 x hx1, eig_bot _ _ hAF1 x hx1, trOn_bot, finsum_zero, mul_zero, add_zero]
    obtain ⟨d, hd, hd'⟩ := UpperTheory.ConvolutionTheory.FX.degree
    obtain ⟨hS, p, C₀, hp, hGeo⟩ := hG
    obtain ⟨eE, fE⟩ := side_fin hTr hEV hTS hOS hEv 𝔢
    obtain ⟨eF, fF⟩ := side_fin hTr hEV hTS hOS hEv 𝔣
    obtain ⟨hΛ, ht⟩ := fam_card hPar 𝔵
    have key := abs3 _ _ _ Prod.fst id Prod.fst
      (fun y j => trOn (eigIn y.2 𝔢.toAmp.A y.1) ((𝔢.Uq 0 ^ j) ∘L Rop μE 𝔢.g ∘L θ.U))
      (fun a j => (1 / 2 : ℂ) * 𝔵.tr Nn a j)
      (fun y j => -c * trOn (eigIn y.2 𝔣.toAmp.A y.1) ((𝔣.Uq 0 ^ j) ∘L Rop μF 𝔣.g ∘L (Twist.id μF).U))
      _ (fun y => At μE 𝔢.S y.2 𝔵.Λ 𝔵.t) (fun a => a ∈ sp) (fun _ => True)
      _ (fun y => ∃ Λ' t', At μF 𝔣.S y.2 Λ' t' ∧ 𝔵.Λ = bcInf Λ' ∧ ∀ w ∉ 𝔢.S, 𝔵.t w = bcSat t' w)
      x hx (not_lt.mp hx1) (2 * p) (by omega) d hd hd' eE (fun a _ _ => ExpF.mul (hexp a) _)
      (fun y h1 h2 => (eF y h1 h2).mul _) (fE x hx) (sp.finite_toSet.subset fun a ha => ha.1) (fF x hx) ?_
    · refine key.mono fun j hj => ?_
      rw [tr_eq, tr_eq]
      have h2 : ∑ᶠ i ∈ {i : ℝ | i ∈ sp ∧ True ∧ id i = x}, (1 / 2 : ℂ) * 𝔵.tr Nn i j = (1 / 2 : ℂ) * 𝔵.tr Nn x j := by
        by_cases hxs : x ∈ sp
        · have : {i : ℝ | i ∈ sp ∧ True ∧ id i = x} = {x} := by
            ext i
            exact ⟨fun h => h.2.2, fun h => ⟨h ▸ hxs, trivial, h⟩⟩
          rw [this, finsum_mem_singleton]
        · have : {i : ℝ | i ∈ sp ∧ True ∧ id i = x} = ∅ := by
            ext i
            exact ⟨fun h => hxs (h.2.2 ▸ h.1), fun h => h.elim⟩
          rw [this, finsum_mem_empty, hsp0 x hx hxs, mul_zero]
      rw [h2, ← mul_finsum_mem] at hj
      linear_combination hj
    intro N
    obtain ⟨cE, hE⟩ := sideEstX hOSX hEV hTS E μE θ 𝔢 𝔵 evE evz Nn Cf hevE hinE hevz hN.1 sp hsp C₀ N
    obtain ⟨cF, hF⟩ := sideEst hOS hEV hTS F (2 + 2) 2 (by norm_num) μF _ 𝔣 evF hevF hinF C₀
    refine ⟨max cE cF, fun η hη hηx => ?_⟩
    have hη1 : η ≤ 1 := hηx.le.trans (not_lt.mp hx1)
    obtain ⟨χ, hχ1, hχ2, hχ3, hχ4, hχ5⟩ := chi_ex η hη
    obtain ⟨sE, hsE, -, hE⟩ := hE η hη hη1 χ hχ1 hχ2 hχ3
    obtain ⟨sF, hsF, -, hF⟩ := hF η hη hη1 χ hχ1 hχ2 hχ3
    obtain ⟨B, _, b, hb1, hb2, hb3⟩ := hKX E μE θ 𝔢 𝔵 η hη
    obtain ⟨B', _, b', hb1', hb3'⟩ := hKill F (2 + 2) (by norm_num) μF 𝔣.toAmp η hη
    obtain ⟨L, hL⟩ := (bdLem E (2 + 2) ∅ ∅ 0 0 0 0 0 0).2.2.2 𝔵.Λ hΛ
    obtain ⟨Φ, hΦ, hΦ0, hΦ1, hΦ2⟩ := hK2 F E (2 + 2) 𝔢.S 𝔣.S hS B B' b b' hb1 hb1' L 𝔵.t (fun w hw => (ht w hw).1)
      (by rw [hL]; exact hb2) (by rw [hL]; exact fun i => hoff (b' i))
    obtain ⟨⟨G, hΦG⟩, hT⟩ := hTS E (2 + 2) 𝔢.S Φ hΦ
    obtain ⟨⟨κ₁, D₁, hκ₁, hB₁⟩, -⟩ := hT G hΦG
    obtain ⟨Φ', G', hΦ', hΦG', hGG, hΦΦ⟩ := hKf F E (2 + 2) 𝔢.S 𝔣.S hS Φ G hΦ hΦG
    have hkill' : ∀ i, Kills 𝔣.S Φ' (b' i) := fun i L' t' h => by
      rw [hΦΦ L' t' (pt_card _ _ _ _ h)]
      exact hΦ2 i L' t' h
    obtain ⟨P₀, κ₂, D₂, hκ₂, hB₂, hP0, hPE, hPF⟩ := sep hEV hVB hSep (by norm_num) 𝔢.toAmp 𝔣.toAmp hS 𝔵.Λ 𝔵.t hΛ
      (fun w hw => (ht w hw).1) sE sF
      (fun y hy => ⟨hη.trans ((hsE y).mp hy).1, ((hsE y).mp hy).2.1, ((hsE y).mp hy).2.2.2⟩)
      (fun y hy => ⟨hη.trans ((hsF y).mp hy).1, ((hsF y).mp hy).2.1, ((hsF y).mp hy).2.2.2⟩)
    have hκ : ∀ w ∈ κ₁ ∪ κ₂, w ∉ 𝔢.S := fun w hw => (Finset.mem_union.mp hw).elim (hκ₁ w) (hκ₂ w)
    obtain ⟨γ, hγ1, hγ0, hγ⟩ := hGeo (κ₁ ∪ κ₂) hκ 𝔵.t (fun w hw => ht w (hκ w hw)) (D₁ + D₂)
    have hP : ∀ y ∈ (map C γ * P₀ : PR E (2 + 2)).vars, y.1 ∉ 𝔢.S := fun y hy =>
      (Finset.mem_union.mp (vars_mul _ _ hy)).elim (fun h => hκ _ (hγ1 y (vars_map _ _ h))) fun h => hκ₂ _ (hB₂.1 y h)
    have hVB0 := hVB F E (2 + 2) 0 (fun _ => 0) (fun _ => Multiset.replicate (2 + 2) 0) (map C γ * P₀) fun _ _ => by simp
    have hP' : ∀ y ∈ (bcPR F (map C γ * P₀ : PR E (2 + 2))).vars, y.1 ∉ 𝔣.S := fun y hy h => by
      obtain ⟨y', h1, h2⟩ := hVB0.2.1 y hy
      exact hP y' h1 ((hS _).mpr (h2 ▸ h))
    obtain ⟨uE, w, huE, hw, hE⟩ := hE Φ G hΦ hΦG (hb3 evE hevE hevz.comm χ hχ1 hχ4 hχ5 Φ G hΦ hΦ1 hΦG) _ hP
    obtain ⟨uF, huF, hF⟩ := hF Φ' G' hΦ' hΦG' (hb3' evF hevF χ hχ1 hχ4 hχ5 Φ' G' hΦ' hkill' hΦG') _ hP'
    refine ⟨sE, sp.filter (η < ·), sF, uE, w, uF, x * val x 𝔵.Λ 𝔵.t (map C γ * P₀ : PR E (2 + 2)) * evK L (hval 𝔵.t) Φ, ?_, hsE,
      fun a => by rw [Finset.mem_filter, and_comm]; rfl, hsF, fun y hy => ?_, fun a _ => ?_, fun y hy => ?_, fun s₀ => ?_⟩
    · rw [map_mul, val_gam]
      exact mul_ne_zero (mul_ne_zero (by exact_mod_cast hx.ne') (mul_ne_zero hγ0 (hP0 x hx.ne'))) hΦ0
    · by_cases hg : At μE 𝔢.S y.2 𝔵.Λ 𝔵.t
      · refine ⟨_, huE y hy L 𝔵.t (hL ▸ hg), fun _ h => ?_, fun h => absurd hg h⟩
        rw [hL, h]
      · obtain ⟨L', t', h1, h2⟩ := hPE y hy hg
        refine ⟨_, huE y hy L' t' h1, fun h => absurd h hg, fun _ => ?_⟩
        rw [map_mul, h2, mul_zero, mul_zero, zero_mul]
    · refine ⟨_, hw a L hL, fun _ h => ?_, fun h => absurd trivial h⟩
      rw [show a = x from h]
    · by_cases hg : ∃ Λ' t', At μF 𝔣.S y.2 Λ' t' ∧ 𝔵.Λ = bcInf Λ' ∧ ∀ w ∉ 𝔢.S, 𝔵.t w = bcSat t' w
      · obtain ⟨Λ', t', h1, h2, h3⟩ := id hg
        obtain ⟨L', rfl⟩ := (bdLem F (2 + 2) ∅ ∅ 0 0 0 0 0 0).2.2.2 Λ' fun τ => (h1.1 τ).1
        refine ⟨_, huF y hy L' t' h1, fun _ h => ?_, fun h => absurd hg h⟩
        rw [h, hΦΦ L' t' fun v hv => (h1.2 v hv).1,
          (hVB F E (2 + 2) x _ t' _ fun z hz => (h1.2 _ fun h => hP z hz ((hS _).mpr h)).1).1, ← h2,
          val_congr x _ _ _ _ h3 _ hP, evK_congr hTS _ Φ hΦ L (fun y => L' (y.1.comp (algebraMap F E), y.2)) _ _ (hL.trans h2) h3]
      · obtain ⟨L', t', h1, h2⟩ := hPF y hy hg
        refine ⟨_, huF y hy L' t' h1, fun h => absurd h hg, fun _ => ?_⟩
        rw [map_mul, map_mul, h2, mul_zero, mul_zero, zero_mul]
    obtain ⟨ME, hME, hE⟩ := hE (2 * p) (by omega) s₀
    obtain ⟨MF, hMF, hF⟩ := hF (2 * p) N s₀
    obtain ⟨J, hJ⟩ := eventually_atTop.mp (hγ evE evF hevE hevF)
    refine ⟨ME + (‖c‖ + 1) * MF, ?_⟩
    filter_upwards [hE, eventually_ge_atTop J, deg_ev d hd p hp (s₀ + D₂)] with j hE hj hdeg m hm m' hm'
    have hBd : Bd (κ₁ ∪ κ₂) (D₁ + D₂) ((j + m') / p) (chebP η (j / (2 * p) + m) * (trunc (d j) G * P₀) : PR E (2 + 2)) := by
      have h1 := (bdLem E (2 + 2) _ _ _ _ _ _ _ _).1 (hB₁ (d j)) hB₂
      have h2 := (bdLem E (2 + 2) _ _ _ _ _ _ _ _).1 ((bdLem E (2 + 2) (κ₁ ∪ κ₂) ∅ 0 0 0 0 0 0).2.1 η (j / (2 * p) + m)) h1
      refine (bdLem E (2 + 2) _ _ _ _ _ _ _ 0).2.2.1 ?_ (by omega) ?_ h2
      · intro z hz
        simpa using hz
      · have := hdeg m'
        omega
    obtain ⟨gE, gF, r1, r2, r3⟩ := hJ (j + m') (by omega) _ hBd.1 hBd.2.1 hBd.2.2
    have q1 : (map C γ * (chebP η (j / (2 * p) + m) * (trunc (d j) G * P₀)) : PR E (2 + 2)) =
        chebP η (j / (2 * p) + m) * (trunc (d j) G * (map C γ * P₀)) := by ring
    rw [q1] at r1 r2
    rw [map_mul (bcPR F), map_mul (bcPR F), hVB0.2.2, ← hGG] at r2
    have b1 := hE (d j) m hm m' hm' gE r1
    have b2 := hF j (d j) m hm m' hm' gF r2
    refine le_trans ?_ (comb_bd ME MF ‖c‖ hME hMF (norm_nonneg _) (d j) cE cF j _ _ _ _ (Nat.cast_nonneg _) (by positivity)
      (by positivity) b1 b2)
    rw [← norm_mul, ← norm_neg (_ - _ - _)]
    refine le_trans (le_of_eq ?_) (norm_add_le _ _)
    congr 1
    rw [r3, mul_sub, Finset.mul_sum, ← sub_eq_zero]
    have : ∀ (u v : ℂ), u * (-c * v) = -(c * (u * v)) := fun u v => by ring
    simp only [this, Finset.sum_neg_distrib, id]
    ring
