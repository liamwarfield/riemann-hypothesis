module

public import Development.WeilBound.ThetaLifts.SmallCones.ConeBasic

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.SmallCones.ConeUnf
section -- merged from Development.WeilBound.ThetaLifts.SmallCones.ConeEx
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem int_prod {α β : Type} [TopologicalSpace α] [TopologicalSpace β] [MeasurableSpace α] [MeasurableSpace β] [BorelSpace α]
    [BorelSpace β] [SecondCountableTopology α] [SecondCountableTopology β] (μ : Measure α) (ν : Measure β) [SFinite ν]
    {θ : α × β → ℂ} (hθ : Continuous θ) {w : α → ℂ} (hw : Continuous w) {a : α → ℝ} (ha : ∀ l, ‖w l‖ = a l)
    (hfin : ∫⁻ l, (∫⁻ g, ‖θ (l, g)‖ₑ ∂ν) * ENNReal.ofReal (a l) ∂μ < ⊤) : Integrable (fun x => θ x * w x.1) (μ.prod ν) := by
  have hc : Continuous fun x : α × β => θ x * w x.1 := hθ.mul (hw.comp continuous_fst)
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hc.measurable.enorm.aemeasurable]
  convert hfin using 3 with l
  simp only [enorm_mul]
  rw [lintegral_mul_const' _ _ (by simp), ← ha, ofReal_norm_eq_enorm]

section Core

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

structure LineOK (B : Base F E) (M : Model σ X W) (om : Rep σ X W) (M₀ : Model σ X₁ W₁) (om₀ : Rep σ X₁ W₁)
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) (μ : Measure (AE F E)ˣ) (u : (AE F E)ˣ → Ten F E n d) (ν : Chr F E) (z : ℕ)
    (S : Submodule ℂ (Fn F n d)) : Prop where
  le : ∀ Ψ ∈ S, Ψ ∈ schA F (Fin n × Fin d)
  stab : ∀ x, ∀ Ψ ∈ S, om x Ψ ∈ S
  sch : ∀ l, ∀ Ψ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ (u l) Ψ) ∈ schA F (Fin n₁ × Fin d₁)
  th : ∀ g h, ∃ l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁), ∀ Φ ∈ schA F _, l Φ = theta om₀ Φ g h
  int : ∀ Ψ ∈ S, ∀ h₁, Integrable (fun x : (AE F E)ˣ × UA σ X₁.J =>
    theta om₀ (e (M.co.rho B.ψ (u x.1) Ψ)) x.2 h₁ * ((ν x.1 : ℂ) * ((absE F E x.1 : ℝ) : ℂ) ^ z)) (μ.prod (M₀.μ.restrict M₀.dom))
  lam : ∀ Ψ ∈ schA F (Fin n × Fin d), ∃ Ψ₁ ∈ schA F (Fin n₁ × Fin d₁), ∀ l₁ ∈ (adeleClass F).adm (Fin n₁ × Fin d₁),
    Integrable (fun l : (AE F E)ˣ => l₁ (e (M.co.rho B.ψ (u l) Ψ)) * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) μ ∧
    l₁ Ψ₁ = ∫ l, l₁ (e (M.co.rho B.ψ (u l) Ψ)) * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z ∂μ

variable {B : Base F E} {M : Model σ X W} {om : Rep σ X W} {M₀ : Model σ X₁ W₁} {om₀ : Rep σ X₁ W₁}
  {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {μ : Measure (AE F E)ˣ} {u : (AE F E)ˣ → Ten F E n d} {ν : Chr F E} {z : ℕ}
  {S : Submodule ℂ (Fn F n d)}

theorem LineOK.theta_sum (h : LineOK B M om M₀ om₀ e μ u ν z S) {m : ℕ} (c : Fin m → ℂ) {Ψ : Fin m → Fn F n₁ d₁}
    (hΨ : ∀ i, Ψ i ∈ schA F (Fin n₁ × Fin d₁)) (g h₁) : theta om₀ (∑ i, c i • Ψ i) g h₁ = ∑ i, c i * theta om₀ (Ψ i) g h₁ := by
  obtain ⟨l, -, hl⟩ := h.th g h₁
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hl _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hΨ i)), map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hl _ (hΨ i), smul_eq_mul]

theorem LineOK.val_sum (h : LineOK B M om M₀ om₀ e μ u ν z S) {m : ℕ} (c : Fin m → ℂ) {Ψ : Fin m → Fn F n d} (hΨ : ∀ i, Ψ i ∈ S)
    (l g h₁) : theta om₀ (e (M.co.rho B.ψ (u l) (∑ i, c i • Ψ i))) g h₁ =
      ∑ i, c i * theta om₀ (e (M.co.rho B.ψ (u l) (Ψ i))) g h₁ := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [rho_linear, map_sum]
  simp only [map_smul]
  exact h.theta_sum c (fun i => h.sch l _ (h.le _ (hΨ i))) g h₁

theorem LineOK.coneI_eq [SFinite μ] [SFinite M₀.μ] (h : LineOK B M om M₀ om₀ e μ u ν z S) {K : Subgroup (UA σ X.J)} (μK : Measure K)
    {Φ : Fn F n d} {m : ℕ} {Ψ : Fin m → Fn F n d} {c : Fin m → K → ℂ} (hΨ : ∀ i, Ψ i ∈ S) (hc : ∀ i, Integrable (c i) μK)
    (hd : ∀ k : K, om (k.1, 1) Φ = ∑ i, c i k • Ψ i) (h₁ : UA σ W₁.J) :
    coneI B M om M₀ om₀ e K μK μ u ν z Φ h₁ = M₀.I om₀ (cone B M om e K μK μ u ν z Φ) h₁ := by
  choose Λ hΛ hΛ' using fun i => h.lam (Ψ i) (h.le _ (hΨ i))
  have h1 : cone B M om e K μK μ u ν z Φ = ∑ i, (∫ k, c i k ∂μK) • Λ i := by
    funext y
    have e1 : ∀ k : K, ∫ l, e (M.co.rho B.ψ (u l) (om (k.1, 1) Φ)) y * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z ∂μ =
        ∑ i, c i k * Λ i y := fun k => by
      have e2 := fun i => hΛ' i _ (ev_adm y)
      simp only [LinearMap.proj_apply] at e2
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hd, rho_linear, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      rw [integral_finsetSum _ fun i _ => by simpa only [mul_assoc] using (e2 i).1.const_mul (c i k)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [(e2 i).2, ← integral_const_mul]
      simp only [mul_assoc]
    simp only [cone, e1, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_finsetSum _ fun i _ => (hc i).mul_const _]
    simp only [integral_mul_const]
  have h2 : ∀ i g, theta om₀ (Λ i) g h₁ =
      ∫ l, theta om₀ (e (M.co.rho B.ψ (u l) (Ψ i))) g h₁ * ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) ∂μ := fun i g => by
    obtain ⟨l, hl, hl'⟩ := h.th g h₁
    rw [← hl' _ (hΛ i), (hΛ' i l hl).2]
    simp only [hl' _ (h.sch _ _ (h.le _ (hΨ i))), mul_assoc]
  have h3 : ∀ i, IntegrableOn (fun g => theta om₀ (Λ i) g h₁) M₀.dom M₀.μ := fun i => by
    simp only [h2]
    exact (h.int _ (hΨ i) h₁).integral_prod_right
  set T : Fin m → ℂ := fun i => M₀.I om₀ (Λ i) h₁ with hT
  have h4 : ∀ i, ∫ l, M₀.I om₀ (e (M.co.rho B.ψ (u l) (Ψ i))) h₁ * ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) ∂μ = T i := fun i => by
    simp only [hT, Model.I, h2]
    rw [← integral_integral_swap (h.int _ (hΨ i) h₁)]
    simp only [integral_mul_const]
  have h5 : ∀ i, Integrable (fun l => M₀.I om₀ (e (M.co.rho B.ψ (u l) (Ψ i))) h₁ * ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z)) μ :=
    fun i => by
      have := (h.int _ (hΨ i) h₁).integral_prod_left
      simpa only [integral_mul_const, Model.I] using this
  have h6 : ∀ k : K, ∫ l, M₀.I om₀ (e (M.co.rho B.ψ (u l) (om (k.1, 1) Φ))) h₁ * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z ∂μ =
      ∑ i, c i k * T i := fun k => by
    rw [← Finset.sum_congr rfl fun i _ => congrArg (c i k * ·) (h4 i)]
    simp only [← integral_const_mul]
    rw [← integral_finsetSum _ fun i _ => (h5 i).const_mul _]
    refine integral_congr_ae ?_
    have : ∀ᵐ l ∂μ, ∀ i, Integrable (fun g => theta om₀ (e (M.co.rho B.ψ (u l) (Ψ i))) g h₁ *
        ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z)) (M₀.μ.restrict M₀.dom) :=
      ae_all_iff.2 fun i => (h.int _ (hΨ i) h₁).prod_right_ae
    filter_upwards [this] with l hl
    simp only [Model.I, hd, h.val_sum _ hΨ, mul_assoc, ← integral_mul_const, ← integral_const_mul, Finset.sum_mul]
    rw [integral_finsetSum _ fun i _ => (hl i).const_mul _]
  rw [h1]
  simp only [coneI, h6]
  rw [integral_finsetSum _ fun i _ => (hc i).mul_const _]
  simp only [integral_mul_const, Model.I, h.theta_sum _ hΛ]
  rw [integral_finsetSum _ fun i _ => (h3 i).const_mul _]
  simp only [integral_const_mul, hT, Model.I]

end Core

end PositivityTheory.ThKCT

end
end

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Core

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
  {B : Base F E} {M : Model σ X W} {om : Rep σ X W} {M₀ : Model σ X₁ W₁} {om₀ : Rep σ X₁ W₁}
  {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {μ : Measure (AE F E)ˣ} {u : (AE F E)ˣ → Ten F E n d} {ν : Chr F E} {z : ℕ}
  {S : Submodule ℂ (Fn F n d)}

theorem LineOK.fin [SFinite μ] [SFinite M₀.μ] (h : LineOK B M om M₀ om₀ e μ u ν z S) {K : Subgroup (UA σ X.J)} (μK : Measure K)
    {Φ : Fn F n d} {m : ℕ} {Ψ : Fin m → Fn F n d} {c : Fin m → K → ℂ} (hΨ : ∀ i, Ψ i ∈ S) (hc : ∀ i, Integrable (c i) μK)
    (hd : ∀ k : K, om (k.1, 1) Φ = ∑ i, c i k • Ψ i) (h₁ : UA σ W₁.J) :
    ∫⁻ k, ∫⁻ l, ∫⁻ g in M₀.dom, ‖theta om₀ (e (M.co.rho B.ψ (u l) (om (k.1, 1) Φ))) g h₁ *
      ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z)‖ₑ ∂M₀.μ ∂μ ∂μK < ⊤ := by
  set J : Fin m → (AE F E)ˣ × UA σ X₁.J → ℂ := fun i x =>
    theta om₀ (e (M.co.rho B.ψ (u x.1) (Ψ i))) x.2 h₁ * ((ν x.1 : ℂ) * ((absE F E x.1 : ℝ) : ℂ) ^ z) with hJ
  have hJi : ∀ i, Integrable (J i) (μ.prod (M₀.μ.restrict M₀.dom)) := fun i => h.int _ (hΨ i) h₁
  have key : ∀ k : K, ∫⁻ l, ∫⁻ g in M₀.dom, ‖theta om₀ (e (M.co.rho B.ψ (u l) (om (k.1, 1) Φ))) g h₁ *
      ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z)‖ₑ ∂M₀.μ ∂μ ≤
      ∑ i, ‖c i k‖ₑ * ∫⁻ x, ‖J i x‖ₑ ∂(μ.prod (M₀.μ.restrict M₀.dom)) := fun k => by
    have e1 : ∀ l g, theta om₀ (e (M.co.rho B.ψ (u l) (om (k.1, 1) Φ))) g h₁ * ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) =
        ∑ i, c i k * J i (l, g) := fun l g => by
      simp only [hd, h.val_sum _ hΨ, hJ, Finset.sum_mul, mul_assoc]
    simp only [e1]
    have hi : Integrable (fun x => ∑ i, c i k * J i x) (μ.prod (M₀.μ.restrict M₀.dom)) :=
      integrable_finsetSum _ fun i _ => (hJi i).const_mul _
    rw [← lintegral_prod (fun x => ‖∑ i, c i k * J i x‖ₑ) hi.1.enorm]
    calc _ ≤ ∫⁻ x, ∑ i, ‖c i k‖ₑ * ‖J i x‖ₑ ∂(μ.prod (M₀.μ.restrict M₀.dom)) :=
          lintegral_mono fun x => (enorm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (enorm_mul _ _).le)
      _ = _ := by
          rw [lintegral_finsetSum' _ fun i _ => (hJi i).1.enorm.const_mul _]
          exact Finset.sum_congr rfl fun i _ => lintegral_const_mul'' _ (hJi i).1.enorm
  refine (lintegral_mono key).trans_lt ?_
  rw [lintegral_finsetSum' _ fun i _ => (hc i).1.enorm.mul_const _]
  refine ENNReal.sum_lt_top.2 fun i _ => ?_
  rw [lintegral_mul_const'' _ (hc i).1.enorm]
  exact ENNReal.mul_lt_top (hc i).2 (hJi i).2

theorem LineOK.unf [SFinite μ] [SFinite M₀.μ] (h : LineOK B M om M₀ om₀ e μ u ν z S) {K : Subgroup (UA σ X.J)} (μK : Measure K)
    {Φ : Fn F n d} {m : ℕ} {Ψ : Fin m → Fn F n d} {c : Fin m → K → ℂ} (hΨ : ∀ i, Ψ i ∈ S) (hc : ∀ i, Integrable (c i) μK)
    (hd : ∀ k : K, om (k.1, 1) Φ = ∑ i, c i k • Ψ i) (ι : (AE F E)ˣ → (AE F E)ˣ)
    (hι : ∀ G : (AE F E)ˣ → ℝ≥0∞, ∫⁻ l, G (ι l) ∂μ = ∫⁻ l, G l ∂μ) (hι' : ∀ G : (AE F E)ˣ → ℂ, ∫ l, G (ι l) ∂μ = ∫ l, G l ∂μ)
    (lev : (AE F E)ˣ × UA σ X₁.J → UA σ X.J) (f : UA σ X.J → ℂ)
    (hf : ∀ l g (k : K), f (lev (ι l, g) * k.1) * (((absE F E (ι l) : ℝ) ^ (1 - (n : ℝ)) : ℝ) : ℂ) =
      theta om₀ (e (M.co.rho B.ψ (u l) (om (k.1, 1) Φ))) g 1 * ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z)) :
    ∫⁻ k, ∫⁻ l, (∫⁻ g in M₀.dom, ‖f (lev (l, g) * k.1)‖ₑ ∂M₀.μ) * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - (n : ℝ))) ∂μ ∂μK < ⊤ ∧
    ∫ k, ∫ l, (∫ g in M₀.dom, f (lev (l, g) * k.1) ∂M₀.μ) * (((absE F E l : ℝ) ^ (1 - (n : ℝ)) : ℝ) : ℂ) ∂μ ∂μK =
      coneI B M om M₀ om₀ e K μK μ u ν z Φ 1 := by
  constructor
  · convert h.fin μK hΨ hc hd 1 using 3 with k
    rw [← hι]
    congr 1
    funext l
    rw [← lintegral_mul_const' _ _ (by simp)]
    congr 1
    funext g
    have he : ENNReal.ofReal ((absE F E (ι l) : ℝ) ^ (1 - (n : ℝ))) =
        ‖(((absE F E (ι l) : ℝ) ^ (1 - (n : ℝ)) : ℝ) : ℂ)‖ₑ := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]
    rw [he, ← eNorm_mul, hf]
  · unfold coneI
    congr 1
    funext k
    rw [← hι']
    congr 1
    funext l
    rw [← integral_mul_const]
    simp only [hf, Model.I, integral_mul_const, mul_assoc]

end Core

end PositivityTheory.ThKCT

end
end

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Core

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

theorem levi_one (H : Plane E d d₁) : IsLevi (σ := σ) (W := W) (W₁ := W₁) H 1 1 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [mat_one']

theorem absE_ne (l : (AE F E)ˣ) : (absE F E l : ℝ) ≠ 0 := by
  have : absE F E l * absE F E l⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact_mod_cast left_ne_zero_of_mul_eq_one this

theorem absE_pos (l : (AE F E)ˣ) : 0 < (absE F E l : ℝ) := lt_of_le_of_ne (NNReal.coe_nonneg _) (absE_ne l).symm

structure LawsT (B : Base F E) (M : Model σ X W) (om : Rep σ X W) (om₀ : Rep σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁)
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) (u : (AE F E)ˣ → Ten F E n d) (w : (AE F E)ˣ → ℂ) (ι : (AE F E)ˣ → (AE F E)ˣ) : Prop where
  one : ι 1 = 1
  w1 : w 1 = 1
  uni : ∀ m ∈ unip σ X H, ∀ Ψ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ (u 1) (om (m, 1) Ψ)) = e (M.co.rho B.ψ (u 1) Ψ)
  tor : ∀ l g₁ p h₁ p', IsLevi H (ι l) g₁ p → IsLevi H' 1 h₁ p' → ∀ Ψ ∈ schA F (Fin n × Fin d),
    (((absE F E (ι l) : ℝ) ^ (1 - (n : ℝ)) : ℝ) : ℂ) • e (M.co.rho B.ψ (u 1) (om (p, p') Ψ)) =
      w l • om₀ (g₁, h₁) (e (M.co.rho B.ψ (u l) Ψ))

structure Laws (B : Base F E) (M : Model σ X W) (om : Rep σ X W) (om₀ : Rep σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁)
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) (u : (AE F E)ˣ → Ten F E n d) (ν χ : Chr F E) (z : ℕ) (ι : (AE F E)ˣ → (AE F E)ˣ) : Prop
    extends LawsT B M om om₀ H H' e u (fun l => (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) ι where
  torW : ∀ t h₁ p', IsLevi H' t h₁ p' → ∃ s : (AE F E)ˣ, ∀ l, ∀ Ψ ∈ schA F (Fin n × Fin d),
    e (M.co.rho B.ψ (u l) (om (1, p') Ψ)) = ((χ t : ℂ) * (((absE F E t : ℝ) ^ (((d : ℝ) - n) / 2) : ℝ) : ℂ) *
      ((ν s : ℂ) * ((absE F E s : ℝ) : ℂ) ^ z)) • om₀ (1, h₁) (e (M.co.rho B.ψ (u (l * s)) Ψ))

variable {B : Base F E} {M : Model σ X W} {om : Rep σ X W} {M₀ : Model σ X₁ W₁} {om₀ : Rep σ X₁ W₁} {H : Plane E n n₁}
  {H' : Plane E d d₁} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {μ : Measure (AE F E)ˣ} {u : (AE F E)ˣ → Ten F E n d} {ν χ : Chr F E} {z : ℕ}
  {ι : (AE F E)ˣ → (AE F E)ˣ} {w : (AE F E)ˣ → ℂ} {χX χW : Chr F E} {r s r' s' r₀ s₀ r₀' s₀' : ℕ}

theorem LawsT.theta (h : LawsT B M om om₀ H H' e u w ι) {l g₁ p h₁ p'} (h1 : IsLevi H (ι l) g₁ p) (h2 : IsLevi H' 1 h₁ p') {Ψ}
    (hΨ : Ψ ∈ schA F (Fin n × Fin d)) :
    thetaSum F (e (M.co.rho B.ψ (u 1) (om (p, p') Ψ))) * (((absE F E (ι l) : ℝ) ^ (1 - (n : ℝ)) : ℝ) : ℂ) =
      theta om₀ (e (M.co.rho B.ψ (u l) Ψ)) g₁ h₁ * w l := by
  have := congrArg (thetaSum F) (h.tor l g₁ p h₁ p' h1 h2 Ψ hΨ)
  rw [thetaSum_smul', thetaSum_smul'] at this
  rw [mul_comm, this, mul_comm]
  rfl

theorem LawsT.rat (h : LawsT B M om om₀ H H' e u w ι) (hD : StabDec) (hTB : ThetaBasic) (hp : IsPair B M χX χW om r s r' s')
    (hp₀ : IsPair B M₀ χX χW om₀ r₀ s₀ r₀' s₀') {j₀ j₁} (hH : H.IsAdapted σ B X X₁ j₀ j₁)
    (hs : ∀ Ψ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ (u 1) Ψ) ∈ schA F (Fin n₁ × Fin d₁)) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d))
    (y) {δ} (hδ : δ ∈ ratU σ X.J) (hx : mat δ *ᵥ incV F H.x = incV F H.x) (g) :
    thv B M om e (u 1) Φ y (δ * g) = thv B M om e (u 1) Φ y g := by
  obtain ⟨m, hm, g₁, p, hp1, rfl, hr⟩ := (hD F E σ B n n₁ X X₁ H j₀ j₁ r s hp.base (Or.inl hp.herm) hH).1 δ 1 (by simpa using hx)
  have hΨ := pair_pres hp (g, y) hΦ
  have e1 : om (m * p * g, y) Φ = om (m, 1) (om (p, 1) (om (g, y) Φ)) := by simp [om_mul, mul_assoc]
  have e2 := h.theta (l := 1) (by rwa [h.one]) (levi_one (W₁ := W₁) H') hΨ
  have e3 := ((hTB F E σ B _ _ X₁ W₁ M₀ χX χW om₀ _ _ _ _ hp₀).1 _ (hs _ hΨ)).2.1 g₁ (hr hδ) 1 (one_mem _) 1 1
  simp only [h.one, h.w1, map_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, mul_one, Circle.coe_one, one_pow] at e2 e3
  unfold thv
  rw [e1, h.uni m hm _ (pair_pres hp _ hΨ), e2, e3]
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta, ← Prod.one_eq_mk]

theorem Laws.coneI_law [μ.IsMulRightInvariant] [MeasurableMul (AE F E)ˣ] (h : Laws B M om om₀ H H' e u ν χ z ι)
    (hp : IsPair B M χX χW om r s r' s') {K : Subgroup (UA σ X.J)} (μK : Measure K) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d))
    {t h₁ p} (hl : IsLevi H' t h₁ p) (y) :
    coneI B M om M₀ om₀ e K μK μ u ν z (om (1, p * y) Φ) 1 =
      (χ t : ℂ) * (((absE F E t : ℝ) ^ (((d : ℝ) - n) / 2) : ℝ) : ℂ) * coneI B M om M₀ om₀ e K μK μ u ν z (om (1, y) Φ) h₁ := by
  obtain ⟨s, hs⟩ := h.torW t h₁ p hl
  unfold coneI
  rw [← integral_const_mul]
  congr 1
  funext k
  rw [← integral_mul_right_eq_self (fun l => M₀.I om₀ (e (M.co.rho B.ψ (u l) (om (k.1, 1) (om (1, y) Φ)))) h₁ * (ν l : ℂ) *
    ((absE F E l : ℝ) : ℂ) ^ z) s, ← integral_const_mul]
  congr 1
  funext l
  have e1 : om (k.1, 1) (om (1, p * y) Φ) = om (1, p) (om (k.1, 1) (om (1, y) Φ)) := by simp [om_mul]
  rw [e1, hs l _ (pair_pres hp _ (pair_pres hp _ hΦ))]
  simp only [Model.I, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta, map_smul, thetaSum_smul', om_mul, Prod.mk_mul_mk, mul_one, one_mul, integral_const_mul,
    map_mul, Circle.coe_mul, NNReal.coe_mul, Complex.ofReal_mul, mul_pow]
  ring

end Core

end PositivityTheory.ThKCT

end
