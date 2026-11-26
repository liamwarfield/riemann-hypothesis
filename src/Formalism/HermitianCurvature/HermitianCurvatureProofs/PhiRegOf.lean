module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbConvDDOfDecDD
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.L1QuotientIntegralBound
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMemMeasurableSet
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

private theorem conj_mem_lemma {ε : Fin (2 * r + k + 1) → Bool} {P a : Mx k r}
    (h1 : P * P⁻¹ = 1) (hPJ : Pᴴ * PI.UpqRep.Jm ε * P = PI.UpqRep.Hpk k r)
    (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    P * a * P⁻¹ ∈ PI.UpqRep.UJset ε := by
  have ha' : aᴴ * PI.UpqRep.Hpk k r * a = PI.UpqRep.Hpk k r := ha
  have hc : (P⁻¹)ᴴ * Pᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  show (P * a * P⁻¹)ᴴ * PI.UpqRep.Jm ε * (P * a * P⁻¹) = PI.UpqRep.Jm ε
  calc (P * a * P⁻¹)ᴴ * PI.UpqRep.Jm ε * (P * a * P⁻¹)
        = (P⁻¹)ᴴ * (aᴴ * (Pᴴ * PI.UpqRep.Jm ε * P) * a) * P⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (P⁻¹)ᴴ * (Pᴴ * PI.UpqRep.Jm ε * P) * P⁻¹ := by rw [hPJ, ha']
      _ = (P⁻¹)ᴴ * Pᴴ * PI.UpqRep.Jm ε * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = PI.UpqRep.Jm ε := by rw [hc, h1, Matrix.one_mul, Matrix.mul_one]

theorem sigma_mul' {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hds : PI.UpqRep.IsDSHpk k r ε lam σ) {a b : Mx k r}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hb : b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    σ (a * b) = (σ a).comp (σ b) := by
  obtain ⟨P, ⟨⟨hPu, hPJ⟩, -⟩, hDS⟩ := hds
  obtain ⟨-, -, ⟨⟨-, hmulU⟩, -, -⟩, -⟩ := hDS
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have key : ∀ g : Mx k r, P⁻¹ * (P * g * P⁻¹) * P = g := fun g => by
    rw [show P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) by simp only [Matrix.mul_assoc],
      h2, Matrix.one_mul, Matrix.mul_one]
  have hprod : P * a * P⁻¹ * (P * b * P⁻¹) = P * (a * b) * P⁻¹ := by
    rw [show P * a * P⁻¹ * (P * b * P⁻¹) = P * a * (P⁻¹ * P) * b * P⁻¹ by
      simp only [Matrix.mul_assoc], h2, Matrix.mul_one, Matrix.mul_assoc P a b]
  have hmul := hmulU _ (conj_mem_lemma h1 hPJ ha) _ (conj_mem_lemma h1 hPJ hb)
  simp only [hprod, key] at hmul
  exact hmul

theorem dd_stable {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)} {w0 : H}
    (hds : PI.UpqRep.IsDSHpk k r ε lam σ) {g : Mx k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ∀ x ∈ DDsp σ w0, σ g x ∈ DDsp σ w0 := by
  intro x hx
  have hmm : ∀ a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      a * b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    intro a ha b hb
    have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
    have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
    show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
    calc (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.QuantumDeterminants.Hpk k r := by rw [ha', hb']
  unfold DDsp at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨h, hh, rfl⟩ := hy
    have e : σ g (σ h w0) = σ (g * h) w0 := by
      rw [sigma_mul' hds hg hh, ContinuousLinearMap.comp_apply]
    rw [e]
    exact Submodule.subset_span ⟨g * h, hmm g hg h hh, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [map_smul]; exact Submodule.smul_mem _ a hy

theorem l_of_be {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {σ : Mx k r → (H →L[ℂ] H)}
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} {l : H → Wp} {x v : H}
    (hbe : be z c π σ μW μN x v = (innerSL ℂ (l v)).smulRight (l x)) (hlv : l v ≠ 0) :
    l x = ((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹ • (be z c π σ μW μN x v) (l v) := by
  have hn : ((‖l v‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have h0 : ‖l v‖ ≠ 0 := norm_ne_zero_iff.mpr hlv
    exact_mod_cast pow_ne_zero 2 h0
  have key : (be z c π σ μW μN x v) (l v) = ((‖l v‖ ^ 2 : ℝ) : ℂ) • l x := by
    rw [hbe]
    simp [inner_self_eq_norm_sq_to_K]
  rw [key, smul_smul, inv_mul_cancel₀ hn, one_smul]

theorem coef_ext {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hds : PI.UpqRep.IsDSHpk k r ε lam σ) (v x : H) :
    ∃ e : Mx k r → ℂ, Continuous e ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), e g = ⟪v, σ g x⟫_ℂ := by
  obtain ⟨P, ⟨⟨hPu, hPJ⟩, -⟩, hDS⟩ := hds
  obtain ⟨-, -, ⟨-, -, hcontU⟩, -⟩ := hDS
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have key : ∀ g : Mx k r, P⁻¹ * (P * g * P⁻¹) * P = g := fun g => by
    rw [show P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) by simp only [Matrix.mul_assoc],
      h2, Matrix.one_mul, Matrix.mul_one]
  have hφ : Continuous fun g : Mx k r => P * g * P⁻¹ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hcont : ContinuousOn (fun g : Mx k r => σ g x) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
    have hc := (hcontU x).comp hφ.continuousOn (fun _ hg => conj_mem_lemma h1 hPJ hg)
    refine hc.congr fun g _ => ?_
    simp only [Function.comp_apply, key]
  have hid : Continuous fun g : Mx k r => g := continuous_id
  have hcl : IsClosed (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
    show IsClosed {g : Mx k r | gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r}
    exact isClosed_eq ((hid.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hid)
      continuous_const
  let f : C(Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ℂ) :=
    ⟨fun g => ⟪v, σ g x⟫_ℂ, (continuousOn_const.inner hcont).restrict⟩
  haveI : NormalSpace (Mx k r) :=
    inferInstanceAs (NormalSpace (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq hcl f
  exact ⟨⇑G, G.continuous, fun g hg => DFunLike.congr_fun hG ⟨g, hg⟩⟩

theorem uh_mem_measurableSet :
    MeasurableSet {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} := by
  have h0 : Continuous fun x : Formalism.QuantumDeterminants.Mt k r => (Matrix.of x : Mx k r) := continuous_id
  have hc : Continuous fun x : Formalism.QuantumDeterminants.Mt k r =>
      (Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of x :=
    (h0.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul h0
  exact (isClosed_eq hc continuous_const).measurableSet

end Formalism.FourierDecayAlt.P.S3dx4
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem prod_ae {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) :
    ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
  obtain ⟨hWs, -, hWc, -⟩ := hW
  obtain ⟨hNs, -, hNc, -⟩ := hN
  have := hWs; have := hNs
  rw [ae_iff]
  have hsub : {p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r |
      ¬ (Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r)} ⊆
      ({x | Matrix.of x ∉ Formalism.QuantumDeterminants.UWset k r z} ×ˢ Set.univ) ∪
        (Set.univ ×ˢ {x | Matrix.of x ∉ Formalism.QuantumDeterminants.Nset k r}) := by
    intro p hp
    by_cases h1 : Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z
    · exact Or.inr ⟨Set.mem_univ _, fun h2 => hp ⟨h1, h2⟩⟩
    · exact Or.inl ⟨h1, Set.mem_univ _⟩
  refine measure_mono_null hsub (measure_union_null ?_ ?_)
  · rw [Measure.prod_prod, hWc, zero_mul]
  · rw [Measure.prod_prod, hNc, mul_zero]

theorem beInt_norm_le {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {σ : Mx k r → (H →L[ℂ] H)} (hds : PI.UpqRep.IsDSHpk k r ε lam σ)
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    {x v : H} {g : Mx k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    {p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r}
    (hp : Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r) :
    ‖beInt z c π σ (σ g x) v p‖ ≤ ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * g) x⟫_ℂ‖ := by
  have hhn : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
    DDSmoothness.uh_mul hp.1.1 hp.2.1
  have hσ : σ (Matrix.of p.1 * Matrix.of p.2 * g) x = σ (Matrix.of p.1 * Matrix.of p.2) (σ g x) := by
    rw [sigma_mul' hds hhn hg]; rfl
  have hi := (MatrixMultiplicationContinuity.uw_inv hp.1).1
  have hπn : ‖π (Matrix.of p.1)⁻¹‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      (fun w => by rw [MatrixMultiplicationContinuity.piW_unitary hT hπ _ hi w, one_mul])
  have hψ : ‖star (Formalism.QuantumDeterminants.psi k r z c (Matrix.of p.2))‖ = 1 := by
    rw [norm_star]; unfold Formalism.QuantumDeterminants.psi; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  unfold beInt
  rw [norm_smul, norm_mul, hψ, mul_one, hσ]
  exact mul_le_of_le_one_right (norm_nonneg _) hπn

theorem be_enorm_le {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp]
    {σ : Mx k r → (H →L[ℂ] H)} (hds : PI.UpqRep.IsDSHpk k r ε lam σ)
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    {x v : H} {g : Mx k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ‖be z c π σ μW μN (σ g x) v‖ₑ ≤
      ∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * g) x⟫_ℂ‖ₑ ∂(μW.prod μN) := by
  unfold be
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae ?_)
  filter_upwards [prod_ae hW hN] with p hp
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (beInt_norm_le hds hT hπ hg hp)

theorem l1_quotient_integral_bound {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mx k r → (H →L[ℂ] H)} (hds : PI.UpqRep.IsDSHpk k r ε lam σ)
    {z : Fin (2 * r + k + 1) → ℂ} {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    (hGm : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG)
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG (muSof μW μN) νq)
    {x v : H} {C a : ℝ}
    (hC : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖⟪v, σ y x⟫_ℂ‖ ≤ C * B.gN y ^ (-a))
    (hI : Integrable (fun y : Formalism.QuantumDeterminants.Mt k r => B.gN (Matrix.of y) ^ (-a)) μG) :
    ∫⁻ g, (∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) x⟫_ℂ‖ₑ ∂(μW.prod μN)) ∂νq < ⊤ := by
  obtain ⟨e, he, hee⟩ := coef_ext hds v x
  set U : Set (Formalism.QuantumDeterminants.Mt k r) := {y | Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} with hU
  set f : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := U.indicator (fun y => ‖e (Matrix.of y)‖ₑ) with hf
  have hfm : Measurable f := by
    have hc : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => e (Matrix.of y)) :=
      he.comp (show Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r)) from continuous_id)
    have : Measurable (fun y : Formalism.QuantumDeterminants.Mt k r => ‖e (Matrix.of y)‖ₑ) := hc.measurable.enorm
    exact this.indicator uh_mem_measurableSet
  have hφ : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) := by
    have h1 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.1 : Mx k r)) := continuous_fst
    have h2 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.2 : Mx k r)) := continuous_snd
    exact h1.matrix_mul h2
  have hmul : ∀ g : Formalism.QuantumDeterminants.Mt k r, Measurable (fun s : Formalism.QuantumDeterminants.Mt k r =>
      f (fun i j => (Matrix.of s * Matrix.of g) i j)) := by
    intro g
    have : Continuous (fun s : Formalism.QuantumDeterminants.Mt k r =>
        (fun i j => (Matrix.of s * Matrix.of g) i j : Formalism.QuantumDeterminants.Mt k r)) := by
      have h1 : Continuous (fun s : Formalism.QuantumDeterminants.Mt k r => (Matrix.of s : Mx k r)) := continuous_id
      exact h1.matrix_mul continuous_const
    exact hfm.comp this.measurable
  have hfacts := DDSmoothness.muSof_facts hW hN
  have hae := DDSmoothness.ae_UH_of_quot hGm.2.2.1 hfacts.1 hfacts.2 hq

  have step1 : ∀ᵐ g ∂νq, (∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) x⟫_ℂ‖ₑ ∂(μW.prod μN)) =
      ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of g) i j) ∂(muSof μW μN) := by
    filter_upwards [hae] with g hg
    unfold muSof
    rw [lintegral_map (hmul g) hφ.measurable]
    apply lintegral_congr_ae
    filter_upwards [prod_ae hW hN] with p hp
    have hhn : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hp.1.1 hp.2.1
    have hin : Matrix.of p.1 * Matrix.of p.2 * Matrix.of g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
      DDSmoothness.uh_mul hhn hg
    have key : (fun i j => (Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) *
        Matrix.of g) i j : Formalism.QuantumDeterminants.Mt k r) ∈ U := hin
    show ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) x⟫_ℂ‖ₑ =
      f (fun i j => (Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) * Matrix.of g) i j)
    rw [hf, Set.indicator_of_mem key]
    show _ = ‖e (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g)‖ₑ
    rw [hee _ hin]
  rw [lintegral_congr_ae step1, ← hq f hfm]

  have hb : ∀ᵐ y ∂μG, f y ≤ ‖C * B.gN (Matrix.of y) ^ (-a)‖ₑ := by
    have hGc : ∀ᵐ y ∂μG, Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
      rw [ae_iff]; simpa using hGm.2.2.1
    filter_upwards [hGc] with y hy
    simp only [hf]
    rw [Set.indicator_of_mem (show y ∈ U from hy), hee _ hy, ← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal ((hC _ hy).trans (le_abs_self _) |>.trans (le_of_eq (Real.norm_eq_abs _).symm))
  calc ∫⁻ y, f y ∂μG ≤ ∫⁻ y, ‖C * B.gN (Matrix.of y) ^ (-a)‖ₑ ∂μG := lintegral_mono_ae hb
    _ < ⊤ := (hI.const_mul C).hasFiniteIntegral

end Formalism.FourierDecayAlt.P.S3dx4
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

theorem ag_lt_a {k r : ℕ} {h : ℝ} (hG : GapOK k r h) : AG k r < aOf r h := by
  have h1 := hG.2.2.2
  have h2 := ag_nonneg k r
  have h3 : 0 ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  linarith

theorem phiReg_of (hSch : SchurH) (hNI : NormIdSm) (hGG : GrowthG) (hDD : DecDD) (hBC : BeConv) :
    More.PhiReg := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS l hbe x hx
  have hS' := hS
  obtain ⟨hl, hds, -, hG, hw0, -, hT, -, hπ, hW, hN, hGm, hq⟩ := hS'
  have hxs : x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := DDSmoothness.DD_smooth hIn.2.2.1 hl hds hw0 x hx
  have hfacts := DDSmoothness.muSof_facts hW hN
  have hae := DDSmoothness.ae_UH_of_quot hGm.2.2.1 hfacts.1 hfacts.2 hq
  by_cases hA : ∃ v ∈ DDsp σ w0, l v ≠ 0
  · obtain ⟨v, hv, hlv⟩ := hA
    set cc : ℂ := ((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹ with hcc
    have hlx : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
        l (σ g x) = cc • (be z c π σ μW μN (σ g x) v) (l v) :=
      fun g hg => l_of_be (hbe _ (dd_stable hds hg x hx) v hv) hlv
    refine ⟨?_, ?_, ?_⟩
    · have hc := (hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS).2.2.1 x hxs v (Or.inl hv)
      have hc2 : ContinuousOn (fun g => cc • (ContinuousLinearMap.apply ℂ Wp (l v))
          (be z c π σ μW μN (σ g x) v)) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :=
        ((ContinuousLinearMap.apply ℂ Wp (l v)).continuous.comp_continuousOn hc).const_smul cc
      exact hc2.congr (fun g hg => hlx g hg)
    · obtain ⟨C, hC⟩ := hDD hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x hx v hv
      have hI := hGG k r μG (aOf r h) hGm (ag_lt_a hG)
      have hfin := l1_quotient_integral_bound hds hW hN hGm hq hC hI
      have hb : ∀ᵐ g ∂νq, ((‖l (σ (Matrix.of g) x)‖₊ : ℝ≥0) : ℝ≥0∞) ≤
          (‖cc‖ₑ * ‖l v‖ₑ) * ∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) x⟫_ℂ‖ₑ ∂(μW.prod μN) := by
        filter_upwards [hae] with g hg
        rw [← enorm_eq_nnnorm, hlx _ hg]
        have hbe' := be_enorm_le (c := c) hds hT hπ hW hN (x := x) (v := v) hg
        calc ‖cc • (be z c π σ μW μN (σ (Matrix.of g) x) v) (l v)‖ₑ
            = ‖cc‖ₑ * ‖(be z c π σ μW μN (σ (Matrix.of g) x) v) (l v)‖ₑ := enorm_smul _ _
          _ ≤ ‖cc‖ₑ * (‖be z c π σ μW μN (σ (Matrix.of g) x) v‖ₑ * ‖l v‖ₑ) := by
            gcongr
            exact ContinuousLinearMap.le_opENorm _ _
          _ ≤ ‖cc‖ₑ * ((∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) x⟫_ℂ‖ₑ ∂(μW.prod μN)) *
              ‖l v‖ₑ) := by gcongr
          _ = _ := by ring
      calc ∫⁻ g, ((‖l (σ (Matrix.of g) x)‖₊ : ℝ≥0) : ℝ≥0∞) ∂νq
          ≤ ∫⁻ g, (‖cc‖ₑ * ‖l v‖ₑ) *
              ∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) x⟫_ℂ‖ₑ ∂(μW.prod μN) ∂νq :=
            lintegral_mono_ae hb
        _ = (‖cc‖ₑ * ‖l v‖ₑ) *
              ∫⁻ g, ∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) x⟫_ℂ‖ₑ ∂(μW.prod μN) ∂νq :=
            lintegral_const_mul' _ _ (by simp [ENNReal.mul_eq_top])
        _ < ⊤ := ENNReal.mul_lt_top (by simp [ENNReal.mul_lt_top]) hfin
    · have hN2 := (hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x hxs v (Or.inl hv) (l v)).1
      have hfin : PI.BesselPeriodGGP.l2SG νq (fun g => be z c π σ μW μN (σ g x) v (l v)) < ⊤ := by
        rw [hN2]; exact ENNReal.ofReal_lt_top
      unfold PI.BesselPeriodGGP.l2SG at hfin ⊢
      calc ∫⁻ g, ((‖l (σ (Matrix.of g) x)‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 ∂νq
          = ∫⁻ g, ((‖cc‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 *
              ((‖be z c π σ μW μN (σ (Matrix.of g) x) v (l v)‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 ∂νq := by
            apply lintegral_congr_ae
            filter_upwards [hae] with g hg
            rw [hlx _ hg, nnnorm_smul, ENNReal.coe_mul, mul_pow]
        _ = ((‖cc‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 *
              ∫⁻ g, ((‖be z c π σ μW μN (σ (Matrix.of g) x) v (l v)‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 ∂νq :=
            lintegral_const_mul' _ _ (by simp)
        _ < ⊤ := ENNReal.mul_lt_top (by simp) hfin
  · push Not at hA
    have hz : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), l (σ g x) = 0 :=
      fun g hg => hA _ (dd_stable hds hg x hx)
    refine ⟨?_, ?_, ?_⟩
    · exact (continuousOn_const (c := (0 : Wp))).congr (fun g hg => hz g hg)
    · have : ∫⁻ g, ((‖l (σ (Matrix.of g) x)‖₊ : ℝ≥0) : ℝ≥0∞) ∂νq = 0 := by
        rw [lintegral_congr_ae (g := fun _ => 0) (by filter_upwards [hae] with g hg; simp [hz _ hg])]
        simp
      rw [this]; exact ENNReal.zero_lt_top
    · unfold PI.BesselPeriodGGP.l2SG
      have : ∫⁻ g, ((‖l (σ (Matrix.of g) x)‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 ∂νq = 0 := by
        rw [lintegral_congr_ae (g := fun _ => 0) (by filter_upwards [hae] with g hg; simp [hz _ hg])]
        simp
      rw [this]; exact ENNReal.zero_lt_top

end Formalism.FourierDecayAlt.P.S3dx4
