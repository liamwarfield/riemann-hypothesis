module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvarianceOfConstantFourierCoefficient
public import Formalism.PeriodIntegrals.ExplicitFormulaCounts.BridgeStdAddChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdaptedTriangularBounded

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.HermitianForms.ExistsIsCharAFOfStd
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.AdelicChar

theorem exists_isCharAF_of_std :
    HeckeCharacterZeroLocus.StdAdditiveCharExists → ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F →
      ∃ ψ, IsCharAF F ψ := by
  intro h F _ _ hF
  obtain ⟨ψ, h1, h2, h3, h4, -⟩ := h F hF
  exact ⟨ψ, h1, h2, h3, h4⟩

theorem exists_isCharAF (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyReal F) :
    ∃ ψ, IsCharAF F ψ :=
  exists_isCharAF_of_std PI.Bridge.bridge_stdAddChar F hF

end GlobalTheory.CompanionTheory.AdelicChar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResABound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResATranslate
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallySmall
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ResMu

open Set GlobalTheory.Eis

variable {D : D7} {p : ℕ}

def res (H : G D p → ℝ≥0) (f : G D p → ℂ) (σ : ℝ) (h : G D p) : ℂ :=
  ((σ - p / 2 : ℝ) : ℂ) * eisS (fam H f ((p : ℂ) / 2) (σ : ℂ)) h

def ufil (p : ℕ) : Ultrafilter ℝ := Ultrafilter.of (𝓝[>] ((p : ℝ) / 2))

theorem ufil_le (p : ℕ) : ((ufil p : Ultrafilter ℝ) : Filter ℝ) ≤ 𝓝[>] ((p : ℝ) / 2) := by
  unfold ufil
  exact Ultrafilter.of_le _

def resA (H : G D p → ℝ≥0) (f : G D p → ℂ) (h : G D p) : ℂ :=
  limUnder ((ufil p : Ultrafilter ℝ) : Filter ℝ) fun σ => res H f σ h

theorem abs_pos' (u : (AE D)ˣ) : 0 < absA D u := by
  exact pos_iff_ne_zero.mpr ((Group.isUnit u).map (absA D)).ne_zero

theorem fam_law {n : ℕ} {H : G D n → ℝ≥0} (hH : IsHt H) {χ : (AE D)ˣ →* Circle} {s₁ : ℂ} {φ : G D n → ℂ} (h : IsLaw χ s₁ φ)
    (z : ℂ) : IsLaw χ z (fam H φ s₁ z) := by
  intro q hq a ha g
  have hx : (0:ℝ) < (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) := NNReal.coe_pos.mpr (abs_pos' _)
  have hxne : ((absA D (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  simp only [fam, npow, hH.2.2 q hq a ha g, h q hq a ha g, NNReal.coe_mul, Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg hx.le (NNReal.coe_nonneg _)]
  have e : z + (n : ℂ) / 2 = (z - s₁) + (s₁ + (n : ℂ) / 2) := by ring
  rw [e, Complex.cpow_add (z - s₁) (s₁ + (n : ℂ) / 2) hxne]
  ring

theorem fam_cont {n : ℕ} {H : G D n → ℝ≥0} (hH : IsHt H) {φ : G D n → ℂ} (hφ : Continuous φ) (s₁ : ℂ) :
    Continuous fun u : ℝ × G D n => fam H φ s₁ (u.1 : ℂ) u.2 := by
  unfold fam npow
  refine Continuous.mul (Continuous.cpow ?_ ?_ ?_) (hφ.comp continuous_snd)
  · exact Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (hH.1.comp continuous_snd))
  · exact (Complex.continuous_ofReal.comp continuous_fst).sub continuous_const
  · intro u
    exact Complex.ofReal_mem_slitPlane.mpr (NNReal.coe_pos.mpr (hH.2.1 u.2))

theorem law_sub {n : ℕ} {s : ℂ} {φ φ' : G D n → ℂ} {χ : (AE D)ˣ →* Circle} (h : IsLaw χ s φ) (h' : IsLaw χ s φ') :
    IsLaw χ s (φ - φ') := by
  intro q hq a ha g
  show φ (q * g) - φ' (q * g) = _ * (φ g - φ' g)
  rw [h q hq a ha g, h' q hq a ha g]
  ring

theorem law_right {n : ℕ} {s : ℂ} {φ : G D n → ℂ} {χ : (AE D)ˣ →* Circle} (h : IsLaw χ s φ) (x : G D n) :
    IsLaw χ s (fun g => φ (g * x)) := by
  intro q hq a ha g
  show φ (q * g * x) = _ * φ (g * x)
  rw [mul_assoc]
  exact h q hq a ha (g * x)

theorem law_bound {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {σ : ℝ}
    {s : G D p → ℂ} (hs : IsLaw 1 (σ : ℂ) s) {δ : ℝ} (hδ : ∀ c ∈ C, ‖s c‖ ≤ δ * (H c : ℝ) ^ (σ + p / 2)) (g : G D p) :
    ‖s g‖ ≤ δ * (H g : ℝ) ^ (σ + p / 2) := by
  obtain ⟨q, hq, c, hc, rfl⟩ := hcov g
  obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hq
  have hx : (0:ℝ) < (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) := NNReal.coe_pos.mpr (abs_pos' _)
  have hHc : (0:ℝ) < (H c : ℝ) := NNReal.coe_pos.mpr (hH.2.1 c)
  rw [hs q hq a ha c, hH.2.2 q hq a ha c]
  have e1 : ((σ : ℂ) + (p : ℂ) / 2) = (((σ + p / 2 : ℝ)) : ℂ) := by push_cast; ring
  rw [norm_mul, norm_mul, e1]
  simp only [npow, MonoidHom.one_apply, Circle.coe_one, norm_one, one_mul]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.ofReal_re, NNReal.coe_mul, Real.mul_rpow hx.le hHc.le]
  calc _ ≤ (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ (σ + p / 2) * (δ * (H c : ℝ) ^ (σ + p / 2)) :=
        mul_le_mul_of_nonneg_left (hδ c hc) (Real.rpow_nonneg hx.le _)
    _ = _ := by ring

theorem exists_bound {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {σ : ℝ} {s : G D p → ℂ} (hc : Continuous s) (hs : IsLaw 1 (σ : ℂ) s) :
    ∃ δ : ℝ, ∀ g, ‖s g‖ ≤ δ * (H g : ℝ) ^ (σ + p / 2) := by
  have hcont : ContinuousOn (fun c => ‖s c‖ / (H c : ℝ) ^ (σ + p / 2)) C := by
    refine ContinuousOn.div hc.norm.continuousOn ?_ ?_
    · exact ((NNReal.continuous_coe.comp hH.1).rpow_const (fun c => Or.inl (NNReal.coe_pos.mpr (hH.2.1 c)).ne')).continuousOn
    · intro c _
      exact (Real.rpow_pos_of_pos (NNReal.coe_pos.mpr (hH.2.1 c)) _).ne'
  obtain ⟨δ, hδ⟩ := hC.exists_bound_of_continuousOn hcont
  refine ⟨δ, law_bound hH hcov hs (fun c hc => ?_)⟩
  have hpos := Real.rpow_pos_of_pos (NNReal.coe_pos.mpr (hH.2.1 c)) (σ + p / 2)
  have := hδ c hc
  rw [Real.norm_eq_abs, abs_div, abs_norm, abs_of_pos hpos, div_le_iff₀ hpos] at this
  exact this

theorem eis_bound (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ σ ∈ Ioc ((p : ℝ) / 2) (p / 2 + 1), ∀ h ∈ C, ∀ (s : G D p → ℂ) (δ : ℝ),
      (∀ g, ‖s g‖ ≤ δ * (H g : ℝ) ^ (σ + p / 2)) →
      CosetConv (P D p) (GF D p) s h ∧ (σ - p / 2) * ‖eisS s h‖ ≤ δ * B := by
  obtain ⟨B, hB⟩ := hS D p hp H hH C hC
  refine ⟨max B 0, le_max_right _ _, fun σ hσ h hh s δ hs => ?_⟩
  obtain ⟨hsum, hle⟩ := hB σ hσ h hh
  have hσ0 : 0 < σ - p / 2 := by linarith [hσ.1]
  have hδ : 0 ≤ δ := by
    have h1 := (norm_nonneg _).trans (hs 1)
    have h2 : 0 < (H 1 : ℝ) ^ (σ + p / 2) := Real.rpow_pos_of_pos (NNReal.coe_pos.mpr (hH.2.1 1)) _
    exact le_of_mul_le_mul_right (by rw [zero_mul]; exact h1) h2
  have hbd : ∀ q : GlobalTheory.Eis.Cosets (P D p) (GF D p), ‖GlobalTheory.Eis.term (P D p) (GF D p) s h q‖ ≤ δ * (H (↑(Quotient.out q) * h) : ℝ) ^ (σ + p / 2) := fun q => hs _
  have hconv : CosetConv (P D p) (GF D p) s h := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbd (hsum.mul_left δ)
  refine ⟨hconv, ?_⟩
  have h1 : ‖eisS s h‖ ≤ δ * ∑' q : GlobalTheory.Eis.Cosets (P D p) (GF D p), (H (↑(Quotient.out q) * h) : ℝ) ^ (σ + p / 2) := by
    unfold eisS GlobalTheory.Eis.cosetSum
    refine (norm_tsum_le_tsum_norm hconv).trans ?_
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum hbd hconv (hsum.mul_left δ)
  calc (σ - p / 2) * ‖eisS s h‖ ≤ (σ - p / 2) * (δ * ∑' q : GlobalTheory.Eis.Cosets (P D p) (GF D p), (H (↑(Quotient.out q) * h) : ℝ) ^ (σ + p / 2)) := mul_le_mul_of_nonneg_left h1 hσ0.le
    _ = δ * ((σ - p / 2) * ∑' q : GlobalTheory.Eis.Cosets (P D p) (GF D p), (H (↑(Quotient.out q) * h) : ℝ) ^ (σ + p / 2)) := by ring
    _ ≤ δ * max B 0 := mul_le_mul_of_nonneg_left (hle.trans (le_max_left _ _)) hδ

theorem eis_sub {s s' : G D p → ℂ} {h : G D p} (hc : CosetConv (P D p) (GF D p) s h) (hc' : CosetConv (P D p) (GF D p) s' h) :
    eisS (s - s') h = eisS s h - eisS s' h := by
  have h1 : Summable fun q => GlobalTheory.Eis.term (P D p) (GF D p) s h q := Summable.of_norm hc
  have h2 : Summable fun q => GlobalTheory.Eis.term (P D p) (GF D p) s' h q := Summable.of_norm hc'
  unfold eisS GlobalTheory.Eis.cosetSum
  exact h1.tsum_sub h2

theorem conv_of_section (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {σ : ℝ} (hσ : σ ∈ Ioc ((p : ℝ) / 2) (p / 2 + 1)) {s : G D p → ℂ}
    (hc : Continuous s) (hs : IsLaw 1 (σ : ℂ) s) (h : G D p) : CosetConv (P D p) (GF D p) s h := by
  obtain ⟨δ, hδ⟩ := exists_bound hH hC hcov hc hs
  obtain ⟨B, _, hB⟩ := eis_bound hS hp hH (isCompact_singleton (x := h))
  exact (hB σ hσ h (Set.mem_singleton h) s δ hδ).1

theorem eventually_small {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C) {T : ℝ → G D p → ℂ}
    (hc : ContinuousOn (fun u : ℝ × G D p => T u.1 u.2) (Icc ((p : ℝ) / 2) (p / 2 + 1) ×ˢ univ))
    (h0 : ∀ c, T ((p : ℝ) / 2) c = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ σ in 𝓝[>] ((p : ℝ) / 2), ∀ c ∈ C, ‖T σ c‖ ≤ ε * (H c : ℝ) ^ (σ + p / 2) := by
  have hHpos : ∀ c, (0:ℝ) < (H c : ℝ) := fun c => NNReal.coe_pos.mpr (hH.2.1 c)
  set F : ℝ × G D p → ℝ := fun u => ‖T u.1 u.2‖ / (H u.2 : ℝ) ^ (u.1 + p / 2) with hF
  have hFc : ContinuousOn F (Icc ((p : ℝ) / 2) (p / 2 + 1) ×ˢ univ) := by
    refine ContinuousOn.div hc.norm ?_ ?_
    · exact (Continuous.rpow (NNReal.continuous_coe.comp (hH.1.comp continuous_snd)) (continuous_fst.add continuous_const) (fun u => Or.inl (hHpos u.2).ne')).continuousOn
    · intro u _
      exact (Real.rpow_pos_of_pos (hHpos u.2) _).ne'
  have hP : ∀ c ∈ C, ∀ᶠ z : ℝ × G D p in 𝓝 (((p : ℝ) / 2), c), z.1 ∈ Icc ((p : ℝ) / 2) (p / 2 + 1) → F (z.1, z.2) < ε := by
    intro c _
    have hmem : (((p : ℝ) / 2), c) ∈ Icc ((p : ℝ) / 2) (p / 2 + 1) ×ˢ (univ : Set (G D p)) := ⟨⟨le_rfl, by linarith⟩, mem_univ _⟩
    have ht := (hFc _ hmem).tendsto
    have h0' : F (((p : ℝ) / 2), c) = 0 := by simp [hF, h0]
    rw [h0'] at ht
    have hh := ht.eventually (gt_mem_nhds hε)
    rw [eventually_nhdsWithin_iff] at hh
    exact hh.mono fun z hz h1 => hz ⟨h1, mem_univ _⟩
  have hev := hC.eventually_forall_of_forall_eventually (P := fun σ c => σ ∈ Icc ((p : ℝ) / 2) (p / 2 + 1) → F (σ, c) < ε) hP
  filter_upwards [hev.filter_mono nhdsWithin_le_nhds, Ioc_mem_nhdsGT (show (p : ℝ) / 2 < p / 2 + 1 by linarith)] with σ hσ hI c hc
  have := hσ c hc (Ioc_subset_Icc_self hI)
  exact ((div_lt_iff₀ (Real.rpow_pos_of_pos (hHpos c) _)).mp this).le

theorem ev_Ioc (p : ℕ) : ∀ᶠ σ in 𝓝[>] ((p : ℝ) / 2), σ ∈ Ioc ((p : ℝ) / 2) (p / 2 + 1) := by
  exact Ioc_mem_nhdsGT (by linarith)

theorem tendsto_diff (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {S S' : ℝ → G D p → ℂ}
    (hc : ContinuousOn (fun u : ℝ × G D p => S u.1 u.2) (Icc ((p : ℝ) / 2) (p / 2 + 1) ×ˢ univ))
    (hc' : ContinuousOn (fun u : ℝ × G D p => S' u.1 u.2) (Icc ((p : ℝ) / 2) (p / 2 + 1) ×ˢ univ))
    (hl : ∀ σ ∈ Icc ((p : ℝ) / 2) (p / 2 + 1), IsLaw 1 (σ : ℂ) (S σ))
    (hl' : ∀ σ ∈ Icc ((p : ℝ) / 2) (p / 2 + 1), IsLaw 1 (σ : ℂ) (S' σ))
    (h0 : S ((p : ℝ) / 2) = S' ((p : ℝ) / 2)) :
    Tendsto (fun σ : ℝ => ((σ - p / 2 : ℝ) : ℂ) * (eisS (S σ) 1 - eisS (S' σ) 1)) (𝓝[>] ((p : ℝ) / 2)) (𝓝 0) := by
  obtain ⟨B, hB0, hB⟩ := eis_bound hS hp hH (isCompact_singleton (x := (1 : G D p)))
  have hcont : ∀ σ ∈ Icc ((p : ℝ) / 2) (p / 2 + 1), Continuous (S σ) := fun σ hσ =>
    hc.comp_continuous (f := fun c : G D p => (σ, c)) (by fun_prop) (fun c => ⟨hσ, mem_univ _⟩)
  have hcont' : ∀ σ ∈ Icc ((p : ℝ) / 2) (p / 2 + 1), Continuous (S' σ) := fun σ hσ =>
    hc'.comp_continuous (f := fun c : G D p => (σ, c)) (by fun_prop) (fun c => ⟨hσ, mem_univ _⟩)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε' : 0 < ε / (B + 1) := div_pos hε (by linarith)
  have hsmall := eventually_small (T := fun σ => S σ - S' σ) hH hC (hc.sub hc') (fun c => by simp [h0]) hε'
  filter_upwards [hsmall, ev_Ioc p] with σ hσs hσ
  have hσI : σ ∈ Icc ((p : ℝ) / 2) (p / 2 + 1) := Ioc_subset_Icc_self hσ
  have hlaw : IsLaw 1 (σ : ℂ) (S σ - S' σ) := law_sub (hl σ hσI) (hl' σ hσI)
  have hall := law_bound hH hcov hlaw hσs
  obtain ⟨_, hb⟩ := hB σ hσ 1 (Set.mem_singleton _) (S σ - S' σ) (ε / (B + 1)) hall
  have hconv := conv_of_section hS hp hH hC hcov hσ (hcont σ hσI) (hl σ hσI) 1
  have hconv' := conv_of_section hS hp hH hC hcov hσ (hcont' σ hσI) (hl' σ hσI) 1
  rw [dist_zero_right, ← eis_sub hconv hconv', norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hσ.1])]
  calc _ ≤ ε / (B + 1) * B := hb
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith

theorem fam_bound {H : G D p → ℝ≥0} (hH : IsHt H) {f : G D p → ℂ} {δ : ℝ} (hf : ∀ g, ‖f g‖ ≤ δ * (H g : ℝ) ^ p) (σ : ℝ) (g : G D p) :
    ‖fam H f ((p : ℂ) / 2) (σ : ℂ) g‖ ≤ δ * (H g : ℝ) ^ (σ + p / 2) := by
  have hHg : (0:ℝ) < (H g : ℝ) := NNReal.coe_pos.mpr (hH.2.1 g)
  unfold fam npow
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hHg]
  have hre : ((σ : ℂ) - (p : ℂ) / 2).re = σ - p / 2 := by simp
  rw [hre]
  calc _ ≤ (H g : ℝ) ^ (σ - p / 2) * (δ * (H g : ℝ) ^ p) := mul_le_mul_of_nonneg_left (hf g) (Real.rpow_nonneg hHg.le _)
    _ = δ * ((H g : ℝ) ^ (σ - p / 2) * (H g : ℝ) ^ ((p : ℕ) : ℝ)) := by rw [Real.rpow_natCast]; ring
    _ = δ * (H g : ℝ) ^ (σ + p / 2) := by
      rw [← Real.rpow_add hHg]
      congr 2
      ring

theorem rho_law {f : G D p → ℂ} (hf : IsRho f) : IsLaw 1 (((p : ℝ) / 2 : ℝ) : ℂ) f := by
  have e : ((((p : ℝ) / 2 : ℝ)) : ℂ) = (p : ℂ) / 2 := by push_cast; ring
  rw [e]
  exact hf.2

theorem rho_bound {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) :
    ∃ δ : ℝ, ∀ g, ‖f g‖ ≤ δ * (H g : ℝ) ^ p := by
  obtain ⟨δ, hδ⟩ := exists_bound hH hC hcov hf.1 (rho_law hf)
  refine ⟨δ, fun g => ?_⟩
  have := hδ g
  have e : ((p : ℝ) / 2 + p / 2) = ((p : ℕ) : ℝ) := by ring
  rw [e, Real.rpow_natCast] at this
  exact this

theorem res_bound (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C' : Set (G D p)} (hC' : IsCompact C') :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (f : G D p → ℂ) (δ : ℝ), (∀ g, ‖f g‖ ≤ δ * (H g : ℝ) ^ p) →
      ∀ σ ∈ Ioc ((p : ℝ) / 2) (p / 2 + 1), ∀ h ∈ C', ‖res H f σ h‖ ≤ δ * B := by
  obtain ⟨B, hB0, hB⟩ := eis_bound hS hp hH hC'
  refine ⟨B, hB0, fun f δ hf σ hσ h hh => ?_⟩
  obtain ⟨_, hb⟩ := hB σ hσ h hh _ δ (fam_bound hH hf σ)
  unfold res
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hσ.1])]
  exact hb

theorem res_tendsto (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) (h : G D p) :
    Tendsto (fun σ => res H f σ h) ((ufil p : Ultrafilter ℝ) : Filter ℝ) (𝓝 (resA H f h)) := by
  obtain ⟨δ, hδ⟩ := rho_bound hH hC hcov hf
  obtain ⟨B, _, hB⟩ := res_bound hS hp hH (isCompact_singleton (x := h))
  have hev : ∀ᶠ σ in ((ufil p : Ultrafilter ℝ) : Filter ℝ), res H f σ h ∈ Metric.closedBall (0 : ℂ) (δ * B) := by
    refine Filter.Eventually.filter_mono (ufil_le p) ((ev_Ioc p).mono fun σ hσ => ?_)
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hB f δ hδ σ hσ h (Set.mem_singleton _)
  obtain ⟨x, _, hx⟩ := (isCompact_closedBall (0 : ℂ) (δ * B)).ultrafilter_le_nhds ((ufil p).map fun σ => res H f σ h)
    (by rw [Ultrafilter.coe_map, Filter.le_principal_iff]; exact hev)
  unfold resA
  exact tendsto_nhds_limUnder ⟨x, by rw [Ultrafilter.coe_map] at hx; exact hx⟩

end GlobalTheory.CompanionTheory.ResMu
end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ResMu

open Set GlobalTheory.Eis

variable {D : D7} {p : ℕ}

theorem law_ratInv {n : ℕ} {z : ℂ} {s : G D n → ℂ} (hs : IsLaw 1 z s) : LeftInv (P D n ⊓ GF D n) s := fun γ hγ g => by
  obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hγ.1
  obtain ⟨u, hu⟩ := GlobalTheory.StdUnn.LeftInvSect.det_rat hγ.2 a ha
  have h1 : absA D (Units.map (incA D).toMonoidHom u) = 1 := absE_inclR u
  rw [hs γ hγ.1 a ha g, hu, h1]
  simp

theorem rho_right {f : G D p → ℂ} (hf : IsRho f) (x : G D p) : IsRho fun g => f (g * x) :=
  ⟨hf.1.comp (continuous_id.mul continuous_const), law_right hf.2 x⟩

theorem fam_law_real {H : G D p → ℝ≥0} (hH : IsHt H) {f : G D p → ℂ} (hf : IsRho f) (σ : ℝ) :
    IsLaw 1 (σ : ℂ) (fam H f ((p : ℂ) / 2) (σ : ℂ)) := fam_law hH hf.2 σ

theorem fam_cont_at {H : G D p → ℝ≥0} (hH : IsHt H) {f : G D p → ℂ} (hf : Continuous f) (s₁ : ℂ) (σ : ℝ) :
    Continuous (fam H f s₁ (σ : ℂ)) :=
  (fam_cont hH hf s₁).comp (f := fun g : G D p => ((σ, g) : ℝ × G D p)) (by fun_prop)

theorem fam_at (H : G D p → ℝ≥0) (f : G D p → ℂ) : fam H f ((p : ℂ) / 2) (((p : ℝ) / 2 : ℝ) : ℂ) = f := by
  funext g
  have : ((((p : ℝ) / 2 : ℝ) : ℂ)) - (p : ℂ) / 2 = 0 := by push_cast; ring
  simp [fam, this]

theorem res_leftInv {H : G D p → ℝ≥0} (hH : IsHt H) {f : G D p → ℂ} (hf : IsRho f) (σ : ℝ) :
    LeftInv (GF D p) (res H f σ) := fun γ hγ g => by
  simp only [res, eisS]
  rw [leftInv_cosetSum (law_ratInv (fam_law_real hH hf σ)) γ hγ g]

theorem eis_right (s : G D p → ℂ) (x : G D p) : eisS s x = eisS (fun g => s (g * x)) 1 := by
  simp only [eisS]
  rw [cosetSum_mul_right, one_mul]

theorem res_equi (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) (x : G D p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x' in 𝓝 x, ∀ σ ∈ Ioc ((p : ℝ) / 2) (p / 2 + 1), ‖res H f σ x' - res H f σ x‖ ≤ ε := by
  obtain ⟨B, hB0, hB⟩ := eis_bound hS hp hH (isCompact_singleton (x := (1 : G D p)))
  have hK : IsCompact (Icc ((p : ℝ) / 2) (p / 2 + 1) ×ˢ C) := isCompact_Icc.prod hC
  have hε' : 0 < ε / (2 * (B + 1)) := by positivity
  have hfc := fam_cont hH hf.1 ((p : ℂ) / 2)
  have hev : ∀ᶠ x' in 𝓝 x, ∀ y ∈ Icc ((p : ℝ) / 2) (p / 2 + 1) ×ˢ C,
      ‖fam H f ((p : ℂ) / 2) (y.1 : ℂ) (y.2 * x') - fam H f ((p : ℂ) / 2) (y.1 : ℂ) (y.2 * x)‖ <
        ε / (2 * (B + 1)) * (H y.2 : ℝ) ^ (y.1 + p / 2) := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have c1 : Continuous fun u : G D p × (ℝ × G D p) => fam H f ((p : ℂ) / 2) (u.2.1 : ℂ) (u.2.2 * u.1) :=
      hfc.comp (f := fun u : G D p × (ℝ × G D p) => ((u.2.1, u.2.2 * u.1) : ℝ × G D p)) (by fun_prop)
    have c2 : Continuous fun u : G D p × (ℝ × G D p) => fam H f ((p : ℂ) / 2) (u.2.1 : ℂ) (u.2.2 * x) :=
      hfc.comp (f := fun u : G D p × (ℝ × G D p) => ((u.2.1, u.2.2 * x) : ℝ × G D p)) (by fun_prop)
    have c3 : Continuous fun u : G D p × (ℝ × G D p) => ε / (2 * (B + 1)) * (H u.2.2 : ℝ) ^ (u.2.1 + p / 2) :=
      continuous_const.mul ((NNReal.continuous_coe.comp (hH.1.comp (continuous_snd.comp continuous_snd))).rpow
        ((continuous_fst.comp continuous_snd).add continuous_const) fun u => Or.inl (NNReal.coe_pos.2 (hH.2.1 _)).ne')
    refine ((c1.sub c2).norm.continuousAt.eventually_lt c3.continuousAt ?_)
    simp only [Pi.sub_apply, sub_self, norm_zero]
    exact mul_pos hε' (Real.rpow_pos_of_pos (NNReal.coe_pos.2 (hH.2.1 _)) _)
  filter_upwards [hev] with x' hx' σ hσ
  have hI' : σ ∈ Icc ((p : ℝ) / 2) (p / 2 + 1) := ⟨hσ.1.le, hσ.2⟩
  have hl := fam_law_real hH hf σ
  have hc := fam_cont_at hH hf.1 ((p : ℂ) / 2) σ
  have hct : ∀ y : G D p, Continuous fun g => fam H f ((p : ℂ) / 2) (σ : ℂ) (g * y) := fun y =>
    hc.comp (continuous_id.mul continuous_const)
  have hb := law_bound hH hcov (law_sub (law_right hl x') (law_right hl x)) (δ := ε / (2 * (B + 1))) (fun c hc =>
    (hx' (σ, c) ⟨hI', hc⟩).le)
  have hf' := (hB σ hσ 1 rfl _ _ hb).2
  rw [eis_sub (conv_of_section hS hp hH hC hcov hσ (hct x') (law_right hl x') 1)
    (conv_of_section hS hp hH hC hcov hσ (hct x) (law_right hl x) 1), ← eis_right, ← eis_right] at hf'
  have e : res H f σ x' - res H f σ x =
      ((σ - p / 2 : ℝ) : ℂ) * (eisS (fam H f ((p : ℂ) / 2) (σ : ℂ)) x' - eisS (fam H f ((p : ℂ) / 2) (σ : ℂ)) x) := by
    simp only [res]; ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith [hσ.1])]
  have : ε / (2 * (B + 1)) * B ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

theorem res_cont (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) {σ : ℝ}
    (hσ : σ ∈ Ioc ((p : ℝ) / 2) (p / 2 + 1)) : Continuous (res H f σ) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [res_equi hS hp hH hC hcov hf x (half_pos hε)] with x' hx'
  rw [dist_eq_norm]
  linarith [hx' σ hσ]

theorem resA_near (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) (x : G D p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x' in 𝓝 x, ‖resA H f x' - resA H f x‖ ≤ ε := by
  filter_upwards [res_equi hS hp hH hC hcov hf x hε] with x' hx'
  have h1 := ((res_tendsto hS hp hH hC hcov hf x').sub (res_tendsto hS hp hH hC hcov hf x)).norm
  refine le_of_tendsto h1 ?_
  refine ufil_le p ?_
  filter_upwards [ev_Ioc p] with σ hσ using hx' σ hσ

theorem resA_cont (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) : Continuous (resA H f) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [resA_near hS hp hH hC hcov hf x (half_pos hε)] with x' hx'
  rw [dist_eq_norm]
  linarith

theorem resA_leftInv (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) : LeftInv (GF D p) (resA H f) := fun γ hγ g => by
  refine tendsto_nhds_unique (res_tendsto hS hp hH hC hcov hf (γ * g)) ?_
  have := res_tendsto hS hp hH hC hcov hf g
  refine this.congr fun σ => ?_
  rw [res_leftInv hH hf σ γ hγ g]

theorem resA_unif (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) {C' : Set (G D p)} (hC' : IsCompact C')
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ σ in ((ufil p : Ultrafilter ℝ) : Filter ℝ), ∀ c ∈ C', ‖res H f σ c - resA H f c‖ ≤ ε := by
  refine hC'.induction_on (p := fun S => ∀ᶠ σ in ((ufil p : Ultrafilter ℝ) : Filter ℝ), ∀ c ∈ S, ‖res H f σ c - resA H f c‖ ≤ ε)
    (by simp) (fun s t hst h => h.mono fun σ hσ c hc => hσ c (hst hc))
    (fun s t hs ht => by
      filter_upwards [hs, ht] with σ h1 h2 c hc
      exact hc.elim (h1 c) (h2 c)) fun x _ => ?_
  have hε3 : 0 < ε / 3 := by positivity
  refine ⟨_, mem_nhdsWithin_of_mem_nhds ((res_equi hS hp hH hC hcov hf x hε3).and (resA_near hS hp hH hC hcov hf x hε3)), ?_⟩
  have h1 : ∀ᶠ σ in ((ufil p : Ultrafilter ℝ) : Filter ℝ), ‖res H f σ x - resA H f x‖ < ε / 3 := by
    have := (res_tendsto hS hp hH hC hcov hf x)
    rw [Metric.tendsto_nhds] at this
    filter_upwards [this _ hε3] with σ hσ
    rwa [dist_eq_norm] at hσ
  filter_upwards [h1, ufil_le p (ev_Ioc p)] with σ hσ hI c hc
  have a1 := hc.1 σ hI
  have a2 := hc.2
  calc ‖res H f σ c - resA H f c‖ = ‖(res H f σ c - res H f σ x) + (res H f σ x - resA H f x) - (resA H f c - resA H f x)‖ := by
        congr 1; ring
    _ ≤ ‖res H f σ c - res H f σ x‖ + ‖res H f σ x - resA H f x‖ + ‖resA H f c - resA H f x‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ ε := by linarith

theorem resA_translate (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) (x : G D p) :
    resA H f x = resA H (fun g => f (g * x)) 1 := by
  have hfx := rho_right hf x
  have hd := tendsto_diff hS hp hH hC hcov
    (S := fun σ g => fam H f ((p : ℂ) / 2) (σ : ℂ) (g * x)) (S' := fun σ => fam H (fun g => f (g * x)) ((p : ℂ) / 2) (σ : ℂ))
    ((fam_cont hH hf.1 _).comp (f := fun u : ℝ × G D p => ((u.1, u.2 * x) : ℝ × G D p)) (by fun_prop)).continuousOn
    (fam_cont hH hfx.1 _).continuousOn
    (fun σ _ => law_right (fam_law_real hH hf σ) x) (fun σ _ => fam_law_real hH hfx σ)
    (by simp only [fam_at])
  have h1 := (hd.mono_left (ufil_le p)).add (res_tendsto hS hp hH hC hcov hfx 1)
  rw [zero_add] at h1
  refine tendsto_nhds_unique (res_tendsto hS hp hH hC hcov hf x) (h1.congr fun σ => ?_)
  simp only [res]
  rw [eis_right (fam H f ((p : ℂ) / 2) (σ : ℂ)) x]
  ring

end GlobalTheory.CompanionTheory.ResMu
end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ResMu

open Set GlobalTheory.Eis

variable {D : D7} {p : ℕ}

theorem resA_lim (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) (f : ℝ → G D p → ℂ)
    (hc : ContinuousOn (fun u : ℝ × G D p => f u.1 u.2) (Icc ((p : ℝ) / 2) (p / 2 + 1) ×ˢ univ))
    (hl : ∀ σ ∈ Icc ((p : ℝ) / 2) (p / 2 + 1), IsLaw 1 (σ : ℂ) (f σ)) (a : ℂ)
    (ha : Tendsto (fun σ : ℝ => ((σ - p / 2 : ℝ) : ℂ) * eisS (f σ) 1) (𝓝[>] ((p : ℝ) / 2)) (𝓝 a)) :
    IsRho (f (p / 2)) ∧ a = resA H (f (p / 2)) 1 := by
  have hm : (p : ℝ) / 2 ∈ Icc ((p : ℝ) / 2) (p / 2 + 1) := ⟨le_rfl, by linarith⟩
  have hc0 : Continuous (f ((p : ℝ) / 2)) :=
      ContinuousOn.comp_continuous (f := fun g : G D p => (((p : ℝ) / 2, g) : ℝ × G D p)) hc
        (continuous_const.prodMk continuous_id) fun g => ⟨hm, mem_univ _⟩
  have h2 := hl _ hm
  have e : ((((p : ℝ) / 2 : ℝ)) : ℂ) = (p : ℂ) / 2 := by push_cast; ring
  rw [e] at h2
  have hf0 : IsRho (f (p / 2)) := And.intro hc0 h2
  refine ⟨hf0, ?_⟩
  have hc' : ContinuousOn (fun u : ℝ × G D p => fam H (f (p / 2)) ((p : ℂ) / 2) (u.1 : ℂ) u.2) (Icc ((p : ℝ) / 2) (p / 2 + 1) ×ˢ univ) :=
    (fam_cont hH hf0.1 _).continuousOn
  have h00 : f ((p : ℝ) / 2) = (fun σ : ℝ => fam H (f (p / 2)) ((p : ℂ) / 2) (σ : ℂ)) ((p : ℝ) / 2) := (fam_at H (f (p / 2))).symm
  have hd := tendsto_diff hS hp hH hC hcov (S := f) (S' := fun σ => fam H (f (p / 2)) ((p : ℂ) / 2) (σ : ℂ)) hc
    hc' hl (fun σ _ => fam_law_real hH hf0 σ) h00
  have h1 := (ha.sub hd).mono_left (ufil_le p)
  rw [sub_zero] at h1
  have h3 : Tendsto (fun σ => res H (f (p / 2)) σ 1) ((ufil p : Ultrafilter ℝ) : Filter ℝ) (𝓝 a) := by
    refine h1.congr fun σ => ?_
    simp only [res]
    ring
  exact tendsto_nhds_unique h3 (res_tendsto hS hp hH hC hcov hf0 1)

theorem rho_add {f f' : G D p → ℂ} (hf : IsRho f) (hf' : IsRho f') : IsRho (f + f') := by
  refine ⟨hf.1.add hf'.1, fun q hq a ha g => ?_⟩
  simp only [Pi.add_apply, hf.2 q hq a ha g, hf'.2 q hq a ha g]; ring

theorem rho_smul {f : G D p → ℂ} (hf : IsRho f) (c : ℂ) : IsRho (c • f) := by
  refine ⟨continuous_const.smul hf.1, fun q hq a ha g => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, hf.2 q hq a ha g]; ring

theorem fam_add (H : G D p → ℝ≥0) (f f' : G D p → ℂ) (s z : ℂ) : fam H (f + f') s z = fam H f s z + fam H f' s z := by
  funext g; simp [fam, mul_add]

theorem fam_smul (H : G D p → ℝ≥0) (f : G D p → ℂ) (c s z : ℂ) : fam H (c • f) s z = c • fam H f s z := by
  funext g; simp only [fam, Pi.smul_apply, smul_eq_mul]; ring

theorem resA_add (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f f' : G D p → ℂ} (hf : IsRho f) (hf' : IsRho f') (h : G D p) :
    resA H (f + f') h = resA H f h + resA H f' h := by
  refine tendsto_nhds_unique (res_tendsto hS hp hH hC hcov (rho_add hf hf') h) ?_
  refine ((res_tendsto hS hp hH hC hcov hf h).add (res_tendsto hS hp hH hC hcov hf' h)).congr' ?_
  refine ufil_le p ?_
  filter_upwards [ev_Ioc p] with σ hσ
  have c1 := conv_of_section hS hp hH hC hcov hσ (fam_cont_at hH hf.1 _ σ) (fam_law_real hH hf σ) h
  have c2 := conv_of_section hS hp hH hC hcov hσ (fam_cont_at hH hf'.1 _ σ) (fam_law_real hH hf' σ) h
  simp only [res, fam_add, eisS]
  rw [cosetSum_add c1 c2]; ring

theorem resA_smul (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) (c : ℂ) (h : G D p) :
    resA H (c • f) h = c * resA H f h := by
  refine tendsto_nhds_unique (res_tendsto hS hp hH hC hcov (rho_smul hf c) h) ?_
  refine ((res_tendsto hS hp hH hC hcov hf h).const_mul c).congr fun σ => ?_
  simp only [res, fam_smul, eisS]
  rw [cosetSum_smul]; ring

theorem npow_real {r : ℝ≥0} (σ : ℝ) : npow r ((σ : ℂ) - (p : ℂ) / 2) = (((r : ℝ) ^ (σ - p / 2) : ℝ) : ℂ) := by
  rw [npow, Complex.ofReal_cpow r.coe_nonneg]; push_cast; rfl

theorem resA_pos (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f)
    (hpos : ∀ g, 0 ≤ (f g).re ∧ (f g).im = 0) (h : G D p) : 0 ≤ (resA H f h).re ∧ (resA H f h).im = 0 := by
  have hT := res_tendsto hS hp hH hC hcov hf h
  have hev : ∀ᶠ σ in ((ufil p : Ultrafilter ℝ) : Filter ℝ), 0 ≤ (res H f σ h).re ∧ (res H f σ h).im = 0 := by
    refine ufil_le p ?_
    filter_upwards [ev_Ioc p] with σ hσ
    have c1 := conv_of_section hS hp hH hC hcov hσ (fam_cont_at hH hf.1 _ σ) (fam_law_real hH hf σ) h
    have hsum : Summable (term (P D p) (GF D p) (fam H f ((p : ℂ) / 2) (σ : ℂ)) h) := c1.of_norm
    have hterm : ∀ q, 0 ≤ (term (P D p) (GF D p) (fam H f ((p : ℂ) / 2) (σ : ℂ)) h q).re ∧
        (term (P D p) (GF D p) (fam H f ((p : ℂ) / 2) (σ : ℂ)) h q).im = 0 := fun q => by
      simp only [term, fam]
      rw [npow_real, Complex.re_ofReal_mul, Complex.im_ofReal_mul, (hpos _).2, mul_zero]
      exact ⟨mul_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _) (hpos _).1, rfl⟩
    have e1 : (eisS (fam H f ((p : ℂ) / 2) (σ : ℂ)) h).re ≥ 0 := by
      simp only [eisS, cosetSum]
      rw [Complex.re_tsum hsum]
      exact tsum_nonneg fun q => (hterm q).1
    have e2 : (eisS (fam H f ((p : ℂ) / 2) (σ : ℂ)) h).im = 0 := by
      simp only [eisS, cosetSum]
      rw [Complex.im_tsum hsum]
      simp only [hterm, tsum_zero]
    simp only [res]
    rw [Complex.re_ofReal_mul, Complex.im_ofReal_mul, e2, mul_zero]
    exact ⟨mul_nonneg (by linarith [hσ.1]) e1, rfl⟩
  have hre := (Complex.continuous_re.tendsto _).comp hT
  have him := (Complex.continuous_im.tendsto _).comp hT
  exact ⟨ge_of_tendsto hre (hev.mono fun σ h => h.1),
    tendsto_nhds_unique him (tendsto_const_nhds.congr' (hev.mono fun σ h => h.2.symm))⟩

theorem resA_bound (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) (H' : G D p → ℝ≥0) (hH' : IsHt H') :
    ∃ K : ℝ, ∀ f, IsRho f → ∀ B : ℝ, (∀ g, ‖f g‖ ≤ B * (H' g : ℝ) ^ p) → ‖resA H f 1‖ ≤ K * B := by
  have hs : IsRho fun g => npow (H' g) (p : ℂ) := by
    refine ⟨continuous_npow hH'.1 hH'.2.1 _, fun q hq a ha g => ?_⟩
    show npow (H' (q * g)) (p : ℂ) = _ * npow (absA D _) ((p : ℂ) / 2 + (p : ℂ) / 2) * npow (H' g) (p : ℂ)
    rw [hH'.2.2 q hq a ha g, npow_mul, show (p : ℂ) / 2 + (p : ℂ) / 2 = p by ring]
    simp
  obtain ⟨δ, hδ⟩ := rho_bound hH hC hcov hs
  have hle : ∀ g, (H' g : ℝ) ^ p ≤ δ * (H g : ℝ) ^ p := fun g => by
    have := hδ g
    rwa [norm_npow (hH'.2.1 g), show ((p : ℂ)).re = (p : ℝ) by simp, Real.rpow_natCast] at this
  obtain ⟨B₁, -, hB₁⟩ := res_bound hS hp hH (isCompact_singleton (x := (1 : G D p)))
  refine ⟨δ * B₁, fun f hf B hB => ?_⟩
  have hB0 : 0 ≤ B := by
    have h1 := (norm_nonneg _).trans (hB 1)
    exact nonneg_of_mul_nonneg_left h1 (pow_pos (NNReal.coe_pos.2 (hH'.2.1 1)) p)
  have hf2 : ∀ g, ‖f g‖ ≤ (B * δ) * (H g : ℝ) ^ p := fun g =>
    (hB g).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hle g) hB0)
  have hlim := (res_tendsto hS hp hH hC hcov hf 1).norm
  refine le_of_tendsto hlim ?_
  refine ufil_le p ?_
  filter_upwards [ev_Ioc p] with σ hσ
  have := hB₁ f _ hf2 σ hσ 1 rfl
  calc _ ≤ B * δ * B₁ := this
    _ = _ := by ring

end GlobalTheory.CompanionTheory.ResMu
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialCoefficientRankZero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialCoefficientRankZero
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.PcZero

theorem blockMatrix_zero {R : Type} [Zero R] {p : ℕ} (hn : 0 + p = p) (a : Matrix (Fin 0) (Fin 0) R)
    (b : Matrix (Fin 0) (Fin p) R) (c : Matrix (Fin p) (Fin 0) R) : bl hn a b c 0 = 0 := by
  ext i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective j
  rcases i with i | i
  · exact i.elim0
  rcases j with j | j
  · exact j.elim0
  simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]

theorem nzx_eq_one {D : D7} {p : ℕ} {hn : 0 + p = p} (M : Maps D hn) (z : hermA D 0) (x : Mx D 0 p) :
    M.nzx z x = 1 := by
  apply Subtype.ext
  apply Units.ext
  have h : mat (M.nzx z x) = 1 := by
    rw [M.nzx_mat, blockMatrix_zero]
    unfold blk4
    rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
  exact h

theorem chz_eq_one {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D 0) (z : hermA D 0) : chz ψ b₀ z = 1 := by
  unfold chz halfTr trA
  simp [Matrix.trace]

theorem zc_eq {D : D7} {p : ℕ} {hn : 0 + p = p} (M : Maps D hn) (m : Meas D 0 p) (ψ : AddChar (AF D.host.F) ℂ)
    (b₀ : HermE D 0) (F : G D p → ℂ) (g : G D p) : zc M m ψ b₀ F g = F g := by
  unfold zc
  simp only [nzx_eq_one, chz_eq_one, one_mul, map_one, mul_one]
  rw [setIntegral_const, Measure.real, m.hz.2.2]
  simp

theorem pc_eq : ∀ (D : D7) (p : ℕ) (hn : 0 + p = p) (M : Maps D hn) (m : Meas D 0 p) (ψ : AddChar (AF D.host.F) ℂ)
    (b₀ : HermE D 0) (F : G D p → ℂ) (g : G D p), pc M m ψ b₀ F g = F g := by
  intro D p hn M m ψ b₀ F g
  unfold PositivityTheory.Rg.Rsw.pc
  simp only [zc_eq, nzx_eq_one, one_mul]
  rw [setIntegral_const, Measure.real, m.hμ.2.2]
  simp

end GlobalTheory.CompanionTheory.PcZero

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialCoefficientRankZeroStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_coefficient_rank_zero : ∀ (D : D7) (p : ℕ) (hn : 0 + p = p) (M : Maps D hn) (m : Meas D 0 p) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D 0) (F : G D p → ℂ) (g : G D p), pc M m ψ b₀ F g = F g := by
  first | exact @GlobalTheory.CompanionTheory.PcZero.pc_eq | exact GlobalTheory.CompanionTheory.PcZero.pc_eq | (intros; apply GlobalTheory.CompanionTheory.PcZero.pc_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialCoefficientUniformLimit
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialCoefficientUniformLimit
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJLim

theorem fj_tendsto : PcBound → ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) {ι : Type} (l : Filter ι) (Fs : ι → G D n → ℂ) (A : G D n → ℂ), Continuous A → LeftInv (GF D n) A → (∀ᶠ i in l, Continuous (Fs i) ∧ LeftInv (GF D n) (Fs i)) → (∀ C : Set (G D n), IsCompact C → ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ c ∈ C, ‖Fs i c - A c‖ ≤ ε) → (∀ᶠ i in l, ∀ (y : Mx D ρ p) (g : G D n), pc M m ψ b₀ (Fs i - A) (M.sh y * g) = pc M m ψ b₀ (Fs i) (M.sh y * g) - pc M m ψ b₀ A (M.sh y * g)) → ∀ (g : G D n) (φ : Mx D ρ p → ℂ), Integrable φ m.μ → Tendsto (fun i => FJ M m ψ b₀ (Fs i) g φ) l (𝓝 (FJ M m ψ b₀ A g φ)) := by
  intro hPc D n ρ p hn M m ψ hψ b₀ ι l Fs A hAc hAinv hFs hunif hadd g φ hφ
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  obtain ⟨hcont, hbd⟩ := hPc D n ρ p hn M m ψ hψ b₀
  obtain ⟨C, hC, -, hCb⟩ := hbd g
  have hφc : Integrable (fun y => conj (φ y)) m.μ := Complex.conjCLE.toContinuousLinearMap.integrable_comp hφ
  have hint : ∀ F : G D n → ℂ, Continuous F → LeftInv (GF D n) F →
      Integrable (fun y => pc M m ψ b₀ F (M.sh y * g) * conj (φ y)) m.μ := by
    intro F hF hinv
    obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hF.continuousOn
    have hc : Continuous fun y => pc M m ψ b₀ F (M.sh y * g) :=
      (hcont F hF hinv).comp (M.sh_cont.mul continuous_const)
    exact hφc.bdd_mul hc.aestronglyMeasurable (Eventually.of_forall fun y => hCb F hF hinv B hB y)
  rw [Metric.tendsto_nhds]
  intro ε hε
  set N : ℝ := ∫ y, ‖φ y‖ ∂m.μ with hN
  have hN0 : 0 ≤ N := integral_nonneg fun _ => norm_nonneg _
  have hδ : 0 < ε / (N + 1) := by positivity
  filter_upwards [hFs, hadd, hunif C hC _ hδ] with i hi hai hui
  have hsub : Continuous (Fs i - A) := hi.1.sub hAc
  have hsinv : LeftInv (GF D n) (Fs i - A) := fun γ hγ x => by
    simp only [Pi.sub_apply, hi.2 γ hγ x, hAinv γ hγ x]
  have hpt : ∀ y, ‖pc M m ψ b₀ (Fs i) (M.sh y * g) - pc M m ψ b₀ A (M.sh y * g)‖ ≤ ε / (N + 1) := by
    intro y
    rw [← hai y g]
    exact hCb _ hsub hsinv _ (fun c hc => by simpa using hui c hc) y
  have hdiff : FJ M m ψ b₀ (Fs i) g φ - FJ M m ψ b₀ A g φ =
      ∫ y, (pc M m ψ b₀ (Fs i) (M.sh y * g) - pc M m ψ b₀ A (M.sh y * g)) * conj (φ y) ∂m.μ := by
    unfold FJ
    rw [← integral_sub (hint _ hi.1 hi.2) (hint _ hAc hAinv)]
    simp only [sub_mul]
  have hle : ‖FJ M m ψ b₀ (Fs i) g φ - FJ M m ψ b₀ A g φ‖ ≤ ε / (N + 1) * N := by
    rw [hdiff, hN, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hφ.norm.const_mul _) (Eventually.of_forall fun y => ?_)
    rw [norm_mul, RCLike.norm_conj]
    exact mul_le_mul_of_nonneg_right (hpt y) (norm_nonneg _)
  rw [dist_eq_norm]
  refine lt_of_le_of_lt hle ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

end GlobalTheory.CompanionTheory.FJLim
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialCoefficientUniformLimitStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_coefficient_uniform_limit : PcBound → ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) {ι : Type} (l : Filter ι) (Fs : ι → G D n → ℂ) (A : G D n → ℂ), Continuous A → LeftInv (GF D n) A → (∀ᶠ i in l, Continuous (Fs i) ∧ LeftInv (GF D n) (Fs i)) → (∀ C : Set (G D n), IsCompact C → ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ c ∈ C, ‖Fs i c - A c‖ ≤ ε) → (∀ᶠ i in l, ∀ (y : Mx D ρ p) (g : G D n), pc M m ψ b₀ (Fs i - A) (M.sh y * g) = pc M m ψ b₀ (Fs i) (M.sh y * g) - pc M m ψ b₀ A (M.sh y * g)) → ∀ (g : G D n) (φ : Mx D ρ p → ℂ), Integrable φ m.μ → Tendsto (fun i => FJ M m ψ b₀ (Fs i) g φ) l (𝓝 (FJ M m ψ b₀ A g φ)) := by
  first | exact @GlobalTheory.CompanionTheory.FJLim.fj_tendsto | exact GlobalTheory.CompanionTheory.FJLim.fj_tendsto | (intros; apply GlobalTheory.CompanionTheory.FJLim.fj_tendsto <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueMeasureIdentity
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ResMu

open Set GlobalTheory.Eis

variable {D : D7} {p : ℕ}

theorem hecke_one : IsHeckeChar D 1 := ⟨continuous_const, fun _ => rfl⟩

theorem hecke_mul_inv {χ' : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ') : IsHeckeChar D (1 * χ'⁻¹) := by
  refine ⟨?_, fun x => ?_⟩
  · have e : (⇑((1 : (AE D)ˣ →* Circle) * χ'⁻¹)) = fun x => (χ' x)⁻¹ := by
      funext x; simp
    rw [e]
    exact h.1.inv
  · simpa using h.2 x

theorem fj_smul {n ρ p' : ℕ} {hn : ρ + p' = n} (M : Maps D hn) (m : Meas D ρ p') (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ)
    (c : ℂ) (F : G D n → ℂ) (g : G D n) (φ : Mx D ρ p' → ℂ) :
    FJ M m ψ b₀ (c • F) g φ = c * FJ M m ψ b₀ F g φ := by
  simp only [FJ, PositivityTheory.Rg.Rsw.pc, PositivityTheory.Rg.Rsw.zc, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem eis_pole_free (hRS : RSec) (hEH : EisHol) (hp : 2 ≤ p) {p' : ℕ} (hn : 1 + p' = p) (M : Maps D hn) (m : Meas D 1 p')
    (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D 1) (hdet : b₀.1.det ≠ 0)
    {χ' : (AE D)ˣ →* Circle} (hχ' : IsHeckeChar D χ') {θ : InfFam D} (hθ : IsInfFam θ) {Ω : G D p' → Mx D 1 p' → ℂ}
    (hΩ : IsTh ψ χ' θ b₀ m.μ Ω) {H : G D p → ℝ≥0} (hH : IsHt H) {f : G D p → ℂ} (hf : IsRho f) (g : G D p) :
    Tendsto (fun σ : ℝ => ((σ - p / 2 : ℝ) : ℂ) * eisS (Rsec M m ψ b₀ (fam H f ((p : ℂ) / 2) (σ : ℂ)) g Ω) 1)
      (𝓝[>] ((p : ℝ) / 2)) (𝓝 0) := by
  obtain ⟨c1, c2, c3⟩ := hRS D p 1 p' hn M m ψ hψ b₀ hdet 1 χ' hecke_one hχ' θ hθ Ω hΩ H hH ((p : ℂ) / 2) f hf.1 hf.2 g
  have hd := hEH D p' (1 * χ'⁻¹) (hecke_mul_inv hχ') _ (fun z => Rsec M m ψ b₀ (fam H f ((p : ℂ) / 2) z) g Ω) c1 c2 c3 1
  have hopen : IsOpen {z : ℂ | (((1 : ℕ) : ℝ) - p') / 2 < z.re ∧ (p' : ℝ) / 2 < z.re} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt continuous_const Complex.continuous_re)
  have hpp : (p : ℝ) = 1 + p' := by rw [← hn]; push_cast; ring
  have hp' : (1 : ℝ) ≤ p' := by
    have : 1 ≤ p' := by omega
    exact_mod_cast this
  have hmem : ((((p : ℝ) / 2 : ℝ)) : ℂ) ∈ {z : ℂ | (((1 : ℕ) : ℝ) - p') / 2 < z.re ∧ (p' : ℝ) / 2 < z.re} := by
    simp only [mem_setOf_eq, Complex.ofReal_re, hpp, Nat.cast_one]
    constructor <;> linarith
  have hcont := (hd.differentiableAt (hopen.mem_nhds hmem)).continuousAt
  have h1 := (hcont.tendsto.comp (Complex.continuous_ofReal.continuousAt (x := (p : ℝ) / 2))).mono_left
    (nhdsWithin_le_nhds (s := Ioi ((p : ℝ) / 2)))
  have h2 : Tendsto (fun σ : ℝ => ((σ - p / 2 : ℝ) : ℂ)) (𝓝[>] ((p : ℝ) / 2)) (𝓝 0) := by
    have : Continuous fun σ : ℝ => ((σ - p / 2 : ℝ) : ℂ) := by fun_prop
    have h3 := (this.tendsto ((p : ℝ) / 2)).mono_left (nhdsWithin_le_nhds (s := Ioi ((p : ℝ) / 2)))
    simpa using h3
  simpa using h2.mul h1

theorem pc_vanish (hHE : HeckeEta) (hFJ : FJEis) (hPB : PcBound) (hRS : RSec) (hEH : EisHol) (hTT : ThTotal) (hS : SphBound)
    (hp : 2 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) {p' : ℕ} (hn : 1 + p' = p) (M : Maps D hn)
    (m : Meas D 1 p') (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) {θ : InfFam D} (hθ : IsInfFam θ)
    (b₀ : HermE D 1) (hb : IsDiagInv b₀) (g : G D p) : pc M m ψ b₀ (resA H f) g = 0 := by
  have hp1 : 1 ≤ p := by omega
  obtain ⟨χ', hχ', hres⟩ := hHE D 1
  have hAc := resA_cont hS hp1 hH hC hcov hf
  have hAl := resA_leftInv hS hp1 hH hC hcov hf
  have hU := ufil_le p
  have key : ∀ g₀ : G D p, (fun y => pc M m ψ b₀ (resA H f) (M.sh y * g₀)) = 0 := fun g₀ => by
    refine hTT D 1 p' m ψ hψ b₀ hb χ' hχ' hres (fun h => absurd h one_ne_zero) θ hθ _ ?_ ?_ ?_
    · exact ((hPB D p 1 p' hn M m ψ hψ b₀).1 _ hAc hAl).comp (M.sh_cont.mul continuous_const)
    · obtain ⟨C₁, hC₁, -, hb₁⟩ := (hPB D p 1 p' hn M m ψ hψ b₀).2 g₀
      obtain ⟨B, hB⟩ := hC₁.exists_bound_of_continuousOn hAc.continuousOn
      exact ⟨B, hb₁ _ hAc hAl B hB⟩
    · intro Ω hΩ
      have hint : Integrable (Ω 1) m.μ := GlobalTheory.SchwartzAInt.integrable_of_mem D θ hθ 1 p' m.μ m.𝓕 m.hμ (Ω 1) (hΩ.mem 1)
      have hFl : ∀ᶠ σ in ((ufil p : Ultrafilter ℝ) : Filter ℝ), Continuous (res H f σ) ∧ LeftInv (GF D p) (res H f σ) := by
        refine hU ?_
        filter_upwards [ev_Ioc p] with σ hσ using ⟨res_cont hS hp1 hH hC hcov hf hσ, res_leftInv hH hf σ⟩
      have hlim := GlobalTheory.T.partial_coefficient_uniform_limit hPB D p 1 p' hn M m ψ hψ b₀ ((ufil p : Ultrafilter ℝ) : Filter ℝ) (fun σ => res H f σ) (resA H f)
        hAc hAl hFl (fun C' hC' ε hε => resA_unif hS hp1 hH hC hcov hf hC' hε)
        (hFl.mono fun σ hσ y g' => GlobalTheory.T.partial_coefficient_sub hPB D p 1 p' hn M m ψ hψ b₀ _ _ hσ.1 hσ.2 hAc hAl y g') g₀ (Ω 1) hint
      have hzero : Tendsto (fun σ => FJ M m ψ b₀ (res H f σ) g₀ (Ω 1)) ((ufil p : Ultrafilter ℝ) : Filter ℝ) (𝓝 0) := by
        refine ((eis_pole_free hRS hEH hp hn M m ψ hψ b₀ hb.2 hχ' hθ hΩ hH hf g₀).mono_left hU).congr' ?_
        refine hU ?_
        filter_upwards [ev_Ioc p] with σ hσ
        have e : res H f σ = ((σ - p / 2 : ℝ) : ℂ) • eisS (fam H f ((p : ℂ) / 2) (σ : ℂ)) := rfl
        rw [e, fj_smul, hFJ D p 1 p' hn M m ψ hψ b₀ hb.2 1 χ' hecke_one hχ' θ hθ Ω hΩ (σ : ℂ) _
          (fam_cont_at hH hf.1 _ σ) (fam_law_real hH hf σ) (by simpa using hσ.1) g₀]
      exact tendsto_nhds_unique hlim hzero
  have := congrFun (key ((M.sh 0)⁻¹ * g)) 0
  simpa [← mul_assoc] using this

theorem resA_n_inv (hME : MapsExist) (hHE : HeckeEta) (hFJ : FJEis) (hPB : PcBound) (hRS : RSec) (hEH : EisHol) (hTT : ThTotal)
    (hPF : PcFc) (hS : SphBound) (hp : 2 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) {nb : hermA D p → G D p}
    {lam : Measure (hermA D p)} {𝓖 : Set (hermA D p)} (hCd : CoefData (D := D) (n := p) nb lam 𝓖) (b : hermA D p) (g : G D p) :
    resA H f (nb b * g) = resA H f g := by
  have hp1 : 1 ≤ p := by omega
  have hAc := resA_cont hS hp1 hH hC hcov hf
  have hAl := resA_leftInv hS hp1 hH hC hcov hf
  obtain ⟨ψ, hψ⟩ := GlobalTheory.CompanionTheory.AdelicChar.exists_isCharAF D.host.F D.sp.cm.totReal
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  have hn : 1 + (p - 1) = p := by omega
  obtain ⟨⟨M⟩, ⟨m⟩⟩ := hME D p 1 (p - 1) hn
  obtain ⟨⟨M0⟩, ⟨m0⟩⟩ := hME D p 0 p (zero_add p)
  have hr : RankLT ψ (resA H f) 1 := (hPF D p 1 (p - 1) hn M m ψ hψ _ hAc hAl).1 fun b₀ hb g =>
    pc_vanish hHE hFJ hPB hRS hEH hTT hS hp hH hC hcov hf hn M m ψ hψ hθ b₀ hb g
  let b0 : HermE D 0 := ⟨0, by ext i; exact i.elim0⟩
  let β : HermE D p := ⟨0, by simp⟩
  have hdet : b0.1.det ≠ 0 := by simp [b0]
  have hβ : IsExt (zero_add p) b0 β := by
    ext i j
    simp only [bl, Matrix.submatrix_apply, β]
    generalize (finSumFinEquiv.trans (finCongr (zero_add p))).symm i = a
    generalize (finSumFinEquiv.trans (finCongr (zero_add p))).symm j = c
    rcases a with a | a
    · exact a.elim0
    · rcases c with c | c
      · exact c.elim0
      · simp
  have h2 := (hPF D p 0 p (zero_add p) M0 m0 ψ hψ _ hAc hAl).2 hr b0 hdet β hβ nb lam 𝓖 hCd
  exact GlobalTheory.T.invariance_of_constant_fourier_coefficient D p ψ nb lam 𝓖 hCd _ hAc hAl β rfl (fun g => by
    rw [← h2 g]; exact GlobalTheory.T.partial_coefficient_rank_zero D p (zero_add p) M0 m0 ψ b0 _ g) b g

theorem resMu_main : MapsExist → HtExist → HeckeEta → FJEis → PcBound → RSec → EisHol → ThTotal → PcFc → SphBound →
    PositivityTheory.PfSWUS.FourierZero → PositivityTheory.PfSWUS.CoefDataExists → ResMu := by
  intro hME hHt hHE hFJ hPB hRS hEH hTT hPF hS _ hCE D p hp
  have hp1 : 1 ≤ p := by omega
  obtain ⟨⟨H, hH⟩, C, hC, hcov⟩ := hHt D p
  refine ⟨fun f => resA H f 1, ?_⟩
  exact
    { add := fun f f' hf hf' => resA_add hS hp1 hH hC hcov hf hf' 1
      smul := fun c f hf => resA_smul hS hp1 hH hC hcov hf c 1
      pos := fun f hf h => resA_pos hS hp1 hH hC hcov hf h 1
      bound := fun H' hH' => resA_bound hS hp1 hH hC hcov H' hH'
      inv_n := fun x b hx f hf => by
        have hb : adj b = b := (GlobalTheory.StdUnn.Model.exists_unip b).1 ⟨x, hx⟩
        obtain ⟨nb, lam, 𝓖, hCd⟩ := hCE D p
        have e : x = nb ⟨b, hb⟩ * 1 := GlobalTheory.StdUnn.LeftInvSect.mat_inj (by rw [mul_one, hx, hCd.1])
        have h1 := resA_translate hS hp1 hH hC hcov hf x
        have h2 := resA_n_inv hME hHE hFJ hPB hRS hEH hTT hPF hS hp hH hC hcov hf hCd ⟨b, hb⟩ 1
        rw [← e] at h2
        exact h1.symm.trans h2
      inv_rat := fun γ hγ f hf => by
        have h1 := resA_translate hS hp1 hH hC hcov hf γ
        have h2 := resA_leftInv hS hp1 hH hC hcov hf γ hγ 1
        rw [mul_one] at h2
        exact h1.symm.trans h2
      lim := fun f hc hl a ha => (resA_lim hS hp1 hH hC hcov f hc hl a ha).2 }

end GlobalTheory.CompanionTheory.ResMu
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueMeasureIdentityStatement
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_measure_identity : MapsExist → HtExist → HeckeEta → FJEis → PcBound → RSec → EisHol → ThTotal → PcFc → SphBound → PositivityTheory.PfSWUS.FourierZero → PositivityTheory.PfSWUS.CoefDataExists → ResMu := by
  first | exact @GlobalTheory.CompanionTheory.ResMu.resMu_main | exact GlobalTheory.CompanionTheory.ResMu.resMu_main | (intros; apply GlobalTheory.CompanionTheory.ResMu.resMu_main <;> assumption)
end
