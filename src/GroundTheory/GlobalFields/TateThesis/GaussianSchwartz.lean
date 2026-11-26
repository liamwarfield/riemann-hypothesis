module

public import Mathlib

@[expose] public section

section -- merged from GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
open Real Function
open scoped ContDiff Nat SchwartzMap

namespace GroundTheory.Global

noncomputable section

theorem one_add_pow_mul_exp_neg_pi_mul_sq_le {r : ℝ} (hr : 0 ≤ r) (N : ℕ) :
    (1 + r) ^ N * Real.exp (-π * r ^ 2) ≤ Real.exp (N ^ 2 / (4 * π)) := by
  have h1 : (1 + r) ^ N ≤ Real.exp (N * r) := by
    calc (1 + r) ^ N ≤ Real.exp r ^ N :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp r]) N
      _ = Real.exp (N * r) := by rw [← Real.exp_nat_mul]
  calc (1 + r) ^ N * Real.exp (-π * r ^ 2) ≤ Real.exp (N * r) * Real.exp (-π * r ^ 2) := by
        gcongr
    _ = Real.exp (N * r - π * r ^ 2) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (N ^ 2 / (4 * π)) := by
      apply Real.exp_le_exp.2
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg ((N : ℝ) - 2 * π * r), Real.pi_pos]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def gaussianFun (x : E) : ℂ := ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ)

theorem contDiff_gaussianFun : ContDiff ℝ ∞ (gaussianFun (E := E)) :=
  Complex.ofRealCLM.contDiff.comp
    (Real.contDiff_exp.comp (contDiff_const.mul (contDiff_norm_sq ℝ)))

theorem norm_iteratedFDeriv_exp (i : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ i Real.exp y‖ = Real.exp y := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos y)]

theorem norm_iteratedFDeriv_gaussian_le (n : ℕ) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ x : E, ‖iteratedFDeriv ℝ n (gaussianFun (E := E)) x‖ ≤
      C * (1 + ‖x‖) ^ k * Real.exp (-π * ‖x‖ ^ 2) := by
  set q : E → ℝ := fun x ↦ -π * ‖x‖ ^ 2 with hq_def
  have hq : q.HasTemperateGrowth := (HasTemperateGrowth.const (-π)).mul (hasTemperateGrowth_norm_sq E)
  have hqs : ContDiff ℝ ∞ q := contDiff_const.mul (contDiff_norm_sq ℝ)
  obtain ⟨k, C, hC, hb⟩ := hq.norm_iteratedFDeriv_le_uniform n
  refine ⟨n ! * max C 1 ^ n, k * n, by positivity, fun x ↦ ?_⟩
  have hx1 : 1 ≤ (1 + ‖x‖) ^ k := one_le_pow₀ (by linarith [norm_nonneg x])
  set D := max C 1 * (1 + ‖x‖) ^ k
  have hD1 : 1 ≤ D := one_le_mul_of_one_le_of_one_le (le_max_right _ _) hx1
  have hcomp : ‖iteratedFDeriv ℝ n (Real.exp ∘ q) x‖ ≤ n ! * Real.exp (q x) * D ^ n := by
    refine norm_iteratedFDeriv_comp_le Real.contDiff_exp hqs (by exact_mod_cast le_top) x
      (fun i _ ↦ (norm_iteratedFDeriv_exp i (q x)).le) fun i hi1 hin ↦ ?_
    calc ‖iteratedFDeriv ℝ i q x‖ ≤ C * (1 + ‖x‖) ^ k := hb i hin x
      _ ≤ D := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ D ^ i := le_self_pow₀ hD1 (by omega)
  have hG : gaussianFun (E := E) = (Complex.ofRealLI : ℝ →ₗᵢ[ℝ] ℂ) ∘ (Real.exp ∘ q) := rfl
  rw [hG, LinearIsometry.norm_iteratedFDeriv_comp_left _
    (Real.contDiff_exp.comp hqs).contDiffAt (by exact_mod_cast le_top)]
  refine hcomp.trans (le_of_eq ?_)
  simp only [D, mul_pow, ← pow_mul, hq_def]
  ring

def gaussianSchwartz (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] : 𝓢(E, ℂ) where
  toFun := gaussianFun
  smooth' := contDiff_gaussianFun
  decay' k n := by
    obtain ⟨C, j, hC, hb⟩ := norm_iteratedFDeriv_gaussian_le (E := E) n
    refine ⟨C * Real.exp ((k + j : ℕ) ^ 2 / (4 * π)), fun x ↦ ?_⟩
    have hk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := pow_le_pow_left₀ (norm_nonneg x) (by linarith) k
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n gaussianFun x‖
        ≤ (1 + ‖x‖) ^ k * (C * (1 + ‖x‖) ^ j * Real.exp (-π * ‖x‖ ^ 2)) :=
          mul_le_mul hk (hb x) (norm_nonneg _) (by positivity)
      _ = C * ((1 + ‖x‖) ^ (k + j) * Real.exp (-π * ‖x‖ ^ 2)) := by rw [pow_add]; ring
      _ ≤ C * Real.exp ((k + j : ℕ) ^ 2 / (4 * π)) :=
          mul_le_mul_of_nonneg_left (one_add_pow_mul_exp_neg_pi_mul_sq_le (norm_nonneg x) _) hC

@[simp]
theorem gaussianSchwartz_apply (x : E) :
    gaussianSchwartz E x = ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ) :=
  rfl

end

end GroundTheory.Global
end

section -- merged from GroundTheory.GlobalFields.TateThesis.NoSmallSubgroups
namespace GroundTheory.Global

open Topology Filter

def NoSmallSubgroups (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∃ U ∈ 𝓝 (1 : G), ∀ H : Subgroup G, (H : Set G) ⊆ U → H = ⊥

theorem norm_sq_sub_one_ge {z : ℂ} (hz : ‖z - 1‖ < 1 / 2) :
    3 / 2 * ‖z - 1‖ ≤ ‖z ^ 2 - 1‖ := by
  have h1 : z ^ 2 - 1 = (z - 1) * (z + 1) := by ring
  have h2 : (3 : ℝ) / 2 ≤ ‖z + 1‖ := by
    have : z + 1 = 2 - (1 - z) := by ring
    have h3 : ‖(2 : ℂ)‖ = 2 := by simp
    have h4 : ‖1 - z‖ = ‖z - 1‖ := norm_sub_rev _ _
    calc (3 : ℝ) / 2 ≤ ‖(2 : ℂ)‖ - ‖1 - z‖ := by rw [h3, h4]; linarith
      _ ≤ ‖(2 : ℂ) - (1 - z)‖ := norm_sub_norm_le _ _
      _ = ‖z + 1‖ := by rw [this]
  rw [h1, norm_mul]
  nlinarith [norm_nonneg (z - 1)]

theorem eq_one_of_forall_norm_pow_two_pow_sub_one_lt {z : ℂ}
    (hz : ∀ k : ℕ, ‖z ^ (2 ^ k) - 1‖ < 1 / 2) : z = 1 := by
  have key : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h := norm_sq_sub_one_ge (hz k)
      rw [← pow_mul, ← pow_succ] at h
      calc (3 / 2 : ℝ) ^ (k + 1) * ‖z - 1‖ = 3 / 2 * ((3 / 2) ^ k * ‖z - 1‖) := by ring
        _ ≤ 3 / 2 * ‖z ^ (2 ^ k) - 1‖ := by gcongr
        _ ≤ _ := h
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / (2 * ‖z - 1‖)) (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 := lt_of_le_of_lt (key k) (hz k)
  rw [div_lt_iff₀ (by positivity)] at hk
  nlinarith

theorem eq_one_of_sq_mem {s : Set ℂ} (hsq : ∀ z ∈ s, z ^ 2 ∈ s)
    (hs : ∀ z ∈ s, ‖z - 1‖ < 1 / 2) {z : ℂ} (hz : z ∈ s) : z = 1 := by
  refine eq_one_of_forall_norm_pow_two_pow_sub_one_lt fun k ↦ hs _ ?_
  induction k with
  | zero => simpa using hz
  | succ k ih =>
    rw [pow_succ, pow_mul]
    exact hsq _ ih

namespace Circle

theorem subgroup_eq_bot_of_norm_sub_one_lt (H : Subgroup Circle)
    (hH : ∀ z ∈ H, ‖(z : ℂ) - 1‖ < 1 / 2) : H = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot, ← Circle.coe_eq_one]
  refine eq_one_of_sq_mem (s := (↑) '' (H : Set Circle)) ?_ ?_ ⟨z, hz, rfl⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨w ^ 2, H.pow_mem hw 2, by simp⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact hH w hw

theorem noSmallSubgroups : NoSmallSubgroups Circle := by
  refine ⟨{z : Circle | ‖(z : ℂ) - 1‖ < 1 / 2}, ?_, fun H hH ↦
    subgroup_eq_bot_of_norm_sub_one_lt H fun z hz ↦ hH hz⟩
  have hc : Continuous fun z : Circle ↦ ‖(z : ℂ) - 1‖ :=
    (continuous_subtype_val.sub continuous_const).norm
  exact (isOpen_lt hc continuous_const).mem_nhds (by simp)

end Circle

namespace Complex

theorem units_subgroup_eq_bot_of_norm_sub_one_lt (H : Subgroup ℂˣ)
    (hH : ∀ z ∈ H, ‖(z : ℂ) - 1‖ < 1 / 2) : H = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot, ← Units.val_eq_one]
  refine eq_one_of_sq_mem (s := (↑) '' (H : Set ℂˣ)) ?_ ?_ ⟨z, hz, rfl⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨w ^ 2, H.pow_mem hw 2, by simp⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact hH w hw

theorem units_noSmallSubgroups : NoSmallSubgroups ℂˣ := by
  refine ⟨{z : ℂˣ | ‖(z : ℂ) - 1‖ < 1 / 2}, ?_, fun H hH ↦
    units_subgroup_eq_bot_of_norm_sub_one_lt H fun z hz ↦ hH hz⟩
  have hc : Continuous fun z : ℂˣ ↦ ‖(z : ℂ) - 1‖ :=
    (Units.continuous_val.sub continuous_const).norm
  exact (isOpen_lt hc continuous_const).mem_nhds (by simp)

end Complex

section Kernel

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H]

theorem isOpen_ker_of_noSmallSubgroups
    (hG : ∀ W ∈ 𝓝 (1 : G), ∃ V : OpenSubgroup G, (V : Set G) ⊆ W) (hH : NoSmallSubgroups H)
    (f : G →* H) (hf : Continuous f) : IsOpen (f.ker : Set G) := by
  obtain ⟨U, hU, hsmall⟩ := hH
  have hW : f ⁻¹' U ∈ 𝓝 (1 : G) := hf.continuousAt.preimage_mem_nhds (by rwa [map_one])
  obtain ⟨V, hV⟩ := hG _ hW
  have hmap : V.toSubgroup.map f = ⊥ := by
    refine hsmall _ ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hV hx
  refine Subgroup.isOpen_mono (H₁ := V.toSubgroup) ?_ V.isOpen
  rwa [← Subgroup.map_eq_bot_iff]

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

end Kernel

end GroundTheory.Global
end

section -- merged from GroundTheory.GlobalFields.TateThesis.Gaussian
namespace GroundTheory.Global

open _root_.Complex MeasureTheory Set Real
open scoped FourierTransform

noncomputable section

theorem mellin_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) {a : ℂ} (ha : 0 < a.re) :
    mellin (fun t : ℝ ↦ ((Real.exp (-(b * t ^ 2)) : ℝ) : ℂ)) a =
      (1 / 2 : ℂ) * (b : ℂ) ^ (-(a / 2)) * Complex.Gamma (a / 2) := by
  have h1 := mellin_comp_rpow (fun u : ℝ ↦ ((Real.exp (-(b * u)) : ℝ) : ℂ)) a 2
  simp only [Real.rpow_two] at h1
  rw [h1, mellin_comp_mul_left (fun u : ℝ ↦ ((Real.exp (-u) : ℝ) : ℂ)) _ hb,
    ← GammaIntegral_eq_mellin, ← Complex.Gamma_eq_integral (by simpa using div_pos ha two_pos)]
  simp only [abs_two, ofReal_ofNat, smul_eq_mul]
  ring_nf
  norm_num
  ring

def realGaussian (x : ℝ) : ℂ := Complex.exp (-π * (x : ℂ) ^ 2)

def realGaussianOdd (x : ℝ) : ℂ := (x : ℂ) * Complex.exp (-π * (x : ℂ) ^ 2)

theorem realGaussian_eq_ofReal (x : ℝ) :
    realGaussian x = ((Real.exp (-(π * x ^ 2)) : ℝ) : ℂ) := by
  simp [realGaussian, ofReal_exp]

theorem fourier_realGaussian : 𝓕 realGaussian = realGaussian := by
  have h := fourier_gaussian_pi (b := 1) (by simp)
  simp only [mul_one, one_cpow, div_one, one_mul] at h
  unfold realGaussian
  rw [h]

theorem integrable_realGaussian : Integrable realGaussian := by
  exact integrable_cexp_neg_mul_sq (b := (π : ℂ)) (by simpa using Real.pi_pos)

theorem integrable_realGaussianOdd : Integrable realGaussianOdd := by
  exact integrable_mul_cexp_neg_mul_sq (b := (π : ℂ)) (by simpa using Real.pi_pos)

theorem hasDerivAt_realGaussian (x : ℝ) :
    HasDerivAt realGaussian (-2 * π * x * realGaussian x) x := by
  have h : HasDerivAt (fun y : ℝ ↦ -π * (y : ℂ) ^ 2) (-π * (2 * (x : ℂ))) x := by
    have := ((hasDerivAt_id x).ofReal_comp).pow 2
    simpa using this.const_mul (-(π : ℂ))
  unfold realGaussian
  convert h.cexp using 1
  ring

theorem fourier_realGaussianOdd : 𝓕 realGaussianOdd = fun y ↦ -I * realGaussianOdd y := by
  have hxf : Integrable (fun x : ℝ ↦ x • realGaussian x) := by
    refine integrable_realGaussianOdd.congr (Filter.Eventually.of_forall fun x ↦ ?_)
    simp [realGaussianOdd, realGaussian, Complex.real_smul]
  funext y
  have hd := hasDerivAt_fourier integrable_realGaussian hxf y
  rw [fourier_realGaussian] at hd
  have h2 := (hasDerivAt_realGaussian y).unique hd
  have h3 : 𝓕 (fun x : ℝ ↦ (-2 * π * I * x) • realGaussian x) y =
      (-2 * π * I) * 𝓕 realGaussianOdd y := by
    rw [fourier_real_eq, fourier_real_eq, ← integral_const_mul]
    congr 1; funext x
    simp only [realGaussianOdd, realGaussian, Circle.smul_def, smul_eq_mul]
    ring
  rw [h3] at h2
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have : 𝓕 realGaussianOdd y = (-2 * π * y * realGaussian y) / (-2 * π * I) := by
    rw [h2]; field_simp
  rw [this, realGaussianOdd, realGaussian]
  field_simp
  ring_nf
  simp [I_sq]

theorem integral_comp_abs_complex (f : ℝ → ℂ) :
    ∫ x : ℝ, f |x| = 2 * ∫ y in Ioi (0 : ℝ), f y := by
  have h := integral_fun_norm_addHaar (volume : Measure ℝ) f
  simp only [Real.norm_eq_abs] at h
  rw [h]
  simp [Complex.real_smul]

theorem mellin_exp_neg_pi_mul_sq {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t : ℝ ↦ ((Real.exp (-(π * t ^ 2)) : ℝ) : ℂ)) s = Gammaℝ s / 2 := by
  rw [mellin_exp_neg_mul_sq Real.pi_pos hs, Gammaℝ_def]
  ring_nf

theorem ofReal_cpow_div_self {y : ℝ} (hy : 0 < y) (s : ℂ) :
    (y : ℂ) ^ s / (y : ℂ) = (y : ℂ) ^ (s - 1) := by
  have hy' : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
  rw [cpow_sub _ _ hy', cpow_one]

theorem integral_realGaussian_mul_abs_cpow {s : ℂ} (hs : 0 < s.re) :
    ∫ x : ℝ, realGaussian x * ((|x| : ℝ) : ℂ) ^ s / ((|x| : ℝ) : ℂ) = Gammaℝ s := by
  have h : (fun x : ℝ ↦ realGaussian x * ((|x| : ℝ) : ℂ) ^ s / ((|x| : ℝ) : ℂ)) =
      fun x ↦ (fun y : ℝ ↦ ((Real.exp (-(π * y ^ 2)) : ℝ) : ℂ) * (y : ℂ) ^ s / (y : ℂ)) |x| := by
    funext x
    simp only [realGaussian_eq_ofReal, sq_abs]
  rw [h, integral_comp_abs_complex
    (fun y : ℝ ↦ ((Real.exp (-(π * y ^ 2)) : ℝ) : ℂ) * (y : ℂ) ^ s / (y : ℂ))]
  have : ∫ y in Ioi (0 : ℝ), ((Real.exp (-(π * y ^ 2)) : ℝ) : ℂ) * (y : ℂ) ^ s / (y : ℂ) =
      mellin (fun t : ℝ ↦ ((Real.exp (-(π * t ^ 2)) : ℝ) : ℂ)) s := by
    rw [mellin]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
    rw [mul_div_assoc, ofReal_cpow_div_self hy, smul_eq_mul, mul_comm]
  rw [this, mellin_exp_neg_pi_mul_sq hs]
  ring

theorem integral_realGaussianOdd_mul_sign_mul_abs_cpow {s : ℂ} (hs : -1 < s.re) :
    ∫ x : ℝ, realGaussianOdd x * (Real.sign x : ℂ) * ((|x| : ℝ) : ℂ) ^ s / ((|x| : ℝ) : ℂ) =
      Gammaℝ (s + 1) := by
  have hs1 : 0 < (s + 1).re := by simp; linarith
  have h : (fun x : ℝ ↦ realGaussianOdd x * (Real.sign x : ℂ) * ((|x| : ℝ) : ℂ) ^ s /
        ((|x| : ℝ) : ℂ)) =
      fun x ↦ (fun y : ℝ ↦ (y : ℂ) * ((Real.exp (-(π * y ^ 2)) : ℝ) : ℂ) * (y : ℂ) ^ s /
        (y : ℂ)) |x| := by
    funext x
    have hx : (x : ℂ) * (Real.sign x : ℂ) = ((|x| : ℝ) : ℂ) := by
      rw [← ofReal_mul]
      congr 1
      rcases lt_trichotomy x 0 with h | h | h
      · rw [Real.sign_of_neg h, abs_of_neg h]; ring
      · simp [h]
      · rw [Real.sign_of_pos h, abs_of_pos h]; ring
    rw [realGaussianOdd, ← realGaussian, realGaussian_eq_ofReal]
    simp only [sq_abs]
    rw [← hx]
    ring
  rw [h, integral_comp_abs_complex
    (fun y : ℝ ↦ (y : ℂ) * ((Real.exp (-(π * y ^ 2)) : ℝ) : ℂ) * (y : ℂ) ^ s / (y : ℂ))]
  have : ∫ y in Ioi (0 : ℝ), (y : ℂ) * ((Real.exp (-(π * y ^ 2)) : ℝ) : ℂ) * (y : ℂ) ^ s / (y : ℂ)
      = mellin (fun t : ℝ ↦ ((Real.exp (-(π * t ^ 2)) : ℝ) : ℂ)) (s + 1) := by
    rw [mellin]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
    have hy' : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hy)
    rw [add_sub_cancel_right, smul_eq_mul]
    field_simp
  rw [this, mellin_exp_neg_pi_mul_sq hs1]
  ring

end

end GroundTheory.Global
end

section -- merged from GroundTheory.GlobalFields.TateThesis.AdeleMeasurable
namespace GroundTheory.Global

open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory
open scoped NumberField.AdeleRing

variable (K : Type*) [Field K]

instance secondCountableTopology_infinitePlaceCompletion (w : InfinitePlace K) :
    SecondCountableTopology w.Completion :=
  (Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology

noncomputable instance measurableSpace_infinitePlaceCompletion (w : InfinitePlace K) :
    MeasurableSpace w.Completion :=
  borel _

instance borelSpace_infinitePlaceCompletion (w : InfinitePlace K) :
    BorelSpace w.Completion :=
  ⟨rfl⟩

variable [NumberField K]

instance secondCountableTopology_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing K) :=
  inferInstanceAs (SecondCountableTopology (∀ w : InfinitePlace K, w.Completion))

noncomputable instance measurableSpace_infiniteAdeleRing : MeasurableSpace (InfiniteAdeleRing K) :=
  inferInstanceAs (MeasurableSpace (∀ w : InfinitePlace K, w.Completion))

instance borelSpace_infiniteAdeleRing : BorelSpace (InfiniteAdeleRing K) :=
  inferInstanceAs (BorelSpace (∀ w : InfinitePlace K, w.Completion))

noncomputable instance measurableSpace_finiteAdeleRing :
    MeasurableSpace (FiniteAdeleRing (𝓞 K) K) :=
  borel _

instance borelSpace_finiteAdeleRing : BorelSpace (FiniteAdeleRing (𝓞 K) K) :=
  ⟨rfl⟩

noncomputable instance measurableSpace_adeleRing : MeasurableSpace 𝔸[K] :=
  inferInstanceAs (MeasurableSpace (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))

instance borelSpace_adeleRing : BorelSpace 𝔸[K] :=
  inferInstanceAs (BorelSpace (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))

end GroundTheory.Global
end

section -- merged from GroundTheory.GlobalFields.TateThesis.LatticePoissonBasic
namespace GroundTheory.Global

open MeasureTheory Module Set Filter Topology
open scoped RealInnerProductSpace FourierTransform SchwartzMap

noncomputable section

section DualLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem innerₗ_nondegenerate : (innerₗ E : LinearMap.BilinForm ℝ E).Nondegenerate :=
  ⟨fun x hx => inner_self_eq_zero.mp (hx x), fun y hy => inner_self_eq_zero.mp (hy y)⟩

def dualLattice (L : Submodule ℤ E) : Submodule ℤ E :=
  LinearMap.BilinForm.dualSubmodule (innerₗ E) L

theorem mem_dualLattice {L : Submodule ℤ E} {μ : E} :
    μ ∈ dualLattice L ↔ ∀ ℓ ∈ L, ∃ k : ℤ, ⟪μ, ℓ⟫ = k := by
  simp only [dualLattice, LinearMap.BilinForm.mem_dualSubmodule, Submodule.mem_one,
    innerₗ_apply_apply, algebraMap_int_eq, eq_intCast]
  exact forall₂_congr fun ℓ _ => exists_congr fun k => eq_comm

theorem dualLattice_span_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E) :
    dualLattice (Submodule.span ℤ (Set.range b)) = Submodule.span ℤ
      (Set.range (LinearMap.BilinForm.dualBasis (innerₗ E) innerₗ_nondegenerate b)) :=
  LinearMap.BilinForm.dualSubmodule_span_of_basis _ _ b

variable [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

theorem dualLattice_eq_span : dualLattice L = Submodule.span ℤ
    (Set.range (LinearMap.BilinForm.dualBasis (innerₗ E) innerₗ_nondegenerate
      ((Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L))) := by
  classical
  conv_lhs => rw [← (Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ]
  exact dualLattice_span_eq _

instance : DiscreteTopology (dualLattice L) := by
  rw [dualLattice_eq_span L]; infer_instance

end DualLattice

section Summability

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


omit [FiniteDimensional ℝ E] in
theorem exists_norm_le_inv_one_add_pow (g : 𝓢(E, F)) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖g x‖ ≤ C * ((1 + ‖x‖) ^ k)⁻¹ := by
  refine ⟨2 ^ k * (SchwartzMap.seminorm ℝ 0 0 g + SchwartzMap.seminorm ℝ k 0 g), by positivity,
    fun x => ?_⟩
  have h1 : ‖g x‖ ≤ SchwartzMap.seminorm ℝ 0 0 g := by
    simpa using g.norm_pow_mul_le_seminorm ℝ 0 x
  have h2 : ‖x‖ ^ (0 + k) * ‖g x‖ ≤ SchwartzMap.seminorm ℝ k 0 g := by
    simpa using g.norm_pow_mul_le_seminorm ℝ k x
  have := pow_mul_le_of_le_of_pow_mul_le (norm_nonneg x) (norm_nonneg _) h1 h2
  simpa using this

theorem exists_summable_bound_comp_add (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (g : 𝓢(E, F)) (R : ℝ) :
    ∃ u : Λ → ℝ, Summable u ∧ ∀ ℓ : Λ, ∀ x : E, ‖x‖ ≤ R → ‖g (x + ℓ)‖ ≤ u ℓ := by
  set k := finrank ℤ Λ + 1
  obtain ⟨C, hC, hg⟩ := exists_norm_le_inv_one_add_pow g k
  set R' := max R 0
  refine ⟨fun ℓ => C * (1 + R') ^ k * ((1 + ‖ℓ‖) ^ k)⁻¹, ?_, ?_⟩
  · apply Summable.mul_left
    have hs := ZLattice.summable_norm_pow_inv (L := Λ) k (by omega)
    refine Summable.of_norm_bounded_eventually hs ?_
    filter_upwards [(Set.finite_singleton (0 : Λ)).compl_mem_cofinite] with ℓ hℓ
    have hpos : 0 < ‖ℓ‖ := norm_pos_iff.mpr hℓ
    rw [Real.norm_of_nonneg (by positivity), inv_pow]
    gcongr
    linarith
  · intro ℓ x hx
    have hR : ‖x‖ ≤ R' := hx.trans (le_max_left _ _)
    have hR0 : 0 ≤ R' := le_max_right _ _
    have key : 1 + ‖ℓ‖ ≤ (1 + R') * (1 + ‖x + ℓ‖) := by
      have : ‖(ℓ : E)‖ ≤ ‖x + ℓ‖ + ‖x‖ := by
        calc ‖(ℓ : E)‖ = ‖(x + ℓ) - x‖ := by simp
          _ ≤ ‖x + ℓ‖ + ‖x‖ := norm_sub_le _ _
      have h' : ‖ℓ‖ ≤ ‖x + ℓ‖ + ‖x‖ := this
      nlinarith [norm_nonneg (x + ℓ)]
    calc ‖g (x + ℓ)‖ ≤ C * ((1 + ‖x + ℓ‖) ^ k)⁻¹ := hg _
      _ = C * ((1 + R') ^ k * (((1 + R') * (1 + ‖x + ℓ‖)) ^ k)⁻¹) := by
          rw [mul_pow, mul_inv, ← mul_assoc ((1 + R') ^ k), mul_inv_cancel₀ (by positivity), one_mul]
      _ ≤ C * ((1 + R') ^ k * ((1 + ‖ℓ‖) ^ k)⁻¹) := by
          gcongr
      _ = C * (1 + R') ^ k * ((1 + ‖ℓ‖) ^ k)⁻¹ := by ring

theorem summable_norm_comp_add (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (g : 𝓢(E, F)) (x : E) : Summable fun ℓ : Λ => ‖g (x + ℓ)‖ := by
  obtain ⟨u, hu, hb⟩ := exists_summable_bound_comp_add Λ g ‖x‖
  exact hu.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ℓ => hb ℓ x le_rfl)

theorem continuous_tsum_comp_add [CompleteSpace F] (Λ : Submodule ℤ E)
    [DiscreteTopology Λ] (g : 𝓢(E, F)) : Continuous fun x => ∑' ℓ : Λ, g (x + ℓ) := by
  refine continuous_iff_continuousAt.mpr fun x₀ => ?_
  obtain ⟨u, hu, hb⟩ := exists_summable_bound_comp_add Λ g (‖x₀‖ + 1)
  have hc : ContinuousOn (fun x => ∑' ℓ : Λ, g (x + ℓ)) (Metric.closedBall 0 (‖x₀‖ + 1)) :=
    continuousOn_tsum (fun ℓ => (g.continuous.comp (continuous_id.add continuous_const)).continuousOn)
      hu (fun ℓ x hx => hb ℓ x (by simpa using hx))
  exact hc.continuousAt (Metric.closedBall_mem_nhds_of_mem (by simp))

end Summability

end

end GroundTheory.Global
end

section -- merged from GroundTheory.GlobalFields.TateThesis.ArchChars
namespace GroundTheory.Global

open _root_.Complex

theorem isCoveringMap_circleExp : IsCoveringMap (Circle.exp : ℝ → Circle) := by
  have h : IsCoveringMap ((↑) : ℝ → AddCircle (2 * Real.pi)) := AddCircle.isCoveringMap_coe _
  exact h.homeomorph_comp AddCircle.homeomorphCircle'

theorem existsUnique_circleExp_of_continuous (χ : ℝ → Circle) (hχ : Continuous χ)
    (hmul : ∀ s t, χ (s + t) = χ s * χ t) : ∃! τ : ℝ, ∀ t, χ t = Circle.exp (τ * t) := by
  have cov := isCoveringMap_circleExp
  have h0 : χ 0 = 1 := by
    have h := hmul 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := χ 0) (by rw [mul_one]; exact h.symm)
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ :=
    cov.existsUnique_continuousMap_lifts ⟨χ, hχ⟩ (0 : ℝ) (0 : ℝ) (by simp [h0])
  have hF' : ∀ t, Circle.exp (F t) = χ t := fun t => congrFun hF t
  have hadd : ∀ s t, F (s + t) = F s + F t := by
    intro s
    have key := cov.eq_of_comp_eq (g₁ := fun t => F (s + t) - F s - F t)
      (g₂ := fun _ => (0 : ℝ)) (by fun_prop) continuous_const (by
        funext t
        simp only [Function.comp_apply, Circle.exp_sub, hF', hmul, Circle.exp_zero]
        simp) 0 (by simp [hF0])
    intro t
    have := congrFun key t
    linarith
  have hlin : ∀ t, F t = F 1 * t := by
    intro t
    have := map_real_smul (AddMonoidHom.mk' F hadd) F.continuous t 1
    simpa [mul_comm] using this
  refine ⟨F 1, fun t => by rw [← hlin, hF'], ?_⟩
  intro τ hτ
  have key := cov.eq_of_comp_eq (g₁ := fun t : ℝ => τ * t) (g₂ := fun t => F 1 * t)
    (by fun_prop) (by fun_prop)
    (by funext t; simp only [Function.comp_apply]; rw [← hτ, ← hlin, hF']) 0 (by simp)
  simpa using congrFun key 1

theorem eq_of_forall_exp_mul_eq {s s' : ℂ}
    (h : ∀ t : ℝ, Complex.exp (s * t) = Complex.exp (s' * t)) : s = s' := by
  have hd : ∀ u : ℂ, HasDerivAt (fun t : ℝ => Complex.exp (u * t)) u 0 := by
    intro u
    have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul u).cexp
    simpa using this
  have e : (fun t : ℝ => Complex.exp (s * t)) = fun t : ℝ => Complex.exp (s' * t) := funext h
  have h' : HasDerivAt (fun t : ℝ => Complex.exp (s * t)) s' 0 := by rw [e]; exact hd s'
  exact (hd s).unique h'

theorem existsUnique_exp_of_continuous (χ : ℝ → ℂˣ) (hχ : Continuous χ)
    (hmul : ∀ s t, χ (s + t) = χ s * χ t) :
    ∃! s : ℂ, ∀ t : ℝ, (χ t : ℂ) = Complex.exp (s * t) := by
  refine existsUnique_of_exists_of_unique ?_
    (fun s s' hs hs' => eq_of_forall_exp_mul_eq fun t => by rw [← hs, ← hs'])
  have hc : Continuous fun t => (χ t : ℂ) := Units.continuous_val.comp hχ
  have hnpos : ∀ t, 0 < ‖(χ t : ℂ)‖ := fun t => norm_pos_iff.mpr (χ t).ne_zero

  have ℓadd : ∀ s t, Real.log ‖(χ (s + t) : ℂ)‖ =
      Real.log ‖(χ s : ℂ)‖ + Real.log ‖(χ t : ℂ)‖ := by
    intro s t
    rw [hmul, Units.val_mul, norm_mul]
    exact Real.log_mul (hnpos s).ne' (hnpos t).ne'
  have ℓcont : Continuous fun t => Real.log ‖(χ t : ℂ)‖ := hc.norm.log fun t => (hnpos t).ne'
  have ℓlin : ∀ t, Real.log ‖(χ t : ℂ)‖ = Real.log ‖(χ 1 : ℂ)‖ * t := by
    intro t
    have := map_real_smul (AddMonoidHom.mk' (fun t => Real.log ‖(χ t : ℂ)‖) ℓadd) ℓcont t 1
    simpa [mul_comm] using this

  let u : ℝ → Circle := fun t => ⟨(χ t : ℂ) / (‖(χ t : ℂ)‖ : ℂ),
    mem_sphere_zero_iff_norm.2 (by simp [(hnpos t).ne'])⟩
  have ucont : Continuous u := by
    apply Continuous.subtype_mk
    exact hc.div (Complex.continuous_ofReal.comp hc.norm) fun t => by
      exact_mod_cast (hnpos t).ne'
  have umul : ∀ s t, u (s + t) = u s * u t := by
    intro s t
    apply Circle.coe_injective
    rw [Circle.coe_mul]
    show (χ (s + t) : ℂ) / (‖(χ (s + t) : ℂ)‖ : ℂ) =
      (χ s : ℂ) / (‖(χ s : ℂ)‖ : ℂ) * ((χ t : ℂ) / (‖(χ t : ℂ)‖ : ℂ))
    rw [hmul, Units.val_mul, norm_mul, Complex.ofReal_mul, mul_div_mul_comm]
  obtain ⟨τ, hτ, -⟩ := existsUnique_circleExp_of_continuous u ucont umul
  refine ⟨Real.log ‖(χ 1 : ℂ)‖ + τ * I, fun t => ?_⟩
  have h1 : (χ t : ℂ) = (‖(χ t : ℂ)‖ : ℂ) * (u t : ℂ) := by
    show _ = _ * (_ / _)
    rw [mul_div_cancel₀]
    exact_mod_cast (hnpos t).ne'
  have h2 : (‖(χ t : ℂ)‖ : ℂ) = Complex.exp ((Real.log ‖(χ 1 : ℂ)‖ * t : ℝ)) := by
    rw [← ℓlin, ← Complex.ofReal_exp, Real.exp_log (hnpos t)]
  rw [h1, h2, hτ t, Circle.coe_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end GroundTheory.Global
end

section -- merged from GroundTheory.GlobalFields.TateThesis.DegreeOnePrimes
namespace GroundTheory.Global

open NumberField IsDedekindDomain Filter Topology Set

noncomputable section

theorem card_primesOver_le_finrank {R S : Type*} [CommRing R] [IsDomain R] [CommRing S]
    [Algebra R S] [Module.Finite R S] [Module.Flat R S] (p : Ideal R) [p.IsPrime]
    [Finite (p.primesOver S)] :
    Nat.card (p.primesOver S) ≤ Module.finrank R S := by
  classical
  let _ := Fintype.ofFinite (p.primesOver S)
  rw [← Ideal.sum_ramification_inertia_eq_finrank p S, Nat.card_eq_fintype_card,
    Fintype.card_eq_sum_ones]
  refine Finset.sum_le_sum fun q _ => ?_
  exact Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (Ideal.ramificationIdx_pos (R := R) q.1).ne' (Ideal.inertiaDeg_pos q.1 R).ne')

variable {K L : Type*} [Field L] [NumberField L]

def rationalPrimeUnder (w : HeightOneSpectrum (𝓞 L)) : ℕ :=
  Ideal.absNorm (w.asIdeal.under ℤ)

omit [NumberField L] in
theorem under_int_ne_bot (w : HeightOneSpectrum (𝓞 L)) : w.asIdeal.under ℤ ≠ ⊥ :=
  mt Ideal.eq_bot_of_comap_eq_bot w.ne_bot


omit [NumberField L] in
theorem rationalPrimeUnder_prime (w : HeightOneSpectrum (𝓞 L)) : (rationalPrimeUnder w).Prime :=
  (Int.prime_absNorm _).mpr (Ideal.prime_of_isPrime (under_int_ne_bot w) inferInstance)


omit [NumberField L] in
theorem span_rationalPrimeUnder (w : HeightOneSpectrum (𝓞 L)) :
    Ideal.span {((rationalPrimeUnder w : ℕ) : ℤ)} = w.asIdeal.under ℤ :=
  Int.ideal_span_absNorm_eq_self _

theorem absNorm_eq_rationalPrimeUnder_pow (w : HeightOneSpectrum (𝓞 L)) :
    Ideal.absNorm w.asIdeal = rationalPrimeUnder w ^ w.asIdeal.inertiaDeg ℤ :=
  (Ideal.absNorm_pow_inertiaDeg (w.asIdeal.under ℤ) w.asIdeal).symm

theorem rationalPrimeUnder_le_absNorm (w : HeightOneSpectrum (𝓞 L)) :
    rationalPrimeUnder w ≤ Ideal.absNorm w.asIdeal := by
  rw [absNorm_eq_rationalPrimeUnder_pow]
  exact Nat.le_self_pow (Ideal.inertiaDeg_pos w.asIdeal ℤ).ne' _

theorem sq_rationalPrimeUnder_le_absNorm {w : HeightOneSpectrum (𝓞 L)}
    (hw : ¬ (Ideal.absNorm w.asIdeal).Prime) :
    rationalPrimeUnder w ^ 2 ≤ Ideal.absNorm w.asIdeal := by
  have hf := Ideal.inertiaDeg_pos w.asIdeal ℤ
  rw [absNorm_eq_rationalPrimeUnder_pow] at hw ⊢
  have hf1 : w.asIdeal.inertiaDeg ℤ ≠ 1 := by
    intro h
    rw [h, pow_one] at hw
    exact hw (rationalPrimeUnder_prime w)
  exact Nat.pow_le_pow_right (rationalPrimeUnder_prime w).pos (by omega)

theorem finite_and_card_fiber_rationalPrimeUnder_le (n : ℕ) :
    Finite {w : HeightOneSpectrum (𝓞 L) // rationalPrimeUnder w = n} ∧
      Nat.card {w : HeightOneSpectrum (𝓞 L) // rationalPrimeUnder w = n} ≤
        Module.finrank ℤ (𝓞 L) := by
  rcases isEmpty_or_nonempty {w : HeightOneSpectrum (𝓞 L) // rationalPrimeUnder w = n} with h | h
  · exact ⟨inferInstance, by simp⟩
  obtain ⟨w₀⟩ := h
  set P := w₀.1.asIdeal.under ℤ with hPdef
  have : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance (under_int_ne_bot w₀.1)
  have : Finite (P.primesOver (𝓞 L)) := (IsDedekindDomain.primesOver_finite P (𝓞 L)).to_subtype
  have hP : ∀ w : {w : HeightOneSpectrum (𝓞 L) // rationalPrimeUnder w = n},
      w.1.asIdeal.under ℤ = P := by
    intro w
    rw [hPdef, ← span_rationalPrimeUnder, ← span_rationalPrimeUnder, w.2, w₀.2]
  let f : {w : HeightOneSpectrum (𝓞 L) // rationalPrimeUnder w = n} → P.primesOver (𝓞 L) :=
    fun w => ⟨w.1.asIdeal, w.1.isPrime, ⟨(hP w).symm⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val hab))
  exact ⟨Finite.of_injective f hf,
    (Nat.card_le_card_of_injective f hf).trans (card_primesOver_le_finrank P)⟩

theorem summable_of_le_rationalPrimeUnder (g : HeightOneSpectrum (𝓞 L) → ℝ) {h : ℕ → ℝ}
    (hg : ∀ w, 0 ≤ g w) (hh0 : ∀ n, 0 ≤ h n) (hh : Summable h)
    (hgh : ∀ w, g w ≤ h (rationalPrimeUnder w)) : Summable g := by
  classical
  rw [← (Equiv.sigmaFiberEquiv (rationalPrimeUnder (L := L))).summable_iff]
  refine (summable_sigma_of_nonneg
    (f := fun x => g (Equiv.sigmaFiberEquiv (rationalPrimeUnder (L := L)) x))
    (fun _ => hg _)).mpr ⟨fun n => ?_, ?_⟩
  · have := (finite_and_card_fiber_rationalPrimeUnder_le (L := L) n).1
    exact Summable.of_finite
  refine Summable.of_nonneg_of_le (fun n => tsum_nonneg fun _ => hg _) (fun n => ?_)
    (hh.mul_left ((Module.finrank ℤ (𝓞 L) : ℕ) : ℝ))
  obtain ⟨hfin, hcard⟩ := finite_and_card_fiber_rationalPrimeUnder_le (L := L) n
  let _ := Fintype.ofFinite {w : HeightOneSpectrum (𝓞 L) // rationalPrimeUnder w = n}
  rw [tsum_fintype]
  calc ∑ y : {w : HeightOneSpectrum (𝓞 L) // rationalPrimeUnder w = n},
        g (Equiv.sigmaFiberEquiv rationalPrimeUnder ⟨n, y⟩)
      ≤ ∑ _y : {w : HeightOneSpectrum (𝓞 L) // rationalPrimeUnder w = n}, h n :=
        Finset.sum_le_sum fun y _ => by
          simpa [Equiv.sigmaFiberEquiv, y.2] using hgh y.1
    _ = (Nat.card {w : HeightOneSpectrum (𝓞 L) // rationalPrimeUnder w = n} : ℝ) * h n := by
        simp [Nat.card_eq_fintype_card]
    _ ≤ (Module.finrank ℤ (𝓞 L) : ℝ) * h n :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hh0 n)

theorem one_le_absNorm (w : HeightOneSpectrum (𝓞 L)) : 1 ≤ Ideal.absNorm w.asIdeal :=
  (rationalPrimeUnder_prime w).one_le.trans (rationalPrimeUnder_le_absNorm w)

theorem summable_absNorm_rpow_neg {s : ℝ} (hs : 1 < s) :
    Summable fun w : HeightOneSpectrum (𝓞 L) => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s) := by
  refine summable_of_le_rationalPrimeUnder _ (h := fun n : ℕ => (n : ℝ) ^ (-s))
    (fun _ => by positivity) (fun _ => by positivity)
    (Real.summable_nat_rpow.mpr (by linarith)) (fun w => ?_)
  exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (rationalPrimeUnder_prime w).pos)
    (by exact_mod_cast rationalPrimeUnder_le_absNorm w) (by linarith)

theorem summable_absNorm_rpow_neg_of_not_prime {s : ℝ} (hs : 1 / 2 < s) :
    Summable fun w : {w : HeightOneSpectrum (𝓞 L) // ¬ (Ideal.absNorm w.asIdeal).Prime} =>
      (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-s) := by
  refine (summable_subtype_iff_indicator
    (s := {w : HeightOneSpectrum (𝓞 L) | ¬ (Ideal.absNorm w.asIdeal).Prime})
    (f := fun w : HeightOneSpectrum (𝓞 L) => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s))).mpr ?_
  refine summable_of_le_rationalPrimeUnder _ (h := fun n : ℕ => (n : ℝ) ^ (-(2 * s)))
    (fun _ => Set.indicator_nonneg (fun _ _ => by positivity) _) (fun _ => by positivity)
    (Real.summable_nat_rpow.mpr (by linarith)) (fun w => ?_)
  by_cases hw : w ∈ {w : HeightOneSpectrum (𝓞 L) | ¬ (Ideal.absNorm w.asIdeal).Prime}
  · rw [Set.indicator_of_mem hw]
    have hp : (0 : ℝ) < rationalPrimeUnder w := by exact_mod_cast (rationalPrimeUnder_prime w).pos
    have hle : ((rationalPrimeUnder w : ℕ) : ℝ) ^ (2 : ℝ) ≤ (Ideal.absNorm w.asIdeal : ℝ) := by
      rw [Real.rpow_two]
      exact_mod_cast sq_rationalPrimeUnder_le_absNorm hw
    calc (Ideal.absNorm w.asIdeal : ℝ) ^ (-s)
        ≤ (((rationalPrimeUnder w : ℕ) : ℝ) ^ (2 : ℝ)) ^ (-s) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hle (by linarith)
      _ = ((rationalPrimeUnder w : ℕ) : ℝ) ^ (-(2 * s)) := by
          rw [← Real.rpow_mul hp.le]; ring_nf
  · rw [Set.indicator_of_notMem hw]
    positivity

theorem summable_absNorm_rpow_neg_subtype (S : Set (HeightOneSpectrum (𝓞 L))) {s : ℝ}
    (hs : 1 < s) : Summable fun w : S => (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-s) :=
  (summable_absNorm_rpow_neg hs).subtype (fun w => w ∈ S)

section relative

variable (K L) [Field K] [NumberField K] [Algebra K L]

def degreeOnePrimes : Set (HeightOneSpectrum (𝓞 L)) :=
  {w | w.asIdeal.inertiaDeg (𝓞 K) = 1}

def higherDegreePrimes : Set (HeightOneSpectrum (𝓞 L)) :=
  {w | 2 ≤ w.asIdeal.inertiaDeg (𝓞 K)}

theorem compl_degreeOnePrimes : (degreeOnePrimes K L)ᶜ = higherDegreePrimes K L := by
  ext w
  have := Ideal.inertiaDeg_pos w.asIdeal (𝓞 K)
  simp only [degreeOnePrimes, higherDegreePrimes, mem_compl_iff, mem_ofPred_eq]
  omega

variable {K L}

theorem not_prime_absNorm_of_mem_higherDegreePrimes {w : HeightOneSpectrum (𝓞 L)}
    (hw : w ∈ higherDegreePrimes K L) : ¬ (Ideal.absNorm w.asIdeal).Prime := by
  rw [← Ideal.absNorm_pow_inertiaDeg (w.asIdeal.under (𝓞 K)) w.asIdeal]
  have : 2 ≤ w.asIdeal.inertiaDeg (𝓞 K) := hw
  exact Nat.Prime.not_prime_pow' (by omega)

theorem higherDegreePrimes_subset :
    higherDegreePrimes K L ⊆ {w : HeightOneSpectrum (𝓞 L) | ¬ (Ideal.absNorm w.asIdeal).Prime} :=
  fun _ hw => not_prime_absNorm_of_mem_higherDegreePrimes hw

theorem summable_indicator_not_prime {s : ℝ} (hs : 1 / 2 < s) :
    Summable ({w : HeightOneSpectrum (𝓞 L) | ¬ (Ideal.absNorm w.asIdeal).Prime}.indicator
      fun w => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s)) :=
  (summable_subtype_iff_indicator
    (s := {w : HeightOneSpectrum (𝓞 L) | ¬ (Ideal.absNorm w.asIdeal).Prime})
    (f := fun w : HeightOneSpectrum (𝓞 L) => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s))).mp
    (summable_absNorm_rpow_neg_of_not_prime hs)


variable (K L) in
theorem summable_higherDegreePrimes {s : ℝ} (hs : 1 / 2 < s) :
    Summable fun w : higherDegreePrimes K L => (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-s) := by
  refine (summable_subtype_iff_indicator (s := higherDegreePrimes K L)
    (f := fun w : HeightOneSpectrum (𝓞 L) => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s))).mpr ?_
  refine Summable.of_nonneg_of_le (fun w => indicator_nonneg (fun _ _ => by positivity) w)
    (fun w => ?_) (summable_indicator_not_prime hs)
  exact indicator_le_indicator_of_subset higherDegreePrimes_subset (fun _ => by positivity) w


variable (K L) in
theorem primeIdealZetaSum_higherDegreePrimes_le :
    ∃ C : ℝ, ∀ s : ℝ, 1 ≤ s → (higherDegreePrimes K L).primeIdealZetaSum s ≤ C := by
  refine ⟨∑' w, {w : HeightOneSpectrum (𝓞 L) | ¬ (Ideal.absNorm w.asIdeal).Prime}.indicator
    (fun w : HeightOneSpectrum (𝓞 L) => (Ideal.absNorm w.asIdeal : ℝ) ^ (-(1 : ℝ))) w,
    fun s hs => ?_⟩
  have h1 := summable_indicator_not_prime (L := L) (s := 1) (by norm_num)
  have hs' := (summable_subtype_iff_indicator (s := higherDegreePrimes K L)
    (f := fun w : HeightOneSpectrum (𝓞 L) => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s))).mp
    (summable_higherDegreePrimes K L (by linarith))
  rw [Set.primeIdealZetaSum_def, tsum_subtype (higherDegreePrimes K L)
    (fun w : HeightOneSpectrum (𝓞 L) => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s))]
  refine Summable.tsum_le_tsum (fun w => ?_) hs' h1
  by_cases hw : w ∈ higherDegreePrimes K L
  · rw [indicator_of_mem hw, indicator_of_mem (higherDegreePrimes_subset hw)]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast one_le_absNorm w) (by linarith)
  · rw [indicator_of_notMem hw]
    exact indicator_nonneg (fun _ _ => by positivity) w


end relative

end

end GroundTheory.Global
end
