module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.XSmulMemWeightedHomogeneousSubmodule
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerIntegralFromISlashChangeOfVariables
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerIntegralFromISlashChangeOfVariables
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
noncomputable section
namespace GlobalTheory.EichlerChange

lemma exists_ball (z : ℂ) (hz : 0 < z.im) :
    ∃ (c : ℂ) (r : ℝ), Metric.ball c r ⊆ {u : ℂ | 0 < u.im} ∧ Complex.I ∈ Metric.ball c r ∧
      z ∈ Metric.ball c r := by
  have key : ∀ (u : ℂ) (R : ℝ), 0 < u.im → 0 < R → u.re ^ 2 + u.im ^ 2 < 2 * R * u.im →
      u ∈ Metric.ball ((R : ℂ) * Complex.I) R := by
    intro u R hu hR h
    rw [Metric.mem_ball, Complex.dist_eq, ← sq_lt_sq₀ (norm_nonneg _) hR.le, Complex.sq_norm,
      Complex.normSq_apply]
    simp
    nlinarith
  set a := (z.re ^ 2 + z.im ^ 2) / z.im with ha
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a * z.im = z.re ^ 2 + z.im ^ 2 := by rw [ha]; field_simp
  refine ⟨((a + 1 : ℝ) : ℂ) * Complex.I, a + 1, ?_, key _ _ (by simp) (by linarith) ?_,
    key _ _ hz (by linarith) ?_⟩
  · intro u hu
    rw [Metric.mem_ball, Complex.dist_eq] at hu
    have := (Complex.abs_im_le_norm _).trans_lt hu
    simp at this
    have := (abs_lt.1 this).1
    show 0 < u.im
    linarith
  · simp; linarith
  · nlinarith [mul_nonneg ha0 hz.le]

lemma hasDerivAt_segInt (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g {z : ℂ | 0 < z.im}) (z : ℂ)
    (hz : 0 < z.im) :
    HasDerivAt (fun τ : ℂ => ∫ t in (0 : ℝ)..1,
      g (Complex.I + t * (τ - Complex.I)) * (τ - Complex.I)) (g z) z := by
  obtain ⟨c, r, hB, hI, hzB⟩ := exists_ball z hz
  obtain ⟨G, hG⟩ := (hg.mono hB).isExactOn_ball
  refine ((hG z hzB).sub_const (G Complex.I)).congr_of_eventuallyEq ?_
  filter_upwards [Metric.isOpen_ball.mem_nhds hzB] with τ hτ
  have hmem : ∀ t ∈ Set.uIcc (0 : ℝ) 1, Complex.I + t * (τ - Complex.I) ∈ Metric.ball c r := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    simpa using (convex_ball c r).add_smul_sub_mem hI hτ ht
  have hd : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => G (Complex.I + s * (τ - Complex.I)))
        (g (Complex.I + t * (τ - Complex.I)) * (τ - Complex.I)) t := by
    intro t ht
    have h1 : HasDerivAt (fun u : ℂ => Complex.I + u * (τ - Complex.I)) (τ - Complex.I) (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const (τ - Complex.I)).const_add Complex.I
    exact (HasDerivAt.comp (t : ℂ) (h₂ := G) (hG _ (hmem t ht)) h1).comp_ofReal
  have hc : ContinuousOn (fun t : ℝ => g (Complex.I + t * (τ - Complex.I)) * (τ - Complex.I))
      (Set.uIcc 0 1) := by
    refine ContinuousOn.mul ?_ continuousOn_const
    exact (hg.continuousOn.mono hB).comp (f := fun t : ℝ => Complex.I + t * (τ - Complex.I))
      (by fun_prop) hmem
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  simp

def ecoef (w : ℕ) (h : ℍ → ℂ) (n : ℕ) (v : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (h ∘ ofComplex) (Complex.I + t * (v - Complex.I)) *
    (-(Complex.I + t * (v - Complex.I))) ^ (w - n) * (v - Complex.I)

lemma coeff_eichler (w : ℕ) (h : ℍ → ℂ) (τ : ℍ) (n : ℕ) :
    (eichler w h τ).coeff n = (w.choose n : ℂ) * ecoef w h n τ := by
  unfold eichler ecoef
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hn
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by simpa using hn)]; simp

lemma hasDerivAt_ecoef (w : ℕ) (h : ℍ → ℂ) (hh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h) (n : ℕ) (z : ℂ)
    (hz : 0 < z.im) :
    HasDerivAt (ecoef w h n) ((h ∘ ofComplex) z * (-z) ^ (w - n)) z :=
  hasDerivAt_segInt (fun u => (h ∘ ofComplex) u * (-u) ^ (w - n))
    ((UpperHalfPlane.mdifferentiable_iff.1 hh).mul (by fun_prop)) z hz

lemma polySlash_apply (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w g p = ∑ i ∈ Finset.range (w + 1), p.coeff i •
      ((C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)) ^ i *
        (C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)) ^ (w - i)) := by
  unfold slP
  rw [LinearMap.sum_apply]
  rfl

lemma polySlash_pow (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (s z u : ℂ)
    (h1 : (g 0 0 : ℂ) - s * g 1 0 = u) (h2 : (g 0 1 : ℂ) - s * g 1 1 = -z * u) :
    slP w g ((X + C (-s)) ^ w) = C (u ^ w) * (X + C (-z)) ^ w := by
  have e : C u * (X + C (-z)) = (C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)) +
      C (-s) * (C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)) := by
    have e1 := congrArg C h1
    have e2 := congrArg C h2
    simp only [map_sub, map_mul, map_neg] at e1 e2 ⊢
    linear_combination (-X) * e1 - e2
  rw [C_pow, ← mul_pow, e, polySlash_apply]
  conv_rhs => rw [add_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_X_add_C_pow, smul_eq_C_mul, mul_pow, C_mul, C_pow, map_natCast]
  ring

lemma coe_smul_eq (σ : SL(2, ℤ)) (τ : ℍ) :
    ((σ • τ : ℍ) : ℂ) = ((mat σ 0 0 : ℂ) * τ + mat σ 0 1) / ((mat σ 1 0 : ℂ) * τ + mat σ 1 1) := by
  rw [coe_specialLinearGroup_apply]
  simp

theorem polySlash_eichler_smul (k : ℕ) (hk : 2 ≤ k) (f : ℍ → ℂ) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (σ : SL(2, ℤ)) : ∃ C : ℂ[X], ∀ τ : ℍ,
      slP (k - 2) (mat σ) (eichler (k - 2) f (σ • τ)) = eichler (k - 2) (f ∣[(k : ℤ)] σ) τ + C := by
  obtain ⟨w, rfl⟩ : ∃ w, k = w + 2 := ⟨k - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  set h : ℍ → ℂ := f ∣[((w + 2 : ℕ) : ℤ)] σ with hdef
  have hh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h := by
    rw [hdef, ModularForm.SL_slash]
    exact hf.slash _ _
  set a : ℂ := ((mat σ 0 0 : ℤ) : ℂ) with ha
  set b : ℂ := ((mat σ 0 1 : ℤ) : ℂ) with hb
  set c : ℂ := ((mat σ 1 0 : ℤ) : ℂ) with hc
  set d : ℂ := ((mat σ 1 1 : ℤ) : ℂ) with hd
  have hdet : a * d - b * c = 1 := by
    have := σ.det_coe
    rw [Matrix.det_fin_two] at this
    rw [ha, hb, hc, hd]
    exact_mod_cast this
  refine ⟨slP w (mat σ) (eichler w f (σ • I)) - eichler w h I, fun τ => ?_⟩
  ext n
  set q : ℕ → ℂ := fun i => ((C a * X + C b) ^ i * (C c * X + C d) ^ (w - i)).coeff n with hq
  have hslP : ∀ p : ℂ[X], (slP w (mat σ) p).coeff n = ∑ i ∈ Finset.range (w + 1), p.coeff i * q i := by
    intro p
    rw [polySlash_apply, finsetSum_coeff]
    simp only [AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]
    rfl
  set Φ : ℂ → ℂ := fun v => ∑ i ∈ Finset.range (w + 1),
      (w.choose i : ℂ) * ecoef w f i ((a * v + b) / (c * v + d)) * q i -
    (w.choose n : ℂ) * ecoef w h n v with hΦ
  have hΦ1 : ∀ τ : ℍ, Φ τ = (slP w (mat σ) (eichler w f (σ • τ))).coeff n - (eichler w h τ).coeff n := by
    intro τ
    simp only [hΦ, hslP, coeff_eichler, coe_smul_eq]
    rfl
  have hder : ∀ z ∈ {z : ℂ | 0 < z.im}, HasDerivAt Φ 0 z := by
    intro z hz
    obtain ⟨τ, rfl⟩ : ∃ τ : ℍ, (τ : ℂ) = z := ⟨⟨z, hz⟩, rfl⟩
    have hj : c * τ + d ≠ 0 := by
      rw [hc, hd, ← ModularGroup.denom_apply]
      exact denom_ne_zero _ _
    have hs : ((σ • τ : ℍ) : ℂ) = (a * τ + b) / (c * τ + d) := coe_smul_eq σ τ
    have hm : HasDerivAt (fun v : ℂ => (a * v + b) / (c * v + d)) ((c * τ + d)⁻¹ ^ 2) (τ : ℂ) := by
      have h1 : HasDerivAt (fun v : ℂ => a * v + b) a (τ : ℂ) := by
        simpa using ((hasDerivAt_id (τ : ℂ)).const_mul a).add_const b
      have h2 : HasDerivAt (fun v : ℂ => c * v + d) c (τ : ℂ) := by
        simpa using ((hasDerivAt_id (τ : ℂ)).const_mul c).add_const d
      refine (h1.fun_div h2 hj).congr_deriv ?_
      rw [inv_pow, div_eq_mul_inv]
      linear_combination ((c * τ + d) ^ 2)⁻¹ * hdet
    have hA : ∀ i, HasDerivAt (fun v : ℂ => ecoef w f i ((a * v + b) / (c * v + d)))
        (f (σ • τ) * (-((σ • τ : ℍ) : ℂ)) ^ (w - i) * (c * τ + d)⁻¹ ^ 2) (τ : ℂ) := by
      intro i
      have := hasDerivAt_ecoef w f hf i _ (σ • τ).im_pos
      simp only [Function.comp_apply, ofComplex_apply] at this
      exact HasDerivAt.comp (τ : ℂ) (h₂ := ecoef w f i) (by rw [← hs]; exact this) hm
    have hB := hasDerivAt_ecoef w h hh n _ τ.im_pos
    simp only [Function.comp_apply, ofComplex_apply] at hB
    have hP := congrArg (fun p : ℂ[X] => p.coeff n)
      (polySlash_pow w (mat σ) ((σ • τ : ℍ) : ℂ) τ (c * τ + d)⁻¹
        (by rw [hs, ← ha, ← hc]; rw [div_eq_mul_inv]
            linear_combination (-a) * mul_inv_cancel₀ hj + (c * τ + d)⁻¹ * hdet)
        (by rw [hs, ← hb, ← hd]; rw [div_eq_mul_inv]
            linear_combination (-b) * mul_inv_cancel₀ hj - (c * τ + d)⁻¹ * τ * hdet))
    simp only [hslP, coeff_C_mul, coeff_X_add_C_pow] at hP
    have hv : h τ = f (σ • τ) * (c * τ + d)⁻¹ ^ (w + 2) := by
      rw [hdef, ModularForm.SL_slash_apply, ModularGroup.denom_apply, zpow_neg, zpow_natCast, inv_pow]
    refine ((HasDerivAt.fun_sum (u := Finset.range (w + 1)) fun i _ =>
      ((hA i).const_mul (w.choose i : ℂ)).mul_const (q i)).fun_sub
        (hB.const_mul (w.choose n : ℂ))).congr_deriv ?_
    have : ∑ i ∈ Finset.range (w + 1), (w.choose i : ℂ) *
        (f (σ • τ) * (-((σ • τ : ℍ) : ℂ)) ^ (w - i) * (c * τ + d)⁻¹ ^ 2) * q i =
        f (σ • τ) * (c * τ + d)⁻¹ ^ 2 * ∑ i ∈ Finset.range (w + 1),
          (-((σ • τ : ℍ) : ℂ)) ^ (w - i) * (w.choose i : ℂ) * q i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hP, hv]
    ring
  have hconst : Φ τ = Φ (I : ℍ) :=
    isOpen_upperHalfPlaneSet.is_const_of_deriv_eq_zero (convex_halfSpace_im_gt 0).isPreconnected
      (fun z hz => (hder z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hder z hz).deriv) τ.im_pos (I : ℍ).im_pos
  rw [hΦ1, hΦ1] at hconst
  rw [coeff_add, coeff_sub]
  linear_combination hconst

end GlobalTheory.EichlerChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerIntegralFromISlashChangeOfVariablesStatement
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eichlerIntegralFromI_slash_change_of_variables : ∀ (k : ℕ), 2 ≤ k → ∀ (f : ℍ → ℂ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → ∀ σ : SL(2, ℤ), ∃ C : ℂ[X], ∀ τ : ℍ, slP (k - 2) (mat σ) (eichler (k - 2) f (σ • τ)) = eichler (k - 2) (f ∣[(k : ℤ)] σ) τ + C := by
  first | exact @GlobalTheory.EichlerChange.polySlash_eichler_smul | exact GlobalTheory.EichlerChange.polySlash_eichler_smul | (intros; apply GlobalTheory.EichlerChange.polySlash_eichler_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PerfectPairingQuotients
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem exists_addChar_quotient {G : Type} [AddCommGroup G] (H : AddSubgroup G) (f : G → ℂ)
    (h0 : f 0 = 1) (hadd : ∀ x y, f (x + y) = f x * f y) (hH : ∀ x ∈ H, f x = 1) :
    ∃ χ : AddChar (G ⧸ H) ℂ, ∀ g : G, χ (g : G ⧸ H) = f g := by
  have hout : ∀ g : G, f (Quotient.out (g : G ⧸ H)) = f g := by
    intro g
    obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_mul H g
    rw [hh, hadd, hH _ h.2, mul_one]
  refine ⟨⟨fun q => f (Quotient.out q), ?_, ?_⟩, hout⟩
  · rw [← QuotientAddGroup.mk_zero, hout, h0]
  · intro a b
    induction a using QuotientAddGroup.induction_on
    induction b using QuotientAddGroup.induction_on
    rw [← QuotientAddGroup.mk_add, hout, hout, hout, hadd]

theorem exists_injective_addChar {G K : Type} [AddCommGroup G] [AddCommGroup K] (H : AddSubgroup G)
    (L : AddSubgroup K) (p : G → K → ℂ)
    (hl : ∀ x y z, p (x + y) z = p x z * p y z) (hr : ∀ x y z, p x (y + z) = p x y * p x z)
    (h0 : ∀ x, p x 0 = 1) (h0' : ∀ y, p 0 y = 1)
    (hH : ∀ g, g ∈ H ↔ ∀ k, p g k = 1) (hL : ∀ k ∈ L, ∀ g, p g k = 1) :
    ∃ Φ : G ⧸ H → AddChar (K ⧸ L) ℂ, Function.Injective Φ ∧
      ∀ (g : G) (k : K), Φ (g : G ⧸ H) (k : K ⧸ L) = p g k := by
  choose χ hχ using fun g : G =>
    exists_addChar_quotient L (p g) (h0 g) (hr g) (fun k hk => hL k hk g)
  have hout : ∀ (g : G) (k : K), p (Quotient.out (g : G ⧸ H)) k = p g k := by
    intro g k
    obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_mul H g
    rw [hh, hl, (hH _).1 h.2, mul_one]
  have hΦ : ∀ (g : G) (k : K), χ (Quotient.out (g : G ⧸ H)) (k : K ⧸ L) = p g k := by
    intro g k
    rw [hχ, hout]
  refine ⟨fun q => χ (Quotient.out q), ?_, hΦ⟩
  intro a b hab
  induction a using QuotientAddGroup.induction_on with | _ a
  induction b using QuotientAddGroup.induction_on with | _ b
  rw [QuotientAddGroup.eq, hH]
  intro k
  have h1 : p a k = p b k := by
    rw [← hΦ, ← hΦ]
    exact congrArg (fun ψ : AddChar (K ⧸ L) ℂ => ψ (k : K ⧸ L)) hab
  rw [hl, ← h1, ← hl, neg_add_cancel, h0']

theorem perfect_pairing_quotients : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (S A T₀ T : AddSubgroup X), (∀ a ∈ A, a ∈ S ↔ ∀ t ∈ T, γ a t = 1) → (∀ t ∈ T, t ∈ T₀ ↔ ∀ a ∈ A, γ a t = 1) → T₀.relIndex T ≠ 0 → S.relIndex A = T₀.relIndex T ∧ (∀ y : X, (∀ a ∈ A, a ∈ S → γ a y = 1) → ∃ t ∈ T, ∀ a ∈ A, γ a y = γ a t) ∧ ∀ t ∈ T, (∑ᶠ q : A ⧸ S.addSubgroupOf A, γ ((Quotient.out q : A) : X) t) = if t ∈ T₀ then (S.relIndex A : ℂ) else 0 := by
  intro R X M _ _ _ _ _ σ w γ W h S A T₀ T hS hT hfin
  have hS' : ∀ a : A, a ∈ S.addSubgroupOf A ↔ ∀ t : T, γ a t = 1 := by
    intro a
    rw [AddSubgroup.mem_addSubgroupOf, hS a a.2]
    simp
  have hT' : ∀ t : T, t ∈ T₀.addSubgroupOf T ↔ ∀ a : A, γ a t = 1 := by
    intro t
    rw [AddSubgroup.mem_addSubgroupOf, hT t t.2]
    simp
  obtain ⟨Φ, hΦi, hΦ⟩ := exists_injective_addChar (S.addSubgroupOf A) (T₀.addSubgroupOf T)
    (fun a t => γ a t) (fun x y z => h.add_left _ _ _) (fun x y z => h.add_right _ _ _)
    (fun x => h.zero_right _) (fun x => h.zero_left _) hS' (fun k hk => (hT' k).1 hk)
  obtain ⟨Ψ, hΨi, hΨ⟩ := exists_injective_addChar (T₀.addSubgroupOf T) (S.addSubgroupOf A)
    (fun t a => γ a t) (fun x y z => h.add_right _ _ _) (fun x y z => h.add_left _ _ _)
    (fun x => h.zero_left _) (fun x => h.zero_right _) hT' (fun k hk => (hS' k).1 hk)
  haveI : Finite (T ⧸ T₀.addSubgroupOf T) := Nat.finite_of_card_ne_zero hfin
  haveI : Finite (A ⧸ S.addSubgroupOf A) := Finite.of_injective Φ hΦi
  letI := Fintype.ofFinite (T ⧸ T₀.addSubgroupOf T)
  letI := Fintype.ofFinite (A ⧸ S.addSubgroupOf A)
  have c1 := Fintype.card_le_of_injective Φ hΦi
  have c2 := Fintype.card_le_of_injective Ψ hΨi
  have c3 := c2
  rw [AddChar.card_eq] at c1 c2
  have hc : Fintype.card (A ⧸ S.addSubgroupOf A) = Fintype.card (T ⧸ T₀.addSubgroupOf T) :=
    le_antisymm c1 c2
  have eA : S.relIndex A = Fintype.card (A ⧸ S.addSubgroupOf A) := Nat.card_eq_fintype_card
  have eT : T₀.relIndex T = Fintype.card (T ⧸ T₀.addSubgroupOf T) := Nat.card_eq_fintype_card
  refine ⟨by rw [eA, eT, hc], ?_, ?_⟩
  · intro y hy
    obtain ⟨χ, hχ⟩ := exists_addChar_quotient (S.addSubgroupOf A) (fun a : A => γ a y)
      (h.zero_left _) (fun a b => h.add_left _ _ _)
      (fun a ha => hy a a.2 (AddSubgroup.mem_addSubgroupOf.1 ha))
    have hb : Function.Bijective Ψ :=
      (Fintype.bijective_iff_injective_and_card Ψ).2 ⟨hΨi, by rw [AddChar.card_eq, hc]⟩
    obtain ⟨q, hq⟩ := hb.2 χ
    induction q using QuotientAddGroup.induction_on with | _ t
    refine ⟨t, t.2, fun a ha => ?_⟩
    have h1 := hΨ t ⟨a, ha⟩
    rw [hq, hχ] at h1
    exact h1
  · intro t ht
    rw [finsum_eq_sum_of_fintype]
    have h1 : ∀ q : A ⧸ S.addSubgroupOf A,
        γ ((Quotient.out q : A) : X) t = Ψ ((⟨t, ht⟩ : T) : T ⧸ T₀.addSubgroupOf T) q := by
      intro q
      conv_rhs => rw [← QuotientAddGroup.out_eq' q]
      rw [hΨ]
    rw [Finset.sum_congr rfl fun q _ => h1 q, AddChar.sum_eq_ite, eA]
    refine if_congr ?_ rfl rfl
    rw [hT t ht]
    constructor
    · intro h0 a ha
      have h2 := hΨ ⟨t, ht⟩ ⟨a, ha⟩
      rw [h0] at h2
      simpa using h2.symm
    · intro h0
      ext q
      rw [← h1, h0 _ (Quotient.out q).2]
      simp

end GlobalTheory.FinWeil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingCoeffNonnegOfEventuallyEvalNat
open Polynomial Filter Module

namespace GlobalTheory

attribute [local instance] MvPolynomial.gradedAlgebra

section Poly

theorem polynomial_eq_of_eventually_eval_nat {P Q : ℚ[X]}
    (h : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) = Q.eval (n : ℚ)) : P = Q := by
  apply eq_of_infinite_eval_eq
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  refine Set.Infinite.mono (s := (Nat.cast : ℕ → ℚ) '' Set.Ici N) ?_
    ((Set.Ici_infinite N).image Nat.cast_injective.injOn)
  rintro _ ⟨n, hn, rfl⟩
  exact hN n hn

theorem leadingCoeff_nonneg_of_eventually_eval_nat {P : ℚ[X]}
    (h : ∀ᶠ n : ℕ in atTop, 0 ≤ P.eval (n : ℚ)) : 0 ≤ P.leadingCoeff := by
  by_contra hneg
  push Not at hneg
  rcases le_or_gt P.degree 0 with h0 | h0
  · obtain ⟨n, hn⟩ := h.exists
    rw [eq_C_of_degree_le_zero h0] at hn hneg
    simp only [eval_C, leadingCoeff_C] at hn hneg
    exact absurd hn (not_le.2 hneg)
  · have := ((tendsto_atBot_of_leadingCoeff_nonpos h0 hneg.le).comp
      (tendsto_natCast_atTop_atTop (R := ℚ))).eventually (eventually_lt_atBot 0)
    obtain ⟨n, h1, h2⟩ := (h.and this).exists
    exact absurd h1 (not_le.2 h2)

theorem coeff_nonneg_of_eventually_eval_nat {P : ℚ[X]} {e : ℕ} (he : P.degree ≤ e)
    (h : ∀ᶠ n : ℕ in atTop, 0 ≤ P.eval (n : ℚ)) : 0 ≤ P.coeff e := by
  rcases he.eq_or_lt with he | he
  · rw [← natDegree_eq_of_degree_eq_some he]
    exact leadingCoeff_nonneg_of_eventually_eval_nat h
  · rw [coeff_eq_zero_of_degree_lt he]

theorem degree_le_of_eventually_eval_nat {P Q : ℚ[X]}
    (hP : ∀ᶠ n : ℕ in atTop, 0 ≤ P.eval (n : ℚ))
    (h : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) ≤ Q.eval (n : ℚ)) : P.degree ≤ Q.degree := by
  by_contra hlt
  push Not at hlt
  have hP0 : P ≠ 0 := by rintro rfl; simp at hlt
  have h1 : 0 ≤ (Q - P).leadingCoeff := leadingCoeff_nonneg_of_eventually_eval_nat (by
    filter_upwards [h] with n hn
    rw [eval_sub]; linarith)
  rw [leadingCoeff_sub_of_degree_lt' hlt] at h1
  have h2 := leadingCoeff_nonneg_of_eventually_eval_nat hP
  exact hP0 (leadingCoeff_eq_zero.1 (by linarith))

theorem exists_int_factorial_mul_coeff {e : ℕ} {P : ℚ[X]} (he : P.degree ≤ e)
    (h : ∀ᶠ n : ℕ in atTop, ∃ z : ℤ, P.eval (n : ℚ) = z) :
    ∃ z : ℤ, (e.factorial : ℚ) * P.coeff e = z := by
  induction e generalizing P with
  | zero =>
    obtain ⟨n, z, hz⟩ := h.exists
    refine ⟨z, ?_⟩
    rw [eq_C_of_degree_le_zero he] at hz
    simpa using hz
  | succ e ih =>
    have h1 := degree_comp_X_add_C_sub_lt P 1 (e + 1) he
    obtain ⟨z, hz⟩ := ih (P := P.comp (X + C 1) - P)
      (degree_le_iff_coeff_zero _ _ |>.2 fun m hm => (degree_lt_iff_coeff_zero _ _).1 h1 m
        (by exact_mod_cast hm)) (by
        filter_upwards [h, (tendsto_add_atTop_nat 1).eventually h] with n ⟨a, ha⟩ ⟨b, hb⟩
        refine ⟨b - a, ?_⟩
        simp only [eval_sub, eval_comp, eval_add, eval_X, eval_C]
        push_cast at hb ⊢
        rw [ha, hb])
    refine ⟨z, ?_⟩
    rw [← hz, coeff_comp_X_add_C_sub P 1 e he, Nat.factorial_succ]
    push_cast
    ring

end Poly

open MvPolynomial DirectSum

variable {ι k : Type*} [Field k]

noncomputable def quotPiece (I : Ideal (MvPolynomial ι k)) (n : ℤ) :
    Submodule k (MvPolynomial ι k ⧸ I) :=
  (weightedHomogeneousSubmodule k (fun _ : ι => (1 : ℤ)) n).map
    (Ideal.Quotient.mkₐ k I).toLinearMap

theorem weightedHomogeneousSubmodule_one_natCast (n : ℕ) :
    weightedHomogeneousSubmodule k (fun _ : ι => (1 : ℤ)) (n : ℤ) =
      homogeneousSubmodule ι k n := by
  ext p
  have : ∀ s : ι →₀ ℕ, Finsupp.weight (fun _ : ι => (1 : ℤ)) s =
      ((Finsupp.weight (1 : ι → ℕ) s : ℕ) : ℤ) := by
    intro s
    simp [Finsupp.weight_apply, Finsupp.sum]
  simp only [mem_weightedHomogeneousSubmodule, mem_homogeneousSubmodule, IsHomogeneous,
    IsWeightedHomogeneous, this, Nat.cast_inj]

theorem quotPiece_natCast (I : Ideal (MvPolynomial ι k)) (n : ℕ) :
    quotPiece I n = (homogeneousSubmodule ι k n).map (Ideal.Quotient.mkₐ k I).toLinearMap := by
  rw [quotPiece, weightedHomogeneousSubmodule_one_natCast]

theorem weightedHomogeneousComponent_one_mem {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) (n : ℤ) {p : MvPolynomial ι k}
    (hp : p ∈ I) : weightedHomogeneousComponent (fun _ : ι => (1 : ℤ)) n p ∈ I := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← sum_homogeneousComponent p, map_sum]
  refine I.sum_mem fun i _ => ?_
  have h1 : homogeneousComponent i p ∈ weightedHomogeneousSubmodule k (fun _ : ι => (1 : ℤ))
      (i : ℤ) := by
    rw [weightedHomogeneousSubmodule_one_natCast]
    exact homogeneousComponent_mem i p
  rw [weightedHomogeneousComponent_of_mem h1]
  split_ifs
  · have := hI i hp
    rwa [show (decompose (homogeneousSubmodule ι k) p i : MvPolynomial ι k) =
      homogeneousComponent i p from decomposition.decompose'_apply p i] at this
  · exact I.zero_mem

instance finite_homogeneousSubmodule' [Finite ι] (n : ℕ) :
    Module.Finite k (homogeneousSubmodule ι k n) := by
  letI := weightedDecomposition k (fun _ : ι => (1 : ℤ))
  rw [← weightedHomogeneousSubmodule_one_natCast]
  exact GradedHilbert.finite_piece _ (X_smul_mem_weightedHomogeneousSubmodule ι k) _

theorem exists_isHilbertPoly_quotPiece [Fintype ι] {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) :
    ∃ P : ℚ[X], IsHilbertPoly (quotPiece I) P ∧ P.degree < (Fintype.card ι : ℕ) := by
  letI := weightedDecomposition k (fun _ : ι => (1 : ℤ))
  have hfin := GradedHilbert.finite_piece _ (X_smul_mem_weightedHomogeneousSubmodule ι k)
  obtain ⟨P, hP, h⟩ := GradedHilbert.exists_polynomial_subquotient _
    (X_smul_mem_weightedHomogeneousSubmodule ι k) Finset.univ I ⊤ le_top
    (by
      intro n m hm
      have := weightedHomogeneousComponent_one_mem hI n hm
      rwa [← weightedDecomposition.decompose'_apply] at this) (by simp) (by simp)
  refine ⟨P, ⟨fun n => ?_, ?_⟩, hP⟩
  · haveI := hfin n
    unfold quotPiece
    infer_instance
  · filter_upwards [h] with n hn
    haveI := hfin n
    have e := GradedHilbert.finrank_map_add_finrank_inf_ker (Ideal.Quotient.mkₐ k I).toLinearMap
      (weightedHomogeneousSubmodule k (fun _ : ι => (1 : ℤ)) n)
    have e2 : LinearMap.ker (Ideal.Quotient.mkₐ k I).toLinearMap = I.restrictScalars k := by
      ext x; simp [Ideal.Quotient.eq_zero_iff_mem]
    rw [e2, inf_comm] at e
    rw [Submodule.restrictScalars_top, top_inf_eq, ← e] at hn
    rw [← hn, quotPiece]
    push_cast
    ring


open Classical in
noncomputable def idealHilbertPoly (I : Ideal (MvPolynomial ι k)) : ℚ[X] := by
  classical
  exact if h : ∃ P, IsHilbertPoly (quotPiece I) P then h.choose else 0

theorem isHilbertPoly_idealHilbertPoly [Finite ι] {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) :
    IsHilbertPoly (quotPiece I) (idealHilbertPoly I) := by
  cases nonempty_fintype ι
  have h : ∃ P, IsHilbertPoly (quotPiece I) P :=
    (exists_isHilbertPoly_quotPiece hI).imp fun _ h => h.1
  rw [idealHilbertPoly, dite_eq_left h]
  exact h.choose_spec

theorem eventually_finrank_quotPiece [Finite ι] {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) :
    ∀ᶠ n : ℕ in atTop, (finrank k (quotPiece I n) : ℚ) = (idealHilbertPoly I).eval (n : ℚ) := by
  have := (tendsto_natCast_atTop_atTop (R := ℤ)).eventually
    (isHilbertPoly_idealHilbertPoly hI).eventually_eq
  simpa using this

theorem finrank_quotPiece_add [Finite ι] (I : Ideal (MvPolynomial ι k)) (n : ℕ) :
    finrank k (quotPiece I n) +
      finrank k (I.restrictScalars k ⊓ homogeneousSubmodule ι k n : Submodule k _) =
      finrank k (homogeneousSubmodule ι k n) := by
  have e := GradedHilbert.finrank_map_add_finrank_inf_ker (Ideal.Quotient.mkₐ k I).toLinearMap
    (homogeneousSubmodule ι k n)
  have e2 : LinearMap.ker (Ideal.Quotient.mkₐ k I).toLinearMap = I.restrictScalars k := by
    ext x; simp [Ideal.Quotient.eq_zero_iff_mem]
  rw [e2, inf_comm] at e
  rw [quotPiece_natCast, e]

theorem eventually_idealHilbertPoly_nonneg [Finite ι] {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) :
    ∀ᶠ n : ℕ in atTop, 0 ≤ (idealHilbertPoly I).eval (n : ℚ) := by
  filter_upwards [eventually_finrank_quotPiece hI] with n hn
  rw [← hn]
  positivity

noncomputable def hilbertDegree (I : Ideal (MvPolynomial ι k)) : ℕ :=
  ⌊((idealHilbertPoly I).natDegree.factorial : ℚ) * (idealHilbertPoly I).leadingCoeff⌋₊

theorem cast_hilbertDegree [Finite ι] {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) :
    (hilbertDegree I : ℚ) =
      ((idealHilbertPoly I).natDegree.factorial : ℚ) * (idealHilbertPoly I).leadingCoeff := by
  obtain ⟨z, hz⟩ := exists_int_factorial_mul_coeff (P := idealHilbertPoly I)
    degree_le_natDegree (by
      filter_upwards [eventually_finrank_quotPiece hI] with n hn
      exact ⟨finrank k (quotPiece I n), by rw [← hn]; simp⟩)
  have h0 : 0 ≤ ((idealHilbertPoly I).natDegree.factorial : ℚ) *
      (idealHilbertPoly I).leadingCoeff := mul_nonneg (by positivity)
    (leadingCoeff_nonneg_of_eventually_eval_nat (eventually_idealHilbertPoly_nonneg hI))
  rw [hilbertDegree, leadingCoeff, hz]
  rw [leadingCoeff, hz] at h0
  lift z to ℕ using (by exact_mod_cast h0)
  simp

theorem cast_hilbertDegree_of_degree_eq [Finite ι] {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) {e : ℕ}
    (he : (idealHilbertPoly I).degree = e) :
    (hilbertDegree I : ℚ) = (e.factorial : ℚ) * (idealHilbertPoly I).coeff e := by
  rw [cast_hilbertDegree hI, leadingCoeff, natDegree_eq_of_degree_eq_some he]

theorem hilbertDegree_eq_zero_iff [Finite ι] {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) :
    hilbertDegree I = 0 ↔ idealHilbertPoly I = 0 := by
  rw [← Nat.cast_eq_zero (R := ℚ), cast_hilbertDegree hI, mul_eq_zero, leadingCoeff_eq_zero]
  simp [Nat.factorial_ne_zero]

def projComponents (I : Ideal (MvPolynomial ι k)) : Set (Ideal (MvPolynomial ι k)) :=
  {P | P ∈ I.minimalPrimes ∧ ∃ i, (X i : MvPolynomial ι k) ∉ P}

theorem finite_projComponents [Finite ι] (I : Ideal (MvPolynomial ι k)) :
    (projComponents I).Finite :=
  I.finite_minimalPrimes_of_isNoetherianRing.subset fun _ h => h.1

noncomputable def projSetDegree [Finite ι] (I : Ideal (MvPolynomial ι k)) : ℕ :=
  ∑ P ∈ (finite_projComponents I).toFinset, hilbertDegree P

def IsProjPureDim (I : Ideal (MvPolynomial ι k)) (e : ℕ) : Prop :=
  ∀ P ∈ projComponents I, ringKrullDim (MvPolynomial ι k ⧸ P) = (e + 1 : ℕ)

def projPoints (I : Ideal (MvPolynomial ι k)) : Set (Projectivization k (ι → k)) :=
  {y | ∀ g ∈ I, MvPolynomial.eval y.rep g = 0}

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorOnCocycleMapsCocycleCoboundaryConj
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorOnCocycleMapsCocycleCoboundaryConj
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.HkC

def lA (g : Matrix (Fin 2) (Fin 2) ℤ) : ℂ[X] := C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)

def lB (g : Matrix (Fin 2) (Fin 2) ℤ) : ℂ[X] := C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)

theorem polySlash_apply (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w g p = ∑ i ∈ Finset.range (w + 1), C (p.coeff i) * (lA g ^ i * lB g ^ (w - i)) := by
  rw [slP, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.comp_apply, lcoeff_apply, LinearMap.toSpanSingleton_apply, ← C_mul']
  rfl

theorem polySlash_monomial (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (k : ℕ) (c : ℂ) (hk : k ≤ w) :
    slP w g (monomial k c) = C c * (lA g ^ k * lB g ^ (w - k)) := by
  rw [polySlash_apply, Finset.sum_eq_single k]
  · simp
  · intro i _ hik; simp [coeff_monomial, Ne.symm hik]
  · intro h; simp at h; omega

theorem mem_degLT_iff {w : ℕ} {p : ℂ[X]} : p ∈ degreeLT ℂ (w + 1) ↔ p.natDegree ≤ w := by
  rw [mem_degreeLT]
  by_cases hp : p = 0
  · subst hp; simp
  · rw [degree_eq_natDegree hp]; norm_cast; omega

theorem natDegree_lA (g : Matrix (Fin 2) (Fin 2) ℤ) : (lA g).natDegree ≤ 1 := natDegree_linear_le
theorem natDegree_lB (g : Matrix (Fin 2) (Fin 2) ℤ) : (lB g).natDegree ≤ 1 := natDegree_linear_le

theorem natDegree_slP_le (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) : (slP w g p).natDegree ≤ w := by
  rw [polySlash_apply]
  apply natDegree_sum_le_of_forall_le
  intro i hi
  have hi' : i ≤ w := by simp at hi; omega
  refine (natDegree_C_mul_le _ _).trans ?_
  refine natDegree_mul_le.trans ?_
  have h1 := natDegree_pow_le_of_le i (natDegree_lA g)
  have h2 := natDegree_pow_le_of_le (w - i) (natDegree_lB g)
  omega

theorem polySlash_mul (h : Matrix (Fin 2) (Fin 2) ℤ) (m n : ℕ) (q r : ℂ[X]) (hq : q.natDegree ≤ m)
    (hr : r.natDegree ≤ n) : slP (m + n) h (q * r) = slP m h q * slP n h r := by
  have eq := as_sum_range' q (m + 1) (by omega)
  have er := as_sum_range' r (n + 1) (by omega)
  rw [polySlash_apply m h q, polySlash_apply n h r, Finset.sum_mul_sum]
  conv_lhs => rw [eq, er, Finset.sum_mul_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  refine Finset.sum_congr rfl fun s hs => Finset.sum_congr rfl fun t ht => ?_
  simp only [Finset.mem_range] at hs ht
  rw [monomial_mul_monomial, polySlash_monomial _ _ _ _ (by omega)]
  have e : m + n - (s + t) = (m - s) + (n - t) := by omega
  rw [e, C_mul, pow_add, pow_add]; ring

theorem polySlash_pow (h : Matrix (Fin 2) (Fin 2) ℤ) (m : ℕ) (q : ℂ[X]) (hq : q.natDegree ≤ m) :
    ∀ k : ℕ, slP (m * k) h (q ^ k) = (slP m h q) ^ k := by
  intro k
  induction k with
  | zero => simp [polySlash_apply]
  | succ k ih =>
    rw [pow_succ, pow_succ, Nat.mul_succ,
      polySlash_mul h (m * k) m (q ^ k) q ((natDegree_pow_le_of_le k hq).trans (le_of_eq (mul_comm _ _))) hq, ih]

theorem polySlash_one_num (g h : Matrix (Fin 2) (Fin 2) ℤ) : slP 1 h (lA g) = lA (g * h) := by
  have c0 : (lA g).coeff 0 = ((g 0 1 : ℤ) : ℂ) := by rw [lA, coeff_add, coeff_C_mul_X, coeff_C]; simp
  have c1 : (lA g).coeff 1 = ((g 0 0 : ℤ) : ℂ) := by rw [lA, coeff_add, coeff_C_mul_X, coeff_C]; simp
  rw [polySlash_apply, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, c0, c1]
  simp only [lA, lB, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  simp only [C_add, C_mul]
  ring

theorem polySlash_one_denom (g h : Matrix (Fin 2) (Fin 2) ℤ) : slP 1 h (lB g) = lB (g * h) := by
  have c0 : (lB g).coeff 0 = ((g 1 1 : ℤ) : ℂ) := by rw [lB, coeff_add, coeff_C_mul_X, coeff_C]; simp
  have c1 : (lB g).coeff 1 = ((g 1 0 : ℤ) : ℂ) := by rw [lB, coeff_add, coeff_C_mul_X, coeff_C]; simp
  rw [polySlash_apply, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, c0, c1]
  simp only [lA, lB, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  simp only [C_add, C_mul]
  ring

theorem polySlash_comp (w : ℕ) (g h : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) (hp : p.natDegree ≤ w) :
    slP w h (slP w g p) = slP w (g * h) p := by
  conv_lhs => rw [as_sum_range' p (w + 1) (by omega)]
  conv_rhs => rw [as_sum_range' p (w + 1) (by omega)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range] at hk
  rw [polySlash_monomial _ _ _ _ (by omega), polySlash_monomial _ _ _ _ (by omega), C_mul', map_smul, C_mul']
  congr 1
  obtain ⟨j, rfl⟩ : ∃ j, w = k + j := ⟨w - k, by omega⟩
  rw [Nat.add_sub_cancel_left,
    polySlash_mul h k j _ _ ((natDegree_pow_le_of_le k (natDegree_lA g)).trans (by omega))
      ((natDegree_pow_le_of_le j (natDegree_lB g)).trans (by omega))]
  have hA := polySlash_pow h 1 (lA g) (natDegree_lA g) k
  have hB := polySlash_pow h 1 (lB g) (natDegree_lB g) j
  rw [one_mul] at hA hB
  rw [hA, hB, polySlash_one_num, polySlash_one_denom]

theorem polySlash_map (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (q : ℂ[X]) :
    (slP w g q).map (starRingEnd ℂ) = slP w g (q.map (starRingEnd ℂ)) := by
  rw [polySlash_apply, polySlash_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, lA, lB, coeff_map]

end GlobalTheory.HeckeFamilyMatrices.HkC

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.HkC

variable {Γ : Subgroup SL(2, ℤ)} {α : Matrix (Fin 2) (Fin 2) ℤ} {ι : Type} {δ : ι → Matrix (Fin 2) (Fin 2) ℤ}

theorem matm (a b : Γ) : mat ↑(a * b) = mat ↑a * mat ↑b := rfl

theorem det_mat (γ : SL(2, ℤ)) : (mat γ).det = 1 := γ.2

theorem det_rep (hD : IsDCReps Γ α δ) (i : ι) : (δ i).det = α.det := by
  obtain ⟨γ1, γ2, h⟩ := hD.1 i
  rw [h, Matrix.det_mul, Matrix.det_mul, det_mat, det_mat]; ring

theorem cancel_right {M N D : Matrix (Fin 2) (Fin 2) ℤ} (hD : D.det ≠ 0) (h : M * D = N * D) : M = N := by
  have h2 : M * (D * D.adjugate) = N * (D * D.adjugate) := by rw [← mul_assoc, h, mul_assoc]
  rw [Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_smul, mul_one, mul_one] at h2
  exact smul_right_injective _ hD h2

theorem rep_uniq (hD : IsDCReps Γ α δ) (hα : α.det ≠ 0) {a b : Γ} {j k : ι}
    (h : mat a * δ j = mat b * δ k) : j = k ∧ a = b := by
  obtain ⟨γ1, γ2, hj⟩ := hD.1 j
  obtain ⟨i, _, hi⟩ := hD.2 (a * γ1) γ2
  have e1 : mat ↑(a * γ1) * α * mat γ2 = mat a * δ j := by rw [hj, matm]; simp only [mul_assoc]
  have hjk : j = k := (hi j ⟨a, e1⟩).trans (hi k ⟨b, e1.trans h⟩).symm
  subst hjk
  refine ⟨rfl, ?_⟩
  have := cancel_right (by rw [det_rep hD]; exact hα) h
  exact Subtype.ext (Subtype.ext this)

theorem rep_exists [Fintype ι] (hD : IsDCReps Γ α δ) (hα : α.det ≠ 0) (γ : Γ) :
    ∃ π : Equiv.Perm ι, ∃ g : ι → Γ, ∀ i, δ i * mat γ = mat (g i) * δ (π i) := by
  have hx : ∀ i, ∃ j, ∃ g : Γ, δ i * mat γ = mat g * δ j := by
    intro i
    obtain ⟨γ1, γ2, hi⟩ := hD.1 i
    obtain ⟨j, ⟨g, hg⟩, _⟩ := hD.2 γ1 (γ2 * γ)
    exact ⟨j, g, by rw [hi, ← hg, matm]; simp only [mul_assoc]⟩
  choose f g hfg using hx
  have hinj : Function.Injective f := by
    intro i k hik
    have h1 := hfg i
    have h2 := hfg k
    rw [hik] at h1
    have hγ : (mat γ).det ≠ 0 := by rw [det_mat]; norm_num
    have e : mat ↑(g k * (g i)⁻¹) * δ i = mat ↑(1 : Γ) * δ k := by
      apply cancel_right hγ
      calc mat ↑(g k * (g i)⁻¹) * δ i * mat γ = mat (g k) * mat ↑(g i)⁻¹ * (δ i * mat γ) := by
              rw [matm]; simp only [mul_assoc]
        _ = mat (g k) * mat ↑(g i)⁻¹ * (mat (g i) * δ (f k)) := by rw [h1]
        _ = mat (g k) * mat ↑((g i)⁻¹ * g i) * δ (f k) := by rw [matm]; simp only [mul_assoc]
        _ = mat (g k) * δ (f k) := by simp
        _ = δ k * mat γ := h2.symm
        _ = mat ↑(1 : Γ) * δ k * mat γ := by simp
    exact (rep_uniq hD hα e).1
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), g, hfg⟩

theorem hk_apply [Fintype ι] (w : ℕ) (hD : IsDCReps Γ α δ) (hα : α.det ≠ 0) (z : Γ → ℂ[X]) (γ : Γ)
    (π : Equiv.Perm ι) (g : ι → Γ) (hg : ∀ i, δ i * mat γ = mat (g i) * δ (π i)) :
    hk Γ w δ z γ = ∑ i, slP w (δ (π i)) (z (g i)) := by
  have hex : ∃ π : Equiv.Perm ι, ∀ i, ∃ γ' : Γ, δ i * mat γ = mat γ' * δ (π i) :=
    ⟨π, fun i => ⟨g i, hg i⟩⟩
  rw [hk, LinearMap.pi_apply, dite_eq_left hex, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.comp_apply, LinearMap.proj_apply]
  have e := ((hex.choose_spec i).choose_spec).symm.trans (hg i)
  obtain ⟨h1, h2⟩ := rep_uniq hD hα e
  rw [h2, h1]

end GlobalTheory.HeckeFamilyMatrices.HkC

namespace GlobalTheory.HeckeFamilyMatrices.HkC

theorem hk_cocycle_coboundary_conj : ∀ (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (ι : Type) [Fintype ι]
    (α : Matrix (Fin 2) (Fin 2) ℤ) (δ : ι → Matrix (Fin 2) (Fin 2) ℤ), 0 < α.det → IsDCReps Γ α δ →
    (∀ z ∈ Z1 Γ w, hk Γ w δ z ∈ Z1 Γ w) ∧ (∀ z ∈ B1 Γ w, hk Γ w δ z ∈ B1 Γ w) ∧
      ∀ z, cj (hk Γ w δ z) = hk Γ w δ (cj z) := by
  intro Γ w ι _ α δ hpos hD
  have hα : α.det ≠ 0 := hpos.ne'
  refine ⟨?_, ?_, ?_⟩
  · rintro z ⟨hz1, hz2⟩
    refine ⟨fun γ => ?_, fun γ γ' => ?_⟩
    · obtain ⟨π, g, hg⟩ := rep_exists hD hα γ
      rw [hk_apply w hD hα z γ π g hg]
      exact Submodule.sum_mem _ fun i _ => mem_degLT_iff.2 (natDegree_slP_le _ _ _)
    · obtain ⟨π1, g1, hg1⟩ := rep_exists hD hα γ
      obtain ⟨π2, g2, hg2⟩ := rep_exists hD hα γ'
      have hg : ∀ i, δ i * mat ↑(γ * γ') = mat ↑(g1 i * g2 (π1 i)) * δ ((π1.trans π2) i) := by
        intro i
        rw [matm, matm, ← mul_assoc, hg1, mul_assoc, hg2, ← mul_assoc]
        rfl
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hk_apply w hD hα z _ _ _ hg, hk_apply w hD hα z γ π1 g1 hg1, hk_apply w hD hα z γ' π2 g2 hg2,
        map_sum]
      simp only [hz2, map_add (f := _), Finset.sum_add_distrib, Equiv.trans_apply]
      have hs := Equiv.sum_comp π1 (fun j => slP w (δ (π2 j)) (z (g2 j)))
      rw [hs, add_left_inj]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [polySlash_comp _ _ _ _ (mem_degLT_iff.1 (hz1 _)), polySlash_comp _ _ _ _ (mem_degLT_iff.1 (hz1 _)),
        ← hg2 (π1 i)]
  · rintro z ⟨⟨p, hp⟩, rfl⟩
    have hp' : p.natDegree ≤ w := mem_degLT_iff.1 hp
    refine ⟨⟨∑ i, slP w (δ i) p, Submodule.sum_mem _ fun i _ => mem_degLT_iff.2 (natDegree_slP_le _ _ _)⟩, ?_⟩
    funext γ
    obtain ⟨π, g, hg⟩ := rep_exists hD hα γ
    rw [hk_apply w hD hα _ γ π g hg]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.pi_apply, LinearMap.sub_apply,
      LinearMap.id_apply, map_sub, Finset.sum_sub_distrib, map_sum]
    have hs := Equiv.sum_comp π (fun j => slP w (δ j) p)
    rw [hs, sub_left_inj]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [polySlash_comp _ _ _ _ hp', polySlash_comp _ _ _ _ hp', hg]
  · intro z
    funext γ
    simp only [cj, hk, LinearMap.pi_apply]
    split_ifs with h
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, Polynomial.map_sum, polySlash_map, cj]
    · simp [cj]

end GlobalTheory.HeckeFamilyMatrices.HkC
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorOnCocycleMapsCocycleCoboundaryConjStatement
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeOperatorOnCocycleMaps_cocycle_coboundary_conj : ∀ (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (ι : Type) [Fintype ι] (α : Matrix (Fin 2) (Fin 2) ℤ) (δ : ι → Matrix (Fin 2) (Fin 2) ℤ), 0 < α.det → IsDCReps Γ α δ → (∀ z ∈ Z1 Γ w, hk Γ w δ z ∈ Z1 Γ w) ∧ (∀ z ∈ B1 Γ w, hk Γ w δ z ∈ B1 Γ w) ∧ ∀ z, cj (hk Γ w δ z) = hk Γ w δ (cj z) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.HkC.hk_cocycle_coboundary_conj | exact GlobalTheory.HeckeFamilyMatrices.HkC.hk_cocycle_coboundary_conj | (intros; apply GlobalTheory.HeckeFamilyMatrices.HkC.hk_cocycle_coboundary_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralOfForallMemDiscreteValuationSubring
open IsLocalRing

namespace GlobalTheory

theorem isIntegral_of_forall_mem_discreteValuationSubring : ∀ (S K : Type) [CommRing S] [IsDomain S] [IsNoetherianRing S] [Field K] [Algebra S K] [IsFractionRing S K] (t : K), (∀ V : ValuationSubring K, IsDiscreteValuationRing V → (∀ s : S, algebraMap S K s ∈ V) → t ∈ V) → IsIntegral S t := by
  intro S K _ _ _ _ _ _ t ht
  by_contra hn
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hn isIntegral_zero
  have : Algebra.EssFiniteType S K := .of_isLocalization K (nonZeroDivisors S)
  have hic : IsIntegrallyClosedIn (integralClosure S K).toSubring K :=
    inferInstanceAs (IsIntegrallyClosedIn (integralClosure S K) K)
  obtain ⟨W, hW, htW⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    (R := (integralClosure S K).toSubring) (x := t) hn
  have hinv : t⁻¹ ∈ W.nonunits := W.inv_mem_nonunits_iff.mpr (Or.inr htW)
  obtain ⟨V, h1, h2, -, h3⟩ := exists_discreteValuationSubring_of_valuationSubring (R := S) W
    (fun r => hW ((integralClosure S K).algebraMap_mem r))
    Set.finite_empty (Set.finite_singleton t⁻¹) (by simp) (by simpa using hinv)
    ⟨_, rfl, inv_ne_zero ht0⟩
  exact (V.inv_mem_nonunits_iff.mp (h3 _ rfl)).resolve_left ht0 (ht V h1 h2)

end GlobalTheory
end
