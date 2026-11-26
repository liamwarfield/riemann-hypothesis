module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
public import ReciprocityTheory.NeutralLocalFields.Reciprocity
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.NormEqOfNormSubLt

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem mem_Tm {m : ℕ} (hm : 0 < m) (t : ℕ × ℕ × ℕ) :
    t ∈ Tm m ↔ t.1 * t.2.2 = m ∧ t.2.1 < t.2.2 := by
  rw [Tm, Finset.mem_image]
  constructor
  · rintro ⟨⟨a, b⟩, hx, rfl⟩
    rw [Finset.mem_sigma, Nat.mem_divisors, Finset.mem_range] at hx
    exact ⟨Nat.mul_div_cancel' hx.1.1, hx.2⟩
  · obtain ⟨a, b, e⟩ := t
    rintro ⟨h1, h2⟩
    simp only at h1 h2
    have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; omega)
    have he : m / a = e := by rw [← h1, Nat.mul_div_cancel_left _ ha]
    refine ⟨⟨a, b⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma, Nat.mem_divisors, Finset.mem_range]
      exact ⟨⟨⟨e, h1.symm⟩, hm.ne'⟩, by rw [he]; exact h2⟩
    · simp only [he]

theorem Tm_pos {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) : 0 < t.1 ∧ 0 < t.2.2 := by
  have h := ((mem_Tm hm t).mp ht).1
  have hpos : 0 < t.1 * t.2.2 := h ▸ hm
  refine ⟨Nat.pos_of_ne_zero fun h0 => ?_, Nat.pos_of_ne_zero fun h0 => ?_⟩ <;>
    rw [h0] at hpos <;> simp at hpos

theorem pt_coe {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) (τ : ℍ) :
    ((pt a b e τ : ℍ) : ℂ) = ((a : ℂ) * τ + b) / e := by
  have hz : 0 < (((a : ℂ) * τ + b) / e).im := by
    rw [Complex.div_natCast_im]
    simp only [Complex.add_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero,
      UpperHalfPlane.coe_im]
    exact div_pos (mul_pos (by exact_mod_cast ha) τ.im_pos) (by exact_mod_cast he)
  unfold pt
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]

theorem DD_ne_zero (τ : ℍ) : DD τ ≠ 0 := by
  exact ModularForm.discriminant_ne_zero τ

theorem smul_of_form {k : ℤ} (g : ModularForm 𝒮ℒ k) (γ : SL(2, ℤ)) (τ : ℍ) :
    g (γ • τ) = denom γ τ ^ k * g τ := by
  have h := SlashInvariantForm.slash_action_eqn'' g (γ := Matrix.SpecialLinearGroup.mapGL ℝ γ)
    (MonoidHom.mem_range.mpr ⟨γ, rfl⟩) τ
  exact h

theorem isMF_AA : IsMF 12 AA := by
  refine ⟨ModularForm.mcast (by norm_num) (ModularForm.E₄.mul (ModularForm.E₄.mul ModularForm.E₄)), fun τ => ?_⟩
  show (ModularForm.E₄.mul (ModularForm.E₄.mul ModularForm.E₄)) τ = AA τ
  rw [ModularForm.coe_mul, Pi.mul_apply, ModularForm.coe_mul, Pi.mul_apply]
  unfold AA
  ring

theorem isMF_DD : IsMF 12 DD := by
  first
    | exact ⟨ModularFormClass.modularForm CuspForm.discriminant, fun τ => rfl⟩
    | exact ⟨ModularFormClass.modularForm CuspForm.discriminant, fun τ => rfl⟩

theorem IsMF.smul_eq {k : ℤ} {f : ℍ → ℂ} (h : IsMF k f) (γ : SL(2, ℤ)) (τ : ℍ) :
    f (γ • τ) = denom γ τ ^ k * f τ := by
  obtain ⟨g, hg⟩ := h
  rw [← hg, ← hg]
  exact smul_of_form g γ τ

theorem AA_smul (γ : SL(2, ℤ)) (τ : ℍ) : AA (γ • τ) = denom γ τ ^ 12 * AA τ := by
  exact isMF_AA.smul_eq γ τ

theorem DD_smul (γ : SL(2, ℤ)) (τ : ℍ) : DD (γ • τ) = denom γ τ ^ 12 * DD τ := by
  exact isMF_DD.smul_eq γ τ

theorem jT_smul (γ : SL(2, ℤ)) (τ : ℍ) : jT (γ • τ) = jT τ := by
  unfold jT
  rw [AA_smul, DD_smul, mul_div_mul_left _ _ (pow_ne_zero _ (UpperHalfPlane.denom_ne_zero _ τ))]

theorem IsMF.congr_weight {k k' : ℤ} {f : ℍ → ℂ} (h : IsMF k f) (hk : k = k') : IsMF k' f := by
  subst hk
  exact h

theorem IsMF.add {k : ℤ} {f g : ℍ → ℂ} (hf : IsMF k f) (hg : IsMF k g) : IsMF k (fun τ => f τ + g τ) := by
  obtain ⟨f', hf'⟩ := hf
  obtain ⟨g', hg'⟩ := hg
  exact ⟨f' + g', fun τ => by simp [hf', hg']⟩

theorem IsMF.sub {k : ℤ} {f g : ℍ → ℂ} (hf : IsMF k f) (hg : IsMF k g) : IsMF k (fun τ => f τ - g τ) := by
  obtain ⟨f', hf'⟩ := hf
  obtain ⟨g', hg'⟩ := hg
  exact ⟨f' - g', fun τ => by simp [hf', hg']⟩

theorem IsMF.const_mul {k : ℤ} {f : ℍ → ℂ} (c : ℂ) (hf : IsMF k f) : IsMF k (fun τ => c * f τ) := by
  obtain ⟨f', hf'⟩ := hf
  exact ⟨c • f', fun τ => by simp [hf']⟩

theorem IsMF.mul {k k' : ℤ} {f g : ℍ → ℂ} (hf : IsMF k f) (hg : IsMF k' g) :
    IsMF (k + k') (fun τ => f τ * g τ) := by
  obtain ⟨f', hf'⟩ := hf
  obtain ⟨g', hg'⟩ := hg
  exact ⟨f'.mul g', fun τ => by rw [ModularForm.coe_mul, Pi.mul_apply, hf', hg']⟩

theorem IsMF.pow {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) (n : ℕ) : IsMF (n * k) (fun τ => f τ ^ n) := by
  induction n with
  | zero =>
    refine IsMF.congr_weight (k := 0) ⟨1, fun τ => ?_⟩ (by simp)
    simp
  | succ n ih =>
    have h := (ih.mul hf).congr_weight (show (n : ℤ) * k + k = ((n + 1 : ℕ) : ℤ) * k by push_cast; ring)
    simpa [pow_succ] using h

theorem zetaC_pow_self {m : ℕ} (hm : 0 < m) : zetaC m ^ m = 1 := by
  unfold zetaC
  rw [← Complex.exp_nat_mul]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have : (m : ℂ) * (2 * Real.pi * Complex.I / m) = 2 * Real.pi * Complex.I := by field_simp
  rw [this, Complex.exp_two_pi_mul_I]

theorem zetaC_mem (m : ℕ) : zetaC m ∈ Rm m := by
  exact Subring.subset_closure (Set.mem_singleton _)

theorem Rm_isIntegral {m : ℕ} (hm : 0 < m) {x : ℂ} (hx : x ∈ Rm m) : IsIntegral ℤ x := by
  have hζ : IsIntegral ℤ (zetaC m) :=
    IsIntegral.of_pow hm (by rw [zetaC_pow_self hm]; exact isIntegral_one)
  have hle : Rm m ≤ (integralClosure ℤ ℂ).toSubring :=
    Subring.closure_le.mpr (Set.singleton_subset_iff.mpr hζ)
  exact hle hx

end ReciprocityTheory.ChartRestriction.L1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs
noncomputable section
open scoped BigOperators Classical
open NumberField IsDedekindDomain Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

def sqD (d : ℕ) : ℂ := Complex.I * ((Real.sqrt d : ℝ) : ℂ)

theorem sqD_sq (d : ℕ) : sqD d ^ 2 = -(d : ℂ) := by
  unfold sqD
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  push_cast
  ring

def KQ (d : ℕ) : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {sqD d}

theorem sqD_isIntegral (d : ℕ) : IsIntegral ℚ (sqD d) := by
  refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℚ), Polynomial.monic_X_pow_add_C _ two_ne_zero, ?_⟩
  simp [sqD_sq]

scoped instance KQ_numberField (d : ℕ) : NumberField (KQ d) where
  to_charZero := inferInstance
  to_finiteDimensional := IntermediateField.adjoin.finiteDimensional (sqD_isIntegral d)

def sqK (d : ℕ) : KQ d := ⟨sqD d, IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)⟩

abbrev Om (d : ℕ) : IntermediateField (KQ d) ℂ := algebraicClosure (KQ d) ℂ

def Aio (d l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) : ValuationSubring (Om d) :=
  ((NormedField.valuation (K := ℂ_[l])).valuationSubring).comap
    ((ι : ℂ →+* ℂ_[l]).comp (algebraMap (Om d) ℂ))

def InertiaEl {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω) : Prop :=
  g ∈ A.decompositionSubgroup E ∧ ∀ x ∈ A, g x - x ∈ A.nonunits

end ReciprocityTheory.ChartRestriction.L1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModLatTau
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem latTau_snd_ne (L : PeriodPair) : L.ω₂ ≠ 0 := by
  simpa using L.indep.ne_zero 1

theorem latTau_im_ne (L : PeriodPair) : (L.ω₁ / L.ω₂).im ≠ 0 := by
  intro h
  have h2 := latTau_snd_ne L
  obtain ⟨r, hr⟩ : ∃ r : ℝ, L.ω₁ / L.ω₂ = (r : ℂ) :=
    ⟨(L.ω₁ / L.ω₂).re, Complex.ext (by simp) (by simp [h])⟩
  have h1 : L.ω₁ = (r : ℂ) * L.ω₂ := by rw [← hr, div_mul_cancel₀ _ h2]
  have h3 := (LinearIndependent.pair_iff.mp L.indep) 1 (-r)
    (by rw [Complex.real_smul, Complex.real_smul, h1]; push_cast; ring)
  norm_num at h3

theorem latTau (L : PeriodPair) : ∃ (c : ℂ) (τ : ℍ), IsTauOf L c τ := by
  have h2 := latTau_snd_ne L
  rcases lt_or_gt_of_ne (latTau_im_ne L) with hneg | hpos
  · refine ⟨L.ω₂, ⟨-(L.ω₁ / L.ω₂), by rw [Complex.neg_im]; linarith⟩, h2, fun x => ?_⟩
    rw [PeriodPair.mem_lattice]
    try simp only [UpperHalfPlane.coe_mk]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨-m, n, by push_cast; field_simp; try ring⟩
    · rintro ⟨u, v, rfl⟩
      exact ⟨-u, v, by push_cast; field_simp; try ring⟩
  · refine ⟨L.ω₂, ⟨L.ω₁ / L.ω₂, hpos⟩, h2, fun x => ?_⟩
    rw [PeriodPair.mem_lattice]
    try simp only [UpperHalfPlane.coe_mk]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨m, n, by field_simp; try ring⟩
    · rintro ⟨u, v, rfl⟩
      exact ⟨u, v, by field_simp; try ring⟩

end ReciprocityTheory.ChartRestriction.L1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.NormNatCastClOfNotDvd
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Polynomial

variable (l : ℕ) [Fact l.Prime]

theorem norm_natCast_Cl (n : ℕ) : ‖(n : ℂ_[l])‖ = ‖(n : ℚ_[l])‖ := by
  rw [← PadicComplex.norm_extends' l (n : ℚ_[l])]
  congr 1
  simp

theorem norm_sub_le_max_Cl (a b : ℂ_[l]) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ :=
  by simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max a (-b)

theorem norm_l_Cl : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [norm_natCast_Cl, Padic.norm_p]

theorem norm_natCast_Cl_of_not_dvd {n : ℕ} (hn : ¬ l ∣ n) : ‖(n : ℂ_[l])‖ = 1 := by
  rw [norm_natCast_Cl, Padic.norm_natCast_eq_one_iff]
  exact ((Fact.out : l.Prime).coprime_iff_not_dvd).2 hn

theorem muP_norm {ζ : ℂ_[l]} (hζ : ζ ∈ muP l) : ‖ζ‖ = 1 := by
  obtain ⟨n, hn, -, h⟩ := hζ
  have : ‖ζ‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this

theorem tch_norm_le {ξ : ℂ_[l]} (hξ : ξ ∈ Tch l) : ‖ξ‖ ≤ 1 := by
  rcases hξ with rfl | h
  · simp
  · exact (muP_norm l h).le

theorem tch_mul {ξ ξ' : ℂ_[l]} (h : ξ ∈ Tch l) (h' : ξ' ∈ Tch l) : ξ * ξ' ∈ Tch l := by
  rcases h with rfl | ⟨n, hn, hln, hζ⟩
  · rw [zero_mul]; exact Set.mem_insert _ _
  rcases h' with rfl | ⟨m, hm, hlm, hζ'⟩
  · rw [mul_zero]; exact Set.mem_insert _ _
  refine Set.mem_insert_of_mem _ ⟨n * m, Nat.mul_pos hn hm, ?_, ?_⟩
  · intro hd
    rcases ((Fact.out : l.Prime).dvd_mul).1 hd with h1 | h1
    · exact hln h1
    · exact hlm h1
  · rw [mul_pow, pow_mul, hζ, one_pow, one_mul, mul_comm n m, pow_mul, hζ', one_pow]

theorem tch_inv {ξ : ℂ_[l]} (h : ξ ∈ Tch l) : ξ⁻¹ ∈ Tch l := by
  rcases h with rfl | ⟨n, hn, hln, hζ⟩
  · rw [inv_zero]; exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ ⟨n, hn, hln, by rw [inv_pow, hζ, inv_one]⟩

theorem tch_near (x : ℂ_[l]) (hx : ‖x‖ ≤ 1) (f : ℕ) (hf : 0 < f) (r : ℝ) (hr : r < 1)
    (h : ‖x ^ (l ^ f) - x‖ ≤ r) : ∃ ξ ∈ Tch l, ‖x - ξ‖ ≤ r := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hq : 2 ≤ l ^ f := le_trans hl (Nat.le_self_pow hf.ne' l)
  obtain ⟨m, hm⟩ : ∃ m, l ^ f = m + 1 := ⟨l ^ f - 1, by omega⟩
  have hm0 : 0 < m := by omega
  have hlm : ¬ l ∣ m := by
    intro hd
    have h1 : l ∣ m + 1 := hm ▸ dvd_pow_self l hf.ne'
    have h2 : l ∣ 1 := (Nat.dvd_add_right hd).1 h1
    exact (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h2)
  by_cases hsmall : ‖x‖ ≤ r
  · exact ⟨0, Set.mem_insert _ _, by simpa using hsmall⟩
  push Not at hsmall
  have hr0 : 0 ≤ r := le_trans (norm_nonneg _) h
  have hx1 : ‖x‖ = 1 := by
    have h1 : ‖x‖ ≤ max ‖x ^ (l ^ f)‖ ‖x ^ (l ^ f) - x‖ := by
      calc ‖x‖ = ‖x ^ (l ^ f) - (x ^ (l ^ f) - x)‖ := by rw [sub_sub_cancel]
        _ ≤ _ := norm_sub_le_max_Cl l _ _
    have h2 : ‖x‖ ≤ ‖x‖ ^ (l ^ f) := by
      rw [← norm_pow]
      rcases le_max_iff.1 h1 with h3 | h3
      · exact h3
      · linarith
    by_contra hne
    have hlt : ‖x‖ < 1 := lt_of_le_of_ne hx hne
    have hpos : 0 < ‖x‖ := lt_of_le_of_lt hr0 hsmall
    have := pow_lt_self_of_lt_one₀ hpos hlt (by omega : 1 < l ^ f)
    linarith
  have hxm : ‖x ^ m - 1‖ ≤ r := by
    have e : x ^ (l ^ f) - x = x * (x ^ m - 1) := by rw [hm]; ring
    rwa [e, norm_mul, hx1, one_mul] at h
  obtain ⟨ζ, hζroot, hζ⟩ := ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.exists_root_near l (X ^ m - C 1)
    (monic_X_pow_sub_C 1 hm0.ne') x
    (by simp only [eval_sub, eval_pow, eval_X, eval_C]; exact lt_of_le_of_lt hxm hr)
  have hζm : ζ ^ m = 1 := by
    have : ζ ^ m - 1 = 0 := by simpa using hζroot
    exact sub_eq_zero.1 this
  have hmu : ζ ∈ muP l := ⟨m, hm0, hlm, hζm⟩
  refine ⟨ζ, Set.mem_insert_of_mem _ hmu, ?_⟩
  have hζ1 : ‖ζ‖ = 1 := muP_norm l hmu
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ1
  have e1 : x - ζ = ζ * (x * ζ⁻¹ - 1) := by
    rw [mul_sub, mul_one, mul_comm x ζ⁻¹, ← mul_assoc, mul_inv_cancel₀ hζ0, one_mul]
  have e2 : x ^ m - 1 = (∑ i ∈ Finset.range m, (x * ζ⁻¹) ^ i) * (x * ζ⁻¹ - 1) := by
    rw [geom_sum_mul, mul_pow, inv_pow, hζm, inv_one, mul_one]
  have hy : ‖x * ζ⁻¹ - 1‖ = ‖x - ζ‖ := by rw [e1, norm_mul, hζ1, one_mul]
  rw [e2, norm_mul, ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.norm_geom_sum_eq_one l (hy ▸ hζ)
    (norm_natCast_Cl_of_not_dvd l hlm), one_mul, hy] at hxm
  exact hxm

end ReciprocityTheory.ChartRestriction.L1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEisInt
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

private theorem hasSum_sigma_mul_qParam_pow_modularForm_E {k : ℕ} (hk : 3 ≤ k) (hke : Even k) (C : ℂ)
    (hC : (riemannZeta k)⁻¹ * (-2 * (Real.pi : ℂ) * Complex.I) ^ k / ((k - 1).factorial : ℂ) = C)
    (τ : ℍ) :
    HasSum (fun m : ℕ => (if m = 0 then (1 : ℂ) else C * (ArithmeticFunction.sigma (k - 1) m : ℂ)) *
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) (ModularForm.E hk τ) := by
  set q := Function.Periodic.qParam 1 (τ : ℂ) with hqdef
  have hqe : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ) = q := by
    simp [hqdef, Function.Periodic.qParam]
  have hq : ‖q‖ < 1 := by
    rw [hqdef, Function.Periodic.norm_qParam]
    refine (Real.exp_lt_exp.mpr ?_).trans_eq Real.exp_zero
    have := τ.im_pos
    have := Real.pi_pos
    simp only [UpperHalfPlane.coe_im, div_one]
    nlinarith
  have hσ : ∀ n : ℕ, ‖((ArithmeticFunction.sigma (k - 1) n : ℕ) : ℂ) * q ^ n‖ ≤ (n : ℝ) ^ k * ‖q‖ ^ n := by
    intro n
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    gcongr
    rw [ArithmeticFunction.sigma_apply]
    push_cast
    calc ∑ d ∈ n.divisors, (d : ℝ) ^ (k - 1) ≤ ∑ d ∈ n.divisors, (n : ℝ) ^ (k - 1) :=
          Finset.sum_le_sum fun d hd => pow_le_pow_left₀ (by positivity)
            (by exact_mod_cast Nat.divisor_le hd) _
      _ = (n.divisors.card : ℝ) * (n : ℝ) ^ (k - 1) := by simp
      _ ≤ (n : ℝ) * (n : ℝ) ^ (k - 1) := by
          gcongr
          exact_mod_cast Nat.card_divisors_le_self n
      _ = (n : ℝ) ^ k := by
          rw [← pow_succ']
          congr 1
          omega
  have hsum : Summable fun n : ℕ => ((ArithmeticFunction.sigma (k - 1) n : ℕ) : ℂ) * q ^ n :=
    Summable.of_norm_bounded (summable_pow_mul_geometric_of_norm_lt_one k (by simpa using hq)) hσ
  have hsum1 : Summable fun n : ℕ =>
      ((ArithmeticFunction.sigma (k - 1) (n + 1) : ℕ) : ℂ) * q ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr hsum
  have hE := EisensteinSeries.q_expansion_riemannZeta hk hke τ
  rw [hE, hC, hqe]
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, if_true, mul_one,
    add_sub_cancel_left, Nat.add_eq_zero, one_ne_zero, and_false, if_false]
  have ht : ∑' n : ℕ+, ((ArithmeticFunction.sigma (k - 1) n : ℕ) : ℂ) * q ^ (n : ℕ) =
      ∑' n : ℕ, ((ArithmeticFunction.sigma (k - 1) (n + 1) : ℕ) : ℂ) * q ^ (n + 1) :=
    tsum_pnat_eq_tsum_succ (f := fun n => ((ArithmeticFunction.sigma (k - 1) n : ℕ) : ℂ) * q ^ n)
  convert hsum1.hasSum.mul_left C using 1 <;>
    first
    | rfl
    | (funext n <;> ring)
    | (congr 1 <;> (rw [← ht]; apply tsum_congr; intro n; simp))

theorem map_eisensteinFourInt : e4Z.map (Int.castRingHom ℂ) = qExpansion 1 E₄ := by
  have hE : E₄ = ModularForm.E (k := 4) (by norm_num) := rfl
  ext m
  refine ModularFormClass.qExpansion_coeff_unique (f := E₄) (h := 1)
    (c := fun m => PowerSeries.coeff m (e4Z.map (Int.castRingHom ℂ))) one_pos (by simp) ?_ m
  intro τ
  have hC : (riemannZeta ((4 : ℕ) : ℂ))⁻¹ * (-2 * (Real.pi : ℂ) * Complex.I) ^ 4 /
      (((4 - 1).factorial : ℕ) : ℂ) = 240 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [show ((4 : ℕ) : ℂ) = 4 by norm_num, riemannZeta_four]
    have hI : Complex.I ^ 4 = 1 := Complex.I_pow_four
    simp only [Nat.factorial, Nat.succ_eq_add_one]
    field_simp
    ring_nf
    rw [hI]
    ring
  have h := hasSum_sigma_mul_qParam_pow_modularForm_E (k := 4) (by norm_num) (by decide) 240 hC τ
  rw [hE]
  convert h using 2 with n
  simp only [e4Z, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  split_ifs <;> simp

theorem map_eisensteinSixInt : e6Z.map (Int.castRingHom ℂ) = qExpansion 1 E₆ := by
  have hE : E₆ = ModularForm.E (k := 6) (by norm_num) := rfl
  ext m
  refine ModularFormClass.qExpansion_coeff_unique (f := E₆) (h := 1)
    (c := fun m => PowerSeries.coeff m (e6Z.map (Int.castRingHom ℂ))) one_pos (by simp) ?_ m
  intro τ
  have hb6 : bernoulli 6 = 1 / 42 := by
    have h5 : bernoulli' 5 = 0 := by
      rw [bernoulli'_def]
      norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
        bernoulli'_three, bernoulli'_four, Nat.choose]
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_def]
    norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
      bernoulli'_three, bernoulli'_four, h5, Nat.choose]
  have hz6 : riemannZeta ((6 : ℕ) : ℂ) = (Real.pi : ℂ) ^ 6 / 945 := by
    have h6 := riemannZeta_two_mul_nat (k := 3) (by norm_num)
    rw [show ((6 : ℕ) : ℂ) = 2 * ((3 : ℕ) : ℂ) by norm_num, h6, hb6]
    norm_num [Nat.factorial]
    ring
  have hC : (riemannZeta ((6 : ℕ) : ℂ))⁻¹ * (-2 * (Real.pi : ℂ) * Complex.I) ^ 6 /
      (((6 - 1).factorial : ℕ) : ℂ) = -504 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [hz6]
    have hI : Complex.I ^ 6 = -1 := by
      rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, Complex.I_sq]
      norm_num
    simp only [Nat.factorial, Nat.succ_eq_add_one]
    field_simp
    ring_nf
    rw [hI]
    ring
  have h := hasSum_sigma_mul_qParam_pow_modularForm_E (k := 6) (by norm_num) (by decide) (-504) hC τ
  rw [hE]
  convert h using 2 with n
  simp only [e6Z, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  split_ifs <;> simp

theorem aC_eq : aC = qExpansion 1 AA := by
  have h1 : AnalyticAt ℂ (cuspFunction 1 ⇑E₄) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero E₄ one_pos (by simp)
  have h2 : AnalyticAt ℂ (cuspFunction 1 (⇑E₄ * ⇑E₄)) 0 := by
    have h3 := ModularFormClass.analyticAt_cuspFunction_zero (E₄.mul E₄) one_pos (by simp)
    rwa [ModularForm.coe_mul] at h3
  have hA : AA = ⇑E₄ * (⇑E₄ * ⇑E₄) := by
    funext τ
    simp only [AA, Pi.mul_apply]
    ring
  rw [hA, qExpansion_mul h1 h2, qExpansion_mul h1 h1, ← map_eisensteinFourInt]
  simp only [aC, aZ, map_pow]
  ring

end ReciprocityTheory.ChartRestriction.L1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGEis
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

def latMap {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) (v : Fin 2 → ℤ) : L.lattice :=
  ⟨c * ((v 0 : ℂ) * (τ : ℂ) + (v 1 : ℂ)), (h.2 _).2 ⟨v 0, v 1, rfl⟩⟩

theorem latMap_bijective {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) :
    Function.Bijective (latMap h) := by
  constructor
  · intro v w hvw
    have h1 : c * ((v 0 : ℂ) * (τ : ℂ) + (v 1 : ℂ)) = c * ((w 0 : ℂ) * (τ : ℂ) + (w 1 : ℂ)) :=
      congrArg Subtype.val hvw
    have h2 := mul_left_cancel₀ h.1 h1
    have him := congrArg Complex.im h2
    have hre := congrArg Complex.re h2
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
      add_zero, Complex.add_re, Complex.mul_re, sub_zero] at him hre
    have hτ : (τ : ℂ).im ≠ 0 := τ.im_ne_zero
    have h0 : (v 0 : ℝ) = w 0 := mul_right_cancel₀ hτ him
    rw [h0] at hre
    have h1' : (v 1 : ℝ) = w 1 := add_left_cancel hre
    funext i
    fin_cases i
    · exact_mod_cast h0
    · exact_mod_cast h1'
  · rintro ⟨x, hx⟩
    obtain ⟨u, v, rfl⟩ := (h.2 x).1 hx
    exact ⟨![u, v], by simp [latMap]⟩

theorem G_eq {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    L.G k = (c ^ k)⁻¹ * (2 * riemannZeta k) * E hk τ := by
  have hE : E hk τ = (1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 k τ := by
    rw [show E hk τ = (1 / 2 : ℂ) • eisensteinSeriesSIF (N := 1) 0 k τ from rfl,
      eisensteinSeriesSIF_apply 0 k τ, smul_eq_mul]
  have H := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk τ
  have h1 : L.G k = ∑' v : Fin 2 → ℤ, (c ^ k)⁻¹ * eisSummand k v τ := by
    rw [PeriodPair.G, ← (Equiv.ofBijective _ (latMap_bijective h)).tsum_eq]
    refine tsum_congr fun v => ?_
    simp [latMap, eisSummand, mul_pow, mul_comm]
  rw [h1, tsum_mul_left, H, hE]
  ring

theorem sixVal : riemannZeta 6 = (Real.pi : ℂ) ^ 6 / 945 := by
  have h5 : bernoulli' 5 = 0 := by
    rw [bernoulli'_def]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one,
      bernoulli'_two, bernoulli'_three, bernoulli'_four]
    norm_num [Nat.choose]
  have h6 : bernoulli' 6 = 1 / 42 := by
    rw [bernoulli'_def]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one,
      bernoulli'_two, bernoulli'_three, bernoulli'_four, h5]
    norm_num [Nat.choose]
  have hB : bernoulli 6 = 1 / 42 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), h6]
  have h := riemannZeta_two_mul_nat (k := 3) (by norm_num)
  norm_num [Nat.factorial, hB] at h
  rw [h]
  ring

theorem g₂_eq {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) :
    L.g₂ = (c ^ 4)⁻¹ * (4 * (Real.pi : ℂ) ^ 4 / 3) * E₄ τ := by
  rw [PeriodPair.g₂, G_eq h (k := 4) (by norm_num) ⟨2, rfl⟩,
    show ((4 : ℕ) : ℂ) = 4 by norm_num, riemannZeta_four]
  have hE : E (k := 4) (by norm_num) τ = E₄ τ := rfl
  rw [hE]
  ring

theorem g₃_eq {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) :
    L.g₃ = (c ^ 6)⁻¹ * (8 * (Real.pi : ℂ) ^ 6 / 27) * E₆ τ := by
  rw [PeriodPair.g₃, G_eq h (k := 6) (by norm_num) ⟨3, rfl⟩,
    show ((6 : ℕ) : ℂ) = 6 by norm_num, sixVal]
  have hE : E (k := 6) (by norm_num) τ = E₆ τ := rfl
  rw [hE]
  ring

end ReciprocityTheory.ChartRestriction.L1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModCMPoint
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem omegaK_sq (d : ℕ) : 4 * omegaK d ^ 2 = 4 * omegaK d - (1 + d) := by
  have hs : (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) ^ 2 = -(d : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    push_cast
    ring
  unfold omegaK
  linear_combination hs

theorem omegaK_lin {d : ℕ} (hd : 0 < d) {t n : ℤ} (h : (t : ℂ) * omegaK d + n = 0) :
    t = 0 ∧ n = 0 := by
  have h2 : (t : ℂ) * (1 + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) + 2 * n = 0 := by
    rw [omegaK] at h
    linear_combination 2 * h
  have hsq : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have h3 : (((t : ℝ) + 2 * n : ℝ) : ℂ) + (((t : ℝ) * Real.sqrt d : ℝ) : ℂ) * Complex.I = 0 := by
    push_cast
    linear_combination h2
  have him : (t : ℝ) * Real.sqrt d = 0 := by
    have := congrArg Complex.im h3
    simpa using this
  have hre : (t : ℝ) + 2 * n = 0 := by
    have := congrArg Complex.re h3
    simpa using this
  have ht : (t : ℝ) = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact h
    · exact absurd h hsq.ne'
  have hn : (n : ℝ) = 0 := by linarith
  exact ⟨by exact_mod_cast ht, by exact_mod_cast hn⟩

theorem cmPoint {d : ℕ} (hd : 0 < d) {L : PeriodPair} (hL : HasCMBy d L) {c : ℂ} {τ : ℍ}
    (h : IsTauOf L c τ) (x y : ℤ) :
    ∃ A B C D : ℤ, ((x : ℂ) + y * omegaK d) * τ = A * τ + B ∧ (x : ℂ) + y * omegaK d = C * τ + D ∧
      4 * (A * D - B * C) = 4 * x ^ 2 + 4 * x * y + y ^ 2 * (1 + d) := by
  obtain ⟨hc, hmem⟩ := h
  have hmul : ∀ w ∈ L.lattice, ((x : ℂ) + y * omegaK d) * w ∈ L.lattice := by
    intro w hw
    have h1 : (x : ℂ) * w ∈ L.lattice := by
      rw [← zsmul_eq_mul]
      exact zsmul_mem hw x
    have h2 : (y : ℂ) * (omegaK d * w) ∈ L.lattice := by
      rw [← zsmul_eq_mul]
      exact zsmul_mem (hL w hw) y
    have e : ((x : ℂ) + y * omegaK d) * w = (x : ℂ) * w + (y : ℂ) * (omegaK d * w) := by ring
    rw [e]
    exact add_mem h1 h2
  have hcτ : c * (τ : ℂ) ∈ L.lattice := (hmem _).2 ⟨1, 0, by push_cast; ring⟩
  have hc1 : c ∈ L.lattice := (hmem _).2 ⟨0, 1, by push_cast; ring⟩
  obtain ⟨A, B, hAB⟩ := (hmem _).1 (hmul _ hcτ)
  obtain ⟨C, D, hCD⟩ := (hmem _).1 (hmul _ hc1)
  have e1 : ((x : ℂ) + y * omegaK d) * τ = A * τ + B := by
    apply mul_left_cancel₀ hc
    linear_combination hAB
  have e2 : (x : ℂ) + y * omegaK d = C * τ + D := by
    apply mul_left_cancel₀ hc
    linear_combination hCD
  refine ⟨A, B, C, D, e1, e2, ?_⟩

  have key : ((x : ℂ) + y * omegaK d - A) * ((x : ℂ) + y * omegaK d - D) = B * C := by
    linear_combination ((x : ℂ) + y * omegaK d - A) * e2 + (C : ℂ) * e1
  have hω := omegaK_sq d
  obtain ⟨ht, hn⟩ := omegaK_lin hd (t := 8 * x * y + 4 * y ^ 2 - 4 * (A + D) * y)
    (n := 4 * x ^ 2 - y ^ 2 * (1 + d) - 4 * (A + D) * x + 4 * (A * D - B * C)) (by
      push_cast
      linear_combination 4 * key - (y : ℂ) ^ 2 * hω)
  by_cases hy : y = 0
  · subst hy
    simp only [Int.cast_zero, zero_mul, add_zero] at e1 e2
    have hτ : 0 < (τ : ℂ).im := τ.im_pos
    have e2' : (x : ℂ) - D = (C : ℂ) * τ := by linear_combination e2
    have e1' : ((x : ℂ) - A) * τ = (B : ℂ) := by linear_combination e1
    have hC : C = 0 := by
      have := congrArg Complex.im e2'
      simp only [Complex.sub_im, Complex.intCast_im, Complex.mul_im, Complex.intCast_re] at this
      have h0 : (C : ℝ) * (τ : ℂ).im = 0 := by linarith
      rcases mul_eq_zero.mp h0 with h0 | h0
      · exact_mod_cast h0
      · exact absurd h0 hτ.ne'
    have hA : A = x := by
      have := congrArg Complex.im e1'
      simp only [Complex.sub_im, Complex.intCast_im, Complex.mul_im, Complex.intCast_re,
        Complex.sub_re] at this
      have h0 : ((x : ℝ) - A) * (τ : ℂ).im = 0 := by linarith
      rcases mul_eq_zero.mp h0 with h0 | h0
      · have : (A : ℝ) = x := by linarith
        exact_mod_cast this
      · exact absurd h0 hτ.ne'
    subst hC hA
    have hD : D = A := by
      have : ((A : ℤ) : ℂ) = D := by linear_combination e2'
      exact_mod_cast this.symm
    subst hD
    ring
  · have h4 : 4 * (y * (2 * x + y - (A + D))) = 0 := by linear_combination ht
    have hs : 2 * x + y - (A + D) = 0 :=
      (mul_eq_zero.mp ((mul_eq_zero.mp h4).resolve_left (by norm_num))).resolve_left hy
    linear_combination hn - 4 * x * hs

end ReciprocityTheory.ChartRestriction.L1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.KurNewton
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

section Ball

variable {K : Type} [NormedField K] [IsUltrametricDist K]

def newtonBall (K : Type) [NormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rwa [norm_neg]

theorem newton_exists_poly (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) :
    ∃ Q : Polynomial (newtonBall K), Q.map (newtonBall K).subtype = P := by
  have hp : (↑P.coeffs : Set K) ⊆ newtonBall K := by
    intro c hc
    obtain ⟨i, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp (Finset.mem_coe.mp hc)
    exact hP i
  exact ⟨P.toSubring (newtonBall K) hp, Polynomial.map_toSubring P (newtonBall K) hp⟩

theorem newton_eval_ball (Q : Polynomial (newtonBall K)) (a : newtonBall K) :
    (Q.map (newtonBall K).subtype).eval (a : K) = ((Q.eval a : newtonBall K) : K) := by
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply (newtonBall K).subtype a

theorem newton_expansion (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) (x y : K)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ∃ k : K, ‖k‖ ≤ 1 ∧ P.eval (x + y) = P.eval x + P.derivative.eval x * y + k * y ^ 2 := by
  obtain ⟨Q, rfl⟩ := newton_exists_poly P hP
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion Q ⟨x, hx⟩ ⟨y, hy⟩
  refine ⟨k, k.2, ?_⟩
  have h := congrArg (fun z : newtonBall K => (z : K)) hk
  have e1 := newton_eval_ball Q (⟨x, hx⟩ + ⟨y, hy⟩)
  have e2 := newton_eval_ball Q ⟨x, hx⟩
  have e3 := newton_eval_ball (Polynomial.derivative Q) ⟨x, hx⟩
  rw [Polynomial.derivative_map]
  simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_pow] at h e1 e2 e3
  rw [e1, e2, e3, h]

theorem newton_lipschitz (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) (x y : K)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖P.eval x - P.eval y‖ ≤ ‖x - y‖ := by
  obtain ⟨Q, rfl⟩ := newton_exists_poly P hP
  obtain ⟨k, hk⟩ := Polynomial.evalSubFactor Q ⟨x, hx⟩ ⟨y, hy⟩
  have h := congrArg (fun z : newtonBall K => (z : K)) hk
  have e1 := newton_eval_ball Q ⟨x, hx⟩
  have e2 := newton_eval_ball Q ⟨y, hy⟩
  simp only [AddSubgroupClass.coe_sub, Subring.coe_mul] at h e1 e2
  rw [e1, e2, h, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) k.2

theorem newton_derivative_coeff (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) (i : ℕ) :
    ‖P.derivative.coeff i‖ ≤ 1 := by
  obtain ⟨Q, rfl⟩ := newton_exists_poly P hP
  rw [Polynomial.derivative_map, Polynomial.coeff_map]
  exact ((Polynomial.derivative Q).coeff i).2

theorem newton_step (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) (x : K) (hx : ‖x‖ ≤ 1)
    (h0 : ‖P.eval x‖ < 1) (h1 : ‖P.derivative.eval x‖ = 1) :
    ∃ y : K, ‖y‖ ≤ 1 ∧ ‖P.derivative.eval y‖ = 1 ∧ ‖P.eval y‖ ≤ ‖P.eval x‖ ^ 2 ∧
      ‖y - x‖ ≤ ‖P.eval x‖ := by
  have hd : P.derivative.eval x ≠ 0 := by
    intro h
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  set t : K := -(P.eval x / P.derivative.eval x) with ht
  have hnt : ‖t‖ = ‖P.eval x‖ := by rw [ht, norm_neg, norm_div, h1, div_one]
  have ht1 : ‖t‖ ≤ 1 := hnt ▸ h0.le
  have hy : ‖x + t‖ ≤ 1 := (IsUltrametricDist.norm_add_le_max x t).trans (max_le hx ht1)
  obtain ⟨k, hk, he⟩ := newton_expansion P hP x t hx ht1
  refine ⟨x + t, hy, ?_, ?_, ?_⟩
  · have hl := newton_lipschitz P.derivative (newton_derivative_coeff P hP) (x + t) x hy hx
    rw [add_sub_cancel_left, hnt] at hl
    have hlt : ‖P.derivative.eval (x + t) - P.derivative.eval x‖ < ‖P.derivative.eval x‖ := by
      rw [h1]; exact lt_of_le_of_lt hl h0
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne
    rw [sub_add_cancel, max_eq_right hlt.le, h1] at this
    exact this
  · have hz : P.eval x + P.derivative.eval x * t = 0 := by
      rw [ht]; field_simp; ring
    rw [he, hz, zero_add, norm_mul, norm_pow, hnt]
    exact mul_le_of_le_one_left (by positivity) hk
  · rw [add_sub_cancel_left, hnt]

end Ball

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem newton_root (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) (x₀ : K) (hx : ‖x₀‖ ≤ 1)
    (h0 : ‖P.eval x₀‖ < 1) (h1 : ‖P.derivative.eval x₀‖ = 1) :
    ∃ x : K, P.eval x = 0 ∧ ‖x - x₀‖ ≤ ‖P.eval x₀‖ := by
  set c : ℝ := ‖P.eval x₀‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg _
  let S : Type := {x : K // ‖x‖ ≤ 1 ∧ ‖P.eval x‖ < 1 ∧ ‖P.derivative.eval x‖ = 1}
  have step : ∀ s : S, ∃ s' : S, ‖P.eval s'.1‖ ≤ ‖P.eval s.1‖ ^ 2 ∧
      ‖s'.1 - s.1‖ ≤ ‖P.eval s.1‖ := by
    intro s
    obtain ⟨y, hy, hy1, hy2, hy3⟩ := newton_step P hP s.1 s.2.1 s.2.2.1 s.2.2.2
    have : ‖P.eval y‖ < 1 :=
      lt_of_le_of_lt hy2 (pow_lt_one₀ (norm_nonneg _) s.2.2.1 two_ne_zero)
    exact ⟨⟨y, hy, this, hy1⟩, hy2, hy3⟩
  choose g hg1 hg2 using step
  let u : ℕ → S := fun n => Nat.rec ⟨x₀, hx, h0, h1⟩ (fun _ s => g s) n
  have hu0 : (u 0).1 = x₀ := rfl
  have hus : ∀ n, u (n + 1) = g (u n) := fun _ => rfl
  have hval : ∀ n, ‖P.eval (u n).1‖ ≤ c * c ^ n := by
    intro n
    induction n with
    | zero => rw [hu0, pow_zero, mul_one]
    | succ n ih =>
      have hle : ‖P.eval (u n).1‖ ≤ c :=
        ih.trans (mul_le_of_le_one_right hc0 (pow_le_one₀ hc0 h0.le))
      calc ‖P.eval (u (n + 1)).1‖ ≤ ‖P.eval (u n).1‖ ^ 2 := by rw [hus]; exact hg1 _
        _ = ‖P.eval (u n).1‖ * ‖P.eval (u n).1‖ := sq _
        _ ≤ (c * c ^ n) * c := mul_le_mul ih hle (norm_nonneg _) (by positivity)
        _ = c * c ^ (n + 1) := by ring
  have hdist : ∀ n, dist (u n).1 (u (n + 1)).1 ≤ c * c ^ n := by
    intro n
    rw [dist_comm, dist_eq_norm, hus]
    exact (hg2 _).trans (hval n)
  have hcau : CauchySeq (fun n => (u n).1) := cauchySeq_of_le_geometric c c h0 hdist
  obtain ⟨x, hxl⟩ := cauchySeq_tendsto_of_complete hcau
  have hnear : ∀ n, ‖(u n).1 - x₀‖ ≤ c := by
    intro n
    induction n with
    | zero => rw [hu0, sub_self, norm_zero]; exact hc0
    | succ n ih =>
      have h2 : ‖(u (n + 1)).1 - (u n).1‖ ≤ c := by
        rw [← dist_eq_norm, dist_comm]
        exact (hdist n).trans (mul_le_of_le_one_right hc0 (pow_le_one₀ hc0 h0.le))
      have := IsUltrametricDist.norm_add_le_max ((u (n + 1)).1 - (u n).1) ((u n).1 - x₀)
      rw [sub_add_sub_cancel] at this
      exact this.trans (max_le h2 ih)
  refine ⟨x, ?_, ?_⟩
  · have hl1 : Filter.Tendsto (fun n => P.eval (u n).1) Filter.atTop (nhds (P.eval x)) :=
      (P.continuous.tendsto x).comp hxl
    have hl2 : Filter.Tendsto (fun n => P.eval (u n).1) Filter.atTop (nhds 0) := by
      apply squeeze_zero_norm hval
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 h0).const_mul c
      rwa [mul_zero] at this
    exact tendsto_nhds_unique hl1 hl2
  · have hl : Filter.Tendsto (fun n => ‖(u n).1 - x₀‖) Filter.atTop (nhds ‖x - x₀‖) :=
      (hxl.sub_const x₀).norm
    exact le_of_tendsto' hl hnear

end ReciprocityTheory.ChartRestriction.L1
end
end
