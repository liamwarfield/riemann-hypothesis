module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGmSlash
section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModPerm
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem perm_Tmat_det {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) : (Tmat t).det = m := by
  simp only [Tm, Finset.mem_image, Finset.mem_sigma, Nat.mem_divisors, Finset.mem_range] at ht
  obtain ⟨⟨a, b⟩, ⟨⟨hdvd, _⟩, _⟩, rfl⟩ := ht
  simp only [Tmat, Matrix.det_fin_two_of, mul_zero, sub_zero]
  exact_mod_cast Nat.mul_div_cancel' hdvd

end ReciprocityTheory.ChartRestriction.L1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModFacSlash
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem denom_SL_coe (γ : SL(2, ℤ)) (z : ℍ) :
    denom γ z = ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) := by
  first
  | rfl
  | simp [UpperHalfPlane.denom]
  | (simp [UpperHalfPlane.denom]; norm_cast)

theorem smul_SL_coe (γ : SL(2, ℤ)) (z : ℍ) :
    ((γ • z : ℍ) : ℂ) = (((γ 0 0 : ℤ) : ℂ) * z + ((γ 0 1 : ℤ) : ℂ)) /
      (((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ)) := by
  first
  | (rw [UpperHalfPlane.coe_smul, UpperHalfPlane.num, denom_SL_coe]; simp)
  | (rw [UpperHalfPlane.specialLinearGroup_apply]; simp)
  | simp [UpperHalfPlane.coe_smul, UpperHalfPlane.num, UpperHalfPlane.denom]

theorem pt_smul {t t' : ℕ × ℕ × ℕ} (ht : 0 < t.1 ∧ 0 < t.2.2) (ht' : 0 < t'.1 ∧ 0 < t'.2.2)
    (γ γ' : SL(2, ℤ))
    (h : Tmat t * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t') (τ : ℍ) :
    pt t.1 t.2.1 t.2.2 (γ • τ) = γ' • pt t'.1 t'.2.1 t'.2.2 τ ∧
      denom γ' (pt t'.1 t'.2.1 t'.2.2 τ) * (t'.2.2 : ℂ) = (t.2.2 : ℂ) * denom γ τ := by
  have hm : ∀ i j, (Tmat t * (γ : Matrix (Fin 2) (Fin 2) ℤ)) i j =
      ((γ' : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t') i j := fun i j => by rw [h]
  have z00 : (t.1 : ℤ) * γ 0 0 + (t.2.1 : ℤ) * γ 1 0 = γ' 0 0 * (t'.1 : ℤ) := by
    have hh := hm 0 0
    simp [Tmat, Matrix.mul_apply, Fin.sum_univ_two] at hh
    linarith
  have z01 : (t.1 : ℤ) * γ 0 1 + (t.2.1 : ℤ) * γ 1 1 = γ' 0 0 * (t'.2.1 : ℤ) + γ' 0 1 * (t'.2.2 : ℤ) := by
    have hh := hm 0 1
    simp [Tmat, Matrix.mul_apply, Fin.sum_univ_two] at hh
    linarith
  have z10 : (t.2.2 : ℤ) * γ 1 0 = γ' 1 0 * (t'.1 : ℤ) := by
    have hh := hm 1 0
    simp [Tmat, Matrix.mul_apply, Fin.sum_univ_two] at hh
    linarith
  have z11 : (t.2.2 : ℤ) * γ 1 1 = γ' 1 0 * (t'.2.1 : ℤ) + γ' 1 1 * (t'.2.2 : ℤ) := by
    have hh := hm 1 1
    simp [Tmat, Matrix.mul_apply, Fin.sum_univ_two] at hh
    linarith
  have c00 : (t.1 : ℂ) * ((γ 0 0 : ℤ) : ℂ) + (t.2.1 : ℂ) * ((γ 1 0 : ℤ) : ℂ) = ((γ' 0 0 : ℤ) : ℂ) * (t'.1 : ℂ) := by exact_mod_cast z00
  have c01 : (t.1 : ℂ) * ((γ 0 1 : ℤ) : ℂ) + (t.2.1 : ℂ) * ((γ 1 1 : ℤ) : ℂ) = ((γ' 0 0 : ℤ) : ℂ) * (t'.2.1 : ℂ) + ((γ' 0 1 : ℤ) : ℂ) * (t'.2.2 : ℂ) := by exact_mod_cast z01
  have c10 : (t.2.2 : ℂ) * ((γ 1 0 : ℤ) : ℂ) = ((γ' 1 0 : ℤ) : ℂ) * (t'.1 : ℂ) := by exact_mod_cast z10
  have c11 : (t.2.2 : ℂ) * ((γ 1 1 : ℤ) : ℂ) = ((γ' 1 0 : ℤ) : ℂ) * (t'.2.1 : ℂ) + ((γ' 1 1 : ℤ) : ℂ) * (t'.2.2 : ℂ) := by exact_mod_cast z11
  have he : (t.2.2 : ℂ) ≠ 0 := by exact_mod_cast ht.2.ne'
  have he' : (t'.2.2 : ℂ) ≠ 0 := by exact_mod_cast ht'.2.ne'
  have hD : ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by rw [← denom_SL_coe]; exact UpperHalfPlane.denom_ne_zero _ _
  have hD' : ((γ' 1 0 : ℤ) : ℂ) * ((pt t'.1 t'.2.1 t'.2.2 τ : ℍ) : ℂ) + ((γ' 1 1 : ℤ) : ℂ) ≠ 0 := by rw [← denom_SL_coe]; exact UpperHalfPlane.denom_ne_zero _ _
  have hZ : ((γ • τ : ℍ) : ℂ) * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) = ((γ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 0 1 : ℤ) : ℂ) := by
    rw [smul_SL_coe γ τ]; exact div_mul_cancel₀ _ hD
  have hW : ((pt t'.1 t'.2.1 t'.2.2 τ : ℍ) : ℂ) * (t'.2.2 : ℂ) = (t'.1 : ℂ) * (τ : ℂ) + (t'.2.1 : ℂ) := by
    rw [pt_coe ht'.1 ht'.2]; exact div_mul_cancel₀ _ he'
  have c2 : (((γ' 1 0 : ℤ) : ℂ) * ((pt t'.1 t'.2.1 t'.2.2 τ : ℍ) : ℂ) + ((γ' 1 1 : ℤ) : ℂ)) * (t'.2.2 : ℂ) = (t.2.2 : ℂ) * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) := by
    linear_combination ((γ' 1 0 : ℤ) : ℂ) * hW - (τ : ℂ) * c10 - c11
  refine ⟨UpperHalfPlane.ext ?_, ?_⟩
  · rw [pt_coe ht.1 ht.2, smul_SL_coe γ' (pt t'.1 t'.2.1 t'.2.2 τ), div_eq_div_iff he hD']
    have key : ((t'.2.2 : ℂ) * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ))) *
        (((t.1 : ℂ) * ((γ • τ : ℍ) : ℂ) + (t.2.1 : ℂ)) * (((γ' 1 0 : ℤ) : ℂ) * ((pt t'.1 t'.2.1 t'.2.2 τ : ℍ) : ℂ) + ((γ' 1 1 : ℤ) : ℂ)) - (((γ' 0 0 : ℤ) : ℂ) * ((pt t'.1 t'.2.1 t'.2.2 τ : ℍ) : ℂ) + ((γ' 0 1 : ℤ) : ℂ)) * (t.2.2 : ℂ)) = 0 := by
      linear_combination (((t.1 : ℂ) * ((γ • τ : ℍ) : ℂ) + (t.2.1 : ℂ)) * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ))) * c2 +
        ((t.2.2 : ℂ) * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ))) * ((t.1 : ℂ) * hZ - ((γ' 0 0 : ℤ) : ℂ) * hW + (τ : ℂ) * c00 + c01)
    rcases mul_eq_zero.mp key with h0 | h0
    · exact absurd h0 (mul_ne_zero he' hD)
    · exact sub_eq_zero.mp h0
  · rw [denom_SL_coe, denom_SL_coe]
    exact c2

theorem fac_smul {t t' : ℕ × ℕ × ℕ} (ht : 0 < t.1 ∧ 0 < t.2.2) (ht' : 0 < t'.1 ∧ 0 < t'.2.2)
    (γ γ' : SL(2, ℤ))
    (h : Tmat t * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t') (τ : ℍ) :
    fac t (γ • τ) = denom γ τ ^ 24 * ((t.2.2 : ℂ) / t'.2.2) ^ 12 * fac t' τ := by
  obtain ⟨h1, h2⟩ := pt_smul ht ht' γ γ' h τ
  have he' : ((t'.2.2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast ht'.2.ne'
  have hd : denom γ' (pt t'.1 t'.2.1 t'.2.2 τ) = (t.2.2 : ℂ) / t'.2.2 * denom γ τ := by
    rw [div_mul_eq_mul_div, eq_div_iff he']
    exact h2
  simp only [fac]
  rw [h1, AA_smul, DD_smul, AA_smul, DD_smul, hd]
  ring

end ReciprocityTheory.ChartRestriction.L1
end
end

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem Gm_smul {m : ℕ} (hm : 0 < m) (γ : SL(2, ℤ)) (τ : ℍ) :
    Gm m (γ • τ) = denom γ τ ^ (24 * (Tm m).card) * Gm m τ := by
  classical
  have hex : ∀ t ∈ Tm m, ∃ (γ' : SL(2, ℤ)) (t' : ℕ × ℕ × ℕ), t' ∈ Tm m ∧
      Tmat t * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t' := by
    intro t ht
    apply hnf_exists hm
    rw [Matrix.det_mul, perm_Tmat_det hm ht, Matrix.SpecialLinearGroup.det_coe, mul_one]
  choose! g σ hσ hg using hex
  have hinvR : ∀ A : SL(2, ℤ),
      (A : Matrix (Fin 2) (Fin 2) ℤ) * ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    intro A
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hinvL : ∀ A : SL(2, ℤ),
      ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (A : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    intro A
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hinj : Set.InjOn σ (Tm m) := by
    intro t1 h1 t2 h2 he
    have e1 := hg t1 h1
    have e2 := hg t2 h2
    rw [← he] at e2
    have key : Tmat t1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) =
        ((g t1 * (g t2)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
          (Tmat t2 * (γ : Matrix (Fin 2) (Fin 2) ℤ)) := by
      rw [e1, e2, Matrix.SpecialLinearGroup.coe_mul, ← mul_assoc, mul_assoc (g t1 : Matrix (Fin 2) (Fin 2) ℤ),
        hinvL, mul_one]
    apply hnf_unique hm h1 h2 (g t1 * (g t2)⁻¹)
    calc Tmat t1 = Tmat t1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
          rw [mul_assoc, hinvR, mul_one]
      _ = ((g t1 * (g t2)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t2 *
            (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
          rw [key]; simp only [mul_assoc]
      _ = ((g t1 * (g t2)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t2 := by
          rw [mul_assoc _ (γ : Matrix (Fin 2) (Fin 2) ℤ), hinvR, mul_one]
  have himg : (Tm m).image σ = Tm m := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
      exact hσ t ht
    · rw [Finset.card_image_of_injOn hinj]
  have hprod : ∀ F : ℕ × ℕ × ℕ → ℂ, ∏ t ∈ Tm m, F (σ t) = ∏ t ∈ Tm m, F t := by
    intro F
    conv_rhs => rw [← himg]
    rw [Finset.prod_image hinj]
  have hfac : ∏ t ∈ Tm m, fac (σ t) τ = ∏ t ∈ Tm m, fac t τ := hprod (fun t => fac t τ)
  have hden : ∏ t ∈ Tm m, ((σ t).2.2 : ℂ) = ∏ t ∈ Tm m, (t.2.2 : ℂ) := hprod (fun t => (t.2.2 : ℂ))
  have hne : ∏ t ∈ Tm m, (t.2.2 : ℂ) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro t ht
    exact_mod_cast (Tm_pos hm ht).2.ne'
  have hstep : ∏ t ∈ Tm m, fac t (γ • τ) =
      ∏ t ∈ Tm m, (denom γ τ ^ 24 * ((t.2.2 : ℂ) / (σ t).2.2) ^ 12 * fac (σ t) τ) :=
    Finset.prod_congr rfl (fun t ht => fac_smul (Tm_pos hm ht) (Tm_pos hm (hσ t ht)) γ (g t) (hg t ht) τ)
  unfold Gm
  rw [hstep, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, ← pow_mul, hfac,
    Finset.prod_pow, Finset.prod_div_distrib, hden, div_self hne, one_pow, mul_one]

end ReciprocityTheory.ChartRestriction.L1
end
end

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem IsMF.mdiff {k : ℤ} {f : ℍ → ℂ} (h : IsMF k f) : MDiff f := by
  obtain ⟨g, hg⟩ := h
  have e : f = ⇑g := funext fun τ => (hg τ).symm
  subst e
  exact ModularFormClass.holo g

theorem IsMF.bdd {k : ℤ} {f : ℍ → ℂ} (h : IsMF k f) : IsBoundedAtImInfty f := by
  obtain ⟨g, hg⟩ := h
  have e : f = ⇑g := funext fun τ => (hg τ).symm
  subst e
  exact ModularFormClass.bdd_at_infty g

theorem pt_im {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) (τ : ℍ) :
    (pt a b e τ).im = (a : ℝ) / e * τ.im := by
  have h1 : (((a : ℂ) * (τ : ℂ) + b) / e).im = (a : ℝ) / e * τ.im := by
    rw [Complex.div_natCast_im]
    simp
    ring
  have hpos : 0 < (((a : ℂ) * (τ : ℂ) + b) / e).im := by
    rw [h1]
    have := τ.im_pos
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    have he' : (0 : ℝ) < e := by exact_mod_cast he
    positivity
  unfold pt
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hpos]
  exact h1

theorem mdiff_comp_pt {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) {f : ℍ → ℂ} (hf : MDiff f) :
    MDiff (fun τ => f (pt a b e τ)) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf ⊢
  have hmap : Set.MapsTo (fun z : ℂ => ((a : ℂ) * z + b) / e) {z | 0 < z.im} {z | 0 < z.im} := by
    intro z hz
    have h := pt_im ha he b ⟨z, hz⟩
    have h2 := congrArg Complex.im (pt_coe ha he b ⟨z, hz⟩)
    have h3 := (pt a b e ⟨z, hz⟩).im_pos
    rw [UpperHalfPlane.coe_im] at h2
    rw [h2] at h3
    exact h3
  have hd : DifferentiableOn ℂ (fun z : ℂ => ((a : ℂ) * z + b) / e) {z | 0 < z.im} := by
    fun_prop
  refine (hf.comp hd hmap).congr fun z hz => ?_
  simp only [Function.comp_apply, pt, ofComplex_apply_of_im_pos hz]

theorem tendsto_pt {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) :
    Filter.Tendsto (pt a b e) atImInfty atImInfty := by
  rw [UpperHalfPlane.atImInfty, Filter.tendsto_comap_iff]
  have h : (UpperHalfPlane.im ∘ pt a b e) = fun τ => (a : ℝ) / e * τ.im := funext fun τ => pt_im ha he b τ
  rw [h]
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hc : (0 : ℝ) < (a : ℝ) / e := by positivity
  exact Filter.Tendsto.const_mul_atTop hc Filter.tendsto_comap

theorem bdd_comp_pt {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) {f : ℍ → ℂ}
    (hf : IsBoundedAtImInfty f) : IsBoundedAtImInfty (fun τ => f (pt a b e τ)) := by
  exact hf.comp_tendsto (tendsto_pt ha he b)

theorem fac_mdiff {t : ℕ × ℕ × ℕ} (ht : 0 < t.1 ∧ 0 < t.2.2) : MDiff (fac t) := by
  have hA := isMF_AA.mdiff
  have hD := isMF_DD.mdiff
  exact (hA.mul (mdiff_comp_pt ht.1 ht.2 t.2.1 hD)).sub ((mdiff_comp_pt ht.1 ht.2 t.2.1 hA).mul hD)

theorem fac_bdd {t : ℕ × ℕ × ℕ} (ht : 0 < t.1 ∧ 0 < t.2.2) : IsBoundedAtImInfty (fac t) := by
  have hA := isMF_AA.bdd
  have hD := isMF_DD.bdd
  exact (hA.mul (bdd_comp_pt ht.1 ht.2 t.2.1 hD)).sub ((bdd_comp_pt ht.1 ht.2 t.2.1 hA).mul hD)

theorem Gm_mdiff {m : ℕ} (hm : 0 < m) : MDiff (Gm m) := by
  unfold Gm
  have key : ∀ s : Finset (ℕ × ℕ × ℕ), s ⊆ Tm m → MDiff (fun τ => ∏ t ∈ s, fac t τ) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simpa using (mdifferentiable_const : MDiff (fun _ : ℍ => (1 : ℂ)))
    | insert t s ht ih =>
      intro hs
      simp only [Finset.prod_insert ht]
      exact (fac_mdiff (Tm_pos hm (hs (Finset.mem_insert_self t s)))).mul
        (ih (fun x hx => hs (Finset.mem_insert_of_mem hx)))
  exact key _ subset_rfl

theorem Gm_bdd {m : ℕ} (hm : 0 < m) : IsBoundedAtImInfty (Gm m) := by
  unfold Gm
  have key : ∀ s : Finset (ℕ × ℕ × ℕ), s ⊆ Tm m → IsBoundedAtImInfty (fun τ => ∏ t ∈ s, fac t τ) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.prod_empty]
      exact Filter.const_boundedAtFilter atImInfty (1 : ℂ)
    | insert t s ht ih =>
      intro hs
      simp only [Finset.prod_insert ht]
      exact Filter.BoundedAtFilter.mul (fac_bdd (Tm_pos hm (hs (Finset.mem_insert_self t s))))
        (ih (fun x hx => hs (Finset.mem_insert_of_mem hx)))
  exact key _ subset_rfl

theorem Gm_slash {m : ℕ} (hm : 0 < m) (γ : SL(2, ℤ)) :
    (Gm m) ∣[24 * ((Tm m).card : ℤ)] γ = Gm m := by
  funext τ
  rw [SL_slash_apply, Gm_smul hm γ τ]
  have hd : denom γ τ ≠ 0 := denom_ne_zero _ τ
  have : (24 * ((Tm m).card : ℤ)) = ((24 * (Tm m).card : ℕ) : ℤ) := by push_cast; ring
  rw [this, zpow_neg, zpow_natCast]
  field_simp

theorem gmForm {m : ℕ} (hm : 0 < m) : IsMF (24 * ((Tm m).card : ℤ)) (Gm m) := by
  refine ⟨{ toFun := Gm m
            slash_action_eq' := ?_
            holo' := Gm_mdiff hm
            bdd_at_cusps' := ?_ }, fun τ => rfl⟩
  · intro A hA
    obtain ⟨A, rfl⟩ := hA
    exact Gm_slash hm A
  · intro c hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [Gm_slash hm γ]
    exact Gm_bdd hm

end ReciprocityTheory.ChartRestriction.L1
