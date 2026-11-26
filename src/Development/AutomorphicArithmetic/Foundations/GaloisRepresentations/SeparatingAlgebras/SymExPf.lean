module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StLocB
public import GroundTheory.AutomorphicForms.Satake

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.SymExPf
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.symEx_pf :
    UpperTheory.Gal.Gen.SymEx := by
  intro n Φ
  refine ⟨polyEmb (n := n) (∏ σ : Equiv.Perm (Fin n), MvPolynomial.rename σ Φ), ?_, ?_, ?_⟩
  · show ∀ τ : Equiv.Perm (Fin n), permAct τ _ = _
    intro τ
    rw [← polyEmb_rename]
    congr 1
    rw [map_prod]
    simp_rw [MvPolynomial.rename_rename]
    exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ (fun σ => rfl)
  · intro z
    rw [evalAt_polyEmb, map_prod]
    refine Finset.prod_congr rfl (fun σ _ => ?_)
    rw [MvPolynomial.aeval_rename]
    rfl
  · intro hΦ
    refine ⟨∏ σ : Equiv.Perm (Fin n), MvPolynomial.rename σ Φ, ?_, fun z => ?_⟩
    · rw [Finset.prod_ne_zero_iff]
      intro σ _ h
      apply hΦ
      exact MvPolynomial.rename_injective _ σ.injective (by rw [h, map_zero])
    · rw [evalAt_polyEmb]
      rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.RepsEx
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.repsEx_pf :
    UpperTheory.Gal.Gen.RepsEx := by
  intro F _ _ _ _ n _ _ μ _ h
  classical
  have hKc := GLnLocal.isCompact_integralGL F n
  have hKo : IsOpen ((GLnLocal.integralGL F n : Subgroup (GL (Fin n) F)) : Set (GL (Fin n) F)) :=
    (integralOpen F n).isOpen
  have hbi := HeckeAlgebra.HeckeAlgebraLevel.val_mem hKc hKo h
  have hsupp : HasCompactSupport ⇑(HeckeAlgebra.HeckeAlgebraLevel.val hKc hKo h) := (HeckeAlgebra.mem _).2
  set φ : GL (Fin n) F → ℂ := ⇑(HeckeAlgebra.HeckeAlgebraLevel.val hKc hKo h) with hφ
  have hright : ∀ g k, k ∈ GLnLocal.integralGL F n → φ (g * k) = φ g := fun g k hk => (hbi k hk g).2
  set S := (finite_image_mk_tsupport (integralOpen F n) hsupp).toFinset with hS
  refine ⟨S.image Quotient.out, ?_, ?_⟩
  · intro g hg g' hg' hgg
    simp only [Finset.mem_image] at hg hg'
    obtain ⟨x, -, rfl⟩ := hg
    obtain ⟨y, -, rfl⟩ := hg'
    have hxy : x = y := by
      rw [← QuotientGroup.out_eq' x, ← QuotientGroup.out_eq' y]
      exact QuotientGroup.eq.2 hgg
    rw [hxy]
  · intro f hf
    have hint := integral_eq_smul_finsum_coset μ (integralOpen F n) hKc (f := fun x => φ x * f x)
      hsupp.mul_right (fun g k hk => by simp only [hright g k hk, hf g k hk])
    rw [hint, Complex.real_smul]
    congr 1
    rw [finsum_eq_sum_of_support_subset (s := S) _ ?_, Finset.sum_image]
    · rfl
    · intro x _ y _ hxy
      exact Quotient.out_injective hxy
    · intro x hx
      have hne : φ (Quotient.out x) ≠ 0 := left_ne_zero_of_mul hx
      rw [hS, Set.Finite.coe_toFinset]
      exact ⟨Quotient.out x, subset_tsupport _ hne, QuotientGroup.out_eq' x⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StarEx
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

namespace UpperTheory.Gal.Gen

private noncomputable def refl {n : ℕ} (z : Fin n → ℂˣ) : Fin n → ℂˣ :=
  fun i => (Units.map (starRingEnd ℂ).toMonoidHom (z i))⁻¹

private noncomputable def star' {n : ℕ} (p : LaurentRing n) : LaurentRing n :=
  p.coeff.sum fun l c => AddMonoidAlgebra.single (-l) ((starRingEnd ℂ) c)

private theorem refl_val {n : ℕ} (z : Fin n → ℂˣ) (i : Fin n) :
    ((refl z i : ℂˣ) : ℂ) = ((starRingEnd ℂ) (z i : ℂ))⁻¹ := by
  simp [refl]

private theorem evalAt_star' {n : ℕ} (p : LaurentRing n) (z : Fin n → ℂˣ) :
    evalAt z (star' p) = (starRingEnd ℂ) (evalAt (refl z) p) := by
  rw [star', map_finsuppSum, evalAt_apply, map_finsuppSum]
  refine Finsupp.sum_congr ?_
  intro l _
  rw [evalAt_single, map_mul, monomialChar_apply, monomialChar_apply, map_prod]
  congr 1
  refine Finset.prod_congr rfl ?_
  intro i _
  simp [refl_val, Units.val_zpow_eq_zpow_val, zpow_neg, map_zpow₀, map_inv₀]

private theorem refl_comp {n : ℕ} (z : Fin n → ℂˣ) (σ : Equiv.Perm (Fin n)) :
    refl (z ∘ σ) = refl z ∘ σ := rfl

private theorem refl_eq {n : ℕ} (z : Fin n → ℂˣ) (hz : ∀ i, ‖(z i : ℂ)‖ = 1) : refl z = z := by
  funext i
  apply Units.ext
  rw [refl_val, Complex.inv_def, Complex.conj_conj, Complex.normSq_conj, Complex.normSq_eq_norm_sq, hz i]
  simp

end UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.starEx_pf :
    UpperTheory.Gal.Gen.StarEx := by
  intro n p hp
  refine ⟨star' p, ?_, fun z hz => ?_⟩
  · intro σ
    refine eq_of_forall_evalAt fun z => ?_
    rw [evalAt_permAct, evalAt_star', evalAt_star', refl_comp, ← evalAt_permAct, hp σ]
  · rw [evalAt_star', refl_eq z hz]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.HalfCancel
noncomputable section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical

namespace UpperTheory.Gal.Gen

private lemma factor_eq {a b t : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0) (hat : a - t * b ≠ 0) :
    (a - t * b) / (a - b) * ((1 - a⁻¹ / b⁻¹) / (1 - t * (a⁻¹ / b⁻¹))) = 1 := by
  have e : a⁻¹ / b⁻¹ = b / a := by field_simp
  rw [e]
  have h1 : 1 - b / a = (a - b) / a := by field_simp
  have h2 : 1 - t * (b / a) = (a - t * b) / a := by field_simp
  rw [h1, h2]
  field_simp

private lemma half_cancel (n : ℕ) (t : ℝ) (h0 : 0 ≤ t) (h1 : t < 1) (w : Fin n → ℂˣ)
    (hw : Function.Injective w) (hn : ∀ i, ‖(w i : ℂ)‖ = 1) :
    (∏ p ∈ prs n, ((w p.1 : ℂ) - (t : ℂ) * (w p.2 : ℂ)) / ((w p.1 : ℂ) - (w p.2 : ℂ))) *
      half (t : ℂ) w⁻¹ = 1 := by
  unfold half
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one (fun p hp => ?_)
  simp only [Pi.inv_apply, Units.val_inv_eq_inv_val]
  simp only [prs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  have hne : p.1 ≠ p.2 := hp.ne
  refine factor_eq (w p.1).ne_zero (w p.2).ne_zero ?_ ?_
  · intro h
    exact hne (hw (Units.ext (sub_eq_zero.mp h)))
  · intro h
    have h' : (w p.1 : ℂ) = (t : ℂ) * (w p.2 : ℂ) := sub_eq_zero.mp h
    have hn' := congrArg norm h'
    rw [norm_mul, hn, hn, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0] at hn'
    linarith

theorem rDens_pf : RFormula → DensSymm → RDens := by
  intro hR hS n t h0 h1 l z hz hn
  rw [hR n (t : ℂ) l z hz, Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hw : Function.Injective (z ∘ σ) := hz.comp σ.injective
  have hwn : ∀ i, ‖((z ∘ σ) i : ℂ)‖ = 1 := fun i => hn (σ i)
  have hc := half_cancel n t h0 h1 (z ∘ σ) hw hwn
  rw [← hS n (t : ℂ) z σ]
  unfold dens
  simp only [Function.comp_apply] at hc
  calc _ = monomialChar l (z ∘ σ) * half (t : ℂ) (z ∘ σ) * ((∏ p ∈ prs n, ((z (σ p.1) : ℂ) - (t : ℂ) * (z (σ p.2) : ℂ)) / ((z (σ p.1) : ℂ) - (z (σ p.2) : ℂ))) * half (t : ℂ) (z ∘ σ)⁻¹) := by ring
    _ = _ := by rw [hc, mul_one]

end UpperTheory.Gal.Gen

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.DensCont
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private lemma pt_val {n : ℕ} (θ : Fin n → UnitAddCircle) (i : Fin n) :
    ((pt θ i : ℂˣ) : ℂ) = ((AddCircle.toCircle (θ i) : Circle) : ℂ) := rfl

private lemma pt_cont {n : ℕ} (i : Fin n) :
    Continuous fun θ : Fin n → UnitAddCircle => ((pt θ i : ℂˣ) : ℂ) := by
  simp only [pt_val]
  fun_prop

private lemma pt_norm {n : ℕ} (θ : Fin n → UnitAddCircle) (i : Fin n) :
    ‖((pt θ i : ℂˣ) : ℂ)‖ = 1 := by
  rw [pt_val]
  exact Circle.norm_coe _

private lemma half_cont {X : Type*} [TopologicalSpace X] {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {n : ℕ}
    (u : X → Fin n → ℂˣ) (hc : ∀ i, Continuous fun x => ((u x i : ℂˣ) : ℂ))
    (hn : ∀ x i, ‖((u x i : ℂˣ) : ℂ)‖ = 1) :
    Continuous fun x => half (t : ℂ) (u x) := by
  unfold half
  refine continuous_finsetProd _ (fun p _ => ?_)
  have h1 := hc p.1
  have h2 := hc p.2
  have hne : ∀ x, ((u x p.2 : ℂˣ) : ℂ) ≠ 0 := fun x => Units.ne_zero _
  have hq : Continuous fun x => ((u x p.1 : ℂˣ) : ℂ) / ((u x p.2 : ℂˣ) : ℂ) := h1.div h2 hne
  refine (continuous_const.sub hq).div (continuous_const.sub (continuous_const.mul hq)) (fun x => ?_)
  intro h
  have hnq : ‖((u x p.1 : ℂˣ) : ℂ) / ((u x p.2 : ℂˣ) : ℂ)‖ = 1 := by
    rw [norm_div, hn, hn, div_one]
  have h' := congrArg norm (sub_eq_zero.mp h).symm
  rw [norm_one, norm_mul, hnq, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0] at h'
  linarith

theorem UpperTheory.Gal.Gen.densCont_pf :
    UpperTheory.Gal.Gen.DensCont := by
  intro n t ht0 ht1
  have hinvc : ∀ i, Continuous fun θ : Fin n → UnitAddCircle => (((pt θ)⁻¹ i : ℂˣ) : ℂ) := by
    intro i
    simp only [Pi.inv_apply, Units.val_inv_eq_inv_val]
    exact (pt_cont i).inv₀ (fun θ => Units.ne_zero _)
  have hinvn : ∀ (θ : Fin n → UnitAddCircle) i, ‖(((pt θ)⁻¹ i : ℂˣ) : ℂ)‖ = 1 := by
    intro θ i
    simp only [Pi.inv_apply, Units.val_inv_eq_inv_val, norm_inv, pt_norm, inv_one]
  refine ⟨half_cont ht0 ht1 _ pt_cont pt_norm, ?_, ?_, pt_norm⟩
  · exact (half_cont ht0 ht1 _ pt_cont pt_norm).mul (half_cont ht0 ht1 _ hinvc hinvn)
  · intro p
    simp only [evalAt_apply, monomialChar_apply, Units.val_zpow_eq_zpow_val]
    unfold Finsupp.sum
    refine continuous_finsetSum _ (fun l _ => ?_)
    refine continuous_const.mul (continuous_finsetProd _ (fun i _ => ?_))
    exact (pt_cont i).zpow₀ _ (fun θ => Or.inl (Units.ne_zero _))
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.DensSymm
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private noncomputable def densPhi {n : ℕ} (t : ℂ) (z : Fin n → ℂˣ) (p : Fin n × Fin n) : ℂ :=
  (1 - (z p.1 : ℂ) / (z p.2 : ℂ)) / (1 - t * ((z p.1 : ℂ) / (z p.2 : ℂ)))

private lemma half_inv_eq {n : ℕ} (t : ℂ) (z : Fin n → ℂˣ) :
    half t z⁻¹ = ∏ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.2 < p.1), densPhi t z p := by
  unfold half
  refine Finset.prod_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simpa using hp
  · intro p hp
    simpa using hp
  · intro p _
    simp
  · intro p _
    simp
  · intro p _
    have h : (((z⁻¹) p.1 : ℂˣ) : ℂ) / (((z⁻¹) p.2 : ℂˣ) : ℂ) = (z p.2 : ℂ) / (z p.1 : ℂ) := by
      simp only [Pi.inv_apply, Units.val_inv_eq_inv_val]
      rw [inv_div_inv]
    simp only [densPhi, Prod.fst_swap, Prod.snd_swap, h]

private lemma dens_eq {n : ℕ} (t : ℂ) (z : Fin n → ℂˣ) :
    dens t z = ∏ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2), densPhi t z p := by
  have h3 : (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2) =
      prs n ∪ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.2 < p.1) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, prs]
    exact ⟨fun h => lt_or_gt_of_ne h, fun h => h.elim (fun h => h.ne) (fun h => h.ne')⟩
  have hd : Disjoint (prs n) ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.2 < p.1)) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, prs] at hp hq
    exact lt_asymm hp hq
  rw [h3, Finset.prod_union hd, ← half_inv_eq]
  rfl

theorem UpperTheory.Gal.Gen.densSymm :
    UpperTheory.Gal.Gen.DensSymm := by
  intro n t z σ
  rw [dens_eq, dens_eq]
  refine Finset.prod_nbij' (Prod.map σ σ) (Prod.map σ.symm σ.symm) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simpa using hp
  · intro p hp
    simpa using hp
  · rintro ⟨a, b⟩ _
    simp
  · rintro ⟨a, b⟩ _
    simp
  · intro p _
    rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GammaInt
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private theorem qInv_props (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : 0 ≤ ((qF F : ℝ))⁻¹ ∧ ((qF F : ℝ))⁻¹ < 1 := by
  have h : 1 < qF F := by
    haveI := fintypeResidue' (F := F)
    exact Finite.one_lt_card
  have h' : (1 : ℝ) < (qF F : ℝ) := by exact_mod_cast h
  exact ⟨by positivity, inv_lt_one_of_one_lt₀ h'⟩

theorem UpperTheory.Gal.Gen.gammaInt_pf :
    UpperTheory.Gal.Gen.RInt → UpperTheory.Gal.Gen.DensCont → UpperTheory.Gal.Gen.GammaInt := by
  intro hR hD F _ _ _ _ n _ _ μ _ g
  obtain ⟨ht0, ht1⟩ := qInv_props F
  have htc : (((((qF F : ℝ))⁻¹ : ℝ)) : ℂ) = ((qF F : ℂ))⁻¹ := by push_cast; rfl
  have hv : vPoly n ((qF F : ℂ))⁻¹ ≠ 0 := vPoly_ne_zero injective_qInv_pow n
  have hint := hR n _ ht0 ht1
  have hcont := (hD n _ ht0 ht1).2.2.1
  rw [htc] at hint
  obtain ⟨l, hl, k₁, hk₁, k₂, hk₂, rfl⟩ := Cartan.exists_eq_mul_diagPow_mul F n g
  have hdt : Cartan.diagPow F n l = Iwasawa.torusPow F n l := by
    apply Units.ext
    rw [Cartan.coe_diagPow, Iwasawa.coe_torusPow]
  have hΓ : ∀ z : Fin n → ℂˣ, zonalSpherical μ z (k₁ * Cartan.diagPow F n l * k₂) =
      (vPoly n ((qF F : ℂ))⁻¹)⁻¹ * (halfModulus F l * evalAt z (hlR ((qF F : ℂ))⁻¹ l)) := by
    intro z
    rw [zonalSpherical_mul_right z _ hk₂, zonalSpherical_mul_left z hk₁, hdt,
      eq_inv_mul_iff_mul_eq₀ hv]
    exact macdonald_formula_hlR z hl
  refine ⟨?_, ?_⟩
  · simp only [hΓ]
    exact continuous_const.mul (continuous_const.mul (hcont _))
  · have hI : ∫ θ : Fin n → UnitAddCircle,
        zonalSpherical μ (pt θ) (k₁ * Cartan.diagPow F n l * k₂) * dens ((qF F : ℂ))⁻¹ (pt θ) =
        (vPoly n ((qF F : ℂ))⁻¹)⁻¹ * halfModulus F l *
          ∫ θ : Fin n → UnitAddCircle, evalAt (pt θ) (hlR ((qF F : ℂ))⁻¹ l) * dens ((qF F : ℂ))⁻¹ (pt θ) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      simp only [hΓ]
      ring
    rw [hI, hint l hl, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hv, one_mul]
    have hdom0 : Cartan.IsDominant (0 : Fin n → ℤ) := fun _ _ _ => le_rfl
    have hd0 : Cartan.diagPow F n 0 = 1 := by
      apply Units.ext
      rw [Cartan.coe_diagPow]
      simp
    by_cases h0 : l = 0
    · subst h0
      rw [if_pos rfl, halfModulus_zero, one_mul, if_pos]
      rw [hd0, mul_one]
      exact mul_mem hk₁ hk₂
    · rw [if_neg h0, mul_zero, if_neg]
      intro hg
      have hk : k₁⁻¹ * (k₁ * Cartan.diagPow F n l * k₂) * k₂⁻¹ ∈ GLnLocal.integralGL F n :=
        mul_mem (mul_mem (inv_mem hk₁) hg) (inv_mem hk₂)
      refine h0 (Cartan.eq_of_mul_diagPow_eq F n hdom0 hl hk (one_mem _) ?_).symm
      rw [hd0]
      group
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.SmallPf
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.small_pf :
    UpperTheory.Gal.Gen.SymEx → UpperTheory.Gal.Gen.StarEx → UpperTheory.Gal.Gen.NullZero → UpperTheory.Gal.Gen.DensCont → UpperTheory.Gal.Gen.Small := by
  intro hSym hStar hNull hDens n Φ hΦ δ hδ
  obtain ⟨P, hPmem, hPprod, hPpoly⟩ := hSym n Φ
  obtain ⟨Ψ, hΨ, hPΨ⟩ := hPpoly hΦ
  obtain ⟨Q, hQmem, hQ⟩ := hStar n P hPmem
  obtain ⟨-, -, hcont, hnorm⟩ := hDens n 0 le_rfl one_pos
  obtain ⟨M, hM⟩ := (isCompact_univ : IsCompact (Set.univ : Set (Fin n → UnitAddCircle))).exists_bound_of_continuousOn
    (hcont P).continuousOn
  set c : ℝ := 1 / (M ^ 2 + 1) with hc
  have hc0 : 0 < c := by positivity
  let g : (Fin n → UnitAddCircle) → ℝ := fun θ => 1 - c * ‖evalAt (pt θ) P‖ ^ 2
  have hg0 : ∀ θ, 0 ≤ g θ := by
    intro θ
    have h1 : ‖evalAt (pt θ) P‖ ≤ M := hM θ (Set.mem_univ _)
    have h2 : ‖evalAt (pt θ) P‖ ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : c * ‖evalAt (pt θ) P‖ ^ 2 ≤ 1 := by
      rw [hc, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
      linarith
    simp only [g]
    linarith
  have hg1 : ∀ θ, g θ ≤ 1 := by
    intro θ
    simp only [g]
    have : 0 ≤ c * ‖evalAt (pt θ) P‖ ^ 2 := by positivity
    linarith
  let pk : ℕ → LaurentRing n := fun k => (1 - (c : ℂ) • (P * Q)) ^ k
  have hpk_mem : ∀ k, pk k ∈ symmetricLaurent (n := n) := by
    intro k
    exact Subalgebra.pow_mem _ (Subalgebra.sub_mem _ (Subalgebra.one_mem _)
      (Subalgebra.smul_mem _ (Subalgebra.mul_mem _ hPmem hQmem) _)) k
  have hpk_eval : ∀ k θ, evalAt (pt θ) (pk k) = ((g θ : ℝ) : ℂ) ^ k := by
    intro k θ
    simp only [pk, g, map_pow, map_sub, map_one, map_smul, map_mul, smul_eq_mul]
    rw [hQ (pt θ) (hnorm θ), Complex.mul_conj']
    push_cast
    ring
  have hF : ∀ k θ, ‖evalAt (pt θ) (pk k)‖ ^ 2 = (g θ ^ k) ^ 2 := by
    intro k θ
    rw [hpk_eval, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg0 θ)]
  have hlim : Filter.Tendsto (fun k => ∫ θ, ‖evalAt (pt θ) (pk k)‖ ^ 2) Filter.atTop
      (nhds (∫ _θ : Fin n → UnitAddCircle, (0 : ℝ))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) (fun k => ?_) (integrable_const _)
      (fun k => Filter.Eventually.of_forall (fun θ => ?_)) ?_
    · exact ((hcont (pk k)).norm.pow 2).aestronglyMeasurable
    · rw [hF, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_one₀ (pow_nonneg (hg0 θ) _) (pow_le_one₀ (hg0 θ) (hg1 θ))
    · filter_upwards [hNull n Ψ hΨ] with θ hθ
      have hP0 : evalAt (pt θ) P ≠ 0 := by rw [hPΨ]; exact hθ
      have hlt : g θ < 1 := by
        simp only [g]
        have : 0 < c * ‖evalAt (pt θ) P‖ ^ 2 := by
          have := norm_pos_iff.mpr hP0
          positivity
        linarith
      simp only [hF]
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (hg0 θ) hlt).pow 2
      simpa using h
  rw [MeasureTheory.integral_zero] at hlim
  obtain ⟨k, hk⟩ := ((tendsto_order.1 hlim).2 δ hδ).exists
  refine ⟨pk k, hpk_mem k, fun z hz => ?_, hk.le⟩
  have hP0 : evalAt z P = 0 := by
    rw [hPprod]
    exact Finset.prod_eq_zero (Finset.mem_univ 1) (by simpa using hz)
  simp only [pk, map_pow, map_sub, map_one, map_smul, map_mul, hP0, zero_mul, smul_zero, sub_zero, one_pow]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.RFormula
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private lemma det_vand_comp {n : ℕ} (v : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) :
    (Matrix.vandermonde (v ∘ σ)).det =
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * (Matrix.vandermonde v).det := by
  have h : Matrix.vandermonde (v ∘ σ) = (Matrix.vandermonde v).submatrix σ id := by
    ext i j; simp [Matrix.vandermonde_apply]
  rw [h, Matrix.det_permute]

private lemma prod_prs {n : ℕ} (f : Fin n → Fin n → ℂ) :
    ∏ p ∈ prs n, f p.1 p.2 = ∏ i, ∏ j ∈ Finset.Ioi i, f i j := by
  rw [Finset.prod_filter, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_filter]
  refine Finset.prod_congr ?_ fun _ _ => rfl
  ext j; simp

private lemma det_rev {n : ℕ} (v : Fin n → ℂ) :
    (Matrix.vandermonde (v ∘ Fin.revPerm)).det = ∏ p ∈ prs n, (v p.1 - v p.2) := by
  rw [Matrix.det_vandermonde, ← prod_prs (fun i j => (v ∘ Fin.revPerm) j - (v ∘ Fin.revPerm) i)]
  refine Finset.prod_nbij' (fun p => (Fin.rev p.2, Fin.rev p.1))
    (fun p => (Fin.rev p.2, Fin.rev p.1)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simpa [Fin.rev_lt_rev] using hp
  · intro p hp
    simpa [Fin.rev_lt_rev] using hp
  · intro p _; simp
  · intro p _; simp
  · intro p _; simp

private lemma sign_sq_one {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign σ : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

private lemma prod_comp {n : ℕ} (v : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) :
    ∏ p ∈ prs n, (v (σ p.1) - v (σ p.2)) =
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ p ∈ prs n, (v p.1 - v p.2) := by
  have h1 := det_rev (v ∘ σ)
  have h2 := det_rev v
  rw [det_vand_comp] at h1 h2
  have h3 := det_vand_comp v σ
  simp only [Function.comp_apply] at h1
  rw [← h1, ← h2, h3]
  ring

private lemma evalAt_alternant {n : ℕ} (z : Fin n → ℂˣ) :
    evalAt z (alternant (staircase n)) = ∏ p ∈ prs n, ((z p.1 : ℂ) - (z p.2 : ℂ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [alternant_eq_det]
    exact (Finset.prod_of_isEmpty _).symm
  · have h := det_rev (fun i => (z i : ℂ))
    rw [det_vand_comp] at h
    rw [alternant_staircase_eq_vdm hn, map_mul, evalAt_vdm_det, ← h, mul_comm]
    simp

theorem UpperTheory.Gal.Gen.rFormula_pf :
    UpperTheory.Gal.Gen.RFormula := by
  intro n t l z hz
  have hD : ∏ p ∈ prs n, ((z p.1 : ℂ) - (z p.2 : ℂ)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun p hp h => ?_
    have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
    exact hlt.ne (hz (Units.ext (sub_eq_zero.mp h)))
  have key := congrArg (evalAt z) (alternant_mul_altQuot (monomial l * hlFactor n t))
  rw [map_mul, evalAt_antisymm, evalAt_alternant] at key
  refine mul_left_cancel₀ hD ?_
  have hR : hlR t l = altQuot (monomial l * hlFactor n t) := rfl
  rw [hR, key, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hs := sign_sq_one σ
  have hc : ∏ p ∈ prs n, ((z (σ p.1) : ℂ) - (z (σ p.2) : ℂ)) =
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ p ∈ prs n, ((z p.1 : ℂ) - (z p.2 : ℂ)) :=
    prod_comp (fun i => (z i : ℂ)) σ
  rw [map_mul, monomial, evalAt_single, one_mul, evalAt_hlFactor, Finset.prod_div_distrib, hc]
  simp only [Function.comp_apply]
  have hs0 : ((Equiv.Perm.sign σ : ℤ) : ℂ) ≠ 0 := left_ne_zero_of_mul_eq_one hs
  field_simp
  linear_combination ((monomialChar l (z ∘ σ)) * ∏ p ∈ prs n, ((z (σ p.1) : ℂ) - t * (z (σ p.2) : ℂ))) * hs
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.HalfInt
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private lemma pt_shift {n : ℕ} (c : ℤ) (s : UnitAddCircle) (θ : Fin n → UnitAddCircle) :
    pt ((fun i : Fin n => (c - ((i : ℕ) : ℤ)) • s) + θ) =
      fun i : Fin n => Circle.toUnits (AddCircle.toCircle s) ^ (c - ((i : ℕ) : ℤ)) * pt θ i := by
  funext i
  simp only [pt, Pi.add_apply, AddCircle.toCircle_add, AddCircle.toCircle_zsmul, map_mul, map_zpow]

private lemma prod_zpow_sum {ι : Type*} (S : Finset ι) (u : ℂˣ) (f : ι → ℤ) :
    ∏ i ∈ S, u ^ f i = u ^ ∑ i ∈ S, f i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

private lemma monoChar_shift {n : ℕ} (l : Fin n → ℤ) (c : ℤ) (m : ℕ)
    (hm : ∑ i : Fin n, l i * (c - ((i : ℕ) : ℤ)) = m) (u : ℂˣ) :
    monomialChar l (fun i : Fin n => u ^ (c - ((i : ℕ) : ℤ))) = (u : ℂ) ^ m := by
  rw [monomialChar_apply, ← Units.coe_prod]
  have h : ∏ i : Fin n, (u ^ (c - ((i : ℕ) : ℤ))) ^ l i = u ^ (m : ℤ) := by
    rw [← hm, ← prod_zpow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_mul, mul_comm]
  rw [h, zpow_natCast, Units.val_pow_eq_pow_val]

private lemma key {n : ℕ} (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) (hM : MeanVal) (hD : DensCont)
    (l : Fin n → ℤ) (c : ℤ) (m : ℕ) (hcm : ∑ i : Fin n, l i * (c - ((i : ℕ) : ℤ)) = m) :
    ∫ θ : Fin n → UnitAddCircle, monomialChar l (pt θ) * half (t : ℂ) (pt θ) =
      ∫ θ : Fin n → UnitAddCircle, monomialChar l (pt θ) * (if m = 0 then 1 else 0) := by
  haveI : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  obtain ⟨hhalf, -, hev, hnorm⟩ := hD n t ht0 ht1
  have hmono : Continuous fun θ : Fin n → UnitAddCircle => monomialChar l (pt θ) := by
    have h := hev (AddMonoidAlgebra.single l 1)
    simpa [evalAt_single] using h
  set F : (Fin n → UnitAddCircle) → ℂ := fun θ => monomialChar l (pt θ) * half (t : ℂ) (pt θ) with hF
  have hFc : Continuous F := hmono.mul hhalf
  let a : UnitAddCircle → Fin n → UnitAddCircle := fun s i => (c - ((i : ℕ) : ℤ)) • s
  have ha : Continuous a := continuous_pi fun i => continuous_zsmul _
  have hshift : ∀ s, ∫ θ, F (a s + θ) = ∫ θ, F θ := fun s => integral_add_left_eq_self F (a s)
  have hG : Continuous (Function.uncurry fun (s : UnitAddCircle) (θ : Fin n → UnitAddCircle) => F (a s + θ)) :=
    hFc.comp ((ha.comp continuous_fst).add continuous_snd)
  have hint : Integrable (Function.uncurry fun (s : UnitAddCircle) (θ : Fin n → UnitAddCircle) => F (a s + θ))
      ((volume : Measure UnitAddCircle).prod (volume : Measure (Fin n → UnitAddCircle))) :=
    hG.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h1 : ∫ θ, F θ = ∫ s : UnitAddCircle, ∫ θ, F (a s + θ) := by
    simp only [hshift, integral_const, probReal_univ, one_smul]
  rw [h1, integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  dsimp only
  have hpt : ∀ s, pt (a s + θ) = (fun i : Fin n => Circle.toUnits (AddCircle.toCircle s) ^ (c - ((i : ℕ) : ℤ))) * pt θ := by
    intro s
    rw [pt_shift]
    rfl
  simp only [hF, hpt, map_mul, monoChar_shift l c m hcm]
  have hz := hM n t ht0 ht1 (pt θ) (hnorm θ) c m
  have hcoe : ∀ s : UnitAddCircle, ((Circle.toUnits (AddCircle.toCircle s) : ℂˣ) : ℂ) = (AddCircle.toCircle s : ℂ) :=
    fun s => rfl
  calc _ = ∫ s : UnitAddCircle, monomialChar l (pt θ) * ((AddCircle.toCircle s : ℂ) ^ m *
        half (t : ℂ) (fun i => Circle.toUnits (AddCircle.toCircle s) ^ (c - ((i : ℕ) : ℤ)) * pt θ i)) := by
        congr 1
        funext s
        rw [hcoe, mul_comm (_ ^ m), mul_assoc]
        rfl
    _ = _ := by rw [integral_const_mul, hz]

theorem UpperTheory.Gal.Gen.halfInt_pf :
    UpperTheory.Gal.Gen.WtPos → UpperTheory.Gal.Gen.MeanVal → UpperTheory.Gal.Gen.DensCont → UpperTheory.Gal.Gen.HalfInt := by
  intro hW hM hD n t ht0 ht1 l hl
  haveI : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  by_cases h0 : l = 0
  · subst h0
    rw [key t ht0 ht1 hM hD (0 : Fin n → ℤ) 0 0 (by simp)]
    simp [monomialChar_zero]
  · obtain ⟨c, hc⟩ := hW n l hl h0
    have hm : ∑ i : Fin n, l i * (c - ((i : ℕ) : ℤ)) = ((∑ i : Fin n, l i * (c - ((i : ℕ) : ℤ))).toNat : ℤ) :=
      (Int.toNat_of_nonneg hc.le).symm
    rw [key t ht0 ht1 hM hD l c _ hm]
    have hne : (∑ i : Fin n, l i * (c - ((i : ℕ) : ℤ))).toNat ≠ 0 := by omega
    simp [hne, h0]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.MeanVal
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private lemma circle_mean (g : ℂ → ℂ)
    (hd : ∀ u ∈ Metric.closedBall (0 : ℂ) 1, DifferentiableAt ℂ g u) :
    ∫ s : UnitAddCircle, g ((AddCircle.toCircle s : Circle) : ℂ) = g 0 := by
  have hc : ContinuousOn g (Metric.closedBall (0 : ℂ) |1|) := by
    intro u hu
    exact (hd u (by simpa using hu)).continuousAt.continuousWithinAt
  have hmv : Real.circleAverage g 0 1 = g 0 :=
    circleAverage_of_differentiable_on_off_countable (s := ∅) Set.countable_empty hc
      (fun u hu => hd u (by
        have := hu.1
        simp only [abs_one, Metric.mem_ball] at this
        simpa using this.le))
  have hpi : (2 * Real.pi) ≠ 0 := Real.two_pi_pos.ne'
  have e : ∀ a : ℝ, ((AddCircle.toCircle (a : UnitAddCircle) : Circle) : ℂ)
      = circleMap 0 1 (2 * Real.pi * a) := by
    intro a
    rw [AddCircle.toCircle_apply_mk, Circle.coe_exp, circleMap]
    simp only [zero_add, Complex.ofReal_one, one_mul]
    congr 1
    push_cast
    ring
  rw [← UnitAddCircle.intervalIntegral_preimage 0, ← hmv, Real.circleAverage_def]
  simp_rw [e]
  rw [intervalIntegral.integral_comp_mul_left (fun θ => g (circleMap 0 1 θ)) hpi]
  simp

private lemma ratio_eq (u : ℂ) (hu : u ≠ 0) (c : ℤ) (i j : ℕ) (hij : i < j) (a b : ℂ) :
    (u ^ (c - (i : ℤ)) * a) / (u ^ (c - (j : ℤ)) * b) = u ^ (j - i) * (a / b) := by
  have h : u ^ (c - (i : ℤ)) / u ^ (c - (j : ℤ)) = u ^ (j - i) := by
    rw [← zpow_sub₀ hu, ← zpow_natCast, Nat.cast_sub hij.le]
    congr 1
    ring
  rw [mul_div_mul_comm, h]

theorem UpperTheory.Gal.Gen.meanVal_pf :
    UpperTheory.Gal.Gen.MeanVal := by
  intro n t ht0 ht1 z hz c m
  set g : ℂ → ℂ := fun u => u ^ m * ∏ p ∈ prs n,
    (1 - u ^ ((p.2 : ℕ) - (p.1 : ℕ)) * ((z p.1 : ℂ) / (z p.2 : ℂ))) /
      (1 - (t : ℂ) * (u ^ ((p.2 : ℕ) - (p.1 : ℕ)) * ((z p.1 : ℂ) / (z p.2 : ℂ)))) with hg
  have hden : ∀ u ∈ Metric.closedBall (0 : ℂ) 1, ∀ p : Fin n × Fin n,
      1 - (t : ℂ) * (u ^ ((p.2 : ℕ) - (p.1 : ℕ)) * ((z p.1 : ℂ) / (z p.2 : ℂ))) ≠ 0 := by
    intro u hu p h0
    have hu1 : ‖u‖ ≤ 1 := by simpa using hu
    have hx : (t : ℂ) * (u ^ ((p.2 : ℕ) - (p.1 : ℕ)) * ((z p.1 : ℂ) / (z p.2 : ℂ))) = 1 :=
      (sub_eq_zero.mp h0).symm
    have hn := congrArg norm hx
    rw [norm_mul, norm_mul, norm_div, hz, hz, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht0,
      norm_one, div_one, mul_one] at hn
    have : ‖u‖ ^ ((p.2 : ℕ) - (p.1 : ℕ)) ≤ 1 := pow_le_one₀ (norm_nonneg _) hu1
    nlinarith
  have hd : ∀ u ∈ Metric.closedBall (0 : ℂ) 1, DifferentiableAt ℂ g u := by
    intro u hu
    refine (differentiableAt_id.pow m).mul ?_
    refine DifferentiableAt.fun_finsetProd fun p _ => ?_
    refine DifferentiableAt.div ?_ ?_ (hden u hu p)
    · exact (differentiableAt_const _).sub ((differentiableAt_id.pow _).mul (differentiableAt_const _))
    · exact (differentiableAt_const _).sub
        ((differentiableAt_const _).mul ((differentiableAt_id.pow _).mul (differentiableAt_const _)))
  have h0 : g 0 = if m = 0 then 1 else 0 := by
    have hp : ∏ p ∈ prs n, (1 - (0 : ℂ) ^ ((p.2 : ℕ) - (p.1 : ℕ)) * ((z p.1 : ℂ) / (z p.2 : ℂ))) /
        (1 - (t : ℂ) * ((0 : ℂ) ^ ((p.2 : ℕ) - (p.1 : ℕ)) * ((z p.1 : ℂ) / (z p.2 : ℂ)))) = 1 := by
      refine Finset.prod_eq_one fun p hp => ?_
      have hlt : (p.1 : ℕ) < (p.2 : ℕ) := (Finset.mem_filter.mp hp).2
      have hk : (p.2 : ℕ) - (p.1 : ℕ) ≠ 0 := by omega
      simp [zero_pow hk]
    simp only [hg, hp, mul_one]
    split_ifs with hm
    · simp [hm]
    · exact zero_pow hm
  have hs : ∀ s : UnitAddCircle, ((AddCircle.toCircle s : Circle) : ℂ) ^ m *
      half (t : ℂ) (fun i => Circle.toUnits (AddCircle.toCircle s) ^ (c - (i : ℕ)) * z i)
      = g ((AddCircle.toCircle s : Circle) : ℂ) := by
    intro s
    simp only [hg, half]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    have hlt : (p.1 : ℕ) < (p.2 : ℕ) := (Finset.mem_filter.mp hp).2
    have hu : ((AddCircle.toCircle s : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have key := ratio_eq _ hu c p.1 p.2 hlt (z p.1 : ℂ) (z p.2 : ℂ)
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Circle.toUnits_apply, Units.val_mk0]
    rw [key]
  simp_rw [hs]
  rw [circle_mean g hd, h0]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.WtPosTermPos
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private lemma wtPos_expand (n : ℕ) (l : Fin n → ℤ) :
    ∑ i : Fin n, ∑ j : Fin n, (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * (l j - l i) =
      2 * (∑ i : Fin n, ((i : ℕ) : ℤ)) * (∑ i, l i) - 2 * n * ∑ i : Fin n, l i * ((i : ℕ) : ℤ) := by
  have h : ∀ i : Fin n, ∑ j : Fin n, (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * (l j - l i) =
      ((i : ℕ) : ℤ) * (∑ j, l j) - n * (l i * ((i : ℕ) : ℤ)) - (∑ j : Fin n, l j * ((j : ℕ) : ℤ))
        + (∑ j : Fin n, ((j : ℕ) : ℤ)) * l i := by
    intro i
    have e : ∀ j : Fin n, (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * (l j - l i) =
        ((i : ℕ) : ℤ) * l j - l i * ((i : ℕ) : ℤ) - l j * ((j : ℕ) : ℤ) + ((j : ℕ) : ℤ) * l i := by
      intro j; ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private lemma wtPos_term {n : ℕ} {l : Fin n → ℤ} (hl : Antitone l) (i j : Fin n) :
    0 ≤ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * (l j - l i) := by
  rcases le_total i j with h | h
  · have h1 : ((i : ℕ) : ℤ) ≤ ((j : ℕ) : ℤ) := by exact_mod_cast h
    have h2 := hl h
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  · have h1 : ((j : ℕ) : ℤ) ≤ ((i : ℕ) : ℤ) := by exact_mod_cast h
    have h2 := hl h
    exact mul_nonneg (by linarith) (by linarith)

private lemma wtPos_term_pos {n : ℕ} {l : Fin n → ℤ} (hl : Antitone l) {i j : Fin n} (hij : l i ≠ l j) :
    0 < (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * (l j - l i) := by
  have hne : i ≠ j := fun h => hij (by rw [h])
  rcases lt_or_gt_of_ne hne with h | h
  · have h1 : ((i : ℕ) : ℤ) < ((j : ℕ) : ℤ) := by exact_mod_cast h
    have h2 : l j < l i := lt_of_le_of_ne (hl h.le) (Ne.symm hij)
    exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
  · have h1 : ((j : ℕ) : ℤ) < ((i : ℕ) : ℤ) := by exact_mod_cast h
    have h2 : l i < l j := lt_of_le_of_ne (hl h.le) hij
    exact mul_pos (by linarith) (by linarith)

private lemma wtPos_sum (n : ℕ) (l : Fin n → ℤ) (c : ℤ) :
    ∑ i, l i * (c - ((i : ℕ) : ℤ)) = c * (∑ i, l i) - ∑ i : Fin n, l i * ((i : ℕ) : ℤ) := by
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, mul_comm]

theorem UpperTheory.Gal.Gen.wtPos_pf :
    UpperTheory.Gal.Gen.WtPos := by
  intro n l hl hl0
  set S : ℤ := ∑ i, l i with hS
  set T : ℤ := ∑ i : Fin n, l i * ((i : ℕ) : ℤ) with hT
  rcases lt_trichotomy S 0 with h | h | h
  · refine ⟨-(|T| + 1), ?_⟩
    rw [wtPos_sum, ← hS, ← hT]
    have h1 : T ≤ |T| := le_abs_self T
    have h2 : 0 ≤ |T| := abs_nonneg T
    nlinarith
  ·
    obtain ⟨a, ha⟩ : ∃ a, l a ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hl0 (funext hc)
    obtain ⟨b, hb⟩ : ∃ b, l a ≠ l b := by
      by_contra hc
      push_neg at hc
      have hs : S = n * l a := by
        rw [hS, Finset.sum_congr rfl (fun i _ => (hc i).symm)]
        simp
      rw [h] at hs
      have hn : (n : ℤ) ≠ 0 := by
        have : 0 < n := Fin.pos a
        exact_mod_cast this.ne'
      exact ha ((mul_eq_zero.mp hs.symm).resolve_left hn)
    have hpos : 0 < ∑ i : Fin n, ∑ j : Fin n, (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * (l j - l i) := by
      refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ => wtPos_term hl i j) ⟨a, Finset.mem_univ a, ?_⟩
      exact Finset.sum_pos' (fun j _ => wtPos_term hl a j) ⟨b, Finset.mem_univ b, wtPos_term_pos hl hb⟩
    rw [wtPos_expand, ← hS, ← hT, h] at hpos
    have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
    have hT0 : T < 0 := by
      by_contra hc
      push_neg at hc
      nlinarith [mul_nonneg hn hc]
    refine ⟨0, ?_⟩
    rw [wtPos_sum, ← hS, ← hT]
    linarith
  · refine ⟨|T| + 1, ?_⟩
    rw [wtPos_sum, ← hS, ← hT]
    have h1 : T ≤ |T| := le_abs_self T
    have h2 : 0 ≤ |T| := abs_nonneg T
    nlinarith
end
