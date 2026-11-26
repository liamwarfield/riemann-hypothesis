module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.DcoShape
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

open scoped Pointwise

private theorem conj_mem {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
    (a : Fin n → ℤ) {g : GL (Fin n) F} (hg : g ∈ iwahori F n)
    (h : ∀ i j, a i < a j → (g : Matrix (Fin n) (Fin n) F) i j = 0) :
    torusPow F n a * g * (torusPow F n a)⁻¹ ∈ iwahori F n := by
  have he : ∀ i j, ((torusPow F n a * g * (torusPow F n a)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      (uniformizer F : F) ^ (a i - a j) * (g : Matrix (Fin n) (Fin n) F) i j := by
    intro i j
    rw [← torusPow_neg, Units.val_mul, Units.val_mul, coe_torusPow, coe_torusPow, Matrix.mul_diagonal,
      Matrix.diagonal_mul, sub_eq_add_neg, zpow_add₀ (GLnLocal.uniformizer_ne_zero F), Pi.neg_apply]
    ring
  have hle : ∀ i j, ValuativeRel.valuation F
      (((torusPow F n a * g * (torusPow F n a)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j) ≤
      ValuativeRel.valuation F ((g : Matrix (Fin n) (Fin n) F) i j) := by
    intro i j
    rw [he]
    rcases lt_or_ge (a i) (a j) with hij | hij
    · rw [h i j hij, mul_zero]
    · obtain ⟨d, hd⟩ : ∃ d : ℕ, a i - a j = d := ⟨(a i - a j).toNat, by omega⟩
      rw [hd, zpow_natCast, map_mul, map_pow]
      exact mul_le_of_le_one_left' (pow_le_one' (valuation_uniformizer_lt_one F).le d)
  obtain ⟨h1, h2, h3⟩ := (mem_iwahori_iff F n).1 hg
  refine (mem_iwahori_iff F n).2 ⟨fun i j => (hle i j).trans (h1 i j),
    fun i j hij => (hle i j).trans_lt (h2 i j hij), fun i => ?_⟩
  rw [he, sub_self, zpow_zero, one_mul, h3]

private theorem fact {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
    {k : GL (Fin n) F} (hk : k ∈ iwahori F n) :
    ∃ u ∈ unipotent F n, u ∈ iwahori F n ∧ ∃ w, k = u * w ∧
      ∀ b : Fin n → ℤ, Antitone b → (torusPow F n b)⁻¹ * w * torusPow F n b ∈ iwahori F n := by
  obtain ⟨x, hx, y, hy, z, hz, rfl⟩ :=
    Parabolic.iwahori_iwahoriFactorization' (β := (id : Fin n → Fin n)) monotone_id k hk
  have hx' := Parabolic.mem_unipotentRadical.1 hx.2
  refine ⟨x, (mem_unipotent F n).2 ⟨hx'.1, fun i => by simpa using hx'.2 i i rfl⟩, hx.1, y * z, mul_assoc _ _ _,
    fun b hb => ?_⟩
  have h1 := conj_mem (-b) hz.1 fun i j hij =>
    (Parabolic.mem_oppositeUnipotentRadical.1 hz.2).1 i j
      (lt_of_not_ge fun h => (hb h).not_gt (neg_lt_neg_iff.1 hij))
  have h2 := conj_mem (-b) hy.1 fun i j hij =>
    Parabolic.mem_levi.1 hy.2 i j (fun h => by
      have h' : i = j := h
      subst h'; exact lt_irrefl _ hij)
  rw [torusPow_neg, inv_inv] at h1 h2
  have := mul_mem h2 h1
  simpa [mul_assoc] using this

theorem UpperTheory.ConvolutionTheory.H.dcoShape :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (a : Fin n → ℤ), Antitone a →
      (∀ g, g ∈ dco F a ↔ ∃ u ∈ unipotent F n ⊓ integralGL F n, ∃ y ∈ iwahori F n, g = u * torusPow F n a * y) ∧
      (∀ b, Antitone b → ∀ g ∈ dco F a, ∀ g' ∈ dco F b, g * g' ∈ dco F (a + b)) ∧
      uFn F a ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ ∧ BiI F (uFn F a) := by
  intro F _ _ _ _ n a ha
  have hbi : ∀ g, ∀ y ∈ iwahori F n, (y * g ∈ dco F a ↔ g ∈ dco F a) ∧ (g * y ∈ dco F a ↔ g ∈ dco F a) := by
    have hl : ∀ g, ∀ y ∈ iwahori F n, g ∈ dco F a → y * g ∈ dco F a := by
      rintro g y hy ⟨x, hx, x', hx', rfl⟩
      exact ⟨y * x, mul_mem hy hx, x', hx', by group⟩
    have hr : ∀ g, ∀ y ∈ iwahori F n, g ∈ dco F a → g * y ∈ dco F a := by
      rintro g y hy ⟨x, hx, x', hx', rfl⟩
      exact ⟨x, hx, x' * y, mul_mem hx' hy, by group⟩
    intro g y hy
    exact ⟨⟨fun h => by simpa using hl _ _ (inv_mem hy) h, hl g y hy⟩,
      ⟨fun h => by simpa using hr _ _ (inv_mem hy) h, hr g y hy⟩⟩
  refine ⟨fun g => ⟨?_, ?_⟩, ?_, ?_, fun g y hy => ⟨?_, ?_⟩⟩
  · rintro ⟨k, hk, y, hy, rfl⟩
    obtain ⟨u, hu, huI, w, rfl, hw⟩ := fact hk
    exact ⟨u, ⟨hu, iwahori_le_integralGL F n huI⟩, _, mul_mem (hw a ha) hy, by group⟩
  · rintro ⟨u, ⟨hu, hu'⟩, y, hy, rfl⟩
    refine ⟨u, ?_, y, hy, rfl⟩
    obtain ⟨h1, h2⟩ := (mem_unipotent F n).1 hu
    refine (mem_iwahori_iff F n).2 ⟨fun i j => ((mem_integralGL_iff F n).1 hu').1 i j, fun i j hij => ?_, fun i => ?_⟩
    · rw [h1 hij, map_zero]; exact zero_lt_one
    · rw [h2, map_one]
  · rintro b hb g ⟨x, hx, y, hy, rfl⟩ g' ⟨x', hx', y', hy', rfl⟩
    obtain ⟨u, hu, huI, w, e, hw⟩ := fact (mul_mem hy hx')
    have h1 := conj_mem a huI fun i j hij =>
      ((mem_unipotent F n).1 hu).1 (lt_of_not_ge fun h => (ha h).not_gt hij)
    refine ⟨_, mul_mem hx h1, _, mul_mem (hw b hb) hy', ?_⟩
    rw [torusPow_add]
    calc x * torusPow F n a * y * (x' * torusPow F n b * y')
        = x * torusPow F n a * (y * x') * torusPow F n b * y' := by group
      _ = _ := by rw [e]; group
  · have e : dco F a = (iwahori F n : Set (GL (Fin n) F)) * {torusPow F n a} * (iwahori F n : Set (GL (Fin n) F)) := by
      ext g
      constructor
      · rintro ⟨x, hx, y, hy, rfl⟩
        exact Set.mul_mem_mul (Set.mul_mem_mul hx rfl) hy
      · rintro ⟨_, ⟨x, hx, _, rfl, rfl⟩, y, hy, rfl⟩
        exact ⟨x, hx, y, hy, rfl⟩
    refine indicator_mem_locallyConstantCompactSupport (R := ℂ) (U := dco F a) ?_ ?_ (1 : ℂ)
    · rw [e]; exact ((isCompact_iwahori F n).mul isCompact_singleton).mul (isCompact_iwahori F n)
    · rw [e]; exact (isOpen_iwahori F n).mul_left
  · by_cases h : g ∈ dco F a
    · simp [uFn, h, (hbi g y hy).1]
    · simp [uFn, h, (hbi g y hy).1]
  · by_cases h : g ∈ dco F a
    · simp [uFn, h, (hbi g y hy).2]
    · simp [uFn, h, (hbi g y hy).2]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.GapDom
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

private theorem mem_supp_monomial {n : ℕ} {a b : Fin n → ℤ}
    (h : a ∈ (monomial b : LaurentRing n).coeff.support) : a = b := by
  rw [AddMonoidAlgebra.coeff_single] at h
  simpa using Finsupp.support_single_subset h

private theorem card_touch_le {n : ℕ} (T : Finset (Fin n × Fin n)) (hT : T ⊆ pairs n) (j : Fin n) :
    (T.filter fun p => p.1 = j ∨ p.2 = j).card ≤ n := by
  have := Finset.card_le_card_of_injOn (s := T.filter fun p => p.1 = j ∨ p.2 = j) (t := Finset.univ)
    (fun p : Fin n × Fin n => if p.1 = j then p.2 else p.1) (fun _ _ => by simp) (by
      rintro ⟨a, b⟩ hp ⟨c, d⟩ hq h
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp hq
      have h1 : a < b := by simpa [pairs] using hT hp.1
      have h2 : c < d := by simpa [pairs] using hT hq.1
      have h3 := hp.2
      have h4 := hq.2
      simp only at h h3 h4
      simp only [Prod.mk.injEq]
      split_ifs at h <;> omega)
  simpa using this

private def Bd {n : ℕ} (T : Finset (Fin n × Fin n)) (e : Fin n → ℤ) : Prop :=
  ∀ j, 0 ≤ e j ∧ e j ≤ ((T.filter fun p => p.1 = j ∨ p.2 = j).card : ℤ)

private theorem bd_insert {n : ℕ} {T : Finset (Fin n × Fin n)} {p : Fin n × Fin n} (hp : p ∉ T)
    {e : Fin n → ℤ} (he : Bd T e) {k : Fin n} (hk : k = p.1 ∨ k = p.2) :
    Bd (insert p T) (Pi.single k 1 + e) := by
  intro j
  obtain ⟨h0, h1⟩ := he j
  rw [Finset.filter_insert]
  by_cases hj : j = k
  · subst hj
    rw [if_pos (by tauto), Finset.card_insert_of_notMem (by simp [hp])]
    simp only [Pi.add_apply, Pi.single_eq_same]
    push_cast
    omega
  · simp only [Pi.add_apply, Pi.single_eq_of_ne hj]
    split_ifs
    · rw [Finset.card_insert_of_notMem (by simp [hp])]
      push_cast
      omega
    · omega

private theorem bd_sum {n : ℕ} (f : Fin n × Fin n → Fin n) (hf : ∀ p, f p = p.1 ∨ f p = p.2)
    (T : Finset (Fin n × Fin n)) : Bd T (∑ p ∈ T, Pi.single (f p) 1) := by
  induction T using Finset.induction_on with
  | empty => intro j; simp
  | insert p T hp ih => rw [Finset.sum_insert hp]; exact bd_insert hp ih (hf p)

private theorem bd_prod {n : ℕ} (t : ℂ) (T : Finset (Fin n × Fin n)) :
    ∀ a ∈ (∏ p ∈ T, (varL p.1 - t • varL p.2) : LaurentRing n).coeff.support, Bd T a := by
  induction T using Finset.induction_on with
  | empty =>
    intro a ha
    rw [Finset.prod_empty] at ha
    have : a = 0 := mem_supp_monomial (b := 0) ha
    subst this
    intro j; simp
  | insert p T hp ih =>
    intro a ha
    rw [Finset.prod_insert hp] at ha
    obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_add.1 (AddMonoidAlgebra.support_coeff_mul_subset _ _ ha)
    rw [AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_smul] at hb
    rcases Finset.mem_union.1 (Finsupp.support_sub hb) with hb | hb
    · rw [mem_supp_monomial hb]; exact bd_insert hp (ih c hc) (Or.inl rfl)
    · rw [mem_supp_monomial (Finsupp.support_smul hb)]; exact bd_insert hp (ih c hc) (Or.inr rfl)

private theorem anti_of_bd {n : ℕ} {ν e : Fin n → ℤ} (hν : Gap n ν) {T : Finset (Fin n × Fin n)}
    (hT : T ⊆ pairs n) (he : Bd T e) : Antitone (ν + e) := by
  intro i j hij
  rcases hij.eq_or_lt with rfl | hij
  · exact le_rfl
  · have h1 := hν i j hij
    have h2 := (he i).1
    have h3 := (he j).2
    have h4 := card_touch_le T hT j
    simp only [Pi.add_apply]
    omega

theorem UpperTheory.ConvolutionTheory.H.gapDom :
    ∀ (n : ℕ) (ν : Fin n → ℤ), Gap n ν → (∀ S ∈ (pairs n).powerset, Antitone (ν + eL S) ∧ Antitone (ν + eR S)) ∧
      (∀ t : ℂ, Dom (monomial ν * dPol n t)) ∧ ∀ a, Antitone a → Gap n (a + ν) := by
  intro n ν hν
  refine ⟨fun S hS => ⟨?_, ?_⟩, fun t a ha => ?_, fun a ha i j hij => ?_⟩
  · exact anti_of_bd hν (Finset.mem_powerset.1 hS) (bd_sum Prod.fst (fun _ => Or.inl rfl) S)
  · exact anti_of_bd hν Finset.sdiff_subset (bd_sum Prod.snd (fun _ => Or.inr rfl) _)
  · obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_add.1 (AddMonoidAlgebra.support_coeff_mul_subset _ _ ha)
    rw [mem_supp_monomial hb]
    exact anti_of_bd hν subset_rfl (bd_prod t _ c hc)
  · have h1 := hν i j hij
    have h2 := ha hij.le
    simp only [Pi.add_apply]
    omega
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.VandSum
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

private theorem vs_single {n : ℕ} (i : Fin n) (w : Fin n → ℂˣ) : monomialChar (Pi.single i 1 : Fin n → ℤ) w = w i := by
  rw [monomialChar_apply, Finset.prod_eq_single i] <;> simp +contextual [Pi.single_apply]

theorem UpperTheory.ConvolutionTheory.H.vandSum :
    ∀ (n : ℕ) (z : Fin n → ℂˣ) (σ τ : Equiv.Perm (Fin n)),
      ∑ S ∈ (pairs n).powerset, sgS S * (monomialChar (eL S) (z ∘ σ) * monomialChar (eR S) (z ∘ τ)) =
        if σ = τ then evalAt (z ∘ σ) (dPol n 1) else 0 := by
  intro n z σ τ
  have hL : ∀ (s : Finset (Fin n × Fin n)) (f : Fin n × Fin n → Fin n) (w : Fin n → ℂˣ),
      monomialChar (∑ p ∈ s, (Pi.single (f p) 1 : Fin n → ℤ)) w = ∏ p ∈ s, (w (f p) : ℂ) := by
    intro s f w
    classical
    induction s using Finset.induction_on with
    | empty => simp [monomialChar_zero]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, monomialChar_add, ih, vs_single]
  have h1 : ∑ S ∈ (pairs n).powerset, sgS S * (monomialChar (eL S) (z ∘ σ) * monomialChar (eR S) (z ∘ τ)) =
      ∏ p ∈ pairs n, ((z (σ p.1) : ℂ) - z (τ p.2)) := by
    simp only [sub_eq_add_neg]
    rw [Finset.prod_add]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [eL, eR, hL S Prod.fst, hL _ Prod.snd, sgS, Finset.prod_neg]
    simp only [Function.comp]
    ring
  rw [h1]
  split_ifs with h
  · subst h
    rw [dPol, map_prod]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [map_sub, one_smul, evalAt_single, evalAt_single, vs_single, vs_single]
    simp
  · by_contra hne
    apply h
    have hge : ∀ j, j ≤ (σ⁻¹ * τ) j := fun j => by
      by_contra hlt
      refine hne (Finset.prod_eq_zero (i := ((σ⁻¹ * τ) j, j)) (by simpa [pairs] using hlt) ?_)
      simp
    have hs : ∑ j : Fin n, (j : ℕ) = ∑ j : Fin n, (((σ⁻¹ * τ) j : Fin n) : ℕ) := (Equiv.sum_comp (σ⁻¹ * τ) fun j : Fin n => (j : ℕ)).symm
    have he := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) fun (j : Fin n) _ => Fin.le_def.1 (hge j)).1 hs
    have : σ⁻¹ * τ = 1 := Equiv.ext fun j => (Fin.ext (he j (Finset.mem_univ _))).symm
    exact inv_mul_eq_one.1 this
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.HlEval
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

private theorem he_single {n : ℕ} (i : Fin n) (m : ℤ) (w : Fin n → ℂˣ) : monomialChar (Pi.single i m : Fin n → ℤ) w = (w i : ℂ) ^ m := by
  rw [monomialChar_apply, Finset.prod_eq_single i] <;> simp +contextual [Pi.single_apply]

private theorem he_d {n : ℕ} (w : Fin n → ℂˣ) : evalAt w (dPol n 1) = ∏ p ∈ pairs n, ((w p.1 : ℂ) - w p.2) := by
  rw [dPol, map_prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [map_sub, one_smul, evalAt_single, evalAt_single, he_single, he_single]
  simp

private theorem he_det {n : ℕ} (w : Fin n → ℂˣ) :
    evalAt w (dPol n 1) = (Matrix.projVandermonde (fun _ => (1 : ℂ)) fun i => (w i : ℂ)).det := by
  rw [he_d, Matrix.det_projVandermonde, Finset.prod_sigma', pairs]
  refine Finset.prod_nbij' (fun p => ⟨p.1, p.2⟩) (fun p => (p.1, p.2)) ?_ ?_ ?_ ?_ ?_ <;> simp

private theorem he_alt {n : ℕ} (w : Fin n → ℂˣ) : evalAt w (alternant (staircase n)) = evalAt w (dPol n 1) := by
  rw [he_det, alternant_eq_det, AlgHom.map_det]
  congr 1
  ext a b
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, monomial, evalAt_single, he_single, one_mul,
    Matrix.projVandermonde_apply, one_pow]
  rw [← zpow_natCast]
  congr 1
  have := b.2
  simp only [staircase, Fin.val_rev]
  omega

private theorem he_sgn {n : ℕ} (w : Fin n → ℂˣ) (σ : Equiv.Perm (Fin n)) :
    evalAt (w ∘ σ) (dPol n 1) = ((Equiv.Perm.sign σ : ℤ) : ℂ) * evalAt w (dPol n 1) := by
  rw [he_det, he_det, ← Matrix.det_permute]
  rfl

theorem UpperTheory.ConvolutionTheory.H.hlEval :
    ∀ (n : ℕ) (t : ℂ) (z : Fin n → ℂˣ), Function.Injective z → ∀ a : Fin n → ℤ,
      (∀ σ : Equiv.Perm (Fin n), evalAt (z ∘ σ) (dPol n 1) ≠ 0) ∧
      evalAt z (hlR t a) = ∑ σ : Equiv.Perm (Fin n), evalAt (z ∘ σ) (dPol n t) / evalAt (z ∘ σ) (dPol n 1) * monomialChar a (z ∘ σ) := by
  intro n t z hz a
  have hne : ∀ σ : Equiv.Perm (Fin n), evalAt (z ∘ σ) (dPol n 1) ≠ 0 := fun σ => by
    rw [he_d]
    refine Finset.prod_ne_zero_iff.2 fun p hp => sub_ne_zero.2 fun h => ?_
    have h1 : p.1 < p.2 := by simpa [pairs] using hp
    exact h1.ne (σ.injective (hz (Units.ext h)))
  refine ⟨hne, ?_⟩
  have h1 := congrArg (evalAt z) (alternant_mul_altQuot (monomial a * hlFactor n t))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, he_alt, antisymm_apply, map_sum] at h1
  have h0 : evalAt z (dPol n 1) ≠ 0 := hne 1
  refine mul_left_cancel₀ h0 (h1.trans ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h2 := he_sgn z σ
  have h3 := hne σ
  rw [Units.smul_def, map_zsmul, evalAt_permAct, map_mul, monomial, evalAt_single, one_mul, zsmul_eq_mul]
  have h4 : ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign σ : ℤ) : ℂ) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have h5 : evalAt z (dPol n 1) = ((Equiv.Perm.sign σ : ℤ) : ℂ) * evalAt (z ∘ σ) (dPol n 1) := by
    rw [h2, ← mul_assoc, h4, one_mul]
  rw [h5]
  change _ * (_ * evalAt (z ∘ σ) (dPol n t)) = _
  field_simp
end
