module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.AdRepBaseLiftApply

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.AlgCyc
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Sd

section Hecke

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

private theorem isAlgPos_mul {χ χ' : HChar F} {n n' : (F →+* ℂ) → ℤ} (h : IsAlgPos χ n) (h' : IsAlgPos χ' n') :
    IsAlgPos (χ * χ') (n + n') := fun k hk => by
  have e : (χ * χ').inf k = χ.inf k * χ'.inf k := rfl
  rw [e, Units.val_mul, h k hk, h' k hk, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_add₀ ((map_ne_zero φ).2 k.ne_zero) _ _).symm

private theorem isAlgPos_inv {χ : HChar F} {n : (F →+* ℂ) → ℤ} (h : IsAlgPos χ n) : IsAlgPos χ⁻¹ (-n) := fun k hk => by
  have e : (χ⁻¹).inf k = (χ.inf k)⁻¹ := rfl
  rw [e, Units.val_inv_eq_inv_val, h k hk, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_neg _ _).symm

private theorem alg_mul {ι : Qbar l ≃+* ℂ} {κ κ' : G F Ω →* (Qbar l)ˣ} (h : IsAlgChar ι κ) (h' : IsAlgChar ι κ') :
    IsAlgChar ι (κ * κ') := by
  obtain ⟨hc, art, χ, a, ha, h1, h2⟩ := h
  obtain ⟨hc', art', χ', a', ha', h1', h2'⟩ := h'
  obtain rfl : art = art' := GlobalTheory.ArtinUniq.globalArtin_unique F Ω art art' ha ha'
  exact ⟨hc.mul hc', art, _, _, ha, isAlgPos_mul h1 h1', h2.mul h2'⟩

private theorem alg_fin (H : GlobalTheory.Published.GlobalArtinReciprocity) (ι : Qbar l ≃+* ℂ) {φ : G F Ω →* (Qbar l)ˣ}
    (ho : IsOpen (φ.ker : Set (G F Ω))) : IsAlgChar ι φ := by
  obtain ⟨art, ha⟩ := H F Ω
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have hfi : Finite (G F Ω ⧸ φ.ker) := Subgroup.quotient_finite_of_isOpen _ ho
  have hpos : 0 < φ.ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  obtain ⟨χ, ⟨h1, h2⟩, -⟩ := exists_unique_hchar_of_finite_order ha ι φ (continuous_of_isOpen_ker' φ ho) hpos
    (MonoidHom.ext fun s => by
      rw [MonoidHom.pow_apply, ← map_pow]
      exact φ.ker.pow_index_mem s)
  exact ⟨continuous_of_isOpen_ker' φ ho, art, χ, 0, ha, isAlgPos_zero_of_orderDvd hpos h1, h2⟩

private theorem alg_cyc (H : GlobalTheory.Published.GlobalArtinReciprocity) (ι : Qbar l ≃+* ℂ) (j : ℤ) :
    IsAlgChar ι (cycBar F Ω l ^ j) := by
  obtain ⟨hc, χ, art, a, h⟩ := UpperTheory.exists_algebraic_heckeChar_cyclotomic H F Ω l ι j (cycBar F Ω l ^ j)
    ⟨1, 1, le_rfl, fun _ _ => rfl, (mul_one _).symm⟩
  exact ⟨hc, art, χ, a, h⟩

end Hecke

theorem UpperTheory.V.Sd.algCyc :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Sd.AlgCyc := by
  intro P F Ω _ _ _ _ _ l _ ι
  refine ⟨fun j χ ho => alg_mul (alg_cyc P.litN.aut.art ι j) (alg_fin P.litN.aut.art ι ho),
    fun _ _ h h' => alg_mul h h', ?_⟩
  rintro κ ⟨hc, art, χ, a, ha, h1, h2⟩
  exact ⟨hc.inv, art, _, _, ha, isAlgPos_inv h1, h2.inv⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ShapeFacts
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial UpperTheory.V.Af UpperTheory.V.Sd

private theorem charpoly_smul' {K : Type} [Field K] [CharZero K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {c : K} (hc : c ≠ 0) :
    (c • M).charpoly = M.charpoly.scaleRoots c := by
  apply Polynomial.funext
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, x = c * y := ⟨c⁻¹ * x, by field_simp⟩
  rw [scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Matrix.eval_charpoly, Matrix.eval_charpoly,
    ← Matrix.det_smul]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [Matrix.scalar_apply, h, mul_sub]

private theorem scaleRoots_prod' {K ι : Type} [Field K] (m : Finset ι) (a : ι → K) (s : K) :
    (∏ j ∈ m, (X - C (a j))).scaleRoots s = ∏ j ∈ m, (X - C (a j * s)) := by
  classical
  induction m using Finset.induction_on with
  | empty => simp [one_scaleRoots]
  | insert j m hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, mul_scaleRoots_of_noZeroDivisors, ih, X_sub_C_scaleRoots]

private theorem sub_le' {K : Type} [NormedField K] [IsUltrametricDist K] (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max _ _

private theorem prod_cong {K ι : Type} [NormedField K] [IsUltrametricDist K] (m : Finset ι) (a b : ι → K)
    (ha : ∀ j, ‖a j‖ ≤ 1) (hab : ∀ j, ‖b j - a j‖ < 1) :
    ∀ i, ‖(∏ j ∈ m, (X - C (a j))).coeff i‖ ≤ 1 ∧
      ‖(∏ j ∈ m, (X - C (a j))).coeff i - (∏ j ∈ m, (X - C (b j))).coeff i‖ < 1 := by
  classical
  induction m using Finset.induction_on with
  | empty =>
    intro i
    simp only [Finset.prod_empty, sub_self, norm_zero, zero_lt_one, and_true, coeff_one]
    split_ifs <;> simp
  | insert j m hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    set p := ∏ j ∈ m, (X - C (a j))
    set q := ∏ j ∈ m, (X - C (b j))
    have hb : ‖b j‖ ≤ 1 := by
      have := IsUltrametricDist.norm_add_le_max (b j - a j) (a j)
      rw [sub_add_cancel] at this
      exact this.trans (max_le (hab j).le (ha j))
    have h1 : ∀ i, ‖a j * p.coeff i‖ ≤ 1 := fun i => by
      rw [norm_mul]; exact mul_le_one₀ (ha j) (norm_nonneg _) (ih i).1
    have h2 : ∀ i, ‖a j * p.coeff i - b j * q.coeff i‖ < 1 := fun i => by
      have e : a j * p.coeff i - b j * q.coeff i = b j * (p.coeff i - q.coeff i) - (b j - a j) * p.coeff i := by ring
      rw [e]
      refine (sub_le' _ _).trans_lt (max_lt ?_ ?_) <;> rw [norm_mul]
      · exact mul_lt_one_of_nonneg_of_lt_one_right hb (norm_nonneg _) (ih i).2
      · exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) (hab j) (ih i).1
    intro i
    cases i with
    | zero =>
      simp only [sub_mul, coeff_sub, coeff_X_mul_zero, coeff_C_mul, zero_sub, norm_neg]
      refine ⟨h1 0, ?_⟩
      rw [neg_sub_neg, norm_sub_rev]
      exact h2 0
    | succ i =>
      simp only [sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul]
      refine ⟨(sub_le' _ _).trans (max_le (ih i).1 (h1 _)), ?_⟩
      rw [sub_sub_sub_comm]
      exact (sub_le' _ _).trans_lt (max_lt (ih i).2 (h2 _))

theorem UpperTheory.V.Sd.shapeFacts :
    UpperTheory.V.Sd.ShapeFacts := by
  intro l _ Γ _ n r δ
  have conj : ∀ (g : GL (Fin n) (Qbar l)) (s : Γ), ((g * tw r δ s * g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
      (δ s : Qbar l) • ((g * r s * g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := fun g s => by
    simp only [Units.val_mul, tw_val, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro H χ ⟨g, hg⟩
    refine ⟨g, fun s hs => ?_⟩
    rw [conj, hg s hs, ← Matrix.diagonal_smul]
    congr 1
    ext i
    simp [mul_comm]
  · rintro H χ χ' e ⟨g, hg⟩ h
    let P : GL (Fin n) (Qbar l) := ⟨e.toPEquiv.toMatrix, e.symm.toPEquiv.toMatrix,
      by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp,
      by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp⟩
    refine ⟨P * g, fun s hs => ?_⟩
    have e1 : P * g * r s * (P * g)⁻¹ = P * (g * r s * g⁻¹) * P⁻¹ := by group
    rw [e1, Units.val_mul, Units.val_mul P, hg s hs]
    change e.toPEquiv.toMatrix * _ * e.symm.toPEquiv.toMatrix = _
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    ext i j
    simp [Matrix.diagonal_apply, h i s hs]
  · rintro H κ ⟨g, hg⟩
    refine ⟨g, fun s => ⟨fun i j hij => ?_, fun i => ?_⟩⟩
    · rw [conj, Matrix.smul_apply, (hg s).1 i j hij, smul_zero]
    · rw [conj, Matrix.smul_apply, (hg s).2 i]
      simp [mul_comm]
  · intro χ hδ h s i
    have e1 : ∏ j, (X - C (((χ j * δ) s : (Qbar l)ˣ) : Qbar l)) = (∏ j, (X - C (χ j s : Qbar l))).scaleRoots (δ s) := by
      rw [scaleRoots_prod']; simp
    have e2 : (∏ j, (X - C (χ j s : Qbar l))).natDegree = n := by
      rw [natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C _]; simp
    rw [e1, tw_val, charpoly_smul' _ (Units.ne_zero _), coeff_scaleRoots, coeff_scaleRoots, e2,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, ← sub_mul, norm_mul, norm_pow, hδ, one_pow, mul_one]
    exact h s i
  · intro χ χ' e hχ h hc s i
    have h1 := h s i
    rw [← Equiv.prod_comp e fun j => (X - C (χ j s : Qbar l))] at h1
    have h2 := (prod_cong Finset.univ (fun j => (χ (e j) s : Qbar l)) (fun j => (χ' j s : Qbar l))
      (fun j => (hχ _ _).le) (fun j => hc j s) i).2
    rw [← sub_add_sub_cancel _ ((∏ j, (X - C (χ (e j) s : Qbar l))).coeff i)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h1 h2)
  · intro hr
    have key : ∀ W, IsInv (tw r δ) W ↔ IsInv r W := fun W => by
      constructor
      · intro h g v hv
        have := W.smul_mem ((δ g : Qbar l)⁻¹) (h g v hv)
        rwa [tw_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at this
      · intro h g v hv
        rw [tw_val, Matrix.smul_mulVec]
        exact W.smul_mem _ (h g v hv)
    unfold IsIrr IsIrrSub at hr ⊢
    simpa only [key] using hr
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.IsAlgOfPos
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af

private theorem isAlg_of_pos {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {κ : HChar K}
    {m : (K →+* ℂ) → ℤ} (hκ : IsAlgPos κ m) : κ.IsAlg m := fun k => hκ k fun φ => by
  have h := IsTotallyComplex.complexEmbedding_not_isReal (Complex.ofRealHom.comp φ)
  refine absurd ?_ h
  rw [ComplexEmbedding.isReal_iff]
  ext x
  simp

private theorem regAlg_twist {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} {P : CuspSub K n}
    (h : (CG.mk P).IsRegAlg) {κ : HChar K} {m : (K →+* ℂ) → ℤ} (hκ : κ.IsAlg m) : (CG.mk (P.twist κ)).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
  have e := ((ParLaws.hasInfChar_infChar (CG.mk P) τ).twist κ).infChar_eq
  rw [CG.twist_mk] at e
  rw [e, (InfType.expo_of_infType K κ).1 m hκ τ]
  refine ⟨(h τ).1.map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := (h τ).2 y hy
  exact ⟨k + m τ, by push_cast; ring⟩

theorem UpperTheory.V.Sd.twC :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Sd.TwC := by
  intro _ F Ω _ _ _ _ _ _ l _ ι n r κ ⟨_, art, χ, a, hart, hpos, hL⟩ ⟨π, hreg, hatt⟩
  exact ⟨π.twist χ, regAlg_twist hreg (isAlg_of_pos hpos),
    UpperTheory.V.Af.Cq.attTwist F Ω l ι n r π hatt art χ a κ hart hL⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.SelfTwGal
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
  GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Base

private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  have hnorm : ∀ {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)),
      normV v = Ideal.absNorm v.asIdeal := by
    intro L _ _ v
    rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hnorm, hnorm]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

private theorem tendsto_under' {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] :
    Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 K') => w.under (𝓞 K)) Filter.cofinite Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  have h0 : Ideal.map (algebraMap (𝓞 K) (𝓞 K')) v.asIdeal ≠ 0 :=
    fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  have e : w.under (𝓞 K) = v := hw
  show w.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← e]
  exact le_rfl

private theorem algSat_eq (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat, Multiset.bind_singleton, Multiset.map_map]

theorem UpperTheory.V.Sd.selfTwGal :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Sd.SelfTwGal := by
  intro P F Ω _ _ _ _ _ l _ ι n r sat hu hc hatt η m hm hη hη1 hT
  obtain ⟨art, ha⟩ := P.litN.aut.art F Ω
  obtain ⟨δ, hδc, hL⟩ := ha.exists_isLAdicOf ι (isAlgPos_zero_of_orderDvd (χ := η) hm hη)
  have hpow : δ ^ m = 1 := hL.pow_eq_one ha.quot.surjective hη
  have hE : ∀ v, η.UnrAt v → CharEig ι δ v (η.val v : ℂˣ) := fun v hv A hA =>
    ⟨(hL.unr_iff ha (Or.inr rfl) hA).2 hv, fun σ hσ => by
      rw [map_inv, Units.val_inv_eq_inv_val, hL.frob_unr ha (Or.inr rfl) hv hA hσ, inv_inv,
        RingEquiv.apply_symm_apply]⟩
  refine ⟨δ, ?_, isOpen_ker_of_pow δ hδc hm fun g => DFunLike.congr_fun hpow g, ?_, ?_⟩
  · rintro rfl
    refine hη1 (Subtype.ext (MonoidHom.ext fun x => Units.ext ?_))
    obtain ⟨σ, hσ⟩ := toAb_surjective (art x)
    have e := hL x σ hσ.symm
    rw [infPow_zero, lPow_zero, inv_one, mul_one, mul_one, MonoidHom.one_apply, Units.val_one, eq_comm,
      map_eq_one_iff _ ι.symm.injective] at e
    exact e
  · refine isoOfFrob P F Ω l ι n r _ hc (UpperTheory.galoisRep_irreducibility_criterion.2 _ _ n r δ hc hδc) hatt.1
      ((UpperTheory.galoisRep_irreducibility_criterion.1 _ (G F Ω) _ n r).2.2 δ hatt.1) ?_
    filter_upwards [hatt.2, hT] with v hv hw
    obtain ⟨B, hB, hF⟩ := hv
    obtain ⟨h1, B', hB', h2⟩ := hw
    obtain rfl := hu v _ _ hB hB'
    refine ⟨_, hF, ?_⟩
    have h4 := UpperTheory.frobenius_eigenvalues_twist F Ω l ι n r δ _ _ _ hF (hE v h1)
    convert h4 using 1
    conv_lhs => rw [← h2]
    simp only [algSat_eq, Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, Units.val_mul, mul_assoc]
  · intro E _ _ _ _ _ hN
    haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
    haveI : Algebra.IsAlgebraic E Ω := Algebra.IsAlgebraic.tower_top (K := F) E
    haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed F, inferInstance⟩
    have hw : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, CharEig ι (δ.comp (res F Ω E)) w 1 := by
      filter_upwards [hN.2.2, (tendsto_under' (K := F) (K' := E)).eventually hT] with w h1 h2
      have hf := normV_under (K := F) w
      have h3 := (UpperTheory.frobenius_power_compatibility F E Ω l ι w _ hf).2 δ _ (hE _ h2.1)
      rwa [← Units.val_pow_eq_pow_val, h1 _ hf, Units.val_one] at h3
    have key := GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob (F := E) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
      (Filter.eventually_cofinite.1 hw) (f := fun s => δ (res F Ω E s)) (f' := fun _ => 1)
      (hδc.comp (continuous_restrictScalarsHom F E Ω)) continuous_const fun v hv _ A hA σ hσ => by
        have h := ((not_not.1 hv : CharEig _ _ _ _) A hA).2 σ hσ
        rw [map_eq_one_iff _ ι.injective, map_inv, Units.val_eq_one, inv_eq_one] at h
        exact h
    exact MonoidHom.ext fun s => congrFun key s
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ResFacts
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd

private theorem isIrr_of_range {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ}
    (r : Γ →* GL (Fin n) k) (r' : Γ' →* GL (Fin n) k) (h : ∀ g, ∃ g', r' g' = r g) (hr : IsIrr r) : IsIrr r' := by
  obtain ⟨h1, -, h3⟩ := hr
  refine ⟨h1, fun _ _ _ => Submodule.mem_top, fun W hW hi => h3 W hW fun g v hv => ?_⟩
  obtain ⟨g', e⟩ := h g
  rw [← e]
  exact hi g' v hv

theorem UpperTheory.V.Sd.resFacts :
    UpperTheory.V.Sd.ResFacts := by
  intro F E Ω _ _ _ _ _ _ _ _ _ _ l _ n r
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsAlgClosure F Ω :=
    ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans F E Ω⟩
  obtain ⟨hemb, hopen, -⟩ := galEmbTop F E Ω
  have hoe : Topology.IsOpenEmbedding (galEmb F E Ω) := by
    refine ⟨hemb, ?_⟩
    rw [← MonoidHom.coe_range, range_galEmb]
    exact hopen
  have hcyc : (cycBar F Ω l).comp (galEmb F E Ω) = cycBar E Ω l := rfl
  have hD : ∀ (A : ValuationSubring Ω) (s : G E Ω), s ∈ Dec (F := E) A → galEmb F E Ω s ∈ Dec (F := F) A :=
    fun A s hs => hs
  have hI : ∀ (A : ValuationSubring Ω) (s : G E Ω), s ∈ Ine (F := E) A → galEmb F E Ω s ∈ Ine (F := F) A :=
    fun A s hs => ⟨hD A s hs.1, hs.2⟩
  refine ⟨hemb.continuous, hopen, hcyc, ⟨isIrr_of_range _ _ ?_, isIrr_of_range _ _ ?_⟩, ?_, ?_, ?_⟩
  · rintro ⟨g, hg⟩
    rw [← range_galEmb] at hg
    obtain ⟨g', rfl⟩ := hg
    exact ⟨g', rfl⟩
  · exact fun g => ⟨⟨_, galEmb_mem F E Ω g⟩, rfl⟩
  · intro h H hH
    refine isIrr_of_range _ _ ?_ (h (H.map (galEmb F E Ω)) (hoe.isOpenMap _ hH))
    rintro ⟨g, g', hg', rfl⟩
    exact ⟨⟨g', hg'⟩, rfl⟩
  · intro τ h A hA
    obtain ⟨g, hg⟩ := h A hA
    exact ⟨g, fun s hs => hg _ (hI A s hs)⟩
  · rintro m ψ A ⟨κ, ⟨g, hg⟩, h2, h3⟩
    let j : ↥(Dec (F := E) A) →* ↥(Dec (F := F) A) :=
      ((galEmb F E Ω).comp (Dec (F := E) A).subtype).codRestrict _ fun s => hD A s s.2
    exact ⟨fun i => (κ i).comp j, ⟨g, fun s => hg (j s)⟩, fun i s hs => h2 i (j s) (hI A s hs), fun i s => h3 i (j s)⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.DenseRangeUnitsR
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af

section Real

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E]

private noncomputable def diagR (E : Type) [Field E] [NumberField E] [IsTotallyReal E] : E →+* TR.Rinf E :=
  (TR.pInf E).comp (algebraMap E (Ad E))

private theorem infDiag_eqR (k : Eˣ) : infDiag k = TR.infId E (Units.map (diagR E).toMonoidHom k) := by
  classical
  have h : ((infDiag k : Ideles E) : AdeleRing (𝓞 E) E) = (algebraMap E (InfiniteAdeleRing E) k, 1) := by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, Units.coe_prod]
    let ι : (∀ w : InfinitePlace E, w.Completion) →* AdeleRing (𝓞 E) E :=
      MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)
    change ∏ w : InfinitePlace E, ι (Pi.mulSingle w (algebraMap E w.Completion k)) =
      ι (fun w => algebraMap E w.Completion k)
    rw [← map_prod, Finset.univ_prod_mulSingle]
  apply Units.ext
  rw [h]
  refine Prod.ext ?_ ?_
  · change _ = 1 - TR.infEq E 1 + TR.infEq E ((TR.infEq E).symm (algebraMap E (InfiniteAdeleRing E) k))
    simp
  · change (1 : Af E) = 1 - 0 + 0
    simp

private theorem denseRange_diagR : DenseRange (diagR E) := by
  have hc : Continuous (TR.infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)
  exact (TR.infEq E).symm.surjective.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap E) hc

private theorem denseRange_unitsR : DenseRange (Units.map (diagR E).toMonoidHom) := by
  refine dense_iff_inter_open.2 fun U hU ⟨u, hu⟩ => ?_
  obtain ⟨k, v, hv, hk⟩ := denseRange_diagR.exists_mem_open (Units.isOpenEmbedding_val.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have h0 : k ≠ 0 := by
    rintro rfl
    exact v.ne_zero (hk.trans (map_zero _))
  exact ⟨v, hv, Units.mk0 k h0, Units.ext hk.symm⟩

private theorem diagR_mk (φ : E →+* ℂ) (k : E) : ((diagR E k (InfinitePlace.mk φ) : ℝ) : ℂ) = φ k := by
  have hr := IsTotallyReal.isReal (InfinitePlace.mk φ)
  have e : diagR E k (InfinitePlace.mk φ) = InfinitePlace.embedding_of_isReal hr k := by
    change InfinitePlace.Completion.extensionEmbeddingOfIsReal hr
      (algebraMap E (InfinitePlace.mk φ).Completion k) = _
    rw [AbsoluteValue.Completion.algebraMap_def]
    simp [WithAbs.algebraMap_right_apply]
  rw [e, InfinitePlace.embedding_of_isReal_apply,
    InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 hr)]

private theorem chiInf_pos {χ : HChar E} {n : (E →+* ℂ) → ℤ} (h : IsAlgPos χ n) (u : (TR.Rinf E)ˣ)
    (hu : ∀ v, 0 < u.val v) :
    ((TR.chiInf χ u : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, ((u.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ n φ := by
  have hc : ∀ v, Continuous fun u : (TR.Rinf E)ˣ => u.val v := fun v => (continuous_apply v).comp Units.continuous_val
  have ho : IsOpen {u : (TR.Rinf E)ˣ | ∀ v, 0 < u.val v} := by
    rw [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun v => isOpen_lt continuous_const (hc v)
  have hcl : IsClosed {u : (TR.Rinf E)ˣ |
      ((TR.chiInf χ u : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, ((u.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ n φ} :=
    isClosed_eq (Units.continuous_val.comp (TR.continuous_chiInf χ)) (continuous_finsetProd _ fun φ _ =>
      (Complex.continuous_ofReal.comp (hc _)).zpow₀ _ fun u => Or.inl
        (Complex.ofReal_ne_zero.2 (TR.unit_ne_zero u _)))
  refine closure_minimal ?_ hcl (denseRange_unitsR.open_subset_closure_inter ho hu)
  rintro _ ⟨hk, k, rfl⟩
  have h1 := h k fun φ => by
    have h2 := hk (InfinitePlace.mk (Complex.ofRealHom.comp φ))
    have h3 := diagR_mk (Complex.ofRealHom.comp φ) (k : E)
    exact h2.trans_eq (Complex.ofReal_injective h3)
  rw [HChar.inf, MonoidHom.comp_apply, infDiag_eqR] at h1
  refine h1.trans (Finset.prod_congr rfl fun φ _ => ?_)
  exact congrArg (· ^ n φ) (diagR_mk φ (k : E)).symm

private theorem expo_intR {χ : HChar E} {n : (E →+* ℂ) → ℤ} (h : IsAlgPos χ n) (v : InfinitePlace E) :
    ∃ k : ℤ, TR.expo χ v = k := by
  classical
  refine ⟨∑ φ : E →+* ℂ, if InfinitePlace.mk φ = v then n φ else 0, TR.expo_eq_of_exp χ v _ fun t => ?_⟩
  rw [chiInf_pos h _ fun w => Real.exp_pos _]
  simp only [TR.expU_val, Complex.ofReal_exp, ← Complex.exp_int_mul]
  rw [← Complex.exp_sum, Int.cast_sum, Finset.sum_mul]
  refine congrArg _ (Finset.sum_congr rfl fun φ _ => ?_)
  split_ifs with e
  · rw [e, Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne e]

end Real

private theorem ev_notMem {K : Type} [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  have hl : l.Prime := Fact.out
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun v hv => ?_)
  exact Ideal.dvd_span_singleton.mpr (not_not.1 hv)

private theorem sys_twist {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {l : ℕ}
    [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {R : G K Ω →* GL (Fin n) (Qbar l)}
    {sat sat' : HeightOneSpectrum (𝓞 K) → Multiset ℂˣ → Prop} (hA : AttachedSys ι R sat) {art : Ideles K →* Gab K Ω}
    {κ : HChar K} {m : (K →+* ℂ) → ℤ} {μ : G K Ω →* (Qbar l)ˣ} (ha : IsGlobalArtin art) (h : IsLAdicOf art ι κ m μ)
    (hs : ∀ w B, sat w B → κ.UnrAt w → sat' w (B.map (· * κ.val w))) : AttachedSys ι (tw R μ) sat' := by
  refine ⟨(UpperTheory.galoisRep_irreducibility_criterion.1 _ (G K Ω) _ n R).2.2 μ hA.1, ?_⟩
  filter_upwards [hA.2, Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified κ), ev_notMem (K := K) l]
    with w ⟨B, hB, hE⟩ hu hl
  refine ⟨_, hs w B hB hu, ?_⟩
  have hc : UpperTheory.V.Af.Bc.CharEig ι μ w (κ.val w : ℂ) := by
    refine fun A hA => ⟨(h.unr_iff ha (Or.inl hl) hA).2 hu, fun σ hσ => ?_⟩
    rw [map_inv, Units.val_inv_eq_inv_val, h.frob_unr ha (Or.inl hl) hu hA hσ, inv_inv, RingEquiv.apply_symm_apply]
  have h4 := UpperTheory.frobenius_eigenvalues_twist K Ω l ι n R μ w _ _ hE hc
  convert h4 using 1
  simp only [algSat, Multiset.bind_singleton, Multiset.map_map, Multiset.pure_def, Multiset.bind_def]
  refine Multiset.map_congr rfl fun b _ => ?_
  simp only [Function.comp_apply, Units.val_mul, mul_assoc]

theorem UpperTheory.V.Sd.twR :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Sd.TwR := by
  rintro - F Ω _ _ _ _ _ _ l _ ι n r κ ⟨-, art, χ, a, ha, hχ, hL⟩ ⟨π, hr, hA⟩
  exact ⟨π.twist χ, hr.twist (expo_intR hχ), sys_twist hA ha hL fun w B hB hu => hB.twist hu⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.DirOf
open UpperTheory.V in
theorem UpperTheory.V.Sd.dirOf :
    UpperTheory.V.Sd.DirOf := by
  intro l _ Ω _ _ _ ι N hN φ hφ
  have : NeZero N := ⟨hN.ne'⟩
  have hs := (Chr.clsOnto Ω N).1
  have hk : (Chr.cls ℚ Ω N).ker ≤ φ.ker := fun s h => by
    have h1 : Chr.cls ℚ Ω N s = 1 := h
    refine hφ s fun ζ hζ => ?_
    rw [Chr.cls_spec N s ζ hζ, h1, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ, pow_one]
  let f := MonoidHom.liftOfRightInverse (Chr.cls ℚ Ω N) (Function.surjInv hs)
    (Function.rightInverse_surjInv hs) ⟨φ, hk⟩
  have hf : ∀ s, f (Chr.cls ℚ Ω N s) = φ s := fun s =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨φ, hk⟩ s
  let χ₀ : DirichletCharacter ℂ N := MulChar.ofUnitHom ((Units.map ι.toRingHom.toMonoidHom).comp f)
  have hd : χ₀.conductor ∣ N := χ₀.conductor_dvd_level
  have hM : NeZero χ₀.conductor := ⟨χ₀.conductor_ne_zero⟩
  refine ⟨χ₀.conductor, hM, χ₀.primitiveCharacter, hd, χ₀.primitiveCharacter_isPrimitive, ?_⟩
  ext s
  have h1 := DFunLike.congr_fun ((Chr.clsFacts ℚ Ω N).2.1 _ hd) s
  have h2 : χ₀.primitiveCharacter (ZMod.unitsMap hd (Chr.cls ℚ Ω N s)) = χ₀ (Chr.cls ℚ Ω N s) := by
    conv_rhs => rw [← χ₀.changeLevel_primitiveCharacter]
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd]
    simp [ZMod.unitsMap_def]
  have h3 : χ₀ (Chr.cls ℚ Ω N s) = ι (φ s) := by
    rw [← hf]
    simp [χ₀]
  rw [Chr.dirG, MonoidHom.comp_apply, ← h1, MulChar.coe_toUnitHom, MulChar.ringHomComp_apply, MonoidHom.comp_apply, h2, h3]
  simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.SymmetricCubePreservesSymplecticForm
open Polynomial UpperTheory.V.Af Formalism.ConjugateSelfDual
open scoped Matrix

namespace UpperTheory.V.Sd

section Rel

variable {K : Type} [NormedField K] [IsUltrametricDist K]

private def Rl (x y : K) : Prop := ‖y‖ ≤ 1 ∧ ‖x - y‖ < 1

private theorem Rl.left {x y : K} (h : Rl x y) : ‖x‖ ≤ 1 := by
  have := IsUltrametricDist.norm_add_le_max (x - y) y
  rw [sub_add_cancel] at this
  exact this.trans (max_le h.2.le h.1)


private theorem Rl.mul {x y z w : K} (h : Rl x y) (h' : Rl z w) : Rl (x * z) (y * w) := by
  refine ⟨by rw [norm_mul]; exact mul_le_one₀ h.1 (norm_nonneg _) h'.1, ?_⟩
  rw [show x * z - y * w = x * (z - w) + (x - y) * w by ring]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
  · rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right h.left (norm_nonneg _) h'.2
  · rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) h.2 h'.1

end Rel

end UpperTheory.V.Sd
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.IrrAb
open Matrix Formalism.MainNotions.N UpperTheory.V.Af UpperTheory.V.U3

theorem UpperTheory.V.Sd.irrAb :
    UpperTheory.V.Sd.IrrAb := by
  intro l _ Γ _ _ _ n r hr hio H H' hH hle hab
  have h0 := hio H hH
  have hne : (⊤ : Submodule (Formalism.ConjugateSelfDual.Qbar l) (Fin n → Formalism.ConjugateSelfDual.Qbar l)) ≠ ⊥ := h0.1
  haveI : Nontrivial (Fin n → Formalism.ConjugateSelfDual.Qbar l) := Submodule.nontrivial_iff (Formalism.ConjugateSelfDual.Qbar l) |>.mp ⟨_, _, hne⟩
  have hn : n ≠ 0 := by
    rintro rfl
    exact hne (Subsingleton.elim _ _)
  refine ⟨hne, fun _ _ _ => trivial, fun W _ hW => ?_⟩
  by_contra hcon
  have hab' : ∀ a b : H, a * b * a⁻¹ * b⁻¹ ∈ H'.subgroupOf H := fun a b =>
    Subgroup.mem_subgroupOf.mpr (hab a a.2 b b.2)
  haveI : (H'.subgroupOf H).Normal := ⟨fun x hx g => by
    have := (H'.subgroupOf H).mul_mem (hab' g x) hx
    simpa using this⟩
  obtain ⟨φ, hφ1, -, hφn, M, hM⟩ := exists_selfTwist (r.comp H.subtype) (H'.subgroupOf H) hab'
    (fun U hU => h0.2.2 U le_top fun g v hv => hU g trivial v hv)
    (fun h => hcon (h W fun g hg v hv => hW ⟨g, Subgroup.mem_subgroupOf.mp hg⟩ v hv))
  have hM' : ∀ g : H, ((φ g : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l) • ((M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l))) =
      (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * M := fun g => by
    have := hM g trivial
    rw [Matrix.mul_smul] at this
    exact this
  have hiff : ∀ g : H, φ g = 1 ↔ (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) =
      (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * M := fun g => by
    constructor
    · intro h
      have := hM' g
      rwa [h, Units.val_one, one_smul] at this
    · intro h
      have h1 := hM' g
      rw [← h] at h1
      haveI : NeZero n := ⟨hn⟩
      have h2 : (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) ≠ 0 :=
        (M * r g).ne_zero
      exact Units.ext (smul_left_injective _ h2 (h1.trans (one_smul _ _).symm))
  have hcl : IsClosed (φ.ker : Set H) := by
    have hc : Continuous fun g : H => (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) :=
      Units.continuous_val.comp (hr.comp continuous_subtype_val)
    have : (φ.ker : Set H) = {g : H | (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) =
      (r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) * M} := Set.ext fun g => hiff g
    rw [this]
    exact isClosed_eq (continuous_const.mul hc) (hc.mul continuous_const)
  haveI : NeZero n := ⟨hn⟩
  have hrg : φ.range ≤ rootsOfUnity n (Formalism.ConjugateSelfDual.Qbar l) := by
    rintro _ ⟨g, rfl⟩
    rw [mem_rootsOfUnity]
    exact DFunLike.congr_fun hφn g
  haveI : Finite φ.range := Finite.of_injective _ (Subgroup.inclusion_injective hrg)
  haveI : φ.ker.FiniteIndex := Subgroup.finiteIndex_ker φ
  have hop : IsOpen (φ.ker : Set H) := Subgroup.isOpen_of_isClosed_of_finiteIndex _ hcl
  have hop' : IsOpen ((φ.ker.map H.subtype : Subgroup Γ) : Set Γ) := by
    rw [Subgroup.coe_map]
    exact hH.isOpenMap_subtype_val _ hop
  have h1 := hio _ hop'
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)))
  have htop := (h1.2.2 (Module.End.eigenspace (Matrix.toLin' (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l))) a) le_top (by
    rintro ⟨_, g, hg, rfl⟩ v hv
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
    change (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) *ᵥ ((r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) *ᵥ v) =
      a • ((r g : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) *ᵥ v)
    rw [Matrix.mulVec_mulVec, (hiff g).mp hg, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul])).resolve_left ha
  have hMa : (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) = a • 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    have : v ∈ Module.End.eigenspace (Matrix.toLin' (M : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l))) a := by
      rw [htop]; trivial
    rw [Module.End.mem_eigenspace_iff] at this
    rw [this]; simp
  apply hφ1
  ext1 g
  exact (hiff g).mpr (by rw [hMa]; simp)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.LineOfNotIrr
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TraceZero
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qf25.modFun :
    {O M ι : Type} → [inst : CommRing O] → [inst_1 : AddCommGroup M] → [_root_.Module O M] → _root_.Module O (ι → M) :=
    fun {O M ι : Type} [CommRing O] [AddCommGroup M] [_root_.Module O M] ↦ Pi.Function.module ι O M
attribute [local instance] UpperTheory.Reformulated.B.Qf25.modFun

theorem UpperTheory.Reformulated.B.Qf25.trace_zero :
    ∀ {k : Type} [inst : Field k] (S T : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) k),
      T.det ≠ (0 : k) →
        S.charpoly.Separable →
          ∀ (v : Fin (2 : ℕ) → k),
            v ≠ (0 : Fin (2 : ℕ) → k) →
              T.mulVec v ∉ k ∙ v →
                ∀ (a b c : k),
                  S.mulVec v = a • v →
                    S.mulVec (T.mulVec v) = b • T.mulVec v →
                      S.mulVec (T.mulVec (T.mulVec v)) = c • T.mulVec (T.mulVec v) → T.trace = (0 : k) := by
  intro k _ S T hdet hsep v hv hw a b c ha hb hc
  have hCH : T.mulVec (T.mulVec v) = T.trace • T.mulVec v - T.det • v := by
    ext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.trace_fin_two,
        Matrix.det_fin_two] <;> ring
  generalize T.mulVec v = w at hw hb hc hCH
  have hD : v 0 * w 1 - v 1 * w 0 ≠ 0 := by
    intro h
    apply hw
    rw [Submodule.mem_span_singleton]
    by_cases h0 : v 0 = 0
    · have h1 : v 1 ≠ 0 := by
        intro h1
        apply hv
        ext i
        fin_cases i
        · exact h0
        · exact h1
      have hw0 : w 0 = 0 := by
        have : v 1 * w 0 = 0 := by linear_combination -h + w 1 * h0
        exact (mul_eq_zero.1 this).resolve_left h1
      refine ⟨w 1 / v 1, ?_⟩
      ext i
      fin_cases i
      · simp [h0, hw0]
      · simp [h1]
    · refine ⟨w 0 / v 0, ?_⟩
      ext i
      fin_cases i
      · simp [h0]
      · show w 0 / v 0 * v 1 = w 1
        field_simp
        linear_combination -h
  rw [hCH, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, ha, hb] at hc
  have c0 : T.trace * (b * w 0) - T.det * (a * v 0) = c * (T.trace * w 0 - T.det * v 0) :=
    congrFun hc 0
  have c1 : T.trace * (b * w 1) - T.det * (a * v 1) = c * (T.trace * w 1 - T.det * v 1) :=
    congrFun hc 1
  by_contra ht
  have hac : a = c := by
    have : T.det * (a - c) * (v 0 * w 1 - v 1 * w 0) = 0 := by
      linear_combination w 0 * c1 - w 1 * c0
    exact sub_eq_zero.1 ((mul_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hD)).resolve_left hdet)
  have hbc : b = c := by
    have : T.trace * (b - c) * (v 0 * w 1 - v 1 * w 0) = 0 := by
      linear_combination v 0 * c1 - v 1 * c0
    exact sub_eq_zero.1 ((mul_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hD)).resolve_left ht)
  subst hac hbc
  have a0 := congrFun ha 0
  have a1 := congrFun ha 1
  have b0 := congrFun hb 0
  have b1 := congrFun hb 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
    at a0 a1 b0 b1
  have s00 : S 0 0 = b := by
    apply mul_right_cancel₀ hD
    linear_combination w 1 * a0 - v 1 * b0
  have s01 : S 0 1 = 0 := by
    apply mul_right_cancel₀ hD
    linear_combination v 0 * b0 - w 0 * a0
  have s11 : S 1 1 = b := by
    apply mul_right_cancel₀ hD
    linear_combination v 0 * b1 - w 0 * a1
  have hp : S.charpoly = (Polynomial.X - Polynomial.C b) * (Polynomial.X - Polynomial.C b) := by
    rw [Matrix.charpoly_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two, s00, s01, s11]
    simp only [map_add (f := _), map_sub, map_mul, map_zero]
    ring
  have hu := hsep.squarefree (Polynomial.X - Polynomial.C b) (hp ▸ dvd_rfl)
  exact Polynomial.not_isUnit_X_sub_C b hu
end

open Polynomial Formalism.ConjugateSelfDual Formalism.MainNotions.N UpperTheory.V.Af UpperTheory.V.Sd
open scoped Matrix

private lemma trace_zero {k : Type} [Field k] (S T : Matrix (Fin 2) (Fin 2) k) (hT : T.det ≠ 0)
    (hS : S.charpoly.Separable) (v : Fin 2 → k) (hv : v ≠ 0) (hw : T *ᵥ v ∉ Submodule.span k {v})
    (a b c : k) (ha : S *ᵥ v = a • v) (hb : S *ᵥ (T *ᵥ v) = b • (T *ᵥ v))
    (hc : S *ᵥ (T *ᵥ (T *ᵥ v)) = c • (T *ᵥ (T *ᵥ v))) : T.trace = 0 :=
  _root_.UpperTheory.Reformulated.B.Qf25.trace_zero S T hT hS v hv hw a b c ha hb hc

private lemma line_of_not_irr {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* GL (Fin 2) k) (h : ¬ IsIrr ρ) :
    ∃ v : Fin 2 → k, v ≠ 0 ∧ ∀ g, ∃ c : k, (ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v = c • v := by
  simp only [IsIrr, IsIrrSub, not_and, not_forall] at h
  obtain ⟨W, -, hW, hne⟩ := h top_ne_bot (fun _ _ _ => Submodule.mem_top)
  rw [not_or] at hne
  have h2 : Module.finrank k W < 2 := by
    simpa using Submodule.finrank_lt hne.2
  have h0 : Module.finrank k W ≠ 0 := fun h => hne.1 (Submodule.finrank_eq_zero.mp h)
  have h1 : Module.finrank k W = 1 := by omega
  obtain ⟨v, hv, hall⟩ := finrank_eq_one_iff'.mp h1
  refine ⟨v, fun h => hv (Subtype.ext h), fun g => ?_⟩
  obtain ⟨c, hc⟩ := hall ⟨_, hW g v v.2⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

private lemma moves_line {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* GL (Fin 2) k) (h : IsIrr ρ) (v : Fin 2 → k)
    (hv : v ≠ 0) : ∃ t, (ρ t : Matrix (Fin 2) (Fin 2) k) *ᵥ v ∉ Submodule.span k {v} := by
  by_contra hcon
  push Not at hcon
  have hinv : IsInv ρ (Submodule.span k {v}) := by
    intro g u hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ _ (hcon g)
  rcases h.2.2 _ le_top hinv with h1 | h1
  · exact hv (Submodule.span_singleton_eq_bot.mp h1)
  · have := finrank_span_singleton (K := k) hv
    rw [h1] at this
    simp at this

private lemma core {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* GL (Fin 2) k) (hirr : IsIrr ρ) (H : Subgroup Γ)
    (hN : H.Normal) (hs : ∃ s ∈ H, (ρ s : Matrix (Fin 2) (Fin 2) k).charpoly.Separable)
    (hred : ¬ IsIrr (ρ.comp H.subtype)) :
    ∃ D : Γ → Prop, (∀ s ∈ H, D s) ∧ (∃ t, ¬ D t) ∧ (∀ s t, D s → ¬ D t → ¬ D (t * s)) ∧
      ∀ t, ¬ D t → (ρ t : Matrix (Fin 2) (Fin 2) k).trace = 0 := by
  obtain ⟨v, hv, hev⟩ := line_of_not_irr _ hred
  obtain ⟨s₀, hs₀, hsep⟩ := hs
  have hev' : ∀ s ∈ H, ∃ c : k, (ρ s : Matrix (Fin 2) (Fin 2) k) *ᵥ v = c • v := fun s hs => hev ⟨s, hs⟩
  have hmul : ∀ (s t : Γ) (u : Fin 2 → k), (ρ (s * t) : Matrix (Fin 2) (Fin 2) k) *ᵥ u =
      (ρ s : Matrix (Fin 2) (Fin 2) k) *ᵥ ((ρ t : Matrix (Fin 2) (Fin 2) k) *ᵥ u) := by
    intro s t u
    rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  have hconj : ∀ g, ∃ c : k, (ρ s₀ : Matrix (Fin 2) (Fin 2) k) *ᵥ ((ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v) =
      c • ((ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v) := by
    intro g
    obtain ⟨c, hc⟩ := hev' _ (hN.conj_mem' s₀ hs₀ g)
    refine ⟨c, ?_⟩
    rw [← Matrix.mulVec_smul, ← hc, ← hmul, ← hmul]
    congr 3
    group
  refine ⟨fun s => (ρ s : Matrix (Fin 2) (Fin 2) k) *ᵥ v ∈ Submodule.span k {v}, fun s hs => ?_,
    moves_line ρ hirr v hv, fun s t hs ht hts => ht ?_, fun t ht => ?_⟩
  · obtain ⟨c, hc⟩ := hev' s hs
    exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
  · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hs
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hv
      have := hmul s⁻¹ s v
      rw [← hc, zero_smul, Matrix.mulVec_zero] at this
      simpa using this
    simp only [hmul, ← hc, Matrix.mulVec_smul] at hts
    exact (Submodule.smul_mem_iff _ hc0).mp hts
  · obtain ⟨a, ha⟩ := hev' s₀ hs₀
    obtain ⟨b, hb⟩ := hconj t
    obtain ⟨c, hc⟩ := hconj (t * t)
    rw [hmul t t] at hc
    exact trace_zero _ _ (Matrix.GeneralLinearGroup.det_ne_zero (ρ t)) hsep v hv ht a b c ha hb hc

theorem UpperTheory.V.Sd.sIabs :
    UpperTheory.V.Sd.SIabs := by
  intro l _ _ Γ _ ρ Φ hΦ hirr hres H hN hs hred
  obtain ⟨D, hH, ⟨t₀, ht₀⟩, hmul, htr⟩ := core ρ hirr H hN hs hred
  have hneg : ∀ t, ¬ D t → ‖(Φ t : Qbar l) + 1‖ < 1 := by
    intro t ht
    have h := hres t 1
    rw [Matrix.charpoly_fin_two, htr t ht, Fin.prod_univ_two] at h
    have e : (X - C ((![1, Φ] : Fin 2 → Γ →* (Qbar l)ˣ) 0 t : Qbar l)) * (X - C ((![1, Φ] : Fin 2 → Γ →* (Qbar l)ˣ) 1 t : Qbar l)) =
        X ^ 2 - C ((Φ t : Qbar l) + 1) * X + C (Φ t : Qbar l) := by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, MonoidHom.one_apply, Units.val_one, map_add (f := _), map_one]
      ring
    rw [e] at h
    simpa [coeff_X_pow, coeff_C, coeff_one] using h
  have hpos : ∀ s, D s → ‖(Φ s : Qbar l) - 1‖ < 1 := by
    intro s hs
    have h1 := hneg _ ht₀
    have h2 := hneg _ (hmul s t₀ hs ht₀)
    rw [map_mul, Units.val_mul] at h2
    have e : (Φ t₀ : Qbar l) * ((Φ s : Qbar l) - 1) = ((Φ t₀ : Qbar l) * Φ s + 1) + (-((Φ t₀ : Qbar l) + 1)) := by ring
    have h3 := IsUltrametricDist.norm_add_le_max ((Φ t₀ : Qbar l) * Φ s + 1) (-((Φ t₀ : Qbar l) + 1))
    rw [← e, norm_mul, hΦ, one_mul, norm_neg] at h3
    exact h3.trans_lt (max_lt h2 h1)
  refine ⟨fun s hs => by simpa [Cong] using hpos s (hH s hs), fun s => ?_⟩
  have e : ((Φ s ^ 2 : (Qbar l)ˣ) : Qbar l) - ((1 : (Qbar l)ˣ) : Qbar l) = ((Φ s : Qbar l) + 1) * ((Φ s : Qbar l) - 1) := by
    rw [Units.val_pow_eq_pow_val, Units.val_one]; ring
  have p1 : ‖(Φ s : Qbar l) + 1‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (Φ s : Qbar l) 1
    simpa [hΦ] using this
  have p2 : ‖(Φ s : Qbar l) - 1‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (Φ s : Qbar l) (-1)
    simpa [hΦ, sub_eq_add_neg] using this
  rw [Cong, e, norm_mul]
  by_cases hs : D s
  · exact mul_lt_one_of_nonneg_of_lt_one_right p1 (norm_nonneg _) (hpos s hs)
  · exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) (hneg s hs) p2
end
