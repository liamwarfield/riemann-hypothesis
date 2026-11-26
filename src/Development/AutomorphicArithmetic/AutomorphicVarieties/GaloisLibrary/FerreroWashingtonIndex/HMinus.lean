module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply
public import GroundTheory.GlobalFields.HasseNorm

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormEqMulCE
noncomputable def UpperTheory.Reformulated.B.Qh29.cE :
    (E : Type) → [inst : Field E] → [inst_1 : NumberField E] → [NumberField.IsCMField E] → E ≃+* E :=
    fun (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] ↦ (NumberField.IsCMField.complexConj E).toRingEquiv

theorem UpperTheory.Reformulated.B.Qh29.norm_eq_mul_cE :
    ∀ (K : Type) [inst : Field K] [inst_1 : NumberField K] [inst_2 : NumberField.IsCMField K] (y : K),
      (Algebra.algebraMap (↥(NumberField.maximalRealSubfield K)) K : ↥(NumberField.maximalRealSubfield K) → K)
          ((Algebra.norm ↥(NumberField.maximalRealSubfield K) : K → ↥(NumberField.maximalRealSubfield K)) y) =
        y * (UpperTheory.Reformulated.B.Qh29.cE K : K → K) y := by
  intro K _ _ _ y
  classical
  have hne := NumberField.IsCMField.complexConj_ne_one K
  have hcard : Nat.card (K ≃ₐ[NumberField.maximalRealSubfield K] K) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
  have huniv : (Finset.univ : Finset (K ≃ₐ[NumberField.maximalRealSubfield K] K)) =
      {1, NumberField.IsCMField.complexConj K} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hne.symm, ← Nat.card_eq_fintype_card, hcard]
  have h := Algebra.norm_eq_prod_automorphisms (NumberField.maximalRealSubfield K) y
  rw [huniv, Finset.prod_pair hne.symm] at h
  exact h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Mk0PrincipalEqOne
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.LocFin
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem ideal_step {R : Type} [CommRing R] [IsDedekindDomain R] (c : R ≃+* R) (P I : Ideal R) (a : R)
    (hP : P ≠ 0) (hI : I ≠ 0) (ha : a ≠ 0) (hc : P.map c = P) (h : I * I.map c = Ideal.span {a}) :
    ∃ b t : R, b * c b = a * t ∧ ∀ w : Ideal R, w.IsPrime → P ≤ w → t ∉ w := by
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_sup_span_eq (I := I * P) (J := I) Ideal.mul_le_left (mul_ne_zero hI hP)
  obtain ⟨J, hJ⟩ : I ∣ Ideal.span {b} := Ideal.dvd_iff_le.2 (hb ▸ le_sup_right)
  have h1 : P ⊔ J = ⊤ := by
    rw [hJ, ← Ideal.mul_sup] at hb
    have := mul_left_cancel₀ hI (hb.trans (mul_one I).symm)
    rwa [Ideal.one_eq_top] at this
  have h2 : P ⊔ J.map c = ⊤ := by
    have := congrArg (Ideal.map c) h1
    rwa [Ideal.map_sup, hc, Ideal.map_top] at this
  have h3 : Ideal.span {b * c b} = Ideal.span {a} * (J * J.map c) := by
    have := congrArg (Ideal.map c) hJ
    rw [Ideal.map_span, Set.image_singleton, Ideal.map_mul] at this
    rw [← Ideal.span_singleton_mul_span_singleton, hJ, this, ← h]; ring
  have h4 : b * c b ∈ Ideal.span {a} :=
    (Ideal.span_singleton_le_iff_mem _).1 (h3 ▸ Ideal.mul_le_left)
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.1 h4
  refine ⟨b, t, ht, fun w hw hPw htw => ?_⟩
  rw [ht, ← Ideal.span_singleton_mul_span_singleton] at h3
  have h5 := mul_left_cancel₀ (by simpa using ha) h3
  have h6 : J * J.map c ≤ w := h5 ▸ (Ideal.span_singleton_le_iff_mem _).2 htw
  rcases hw.mul_le.1 h6 with h7 | h7
  · exact hw.ne_top (top_le_iff.1 (h1 ▸ sup_le hPw h7))
  · exact hw.ne_top (top_le_iff.1 (h2 ▸ sup_le hPw h7))

private theorem norm_cm (K : Type) [Field K] [NumberField K] [IsCMField K] (b : K) :
    algebraMap (maximalRealSubfield K) K (Algebra.norm (maximalRealSubfield K) b) = b * IsCMField.complexConj K b := by
  classical
  have hcard : Fintype.card (K ≃ₐ[maximalRealSubfield K] K) = 2 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.card_top, ← IsCMField.zpowers_complexConj_eq_top, Nat.card_zpowers,
      IsCMField.orderOf_complexConj]
  have hne := (IsCMField.complexConj_ne_one K).symm
  have huniv : (Finset.univ : Finset (K ≃ₐ[maximalRealSubfield K] K)) = {1, IsCMField.complexConj K} :=
    (Finset.eq_univ_of_card _ (by rw [Finset.card_pair hne, hcard])).symm
  rw [Algebra.norm_eq_prod_automorphisms, huniv, Finset.prod_pair hne]
  rfl

theorem UpperTheory.V.FW.locFin :
    ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (x : (maximalRealSubfield K)ˣ) (a : 𝓞 K) (I : (Ideal (𝓞 K))⁰), UnrFin K → (a : K) = algebraMap (maximalRealSubfield K) K x → (I * idMap (cE K) I).1 = Ideal.span {a} → ∀ v, GroundTheory.Global.IdeleGroup.finiteProj v (GroundTheory.Global.IdeleGroup.diagonal (maximalRealSubfield K) x) ∈ (GroundTheory.Global.IdeleNorm.finiteLocalNorm K v).range := by
  intro K _ _ _ x a I hunr hax hI v
  have haK : (a : K) ≠ 0 := by rw [hax]; simp
  have ha : a ≠ 0 := fun h => haK (by rw [h]; rfl)
  obtain ⟨w⟩ := GroundTheory.Global.nonempty_placesOver K v
  have hw : w.1.asIdeal.LiesOver v.asIdeal := inferInstance
  have hP : v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)) ≠ 0 :=
    fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)
  have hc : (v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K))).map (RingOfIntegers.mapRingEquiv (cE K)) =
      v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)) := by
    have : ((RingOfIntegers.mapRingEquiv (cE K) : 𝓞 K ≃+* 𝓞 K) : 𝓞 K →+* 𝓞 K).comp (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)) = algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) := by
      ext y
      exact (IsCMField.complexConj K).commutes (y : maximalRealSubfield K)
    rw [← Ideal.map_coe, Ideal.map_map, this]
  obtain ⟨b, t, hbt, ht⟩ := ideal_step (RingOfIntegers.mapRingEquiv (cE K)) _ I.1 a hP (nonZeroDivisors.ne_zero I.2) ha hc hI
  have htw : t ∉ w.1.asIdeal := ht _ w.1.isPrime (Ideal.map_le_iff_le_comap.2 hw.over.le)
  have ht0 : t ≠ 0 := fun h => htw (h ▸ zero_mem _)
  have hb0 : (b : K) ≠ 0 := by
    intro h
    have : b = 0 := by simpa using h
    rw [this, zero_mul] at hbt
    exact mul_ne_zero ha ht0 hbt.symm
  set n : (maximalRealSubfield K)ˣ := Units.map (Algebra.norm (maximalRealSubfield K)) (Units.mk0 (b : K) hb0) with hn
  have hy : algebraMap (maximalRealSubfield K) K ((n * x⁻¹ : (maximalRealSubfield K)ˣ) : maximalRealSubfield K) = (t : K) := by
    have h1 : algebraMap (maximalRealSubfield K) K n = (a : K) * t :=
      (norm_cm K b).trans (congrArg (fun z : 𝓞 K => (z : K)) hbt)
    rw [Units.val_mul, map_mul, h1, Units.val_inv_eq_inv_val, map_inv₀, ← hax]
    field_simp
  have hv : v.valuation (maximalRealSubfield K) ((n * x⁻¹ : (maximalRealSubfield K)ˣ) : maximalRealSubfield K) = 1 := by
    have h1 := HeightOneSpectrum.valuation_liesOver K v w.1 ((n * x⁻¹ : (maximalRealSubfield K)ˣ) : maximalRealSubfield K)
    rw [hy, (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := K) w.1).2 htw] at h1
    apply (pow_eq_one_iff.1 h1).resolve_right
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.1.asIdeal v.ne_bot]
    exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver _ v.ne_bot
  have h1 : GroundTheory.Global.IdeleGroup.finiteProj v (GroundTheory.Global.IdeleGroup.diagonal (maximalRealSubfield K) n) ∈
      (GroundTheory.Global.IdeleNorm.finiteLocalNorm K v).range := by
    rw [hn, ← GroundTheory.Global.ideleNorm_diagonal, GroundTheory.Global.IdeleNorm.finiteProj_ideleNorm]
    exact ⟨_, rfl⟩
  have h2 : GroundTheory.Global.IdeleGroup.finiteProj v (GroundTheory.Global.IdeleGroup.diagonal (maximalRealSubfield K) (n * x⁻¹)) ∈
      (GroundTheory.Global.IdeleNorm.finiteLocalNorm K v).range := by
    refine Subgroup.map_le_range _ (GroundTheory.Global.IdeleNorm.integerUnitsOver K v) ?_
    rw [GroundTheory.Global.IdeleNorm.map_integerUnitsOver_eq_of_ramificationIdx_eq_one v w (hunr w.1)]
    refine HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.2 ?_
    rw [GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans hv
  have h3 := mul_mem (inv_mem h2) h1
  rwa [← map_inv, ← map_inv, ← map_mul, ← map_mul, mul_inv_rev, inv_inv, inv_mul_cancel_right] at h3
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.LocInf
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

theorem UpperTheory.V.FW.locInf :
    ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (x : (maximalRealSubfield K)ˣ), (∀ φ : K →+* ℂ, 0 < (φ (algebraMap (maximalRealSubfield K) K x)).re) → ∀ v, GroundTheory.Global.IdeleGroup.infiniteProj v (GroundTheory.Global.IdeleGroup.diagonal (maximalRealSubfield K) x) ∈ (GroundTheory.Global.IdeleNorm.infiniteLocalNorm K v).range := by
  intro K _ _ _ x hx v
  classical
  obtain ⟨W, rfl⟩ := InfinitePlace.comap_surjective (k := maximalRealSubfield K) (K := K) v
  set u := W.comap (algebraMap (maximalRealSubfield K) K) with hu_def
  have hWu : W.LiesOver u := { under_eq := rfl }
  have hu : u.IsReal := IsTotallyReal.isReal u
  have hpos : 0 < InfinitePlace.Completion.ringEquivRealOfIsReal hu
      (algebraMap (maximalRealSubfield K) u.Completion (x : maximalRealSubfield K)) := by
    have h0 : InfinitePlace.Completion.ringEquivRealOfIsReal hu
        (algebraMap (maximalRealSubfield K) u.Completion (x : maximalRealSubfield K)) =
        InfinitePlace.embedding_of_isReal hu (x : maximalRealSubfield K) := by
      change InfinitePlace.Completion.extensionEmbeddingOfIsReal hu _ = _
      rw [InfinitePlace.Completion.algebraMap_apply]
      exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hu _
    rw [h0]
    have h1 := InfinitePlace.embedding_of_isReal_apply hu (x : maximalRealSubfield K)
    have h3 := hx W.embedding
    rcases InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq W u with h2 | h2
    · have h4 := congrArg (fun f => (f (x : maximalRealSubfield K)).re) h2
      simp only [RingHom.coe_comp, Function.comp_apply] at h4
      rw [h4, ← h1] at h3
      rwa [Complex.ofReal_re] at h3
    · have h4 := congrArg (fun f => (f (x : maximalRealSubfield K)).re) h2
      simp only [RingHom.coe_comp, Function.comp_apply, ComplexEmbedding.conjugate_coe_eq,
        Complex.conj_re] at h4
      rw [h4, ← h1] at h3
      rwa [Complex.ofReal_re] at h3
  letI : Algebra u.Completion W.Completion := AbsoluteValue.Completion.algebraOfLiesOver u.1 W.1
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hu with he
  set a := algebraMap (maximalRealSubfield K) u.Completion (x : maximalRealSubfield K) with ha
  set d := Module.finrank u.Completion W.Completion with hd_def
  have hd : 0 < d := by
    rcases W.isUnramified_or_isRamified (maximalRealSubfield K) with h | h
    · rw [hd_def, h.finrank_eq_one u]; norm_num
    · rw [hd_def, h.finrank_eq_two u]; norm_num
  set r : u.Completion := e.symm (e a ^ ((d : ℝ)⁻¹)) with hr_def
  have hr : r ^ d = a := by
    apply e.injective
    rw [map_pow, hr_def, RingEquiv.apply_symm_apply, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le,
      inv_mul_cancel₀ (by exact_mod_cast hd.ne'), Real.rpow_one]
  have ha0 : a ≠ 0 := by
    rw [ha]
    exact (map_ne_zero _).mpr x.ne_zero
  have hr0 : algebraMap u.Completion W.Completion r ≠ 0 := by
    rw [map_ne_zero]
    rintro h0
    rw [h0, zero_pow hd.ne'] at hr
    exact ha0 hr.symm
  let w0 : ↑(InfinitePlace.placesOver K u) := ⟨W, hWu⟩
  refine ⟨Pi.mulSingle w0 (Units.mk0 _ hr0), ?_⟩
  apply Units.ext
  simp only [GroundTheory.Global.IdeleNorm.infiniteLocalNorm, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [Fintype.prod_eq_single w0 (fun w hw => by rw [Pi.mulSingle_eq_of_ne hw, map_one]),
    Pi.mulSingle_eq_same, Units.coe_map, Units.val_mk0]
  rw [GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal]
  rw [← InfinitePlace.Completion.algebraMap_apply]
  change Algebra.norm u.Completion (algebraMap u.Completion W.Completion r) = a
  rw [Algebra.norm_algebraMap, ← hd_def, hr]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.ClassGroupDivMemOfMulConjEq
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem quotient_mem_of_norm_eq_involution {M C : Type} [CommMonoidWithZero M] [UniqueFactorizationMonoid M] [Subsingleton Mˣ]
    [CommGroup C] (σ : M ≃* M) (hσ : ∀ x, σ (σ x) = x) (H : Subgroup C) (f : M → C)
    (hf : ∀ a b, a ≠ 0 → b ≠ 0 → f (a * b) = f a * f b) (hH : ∀ a, a ≠ 0 → f a / f (σ a) ∈ H) (I : M) :
    I ≠ 0 → ∀ J : M, J ≠ 0 → I * σ I = J * σ J → f I / f J ∈ H := by
  refine UniqueFactorizationMonoid.induction_on_prime
    (P := fun I => I ≠ 0 → ∀ J : M, J ≠ 0 → I * σ I = J * σ J → f I / f J ∈ H) I ?_ ?_ ?_
  · intro h
    exact absurd rfl h
  · intro x hx _ J _ hxJ
    rw [isUnit_iff_eq_one] at hx
    subst hx
    rw [map_one, mul_one] at hxJ
    have hJ1 : J = 1 := isUnit_iff_eq_one.mp (Units.mkOfMulEqOne J (σ J) hxJ.symm).isUnit
    subst hJ1
    rw [div_self']
    exact H.one_mem
  · intro a p ha hp ih _ J hJ hE
    have h0 : σ 0 = 0 := by
      have h := map_mul σ 0 (σ.symm 0)
      rwa [zero_mul, MulEquiv.apply_symm_apply, mul_zero] at h
    have hne : ∀ x : M, x ≠ 0 → σ x ≠ 0 := by
      intro x hx h
      apply hx
      rw [← hσ x, h, h0]
    have hp0 : p ≠ 0 := hp.ne_zero
    have hsp0 := hne p hp0
    have hd : p ∣ J * σ J := hE ▸ dvd_mul_of_dvd_left (dvd_mul_right p a) _
    rw [map_mul] at hE
    rcases hp.dvd_or_dvd hd with ⟨J₀, rfl⟩ | ⟨K₀, hK⟩
    · have hJ0 : J₀ ≠ 0 := right_ne_zero_of_mul hJ
      rw [map_mul] at hE
      have e1 : (p * σ p) * (a * σ a) = (p * σ p) * (J₀ * σ J₀) := by
        simpa only [mul_comm, mul_assoc, mul_left_comm] using hE
      have e2 := mul_left_cancel₀ (mul_ne_zero hp0 hsp0) e1
      rw [hf p a hp0 ha, hf p J₀ hp0 hJ0, mul_div_mul_left_eq_div]
      exact ih ha J₀ hJ0 e2
    · have hsJ := hne J hJ
      have hK0 : K₀ ≠ 0 := by
        rw [hK] at hsJ
        exact right_ne_zero_of_mul hsJ
      have hsK0 := hne K₀ hK0
      have hJ' : J = σ p * σ K₀ := by rw [← hσ J, hK, map_mul]
      rw [hK, hJ'] at hE
      have e1 : (p * σ p) * (a * σ a) = (p * σ p) * (K₀ * σ K₀) := by
        simpa only [mul_comm, mul_assoc, mul_left_comm] using hE
      have e2 := mul_left_cancel₀ (mul_ne_zero hp0 hsp0) e1
      have key := H.mul_mem (hH p hp0) (H.mul_mem (ih ha K₀ hK0 e2) (hH K₀ hK0))
      rw [div_mul_div_cancel, div_mul_div_comm] at key
      rw [hJ', hf p a hp0 ha, hf (σ p) (σ K₀) hsp0 hsK0]
      exact key

theorem UpperTheory.V.FW.classGroup_div_mem_of_mul_conj_eq :
    ∀ (K : Type) [Field K] [NumberField K] (τ : K ≃+* K) (I J : (Ideal (𝓞 K))⁰), (∀ x, τ (τ x) = x) → I * idMap τ I = J * idMap τ J → ClassGroup.mk0 I / ClassGroup.mk0 J ∈ difR (clMap τ) := by
  intro K _ _ τ I J hτ hIJ
  classical
  have hee : ∀ x : 𝓞 K, RingOfIntegers.mapRingEquiv τ (RingOfIntegers.mapRingEquiv τ x) = x :=
    fun x => RingOfIntegers.ext (hτ x)
  have hmap : ∀ I : Ideal (𝓞 K), Ideal.map (RingOfIntegers.mapRingEquiv τ)
      (Ideal.map (RingOfIntegers.mapRingEquiv τ) I) = I := by
    intro I
    show Ideal.map (RingOfIntegers.mapRingEquiv τ : 𝓞 K →+* 𝓞 K)
      (Ideal.map (RingOfIntegers.mapRingEquiv τ : 𝓞 K →+* 𝓞 K) I) = I
    rw [Ideal.map_map]
    convert Ideal.map_id I
    exact RingHom.ext fun x => hee x
  let σ : Ideal (𝓞 K) ≃* Ideal (𝓞 K) :=
    { toFun := Ideal.map (RingOfIntegers.mapRingEquiv τ)
      invFun := Ideal.map (RingOfIntegers.mapRingEquiv τ)
      left_inv := hmap
      right_inv := hmap
      map_mul' := Ideal.map_mul (RingOfIntegers.mapRingEquiv τ) }
  let f : Ideal (𝓞 K) → ClassGroup (𝓞 K) := fun a =>
    if h : a ∈ (Ideal (𝓞 K))⁰ then ClassGroup.mk0 ⟨a, h⟩ else 1
  have hfv : ∀ a (h : a ∈ (Ideal (𝓞 K))⁰), f a = ClassGroup.mk0 ⟨a, h⟩ := fun a h => dif_pos h
  have hf : ∀ a b, a ≠ 0 → b ≠ 0 → f (a * b) = f a * f b := by
    intro a b ha hb
    have ha' := mem_nonZeroDivisors_of_ne_zero ha
    have hb' := mem_nonZeroDivisors_of_ne_zero hb
    rw [hfv a ha', hfv b hb', hfv (a * b) (Submonoid.mul_mem _ ha' hb'), ← map_mul]
    rfl
  have hH : ∀ a, a ≠ 0 → f a / f (σ a) ∈ difR (clMap τ) := by
    intro a ha
    have ha' := mem_nonZeroDivisors_of_ne_zero ha
    have hs' : σ a ∈ (Ideal (𝓞 K))⁰ := (idMap τ ⟨a, ha'⟩).2
    rw [hfv a ha', hfv _ hs']
    refine ⟨ClassGroup.mk0 ⟨a, ha'⟩, ?_⟩
    rw [MonoidHom.div_apply, MonoidHom.id_apply, class_map_mk0]
    rfl
  have key := quotient_mem_of_norm_eq_involution σ (fun x => hmap x) (difR (clMap τ)) f hf hH (I : Ideal (𝓞 K))
    (nonZeroDivisors.coe_ne_zero I) J (nonZeroDivisors.coe_ne_zero J) (congrArg Subtype.val hIJ)
  rwa [hfv _ I.2, hfv _ J.2] at key
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem norm_eq_mul_cE (K : Type) [Field K] [NumberField K] [IsCMField K] (y : K) :
    algebraMap (maximalRealSubfield K) K (Algebra.norm (maximalRealSubfield K) y) = y * cE K y :=
  _root_.UpperTheory.Reformulated.B.Qh29.norm_eq_mul_cE K y

private def prI {K : Type} [Field K] [NumberField K] (b : 𝓞 K) (hb : b ≠ 0) : (Ideal (𝓞 K))⁰ :=
  ⟨Ideal.span {b}, mem_nonZeroDivisors_of_ne_zero (by simpa using hb)⟩

private theorem mk0_principal_eq_one {K : Type} [Field K] [NumberField K] (b : 𝓞 K) (hb : b ≠ 0) :
    ClassGroup.mk0 (prI b hb) = 1 :=
  (ClassGroup.mk0_eq_one_iff _).2 ⟨⟨b, rfl⟩⟩

private theorem prI_mul {K : Type} [Field K] [NumberField K] (τ : K ≃+* K) (b : 𝓞 K) (hb : b ≠ 0) :
    (prI b hb * idMap τ (prI b hb)).1 = Ideal.span {b * RingOfIntegers.mapRingEquiv τ b} := by
  change Ideal.span {b} * (Ideal.span {b}).map (RingOfIntegers.mapRingEquiv τ) = _
  rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_mul_span_singleton]

theorem UpperTheory.V.FW.hasse :
    ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (a : 𝓞 K) (I : (Ideal (𝓞 K))⁰), UnrFin K → cE K (a : K) = a → (∀ φ : K →+* ℂ, 0 < (φ (a : K)).re) → (I * idMap (cE K) I).1 = Ideal.span {a} → ClassGroup.mk0 I ∈ difR (clMap (cE K)) := by
  intro K _ _ _ a I hU ha hpos hI
  have ha0 : a ≠ 0 := by
    intro h
    have := nonZeroDivisors.ne_zero (I * idMap (cE K) I).2
    rw [hI, h] at this
    simp at this
  have ha0' : (a : K) ≠ 0 := by simpa using ha0
  have hmem : (a : K) ∈ maximalRealSubfield K := (IsCMField.complexConj_eq_self_iff K _).1 ha
  have hx0 : (⟨a, hmem⟩ : maximalRealSubfield K) ≠ 0 := fun h => ha0' (congrArg Subtype.val h)
  have hax : (a : K) = algebraMap (maximalRealSubfield K) K (Units.mk0 _ hx0 : (maximalRealSubfield K)ˣ) := rfl
  obtain ⟨β, hβ⟩ := (GroundTheory.Global.mem_range_norm_iff_forall_local_of_finrank_eq_two (L := K)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (Units.mk0 _ hx0)).2
    ⟨locFin K _ a I hU hax hI, locInf K _ fun φ => hax ▸ hpos φ⟩
  have hβ' : (β : K) * cE K β = a := by
    rw [← norm_eq_mul_cE, hax, ← hβ]
    rfl
  obtain ⟨b, d, hd, hbd⟩ := IsFractionRing.div_surjective (A := 𝓞 K) (β : K)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hd0' : (d : K) ≠ 0 := by simpa using hd0
  have hb : (b : K) = d * β := by
    rw [← hbd]
    exact (mul_div_cancel₀ _ hd0').symm
  have hb0 : b ≠ 0 := by
    intro h
    rw [h] at hb
    exact mul_ne_zero hd0' β.ne_zero (by simpa using hb.symm)
  have key : d * RingOfIntegers.mapRingEquiv (cE K) d * a = b * RingOfIntegers.mapRingEquiv (cE K) b := by
    apply Subtype.ext
    change (d : K) * cE K d * a = (b : K) * cE K b
    rw [hb, map_mul, ← hβ']
    ring
  have := classGroup_div_mem_of_mul_conj_eq K (cE K) (prI d hd0 * I) (prI b hb0) (IsCMField.complexConj_apply_apply K) (by
    apply Subtype.ext
    rw [map_mul, mul_mul_mul_comm, Submonoid.coe_mul, hI, prI_mul, prI_mul,
      Ideal.span_singleton_mul_span_singleton, key])
  rwa [map_mul, mk0_principal_eq_one, mk0_principal_eq_one, one_mul, div_one] at this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.RealGen
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem real_eq_one_of_nonneg_of_mul_self_eq_one (x : ℝ) (h0 : 0 ≤ x) (h : x * x = 1) : x = 1 := by
  nlinarith

theorem UpperTheory.V.FW.realGen :
    ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (x : Cl K), Function.Surjective (IsCMField.unitsMulComplexConjInv K) → x ∈ minK (clMap (cE K)) → ∃ (I : (Ideal (𝓞 K))⁰) (a : 𝓞 K), ClassGroup.mk0 I = x ∧ a ≠ 0 ∧ cE K (a : K) = a ∧ (I * idMap (cE K) I).1 = Ideal.span {a} := by
  intro K _ _ _ x hsurj hx
  set σ := RingOfIntegers.mapRingEquiv (cE K) with hσdef
  have hσK : ∀ y : 𝓞 K, ((σ y : 𝓞 K) : K) = cE K (y : K) := fun y => rfl
  have hσσ : ∀ y : 𝓞 K, σ (σ y) = y := fun y => by
    apply RingOfIntegers.ext
    rw [hσK, hσK]
    exact IsCMField.complexConj_apply_apply K (y : K)
  have hw : ∀ (w : InfinitePlace K) (y : 𝓞 K), w (σ y : K) = w (y : K) := fun w y =>
    IsCMField.infinitePlace_complexConj K w (y : K)
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective x
  set J := idMap (cE K) I with hJdef
  have hJ : (J : Ideal (𝓞 K)) = Ideal.map σ (I : Ideal (𝓞 K)) := rfl
  have hmapmap : ∀ A : Ideal (𝓞 K), Ideal.map σ (Ideal.map σ A) = A := by
    intro A
    show Ideal.map (σ : 𝓞 K →+* 𝓞 K) (Ideal.map (σ : 𝓞 K →+* 𝓞 K) A) = A
    rw [Ideal.map_map]
    have : (σ : 𝓞 K →+* 𝓞 K).comp (σ : 𝓞 K →+* 𝓞 K) = RingHom.id _ :=
      RingHom.ext fun y => hσσ y
    rw [this, Ideal.map_id]
  have hJJ : Ideal.map σ (J : Ideal (𝓞 K)) = I := by
    rw [hJ, hmapmap]
  have hprin : Submodule.IsPrincipal ((I * J : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) := by
    rw [← ClassGroup.mk0_eq_one_iff (I * J).2]
    have := hx
    simp only [minK, MonoidHom.mem_ker, MonoidHom.mul_apply, class_map_mk0, MonoidHom.id_apply] at this
    rw [← map_mul, mul_comm] at this
    exact this
  obtain ⟨b, hb⟩ := hprin
  have hb' : ((I * J : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = Ideal.span {b} := hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl] at hb'
    exact nonZeroDivisors.coe_ne_zero (I * J) hb'
  have hspan : Ideal.span {σ b} = Ideal.span {b} := by
    rw [← Set.image_singleton, ← Ideal.map_span, ← hb', Submonoid.coe_mul, Ideal.map_mul, ← hJ,
      hJJ, mul_comm]
  obtain ⟨t, ht⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  have hσt : σ (t : 𝓞 K) * t = 1 := by
    have h1 := congrArg σ ht
    rw [map_mul, hσσ] at h1
    have : b * (σ t * t) = b * 1 := by
      rw [← mul_assoc, h1, ht, mul_one]
    exact mul_left_cancel₀ hb0 this
  have htor : t⁻¹ ∈ Units.torsion K := by
    refine inv_mem ?_
    rw [Units.mem_torsion]
    intro w
    show w ((t : 𝓞 K) : K) = 1
    have hK : ((σ t : 𝓞 K) : K) * ((t : 𝓞 K) : K) = 1 := by
      exact_mod_cast congrArg (fun y : 𝓞 K => (y : K)) hσt
    have hprod := congrArg w hK
    rw [map_mul, map_one, hw] at hprod
    exact real_eq_one_of_nonneg_of_mul_self_eq_one _ (AbsoluteValue.nonneg _ _) hprod
  obtain ⟨v, hv⟩ := hsurj ⟨t⁻¹, htor⟩
  have hv2 : v * ((IsCMField.unitsComplexConj K) v)⁻¹ = t⁻¹ := by
    have hv1 := congrArg Subtype.val hv
    rw [IsCMField.unitsMulComplexConjInv_apply] at hv1
    exact hv1
  rw [mul_inv_eq_iff_eq_mul] at hv2
  have hv' : (v : 𝓞 K) = ((t⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * σ v := by
    have h3 := congrArg Units.val hv2
    rw [Units.val_mul] at h3
    exact h3
  have hσb : σ b = b * ((t⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by
    calc σ b = σ b * t * ((t⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by rw [mul_assoc, Units.mul_inv, mul_one]
      _ = b * ((t⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by rw [ht]
  refine ⟨I, b * v, rfl, mul_ne_zero hb0 v.ne_zero, ?_, ?_⟩
  · rw [← hσK]
    congr 1
    rw [map_mul, hσb, mul_assoc, ← hv']
  · rw [Ideal.span_singleton_mul_right_unit v.isUnit]
    exact hb'
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

section

variable {K : Type} [Field K] [NumberField K] [IsCMField K] {ι : Type}

private theorem hMinus_im (φ : K →+* ℂ) {a : K} (ha : cE K a = a) : (φ a).im = 0 := by
  have h := IsCMField.complexEmbedding_complexConj K φ a
  have h2 : IsCMField.complexConj K a = a := ha
  rw [h2] at h
  exact Complex.conj_eq_iff_im.1 h.symm

private theorem hMinus_re (φ : K →+* ℂ) {a : K} (ha : cE K a = a) (h0 : a ≠ 0) : (φ a).re ≠ 0 := by
  intro hre
  apply h0
  have h : φ a = 0 := Complex.ext hre (hMinus_im φ ha)
  exact φ.injective (by rw [h, map_zero])

private theorem hMinus_mul (e : ι → K →+* ℂ) {a b : K} (ha : cE K a = a) (ha0 : a ≠ 0) (hb : cE K b = b) (hb0 : b ≠ 0) :
    sgn e (a * b) = sgn e a + sgn e b := by
  funext i
  simp only [sgn, Pi.add_apply, map_mul, Complex.mul_re, hMinus_im (e i) ha, hMinus_im (e i) hb,
    mul_zero, sub_zero]
  have h1 := hMinus_re (e i) ha ha0
  have h2 := hMinus_re (e i) hb hb0
  rcases h1.lt_or_gt with p | p <;> rcases h2.lt_or_gt with q | q
  · rw [if_neg (not_lt.mpr (mul_pos_of_neg_of_neg p q).le), if_pos p, if_pos q]
    decide
  · rw [if_pos (mul_neg_of_neg_of_pos p q), if_pos p, if_neg (not_lt.mpr q.le)]
    decide
  · rw [if_pos (mul_neg_of_pos_of_neg p q), if_neg (not_lt.mpr p.le), if_pos q]
    decide
  · rw [if_neg (not_lt.mpr (mul_pos p q).le), if_neg (not_lt.mpr p.le), if_neg (not_lt.mpr q.le)]
    decide

private theorem hMinus_neg (f : ι → ZMod 2) : -f = f := by
  funext i
  exact ZMod.neg_eq_self_mod_two _

private theorem hMinus_ne (u : (𝓞 K)ˣ) : ((u : 𝓞 K) : K) ≠ 0 := by
  intro h
  apply u.ne_zero
  exact RingOfIntegers.ext (h.trans (by simp))

private theorem hMinus_unit (e : ι → K →+* ℂ) {f : ι → ZMod 2} (hf : f ∈ sgnE e) :
    ∃ u : (𝓞 K)ˣ, cE K ((u : 𝓞 K) : K) = ((u : 𝓞 K) : K) ∧ f = sgn e ((u : 𝓞 K) : K) := by
  unfold sgnE at hf
  induction hf using AddSubgroup.closure_induction with
  | mem x hx => exact hx
  | zero =>
    refine ⟨1, by simp, ?_⟩
    funext i
    simp [sgn]
  | add x y _ _ hx hy =>
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    refine ⟨u * v, ?_, ?_⟩
    · push_cast
      rw [map_mul, hu, hv]
    · push_cast
      rw [hMinus_mul e hu (hMinus_ne u) hv (hMinus_ne v)]
  | neg x _ hx =>
    rwa [hMinus_neg]

private theorem hMinus_pos (e : ι → K →+* ℂ) (he : Function.Surjective e) {a : K} (ha : cE K a = a) (h0 : a ≠ 0)
    (h : sgn e a = 0) (φ : K →+* ℂ) : 0 < (φ a).re := by
  obtain ⟨i, rfl⟩ := he φ
  have hi := congr_fun h i
  simp only [sgn, Pi.zero_apply] at hi
  split_ifs at hi with hlt
  · exact absurd hi (by decide)
  · exact lt_of_le_of_ne (not_lt.mp hlt) (hMinus_re (e i) ha h0).symm

end

private theorem idMap_complexConj_involutive {K : Type} [Field K] [NumberField K] [IsCMField K] (I : ↥(Ideal (𝓞 K))⁰) :
    idMap (cE K) (idMap (cE K) I) = I := by
  apply Subtype.ext
  show Ideal.map (RingOfIntegers.mapRingEquiv (cE K))
    (Ideal.map (RingOfIntegers.mapRingEquiv (cE K)) (I : Ideal (𝓞 K))) = I
  have hs : (RingOfIntegers.mapRingEquiv (cE K)).symm = RingOfIntegers.mapRingEquiv (cE K) := by
    ext x
    simp only [cE, RingOfIntegers.mapRingEquiv_symm_apply, RingOfIntegers.mapRingEquiv_apply]
    simp
    rw [AlgEquiv.symm_apply_eq, IsCMField.complexConj_apply_apply]
  have h := Ideal.map_of_equiv (I := (I : Ideal (𝓞 K))) (RingOfIntegers.mapRingEquiv (cE K))
  rw [hs] at h
  exact h

private theorem classGroup_inv_mul_mem_difR_of_sign {K : Type} [Field K] [NumberField K] [IsCMField K] {ι : Type} (e : ι → K →+* ℂ)
    (hU : UnrFin K) (he : Function.Surjective e) (I J : ↥(Ideal (𝓞 K))⁰) (a b : 𝓞 K) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (har : cE K (a : K) = a) (hbr : cE K (b : K) = b)
    (hIa : ((I * idMap (cE K) I : ↥(Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = Ideal.span {a})
    (hJb : ((J * idMap (cE K) J : ↥(Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = Ideal.span {b})
    (hx : ClassGroup.mk0 I ∈ minK (clMap (cE K))) (hs : sgn e (a : K) + sgn e (b : K) ∈ sgnE e) :
    (ClassGroup.mk0 I)⁻¹ * ClassGroup.mk0 J ∈ difR (clMap (cE K)) := by
  obtain ⟨u, hu, hsu⟩ := hMinus_unit e hs
  have ha0' : (a : K) ≠ 0 := fun h => ha0 (RingOfIntegers.ext (h.trans (by simp)))
  have hb0' : (b : K) ≠ 0 := fun h => hb0 (RingOfIntegers.ext (h.trans (by simp)))
  have habr : cE K ((a : K) * b) = (a : K) * b := by rw [map_mul, har, hbr]
  have hab0 : (a : K) * b ≠ 0 := mul_ne_zero ha0' hb0'
  have hcr : cE K (((a * b * (u : 𝓞 K) : 𝓞 K)) : K) = ((a * b * (u : 𝓞 K) : 𝓞 K) : K) := by
    push_cast
    rw [map_mul, habr, hu]
  have hc0 : (((a * b * (u : 𝓞 K) : 𝓞 K)) : K) ≠ 0 := by
    push_cast
    exact mul_ne_zero hab0 (hMinus_ne u)
  have hcs : sgn e (((a * b * (u : 𝓞 K) : 𝓞 K)) : K) = 0 := by
    have e1 : (((a * b * (u : 𝓞 K) : 𝓞 K)) : K) = (a : K) * b * ((u : 𝓞 K) : K) := by push_cast; rfl
    rw [e1, hMinus_mul e habr hab0 hu (hMinus_ne u), hMinus_mul e har ha0' hbr hb0', hsu]
    calc sgn e ((u : 𝓞 K) : K) + sgn e ((u : 𝓞 K) : K)
        = -sgn e ((u : 𝓞 K) : K) + sgn e ((u : 𝓞 K) : K) := by rw [hMinus_neg]
      _ = 0 := neg_add_cancel _
  have hpos : ∀ φ : K →+* ℂ, 0 < (φ (((a * b * (u : 𝓞 K) : 𝓞 K)) : K)).re :=
    hMinus_pos e he hcr hc0 hcs
  have hL : ((idMap (cE K) I * J) * idMap (cE K) (idMap (cE K) I * J) : ↥(Ideal (𝓞 K))⁰) =
      (I * idMap (cE K) I) * (J * idMap (cE K) J) := by
    rw [map_mul, idMap_complexConj_involutive]
    ac_rfl
  have hLs : (((idMap (cE K) I * J) * idMap (cE K) (idMap (cE K) I * J) : ↥(Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) =
      Ideal.span {a * b * (u : 𝓞 K)} := by
    rw [hL, Submonoid.coe_mul, hIa, hJb, Ideal.span_singleton_mul_span_singleton,
      Ideal.span_singleton_mul_right_unit u.isUnit]
  have hmem := hasse K (a * b * (u : 𝓞 K)) (idMap (cE K) I * J) hU hcr hpos hLs
  have hinv : clMap (cE K) (ClassGroup.mk0 I) = (ClassGroup.mk0 I)⁻¹ := by
    rw [MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.id_apply] at hx
    exact eq_inv_of_mul_eq_one_left hx
  rwa [map_mul, ← class_map_mk0, hinv] at hmem

theorem UpperTheory.V.FW.hMinus :
    ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (ι : Type) [Finite ι] (e : ι → K →+* ℂ) (V : AddSubgroup (ι → ZMod 2)), UnrFin K → Function.Surjective (IsCMField.unitsMulComplexConjInv K) → Function.Surjective e → (∀ a : K, cE K a = a → sgn e a ∈ V) → (difR (clMap (cE K))).relIndex (minK (clMap (cE K))) ≤ (sgnE e).relIndex V := by
  intro K _ _ _ ι _ e V hU hsurj he hV
  have hx : ∀ x : minK (clMap (cE K)), ∃ (I : ↥(Ideal (𝓞 K))⁰) (a : 𝓞 K),
      ClassGroup.mk0 I = (x : ClassGroup (𝓞 K)) ∧ a ≠ 0 ∧ cE K (a : K) = a ∧
      ((I * idMap (cE K) I : ↥(Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = Ideal.span {a} :=
    fun x => realGen K x hsurj x.2
  choose I a hI ha0 har hIa using hx
  let g : minK (clMap (cE K)) → V := fun x => ⟨sgn e (a x : K), hV _ (har x)⟩
  let F : minK (clMap (cE K)) ⧸ (difR (clMap (cE K))).subgroupOf (minK (clMap (cE K))) →
      V ⧸ (sgnE e).addSubgroupOf V := fun c => ((g c.out : V) : V ⧸ (sgnE e).addSubgroupOf V)
  have hinj : Function.Injective F := by
    intro c d hcd
    rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' d, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 := QuotientAddGroup.eq.mp hcd
    rw [AddSubgroup.mem_addSubgroupOf] at h1
    have h2 : sgn e (a c.out : K) + sgn e (a d.out : K) ∈ sgnE e := by
      have e2 : ((-g c.out + g d.out : V) : ι → ZMod 2) = -sgn e (a c.out : K) + sgn e (a d.out : K) := rfl
      rw [e2, hMinus_neg] at h1
      exact h1
    have hm : ClassGroup.mk0 (I c.out) ∈ minK (clMap (cE K)) := by
      rw [hI c.out]
      exact c.out.2
    have key := classGroup_inv_mul_mem_difR_of_sign e hU he (I c.out) (I d.out) (a c.out) (a d.out) (ha0 _) (ha0 _) (har _) (har _)
      (hIa _) (hIa _) hm h2
    rw [hI, hI] at key
    simpa using key
  show ((difR (clMap (cE K))).subgroupOf (minK (clMap (cE K)))).index ≤ ((sgnE e).addSubgroupOf V).index
  exact Nat.card_le_card_of_injective F hinj
