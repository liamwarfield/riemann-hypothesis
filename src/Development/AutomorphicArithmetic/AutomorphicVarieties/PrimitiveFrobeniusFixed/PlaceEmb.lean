module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.XEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.AlgStep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.XNormDiv
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

section Tower

variable {M N : ℕ} [NeZero M] [NeZero N] {K K' : Type} [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K]
  [Field K'] [NumberField K'] [IsCyclotomicExtension {N} ℚ K'] [Algebra K K']

end Tower

section One

variable {M : ℕ} [NeZero M] {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K]

end One

private theorem algebraMap_sgO_eq_sg_algebraMap (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (t : (ZMod M)ˣ) (x : 𝓞 K) :
    algebraMap (𝓞 K) K (sgO M K t x) = sg M K t (algebraMap (𝓞 K) K x) := by
  unfold sgO
  rfl

private theorem sgO_mul_apply (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (a b : (ZMod M)ˣ) (x : 𝓞 K) :
    sgO M K (a * b) x = sgO M K a (sgO M K b x) := by
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  rw [algebraMap_sgO_eq_sg_algebraMap, algebraMap_sgO_eq_sg_algebraMap, algebraMap_sgO_eq_sg_algebraMap, map_mul, AlgEquiv.mul_apply]

private theorem sgO_symm_apply_eq_sgO_inv (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (a : (ZMod M)ˣ) (x : 𝓞 K) :
    (sgO M K a).symm x = sgO M K a⁻¹ x := by
  rw [RingEquiv.symm_apply_eq, ← sgO_mul_apply, mul_inv_cancel]
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  rw [algebraMap_sgO_eq_sg_algebraMap, map_one, AlgEquiv.one_apply]

private theorem map_sgO_conjI_eq_conjI_mul_inv (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (𝔞 : Ideal (𝓞 K)) (s t : (ZMod M)ˣ) :
    Ideal.map ((sgO M K s : 𝓞 K ≃+* 𝓞 K) : 𝓞 K →+* 𝓞 K) (conjI M K 𝔞 t) = conjI M K 𝔞 (t * s⁻¹) := by
  unfold conjI
  rw [Ideal.map_comap_of_equiv]
  ext x
  rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap, sgO_symm_apply_eq_sgO_inv, sgO_mul_apply]

private theorem spanSingleton_sg_eq_prod_conjI_pow_th_mul_of_eq_prod (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (b : ℕ) (𝔞 : Ideal (𝓞 K)) (X : K)
    (hX : FractionalIdeal.spanSingleton (𝓞 K)⁰ X = ∏ t, ((conjI M K 𝔞 t : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ^ th M b ↑t)
    (s : (ZMod M)ˣ) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (sg M K s X) = ∏ t, ((conjI M K 𝔞 t : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ^ th M b ↑(t * s) := by
  let f : 𝓞 K →+* 𝓞 K := ((sgO M K s : 𝓞 K ≃+* 𝓞 K) : 𝓞 K →+* 𝓞 K)
  have hf : (𝓞 K)⁰ ≤ Submonoid.comap f (𝓞 K)⁰ :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (sgO M K s).injective
  have key : IsLocalization.map K f hf = ((sg M K s : K ≃ₐ[ℚ] K) : K →+* K) := by
    apply IsLocalization.ringHom_ext (𝓞 K)⁰
    ext x
    simp only [RingHom.comp_apply, IsLocalization.map_eq]
    exact algebraMap_sgO_eq_sg_algebraMap M K s x
  have h := congrArg (FractionalIdeal.extendedHom' K hf) hX
  rw [FractionalIdeal.extendedHom'_apply, FractionalIdeal.extended_spanSingleton, key, map_prod] at h
  rw [show (sg M K s) X = ((sg M K s : K ≃ₐ[ℚ] K) : K →+* K) X from rfl, h]
  refine Fintype.prod_equiv (Equiv.mulRight s⁻¹) _ _ (fun t => ?_)
  rw [map_zpow₀, FractionalIdeal.extendedHom'_apply, FractionalIdeal.extended_coeIdeal_eq_map,
    Equiv.coe_mulRight, inv_mul_cancel_right]
  beta_reduce
  dsimp only [f]
  rw [map_sgO_conjI_eq_conjI_mul_inv]

private theorem sg_algebraMap_eq_algebraMap_sg_unitsMap (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K'] (t : (ZMod (q * M))ˣ) (x : K) :
    sg (q * M) K' t (algebraMap K K' x) = algebraMap K K' (sg M K (ZMod.unitsMap (dvd_mul_left M q) t) x) := by
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {M} ℚ K
  have h := IsCyclotomicExtension.Rat.galEquivZMod_restrictNormal_apply (q * M) K' K (dvd_mul_left M q) (sg (q * M) K' t)
  have e2 : (sg (q * M) K' t).restrictNormal K = sg M K (ZMod.unitsMap (dvd_mul_left M q) t) := by
    unfold sg at h ⊢
    rw [MulEquiv.apply_symm_apply] at h
    rw [← h, MulEquiv.symm_apply_apply]
  rw [← AlgEquiv.restrictNormal_commutes, e2]

private theorem cyclotomic_rat_algEquiv_apply_comm (N : ℕ) [NeZero N] (K' : Type) [Field K'] [NumberField K'] [IsCyclotomicExtension {N} ℚ K'] (a b : K' ≃ₐ[ℚ] K') (y : K') :
    a (b y) = b (a y) := by
  have hab : a * b = b * a :=
    (IsCyclotomicExtension.Rat.galEquivZMod N K').injective (by rw [map_mul, map_mul, mul_comm])
  rw [← AlgEquiv.mul_apply, hab, AlgEquiv.mul_apply]

private theorem norm_sg_eq_sg_unitsMap_norm (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K'] (t : (ZMod (q * M))ˣ) (y : K') :
    Algebra.norm K (sg (q * M) K' t y) = sg M K (ZMod.unitsMap (dvd_mul_left M q) t) (Algebra.norm K y) := by
  haveI : IsGalois ℚ K' := IsCyclotomicExtension.isGalois {q * M} ℚ K'
  haveI : IsGalois K K' := IsGalois.tower_top_of_isGalois ℚ K K'
  apply (algebraMap K K').injective
  rw [← sg_algebraMap_eq_algebraMap_sg_unitsMap, Algebra.norm_eq_prod_automorphisms, Algebra.norm_eq_prod_automorphisms, map_prod]
  refine Finset.prod_congr rfl fun σ _ => ?_
  exact cyclotomic_rat_algEquiv_apply_comm (q * M) K' (σ.restrictScalars ℚ) (sg (q * M) K' t) y

private theorem algebraMap_norm_eq_prod_sg_ker_unitsMap (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K'] (y : K') :
    algebraMap K K' (Algebra.norm K y) =
      ∏ k ∈ Finset.univ.filter (fun k : (ZMod (q * M))ˣ => ZMod.unitsMap (dvd_mul_left M q) k = 1), sg (q * M) K' k y := by
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {M} ℚ K
  haveI : IsGalois ℚ K' := IsCyclotomicExtension.isGalois {q * M} ℚ K'
  haveI : IsGalois K K' := IsGalois.tower_top_of_isGalois ℚ K K'
  rw [Algebra.norm_eq_prod_automorphisms]
  refine Finset.prod_bij (fun σ _ => IsCyclotomicExtension.Rat.galEquivZMod (q * M) K' (σ.restrictScalars ℚ))
    ?_ ?_ ?_ ?_
  · intro σ _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← IsCyclotomicExtension.Rat.galEquivZMod_restrictNormal_apply (q * M) K' K (dvd_mul_left M q)]
    have h1 : (σ.restrictScalars ℚ).restrictNormal K = 1 := by
      ext x
      apply (algebraMap K K').injective
      rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.one_apply]
      exact σ.commutes x
    rw [h1, map_one]
  · intro σ₁ _ σ₂ _ h
    exact AlgEquiv.restrictScalars_injective ℚ ((IsCyclotomicExtension.Rat.galEquivZMod (q * M) K').injective h)
  · intro k hk
    rw [Finset.mem_filter] at hk
    let σ : K' ≃ₐ[K] K' := AlgEquiv.ofRingEquiv (f := (sg (q * M) K' k).toRingEquiv) (fun x => by
      change sg (q * M) K' k (algebraMap K K' x) = algebraMap K K' x
      rw [sg_algebraMap_eq_algebraMap_sg_unitsMap, hk.2, map_one, AlgEquiv.one_apply])
    refine ⟨σ, Finset.mem_univ _, ?_⟩
    have hσ : σ.restrictScalars ℚ = sg (q * M) K' k := by
      ext x
      rfl
    rw [hσ]
    unfold sg
    exact MulEquiv.apply_symm_apply _ _
  · intro σ _
    change σ y = sg (q * M) K' (IsCyclotomicExtension.Rat.galEquivZMod (q * M) K' (σ.restrictScalars ℚ)) y
    unfold sg
    rw [MulEquiv.symm_apply_apply]
    rfl

private theorem sgO_algebraMap_eq_algebraMap_sgO_unitsMap (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K'] (t : (ZMod (q * M))ˣ) (x : 𝓞 K) :
    sgO (q * M) K' t (algebraMap (𝓞 K) (𝓞 K') x) = algebraMap (𝓞 K) (𝓞 K') (sgO M K (ZMod.unitsMap (dvd_mul_left M q) t) x) := by
  apply FaithfulSMul.algebraMap_injective (𝓞 K') K'
  rw [algebraMap_sgO_eq_sg_algebraMap, ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 K') K', ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 K') K',
    IsScalarTower.algebraMap_apply (𝓞 K) K K', IsScalarTower.algebraMap_apply (𝓞 K) K K', sg_algebraMap_eq_algebraMap_sg_unitsMap, algebraMap_sgO_eq_sg_algebraMap]

private theorem map_comap_ringEquiv_eq_comap_map_of_semiconj {A B : Type} [CommRing A] [CommRing B] (ι : A →+* B) (e : A ≃+* A) (e' : B ≃+* B)
    (h : ∀ x, ι (e x) = e' (ι x)) (J : Ideal A) :
    Ideal.map ι (Ideal.comap e J) = Ideal.comap e' (Ideal.map ι J) := by
  have h1 : Ideal.comap e J = Ideal.map (e.symm : A →+* A) J := (Ideal.map_comap_of_equiv e.symm).symm
  have h2 : Ideal.comap e' (Ideal.map ι J) = Ideal.map (e'.symm : B →+* B) (Ideal.map ι J) :=
    (Ideal.map_comap_of_equiv e'.symm).symm
  rw [h1, h2, Ideal.map_map, Ideal.map_map]
  congr 1
  ext x
  change ι (e.symm x) = e'.symm (ι x)
  rw [RingEquiv.eq_symm_apply, ← h, RingEquiv.apply_symm_apply]

private theorem ideal_comap_ringEquiv_prod {B : Type} [CommRing B] (e : B ≃+* B) {ι : Type} (s : Finset ι) (I : ι → Ideal B) :
    Ideal.comap e (∏ i ∈ s, I i) = ∏ i ∈ s, Ideal.comap e (I i) := by
  have h1 : ∀ J : Ideal B, Ideal.comap e J = Ideal.mapHom (e.symm : B →+* B) J := fun J =>
    (Ideal.map_comap_of_equiv e.symm).symm
  simp only [h1]
  exact map_prod (Ideal.mapHom (e.symm : B →+* B)) I s

private theorem ideal_comap_ringEquiv_span_singleton {B : Type} [CommRing B] (e : B ≃+* B) (x : B) :
    Ideal.comap e (Ideal.span {x}) = Ideal.span {e.symm x} := by
  have h1 : Ideal.comap e (Ideal.span {x}) = Ideal.map (e.symm : B →+* B) (Ideal.span {x}) :=
    (Ideal.map_comap_of_equiv e.symm).symm
  rw [h1, Ideal.map_span, Set.image_singleton]
  rfl

private theorem ideal_comap_ringEquiv_pow {B : Type} [CommRing B] (e : B ≃+* B) (J : Ideal B) (n : ℕ) :
    Ideal.comap e (J ^ n) = (Ideal.comap e J) ^ n := by
  have h1 : ∀ I : Ideal B, Ideal.comap e I = Ideal.map (e.symm : B →+* B) I := fun I =>
    (Ideal.map_comap_of_equiv e.symm).symm
  rw [h1, h1, Ideal.map_pow]

private theorem map_relNorm_eq_prod_conjI_ker_unitsMap (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K'] (𝔞 : Ideal (𝓞 K')) (h𝔞 : 𝔞 ≠ ⊥) :
    Ideal.map (algebraMap (𝓞 K) (𝓞 K')) (Ideal.relNorm (𝓞 K) 𝔞) =
      ∏ k ∈ Finset.univ.filter (fun k : (ZMod (q * M))ˣ => ZMod.unitsMap (dvd_mul_left M q) k = 1), conjI (q * M) K' 𝔞 k := by
  have hmem : 𝔞 ∈ (Ideal (𝓞 K'))⁰ := mem_nonZeroDivisors_of_ne_zero h𝔞
  have hn0 : orderOf (ClassGroup.mk0 ⟨𝔞, hmem⟩) ≠ 0 := (orderOf_pos _).ne'
  obtain ⟨x, hx⟩ : ∃ x : 𝓞 K', 𝔞 ^ orderOf (ClassGroup.mk0 ⟨𝔞, hmem⟩) = Ideal.span {x} := by
    have h1 : ClassGroup.mk0 ⟨𝔞 ^ orderOf (ClassGroup.mk0 ⟨𝔞, hmem⟩), pow_mem hmem _⟩ = 1 := by
      rw [show (⟨𝔞 ^ orderOf (ClassGroup.mk0 ⟨𝔞, hmem⟩), pow_mem hmem _⟩ : (Ideal (𝓞 K'))⁰) =
        ⟨𝔞, hmem⟩ ^ orderOf (ClassGroup.mk0 ⟨𝔞, hmem⟩) from Subtype.ext (by simp), map_pow, pow_orderOf_eq_one]
    obtain ⟨x, hx⟩ := ((ClassGroup.mk0_eq_one_iff _).mp h1).principal
    exact ⟨x, hx⟩
  apply pow_left_injective hn0
  dsimp only
  rw [← Ideal.map_pow, ← map_pow, hx, Ideal.relNorm_singleton, Ideal.map_span, Set.image_singleton,
    ← Finset.prod_pow]
  unfold conjI
  simp_rw [← ideal_comap_ringEquiv_pow, hx, ideal_comap_ringEquiv_span_singleton, sgO_symm_apply_eq_sgO_inv]
  rw [Ideal.prod_span_singleton]
  congr 2
  apply FaithfulSMul.algebraMap_injective (𝓞 K') K'
  rw [← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 K') K', IsScalarTower.algebraMap_apply (𝓞 K) K K',
    Algebra.algebraMap_intNorm (L := K'), algebraMap_norm_eq_prod_sg_ker_unitsMap M q K K', map_prod]
  simp_rw [algebraMap_sgO_eq_sg_algebraMap]
  refine Finset.prod_nbij' (·⁻¹) (·⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_filter, Set.mem_setOf_eq] at hk ⊢
    rw [map_inv, hk, inv_one]
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_filter, Set.mem_setOf_eq] at hk ⊢
    rw [map_inv, hk, inv_one]
  · intro k _
    simp
  · intro k _
    simp
  · intro k _
    simp

private theorem map_conjI_relNorm_eq_prod_conjI_fiber_unitsMap (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K'] (𝔞 : Ideal (𝓞 K')) (h𝔞 : 𝔞 ≠ ⊥) (t : (ZMod M)ˣ) :
    Ideal.map (algebraMap (𝓞 K) (𝓞 K')) (conjI M K (Ideal.relNorm (𝓞 K) 𝔞) t) =
      ∏ t' ∈ Finset.univ.filter (fun t' : (ZMod (q * M))ˣ => ZMod.unitsMap (dvd_mul_left M q) t' = t), conjI (q * M) K' 𝔞 t' := by
  obtain ⟨t₀, rfl⟩ := ZMod.unitsMap_surjective (dvd_mul_left M q) t
  rw [show conjI M K (Ideal.relNorm (𝓞 K) 𝔞) (ZMod.unitsMap (dvd_mul_left M q) t₀) =
      Ideal.comap (sgO M K (ZMod.unitsMap (dvd_mul_left M q) t₀)) (Ideal.relNorm (𝓞 K) 𝔞) from rfl,
    map_comap_ringEquiv_eq_comap_map_of_semiconj (algebraMap (𝓞 K) (𝓞 K')) (sgO M K _) (sgO (q * M) K' t₀)
      (fun x => (sgO_algebraMap_eq_algebraMap_sgO_unitsMap M q K K' t₀ x).symm),
    map_relNorm_eq_prod_conjI_ker_unitsMap M q K K' 𝔞 h𝔞, ideal_comap_ringEquiv_prod]
  refine Finset.prod_nbij' (· * t₀) (· * t₀⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_filter, Set.mem_setOf_eq] at hk ⊢
    rw [map_mul, hk, one_mul]
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_filter, Set.mem_setOf_eq] at hk ⊢
    rw [map_mul, hk, map_inv, mul_inv_cancel]
  · intro k _
    simp
  · intro k _
    simp
  · intro k _
    unfold conjI
    ext x
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap, sgO_mul_apply]

private theorem prod_zpow_eq_zpow_sum_of_ne_zero {G : Type} [CommGroupWithZero G] (a : G) (ha : a ≠ 0) {ι : Type} (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := by
  refine Finset.cons_induction ?_ (fun j s hj ih => ?_) s
  · simp
  · rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add₀ ha]

private theorem fractionalIdeal_spanSingleton_finset_prod {R P : Type} [CommRing R] [CommRing P] [Algebra R P] {S : Submonoid R} [IsLocalization S P] {ι : Type} (s : Finset ι) (f : ι → P) :
    FractionalIdeal.spanSingleton S (∏ i ∈ s, f i) = ∏ i ∈ s, FractionalIdeal.spanSingleton S (f i) := by
  refine Finset.cons_induction ?_ (fun j s hj ih => ?_) s
  · simp [FractionalIdeal.spanSingleton_one]
  · rw [Finset.prod_cons, Finset.prod_cons, ← FractionalIdeal.spanSingleton_mul_spanSingleton, ih]

private theorem isFractionRing_map_ringOfIntegers_eq_algebraMap (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] (x : K) :
    IsFractionRing.map (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 K')) x = algebraMap K K' x := by
  have h : (IsFractionRing.map (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 K')) : K →+* K') = algebraMap K K' := by
    apply IsLocalization.ringHom_ext (𝓞 K)⁰
    ext y
    rw [RingHom.comp_apply, RingHom.comp_apply, IsFractionRing.map, IsLocalization.map_eq,
      ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 K') K', ← IsScalarTower.algebraMap_apply (𝓞 K) K K']
  exact RingHom.congr_fun h x

private theorem fractionalIdeal_coeIdeal_finset_prod {R P : Type} [CommRing R] [CommRing P] [Algebra R P] (S : Submonoid R) {ι : Type} (s : Finset ι) (I : ι → Ideal R) :
    ((∏ i ∈ s, I i : Ideal R) : FractionalIdeal S P) = ∏ i ∈ s, (I i : FractionalIdeal S P) :=
  map_prod (FractionalIdeal.coeIdealHom S P) I s

private theorem prod_fiber_prod_zpow_eq_prod_zpow_comp {G α β : Type} [DivisionCommMonoid G] [Fintype α] [Fintype β] [DecidableEq β] (g : α → β) (F : α → G) (e : β → ℤ) :
    ∏ t, (∏ t' ∈ Finset.univ.filter (fun t' => g t' = t), F t') ^ e t = ∏ t', F t' ^ e (g t') := by
  rw [← Finset.prod_fiberwise Finset.univ g (fun t' => F t' ^ e (g t'))]
  refine Finset.prod_congr rfl (fun t _ => ?_)
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl (fun t' ht' => ?_)
  rw [(Finset.mem_filter.mp ht').2]

private theorem coeIdeal_conjI_ne_zero_of_ne_bot (N : ℕ) [NeZero N] (K' : Type) [Field K'] [NumberField K'] [IsCyclotomicExtension {N} ℚ K'] (𝔞 : Ideal (𝓞 K')) (h𝔞 : 𝔞 ≠ ⊥) (t : (ZMod N)ˣ) :
    ((conjI N K' 𝔞 t : Ideal (𝓞 K')) : FractionalIdeal (𝓞 K')⁰ K') ≠ 0 := by
  rw [FractionalIdeal.coeIdeal_ne_zero]
  unfold conjI
  have h1 : Ideal.comap (sgO N K' t) 𝔞 = Ideal.map ((sgO N K' t).symm : 𝓞 K' →+* 𝓞 K') 𝔞 :=
    (Ideal.map_comap_of_equiv (sgO N K' t).symm).symm
  rw [h1, Ne, Ideal.map_eq_bot_iff_of_injective (f := ((sgO N K' t).symm : 𝓞 K' →+* 𝓞 K')) (sgO N K' t).symm.injective]
  exact h𝔞

theorem UpperTheory.V.ML.xNormDiv :
    ∀ (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K'], q.Prime → ∀ u : (ZMod M)ˣ, (u : ZMod M) = q → ∀ (b : ℕ), b < q → ∀ (𝔞 : Ideal (𝓞 K')) (X' : K') (X : K), 𝔞 ≠ ⊥ → IsX (q * M) K' b 𝔞 X' → IsX M K b (Ideal.relNorm (𝓞 K) 𝔞) X →
    ∃ ζ : K, ζ ^ (2 * M) = 1 ∧ Algebra.norm K X' = ζ * (X / (sg M K u)⁻¹ X) := by
  intro M q _ _ K K' _ _ _ _ _ _ _ hq u hu b hb 𝔞 X' X h𝔞 hX' hX
  unfold IsX at hX' hX
  have hneg : ZMod.unitsMap (dvd_mul_left M q) (-1) = -1 := by
    ext
    simp [ZMod.unitsMap]
  have hN1 : Algebra.norm K X' * sg M K (-1) (Algebra.norm K X') = 1 := by
    rw [← hneg, ← norm_sg_eq_sg_unitsMap_norm M q K K', ← map_mul, hX'.1, map_one]
  have hY1 : X / (sg M K u)⁻¹ X * sg M K (-1) (X / (sg M K u)⁻¹ X) = 1 := by
    have hc : (sg M K u)⁻¹ (sg M K (-1) X) = sg M K (-1) ((sg M K u)⁻¹ X) :=
      cyclotomic_rat_algEquiv_apply_comm M K (sg M K u)⁻¹ (sg M K (-1)) X
    rw [map_div₀, ← hc, div_mul_div_comm, ← map_mul, hX.1, map_one, div_one]
  have hτX : FractionalIdeal.spanSingleton (𝓞 K)⁰ ((sg M K u)⁻¹ X) =
      ∏ t, ((conjI M K (Ideal.relNorm (𝓞 K) 𝔞) t : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ^ th M b ↑(t * u⁻¹) := by
    rw [← map_inv]
    exact spanSingleton_sg_eq_prod_conjI_pow_th_mul_of_eq_prod M K b _ X hX.2 u⁻¹
  have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ (Algebra.norm K X') =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (X / (sg M K u)⁻¹ X) := by
    apply FractionalIdeal.extendedHom_injective (𝓞 K) K K' (𝓞 K')
    dsimp only
    rw [← FractionalIdeal.spanSingleton_div_spanSingleton, hX.2, hτX, map_div₀, map_prod, map_prod,
      FractionalIdeal.extendedHom_spanSingleton, isFractionRing_map_ringOfIntegers_eq_algebraMap, algebraMap_norm_eq_prod_sg_ker_unitsMap M q K K', fractionalIdeal_spanSingleton_finset_prod]
    simp_rw [map_zpow₀, FractionalIdeal.extendedHom_coeIdeal_eq_map, map_conjI_relNorm_eq_prod_conjI_fiber_unitsMap M q K K' 𝔞 h𝔞,
      fractionalIdeal_coeIdeal_finset_prod, spanSingleton_sg_eq_prod_conjI_pow_th_mul_of_eq_prod (q * M) K' b 𝔞 X' hX'.2]
    rw [prod_fiber_prod_zpow_eq_prod_zpow_comp, prod_fiber_prod_zpow_eq_prod_zpow_comp, Finset.prod_comm, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl (fun t' _ => ?_)
    rw [prod_zpow_eq_zpow_sum_of_ne_zero _ (coeIdeal_conjI_ne_zero_of_ne_bot (q * M) K' 𝔞 h𝔞 t'), ← zpow_sub₀ (coeIdeal_conjI_ne_zero_of_ne_bot (q * M) K' 𝔞 h𝔞 t')]
    congr 1
    rw [mul_comm (ZMod.unitsMap (dvd_mul_left M q) t') u⁻¹,
      ← thDist M q b hq hb u hu (ZMod.unitsMap (dvd_mul_left M q) t')]
    refine Finset.sum_nbij' (t' * ·) (t'⁻¹ * ·) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_filter, Set.mem_setOf_eq] at hk ⊢
      rw [map_mul, hk, mul_one]
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_filter, Set.mem_setOf_eq] at hk ⊢
      rw [map_mul, hk, map_inv, inv_mul_cancel]
    · intro k _
      simp
    · intro k _
      simp
    · intro k _
      rfl
  have hY0 : X / (sg M K u)⁻¹ X ≠ 0 := by
    intro h
    rw [h, zero_mul] at hY1
    exact zero_ne_one hY1
  have hr1 : Algebra.norm K X' / (X / (sg M K u)⁻¹ X) * sg M K (-1) (Algebra.norm K X' / (X / (sg M K u)⁻¹ X)) = 1 := by
    rw [map_div₀ (sg M K (-1)) (Algebra.norm K X'), div_mul_div_comm, hN1, hY1, div_one]
  have hrs : FractionalIdeal.spanSingleton (𝓞 K)⁰ (Algebra.norm K X' / (X / (sg M K u)⁻¹ X)) = 1 := by
    rw [← FractionalIdeal.spanSingleton_div_spanSingleton, hspan, div_self]
    rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
  have hIsXr : IsX M K b ⊤ (Algebra.norm K X' / (X / (sg M K u)⁻¹ X)) := by
    unfold IsX
    refine ⟨hr1, ?_⟩
    rw [hrs]
    simp [conjI, FractionalIdeal.coeIdeal_top]
  have hIsX1 : IsX M K b ⊤ 1 := by
    unfold IsX
    refine ⟨by simp, ?_⟩
    simp [conjI, FractionalIdeal.coeIdeal_top, FractionalIdeal.spanSingleton_one]
  obtain ⟨ζ, hζ, hrζ⟩ := xUniq M K b ⊤ 1 _ top_ne_bot hIsX1 hIsXr
  refine ⟨ζ, hζ, ?_⟩
  rw [mul_one] at hrζ
  rw [← hrζ, div_mul_cancel₀ _ hY0]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.AdmissiblePrimeNotDvdOrderOfAndNotDvdLevel
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.admissible_prime_not_dvd_orderOf_and_not_dvd_level :
    ∀ (l F r d : ℕ), F ≠ 0 → l.Prime → r.Prime → r ≡ 1 [MOD F] → ML.admitted l F r d → ¬ l ∣ orderOf (r : ZMod (F * d)) ∧ ¬ r ∣ F * d := by
  intro l F r d _ hl hr hrF hd
  obtain ⟨hsq, hq⟩ := hd
  have hone : ∀ p : ℕ, p.Prime → p ≡ 1 [MOD F] → ¬ p ∣ F := fun p hp h hpF => by
    have h1 : p ≡ 1 [MOD p] := h.of_dvd hpF
    have h2 : p ∣ 1 := (h1.dvd_iff dvd_rfl).1 dvd_rfl
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  refine ⟨?_, ?_⟩
  · set n := ∏ q ∈ d.primeFactors, orderOf (r : ZMod q) with hn
    have hln : ¬ l ∣ n := by
      intro h
      obtain ⟨q, hqm, hlq⟩ := (Prime.dvd_finsetProd_iff hl.prime _).1 h
      exact (hq q (Nat.prime_of_mem_primeFactors hqm) (Nat.dvd_of_mem_primeFactors hqm)).2.2.2 hlq
    have hcop : Nat.Coprime F d := by
      apply Nat.coprime_of_dvd
      intro k hk hkF hkd
      exact hone k hk (hq k hk hkd).2.1 hkF
    have hpos : 1 ≤ r ^ n := Nat.one_le_pow _ _ hr.pos
    have hF : r ^ n ≡ 1 [MOD F] := by simpa using hrF.pow n
    have hD : r ^ n ≡ 1 [MOD d] := by
      have h1 : ∏ q ∈ d.primeFactors, q ∣ r ^ n - 1 := by
        apply Finset.prod_primes_dvd
        · intro a ha
          exact (Nat.prime_of_mem_primeFactors ha).prime
        · intro a ha
          have h2 : (r : ZMod a) ^ n = 1 :=
            orderOf_dvd_iff_pow_eq_one.1 (Finset.dvd_prod_of_mem (fun q : ℕ => orderOf (r : ZMod q)) ha)
          have h3 : r ^ n ≡ 1 [MOD a] := by
            rw [← ZMod.natCast_eq_natCast_iff]
            simpa using h2
          exact (Nat.modEq_iff_dvd' hpos).1 h3.symm
      rw [Nat.prod_primeFactors_of_squarefree hsq] at h1
      exact ((Nat.modEq_iff_dvd' hpos).2 h1).symm
    have hFD : r ^ n ≡ 1 [MOD F * d] := (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨hF, hD⟩
    have h4 : (r : ZMod (F * d)) ^ n = 1 := by
      have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hFD
      simpa using this
    exact fun h => hln (h.trans (orderOf_dvd_of_pow_eq_one h4))
  · intro h
    rcases (Nat.Prime.dvd_mul hr).1 h with h | h
    · exact hone r hr hrF h
    · exact (hq r hr h).2.2.1 rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ValuationKummerElementEqOneOfNotOver
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem val_count_int {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) (ha : a ≠ 0) :
    v.valuation K (a : K) = WithZero.exp (-FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K))) := by
  have h1 : v.valuation K (a : K) = v.intValuation a := v.valuation_of_algebraMap a
  have h2 : FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K)
      = ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :=
    (FractionalIdeal.coeIdeal_span_singleton a).symm
  rw [h1, h2, v.intValuation_if_neg ha, FractionalIdeal.count_coe K v (by simpa using ha)]

private theorem val_count {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : K) (hx : x ≠ 0) :
    v.valuation K x = WithZero.exp (-FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)) := by
  obtain ⟨a, b, hb, e⟩ := IsFractionRing.div_surjective (𝓞 K) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : (b : K) ≠ 0 := by exact_mod_cast hb0
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hx
    simp [← e]
  have e' : x * (b : K) = (a : K) := by
    rw [← e]; exact div_mul_cancel₀ _ hbK
  have h1 := val_count_int v a ha0
  have h2 := val_count_int v b hb0
  rw [← e', map_mul, h2, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul K v (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hbK), neg_add, WithZero.exp_add] at h1
  exact mul_right_cancel₀ WithZero.exp_ne_zero h1

theorem UpperTheory.valuation_kummerElement_eq_one_of_not_over :
    ∀ (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (b r : ℕ) (v w : HeightOneSpectrum (𝓞 K)) (X : K), IsX M K b v.asIdeal X → (r : 𝓞 K) ∈ v.asIdeal → (r : 𝓞 K) ∉ w.asIdeal → w.valuation K X = 1 := by
  intro M _ K _ _ _ b r v w X hX hv hw
  have hX0 : X ≠ 0 := left_ne_zero_of_mul_eq_one hX.1
  let P : (ZMod M)ˣ → HeightOneSpectrum (𝓞 K) := fun t =>
    HeightOneSpectrum.comap (sgO M K t : 𝓞 K →+* 𝓞 K) (sgO M K t).surjective v
  have hP : ∀ t, (P t).asIdeal = conjI M K v.asIdeal t := fun t => rfl
  have hne : ∀ t, P t ≠ w := by
    intro t h
    apply hw
    rw [← h, hP, mem_conjI, map_natCast]
    exact hv
  rw [val_count w X hX0, hX.2, FractionalIdeal.count_prod]
  · rw [Finset.sum_eq_zero, neg_zero, WithZero.exp_zero]
    intro t _
    rw [FractionalIdeal.count_zpow, ← hP, FractionalIdeal.count_maximal_coprime K w (hne t), mul_zero]
  · intro t _
    apply zpow_ne_zero
    rw [← hP]
    exact FractionalIdeal.coeIdeal_ne_zero.mpr (P t).ne_bot
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ValuationComapIsEquivOfLtOneIffMemPrime
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem int_le {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {b : Ω} (hb : IsIntegral ℤ b) :
    A.valuation b ≤ 1 := by
  have h : IsIntegral A b := hb.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [A.valuation_le_one_iff, ← hy]
  exact y.2

theorem UpperTheory.valuation_comap_isEquiv_of_lt_one_iff_mem_prime :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] (ι : K →+* Ω) (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 K)), (∀ y : 𝓞 K, A.valuation (ι (y : K)) < 1 ↔ y ∈ w.asIdeal) → (A.valuation.comap ι).IsEquiv (w.valuation K) := by
  intro K Ω _ _ _ ι A w h
  have hle : ∀ y : 𝓞 K, A.valuation (ι (y : K)) ≤ 1 := fun y =>
    int_le A (y.isIntegral_coe.map ι.toIntAlgHom)
  have key : ∀ x : K, w.valuation K x ≤ 1 → ∃ a s : 𝓞 K, s ∉ w.asIdeal ∧ x * (s : K) = (a : K) ∧
      A.valuation (ι x) = A.valuation (ι (a : K)) := by
    intro x hx
    obtain ⟨a, s, hs⟩ := w.exists_primeCompl_mul_eq_of_integer x hx
    have hs' : (s : 𝓞 K) ∉ w.asIdeal := s.2
    have hs2 : x * ((s : 𝓞 K) : K) = (a : K) := hs
    refine ⟨a, s, hs', hs2, ?_⟩
    have h1 : A.valuation (ι ((s : 𝓞 K) : K)) = 1 :=
      le_antisymm (hle _) (not_lt.1 fun hh => hs' ((h _).1 hh))
    rw [← hs2, map_mul, map_mul, h1, mul_one]
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  rw [Valuation.comap_apply]
  constructor
  · intro hx
    by_contra hw
    have hw' : 1 < w.valuation K x := not_le.1 hw
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hw'
    have hinv : w.valuation K x⁻¹ < 1 := by
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ hw'
    obtain ⟨a, s, -, hs2, he⟩ := key x⁻¹ hinv.le
    have ha : w.valuation K (a : K) < 1 := by
      rw [← hs2, map_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hinv (w.valuation_le_one s)
    have ha' : a ∈ w.asIdeal := (w.valuation_lt_one_iff_mem a).1 ha
    have h2 : A.valuation (ι x⁻¹) < 1 := he ▸ (h a).2 ha'
    have h3 := mul_lt_one_of_nonneg_of_lt_one_left zero_le h2 hx
    rw [← map_mul, ← map_mul, inv_mul_cancel₀ hx0, map_one, map_one] at h3
    exact lt_irrefl _ h3
  · intro hx
    obtain ⟨a, s, -, -, he⟩ := key x hx
    rw [he]
    exact hle a
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.NormCyclotomicPrimeLayerEqNrmGenerator
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem cyc_hom_ext {K Ω : Type} [Field K] [CharZero K] [Field Ω] [CharZero Ω] (N : ℕ) [NeZero N]
    [IsCyclotomicExtension {N} ℚ K] (f g : K →+* Ω) (h : ∀ x : K, x ^ N = 1 → f x = g x) : f = g := by
  have key : f.toRatAlgHom = g.toRatAlgHom := by
    apply AlgHom.ext
    intro x
    have hx := IsCyclotomicExtension.adjoin_roots (S := {N}) (A := ℚ) x
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨n, hn, -, hy1⟩ := hy
      rw [Set.mem_singleton_iff] at hn
      rw [hn] at hy1
      exact h y hy1
    | algebraMap c => rw [AlgHom.commutes, AlgHom.commutes]
    | add a b _ _ ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
    | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]
  ext x
  exact congrArg (fun φ : K →ₐ[ℚ] Ω => φ x) key

private theorem card_gal (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K']
    [IsGalois K K'] (hq : q.Prime) (hc : q.Coprime M) : Nat.card (K' ≃ₐ[K] K') = q - 1 := by
  haveI : IsScalarTower ℚ K K' := inferInstance
  haveI : FiniteDimensional K K' := Module.Finite.of_restrictScalars_finite ℚ K K'
  have h1 := IsCyclotomicExtension.finrank K' (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (q * M)))
  have h2 := IsCyclotomicExtension.finrank K (Polynomial.cyclotomic.irreducible_rat (NeZero.pos M))
  rw [IsGalois.card_aut_eq_finrank]
  have htow := Module.finrank_mul_finrank ℚ K K'
  rw [h1, h2, Nat.totient_mul hc, Nat.totient_prime hq] at htow
  have hM : 0 < M.totient := Nat.totient_pos.mpr (NeZero.pos M)
  exact Nat.eq_of_mul_eq_mul_left hM (by rw [htow, mul_comm])

theorem UpperTheory.norm_cyclotomic_prime_layer_eq_nrm_generator :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K'] (ι' : K' →+* Ω), q.Prime → q.Coprime M → ∀ τ ∈ fixMu ℚ Ω M, GenAt q τ → ∀ x : K', nrm q τ (ι' x) = ι' (algebraMap K K' (Algebra.norm K x)) := by
  intro Ω _ _ M q _ _ K K' _ _ _ _ _ _ _ ι' hq hc τ hτ hgen x
  classical
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : IsScalarTower ℚ K K' := inferInstance
  haveI : FiniteDimensional K K' := Module.Finite.of_restrictScalars_finite ℚ K K'
  haveI : IsGalois ℚ K' := IsCyclotomicExtension.isGalois {q * M} ℚ K'
  haveI : IsGalois K K' := IsGalois.tower_top_of_isGalois ℚ K K'
  obtain ⟨b, hbgen, hb⟩ := hgen
  have hb' : ∀ y : Ω, y ^ q = 1 → τ y = y ^ (b : ZMod q).val := hb
  have hτM : ∀ y : Ω, y ^ M = 1 → τ y = y := hτ
  have hpm : ∀ {R : Type} [Monoid R] (y : R) (N m n : ℕ), y ^ N = 1 → m ≡ n [MOD N] → y ^ m = y ^ n := by
    intro R _ y N m n hy h
    rw [← Nat.mod_add_div m N, ← Nat.mod_add_div n N, show m % N = n % N from h, pow_add, pow_add,
      pow_mul, pow_mul, hy, one_pow, one_pow]
  obtain ⟨A, hA1, hA0⟩ : ∃ A, A ≡ 1 [MOD q] ∧ A ≡ 0 [MOD M] :=
    ⟨(Nat.chineseRemainder hc 1 0).1, (Nat.chineseRemainder hc 1 0).2.1, (Nat.chineseRemainder hc 1 0).2.2⟩
  obtain ⟨B, hB0, hB1⟩ : ∃ B, B ≡ 0 [MOD q] ∧ B ≡ 1 [MOD M] :=
    ⟨(Nat.chineseRemainder hc 0 1).1, (Nat.chineseRemainder hc 0 1).2.1, (Nat.chineseRemainder hc 0 1).2.2⟩
  obtain ⟨e, he⟩ : ∃ e, e = A * (b : ZMod q).val + B := ⟨_, rfl⟩
  have he_q : e ≡ (b : ZMod q).val [MOD q] := by
    have h := (hA1.mul_right (b : ZMod q).val).add hB0
    rwa [one_mul, add_zero, ← he] at h
  have he_M : e ≡ 1 [MOD M] := by
    have h := (hA0.mul_right (b : ZMod q).val).add hB1
    rwa [zero_mul, zero_add, ← he] at h
  have hτe : ∀ y : Ω, y ^ (q * M) = 1 → τ y = y ^ e := by
    intro y hy
    have hAB : A + B ≡ 1 [MOD q * M] := (Nat.modEq_and_modEq_iff_modEq_mul hc).mp
      ⟨by simpa using hA1.add hB0, by simpa using hA0.add hB1⟩
    obtain ⟨cA, hcA⟩ := (Nat.modEq_zero_iff_dvd.mp hA0)
    obtain ⟨cB, hcB⟩ := (Nat.modEq_zero_iff_dvd.mp hB0)
    have hyA : (y ^ A) ^ q = 1 := by
      rw [← pow_mul, show A * q = q * M * cA by rw [hcA]; ring, pow_mul, hy, one_pow]
    have hyB : (y ^ B) ^ M = 1 := by
      rw [← pow_mul, show B * M = q * M * cB by rw [hcB]; ring, pow_mul, hy, one_pow]
    calc τ y = τ (y ^ A * y ^ B) := by rw [← pow_add, hpm y (q * M) (A + B) 1 hy hAB, pow_one]
      _ = (y ^ A) ^ (b : ZMod q).val * y ^ B := by rw [map_mul, hb' _ hyA, hτM _ hyB]
      _ = y ^ e := by rw [he, ← pow_mul, ← pow_add]
  have hζ := IsCyclotomicExtension.zeta_spec (q * M) ℚ K'
  have he_cop : e.Coprime (q * M) := by
    apply Nat.Coprime.mul_right
    · exact he_q.gcd_eq.trans (ZMod.val_coe_unit_coprime b)
    · exact he_M.gcd_eq.trans (Nat.gcd_one_left M)
  have hμ := hζ.pow_of_coprime e he_cop
  have hirr := Polynomial.cyclotomic.irreducible_rat (NeZero.pos (q * M))
  have hσ0ζ := IsCyclotomicExtension.fromZetaAut_spec hμ hirr
  have hσ0 : ∀ z : K', z ^ (q * M) = 1 → IsCyclotomicExtension.fromZetaAut hμ hirr z = z ^ e := by
    intro z hz
    obtain ⟨j, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz
    rw [map_pow, hσ0ζ, ← pow_mul, ← pow_mul, mul_comm e j]
  have hσ0K : ∀ y : K, IsCyclotomicExtension.fromZetaAut hμ hirr (algebraMap K K' y) = algebraMap K K' y := by
    have h := cyc_hom_ext M ((IsCyclotomicExtension.fromZetaAut hμ hirr).toRingEquiv.toRingHom.comp (algebraMap K K'))
      (algebraMap K K') (fun y hy => by
        show IsCyclotomicExtension.fromZetaAut hμ hirr (algebraMap K K' y) = algebraMap K K' y
        have h1 : (algebraMap K K' y) ^ M = 1 := by rw [← map_pow, hy, map_one]
        rw [hσ0 _ (by rw [mul_comm, pow_mul, h1, one_pow]), hpm _ M e 1 h1 he_M, pow_one])
    exact fun y => RingHom.congr_fun h y
  let σ1 : K' ≃ₐ[K] K' := AlgEquiv.ofRingEquiv (f := (IsCyclotomicExtension.fromZetaAut hμ hirr).toRingEquiv) hσ0K
  have hσ1 : ∀ z : K', z ^ (q * M) = 1 → σ1 z = z ^ e := fun z hz => hσ0 z hz
  have hcomm : ∀ z : K', τ (ι' z) = ι' (σ1 z) := by
    have h := cyc_hom_ext (q * M) ((τ : Ω ≃ₐ[ℚ] Ω).toRingEquiv.toRingHom.comp ι') (ι'.comp σ1.toRingEquiv.toRingHom)
      (fun z hz => by
        show τ (ι' z) = ι' (σ1 z)
        rw [hσ1 z hz, map_pow, hτe _ (by rw [← map_pow, hz, map_one])])
    exact fun z => RingHom.congr_fun h z
  have hcommi : ∀ i : ℕ, ∀ z : K', (τ ^ i) (ι' z) = ι' ((σ1 ^ i) z) := by
    intro i
    induction i with
    | zero => intro z; rw [pow_zero, pow_zero, AlgEquiv.one_apply, AlgEquiv.one_apply]
    | succ i ih => intro z; rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hcomm, ih]
  have hζq : IsPrimitiveRoot (IsCyclotomicExtension.zeta (q * M) ℚ K' ^ M) q := by
    have h := hζ.pow_of_dvd (NeZero.ne M) (dvd_mul_left M q)
    rwa [Nat.mul_div_cancel q (NeZero.pos M)] at h
  have hζq1 : (IsCyclotomicExtension.zeta (q * M) ℚ K' ^ M) ^ (q * M) = 1 := by
    rw [pow_mul, hζq.pow_eq_one, one_pow]
  have hσpow : ∀ i : ℕ, (σ1 ^ i) (IsCyclotomicExtension.zeta (q * M) ℚ K' ^ M)
      = (IsCyclotomicExtension.zeta (q * M) ℚ K' ^ M) ^ (e ^ i) := by
    intro i
    induction i with
    | zero => rw [pow_zero, pow_zero, pow_one, AlgEquiv.one_apply]
    | succ i ih => rw [pow_succ, AlgEquiv.mul_apply, hσ1 _ hζq1, map_pow, ih, ← pow_mul, pow_succ]
  have horder : orderOf b = q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hbgen, Nat.card_eq_fintype_card, ZMod.card_units]
  have hinj : ∀ i ∈ Finset.range (q - 1), ∀ j ∈ Finset.range (q - 1), σ1 ^ i = σ1 ^ j → i = j := by
    intro i hi j hj hij
    have h1 : (IsCyclotomicExtension.zeta (q * M) ℚ K' ^ M) ^ (e ^ i) = (IsCyclotomicExtension.zeta (q * M) ℚ K' ^ M) ^ (e ^ j) := by
      rw [← hσpow, ← hσpow, hij]
    rw [hpm _ q (e ^ i) (e ^ i % q) hζq.pow_eq_one (Nat.mod_modEq _ _).symm,
      hpm _ q (e ^ j) (e ^ j % q) hζq.pow_eq_one (Nat.mod_modEq _ _).symm] at h1
    have h2 : e ^ i ≡ e ^ j [MOD q] := hζq.pow_inj (Nat.mod_lt _ hq.pos) (Nat.mod_lt _ hq.pos) h1
    have h3 : ((e : ZMod q)) = (b : ZMod q) := by
      rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr he_q, ZMod.natCast_zmod_val]
    have h4 : (b : ZMod q) ^ i = (b : ZMod q) ^ j := by
      rw [← h3, ← Nat.cast_pow, ← Nat.cast_pow, (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2]
    have h5 : b ^ i = b ^ j := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, h4])
    have h6 := pow_eq_pow_iff_modEq.mp h5
    rw [horder] at h6
    have h7 : i % (q - 1) = j % (q - 1) := h6
    rwa [Nat.mod_eq_of_lt (Finset.mem_range.mp hi), Nat.mod_eq_of_lt (Finset.mem_range.mp hj)] at h7
  have himg : (Finset.range (q - 1)).image (fun i => σ1 ^ i) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn (fun i hi j hj h => hinj i hi j hj h), Finset.card_range,
      ← Nat.card_eq_fintype_card, card_gal M q K K' hq hc]
  show ∏ i ∈ Finset.range (q - 1), (τ ^ i) (ι' x) = _
  rw [Algebra.norm_eq_prod_automorphisms, map_prod, ← himg, Finset.prod_image (fun i hi j hj h => hinj i hi j hj h)]
  exact Finset.prod_congr rfl (fun i _ => hcommi i x)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.RelNormCyclotomicPrimeEqPowDvdOrderOf
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.relNorm_cyclotomic_prime_eq_pow_dvd_orderOf :
    ∀ (N r : ℕ) [NeZero N] (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [IsCyclotomicExtension {N} ℚ K'] [Algebra K K'], r.Prime → ¬ r ∣ N → ∀ (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 K')), (r : 𝓞 K') ∈ v'.asIdeal → (∀ y : 𝓞 K, algebraMap (𝓞 K) (𝓞 K') y ∈ v'.asIdeal ↔ y ∈ v.asIdeal) → ∃ s : ℕ, s ∣ orderOf (r : ZMod N) ∧ Ideal.relNorm (𝓞 K) v'.asIdeal = v.asIdeal ^ s := by
  intro N r _ K K' _ _ _ _ _ _ hp hN v v' hr hvv
  have : Fact r.Prime := ⟨hp⟩
  have hvp : v'.asIdeal.IsPrime := v'.isPrime
  have hm : v.asIdeal.IsMaximal := v.isMaximal
  have hm' : v'.asIdeal.IsMaximal := v'.isMaximal
  have hmax : (Ideal.span {(r : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hlo : v'.asIdeal.LiesOver (Ideal.span {(r : ℤ)}) := by
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hr
  have hl2 : v'.asIdeal.LiesOver v.asIdeal := ⟨by
    ext y
    rw [Ideal.under_def, Ideal.mem_comap]
    exact (hvv y).symm⟩
  have h3 := Ideal.inertiaDeg_tower (R := ℤ) v.asIdeal v'.asIdeal
  rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd r K' v'.asIdeal hN] at h3
  refine ⟨v'.asIdeal.inertiaDeg (𝓞 K), ?_, ?_⟩
  · rw [h3]; exact Dvd.intro_left _ rfl
  · exact Ideal.relNorm_eq_pow_of_isMaximal v'.asIdeal v.asIdeal
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem hom_ext {K Ω : Type} [Field K] [CharZero K] [Field Ω] (N : ℕ) [NeZero N]
    [IsCyclotomicExtension {N} ℚ K] (f g : K →+* Ω) (h : ∀ x : K, x ^ N = 1 → f x = g x) : f = g := by
  haveI : CharZero Ω := f.charZero_iff f.injective |>.1 inferInstance
  have hζ := IsCyclotomicExtension.zeta_spec N ℚ K
  have e : f.toRatAlgHom = g.toRatAlgHom :=
    AlgHom.ext_of_adjoin_eq_top (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ) fun x hx => by
      rw [Set.mem_singleton_iff.1 hx]
      exact h _ hζ.pow_eq_one
  exact RingHom.ext fun x => DFunLike.congr_fun e x

private theorem lift_sg {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] (N : ℕ) [NeZero N]
    [IsCyclotomicExtension {N} ℚ K] (ι : K →+* Ω) (b : (ZMod N)ˣ) (g : G ℚ Ω) (hg : Lifts N b g) (x : K) :
    g (ι x) = ι (sg N K b x) := by
  refine DFunLike.congr_fun (hom_ext N (g.toRingEquiv.toRingHom.comp ι) (ι.comp (sg N K b).toRingEquiv.toRingHom)
    fun y hy => ?_) x
  change g (ι y) = ι (sg N K b y)
  rw [hg _ (by rw [← map_pow, hy, map_one]), sg_apply N K b hy, map_pow]

private theorem fix_emb {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] (N : ℕ) [NeZero N]
    [IsCyclotomicExtension {N} ℚ K] (ι : K →+* Ω) (g : G ℚ Ω) (hg : g ∈ fixMu ℚ Ω N) (x : K) :
    g (ι x) = ι x :=
  DFunLike.congr_fun (hom_ext N (g.toRingEquiv.toRingHom.comp ι) ι
    fun y hy => hg _ (by rw [← map_pow, hy, map_one])) x

private theorem inv_emb {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] (N q : ℕ) [NeZero N]
    [IsCyclotomicExtension {N} ℚ K] (ι : K →+* Ω) (u : (ZMod N)ˣ) (hu : (u : ZMod N) = q) (g : G ℚ Ω)
    (hg : Pows N q g) (x : K) : g⁻¹ (ι x) = ι ((sg N K u)⁻¹ x) := by
  have h : Lifts N u g := fun y hy => by rw [hg y hy, hu, ZMod.val_natCast, ← pow_eq_pow_mod _ hy]
  apply g.injective
  rw [lift_sg N ι u g h]
  change g (g.symm _) = ι (sg N K u ((sg N K u).symm x))
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

private theorem place_emb {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (ι : K →+* Ω) (A : ValuationSubring Ω) (hA : A ≠ ⊤) :
    ∃ w : HeightOneSpectrum (𝓞 K), ∀ y : 𝓞 K, A.valuation (ι (y : K)) < 1 ↔ y ∈ w.asIdeal := by
  letI : Algebra K Ω := ι.toAlgebra
  haveI : IsScalarTower ℚ K Ω := IsScalarTower.of_algebraMap_eq fun q => by simp
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure K Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  exact (UpperTheory.V.Kum.placeDict K Ω).2.1 A hA

private theorem ne_top {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {n : ℕ} (hn : n ≠ 0)
    (h : Over A n) : A ≠ ⊤ := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  rintro rfl
  have h1 : (⊤ : ValuationSubring Ω).valuation (n : Ω)⁻¹ ≤ 1 :=
    (ValuationSubring.valuation_le_one_iff _ _).2 (ValuationSubring.mem_top _)
  have h2 := mul_lt_one_of_nonneg_of_lt_one_left zero_le h h1
  rw [← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn), map_one] at h2
  exact lt_irrefl _ h2

private theorem val_top {Ω : Type} [Field Ω] {x : Ω} (hx : x ≠ 0) : (⊤ : ValuationSubring Ω).valuation x = 1 := by
  have h (y : Ω) : (⊤ : ValuationSubring Ω).valuation y ≤ 1 :=
    (ValuationSubring.valuation_le_one_iff _ _).2 (ValuationSubring.mem_top _)
  refine le_antisymm (h x) ?_
  have h1 := h x⁻¹
  rw [map_inv₀] at h1
  exact (inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx))).1 h1

private theorem tower {K K' Ω : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Field Ω] (M N : ℕ)
    [NeZero M] [NeZero N] [IsCyclotomicExtension {M} ℚ K] [IsCyclotomicExtension {N} ℚ K'] (h : M ∣ N)
    (ι : K →+* Ω) (ι' : K' →+* Ω) : ∃ j : K →+* K', ∀ x, ι' (j x) = ι x := by
  have hζ := IsCyclotomicExtension.zeta_spec M ℚ K
  have hζ' := (IsCyclotomicExtension.zeta_spec N ℚ K').map_of_injective ι'.injective
  have key : ∀ x : K, ι x ∈ ι'.fieldRange := fun x => by
    have hx : x ∈ Algebra.adjoin ℚ {IsCyclotomicExtension.zeta M ℚ K} := by
      rw [IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := h
      obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one (ξ := ι x)
        (by rw [Set.mem_singleton_iff.1 hx, pow_mul, ← map_pow, hζ.pow_eq_one, map_one, one_pow])
      exact ⟨_, (map_pow ι' _ i).trans hi⟩
    | algebraMap x => exact ⟨(x : K'), by simp⟩
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  choose j hj using key
  exact ⟨{ toFun := j
           map_one' := ι'.injective (by rw [hj, map_one, map_one])
           map_mul' := fun x y => ι'.injective (by rw [map_mul, hj, hj, hj, map_mul])
           map_zero' := ι'.injective (by rw [hj, map_zero, map_zero])
           map_add' := fun x y => ι'.injective (by rw [map_add (f := _), hj, hj, hj, map_add (f := _)]) }, hj⟩

private def XO {Ω : Type} [Field Ω] (N b : ℕ) (A₀ : ValuationSubring Ω) (x : Ω) : Prop :=
  ∃ (_ : NeZero N) (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCyclotomicExtension {N} ℚ K) (ι : K →+* Ω)
    (v : HeightOneSpectrum (𝓞 K)) (X : K), (∀ y : 𝓞 K, A₀.valuation (ι (y : K)) < 1 ↔ y ∈ v.asIdeal) ∧
    IsX N K b v.asIdeal X ∧ x = ι X

private theorem xo_ex {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N b : ℕ) (hb : b < N)
    (A₀ : ValuationSubring Ω) (hA : A₀ ≠ ⊤) : ∃ x, XO N b A₀ x := by
  haveI : NeZero N := ⟨by omega⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  let K := CyclotomicField N ℚ
  haveI : @IsCyclotomicExtension {N} ℚ K _ _ DivisionRing.toRatAlgebra := by
    have h := CyclotomicField.isCyclotomicExtension N ℚ
    have e : (DivisionRing.toRatAlgebra : Algebra ℚ K) = CyclotomicField.algebra N ℚ := Subsingleton.elim _ _
    rw [e]
    exact h
  let ι : K →+* Ω := (IsAlgClosed.lift : K →ₐ[ℚ] Ω).toRingHom
  obtain ⟨v, hv⟩ := place_emb ι A₀ hA
  obtain ⟨X, hX⟩ := xEx N K b v.asIdeal hb v.ne_bot
  exact ⟨ι X, inferInstance, K, inferInstance, inferInstance, inferInstance, ι, v, X, hv, hX, rfl⟩

private theorem xo_one {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {N b r : ℕ} {A₀ : ValuationSubring Ω}
    (hr : Over A₀ r) {x : Ω} (h : XO N b A₀ x) :
    x ≠ 0 ∧ (∀ g ∈ fixMu ℚ Ω N, g x = x) ∧ ∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation x = 1 := by
  obtain ⟨_, K, _, _, _, ι, v, X, hv, hX, rfl⟩ := h
  have h0 : ι X ≠ 0 := (map_ne_zero ι).2 (left_ne_zero_of_mul_eq_one hX.1)
  refine ⟨h0, fun g hg => fix_emb N ι g hg X, fun A hA => ?_⟩
  by_cases ht : A = ⊤
  · rw [ht]; exact val_top h0
  obtain ⟨w, hw⟩ := place_emb ι A ht
  have h1 := UpperTheory.valuation_kummerElement_eq_one_of_not_over N K b r v w X hX ((hv r).1 (by simpa using hr))
    fun h => hA (by simpa using (hw r).2 h)
  exact (UpperTheory.valuation_comap_isEquiv_of_lt_one_iff_mem_prime K Ω ι A w hw).eq_one_iff_eq_one.2 h1

private theorem xo_ord {Ω : Type} [Field Ω] [Algebra ℚ Ω] {F b r : ℕ} (hp : r.Prime) (h1 : r ≡ 1 [MOD F])
    {A₀ : ValuationSubring Ω} (hr : Over A₀ r) {x : Ω} (h : XO F b A₀ x) : HasOrd F r A₀ x fun t => th F b t := by
  obtain ⟨_, K, _, _, _, ι, v, X, hv, hX, rfl⟩ := h
  intro t σ hσ
  let w : HeightOneSpectrum (𝓞 K) := v.comap (sgO F K t).toRingHom (sgO F K t).surjective
  have hw : ∀ y : 𝓞 K, A₀.valuation ((σ.toRingEquiv.toRingHom.comp ι) (y : K)) < 1 ↔ y ∈ w.asIdeal := fun y => by
    change A₀.valuation (σ (ι y)) < 1 ↔ sgO F K t y ∈ v.asIdeal
    rw [lift_sg F ι t σ hσ, ← hv]
    rfl
  have h2 := UpperTheory.valuation_kummerElement_at_conjugate_prime F K b r v w X t hp h1 hX ((hv r).1 (by simpa using hr)) rfl
  rw [← map_zpow₀] at h2
  have h3 := ((UpperTheory.valuation_comap_isEquiv_of_lt_one_iff_mem_prime K Ω _ A₀ w hw).eq_iff).2 h2
  simpa using h3

private theorem xo_pair {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {M q b r : ℕ} (hp : r.Prime)
    (hq : q.Prime) (hco : q.Coprime M) (hr' : ¬ r ∣ q * M) (hbM : b < M) (hbq : b < q)
    {A₀ : ValuationSubring Ω} (hr : Over A₀ r) {x x' : Ω} (h : XO M b A₀ x) (h' : XO (q * M) b A₀ x') :
    ∃ s : ℕ, s ∣ orderOf (r : ZMod (q * M)) ∧
      (∀ τ ∈ fixMu ℚ Ω M, GenAt q τ → ∀ φ : G ℚ Ω, Pows M q φ →
        ∃ ζ : Ω, ζ ^ (2 * (q * M)) = 1 ∧ nrm q τ x' = ζ * (x / φ⁻¹ x) ^ s) ∧
      ∀ φ : G ℚ Ω, Pows M q φ → ∃ ζ : Ω, ζ ^ (2 * (q * M)) = 1 ∧
        ∀ A : ValuationSubring Ω, Over A q → A.valuation (x' - ζ * φ⁻¹ x ^ s) < 1 := by
  obtain ⟨_, K, _, _, _, ι, v, X, hv, hX, rfl⟩ := h
  obtain ⟨_, K', _, _, _, ι', v', X', hv', hX', rfl⟩ := h'
  obtain ⟨j, hj⟩ := tower M (q * M) (dvd_mul_left M q) ι ι'
  letI : Algebra K K' := j.toAlgebra
  have hj' : ∀ x, ι' (algebraMap K K' x) = ι x := hj
  obtain ⟨s, hs, hn⟩ := UpperTheory.relNorm_cyclotomic_prime_eq_pow_dvd_orderOf (q * M) r K K' hp hr' v v' ((hv' r).1 (by simpa using hr)) fun y => by
    rw [← hv, ← hv', ← hj']
    rfl
  have hXs := (xMul M K b).2.2.1 v.asIdeal X s v.ne_bot hX
  rw [← hn] at hXs
  have hu : ((ZMod.unitOfCoprime q hco : (ZMod M)ˣ) : ZMod M) = q := ZMod.coe_unitOfCoprime q hco
  refine ⟨s, hs, fun τ hτ hg φ hφ => ?_, fun φ hφ => ?_⟩
  · obtain ⟨ζ, hζ, he⟩ := xNormDiv M q K K' hq _ hu b hbq v'.asIdeal X' (X ^ s) v'.ne_bot hX' hXs
    refine ⟨ι ζ, ?_, ?_⟩
    · rw [show 2 * (q * M) = 2 * M * q by ring, pow_mul, ← map_pow, hζ, map_one, one_pow]
    · rw [UpperTheory.norm_cyclotomic_prime_layer_eq_nrm_generator Ω M q K K' ι' hq hco τ hτ hg, hj', he, inv_emb M q ι _ hu φ hφ]
      simp only [map_mul, map_div₀, map_pow, div_pow]
  · have hqr : r.Coprime q := (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hr' (h.mul_right M)
    have hq' : (q : 𝓞 K') ∉ v'.asIdeal := fun h =>
      (placeBasic Ω).2.2.2.1 A₀ r q hqr hr (by simpa using (hv' q).2 h)
    have hc : IsCoprime v'.asIdeal (Ideal.span {(q : 𝓞 K')}) := by
      rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hne
      exact hq' ((v'.isMaximal.eq_of_le hne le_sup_left).ge (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
    obtain ⟨ζ, hζ, he⟩ := xCong M q K K' hq _ hu b hbM hbq v'.asIdeal X' (X ^ s) hc hX' hXs
    refine ⟨ι' ζ, by rw [← map_pow, hζ, map_one], fun A hA => ?_⟩
    obtain ⟨w, hw⟩ := place_emb ι' A (ne_top hq.ne_zero hA)
    have h3 := (UpperTheory.valuation_comap_isEquiv_of_lt_one_iff_mem_prime K' Ω ι' A w hw).lt_one_iff_lt_one.2 (he w ((hw q).1 (by simpa using hA)))
    rw [Valuation.comap_apply, map_sub, map_mul, hj', map_pow, map_pow, ← inv_emb M q ι _ hu φ hφ] at h3
    exact h3

theorem UpperTheory.V.ML.laxEx :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l F r b : ℕ) [NeZero F], l.Prime → r.Prime → r ≡ 1 [MOD F] → b < F → ∀ A₀ : ValuationSubring Ω, Over A₀ r →
    ∃ (X : ℕ → Ω) (s : ℕ → ℕ → ℕ), Lax l F r X s ∧ HasOrd F r A₀ (X 1) fun t => th F b t := by
  intro Ω _ _ _ l F r b _ hl hr h1 hb A₀ hA
  have hlt : ∀ d, d ≠ 0 → b < F * d := fun d hd => hb.trans_le (Nat.le_mul_of_pos_right F (Nat.pos_of_ne_zero hd))
  have hX : ∀ d : ℕ, ∃ x : Ω, d ≠ 0 → XO (F * d) b A₀ x := fun d => by
    by_cases hd : d = 0
    · exact ⟨0, fun h => absurd hd h⟩
    · obtain ⟨x, hx⟩ := xo_ex (F * d) b (hlt d hd) A₀ (ne_top hr.ne_zero hA)
      exact ⟨x, fun _ => hx⟩
  choose X hX using hX
  have hs : ∀ d q : ℕ, ∃ s : ℕ, q.Prime → ML.admitted l F r (q * d) → ¬ l ∣ s ∧
      (∀ τ ∈ fixMu ℚ Ω (F * d), GenAt q τ → ∀ φ : G ℚ Ω, Pows (F * d) q φ →
        ∃ ζ : Ω, ζ ^ (2 * F * (q * d)) = 1 ∧ nrm q τ (X (q * d)) = ζ * (X d / φ⁻¹ (X d)) ^ s) ∧
      ∀ φ : G ℚ Ω, Pows (F * d) q φ → ∃ ζ : Ω, ζ ^ (2 * F * (q * d)) = 1 ∧
        ∀ A : ValuationSubring Ω, Over A q → A.valuation (X (q * d) - ζ * φ⁻¹ (X d) ^ s) < 1 := fun d q => by
    by_cases h : q.Prime ∧ ML.admitted l F r (q * d)
    swap
    · exact ⟨0, fun a b => absurd ⟨a, b⟩ h⟩
    obtain ⟨hq, ha⟩ := h
    have h0 : q * d ≠ 0 := ha.1.ne_zero
    have hd : d ≠ 0 := right_ne_zero_of_mul h0
    have he : F * (q * d) = q * (F * d) := by ring
    have hqF : q ≡ 1 [MOD F] := (ha.2 q hq (dvd_mul_right q d)).2.1
    have hco : q.Coprime (F * d) := Nat.Coprime.mul_right
      (by rw [Nat.Coprime, hqF.gcd_eq]; exact Nat.gcd_one_left F) (Nat.coprime_of_squarefree_mul ha.1)
    have hFq : F < q := by
      have h2 := Nat.le_of_dvd (by have := hq.two_le; omega) ((Nat.modEq_iff_dvd' hq.one_le).1 hqF.symm)
      have := hq.two_le
      omega
    obtain ⟨hc1, hc2⟩ := UpperTheory.admissible_prime_not_dvd_orderOf_and_not_dvd_level l F r (q * d) (NeZero.ne F) hl hr h1 ha
    have hx' := hX (q * d) h0
    rw [he] at hc1 hc2 hx'
    obtain ⟨s, hs, h2, h3⟩ := xo_pair hr hq hco hc2 (hlt d hd) (hb.trans hFq) hA (hX d hd) hx'
    rw [show 2 * (q * (F * d)) = 2 * F * (q * d) by ring] at h2 h3
    exact ⟨s, fun _ _ => ⟨fun h => hc1 (h.trans hs), h2, h3⟩⟩
  choose s hs using hs
  refine ⟨X, s, ⟨fun d hd => (xo_one hA (hX d hd.1.ne_zero)).1, fun d hd => (xo_one hA (hX d hd.1.ne_zero)).2.1,
    fun d hd => (xo_one hA (hX d hd.1.ne_zero)).2.2, fun d q hq ha => (hs d q hq ha).1,
    fun d q hq ha => (hs d q hq ha).2.1, fun d q hq ha => (hs d q hq ha).2.2⟩, ?_⟩
  have h := hX 1 one_ne_zero
  rw [mul_one] at h
  exact xo_ord hr h1 hA h
