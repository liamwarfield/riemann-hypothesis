module

public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Existence

@[expose] public section

section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportBB
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ValuativeRel Function

theorem continuous_gal_of_fix {k F k' F' : Type*} [Field k] [Field F] [Algebra k F] [Field k'] [Field F']
    [Algebra k' F'] [Algebra.IsIntegral k F] (φ : (F ≃ₐ[k] F) →* (F' ≃ₐ[k'] F'))
    (h : ∀ y : F', ∃ x : F, ∀ σ : F ≃ₐ[k] F, σ x = x → φ σ y = y) : Continuous φ := by
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, map_one]
  refine Filter.tendsto_def.2 fun s hs => ?_
  rw [krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨E, hE, hEs⟩ := hs
  let b := Module.finBasis k' E
  choose c hc using h
  have hopen : IsOpen (⋂ i, {σ : F ≃ₐ[k] F | σ (c (b i : F')) = c (b i : F')}) :=
    isOpen_iInter_of_finite fun i => stabilizer_isOpen_of_isIntegral (K := k) (c (b i : F'))
  refine Filter.mem_of_superset (hopen.mem_nhds (Set.mem_iInter.2 fun i => rfl)) fun σ hσ => hEs ?_
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : F') := by
    have := congrArg E.val (b.sum_repr ⟨x, hx⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    exact this.symm
  rw [hx']
  show φ σ _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, map_mul, AlgEquiv.commutes]
  exact congrArg _ (hc _ σ (Set.mem_iInter.1 hσ i))

theorem exists_topAb_iso {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (φ : G ≃* H) (hφ : IsHomeomorph φ) :
    ∃ ψ : TopologicalAbelianization G ≃* TopologicalAbelianization H, IsHomeomorph ψ ∧
      ∀ g : G, ψ (QuotientGroup.mk g) = QuotientGroup.mk (φ g) := by
  have hc : (commutator G).map (φ : G →* H) = commutator H := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ φ.surjective]
  have hmap : (Subgroup.topologicalClosure (commutator G)).map (φ : G →* H) =
      Subgroup.topologicalClosure (commutator H) := by
    apply SetLike.coe_injective
    rw [Subgroup.coe_map, Subgroup.topologicalClosure_coe, Subgroup.topologicalClosure_coe, ← hc, Subgroup.coe_map]
    exact (hφ.homeomorph φ).image_closure _
  let ψ := QuotientGroup.congr _ _ φ hmap
  have h1 : Continuous ψ :=
    (QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff).2
      (QuotientGroup.continuous_mk.comp hφ.continuous)
  have hs : Continuous φ.symm :=
    (φ.toEquiv.toHomeomorphOfContinuousOpen hφ.continuous hφ.isOpenMap).symm.continuous
  have h2 : Continuous ψ.symm :=
    (QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff).2
      (QuotientGroup.continuous_mk.comp hs)
  exact ⟨ψ, (Homeomorph.mk ψ.toEquiv h1 h2).isHomeomorph, fun g => rfl⟩

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] {p : ℕ} [Fact p.Prime] (m : Model K p)

theorem Model.E_symm_coe (x : m.K') :
    m.E.symm (x : PadicAlgCl p) = algebraMap K (AlgebraicClosure K) (m.e.symm x) := by
  rw [RingEquiv.symm_apply_eq, m.comm, RingEquiv.apply_symm_apply]

include m in
theorem Model.charZero : CharZero K :=
  charZero_of_injective_ringHom (f := (m.e.symm : m.K' →+* K)) m.e.symm.injective

noncomputable def Model.galIso : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) ≃* GK p m.K' where
  toFun σ :=
    { m.E.symm.trans (σ.toRingEquiv.trans m.E) with
      commutes' := fun x => by
        show m.E (σ (m.E.symm (x : PadicAlgCl p))) = (x : PadicAlgCl p)
        rw [m.E_symm_coe, AlgEquiv.commutes, m.comm, RingEquiv.apply_symm_apply] }
  invFun τ :=
    { m.E.trans (τ.toRingEquiv.trans m.E.symm) with
      commutes' := fun x => by
        show m.E.symm (τ (m.E (algebraMap K (AlgebraicClosure K) x))) = algebraMap K (AlgebraicClosure K) x
        rw [m.comm, show τ ((m.e x : m.K') : PadicAlgCl p) = _ from τ.commutes (m.e x)]
        show m.E.symm ((m.e x : m.K') : PadicAlgCl p) = _
        rw [m.E_symm_coe, RingEquiv.symm_apply_apply] }
  left_inv σ := by
    ext x
    show m.E.symm (m.E (σ (m.E.symm (m.E x)))) = σ x
    rw [RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
  right_inv τ := by
    ext x
    show m.E (m.E.symm (τ (m.E (m.E.symm x)))) = τ x
    rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  map_mul' σ τ := by
    ext x
    show m.E (σ (τ (m.E.symm x))) = m.E (σ (m.E.symm (m.E (τ (m.E.symm x)))))
    rw [RingEquiv.symm_apply_apply]

theorem Model.isGalIso_galIso : m.IsGalIso m.galIso := fun σ x => by
  show m.E (σ (m.E.symm (m.E x))) = m.E (σ x)
  rw [RingEquiv.symm_apply_apply]

variable {m}

theorem Model.IsGalIso.symm_apply {φ} (hφ : m.IsGalIso φ) (τ : GK p m.K') (x : AlgebraicClosure K) :
    m.E (φ.symm τ x) = τ (m.E x) := by
  rw [← hφ, MulEquiv.apply_symm_apply]

theorem Model.IsGalIso.galois_iso_isHomeomorph {φ} (hφ : m.IsGalIso φ) : IsHomeomorph φ := by
  have hint : Algebra.IsIntegral m.K' (PadicAlgCl p) := Algebra.IsIntegral.tower_top (R := ℚ_[p])
  have h1 : Continuous φ.toMonoidHom := continuous_gal_of_fix φ.toMonoidHom fun y => ⟨m.E.symm y, fun σ hσ => by
    show φ σ y = y
    have := hφ σ (m.E.symm y)
    rwa [hσ, RingEquiv.apply_symm_apply] at this⟩
  have h2 : Continuous φ.symm.toMonoidHom := continuous_gal_of_fix φ.symm.toMonoidHom fun y => ⟨m.E y, fun τ hτ => by
    show φ.symm τ y = y
    apply m.E.injective
    rw [hφ.symm_apply, hτ]⟩
  exact (Homeomorph.mk φ.toEquiv h1 h2).isHomeomorph

theorem Model.isFrobeniusLift_iff_model [IsNonarchimedeanLocalField K] {φ} (hφ : m.IsGalIso φ)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) : IsFrobeniusLift K g ↔ IsFrob p m.K' (φ g) := by
  constructor
  · intro h y hy
    have h1 := h (m.E.symm y) ((m.mem_integral_closure_iff_norm _).2 (by rwa [RingEquiv.apply_symm_apply]))
    rw [m.mem_maximal_ideal_closure_iff_norm, map_sub, map_pow, ← hφ, RingEquiv.apply_symm_apply, m.card_residue_field_model] at h1
    exact h1
  · intro h x hx
    have h1 := h (m.E x) ((m.mem_integral_closure_iff_norm _).1 hx)
    rw [m.mem_maximal_ideal_closure_iff_norm, map_sub, map_pow, ← hφ, m.card_residue_field_model]
    exact h1

theorem Model.exists_abelianization_iso {φ} (hφ : m.IsGalIso φ) :
    ∃ ψ : Field.absoluteGaloisGroupAbelianization K ≃* GKab p m.K', IsHomeomorph ψ ∧
      ∀ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ψ (toAb K g) = toAbK p m.K' (φ g) :=
  exists_topAb_iso φ hφ.galois_iso_isHomeomorph

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.RecArtin
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

theorem exists_artin_hom (hK : FiniteDimensional ℚ_[p] K) : ∃ Art : Kˣ →* GKab p K, ∀ (a : Kˣ) (g : GK p K), toAbK p K g = Art a →
    ∀ L, IsAbLK p K L → IsRecip p K L a g := by
  classical
  let γ : IntermediateField ℚ_[p] (PadicAlgCl p) → Kˣ → GK p K := fun L a =>
    if h : IsAbLK p K L then (exists_isRecip h a).choose else 1
  have hγ : ∀ L, IsAbLK p K L → ∀ a, IsRecip p K L a (γ L a) := by
    intro L hL a
    simp only [γ, dif_pos hL]
    exact (exists_isRecip hL a).choose_spec
  obtain ⟨f, hf⟩ := exists_hom_GKab hK γ
    (fun L hL a b => IsRecip.unique hL (hγ L hL (a * b)) ((hγ L hL a).mul (hγ L hL b)))
    (fun L L' hL hL' hle a => IsRecip.unique hL (hγ L hL a) ((hγ L' hL' a).of_le hle))
  exact ⟨f, fun a g hg L hL => (hγ L hL a).congr (hf L hL a g hg)⟩

theorem isFrob_of_forall_Kn (hK : FiniteDimensional ℚ_[p] K) (g : GK p K)
    (h : ∀ n, 0 < n → (frobK p K)⁻¹ * g ∈ subG p K (Kn p K n)) : IsFrob p K g := by
  rw [isFrob_iff hK]
  intro ζ m hm hζ
  obtain ⟨n, hn, hζn⟩ := (mem_Kur_iff hK ζ).1 (mem_Kur_of_pow hK hm hζ)
  have h1 : frobK p K ζ = g ζ :=
    (mk_eq_mk_iff (M := Kn p K n) (frobK p K) g).1 (QuotientGroup.eq.2 (h n hn)) ζ hζn
  rw [← h1]
  exact (isFrob_iff hK _).1 (isFrob_frobK hK) ζ m hm hζ

theorem isFrob_of_isRecip (hK : FiniteDimensional ℚ_[p] K) (π : Kˣ) (hπ : vK p K π = 1) (g : GK p K)
    (h : ∀ L, IsAbLK p K L → IsRecip p K L π g) : IsFrob p K g :=
  isFrob_of_forall_Kn hK g fun _ hn =>
    IsRecip.unique (isAbLK_Kn hK hn) (isRecip_uniformiser_Kn hK hn π hπ) (h _ (isAbLK_Kn hK hn))

theorem IsRecip.inv_mul_mem (hK : FiniteDimensional ℚ_[p] K) (hL : IsAbLK p K L) {a b : Kˣ} {g g' : GK p K}
    (h : IsRecip p K L a g) (h' : IsRecip p K L b g') : g⁻¹ * g' ∈ subG p K L ↔ a⁻¹ * b ∈ normGrp p K L := by
  obtain ⟨k, hk⟩ := exists_isRecip hL (a⁻¹ * b)
  have h1 : IsRecip p K L b (g * k) := by
    have := h.mul hk
    rwa [mul_inv_cancel_left] at this
  have h2 : (g * k)⁻¹ * g' ∈ subG p K L := IsRecip.unique hL h1 h'
  rw [← hk.mem_subG_iff hK hL]
  have h3 : g⁻¹ * g' = k * ((g * k)⁻¹ * g') := by group
  rw [h3]
  exact Subgroup.mul_mem_cancel_right _ h2

theorem isArtinK_of_isRecip (hK : FiniteDimensional ℚ_[p] K) (Art : Kˣ →* GKab p K)
    (h : ∀ (a : Kˣ) (g : GK p K), toAbK p K g = Art a → ∀ L, IsAbLK p K L → IsRecip p K L a g) :
    IsArtinK p K Art := by
  have hsurj : ∀ L, IsAbLK p K L → ∀ g : GK p K, ∃ (x : Kˣ) (g' : GK p K), toAbK p K g' = Art x ∧
      g'⁻¹ * g ∈ subG p K L := by
    intro L hL g
    obtain ⟨a, ha⟩ := exists_isRecip_of_gal hK hL g
    obtain ⟨g', hg'⟩ := toAbK_surjective (Art a)
    exact ⟨a, g', hg', IsRecip.unique hL (h a g' hg' L hL) ha⟩
  refine ⟨?_, ?_, (denseRange_GKab_iff hK Art).2 hsurj, ?_, fun L hL => ⟨hsurj L hL, ?_⟩⟩
  · rw [continuous_GKab_iff hK]
    intro L hL x
    have hopen : IsOpen ((fun y : Kˣ => x⁻¹ * y) ⁻¹' (normGrp p K L : Set Kˣ)) :=
      (isOpen_normGrp hK hL.fin hL.le).preimage (continuous_const.mul continuous_id)
    have hx : x ∈ (fun y : Kˣ => x⁻¹ * y) ⁻¹' (normGrp p K L : Set Kˣ) := by
      show x⁻¹ * x ∈ normGrp p K L
      rw [inv_mul_cancel]; exact one_mem _
    filter_upwards [hopen.mem_nhds hx] with y hy g g' hg hg'
    exact (IsRecip.inv_mul_mem hK hL (h x g hg L hL) (h y g' hg' L hL)).2 hy
  · rw [injective_iff_map_eq_one]
    intro a ha
    refine eq_one_of_forall_mem_normGrp hK a fun L hL => ?_
    have h1 : toAbK p K 1 = Art a := by rw [map_one, ha]
    exact ((h a 1 h1 L hL).mem_subG_iff hK hL).1 (one_mem _)
  · intro π hπ g hg
    exact isFrob_of_isRecip hK π hπ g (h π g hg)
  · intro x g hg
    exact (h x g hg L hL).mem_subG_iff hK hL

theorem exists_isArtinK (hK : FiniteDimensional ℚ_[p] K) : ∃ Art : Kˣ →* GKab p K, IsArtinK p K Art := by
  obtain ⟨Art, h⟩ := exists_artin_hom hK
  exact ⟨Art, isArtinK_of_isRecip hK Art h⟩

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportB
section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportBC
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ValuativeRel Function

open scoped commutatorElement

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] {p : ℕ} [Fact p.Prime] (m : Model K p)

noncomputable def Model.mapField (L : IntermediateField K (AlgebraicClosure K)) :
    IntermediateField ℚ_[p] (PadicAlgCl p) :=
  (L.toSubfield.map (m.E : AlgebraicClosure K →+* PadicAlgCl p)).toIntermediateField fun x =>
    ⟨algebraMap K _ (m.e.symm (algebraMap ℚ_[p] m.K' x)), L.algebraMap_mem _, by
      show m.E _ = _
      rw [m.comm, RingEquiv.apply_symm_apply]
      rfl⟩

theorem Model.corr_mapField (L : IntermediateField K (AlgebraicClosure K)) : m.Corr L (m.mapField L) := fun x =>
  ⟨by rintro ⟨y, hy, hyx⟩; rwa [← m.E.injective hyx], fun hx => ⟨x, hx, rfl⟩⟩

noncomputable def Model.comapField (L' : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : m.K' ≤ L') :
    IntermediateField K (AlgebraicClosure K) :=
  (L'.toSubfield.comap (m.E : AlgebraicClosure K →+* PadicAlgCl p)).toIntermediateField fun x => by
    show m.E (algebraMap K _ x) ∈ L'
    rw [m.comm]
    exact h (m.e x).2

theorem Model.corr_comapField (L' : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : m.K' ≤ L') :
    m.Corr (m.comapField L' h) L' := fun _ => Iff.rfl

variable {m} {L : IntermediateField K (AlgebraicClosure K)} {L' : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem Model.Corr.le (h : m.Corr L L') : m.K' ≤ L' := fun x hx => by
  have := (h (algebraMap K _ (m.e.symm ⟨x, hx⟩))).2 (L.algebraMap_mem _)
  rwa [m.comm, RingEquiv.apply_symm_apply] at this

noncomputable def Model.Corr.equiv (h : m.Corr L L') : L ≃+* IntermediateField.extendScalars h.le where
  toFun x := ⟨m.E x, (h x).2 x.2⟩
  invFun y := ⟨m.E.symm y, (h _).1 (by rw [RingEquiv.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext (m.E.symm_apply_apply _)
  right_inv y := Subtype.ext (m.E.apply_symm_apply _)
  map_mul' x y := Subtype.ext (map_mul m.E _ _)
  map_add' x y := Subtype.ext (map_add m.E _ _)

theorem Model.Corr.equiv_comp (h : m.Corr L L') :
    (algebraMap m.K' (IntermediateField.extendScalars h.le)).comp (m.e : K →+* m.K') =
      (h.equiv : L →+* IntermediateField.extendScalars h.le).comp (algebraMap K L) :=
  RingHom.ext fun x => Subtype.ext (m.comm x).symm

theorem Model.Corr.equiv_symm_comp (h : m.Corr L L') :
    (algebraMap K L).comp (m.e.symm : m.K' →+* K) =
      (h.equiv.symm : IntermediateField.extendScalars h.le →+* L).comp
        (algebraMap m.K' (IntermediateField.extendScalars h.le)) :=
  RingHom.ext fun x => Subtype.ext (m.E_symm_coe x).symm

theorem Model.Corr.finite_iff (h : m.Corr L L') : FiniteDimensional K L ↔ FiniteDimensional ℚ_[p] L' := by
  constructor
  · intro hL
    have h1 : Module.Finite m.K' (IntermediateField.extendScalars h.le) :=
      Module.Finite.of_equiv_equiv m.e h.equiv h.equiv_comp
    have := m.fin
    have h2 : FiniteDimensional ℚ_[p] (IntermediateField.extendScalars h.le) :=
      FiniteDimensional.trans ℚ_[p] m.K' _
    exact h2
  · intro hL'
    have := finDim_extendScalars_of_le p hL' h.le
    exact Module.Finite.of_equiv_equiv m.e.symm h.equiv.symm h.equiv_symm_comp

theorem Model.Corr.norm_eq (h : m.Corr L L') (z : L) :
    m.e (Algebra.norm K z) = Algebra.norm m.K' (h.equiv z) := by
  rw [Algebra.norm_eq_of_equiv_equiv m.e h.equiv h.equiv_comp, RingEquiv.apply_symm_apply]

theorem Model.mem_fixingSubgroup_iff_model {φ} (hφ : m.IsGalIso φ) (h : m.Corr L L')
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) : g ∈ L.fixingSubgroup ↔ φ g ∈ subG p m.K' L' := by
  rw [IntermediateField.mem_fixingSubgroup_iff, mem_subG_iff]
  constructor
  · intro hg y hy
    have hx : m.E.symm y ∈ L := (h _).1 (by rwa [RingEquiv.apply_symm_apply])
    have := hφ g (m.E.symm y)
    rwa [hg _ hx, RingEquiv.apply_symm_apply] at this
  · intro hg x hx
    apply m.E.injective
    rw [← hφ]
    exact hg _ ((h x).2 hx)

theorem Model.abelian_restriction_eq_one_iff {φ} (hφ : m.IsGalIso φ) (h : m.Corr L L') (hL : IsFiniteAbelian K L)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    abRestrict K L hL (toAb K g) = 1 ↔ φ g ∈ subG p m.K' L' := by
  have := hL.isGalois
  rw [abRestrict_mk, ← Model.mem_fixingSubgroup_iff_model hφ h g, ← IntermediateField.restrictNormalHom_ker,
    MonoidHom.mem_ker]

theorem map_commutator_mulEquiv {G H : Type*} [Group G] [Group H] (φ : G ≃* H) :
    (commutator G).map (φ : G →* H) = commutator H := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ φ.surjective]

theorem Model.isFiniteAbelian_iff_model (h : m.Corr L L') : IsFiniteAbelian K L ↔ IsAbLK p m.K' L' := by
  have hφ := m.isGalIso_galIso
  constructor
  · intro hL
    refine ⟨h.le, h.finite_iff.1 hL.finiteDimensional, ?_⟩
    intro τ hτ
    rw [← map_commutator_mulEquiv m.galIso] at hτ
    obtain ⟨g, hg, rfl⟩ := hτ
    show m.galIso g ∈ _
    rw [← Model.abelian_restriction_eq_one_iff hφ h hL]
    have h1 : toAb K g = 1 :=
      (QuotientGroup.eq_one_iff (N := Subgroup.topologicalClosure (commutator (Field.absoluteGaloisGroup K))) g).2
        (Subgroup.le_topologicalClosure (G := Field.absoluteGaloisGroup K) _ hg)
    rw [h1, map_one]
  · intro hL'
    have := m.charZero
    have hfd := h.finite_iff.2 hL'.fin
    have hn : L.fixingSubgroup.Normal := by
      have h1 : L.fixingSubgroup = (subG p m.K' L').comap m.galIso.toMonoidHom := by
        ext g
        exact Model.mem_fixingSubgroup_iff_model hφ h g
      rw [h1]
      have := hL'.normal
      infer_instance
    have hG : IsGalois K L := (InfiniteGalois.normal_iff_isGalois L).1 hn
    refine ⟨hfd, hG, fun a b => ?_⟩
    obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure K) a
    obtain ⟨g', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure K) b
    rw [← map_mul, ← map_mul, ← inv_mul_eq_one, ← map_inv, ← map_mul, ← MonoidHom.mem_ker,
      IntermediateField.restrictNormalHom_ker, Model.mem_fixingSubgroup_iff_model hφ h]
    apply hL'.comm
    have h2 : (g * g')⁻¹ * (g' * g) = ⁅g'⁻¹, g⁻¹⁆ := by
      rw [commutatorElement_def]; group
    rw [h2, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem Model.mem_normGroup_iff_model (h : m.Corr L L') (hL : FiniteDimensional K L) (x : Kˣ) :
    x ∈ normGroup K L ↔ m.eU x ∈ normGrp p m.K' L' := by
  have hL' := h.finite_iff.1 hL
  rw [mem_normGrp_iff]
  constructor
  · rintro ⟨y, rfl⟩
    let y' : (PadicAlgCl p)ˣ := Units.map (m.E : AlgebraicClosure K →* PadicAlgCl p)
      (Units.map (algebraMap L (AlgebraicClosure K) : L →* AlgebraicClosure K) y)
    have hy' : (Additive.ofMul y' : KbarMult p) ∈ multOf p L' := (h _).2 y.1.2
    refine ⟨Additive.ofMul y', hy', ?_⟩
    refine Additive.toMul.injective (Units.ext ?_)
    refine (normHom_eq_algebraNorm hL' h.le _ hy').trans ?_
    exact congrArg Subtype.val (h.norm_eq (y : L)).symm
  · rintro ⟨y, hy, hyx⟩
    let w : IntermediateField.extendScalars h.le := ⟨((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p), hy⟩
    have hw : w ≠ 0 := fun h0 => (Additive.toMul y : (PadicAlgCl p)ˣ).ne_zero (congrArg Subtype.val h0)
    have hz : h.equiv.symm w ≠ 0 := by simpa using hw
    refine ⟨Units.mk0 _ hz, Units.ext (m.e.injective (Subtype.ext ?_))⟩
    show ((m.e (Algebra.norm K (h.equiv.symm w)) : m.K') : PadicAlgCl p) = _
    rw [h.norm_eq, RingEquiv.apply_symm_apply, ← normHom_eq_algebraNorm hL' h.le y hy, hyx]
    rfl

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ValuativeRel Function

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] {p : ℕ} [Fact p.Prime]
  (m : Model K p)

theorem Model.isUniformiser_iff (π : Kˣ) : IsUniformiser K (π : K) ↔ vK p m.K' (m.eU π) = 1 := m.isUniformiser_iff_valuation_one π

theorem Model.isHomeomorph_eU : IsHomeomorph m.eU := m.isHomeomorph_units_model

theorem Model.exists_isGalIso : ∃ φ, m.IsGalIso φ := ⟨m.galIso, m.isGalIso_galIso⟩

theorem Model.isFrobeniusLift_iff {φ} (hφ : m.IsGalIso φ) (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    IsFrobeniusLift K g ↔ IsFrob p m.K' (φ g) := Model.isFrobeniusLift_iff_model hφ g

theorem Model.exists_abIso {φ} (hφ : m.IsGalIso φ) :
    ∃ ψ : Field.absoluteGaloisGroupAbelianization K ≃* GKab p m.K', IsHomeomorph ψ ∧
      ∀ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ψ (toAb K g) = toAbK p m.K' (φ g) := Model.exists_abelianization_iso hφ

theorem Model.exists_corr (L : IntermediateField K (AlgebraicClosure K)) :
    ∃ L' : IntermediateField ℚ_[p] (PadicAlgCl p), m.K' ≤ L' ∧ m.Corr L L' :=
  ⟨m.mapField L, (m.corr_mapField L).le, m.corr_mapField L⟩

theorem Model.exists_corr' (L' : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : m.K' ≤ L') :
    ∃ L : IntermediateField K (AlgebraicClosure K), m.Corr L L' :=
  ⟨m.comapField L' h, m.corr_comapField L' h⟩

theorem Model.isFiniteAbelian_iff {L : IntermediateField K (AlgebraicClosure K)}
    {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : m.Corr L L') :
    IsFiniteAbelian K L ↔ IsAbLK p m.K' L' := Model.isFiniteAbelian_iff_model h

theorem Model.abRestrict_eq_one_iff {φ} (hφ : m.IsGalIso φ) {L : IntermediateField K (AlgebraicClosure K)}
    {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : m.Corr L L') (hL : IsFiniteAbelian K L)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    abRestrict K L hL (toAb K g) = 1 ↔ φ g ∈ subG p m.K' L' := Model.abelian_restriction_eq_one_iff hφ h hL g

theorem Model.mem_normGroup_iff {L : IntermediateField K (AlgebraicClosure K)}
    {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : m.Corr L L') (hL : FiniteDimensional K L) (x : Kˣ) :
    x ∈ normGroup K L ↔ m.eU x ∈ normGrp p m.K' L' := Model.mem_normGroup_iff_model h hL x

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportA
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ValuativeRel Function Filter Topology

section

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem hausdorff_local_field : T2Space K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

variable {K}

theorem valuation_lt_one_iff_topologically_nilpotent (x : K) :
    valuation K x < 1 ↔ Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  constructor
  · intro hx
    rw [(IsValuativeTopology.hasBasis_nhds_zero K).tendsto_right_iff]
    intro γ _
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hx γ
    filter_upwards [eventually_ge_atTop n] with m hm
    rw [map_pow]
    exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' hx.le hm) hn
  · intro h
    have h1 := (IsValuativeTopology.hasBasis_nhds_zero K).tendsto_right_iff.1 h 1 trivial
    obtain ⟨n, hn⟩ := (h1.and (eventually_ge_atTop 1)).exists
    obtain ⟨hn1, hn2⟩ := hn
    rw [Set.mem_ofPred_eq, map_pow, Units.val_one] at hn1
    by_contra hc
    exact absurd hn1 (not_lt.2 (one_le_pow₀ (not_lt.1 hc)))

theorem isClosed_valuation_integers : IsClosed (𝒪[K] : Set K) := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  exact Valued.isClosed_integer K

end

section

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K]

theorem exists_residue_char : ∃ p : ℕ, p.Prime ∧ valuation K (p : K) < 1 := by
  obtain ⟨p, hp⟩ := CharP.exists 𝓀[K]
  have hpp : p.Prime := by
    rcases CharP.char_is_prime_or_zero 𝓀[K] p with h | h
    · exact h
    · subst h
      have := CharP.charP_to_charZero 𝓀[K]
      exact absurd (inferInstance : Finite 𝓀[K]) (not_finite_iff_infinite.2 inferInstance)
  refine ⟨p, hpp, ?_⟩
  have h0 : IsLocalRing.residue 𝒪[K] (p : 𝒪[K]) = 0 := by
    rw [map_natCast]; exact CharP.cast_eq_zero _ p
  rw [IsLocalRing.residue_eq_zero_iff] at h0
  have := (Valuation.Integer.not_isUnit_iff_valuation_lt_one (v := valuation K) (x := (p : 𝒪[K]))).1 h0
  simpa using this

theorem finite_over_padic (p : ℕ) [Fact p.Prime] (f : ℚ_[p] →+* K) (hf : Continuous f) :
    (letI := f.toAlgebra; FiniteDimensional ℚ_[p] K) := by
  let := f.toAlgebra
  have := hausdorff_local_field K
  have : ContinuousSMul ℚ_[p] K := continuousSMul_of_algebraMap _ _ hf
  exact FiniteDimensional.of_locallyCompactSpace ℚ_[p]

end

section

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K]
  (p : ℕ) [Fact p.Prime]

theorem valuation_intCast_le_one_local_class_field (n : ℤ) : valuation K (n : K) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).1 (intCast_mem 𝒪[K] n)

theorem rational_valuation_le_one (hp : valuation K (p : K) < 1) (q : ℚ) (hq : Rat.padicValuation p q ≤ 1) :
    valuation K (q : K) ≤ 1 := by
  rw [Rat.padicValuation_le_one_iff] at hq
  have hc : IsCoprime (p : ℤ) (q.den : ℤ) :=
    Int.isCoprime_iff_gcd_eq_one.2 (by
      rw [Int.gcd_natCast_natCast]
      exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hq)
  obtain ⟨a, b, hab⟩ := hc
  have hden : 1 ≤ valuation K (q.den : K) := by
    by_contra hlt
    rw [not_le] at hlt
    have e : ((a : K) * (p : K) + (b : K) * (q.den : K)) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → K) hab
    have h1 : valuation K ((a : K) * (p : K)) < 1 := by
      rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (valuation_intCast_le_one_local_class_field a)) hp
    have h2 : valuation K ((b : K) * (q.den : K)) < 1 := by
      rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (valuation_intCast_le_one_local_class_field b)) hlt
    have := (valuation K).map_add_lt h1 h2
    rw [e, map_one] at this
    exact lt_irrefl _ this
  rw [Rat.cast_def, map_div₀]
  have hpos : 0 < valuation K (q.den : K) := lt_of_lt_of_le zero_lt_one hden
  rw [div_le_one₀ hpos]
  exact (valuation_intCast_le_one_local_class_field q.num).trans hden

noncomputable def transportRatHom (K : Type) [Field K] [CharZero K] : WithVal (Rat.padicValuation p) →+* K :=
  (algebraMap ℚ K).comp (WithVal.equiv (Rat.padicValuation p)).toRingHom

theorem transportRatHom_apply (x : WithVal (Rat.padicValuation p)) :
    transportRatHom p K x = ((WithVal.equiv (Rat.padicValuation p) x : ℚ) : K) := rfl

theorem rational_valuation_le_pow (hp : valuation K (p : K) < 1) (q : ℚ) (n : ℕ)
    (hq : Rat.padicValuation p q < Rat.padicValuation p ((p : ℚ) ^ n)) :
    valuation K (q : K) ≤ valuation K (p : K) ^ n := by
  have hp0 : ((p : ℚ) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hpv : Rat.padicValuation p ((p : ℚ) ^ n) ≠ 0 := by
    rw [ne_eq, map_eq_zero]; exact hp0
  have h1 : Rat.padicValuation p (q / (p : ℚ) ^ n) ≤ 1 := by
    rw [map_div₀]
    exact (div_lt_one₀ (zero_lt_iff.2 hpv)).2 hq |>.le
  have h2 := rational_valuation_le_one (K := K) p hp _ h1
  have hpF : ((p : K) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hvF : valuation K ((p : K) ^ n) ≠ 0 := by rw [ne_eq, map_eq_zero]; exact hpF
  push_cast at h2
  rw [map_div₀, div_le_one₀ (zero_lt_iff.2 hvF), map_pow] at h2
  exact h2

theorem continuous_rational_hom_of_valuation (hp : valuation K (p : K) < 1) : Continuous (transportRatHom p K) := by
  refine continuous_of_continuousAt_zero (transportRatHom p K) ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff s).1 hs
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hp γ
  let y : WithVal (Rat.padicValuation p) := WithVal.toVal _ ((p : ℚ) ^ n)
  have hy0 : y ≠ 0 := by
    simp only [y, ne_eq, WithVal.toVal_eq_zero]
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hU := Valued.isOpen_ball (WithVal (Rat.padicValuation p)) (Valued.v.restrict y)
  have h0 : (0 : WithVal (Rat.padicValuation p)) ∈ {x | Valued.v.restrict x < Valued.v.restrict y} := by
    simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff, map_zero]
    exact zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hy0)
  rw [Filter.mem_map]
  filter_upwards [hU.mem_nhds h0] with x hx
  show transportRatHom p K x ∈ s
  simp only [Valuation.restrict_lt_iff] at hx
  apply hγ
  rw [Set.mem_ofPred_eq, transportRatHom_apply]
  exact lt_of_le_of_lt (rational_valuation_le_pow p hp _ n hx) hn

theorem exists_continuous_padic_hom (hp : valuation K (p : K) < 1) : ∃ f : ℚ_[p] →+* K, Continuous f := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  refine ⟨(UniformSpace.Completion.extensionHom (transportRatHom p K) (continuous_rational_hom_of_valuation p hp)).comp
    (Padic.withValRingEquiv (p := p)).symm.toRingHom, ?_⟩
  exact UniformSpace.Completion.continuous_extension.comp (Padic.withValUniformEquiv (p := p)).symm.continuous

end

section

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {p : ℕ} [Fact p.Prime]

theorem padic_hom_valuation_lt_one (f : ℚ_[p] →+* K) (hf : Continuous f) (x : ℚ_[p]) (hx : ‖x‖ < 1) :
    valuation K (f x) < 1 := by
  rw [valuation_lt_one_iff_topologically_nilpotent]
  have h := (tendsto_pow_atTop_nhds_zero_iff_norm_lt_one (x := x)).2 hx
  have h2 := (hf.tendsto 0).comp h
  rw [map_zero] at h2
  refine h2.congr fun n => ?_
  simp

theorem padic_hom_mem_integers_iff (f : ℚ_[p] →+* K) (hf : Continuous f) (x : ℚ_[p]) :
    f x ∈ 𝒪[K] ↔ ‖x‖ ≤ 1 := by
  constructor
  · intro h
    by_contra hc
    rw [not_le] at hc
    have hx0 : x ≠ 0 := by rintro rfl; simp at hc; linarith
    have h1 : ‖x⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hc
    have h2 := padic_hom_valuation_lt_one f hf _ h1
    rw [Valuation.mem_integer_iff] at h
    have h3 : valuation K (f x * f x⁻¹) < 1 := by
      rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' h) h2
    rw [← map_mul, mul_inv_cancel₀ hx0, map_one, map_one] at h3
    exact lt_irrefl _ h3
  · intro h
    have hcl : IsClosed {z : ℤ_[p] | f (z : ℚ_[p]) ∈ (𝒪[K] : Set K)} :=
      isClosed_valuation_integers.preimage (hf.comp continuous_subtype_val)
    have hall : ∀ z : ℤ_[p], f (z : ℚ_[p]) ∈ (𝒪[K] : Set K) := by
      intro z
      refine PadicInt.denseRange_intCast.induction_on (p := fun z : ℤ_[p] => f (z : ℚ_[p]) ∈ (𝒪[K] : Set K)) z hcl ?_
      intro n
      simp only [PadicInt.coe_intCast, map_intCast, SetLike.mem_coe]
      exact intCast_mem 𝒪[K] n
    exact hall ⟨x, h⟩

end

theorem mem_integers_iff_norm_of_homeomorph {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {L : Type} [NormedField L] (e : K ≃+* L) (he : IsHomeomorph e) (x : K) :
    x ∈ 𝒪[K] ↔ ‖e x‖ ≤ 1 := by
  have key : ∀ y : K, valuation K y < 1 ↔ ‖e y‖ < 1 := by
    intro y
    rw [valuation_lt_one_iff_topologically_nilpotent, ← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
    have h0 : 𝓝 (0 : K) = comap e (𝓝 0) := by
      rw [← map_zero e]; exact he.isInducing.nhds_eq_comap 0
    rw [h0, tendsto_comap_iff]
    refine tendsto_congr fun n => ?_
    simp
  rw [Valuation.mem_integer_iff]
  by_cases hx : x = 0
  · subst hx; simp
  have h := key x⁻¹
  rw [map_inv₀, map_inv₀, norm_inv] at h
  have hv : 0 < valuation K x := zero_lt_iff.2 (by simpa using hx)
  have hn : 0 < ‖e x‖ := by rw [norm_pos_iff]; simpa using hx
  rw [inv_lt_one₀ hv, inv_lt_one₀ hn] at h
  rw [← not_lt, ← not_lt, h]

theorem exists_model_of_algebra (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] [ContinuousSMul ℚ_[p] K] :
    ∃ m : Model K p, ∀ x : ℚ_[p], (m.e (algebraMap ℚ_[p] K x) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) x := by
  have := hausdorff_local_field K
  let φ : K →ₐ[ℚ_[p]] PadicAlgCl p := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let e : K ≃ₐ[ℚ_[p]] φ.fieldRange := AlgEquiv.ofInjectiveField φ
  have hfin : FiniteDimensional ℚ_[p] φ.fieldRange := Module.Finite.equiv e.toLinearEquiv
  let _ : Algebra K (PadicAlgCl p) := φ.toRingHom.toAlgebra
  have : IsScalarTower ℚ_[p] K (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  have : Algebra.IsAlgebraic K (PadicAlgCl p) := Algebra.IsAlgebraic.tower_top (K := ℚ_[p]) K
  have : IsAlgClosure K (PadicAlgCl p) := ⟨inferInstance, inferInstance⟩
  let E : AlgebraicClosure K ≃ₐ[K] PadicAlgCl p := IsAlgClosure.equiv K _ _
  have hhomeo : IsHomeomorph e.toRingEquiv :=
    (e.toLinearEquiv.toContinuousLinearEquiv.toHomeomorph).isHomeomorph
  refine ⟨{ K' := φ.fieldRange, fin := hfin, e := e.toRingEquiv, E := E.toRingEquiv, comm := ?_, homeo := hhomeo, int := ?_ }, ?_⟩
  · intro x
    exact E.commutes x
  · intro x
    exact mem_integers_iff_norm_of_homeomorph e.toRingEquiv hhomeo x
  · intro x
    exact φ.commutes x

section

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K]

theorem exists_padic_hom (p : ℕ) [Fact p.Prime] (hp : valuation K (p : K) < 1) :
    ∃ f : ℚ_[p] →+* K, Continuous f ∧ ∀ x, f x ∈ 𝒪[K] ↔ ‖x‖ ≤ 1 := by
  obtain ⟨f, hf⟩ := exists_continuous_padic_hom (K := K) p hp
  exact ⟨f, hf, padic_hom_mem_integers_iff f hf⟩

theorem exists_model : ∃ (p : ℕ) (_ : Fact p.Prime), Nonempty (Model K p) := by
  obtain ⟨p, hpp, hp⟩ := exists_residue_char K
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨f, hf, -⟩ := exists_padic_hom K p hp
  let _ := f.toAlgebra
  have : FiniteDimensional ℚ_[p] K := finite_over_padic K p f hf
  have : ContinuousSMul ℚ_[p] K := continuousSMul_of_algebraMap _ _ hf
  obtain ⟨m, -⟩ := exists_model_of_algebra p K
  exact ⟨p, inferInstance, ⟨m⟩⟩

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ValuativeRel Function

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] {p : ℕ} [Fact p.Prime]
  (m : Model K p)

theorem toAb_surjective' (F : Type) [Field F] (a : Field.absoluteGaloisGroupAbelianization F) :
    ∃ g : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, toAb F g = a := QuotientGroup.mk'_surjective _ a

theorem toAb_inv_mul (F : Type) [Field F] (g h : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    toAb F (g⁻¹ * h) = (toAb F g)⁻¹ * toAb F h := by
  exact (map_mul (toAb F) g⁻¹ h).trans (congrArg (· * toAb F h) (map_inv (toAb F) g))

theorem continuous_symm_of_isHomeomorph {G H : Type*} [Mul G] [Mul H] [TopologicalSpace G] [TopologicalSpace H]
    (e : G ≃* H) (he : IsHomeomorph e) : Continuous e.symm := by
  rw [continuous_def]
  intro s hs
  have : e.symm ⁻¹' s = e '' s :=
    (Set.image_eq_preimage_of_inverse e.left_inv e.right_inv).symm ▸ rfl
  rw [this]
  exact he.isOpenMap s hs

theorem Model.isArtinK_of_isLocalArtinMap {φ} (hφ : m.IsGalIso φ)
    (ψ : Field.absoluteGaloisGroupAbelianization K ≃* GKab p m.K') (hψ : IsHomeomorph ψ)
    (hψφ : ∀ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ψ (toAb K g) = toAbK p m.K' (φ g))
    (Art : Kˣ →* Field.absoluteGaloisGroupAbelianization K) (h : IsLocalArtinMap K Art) :
    IsArtinK p m.K' ((ψ.toMonoidHom.comp Art).comp m.eU.symm.toMonoidHom) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hsymm : Continuous m.eU.symm := continuous_symm_of_isHomeomorph _ m.isHomeomorph_eU

  have key : ∀ (x' : (m.K')ˣ) (g' : GK p m.K'),
      toAbK p m.K' g' = ((ψ.toMonoidHom.comp Art).comp m.eU.symm.toMonoidHom) x' →
      toAb K (φ.symm g') = Art (m.eU.symm x') := by
    intro x' g' hg
    apply ψ.injective
    rw [hψφ, MulEquiv.apply_symm_apply, hg]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hψ.continuous.comp (h1.comp hsymm)
  · exact ψ.injective.comp (h2.comp m.eU.symm.injective)
  · exact (hψ.surjective.denseRange.comp h3 hψ.continuous).comp m.eU.symm.surjective.denseRange
      (hψ.continuous.comp h1)
  · intro π' hπ' g' hg'
    have := h4 (m.eU.symm π') ((m.isUniformiser_iff _).2 (by rwa [MulEquiv.apply_symm_apply]))
      (φ.symm g') (key _ _ hg')
    rw [m.isFrobeniusLift_iff hφ, MulEquiv.apply_symm_apply] at this
    exact this
  · intro L' hL'
    obtain ⟨L, hL⟩ := m.exists_corr' L' hL'.le
    have hab : IsFiniteAbelian K L := (m.isFiniteAbelian_iff hL).2 hL'
    obtain ⟨h6, h7⟩ := h5 L hab
    refine ⟨?_, ?_⟩
    · intro g'
      obtain ⟨x, hx⟩ := h6 (abRestrict K L hab (toAb K (φ.symm g')))
      obtain ⟨g2, hg2⟩ := toAb_surjective' K (Art x)
      refine ⟨m.eU x, φ g2, ?_, ?_⟩
      · rw [← hψφ, hg2]
        show _ = ψ (Art (m.eU.symm (m.eU x)))
        rw [MulEquiv.symm_apply_apply]
      · have : abRestrict K L hab (toAb K (g2⁻¹ * φ.symm g')) = 1 := by
          rw [toAb_inv_mul, map_mul, map_inv, hg2, ← hx]
          exact inv_mul_cancel _
        rw [m.abRestrict_eq_one_iff hφ hL hab] at this
        simpa using this
    · intro x' g' hg'
      have hk := key _ _ hg'
      have e1 : m.eU.symm x' ∈ ((abRestrict K L hab).comp Art).ker ↔ m.eU.symm x' ∈ normGroup K L := by
        rw [h7]
      rw [m.mem_normGroup_iff hL hab.finiteDimensional, MulEquiv.apply_symm_apply, MonoidHom.mem_ker,
        MonoidHom.comp_apply, ← hk, m.abRestrict_eq_one_iff hφ hL hab, MulEquiv.apply_symm_apply] at e1
      exact e1

theorem Model.isLocalArtinMap_of_isArtinK {φ} (hφ : m.IsGalIso φ)
    (ψ : Field.absoluteGaloisGroupAbelianization K ≃* GKab p m.K') (hψ : IsHomeomorph ψ)
    (hψφ : ∀ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ψ (toAb K g) = toAbK p m.K' (φ g))
    (Art : Kˣ →* Field.absoluteGaloisGroupAbelianization K)
    (h : IsArtinK p m.K' ((ψ.toMonoidHom.comp Art).comp m.eU.symm.toMonoidHom)) :
    IsLocalArtinMap K Art := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hψs : Continuous ψ.symm := continuous_symm_of_isHomeomorph _ hψ
  have hArt : ∀ x, ((ψ.toMonoidHom.comp Art).comp m.eU.symm.toMonoidHom) (m.eU x) = ψ (Art x) := by
    intro x
    show ψ (Art (m.eU.symm (m.eU x))) = _
    rw [MulEquiv.symm_apply_apply]
  have hfun : (Art : Kˣ → _) =
      ψ.symm ∘ ((ψ.toMonoidHom.comp Art).comp m.eU.symm.toMonoidHom) ∘ m.eU := by
    funext x
    show _ = ψ.symm (((ψ.toMonoidHom.comp Art).comp m.eU.symm.toMonoidHom) (m.eU x))
    rw [hArt, MulEquiv.symm_apply_apply]
  have key : ∀ (x : Kˣ) (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K), toAb K g = Art x →
      toAbK p m.K' (φ g) = ((ψ.toMonoidHom.comp Art).comp m.eU.symm.toMonoidHom) (m.eU x) := by
    intro x g hg
    rw [hArt, ← hψφ, hg]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hfun]
    exact hψs.comp (h1.comp m.isHomeomorph_eU.continuous)
  · rw [hfun]
    exact ψ.symm.injective.comp (h2.comp m.eU.injective)
  · rw [hfun]
    exact (ψ.symm.surjective.denseRange.comp h3 hψs).comp m.eU.surjective.denseRange
      (hψs.comp h1)
  · intro π hπ g hg
    rw [m.isFrobeniusLift_iff hφ]
    exact h4 (m.eU π) ((m.isUniformiser_iff _).1 hπ) (φ g) (key _ _ hg)
  · intro L hab
    obtain ⟨L', -, hL⟩ := m.exists_corr L
    have hL' : IsAbLK p m.K' L' := (m.isFiniteAbelian_iff hL).1 hab
    obtain ⟨h6, h7⟩ := h5 L' hL'
    refine ⟨?_, ?_⟩
    · intro τ
      have := hab.isGalois
      obtain ⟨g, hg⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) (AlgebraicClosure K) τ
      obtain ⟨x', g', hg', hmem⟩ := h6 (φ g)
      refine ⟨m.eU.symm x', ?_⟩
      have e1 : toAb K (φ.symm g') = Art (m.eU.symm x') := by
        apply ψ.injective
        rw [hψφ, MulEquiv.apply_symm_apply, hg']
        rfl
      have e2 : abRestrict K L hab (toAb K ((φ.symm g')⁻¹ * g)) = 1 := by
        rw [m.abRestrict_eq_one_iff hφ hL hab]
        simpa using hmem
      rw [toAb_inv_mul, map_mul, map_inv, inv_mul_eq_one] at e2
      rw [MonoidHom.comp_apply, ← e1, e2, abRestrict_mk, hg]
    · ext x
      obtain ⟨g, hg⟩ := toAb_surjective' K (Art x)
      rw [m.mem_normGroup_iff hL hab.finiteDimensional, ← h7 (m.eU x) (φ g) (key _ _ hg), MonoidHom.mem_ker,
        MonoidHom.comp_apply, ← hg, m.abRestrict_eq_one_iff hφ hL hab]

theorem Model.isLocalArtinMap_iff {φ} (hφ : m.IsGalIso φ)
    (ψ : Field.absoluteGaloisGroupAbelianization K ≃* GKab p m.K') (hψ : IsHomeomorph ψ)
    (hψφ : ∀ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ψ (toAb K g) = toAbK p m.K' (φ g))
    (Art : Kˣ →* Field.absoluteGaloisGroupAbelianization K) :
    IsLocalArtinMap K Art ↔
      IsArtinK p m.K' ((ψ.toMonoidHom.comp Art).comp m.eU.symm.toMonoidHom) :=
  ⟨m.isArtinK_of_isLocalArtinMap hφ ψ hψ hψφ Art, m.isLocalArtinMap_of_isArtinK hφ ψ hψ hψφ Art⟩

theorem Model.artin_reciprocity_of_model (h : ∃ Art, IsArtinK p m.K' Art) : LocalReciprocity K := by
  obtain ⟨Art', hA⟩ := h
  obtain ⟨φ, hφ⟩ := m.exists_isGalIso
  obtain ⟨ψ, hψ, hψφ⟩ := m.exists_abIso hφ
  refine ⟨(ψ.symm.toMonoidHom.comp Art').comp m.eU.toMonoidHom, ?_⟩
  rw [m.isLocalArtinMap_iff hφ ψ hψ hψφ]
  convert hA using 1
  ext x
  simp

theorem artin_reciprocity_char_zero (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K] : LocalReciprocity K := by
  obtain ⟨p, hp, ⟨m⟩⟩ := exists_model K
  exact m.artin_reciprocity_of_model (exists_isArtinK m.fin)

end ReciprocityTheory.DiscreteGroups.LocalClassField
