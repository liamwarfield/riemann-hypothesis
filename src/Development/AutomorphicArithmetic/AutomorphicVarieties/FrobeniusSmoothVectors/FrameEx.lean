module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CyclotomicInertiaSpan.CycIne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LinkEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Strict
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.RankLeOfCardLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.ToZModEqOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.ResH1SurjectiveOfIsomorphism
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.CastToZModPowOne

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.B1p
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC
open scoped Pointwise
attribute [local instance 10000] DivisionSemiring.to_moduleIsTorsionFree
private theorem exists_conj {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {A₀ A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (h₀ : IsPlaceOver A₀ v) (hA : IsPlaceOver A v) :
    ∃ u : G F Ω, ∀ x ∈ Ine (F := F) A, u⁻¹ * x * u ∈ Dec (F := F) A₀ := by
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := F) h₀ hA
  have h : IsLift (RingEquiv.refl F) g.toRingEquiv := fun x => g.commutes x
  have hm : ∀ x, g.toRingEquiv x ∈ A ↔ x ∈ A₀ := fun x => by
    show g • x ∈ A ↔ _
    rw [← hg]
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  exact ⟨g, fun x hx => conjGal_mem_Dec h hm hx.1⟩

theorem UpperTheory.V.GC.b1p :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] (Φ : Fr.Frame l k) (S : Finset (HeightOneSpectrum (𝓞 F))) (K : Subgroup (G F Ω)) (π : G F Ω →* Φ.Γ) (ι : ∀ v, Φ.Gv v →* G F Ω) (A : Φ.V → ValuationSubring Ω) (pl : Φ.V → HeightOneSpectrum (𝓞 F)) (e : Φ.Inf ≃ InfinitePlace F) (c : Φ.Inf → G F Ω), FLink l Φ S K π ι A pl e c → (∀ v, ∃ g, Φ.Ψ (Φ.loc v g) ^ 2 ≠ 1) → ∀ C₀ : ℕ, clRk l (K ⊓ (cycMod F Ω l 1).ker) ≤ C₀ → Module.rank k (H1C (k := k) (W := k) Φ.loc (chRep (Φ.Ψ⁻¹ ^ 2 * Φ.delK k)) fun _ => ⊥) ≤ C₀ := by
  intro F Ω _ _ _ _ _ l hl k _ _ Φ S K π ι A pl e c L h3 C₀ hC
  haveI := L.g.normal
  have hω : IsOpen ((cycMod F Ω l 1).ker : Set (G F Ω)) :=
    (isOpen_discrete {(1 : (ZMod (l ^ 1))ˣ)}).preimage GlobalTheory.Published.PoitouTate.continuous_cycMod
  have hidx : ¬ l ∣ (K ⊓ (cycMod F Ω l 1).ker).relIndex ⊤ := by
    rw [Subgroup.relIndex_top_right]
    intro h
    have h1 : (K ⊓ (cycMod F Ω l 1).ker).index ∣ K.index * (cycMod F Ω l 1).ker.index := by
      rw [← Subgroup.relIndex_mul_index (inf_le_left : K ⊓ (cycMod F Ω l 1).ker ≤ K), mul_comm,
        Subgroup.inf_relIndex_left]
      exact Nat.mul_dvd_mul_left _ (Subgroup.relIndex_dvd_index_of_normal _ _)
    rcases (hl.out.dvd_mul).1 (h.trans h1) with h2 | h2
    · exact L.g.idx h2
    · rw [Subgroup.index_ker] at h2
      have h4 := h2.trans (Subgroup.card_subgroup_dvd_card _)
      haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, pow_one, Nat.totient_prime hl.out] at h4
      have h5 := hl.out.two_le
      have := Nat.le_of_dvd (by omega) h4
      omega
  have key := strGen F Ω l k ⊤ (K ⊓ (cycMod F Ω l 1).ker) le_top (L.g.isOpen.inter hω) hidx Φ.Γ
    (π.comp (Subgroup.subtype ⊤)) (L.g.cont.comp continuous_subtype_val)
    (fun y => by
      obtain ⟨x, hx⟩ := L.g.onto y
      exact ⟨⟨x, trivial⟩, hx⟩)
    Φ.V Φ.Gv Φ.loc (Φ.Ψ⁻¹ ^ 2 * Φ.delK k)
    (fun u hu => by
      have h1 := L.K_del _ hu.1
      have h2 := L.K_Ψ _ hu.1
      simp [Frame.delK, h1, h2])
    (fun B u hu hK => by
      obtain ⟨p1, p2, -⟩ := Kum.placeDict F Ω
      by_cases hB : B = ⊤
      · left
        rw [hB, p1, Subgroup.mem_bot] at hu
        simp [hu]
      obtain ⟨w, hw⟩ := p2 B hB
      by_cases hS : w ∈ S
      · right
        obtain ⟨v, rfl⟩ := (L.loc.mem w).2 (L.only w hS)
        obtain ⟨g, hg⟩ := exists_conj (L.loc.isOver v) hw
        have h1 := hg _ hu
        rw [← L.loc.range v] at h1
        obtain ⟨s, hs⟩ := h1
        refine ⟨v, s, π g, ?_⟩
        rw [L.loc_eq, hs]
        simp [mul_assoc]
      · left
        have : u.1 ∈ π.ker := by
          rw [L.g.ker]
          refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
          simp only [Set.mem_iUnion]
          exact ⟨w, hS, B, hw, hu, hK.1⟩
        exact this)
  haveI : IsEmpty {v // ∀ s, (Φ.Ψ⁻¹ ^ 2 * Φ.delK k) (Φ.loc v s) = 1} := ⟨fun ⟨v, hv⟩ => by
    obtain ⟨g, hg⟩ := h3 v
    have h1 : Φ.del (Φ.loc v g) = 1 := (Φ.loc0 v g).2
    have h2 := hv g
    apply hg
    simpa [Frame.delK, h1] using h2⟩
  rw [Nat.card_of_isEmpty, Nat.cast_zero, add_zero, Cardinal.lift_id] at key
  exact key.trans hC
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FieldEx
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem fix_fix {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (H : Subgroup (Ω ≃ₐ[ℚ] Ω))
    (h : IsOpen (H : Set (Ω ≃ₐ[ℚ] Ω))) : (IntermediateField.fixedField H).fixingSubgroup = H :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨H, H.isClosed_of_isOpen h⟩

private theorem commutator_le_ker_of_hom_int_units {Γ : Type*} [Group Γ] (η : Γ →* ℤˣ) : commutator Γ ≤ η.ker := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

private theorem conj_ne_self_of_sq_eq_neg_natCast (z : ℂ) (D : ℕ) (hD : 0 < D) (h : z ^ 2 = -(D : ℂ)) :
    starRingEnd ℂ z ≠ z := by
  intro hc
  have him : z.im = 0 := Complex.conj_eq_iff_im.mp hc
  have h1 := congrArg Complex.re h
  simp [pow_two, him] at h1
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  nlinarith [mul_self_nonneg z.re]

theorem UpperTheory.V.Fr.field_ex :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∀ (m : ℕ) (U : Subgroup (G ℚ Ω)), UFacts l η Ψ M m U → ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : IsCMField L) (_ : Algebra L Ω), IsAbelianGalois ℚ L ∧ upl Ω L = U ∧ galOf ℚ L Ω = U ⊓ η.ker := by
  intro Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG m U hU
  obtain ⟨D, δ, hD, -, hδ2, hδ⟩ := hG.quad
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    simp at hδ2
    omega
  have hker : ∀ s : G ℚ Ω, η s = 1 ↔ s δ = δ := by
    intro s
    constructor
    · intro h
      rw [hδ s, h]
      simp
    · intro h
      rcases Int.units_eq_one_or (η s) with h1 | h1
      · exact h1
      · exfalso
        rw [hδ s, h1] at h
        simp at h
        have h2 : (2 : Ω) * δ = 0 := by linear_combination -h
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact two_ne_zero h3
        · exact hδ0 h3
  have hint : IsIntegral ℚ δ := Algebra.IsIntegral.isIntegral δ
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {δ}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hkerO : IsOpen (η.ker : Set (G ℚ Ω)) := by
    refine Subgroup.isOpen_mono ?_ (IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin ℚ {δ}))
    intro s hs
    rw [MonoidHom.mem_ker, hker]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hs δ
      (IntermediateField.mem_adjoin_simple_self ℚ δ)
  have hHo : IsOpen ((U ⊓ η.ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := by
    rw [Subgroup.coe_inf]
    exact hU.isOpen.inter hkerO
  have hcomm : commutator (G ℚ Ω) ≤ U ⊓ η.ker := le_inf hU.ab (commutator_le_ker_of_hom_int_units η)
  set L := IntermediateField.fixedField (U ⊓ η.ker) with hLdef
  have hfix : L.fixingSubgroup = U ⊓ η.ker := fix_fix _ hHo
  haveI : FiniteDimensional ℚ L := (InfiniteGalois.isOpen_iff_finite L).mp (by rw [hfix]; exact hHo)
  haveI : NumberField L := ⟨⟩
  have hN : (L.fixingSubgroup).Normal := by
    rw [hfix]
    refine ⟨fun n hn g => ?_⟩
    have hc : g * n * g⁻¹ * n⁻¹ ∈ U ⊓ η.ker :=
      hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
    have he : g * n * g⁻¹ = g * n * g⁻¹ * n⁻¹ * n := by
      group
    rw [he]
    exact Subgroup.mul_mem _ hc hn
  have hAb : @IsAbelianGalois ℚ L _ _ (IntermediateField.algebra' L) := by
    letI : Algebra ℚ L := IntermediateField.algebra' L
    haveI hg : IsGalois ℚ L := (InfiniteGalois.normal_iff_isGalois L).mp hN
    haveI : IsMulCommutative Gal(L/ℚ) := ⟨⟨fun a b => by
      obtain ⟨a', rfl⟩ := AlgEquiv.restrictNormalHom_surjective Ω a
      obtain ⟨b', rfl⟩ := AlgEquiv.restrictNormalHom_surjective Ω b
      have hc : a' * b' * a'⁻¹ * b'⁻¹ ∈ (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Ω) L).ker := by
        rw [IntermediateField.restrictNormalHom_ker, hfix]
        exact hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top a') (Subgroup.mem_top b'))
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at hc
      exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hc)⟩⟩
    exact ⟨⟩
  haveI : IsAbelianGalois ℚ L := by
    convert hAb <;> exact Subsingleton.elim _ _
  have hδL : δ ∈ L := by
    rw [IntermediateField.mem_fixedField_iff]
    intro s hs
    exact (hker s).mp (MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp hs).2)
  have hδL2 : (⟨δ, hδL⟩ : L) ^ 2 = -(D : L) := by
    apply Subtype.ext
    simpa using hδ2
  haveI : NumberField.IsTotallyComplex L := ⟨fun v => by
    rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex, NumberField.InfinitePlace.isReal_iff]
    intro hv
    apply conj_ne_self_of_sq_eq_neg_natCast (v.embedding ⟨δ, hδL⟩) D hD
    · rw [← map_pow, hδL2]
      simp
    · have := RingHom.congr_fun hv ⟨δ, hδL⟩
      rwa [NumberField.ComplexEmbedding.conjugate_coe_eq] at this⟩
  obtain ⟨j, hj⟩ := hG.cc
  have hσU : σ ∈ U := hU.real σ hG.cc
  have hησ : η σ = -1 := by
    rcases Int.units_eq_one_or (η σ) with h | h
    · exfalso
      have hσδ : σ δ = δ := (hker σ).mp h
      apply conj_ne_self_of_sq_eq_neg_natCast (j δ) D hD
      · rw [← map_pow, hδ2]
        simp
      · rw [← hj, hσδ]
    · exact h
  have hcc : ∀ z : L, σ (z : Ω) = ((NumberField.IsCMField.complexConj L z : L) : Ω) := by
    intro z
    apply j.injective
    rw [hj]
    exact (NumberField.IsCMField.complexEmbedding_complexConj L (j.comp (algebraMap L Ω)) z).symm
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · ext s
    change (∀ x ∈ NumberField.maximalRealSubfield L, s (algebraMap L Ω x) = algebraMap L Ω x) ↔ s ∈ U
    constructor
    · intro h
      rw [← fix_fix U hU.isOpen, IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      have hyL : y ∈ L := (IntermediateField.mem_fixedField_iff _ _).mpr fun f hf =>
        (IntermediateField.mem_fixedField_iff _ _).mp hy f (Subgroup.mem_inf.mp hf).1
      have hre : (⟨y, hyL⟩ : L) ∈ NumberField.maximalRealSubfield L := by
        rw [← NumberField.IsCMField.complexConj_eq_self_iff]
        apply Subtype.ext
        rw [← hcc]
        exact (IntermediateField.mem_fixedField_iff _ _).mp hy σ hσU
      exact h _ hre
    · intro hs x hx
      have hσx : σ (x : Ω) = x := by
        rw [hcc, (NumberField.IsCMField.complexConj_eq_self_iff L x).mpr hx]
      show s (x : Ω) = x
      rcases Int.units_eq_one_or (η s) with h1 | h1
      · exact (IntermediateField.mem_fixedField_iff _ _).mp x.2 s (Subgroup.mem_inf.mpr ⟨hs, h1⟩)
      · have hm : σ * s ∈ U ⊓ η.ker := by
          refine Subgroup.mem_inf.mpr ⟨U.mul_mem hσU hs, ?_⟩
          rw [MonoidHom.mem_ker, map_mul, hησ, h1]
          rfl
        have := (IntermediateField.mem_fixedField_iff _ _).mp x.2 (σ * s) hm
        rw [AlgEquiv.mul_apply] at this
        apply σ.injective
        rw [this, hσx]
  · ext s
    change (∀ x : L, s (algebraMap L Ω x) = algebraMap L Ω x) ↔ s ∈ U ⊓ η.ker
    rw [← hfix, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x hx
      exact h ⟨x, hx⟩
    · intro h x
      exact h x x.2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.OkBasic
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V
open scoped Pointwise

private theorem padic_hom_ext {l : ℕ} [Fact l.Prime] {k : Type} [CommRing k] [CharP k l] (f g : ℤ_[l] →+* k) : f = g := by
  ext x
  have h := PadicInt.sub_zmodRepr_mem x
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h
  obtain ⟨y, hy⟩ := h
  have e : x = y * l + (x.zmodRepr : ℤ_[l]) := by rw [hy]; ring
  rw [e]
  simp

private theorem cc_sq {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {c : G F Ω} {j : Ω →+* ℂ}
    (h : ∀ x, j (c x) = starRingEnd ℂ (j x)) : c * c = 1 := by
  refine AlgEquiv.ext fun x => j.injective ?_
  rw [AlgEquiv.mul_apply, h, h, starRingEnd_self_apply]
  rfl

private theorem eta_cc {Ω : Type} [Field Ω] [CharZero Ω] {η : G ℚ Ω →* ℤˣ} {D : ℕ} {δ : Ω} (hD : 0 < D)
    (hδ : δ ^ 2 = -(D : Ω)) (hη : ∀ s : G ℚ Ω, s δ = (η s : ℤ) • δ) {c : G ℚ Ω} {j : Ω →+* ℂ}
    (h : ∀ x, j (c x) = starRingEnd ℂ (j x)) : η c = -1 := by
  refine (Int.units_eq_one_or _).resolve_left fun h1 => ?_
  have h2 := h δ
  rw [hη, h1, Units.val_one, one_smul] at h2
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h2.symm
  have h3 := congrArg j hδ
  rw [map_pow, map_neg, map_natCast, hr] at h3
  have h4 : r ^ 2 = -(D : ℝ) := by exact_mod_cast h3
  have h5 : (0 : ℝ) < D := by exact_mod_cast hD
  nlinarith [sq_nonneg r]

private theorem smul_over {Ω : Type} [Field Ω] [CharZero Ω] {l : ℕ} {B : ValuationSubring Ω} (γ : G ℚ Ω)
    (h : B.valuation (l : Ω) < 1) : (γ • B).valuation (l : Ω) < 1 := by
  rw [valuation_lt_one_iff'] at h ⊢
  simpa only [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, map_natCast, map_inv₀] using h

private theorem cpt_gal (F Ω : Type) [Field F] [CharZero F] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra F Ω] :
    CompactSpace (G F Ω) := by
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI : IsGalois F Ω := IsGalois.tower_top_of_isGalois ℚ F Ω
  infer_instance

theorem UpperTheory.V.Fr.ok_basic :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∀ (m : ℕ) (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] (g₁ : G ℚ Ω) (Φ : Frame l (ResidueField O)), UFacts l η Ψ M m (upl Ω L) → Linked l η Ψ σ g₁ B M L Φ → barChar O Ψ g₁ ^ 2 ≠ 1 → IsOpen (Φ.del.ker : Set Φ.Γ) ∧ Φ.c * Φ.c = 1 ∧ Φ.del Φ.c = -1 ∧ (∀ v, Continuous (Φ.loc0 v)) ∧ Continuous Φ.eps ∧ IsOpen (Φ.Ψ.ker : Set Φ.Γ) ∧ Φ.Ψ Φ.c = 1 ∧ Φ.Ψ Φ.g0 ^ 2 ≠ 1 ∧ Fintype.card Φ.Inf = Φ.d ∧ (∀ w, Φ.cw w * Φ.cw w = 1) ∧ (∀ w, Φ.del (Φ.cw w) = -1) ∧ (∃ g : Φ.G0, Φ.om (ResidueField O) g ≠ 1) ∧ (∀ j : ℤ, j = 1 ∨ j = -1 → ∃ g : Φ.G0, Φ.om (ResidueField O) g * Φ.Ψ g ^ j ≠ 1) ∧ (∀ j : ℤ, j = 2 ∨ j = -2 → ∃ g, Φ.om (ResidueField O) g * Φ.Ψ g ^ j * Φ.delK (ResidueField O) g ≠ 1) ∧ (∀ v, ∃ g, Φ.Ψ (Φ.loc v g) ^ 2 ≠ 1) ∧ (¬ ∃ j : ℤ, ∀ g : Φ.G0, Φ.om (ResidueField O) g = Φ.Ψ g ^ j) ∧ (∀ v, ∀ g ∈ Φ.Nv v, Φ.Ψ (Φ.loc v g) = 1) ∧ (∀ v, l ^ m ≤ Φ.dv v) ∧ Nonempty Φ.V := by
  intro Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG m L _ _ _ _ g₁ Φ hU hL hg₁
  obtain ⟨k, S, π, ι, pl, e, c, F, hπ, -⟩ := hL
  haveI : CompactSpace (G (W.Lp L) Ω) := cpt_gal _ _
  have hq : Topology.IsQuotientMap π := F.g.cont.isClosedMap.isQuotientMap F.g.cont F.g.onto
  have hom : ∀ s, Φ.om (ResidueField O) (k.p s) = omO Ω l O s := fun s => by
    apply Units.ext
    show (ZMod.castHom (dvd_refl l) (ResidueField O)).comp PadicInt.toZMod (Φ.eps (k.p s) : ℤ_[l]ˣ) =
      (ZMod.castHom (dvd_pow_self l one_ne_zero) (ResidueField O)).comp (PadicInt.toZModPow 1) (cycZ ℚ Ω l s : ℤ_[l]ˣ)
    rw [k.eps, padic_hom_ext ((ZMod.castHom (dvd_refl l) (ResidueField O)).comp PadicInt.toZMod)]
  have hpl : ∀ v, (k.pl v).valuation (l : Ω) < 1 := fun v => by
    obtain ⟨γ, -, h⟩ := k.pl_conj v
    exact h ▸ smul_over γ hG.over_l
  have h0 : ∀ s (h : s ∈ upl Ω L ⊓ η.ker), k.p ⟨s, h.1⟩ ∈ Φ.del.ker := fun s h => (k.del _).trans h.2
  have f5 : ¬ ∃ j : ℤ, ∀ g : Φ.G0, Φ.om (ResidueField O) g = Φ.Ψ g ^ j := by
    rintro ⟨j, hj⟩
    refine hU.f5 ⟨j, fun s hs => ?_⟩
    have := hj ⟨_, h0 s hs⟩
    rwa [hom, k.psi] at this
  obtain ⟨hσ, hc⟩ := k.c
  obtain ⟨hg, hg0⟩ := k.g0
  obtain ⟨D, δ, hD, -, hδ, hη⟩ := hG.quad
  refine ⟨F.del_open, ?_, F.del_c, fun v => ?_, ?_, ?_, ?_, ?_, ?_, fun w => ?_, fun w => ?_, ?_, fun j hj => ?_,
    fun j hj => ?_, fun v => ?_, f5, fun v g hg => ?_, fun v => ?_, ?_⟩
  · obtain ⟨j, hj⟩ := hG.cc
    rw [← hc, ← map_mul, ← map_one k.p]
    exact congrArg k.p (Subtype.ext (cc_sq hj))
  · refine continuous_induced_rng.2 ?_
    have : Subtype.val ∘ Φ.loc0 v = k.p ∘ k.j v := funext (k.j_loc v)
    exact this ▸ k.p_cont.comp (k.j_cont v)
  · refine hq.continuous_iff.2 ?_
    have : Φ.eps ∘ π = cycZ (W.Lp L) Ω l := funext F.eps
    exact this ▸ continuous_cycZ _ _ l
  · exact hq.isOpen_preimage.1 (Subgroup.isOpen_mono (H₂ := Φ.Ψ.ker.comap π) F.K_Ψ F.g.isOpen)
  · rw [← hc, k.psi]
    exact hG.even
  · rw [← hg0, k.psi]
    exact hg₁
  · classical
    haveI := F.real
    rw [Fintype.card_congr e, Frame.d, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyReal.nrComplexPlaces_eq_zero, add_zero, ← IsTotallyReal.finrank,
      ← sum_locDegree l (Finset.univ.image pl) fun v => by
        rw [← F.loc.mem, Finset.mem_image]; exact ⟨fun ⟨a, _, h⟩ => ⟨a, h⟩, fun ⟨a, h⟩ => ⟨a, Finset.mem_univ _, h⟩⟩,
      Finset.sum_image fun a _ b _ h => F.loc.inj h]
    exact Finset.sum_congr rfl fun v _ => (F.dv v).symm
  · obtain ⟨j, hj, -⟩ := F.cc w
    rw [F.cw, ← map_mul, cc_sq hj, map_one]
  · obtain ⟨j, hj, -⟩ := F.cc w
    rw [F.cw, hπ _ fun x hx => (c w).commutes ⟨x, hx⟩, k.del]
    exact eta_cc hD hδ hη hj
  · by_contra h
    exact f5 ⟨0, fun g => by_contra fun h' => h ⟨g, by simpa using h'⟩⟩
  · obtain ⟨s, hs, h⟩ := hU.f2b j hj
    exact ⟨⟨_, h0 s hs⟩, by rwa [hom, k.psi]⟩
  · obtain ⟨s, hs, h⟩ := hU.f2c j hj
    refine ⟨k.p ⟨s, hs.1⟩, ?_⟩
    rwa [hom, k.psi, Frame.delK, MonoidHom.comp_apply, MonoidHom.mem_ker.1 (h0 s hs), map_one, mul_one]
  · obtain ⟨s, hs, h⟩ := hU.f3 _ (hpl v)
    obtain ⟨g, hg⟩ := (k.j_range v ⟨s, hs.2⟩).2 hs.1
    exact ⟨g, by rwa [k.j_loc, k.psi, hg]⟩
  · obtain ⟨j, hj⟩ := hG.Ψ_l
    have h1 : Φ.eps (Φ.loc v g) = 1 := hg.2
    have h2 : Φ.om (ResidueField O) (Φ.loc v g) = 1 := by rw [Frame.om, MonoidHom.comp_apply, h1, map_one]
    rw [k.j_loc, hom] at h2
    rw [k.j_loc, k.psi, hj _ (hpl v) _ ((k.j_ine v g).1 hg.1), h2, one_pow]
  · exact k.dv v ▸ hU.deg _ (hpl v)
  · exact ⟨(k.pl_all B hG.over_l).exists.choose⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusGaloisFieldFourCompatibility
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V
open scoped Pointwise

namespace UpperTheory.V.Fr.DescentValuationAlt

private theorem smul_val_lt {Ω : Type} [Field Ω] [Algebra ℚ Ω] (g : G ℚ Ω) (A : ValuationSubring Ω) (n : ℕ)
    (hA : A.valuation (n : Ω) < 1) : (g • A).valuation (n : Ω) < 1 := by
  have fix : ∀ y : Ω, g y = y → (y ∈ g • A ↔ y ∈ A) := by
    intro y hy
    have hy' : g • y = y := hy
    constructor
    · intro h
      obtain ⟨s, hs, hgs⟩ := (ValuationSubring.mem_smul_pointwise_iff_exists g y A).mp h
      have : s = y := by
        rw [← inv_smul_smul g s, hgs, inv_smul_eq_iff, hy']
      rwa [this] at hs
    · intro h
      have := ValuationSubring.smul_mem_pointwise_smul g y A h
      rwa [hy'] at this
  have vlt : ∀ (C : ValuationSubring Ω) (x : Ω), x ≠ 0 → (C.valuation x < 1 ↔ x ∈ C ∧ x⁻¹ ∉ C) := by
    intro C x hx
    haveI : Nontrivial C.ValueGroup := GroupWithZero.toNontrivial
    rw [← ValuationSubring.valuation_le_one_iff, ← ValuationSubring.valuation_le_one_iff, map_inv₀,
      inv_le_one₀ ((Valuation.pos_iff _).mpr hx), lt_iff_le_not_ge]
  by_cases h0 : (n : Ω) = 0
  · rw [h0, map_zero]
    haveI : Nontrivial (g • A).ValueGroup := GroupWithZero.toNontrivial
    exact zero_lt_one
  · have hn : g (n : Ω) = n := map_natCast g n
    have hni : g ((n : Ω)⁻¹) = (n : Ω)⁻¹ := by rw [map_inv₀, hn]
    rw [vlt _ _ h0] at hA ⊢
    rw [fix _ hn, fix _ hni]
    exact hA

private theorem descend {U Γ k : Type} [Group U] [TopologicalSpace U] [IsTopologicalGroup U] [CompactSpace U]
    [Group Γ] [TopologicalSpace Γ] [T2Space Γ] [CommRing k] (p : U →* Γ) (hc : Continuous p)
    (hs : Function.Surjective p) (S : Set U) (hk : p.ker = (Subgroup.normalClosure S).topologicalClosure)
    (χ : Γ →* kˣ) (y : U → k) (hl : IsLocallyConstant y) (hy : ∀ s t, y (s * t) = y s + χ (p s) * y t)
    (hS : ∀ s ∈ S, y s = 0) :
    ∃ φ : Γ → k, IsLocallyConstant φ ∧ ∀ s, φ (p s) = y s := by
  have hy1 : y 1 = 0 := by
    have e := hy 1 1
    rw [mul_one, map_one, map_one, Units.val_one, one_mul] at e
    linear_combination -e
  let H : Subgroup U :=
    { carrier := {t | p t = 1 ∧ y t = 0}
      one_mem' := ⟨map_one p, hy1⟩
      mul_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        show p (a * b) = 1 ∧ y (a * b) = 0
        refine ⟨by rw [map_mul, ha1, hb1, one_mul], ?_⟩
        rw [hy, ha2, hb2, mul_zero, add_zero]
      inv_mem' := by
        rintro a ⟨ha1, ha2⟩
        show p a⁻¹ = 1 ∧ y a⁻¹ = 0
        refine ⟨by rw [map_inv, ha1, inv_one], ?_⟩
        have e := hy a a⁻¹
        rw [mul_inv_cancel, hy1, ha2, ha1, map_one, Units.val_one, one_mul, zero_add] at e
        exact e.symm }
  have hH : H.Normal := ⟨fun t ht g => by
    obtain ⟨ht1, ht2⟩ := ht
    show p (g * t * g⁻¹) = 1 ∧ y (g * t * g⁻¹) = 0
    refine ⟨by rw [map_mul, map_mul, map_inv, ht1, mul_one, mul_inv_cancel], ?_⟩
    have e1 := hy (g * t) g⁻¹
    have e2 := hy g t
    have e3 := hy g g⁻¹
    rw [mul_inv_cancel, hy1] at e3
    rw [map_mul, ht1, mul_one] at e1
    rw [ht2, mul_zero, add_zero] at e2
    rw [e1, e2, ← e3]⟩
  have hcl : IsClosed (H : Set U) :=
    (isClosed_eq hc continuous_const).inter (hl.isClosed_fiber 0)
  have hKH : p.ker ≤ H := by
    rw [hk]
    apply Subgroup.topologicalClosure_minimal _ _ hcl
    haveI := hH
    apply Subgroup.normalClosure_le_normal
    intro s hsS
    have hps : p s = 1 := by
      rw [← MonoidHom.mem_ker, hk]
      exact Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hsS)
    exact ⟨hps, hS s hsS⟩
  have hfib : ∀ s t, p s = p t → y s = y t := by
    intro s t hst
    have hk' : s⁻¹ * t ∈ p.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hst, inv_mul_cancel]
    obtain ⟨_, h2⟩ := hKH hk'
    have e := hy s (s⁻¹ * t)
    rw [mul_inv_cancel_left, h2, mul_zero, add_zero] at e
    exact e.symm
  have hq : Topology.IsQuotientMap p := (hc.isClosedMap).isQuotientMap hc hs
  refine ⟨fun γ => y (Function.surjInv hs γ), fun V => ?_, fun s => hfib _ _ (Function.surjInv_eq hs (p s))⟩
  have e : p ⁻¹' ((fun γ => y (Function.surjInv hs γ)) ⁻¹' V) = y ⁻¹' V := by
    ext s
    simp only [Set.mem_preimage]
    rw [hfib _ _ (Function.surjInv_eq hs (p s))]
  apply hq.isOpen_preimage.mp
  rw [e]
  exact hl V

end UpperTheory.V.Fr.DescentValuationAlt

open UpperTheory.V.Fr.DescentValuationAlt in
theorem UpperTheory.V.Fr.frobenius_galoisField_four_compatibility :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∀ (m : ℕ) (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] (g₁ : G ℚ Ω) (Φ : Frame l (ResidueField O)), UFacts l η Ψ M m (upl Ω L) → Linked l η Ψ σ g₁ B M L Φ → ∀ a : ℕ, a = 1 ∨ a = 2 → StrictCl l η Ψ ((barChar O Ψ)⁻¹ ^ a * etaO O η) (upl Ω L) → Nontrivial (H1C Φ.loc (chRep (Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O))) fun _ => ⊥) := by
  intro Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG m L _ _ _ _ g₁ Φ hU hL a ha hS
  obtain ⟨k, -⟩ := hL
  obtain ⟨y, hyl, hyc, hyn, hyd, hyi⟩ := hS
  have hχ : ∀ s : upl Ω L, (Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O)) (k.p s)
      = ((barChar O Ψ)⁻¹ ^ a * etaO O η) s := by
    intro s
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.pow_apply,
      MonoidHom.inv_apply, MonoidHom.inv_apply, k.psi]
    congr 1
    simp only [Frame.delK, etaO, MonoidHom.comp_apply, k.del]
  have hUc : IsClosed (upl Ω L : Set (G ℚ Ω)) := Subgroup.isClosed_of_isOpen _ hU.isOpen
  haveI : CompactSpace (upl Ω L) := isCompact_iff_compactSpace.mp hUc.isCompact
  obtain ⟨φ, hφl, hφ⟩ := descend k.p k.p_cont k.p_surj _ k.p_ker (Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O))
    (fun s => y s) (hyl.comp_continuous continuous_subtype_val)
    (fun s t => by rw [hχ s]; exact hyc s t)
    (fun s hs => by
      obtain ⟨B', hB', hI, hη, hb⟩ := hs
      exact hyi B' hB' s (Subgroup.mem_inf.mpr ⟨hI, s.2⟩) hη hb)
  have hρ : ∀ (γ : Φ.Γ) (w : ResidueField O),
      (chRep (Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O)) γ) w
        = ((Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O)) γ : ResidueField O) * w := fun γ w => rfl
  have hcoc : ∀ γ δ : Φ.Γ, φ (γ * δ)
      = φ γ + ((Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O)) γ : ResidueField O) * φ δ := by
    intro γ δ
    obtain ⟨s, rfl⟩ := k.p_surj γ
    obtain ⟨t, rfl⟩ := k.p_surj δ
    rw [← map_mul, hφ, hφ, hφ, hχ]
    exact hyc s t
  have hloc : ∀ v : Φ.V, ∃ b : ResidueField O, ∀ g : Φ.Gv v,
      φ (Φ.loc v g) = ((Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O)) (Φ.loc v g) : ResidueField O) * b - b := by
    intro v
    obtain ⟨γ, -, hγ⟩ := k.pl_conj v
    have hv : (k.pl v).valuation (l : Ω) < 1 := by
      rw [hγ]
      exact smul_val_lt γ B l hG.over_l
    obtain ⟨b, hb⟩ := hyd _ hv
    refine ⟨b, fun g => ?_⟩
    rw [k.j_loc, hφ, hχ]
    exact hb _ ((k.j_range v _).mp (MonoidHom.mem_range.mpr ⟨g, rfl⟩))
  choose b hb using hloc
  let z : Z1C Φ.loc (chRep (Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O))) (fun _ => ⊥) :=
    ⟨(φ, b), ⟨hφl, fun γ δ => by rw [hρ]; exact hcoc γ δ,
      fun v g => by rw [Submodule.mem_bot, hρ, ← hb v g, sub_self]⟩⟩
  refine ⟨⟨Submodule.Quotient.mk z, 0, fun h => ?_⟩⟩
  have hz := (Submodule.Quotient.mk_eq_zero _).mp h
  rw [Submodule.mem_comap] at hz
  obtain ⟨X, hX1, -⟩ := hz
  apply hyn
  refine ⟨X, fun s hs => ?_⟩
  have e1 := hφ ⟨s, hs⟩
  have e2 := hX1 (k.p ⟨s, hs⟩)
  rw [hρ, hχ] at e2
  rw [← e2]
  exact e1.symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ClrkTr
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.clrk_tr :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (U : Subgroup (G ℚ Ω)), U ≤ galOf ℚ F Ω → GC.clRk l (U.comap (galEmb ℚ F Ω)) = GC.clRk l U := by
  intro Ω _ _ _ l _ F _ _ _ U hU
  haveI : Module.IsTorsionFree F Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) F⟩
  have hemb := (galEmbTop ℚ F Ω).1
  have hfam := (galEmbFam ℚ F Ω l).1
  let e : U.comap (galEmb ℚ F Ω) ≃ U :=
    { toFun := fun u => ⟨galEmb ℚ F Ω u.1, u.2⟩
      invFun := fun u => ⟨Kum.toGal F hU u, u.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc : Continuous e := (hemb.continuous.comp continuous_subtype_val).subtype_mk _
  have hc' : Continuous e.symm := (hemb.continuous_iff.2 continuous_subtype_val).subtype_mk _
  have hI : ∀ (A : ValuationSubring Ω) (σ : G F Ω), galEmb ℚ F Ω σ ∈ Ine (F := ℚ) A ↔ σ ∈ Ine (F := F) A :=
    fun A σ => SetLike.ext_iff.1 (hfam A).2 σ
  have hD : ∀ (A : ValuationSubring Ω) (σ : G F Ω), galEmb ℚ F Ω σ ∈ Dec (F := ℚ) A ↔ σ ∈ Dec (F := F) A :=
    fun A σ => SetLike.ext_iff.1 (hfam A).1 σ
  have key : (Kum.XDual 1 U (ZMod l) (ZMod l)).map (LinearEquiv.funCongrLeft (ZMod l) (ZMod l) e).toLinearMap =
      Kum.XDual 1 (U.comap (galEmb ℚ F Ω)) (ZMod l) (ZMod l) := by
    ext φ
    constructor
    · rintro ⟨ψ, ⟨h1, h2, h3, h4⟩, rfl⟩
      exact ⟨h1.comp_continuous hc, fun a b => h2 (e a) (e b), fun A u h => h3 A (e u) ((hI A _).2 h),
        fun A hA u h => h4 A hA (e u) ((hD A _).2 h)⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨φ ∘ e.symm, ⟨h1.comp_continuous hc', fun a b => h2 (e.symm a) (e.symm b),
        fun A u h => h3 A (e.symm u) ((hI A _).1 h), fun A hA u h => h4 A hA (e.symm u) ((hD A _).1 h)⟩, rfl⟩
  unfold GC.clRk
  rw [← key]
  exact ((LinearEquiv.funCongrLeft (ZMod l) (ZMod l) e).submoduleMap _).rank_eq.symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EtaleSimplicialCochainSchemeSectionExtensionNatu
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem galois_sqrt_sign {Ω : Type} [Field Ω] [CharZero Ω] (s : G ℚ Ω) {x : Ω} {n : ℤ} (hx : x ^ 2 = n) :
    s x = x ∨ s x = -x := by
  apply sq_eq_sq_iff_eq_or_eq_neg.1
  rw [← map_pow, hx, map_intCast]

private theorem decomposition_fixes_sqrt {Ω : Type} [Field Ω] [CharZero Ω] (B : ValuationSubring Ω) {x : Ω} {k : ℤ}
    (hx : x ^ 2 = ((1 + 4 * k : ℤ) : Ω)) (hk : B.valuation (k : Ω) < 1) {s : G ℚ Ω} (hs : s ∈ Dec (F := ℚ) B) : s x = x := by
  refine (galois_sqrt_sign s hx).resolve_right fun h => ?_
  set y : Ω := (1 + x) / 2 with hy
  have h1 : s y = 1 - y := by rw [hy, map_div₀, map_add (f := _), map_one, h, map_ofNat]; ring
  have h2 : y * (1 - y) = -k := by
    push_cast at hx
    rw [hy]; linear_combination (-1 / 4 : Ω) * hx
  have h3 : B.valuation (1 - y) < 1 ↔ B.valuation y < 1 := by rw [← h1]; exact valuation_apply_lt_one_iff hs y
  have h4 : B.valuation y < 1 := by
    by_contra h5
    have h6 : 1 ≤ B.valuation (y * (1 - y)) := by
      rw [map_mul]; exact one_le_mul (not_lt.1 h5) (not_lt.1 (h3.not.2 h5))
    rw [h2, Valuation.map_neg] at h6
    exact absurd hk (not_lt.2 h6)
  have h7 := B.valuation.map_add_lt h4 (h3.2 h4)
  have hy' : y + (1 - y) = 1 := by ring
  rw [hy', map_one] at h7
  exact lt_irrefl _ h7

private theorem etaleSimplicialCochain_scheme_section_extension_naturality {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {p n : ℕ} (hp : B.valuation (p : Ω) < 1)
    (h : p.Coprime n) : ¬ B.valuation (n : Ω) < 1 := by
  intro hn
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have e : (a : Ω) * p + b * n = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  have hm : ∀ (c : ℤ) (z : Ω), B.valuation z < 1 → B.valuation (c * z) < 1 := fun c z hz => by
    rw [map_mul]
    exact (mul_le_of_le_one_left' ((B.valuation_le_one_iff _).2 (intCast_mem B c))).trans_lt hz
  have := B.valuation.map_add_lt (hm a _ hp) (hm b _ hn)
  rw [e, map_one] at this
  exact lt_irrefl _ this

private theorem inertia_fixes_sqrt_discriminant {Ω : Type} [Field Ω] [CharZero Ω] (B : ValuationSubring Ω) {δ : Ω} {D : ℕ}
    (hδ : δ ^ 2 = -(D : Ω)) (hD : ¬ B.valuation ((4 * D : ℕ) : Ω) < 1) {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) B) : s δ = δ := by
  refine (galois_sqrt_sign s (n := -D) (by rw [hδ]; simp)).resolve_right fun h => hD ?_
  have h1 : B.valuation δ ≤ 1 := by
    have : B.valuation δ ^ 2 ≤ 1 := by
      rw [← map_pow, hδ, Valuation.map_neg]; exact (B.valuation_le_one_iff _).2 (natCast_mem B D)
    exact (pow_le_one_iff_of_nonneg zero_le' two_ne_zero).1 this
  have h2 := hs.2 δ h1
  have e : ((4 * D : ℕ) : Ω) = -((s δ - δ) ^ 2) := by rw [h]; push_cast; linear_combination (4 : Ω) * hδ
  rw [e, Valuation.map_neg, map_pow]
  exact pow_lt_one₀ zero_le' h2 two_ne_zero

private theorem gauss_sqrt_inertia_negates {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [hp : Fact p.Prime] (h4 : p % 4 = 3)
    (B : ValuationSubring Ω) (hB : B.valuation (p : Ω) < 1) :
    ∃ x : Ω, x ^ 2 = -(p : Ω) ∧ ∃ s ∈ Ine (F := ℚ) B, s x = -x := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero (p : Ω) := ⟨Nat.cast_ne_zero.2 hp.out.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω p
  have h2 : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  let ψ := AddChar.zmodChar p hζ.pow_eq_one
  have hψ : ψ.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root p hζ
  let χ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom Ω)
  have hχ : χ ≠ 1 := (MulChar.ringHomComp_ne_one_iff (RingHom.injective_int _)).2 (quadraticChar_ne_one h2)
  have hq : χ.IsQuadratic := (quadraticChar_isQuadratic _).comp _
  have hm : χ (-1) = -1 := by
    show ((quadraticChar (ZMod p) (-1) : ℤ) : Ω) = -1
    rw [quadraticChar_neg_one h2, ZMod.card, ZMod.χ₄_nat_three_mod_four h4]; simp
  have hmem : (-1 : (ZMod p)ˣ) ∈ (Ine (F := ℚ) B).map (B1.cycN ℚ Ω p) := by
    rw [B1.cycIne Ω p p B hB, B3.pPart, MonoidHom.mem_ker]
    have : ordCompl[p] p = 1 := by rw [hp.out.factorization_self, pow_one, Nat.div_self hp.out.pos]
    have : Subsingleton (ZMod (ordCompl[p] p)) := by rw [this]; infer_instance
    exact Subsingleton.elim _ _
  obtain ⟨s, hs, hs'⟩ := hmem
  refine ⟨gaussSum χ ψ, by rw [gaussSum_sq hχ hq hψ, hm, ZMod.card]; simp, s, hs, ?_⟩
  have h3 := gaussSum_mulShift χ ψ (-1)
  rw [Units.val_neg, Units.val_one, hm, neg_one_mul, neg_eq_iff_eq_neg] at h3
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h3, gaussSum, gaussSum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul]
  congr 1
  · exact map_intCast s _
  · have h5 : ψ a ^ p = 1 := by rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one]
    rw [B1.cycN_spec ℚ Ω p s h5, hs', ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_zmod_val, AddChar.mulShift_apply]
    simp

private theorem complex_conjugation_fixes_sqrt {Ω : Type} [Field Ω] [CharZero Ω] {τ : G ℚ Ω} (h : IsCC τ) {z : Ω} {n : ℕ} (hn : 0 < n)
    (hz : z ^ 2 = n) : τ z = z := by
  refine (galois_sqrt_sign τ (n := n) (by rw [hz]; simp)).resolve_right fun h1 => ?_
  obtain ⟨j, hj⟩ := h
  have h2 : starRingEnd ℂ (j z) = -j z := by rw [← map_neg, ← h1]; exact (hj z).symm
  have h3 := Complex.mul_conj (j z)
  rw [h2, mul_neg, ← sq, ← map_pow, hz, map_natCast] at h3
  have h4 : -(n : ℝ) = Complex.normSq (j z) := by exact_mod_cast h3
  have h5 := Complex.normSq_nonneg (j z)
  have h6 : (0 : ℝ) < n := by exact_mod_cast hn
  linarith

theorem UpperTheory.V.Fr.exists_twistCharacter_continuousCohomology :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∃ H₀, FrobeniusSplitPrimeDatum η M H₀ := by
  intro Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG
  obtain ⟨D, δ, hD, -, hδ, hη⟩ := hG.quad
  have hM := hG.M_ne
  obtain ⟨p, hlt, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_zmodEq (4 * D + M) (q := 4 * M) (a := -1) (by omega)
    isCoprime_one_left.neg_left
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht⟩ := hmod.dvd
  have ht' : -(p : ℤ) = 1 + 4 * (M * t) := by push_cast at ht; linear_combination ht
  obtain ⟨A, hA⟩ := (B3.placesQ Ω).1 p hp
  obtain ⟨x, hx, s, hs, hsx⟩ := gauss_sqrt_inertia_negates p (by omega) A hA
  have hsδ : s δ = δ := inertia_fixes_sqrt_discriminant A hδ (etaleSimplicialCochain_scheme_section_extension_naturality A hA (Nat.coprime_of_lt_prime (by omega) (by omega) hp)) hs
  have hz : (δ * x) ^ 2 = ((D * p : ℕ) : Ω) := by rw [mul_pow, hδ, hx]; push_cast; ring
  have hpos : 0 < D * p := Nat.mul_pos hD hp.pos
  have hz0 : δ * x ≠ 0 := fun h => by
    rw [h, zero_pow two_ne_zero] at hz
    exact hpos.ne (by exact_mod_cast hz)
  have hne : -(δ * x) ≠ δ * x := fun h => hz0 (by linear_combination (-1 / 2 : Ω) * h)
  have hsz : s (δ * x) = -(δ * x) := by rw [map_mul, hsδ, hsx, mul_neg]
  have hmem : ∀ g : G ℚ Ω, g ∈ MulAction.stabilizer (G ℚ Ω) (δ * x) ↔ g (δ * x) = δ * x := fun g => Iff.rfl
  have : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  refine ⟨MulAction.stabilizer (G ℚ Ω) (δ * x), stabilizer_isOpen_of_isIntegral _, ?_, fun τ hτ => complex_conjugation_fixes_sqrt hτ hpos hz,
    fun B' hB' => ?_, A, etaleSimplicialCochain_scheme_section_extension_naturality A hA (Nat.coprime_of_lt_prime hM (by omega) hp), fun h => hne (hsz.symm.trans (h hs))⟩
  · refine Subgroup.index_eq_two_iff.2 ⟨s, fun b => ?_⟩
    rw [hmem, hmem, AlgEquiv.mul_apply, hsz, map_neg]
    rcases galois_sqrt_sign b (n := (D * p : ℕ)) (hz.trans (Int.cast_natCast _).symm) with h | h
    · rw [h]; exact Or.inr ⟨rfl, hne⟩
    · rw [h, neg_neg]; exact Or.inl ⟨rfl, hne⟩
  · have hk : B'.valuation ((M * t : ℤ) : Ω) < 1 := by
      rw [Int.cast_mul, Int.cast_natCast, map_mul]
      exact mul_lt_one_of_lt_of_le hB' ((B'.valuation_le_one_iff _).2 (intCast_mem B' t))
    ext g
    refine and_congr_right fun hg => ?_
    have hgx : g x = x := decomposition_fixes_sqrt B' (by rw [← ht', hx]; simp) hk hg
    show g (δ * x) = δ * x ↔ η g = 1
    rw [map_mul, hgx, hη]
    rcases Int.units_eq_one_or (η g) with h | h
    · simp [h]
    · rw [h]
      refine iff_of_false (fun h' => hne ?_) (by decide)
      simpa using h'
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AuxwEx
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem ax_cycMod_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hl : Fact l.Prime]
    {s : G ℚ Ω} (hs : ∀ ζ : Ω, ζ ^ l = 1 → s ζ = ζ) : cycMod ℚ Ω l 1 s = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  apply Units.ext
  show PadicInt.toZModPow 1 ((cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s)).val) = 1
  rw [cyclotomicCharacter.toZModPow]
  symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  have ht' : (t : Ω) ^ l = 1 := by
    have := congrArg Units.val ((mem_rootsOfUnity _ _).1 ht)
    simpa using this
  have hl1 : l ^ 1 ≠ 1 := by
    have := hl.out.one_lt
    rw [pow_one]
    omega
  rw [ZMod.val_one'' hl1, pow_one]
  exact hs _ ht'

theorem UpperTheory.V.Fr.auxw_ex :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∀ Q : ℕ, Q ≠ 0 → ∃ w, FrobeniusWitnessPrime l η Ψ M w ∧ w ≡ 1 [MOD Q] := by
  intro Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG Q hQ
  obtain ⟨a, hη, hbar⟩ := hG.cyc
  have hM := hG.M_ne
  have hlM := hG.l_dvd
  have hL : M ^ (a + 1) * Q ≠ 0 := mul_ne_zero (pow_ne_zero _ hM) hQ
  obtain ⟨w, hw, hwgt, hw1⟩ := Nat.exists_prime_gt_modEq_one (M ^ (a + 1) * Q) hL
  have hMaL : M ^ a ∣ M ^ (a + 1) * Q := Dvd.dvd.mul_right (pow_dvd_pow M (Nat.le_succ a)) Q
  have hlL : l ∣ M ^ (a + 1) * Q :=
    dvd_trans hlM (dvd_trans (dvd_pow_self M (Nat.succ_ne_zero a)) (dvd_mul_right _ _))
  have hML : M ∣ M ^ (a + 1) * Q := dvd_trans (dvd_pow_self M (Nat.succ_ne_zero a)) (dvd_mul_right _ _)
  have hndvd : ∀ m, m ∣ M ^ (a + 1) * Q → ¬ w ∣ m := by
    intro m hm hwm
    have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hL) hm
    have h2 := Nat.le_of_dvd (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hL hm)) hwm
    omega
  refine ⟨w, ⟨hw, hndvd M hML, Nat.ModEq.of_dvd hlL hw1, ?_⟩, Nat.ModEq.of_dvd (dvd_mul_left Q _) hw1⟩
  intro B' hB' s hs
  haveI := Fact.mk hw
  have fix : ∀ m, m ∣ M ^ (a + 1) * Q → ∀ ζ : Ω, ζ ^ m = 1 → s ζ = ζ := by
    intro m hm
    have hcop : m.Coprime w := ((Nat.Prime.coprime_iff_not_dvd hw).2 (hndvd m hm)).symm
    obtain ⟨k, hk⟩ := UpperTheory.V.LDataCardLeFinrank.decActRoots ℚ Ω w B' hB' m hcop s hs
    intro ζ hζ
    rw [hk ζ hζ]
    have hwk : w ^ k ≡ 1 [MOD m] := by
      have := (Nat.ModEq.of_dvd hm hw1).pow k
      rwa [one_pow] at this
    rw [pow_eq_pow_mod _ hζ, show w ^ k % m = 1 % m from hwk, ← pow_eq_pow_mod 1 hζ, pow_one]
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  · exact hη s (fix _ hMaL)
  · exact hbar s (fix _ hMaL)
  · rw [MonoidHom.mem_ker]
    change (Units.map _) ((cycMod ℚ Ω l 1) s) = 1
    rw [ax_cycMod_one l (fix l hlL), map_one]
end

attribute [local instance 10000] DivisionSemiring.to_moduleIsTorsionFree

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem cycMod_emb (F Ω : Type) [Field F] [NumberField F] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra F Ω]
    (l : ℕ) [Fact l.Prime] (g : G F Ω) : cycMod ℚ Ω l 1 (galEmb ℚ F Ω g) = cycMod F Ω l 1 g := rfl

private theorem one_of_cast (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] (x : ℤ_[l])
    (h : ZMod.castHom (dvd_refl l) k (PadicInt.toZMod x) = 1) : PadicInt.toZModPow 1 x = 1 := by
  have h1 : x - 1 ∈ RingHom.ker (PadicInt.toZMod : ℤ_[l] →+* ZMod l) := by
    rw [RingHom.mem_ker, RingHom.map_sub, map_one, sub_eq_zero]
    exact (ZMod.castHom (dvd_refl l) k).injective (h.trans (map_one _).symm)
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, ← pow_one (l : ℤ_[l]), ← PadicInt.ker_toZModPow,
    RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at h1
  exact h1

private theorem rk_link {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (L : Type) [Field L]
    [NumberField L] [IsCMField L] [Algebra L Ω] (A A' : Subgroup (G ℚ Ω)) :
    GC.clRk l ((A ⊓ A').comap (galEmb ℚ (W.Lp L) Ω) ⊓ (cycMod (W.Lp L) Ω l 1).ker) =
      GC.clRk l (upl Ω L ⊓ A ⊓ A' ⊓ (cycMod ℚ Ω l 1).ker) := by
  have hU : upl Ω L ⊓ A ⊓ A' ⊓ (cycMod ℚ Ω l 1).ker ≤ galOf ℚ (W.Lp L) Ω :=
    fun g hg x => hg.1.1.1 x.1 x.2
  rw [← clrk_tr Ω l (W.Lp L) _ hU]
  congr 1
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_comap, MonoidHom.mem_ker]
  rw [cycMod_emb]
  constructor
  · rintro ⟨⟨ha, ha'⟩, hc⟩
    exact ⟨⟨⟨fun x hx => galEmb_mem ℚ (W.Lp L) Ω g ⟨x, hx⟩, ha⟩, ha'⟩, hc⟩
  · rintro ⟨⟨⟨_, ha⟩, ha'⟩, hc⟩
    exact ⟨⟨ha, ha'⟩, hc⟩

private theorem ok_link (P : GC.Hypotheses₂) {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type}
    [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ : G ℚ Ω}
    {B : ValuationSubring Ω} {M : ℕ} {Hb : Subgroup (G ℚ Ω)} (hG : Gen l η Ψ σ B M Hb) (m C₀ : ℕ) (L : Type) [Field L]
    [NumberField L] [IsCMField L] [Algebra L Ω] (g₁ : G ℚ Ω) (Φ : Frame l (ResidueField O))
    (hU : UFacts l η Ψ M m (upl Ω L)) (hL : Linked l η Ψ σ g₁ B M L Φ) (hg : barChar O Ψ g₁ ^ 2 ≠ 1)
    (hS : ∀ a : ℕ, a = 1 ∨ a = 2 → StrictCl l η Ψ ((barChar O Ψ)⁻¹ ^ a * etaO O η) (upl Ω L))
    (hC : GC.clRk l (upl Ω L ⊓ η.ker ⊓ (barChar O Ψ).ker ⊓ (cycMod ℚ Ω l 1).ker) ≤ C₀) (hm : 3 * C₀ + 7 < l ^ m) :
    Φ.Ok C₀ ∧ Φ.Big C₀ := by
  haveI : IsAlgClosure (W.Lp L) Ω :=
    ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) (W.Lp L)⟩
  have hb := ok_basic l η Ψ σ B M Hb hG m L g₁ Φ hU hL hg
  obtain ⟨h_del_open, h_csq, h_delc, h_loc, h_eps, h_Ψopen, h_Ψc, h_g0, h_card, h_cw, h_delcw,
    h_f2a, h_f2b, h_f2c, h_f3, h_f5, h_ΨN, h_dv, h_ne⟩ := hb
  have hf4 := frobenius_galoisField_four_compatibility l η Ψ σ B M Hb hG m L g₁ Φ hU hL 1 (Or.inl rfl) (hS 1 (Or.inl rfl))
  have hf4' := frobenius_galoisField_four_compatibility l η Ψ σ B M Hb hG m L g₁ Φ hU hL 2 (Or.inr rfl) (hS 2 (Or.inr rfl))
  rw [pow_one] at hf4
  obtain ⟨k, S, π, ι, pl, e, c, hF, hπ, hι⟩ := hL
  have hrk : GC.clRk l (((η.ker ⊓ (barChar O Ψ).ker).comap (galEmb ℚ (W.Lp L) Ω)) ⊓
      (cycMod (W.Lp L) Ω l 1).ker) ≤ C₀ := by
    rw [rk_link l L η.ker (barChar O Ψ).ker]
    exact hC
  have hom : ∀ v : Φ.V, ∃ s, (Φ.om (ResidueField O)) ((Φ.loc v) s) ≠ 1 := by
    intro v
    obtain ⟨g, hg'⟩ := k.mu v
    refine ⟨g, fun h => hg' ?_⟩
    rw [k.j_loc] at h
    simp only [Frame.om, MonoidHom.comp_apply, k.eps] at h
    have h1 := congrArg Units.val h
    simp only [Units.coe_map, Units.val_one, MonoidHom.coe_coe, RingHom.coe_comp,
      Function.comp_apply] at h1
    apply Units.ext
    simp only [cycMod, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, Units.val_one]
    exact one_of_cast l (ResidueField O) _ h1
  have hfin : Finite (ResidueField O) := hG.fin
  have hok : Φ.Ok C₀ :=
    { l_odd := hG.odd
      fin := hfin
      del_open := h_del_open
      c_sq := h_csq
      del_c := h_delc
      loc_cont := h_loc
      eps_cont := h_eps
      Ψ_open := h_Ψopen
      Ψ_c := h_Ψc
      baseSubgroup_spec := h_g0
      phi := GC.phi _ Ω l _ Φ S _ π ι k.pl pl e c hF
      card_inf := h_card
      cw_sq := h_cw
      del_cw := h_delcw
      f2a := h_f2a
      f2b := h_f2b
      f2c := h_f2c
      f3 := h_f3
      f4 := hf4
      f4' := hf4'
      f5 := h_f5
      Ψ_N := h_ΨN
      gen := GC.gen P _ Ω l _ Φ S _ π ι k.pl pl e c hF hom
      cl := GC.cl _ Ω l _ Φ S _ π ι k.pl pl e c hF
      ec := GC.ec P _ Ω l _ Φ S _ π ι k.pl pl e c hF
      b1p := GC.b1p _ Ω l _ Φ S _ π ι k.pl pl e c hF h_f3 C₀ hrk
      b1 := GC.b1 _ Ω l _ Φ S _ π ι k.pl pl e c hF h_f3 C₀ hrk
      h1 := GC.h1 P _ Ω l _ Φ S _ π ι k.pl pl e c hF hfin hom C₀ hrk }
  refine ⟨hok, ?_, ?_⟩
  · obtain ⟨v⟩ := h_ne
    have h1 : Φ.dv v ≤ Φ.d := by
      unfold Frame.d
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
    have := h_dv v
    omega
  · intro v
    have := h_dv v
    omega

theorem UpperTheory.V.Fr.frame_ex :
    GC.Hypotheses₂ → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∀ Q : ℕ, Q ≠ 0 → HasFrameW l η Ψ σ B M Q := by
  intro P Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG Q hQ
  obtain ⟨H₀, h0⟩ := exists_twistCharacter_continuousCohomology l η Ψ σ B M Hb hG
  obtain ⟨w, hw, hwQ⟩ := auxw_ex l η Ψ σ B M Hb hG Q hQ
  obtain ⟨C₀, hC₀⟩ := b0 l η Ψ σ B M Hb hG H₀ w h0 hw
  have hl : l.Prime := Fact.out
  set m := 3 * C₀ + 7 with hm_def
  have hm : 3 * C₀ + 7 < l ^ m := Nat.lt_pow_self hl.one_lt
  have hU := ufacts l η Ψ σ B M Hb hG H₀ w h0 hw m
  obtain ⟨L, iF, iN, iC, iA, hab, hup, hgal⟩ := field_ex l η Ψ σ B M Hb hG m _ hU
  have hM : B.valuation (M : Ω) < 1 := by
    obtain ⟨t, ht⟩ := hG.l_dvd
    rw [ht, Nat.cast_mul, map_mul]
    have hle : B.valuation (t : Ω) ≤ 1 := B.valuation_le_one ⟨(t : Ω), natCast_mem B t⟩
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hle) hG.over_l
  obtain ⟨s, ⟨hsD, hsU⟩, hs2⟩ := hU.f3 B hG.over_l
  have hsη : s ∈ η.ker := hU.split B hM ⟨hsD, hsU⟩
  have hs : s ∈ galOf ℚ L Ω := by
    rw [hgal]
    exact ⟨hsU, hsη⟩
  rw [← hup] at hU
  obtain ⟨Φ, hL⟩ := link_ex l η Ψ σ B M Hb hG m L s hU hab (by rw [hgal, hup]) hs
  have hS : ∀ a : ℕ, a = 1 ∨ a = 2 → StrictCl l η Ψ ((barChar O Ψ)⁻¹ ^ a * etaO O η) (upl Ω L) := by
    intro a ha
    rw [hup]
    exact strict P l η Ψ σ B M Hb hG H₀ w h0 hw m a ha
  have hC : GC.clRk l (upl Ω L ⊓ η.ker ⊓ (barChar O Ψ).ker ⊓ (cycMod ℚ Ω l 1).ker) ≤ C₀ := by
    rw [hup]
    exact hC₀ m
  obtain ⟨hok, hbig⟩ := ok_link P l hG m C₀ L s Φ hU hL hs2 hS hC hm
  refine ⟨L, iF, iN, iC, iA, s, Φ, C₀, w, hL, hok, hbig, hw, hwQ, ?_⟩
  rw [hup]
  intro x hx
  exact hx.1.1.2
