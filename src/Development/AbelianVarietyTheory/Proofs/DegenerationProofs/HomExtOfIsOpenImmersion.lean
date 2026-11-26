module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemRangeAppLEChartIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteTorusExtensionOfModel
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RegularOfBoundedAtPadicAlgClPoints

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomExtOfIsOpenImmersion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}
  {Ω' : Type} [Field Ω'] [Algebra o Ω'] {M' : RatModel o Ω'} {φ : Ω →ₐ[o] Ω'}

theorem hom_ext_of_isOpenImmersion {W : Scheme.{0}} (q : W ⟶ M'.Z) [IsOpenImmersion q] {p : Sp Ω' ⟶ W}
    (hp : p ≫ q = M'.pt) {g h : W ⟶ M.Z} (hg : p ≫ g = spMap φ.toRingHom ≫ M.pt)
    (hh : p ≫ h = spMap φ.toRingHom ≫ M.pt) : g = h := by
  have := M.sep
  have : IsReduced W := isReduced_of_isOpenImmersion q
  have : IsDominant p := by
    refine ⟨q.isOpenEmbedding.isInducing.dense_iff.2 fun w => ?_⟩
    have e : q '' Set.range p = Set.range M'.pt := by
      rw [← hp, ← Set.range_comp]
      rfl
    rw [e]
    exact M'.pt.denseRange _
  refine ext_of_isDominant_of_isSeparated M.s (ext_of_isDominant p ?_) p (hg.trans hh.symm)
  rw [← Category.assoc, hg, ← Category.assoc, hh]

theorem exists_hom_of_map_ringOn {U : M.Z.Opens} (hU : IsAffineOpen U) (hUne : (U : Set M.Z).Nonempty)
    {V : M'.Z.Opens} (hVne : (V : Set M'.Z).Nonempty) (h : ∀ x ∈ M.ringOn U, φ x ∈ M'.ringOn V) :
    ∃ g : Spec Γ(M'.Z, V) ⟶ M.Z,
      Spec.map (valMap M'.pt V (M'.top_le_preimage_pt hVne)) ≫ g = spMap φ.toRingHom ≫ M.pt := by
  let χ : M.ringOn U →+* M'.ringOn V :=
    (φ.toRingHom.comp (M.ringOn U).val.toRingHom).codRestrict (M'.ringOn V) fun x => h x x.2
  let ψ : Γ(M.Z, U) →+* Γ(M'.Z, V) :=
    (M'.sectionsEquiv V hVne).symm.toRingHom.comp (χ.comp (M.sectionsEquiv U hUne).toRingHom)
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec, ?_⟩
  conv_rhs => rw [← specMap_valMap_fromSpec hU M.pt (M.top_le_preimage_pt hUne)]
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  congr 2
  ext a
  have e : (M'.sectionsEquiv V hVne (ψ a) : Ω') = φ (M.sectionsEquiv U hUne a) :=
    congrArg Subtype.val ((M'.sectionsEquiv V hVne).apply_symm_apply _)
  exact e

theorem exists_isHom_of_local (h : ∀ z : M'.Z, ∃ (V : M'.Z.Opens) (U : M.Z.Opens), z ∈ V ∧ IsAffineOpen U ∧
    (U : Set M.Z).Nonempty ∧ ∀ x ∈ M.ringOn U, φ x ∈ M'.ringOn V) : ∃ f, M.IsHom M' φ f := by
  have h' : ∀ z : M'.Z, ∃ (V : M'.Z.Opens) (_ : IsAffineOpen V) (hz : z ∈ V) (g : Spec Γ(M'.Z, V) ⟶ M.Z),
      Spec.map (valMap M'.pt V (M'.top_le_preimage_pt ⟨z, hz⟩)) ≫ g = spMap φ.toRingHom ≫ M.pt := fun z => by
    obtain ⟨V, U, hz, hU, hne, H⟩ := h z
    obtain ⟨W, hW, hzW, hle⟩ := exists_isAffineOpen_mem_and_subset hz
    exact ⟨W, hW, hzW, exists_hom_of_map_ringOn hU hne ⟨z, hzW⟩ fun x hx => ringOn_anti hle (H x hx)⟩
  choose V hV hz g hg using h'
  have hp := fun z => specMap_valMap_fromSpec (hV z) M'.pt (M'.top_le_preimage_pt ⟨z, hz z⟩)
  let 𝒰 : M'.Z.OpenCover := Scheme.Cover.mkOfCovers M'.Z (fun z => Spec Γ(M'.Z, V z)) (fun z => (hV z).fromSpec)
    fun z => by
      have : z ∈ Set.range (hV z).fromSpec := (hV z).range_fromSpec ▸ hz z
      exact ⟨z, this⟩
  have hc : ∀ z w, pullback.fst (hV z).fromSpec (hV w).fromSpec ≫ g z =
      pullback.snd (hV z).fromSpec (hV w).fromSpec ≫ g w := fun z w =>
    hom_ext_of_isOpenImmersion (φ := φ) (pullback.fst _ _ ≫ (hV z).fromSpec)
      (p := pullback.lift _ _ ((hp z).trans (hp w).symm))
      (by rw [pullback.lift_fst_assoc, hp]) (by rw [pullback.lift_fst_assoc, hg])
      (by rw [pullback.lift_snd_assoc, hg])
  refine ⟨𝒰.glueMorphisms g hc, ?_⟩
  have e : (hV (genericPoint M'.Z)).fromSpec ≫ 𝒰.glueMorphisms g hc = g _ := 𝒰.ι_glueMorphisms g hc _
  unfold IsHom
  rw [← hg (genericPoint M'.Z), ← e, ← Category.assoc, hp]

theorem Div.map_mem_O_of_mem_adjoin {J : Type} {t : J → Ω} {i : J} {z : M'.Z}
    (h : M'.Div (fun j => φ (t j)) i z) {x : Ω} (hx : x ∈ Algebra.adjoin o (Set.range fun j => t j / t i)) :
    φ x ∈ M'.O z := by
  refine (Algebra.adjoin_le ?_ : _ ≤ (M'.O z).comap φ) hx
  rintro _ ⟨j, rfl⟩
  simpa using h.2 j

theorem Div.map_mem_O_of_isIntegral {J : Type} {t : J → Ω} {i : J} {z : M'.Z}
    (h : M'.Div (fun j => φ (t j)) i z) [IsIntegrallyClosed (M'.O z)] {x : Ω}
    (hx : IsIntegral (Algebra.adjoin o (Set.range fun j => t j / t i)) x) : φ x ∈ M'.O z := by
  let χ : Algebra.adjoin o (Set.range fun j => t j / t i) →+* M'.O z :=
    (φ.toRingHom.comp (Subalgebra.val _).toRingHom).codRestrict (M'.O z) fun y => h.map_mem_O_of_mem_adjoin y.2
  have hi : IsIntegral (M'.O z) (φ x) := hx.map_of_comp_eq χ φ.toRingHom (RingHom.ext fun _ => rfl)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  exact hy ▸ y.2

theorem IsCl.exists_isHom {J : Type} [Finite J] {t : J → Ω} (h : M.IsCl t) (hd : M'.HasDiv fun j => φ (t j)) :
    ∃ f, M.IsHom M' φ f := by
  refine exists_isHom_of_local fun z => ?_
  obtain ⟨i, hi⟩ := hd z
  have hi0 : t i ≠ 0 := (map_ne_zero φ).1 hi.1
  obtain ⟨U, hU, hD, hR⟩ := h.2 i hi0
  exact ⟨⟨_, M'.isOpen_setOf_div (fun j => φ (t j)) i⟩, U, hi, hU,
    ⟨genericPoint M.Z, hD ▸ div_genericPoint hi0⟩,
    fun x hx => mem_ringOn.2 fun w hw => Div.map_mem_O_of_mem_adjoin hw (hR ▸ hx)⟩

theorem IsNm.exists_isHom {J : Type} [Finite J] {t : J → Ω} (h : M.IsNm t) (hd : M'.HasDiv fun j => φ (t j))
    (hn : ∀ z, IsIntegrallyClosed (M'.O z)) : ∃ f, M.IsHom M' φ f := by
  refine exists_isHom_of_local fun z => ?_
  obtain ⟨i, hi⟩ := hd z
  have hi0 : t i ≠ 0 := (map_ne_zero φ).1 hi.1
  obtain ⟨U, hU, hD, hR⟩ := h.2 i hi0
  exact ⟨⟨_, M'.isOpen_setOf_div (fun j => φ (t j)) i⟩, U, hi, hU,
    ⟨genericPoint M.Z, hD ▸ div_genericPoint hi0⟩,
    fun x hx => mem_ringOn.2 fun w hw => Div.map_mem_O_of_isIntegral hw ((hR x).1 hx)⟩

end GlobalTheory.ZH.RatModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecializesIsLocalization
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem finite_notMem_coheight_le_one {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X] (U : X.Opens)
    (hU : (U : Set X).Nonempty) : {ξ : X | ξ ∉ U ∧ Order.coheight ξ ≤ 1}.Finite := by
  obtain ⟨S, hS, hcl, hirr, hun⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible U.isOpen.isClosed_compl
  have hg : genericPoint X ∈ U := (genericPoint_specializes hU.some).mem_open U.isOpen hU.some_mem
  refine (hS.biUnion (t := fun C => {κ | IsGenericPoint κ C}) fun C _ =>
    Set.Subsingleton.finite fun _ h _ h' => h.eq h').subset ?_
  rintro ξ ⟨hξ, h1⟩
  obtain ⟨C, hC, hξC⟩ : ξ ∈ ⋃₀ S := hun ▸ hξ
  obtain ⟨κ, hκ⟩ := QuasiSober.sober (hirr C hC) (hcl C hC)
  have hκU : κ ∈ (U : Set X)ᶜ := hun ▸ ⟨C, hC, hκ.mem⟩
  refine Set.mem_biUnion hC ?_
  by_cases h : ξ ⤳ κ
  · rwa [(h.antisymm (hκ.specializes hξC)).eq]
  · have hlt : ξ < κ := lt_of_le_not_ge (hκ.specializes hξC) h
    have hlt' : κ < genericPoint X := lt_of_le_not_ge (genericPoint_specializes κ)
      fun h' => hκU (((genericPoint_specializes κ).antisymm h').eq ▸ hg)
    have h2 := (add_le_add_left (le_add_self.trans (Order.coheight_add_one_le hlt')) 1).trans
      ((Order.coheight_add_one_le hlt).trans h1)
    exact absurd h2 (by decide)

namespace RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)

theorem isNoetherian [IsNoetherianRing o] : IsNoetherian M.Z :=
  have := M.lft
  have := M.qc
  have : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  have : CompactSpace M.Z := QuasiCompact.compactSpace_of_compactSpace M.s
  {}

theorem isNoetherianRing_O [IsNoetherianRing o] (z : M.Z) : IsNoetherianRing (M.O z) :=
  have := M.isNoetherian
  isNoetherianRing_of_ringEquiv _ (M.stalkEquiv z)

theorem coheight_le_one_of_valuationRing [IsNoetherianRing o] {ξ : M.Z} (h : ValuationRing (M.O ξ)) :
    Order.coheight ξ ≤ 1 := by
  have := M.isNoetherianRing_O ξ
  have : IsPrincipalIdealRing (M.O ξ) := IsPrincipalIdealRing.of_isNoetherianRing_of_isBezout
  have h1 : ringKrullDim (M.O ξ) ≤ 1 := Ring.krullDimLE_iff.1 inferInstance
  rw [← ringKrullDim_eq_of_ringEquiv (M.stalkEquiv ξ), ringKrullDim_stalk_eq_coheight] at h1
  exact_mod_cast h1

theorem exists_specializes_isLocalization (z : M.Z) (q : Ideal (M.O z)) [q.IsPrime] :
    ∃ (ξ : M.Z) (h : ξ ⤳ z),
      letI := (Subalgebra.inclusion (O_le_of_specializes h)).toRingHom.toAlgebra
      IsLocalization.AtPrime (M.O ξ) q := by
  obtain ⟨V, hV, hz, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := z) trivial
  let ψ : ∀ {x : M.Z} (_ : x ∈ V), Γ(M.Z, V) →+* M.O x := fun {x} hx =>
    (M.stalkEquiv x).toRingHom.comp (M.Z.presheaf.germ V x hx).hom
  have hψ : ∀ {x : M.Z} (hx : x ∈ V) (f : Γ(M.Z, V)), ψ hx f = ⟨valF M.pt V f, valF_mem_O hx f⟩ :=
    fun hx f => stalkEquiv_germ hx f
  have hloc : ∀ (p : PrimeSpectrum Γ(M.Z, V)) (hp : hV.fromSpec p ∈ V),
      @IsLocalization.AtPrime _ _ (M.O (hV.fromSpec p)) _ (ψ hp).toAlgebra p.asIdeal _ := fun p hp => by
    let : Algebra Γ(M.Z, V) (M.Z.presheaf.stalk (hV.fromSpec p)) :=
      TopCat.Presheaf.algebra_section_stalk M.Z.presheaf (U := V) ⟨_, hp⟩
    let := (ψ hp).toAlgebra
    have : IsLocalization p.asIdeal.primeCompl (M.Z.presheaf.stalk (hV.fromSpec p)) :=
      hV.isLocalization_stalk' p hp
    exact IsLocalization.isLocalization_of_algEquiv p.asIdeal.primeCompl
      ({ M.stalkEquiv _ with commutes' := fun _ => rfl } :
        M.Z.presheaf.stalk (hV.fromSpec p) ≃ₐ[Γ(M.Z, V)] M.O (hV.fromSpec p))
  have hmem : ∀ p : PrimeSpectrum Γ(M.Z, V), hV.fromSpec p ∈ V := fun p => by
    rw [← SetLike.mem_coe, ← hV.range_fromSpec]
    exact ⟨_, rfl⟩
  obtain ⟨p₀, rfl⟩ : ∃ p₀ : PrimeSpectrum Γ(M.Z, V), hV.fromSpec p₀ = z :=
    (hV.range_fromSpec ▸ hz : z ∈ Set.range hV.fromSpec)
  let := (ψ hz).toAlgebra
  have h₀ := hloc p₀ hz
  let p : PrimeSpectrum Γ(M.Z, V) := ⟨q.comap (ψ hz), inferInstance⟩
  have hle : p.asIdeal ≤ p₀.asIdeal := fun a ha =>
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (M.O (hV.fromSpec p₀)) p₀.asIdeal a).1
      (IsLocalRing.le_maximalIdeal_of_isPrime q ha)
  have hs : hV.fromSpec p ⤳ hV.fromSpec p₀ :=
    ((PrimeSpectrum.le_iff_specializes p p₀).1 hle).map hV.fromSpec.continuous
  refine ⟨_, hs, ?_⟩
  let := (Subalgebra.inclusion (O_le_of_specializes hs)).toRingHom.toAlgebra
  let := (ψ (hmem p)).toAlgebra
  have h₁ := hloc p (hmem p)
  have : IsScalarTower Γ(M.Z, V) (M.O (hV.fromSpec p₀)) (M.O (hV.fromSpec p)) :=
    IsScalarTower.of_algebraMap_eq fun a => (hψ (hmem p) a).trans
      (congrArg (Subalgebra.inclusion (O_le_of_specializes hs)) (hψ hz a)).symm
  have h₂ := IsLocalization.isLocalization_of_submonoid_le (M.O (hV.fromSpec p₀)) (M.O (hV.fromSpec p))
    p₀.asIdeal.primeCompl p.asIdeal.primeCompl (fun a ha h => ha (hle h))
  refine IsLocalization.of_le_of_exists_dvd (p.asIdeal.primeCompl.map (algebraMap _ (M.O (hV.fromSpec p₀)))) _
    (by rintro _ ⟨a, ha, rfl⟩; exact ha) fun n hn => ?_
  obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj p₀.asIdeal.primeCompl n
  refine ⟨_, ⟨a, fun ha => ?_, rfl⟩, _, e.symm⟩
  have ha' : algebraMap _ (M.O (hV.fromSpec p₀)) a ∈ q := ha
  rw [← e] at ha'
  exact hn ((Ideal.mul_unit_mem_iff_mem q (IsLocalization.map_units _ s)).1 ha')

theorem mem_O_of_forall_valuationRing [IsNoetherianRing o] (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z)
    (z : M.Z) (φ : Ω) (h : ∀ ξ : M.Z, ξ ⤳ z → ValuationRing (M.O ξ) → φ ∈ M.O ξ) : φ ∈ M.O z := by
  have := M.isNoetherianRing_O z
  have := isIntegrallyClosed_O hn z
  obtain ⟨y, rfl⟩ : φ ∈ (algebraMap (M.O z) Ω).range := by
    refine (mem_range_algebraMap_iff_forall_height_eq_one φ).mpr fun q _ h1 => ?_
    obtain ⟨ξ, hξ, hloc⟩ := M.exists_specializes_isLocalization z q
    let := (Subalgebra.inclusion (O_le_of_specializes hξ)).toRingHom.toAlgebra
    have : IsScalarTower (M.O z) (M.O ξ) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have := isDiscreteValuationRing_of_height_eq_one q h1 (M.O ξ)
    exact (mem_range_algebraMap_iff_mem_primeLocalSubalgebra q (M.O ξ) φ).mp
      ⟨⟨φ, h ξ hξ inferInstance⟩, rfl⟩
  exact y.2

end RatModel

theorem normalModel_height_le_one :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) [IsNoetherianRing o],
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (z : M.Z),
      (∀ φ : Ω, (∀ ξ : M.Z, ξ ⤳ z → ValuationRing (M.O ξ) → φ ∈ M.O ξ) → φ ∈ M.O z) ∧
      IsNoetherianRing (M.O z) ∧
      ∀ U : M.Z.Opens, (U : Set M.Z).Nonempty → {ξ : M.Z | ξ ∉ U ∧ ValuationRing (M.O ξ)}.Finite := by
  intro o Ω _ _ _ M _ hn z
  have := M.isNoetherian
  exact ⟨M.mem_O_of_forall_valuationRing hn z, M.isNoetherianRing_O z, fun U hU =>
    (finite_notMem_coheight_le_one U hU).subset fun _ h => ⟨h.1, M.coheight_le_one_of_valuationRing h.2⟩⟩

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMaximalComapMaximalIdealOO
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

open GlobalTheory.Points IsLocalRing

variable {p : ℕ} [Fact p.Prime]

noncomputable def padicIntToOO (p : ℕ) [Fact p.Prime] : ℤ_[p] →+* OO p :=
  (algebraMap ℤ_[p] (PadicAlgCl p)).codRestrict (OO p) fun _ =>
    (mem_OO_iff _).2 ((GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).1 isIntegral_algebraMap)

theorem isIntegral_padicIntToOO : (padicIntToOO p).IsIntegral := by
  intro x
  obtain ⟨q, hq, h⟩ := (GlobalTheory.isIntegral_padicInt_iff_norm_le_one (x : PadicAlgCl p)).2 ((mem_OO_iff _).1 x.2)
  refine ⟨q, hq, Subtype.ext ?_⟩
  exact (Polynomial.hom_eval₂ q (padicIntToOO p) (OO p).subtype x).trans h

theorem natCast_residueField_OO : ((p : ℕ) : ResidueField (OO p)) = 0 := by
  rw [← map_natCast (residue (OO p)), residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
    not_isUnit_OO_iff]
  have h : (((p : ℕ) : OO p) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) p := by simp
  rw [h, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

theorem isIntegral_int_residueField_OO : (Int.castRingHom (ResidueField (OO p))).IsIntegral := by
  intro x
  set ψ : ℤ_[p] →+* ResidueField (OO p) := (residue (OO p)).comp (padicIntToOO p)
  have hψ : ψ.IsIntegral :=
    RingHom.IsIntegral.trans _ _ isIntegral_padicIntToOO
      (RingHom.isIntegral_of_surjective _ residue_surjective)
  obtain ⟨q, hq, h⟩ := hψ x
  have hl : q.map ψ ∈ Polynomial.lifts (Int.castRingHom (ResidueField (OO p))) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    have h1 := PadicInt.sub_zmodRepr_mem (q.coeff n)
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h1
    obtain ⟨c, hc⟩ := h1
    have h2 := congrArg ψ hc
    rw [map_sub, map_mul, map_natCast, map_natCast, natCast_residueField_OO, zero_mul, sub_eq_zero] at h2
    exact ⟨((q.coeff n).zmodRepr : ℤ), by rw [h2]; simp⟩
  obtain ⟨r, hr, -, hrm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (hq.map ψ)
  refine ⟨r, hrm, ?_⟩
  rw [← Polynomial.eval_map, hr, Polynomial.eval_map, h]

theorem isMaximal_comap_maximalIdeal_OO {A : Type*} [CommRing A] (φ : A →+* OO p) :
    ((maximalIdeal (OO p)).comap φ).IsMaximal := by
  have h : ((residue (OO p)).comp φ).IsIntegral := by
    refine RingHom.IsIntegral.tower_top (Int.castRingHom A) _ ?_
    rw [RingHom.ext_int (RingHom.comp _ _) (Int.castRingHom _)]
    exact isIntegral_int_residueField_OO
  have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ h ⊥
  rwa [← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot, ker_residue] at this

theorem isClosed_singleton_cPt {X : Scheme.{0}} (y : Sp (OO p) ⟶ X) : IsClosed ({y (cPt p)} : Set X) := by
  rw [← closure_subset_iff_isClosed]
  intro w hw
  have hs : y (cPt p) ⤳ w := specializes_iff_mem_closure.2 hw
  obtain ⟨U, hU, hwU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := w) trivial
  have hzU : y (cPt p) ∈ U := hs.mem_open U.isOpen hwU
  have hle : ⊤ ≤ y ⁻¹ᵁ U := (le_preimage_iff y U).2 hzU
  have key : ∀ f : Γ(X, U), y (cPt p) ∈ X.basicOpen f ↔
      f ∉ (maximalIdeal (OO p)).comap (valMap y U hle).hom := fun f => by
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff, not_not, ← le_preimage_iff,
      le_preimage_basicOpen_iff y hle, valR_eq y U hle]
  have hm := isMaximal_comap_maximalIdeal_OO (valMap y U hle).hom
  refine (Specializes.antisymm ?_ hs).eq
  rw [specializes_iff_forall_open]
  intro V hV hzV
  obtain ⟨f, hfV, hzf⟩ := hU.exists_basicOpen_le (V := ⟨V, hV⟩) ⟨_, hzV⟩ hzU
  refine hfV ?_
  obtain ⟨g, c, hc, e⟩ := hm.exists_inv ((key f).1 hzf)
  have hwc : w ∉ X.basicOpen c := fun h => (key c).1 (hs.mem_open (X.basicOpen c).isOpen h) hc
  rw [X.mem_basicOpen _ _ hwU] at hwc
  show w ∈ X.basicOpen f
  rw [X.mem_basicOpen _ _ hwU]
  have e' := congrArg (X.presheaf.germ U w hwU).hom e
  rw [map_add (f := _), map_mul, map_one] at e'
  rcases isUnit_or_isUnit_of_add_one e' with h | h
  · exact isUnit_of_mul_isUnit_right h
  · exact absurd h hwc

theorem isClosed_centre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [Algebra.FiniteType ℤ o]
    (M : RatModel o Ω) (U : Set M.Z) (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z),
    M.Cen U z y → IsClosed ({z} : Set M.Z) :=
  fun _ _ _ _ _ _ _ _ _ _ _ y h => h.1 ▸ isClosed_singleton_cPt y

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantTermRepresentativeDependence
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantTermRepresentativeDependence
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex.NumD
variable {O : Type} [CommRing O] (N : NumD O)

theorem vt_mul_io_shift (g : N.Gt) (w χ : N.X) :
    ((N.ψ w * g.s w : Oˣ) : O) * N.vt (g * N.io w) χ = N.vt g (χ + w) := by
  have e : N.c χ * (g * N.io w).b = N.c (χ + w) * g.b := by
    rw [Gt.mul_b, io_b, N.c_add, mul_assoc, mul_comm g.b]
  rw [vt, vt, e, ← mul_assoc, ← Units.val_mul]
  congr 2
  have a := congrArg Additive.ofMul (g.mult χ w)
  rw [Gt.mul_s, io_s, io_b, N.ψ_add, N.τ_symm w χ, N.cub.s12 (N.c χ) g.b]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div] at a ⊢
  linear_combination (norm := abel) -a

theorem vt_mul_tor_shift (g : N.Gt) (t : Multiplicative N.X →* Oˣ) (χ : N.X) :
    N.vt (g * N.tor t) χ = (t (Multiplicative.ofAdd χ) : Oˣ) * N.vt g χ := by
  rw [vt, vt, mul_comm g, N.tor_mul_s_apply, Gt.mul_b, tor_b, one_mul, mul_left_comm (N.ψ χ), Units.val_mul, mul_assoc]

theorem tk_qTriv_right {k : ℕ} (p : N.QT k) (z : N.X) : N.tk p (N.qTriv k z) = p.1.2.s z ^ k :=
  ((GlobalTheory.T.degenerationData_psi_quadratic_generators_linear O N k z).2.2 p.1.2).1

theorem tk_qTriv_left {k : ℕ} (p : N.QT k) (z : N.X) : N.tk (N.qTriv k z) p = p.1.2.s z ^ k := by
  rw [← Gt.pow_s, N.mem_QT.1 p.2, io_s, N.τ_symm]
  rfl

theorem wQ_qTriv_odd {k : ℕ} (hk : Odd k) (z : N.X) : N.wQ (N.qTriv k z) = N.ψ z ^ k := by
  symm
  rw [(GlobalTheory.T.wQ_characterization_and_mul_relation O N k hk (N.qTriv k z) (N.qTriv k z)).1, tk_qTriv_right]
  obtain ⟨h₁, h₂, -⟩ := GlobalTheory.T.degenerationData_psi_quadratic_generators_linear O N k z
  constructor
  · change _ * dbl N.θ N.σ (N.c z) ^ k = N.τ z z ^ k
    rw [h₁, mul_pow, ← pow_mul, ← pow_mul, mul_comm k 2]
  · change _ = N.ψ (k • z) * mulq N.θ N.σ k (N.c z)
    rw [h₂, ← pow_mul, sq]

theorem wQ_mul_qTriv_odd {k : ℕ} (hk : Odd k) (p : N.QT k) (z : N.X) :
    N.wQ (p * N.qTriv k z) = N.wQ p * N.ψ z ^ k * p.1.2.s z ^ k := by
  have h := (GlobalTheory.T.wQ_characterization_and_mul_relation O N k hk p (N.qTriv k z)).2.1
  rw [wp, tk_qTriv_right, tk_qTriv_left, div_self', one_pow, one_mul, N.wQ_qTriv_odd hk] at h
  exact h.symm

theorem txT_mul_qTriv {m : ℕ} (hm : Odd m) (p : N.QT (m ^ 2)) (z χ : N.X) :
    N.txT m (p * N.qTriv (m ^ 2) z) χ = N.txT m p (χ + m • z) := by
  have e : (p * N.qTriv (m ^ 2) z).1.2 = p.1.2 * N.io z := rfl
  rw [txT, txT, N.wQ_mul_qTriv_odd hm.pow, e, mul_pow, ← N.io_nsmul, ← N.vt_mul_io_shift, ← mul_assoc,
    ← Units.val_mul]
  congr 2
  have h₁ := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB m 0 p.1.2.b (N.c z)).2.1
  obtain ⟨-, h₂, h₃⟩ := GlobalTheory.T.degenerationData_psi_quadratic_generators_linear O N m z
  have h₄ := congrArg (· ^ m) (h₃ p.1.2).1
  have h₅ := Gt.pow_s p.1.2 m (m • z)
  rw [N.c_nsmul] at h₅
  simp only [mul_pow, ← pow_mul, ← sq] at h₄
  rw [Gt.mul_b, io_b, h₁, ← h₂, ← h₄, ← h₅]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]
  abel

theorem txT_mul_tor {m : ℕ} (hm : Odd m) (p p' : N.QT (m ^ 2)) (χ : N.X) (t : Multiplicative N.X →* Oˣ)
    (h : p'.1.1 = p.1.1) (h' : p'.1.2 = p.1.2 * N.tor t) :
    N.txT m p' χ = (t p.1.1 ^ ((m ^ 2 - 1) / 2) * t (Multiplicative.ofAdd (p.1.1.toAdd + m • χ)) : Oˣ) *
      N.txT m p χ := by
  have ht : t ^ (m ^ 2) = 1 := by
    apply N.tor_injective
    have a := N.mem_QT.1 p'.2
    rw [h, h', mul_pow, N.mem_QT.1 p.2, mul_eq_left] at a
    rw [N.tor_pow, a, N.tor_one]
  obtain ⟨j, hj⟩ : Odd (m ^ 2) := hm.pow
  have hd : (m ^ 2 - 1) / 2 = j := by omega
  have hy : t p.1.1 ^ j * t p.1.1 ^ j * t p.1.1 = 1 := by
    rw [← pow_add, ← pow_succ, ← two_mul, ← hj, ← MonoidHom.pow_apply, ht, MonoidHom.one_apply]
  have hb : p'.1.2.b = p.1.2.b := by rw [h', Gt.mul_b, tor_b, mul_one]
  have hs : p'.1.2.s p.1.1.toAdd = t p.1.1 * p.1.2.s p.1.1.toAdd := by
    rw [h', mul_comm p.1.2, N.tor_mul_s_apply]
    rfl
  rw [txT, txT, wQ, wQ, NumB.wS, NumB.wS, hb, h, hs, h', mul_pow, ← N.tor_pow, vt_mul_tor_shift, hd,
    ← mul_assoc, ← mul_assoc, ← Units.val_mul, ← Units.val_mul]
  congr 2
  rw [ofAdd_add, ofAdd_toAdd, ofAdd_nsmul, map_mul, map_pow, MonoidHom.pow_apply]
  have a := congrArg Additive.ofMul hy
  apply Additive.ofMul.injective
  simp only [div_pow, mul_pow, ofMul_mul, ofMul_div, ofMul_one] at a ⊢
  linear_combination (norm := abel) -a

end GlobalTheory.Ex.NumD

namespace GlobalTheory.Ex

theorem txT_shift : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (m : ℕ), Odd m → ∀ (p p' : N.QT (m ^ 2)) (χ : N.X), (∀ z, p'.1.1.toAdd = p.1.1.toAdd + m ^ 2 • z → p'.1.2 = p.1.2 * N.io z → N.txT m p' χ = N.txT m p (χ + m • z)) ∧ (∀ t : Multiplicative N.X →* Oˣ, p'.1.1 = p.1.1 → p'.1.2 = p.1.2 * N.tor t → N.txT m p' χ = (t p.1.1 ^ ((m ^ 2 - 1) / 2) * t (Multiplicative.ofAdd (p.1.1.toAdd + m • χ)) : Oˣ) * N.txT m p χ) := by
  intro O _ N m hm p p' χ
  refine ⟨fun z h h' => ?_, fun t h h' => N.txT_mul_tor hm p p' χ t h h'⟩
  have e : p' = p * N.qTriv (m ^ 2) z := Subtype.ext (Prod.ext h h')
  rw [e, N.txT_mul_qTriv hm]

end GlobalTheory.Ex
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantTermRepresentativeDependenceStatement
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstantTerm_representative_dependence : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (m : ℕ), Odd m → ∀ (p p' : N.QT (m ^ 2)) (χ : N.X), (∀ z, p'.1.1.toAdd = p.1.1.toAdd + m ^ 2 • z → p'.1.2 = p.1.2 * N.io z → N.txT m p' χ = N.txT m p (χ + m • z)) ∧ (∀ t : Multiplicative N.X →* Oˣ, p'.1.1 = p.1.1 → p'.1.2 = p.1.2 * N.tor t → N.txT m p' χ = (t p.1.1 ^ ((m ^ 2 - 1) / 2) * t (Multiplicative.ofAdd (p.1.1.toAdd + m • χ)) : Oˣ) * N.txT m p χ) := by
  first | exact @GlobalTheory.Ex.txT_shift | exact GlobalTheory.Ex.txT_shift | (intros; apply GlobalTheory.Ex.txT_shift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteDvrTorusExtensionSpecialFibre
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open IsLocalRing

theorem nonempty_torusExtension_of_comp_eq {K : Type} [Field K] {S S₁ S₂ : Scheme.{0}} {a : S₁ ⟶ S}
    {b : Spec (CommRingCat.of K) ⟶ S₁} {c : S₂ ⟶ S} {d : Spec (CommRingCat.of K) ⟶ S₂} (e : b ≫ a = d ≫ c)
    (G : Over S) [GrpObj G] (h : Nonempty (TorusExtension ((Over.pullback b).obj ((Over.pullback a).obj G)))) :
    Nonempty (TorusExtension ((Over.pullback d).obj ((Over.pullback c).obj G))) := by
  obtain ⟨T⟩ := h
  haveI : IsMonHom (pullCompIso b a G).symm.hom := inferInstanceAs (IsMonHom (pullCompIso b a G).inv)
  have h₁ : Nonempty (TorusExtension ((Over.pullback (b ≫ a)).obj G)) := ⟨torusExtOfIso (pullCompIso b a G).symm T⟩
  rw [e] at h₁
  obtain ⟨T₁⟩ := h₁
  exact ⟨torusExtOfIso (pullCompIso d c G) T₁⟩

theorem exists_finite_dvr_torusExtension_specialFibre : ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] [IsAdicComplete (IsLocalRing.maximalIdeal V') V'] (G : Over (Spec (CommRingCat.of V'))) [GrpObj G], IsSemiAbelian G → ∃ (V'' : Type) (_ : CommRing V'') (_ : IsDomain V'') (_ : IsDiscreteValuationRing V'') (_ : IsAdicComplete (IsLocalRing.maximalIdeal V'') V'') (_ : Algebra V' V''), Module.Finite V' V'' ∧ Function.Injective (algebraMap V' V'') ∧ IsLocalHom (algebraMap V' V'') ∧ IsSemiAbelian (baseChange V' V'' G) ∧ Nonempty (TorusExtension (specialFibre V'' (baseChange V' V'' G))) := by
  intro V' _ _ _ _ G _ hG
  have h₀ : IsSemiAbelian ((Over.pullback (spMap (residue V'))).obj G) := IsSemiAbelian.pullback _ G hG
  haveI := h₀.smooth
  haveI := h₀.quasiCompact
  haveI := h₀.separated
  let k := ResidueField V'
  let Ω := AlgebraicClosure k
  obtain ⟨T⟩ := h₀.fibres Ω (spMap (algebraMap k Ω))
  obtain ⟨s, hs, H⟩ := FieldModel.exists_finite_torusExtension_range (algebraMap k Ω) _ T
  haveI : Finite s := hs.to_subtype
  haveI : FiniteDimensional k (IntermediateField.adjoin k s) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨V'', i1, i2, i3, i4, i5, hf, hi, hl, e, he⟩ := nb V' (IntermediateField.adjoin k s)
  refine ⟨V'', i1, i2, i3, i4, i5, hf, hi, hl, IsSemiAbelian.pullback _ G hG, ?_⟩
  have hT := H _ (ResidueField.map (algebraMap V' V''))
    ((algebraMap (IntermediateField.adjoin k s) Ω).comp e.symm.toRingHom)
    (by
      rw [← he]
      ext x
      simp [k])
    (fun x hx => ⟨e ⟨x, IntermediateField.subset_adjoin _ _ hx⟩, by simp⟩)
  refine nonempty_torusExtension_of_comp_eq ?_ G hT
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    ResidueField.map_comp_residue]
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClassicalPointsAndLocalRegularity
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)

theorem _root_.GlobalTheory.ZH.RatModel.locallyOfFiniteType_int [Algebra.FiniteType ℤ o] :
    LocallyOfFiniteType (M.s ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℤ o)) := by
  haveI := M.lft
  haveI : LocallyOfFiniteType (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℤ o)) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
  infer_instance

theorem _root_.GlobalTheory.ZH.RatModel.flat_int [CharZero Ω] (π : M.Z ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℤ) : Flat π := by
  rw [Flat.iff_flat_stalkMap]
  intro x
  haveI : CharZero (M.Z.presheaf.stalk x) :=
    RingHom.charZero ((M.O x).val.toRingHom.comp
      (M.stalkEquiv x).toRingHom)
  let q : PrimeSpectrum ℤ := π x
  haveI : q.asIdeal.IsPrime := q.isPrime
  letI : Algebra ((Spec.structureSheaf ℤ).presheaf.stalk q) (M.Z.presheaf.stalk x) :=
    (π.stalkMap x).hom.toAlgebra
  have hflat : Module.Flat ℤ (M.Z.presheaf.stalk x) := inferInstance
  have hT : @IsScalarTower ℤ ((Spec.structureSheaf ℤ).presheaf.stalk q)
      (M.Z.presheaf.stalk x)
      (StructureSheaf.stalkAlgebra ℤ q).toSMul this.toSMul (AddCommGroup.toIntModule _).toSMul := by
    refine @IsScalarTower.mk ℤ ((Spec.structureSheaf ℤ).presheaf.stalk q)
      (M.Z.presheaf.stalk x)
      (StructureSheaf.stalkAlgebra ℤ q).toSMul this.toSMul (AddCommGroup.toIntModule _).toSMul
      (fun n s m => ?_)
    have h1 := @Algebra.smul_def' ℤ ((Spec.structureSheaf ℤ).presheaf.stalk q) _ _
      (StructureSheaf.stalkAlgebra ℤ q) n s
    have h2 : @algebraMap ℤ ((Spec.structureSheaf ℤ).presheaf.stalk q) _ _
        (StructureSheaf.stalkAlgebra ℤ q) n = n :=
      eq_intCast _ n
    rw [h2] at h1
    erw [h1]
    rw [mul_smul, Int.cast_smul_eq_zsmul]
  exact (@Module.flat_iff_of_isLocalization ℤ ((Spec.structureSheaf ℤ).presheaf.stalk q) _ _
    (StructureSheaf.stalkAlgebra ℤ q) q.asIdeal.primeCompl (StructureSheaf.IsLocalization.to_stalk ℤ q)
    (M.Z.presheaf.stalk x) _ _ _ hT).mpr hflat

end GlobalTheory.ZH.RatModel

namespace GlobalTheory.ZH

theorem _root_.GlobalTheory.ZH.classical_points_and_local_regularity :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [Algebra.FiniteType ℤ o] [CharZero Ω]
      (M : _root_.GlobalTheory.ZH.RatModel o Ω)
      (U₀ : M.Z.Opens), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z →
      ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty →
        ∀ z : M.Z, IsClosed ({z} : Set M.Z) →
        (∃ (p : ℕ) (_ : Fact p.Prime)
          (y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (_root_.GlobalTheory.ZH.OO p) ⟶ M.Z),
          M.Cen U₁ z y) ∧
        ∀ φ ∈ M.ringOn U₁,
          (∀ (p : ℕ) [Fact p.Prime]
            (y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (_root_.GlobalTheory.ZH.OO p) ⟶ M.Z),
            M.Cen U₁ z y →
            ‖M.val (_root_.GlobalTheory.ZH.gPt p ≫ y) φ‖ ≤ 1) →
          φ ∈ M.O z) ∧ JacobsonSpace M.Z) := by
  intro o Ω _ _ _ _ _ M U₀ hN
  haveI := _root_.GlobalTheory.ZH.RatModel.locallyOfFiniteType_int M
  haveI : Flat (M.s ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℤ o)) := M.flat_int _
  refine ⟨fun U₁ _ hU₁ z hz => ⟨?_, ?_⟩,
    _root_.GlobalTheory.jacobsonSpace_of_locallyOfFiniteType_int (M.s ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℤ o))⟩
  · obtain ⟨p, hp, y, h1, h2⟩ := _root_.GlobalTheory.padicAlgCl_integral_points.1 M.Z
      (M.s ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℤ o)) z hz U₁ hU₁
    exact ⟨p, hp, y, h1, h2⟩
  · intro φ hφ hb
    obtain ⟨f, rfl⟩ :=
      (_root_.GlobalTheory.ZH.RatModel.mem_ringOn_iff_exists hU₁).1 hφ
    haveI := _root_.GlobalTheory.ZH.RatModel.isIntegrallyClosed_O hN z
    haveI : IsIntegrallyClosed (M.Z.presheaf.stalk z) :=
      IsIntegrallyClosed.of_equiv (M.stalkEquiv z).symm
    have hbounded : ∀ (p : ℕ) [Fact p.Prime]
        (y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (_root_.GlobalTheory.ZH.OO p) ⟶ M.Z),
        y (_root_.GlobalTheory.ZH.cPt p) = z →
        Set.range (_root_.GlobalTheory.ZH.gPt p ≫ y) ⊆ U₁ →
        ‖_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valF
          (_root_.GlobalTheory.ZH.gPt p ≫ y) U₁ f‖ ≤ 1 := by
      intro p _ y hy hr
      have hle := hb p y ⟨hy, hr⟩
      rwa [_root_.GlobalTheory.ZH.RatModel.val_valF hr] at hle
    haveI : Nonempty U₁ := hU₁.to_subtype
    obtain ⟨p, hp, hpx⟩ := _root_.GlobalTheory.exists_prime_residueField_eq_zero
      (M.s ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℤ o)) hz
    haveI : Fact p.Prime := ⟨hp⟩
    have hm := _root_.GlobalTheory.mem_range_stalk_of_forall_norm_le_one
      (M.s ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℤ o)) hz hpx (φ := f) fun K _ y hy hyx => by
        haveI := isLocalHom_integralClosureToPadicAlgClIntegers K
        have e : gPt p ≫ spMap (integralClosureToPadicAlgClIntegers K) ≫ y =
            spMap K.val.toRingHom ≫
              Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y := by
          rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
          rfl
        have h1 : (spMap (integralClosureToPadicAlgClIntegers K) ≫ y) (cPt p) =
            y (IsLocalRing.closedPoint (integralClosure ℤ_[p] K)) := by
          refine (Scheme.Hom.comp_apply _ _ _).trans (congrArg y ?_)
          exact IsLocalRing.comap_closedPoint (integralClosureToPadicAlgClIntegers K)
        have h2 : Set.range (gPt p ≫ (spMap (integralClosureToPadicAlgClIntegers K) ≫ y)) ⊆ U₁ := by
          rw [e]
          rintro _ ⟨q, rfl⟩
          exact hy (Set.mem_univ (spMap K.val.toRingHom q))
        have h3 : valF (gPt p ≫ (spMap (integralClosureToPadicAlgClIntegers K) ≫ y)) U₁ f =
            (((Scheme.ΓSpecIso (.of K)).hom
              ((Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y).appLE
                U₁ ⊤ hy f) : K) : PadicAlgCl p) := by
          rw [e]
          have ht : ⊤ ≤ (spMap K.val.toRingHom ≫
              (Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y)) ⁻¹ᵁ U₁ :=
            fun q _ => hy (Set.mem_univ (spMap K.val.toRingHom q))
          rw [valF, dite_eq_left ht]
          have eqn : (spMap K.val.toRingHom ≫
              (Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y)).appLE U₁ ⊤ ht ≫
              (Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl p))).hom =
              (Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y).appLE U₁ ⊤ hy ≫
              (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ CommRingCat.ofHom K.val.toRingHom := by
            rw [← Scheme.ΓSpecIso_naturality, ← Scheme.Hom.appLE_comp_appLE (spMap K.val.toRingHom) _ U₁ ⊤ ⊤ hy le_rfl, Category.assoc]
            rfl
          exact congrArg (fun g => g.hom f) eqn
        rw [← h3]
        exact hbounded p (spMap (integralClosureToPadicAlgClIntegers K) ≫ y) (h1.trans hyx) h2
    obtain ⟨W, hW, ψ, hzW, -, hs⟩ :=
      _root_.GlobalTheory.exists_germToFunctionField_eq_of_mem_range_stalk hm (W := ⊤) trivial
    have hg : ∀ (W : M.Z.Opens) [Nonempty W], genericPoint M.Z ∈ W := fun W h =>
      ((genericPoint_spec M.Z).mem_open_set_iff W.isOpen).mpr (by simpa using h)
    haveI : Nonempty (W ⊓ U₁ : M.Z.Opens) := ⟨⟨_, hg W, hg U₁⟩⟩
    have h := M.Z.germToFunctionField_injective (W ⊓ U₁)
      ((M.Z.presheaf.germ_res_apply (homOfLE inf_le_left) _ _ ψ).trans
        (hs.trans (M.Z.presheaf.germ_res_apply (homOfLE inf_le_right) _ _ f).symm))
    rw [_root_.GlobalTheory.ZH.RatModel.mem_O]
    refine ⟨W, ψ, hzW, ?_⟩
    have hne := M.nonempty_inf ⟨z, hzW⟩ hU₁
    have hv := congrArg (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valF M.pt _) h
    rwa [M.valF_resG _ hne,
      M.valF_resG _ hne] at hv

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAffineOpenRingOnEqAdjoinInv
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsRingHomOfMulPowMem
namespace GlobalTheory

theorem exists_mul_pow_mem_of_fg {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω]
    (A B : Subalgebra O Ω) (hA : A.FG)
    (hB : ∀ x : Ω, ∃ a ∈ B, ∃ b ∈ B, b ≠ 0 ∧ x * b = a) :
    ∃ d ∈ B, d ≠ 0 ∧ ∀ a ∈ A, ∃ n : ℕ, a * d ^ n ∈ B := by
  classical
  obtain ⟨s, hs⟩ := hA
  have hden : ∀ x : Ω, ∃ b ∈ B, b ≠ 0 ∧ x * b ∈ B := by
    intro x
    obtain ⟨a, ha, b, hb, hb0, hx⟩ := hB x
    exact ⟨b, hb, hb0, by rw [hx]; exact ha⟩
  choose den hdenB hden0 hdenmul using hden
  have hD : ∏ x ∈ s, den x ∈ B := Subalgebra.prod_mem B (fun x _ => hdenB x)
  refine ⟨∏ x ∈ s, den x, hD, Finset.prod_ne_zero_iff.mpr (fun x _ => hden0 x), ?_⟩
  intro a ha
  rw [← hs] at ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>

    refine ⟨1, ?_⟩
    rw [pow_one, ← Finset.mul_prod_erase s den (Finset.mem_coe.mp hx), ← mul_assoc]
    exact mul_mem (hdenmul x) (Subalgebra.prod_mem B (fun y _ => hdenB y))
  | algebraMap r =>
    exact ⟨0, by rw [pow_zero, mul_one]; exact B.algebraMap_mem r⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have e : (x + y) * (∏ z ∈ s, den z) ^ (n + m) =
        x * (∏ z ∈ s, den z) ^ n * (∏ z ∈ s, den z) ^ m +
          y * (∏ z ∈ s, den z) ^ m * (∏ z ∈ s, den z) ^ n := by ring
    rw [e]
    exact add_mem (mul_mem hn (pow_mem hD m)) (mul_mem hm (pow_mem hD n))
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have e : x * y * (∏ z ∈ s, den z) ^ (n + m) =
        (x * (∏ z ∈ s, den z) ^ n) * (y * (∏ z ∈ s, den z) ^ m) := by ring
    rw [e]
    exact mul_mem hn hm

end GlobalTheory
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

section

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_of_mul_pow_mem_of_inv_mem {S : Subalgebra o Ω} {d x : Ω} (hd : d ≠ 0) (hi : d⁻¹ ∈ S) {n : ℕ}
    (h : x * d ^ n ∈ S) : x ∈ S := by
  have := S.mul_mem h (S.pow_mem hi n)
  rwa [_root_.mul_assoc, ← mul_pow, mul_inv_cancel₀ hd, one_pow, _root_.mul_one] at this

theorem exists_mul_eq_of_eq_div {R : Subalgebra o Ω} (h : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) (x : Ω) :
    ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h x
  by_cases h0 : b = 0
  · exact ⟨0, R.zero_mem, 1, R.one_mem, one_ne_zero, by simp [h0]⟩
  · exact ⟨a, ha, b, hb, h0, div_mul_cancel₀ a h0⟩

theorem exists_adjoin_inv_eq (R B : Subalgebra o Ω) (A : Set Ω) (hR : R.FG) (hB : B.FG)
    (hRf : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a)
    (hBf : ∀ x : Ω, ∃ a ∈ B, ∃ b ∈ B, b ≠ 0 ∧ x * b = a) (hA : A.Finite) :
    ∃ a ∈ R, ∃ c ∈ B, a ≠ 0 ∧ c ≠ 0 ∧
      Algebra.adjoin o (insert c⁻¹ (B : Set Ω)) = Algebra.adjoin o (insert a⁻¹ (R : Set Ω)) ∧
      A ⊆ Algebra.adjoin o (insert a⁻¹ (R : Set Ω)) := by
  obtain ⟨d, hdR, hd0, hd⟩ := exists_mul_pow_mem_of_fg (B ⊔ Algebra.adjoin o A) R
    (hB.sup (Subalgebra.fg_def.2 ⟨_, hA, rfl⟩)) hRf
  obtain ⟨c, hcB, hc0, hc⟩ := exists_mul_pow_mem_of_fg (R ⊔ Algebra.adjoin o {d⁻¹}) B
    (hR.sup (Subalgebra.fg_def.2 ⟨_, Set.finite_singleton _, rfl⟩)) hBf
  obtain ⟨m, hm⟩ := hd c (le_sup_left (a := B) hcB)
  have ha0 : d * (c * d ^ m) ≠ 0 := mul_ne_zero hd0 (mul_ne_zero hc0 (pow_ne_zero _ hd0))
  set S := Algebra.adjoin o (insert (d * (c * d ^ m))⁻¹ (R : Set Ω)) with hS
  set S' := Algebra.adjoin o (insert c⁻¹ (B : Set Ω)) with hS'
  have hRS : ∀ x ∈ R, x ∈ S := fun x hx => Algebra.subset_adjoin (Set.mem_insert_of_mem _ hx)
  have haS : (d * (c * d ^ m))⁻¹ ∈ S := Algebra.subset_adjoin (Set.mem_insert _ _)
  have hdS : d⁻¹ ∈ S := by
    have := S.mul_mem haS (hRS _ hm)
    convert this using 1
    field_simp
  have hcS : c⁻¹ ∈ S := by
    have := S.mul_mem haS (hRS _ (R.mul_mem hdR (R.pow_mem hdR m)))
    convert this using 1
    field_simp
  have h1 : ∀ x ∈ B ⊔ Algebra.adjoin o A, x ∈ S := fun x hx => by
    obtain ⟨n, hn⟩ := hd x hx
    exact mem_of_mul_pow_mem_of_inv_mem hd0 hdS (hRS _ hn)
  have hcS' : c⁻¹ ∈ S' := Algebra.subset_adjoin (Set.mem_insert _ _)
  have h2 : ∀ x ∈ R ⊔ Algebra.adjoin o {d⁻¹}, x ∈ S' := fun x hx => by
    obtain ⟨n, hn⟩ := hc x hx
    exact mem_of_mul_pow_mem_of_inv_mem hc0 hcS' (Algebra.subset_adjoin (Set.mem_insert_of_mem _ hn))
  have hdS' : d⁻¹ ∈ S' := h2 _ (le_sup_right (a := R) (Algebra.subset_adjoin (Set.mem_singleton _)))
  refine ⟨_, R.mul_mem hdR hm, c, hcB, ha0, hc0, le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_le ?_),
    fun x hx => h1 x (le_sup_right (a := B) (Algebra.subset_adjoin hx))⟩
  · rintro x (rfl | hx)
    · exact hcS
    · exact h1 x (le_sup_left (a := B) hx)
  · rintro x (rfl | hx)
    · have := S'.mul_mem hdS' (S'.mul_mem hcS' (S'.pow_mem hdS' m))
      rwa [inv_pow, ← mul_inv, ← mul_inv] at this
    · exact h2 x (le_sup_left (a := R) hx)

namespace RatModel

variable {M : RatModel o Ω}

theorem fg_ringOn {V : M.Z.Opens} (hV : IsAffineOpen V) (hne : (V : Set M.Z).Nonempty) :
    (M.ringOn V).FG := by
  have := M.lft
  have h1 : (M.s.appLE ⊤ V le_top).hom.FiniteType := M.s.finiteType_appLE (isAffineOpen_top _) hV _
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of o)).symm.commRingCatIsoToRingEquiv.surjective
  have h3 : (M.sectionsEquiv V hne).toRingHom.FiniteType :=
    RingHom.FiniteType.of_surjective _ (M.sectionsEquiv V hne).surjective
  have h4 := h3.comp (h1.comp h2)
  have e : (M.sectionsEquiv V hne).toRingHom.comp ((M.s.appLE ⊤ V le_top).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom) = algebraMap o (M.ringOn V) :=
    RingHom.ext fun a => Subtype.ext ((coe_sectionsEquiv V hne _).trans (M.valF_constFn hne a))
  rw [e, RingHom.finiteType_algebraMap] at h4
  exact (Subalgebra.fg_iff_finiteType _).2 h4

theorem nonempty_basicOpen {V : M.Z.Opens} (hne : (V : Set M.Z).Nonempty) {g : Γ(M.Z, V)}
    (hg : valF M.pt V g ≠ 0) : ((M.Z.basicOpen g : M.Z.Opens) : Set M.Z).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro h
  apply hg
  rw [(basicOpen_eq_bot_iff g).1 (SetLike.coe_injective h), ← M.res_apply V hne, map_zero]

theorem ringOn_basicOpen {V : M.Z.Opens} (hV : IsAffineOpen V) (hne : (V : Set M.Z).Nonempty) {g : Γ(M.Z, V)}
    (hg0 : valF M.pt V g ≠ 0) :
    M.ringOn (M.Z.basicOpen g) = Algebra.adjoin o (insert (valF M.pt V g)⁻¹ (M.ringOn V : Set Ω)) := by
  have hg := nonempty_basicOpen hne hg0
  refine le_antisymm (fun x hx => ?_) (Algebra.adjoin_le ?_)
  · obtain ⟨f, rfl⟩ := (mem_ringOn_iff_exists hg).1 hx
    have := hV.isLocalization_basicOpen g
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g f
    have h1 := congrArg (M.res _ hg) ha
    have h2 : ∀ t : Γ(M.Z, V), M.res _ hg (algebraMap Γ(M.Z, V) Γ(M.Z, M.Z.basicOpen g) t) = M.res V hne t :=
      fun t => M.res_resG (M.Z.basicOpen_le g) hg t
    rw [map_mul, map_pow, h2, h2, res_apply, res_apply, res_apply] at h1
    refine mem_of_mul_pow_mem_of_inv_mem hg0 (Algebra.subset_adjoin (Set.mem_insert _ _)) (n := n) ?_
    rw [h1]
    exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ((mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩))
  · rintro x (rfl | hx)
    · exact mem_ringOn.2 fun z hz =>
        ((isUnit_O_iff _).1 ((isUnit_valF_iff (M.Z.basicOpen_le g hz) g).2 hz)).2
    · exact ringOn_anti (M.Z.basicOpen_le g) hx

end RatModel

end

theorem exists_affineOpen_ringOn_eq_adjoin_inv : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (R : Subalgebra o Ω) (A : Set Ω), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) → A.Finite → ∀ W : M.Z.Opens, (W : Set M.Z).Nonempty → ∃ (U₀ : M.Z.Opens) (a : Ω), U₀ ≤ W ∧ (U₀ : Set M.Z).Nonempty ∧ IsAffineOpen U₀ ∧ a ∈ R ∧ a ≠ 0 ∧ M.ringOn U₀ = Algebra.adjoin o (insert a⁻¹ (R : Set Ω)) ∧ A ⊆ M.ringOn U₀ := by
  intro o Ω _ _ _ M R A hR hRf hA W ⟨w, hw⟩
  obtain ⟨V, hV, hwV, hVW⟩ := exists_isAffineOpen_mem_and_subset (U := W) hw
  have hne : (V : Set M.Z).Nonempty := ⟨w, hwV⟩
  obtain ⟨a, ha, c, hc, ha0, hc0, he, hAS⟩ := exists_adjoin_inv_eq R (M.ringOn V) A hR
    (RatModel.fg_ringOn hV hne) (exists_mul_eq_of_eq_div hRf) (exists_mul_eq_of_eq_div fun x => by
      obtain ⟨a, b, -, h⟩ := RatModel.exists_eq_div hV hne x
      exact ⟨_, (RatModel.mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩, _,
        (RatModel.mem_ringOn_iff_exists hne).2 ⟨b, rfl⟩, h⟩) hA
  obtain ⟨g, rfl⟩ := (RatModel.mem_ringOn_iff_exists hne).1 hc
  have h := (RatModel.ringOn_basicOpen hV hne hc0).trans he
  exact ⟨M.Z.basicOpen g, a, (M.Z.basicOpen_le g).trans hVW, RatModel.nonempty_basicOpen hne hc0,
    hV.basicOpen g, ha, ha0, h, h ▸ hAS⟩

end GlobalTheory.ZH
end
