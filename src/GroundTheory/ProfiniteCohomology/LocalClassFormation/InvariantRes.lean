module

public import GroundTheory.ProfiniteCohomology.LocalClassFormation.OrderInfRes
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.OrderScalars
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.Unramified
public import GroundTheory.ProfiniteCohomology.GaloisCohomology.BrauerInflation
public import GroundTheory.LocalFields.SeparableClosure
public import GroundTheory.LocalFields.MaximalUnramified
public import GroundTheory.ProfiniteCohomology.EulerChar
public import GroundTheory.Brauer.Degree

@[expose] public section

section -- merged from GroundTheory.Brauer.BaseChangeRestriction
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Brauer

open CategoryTheory groupCohomology GroundTheory.ProfCoh

universe u

section Cocycles

variable {k : Type u} [CommRing k] {H : Type u} [Group H] [TopologicalSpace H]
  [IsTopologicalGroup H] {B : Rep.{u} k H} [IsDiscreteRep B]

end Cocycles

section Topology

variable {K Ks : Type u} [Field K] [Field Ks] [Algebra K Ks]

end Topology

section Main

variable {K Ks : Type u} [Field K] [Field Ks] [Algebra K Ks] [IsSepClosure K Ks]

instance isSepClosure_intermediateField (E : IntermediateField K Ks) : IsSepClosure E Ks :=
  ⟨IsSepClosure.sep_closed K, Algebra.isSeparable_tower_top_of_isSeparable K E Ks⟩

variable (E : IntermediateField K Ks)

end Main

end GroundTheory.Brauer
end
end

section -- merged from GroundTheory.ProfiniteCohomology.LocalClassFormation.InvariantSplit
section -- merged from GroundTheory.ProfiniteCohomology.LocalClassFormation.InvariantLevels
section -- merged from GroundTheory.ProfiniteCohomology.LocalClassFormation.InvariantDefs
section -- merged from GroundTheory.ProfiniteCohomology.LocalClassFormation.FinrankLeNatCardGroupCohomologyTwoGalUnits
section -- merged from GroundTheory.ProfiniteCohomology.LocalClassFormation.UnramifiedRes
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory GroundTheory.LocalField ValuativeRel

instance valuativeExtension_self (F : Type*) [Field F] [ValuativeRel F] : ValuativeExtension F F :=
  ⟨fun {_ _} => Iff.rfl⟩

section Tower

variable (K K' L L' : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  [IsUnramified K L] [Field K'] [Field L'] [Algebra K K'] [Algebra K L'] [Algebra K' L']
  [Algebra L L'] [IsScalarTower K K' L'] [IsScalarTower K L L']

noncomputable def galRestrict : Gal(L'/K') →* Gal(L/K) :=
  haveI : IsGalois K L := isGalois_of_unramified K L IsUnramified.ramificationIndex_eq_one
  (AlgEquiv.restrictNormalHom L).comp
    { toFun := fun σ : Gal(L'/K') => AlgEquiv.restrictScalars K σ
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem algebraMap_galRestrict_apply (σ : Gal(L'/K')) (x : L) :
    algebraMap L L' (galRestrict K K' L L' σ x) = σ (algebraMap L L' x) := by
  have : IsGalois K L := isGalois_of_unramified K L IsUnramified.ramificationIndex_eq_one
  exact AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalars K σ) L x

noncomputable def unitsResHom :
    Rep.res (galRestrict K K' L L') (galUnitsZ K L) ⟶ galUnitsZ K' L' :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (Units.map (algebraMap L L' : L →* L'))).toIntLinearMap,
    fun σ => by
      ext x
      exact algebraMap_galRestrict_apply K K' L L' σ _⟩

noncomputable abbrev unitsResH2 :
    groupCohomology (galUnitsZ K L) 2 ⟶ groupCohomology (galUnitsZ K' L') 2 :=
  groupCohomology.map (galRestrict K K' L L') (unitsResHom K K' L L') 2

variable [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K'] [ValuativeRel L']
  [TopologicalSpace L'] [IsNonarchimedeanLocalField L'] [ValuativeExtension K K']
  [ValuativeExtension K' L'] [ValuativeExtension L L'] [FiniteDimensional K K']
  [FiniteDimensional K' L'] [IsUnramified K' L']


omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [FiniteDimensional K L] in
theorem ramificationIndex_right_eq :
    (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L'))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) = (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation K'))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) := by
  have : ValuativeExtension K L' := valuativeExtension_trans K K' L'
  have : FiniteDimensional K L' := FiniteDimensional.trans K K' L'
  have : FiniteDimensional L L' := FiniteDimensional.right K L L'
  have h1 := ramificationIndex_tower K L L'
  have h2 := ramificationIndex_tower K K' L'
  have hKL : ramificationIndex K L = 1 := IsUnramified.ramificationIndex_eq_one
  have hK'L' : ramificationIndex K' L' = 1 := IsUnramified.ramificationIndex_eq_one
  rw [hKL, one_mul] at h1
  rw [hK'L', mul_one] at h2
  exact h1.symm.trans h2

theorem card_residueField_eq_pow : Nat.card 𝓀[K'] = Nat.card 𝓀[K] ^ ((IsLocalRing.maximalIdeal 𝒪[K']).inertiaDeg (𝒪[K])) := by
  let := Fintype.ofFinite 𝓀[K]
  let := Fintype.ofFinite 𝓀[K']
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := 𝓀[K]) (V := 𝓀[K']), residueDegree_eq_finrank]

theorem galRestrict_frob : galRestrict K K' L L' (frob K' L') = frob K L ^ ((IsLocalRing.maximalIdeal 𝒪[K']).inertiaDeg (𝒪[K])) := by
  have he := IsUnramified.ramificationIndex_eq_one (K := K) (L := L)
  apply residueAlgEquiv_injective_of_unramified K L he
  ext y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  have hpow : ∀ n : ℕ, residueAlgEquiv K L (frob K L ^ n) (IsLocalRing.residue 𝒪[L] x) =
      IsLocalRing.residue 𝒪[L] x ^ (Nat.card 𝓀[K] ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', map_mul, AlgEquiv.mul_apply, ih, map_pow, residueAlgEquiv_frobenius_apply,
        ← pow_mul, pow_succ, mul_comm]
  rw [hpow, ← card_residueField_eq_pow K K', residueAlgEquiv_residue]
  apply (algebraMap 𝓀[L] 𝓀[L']).injective
  rw [map_pow, IsLocalRing.ResidueField.algebraMap_residue,
    IsLocalRing.ResidueField.algebraMap_residue]
  have hx : algebraMap 𝒪[L] 𝒪[L'] (integerAlgEquiv K L (galRestrict K K' L L' (frob K' L')) x) =
      integerAlgEquiv K' L' (frob K' L') (algebraMap 𝒪[L] 𝒪[L'] x) :=
    Subtype.ext (algebraMap_galRestrict_apply K K' L L' _ _)
  rw [hx, residue_frobenius_apply]

theorem unitsResH2_comp_h2Valuation :
    unitsResH2 K K' L L' ≫ h2Valuation K' L' =
      h2Valuation K L ≫ groupCohomology.map (galRestrict K K' L L')
        (intMulRes (galRestrict K K' L L') ((_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation K'))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))))) 2 := by
  have : FiniteDimensional K L' := FiniteDimensional.trans K K' L'
  have : FiniteDimensional L L' := FiniteDimensional.right K L L'
  simp only [h2Valuation, groupCohomology.functor_map]
  rw [← groupCohomology.map_comp, ← groupCohomology.map_comp]
  refine groupCohomology.map_congr (by ext; rfl) (LinearMap.ext fun x => ?_) 2
  change ord (algebraMap L L' ((Additive.toMul x : Lˣ) : L)) =
    ((_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation K'))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) : ℤ) * ord ((Additive.toMul x : Lˣ) : L)
  rw [ord_algebraMap, ramificationIndex_right_eq K K' L L']

theorem unramifiedInv_unitsResH2 (x : groupCohomology (galUnitsZ K L) 2) :
    unramifiedInv K' L' ((unitsResH2 K K' L L').hom x) =
      Module.finrank K K' • unramifiedInv K L x := by
  have hsq := congrArg (fun h => h.hom x) (unitsResH2_comp_h2Valuation K K' L L')
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hsq
  rw [unramifiedInv_apply, hsq, h2IntAddEquiv_map_intMulRes, unramifiedInv_apply,
    AddMonoidHom.smul_apply, AddMonoidHom.comp_apply, MonoidHom.toAdditive_apply_apply,
    toMul_ofMul, galRestrict_frob, ofMul_pow, map_nsmul, map_zsmul, map_nsmul,
    ← ramificationIndex_mul_residueDegree K K', mul_nsmul', natCast_zsmul]

end Tower

section Inflation

variable (K L L' : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Field L'] [ValuativeRel L'] [TopologicalSpace L']
  [IsNonarchimedeanLocalField L'] [Algebra K L] [Algebra K L'] [Algebra L L']
  [IsScalarTower K L L'] [ValuativeExtension K L] [ValuativeExtension K L']
  [ValuativeExtension L L'] [FiniteDimensional K L] [FiniteDimensional K L'] [IsUnramified K L]
  [IsUnramified K L']

theorem unramifiedInv_inflation (x : groupCohomology (galUnitsZ K L) 2) :
    unramifiedInv K L' ((unitsResH2 K K L L').hom x) = unramifiedInv K L x := by
  rw [unramifiedInv_unitsResH2, Module.finrank_self, one_smul]

end Inflation

end GroundTheory.ProfCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory CategoryTheory.Limits groupCohomology GroundTheory.LocalField ValuativeRel
  IntermediateField

section Compare

variable (K K' L L' : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  [IsUnramified K L] [Field K'] [Field L'] [Algebra K K'] [Algebra K L'] [Algebra K' L']
  [Algebra L L'] [IsScalarTower K K' L'] [IsScalarTower K L L'] [Normal K L]

theorem h2GalUnitsAddEquiv_unitsRes_unitsInfl (y : groupCohomology (galUnits K L) 2) :
    h2GalUnitsAddEquiv K' L' ((unitsInfl K L L' 2 ≫ unitsRes K K' L' 2).hom y) =
      (unitsResH2 K K' L L').hom (h2GalUnitsAddEquiv K L y) := by
  refine H2_induction_on y fun c => ?_
  rw [h2GalUnitsAddEquiv_H2_class, unitsInfl, unitsRes, ← groupCohomology.map_comp]
  have h1 := congrArg (fun h => ModuleCat.Hom.hom h c) (groupCohomology.H2π_comp_map
    ((AlgEquiv.restrictNormalHom (F := K) (K₁ := L') L).comp (galRestrictScalars K K' L'))
    ((Rep.resFunctor (galRestrictScalars K K' L')).map (unitsInclHom K L L') ≫
      unitsResScalarsHom K K' L'))
  have h2 := congrArg (fun h => ModuleCat.Hom.hom h (cocycles₂IntRepAddEquiv (galUnitsHom K L) c))
    (groupCohomology.H2π_comp_map (galRestrict K K' L L') (unitsResHom K K' L L'))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
  rw [h1, h2, h2GalUnitsAddEquiv_H2_class]
  rfl

variable [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K'] [ValuativeRel L']
  [TopologicalSpace L'] [IsNonarchimedeanLocalField L'] [ValuativeExtension K K']
  [ValuativeExtension K' L'] [ValuativeExtension L L'] [FiniteDimensional K K']
  [FiniteDimensional K' L'] [IsUnramified K' L']

theorem unitsInfl_comp_unitsRes_eq_zero (h : Module.finrank K L ∣ Module.finrank K K') :
    unitsInfl K L L' 2 ≫ unitsRes K K' L' 2 = 0 := by
  ext y
  apply (h2GalUnitsAddEquiv K' L').injective
  rw [h2GalUnitsAddEquiv_unitsRes_unitsInfl, ModuleCat.hom_zero, LinearMap.zero_apply, map_zero]
  apply unramifiedInv_injective K' L'
  rw [unramifiedInv_unitsResH2, map_zero]
  obtain ⟨m, hm⟩ := h
  have hz := (mem_range_unramifiedInv_iff K L (unramifiedInv K L (h2GalUnitsAddEquiv K L y))).1
    ⟨_, rfl⟩
  rw [hm, mul_comm, mul_nsmul, smul_comm, hz, nsmul_zero]

end Compare

section Main

variable {K L : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]

theorem finrank_le_natCard_groupCohomology_two_galUnits :
    Module.finrank K L ≤ Nat.card (groupCohomology (galUnits K L) 2) := by
  classical
  set n := Module.finrank K L with hn_def
  have hn : n ≠ 0 := Module.finrank_pos.ne'

  set q := Nat.card 𝓀[K] with hq_def
  set f := Module.finrank 𝓀[K] 𝓀[L] with hf_def
  have hQ : Nat.card 𝓀[L] = q ^ f := by
    have := Fintype.ofFinite 𝓀[K]
    have := Fintype.ofFinite 𝓀[L]
    rw [hq_def, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Module.card_eq_pow_finrank (K := 𝓀[K]) (V := 𝓀[L])]
  have hf : f ≠ 0 := by
    have := ramificationIndex_mul_residueDegree K L
    rw [residueDegree_eq_finrank] at this
    exact right_ne_zero_of_mul (this.trans_ne hn)
  have hq : 1 < q := Finite.one_lt_card

  let Ω := AlgebraicClosure L
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_card_pow_sub_one (K := L) (Ksep := Ω) hn
  rw [hQ, ← pow_mul] at hζ

  let L0 : IntermediateField K Ω := (IsScalarTower.toAlgHom K L Ω).fieldRange
  let eL : L ≃ₐ[K] L0 := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K L Ω)
  have : IsGalois K L0 := IsGalois.of_algEquiv eL
  have : FiniteDimensional K L0 := LinearEquiv.finiteDimensional eL.toLinearEquiv
  obtain ⟨hKζ, -, hKζgal, -⟩ :=
    isUnramifiedSubextension_adjoin_spec (K := K) (Ksep := Ω) (mul_ne_zero hf hn) hζ
  have := hKζgal
  have : FiniteDimensional K K⟮ζ⟯ := hKζ.1
  let M0 : IntermediateField K Ω := L0 ⊔ K⟮ζ⟯
  let φL : L →ₐ[K] M0 := (IsScalarTower.toAlgHom K L Ω).codRestrict M0.toSubalgebra
    fun x => (le_sup_left : L0 ≤ M0) ⟨x, rfl⟩
  let : Algebra L M0 := φL.toRingHom.toAlgebra
  have : IsScalarTower K L M0 := IsScalarTower.of_algebraMap_eq fun x => (φL.commutes x).symm
  have : FiniteDimensional L M0 := Module.Finite.of_restrictScalars_finite K L M0
  let := (finiteExtensionStructure L M0).rel
  let := (finiteExtensionStructure L M0).top
  have : IsNonarchimedeanLocalField M0 := finiteExtensionStructure_isNonarchimedeanLocalField L M0
  have : ValuativeExtension L M0 := finiteExtensionStructure_valuativeExtension L M0
  have : ValuativeExtension K M0 := valuativeExtension_trans K L M0
  let ζM : M0 := ⟨ζ, (le_sup_right : K⟮ζ⟯ ≤ M0) (mem_adjoin_simple_self K ζ)⟩
  have hζM : IsPrimitiveRoot ζM (q ^ (f * n) - 1) :=
    (IsPrimitiveRoot.map_iff_of_injective (f := M0.val) M0.val.injective).1 hζ

  have hF := isUnramifiedSubextension_adjoin (K := L) (Ksep := M0) hn
    (show IsPrimitiveRoot ζM (Nat.card 𝓀[L] ^ n - 1) by rw [hQ, ← pow_mul]; exact hζM)
  have htop : L⟮ζM⟯ = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    have hle : M0 ≤ ((L⟮ζM⟯).restrictScalars K).map M0.val := by
      refine sup_le ?_ ?_
      · rintro _ ⟨y, rfl⟩
        exact ⟨algebraMap L M0 y, (L⟮ζM⟯).algebraMap_mem y, rfl⟩
      · rw [adjoin_simple_le_iff]
        exact ⟨ζM, mem_adjoin_simple_self L ζM, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hle x.2
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  have : IsUnramified L M0 := by
    have h1 : IsUnramified L L⟮ζM⟯ := (isUnramified_iff _ _).2 hF.1.ramificationIndex_eq_one
    set_option synthInstance.maxHeartbeats 200000 in
    have hfr : Module.finrank L⟮ζM⟯ M0 = 1 := by
      have h := Module.finrank_mul_finrank L L⟮ζM⟯ M0
      have h' : Module.finrank L L⟮ζM⟯ = Module.finrank L M0 := by
        rw [htop]
        exact IntermediateField.finrank_top'
      rw [h'] at h
      exact (Nat.mul_eq_left Module.finrank_pos.ne').1 h
    have h2 : IsUnramified L⟮ζM⟯ M0 := by
      rw [isUnramified_iff]
      have := ramificationIndex_mul_residueDegree L⟮ζM⟯ M0
      rw [hfr] at this
      exact Nat.eq_one_of_mul_eq_one_right this
    exact (isUnramified_tower_iff L L⟮ζM⟯ M0).2 ⟨h1, h2⟩

  have hdvd : q ^ n - 1 ∣ q ^ (f * n) - 1 := by
    have := Nat.sub_dvd_pow_sub_pow (q ^ n) 1 f
    rwa [one_pow, ← pow_mul, mul_comm] at this
  have hpos : 0 < q ^ n - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hn hq)
  set k := (q ^ (f * n) - 1) / (q ^ n - 1) with hk_def
  have hk0 : k ≠ 0 := (Nat.div_pos (Nat.le_of_dvd
    (Nat.sub_pos_of_lt (Nat.one_lt_pow (mul_ne_zero hf hn) hq)) hdvd) hpos).ne'
  have hkdvd : k ∣ q ^ (f * n) - 1 := Nat.div_dvd_of_dvd hdvd
  have hζk : IsPrimitiveRoot (ζM ^ k) (q ^ n - 1) := by
    have := hζM.pow_of_dvd hk0 hkdvd
    rwa [hk_def, Nat.div_div_self hdvd
      (Nat.sub_pos_of_lt (Nat.one_lt_pow (mul_ne_zero hf hn) hq)).ne'] at this
  obtain ⟨hE, hEn, hEgal, hEcyc, -⟩ :=
    isUnramifiedSubextension_adjoin_spec (K := K) (Ksep := M0) hn hζk
  have := hEgal
  have := hEcyc
  have : FiniteDimensional K K⟮ζM ^ k⟯ := hE.1
  have : IsUnramified K K⟮ζM ^ k⟯ := (isUnramified_iff _ _).2 hE.ramificationIndex_eq_one

  have hvanish := unitsInfl_comp_unitsRes_eq_zero K L K⟮ζM ^ k⟯ M0 (by rw [hEn])
  have := finite_groupCohomology_two_galUnits (K := K) (L := L)
  have hle := natCard_le_of_unitsInfl_comp_unitsRes_eq_zero K K⟮ζM ^ k⟯ L M0 hvanish
  rw [natCard_groupCohomology_two_galUnits_of_isCyclic, hEn] at hle
  exact hle

theorem natCard_groupCohomology_two_galUnits :
    Nat.card (groupCohomology (galUnits K L) 2) = Module.finrank K L :=
  le_antisymm (Nat.le_of_dvd Module.finrank_pos natCard_groupCohomology_two_galUnits_dvd)
    finrank_le_natCard_groupCohomology_two_galUnits

end Main

end GroundTheory.ProfCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IntermediateField GroundTheory.LocalField ValuativeRel

variable (F Ω : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field Ω] [Algebra F Ω] [IsSepClosure F Ω]

section Root

noncomputable def unramifiedRoot (n : ℕ+) : Ω :=
  haveI := IsSepClosure.sep_closed F (K := Ω)
  (exists_isPrimitiveRoot_card_pow_sub_one (K := F) (Ksep := Ω) n.ne_zero).choose

theorem isPrimitiveRoot_unramifiedRoot (n : ℕ+) :
    IsPrimitiveRoot (unramifiedRoot F Ω n) (Nat.card 𝓀[F] ^ (n : ℕ) - 1) :=
  haveI := IsSepClosure.sep_closed F (K := Ω)
  (exists_isPrimitiveRoot_card_pow_sub_one (K := F) (Ksep := Ω) n.ne_zero).choose_spec

noncomputable def unramifiedLevel (n : ℕ+) : IntermediateField F Ω :=
  F⟮unramifiedRoot F Ω n⟯

theorem unramifiedLevel_eq (n : ℕ+) : unramifiedLevel F Ω n = F⟮unramifiedRoot F Ω n⟯ :=
  rfl

theorem isUnramifiedSubextension_unramifiedLevel (n : ℕ+) :
    IsUnramifiedSubextension (unramifiedLevel F Ω n) :=
  (isUnramifiedSubextension_adjoin n.ne_zero (isPrimitiveRoot_unramifiedRoot F Ω n)).1

theorem finrank_unramifiedLevel (n : ℕ+) : Module.finrank F (unramifiedLevel F Ω n) = n :=
  (isUnramifiedSubextension_adjoin n.ne_zero (isPrimitiveRoot_unramifiedRoot F Ω n)).2

instance finiteDimensional_unramifiedLevel (n : ℕ+) :
    FiniteDimensional F (unramifiedLevel F Ω n) :=
  (isUnramifiedSubextension_unramifiedLevel F Ω n).1

instance isGalois_unramifiedLevel (n : ℕ+) : IsGalois F (unramifiedLevel F Ω n) :=
  IsUnramifiedSubextension.isGalois (isUnramifiedSubextension_unramifiedLevel F Ω n)

theorem unramifiedLevel_le {m n : ℕ+} (h : (m : ℕ) ∣ n) :
    unramifiedLevel F Ω m ≤ unramifiedLevel F Ω n :=
  haveI := IsSepClosure.sep_closed F (K := Ω)
  IsUnramifiedSubextension.le_adjoin (isUnramifiedSubextension_unramifiedLevel F Ω m) n.ne_zero
    ((finrank_unramifiedLevel F Ω m).symm ▸ h) (isPrimitiveRoot_unramifiedRoot F Ω n)

end Root

section Structure

variable [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension F Ω]

instance isUnramified_unramifiedLevel (n : ℕ+) : IsUnramified F (unramifiedLevel F Ω n) :=
  ⟨IsUnramifiedSubextension.ramificationIndex_eq_one (isUnramifiedSubextension_unramifiedLevel F Ω n)⟩

noncomputable def unramifiedLevelInv (n : ℕ+) :
    groupCohomology (galUnits F (unramifiedLevel F Ω n)) 2 →+ QZ :=
  (unramifiedInv F (unramifiedLevel F Ω n)).comp
    (h2GalUnitsAddEquiv F (unramifiedLevel F Ω n)).toAddMonoidHom

theorem unramifiedLevelInv_apply (n : ℕ+) (y : groupCohomology (galUnits F (unramifiedLevel F Ω n)) 2) :
    unramifiedLevelInv F Ω n y =
      unramifiedInv F (unramifiedLevel F Ω n) (h2GalUnitsAddEquiv F (unramifiedLevel F Ω n) y) :=
  rfl

noncomputable def brauerInvFun (x : galoisBrauerGroup F Ω) : QZ :=
  open Classical in
  if h : ∃ (n : ℕ+) (y : groupCohomology (galUnits F (unramifiedLevel F Ω n)) 2),
      (brauerInflation (unramifiedLevel F Ω n)).hom y = x then
    unramifiedLevelInv F Ω h.choose h.choose_spec.choose
  else 0

end Structure

end GroundTheory.ProfCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IntermediateField GroundTheory.LocalField ValuativeRel

section Self

variable (K M : Type) [Field K] [Field M] [Algebra K M]

theorem unitsRes_self (n : ℕ) : unitsRes K K M n = 𝟙 _ := by
  rw [unitsRes, ← groupCohomology.map_id]
  exact groupCohomology.map_congr (by ext; rfl) rfl n

end Self

variable (F Ω : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field Ω] [Algebra F Ω] [IsSepClosure F Ω]
  [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension F Ω]

theorem unramifiedLevelInv_unitsInflationOfLE {m n : ℕ+} (h : (m : ℕ) ∣ n)
    (y : groupCohomology (galUnits F (unramifiedLevel F Ω m)) 2) :
    unramifiedLevelInv F Ω n ((unitsInflationOfLE (unramifiedLevel_le F Ω h) 2).hom y) =
      unramifiedLevelInv F Ω m y := by
  let _ : Algebra (unramifiedLevel F Ω m) (unramifiedLevel F Ω n) :=
    (IntermediateField.inclusion (unramifiedLevel_le F Ω h)).toRingHom.toAlgebra
  have : IsScalarTower F (unramifiedLevel F Ω m) (unramifiedLevel F Ω n) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : ValuativeExtension (unramifiedLevel F Ω m) (unramifiedLevel F Ω n) :=
    IntermediateField.valuativeExtension_inclusion _
  have key : unitsInflationOfLE (unramifiedLevel_le F Ω h) 2 =
      unitsInfl F (unramifiedLevel F Ω m) (unramifiedLevel F Ω n) 2 ≫
        unitsRes F F (unramifiedLevel F Ω n) 2 := by
    rw [unitsRes_self, Category.comp_id]
    rfl
  rw [unramifiedLevelInv_apply, unramifiedLevelInv_apply, key,
    h2GalUnitsAddEquiv_unitsRes_unitsInfl, unramifiedInv_inflation]

theorem unramifiedLevelInv_eq_of_brauerInflation_eq {m n : ℕ+}
    {y : groupCohomology (galUnits F (unramifiedLevel F Ω m)) 2}
    {z : groupCohomology (galUnits F (unramifiedLevel F Ω n)) 2}
    (h : (brauerInflation (unramifiedLevel F Ω m)).hom y =
      (brauerInflation (unramifiedLevel F Ω n)).hom z) :
    unramifiedLevelInv F Ω m y = unramifiedLevelInv F Ω n z := by
  have hm : ((m : ℕ)) ∣ ((m * n : ℕ+) : ℕ) := ⟨n, by simp⟩
  have hn : ((n : ℕ)) ∣ ((m * n : ℕ+) : ℕ) := ⟨m, by simp [mul_comm]⟩
  have hinj := brauerInflation_injective (L := Ω) (unramifiedLevel F Ω (m * n))
  have heq : (unitsInflationOfLE (unramifiedLevel_le F Ω hm) 2).hom y =
      (unitsInflationOfLE (unramifiedLevel_le F Ω hn) 2).hom z := by
    apply hinj
    have e1 := congrArg (fun φ => φ.hom y)
      (unitsInflationOfLE_comp_unitsInflation (L := Ω) (unramifiedLevel_le F Ω hm) 2)
    have e2 := congrArg (fun φ => φ.hom z)
      (unitsInflationOfLE_comp_unitsInflation (L := Ω) (unramifiedLevel_le F Ω hn) 2)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e1 e2
    rw [e1, e2]
    exact h
  rw [← unramifiedLevelInv_unitsInflationOfLE F Ω hm y, heq,
    unramifiedLevelInv_unitsInflationOfLE F Ω hn z]

theorem brauerInvFun_brauerInflation (n : ℕ+)
    (y : groupCohomology (galUnits F (unramifiedLevel F Ω n)) 2) :
    brauerInvFun F Ω ((brauerInflation (unramifiedLevel F Ω n)).hom y) =
      unramifiedLevelInv F Ω n y := by
  have hex : ∃ (m : ℕ+) (z : groupCohomology (galUnits F (unramifiedLevel F Ω m)) 2),
      (brauerInflation (unramifiedLevel F Ω m)).hom z =
        (brauerInflation (unramifiedLevel F Ω n)).hom y := ⟨n, y, rfl⟩
  rw [brauerInvFun, dite_eq_left hex]
  exact unramifiedLevelInv_eq_of_brauerInflation_eq F Ω hex.choose_spec.choose_spec

end GroundTheory.ProfCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IntermediateField GroundTheory.LocalField ValuativeRel

variable (F Ω : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field Ω] [Algebra F Ω] [IsSepClosure F Ω]
  [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension F Ω]


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension F Ω] in
theorem brauerInflation_unitsInflationOfLE {E E' : IntermediateField F Ω} (h : E ≤ E')
    [FiniteDimensional F E] [Normal F E] [FiniteDimensional F E'] [Normal F E']
    (y : groupCohomology (galUnits F E) 2) :
    (brauerInflation E').hom ((unitsInflationOfLE h 2).hom y) = (brauerInflation E).hom y := by
  have e := congrArg (fun φ => φ.hom y) (unitsInflationOfLE_comp_unitsInflation (L := Ω) h 2)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using e

theorem exists_unramifiedLevel_brauerInflation_eq (E : IntermediateField F Ω) [FiniteDimensional F E]
    [IsGalois F E] (N : ℕ+) (hEN : Module.finrank F E = N) (y : groupCohomology (galUnits F E) 2) :
    ∃ z : groupCohomology (galUnits F (unramifiedLevel F Ω N)) 2,
      (brauerInflation (unramifiedLevel F Ω N)).hom z = (brauerInflation E).hom y := by
  classical
  set n := Module.finrank F E with hn_def
  have hn : n ≠ 0 := Module.finrank_pos.ne'
  have hNn : (N : ℕ) = n := hEN.symm

  set q := Nat.card 𝓀[F] with hq_def
  set f := Module.finrank 𝓀[F] 𝓀[E] with hf_def
  have hQ : Nat.card 𝓀[E] = q ^ f := by
    have := Fintype.ofFinite 𝓀[F]
    have := Fintype.ofFinite 𝓀[E]
    rw [hq_def, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Module.card_eq_pow_finrank (K := 𝓀[F]) (V := 𝓀[E])]
  have hf : f ≠ 0 := by
    have := ramificationIndex_mul_residueDegree F E
    rw [residueDegree_eq_finrank] at this
    exact right_ne_zero_of_mul (this.trans_ne hn)

  have := IsSepClosure.sep_closed F (K := Ω)
  obtain ⟨ζ, hζE⟩ := exists_isPrimitiveRoot_card_pow_sub_one (K := E) (Ksep := Ω) hn
  have hζ : IsPrimitiveRoot ζ (q ^ (f * n) - 1) := by rwa [hQ, ← pow_mul] at hζE
  have hKζ := (isUnramifiedSubextension_adjoin (K := F) (Ksep := Ω) (mul_ne_zero hf hn) hζ).1
  have : FiniteDimensional F F⟮ζ⟯ := hKζ.1
  have : IsGalois F F⟮ζ⟯ := IsUnramifiedSubextension.isGalois hKζ
  set M : IntermediateField F Ω := E ⊔ F⟮ζ⟯ with hM_def
  have hEM : E ≤ M := le_sup_left
  let _ : Algebra E M := (IntermediateField.inclusion hEM).toRingHom.toAlgebra
  have : IsScalarTower F E M := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional E M := Module.Finite.of_restrictScalars_finite F E M
  have : ValuativeExtension E M := IntermediateField.valuativeExtension_inclusion hEM

  let ζM : M := ⟨ζ, (le_sup_right : F⟮ζ⟯ ≤ M) (mem_adjoin_simple_self F ζ)⟩
  have hζM : IsPrimitiveRoot ζM (Nat.card 𝓀[E] ^ n - 1) :=
    (IsPrimitiveRoot.map_iff_of_injective (f := M.val) M.val.injective).1 hζE
  have htop : E⟮ζM⟯ = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    have hle : M ≤ ((E⟮ζM⟯).restrictScalars F).map M.val := by
      refine sup_le ?_ ?_
      · intro y hy
        exact ⟨algebraMap E M ⟨y, hy⟩, (E⟮ζM⟯).algebraMap_mem _, rfl⟩
      · rw [adjoin_simple_le_iff]
        exact ⟨ζM, mem_adjoin_simple_self E ζM, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hle x.2
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  have : IsUnramified E M :=
    ⟨ramificationIndex_eq_one_of_adjoin_eq_top hζM (natCast_card_pow_sub_one_ne_zero (K := E) hn)
      htop⟩

  have hNM : unramifiedLevel F Ω N ≤ M :=
    (IsUnramifiedSubextension.le_adjoin (isUnramifiedSubextension_unramifiedLevel F Ω N)
      (mul_ne_zero hf hn) (by rw [finrank_unramifiedLevel, hNn]; exact dvd_mul_left n f) hζ).trans
      le_sup_right
  let _ : Algebra (unramifiedLevel F Ω N) M := (IntermediateField.inclusion hNM).toRingHom.toAlgebra
  have : IsScalarTower F (unramifiedLevel F Ω N) M := IsScalarTower.of_algebraMap_eq' rfl
  have : ValuativeExtension (unramifiedLevel F Ω N) M :=
    IntermediateField.valuativeExtension_inclusion hNM

  have hvanish := unitsInfl_comp_unitsRes_eq_zero F E (unramifiedLevel F Ω N) M
    (by rw [finrank_unramifiedLevel, hNn])

  have hAB : LinearMap.range (unitsInfl F (unramifiedLevel F Ω N) M 2).hom ≤
      LinearMap.range (unitsInfl F E M 2).hom := by
    rintro _ ⟨w, rfl⟩
    rw [range_unitsInfl_two_eq_ker_unitsRes F E M, LinearMap.mem_ker]
    exact congrArg (fun φ => φ.hom w) hvanish
  have hcardA : Nat.card (LinearMap.range (unitsInfl F (unramifiedLevel F Ω N) M 2).hom) = n := by
    rw [← Nat.card_congr (LinearEquiv.ofInjective _
      (unitsInfl_two_injective F (unramifiedLevel F Ω N) M)).toEquiv,
      natCard_groupCohomology_two_galUnits, finrank_unramifiedLevel, hNn]
  have hcardB : Nat.card (LinearMap.range (unitsInfl F E M 2).hom) = n := by
    rw [← Nat.card_congr (LinearEquiv.ofInjective _ (unitsInfl_two_injective F E M)).toEquiv,
      natCard_groupCohomology_two_galUnits]
  have : Finite (LinearMap.range (unitsInfl F E M 2).hom) :=
    Nat.finite_of_card_ne_zero (hcardB.trans_ne hn)
  have hBA : LinearMap.range (unitsInfl F E M 2).hom ≤
      LinearMap.range (unitsInfl F (unramifiedLevel F Ω N) M 2).hom := by
    have : Finite (LinearMap.range (unitsInfl F E M 2).hom).toAddSubgroup := this
    have h := AddSubgroup.eq_of_le_of_card_ge (H := (LinearMap.range
      (unitsInfl F (unramifiedLevel F Ω N) M 2).hom).toAddSubgroup)
      (K := (LinearMap.range (unitsInfl F E M 2).hom).toAddSubgroup) hAB
      (by
        change Nat.card (LinearMap.range (unitsInfl F E M 2).hom) ≤
          Nat.card (LinearMap.range (unitsInfl F (unramifiedLevel F Ω N) M 2).hom)
        rw [hcardA, hcardB])
    intro v hv
    have hv' : v ∈ (LinearMap.range (unitsInfl F E M 2).hom).toAddSubgroup := hv
    rw [← h] at hv'
    exact hv'
  obtain ⟨z, hz⟩ := hBA ⟨y, rfl⟩
  refine ⟨z, ?_⟩
  rw [← brauerInflation_unitsInflationOfLE F Ω hNM, ← brauerInflation_unitsInflationOfLE F Ω hEM]
  exact congrArg (brauerInflation M).hom hz

theorem exists_brauerInflation_unramifiedLevel (x : galoisBrauerGroup F Ω) :
    ∃ (n : ℕ+) (y : groupCohomology (galUnits F (unramifiedLevel F Ω n)) 2),
      (brauerInflation (unramifiedLevel F Ω n)).hom y = x := by
  obtain ⟨E, y, rfl⟩ := exists_brauerInflation_eq x
  obtain ⟨z, hz⟩ := exists_unramifiedLevel_brauerInflation_eq F Ω E.toIntermediateField
    ⟨Module.finrank F E.toIntermediateField, Module.finrank_pos⟩ rfl y
  exact ⟨_, z, hz⟩

noncomputable def brauerInv : galoisBrauerGroup F Ω →+ QZ where
  toFun := brauerInvFun F Ω
  map_zero' := by
    have h := brauerInvFun_brauerInflation F Ω 1 0
    rwa [map_zero, map_zero] at h
  map_add' x₁ x₂ := by
    obtain ⟨m, y, rfl⟩ := exists_brauerInflation_unramifiedLevel F Ω x₁
    obtain ⟨n, z, rfl⟩ := exists_brauerInflation_unramifiedLevel F Ω x₂
    have hm : (m : ℕ) ∣ ((m * n : ℕ+) : ℕ) := ⟨n, by simp⟩
    have hn : (n : ℕ) ∣ ((m * n : ℕ+) : ℕ) := ⟨m, by simp [mul_comm]⟩
    rw [← brauerInflation_unitsInflationOfLE F Ω (unramifiedLevel_le F Ω hm) y,
      ← brauerInflation_unitsInflationOfLE F Ω (unramifiedLevel_le F Ω hn) z,
      ← LinearMap.map_add]
    simp only [brauerInvFun_brauerInflation]
    exact map_add _ _ _

theorem brauerInv_brauerInflation (n : ℕ+)
    (y : groupCohomology (galUnits F (unramifiedLevel F Ω n)) 2) :
    brauerInv F Ω ((brauerInflation (unramifiedLevel F Ω n)).hom y) = unramifiedLevelInv F Ω n y :=
  brauerInvFun_brauerInflation F Ω n y

theorem unramifiedLevelInv_injective (n : ℕ+) : Function.Injective (unramifiedLevelInv F Ω n) :=
  (unramifiedInv_injective F (unramifiedLevel F Ω n)).comp (h2GalUnitsAddEquiv F _).injective

theorem brauerInv_injective : Function.Injective (brauerInv F Ω) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨n, y, rfl⟩ := exists_brauerInflation_unramifiedLevel F Ω x
  rw [brauerInv_brauerInflation] at hx
  have hy : y = 0 := unramifiedLevelInv_injective F Ω n (hx.trans (map_zero _).symm)
  rw [hy, map_zero]

theorem brauerInv_surjective : Function.Surjective (brauerInv F Ω) := by
  intro a
  obtain ⟨n, hna⟩ : ∃ n : ℕ+, (n : ℕ) • a = 0 := by
    obtain ⟨k, hk, hka⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 (isAddTorsion_QZ a)
    exact ⟨⟨k, hk⟩, hka⟩
  have hmem : a ∈ (unramifiedInv F (unramifiedLevel F Ω n)).range := by
    rw [mem_range_unramifiedInv_iff, finrank_unramifiedLevel]
    exact hna
  obtain ⟨w, hw⟩ := hmem
  refine ⟨(brauerInflation (unramifiedLevel F Ω n)).hom ((h2GalUnitsAddEquiv F _).symm w), ?_⟩
  rw [brauerInv_brauerInflation, unramifiedLevelInv_apply, AddEquiv.apply_symm_apply, hw]

theorem brauerInv_bijective : Function.Bijective (brauerInv F Ω) :=
  ⟨brauerInv_injective F Ω, brauerInv_surjective F Ω⟩

end GroundTheory.ProfCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IntermediateField GroundTheory.LocalField ValuativeRel

section Bridge

variable (K K' L L' : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  [IsUnramified K L] [Field K'] [Field L'] [Algebra K K'] [Algebra K L'] [Algebra K' L']
  [Algebra L L'] [IsScalarTower K K' L'] [IsScalarTower K L L']

noncomputable def unitsResHomU :
    Rep.res (galRestrict K K' L L') (galUnits K L) ⟶ galUnits K' L' :=
  Rep.ofHom ⟨uliftIntLinearMap (A := Additive Lˣ) (B := Additive L'ˣ)
    (MonoidHom.toAdditive (Units.map ((algebraMap L L' : L →+* L') : L →* L'))), fun σ => by
      ext x
      exact algebraMap_galRestrict_apply K K' L L' σ _⟩

noncomputable abbrev unitsResH2Lift :
    groupCohomology (galUnits K L) 2 ⟶ groupCohomology (galUnits K' L') 2 :=
  groupCohomology.map (galRestrict K K' L L') (unitsResHomU K K' L L') 2

theorem h2GalUnitsAddEquiv_unitsResH2Lift (y : groupCohomology (galUnits K L) 2) :
    h2GalUnitsAddEquiv K' L' ((unitsResH2Lift K K' L L').hom y) =
      (unitsResH2 K K' L L').hom (h2GalUnitsAddEquiv K L y) := by
  refine groupCohomology.H2_induction_on y fun c => ?_
  have h1 := congrArg (fun h => ModuleCat.Hom.hom h c)
    (groupCohomology.H2π_comp_map (galRestrict K K' L L') (unitsResHomU K K' L L'))
  have h2 := congrArg (fun h => ModuleCat.Hom.hom h (cocycles₂IntRepAddEquiv (galUnitsHom K L) c))
    (groupCohomology.H2π_comp_map (galRestrict K K' L L') (unitsResHom K K' L L'))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
  rw [h1, h2GalUnitsAddEquiv_H2_class, h2GalUnitsAddEquiv_H2_class, h2]
  rfl

end Bridge

section Restriction

variable (F F' Ω : Type) [Field F] [Field F'] [Field Ω] [Algebra F F'] [Algebra F' Ω] [Algebra F Ω]
  [IsScalarTower F F' Ω]

theorem continuous_restrictScalarsHom_of_tower :
    Continuous (AlgEquiv.restrictScalarsHom F : (Ω ≃ₐ[F'] Ω) →* (Ω ≃ₐ[F] Ω)) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨S, hS, hSs⟩ := (krullTopology_mem_nhds_one_iff F Ω s).1 hs
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  let b := Module.finBasis F S
  let T : Set Ω := Set.range fun i => (b i : Ω)
  refine ⟨IntermediateField.adjoin F' T, ?_, ?_⟩
  · refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
    obtain ⟨i, rfl⟩ := hx
    exact ((IsIntegral.of_finite F (b i)).map S.val).tower_top
  · intro σ hσ
    apply hSs
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
    intro x hx
    have hT : ∀ i, (AlgEquiv.restrictScalarsHom F σ) (b i : Ω) = b i := fun i =>
      hσ _ (IntermediateField.subset_adjoin F' T ⟨i, rfl⟩)
    have hx' : x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : Ω) := by
      calc x = S.val (∑ i, b.repr ⟨x, hx⟩ i • b i) := by rw [b.sum_repr]; rfl
        _ = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : Ω) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          exact Finset.sum_congr rfl fun i _ => map_smul S.val _ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx', map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hT]

def galUnitsResScalars :
    Rep.res (AlgEquiv.restrictScalarsHom F : (Ω ≃ₐ[F'] Ω) →* (Ω ≃ₐ[F] Ω)) (galUnits F Ω) ⟶
      galUnits F' Ω :=
  Rep.ofHom ⟨uliftIntLinearMap (A := Additive Ωˣ) (B := Additive Ωˣ) (AddMonoidHom.id _),
    fun σ => by
      ext x
      rfl⟩

variable [IsGalois F Ω] [IsGalois F' Ω]

noncomputable def brauerRes : galoisBrauerGroup F Ω ⟶ galoisBrauerGroup F' Ω :=
  cohomologyMapAlong (AlgEquiv.restrictScalarsHom F) (continuous_restrictScalarsHom_of_tower F F' Ω)
    (galUnitsResScalars F F' Ω) 2

theorem brauerRes_eq : brauerRes F F' Ω = cohomologyMapAlong (AlgEquiv.restrictScalarsHom F)
    (continuous_restrictScalarsHom_of_tower F F' Ω) (galUnitsResScalars F F' Ω) 2 :=
  rfl

end Restriction

section Square

variable (F F' Ω : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field F'] [ValuativeRel F'] [TopologicalSpace F'] [IsNonarchimedeanLocalField F']
  [Algebra F F'] [ValuativeExtension F F'] [FiniteDimensional F F']
  [Field Ω] [Algebra F' Ω] [Algebra F Ω] [IsScalarTower F F' Ω] [IsSepClosure F Ω] [IsSepClosure F' Ω]
  [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension F Ω]
  [ValuativeExtension F' Ω]


omit [ValuativeRel F'] [TopologicalSpace F'] [IsNonarchimedeanLocalField F'] [ValuativeExtension F F']
  [FiniteDimensional F F'] [ValuativeExtension F' Ω] in
theorem unitsInflationCochains_comp_cochainsMapAlong (E : IntermediateField F Ω)
    (E' : IntermediateField F' Ω) [FiniteDimensional F E] [Normal F E] [IsUnramified F E]
    [FiniteDimensional F' E'] [Normal F' E'] [Algebra E E'] [IsScalarTower F E E']
    (hι : ∀ x : E, ((algebraMap E E' x : E') : Ω) = x) :
    unitsInflationCochains E ≫ cochainsMapAlong (AlgEquiv.restrictScalarsHom F)
        (continuous_restrictScalarsHom_of_tower F F' Ω) (galUnitsResScalars F F' Ω) =
      groupCohomology.cochainsMap (galRestrict F F' E E') (unitsResHomU F F' E E') ≫
        unitsInflationCochains E' := by
  have hres : ∀ σ : Ω ≃ₐ[F'] Ω, AlgEquiv.restrictNormalHom E (AlgEquiv.restrictScalarsHom F σ) =
      galRestrict F F' E E' (AlgEquiv.restrictNormalHom E' σ) := by
    intro σ
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    calc ((AlgEquiv.restrictNormalHom E (AlgEquiv.restrictScalarsHom F σ) x : E) : Ω)
        = σ (x : Ω) := AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalarsHom F σ) E x
      _ = σ ((algebraMap E E' x : E') : Ω) := by rw [hι]
      _ = ((AlgEquiv.restrictNormalHom E' σ (algebraMap E E' x) : E') : Ω) :=
          (AlgEquiv.restrictNormal_commutes σ E' _).symm
      _ = ((algebraMap E E' (galRestrict F F' E E' (AlgEquiv.restrictNormalHom E' σ) x) : E') : Ω) := by
          rw [algebraMap_galRestrict_apply]
      _ = _ := hι _
  ext n x : 3
  apply (ModuleCat.mono_iff_injective ((cochainsComplexι (galUnits F' Ω)).f n)).1 inferInstance
  funext g
  have hg : (fun i => AlgEquiv.restrictNormalHom E (AlgEquiv.restrictScalarsHom F (g i))) =
      ⇑(galRestrict F F' E E') ∘ fun i => AlgEquiv.restrictNormalHom E' (g i) :=
    funext fun i => hres (g i)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [cochainsComplexι_cochainsMapAlong_apply, unitsInflationCochains_f_hom_apply]
  beta_reduce
  erw [unitsInflationCochains_f_hom_apply]
  simp only [Function.comp_apply]
  rw [hg]
  apply Additive.toMul.injective
  apply Units.ext
  exact (hι _).symm


omit [ValuativeRel F'] [TopologicalSpace F'] [IsNonarchimedeanLocalField F'] [ValuativeExtension F F']
  [FiniteDimensional F F'] [ValuativeExtension F' Ω] in
theorem brauerRes_brauerInflation (E : IntermediateField F Ω)
    (E' : IntermediateField F' Ω) [FiniteDimensional F E] [Normal F E] [IsUnramified F E]
    [FiniteDimensional F' E'] [Normal F' E'] [Algebra E E'] [IsScalarTower F E E']
    (hι : ∀ x : E, ((algebraMap E E' x : E') : Ω) = x) (y : groupCohomology (galUnits F E) 2) :
    (brauerRes F F' Ω).hom ((brauerInflation E).hom y) =
      (brauerInflation E').hom ((unitsResH2Lift F F' E E').hom y) := by
  have h := congrArg (fun φ => HomologicalComplex.homologyMap φ 2)
    (unitsInflationCochains_comp_cochainsMapAlong F F' Ω E E' hι)
  simp only [HomologicalComplex.homologyMap_comp] at h
  exact congrArg (fun φ => φ.hom y) h


omit [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension F Ω]
  [ValuativeExtension F' Ω] in
theorem unramifiedLevel_le_unramifiedLevel (n : ℕ+) :
    unramifiedLevel F Ω n ≤ (unramifiedLevel F' Ω n).restrictScalars F := by
  rw [unramifiedLevel_eq, adjoin_simple_le_iff, mem_restrictScalars]
  have hζ := isPrimitiveRoot_unramifiedRoot F Ω n
  have hζ' := isPrimitiveRoot_unramifiedRoot F' Ω n
  have hq := card_residueField_eq_pow_residueDegree F F'
  have hdvd : Nat.card 𝓀[F] ^ (n : ℕ) - 1 ∣ Nat.card 𝓀[F'] ^ (n : ℕ) - 1 := by
    rw [hq, ← pow_mul, mul_comm]
    exact pow_sub_one_dvd_pow_sub_one _ (dvd_mul_right _ _)
  have hpow : unramifiedRoot F Ω n ^ (Nat.card 𝓀[F'] ^ (n : ℕ) - 1) = 1 := by
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, pow_mul, hζ.pow_eq_one, one_pow]
  have : NeZero (Nat.card 𝓀[F'] ^ (n : ℕ) - 1) := ⟨by
    have := Nat.one_lt_pow n.ne_zero (one_lt_card_residueField F')
    omega⟩
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hpow
  rw [unramifiedLevel_eq, ← hi]
  exact pow_mem (mem_adjoin_simple_self F' _) i

theorem brauerInv_brauerRes (x : galoisBrauerGroup F Ω) :
    brauerInv F' Ω ((brauerRes F F' Ω).hom x) = Module.finrank F F' • brauerInv F Ω x := by
  obtain ⟨n, y, rfl⟩ := exists_brauerInflation_unramifiedLevel F Ω x
  have hle := unramifiedLevel_le_unramifiedLevel F F' Ω n
  let ι : unramifiedLevel F Ω n →+* unramifiedLevel F' Ω n :=
    { toFun := fun a => ⟨a.1, hle a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let _ : Algebra (unramifiedLevel F Ω n) (unramifiedLevel F' Ω n) := ι.toAlgebra
  have : IsScalarTower F (unramifiedLevel F Ω n) (unramifiedLevel F' Ω n) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      apply Subtype.ext
      change ((algebraMap F (unramifiedLevel F' Ω n) a : unramifiedLevel F' Ω n) : Ω) =
        algebraMap F Ω a
      rw [IsScalarTower.algebraMap_apply F F' (unramifiedLevel F' Ω n) a,
        IsScalarTower.algebraMap_apply F F' Ω a]
      rfl
  have : ValuativeExtension (unramifiedLevel F Ω n) (unramifiedLevel F' Ω n) :=
    ⟨fun {a b} => by
      rw [← IntermediateField.coe_vle_coe_iff (L := Ω) a b,
        ← IntermediateField.coe_vle_coe_iff (L := Ω)]
      rfl⟩
  rw [brauerRes_brauerInflation F F' Ω (unramifiedLevel F Ω n) (unramifiedLevel F' Ω n)
      (fun _ => rfl), brauerInv_brauerInflation,
    brauerInv_brauerInflation, unramifiedLevelInv_apply, unramifiedLevelInv_apply,
    h2GalUnitsAddEquiv_unitsResH2Lift, unramifiedInv_unitsResH2]

end Square

end GroundTheory.ProfCoh
