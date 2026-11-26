module

public import GroundTheory.ProfiniteCohomology.LocalTateDuality.KummerCup
public import GroundTheory.LocalFields.NormCorrespondence
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing

@[expose] public section

section -- merged from GroundTheory.ProfiniteCohomology.LocalTateDuality.MainDefs
section -- merged from GroundTheory.ProfiniteCohomology.LocalTateDuality.EqZeroOfForallCupPairingZmodMulEqZeroLeft
section -- merged from GroundTheory.ProfiniteCohomology.LocalTateDuality.NormCharacters
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open IntermediateField GroundTheory.LocalField

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {Ω : Type*} [Field Ω] [Algebra F Ω] [IsSepClosure F Ω]


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsSepClosure F Ω] in
theorem exists_norm_iff_mem_range_normUnits (E : IntermediateField F Ω) [FiniteDimensional F E]
    (a : Fˣ) : (∃ y : E, Algebra.norm F y = (a : F)) ↔ a ∈ (normUnits F E).range := by
  constructor
  · rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [Algebra.norm_zero] at hy
      exact a.ne_zero hy.symm
    exact ⟨Units.mk0 y hy0, Units.ext (by simp [hy])⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u, rfl⟩


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsSepClosure F Ω] in
theorem exists_norm_of_eq {E₁ E₂ : IntermediateField F Ω} (h : E₁ = E₂) {a : F}
    (hy : ∃ y : E₁, Algebra.norm F y = a) : ∃ y : E₂, Algebra.norm F y = a := by
  subst h
  exact hy

theorem eq_top_of_forall_exists_norm (H : Subgroup Gal(Ω/F)) [H.Normal]
    (hH : IsOpen (H : Set Gal(Ω/F))) (hcomm : ∀ σ τ : Gal(Ω/F), σ * τ * σ⁻¹ * τ⁻¹ ∈ H)
    (h : ∀ a : Fˣ, ∃ y : fixedField H, Algebra.norm F y = (a : F)) : H = ⊤ := by
  set E := fixedField H with hE
  have hfix : E.fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, Subgroup.isClosed_of_isOpen H hH⟩
  have hfin : FiniteDimensional F E :=
    (InfiniteGalois.isOpen_iff_finite E).1 (by rw [hfix]; exact hH)
  have hgal : IsGalois F E :=
    (InfiniteGalois.normal_iff_isGalois E).1 (by rw [hfix]; infer_instance)
  have hc : ∀ σ' τ' : Gal(E/F), σ' * τ' = τ' * σ' := by
    intro σ' τ'
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := E) (E := Ω) σ'
    obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := E) (E := Ω) τ'
    have hk : σ * τ * σ⁻¹ * τ⁻¹ ∈ (AlgEquiv.restrictNormalHom E).ker := by
      rw [E.restrictNormalHom_ker, hfix]
      exact hcomm σ τ
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at hk
    have key : ∀ {M : Type _} [Group M] (x y : M), x * y * x⁻¹ * y⁻¹ = 1 → x * y = y * x := by
      intro M _ x y hxy
      calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
        _ = y * x := by rw [hxy, one_mul]
    exact key _ _ hk
  have : IsAbelianGalois F E := { toIsGalois := hgal, toIsMulCommutative := ⟨⟨hc⟩⟩ }
  have hidx := index_range_normUnits_of_isAbelianGalois (Ω := Ω) E
  have htop : (normUnits F E).range = ⊤ :=
    eq_top_iff.2 fun a _ => (exists_norm_iff_mem_range_normUnits E a).1 (h a)
  rw [htop, Subgroup.index_top] at hidx
  have hbot : E = ⊥ := IntermediateField.finrank_eq_one_iff.1 hidx.symm
  rw [← hfix, hbot, IntermediateField.fixingSubgroup_bot]

theorem exists_zmod_char_not_norm {n : ℕ} (hn : (n : F) ≠ 0) (a : Fˣ) (ha : ∀ b : Fˣ, b ^ n ≠ a) :
    ∃ ψ : Gal(Ω/F) →* Multiplicative (ZMod n), IsOpen (ψ.ker : Set Gal(Ω/F)) ∧
      ¬ ∃ y : fixedField ψ.ker, Algebra.norm F y = (a : F) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn Nat.cast_zero
  have : NeZero n := ⟨hn0⟩
  set P := (powMonoidHom n : Fˣ →* Fˣ).range with hP
  have hPopen : IsOpen (P : Set Fˣ) := isOpen_range_pow hn
  have hPfin : Finite (Fˣ ⧸ P) := finite_quotient_range_pow hn
  have : P.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hkill : ∀ q : Additive (Fˣ ⧸ P), n • q = 0 := by
    intro q
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul q)
    have hq : q = Additive.ofMul (x : Fˣ ⧸ P) := by rw [hx]; rfl
    rw [hq, ← ofMul_pow, ← QuotientGroup.mk_pow, (QuotientGroup.eq_one_iff (x ^ n)).2 (MonoidHom.mem_range.2 ⟨x, rfl⟩),
      ofMul_one]
  have hane : Additive.ofMul (a : Fˣ ⧸ P) ≠ 0 := by
    intro h0
    have h1 : (a : Fˣ ⧸ P) = 1 := congrArg Additive.toMul h0
    obtain ⟨b, hb⟩ := (QuotientGroup.eq_one_iff _).1 h1
    exact ha b hb
  obtain ⟨χ, hχ⟩ := zmod_exists_apply_ne_zero (A := Additive (Fˣ ⧸ P)) hkill hane
  let φ : Fˣ →* Multiplicative (ZMod n) :=
    (AddMonoidHom.toMultiplicativeRight χ).comp (QuotientGroup.mk' P)
  have hφ : ∀ x : Fˣ, φ x = Multiplicative.ofAdd (χ (Additive.ofMul (x : Fˣ ⧸ P))) := fun _ => rfl
  have hPle : P ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, hφ, (QuotientGroup.eq_one_iff _).2 hx, ofMul_one, map_zero, ofAdd_zero]
  have hH'open : IsOpen (φ.ker : Set Fˣ) := Subgroup.isOpen_mono hPle hPopen
  have : φ.ker.FiniteIndex := Subgroup.finiteIndex_of_le hPle
  have haH' : a ∉ φ.ker := by
    rw [MonoidHom.mem_ker, hφ]
    intro h1
    exact hχ (Multiplicative.ofAdd.injective h1)
  obtain ⟨E, hEfin, hEab, hEH⟩ := exists_isAbelianGalois_range_normUnits_eq (Ω := Ω) φ.ker hH'open
  have := hEfin
  have := hEab
  let φbar : Fˣ ⧸ (normUnits F E).range →* Multiplicative (ZMod n) :=
    QuotientGroup.lift _ φ (le_of_eq hEH)
  have hφbar : Function.Injective φbar := by
    refine (injective_iff_map_eq_one φbar).2 fun q hq => ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      have hx : x ∈ φ.ker := hq
      rw [← hEH] at hx
      exact (QuotientGroup.eq_one_iff _).2 hx
  let ψ : Gal(Ω/F) →* Multiplicative (ZMod n) :=
    (φbar.comp (localReciprocityAbelian E).toMonoidHom).comp (AlgEquiv.restrictNormalHom E)
  have hker : ψ.ker = E.fixingSubgroup := by
    rw [← E.restrictNormalHom_ker]
    ext σ
    simp only [MonoidHom.mem_ker]
    constructor
    · intro h1
      have h2 : (localReciprocityAbelian E) (AlgEquiv.restrictNormalHom E σ) = 1 :=
        hφbar (h1.trans (map_one φbar).symm)
      exact (MulEquiv.map_eq_one_iff _).1 h2
    · intro h1
      change φbar ((localReciprocityAbelian E) (AlgEquiv.restrictNormalHom E σ)) = 1
      rw [h1, map_one, map_one]
  refine ⟨ψ, ?_, ?_⟩
  · rw [hker]
    exact IntermediateField.fixingSubgroup_isOpen E
  · have hfE : fixedField ψ.ker = E := by
      rw [hker]
      exact InfiniteGalois.fixedField_fixingSubgroup E
    intro hy
    have := (exists_norm_iff_mem_range_normUnits E a).1 (exists_norm_of_eq hfE hy)
    rw [hEH] at this
    exact haH' this

end GroundTheory.ProfCoh
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory IntermediateField

attribute [local instance 2000] Rep.hV2

attribute [local irreducible] localClassFormationOfIsSepClosure

variable {K Ksep : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] {n : ℕ}

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ksep] in
theorem unitsInvariantOpen_mul (W : Subgroup Gal(Ksep/K)) (a b : (fixedField W)ˣ) :
    unitsInvariantOpen W (a * b) = unitsInvariantOpen W a + unitsInvariantOpen W b := by
  apply Subtype.ext
  change Additive.ofMul (Units.map (algebraMap (fixedField W) Ksep : fixedField W →* Ksep) (a * b)) =
    Additive.ofMul (Units.map (algebraMap (fixedField W) Ksep : fixedField W →* Ksep) a) +
      Additive.ofMul (Units.map (algebraMap (fixedField W) Ksep : fixedField W →* Ksep) b)
  rw [map_mul, ofMul_mul]


omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ksep] in
theorem natCast_fixedField_ne_zero (hn : (n : K) ≠ 0) (W : Subgroup Gal(Ksep/K)) :
    (n : fixedField W) ≠ 0 := by
  rw [← map_natCast (algebraMap K (fixedField W))]
  exact (map_ne_zero_iff _ (algebraMap K (fixedField W)).injective).2 hn

theorem finite_cohomology_one_res_galRootsOfUnity (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K)) :
    Finite (cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n)) 1) := by
  let := GroundTheory.LocalField.algebraicValuativeRel K Ksep
  let := GroundTheory.LocalField.algebraicTopology K Ksep
  have := GroundTheory.LocalField.algebraicTopology_isValuativeTopology K Ksep
  have := GroundTheory.LocalField.algebraicValuativeRel_valuativeExtension K Ksep
  have hfinE : Finite ((fixedField (U : Subgroup Gal(Ksep/K)))ˣ ⧸
      (powMonoidHom n : (fixedField (U : Subgroup Gal(Ksep/K)))ˣ →* _).range) :=
    GroundTheory.LocalField.finite_quotient_range_pow (natCast_fixedField_ne_zero hn _)
  let κ : (fixedField (U : Subgroup Gal(Ksep/K)))ˣ →*
      Multiplicative (cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype
        (galRootsOfUnity.{0} K Ksep n)) 1) :=
    { toFun := fun a => Multiplicative.ofAdd ((δ (kummerSeqOpen_shortExact hn (U : Subgroup Gal(Ksep/K)))
        0 1 rfl).hom ((H0Iso _).inv.hom (unitsInvariantOpen (U : Subgroup Gal(Ksep/K)) a)))
      map_one' := by
        have h := unitsInvariantOpen_pow (U : Subgroup Gal(Ksep/K)) 1 0
        rw [pow_zero, zero_smul] at h
        rw [h, map_zero, map_zero, ofAdd_zero]
      map_mul' := fun a b => by
        rw [unitsInvariantOpen_mul, map_add (f := _), map_add (f := _), ofAdd_add] }
  have hle : (powMonoidHom n : (fixedField (U : Subgroup Gal(Ksep/K)))ˣ →* _).range ≤ κ.ker := by
    rintro _ ⟨b, rfl⟩
    rw [MonoidHom.mem_ker]
    change Multiplicative.ofAdd ((δ (kummerSeqOpen_shortExact hn (U : Subgroup Gal(Ksep/K))) 0 1 rfl).hom
      ((H0Iso _).inv.hom (unitsInvariantOpen (U : Subgroup Gal(Ksep/K)) (b ^ n)))) = 1
    rw [δ_unitsInvariantOpen_pow_eq_zero hn, ofAdd_zero]
  refine Finite.of_surjective (fun q => Multiplicative.toAdd (QuotientGroup.lift _ κ hle q)) fun y => ?_
  obtain ⟨a, rfl⟩ := exists_δ_unitsInvariantOpen_eq hn U y
  exact ⟨(a : _ ⧸ (powMonoidHom n : (fixedField (U : Subgroup Gal(Ksep/K)))ˣ →* _).range), rfl⟩

theorem eq_zero_of_forall_cupPairing_zmodMul_eq_zero_left (hn : (n : K) ≠ 0)
    (U : OpenSubgroup Gal(Ksep/K)) (x : cohomology (zmodRep.{0} (U : Subgroup Gal(Ksep/K)) n) 1)
    (h : ∀ y : cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n)) 1,
      cupPairing (zmodMulPairing n (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n))
        (nsmul_res_galRootsOfUnity_eq_zero hn _)) (show 1 + 1 = 2 from rfl) x y = 0) :
    x = 0 := by
  let := GroundTheory.LocalField.algebraicValuativeRel K Ksep
  let := GroundTheory.LocalField.algebraicTopology K Ksep
  have := GroundTheory.LocalField.algebraicTopology_isValuativeTopology K Ksep
  have := GroundTheory.LocalField.algebraicValuativeRel_valuativeExtension K Ksep
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective _ 1 x
  have hnorm := fun a => (cupPairing_δ_unitsInvariantOpen_eq_zero_iff hn U z a).1 (h _)
  have hopen : IsOpen (charKer (charAdd (openChar n U z)) : Set Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K)))) := by
    have e : (charKer (charAdd (openChar n U z)) : Set Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K)))) =
        (fun g => openChar n U z (Additive.ofMul g)) ⁻¹' {0} := by
      ext g
      exact mem_charKer
    rw [e]
    exact (isOpen_discrete _).preimage ((openChar n U z).continuous_toFun.comp continuous_ofMul)
  have hcomm : ∀ σ τ : Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K))),
      σ * τ * σ⁻¹ * τ⁻¹ ∈ charKer (charAdd (openChar n U z)) := fun σ τ => by
    rw [mem_charKer, ofMul_mul, ofMul_mul, ofMul_mul, ofMul_inv, ofMul_inv, map_add (f := _), map_add (f := _), map_add (f := _),
      map_neg, map_neg]
    abel
  have htop := eq_top_of_forall_exists_norm _ hopen hcomm hnorm
  rw [cohomologyπ_one_eq_zero_iff_of_trivial _ (fun _ _ => rfl)]
  exact fun g => ULift.ext (zmodCocycleHom_eq_zero_of_charKer_eq_top hn U z htop g)

theorem eq_zero_of_forall_cupPairing_zmodMul_eq_zero_right (hn : (n : K) ≠ 0)
    (U : OpenSubgroup Gal(Ksep/K))
    (y : cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n)) 1)
    (h : ∀ x : cohomology (zmodRep.{0} (U : Subgroup Gal(Ksep/K)) n) 1,
      cupPairing (zmodMulPairing n (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n))
        (nsmul_res_galRootsOfUnity_eq_zero hn _)) (show 1 + 1 = 2 from rfl) x y = 0) :
    y = 0 := by
  let := GroundTheory.LocalField.algebraicValuativeRel K Ksep
  let := GroundTheory.LocalField.algebraicTopology K Ksep
  have := GroundTheory.LocalField.algebraicTopology_isValuativeTopology K Ksep
  have := GroundTheory.LocalField.algebraicValuativeRel_valuativeExtension K Ksep
  obtain ⟨a, rfl⟩ := exists_δ_unitsInvariantOpen_eq hn U y
  by_cases ha : ∃ b : (fixedField (U : Subgroup Gal(Ksep/K)))ˣ, b ^ n = a
  · obtain ⟨b, rfl⟩ := ha
    exact δ_unitsInvariantOpen_pow_eq_zero hn _ b
  · simp only [not_exists] at ha
    obtain ⟨ψ, hψo, hψ⟩ := exists_zmod_char_not_norm (Ω := Ksep) (natCast_fixedField_ne_zero hn _) a ha
    obtain ⟨z, hz⟩ := exists_cocycle_charKer_eq hn U ψ hψo
    exact (hψ (exists_norm_of_eq (congrArg fixedField hz)
      ((cupPairing_δ_unitsInvariantOpen_eq_zero_iff hn U z a).1 (h _)))).elim

theorem isPerfectPairing_localInvRootsOfUnity (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K)) :
    IsPerfectPairing
      (bilinAddHom (cupPairing (zmodMulPairing n
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n))
        (nsmul_eq_zero_of_nonempty_addEquiv (nonempty_addEquiv_galRootsOfUnity hn)))
        (show 1 + 1 = 2 from rfl)))
      (localInvRootsOfUnity hn U).toAddMonoidHom := by
  have : NeZero n := ⟨ne_zero_of_natCast_ne_zero' hn⟩
  set β := bilinAddHom (cupPairing (zmodMulPairing n
    (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n))
    (nsmul_eq_zero_of_nonempty_addEquiv (nonempty_addEquiv_galRootsOfUnity hn)))
    (show 1 + 1 = 2 from rfl)) with hβ
  set t := (localInvRootsOfUnity hn U).toAddMonoidHom with ht
  have ht0 : ∀ c, t c = 0 → c = 0 := fun c hc =>
    (localInvRootsOfUnity hn U).injective (hc.trans (map_zero _).symm)
  have h1 : Function.Injective ((AddMonoidHom.compHom t).comp β) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    refine eq_zero_of_forall_cupPairing_zmodMul_eq_zero_left hn U x fun y => ht0 _ ?_
    exact DFunLike.congr_fun hx y
  have h2 : Function.Injective ((AddMonoidHom.compHom t).comp β.flip) := by
    refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
    refine eq_zero_of_forall_cupPairing_zmodMul_eq_zero_right hn U y fun x => ht0 _ ?_
    exact DFunLike.congr_fun hy x
  have hYfin := finite_cohomology_one_res_galRootsOfUnity hn U
  have hXfin : Finite (cohomology (zmodRep.{0} (U : Subgroup Gal(Ksep/K)) n) 1) :=
    Finite.of_injective _ h1
  have c1 := Nat.card_le_card_of_injective _ h1
  have c2 := Nat.card_le_card_of_injective _ h2
  have c3 := card_addMonoidHom_zmod_le (n := n)
    (A := cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n)) 1)
  have c4 := card_addMonoidHom_zmod_le (n := n)
    (A := cohomology (zmodRep.{0} (U : Subgroup Gal(Ksep/K)) n) 1)
  exact ⟨h1.bijective_of_nat_card_le (by omega), h2.bijective_of_nat_card_le (by omega)⟩

end GroundTheory.ProfCoh
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory IntermediateField GroundTheory.LocalField

universe u

attribute [local instance 2000] Rep.hV2

section Top

variable (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω]

theorem brauerInv_eq_localInv_top (y : galoisBrauerGroup K Ω) :
    brauerInv K Ω y = localInv K Ω ⊤
      ((cohomologyRes (galUnits.{0} K Ω) ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)) 2).hom
        y) := by
  rw [localInv_apply]
  have : IsSepClosure (fixedField ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K))) Ω :=
    ⟨IsSepClosure.sep_closed K, Algebra.isSeparable_tower_top_of_isSeparable K _ Ω⟩
  have : IsGalois (fixedField ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K))) Ω :=
    IsGalois.tower_top_of_isGalois K _ Ω
  have hres : (openCohomologyIso (⊤ : OpenSubgroup Gal(Ω/K)) 2).hom.hom
      ((cohomologyRes (galUnits.{0} K Ω) ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)) 2).hom
        y) =
      (brauerRes K (fixedField ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K))) Ω).hom y := by
    rw [openCohomologyIso_hom, cohomologyRes_eq, ← ModuleCat.comp_apply,
      ← cohomologyMapAlong_comp, brauerRes_eq]
    congr 1
  have hrank :
      Module.finrank K (fixedField ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K))) = 1 := by
    rw [← index_openSubgroup]
    exact Subgroup.index_top
  rw [hres, brauerInv_brauerRes, hrank, one_smul]

end Top

section SepClosure

variable (K Ksep : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

def brauerInvOfIsSepClosure : galoisBrauerGroup K Ksep →+ QZ :=
  letI := algebraicValuativeRel K Ksep
  letI := algebraicTopology K Ksep
  haveI := algebraicTopology_isValuativeTopology K Ksep
  haveI := algebraicValuativeRel_valuativeExtension K Ksep
  brauerInv K Ksep

theorem brauerInvOfIsSepClosure_eq_inv_top (y : galoisBrauerGroup K Ksep) :
    brauerInvOfIsSepClosure K Ksep y = (localClassFormationOfIsSepClosure K Ksep).inv ⊤
      ((cohomologyRes (galUnits.{0} K Ksep)
        ((⊤ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)) 2).hom y) :=
  letI := algebraicValuativeRel K Ksep
  letI := algebraicTopology K Ksep
  haveI := algebraicTopology_isValuativeTopology K Ksep
  haveI := algebraicValuativeRel_valuativeExtension K Ksep
  brauerInv_eq_localInv_top K Ksep y

variable {K Ksep} {n : ℕ}

def localDualityHypotheses (hn : (n : K) ≠ 0) :
    DualityHypotheses n (galRootsOfUnity.{0} K Ksep n) where
  nonempty_addEquiv := nonempty_addEquiv_galRootsOfUnity hn
  finite_cohomology := finite_cohomology_galois_le_two K Ksep hn
  subsingleton_cohomology_three := subsingleton_cohomology_three_galois K Ksep hn
  t := localInvRootsOfUnity hn
  t_cores := localInvRootsOfUnity_cores hn
  isPerfectPairing := isPerfectPairing_localInvRootsOfUnity hn

theorem localDualityHypotheses_alt (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K)) :
    (localDualityHypotheses (Ksep := Ksep) hn).t U = localInvRootsOfUnity hn U :=
  rfl

end SepClosure

section Bridge

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

def dualRepRootsOfUnityIso (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) (n : ℕ)
    (hM : ∀ m : M, n • m = 0) :
    dualRep (galRootsOfUnity.{u} K L n) M ≅ cartierDual K L M :=
  cartierDualIsoHomRootsOfUnityOfNsmul K L M n hM

variable {K L}

end Bridge

section Pairing

variable (K Ksep : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

def localDualityPairing (M : Rep (ULift.{0} ℤ) Gal(Ksep/K)) [IsDiscreteRep M] [Finite M]
    {r s : ℕ} (h : r + s = 2) :
    cohomology M r →+ cohomology (cartierDual K Ksep M) s →+ QZ :=
  (AddMonoidHom.compHom (brauerInvOfIsSepClosure K Ksep)).comp
    (bilinAddHom (cupPairing (cartierPairing K Ksep M) h))

variable {K Ksep}

theorem localDualityPairing_apply (M : Rep (ULift.{0} ℤ) Gal(Ksep/K)) [IsDiscreteRep M] [Finite M]
    {r s : ℕ} (h : r + s = 2) (x : cohomology M r) (y : cohomology (cartierDual K Ksep M) s) :
    localDualityPairing K Ksep M h x y =
      brauerInvOfIsSepClosure K Ksep (cupPairing (cartierPairing K Ksep M) h x y) :=
  rfl

end Pairing

end GroundTheory.ProfCoh
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

universe u

attribute [local instance 2000] Rep.hV2

section Transport

variable {n : ℕ} [NeZero n]

theorem bijective_of_zmodToQZ {X X' Y Y' : Type*} [AddCommGroup X] [AddCommGroup X']
    [AddCommGroup Y] [AddCommGroup Y'] (β : X →+ Y →+ ZMod n) (γ : X' →+ Y' →+ QZ)
    (e₁ : X ≃+ X') (e₂ : Y ≃+ Y') (hY : ∀ y : Y, n • y = 0)
    (hγ : ∀ x y, γ (e₁ x) (e₂ y) = zmodToQZ n (β x y)) (hβ : Function.Bijective β) :
    Function.Bijective γ := by
  refine ⟨fun x₁ x₂ hx => ?_, fun χ => ?_⟩
  · obtain ⟨a₁, rfl⟩ := e₁.surjective x₁
    obtain ⟨a₂, rfl⟩ := e₁.surjective x₂
    refine congrArg e₁ (hβ.1 (AddMonoidHom.ext fun y => zmodToQZ_injective ?_))
    rw [← hγ, ← hγ, hx]
  · have hχ : ∀ y, n • (χ.comp e₂.toAddMonoidHom) y = 0 := fun y => by
      rw [← map_nsmul, hY, map_zero]
    obtain ⟨x, hx⟩ := hβ.2 (zmodOfQZ _ hχ)
    refine ⟨e₁ x, AddMonoidHom.ext fun y' => ?_⟩
    obtain ⟨y, rfl⟩ := e₂.surjective y'
    rw [hγ, hx, zmodToQZ_zmodOfQZ]
    rfl

end Transport

section CohomologyIso

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def cohomologyAddEquivOfIso {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] (e : A ≅ B)
    (m : ℕ) : cohomology A m ≃+ cohomology B m where
  toFun := (cohomologyMap e.hom m).hom
  invFun := (cohomologyMap e.inv m).hom
  left_inv x := by
    rw [← ModuleCat.comp_apply, ← cohomologyMap_comp, e.hom_inv_id, cohomologyMap_id]
    rfl
  right_inv x := by
    rw [← ModuleCat.comp_apply, ← cohomologyMap_comp, e.inv_hom_id, cohomologyMap_id]
    rfl
  map_add' := map_add _

theorem cohomologyAddEquivOfIso_apply {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B]
    (e : A ≅ B) (m : ℕ) (x : cohomology A m) :
    cohomologyAddEquivOfIso e m x = (cohomologyMap e.hom m).hom x :=
  rfl

end CohomologyIso

section Local

variable {K Ksep : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

attribute [local irreducible] localClassFormationOfIsSepClosure

instance isDiscreteRep_dualRep_galRootsOfUnity (n : ℕ) (M : Rep (ULift.{0} ℤ) Gal(Ksep/K))
    [IsDiscreteRep M] [Finite M] : IsDiscreteRep (dualRep (galRootsOfUnity.{0} K Ksep n) M) :=
  isDiscreteRep_dualRep _ _

theorem brauerInvOfIsSepClosure_rootsOfUnity {n : ℕ} (hn : (n : K) ≠ 0)
    (z : cohomology (galRootsOfUnity.{0} K Ksep n) 2) :
    brauerInvOfIsSepClosure K Ksep ((cohomologyMap (rootsOfUnityToUnits K Ksep n) 2).hom z) =
      zmodToQZ n ((localDualityHypotheses (Ksep := Ksep) hn).tTop z) := by
  have : NeZero n := ⟨ne_zero_of_natCast_ne_zero' hn⟩
  have hres := congrArg (fun φ => φ.hom z) (cohomologyMap_comp_cohomologyRes
    (galRootsOfUnity.{0} K Ksep n) (rootsOfUnityToUnits K Ksep n) ((⊤ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)) 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hres
  rw [brauerInvOfIsSepClosure_eq_inv_top, hres, DualityHypotheses.tTop, AddMonoidHom.comp_apply,
    localDualityHypotheses_alt]
  change _ = zmodToQZ n (localInvRootsOfUnity hn ⊤ _)
  rw [zmodToQZ_localInvRootsOfUnity, rootsOfUnityInv_apply]
  rfl

theorem tensorHom_dualRepRootsOfUnityIso_cartierPairing (M : Rep (ULift.{0} ℤ) Gal(Ksep/K))
    {n : ℕ} (hM : ∀ m : M, n • m = 0) :
    (𝟙 M ⊗ₘ (dualRepRootsOfUnityIso K Ksep M n hM).hom) ≫ cartierPairing K Ksep M =
      evalPairing (galRootsOfUnity.{0} K Ksep n) M ≫ rootsOfUnityToUnits K Ksep n := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a f => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem localDualityPairing_cohomologyMap (M : Rep (ULift.{0} ℤ) Gal(Ksep/K)) [IsDiscreteRep M]
    [Finite M] {n : ℕ} (hn : (n : K) ≠ 0) (hM : ∀ m : M, n • m = 0) {r s : ℕ} (h : r + s = 2)
    (x : cohomology M r) (y : cohomology (dualRep (galRootsOfUnity.{0} K Ksep n) M) s) :
    localDualityPairing K Ksep M h x
        ((cohomologyMap (dualRepRootsOfUnityIso K Ksep M n hM).hom s).hom y) =
      zmodToQZ n (dualityMap (galRootsOfUnity.{0} K Ksep n) h
        (localDualityHypotheses (Ksep := Ksep) hn).tTop M x y) := by
  have hc := cupPairing_cohomologyMap (cartierPairing K Ksep M) (𝟙 M)
    (dualRepRootsOfUnityIso K Ksep M n hM).hom h x y
  rw [cohomologyMap_id, ModuleCat.id_apply, tensorHom_dualRepRootsOfUnityIso_cartierPairing] at hc
  rw [localDualityPairing_apply, hc, dualityMap_apply, ← brauerInvOfIsSepClosure_rootsOfUnity hn,
    cohomologyMap_cupPairing]

theorem finite_cohomology_localField (M : Rep (ULift.{0} ℤ) Gal(Ksep/K)) [IsDiscreteRep M]
    [Finite M] (hM : (Nat.card M : K) ≠ 0) (r : ℕ) : Finite (cohomology M r) :=
  finite_cohomology_galois_top K Ksep hM M (fun _ => card_nsmul_eq_zero') r

theorem subsingleton_cohomology_localField (M : Rep (ULift.{0} ℤ) Gal(Ksep/K)) [IsDiscreteRep M]
    [Finite M] (hM : (Nat.card M : K) ≠ 0) (r : ℕ) (hr : 3 ≤ r) :
    Subsingleton (cohomology M r) :=
  subsingleton_cohomology_galois_top K Ksep hM M (fun _ => card_nsmul_eq_zero') r hr

theorem bijective_localDualityPairing (M : Rep (ULift.{0} ℤ) Gal(Ksep/K)) [IsDiscreteRep M]
    [Finite M] (hM : (Nat.card M : K) ≠ 0) {r s : ℕ} (h : r + s = 2) :
    Function.Bijective (localDualityPairing K Ksep M h) := by
  set n := Nat.card M
  have : NeZero n := ⟨ne_zero_of_natCast_ne_zero' hM⟩
  have hMn : ∀ m : M, n • m = 0 := fun _ => card_nsmul_eq_zero'
  have hD : ∀ d : galRootsOfUnity.{0} K Ksep n, n • d = 0 :=
    nsmul_eq_zero_of_nonempty_addEquiv (nonempty_addEquiv_galRootsOfUnity hM)
  refine bijective_of_zmodToQZ
    (dualityMap (galRootsOfUnity.{0} K Ksep n) h (localDualityHypotheses (Ksep := Ksep) hM).tTop M)
    (localDualityPairing K Ksep M h) (AddEquiv.refl _)
    (cohomologyAddEquivOfIso (dualRepRootsOfUnityIso K Ksep M n hMn) s)
    (nsmul_cohomology_eq_zero _ (nsmul_dualRep_eq_zero hD) s)
    (fun x y => localDualityPairing_cohomologyMap M hM hMn h x y)
    ((localDualityHypotheses hM).bijective_dualityMap_of_group M hMn h)

end Local

end GroundTheory.ProfCoh
