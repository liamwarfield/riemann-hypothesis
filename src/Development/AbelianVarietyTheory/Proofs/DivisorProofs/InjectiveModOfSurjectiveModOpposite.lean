module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTautologicalBaseNsmulDegenerationData
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataNsmulRescaleKeepsLaws
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryModuliObjectSpreadNormalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalAbelianSchemeTorsionRationalFieldPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveModOfSurjectiveModOpposite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveModOfSurjectiveModOpposite
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

noncomputable section

namespace GlobalTheory.LowFilt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem datum_finite_int (D : Datum H) : Module.Finite ℤ D.La := by
  haveI := D.fin
  exact Module.Finite.trans (𝓞 E) D.La

theorem datum_isTorsionFree_int (D : Datum H) : Module.IsTorsionFree ℤ D.La := by
  refine Module.isTorsionFree_iff_smul_eq_zero.2 ?_
  intro k x hkx
  by_contra hk
  push_neg at hk
  have hx : x = 0 := D.unimod.1 (LinearMap.ext fun b => by
    have := congrArg (fun v => D.EF v b) hkx
    simp only [map_zsmul, LinearMap.smul_apply, map_zero, LinearMap.zero_apply, smul_eq_mul, mul_eq_zero] at this
    simpa using this.resolve_left hk.1)
  exact hk.2 hx

theorem sub_free_finite (D : Datum H) (Z : Submodule (𝓞 E) D.La) : Module.Free ℤ Z ∧ Module.Finite ℤ Z := by
  haveI := datum_finite_int D
  haveI := datum_isTorsionFree_int D
  haveI : IsNoetherian ℤ D.La := isNoetherian_of_isNoetherianRing_of_finite ℤ D.La
  let f : Z →ₗ[ℤ] D.La := Z.subtype.toAddMonoidHom.toIntLinearMap
  have hf : Function.Injective f := Subtype.val_injective
  haveI : Module.Finite ℤ Z := Module.Finite.of_injective f hf
  haveI : Module.IsTorsionFree ℤ Z := hf.moduleIsTorsionFree f (fun r m => f.map_smul r m)
  exact ⟨inferInstance, inferInstance⟩

theorem IsOpp.finrank_int_eq {D : Datum H} {Z Z' : Submodule (𝓞 E) D.La} (h : IsOpp D Z Z') :
    Module.finrank ℤ Z' = Module.finrank ℤ Z := by
  obtain ⟨hZf, hZn⟩ := sub_free_finite D Z
  let ψ : Z' →ₗ[ℤ] Module.Dual ℤ Z :=
    { toFun := fun b => (D.EF.flip (b : D.La)).comp Z.subtype.toAddMonoidHom.toIntLinearMap
      map_add' := fun b b' => by ext a; simp
      map_smul' := fun k b => by ext a; simp }
  have hψ : Function.Bijective ψ := by
    refine ⟨fun b b' hbb => ?_, fun φ => ?_⟩
    · obtain ⟨c, -, hu⟩ := h.2.2.1 ((ψ b).toAddMonoidHom)
      have e1 := hu b (fun a => rfl)
      have e2 := hu b' (fun a => by rw [hbb]; rfl)
      exact e1.trans e2.symm
    · obtain ⟨b, hb, -⟩ := h.2.2.1 φ.toAddMonoidHom
      exact ⟨b, LinearMap.ext fun a => hb a⟩
  rw [(LinearEquiv.ofBijective ψ hψ).finrank_eq]
  classical
  let bZ := Module.Free.chooseBasis ℤ Z
  rw [Module.finrank_eq_card_basis bZ.dualBasis, Module.finrank_eq_card_basis bZ]

theorem IsOpp.mem_nsmul_of_surj_mod {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (D : Datum H) (y : D.La →ₗ[𝓞 E] X) (n : ℕ) (hn : 0 < n) (Z Z' : Submodule (𝓞 E) D.La)
    (h : IsOpp D Z Z') (hr : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X)
    (hs : ∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) (b : D.La) (hb : b ∈ Z') (hy : ∃ e, y b = n • e) :
    ∃ e ∈ Z', b = n • e := by
  obtain ⟨hZf, hZn⟩ := sub_free_finite D Z
  obtain ⟨hZf', hZn'⟩ := sub_free_finite D Z'
  have hrank : Module.finrank ℤ Z' = Module.finrank ℤ X := by
    rw [h.finrank_int_eq, GlobalTheory.finrank_int_eq_finrank_ringOfIntegers_mul E Z,
      GlobalTheory.finrank_int_eq_finrank_ringOfIntegers_mul E X, hr]
  let nB : AddSubgroup X := (nsmulAddMonoidHom n : X →+ X).range
  let nA : AddSubgroup Z' := (nsmulAddMonoidHom n : Z' →+ Z').range
  let g : Z' →+ X := y.toAddMonoidHom.comp Z'.subtype.toAddMonoidHom
  let f : Z' →+ X ⧸ nB := (QuotientAddGroup.mk' nB).comp g
  have hf : Function.Surjective f := by
    rintro ⟨x⟩
    obtain ⟨c, hc, e, he⟩ := hs x
    refine ⟨⟨c, hc⟩, ?_⟩
    show (QuotientAddGroup.mk (y c) : X ⧸ nB) = QuotientAddGroup.mk x
    rw [he, QuotientAddGroup.eq]
    exact ⟨-e, by simp⟩
  have hAK : nA ≤ f.ker := by
    rintro _ ⟨a, rfl⟩
    rw [AddMonoidHom.mem_ker]
    show (QuotientAddGroup.mk (y ((n • a : Z') : D.La)) : X ⧸ nB) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact ⟨y a, by simp⟩
  have hK : f.ker.index = n ^ Module.finrank ℤ X := by
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf, AddSubgroup.card_top]
    exact AddSubgroup.index_range_nsmul X n
  have hA : nA.index = n ^ Module.finrank ℤ X := by
    rw [← hrank]
    exact AddSubgroup.index_range_nsmul Z' n
  have hpos : 0 < n ^ Module.finrank ℤ X := pow_pos hn _
  have hrel : nA.relIndex f.ker = 1 := by
    have := AddSubgroup.relIndex_mul_index hAK
    rw [hK, hA] at this
    exact (Nat.mul_eq_right hpos.ne').1 this
  have hmem : (⟨b, hb⟩ : Z') ∈ f.ker := by
    obtain ⟨e, he⟩ := hy
    rw [AddMonoidHom.mem_ker]
    show (QuotientAddGroup.mk (y b) : X ⧸ nB) = 0
    rw [QuotientAddGroup.eq_zero_iff, he]
    exact ⟨e, rfl⟩
  obtain ⟨c, hc⟩ := AddSubgroup.relIndex_eq_one.1 hrel hmem
  exact ⟨c, c.2, (congrArg Subtype.val hc).symm.trans rfl⟩

end GlobalTheory.LowFilt

theorem GlobalTheory.LowFilt.inj_mod_of_surj_mod : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ), 0 < n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X → (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) →
    ∀ b ∈ Z', (∃ e, y b = n • e) → ∃ e ∈ Z', b = n • e :=
  fun D _ _ _ _ _ y n hn Z Z' h hr hs b hb hy => IsOpp.mem_nsmul_of_surj_mod D y n hn Z Z' h hr hs b hb hy
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveModOfSurjectiveModOppositeStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_mod_of_surjective_mod_opposite : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ), 0 < n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X → (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) →
    ∀ b ∈ Z', (∃ e, y b = n • e) → ∃ e ∈ Z', b = n • e := by
  first | exact @GlobalTheory.LowFilt.inj_mod_of_surj_mod | exact GlobalTheory.LowFilt.inj_mod_of_surj_mod | (intros; apply GlobalTheory.LowFilt.inj_mod_of_surj_mod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonemptyOpenThetaRingRegular
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonemptyOpenThetaRingRegular
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep

theorem exists_opens_R_le_O : ∀ X₁ : GlobalTheory.GSep.GSet, ∃ U : X₁.M.Z.Opens, (U : Set X₁.M.Z).Nonempty ∧
    ∀ z ∈ U, X₁.S.R ≤ X₁.M.O z := by
  intro X₁
  obtain ⟨s, hs⟩ := X₁.S.fg
  refine ⟨⟨⋂ x ∈ s, {z | x ∈ X₁.M.O z}, isOpen_biInter_finset fun x _ => X₁.M.isOpen_setOf_mem_O x⟩,
    ⟨genericPoint X₁.M.Z, ?_⟩, ?_⟩
  · show genericPoint X₁.M.Z ∈ ⋂ x ∈ s, {z | x ∈ X₁.M.O z}
    refine Set.mem_iInter₂.2 fun x _ => ?_
    show x ∈ X₁.M.O (genericPoint X₁.M.Z)
    rw [RatModel.O_genericPoint]
    exact Algebra.mem_top
  · intro z hz
    have hz' : z ∈ ⋂ x ∈ s, {z | x ∈ X₁.M.O z} := hz
    rw [← hs]
    exact Algebra.adjoin_le fun x hx => Set.mem_iInter₂.1 hz' x hx

end GlobalTheory.GSep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonemptyOpenThetaRingRegularStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonempty_open_thetaRing_regular : ∀ X₁ : GlobalTheory.GSep.GSet, ∃ U : X₁.M.Z.Opens, (U : Set X₁.M.Z).Nonempty ∧ ∀ z ∈ U, X₁.S.R ≤ X₁.M.O z := by
  first | exact @GlobalTheory.GSep.exists_opens_R_le_O | exact GlobalTheory.GSep.exists_opens_R_le_O | (intros; apply GlobalTheory.GSep.exists_opens_R_le_O <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIsUnitDividingThetaConstantNeZeroDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIsUnitDividingThetaConstantNeZeroDvd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep

theorem unit_ne_zero_dvd : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → IsUnit ((X₁.S.r * X₁.S.N : ℕ) : V) ∧ 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 ∧ ∀ a, ∃ r : V, 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ = algebraMap V (FractionRing V) r * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 x₀
  intro hdiv
  have sp : ∀ w, X₁.M.Z.fromSpecStalk z₁ w ⤳ z₁ := fun w => by
    have : X₁.M.Z.fromSpecStalk z₁ w ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨w, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  set y' : Sp V ⟶ X₁.M.Z := spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hy'
  set y : Sp (FractionRing V) ⟶ X₁.M.Z := jK V ≫ y' with hy
  have h1 : y' (closedPoint V) ⤳ z₁ := sp _
  set ξ := y (closedPoint (FractionRing V)) with hξ
  have hξz : ξ ⤳ z₁ := sp _
  have hyξ : ∀ w, y w ⤳ ξ := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton y _)
  have hx₀ : X₁.S.th x₀ ∈ X₁.M.O ξ := 𝔪.reg _ (X₁.S.th_mem x₀)
  have key : ∀ a, 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ =
      algebraMap V (FractionRing V) (RatModel.valLoc y' z₁ h1 ⟨_, hdiv.2 a⟩) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
    intro a
    have hq : X₁.S.th a / X₁.S.th x₀ ∈ X₁.M.O ξ := RatModel.O_le_of_specializes hξz (hdiv.2 a)
    have e : X₁.S.th a = X₁.S.th a / X₁.S.th x₀ * X₁.S.th x₀ := (div_mul_cancel₀ _ hdiv.1).symm
    rw [𝔪.yK_eq, 𝔪.yK_eq]
    change X₁.M.val y (X₁.S.th a) = _ * X₁.M.val y (X₁.S.th x₀)
    rw [show X₁.M.val y (X₁.S.th a) = X₁.M.val y (X₁.S.th a / X₁.S.th x₀ * X₁.S.th x₀) from congrArg _ e,
      RatModel.val_mul hyξ hq hx₀]
    congr 1
    exact RatModel.val_spMap_comp (algebraMap V (FractionRing V)) y' h1 ⟨_, hdiv.2 a⟩
  refine ⟨?_, ?_, fun a => ⟨_, key a⟩⟩
  · have := X₁.S.unit.map (ev.comp ((X₁.M.stalkEquiv z₁).symm.toRingHom.comp (algebraMap X₁.o₁ (X₁.M.O z₁))))
    rwa [map_natCast] at this
  · intro h0
    obtain ⟨c, -, hc⟩ := GoodOut.exists_th_notMem abelianSchemeLaws_all.1 abelianSchemeLaws_all.2 X₁.ρ
      ⟨RingHom.ker 𝔪.yK, RingHom.ker_isPrime _⟩ x₀
    exact hc (by
      change 𝔪.yK _ = 0
      rw [key, h0, mul_zero])

end GlobalTheory.GSep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIsUnitDividingThetaConstantNeZeroDvdStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_isUnit_dividingThetaConstant_ne_zero_dvd : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → IsUnit ((X₁.S.r * X₁.S.N : ℕ) : V) ∧ 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 ∧ ∀ a, ∃ r : V, 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ = algebraMap V (FractionRing V) r * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
  exact @GlobalTheory.GSep.unit_ne_zero_dvd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSectionsExhaustOfGenericGeometric
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSectionsExhaustOfGenericGeometric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.IntTerm

theorem tf_apply_eq_genericPoint {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F]
    [Algebra (FractionRing R) F] (a : Sp F) : (TF (R := R) F).hom a = genericPoint (Sp R) := by
  rw [genericPoint_eq_bot_of_affine]
  have ha : (a : PrimeSpectrum F).asIdeal = ⊥ :=
    @Ideal.eq_bot_of_prime _ _ _ (a : PrimeSpectrum F).isPrime
  have hinj : Function.Injective ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))) :=
    (algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective R (FractionRing R))
  apply PrimeSpectrum.ext
  show Ideal.comap _ (Ideal.comap _ (a : PrimeSpectrum F).asIdeal) = ⊥
  rw [ha, Ideal.comap_comap]
  exact Ideal.comap_bot_of_injective _ hinj

theorem exists_eq_section_of_finite_flat {R : Type} [CommRing R] [IsDomain R] (T : Over (Sp R))
    [IsFinite T.hom] [Flat T.hom] {C : Type} (σ : C → (𝟙_ (Over (Sp R)) ⟶ T))
    (H : ∀ t : TF (R := R) (AlgebraicClosure (FractionRing R)) ⟶ T, ∃ c, t = toUnit _ ≫ σ c)
    (K : Type) [Field K] (x : Sp K ⟶ Sp R) (p : Over.mk x ⟶ T) : ∃ c, p = toUnit _ ≫ σ c := by
  set Kb := AlgebraicClosure (FractionRing R)
  set q := p.left (IsLocalRing.closedPoint K) with hqdef
  obtain ⟨q', hq'q, hq'⟩ := Flat.generalizingMap T.hom (genericPoint_specializes (T.hom q))
  let j : Sp Kb ⟶ Sp R := (TF (R := R) Kb).hom
  obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := T.hom) (g := j) q'
    (IsLocalRing.closedPoint Kb) (by rw [hq']; exact (tf_apply_eq_genericPoint (R := R) Kb _).symm)
  have : LocallyOfFiniteType (pullback.snd T.hom j) := inferInstance
  have : IsIntegralHom (pullback.snd T.hom j) := inferInstance
  have := LocallyOfFiniteType.jacobsonSpace (pullback.snd T.hom j)
  obtain ⟨c, hcz, hcc⟩ := nonempty_inter_closedPoints (X := (pullback T.hom j : Scheme))
    (Z := closure {z}) ⟨z, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  have hzc : z = c := GlobalTheory.eq_of_specializes_of_isIntegralHom (pullback.snd T.hom j)
    (specializes_iff_mem_closure.2 hcz) (Subsingleton.elim _ _)
  subst hzc
  let s : Sp Kb ⟶ pullback T.hom j := pointOfClosedPoint (pullback.snd T.hom j) z hcc
  have hs : s ≫ pullback.snd T.hom j = 𝟙 _ := pointOfClosedPoint_comp (pullback.snd T.hom j) z hcc
  have hsz : ∀ a, s a = z := fun a => pointOfClosedPoint_apply (pullback.snd T.hom j) z hcc a
  let t : TF (R := R) Kb ⟶ T := Over.homMk (s ≫ pullback.fst T.hom j) (by
    show (s ≫ pullback.fst T.hom j) ≫ T.hom = j
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp])
  obtain ⟨c0, hc0⟩ := H t
  have hσ : IsClosedImmersion (σ c0).left := by
    have h1 : (σ c0).left ≫ T.hom = 𝟙 _ := Over.w (σ c0)
    have : IsClosedImmersion ((σ c0).left ≫ T.hom) := by rw [h1]; infer_instance
    exact IsClosedImmersion.of_comp (σ c0).left T.hom
  have hq'mem : q' ∈ Set.range (σ c0).left := by
    let pt : Sp Kb := IsLocalRing.closedPoint Kb
    refine ⟨(toUnit (TF (R := R) Kb)).left pt, ?_⟩
    have e1 : t.left pt = q' := by
      show pullback.fst T.hom j (s pt) = q'
      rw [hsz, hz1]
    rw [← e1, hc0]
    rfl
  have hqmem : q ∈ Set.range (σ c0).left :=
    hq'q.mem_closed (σ c0).left.isClosedEmbedding.isClosed_range hq'mem
  have : IsReduced (Sp K) := inferInstance
  obtain ⟨l, hl⟩ := GlobalTheory.AbelianSubgroupFinite.exists_lift_of_range_subset (T := Sp K) p.left (σ c0).left (by
    rintro _ ⟨(a : Sp K), rfl⟩
    rw [Subsingleton.elim a (IsLocalRing.closedPoint K)]
    exact hqmem)
  have hlx : l = x := by
    have h1 : (σ c0).left ≫ T.hom = 𝟙 _ := Over.w (σ c0)
    have h2 : p.left ≫ T.hom = x := Over.w p
    rw [← h2, ← hl, Category.assoc, h1, Category.comp_id]
  refine ⟨c0, Over.OverMorphism.ext ?_⟩
  rw [Over.comp_left, ← hl, hlx]
  congr 1

end GlobalTheory.Poinc.IntTerm

namespace GlobalTheory.Poinc.IntTerm

theorem exhausts_of_generic : ∀ (V : Type) [CommRing V] [IsDomain V] [IsNoetherianRing V]
    (P : PolAV (Sp V)) (N : ℕ), 1 ≤ N → ∀ (C : Type) (b : C → (𝟙_ (Over (Sp V)) ⟶ P.A)),
    (∀ c, b c ^ N = 1) →
    (∀ p : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ P.A, p ^ N = 1 → ∃ c, p = toUnit _ ≫ b c) →
    IntTerm.Exhausts P N b := by
  intro V _ _ _ P N hN C b hb H K _ _ x p hp
  obtain ⟨h1, h2, -⟩ := GlobalTheory.abelianSchemeLaws_all.1.mulN (Sp V) P N hN
  rw [Out.mulA, ← GrpTangent.mulN_eq_pow] at h1 h2
  haveI : IsFinite (torsion P.A N).hom :=
    MorphismProperty.of_isPullback (P := @IsFinite) (GrpTangent.isPullback_torsion P.A N) h1
  haveI : Flat (torsion P.A N).hom :=
    MorphismProperty.of_isPullback (P := @Flat) (GrpTangent.isPullback_torsion P.A N) h2
  haveI : Mono (torsion.ι P.A N) := inferInstanceAs (Mono (pullback.fst _ _))
  obtain ⟨hι, hu⟩ := GlobalTheory.LamF.torsion_universal P.A N
  choose σ hσ using fun c => hu _ (b c) (hb c)
  obtain ⟨t, ht⟩ := hu _ p hp
  obtain ⟨c, hc⟩ := exists_eq_section_of_finite_flat (torsion P.A N) σ (fun t' => by
      obtain ⟨c, hc⟩ := H (t' ≫ torsion.ι P.A N) (by rw [← comp_pow, hι, comp_one])
      exact ⟨c, by rw [← cancel_mono (torsion.ι P.A N), hc, Category.assoc, hσ]⟩) K x t
  exact ⟨c, by rw [← ht, hc, Category.assoc, hσ]⟩

end GlobalTheory.Poinc.IntTerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSectionsExhaustOfGenericGeometricStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionSections_exhaust_of_generic_geometric : ∀ (V : Type) [CommRing V] [IsDomain V] [IsNoetherianRing V] (P : PolAV (Sp V)) (N : ℕ), 1 ≤ N → ∀ (C : Type) (b : C → (𝟙_ (Over (Sp V)) ⟶ P.A)), (∀ c, b c ^ N = 1) → (∀ p : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ P.A, p ^ N = 1 → ∃ c, p = toUnit _ ≫ b c) → IntTerm.Exhausts P N b := by
  first | exact @GlobalTheory.Poinc.IntTerm.exhausts_of_generic | exact GlobalTheory.Poinc.IntTerm.exhausts_of_generic | (intros; apply GlobalTheory.Poinc.IntTerm.exhausts_of_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedMemberBaseChangeInjectiveLocalHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedMemberBaseChangeInjectiveLocalHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep.MemBC

open GlobalTheory.ArcPull GlobalTheory.Poinc.Sep.MemBC

theorem pt_comp (X₁ : GSet) (z₁ : X₁.M.Z) {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V']
    (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (j : V →+* V') (hj : Function.Injective j) :
    jK V' ≫ spMap (j.comp ev) ≫ X₁.M.Z.fromSpecStalk z₁ =
      spMap (fracMap hj) ≫ (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) := by
  have sq := fracMap_sq hj
  rw [Category.id_comp] at sq
  rw [spMap_comp, Category.assoc, ← Category.assoc (jK V'), sq]
  simp only [genMap, Category.assoc]

theorem regAt_comp (X₁ : GSet) (z₁ : X₁.M.Z) {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V']
    (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (j : V →+* V') (hj : Function.Injective j) (h : RegAt X₁ z₁ ev) :
    RegAt X₁ z₁ (j.comp ev) := by
  intro a ha
  rw [pt_comp X₁ z₁ ev j hj]
  convert h a ha using 2
  exact GlobalTheory.FlagBundle.spMap_comp_apply_field (fracMap hj) _ _ _

theorem yK_comp (X₁ : GSet) (z₁ : X₁.M.Z) {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V']
    (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (j : V →+* V') (hj : Function.Injective j) (yK : X₁.S.R →+* FractionRing V)
    (h : ∀ a : X₁.S.R, yK a = X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a) (a : X₁.S.R) :
    (fracMap hj).comp yK a = X₁.M.val (jK V' ≫ spMap (j.comp ev) ≫ X₁.M.Z.fromSpecStalk z₁) a := by
  rw [pt_comp X₁ z₁ ev j hj]
  exact (congrArg (fracMap hj) (h a)).trans (val_spMap_comp_field' X₁.M (fracMap hj) _ _).symm

theorem gMem_baseChange : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (j : V →+* V') (k : FractionRing V →+* FractionRing V'), IsCN V' → Function.Injective j → IsLocalHom j → (∀ v : V, k (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (j v)) → ∃ 𝔫 : GlobalTheory.GSep.GMem X₁ z₁ act V' (j.comp ev) X (fun i => j (t i)) δ, (∀ r, 𝔫.yK r = k (𝔪.yK r)) ∧ ∀ a mu, 𝔪.YY a mu → 𝔫.YY a mu := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 V' _ _ _ j kf hV' hj hl hkv
  have hV := 𝔪.cn
  have hkf : fracMap hj = kf :=
    IsLocalization.ringHom_ext (nonZeroDivisors V)
      (RingHom.ext fun v => by
        simp only [RingHom.comp_apply]
        exact (fracMap_algebraMap hj v).trans (hkv v).symm)
  have hAd : AdmBase V (maximalIdeal V) := ⟨hV.1, inferInstance, hV.2.1, hV.2.2.1⟩
  have hAd' : AdmBase V' (maximalIdeal V') := ⟨hV'.1, inferInstance, hV'.2.1, hV'.2.2.1⟩
  have hI : (maximalIdeal V).map j ≤ maximalIdeal V' := map_maximalIdeal_le j
  obtain ⟨D', hD, A', gA, U', hPU, hgA, htA, hrel⟩ := exists_pull_gen hAd hAd' j hj hI 𝔪.semi 𝔪.U
  have hwl : LBIso A'.L (X₁.ρ.P.L.pull (gA ≫ 𝔪.φ)) :=
    LBIso.trans A'.isLB (pull_isLB 𝔪.A.isLB _) (pull_isLB X₁.ρ.P.isLB _) htA (lbIso_pull_comp ⟨𝔪.wl, 𝔪.wl_gen⟩ gA)
  obtain ⟨wl, hwl⟩ := hwl
  haveI := 𝔪.loc
  have hlev : 1 ≤ X₁.S.r * X₁.S.N := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega))
  refine ⟨{
    cn := hV'
    loc := inferInstance
    reg := regAt_comp X₁ z₁ ev j hj 𝔪.reg
    yK := (fracMap hj).comp 𝔪.yK
    yK_eq := yK_comp X₁ z₁ ev j hj 𝔪.yK 𝔪.yK_eq
    D := D'
    e₈ := 𝔪.e₈.trans hD.xe.symm
    G := (Over.pullback (specOf j)).obj 𝔪.G
    semi := IsSemiAbelian.pullback _ _ 𝔪.semi
    A := A'
    U := U'
    φ := gA ≫ 𝔪.φ
    cart := (hgA.comp 𝔪.cart).congr (by rw [spMap_comp]) rfl
    wl := wl
    wl_gen := hwl
    equiv := fun a => ?_
    psi := fun mu => ?_ }, fun r => ?_, ?_⟩
  · obtain ⟨E, hE1, hE2⟩ := 𝔪.equiv a
    have := E.homG
    obtain ⟨E', h1, h2, -⟩ := EndBaseChange.exists_end hD hPU E ((Over.pullback (specOf j)).map E.aG)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
    refine ⟨E', ?_, fun mu => ?_⟩
    · rw [← Category.assoc, aA_comm j hj 𝔪.U.toUnifPre U'.toUnifPre gA hgA hrel E E' h1, Category.assoc, hE1,
        Category.assoc]
    · apply hD.xe.injective
      simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply, h2, hE2]
  · obtain ⟨u, hu⟩ := 𝔪.psi mu
    have hr : Formalism.L2.Pj.PsiCoord 𝔪.D.toPre (hD.xe (hD.xe.symm (𝔪.e₈ mu))) (u * t mu) := by
      rw [AddEquiv.apply_symm_apply]; exact hu
    obtain ⟨u', hu'⟩ := GlobalTheory.PelCoordPull.psiCoord_pull hD _ _ hr
    refine ⟨u' * Units.map j.toMonoidHom u, ?_⟩
    convert hu' using 1
    · exact AddEquiv.trans_apply _ _ _
    · rw [map_mul]
      simp [_root_.mul_assoc]
  · show (fracMap hj).comp 𝔪.yK r = kf (𝔪.yK r)
    rw [hkf]; rfl
  · rintro a mu ⟨p, x, hpy, hqx, hxφ⟩
    obtain ⟨p', x', σ, hσ, hp'y, hq', hx'⟩ := yy_pull' hV hV' j hj hl 𝔪.semi 𝔪.U D' hD A' gA U' hPU hgA hrel _ hlev p x hqx
    refine ⟨p', x', ?_, hq', ?_⟩
    · show p'.y = (𝔪.e₈.trans hD.xe.symm) mu
      rw [AddEquiv.trans_apply, hp'y, hpy]
    · show x'.left ≫ gA ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V') (AlgebraicClosure (FractionRing V'))).comp
          ((fracMap hj).comp 𝔪.yK)) ≫ (X₁.ρ.pt a).left
      rw [← Category.assoc, hx', Category.assoc, hxφ, ← Category.assoc, ← spMap_comp]
      congr 2
      rw [← RingHom.comp_assoc, hσ, RingHom.comp_assoc]

end GlobalTheory.GSep.MemBC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedMemberBaseChangeInjectiveLocalHomStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedMember_baseChange_injective_localHom : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (j : V →+* V') (k : FractionRing V →+* FractionRing V'), IsCN V' → Function.Injective j → IsLocalHom j → (∀ v : V, k (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (j v)) → ∃ 𝔫 : GlobalTheory.GSep.GMem X₁ z₁ act V' (j.comp ev) X (fun i => j (t i)) δ, (∀ r, 𝔫.yK r = k (𝔪.yK r)) ∧ ∀ a mu, 𝔪.YY a mu → 𝔫.YY a mu := by
  first | exact @GlobalTheory.GSep.MemBC.gMem_baseChange | exact GlobalTheory.GSep.MemBC.gMem_baseChange | (intros; apply GlobalTheory.GSep.MemBC.gMem_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigTorsFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

namespace GlobalTheory.GSep.TwistTranslate
open GlobalTheory.UT.CoefBasic GlobalTheory.AdicSum GlobalTheory.Poinc.Tors.AnyField GlobalTheory.Poinc.Tors.ValPair GlobalTheory.Poinc.Tors.Translate

variable {I : Type} {X₁ : GlobalTheory.GSep.GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}

theorem x_add (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A))
    (hx : ∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) (a τ : X₁.S.Gam)
    (xτ : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) (hτ : xτ.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) :
    x (a + τ) = x a * xτ := by
  let U : Over.mk ((TFK (R := V) (FractionRing V)).hom ≫ spMap 𝔪.yK) ⟶ baseOver (Sp X₁.S.R) :=
    Over.homMk (spMap 𝔪.yK) (by
      show spMap 𝔪.yK ≫ 𝟙 _ = _
      rw [Category.comp_id]
      change _ = Spec.map (𝟙 _) ≫ _
      rw [Spec.map_id, Category.id_comp])
  have key := 𝔪.cart.2 (TFK (R := V) (FractionRing V)) (x a) xτ (U ≫ X₁.ρ.pt a) (U ≫ X₁.ρ.pt τ)
    (hx a).symm hτ.symm
  rw [← MonObj.comp_mul, ← X₁.ρ.pt_add] at key
  apply Over.OverMorphism.ext
  refine 𝔪.cart.1.hom_ext ?_ ?_
  · rw [hx (a + τ), ← key]; rfl
  · rw [Over.w, Over.w]

theorem eq_yK_zeta_pow (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (u : FractionRing V)
    (hu : u ^ ((X₁.S.r * X₁.S.N) ^ 2) = 1) : ∃ e : ℕ, u = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) := by
  haveI : CharZero V := 𝔪.cn.2.2.2
  haveI : CharZero (FractionRing V) := IsFractionRing.charZero V
  set k := (X₁.S.r * X₁.S.N) ^ 2 with hk
  have hkpos : 0 < k := by
    have h1 := X₁.S.r_pos; have h2 := X₁.S.N_ge
    positivity
  have hinj : Function.Injective (algebraMap X₁.o₁ X₁.S.R) := by
    intro a b hab
    apply X₁.ar.inj
    have := congrArg (fun x : X₁.S.R => (x : X₁.Ω₁)) hab
    simpa using this
  have hR : IsPrimitiveRoot (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ) k := X₁.S.prim.map_of_injective hinj
  have hroot : (Polynomial.cyclotomic k (FractionRing V)).IsRoot (𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ)) := by
    have h := (hR.isRoot_cyclotomic hkpos).map (f := 𝔪.yK)
    rwa [Polynomial.map_cyclotomic] at h
  haveI : NeZero (k : FractionRing V) := ⟨by exact_mod_cast hkpos.ne'⟩
  have hK : IsPrimitiveRoot (𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ)) k :=
    (Polynomial.isRoot_cyclotomic_iff).1 hroot
  obtain ⟨e, -, he⟩ := hK.eq_pow_of_pow_eq_one hu
  exact ⟨e, by rw [map_pow, map_pow, he]⟩

theorem exists_rig_torsFrame (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ)
    (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a))
    (hx : ∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left)
    (hfr : ∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
        val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) :
    ∃ ρA : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A)), ρA.IsGen ∧ ∀ a, IsTorsFrame 𝔪.A ρA (X₁.S.r * X₁.S.N) (x a) (fr a) := by
  have gp := 𝔪.cart
  have hw := 𝔪.wl_gen
  obtain ⟨rig', hrig', Hr⟩ := GlobalTheory.ConstFam.exists_gen_through (K := PUnit) (φ' := fun _ => eSec 𝔪.A.A)
    (φ := fun _ => eSec X₁.ρ.P.A) (ε := fun _ => 1) (h := spMap 𝔪.yK) hw X₁.ρ.P.isLB 𝔪.A.isLB
    (fun _ => PolBaseChange.eSec_comm gp) X₁.ρ.rig X₁.ρ.rig_gen
  have hr : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over _)).left) (z : Z) J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      GlobalTheory.FrameMove.rval X₁.ρ.rig (r ≫ spMap 𝔪.yK) z J =
        GlobalTheory.ConstFam.wVal 𝔪.wl z J J' (r ≫ eSec 𝔪.A.A) * GlobalTheory.FrameMove.rval rig' r z J' :=
    fun Z r z J J' hJ hJ' =>
      (Hr Z r z J J' hJ hJ').trans (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _)))
  refine ⟨rig', hrig', fun a => ?_⟩
  exact GlobalTheory.FrameMove.isTorsFrame_move gp hw hr (hx a) (X₁.ρ.fr_tors a) (hfr a).1
    (fun z J J' hJ hJ' => ((hfr a).2 z J J' hJ hJ').symm)

theorem over_translate (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (w₀ : W0 𝔪.U.toUnifPre) (hw₀ : w₀.IsGen)
    (ρA : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A))) (hρ : ρA.IsGen) (x₁ : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)
    (e₁ : FrAt x₁) (he₁ : IsTorsFrame 𝔪.A ρA (X₁.S.r * X₁.S.N) x₁ e₁)
    (g₁ : GtPtF 𝔪.D.toPre (FractionRing V)) (w₁ : Frm 𝔪.D.toPre (FractionRing V) 1 g₁.b)
    (hg₁ : ∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g₁ o ∧ o.IsZero) (hw₁ : w₁.IsGen) (H₁ : 𝔪.Over' w₀ g₁ w₁ x₁ e₁)
    (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ) (hχ : χ ^ (X₁.S.r * X₁.S.N) = 1)
    (g₀ : GtPtF 𝔪.D.toPre (FractionRing V)) (ht : IsTor χ g₀)
    (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)
    (_ : p.y = 0) (hp : p.g = g₀) (hx : QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x)
    (g₂ : GtPtF 𝔪.D.toPre (FractionRing V)) (hadd : g₁.IsAdd g₀ g₂) (w₂ : Frm 𝔪.D.toPre (FractionRing V) 1 g₂.b)
    (hww : ∀ z J, Good 𝔪.D.toPre.P.L z J → val w₂ (𝟙 _) z J = val w₁ (𝟙 _) z J)
    (x₂ : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) (hx₂ : x₂ = x₁ * x) :
    ∃ e₂ : FrAt x₂, IsTorsFrame 𝔪.A ρA (X₁.S.r * X₁.S.N) x₂ e₂ ∧ 𝔪.Over' w₀ g₂ w₂ x₂ e₂ := by
  obtain ⟨o, ho, _⟩ := hg₁
  subst hp
  have hB : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  haveI := 𝔪.cn.2.2.2
  have hn : 1 ≤ X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (lt_of_lt_of_le two_pos X₁.S.N_ge)
  obtain ⟨w, hw, vw⟩ := exists_gen 𝔪.D.toPre.P.isLB (φ' := DegPre.lineφ 𝔪.D.toPre _ g₂.b) (ε' := DegPre.lineε 1)
    (fun U _ h => by rw [(ThetaAverage.val_translate ht hadd).1]) w₁ hw₁
  have vw' := fun z J hJ => vw _ (𝟙 _) z J hJ
  obtain ⟨e₂, he₂, H₂⟩ := exists_liesOver hB 𝔪.semi 𝔪.U hw₀ hn hw₁ he₁.2.1 H₁ hχ p ht hx hadd hw vw' hx₂
  refine ⟨e₂, isTorsFrame_of_liesOver hB 𝔪.semi 𝔪.U hw₀ hρ hn ho hw₁ he₁ H₁ hχ ht hadd hw vw' ?_ he₂ H₂,
    fun k hk wk e => H₂ k hk wk fun z J hJ => by rw [e z J hJ, hww z J hJ, vw' z J hJ]⟩
  rw [hx₂, mul_pow, he₁.1, (hx w₀ hw₀).1, _root_.mul_one]


attribute [local instance] GlobalTheory.TorusExt.gtGroup in
theorem twistSum_translate : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : X → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ, χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → ∃ e : ℕ, SumF (maximalIdeal V) (FractionRing V) (fun mu : X => ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) * (algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩)) (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) * 𝔪.yK ⟨X₁.S.th (lab c + τ), X₁.S.th_mem (lab c + τ)⟩) := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 x₀ C lab _ T hT c τ _ χ hχ hyp
  obtain ⟨x, fr, th, w₀, s, g', w, hx, hfr, hth, hw₀, hs, hc, hTc⟩ := hT
  obtain ⟨ρA, hρA, htors⟩ := exists_rig_torsFrame 𝔪 x fr hx hfr
  have hg₀ : IsTor χ (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) :=
    (isTor_iff _ _).2 (GlobalTheory.TorusExt.isTorusPtF_torusPt χ)
  obtain ⟨p, xτ, hpy, hpg, hq, hxτ⟩ := hyp _ hg₀
  have hadd := (GlobalTheory.TorusExt.isAdd_iff_eq (g' c) (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) _).2 rfl
  have hb := (GlobalTheory.UT.ThetaAverage.val_translate hg₀ hadd).1
  obtain ⟨w'', hw''g, hw''v⟩ : ∃ w'' : Frm 𝔪.D.toPre (FractionRing V) 1 (g' c + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)).b,
      w''.IsGen ∧ ∀ z J, val w'' (𝟙 _) z J = val (w c) (𝟙 _) z J := by
    revert hb
    generalize (g' c + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)).b = b
    rintro rfl
    exact ⟨w c, (hc c).2.1, fun _ _ => rfl⟩
  obtain ⟨e₂, he₂, hov⟩ := over_translate 𝔪 w₀ hw₀ ρA hρA (x (lab c)) (fr (lab c)) (htors _)
    (g' c) (w c) (hc c).1 (hc c).2.1 (hc c).2.2 χ hχ _ hg₀ p xτ hpy hpg hq _ hadd w'' (fun z J _ => hw''v z J)
    (x (lab c + τ)) (x_add 𝔪 x hx (lab c) τ xτ hxτ)
  obtain ⟨u, hu, hval⟩ := GlobalTheory.Poinc.TorsRatio.valAt_torsFrame_ratio V 𝔪.A ρA hρA _
    (Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)) _ _ _
    (htors (lab c + τ)) he₂ th _ (hth (lab c + τ))
  have hsum := hov 1 le_rfl w'' (fun z J _ => (pow_one _).symm) hw''g th s _ hs hval
  obtain ⟨e, he⟩ := eq_yK_zeta_pow 𝔪 u hu
  refine ⟨e, ?_⟩
  rw [← he]
  have hco : ∀ χ', coef s (g' c + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) w'' χ' =
      ((χ (Multiplicative.ofAdd χ') : (FractionRing V)ˣ) : FractionRing V) * coef s (g' c) (w c) χ' := fun χ' => by
    rw [GlobalTheory.UT.ThetaAverage.coef_translate hg₀ hadd (hc c).2.1 (c := 1) (fun z J _ => by rw [hw''v, map_one, _root_.one_mul]) s χ',
      _root_.one_mul]
  have hA := admissibleBase_of_completeNormalLocalCharZero 𝔪.cn
  have key := ((GlobalTheory.AdicSum.sumF_calculus V _ hA (FractionRing V) _
    (coef s (g' c + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) w'') 0 _ 0).2.2 X 𝔪.e₈
    𝔪.e₈.injective (fun j hj => absurd ⟨𝔪.e₈.symm j, 𝔪.e₈.apply_symm_apply j⟩ hj)).2 hsum
  convert key using 2 with mu
  simp only [Function.comp_apply, hco, hTc]

end GlobalTheory.GSep.TwistTranslate
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenPartClassifiedMonomialBoundaryFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenPartClassifiedMonomialBoundaryFamily
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.OpenPart

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem pow_eq_one_of_left_eq {S T : Scheme.{0}} {G : Over S} [GrpObj G] {a b : T ⟶ S} (h : a = b)
    (u : Over.mk a ⟶ G) (v : Over.mk b ⟶ G) (huv : u.left = v.left) {n : ℕ} (hu : u ^ n = 1) : v ^ n = 1 := by
  subst h
  obtain rfl : u = v := Over.OverMorphism.ext huv
  exact hu

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem torsRat_of_point {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E))
    {A : Type} [CommRing A] [IsDomain A] {K₀ : Type} [Field K₀] (gA : A →+* K₀) (ρ : K₀ →+* FractionRing A)
    (hρ : ρ.comp gA = algebraMap A (FractionRing A)) (tO : SAB H (Sp A)) (tK : SAB H (Sp K₀))
    (k : SABMap tK tO (spMap gA)) (y : Sp K₀ ⟶ Xo.XF c) (mK : SABMap tK Xo.univ.t (y ≫ pullback.fst _ _)) :
    GlobalTheory.TChart.TorsRat tO.G l.M' := by
  intro K _ _ κ x hx
  let κ' : K₀ →+* K := κ.comp ρ
  have e₀ : spMap κ' ≫ spMap gA = spMap κ ≫ jK A := by
    rw [spMap_comp', spMap_comp']
    show spMap (κ.comp (ρ.comp gA)) = _
    rw [hρ]
  have hw : x.left ≫ tO.G.hom = spMap κ' ≫ spMap gA := (Over.w x).trans e₀.symm
  let xK : Over.mk (spMap κ') ⟶ tK.G :=
    Over.homMk (k.cart.1.lift x.left (spMap κ') hw) (k.cart.1.lift_snd _ _ _)
  have hxK : xK ^ l.M' = 1 := by
    have hpush : pushHom k.cart (Over.mk (spMap κ')) xK ^ l.M' = 1 :=
      pow_eq_one_of_left_eq e₀.symm x _ (k.cart.1.lift_fst _ _ _).symm hx
    apply (fun (u v : Over.mk (spMap κ') ⟶ tK.G) (e : pushHom k.cart (Over.mk (spMap κ')) u = pushHom k.cart (Over.mk (spMap κ')) v) =>
      Over.OverMorphism.ext (k.cart.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])))
    rw [map_pow, hpush, map_one]
  let x' := pushHom mK.cart (Over.mk (spMap κ')) xK
  have hx' : x' ^ l.M' = 1 := by rw [← map_pow, hxK, map_one]
  obtain ⟨x₀, -, hx₀⟩ := GlobalTheory.T.universalAbelianScheme_torsion_rational_fieldPoint Xo c φ K₀ K κ' y x' hx'
  have w₀ : x₀.left ≫ Xo.univ.t.G.hom = 𝟙 _ ≫ (y ≫ pullback.fst _ _) := by
    rw [Category.id_comp]; exact Over.w x₀
  let s₀ := mK.cart.1.lift x₀.left (𝟙 _) w₀
  have hs₀ : s₀ ≫ tK.G.hom = 𝟙 _ := mK.cart.1.lift_snd _ _ _
  have hK : xK.left = spMap κ' ≫ s₀ := by
    apply mK.cart.1.hom_ext
    · rw [Category.assoc, mK.cart.1.lift_fst]
      exact hx₀
    · rw [Category.assoc, hs₀]
      erw [Category.comp_id]
      exact k.cart.1.lift_snd _ _ _
  have hover : (spMap ρ ≫ s₀ ≫ k.φ) ≫ tO.G.hom = jK A := by
    rw [Category.assoc, Category.assoc, k.cart.1.w, ← Category.assoc s₀, hs₀, Category.id_comp, spMap_comp', hρ]
  refine ⟨Over.homMk (spMap ρ ≫ s₀ ≫ k.φ) hover, ?_⟩
  show x.left = spMap κ ≫ spMap ρ ≫ s₀ ≫ k.φ
  have e₁ : spMap κ ≫ spMap ρ = spMap κ' := spMap_comp' _ _
  calc x.left = xK.left ≫ k.φ := (k.cart.1.lift_fst _ _ _).symm
    _ = (spMap κ' ≫ s₀) ≫ k.φ := by rw [hK]
    _ = spMap κ ≫ spMap ρ ≫ s₀ ≫ k.φ := by rw [← e₁]; simp only [Category.assoc]

end GlobalTheory.UCanon.OpenPart

namespace GlobalTheory.UCanon.OpenPart

theorem ring_facts {R : Type} [CommRing R] [IsDomain R] (f : R) (hf : f ≠ 0) (A : Type) [CommRing A] [IsDomain A]
    [Algebra R A] [IsLocalization.Away f A] :
    ∃ (gA : A →+* FractionRing R) (ρ : FractionRing R →+* FractionRing A),
      gA.comp (algebraMap R A) = algebraMap R (FractionRing R) ∧ ρ.comp gA = algebraMap A (FractionRing A) ∧
      ∀ g : A →+* FractionRing R, g.comp (algebraMap R A) = algebraMap R (FractionRing R) → g = gA := by
  have hle : Submonoid.powers f ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  have hu : IsUnit (algebraMap R (FractionRing R) f) :=
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hf)
  have hgA : (IsLocalization.Away.lift f hu : A →+* FractionRing R).comp (algebraMap R A) = algebraMap R (FractionRing R) :=
    IsLocalization.Away.lift_comp _ hu
  have hinj : Function.Injective ((algebraMap A (FractionRing A)).comp (algebraMap R A)) := by
    rw [RingHom.coe_comp]
    exact (IsFractionRing.injective A (FractionRing A)).comp (IsLocalization.injective A hle)
  refine ⟨IsLocalization.Away.lift f hu, IsFractionRing.lift (K := FractionRing R) hinj, hgA, ?_, fun g hg =>
    IsLocalization.ringHom_ext (Submonoid.powers f) (hg.trans hgA.symm)⟩
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  rw [RingHom.comp_assoc, hgA]
  exact RingHom.ext fun r => by rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap, RingHom.comp_apply]

end GlobalTheory.UCanon.OpenPart

namespace GlobalTheory.UCanon.OpenPart

theorem openCls : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ C : MonoFam Xo c φ R, OpenCls C := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ hR C
  obtain ⟨⟨hN, -, hIC, -⟩, -⟩ := id hR
  have hf0 : (∏ i, C.s i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => C.s_ne_zero i
  have hle : Submonoid.powers (∏ i, C.s i) ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hf0
  haveI : IsDomain (Localization.Away (∏ i, C.s i)) := IsLocalization.isDomain_localization hle
  haveI : IsNoetherianRing (Localization.Away (∏ i, C.s i)) :=
    IsLocalization.isNoetherianRing (Submonoid.powers (∏ i, C.s i)) _ hN
  haveI : IsIntegrallyClosed (Localization.Away (∏ i, C.s i)) :=
    isIntegrallyClosed_of_isLocalization _ (Submonoid.powers (∏ i, C.s i)) hle

  let aR := algebraMap R (Localization.Away (∏ i, C.s i))
  let incl := (IntermediateField.inclusion c.le).toRingHom
  obtain ⟨gA, ρ, hgA, hρ, hgU⟩ := ring_facts _ hf0 (Localization.Away (∏ i, C.s i))
  have eR : spMap gA ≫ spMap aR = jK R := by rw [spMap_comp', hgA]

  obtain ⟨tO, ⟨mO⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap aR) C.t
  obtain ⟨hprop, hamp, hkt⟩ := GlobalTheory.T.isProper_relAmple_kTriv_of_trivialisations_generate R hR C.t C.P (∏ i, C.s i)
    (fun y => C.mono.psiUnitOn y fun p hp => hp) tO mO

  let s' : Sp (FractionRing R) ⟶ Sp (KA l) := (C.y ≫ pullback.fst _ _) ≫ Xo.s
  obtain ⟨oK, ⟨mK⟩⟩ := (GlobalTheory.UCanon.obj_pull_comp_cancel (D := Dw) (l := l)).1 Xo.s Xo.univ (C.y ≫ pullback.fst _ _) s' rfl
  obtain ⟨t', ⟨m₁⟩, ⟨m₂⟩⟩ := C.gen
  obtain ⟨k₁⟩ := GlobalTheory.TraitOrder.cancel (Category.id_comp _) m₂ mK.toSABMap
  obtain ⟨k₂⟩ := GlobalTheory.TraitOrder.comp (Category.id_comp _) m₁ k₁
  obtain ⟨k₃⟩ := GlobalTheory.TraitOrder.cancel eR mO k₂
  have htors := torsRat_of_point Xo c φ gA ρ hρ tO oK.t k₃ C.y mK.toSABMap
  let b' : c.F →+* Localization.Away (∏ i, C.s i) := aR.comp C.b
  have hs' : s' = spMap gA ≫ spMap (b'.comp incl) := by
    show (C.y ≫ pullback.fst _ _) ≫ Xo.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, C.y_over, ← eR]
    simp only [Category.assoc, spMap_comp']
  obtain ⟨o, ho, ⟨mo⟩⟩ := GlobalTheory.T.exists_unitaryModuliObject_spread_normal_domain Dw l c _ b' tO hprop hamp hkt htors (FractionRing R) gA s' oK hs' k₃
  obtain ⟨fX, ⟨hfs, ⟨mf⟩⟩, -⟩ := Xo.rep (Sp (Localization.Away (∏ i, C.s i))) (spMap (b'.comp incl)) inferInstance o
  have hfs' : fX ≫ Xo.s = spMap b' ≫ spMap incl := hfs.trans (spMap_comp' _ _).symm
  subst ho
  refine ⟨pullback.lift fX (spMap b') hfs', o.t, ⟨mO⟩, ?_, fun g hg => ?_⟩
  · rw [pullback.lift_fst]
    exact ⟨mf.toSABMap⟩
  obtain ⟨g₀, rfl⟩ := Spec.map_surjective g
  have h₁ : CommRingCat.ofHom (algebraMap R (Localization.Away (∏ i, C.s i))) ≫ g₀ =
      CommRingCat.ofHom (algebraMap R (FractionRing R)) := Spec.map_injective (by rw [Spec.map_comp]; exact hg)
  have hg₀ : g₀ = CommRingCat.ofHom gA := by
    have e := hgU g₀.hom (by
      have := congrArg CommRingCat.Hom.hom h₁
      simpa using this)
    rw [← e]
    rfl
  subst hg₀
  obtain ⟨_, _, huK⟩ := Xo.rep (Sp (FractionRing R)) s' inferInstance oK
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst]
    obtain ⟨n₁, -⟩ := ((GlobalTheory.UCanon.obj_pull_comp_cancel (D := Dw) (l := l)).2 Xo.s (spMap (b'.comp incl)) s' Xo.univ o oK
      fX (spMap gA) mf).1 mo
    exact (huK _ ⟨by rw [Category.assoc, hfs]; exact hs'.symm, ⟨n₁⟩⟩).trans (huK _ ⟨rfl, ⟨mK⟩⟩).symm
  · rw [Category.assoc, pullback.lift_snd, C.y_over, ← eR, Category.assoc, spMap_comp' C.b aR]

end GlobalTheory.UCanon.OpenPart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenPartClassifiedMonomialBoundaryFamilyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.openPart_classified_monomialBoundaryFamily : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ C : MonoFam Xo c φ R, OpenCls C := by
  first | exact @GlobalTheory.UCanon.OpenPart.openCls | exact GlobalTheory.UCanon.OpenPart.openCls | (intros; apply GlobalTheory.UCanon.OpenPart.openCls <;> assumption)
end
end
