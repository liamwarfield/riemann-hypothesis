module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimilitudeOfAutModLevelIdeal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspFormsDominantWeightFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFramedPointMoveUniversalTriple
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.PointwiseNormSectionEqFlagDomainNorm
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlagDomainModelsExponentsLevelM
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointsAllNormalisationsFamilyUnif
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArithmeticGroupCuspCentreLattice
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CmHostRootComplexEqPmSqrt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrMoveTransfer
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory.LevelActionLaws

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H}
  {l : Level H}

attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

theorem exists_levAut (hpq : 1 ≤ D.p + D.q) (Xo : Moduli D l) (g : Sim D)
    (hν : (l.A : ℤ) ∣ g.ν l.A - 1) : ∃ ρ : Xo.X ≅ Xo.X, Xo.LevAut g ρ := by
  have hsim := exists_obj_twist_by_similitude SimAlg.sim_group
  have hred : IsReduced Xo.X := by
    haveI := Xo.smooth
    exact (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ Xo.s
      (SmoothOfRelativeDimension.smooth D.dim _)).1
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨i, hi⟩ := (ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ Xo.univ Xo.univ).1
  obtain ⟨g', hg'⟩ := (SimAlg.sim_group E H D hpq).2.2.2 g
  have hν' : (l.A : ℤ) ∣ g'.ν l.A - 1 := by
    have h₁ := (hg' l.A l.A_pos).2
    have : g'.ν l.A - 1 = (g.ν l.A * g'.ν l.A - 1) - (g.ν l.A - 1) * g'.ν l.A := by ring
    rw [this]
    exact dvd_sub h₁ (hν.mul_right _)
  obtain ⟨o₁, m₁, a₁, b₁⟩ := hsim E H D l _ _ _ _ Xo.univ g hpq hν
  obtain ⟨o₂, m₂, a₂, b₂⟩ := hsim E H D l _ _ _ _ Xo.univ g' hpq hν'
  obtain ⟨f, hf⟩ := Moduli.LevelAction.exists_twists Xo g hred i.toSABMap hi o₁ m₁ a₁ b₁
  obtain ⟨f', hf'⟩ := Moduli.LevelAction.exists_twists Xo g' hred i.toSABMap hi o₂ m₂ a₂ b₂
  exact ⟨⟨f, f', Moduli.LevelAction.comp_eq_id_of_twists Xo hred i hf hf' (fun a => ((hg' _ hM).1 a).2)
      (fun a => ((hg' _ l.A_pos).1 a).2),
    Moduli.LevelAction.comp_eq_id_of_twists Xo hred i hf' hf (fun a => ((hg' _ hM).1 a).1)
      (fun a => ((hg' _ l.A_pos).1 a).1)⟩, hf⟩

theorem eta_congr (Xo : Moduli D l) {a b : D.La} (h : a - b ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) :
    Xo.univ.eta a = Xo.univ.eta b := by
  have e : a = (a - b) + b := by abel
  rw [e, Xo.univ.eta_add, Xo.univ.eta_ker _ h, one_mul]

theorem etaA_congr (Xo : Moduli D l) {a b : D.La} (h : D.ModN l.A (a - b)) :
    Xo.univ.etaA a = Xo.univ.etaA b := by
  obtain ⟨x, hx⟩ := h
  have e : a = (a - b) + b := by abel
  rw [e, Xo.univ.etaA_add, hx, Xo.univ.etaA_ker, one_mul]

theorem exists_sim (hpq : 1 ≤ D.p + D.q) (hA : l.A.Coprime l.M) (γ : LaMod D l ≃ₗ[𝓞 E] LaMod D l) :
    ∃ g : Sim D, (∀ a, g.f l.M a - liftLa γ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) ∧
      (∀ a, D.ModN l.A (g.f l.A a - a)) ∧ (l.A : ℤ) ∣ g.ν l.A - 1 := by
  refine GlobalTheory.exists_sim_of_aut_mod E H D l l.A (liftLa γ) hpq l.A_pos hA fun x hx => ?_
  have h := liftLa_spec γ x
  rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 hx] at h
  have h2 := γ.map_eq_zero_iff.1 h.symm
  exact (Submodule.Quotient.mk_eq_zero _).1 h2

theorem exists_move (hpq : 1 ≤ D.p + D.q) (hA : l.A.Coprime l.M) (Xo : Moduli D l)
    (γ : LaMod D l ≃ₗ[𝓞 E] LaMod D l) :
    ∃ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), IsIso ρ ∧
      IsLevMove ρ ν (liftLa γ) LinearMap.id := by
  obtain ⟨g, h1, h2, h3⟩ := exists_sim hpq hA γ
  obtain ⟨ρ, hs, ν, hM, hAA⟩ := exists_levAut hpq Xo g h3
  refine ⟨ρ.hom, ν, inferInstance, hs, fun a => ?_, fun a => ?_⟩
  · rw [← eta_congr Xo (h1 a)]; exact hM a
  · have e := hAA a
    rw [etaA_congr Xo (h2 a)] at e
    exact e

theorem move_unique (hpq : 1 ≤ D.p + D.q) (hA : l.A.Coprime l.M) (Xo : Moduli D l) (c : Coeff l)
    (γ : LaMod D l ≃ₗ[𝓞 E] LaMod D l) {ρ ρ' : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ}
    {ν' : SABMap Xo.univ.t Xo.univ.t ρ'} (i : IsIso ρ) (i' : IsIso ρ')
    (h : IsLevMove ρ ν (liftLa γ) LinearMap.id) (h' : IsLevMove ρ' ν' (liftLa γ) LinearMap.id) :
    ρ = ρ' ∧ ν.φ = ν'.φ :=
  GlobalTheory.T.levelMove_moduli_unique_universalTriple E H D l Xo c ρ ρ' ν ν' _ _ _ _ hpq (fun a => by simp) (fun a => ⟨0, by simp⟩) i i' h h'
    (exists_sim hpq hA γ)

theorem frMove_transfer (hpq : 1 ≤ D.p + D.q) (hA : l.A.Coprime l.M) (Xo : Moduli D l) (c : Coeff l)
    (γ : LaMod D l ≃ₗ[𝓞 E] LaMod D l) {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ} (i : IsIso ρ)
    (h : IsLevMove ρ ν (liftLa γ) LinearMap.id) {S : Type} [CommRing S] [Algebra c.F S] {y y' : FrPt Xo c S}
    (hy : levR (liftLa γ, LinearMap.id) y y') : FrMove ρ ν y y' := by
  obtain ⟨ρ', ν', i', h', hm⟩ := hy
  obtain ⟨rfl, e⟩ := move_unique hpq hA Xo c γ i i' h h'
  obtain ⟨⟨w, hw⟩, hu⟩ := GlobalTheory.T.existsUnique_framedPoint_move_universalTriple E H D l Xo c ρ ν h.1 S y
  rwa [← hu w y' ν' e.symm hw hm]

theorem liftLa_one_sub (a : D.La) :
    liftLa (1 : LaMod D l ≃ₗ[𝓞 E] LaMod D l) a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  rw [← Submodule.Quotient.eq]
  exact liftLa_spec 1 a

theorem liftLa_mul_sub (γ δ : LaMod D l ≃ₗ[𝓞 E] LaMod D l) (a : D.La) :
    liftLa (γ * δ) a - liftLa γ (liftLa δ a) ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  rw [← Submodule.Quotient.eq]
  have h1 := liftLa_spec (γ * δ) a
  have h2 := liftLa_spec γ (liftLa δ a)
  rw [liftLa_spec δ a] at h2
  exact h1.trans h2.symm

end GlobalTheory.LevelActionLaws
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefficientFieldAlgClosedInFunctionFieldsOfPerio
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefficientFieldAlgClosedInFunctionFieldsOfPerio
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat.FixedConst

open Polynomial

theorem exists_section_of_isIntegral {Y : Scheme.{0}} [GlobalTheory.IsNormalScheme Y] [IsIntegral Y] (p : Γ(Y, ⊤)[X])
    (hp : p.Monic) (r : Y.residueField (genericPoint Y))
    (hr : p.eval₂ (Y.evaluation ⊤ (genericPoint Y) trivial).hom r = 0) :
    ∃ s : Γ(Y, ⊤), (Y.evaluation ⊤ (genericPoint Y) trivial).hom s = r ∧ p.eval s = 0 := by
  haveI : Nonempty (⊤ : Y.Opens) := ⟨Nonempty.some inferInstance, trivial⟩
  obtain ⟨t, rfl⟩ := Y.residue_surjective (genericPoint Y) r
  let ρ : Y.functionField →+* Y.residueField (genericPoint Y) := (Y.residue (genericPoint Y)).hom
  have e : (Y.evaluation ⊤ (genericPoint Y) trivial).hom = ρ.comp (algebraMap Γ(Y, ⊤) Y.functionField) := rfl
  have ht : p.eval₂ (algebraMap Γ(Y, ⊤) Y.functionField) t = 0 := by
    apply ρ.injective
    rw [hom_eval₂, ← e, map_zero]
    exact hr
  obtain ⟨s, hs⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral (R := Γ(Y, ⊤)) (A := Y.functionField)
    (x := t) ⟨p, hp, ht⟩
  refine ⟨s, by rw [e, RingHom.comp_apply, hs], ?_⟩
  apply Y.germToFunctionField_injective ⊤
  rw [← hs, eval₂_at_apply] at ht
  exact ht.trans (map_zero _).symm

theorem exists_extension_zero {Y : Scheme.{0}} (V W : Y.Opens) (hU : V ⊔ W = ⊤) (hVW : Disjoint V W) (s : Γ(Y, V)) :
    ∃ f : Γ(Y, ⊤), Y.presheaf.map (homOfLE le_top).op f = s ∧
      Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op f = 0 := by
  have hs : ∀ T : Y.Opens, T = ⊥ → Subsingleton Γ(Y, T) := fun T hT ↦
    CommRingCat.subsingleton_of_isTerminal (Y.sheaf.isTerminalOfEqEmpty hT)
  obtain ⟨e, he, -⟩ := Y.sheaf.existsUnique_gluing' (fun b : Bool ↦ cond b V W) ⊤
    (fun b ↦ homOfLE le_top)
    (by rw [iSup_bool_eq]; exact hU.ge)
    (fun b ↦ match b with | true => s | false => (0 : Γ(Y, W))) (by
      rintro (_ | _) (_ | _)
      · rfl
      · exact (hs _ (hVW.symm.eq_bot)).elim _ _
      · exact (hs _ (hVW.eq_bot)).elim _ _
      · rfl)
  exact ⟨e, he true, he false⟩

theorem exists_section {Y : Scheme.{0}} [GlobalTheory.IsNormalScheme Y] [IsLocallyNoetherian Y] (Z : irreducibleComponents Y)
    (ξ : Y) (hξ : IsGenericPoint ξ Z.1) (p : Γ(Y, ⊤)[X]) (hp : p.Monic) (r : Y.residueField ξ)
    (hr : p.eval₂ (Y.evaluation ⊤ ξ trivial).hom r = 0) :
    ∃ f : Γ(Y, ⊤), (Y.evaluation ⊤ ξ trivial).hom f = r ∧ f * p.eval f = 0 := by
  let V : Y.Opens := IsNormalScheme.component Z
  let W : Y.Opens := ⟨Z.1ᶜ, (IsNormalScheme.isClosed_component Z).isOpen_compl⟩
  have hU : V ⊔ W = ⊤ := by
    refine le_antisymm le_top fun x _ ↦ ?_
    by_cases h : x ∈ Z.1
    exacts [Or.inl h, Or.inr h]
  have hVW : Disjoint V W := by
    rw [← TopologicalSpace.Opens.coe_disjoint]
    exact Set.disjoint_left.mpr fun x hx hx' ↦ hx' hx
  obtain rfl : V.ι (genericPoint V.toScheme) = ξ := by
    refine IsGenericPoint.eq ?_ hξ
    have h := (genericPoint_spec V.toScheme).image V.ι.continuous
    rwa [Set.image_univ, Scheme.Opens.range_ι, (IsNormalScheme.isClosed_component Z).closure_eq] at h
  let φ := (V.ι.residueFieldMap (genericPoint V.toScheme)).hom
  have e : ∀ f : Γ(Y, ⊤), φ ((Y.evaluation ⊤ (V.ι (genericPoint V.toScheme)) trivial).hom f) =
      (V.toScheme.evaluation ⊤ (genericPoint V.toScheme) trivial).hom (V.ι.appTop.hom f) := fun f =>
    Scheme.evaluation_naturality_apply V.ι (genericPoint V.toScheme) (V := ⊤) trivial f
  obtain ⟨s, hs, hps⟩ := exists_section_of_isIntegral (p.map V.ι.appTop.hom) (hp.map _) (φ r) (by
    have e' : φ.comp (Y.evaluation ⊤ (V.ι (genericPoint V.toScheme)) trivial).hom =
        (V.toScheme.evaluation ⊤ (genericPoint V.toScheme) trivial).hom.comp V.ι.appTop.hom := RingHom.ext e
    rw [eval₂_map, ← e', ← hom_eval₂, hr, map_zero])
  obtain ⟨f, h1, h0⟩ := exists_extension_zero V W hU hVW (V.topIso.hom.hom s)
  have e2 : V.ι.appTop ≫ V.topIso.hom = Y.presheaf.map (homOfLE le_top).op := by
    rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
    exact (Y.presheaf.map_comp _ _).symm
  have hf : V.ι.appTop.hom f = s := by
    apply V.topIso.commRingCatIsoToRingEquiv.injective
    exact (congrArg (fun g => g.hom f) e2).trans h1
  refine ⟨f, φ.injective (by rw [e, hf, hs]), ?_⟩
  refine Y.sheaf.eq_of_locally_eq₂ (homOfLE (le_top : V ≤ ⊤)) (homOfLE (le_top : W ≤ ⊤)) hU.ge _ _ ?_ ?_
  · change Y.presheaf.map (homOfLE le_top).op (f * p.eval f) = Y.presheaf.map (homOfLE le_top).op 0
    rw [← e2]
    change V.topIso.hom.hom (V.ι.appTop.hom _) = V.topIso.hom.hom (V.ι.appTop.hom _)
    rw [map_mul, ← eval₂_at_apply, hf, ← Polynomial.eval_map, hps, mul_zero, map_zero V.ι.appTop.hom]
  · change Y.presheaf.map (homOfLE le_top).op (f * p.eval f) = Y.presheaf.map (homOfLE le_top).op 0
    rw [map_mul, h0, zero_mul, map_zero]

theorem mem_range_of_fixed {K L : Type} [Field K] [Field L] [Countable L] [Algebra K L] [Algebra K ℂ] [CharZero K]
    (φ : L →ₐ[K] ℂ) {r : L} (hr : IsIntegral K r)
    (h : ∀ τ : ℂ ≃+* ℂ, (∀ x : K, τ (algebraMap K ℂ x) = algebraMap K ℂ x) → τ (φ r) = φ r) :
    r ∈ (algebraMap K L).range := by
  let M := IntermediateField.adjoin K {r}
  haveI : FiniteDimensional K M := IntermediateField.adjoin.finiteDimensional hr
  have key : ∀ ψ : M →ₐ[K] ℂ, ψ = φ.comp M.val := by
    intro ψ
    obtain ⟨τ, hτ⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq M (φ.comp M.val).toRingHom ψ.toRingHom
    refine IntermediateField.algHom_ext_of_eq_adjoin K (S := M) rfl fun x hx => ?_
    obtain rfl : x = r := hx
    refine (hτ _).symm.trans (h τ fun y => ?_)
    have := hτ (algebraMap K M y)
    simpa using this
  have hc : Module.finrank K M ≤ 1 := by
    rw [← AlgHom.card K M ℂ]
    exact Fintype.card_le_one_iff.2 fun a b => (key a).trans (key b).symm
  have h1 : Module.finrank K M = 1 := le_antisymm hc Module.finrank_pos
  exact IntermediateField.mem_bot.1 (IntermediateField.finrank_adjoin_simple_eq_one_iff.1 h1)

noncomputable def ev {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) : Γ(Y, ⊤) →+* ℂ :=
  (x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom

theorem valAt'_top {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (f : Γ(Y, ⊤)) : valAt' x ⊤ f = ev x f := by
  have h : ⊤ ≤ x ⁻¹ᵁ ⊤ := le_rfl
  rw [valAt', dite_eq_left h, valAt, ev]
  exact congrArg (fun g => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (g.hom f)) (x.appLE_eq_app (U := ⊤))

theorem ev_comp {Y Y' : Scheme.{0}} (x : Sp ℂ ⟶ Y) (g : Y ⟶ Y') (f : Γ(Y', ⊤)) :
    ev (x ≫ g) f = ev x (g.appTop.hom f) := by
  rw [ev, ev, Scheme.Hom.comp_appTop]; rfl

theorem ev_spec {R : CommRingCat.{0}} (j : R ⟶ CommRingCat.of ℂ) (a : Γ(Spec R, ⊤)) :
    ev (Spec.map j) a = j.hom ((Scheme.ΓSpecIso R).hom.hom a) := by
  rw [ev, Scheme.ΓSpecIso_naturality]; rfl

theorem ev_conj {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (τ : ℂ →+* ℂ) (f : Γ(Y, ⊤)) : ev (spMap τ ≫ x) f = τ (ev x f) := by
  rw [ev_comp, ev_spec]; rfl

theorem ΓSpecIso_fromSpecResidueField {Y : Scheme.{0}} (ξ : Y) :
    (Y.fromSpecResidueField ξ).appTop ≫ (Scheme.ΓSpecIso _).hom = Y.evaluation ⊤ ξ trivial := by
  rw [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
    Scheme.fromSpecStalk_appTop]
  simp [Scheme.evaluation]

theorem ev_residue {Y : Scheme.{0}} (ξ : Y) (φ : Y.residueField ξ →+* ℂ) (f : Γ(Y, ⊤)) :
    ev (Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecResidueField ξ) f = φ ((Y.evaluation ⊤ ξ trivial).hom f) := by
  rw [ev_comp, ev_spec, ← ΓSpecIso_fromSpecResidueField]; rfl

theorem emb_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) (σ : KA l →+* ℂ)
    (hσ : σ (baseKA l).ρ = H.rt0) (hA : l.A = 1) : σ = algebraMap (KA l) ℂ := by
  have h : σ.toRatAlgHom = (KA l).val := by
    refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (S := KA l) rfl fun x hx => ?_
    rcases hx with rfl | rfl
    · exact hσ
    · have e : zeta l.A = 1 := by simp [zeta, hA]
      have e' : ∀ h, (⟨zeta l.A, h⟩ : KA l) = 1 := fun _ => Subtype.ext e
      exact (congrArg _ (e' _)).trans ((map_one _).trans e.symm)
  exact RingHom.ext fun x => DFunLike.congr_fun h x

theorem fnAlgClosed_of_permutes_id : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ c : Coeff l, (∀ τ : ℂ ≃+* ℂ, (∀ x ∈ c.F, τ x = x) → ConjugationPermutesPeriods F τ id) → FnAlgClosed (Xo := Xo) (c := c) := by
  intro E _ _ _ H D l Xo σ g ty F h1 hσ hty hA c hperm Z a ha
  obtain ⟨r, rfl⟩ := GlobalTheory.GeomIrr.mem_range_of_isAlgebraic_ratFun a (ha.tower_top (kap Z))
  have hr : IsIntegral c.F r := (isIntegral_algebraMap_iff ).1 ha.isIntegral
  suffices h : r ∈ (algebraMap c.F (kap Z)).range by
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by rw [← hk, ← IsScalarTower.algebraMap_apply]⟩
  have hfin : FiniteDimensional ℚ c.F := c.fin
  have hcF : Countable c.F := Cardinal.mk_le_aleph0_iff.1 (by
    simpa [Cardinal.mkRat] using Algebra.IsAlgebraic.cardinalMk_le_max ℚ c.F)
  have hk : Countable (kap Z) :=
    GlobalTheory.GenericReading.countable_of_fg_top ((GlobalTheory.Reg.kap_fg_trdeg E H D l Xo c).1 Z)
  obtain ⟨φ⟩ : Nonempty (kap Z →ₐ[c.F] ℂ) := GlobalTheory.nonempty_algHom_complex_of_countable c.F (kap Z)
  refine mem_range_of_fixed φ hr fun τ hτ => ?_
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have := CompFin.isNoetherian_XF Xo c
  have : GlobalTheory.IsNormalScheme (Xo.XF c) := (GlobalTheory.isNormalScheme_iff _).2
    (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (strK (Xo := Xo) (c := c))
      ((GlobalTheory.isNormalScheme_iff _).1 inferInstance))
  let κ : c.F →+* Γ(Xo.XF c, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv ≫ (strK (Xo := Xo) (c := c)).appTop).hom
  let j : c.F →+* ℂ := algebraMap c.F ℂ
  have hκ : ∀ (x : Sp ℂ ⟶ Xo.XF c) (i : c.F →+* ℂ), x ≫ strK = spMap i → (ev x).comp κ = i := by
    intro x i hx
    ext k
    change ev x ((strK (Xo := Xo) (c := c)).appTop.hom _) = _
    rw [← ev_comp, hx, ev_spec]
    exact congrArg i ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv_hom_id_apply k)
  let x : Sp ℂ ⟶ Xo.XF c := Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ genSp Z
  have hx : x ≫ strK = spMap j := by
    rw [Category.assoc, ← Spec.map_preimage (genSp Z ≫ strK), ← Spec.map_comp]
    congr 1
    ext k
    exact φ.commutes k
  have hev : ∀ f, ev x f = φ (((Xo.XF c).evaluation ⊤ (genPt Z) trivial).hom f) := ev_residue _ φ.toRingHom
  have hm := minpoly.monic hr
  obtain ⟨f, hf, hf0⟩ := exists_section Z (genPt Z)
    ((Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents _ Z.2)) ((minpoly c.F r).map κ) (hm.map _) r (by
    apply φ.toRingHom.injective
    rw [hom_eval₂, ← (RingHom.ext hev : ev x = φ.toRingHom.comp _), eval₂_map, hκ x j hx, map_zero]
    exact (aeval_algHom_apply φ r _).trans (by rw [minpoly.aeval, map_zero]))
  have hS : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap j →
      valAt' y ⊤ f ∈ insert 0 ((minpoly c.F r).rootSet ℂ) := by
    intro y hy
    have h := congrArg (ev y) hf0
    rw [map_mul, ← eval₂_at_apply, eval₂_map, hκ y j hy, map_zero, mul_eq_zero] at h
    rw [valAt'_top]
    exact h.imp id fun h => mem_rootSet.2 ⟨hm.ne_zero, h⟩
  obtain ⟨i, P, hP, hu⟩ := F.onto (x ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hx, emb_eq l σ hσ hA, ← Spec.map_comp]
    rfl)
  obtain ⟨P', hP', hu'⟩ := hperm τ (fun z hz => hτ ⟨z, hz⟩) i P hP
  have key := GlobalTheory.T.regularFunction_const_of_finite_values_on_period_space E H D l Xo σ g ty F h1 hσ hty hA c j f _ ((rootSet_finite _ _).insert 0) hS i P' P hP' hP
    (spMap (τ : ℂ →+* ℂ) ≫ x) x (by rw [Category.assoc, ← hu]; exact hu') (by
      rw [Category.assoc, hx, ← Spec.map_comp]
      congr 1
      ext k
      exact hτ k) hu.symm hx
  rwa [valAt'_top, valAt'_top, ev_conj, hev, hf] at key

end GlobalTheory.CompRat.FixedConst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefficientFieldAlgClosedInFunctionFieldsOfPerioStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficientField_algClosed_in_functionFields_of_periodSpaces : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ c : Coeff l, (∀ τ : ℂ ≃+* ℂ, (∀ x ∈ c.F, τ x = x) → ConjugationPermutesPeriods F τ id) → FnAlgClosed (Xo := Xo) (c := c) := by
  first | exact @GlobalTheory.CompRat.FixedConst.fnAlgClosed_of_permutes_id | exact GlobalTheory.CompRat.FixedConst.fnAlgClosed_of_permutes_id | (intros; apply GlobalTheory.CompRat.FixedConst.fnAlgClosed_of_permutes_id <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongrOfDvdModulus
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree GlobalTheory.FrameNorm
open Formalism.L2.Pj hiding Unf GoodEmb relab
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem congr_of_dvd_modulus {E : Type} [Field E] [NumberField E] {r : ℕ} {L : Type} [AddCommGroup L] [Module (𝓞 E) L]
    (Λ : Submodule (𝓞 E) (Fin r → E)) (φ : L ≃ₗ[𝓞 E] Λ) (γ : Matrix (Fin r) (Fin r) E) {m N : ℕ} (hd : m ∣ N)
    (h : ∀ x ∈ Λ, ∃ y ∈ Λ, Matrix.mulVec γ x - x = (N : E) • y) (a : L) :
    ∃ b : L, γ.mulVec (φ a : Fin r → E) = (φ a : Fin r → E) + m • (φ b : Fin r → E) := by
  obtain ⟨d, rfl⟩ := hd
  obtain ⟨y, hy, e⟩ := h _ (φ a).2
  refine ⟨φ.symm (d • ⟨y, hy⟩), ?_⟩
  rw [LinearEquiv.apply_symm_apply, ← sub_eq_iff_eq_add', e, Nat.cast_smul_eq_nsmul, mul_smul]
  rfl

theorem exists_unf_hasPrinc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (σ : c.F →+* ℂ) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : Dw.La →ₗ[𝓞 E] (Fin r → E)), 1 ≤ Dw.p + Dw.q → GoodEmb c σ → cc ξ₀ = -ξ₀ → (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ ξ₀).im < 0) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ x) (φ y))) → ∃ U : Unf Xo c σ r, IsUnf U ∧ HasPrinc U l.M' ∧ Nonempty U.Comp ∧ (∀ k la γ, (U.X k).χ la γ = 1) ∧ (∀ k, (U.X k).Gm = Gm ∧ (U.X k).ξ0 = ξ₀) ∧ (∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x)) ∧ ∀ ρ, FJ.LatZ U.X ρ ∧ (l.A = 1 → FJ.ExpoMatch U.X 1 ρ l.M) := by
  intro E _ _ _ H Dw l Xo c σ r ξ₀ Gm φ hpq hσ hξ hneg hφ
  have hN : N1c := GlobalTheory.T.cmModuli_consequence_of_abelianSchemeLaws
  have hH := GlobalTheory.T.hasse_norm_theorem_quadratic_extension
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have hT : Out.SecTwistSt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  classical
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  obtain ⟨F⟩ := hN E H Dw l Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) _
    (fun j => relab c σ (e j).1) hpq hσ ((GlobalTheory.T.relabelEmbeddings_good_bijective_conj_compat E H l c σ hσ).2.2.2 Dw _ e)
  obtain ⟨M, hM, hX, hG⟩ := GlobalTheory.T.exists_flagDomainModels_of_familyUniformisation hH E H Dw l Xo _ _ _ F r ξ₀ Gm φ hξ hneg hφ
  obtain ⟨un, hun⟩ := GlobalTheory.T.exists_framedPoints_all_normalisations_familyUnif hB hT E H Dw l Xo c σ _ e F r M hσ hM hX
  have hred : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  refine ⟨unfOf e F M un, GlobalTheory.T.familyUniformisation_isComplexUniformisation hB E H Dw l Xo c σ _ e F r M un hσ hM hX hun, fun k γ hγ h => ?_,
    ⟨⟨0, F.n_pos⟩⟩, hM.chi, hG,
    fun k x => GlobalTheory.T.framedPoint_reduced_from_testRing hB E H Dw l Xo c (CAt σ) _, fun ρ => ⟨GlobalTheory.T.arithmeticGroup_cuspCentre_lattice E r ρ _ _, fun hA => ?_⟩⟩
  · exact (hM.gam k γ).2 ⟨hγ, fun a _ => congr_of_dvd_modulus _ (M.φ k) _ (Nat.dvd_lcm_left _ _) h a,
      fun a => congr_of_dvd_modulus _ (M.φ k) _ (Nat.dvd_lcm_right _ _) h a⟩
  · exact GlobalTheory.T.flagDomainModels_exponents_levelM E H Dw l Xo _ _ _ F r M ρ hM hA

end GlobalTheory.FrameUnif
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFrameUniformisationPrescribedSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFrameUniformisationPrescribedSpace
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree
open Formalism.L2.Pj hiding Unf GoodEmb relab
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem exists_unf_of_space : N1c → GlobalTheory.Published.HasseNormSt → Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : Dw.La →ₗ[𝓞 E] (Fin r → E)), 1 ≤ Dw.p + Dw.q → GoodEmb c σ → cc ξ₀ = -ξ₀ → (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ ξ₀).im < 0) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ x) (φ y))) → ∃ U : Unf Xo c σ r, IsUnf U ∧ Nonempty U.Comp ∧ (∀ k la γ, (U.X k).χ la γ = 1) ∧ (∀ k, (U.X k).Gm = Gm ∧ (U.X k).ξ0 = ξ₀) ∧ (∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x)) ∧ ∀ ρ, FJ.LatZ U.X ρ ∧ (l.A = 1 → FJ.ExpoMatch U.X 1 ρ l.M) := by
  intro hN hH hB hT E _ _ _ H Dw l Xo c σ r ξ₀ Gm φ hpq hσ hξ hneg hφ
  classical
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  obtain ⟨F⟩ := hN E H Dw l Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) _
    (fun j => relab c σ (e j).1) hpq hσ ((GlobalTheory.T.relabelEmbeddings_good_bijective_conj_compat E H l c σ hσ).2.2.2 Dw _ e)
  obtain ⟨M, hM, hX, hG⟩ := GlobalTheory.T.exists_flagDomainModels_of_familyUniformisation hH E H Dw l Xo _ _ _ F r ξ₀ Gm φ hξ hneg hφ
  obtain ⟨un, hun⟩ := GlobalTheory.T.exists_framedPoints_all_normalisations_familyUnif hB hT E H Dw l Xo c σ _ e F r M hσ hM hX
  have hred : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  refine ⟨unfOf e F M un, GlobalTheory.T.familyUniformisation_isComplexUniformisation hB E H Dw l Xo c σ _ e F r M un hσ hM hX hun, ⟨⟨0, F.n_pos⟩⟩, hM.chi, hG,
    fun k x => GlobalTheory.T.framedPoint_reduced_from_testRing hB E H Dw l Xo c (CAt σ) _, fun ρ => ⟨GlobalTheory.T.arithmeticGroup_cuspCentre_lattice E r ρ _ _, fun hA => ?_⟩⟩
  exact GlobalTheory.T.flagDomainModels_exponents_levelM E H Dw l Xo _ _ _ F r M ρ hM hA

end GlobalTheory.FrameUnif
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFrameUniformisationPrescribedSpaceStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree
open Formalism.L2.Pj hiding Unf GoodEmb relab
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frameUniformisation_prescribedSpace : N1c → GlobalTheory.Published.HasseNormSt → Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : Dw.La →ₗ[𝓞 E] (Fin r → E)), 1 ≤ Dw.p + Dw.q → GoodEmb c σ → cc ξ₀ = -ξ₀ → (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ ξ₀).im < 0) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ x) (φ y))) → ∃ U : Unf Xo c σ r, IsUnf U ∧ Nonempty U.Comp ∧ (∀ k la γ, (U.X k).χ la γ = 1) ∧ (∀ k, (U.X k).Gm = Gm ∧ (U.X k).ξ0 = ξ₀) ∧ (∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x)) ∧ ∀ ρ, FJ.LatZ U.X ρ ∧ (l.A = 1 → FJ.ExpoMatch U.X 1 ρ l.M) := by
  first | exact @GlobalTheory.FrameUnif.exists_unf_of_space | exact GlobalTheory.FrameUnif.exists_unf_of_space | (intros; apply GlobalTheory.FrameUnif.exists_unf_of_space <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianLatticeSignatureSplitOfDefinite
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianLatticeSignatureSplitOfDefinite
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in
private theorem rt0_im_ne_zero (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : H.rt0.im ≠ 0 := by
  intro h
  have hd : H.d ≠ 0 := by
    have := H.2
    omega
  have hpos : (0 : ℝ) < H.d := by exact_mod_cast Nat.pos_of_ne_zero hd
  have := congrArg Complex.re H.sqrt_neg_disc_sq
  simp [sq, Complex.mul_re, h] at this
  nlinarith [mul_self_nonneg H.rt0.re]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in
private theorem embedding_rt_eq_or_eq_neg (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) :
    τ H.rt = H.rt0 ∨ τ H.rt = -H.rt0 := by
  have hsq : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
    push_cast at this
    exact this
  have h2 : (τ H.rt) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, hsq, H.sqrt_neg_disc_sq]
    simp
  exact sq_eq_sq_iff_eq_or_eq_neg.1 h2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in
private theorem exists_pos_form_rt_eq_im_mul {D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {g : ℕ} {ty : Fin g → E →+* ℂ}
    {P : D.La →+ (Fin g → ℂ)} (hP : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P) (c : ℂ)
    (hc : ∀ x, P (H.rt • x) = c • P x) {a : D.La} (ha : a ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ (((D.EF (H.rt • a)) a : ℤ) : ℝ) = c.im * r := by
  obtain ⟨-, hinj, -, -, Hm, -, hpos, hform⟩ := hP
  have hPa : P a ≠ 0 := fun h => ha (hinj (h.trans (map_zero P).symm))
  refine ⟨(_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (P a) (P a)).re, hpos _ hPa, ?_⟩
  have h0 : (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (P a) (P a)).im = 0 := by
    rw [hform, D.alt, Int.cast_zero]
  rw [← hform, hc]
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm] at h0 ⊢
  rw [smul_dotProduct, smul_eq_mul, Complex.mul_im, h0]
  ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in
theorem _root_.GlobalTheory.CompRat.splitLat_of_definite : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H),
    D.p = 0 ∨ D.q = 0 → _root_.GlobalTheory.CompRat.SplitLat D := by
  intro E _ _ _ H D hpq
  obtain ⟨g, ty, hty⟩ := _root_.GlobalTheory.PureTypeModel.exists_isTypeFn H D.p D.q
  obtain ⟨P, hP⟩ := _root_.GlobalTheory.PeriodNonempty.exists_isPeriod E H D g ty hty
  have hscal : ∀ c : ℂ, (∀ i, ty i H.rt = c) → ∀ x, P (H.rt • x) = c • P x := by
    intro c hc x
    funext i
    rw [hP.1, hc]
    rfl
  have hcard : ∀ i, Nat.card {j // ty j = ty i} ≠ 0 := by
    intro i
    haveI : Nonempty {j // ty j = ty i} := ⟨⟨i, rfl⟩⟩
    exact Nat.card_pos.ne'
  have him := rt0_im_ne_zero H
  have hsq := mul_self_pos.2 him
  unfold _root_.GlobalTheory.CompRat.SplitLat
  rcases hpq with hp | hq
  · have hc : ∀ i, ty i H.rt = -H.rt0 := by
      intro i
      rcases embedding_rt_eq_or_eq_neg H (ty i) with h | h
      · exact absurd ((hty (ty i)).1 h) (by rw [hp]; exact hcard i)
      · exact h
    refine ⟨⊥, ⊤, by simp, ?_, ?_, ?_, ?_, ?_⟩
    · intro a ha b _
      rw [(Submodule.mem_bot _).1 ha]
      simp
    · rw [finrank_bot, hp]
    · rw [finrank_top, D.rank, hp, zero_add]
    · intro a ha h0
      exact absurd ((Submodule.mem_bot _).1 ha) h0
    · intro a _ ha0
      obtain ⟨r, hr, he⟩ := exists_pos_form_rt_eq_im_mul hP _ (hscal _ hc) ha0
      rw [he, Complex.neg_im]
      nlinarith [mul_pos hsq hr]
  · have hc : ∀ i, ty i H.rt = H.rt0 := by
      intro i
      by_contra h
      exact absurd ((hty (ty i)).2 h) (by rw [hq]; exact hcard i)
    refine ⟨⊤, ⊥, by simp, ?_, ?_, ?_, ?_, ?_⟩
    · intro a _ b hb
      rw [(Submodule.mem_bot _).1 hb]
      simp
    · rw [finrank_top, D.rank, hq, add_zero]
    · rw [finrank_bot, hq]
    · intro a _ ha0
      obtain ⟨r, hr, he⟩ := exists_pos_form_rt_eq_im_mul hP _ (hscal _ hc) ha0
      rw [he]
      nlinarith [mul_pos hsq hr]
    · intro a ha h0
      exact absurd ((Submodule.mem_bot _).1 ha) h0

end GlobalTheory.CompRat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianLatticeSignatureSplitOfDefiniteStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianLatticeSignatureSplit_of_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), D.p = 0 ∨ D.q = 0 → SplitLat D := by
  first | exact @GlobalTheory.CompRat.splitLat_of_definite | exact GlobalTheory.CompRat.splitLat_of_definite | (intros; apply GlobalTheory.CompRat.splitLat_of_definite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemberDictionaryInvariantRationalLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemberDictionaryInvariantRationalLevel
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem dict_invariant : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ dict, C.IsDict dict → ∀ Kf : Subgroup (GA D V), IsLevelK V l.M Kf → (∀ γ ∈ GQ V, ∀ g, ∃ γ' ∈ (C.M.X (dict g).1).Γ, dict (γ * g) = ⟨(dict g).1, lact γ' (dict g).2⟩) ∧ (∀ k ∈ Kf, ∀ g, ∃ γ' ∈ (C.M.X (dict g).1).Γ, dict (g * k) = ⟨(dict g).1, lact γ' (dict g).2⟩) ∧ (∀ g, (dict g).2 ∈ (C.M.X (dict g).1).dom) ∧ (∀ g τ i, ‖dmin (C.M.X (dict g).1).Gm (dict g).2 τ i‖ = 1) ∧ ∀ g k γ, C.Mark g k γ → ∃ δ ∈ (C.M.X k).Γ, dict g = ⟨k, lact δ (C.fr (γ * g) k)⟩ := by
  intro D H Dw l Xo c σ V r C hC dict hd Kf hK
  have last : ∀ g k γ, C.Mark g k γ → ∃ δ ∈ (C.M.X k).Γ, dict g = ⟨k, lact δ (C.fr (γ * g) k)⟩ := by
    intro g k γ hm
    obtain ⟨γ₀, hm₀, hf⟩ := hd.1 g
    have hu := GlobalTheory.T.marking_component_unique_frame_unique_arithmeticGroup D H Dw l Xo c σ V r C hC g
    have hk : (dict g).1 = k := hu.1 _ _ _ _ hm₀ hm
    subst hk
    obtain ⟨δ, hδ, he⟩ := hu.2 _ γ γ₀ hm hm₀
    refine ⟨δ, hδ, ?_⟩
    rw [← he, ← hf]
  refine ⟨?_, ?_, ?_, ?_, last⟩
  · intro γ hγ g
    obtain ⟨γ₀, hm₀, hf⟩ := hd.1 g
    have hm := (GlobalTheory.T.markingRule_translate_stable D H Dw l Xo c σ V r C hC g _ γ₀ hm₀).1 γ hγ
    obtain ⟨δ, hδ, he⟩ := last _ _ _ hm
    refine ⟨δ, hδ, ?_⟩
    rw [he, hf, mul_assoc, inv_mul_cancel_left]
  · intro k hk g
    obtain ⟨γ₀, hm₀, hf⟩ := hd.1 g
    have hk' := (hK k).1 hk
    have hm := (GlobalTheory.T.markingRule_translate_stable D H Dw l Xo c σ V r C hC g _ γ₀ hm₀).2.1 k hk'.2
    obtain ⟨δ, hδ, he⟩ := last _ _ _ hm
    refine ⟨δ, hδ, ?_⟩
    rw [he, hf, ← mul_assoc,
      (GlobalTheory.T.memberDictionary_frames_orthonormal_unit D H Dw l Xo c σ V r C hC (γ₀ * g) (dict g).1).2.2.2.2.1 k hk'.1]
  · intro g
    obtain ⟨γ₀, -, hf⟩ := hd.1 g
    rw [hf]
    exact (GlobalTheory.T.memberDictionary_frames_orthonormal_unit D H Dw l Xo c σ V r C hC (γ₀ * g) (dict g).1).2.1
  · intro g τ i
    obtain ⟨γ₀, -, hf⟩ := hd.1 g
    rw [hf]
    exact (GlobalTheory.T.memberDictionary_frames_orthonormal_unit D H Dw l Xo c σ V r C hC (γ₀ * g) (dict g).1).2.2.1 τ i

end GlobalTheory.Member
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemberDictionaryInvariantRationalLevelStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memberDictionary_invariant_rational_level : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ dict, C.IsDict dict → ∀ Kf : Subgroup (GA D V), IsLevelK V l.M Kf → (∀ γ ∈ GQ V, ∀ g, ∃ γ' ∈ (C.M.X (dict g).1).Γ, dict (γ * g) = ⟨(dict g).1, lact γ' (dict g).2⟩) ∧ (∀ k ∈ Kf, ∀ g, ∃ γ' ∈ (C.M.X (dict g).1).Γ, dict (g * k) = ⟨(dict g).1, lact γ' (dict g).2⟩) ∧ (∀ g, (dict g).2 ∈ (C.M.X (dict g).1).dom) ∧ (∀ g τ i, ‖dmin (C.M.X (dict g).1).Gm (dict g).2 τ i‖ = 1) ∧ ∀ g k γ, C.Mark g k γ → ∃ δ ∈ (C.M.X k).Γ, dict g = ⟨k, lact δ (C.fr (γ * g) k)⟩ := by
  first | exact @GlobalTheory.Member.dict_invariant | exact GlobalTheory.Member.dict_invariant | (intros; apply GlobalTheory.Member.dict_invariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPermPeriodSpacesComplexAut
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPermPeriodSpacesComplexAut
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.ConjPermutes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  unfold spMap
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem ringHom_ext {l : Level H} (hA : l.A = 1) {f f' : KA l →+* ℂ} (h : f (baseKA l).ρ = f' (baseKA l).ρ) :
    f = f' := by
  have hz : zeta l.A = 1 := by
    unfold zeta
    rw [hA]
    simp
  suffices key : ∀ (x : ℂ) (hx : x ∈ IntermediateField.adjoin ℚ ({H.rt0, zeta l.A} : Set ℂ)),
      f ⟨x, hx⟩ = f' ⟨x, hx⟩ by
    ext y
    exact key y.1 y.2
  intro x hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact h
    · exact (congrArg f (Subtype.ext hz)).trans ((map_one f).trans
        ((map_one f').symm.trans (congrArg f' (Subtype.ext hz)).symm))
  | algebraMap r =>
    show f (algebraMap ℚ (KA l) r) = f' (algebraMap ℚ (KA l) r)
    rw [eq_ratCast (algebraMap ℚ (KA l)) r, map_ratCast, map_ratCast]
  | add x y hx hy ihx ihy =>
    show f (⟨x, hx⟩ + ⟨y, hy⟩) = f' (⟨x, hx⟩ + ⟨y, hy⟩)
    rw [map_add (f := _), map_add (f := _), ihx, ihy]
  | inv x hx ih =>
    show f (⟨x, hx⟩⁻¹) = f' (⟨x, hx⟩⁻¹)
    rw [map_inv₀, map_inv₀, ih]
  | mul x y hx hy ihx ihy =>
    show f (⟨x, hx⟩ * ⟨y, hy⟩) = f' (⟨x, hx⟩ * ⟨y, hy⟩)
    rw [map_mul, map_mul, ihx, ihy]

theorem valAt'_top {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (f : Γ(X, ⊤)) :
    valAt' x ⊤ f = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (x.appTop.hom f) := by
  unfold valAt'
  rw [dite_eq_left (by simp)]
  unfold valAt
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

theorem valAt'_spMap_comp {X : Scheme.{0}} (τ : ℂ →+* ℂ) (x : Sp ℂ ⟶ X) (f : Γ(X, ⊤)) :
    valAt' (spMap τ ≫ x) ⊤ f = τ (valAt' x ⊤ f) := by
  rw [valAt'_top, valAt'_top]
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom τ)
  have h2 := congrArg (fun φ => φ.hom (x.appTop.hom f)) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  simp only [spMap, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  exact h2

theorem valAt'_idem {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {e : Γ(X, ⊤)} (he : e * e = e) :
    valAt' x ⊤ e ∈ ({0, 1} : Set ℂ) := by
  rw [valAt'_top]
  have h : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (x.appTop.hom e) *
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (x.appTop.hom e) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (x.appTop.hom e) := by
    rw [← map_mul, ← map_mul, he]
  generalize (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (x.appTop.hom e) = v at h ⊢
  have h2 : v * (v - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h2 with h0 | h1
  · simp [h0]
  · simp [sub_eq_zero.1 h1]

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem exists_period (F : FamilyUnif Xo σ ty) (hty : IsTypeFn H D.p D.q ty) (i : Fin F.n) :
    ∃ P, IsPeriod (F.Di i) ty P := by
  obtain ⟨hp, hq⟩ := F.sig i
  exact GlobalTheory.PeriodNonempty.exists_isPeriod E H (F.Di i) g ty (by rw [hp, hq]; exact hty)

private theorem key_lemma' (F : FamilyUnif Xo σ ty) (hD : 1 ≤ D.p + D.q) (hσ : σ (baseKA l).ρ = H.rt0)
    (hty : IsTypeFn H D.p D.q ty) (hA : l.A = 1) (τ : ℂ ≃+* ℂ) (hτ : τ H.rt0 = H.rt0)
    (i k k' : Fin F.n) (P P' : (F.Di i).La →+ (Fin g → ℂ)) (Q : (F.Di k).La →+ (Fin g → ℂ))
    (Q' : (F.Di k').La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F.Di i) ty P')
    (hQ : IsPeriod (F.Di k) ty Q) (hQ' : IsPeriod (F.Di k') ty Q')
    (h1 : spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u k Q) (h2 : spMap (τ : ℂ →+* ℂ) ≫ F.u i P' = F.u k' Q') :
    k' = k := by
  classical
  obtain ⟨c, -, he⟩ := GlobalTheory.T.exists_coeffField_idempotent_cutting_periodSpaces E H D l Xo σ g ty F hD hσ hty hA (Classical.arbitrary _)
  obtain ⟨e, hee, hev⟩ := he k
  have hs : τ.symm H.rt0 = H.rt0 := by
    rw [RingEquiv.symm_apply_eq]
    exact hτ.symm
  have hjc : σ = ((τ.symm : ℂ →+* ℂ).comp c.F.val.toRingHom).comp
      (IntermediateField.inclusion c.le).toRingHom :=
    ringHom_ext hA (hσ.trans hs.symm)
  have hw : F.u i P ≫ Xo.s = spMap ((τ.symm : ℂ →+* ℂ).comp c.F.val.toRingHom) ≫
      spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [F.10 i P hP, spMap_comp, ← hjc]
  have hw' : F.u i P' ≫ Xo.s = spMap ((τ.symm : ℂ →+* ℂ).comp c.F.val.toRingHom) ≫
      spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [F.10 i P' hP', spMap_comp, ← hjc]
  have hsnd : spMap (τ : ℂ →+* ℂ) ≫ spMap ((τ.symm : ℂ →+* ℂ).comp c.F.val.toRingHom) =
      spMap c.F.val.toRingHom := by
    rw [spMap_comp]
    congr 1
    ext z
    simp
  have hv1 := hev k Q hQ (spMap (τ : ℂ →+* ℂ) ≫ pullback.lift (F.u i P) _ hw)
    (by rw [Category.assoc, pullback.lift_fst]; exact h1)
    (by rw [Category.assoc, pullback.lift_snd]; exact hsnd)
  have hv2 := hev k' Q' hQ' (spMap (τ : ℂ →+* ℂ) ≫ pullback.lift (F.u i P') _ hw')
    (by rw [Category.assoc, pullback.lift_fst]; exact h2)
    (by rw [Category.assoc, pullback.lift_snd]; exact hsnd)
  have heq := GlobalTheory.CompRat.valAt_eq_of_finite_values E H D l Xo σ g ty F hD hσ hty hA c
    ((τ.symm : ℂ →+* ℂ).comp c.F.val.toRingHom) e {0, 1}
    (Set.toFinite _) (fun y _ => valAt'_idem y hee) i P P' hP hP'
    (pullback.lift (F.u i P) _ hw) (pullback.lift (F.u i P') _ hw')
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  rw [valAt'_spMap_comp, if_pos rfl] at hv1
  rw [valAt'_spMap_comp, ← heq, hv1] at hv2
  by_contra hne
  rw [if_neg hne] at hv2
  exact one_ne_zero hv2

private theorem spMap_comp_u_comp_s_eq_of_fixes_rt0 (F : FamilyUnif Xo σ ty) (hσ : σ (baseKA l).ρ = H.rt0) (hA : l.A = 1)
    (τ : ℂ ≃+* ℂ) (hτ : τ H.rt0 = H.rt0) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) : (spMap (τ : ℂ →+* ℂ) ≫ F.u i P) ≫ Xo.s = spMap σ := by
  rw [Category.assoc, F.10 i P hP, spMap_comp]
  congr 1
  exact ringHom_ext hA (by rw [RingHom.comp_apply, hσ]; exact hτ)

theorem exists_map (F : FamilyUnif Xo σ ty) (hD : 1 ≤ D.p + D.q) (hσ : σ (baseKA l).ρ = H.rt0)
    (hty : IsTypeFn H D.p D.q ty) (hA : l.A = 1) (τ : ℂ ≃+* ℂ) (hτ : τ H.rt0 = H.rt0) :
    ∃ π : Fin F.n → Fin F.n, ConjugationPermutesPeriods F τ π := by
  classical
  choose P0 hP0 using fun i => exists_period F hty i
  choose k Q hQ hkQ using fun i => F.18 _ (spMap_comp_u_comp_s_eq_of_fixes_rt0 F hσ hA τ hτ i (P0 i) (hP0 i))
  refine ⟨k, fun i P hP => ?_⟩
  obtain ⟨k', Q', hQ', hk'⟩ := F.18 _ (spMap_comp_u_comp_s_eq_of_fixes_rt0 F hσ hA τ hτ i P hP)
  have hkk := key_lemma' F hD hσ hty hA τ hτ i (k i) k' (P0 i) P (Q i) Q' (hP0 i) hP (hQ i) hQ'
    (hkQ i).symm hk'.symm
  subst hkk
  exact ⟨Q', hQ', hk'.symm⟩

theorem exists_perm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∃ π : Equiv.Perm (Fin F.n), ConjugationPermutesPeriods F τ π := by
  intro E _ _ _ H D l Xo σ g ty F hD hσ hty hA τ hτ
  obtain ⟨π, hπ⟩ := exists_map F hD hσ hty hA τ hτ
  have hτ' : τ.symm H.rt0 = H.rt0 := by
    rw [RingEquiv.symm_apply_eq]
    exact hτ.symm
  obtain ⟨π', hπ'⟩ := exists_map F hD hσ hty hA τ.symm hτ'
  have hinv : ∀ i, π' (π i) = i := by
    intro i
    obtain ⟨P, hP⟩ := exists_period F hty i
    obtain ⟨Q, hQ, h1⟩ := hπ i P hP
    obtain ⟨R, hR, h2⟩ := hπ' (π i) Q hQ
    have h3 : spMap (τ.symm : ℂ →+* ℂ) ≫ spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i P := by
      rw [← Category.assoc, spMap_comp]
      have hid : (τ.symm : ℂ →+* ℂ).comp (τ : ℂ →+* ℂ) = RingHom.id ℂ := by
        ext z
        simp
      rw [hid]
      unfold spMap
      simp
    rw [h1, h2] at h3
    exact F.19 _ _ _ _ hR hP h3
  have hinj : Function.Injective π := fun a b hab => by rw [← hinv a, ← hinv b, hab]
  exact ⟨Equiv.ofBijective π hinj.bijective_of_finite, hπ⟩

end GlobalTheory.ConjPermutes
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPermPeriodSpacesComplexAutStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_perm_periodSpaces_complexAut : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∃ π : Equiv.Perm (Fin F.n), ConjugationPermutesPeriods F τ π := by
  first | exact @GlobalTheory.ConjPermutes.exists_perm | exact GlobalTheory.ConjPermutes.exists_perm | (intros; apply GlobalTheory.ConjPermutes.exists_perm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspFormsFiniteDimensionalOfGoodEmb
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory

theorem cuspForms_finiteDimensional_of_goodEmb :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.Pj.Unf Xo c σ r) (σ : c.F →+* ℂ), Formalism.L2.Pj.GoodEmb c σ → Formalism.L2.Pj.IsUnf (U σ) → Formalism.L2.Pj.CuspFD Xo c U := by
  intro E _ _ _ H Dw l Xo c r U σ hσ hU
  exact (Formalism.L2.PjFree.cuspFD_ofPj U).1
    (GlobalTheory.cuspForms_finiteDimensional_of_isUnf GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c r
      (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) σ ((Formalism.L2.PjFree.goodEmb_iff σ).2 hσ)
      ((Formalism.L2.PjFree.isUnf_ofPj (U σ)).2 hU))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDictionaryByMarkingRule
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDictionaryByMarkingRule
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

theorem GlobalTheory.Member.Ctx.exists_isDict : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∃ dict, C.IsDict dict := by
  intro D H Dw l Xo c σ V r C hC
  classical
  choose k₀ γ₀ h₀ using GlobalTheory.T.exists_component_lattice_marking_adelic D H Dw l Xo c σ V r C hC
  refine ⟨fun h => if hk : ∃ k, C.Mark h k 1 then ⟨hk.choose, C.fr h hk.choose⟩
    else ⟨k₀ h, C.fr (γ₀ h * h) (k₀ h)⟩, ?_, ?_⟩
  · intro h
    by_cases hk : ∃ k, C.Mark h k 1
    · refine ⟨1, ?_⟩
      beta_reduce
      rw [dite_eq_left hk]
      exact ⟨hk.choose_spec, by rw [one_mul]⟩
    · refine ⟨γ₀ h, ?_⟩
      beta_reduce
      rw [dite_eq_right hk]
      exact ⟨h₀ h, rfl⟩
  · intro k
    obtain ⟨h, hf, hm⟩ := GlobalTheory.T.exists_finiteAdelic_element_marking_component D H Dw l Xo c σ V r C hC k
    have hk : ∃ k, C.Mark h k 1 := ⟨k, hm⟩
    refine ⟨h, ?_⟩
    beta_reduce
    rw [dite_eq_left hk]
    have e : hk.choose = k :=
      (GlobalTheory.T.marking_component_unique_frame_unique_arithmeticGroup D H Dw l Xo c σ V r C hC h).1 _ _ _ _ hk.choose_spec hm
    rw [e]
    have := (GlobalTheory.T.memberDictionary_frames_orthonormal_unit D H Dw l Xo c σ V r C hC 1 k).2.2.2.2.1 h hf
    rw [one_mul] at this
    rw [this]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDictionaryByMarkingRuleStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dictionary_by_marking_rule : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∃ dict, C.IsDict dict := by
  first | exact @GlobalTheory.Member.Ctx.exists_isDict | exact GlobalTheory.Member.Ctx.exists_isDict | (intros; apply GlobalTheory.Member.Ctx.exists_isDict <;> assumption)
end
end
