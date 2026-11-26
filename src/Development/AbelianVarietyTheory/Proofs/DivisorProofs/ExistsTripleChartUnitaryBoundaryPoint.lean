module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrCongrOfResidueFixedByDecomposition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleBasisSectionsAbelianSchemeOverDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixDescentUnramifiedDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGoodReductionOfUnramifiedAbelianSchemeModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaFixedFieldValuationRingStrictlyHenselian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTautologicalChartVersality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartIsEtaleCompletionLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedAdicCompletionTensorResidueField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTripleChartUnitaryBoundaryPointRigid
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointRigidTautologicalChartUnitaryBoundary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegeneratingMonomialFamilyAlgClosedResidue
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonoFamThrough
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitRamifiedExtensionFormMultiple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitRamifiedExtensionFormMultiple
open AlgebraicGeometry CategoryTheory Limits IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.UPoinc

theorem mumBase_of_cdvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V] [CharZero V] : GlobalTheory.Mum.Base V :=
  ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, inferInstance⟩

theorem uTrait_ramExt : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} (T : GlobalTheory.UPoinc.UTrait Xo c) (n : ℕ), 0 < n →
    ∃ (T₂ : GlobalTheory.UPoinc.UTrait Xo c) (g : T.V →+* T₂.V) (gK : FractionRing T.V →+* FractionRing T₂.V)
      (e : T.P.D.toPre.X ≃ₗ[𝓞 E] T₂.P.D.toPre.X) (q : ℕ), Function.Injective g ∧ IsLocalHom g ∧
      (∀ a, gK (algebraMap T.V _ a) = algebraMap T₂.V _ (g a)) ∧ T₂.y = spMap gK ≫ T.y ∧ 0 < q ∧
      ∀ a b, T₂.be (e a) (e b) = ((n * q : ℕ) : ℤ) * T.be a b := by
  intro E _ _ _ H Dw l Xo c T n hn
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  haveI : IsAdicComplete (maximalIdeal T.V) T.V := T.cdvr.2.1
  haveI : CharZero T.V := T.cdvr.2.2
  let T0 : Formalism.L2.Pj.CDVR := { V := T.V }
  obtain ⟨T₁, g₁, κ, e₁, ϖ₁, hg₁, hl₁, hϖ₁, hκ, hne₁, hass₁⟩ :=
    GlobalTheory.ArcExt.exists_ramified_ext T0 (Ω := AlgebraicClosure T0.Fr) ⊥ n hn T.ϖ T.irr
  let gK₁ : FractionRing T.V →+* FractionRing T₁.V :=
    κ.comp (algebraMap T0.Fr (⊥ : IntermediateField T0.Fr (AlgebraicClosure T0.Fr)))
  have hgK₁ : ∀ a, gK₁ (algebraMap T.V _ a) = algebraMap T₁.V _ (g₁ a) := hκ
  haveI : IsAdicComplete (maximalIdeal T₁.V) T₁.V := T₁.cpl
  have hB₁ : GlobalTheory.Mum.Base T₁.V := mumBase_of_cdvr T₁.V
  obtain ⟨T₂, f, fK, hf, hfl, -, hfK, hy⟩ :=
    GlobalTheory.T.exists_unitaryTrait_through_moduliGenericPoint E H Dw l Xo c T₁.V hB₁ inferInstance (spMap gK₁ ≫ T.y)
  haveI : IsDiscreteValuationRing T₂.V := T₂.cdvr.1
  haveI : IsAdicComplete (maximalIdeal T₂.V) T₂.V := T₂.cdvr.2.1
  haveI : CharZero T₂.V := T₂.cdvr.2.2

  have hfϖ0 : f ϖ₁ ≠ 0 := fun h => hϖ₁.ne_zero (hf (by rw [h, map_zero]))
  obtain ⟨e₂, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hfϖ0 T₂.irr
  have he₂ : 0 < e₂ := by
    rcases Nat.eq_zero_or_pos e₂ with h | h
    · exfalso
      rw [h, pow_zero, mul_one] at hu
      exact hϖ₁.not_isUnit ((isUnit_map_iff f ϖ₁).1 (hu ▸ u.isUnit))
    · exact h
  have he₁ : 0 < e₁ := by
    rcases Nat.eq_zero_or_pos e₁ with h | h
    · exfalso
      rw [h, pow_zero] at hass₁
      exact T.irr.not_isUnit ((isUnit_map_iff g₁ T.ϖ).1 (associated_one_iff_isUnit.1 hass₁))
    · exact h
  have hassf : Associated (f ϖ₁) (T₂.ϖ ^ e₂) := ⟨u⁻¹, by rw [hu, mul_comm (u : T₂.V), mul_assoc, Units.mul_inv, mul_one]⟩
  have hass : Associated ((f.comp g₁) T.ϖ) (T₂.ϖ ^ (e₁ * e₂)) := by
    have h1 : Associated (f (g₁ T.ϖ)) (f ϖ₁ ^ e₁) := by
      rw [← map_pow]; exact hass₁.map f
    rw [mul_comm, pow_mul]
    exact h1.trans (hassf.pow_pow)
  have hyc : spMap (fK.comp gK₁) ≫ T.y = spMap (RingHom.id (FractionRing T₂.V)) ≫ T₂.y := by
    have hid : spMap (RingHom.id (FractionRing T₂.V)) = 𝟙 _ := by
      show Spec.map (CommRingCat.ofHom (RingHom.id _)) = _
      rw [CommRingCat.ofHom_id, Spec.map_id]
    rw [hy, hid, Category.id_comp, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp]; rfl
  have hcomp : ∀ a, (fK.comp gK₁) (algebraMap T.V _ a) = algebraMap T₂.V _ ((f.comp g₁) a) := fun a => by
    simp only [RingHom.comp_apply]
    rw [hgK₁, hfK]
  obtain ⟨e, he⟩ := GlobalTheory.T.traitsOfModuliPoint_have_isomorphic_proportional_lattices E H Dw l Xo c T T₂ T₂.V (f.comp g₁) (RingHom.id T₂.V) (fK.comp gK₁)
    (RingHom.id _) (mumBase_of_cdvr T₂.V) inferInstance (hf.comp hg₁) Function.injective_id inferInstance
    inferInstance hcomp (fun _ => rfl) hyc T₂.ϖ (e₁ * e₂) 1 T₂.irr hass (by rw [pow_one]; rfl)
  obtain ⟨k, hk⟩ := hne₁
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hk; omega
    · exact h
  refine ⟨T₂, f.comp g₁, fK.comp gK₁, e, k * e₂, hf.comp hg₁, inferInstance, hcomp, ?_, Nat.mul_pos hk0 he₂,
    fun a b => ?_⟩
  · rw [hy, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp]; rfl
  · have h := he a b
    rw [Nat.cast_one, one_mul] at h
    rw [← h, hk, mul_assoc]

end GlobalTheory.UPoinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitRamifiedExtensionFormMultipleStatement
open AlgebraicGeometry CategoryTheory Limits IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryTrait_ramifiedExtension_form_multiple : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} (T : GlobalTheory.UPoinc.UTrait Xo c) (n : ℕ), 0 < n →
    ∃ (T₂ : GlobalTheory.UPoinc.UTrait Xo c) (g : T.V →+* T₂.V) (gK : FractionRing T.V →+* FractionRing T₂.V)
      (e : T.P.D.toPre.X ≃ₗ[𝓞 E] T₂.P.D.toPre.X) (q : ℕ), Function.Injective g ∧ IsLocalHom g ∧
      (∀ a, gK (algebraMap T.V _ a) = algebraMap T₂.V _ (g a)) ∧ T₂.y = spMap gK ≫ T.y ∧ 0 < q ∧
      ∀ a b, T₂.be (e a) (e b) = ((n * q : ℕ) : ℤ) * T.be a b := by
  first | exact @GlobalTheory.UPoinc.uTrait_ramExt | exact GlobalTheory.UPoinc.uTrait_ramExt | (intros; apply GlobalTheory.UPoinc.uTrait_ramExt <;> assumption)
end
end

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChartTrait

theorem exists_cdvr_through {U S : Scheme.{0}} (j : U ⟶ S) [IsOpenImmersion j] (hd : Dense (Set.range j))
    [IsLocallyNoetherian S] (x : S) (hx : x ∉ Set.range j) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (a : Sp W ⟶ S) (y₀ : Sp (FractionRing W) ⟶ U),
      y₀ ≫ j = jK W ≫ a ∧ a (closedPoint W) = x := by
  have : IsDominant j := ⟨hd⟩
  let O := S.presheaf.stalk x
  obtain ⟨ge, hge, hs⟩ := exists_mem_genericPoints_specializes x
  have hge' := genericPoints_subset_range_of_isDominant j hge
  have h1 : ge ∈ Set.range (S.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact hs
  obtain ⟨q, rfl⟩ := h1
  have hop : IsOpen (S.fromSpecStalk x ⁻¹' Set.range j) :=
    j.isOpenEmbedding.isOpen_range.preimage (S.fromSpecStalk x).continuous
  obtain ⟨_, ⟨f, rfl⟩, hqf, hf⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (a := q) hge' hop
  have hfm : f ∈ maximalIdeal O := by
    by_contra hn
    have : S.fromSpecStalk x (closedPoint O) ∈ Set.range j :=
      hf (show closedPoint O ∈ PrimeSpectrum.basicOpen f from hn)
    rw [Scheme.fromSpecStalk_closedPoint] at this
    exact hx this
  let Ω := AlgebraicClosure (ResidueField O)
  let φ : O →+* Ω := (algebraMap (ResidueField O) Ω).comp (residue O)
  have : IsLocalHom φ := ⟨fun a ha => by
    by_contra h
    have : residue O a = 0 := (residue_eq_zero_iff a).2 h
    simp [φ, this] at ha⟩
  obtain ⟨W, _, _, _, _, ψ, ιW, hψ, hιW⟩ := GlobalTheory.GeomTrait.exists_dvr (O := O) (Ω := Ω) hfm q.asIdeal q.isPrime hqf φ
  let a : Sp W ⟶ S := Spec.map (CommRingCat.ofHom ψ) ≫ S.fromSpecStalk x
  obtain ⟨y, hy⟩ := GlobalTheory.HomExt.exists_lift_of_range_subset j
    (spMap (algebraMap W (FractionRing W)) ≫ a) (by
      rintro _ ⟨t, rfl⟩
      have : spMap (algebraMap W (FractionRing W)) t = (⊥ : PrimeSpectrum W) := by
        apply PrimeSpectrum.ext
        change Ideal.comap (algebraMap W (FractionRing W)) t.asIdeal = ⊥
        rw [@Ideal.eq_bot_of_prime _ _ t.asIdeal t.isPrime]
        exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)
      rw [Scheme.Hom.comp_apply, this]
      exact hf (a := PrimeSpectrum.comap ψ ⊥) hψ)
  have hloc : IsLocalHom ψ := ⟨fun r hr => by
    by_contra h
    have h2 : φ r = ιW (residue W (ψ r)) := by rw [← hιW]; rfl
    have : residue W (ψ r) ≠ 0 := by
      rw [Ne, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, not_not]; exact hr
    have h3 : φ r ≠ 0 := by rw [h2]; exact (map_ne_zero ιW).2 this
    exact h (isUnit_of_map_unit φ r (IsUnit.mk0 _ h3))⟩
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, a, y, hy, ?_⟩
  change S.fromSpecStalk x (Spec.map (CommRingCat.ofHom ψ) (closedPoint W)) = x
  have : Spec.map (CommRingCat.ofHom ψ) (closedPoint W) = closedPoint O :=
    IsLocalRing.comap_closedPoint ψ
  rw [this, Scheme.fromSpecStalk_closedPoint]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem trait_be_pos (T : UPoinc.UTrait Xo c) {x : T.P.D.toPre.X} (hx : x ≠ 0) : 0 < T.be x x := by
  obtain ⟨i, hi⟩ := IsMonomial.exists_pos (maximalIdeal.isMaximal T.V).ne_top T.mono hx
  fin_cases i
  exact hi

theorem trait_finrank_le {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R]
    {y : Sp (FractionRing R) ⟶ Xo.XF c} {t : SAB H (Sp R)} (hg : UPoinc.GenOf Xo c y t) (P : PELUnif (maximalIdeal R) t) :
    Module.finrank (𝓞 E) P.D.toPre.X ≤ min Dw.p Dw.q := by
  obtain ⟨tK, ⟨m⟩, ⟨m'⟩⟩ := hg
  let K := AlgebraicClosure (FractionRing R)
  let f : R →+* K := (algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R (FractionRing R))
  haveI : CharZero K := ⟨fun a b h => Nat.cast_injective (R := R) (hf (by simpa using h))⟩
  let x' : Sp K ⟶ Sp (FractionRing R) := spMap (algebraMap (FractionRing R) K)
  have hx : x' ≫ jK R = spMap f := by
    rw [← GlobalTheory.TorRef.DomFine.spMap_comp']
  obtain ⟨β₀, hβ₀⟩ := Spec.map_surjective ((x' ≫ y ≫ pullback.fst _ _) ≫ Xo.s)
  have hdet := (Xo.univ.geom K (x' ≫ y ≫ pullback.fst _ _) β₀.hom hβ₀.symm).1
  have hr : (β₀.hom (baseKA l).ρ) ^ 2 = -(H.d : K) := by
    rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  have bound : ∀ (τ : 𝓞 E →+* K) (N : ℕ), LieMult Xo.univ.t.act (x' ≫ y ≫ pullback.fst _ _) τ N →
      Module.finrank (𝓞 E) P.D.toPre.X ≤ N := by
    intro τ N hN
    have h₅ := (GlobalTheory.lieMult_iff_of_isGrpPullback m'.cart tK.act Xo.univ.t.act m'.act x' τ N).2 hN
    have h₆ := (GlobalTheory.lieMult_iff_of_isGrpPullback m.cart tK.act t.act m.act x' τ N).1 h₅
    rw [hx] at h₆
    obtain ⟨n, -, hn⟩ := GlobalTheory.CharRank.lieMult_unif_loc H R t P K f hf τ N h₆
    omega
  obtain ⟨τ₁, τ₂, h₁, h₂⟩ := GlobalTheory.CharRank.exists_chars H K _ hr
  exact le_min (bound τ₁ _ ((hdet τ₁).1 h₁)) (bound τ₂ _ ((hdet τ₂).2 h₂))

theorem bal_diag_eq {X : Type} [AddCommGroup X] [Module (𝓞 E) X] {β : LinearMap.BilinForm ℤ X}
    (hβ : β ∈ balForms (H.bar : 𝓞 E → 𝓞 E) X) (y : X) : β y y = 2 * β (H.w0 • y) y := by
  obtain ⟨h1, h2⟩ := hβ
  have h := h2 H.w0 y y
  rw [GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, sub_smul, one_smul, map_sub, h1 y (H.w0 • y)] at h
  linarith

theorem spMap_sq {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D] (f : A →+* B) (g : A →+* C)
    (f' : B →+* D) (g' : C →+* D) (h : ∀ a, f' (f a) = g' (g a)) : spMap f' ≫ spMap f = spMap g' ≫ spMap g := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a
  exact h a

theorem spMap_comp_ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]
  rfl

theorem exists_monoFam_through : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ x : S, x ∉ Set.range j → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (C : MonoFam Xo c φ V) (ξV : Sp V ⟶ S), GlobalTheory.Mum.Base V ∧ C.y ≫ j = jK V ≫ ξV ∧ ξV (closedPoint V) = x := by
  intro E _ _ _ H Dw l Xo c φ hpq hpol hnsi Z zs i OZ N d J S π j _ BD hU hsep x hx
  obtain ⟨⟨-, -, -, -, hizs, -, -⟩, -, -, -, ⟨-, hproj, -, hdense, hjπ, -, -, -⟩, -⟩ := hU
  haveI : LocallyOfFiniteType (π ≫ zs) := GlobalTheory.T.locallyOfFiniteType_of_isProjOver c.F S (π ≫ zs) hproj
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)
  obtain ⟨W, _, _, _, _, a, y₀, hy₀, hax⟩ := exists_cdvr_through j hdense x hx
  let b₀ : c.F →+* W := (Spec.preimage (a ≫ π ≫ zs)).hom
  have hb₀ : spMap b₀ = a ≫ π ≫ zs := Spec.map_preimage _
  haveI : CharZero W := charZero_of_injective_ringHom b₀.injective
  have hW : GlobalTheory.Mum.Base W := ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, inferInstance⟩
  obtain ⟨T, f₁, fK₁, -, hloc₁, -, hc₁, hTy⟩ := GlobalTheory.T.exists_unitaryTrait_through_moduliGenericPoint E H Dw l Xo c W hW inferInstance y₀

  haveI := hloc₁
  obtain ⟨_, _, _⟩ := T.cdvr
  haveI : Module.Projective (𝓞 E) T.P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) T.P.D.toPre.X
  haveI : Module.Finite (𝓞 E) T.P.D.toPre.X := Module.Finite.of_restrictScalars_finite ℤ _ _
  have hpolT : IsPolFanOn (H.bar : 𝓞 E → 𝓞 E) φ T.P.D.toPre.X := hpol _ (trait_finrank_le T.gen T.P)
  have hbal : T.be ∈ balForms (H.bar : 𝓞 E → 𝓞 E) T.P.D.toPre.X :=
    (balForms_eq_levelForms H T.P.D.toPre.X).symm ▸ T.lev
  obtain ⟨r, gm, k, cc, hgm, hk, hcc, hsum⟩ := GlobalTheory.Poinc.Cover.exists_cone (𝓞 E) (H.bar : 𝓞 E → 𝓞 E) φ
    T.P.D.toPre.X hpolT T.be hbal (fun y hy => trait_be_pos T hy)
  have hM : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  obtain ⟨T₂, g, gK, e, q, -, hgloc, hgK, hT₂y, hq, hbe⟩ := GlobalTheory.T.exists_unitaryTrait_ramifiedExtension_form_multiple T (k * l.M') (Nat.mul_pos hk hM)
  haveI := hgloc
  obtain ⟨_, _, _⟩ := T₂.cdvr

  have hW₁ : spMap fK₁ ≫ jK W = jK T.V ≫ spMap f₁ := spMap_sq (algebraMap W _) f₁ fK₁ (algebraMap T.V _) hc₁
  have hT₁ : spMap gK ≫ jK T.V = jK T₂.V ≫ spMap g := spMap_sq (algebraMap T.V _) g gK (algebraMap T₂.V _) hgK
  have hy0s : y₀ ≫ pullback.snd _ _ = jK W ≫ spMap b₀ := by
    rw [hb₀, ← hizs, ← hjπ]
    simp only [Category.assoc]
    rw [reassoc_of% hy₀]
  let bb : c.F →+* T₂.V := g.comp (f₁.comp b₀)
  have hover : T₂.y ≫ pullback.snd _ _ = jK T₂.V ≫ spMap bb := by
    rw [hT₂y, hTy]
    simp only [Category.assoc]
    rw [hy0s, reassoc_of% hW₁, reassoc_of% hT₁]
    simp only [bb, spMap_comp_, Category.assoc]
  have hev : ∀ i z, gm i z z = 2 * gm i (H.w0 • z) z := fun i z => bal_diag_eq (hgm.mem i) z
  have hnn : ∀ i z, 0 ≤ gm i (H.w0 • z) z := fun i z => by
    have := hgm.nonneg i z
    rw [hev] at this
    omega
  have hsumz : ∀ z, (k : ℤ) * T.be z z = ∑ i, (cc i : ℤ) * gm i z z := fun z => by
    have := congrArg (fun β : LinearMap.BilinForm ℤ T.P.D.toPre.X => β z z) hsum
    simpa [LinearMap.sum_apply, nsmul_eq_mul] using this
  have hmono : IsMonomial T₂.P.D.toPre (fun i => T₂.ϖ ^ (q * cc i))
      (fun i => (l.M' : ℤ) • pull e.symm.toLinearMap (gm i)) := by
    intro y
    obtain ⟨u, n₀, hn₀, hψ⟩ := T₂.mono y
    have hy : y = e (e.symm y) := (e.apply_symm_apply y).symm
    set z := e.symm y
    refine ⟨u, fun i => (l.M' * gm i (H.w0 • z) z).toNat, fun i => ?_, ?_⟩
    · simp only [LinearMap.smul_apply, pull_apply, LinearEquiv.coe_coe, smul_eq_mul]
      rw [Int.toNat_of_nonneg (mul_nonneg (by positivity) (hnn i z)), hev]
      ring
    · convert hψ using 2
      rw [Fin.prod_univ_one]
      simp only [Matrix.cons_val_zero, ← pow_mul, Finset.prod_pow_eq_pow_sum]
      congr 1
      have h0 : T₂.be y y = 2 * n₀ 0 := by simpa using hn₀ 0
      rw [hy, hbe] at h0
      have hz := hsumz z
      have hcast : ((∑ i, q * cc i * (l.M' * gm i (H.w0 • z) z).toNat : ℕ) : ℤ) =
          ∑ i, (q : ℤ) * cc i * (l.M' * gm i (H.w0 • z) z) := by
        push_cast
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Int.toNat_of_nonneg (mul_nonneg (by positivity) (hnn i z))]
      have hz2 : (k : ℤ) * T.be z z = 2 * ∑ i, (cc i : ℤ) * gm i (H.w0 • z) z := by
        rw [hz, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hev]
        ring
      have hS : ∑ i, (q : ℤ) * cc i * (l.M' * gm i (H.w0 • z) z) =
          (q * l.M') * ∑ i, (cc i : ℤ) * gm i (H.w0 • z) z := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      have h2 : (2 : ℤ) * (∑ i, (q : ℤ) * cc i * (l.M' * gm i (H.w0 • z) z)) = 2 * (n₀ 0 : ℤ) := by
        rw [← h0, hS]
        push_cast
        linear_combination (-((q : ℤ) * l.M')) * hz2
      have h3 := mul_left_cancel₀ (two_ne_zero) h2
      exact_mod_cast hcast.trans h3
  let C : MonoFam Xo c φ T₂.V :=
    { b := bb, t := T₂.t, P := T₂.P, y := T₂.y, y_over := hover, gen := T₂.gen, m := r,
      s := fun i => T₂.ϖ ^ (q * cc i),
      s_mem := fun i => Ideal.pow_mem_of_mem _ ((mem_maximalIdeal _).2 T₂.irr.not_isUnit) _
        (Nat.mul_pos hq (hcc i)),
      δ := fun i => pull e.symm.toLinearMap (gm i), cone := hgm.pull_equiv e.symm,
      rank := trait_finrank_le T₂.gen T₂.P, mono := hmono }
  have hcomp : C.y ≫ j = jK T₂.V ≫ (spMap (g.comp f₁) ≫ a) := by
    show T₂.y ≫ j = _
    rw [hT₂y, hTy]
    simp only [Category.assoc]
    rw [hy₀, reassoc_of% hW₁, reassoc_of% hT₁, spMap_comp_]
    simp only [Category.assoc]
  have hcl : (spMap (g.comp f₁) ≫ a) (closedPoint T₂.V) = x := by
    have h1 : spMap (g.comp f₁) (closedPoint T₂.V) = closedPoint W := IsLocalRing.comap_closedPoint (g.comp f₁)
    change a (spMap (g.comp f₁) (closedPoint T₂.V)) = x
    rw [h1, hax]
  exact ⟨T₂.V, inferInstance, inferInstance, inferInstance, C, spMap (g.comp f₁) ≫ a,
    ⟨⟨inferInstance, inferInstance, inferInstance, ‹_›⟩, ‹_›⟩, hcomp, hcl⟩

end GlobalTheory.UChartTrait
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrAlgClosedResidueInjectiveLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperRestrictOfPsiUnitOn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
noncomputable section
namespace GlobalTheory.UnifProperChar
section Inertia

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusExt GlobalTheory.BXOf GlobalTheory.UnramTorsion

attribute [local instance] gtGroup

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

end Inertia

section Reduction

open GlobalTheory.Published GlobalTheory.Published.AbVarRed

end Reduction

theorem exists_dvr_centre (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R) [I.IsPrime] :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (φ : R →+* V),
      IsAlgClosed (ResidueField V) ∧ Function.Injective φ ∧ (maximalIdeal V).comap φ = I := by
  obtain ⟨V, _, _, _, φ, hφ, hc⟩ : ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (φ : R →+* V), Function.Injective φ ∧ (maximalIdeal V).comap φ = I := by
    rcases eq_or_ne I ⊥ with rfl | hI
    · let K := FractionRing R
      let φ : R →+* PowerSeries K := (PowerSeries.C (R := K)).comp (algebraMap R K)
      have hφ : Function.Injective φ := PowerSeries.C_injective.comp (IsFractionRing.injective R K)
      refine ⟨PowerSeries K, inferInstance, inferInstance, inferInstance, φ, hφ, ?_⟩
      refine eq_bot_iff.2 fun r hr => ?_
      rw [Ideal.mem_comap, PowerSeries.maximalIdeal_eq_span_X, Ideal.mem_span_singleton,
        PowerSeries.X_dvd_iff] at hr
      have : algebraMap R K r = 0 := by simpa [φ] using hr
      exact (Ideal.mem_bot).2 (IsFractionRing.injective R K (this.trans (map_zero _).symm))
    · obtain ⟨V, _, _, hV, -, φ, h1, h2⟩ :=
        exists_complete_discreteValuationRing_of_prime_lt ⊥ I (bot_lt_iff_ne_bot.2 hI)
      exact ⟨V, inferInstance, inferInstance, hV, φ, (RingHom.injective_iff_ker_eq_bot φ).2 h1, h2⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨V', _, _, _, _, h1, h2, -, h3⟩ := GlobalTheory.ClosedResidueExt.exists_unramified_ext V hπ
  refine ⟨V', inferInstance, inferInstance, inferInstance, (algebraMap V V').comp φ, h3, h1.comp hφ, ?_⟩
  rw [← Ideal.comap_comap, ← hc]
  congr 1
  exact eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (algebraMap_isIntegral_iff.mpr h2) (maximalIdeal V'))

end GlobalTheory.UnifProperChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrAlgClosedResidueInjectiveLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompleteClosedDvr

theorem exists_complete_dvr_isAlgClosed : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V], ¬ IsField V → Nonempty (ℚ →+* V) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (ρ : V →+* W), IsAdicComplete (maximalIdeal W) W ∧ IsAlgClosed (ResidueField W) ∧ Function.Injective ρ ∧ IsLocalHom ρ := by
  intro V _ _ _ _ _ _
  obtain ⟨D, _, _, _, φ, hac, hinj, hc⟩ := GlobalTheory.UnifProperChar.exists_dvr_centre V (maximalIdeal V)
  have : IsLocalHom φ := ((IsLocalRing.local_hom_tfae φ).out 1 5).mpr hc
  have hb := AdicCompletion.residueField_map_bijective_of_fg (R := D)
    (maximalIdeal D).fg_of_isNoetherianRing
  refine ⟨AdicCompletion (maximalIdeal D) D, inferInstance, inferInstance, inferInstance,
    (algebraMap D _).comp φ, inferInstance, ?_,
    (GlobalTheory.injective_and_isLocalHom_adicCompletion_comp φ hinj).1,
    (GlobalTheory.injective_and_isLocalHom_adicCompletion_comp φ hinj).2⟩
  exact IsAlgClosed.of_ringEquiv (ResidueField D) _ (RingEquiv.ofBijective _ hb)

end GlobalTheory.CompleteClosedDvr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrAlgClosedResidueInjectiveLocalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complete_dvr_algClosed_residue_injective_local : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V], ¬ IsField V → Nonempty (ℚ →+* V) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (ρ : V →+* W), IsAdicComplete (maximalIdeal W) W ∧ IsAlgClosed (ResidueField W) ∧ Function.Injective ρ ∧ IsLocalHom ρ := by
  first | exact @GlobalTheory.CompleteClosedDvr.exists_complete_dvr_isAlgClosed | exact GlobalTheory.CompleteClosedDvr.exists_complete_dvr_isAlgClosed | (intros; apply GlobalTheory.CompleteClosedDvr.exists_complete_dvr_isAlgClosed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegeneratingMonomialFamilyAlgClosedResidue
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UChartGeo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {φ : InvFun (𝓞 E)}

theorem nontrivial_of_not_mem_range {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : GlobalTheory.Mum.Base V)
    (C : MonoFam Xo c φ V) {S T : Scheme.{0}} (s : S ⟶ T) [IsSeparated s] (j : Xo.XF c ⟶ S) (ξV : Sp V ⟶ S)
    (hs : ∀ f g : Sp V ⟶ S, jK V ≫ f = jK V ≫ g → f ≫ s = g ≫ s)
    (hy : C.y ≫ j = jK V ≫ ξV) (hx : ξV (closedPoint V) ∉ Set.range j) : Nontrivial C.P.D.toPre.X := by
  by_contra hX
  rw [not_nontrivial_iff_subsingleton] at hX
  haveI : IsEmpty (Fin C.m) := ⟨fun i =>
    C.cone.linearIndependent.ne_zero i (LinearMap.ext₂ fun a b => by
      rw [Subsingleton.elim a 0]; simp)⟩
  have hprod : ∏ i, C.s i = 1 := by simp [Finset.univ_eq_empty]
  obtain ⟨yo, -, -, -, hg⟩ := GlobalTheory.T.openPart_classified_monomialBoundaryFamily Xo c φ V hV C
  let A := Localization.Away (∏ i, C.s i)
  let e : V ≃ₐ[V] A := IsLocalization.atUnit V A (∏ i, C.s i) (by rw [hprod]; exact isUnit_one)
  let h : A →+* V := e.symm.toRingEquiv.toRingHom
  have hcomp : h.comp (algebraMap V A) = RingHom.id V := by
    ext r
    show e.symm (algebraMap V A r) = r
    exact e.symm.commutes r
  have hid : spMap h ≫ spMap (algebraMap V A) = 𝟙 _ := by
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
    exact Spec.map_id _
  have hψ : jK V ≫ spMap h ≫ yo = C.y := by
    rw [← Category.assoc]
    exact hg _ (by rw [Category.assoc, hid, Category.comp_id])
  have hgen : jK V ≫ (spMap h ≫ yo) ≫ j = jK V ≫ ξV := by
    rw [← Category.assoc, hψ, hy]
  haveI : IsDominant (jK V) := (GlobalTheory.Mum.Modif.self V).dominant
  have heq : (spMap h ≫ yo) ≫ j = ξV :=
    ext_of_isDominant_of_isSeparated s (hs _ _ hgen) (jK V) hgen
  exact hx ⟨(spMap h ≫ yo) (closedPoint V), by
    show ((spMap h ≫ yo) ≫ j) (closedPoint V) = _
    rw [heq]⟩

end GlobalTheory.UChartGeo

namespace GlobalTheory.UChartGeo


set_option maxHeartbeats 1000000 in
theorem exists_monoFam_algClosed : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ x : S, x ∉ Set.range j → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (C : MonoFam Xo c φ V) (ξV : Sp V ⟶ S), GlobalTheory.Mum.Base V ∧ IsAlgClosed (ResidueField V) ∧ Nontrivial C.P.D.toPre.X ∧ C.y ≫ j = jK V ≫ ξV ∧ ξV (closedPoint V) = x := by
  intro E _ _ _ H Dw l Xo c φ hpq hpf hns Z zs i OZ N d J S π j _ BD hU hS x hx
  obtain ⟨V, _, _, _, C, ξV, hV, hy, hxV⟩ :=
    GlobalTheory.UChartTrait.exists_monoFam_through Xo c φ hpq hpf hns zs i OZ N d J π j BD hU hS x hx
  obtain ⟨Nn, ιP, hci, hι⟩ := hU.2.2.2.2.1.2.1
  haveI : IsSeparated (π ≫ zs) := by rw [← hι]; infer_instance
  haveI : IsDominant (jK V) := (GlobalTheory.Mum.Modif.self V).dominant
  have hs : ∀ f g : Sp V ⟶ S, jK V ≫ f = jK V ≫ g → f ≫ π ≫ zs = g ≫ π ≫ zs := fun f g hfg =>
    ext_of_isDominant_of_isSeparated (terminal.from (Sp c.F)) (terminal.hom_ext _ _) (jK V) (by
      rw [← Category.assoc, hfg, Category.assoc])
  have hX : Nontrivial C.P.D.toPre.X :=
    nontrivial_of_not_mem_range hV C (π ≫ zs) j ξV hs hy (hxV ▸ hx)
  obtain ⟨y0, hy0⟩ := exists_ne (0 : C.P.D.toPre.X)
  obtain ⟨i0, -⟩ := C.mono.exists_pos (maximalIdeal.isMaximal _).ne_top hy0
  have hnf : ¬ IsField V := by
    intro hf
    have hm := C.s_mem i0
    rw [(IsLocalRing.isField_iff_maximalIdeal_eq).1 hf, Ideal.mem_bot] at hm
    exact C.s_ne_zero i0 hm
  haveI : IsNoetherianRing V := hV.1.1
  haveI : CharZero V := hV.2
  obtain ⟨W, _, _, _, ρ, hcomp, hac, hinj, hloc⟩ := GlobalTheory.T.exists_complete_dvr_algClosed_residue_injective_local V hnf ⟨C.b.comp (algebraMap ℚ c.F)⟩
  haveI : CharZero W := charZero_of_injective_ringHom hinj
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hne : ∀ k, ρ (C.s k) ≠ 0 := fun k h0 => C.s_ne_zero k (hinj (h0.trans (map_zero ρ).symm))
  choose w u hwu using fun k => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hne k) hϖ
  have hW : GlobalTheory.UU.CDVR W := ⟨inferInstance, hcomp, inferInstance⟩
  obtain ⟨t, P, e, be, -, htK, hbe, -, hmono, -⟩ := trait_pull C hV W hW ϖ ρ hinj hloc w u hwu
  have hinj' : Function.Injective ((algebraMap W (FractionRing W)).comp ρ) :=
    (IsFractionRing.injective W (FractionRing W)).comp hinj
  obtain ⟨gam, hgam⟩ : ∃ gam : FractionRing V →+* FractionRing W,
      gam.comp (algebraMap V (FractionRing V)) = (algebraMap W (FractionRing W)).comp ρ :=
    ⟨IsFractionRing.lift hinj', RingHom.ext fun r => by
      rw [RingHom.comp_apply, RingHom.comp_apply]; exact IsFractionRing.lift_algebraMap hinj' r⟩
  have hκ : spMap gam ≫ jK V = jK W ≫ spMap ρ := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hgam]
  obtain ⟨tK, h1, h2⟩ := htK (spMap gam) hκ
  have hover : (spMap gam ≫ C.y) ≫ pullback.snd _ _ = jK W ≫ spMap (ρ.comp C.b) := by
    rw [Category.assoc, C.y_over, ← Category.assoc, hκ, Category.assoc]
    congr 1
    exact (Spec.map_comp (CommRingCat.ofHom C.b) (CommRingCat.ofHom ρ)).symm
  let F : Fam Xo c W := ⟨ρ.comp C.b, t, P, spMap gam ≫ C.y, hover, ⟨tK, h1, h2⟩⟩
  let β : LinearMap.BilinForm ℤ P.D.toPre.X := ∑ k, (w k : ℤ) • pull e.toLinearMap (C.δ k)
  have hβ : β ∈ balForms H.bar P.D.toPre.X :=
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (pull_mem _ (C.cone.mem k))
  have hbeq : be = (l.M' : ℤ) • β := by
    rw [hbe, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ext a b
    simp only [LinearMap.smul_apply, pull_apply, smul_eq_mul]
    ring
  have hmono' : IsMonomial F.P.D.toPre ![ϖ] ![(l.M' : ℤ) • β] := hbeq ▸ hmono
  have hϖm : ϖ ∈ maximalIdeal W := (mem_maximalIdeal _).2 hϖ.not_isUnit
  obtain ⟨C', hC'⟩ := F.exists_monoFam hpf hϖm hβ hmono'
  have hyC : C'.toFam.y = spMap gam ≫ C.y := by rw [hC']
  refine ⟨W, inferInstance, inferInstance, inferInstance, C', spMap ρ ≫ ξV,
    ⟨⟨inferInstance, inferInstance, inferInstance, hcomp⟩, inferInstance⟩, hac, ?_, ?_, ?_⟩
  · rw [hC']
    exact e.symm.injective.nontrivial
  · show C'.toFam.y ≫ j = _
    rw [hyC, Category.assoc, hy, ← Category.assoc, hκ, Category.assoc]
  · show ξV (spMap ρ (closedPoint W)) = x
    have hcl : spMap ρ (closedPoint W) = closedPoint V := IsLocalRing.comap_closedPoint ρ
    rw [hcl, hxV]

end GlobalTheory.UChartGeo
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegeneratingMonomialFamilyAlgClosedResidueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degenerating_monomialFamily_algClosed_residue : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ x : S, x ∉ Set.range j → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (C : MonoFam Xo c φ V) (ξV : Sp V ⟶ S), GlobalTheory.Mum.Base V ∧ IsAlgClosed (ResidueField V) ∧ Nontrivial C.P.D.toPre.X ∧ C.y ≫ j = jK V ≫ ξV ∧ ξV (closedPoint V) = x := by
  first | exact @GlobalTheory.UChartGeo.exists_monoFam_algClosed | exact GlobalTheory.UChartGeo.exists_monoFam_algClosed | (intros; apply GlobalTheory.UChartGeo.exists_monoFam_algClosed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointRigidTautologicalChartUnitaryBoundary
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem exists_tautB_chart_at : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ x : S, x ∉ Set.range j → ∃ (k : Type) (_ : Field k) (m e : ℕ) (C : MonoFam Xo c φ (ChartRing k m e)) (ξ : Sp (ChartRing k m e) ⟶ S), IsTautB C ∧ C.y ≫ j = jK _ ≫ ξ ∧ ξ (closedPoint _) = x := by
  intro E _ _ _ H Dw l Xo c φ hpq hpol hns Z zs i OZ N d J S π j _ BD hU hS x hx
  obtain ⟨V, _, _, _, C, ξV, hB, hac, hnt, hC, hV⟩ :=
    GlobalTheory.T.exists_degenerating_monomialFamily_algClosed_residue Xo c φ hpq hpol hns zs i OZ N d J π j BD hU hS x hx
  obtain ⟨k, _, m, e, C₁, ξ, θ, hT, hC₁, hθ, hξ⟩ :=
    GlobalTheory.T.exists_tautological_chart_versality Xo c φ hpq hpol hns zs i OZ N d J π j BD hU hS V hB hac C ξV hnt hC
  refine ⟨k, inferInstance, m, e, C₁, ξ, hT, hC₁, ?_⟩
  rw [← hV, ← hξ]
  change _ = ξ.base ((spMap θ).base (closedPoint V))
  have h0 : (spMap θ).base (closedPoint V) = closedPoint (ChartRing k m e) := by
    haveI := hθ
    exact IsLocalRing.comap_closedPoint θ
  rw [h0]

end GlobalTheory.UCanon
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointRigidTautologicalChartUnitaryBoundaryStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pointRigid_tautological_chart_unitary_boundary : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ x : S, x ∉ Set.range j → ∃ (k : Type) (_ : Field k) (m e : ℕ) (C : MonoFam Xo c φ (ChartRing k m e)) (ξ : Sp (ChartRing k m e) ⟶ S), IsTautB C ∧ C.y ≫ j = jK _ ≫ ξ ∧ ξ (closedPoint _) = x := by
  first | exact @GlobalTheory.UCanon.exists_tautB_chart_at | exact GlobalTheory.UCanon.exists_tautB_chart_at | (intros; apply GlobalTheory.UCanon.exists_tautB_chart_at <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartBoundaryEquations
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealEqSpanMonomialOfOrdersAlongCompleteDVRStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_eq_span_monomial_of_orders_along_completeDVR : ∀ (k : Type) [Field k] [CharZero k] (m e : ℕ) (I : Ideal (ChartRing k m e)) (a : Fin m → ℕ), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ ψ : ChartRing k m e →+* W, Function.Injective ψ → IsLocalHom ψ → I.map ψ = Ideal.span {ψ (∏ i, bdParam k m e i ^ a i)}) → I = Ideal.span {∏ i, bdParam k m e i ^ a i} := by
  first | exact @GlobalTheory.MonoVal.eq_span_monomial_of_forall_cdvr | exact GlobalTheory.MonoVal.eq_span_monomial_of_forall_cdvr | (intros; apply GlobalTheory.MonoVal.eq_span_monomial_of_forall_cdvr <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartBoundaryEquations
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanonBd

theorem prime_X {σ A : Type} [CommRing A] [IsDomain A] (i : σ) : Prime (MvPowerSeries.X i : MvPowerSeries σ A) := by
  classical
  have key : ∀ f : MvPowerSeries σ A, MvPowerSeries.X i ∣ f ↔ (1 : ℕ∞) ≤ f.weightedOrder (Pi.single i 1) := fun f => by
    have hw : ∀ d : σ →₀ ℕ, Finsupp.weight (Pi.single i 1 : σ → ℕ) d = d i := fun d => by
      rw [Finsupp.weight_single_one_apply]
    rw [MvPowerSeries.X_dvd_iff]
    refine ⟨fun h => ?_, fun h d hd => ?_⟩
    · exact MvPowerSeries.nat_le_weightedOrder _ (n := 1) fun d hd => h d (by rw [hw] at hd; omega)
    · exact MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder _ (lt_of_lt_of_le (by rw [hw, hd]; simp) h)
  refine ⟨fun h => ?_, fun h => ?_, fun f g h => ?_⟩
  · simpa [MvPowerSeries.coeff_X] using congrArg (MvPowerSeries.coeff (Finsupp.single i 1)) h
  · simpa using h.map MvPowerSeries.constantCoeff
  · rw [key, MvPowerSeries.weightedOrder_mul] at h
    rw [key, key]
    by_contra hn
    simp only [not_or, not_le, Order.lt_one_iff] at hn
    simp [hn.1, hn.2] at h

theorem isRadical_span_prod_X {σ A : Type} [CommRing A] [IsDomain A] {m : ℕ} (v : Fin m → σ) (hv : Function.Injective v) :
    (Ideal.span {∏ i, (MvPowerSeries.X (v i) : MvPowerSeries σ A)}).IsRadical := by
  classical
  intro x hx
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.1 hx
  rw [Ideal.mem_span_singleton] at hn ⊢
  refine GlobalTheory.RelParamRad.prod_dvd_of_forall_dvd m _ (fun i => prime_X (v i)) (fun i j hij => ?_) x
    fun i => (prime_X (v i)).dvd_of_dvd_pow ((Finset.dvd_prod_of_mem _ (Finset.mem_univ i)).trans hn)
  by_contra hne
  have := MvPowerSeries.X_dvd_iff.1 hij (Finsupp.single (v j) 1)
    (Finsupp.single_eq_of_ne fun h => hne (hv h))
  simp [MvPowerSeries.coeff_X] at this

theorem mem_support_of_idlAlong_le {S : Scheme.{0}} (I : S.IdealSheafData) {R : Type} [CommRing R] [IsLocalRing R]
    (ξ : Sp R ⟶ S) (p : Sp R) (h : idlAlong I ξ ≤ p.asIdeal) : ξ p ∈ I.support := by
  have idlAlong_comp_local {X : Scheme.{0}} (J : X.IdealSheafData) {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S]
      [IsLocalRing S] (χ : Sp R ⟶ X) (f : R →+* S) : idlAlong J (spMap f ≫ χ) = (idlAlong J χ).map f := by
    have eq_map {A : Type} [CommRing A] [IsLocalRing A] (ψ : Sp A ⟶ X)
        (U : X.affineOpens) (hle : ⊤ ≤ ψ ⁻¹ᵁ U.1) :
        idlAlong J ψ = (J.ideal U).map (ψ.appLE U.1 ⊤ hle ≫ (Scheme.ΓSpecIso (.of A)).hom).hom := by
      have hx : ψ (closedPoint A) ∈ U.1 := hle trivial
      unfold idlAlong
      rw [ds_stalkId_eq_map J U _ hx, Ideal.map_map, ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
      congr 2
    obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (show χ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
    have hle : ⊤ ≤ χ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem χ hx).ge
    have hle' : ⊤ ≤ (spMap f ≫ χ) ⁻¹ᵁ U := fun x _ => hle (show spMap f x ∈ (⊤ : (Sp R).Opens) from trivial)
    rw [eq_map χ ⟨U, hU⟩ hle, eq_map _ ⟨U, hU⟩ hle', Ideal.map_map]
    congr 1
    have e : (spMap f ≫ χ).appLE U ⊤ hle' = χ.appLE U ⊤ hle ≫ (spMap f).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    rw [e, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc, CommRingCat.hom_comp]
    rfl
  haveI : p.asIdeal.IsPrime := PrimeSpectrum.isPrime p
  let lo := algebraMap R (Localization.AtPrime p.asIdeal)
  have e : (spMap lo ≫ ξ) (closedPoint (Localization.AtPrime p.asIdeal)) = ξ p := by
    change ξ (spMap lo (closedPoint _)) = ξ p
    congr 1
    apply PrimeSpectrum.ext
    exact Localization.AtPrime.under_maximalIdeal
  rw [← e]
  refine (mem_support_iff_stalkId I _).2 fun htop => ?_
  have h₁ : idlAlong I (spMap lo ≫ ξ) = ⊤ := by rw [idlAlong, htop, Ideal.map_top]
  rw [idlAlong_comp_local] at h₁
  have h₂ : (idlAlong I ξ).map lo ≤ maximalIdeal _ :=
    (Ideal.map_mono h).trans (Localization.AtPrime.map_eq_maximalIdeal).le
  exact (maximalIdeal.isMaximal _).ne_top (top_le_iff.1 (h₁ ▸ h₂))

theorem mem_range_of_away {X S : Scheme.{0}} [S.IsSeparated] (j : X ⟶ S) {R : Type} [CommRing R] [IsDomain R]
    (ξ : Sp R ⟶ S) (y : Sp (FractionRing R) ⟶ X) (hy : y ≫ j = jK R ≫ ξ) (f : R) (yo : Sp (Localization.Away f) ⟶ X)
    (hyo : ∀ g : Sp (FractionRing R) ⟶ Sp (Localization.Away f),
      g ≫ spMap (algebraMap R (Localization.Away f)) = jK R → g ≫ yo = y)
    (p : Sp R) (hp : f ∉ p.asIdeal) : ξ p ∈ Set.range j := by
  have hf : f ≠ 0 := fun h => hp (h ▸ p.asIdeal.zero_mem)
  have hle : Submonoid.powers f ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  haveI : IsDomain (Localization.Away f) := IsLocalization.isDomain_localization hle
  have hu : ∀ x : Submonoid.powers f, IsUnit (algebraMap R (FractionRing R) x) := fun x =>
    IsLocalization.map_units (FractionRing R) (⟨x.1, hle x.2⟩ : nonZeroDivisors R)
  let lf : Localization.Away f →+* FractionRing R := IsLocalization.lift hu
  let lo := spMap (algebraMap R (Localization.Away f))
  let κ : Sp (FractionRing R) ⟶ Sp (Localization.Away f) := spMap lf
  have hκ : κ ≫ lo = jK R := by
    rw [← Spec.map_comp]
    exact congrArg spMap (IsLocalization.lift_comp hu)
  have hinj : Function.Injective lf := by
    refine (IsLocalization.lift_injective_iff hu).2 fun x x' => ?_
    rw [(IsLocalization.injective (Localization.Away f) hle).eq_iff, (IsFractionRing.injective R (FractionRing R)).eq_iff]
  haveI hdom : IsDominant κ := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical lf).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot lf).1 hinj]; exact bot_le)⟩
  have hξ : lo ≫ ξ = yo ≫ j := by
    refine ext_of_isDominant κ ?_
    rw [← Category.assoc, hκ, ← hy, ← Category.assoc, hyo κ hκ]
  have hq : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) := by
    rw [PrimeSpectrum.localization_away_comap_range _ f]
    exact hp
  obtain ⟨q, hq⟩ := hq
  refine ⟨yo q, ?_⟩
  change (yo ≫ j) q = ξ p
  rw [← hξ, ← hq]
  rfl

theorem boundary_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTautB C → ∀ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ → (∀ p : Sp (ChartRing k m e), ξ p ∈ Set.range j ↔ ∏ i, C.s i ∉ p.asIdeal) ∧ idlAlong (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl) ξ = Ideal.span {∏ i, C.s i} ∧ ∃ a : Fin C.m → ℕ, (∀ i, (a i : ℝ) = d * φ.evalZ ((l.M' : ℤ) • C.δ i)) ∧ idlAlong BD.idealSheaf ξ = Ideal.span {∏ i, C.s i ^ a i} := by
  intro E _ _ _ H Dw l Xo c φ hpq hφ hns Z zs i OZ N d J S π j _ BD hP hS k _ m e C hT ξ hy
  have idlAlong_comp_local {X : Scheme.{0}} (J : X.IdealSheafData) {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S]
      [IsLocalRing S] (χ : Sp R ⟶ X) (f : R →+* S) : idlAlong J (spMap f ≫ χ) = (idlAlong J χ).map f := by
    have eq_map {A : Type} [CommRing A] [IsLocalRing A] (ψ : Sp A ⟶ X)
        (U : X.affineOpens) (hle : ⊤ ≤ ψ ⁻¹ᵁ U.1) :
        idlAlong J ψ = (J.ideal U).map (ψ.appLE U.1 ⊤ hle ≫ (Scheme.ΓSpecIso (.of A)).hom).hom := by
      have hx : ψ (closedPoint A) ∈ U.1 := hle trivial
      unfold idlAlong
      rw [ds_stalkId_eq_map J U _ hx, Ideal.map_map, ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
      congr 2
    obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (show χ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
    have hle : ⊤ ≤ χ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem χ hx).ge
    have hle' : ⊤ ≤ (spMap f ≫ χ) ⁻¹ᵁ U := fun x _ => hle (show spMap f x ∈ (⊤ : (Sp R).Opens) from trivial)
    rw [eq_map χ ⟨U, hU⟩ hle, eq_map _ ⟨U, hU⟩ hle', Ideal.map_map]
    congr 1
    have e : (spMap f ≫ χ).appLE U ⊤ hle' = χ.appLE U ⊤ hle ≫ (spMap f).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    rw [e, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc, CommRingCat.hom_comp]
    rfl
  have hEt := GlobalTheory.T.tautologicalChart_isEtaleCompletion_localRing Xo c φ hpq hφ hns zs i OZ N d J π j BD hP hS C hT ξ hy
  obtain ⟨-, -, -, ⟨hd, hJ, -⟩, ⟨-, hproj, -, -, -, hπ, hBD, hval⟩, -⟩ := hP
  obtain ⟨hm, hs, ⟨yo, -, -, -, hyo⟩, -⟩ := hT.1
  haveI : CharZero (ChartRing k m e) := (C.b.charZero_iff C.b.injective).1 inferInstance
  haveI : CharZero k := RingHom.charZero (algebraMap k (ChartRing k m e))
  have hA := GlobalTheory.MumfordChart.admissibleBase_chartRing k m e
  haveI : IsProper (π ≫ zs) := by
    obtain ⟨n, lo, hlo, h⟩ := hproj
    have := isProper_str c.F n
    rw [← h]
    infer_instance
  haveI : S.IsSeparated := by
    constructor
    rw [← terminal.comp_from (π ≫ zs)]
    infer_instance

  haveI := GlobalTheory.PointStepCompare.projective_of_free E (X := C.P.D.toPre.X)
  have hF := hφ C.P.D.toPre.X C.rank
  have hM : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  have hex : ∀ i, ∃ a : ℕ, 0 < a ∧ (a : ℝ) = d * φ.evalZ ((l.M' : ℤ) • C.δ i) := fun i => by
    obtain ⟨n, hn⟩ := hF.exists_nat (C.cone.mem i) (C.cone.nonneg i)
    have h0 := hF.pos _ (C.cone.mem i) (C.cone.nonneg i) (C.cone.linearIndependent.ne_zero i)
    rw [hn] at h0
    refine ⟨d * (l.M' * n), by have : 0 < n := by exact_mod_cast h0
                               positivity, ?_⟩
    rw [C.cone.evalZ_smul, hn]
    push_cast
    rfl
  choose a ha0 ha using hex
  have hprod : ∀ b : Fin C.m → ℕ, ∏ i, C.s i ^ b i = ∏ i, bdParam k m e i ^ b (Fin.cast hm.symm i) := fun b =>
    Fintype.prod_equiv (finCongr hm) _ _ fun i => by rw [hs]; rfl
  have hs0 : ∀ i, C.s i ≠ 0 := fun i => by rw [hs]; exact (prime_X _).ne_zero

  have hdiv : idlAlong BD.idealSheaf ξ = Ideal.span {∏ i, C.s i ^ a i} := by
    rw [hprod]
    refine GlobalTheory.T.ideal_eq_span_monomial_of_orders_along_completeDVR k m e _ _ fun W _ _ _ hW ψ hψ hψl => ?_
    rw [← hprod, ← idlAlong_comp_local]
    haveI : IsDiscreteValuationRing W := hW.1
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
    choose w hw using fun i => IsDiscreteValuationRing.associated_pow_irreducible
      ((map_ne_zero_iff ψ hψ).2 (hs0 i)) hϖ
    have hκ : spMap (GlobalTheory.ArcPull.fracMap hψ) ≫ jK _ = jK W ≫ spMap ψ :=
      (GlobalTheory.ArcPull.fracMap_sq hψ).symm.trans (Category.id_comp _)
    obtain ⟨t, tK, P, h₁, h₂, be, hbe, hmon, hev⟩ :=
      GlobalTheory.T.monomialBoundaryFamily_pull_unitaryTrait_form Xo c φ _ ⟨hA, inferInstance⟩ C W hW ψ hψ hψl ϖ hϖ w hw _ hκ
    obtain ⟨n, hn, hI⟩ := hval W hW ϖ hϖ (spMap ψ ≫ ξ) _ (by rw [Category.assoc, hy, reassoc_of% hκ]) t tK h₁ h₂ P be hbe hmon
    have hn' : n = ∑ i, w i * a i := by
      apply Nat.cast_injective (R := ℝ)
      rw [hn, hev, Finset.mul_sum]
      push_cast
      exact Finset.sum_congr rfl fun i _ => by rw [ha]; ring
    rw [hI, hn', Ideal.span_singleton_eq_span_singleton, map_prod, ← Finset.prod_pow_eq_pow_sum]
    exact Associated.prod _ _ _ fun i _ => by rw [map_pow, pow_mul]; exact (hw i).symm.pow_pow

  have hset : ∀ p : Sp (ChartRing k m e), ξ p ∈ Set.range j ↔ ∏ i, C.s i ∉ p.asIdeal := fun p => by
    refine ⟨fun h hp => ?_, mem_range_of_away j ξ C.y hy _ yo hyo p⟩
    have h₁ : ξ p ∈ BD.idealSheaf.support := by
      refine mem_support_of_idlAlong_le _ ξ p ?_
      rw [hdiv, Ideal.span_singleton_le_iff_mem]
      exact Ideal.mem_of_dvd _ (Finset.prod_dvd_prod_of_dvd _ _ fun i _ => dvd_pow_self _ (ha0 i).ne') hp
    rw [hBD, Scheme.IdealSheafData.support_comap] at h₁
    rw [← hπ] at h
    exact hJ _ h₁ h
  refine ⟨hset, ?_, a, ha, hdiv⟩
  haveI := GlobalTheory.GenFan.essFiniteType_int_stalk c.F S (π ≫ zs) (ξ (closedPoint _))
  haveI := hA.1
  refine GlobalTheory.PolDeg.idlAlong_vanishingIdeal_compl S j.opensRange _ ξ _ ?_ (fun p => ?_)
    (GlobalTheory.EtaleCompletionRadical.isRadical_map_of_isEtaleCompletion _ _ _ hA.2.2.2 hEt
      (GlobalTheory.GenFan.formallyUnramified_residue_comp_of_isEtaleCompletion k m e _ hEt))
  · simp only [hs]
    exact isRadical_span_prod_X (fun i => Sum.inl (Fin.cast hm i)) (Sum.inl_injective.comp (Fin.cast_injective hm))
  · rw [Scheme.Hom.coe_opensRange]
    exact hset p

end GlobalTheory.UCanonBd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartBoundaryEquationsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tautologicalChart_boundary_equations : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTautB C → ∀ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ → (∀ p : Sp (ChartRing k m e), ξ p ∈ Set.range j ↔ ∏ i, C.s i ∉ p.asIdeal) ∧ idlAlong (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl) ξ = Ideal.span {∏ i, C.s i} ∧ ∃ a : Fin C.m → ℕ, (∀ i, (a i : ℝ) = d * φ.evalZ ((l.M' : ℤ) • C.δ i)) ∧ idlAlong BD.idealSheaf ξ = Ideal.span {∏ i, C.s i ^ a i} := by
  first | exact @GlobalTheory.UCanonBd.boundary_eq | exact GlobalTheory.UCanonBd.boundary_eq | (intros; apply GlobalTheory.UCanonBd.boundary_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTripleChartUnitaryBoundaryPointRigid
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem uPre_of_boundary_pointRigid {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (hpq : 1 ≤ Dw.p + Dw.q)
    (hφ : IsPolFan H.bar (min Dw.p Dw.q) φ) (hns : NoSelfInt H.bar (min Dw.p Dw.q) φ)
    {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData)
    {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S)
    (hP : GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD) (hS : SepB Xo c φ j)
    (x : S) (hx : x ∉ Set.range j) : UPre Xo c φ j BD d x := by
  obtain ⟨k, _, m, e, C, ξ, hT, hy, hξ⟩ :=
    GlobalTheory.T.exists_pointRigid_tautological_chart_unitary_boundary Xo c φ hpq hφ hns zs i OZ N d J π j BD hP hS x hx
  have hE := GlobalTheory.T.tautologicalChart_isEtaleCompletion_localRing Xo c φ hpq hφ hns zs i OZ N d J π j BD hP hS C hT ξ hy
  obtain ⟨hset, hred, a, ha, hbd⟩ :=
    GlobalTheory.T.tautologicalChart_boundary_equations Xo c φ hpq hφ hns zs i OZ N d J π j BD hP hS C hT ξ hy
  exact ⟨k, inferInstance, m, e, C, ξ, a, hT.1, hy, hξ, hE, hred, hset, ha, hbd⟩

end GlobalTheory.UCanon
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTripleChartUnitaryBoundaryPointRigidStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tripleChart_unitary_boundary_pointRigid : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x := by
  first | exact @GlobalTheory.UCanon.uPre_of_boundary_pointRigid | exact GlobalTheory.UCanon.uPre_of_boundary_pointRigid | (intros; apply GlobalTheory.UCanon.uPre_of_boundary_pointRigid <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTripleChartUnitaryBoundaryPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChart

theorem uPre_of_boundary {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (hpq : 1 ≤ Dw.p + Dw.q)
    (hφ : IsPolFan H.bar (min Dw.p Dw.q) φ) (hns : NoSelfInt H.bar (min Dw.p Dw.q) φ)
    {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData)
    {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S)
    (hP : GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD) (hS : SepB Xo c φ j)
    (x : S) (hx : x ∉ Set.range j) : UPre Xo c φ j BD d x :=
  GlobalTheory.T.exists_tripleChart_unitary_boundary_pointRigid Xo c φ hpq hφ hns zs i OZ N d J π j BD hP hS x hx

end GlobalTheory.UChart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTripleChartUnitaryBoundaryPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tripleChart_unitary_boundary_point : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x := by
  first | exact @GlobalTheory.UChart.uPre_of_boundary | exact GlobalTheory.UChart.uPre_of_boundary | (intros; apply GlobalTheory.UChart.uPre_of_boundary <;> assumption)
end
