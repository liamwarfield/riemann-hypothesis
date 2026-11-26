module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelDescentIntegralClosure
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyCoordIdeal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DedekindConstantsDegreeTwo
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagM3FromLocal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelDescentGenericFibre
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ArithmeticRelationsStatementHolds
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeFlagOutsidePrimeFibres
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeFlagCmTypeDegree

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyDedekindConstants
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyDedekindConstants
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.CoordRead

noncomputable section

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {V : Type} [AddCommGroup V] [Module Ω V]

theorem map_flagStep {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E'] {r : ℕ}
    (f : E →ₗ[Ω] E') (v : Fin r → E) (i : ℕ) : (flagStep Ω v i).map f = flagStep Ω (f ∘ v) i := by
  simp only [flagStep, Submodule.map_span, Set.image_comp]

theorem lc_comp_basisFun {r : ℕ} (b : Fin r → V) :
    Fintype.linearCombination Ω b ∘ ⇑(Pi.basisFun Ω (Fin r)) = b := by
  classical
  funext i
  simp [Pi.basisFun_apply, Fintype.linearCombination_apply_single]

theorem flagStep_le_span {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ} (b : Fin r → E) (i : ℕ) :
    flagStep Ω b i ≤ Submodule.span Ω (Set.range b) :=
  Submodule.span_mono (Set.image_subset_range _ _)

theorem exists_coords {r : ℕ} (b b' : Fin r → V) (h : ∀ i, flagStep Ω b' i = flagStep Ω b i) :
    ∃ b'c : Fin r → (Fin r → Ω), Fintype.linearCombination Ω b ∘ b'c = b' := by
  have hmem : ∀ k, b' k ∈ LinearMap.range (Fintype.linearCombination Ω b) := by
    intro k
    rw [Fintype.range_linearCombination]
    apply flagStep_le_span b r
    rw [← h r]
    exact Submodule.subset_span ⟨k, k.2, rfl⟩
  choose b'c hb'c using hmem
  exact ⟨b'c, funext hb'c⟩

theorem gr_comap {r : ℕ} (b : Fin r → V) (hb : LinearIndependent Ω b) (L : Lat ξ V) (i : Fin r) :
    (L.comap (Fintype.linearCombination Ω b)).gr (⇑(Pi.basisFun Ω (Fin r))) i = L.gr b i := by
  have hinj : Function.Injective (Fintype.linearCombination Ω b) := hb.fintypeLinearCombination_injective
  have hlc := lc_comp_basisFun (Ω := Ω) b
  have hfl : ∀ j, (flagStep Ω (⇑(Pi.basisFun Ω (Fin r))) j).map (Fintype.linearCombination Ω b) = flagStep Ω b j := by
    intro j; rw [map_flagStep, hlc]
  have he : ∀ j, Fintype.linearCombination Ω b (Pi.basisFun Ω (Fin r) j) = b j := fun j => congrFun hlc j
  funext q
  unfold Lat.gr
  congr 1
  ext t
  constructor
  · rintro ⟨z, hz, hzt⟩
    refine ⟨Fintype.linearCombination Ω b z, hz, ?_⟩
    have := Submodule.mem_map_of_mem (f := Fintype.linearCombination Ω b) hzt
    rwa [map_sub, map_smul, he, hfl] at this
  · rintro ⟨v, hv, hvt⟩
    have hvs : v ∈ LinearMap.range (Fintype.linearCombination Ω b) := by
      rw [Fintype.range_linearCombination]
      have h1 := flagStep_le_span b i hvt
      have h2 : t • b i ∈ Submodule.span Ω (Set.range b) :=
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      simpa using add_mem h1 h2
    obtain ⟨z, rfl⟩ := hvs
    refine ⟨z, hv, ?_⟩
    have : Fintype.linearCombination Ω b (z - t • Pi.basisFun Ω (Fin r) i) ∈
        (flagStep Ω (⇑(Pi.basisFun Ω (Fin r))) i).map (Fintype.linearCombination Ω b) := by
      rw [map_sub, map_smul, he, hfl]; exact hvt
    obtain ⟨w, hw, hwz⟩ := this
    rwa [← hinj hwz]

theorem isFlagVBOn_comap {r : ℕ} (b : Fin r → V) (hb : LinearIndependent Ω b) (L : Lat ξ V) (T : Set (Cpt ξ))
    (h : L.IsFlagVBOn T b) :
    (L.comap (Fintype.linearCombination Ω b)).IsFlagVBOn T (⇑(Pi.basisFun Ω (Fin r))) := by
  have hinj : Function.Injective (Fintype.linearCombination Ω b) := hb.fintypeLinearCombination_injective
  have hlc := lc_comp_basisFun (Ω := Ω) b
  intro p hp
  obtain ⟨U, hU, b', hfl, hfr⟩ := h p hp
  obtain ⟨b'c, hb'c⟩ := exists_coords b b' hfl
  refine ⟨U, hU, b'c, ?_, ?_⟩
  · intro i
    apply Submodule.map_injective_of_injective hinj
    rw [map_flagStep, map_flagStep, hb'c, hlc, hfl]
  · intro q hq hqU
    obtain ⟨hli, hsp⟩ := hfr q hq hqU
    refine ⟨LinearIndependent.of_comp (Fintype.linearCombination Ω b) (by rw [hb'c]; exact hli), ?_⟩
    show (L q).comap ((Fintype.linearCombination Ω b).restrictScalars (regAt ξ q)) = _
    have hinj' : Function.Injective ((Fintype.linearCombination Ω b).restrictScalars (regAt ξ q)) := hinj
    rw [hsp, ← hb'c, Set.range_comp]
    have : Submodule.span (regAt ξ q) (⇑(Fintype.linearCombination Ω b) '' Set.range b'c) =
        (Submodule.span (regAt ξ q) (Set.range b'c)).map ((Fintype.linearCombination Ω b).restrictScalars (regAt ξ q)) := by
      rw [Submodule.map_span]; rfl
    rw [this, Submodule.comap_map_eq_of_injective hinj']

end

end GlobalTheory.CompanionTheory.Ar.CoordRead

namespace GlobalTheory.CompanionTheory.Ar.CoordRead

theorem flagPair_coord : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type)
    [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω),
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ d : ℕ, ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 1) →
    ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsDedekindDomain A] [Module.Finite ℤ A], Function.Injective (algebraMap A Ω) →
    HasConstants ℤ A y → ∀ (p : ℕ), p.Prime → ∀ (m : Ideal A) [m.IsPrime], (p : A) ∈ m →
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m]
      [Algebra O Ω] [IsScalarTower A O Ω] (ϖ : O), Irreducible ϖ →
    ∀ (V : Type) [AddCommGroup V] [Module Ω V] (r : ℕ) (b : Fin r → V), LinearIndependent Ω b →
    ∀ (L L' : Lat ξ V) (Q : LocPair J ℤ (Fin r)), IsLatFlagPair y (overPrime ξ p) L L' b Q →
      (∀ q : Cpt ξ, q ∈ overPrime ξ p → ¬ InFibre ξ p q → L q = L' q) →
      ∃ (B B' : ChartBundle O (segreVec y) r (Fin r → Ω)) (v v' : Module.Basis (Fin r) Ω (Fin r → Ω)),
        (∀ c, segreVec y c ≠ 0 → B.lat c = coordLat O y L b c ∧ B'.lat c = coordLat O y L' b c) ∧
        IsFlagPair ϖ y B B' v v' Q.x Q.x' (Q.map (Int.castRingHom O)).f (Q.map (Int.castRingHom O)).g := by
  intro X Ω _ ξ K _ _ J _ y hT d hd A _ _ _ _ hA hC p hp m _ hm O _ _ _ _ _ _ _ ϖ hϖ V _ _ r b hb L L' Q hP hoff
  have hpair : IsLatFlagPair y (overPrime ξ p) (L.comap (Fintype.linearCombination Ω b))
      (L'.comap (Fintype.linearCombination Ω b)) (⇑(Pi.basisFun Ω (Fin r))) Q := by
    obtain ⟨h1, h2, h3⟩ := hP
    refine ⟨isFlagVBOn_comap b hb L _ h1, isFlagVBOn_comap b hb L' _ h2, fun i => ?_⟩
    rw [gr_comap b hb L i, gr_comap b hb L' i]
    exact h3 i
  have hoff' : ∀ q : Cpt ξ, q ∈ overPrime ξ p → ¬ InFibre ξ p q →
      (L.comap (Fintype.linearCombination Ω b)) q = (L'.comap (Fintype.linearCombination Ω b)) q := by
    intro q h1 h2
    show (L q).comap _ = (L' q).comap _
    rw [hoff q h1 h2]
  obtain ⟨B, B', v, v', hlat, -, -, hfp⟩ := GlobalTheory.T.dedekind_constants_degree_two X Ω ξ K J y hT d hd A hA hC p hp m hm O ϖ hϖ
    (Fin r → Ω) r (Pi.basisFun Ω (Fin r)) (L.comap (Fintype.linearCombination Ω b))
    (L'.comap (Fintype.linearCombination Ω b)) Q hpair hoff'
  refine ⟨B, B', v, v', fun c hc => ⟨AddSubgroup.ext fun z => ?_, AddSubgroup.ext fun z => ?_⟩, hfp⟩
  · rw [(hlat c hc z).1]
    simp only [coordLat, AddSubgroup.mem_iInf]
    rfl
  · rw [(hlat c hc z).2]
    simp only [coordLat, AddSubgroup.mem_iInf]
    rfl

end GlobalTheory.CompanionTheory.Ar.CoordRead
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyDedekindConstantsStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_dedekind_constants : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type)
    [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω),
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ d : ℕ, IsArithVar (mCoordIdeal y) (d + 1) →
    ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsDedekindDomain A] [Module.Finite ℤ A], Function.Injective (algebraMap A Ω) →
    HasConstants ℤ A y → ∀ (p : ℕ), p.Prime → ∀ (m : Ideal A) [m.IsPrime], (p : A) ∈ m →
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m]
      [Algebra O Ω] [IsScalarTower A O Ω] (ϖ : O), Irreducible ϖ →
    ∀ (V : Type) [AddCommGroup V] [Module Ω V] (r : ℕ) (b : Fin r → V), LinearIndependent Ω b →
    ∀ (L L' : Lat ξ V) (Q : LocPair J ℤ (Fin r)), IsLatFlagPair y (overPrime ξ p) L L' b Q →
      (∀ q : Cpt ξ, q ∈ overPrime ξ p → ¬ InFibre ξ p q → L q = L' q) →
      ∃ (B B' : ChartBundle O (segreVec y) r (Fin r → Ω)) (v v' : Module.Basis (Fin r) Ω (Fin r → Ω)),
        (∀ c, segreVec y c ≠ 0 → B.lat c = coordLat O y L b c ∧ B'.lat c = coordLat O y L' b c) ∧
        IsFlagPair ϖ y B B' v v' Q.x Q.x' (Q.map (Int.castRingHom O)).f (Q.map (Int.castRingHom O)).g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CoordRead.flagPair_coord | exact GlobalTheory.CompanionTheory.Ar.CoordRead.flagPair_coord | (intros; apply GlobalTheory.CompanionTheory.Ar.CoordRead.flagPair_coord <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagBasisLinIndepSpan
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagBasisLinIndepSpan
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.FlagBasis

theorem flagStep_full {E : Type} [AddCommGroup E] (Ω : Type) [Field Ω] [Module Ω E] {r : ℕ} (b : Fin r → E) :
    GlobalTheory.CompanionTheory.Ar.flagStep Ω b r = Submodule.span Ω (Set.range b) := by
  unfold GlobalTheory.CompanionTheory.Ar.flagStep
  have : {k : Fin r | (k : ℕ) < r} = Set.univ := by ext k; simp [k.2]
  rw [this, Set.image_univ]

theorem flag_b_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ)
    (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y)
    (Fl : 𝔐.Flag) (t : CMType H ⊕ CMType H),
    LinearIndependent Ω (Fl.b t) ∧ Submodule.span Ω (Set.range (Fl.b t)) = 𝔐.Vgen t := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ J y 𝔐 Fl t
  letI := 𝔐.fn.toAlgebra
  obtain ⟨cc, u, hc, _hj, _hjc, hb, _hu1, _hu0, hflag, _⟩ := Fl.generic
  refine ⟨hb t, ?_⟩
  have hle : Submodule.span Ω (Set.range (Fl.b t)) ≤ 𝔐.Vgen t := by
    rw [← flagStep_full, hflag t (labelRk D t), flagStep_full, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ ?_
    exact (Fl.V₀_mem t (cc t l)).1 ((hc t).2 ▸ Submodule.subset_span ⟨l, rfl⟩)
  obtain ⟨U, hpU, b', hspan, hfr⟩ := 𝔐.vb t ⟨GlobalTheory.CompanionTheory.Ar.genPt 𝔐.ξ, 𝔐.all _⟩ trivial
  have hli' : LinearIndependent Ω b' := (hfr _ trivial hpU).1
  have hV : Submodule.span Ω (Set.range b') = 𝔐.Vgen t := hspan
  haveI : FiniteDimensional Ω (𝔐.Vgen t) := by
    rw [← hV]; exact FiniteDimensional.span_of_finite Ω (Set.finite_range b')
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [← hV, finrank_span_eq_card (hb t), finrank_span_eq_card hli']

end GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.FlagBasis
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagBasisLinIndepSpanStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_basis_lin_indep_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ)
    (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y)
    (Fl : 𝔐.Flag) (t : CMType H ⊕ CMType H),
    LinearIndependent Ω (Fl.b t) ∧ Submodule.span Ω (Set.range (Fl.b t)) = 𝔐.Vgen t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.FlagBasis.flag_b_basis | exact GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.FlagBasis.flag_b_basis | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.FlagBasis.flag_b_basis <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldDvrExtension
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldDvrExtension
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.FnExt

theorem fnField_top_of_adjoin_root : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω), fnField O y = ⊤ →
    ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] (Ω' : Type) [Field Ω']
      [Algebra Ω Ω'] [Algebra O' Ω'] [Algebra O Ω'] [IsScalarTower O O' Ω'] [IsScalarTower O Ω Ω'] (ζ : O'),
      Algebra.adjoin Ω {algebraMap O' Ω' ζ} = ⊤ → fnField O' (fun v => algebraMap Ω Ω' (y v)) = ⊤ := by
  intro O _ _ _ Ω _ _ K J y hy O' _ _ _ _ Ω' _ _ _ _ _ _ ζ hζ
  set L := fnField O' (fun v => algebraMap Ω Ω' (y v)) with hL

  have himg : ∀ a : Ω, algebraMap Ω Ω' a ∈ L := by
    have hmap : (⊤ : Subfield Ω).map (algebraMap Ω Ω') ≤ L := by
      rw [← hy]
      unfold fnField
      rw [Subfield.map_le_iff_le_comap, Subfield.closure_le]
      rintro x (⟨a, rfl⟩ | ⟨q, rfl⟩)
      · show algebraMap Ω Ω' (algebraMap O Ω a) ∈ L
        rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply O O' Ω']
        exact Subfield.subset_closure (Or.inl ⟨_, rfl⟩)
      · show algebraMap Ω Ω' (y ⟨q.1, q.2.1⟩ / y ⟨q.1, q.2.2⟩) ∈ L
        rw [map_div₀]
        exact Subfield.subset_closure (Or.inr ⟨q, rfl⟩)
    intro a
    exact hmap ⟨a, Subfield.mem_top a, rfl⟩
  have hζL : algebraMap O' Ω' ζ ∈ L := Subfield.subset_closure (Or.inl ⟨ζ, rfl⟩)
  let S : Subalgebra Ω Ω' :=
    { L.toSubring with algebraMap_mem' := himg }
  have hle : Algebra.adjoin Ω {algebraMap O' Ω' ζ} ≤ S := by
    rw [Algebra.adjoin_le_iff]
    rw [Set.singleton_subset_iff]
    exact hζL
  rw [hζ] at hle
  rw [eq_top_iff]
  intro x _
  exact hle (Algebra.mem_top (x := x))

end GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.FnExt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldDvrExtensionStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.function_field_dvr_extension : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω), fnField O y = ⊤ →
    ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] (Ω' : Type) [Field Ω']
      [Algebra Ω Ω'] [Algebra O' Ω'] [Algebra O Ω'] [IsScalarTower O O' Ω'] [IsScalarTower O Ω Ω'] (ζ : O'),
      Algebra.adjoin Ω {algebraMap O' Ω' ζ} = ⊤ → fnField O' (fun v => algebraMap Ω Ω' (y v)) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.FnExt.fnField_top_of_adjoin_root | exact GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.FnExt.fnField_top_of_adjoin_root | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.FnExt.fnField_top_of_adjoin_root <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDvrExtensionField
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDvrExtensionField
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.ExtExists

theorem exists_dvr_in_finite_ext (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [CharZero K] [Algebra O K] [IsFractionRing O K]
    (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra O L] [IsScalarTower O K L]
    (z : L) (n : ℕ) (hn : 0 < n) (hz : IsPrimitiveRoot z n) :
    ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O')
      (_ : Algebra O O') (_ : IsLocalHom (algebraMap O O')) (_ : Algebra.IsAlgebraic O O')
      (_ : Algebra O' L) (_ : IsScalarTower O O' L) (ζ : O'),
      Function.Injective (algebraMap O' L) ∧ IsPrimitiveRoot ζ n ∧ algebraMap O' L ζ = z := by
  haveI : Algebra.IsSeparable K L := inferInstance
  haveI : IsDedekindDomain (integralClosure O L) := integralClosure.isDedekindDomain O K L
  haveI : IsFractionRing (integralClosure O L) L := integralClosure.isFractionRing_of_finite_extension K L
  haveI : Algebra.IsIntegral O (integralClosure O L) := inferInstance
  have hinjOL : Function.Injective (algebraMap O L) := by
    rw [IsScalarTower.algebraMap_eq O K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective O K)
  have hinjA : Function.Injective (algebraMap O (integralClosure O L)) := fun a b h =>
    hinjOL (congrArg (fun w : integralClosure O L => (w : L)) h)
  have hinjAL : Function.Injective (algebraMap (integralClosure O L) L) := Subtype.val_injective
  obtain ⟨P, hPmax, hPover⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := integralClosure O L) (IsLocalRing.maximalIdeal O)
    (fun x hx => by
      rw [RingHom.mem_ker] at hx
      rw [hinjA (hx.trans (map_zero _).symm)]
      exact Ideal.zero_mem _)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖP : algebraMap O (integralClosure O L) ϖ ∈ P := by
    change ϖ ∈ Ideal.under O P
    rw [hPover, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hϖ.not_isUnit
  have hP0 : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hϖP
    exact hϖ.ne_zero (hinjA (hϖP.trans (map_zero _).symm))
  haveI := hPmax.isPrime
  haveI hdvr : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _ hP0 _
  have hAW : Function.Injective (algebraMap (integralClosure O L) (Localization.AtPrime P)) :=
    IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors P)
  have hunit : ∀ y : P.primeCompl, IsUnit (algebraMap (integralClosure O L) L y) := fun y =>
    IsUnit.mk0 _ fun h => y.2 (by
      have : (y : integralClosure O L) = 0 := hinjAL (h.trans (map_zero _).symm)
      rw [this]; exact Ideal.zero_mem _)
  let f : Localization.AtPrime P →+* L := IsLocalization.lift (M := P.primeCompl) hunit
  have hf : ∀ a, f (algebraMap (integralClosure O L) (Localization.AtPrime P) a) =
      algebraMap (integralClosure O L) L a := fun a => IsLocalization.lift_eq hunit a
  have hfinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj P.primeCompl x
    have h1 := congrArg f h
    rw [map_mul, hx, zero_mul, hf] at h1
    have ha : a = 0 := hinjAL (h1.symm.trans (map_zero _).symm)
    rw [ha, map_zero] at h
    have hs : algebraMap (integralClosure O L) (Localization.AtPrime P) s ≠ 0 :=
      (IsLocalization.map_units (Localization.AtPrime P) s).ne_zero
    exact (mul_eq_zero.1 h).resolve_right hs
  letI algWL : Algebra (Localization.AtPrime P) L := f.toAlgebra
  have hOW : ∀ x : O, algebraMap O (Localization.AtPrime P) x =
      algebraMap (integralClosure O L) (Localization.AtPrime P) (algebraMap O (integralClosure O L) x) :=
    fun x => IsScalarTower.algebraMap_apply O (integralClosure O L) (Localization.AtPrime P) x
  have hWL : ∀ x, algebraMap (Localization.AtPrime P) L x = f x := fun _ => rfl
  haveI tower : IsScalarTower O (Localization.AtPrime P) L :=
    IsScalarTower.of_algebraMap_eq (R := O) (S := Localization.AtPrime P) (A := L) fun x => by
      rw [hOW, hWL, hf]; rfl
  have hloc : IsLocalHom (algebraMap O (Localization.AtPrime P)) := ⟨fun x hx => by
    by_contra hxu
    have hxm : x ∈ IsLocalRing.maximalIdeal O := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact hxu
    rw [← hPover, Ideal.mem_comap] at hxm
    have hm := (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P _).2 hxm
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm
    exact hm (by rw [← hOW]; exact hx)⟩
  haveI hOLalg : Algebra.IsAlgebraic O L :=
    (IsFractionRing.comap_isAlgebraic_iff (A := O) (K := K) (C := L)).2 inferInstance
  have halg : Algebra.IsAlgebraic O (Localization.AtPrime P) :=
    ⟨fun x => (isAlgebraic_algebraMap_iff (A := L) hfinj).1 (Algebra.IsAlgebraic.isAlgebraic _)⟩
  have hzint : _root_.IsIntegral O z := IsIntegral.of_pow hn (hz.pow_eq_one ▸ isIntegral_one)
  let zA : integralClosure O L := ⟨z, hzint⟩
  have hfz : f (algebraMap (integralClosure O L) (Localization.AtPrime P) zA) = z := hf zA
  refine ⟨Localization.AtPrime P, inferInstance, inferInstance, hdvr, inferInstance, hloc, halg, algWL, tower,
    algebraMap (integralClosure O L) (Localization.AtPrime P) zA, hfinj, ?_, hfz⟩
  exact IsPrimitiveRoot.of_map_of_injective (f := f) (by rw [hfz]; exact hz) hfinj

theorem exists_dvr_of_generator (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Ω : Type) [Field Ω] [CharZero Ω] [Algebra O Ω] (hinj : Function.Injective (algebraMap O Ω))
    (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra O Ω'] [IsScalarTower O Ω Ω']
    (z : Ω') (n : ℕ) (hn : 0 < n) (hz : IsPrimitiveRoot z n) (htop : Algebra.adjoin Ω {z} = ⊤) :
    ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O')
      (_ : Algebra O O') (_ : IsLocalHom (algebraMap O O')) (_ : Algebra.IsAlgebraic O O')
      (_ : Algebra O' Ω') (_ : IsScalarTower O O' Ω') (ζ : O'),
      Function.Injective (algebraMap O' Ω') ∧ IsPrimitiveRoot ζ n ∧
        Algebra.adjoin Ω {algebraMap O' Ω' ζ} = ⊤ := by
  haveI : FaithfulSMul O Ω := (faithfulSMul_iff_algebraMap_injective O Ω).2 hinj
  letI algKΩ : Algebra (FractionRing O) Ω := FractionRing.liftAlgebra O Ω
  haveI towKΩ : IsScalarTower O (FractionRing O) Ω := FractionRing.isScalarTower_liftAlgebra O Ω
  haveI : CharZero (FractionRing O) :=
    ((algebraMap (FractionRing O) Ω).charZero_iff (algebraMap (FractionRing O) Ω).injective).2 inferInstance
  letI algKΩ' : Algebra (FractionRing O) Ω' :=
    ((algebraMap Ω Ω').comp (algebraMap (FractionRing O) Ω)).toAlgebra
  haveI towK : IsScalarTower O (FractionRing O) Ω' := IsScalarTower.of_algebraMap_eq fun x => by
    change _ = algebraMap Ω Ω' (algebraMap (FractionRing O) Ω (algebraMap O (FractionRing O) x))
    rw [← IsScalarTower.algebraMap_apply O (FractionRing O) Ω, ← IsScalarTower.algebraMap_apply O Ω Ω']
  have hzi : _root_.IsIntegral (FractionRing O) z := IsIntegral.of_pow hn (hz.pow_eq_one ▸ isIntegral_one)
  haveI : FiniteDimensional (FractionRing O) (IntermediateField.adjoin (FractionRing O) {z}) :=
    IntermediateField.adjoin.finiteDimensional hzi
  have hgen : IsPrimitiveRoot (IntermediateField.AdjoinSimple.gen (FractionRing O) z) n :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap (IntermediateField.adjoin (FractionRing O) {z}) Ω')
      (by rw [IntermediateField.AdjoinSimple.algebraMap_gen]; exact hz)
      (algebraMap (IntermediateField.adjoin (FractionRing O) {z}) Ω').injective
  obtain ⟨O', i1, i2, i3, i4, i5, i6, i7, i8, ζ, hinjL, hζ, hζz⟩ :=
    exists_dvr_in_finite_ext O (FractionRing O) (IntermediateField.adjoin (FractionRing O) {z})
      (IntermediateField.AdjoinSimple.gen (FractionRing O) z) n hn hgen
  haveI towL : IsScalarTower O (IntermediateField.adjoin (FractionRing O) {z}) Ω' :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply O (FractionRing O) Ω',
        IsScalarTower.algebraMap_apply O (FractionRing O) (IntermediateField.adjoin (FractionRing O) {z}),
        ← IsScalarTower.algebraMap_apply (FractionRing O) (IntermediateField.adjoin (FractionRing O) {z}) Ω']
  letI algO'Ω' : Algebra O' Ω' :=
    ((algebraMap (IntermediateField.adjoin (FractionRing O) {z}) Ω').comp
      (algebraMap O' (IntermediateField.adjoin (FractionRing O) {z}))).toAlgebra
  have hO'Ω' : ∀ x : O', algebraMap O' Ω' x =
      algebraMap (IntermediateField.adjoin (FractionRing O) {z}) Ω'
        (algebraMap O' (IntermediateField.adjoin (FractionRing O) {z}) x) := fun _ => rfl
  haveI tow : IsScalarTower O O' Ω' := IsScalarTower.of_algebraMap_eq fun x => by
    rw [hO'Ω', ← IsScalarTower.algebraMap_apply O O' (IntermediateField.adjoin (FractionRing O) {z}),
      ← IsScalarTower.algebraMap_apply O (IntermediateField.adjoin (FractionRing O) {z}) Ω']
  refine ⟨O', i1, i2, i3, i4, i5, i6, algO'Ω', tow, ζ, ?_, hζ, ?_⟩
  · have : (algebraMap O' Ω' : O' → Ω') =
        (algebraMap (IntermediateField.adjoin (FractionRing O) {z}) Ω') ∘
          (algebraMap O' (IntermediateField.adjoin (FractionRing O) {z})) := rfl
    rw [this]
    exact (algebraMap (IntermediateField.adjoin (FractionRing O) {z}) Ω').injective.comp hinjL
  · rw [hO'Ω', hζz, IntermediateField.AdjoinSimple.algebraMap_gen]
    exact htop

end GlobalTheory.CompanionTheory.Ar.Num.ExtExists

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem exists_ext_primitive_root : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [CharZero Ω] [Algebra O Ω], Function.Injective (algebraMap O Ω) → ∀ n : ℕ, 0 < n → ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (_ : Algebra O O') (_ : IsLocalHom (algebraMap O O')) (_ : Algebra.IsAlgebraic O O') (Ω' : Type) (_ : Field Ω') (_ : Algebra Ω Ω') (_ : Algebra O' Ω') (_ : Algebra O Ω') (_ : IsScalarTower O O' Ω') (_ : IsScalarTower O Ω Ω') (ζ : O'), Function.Injective (algebraMap O' Ω') ∧ IsPrimitiveRoot ζ n ∧ Algebra.adjoin Ω {algebraMap O' Ω' ζ} = ⊤ := by
  intro O _ _ _ Ω _ _ _ hinj n hn
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.2 hn.ne'⟩
  have hz := IsCyclotomicExtension.zeta_spec n Ω (CyclotomicField n Ω)
  obtain ⟨O', i1, i2, i3, i4, i5, i6, i7, i8, ζ, h1, h2, h3⟩ :=
    ExtExists.exists_dvr_of_generator O Ω hinj (CyclotomicField n Ω) _ n hn hz
      (IsCyclotomicExtension.adjoin_primitive_root_eq_top hz)
  exact ⟨O', i1, i2, i3, i4, i5, i6, CyclotomicField n Ω, inferInstance, inferInstance, i7, inferInstance, i8, inferInstance, ζ, h1, h2, h3⟩

end GlobalTheory.CompanionTheory.Ar.Num
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDvrExtensionFieldStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_extension_field : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [CharZero Ω] [Algebra O Ω], Function.Injective (algebraMap O Ω) → ∀ n : ℕ, 0 < n → ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (_ : Algebra O O') (_ : IsLocalHom (algebraMap O O')) (_ : Algebra.IsAlgebraic O O') (Ω' : Type) (_ : Field Ω') (_ : Algebra Ω Ω') (_ : Algebra O' Ω') (_ : Algebra O Ω') (_ : IsScalarTower O O' Ω') (_ : IsScalarTower O Ω Ω') (ζ : O'), Function.Injective (algebraMap O' Ω') ∧ IsPrimitiveRoot ζ n ∧ Algebra.adjoin Ω {algebraMap O' Ω' ζ} = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.exists_ext_primitive_root | exact GlobalTheory.CompanionTheory.Ar.Num.exists_ext_primitive_root | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.exists_ext_primitive_root <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagPairChartBundleCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartBundleFinitelyGenerated
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartBundleFinitelyGenerated
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

namespace GlobalTheory.CompanionTheory.Ar.Geo

theorem chartBundle_lat_fg : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (ι : Type) (x : ι → Ω) (r : ℕ)
    (B : ChartBundle O x r (Fin r → Ω)) (c : ι), x c ≠ 0 → ∃ (n : ℕ) (s : Fin n → Fin r → Ω), (∀ k, s k ∈ B.lat c) ∧
      ∀ e ∈ B.lat c, ∃ a : Fin n → Ω, (∀ k, a k ∈ chartRing O x c) ∧ e = ∑ k, a k • s k :=
  PositivityTheory.Xgn.chart_lattice_finitely_generated

end GlobalTheory.CompanionTheory.Ar.Geo
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartBundleFinitelyGeneratedStatement
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_bundle_finitely_generated : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (ι : Type) (x : ι → Ω) (r : ℕ)
    (B : ChartBundle O x r (Fin r → Ω)) (c : ι), x c ≠ 0 → ∃ (n : ℕ) (s : Fin n → Fin r → Ω), (∀ k, s k ∈ B.lat c) ∧
      ∀ e ∈ B.lat c, ∃ a : Fin n → Ω, (∀ k, a k ∈ chartRing O x c) ∧ e = ∑ k, a k • s k := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Geo.chartBundle_lat_fg | exact GlobalTheory.CompanionTheory.Ar.Geo.chartBundle_lat_fg | (intros; apply GlobalTheory.CompanionTheory.Ar.Geo.chartBundle_lat_fg <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ReversedDualTriangular
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ReversedDualTriangular
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

namespace GlobalTheory.CompanionTheory.Ar.DualPair

theorem dualRevTri : ∀ (Ω : Type) [Field Ω] (r : ℕ) (w w' v v' : Module.Basis (Fin r) Ω (Fin r → Ω)),
    (∀ i j, w i ⬝ᵥ v j = if i = j.rev then 1 else 0) → (∀ i j, w' i ⬝ᵥ v' j = if i = j.rev then 1 else 0) →
    (∀ i j, i < j → w.repr (w' i) j = 0) →
    (∀ i j, i < j → v.repr (v' i) j = 0) ∧ ∀ i, v.repr (v' i) i * w.repr (w' i.rev) i.rev = 1 := by
  intro Ω _ r w w' v v' h1 h2 h3
  exact PositivityTheory.Xgn.dual_basis_reverse_triangular Ω r w w' v v' h1 h2 h3

end GlobalTheory.CompanionTheory.Ar.DualPair
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ReversedDualTriangularStatement
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reversed_dual_triangular : ∀ (Ω : Type) [Field Ω] (r : ℕ) (w w' v v' : Module.Basis (Fin r) Ω (Fin r → Ω)),
    (∀ i j, w i ⬝ᵥ v j = if i = j.rev then 1 else 0) → (∀ i j, w' i ⬝ᵥ v' j = if i = j.rev then 1 else 0) →
    (∀ i j, i < j → w.repr (w' i) j = 0) →
    (∀ i j, i < j → v.repr (v' i) j = 0) ∧ ∀ i, v.repr (v' i) i * w.repr (w' i.rev) i.rev = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.DualPair.dualRevTri | exact GlobalTheory.CompanionTheory.Ar.DualPair.dualRevTri | (intros; apply GlobalTheory.CompanionTheory.Ar.DualPair.dualRevTri <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartBundleLatticeGenerators
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartBundleLatticeGenerators
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem dotDual_overlap : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (ι : Type) (x : ι → Ω) (r : ℕ)
    (L : ι → AddSubgroup (Fin r → Ω)),
    (∀ c, ∀ a ∈ chartRing O x c, ∀ e ∈ L c, a • e ∈ L c) →
    (∀ i j, x i ≠ 0 → x j ≠ 0 → ∀ e ∈ L i, ∃ m : ℕ, (x i / x j) ^ m • e ∈ L j) →
    (∀ c, x c ≠ 0 → ∃ (n : ℕ) (s : Fin n → Fin r → Ω), (∀ k, s k ∈ L c) ∧
      ∀ e ∈ L c, ∃ a : Fin n → Ω, (∀ k, a k ∈ chartRing O x c) ∧ e = ∑ k, a k • s k) →
    ∀ i j, x i ≠ 0 → x j ≠ 0 → ∀ e ∈ dotDual (chartRing O x i) (L i),
      ∃ m : ℕ, (x i / x j) ^ m • e ∈ dotDual (chartRing O x j) (L j) :=
  PositivityTheory.Xgn.hodge_dual_lattice_overlap

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartBundleLatticeGeneratorsStatement
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_bundle_lattice_generators : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (ι : Type) (x : ι → Ω) (r : ℕ)
    (L : ι → AddSubgroup (Fin r → Ω)),
    (∀ c, ∀ a ∈ chartRing O x c, ∀ e ∈ L c, a • e ∈ L c) →
    (∀ i j, x i ≠ 0 → x j ≠ 0 → ∀ e ∈ L i, ∃ m : ℕ, (x i / x j) ^ m • e ∈ L j) →
    (∀ c, x c ≠ 0 → ∃ (n : ℕ) (s : Fin n → Fin r → Ω), (∀ k, s k ∈ L c) ∧
      ∀ e ∈ L c, ∃ a : Fin n → Ω, (∀ k, a k ∈ chartRing O x c) ∧ e = ∑ k, a k • s k) →
    ∀ i j, x i ≠ 0 → x j ≠ 0 → ∀ e ∈ dotDual (chartRing O x i) (L i),
      ∃ m : ℕ, (x i / x j) ^ m • e ∈ dotDual (chartRing O x j) (L j) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.dotDual_overlap | exact GlobalTheory.CompanionTheory.Ar.Num.dotDual_overlap | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.dotDual_overlap <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartBundleLocalGeneration
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartBundleLocalGeneration
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem chartBundle_dotDual_localFrame : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (ι : Type) (x : ι → Ω) (r : ℕ)
    (B : ChartBundle O x r (Fin r → Ω)),
    (∀ c, x c ≠ 0 → ∃ (n : ℕ) (s : Fin n → Fin r → Ω), (∀ k, s k ∈ B.lat c) ∧
      ∀ e ∈ B.lat c, ∃ a : Fin n → Ω, (∀ k, a k ∈ chartRing O x c) ∧ e = ∑ k, a k • s k) →
    ∀ i, x i ≠ 0 → ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ chartRing O x i) ∧ (∀ l, c l ∈ chartRing O x i) ∧
      ∑ l, c l * f l = 1 ∧ ∀ l, ∃ b : Fin r → Fin r → Ω, LinearIndependent Ω b ∧
        Submodule.span Ω (Set.range b) = ⊤ ∧ ∀ e : Fin r → Ω,
          ((∃ n : ℕ, f l ^ n • e ∈ dotDual (chartRing O x i) (B.lat i)) ↔
            ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ chartRing O x i) ∧ e = ∑ q, a q • b q) :=
  PositivityTheory.Xgn.hodge_dual_frame_exists

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartBundleLocalGenerationStatement
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_bundle_local_generation : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (ι : Type) (x : ι → Ω) (r : ℕ)
    (B : ChartBundle O x r (Fin r → Ω)),
    (∀ c, x c ≠ 0 → ∃ (n : ℕ) (s : Fin n → Fin r → Ω), (∀ k, s k ∈ B.lat c) ∧
      ∀ e ∈ B.lat c, ∃ a : Fin n → Ω, (∀ k, a k ∈ chartRing O x c) ∧ e = ∑ k, a k • s k) →
    ∀ i, x i ≠ 0 → ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ chartRing O x i) ∧ (∀ l, c l ∈ chartRing O x i) ∧
      ∑ l, c l * f l = 1 ∧ ∀ l, ∃ b : Fin r → Fin r → Ω, LinearIndependent Ω b ∧
        Submodule.span Ω (Set.range b) = ⊤ ∧ ∀ e : Fin r → Ω,
          ((∃ n : ℕ, f l ^ n • e ∈ dotDual (chartRing O x i) (B.lat i)) ↔
            ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ chartRing O x i) ∧ e = ∑ q, a q • b q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.chartBundle_dotDual_localFrame | exact GlobalTheory.CompanionTheory.Ar.Num.chartBundle_dotDual_localFrame | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.chartBundle_dotDual_localFrame <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsReversedDualBasis
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsReversedDualBasis
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

namespace GlobalTheory.CompanionTheory.Ar.DualRev

theorem dotDualRevBasis (Ω : Type) [Field Ω] (r : ℕ) (w : Module.Basis (Fin r) Ω (Fin r → Ω)) :
    ∃ v : Module.Basis (Fin r) Ω (Fin r → Ω), ∀ i j, w i ⬝ᵥ v j = if i = j.rev then 1 else 0 := by
  classical
  set v : Fin r → Fin r → Ω := fun j t => w.dualBasis (Fin.rev j) (fun s => if t = s then 1 else 0) with hv
  have key : ∀ i j, w i ⬝ᵥ v j = if i = j.rev then 1 else 0 := by
    intro i j
    have h1 : w i ⬝ᵥ v j = w.dualBasis (Fin.rev j) (w i) := by
      rw [LinearMap.pi_apply_eq_sum_univ (w.dualBasis (Fin.rev j)) (w i)]
      simp [dotProduct, hv, smul_eq_mul]
    rw [h1, Module.Basis.dualBasis_apply, Module.Basis.repr_self, Finsupp.single_apply]
  have hli : LinearIndependent Ω v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j0
    have := congrArg (fun x => w (Fin.rev j0) ⬝ᵥ x) hg
    simp only [dotProduct_sum, dotProduct_smul, key, smul_eq_mul, dotProduct_zero] at this
    simpa [Fin.rev_inj, eq_comm] using this
  have hcard : Fintype.card (Fin r) = Module.finrank Ω (Fin r → Ω) := by
    rw [Fintype.card_fin, Module.finrank_fin_fun]
  by_cases hr : r = 0
  · subst hr
    exact ⟨w, fun i => i.elim0⟩
  haveI : Nonempty (Fin r) := ⟨⟨0, Nat.pos_of_ne_zero hr⟩⟩
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard, ?_⟩
  intro i j
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  exact key i j

end GlobalTheory.CompanionTheory.Ar.DualRev
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsReversedDualBasisStatement
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reversed_dual_basis : ∀ (Ω : Type) [Field Ω] (r : ℕ) (w : Module.Basis (Fin r) Ω (Fin r → Ω)),
    ∃ v : Module.Basis (Fin r) Ω (Fin r → Ω), ∀ i j, w i ⬝ᵥ v j = if i = j.rev then 1 else 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.DualRev.dotDualRevBasis | exact GlobalTheory.CompanionTheory.Ar.DualRev.dotDualRevBasis | (intros; apply GlobalTheory.CompanionTheory.Ar.DualRev.dotDualRevBasis <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagPairChartBundleCompat
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.DualPair

open GroundTheory.Heights₂.Heights.NumbersDVR (IsVerticalDivisor ratDiv)

theorem mem_dualBundle {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω] {r : ℕ}
    (R : Subalgebra O Ω) (L : AddSubgroup (Fin r → Ω)) (e : Fin r → Ω) :
    e ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ e ∈ R := by
  simp [dotDual, AddSubgroup.mem_iInf]

def dualBundle {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω] {ι : Type} {x : ι → Ω} {r : ℕ}
    (B : ChartBundle O x r (Fin r → Ω)) : ChartBundle O x r (Fin r → Ω) where
  lat c := dotDual (chartRing O x c) (B.lat c)
  stable c a ha e he := by
    rw [mem_dualBundle] at he ⊢
    intro l hl
    rw [dotProduct_smul, smul_eq_mul]
    exact mul_mem ha (he l hl)
  frame := GlobalTheory.T.chart_bundle_local_generation O Ω ι x r B (GlobalTheory.T.chart_bundle_finitely_generated O Ω ι x r B)
  overlap := GlobalTheory.T.chart_bundle_lattice_generators O Ω ι x r B.lat B.stable B.overlap (GlobalTheory.T.chart_bundle_finitely_generated O Ω ι x r B)

def dotForm (Ω : Type) [Field Ω] (r : ℕ) : (Fin r → Ω) →ₗ[Ω] (Fin r → Ω) →ₗ[Ω] Ω :=
  LinearMap.mk₂ Ω (fun a b => a ⬝ᵥ b) add_dotProduct (fun c a b => smul_dotProduct c a b) dotProduct_add
    (fun c a b => dotProduct_smul c a b)

theorem dotForm_apply (Ω : Type) [Field Ω] (r : ℕ) (a b : Fin r → Ω) : dotForm Ω r a b = a ⬝ᵥ b := rfl

theorem dotForm_flip_bijective (Ω : Type) [Field Ω] (r : ℕ) : Function.Bijective (dotForm Ω r).flip := by
  have hinj : Function.Injective (dotForm Ω r).flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    funext q
    have := LinearMap.congr_fun hb (Pi.single q 1)
    simpa [dotForm_apply, single_one_dotProduct] using this
  refine ⟨hinj, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by simp [Subspace.dual_finrank_eq])).1 hinj

theorem isVerticalDivisor_swap {K : Type} [DecidableEq K] {ι : K → Type} {O : Type} [CommRing O]
    {P : Ideal (MvPolynomial (Σ k, ι k) O)} {ϖ : O} {b : K → ℤ} {f g : MvPolynomial (Σ k, ι k) O}
    (h : IsVerticalDivisor P ϖ b f g) : IsVerticalDivisor P ϖ (-b) g f := by
  refine ⟨?_, h.den_not_mem, h.num_not_mem, ?_, ?_⟩
  · obtain ⟨bf, bg, hf, hg, hb⟩ := h.degrees
    refine ⟨bg, bf, hg, hf, ?_⟩
    rw [← hb]
    funext k
    simp
  · intro W hW
    apply h.vertical W
    unfold ratDiv at hW ⊢
    exact fun h0 => hW (sub_eq_zero.mpr (sub_eq_zero.mp h0).symm)
  · intro W hp hPW hrel hϖ
    obtain ⟨u, v, hu, hv, h1⟩ := h.unit_off_special W hp hPW hrel hϖ
    refine ⟨v, u, hv, hu, ?_⟩
    rw [← neg_sub]
    exact P.neg_mem h1

theorem dualPair : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (ϖ : O) (r : ℕ) (B B' : ChartBundle O (segreVec y) r (Fin r → Ω)) (w w' : Module.Basis (Fin r) Ω (Fin r → Ω))
    (x x' : Fin r → K → ℤ) (f g : Fin r → MvPolynomial (Σ k, J k) O), IsFlagPair ϖ y B B' w w' x x' f g →
    ∃ (C C' : ChartBundle O (segreVec y) r (Fin r → Ω)) (v v' : Module.Basis (Fin r) Ω (Fin r → Ω)),
      (∀ c, segreVec y c ≠ 0 → C.lat c = dotDual (chartRing O (segreVec y) c) (B.lat c) ∧
        C'.lat c = dotDual (chartRing O (segreVec y) c) (B'.lat c)) ∧
      IsFlagPair ϖ y C C' v v' (fun i => -x (Fin.rev i)) (fun i => -x' (Fin.rev i)) (fun i => g (Fin.rev i))
        (fun i => f (Fin.rev i)) := by
  intro O _ _ _ Ω _ _ K _ _ J _ y ϖ r B B' w w' x x' f g h
  obtain ⟨v, hv⟩ := GlobalTheory.T.exists_reversed_dual_basis Ω r w
  obtain ⟨v', hv'⟩ := GlobalTheory.T.exists_reversed_dual_basis Ω r w'
  obtain ⟨htri, hdiag⟩ := GlobalTheory.T.reversed_dual_triangular Ω r w w' v v' hv hv' h.sameFlag
  have hdual : ∀ B₀ : ChartBundle O (segreVec y) r (Fin r → Ω),
      IsDualLat O y (dotForm Ω r) B₀.lat (dualBundle B₀).lat := by
    intro B₀
    refine ⟨dotForm_flip_bijective Ω r, fun s _ e => ?_⟩
    exact mem_dualBundle _ _ _
  refine ⟨dualBundle B, dualBundle B', v, v', fun c _ => ⟨rfl, rfl⟩, ?_⟩
  refine ⟨?_, ?_, htri, fun i => ?_, fun i => ?_⟩
  · exact GlobalTheory.T.dual_lattice_flag_frame O Ω K J y r (Fin r → Ω) (Fin r → Ω) B (dualBundle B) (dotForm Ω r) (hdual B) w x h.flag v
      (fun i j => by rw [dotForm_apply]; exact hv i j)
  · exact GlobalTheory.T.dual_lattice_flag_frame O Ω K J y r (Fin r → Ω) (Fin r → Ω) B' (dualBundle B') (dotForm Ω r) (hdual B') w' x'
      h.flag' v' (fun i j => by rw [dotForm_apply]; exact hv' i j)
  · have := isVerticalDivisor_swap (h.vertical i.rev)
    convert this using 1
    ring
  · show aeval y (g i.rev) = v.repr (v' i) i * aeval y (f i.rev)
    rw [h.generic i.rev, ← mul_assoc, hdiag i, one_mul]

end GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.DualPair
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagPairChartBundleCompatStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_pair_chart_bundle_compat : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (ϖ : O) (r : ℕ) (B B' : ChartBundle O (segreVec y) r (Fin r → Ω)) (w w' : Module.Basis (Fin r) Ω (Fin r → Ω))
    (x x' : Fin r → K → ℤ) (f g : Fin r → MvPolynomial (Σ k, J k) O), IsFlagPair ϖ y B B' w w' x x' f g →
    ∃ (C C' : ChartBundle O (segreVec y) r (Fin r → Ω)) (v v' : Module.Basis (Fin r) Ω (Fin r → Ω)),
      (∀ c, segreVec y c ≠ 0 → C.lat c = dotDual (chartRing O (segreVec y) c) (B.lat c) ∧
        C'.lat c = dotDual (chartRing O (segreVec y) c) (B'.lat c)) ∧
      IsFlagPair ϖ y C C' v v' (fun i => -x (Fin.rev i)) (fun i => -x' (Fin.rev i)) (fun i => g (Fin.rev i))
        (fun i => f (Fin.rev i)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.DualPair.dualPair | exact GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.DualPair.dualPair | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.DualPair.dualPair <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelOnHodgeFromFamily
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num.HodgeModel

theorem model_on_hodge_of_family_pos : FamilyExistsPos → HodgeLatticeFlagBound := by
  intro hF E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hV _ _ Fl S₀ T hT p hpS hpS₀ hHT hp2 hdisc φ hφ A _ _ _
  intro m _ hm O _ _ _ _ _ _ _
  rcases Nat.eq_zero_or_pos (D.p + D.q) with h0 | hpos
  · haveI : IsEmpty (Fin (D.p + D.q)) := by rw [h0]; exact Fin.isEmpty'
    intro τ k _ Q _
    have h1 : ((T.map (Int.castRingHom O)).comp fun i : Fin (D.p + D.q) => (τ, i)).ck (pointIdeal O y) k Q = 0 := by
      simp [LocPair.ck, GroundTheory.Heights₂.Heights.NumbersDVR.pairNum]
    have h3 : ∀ τ', liePs (Ψ := CMType H) (N := D.p + D.q) D.p (k - 1) τ' = 0 := by
      rintro (τ' | τ') <;> simp [liePs]
    have h2 : bracket (N := D.p + D.q) D.p φ p k τ = 0 := by
      simp [bracket, h3]
    rw [h1, h2]
    simp [cycNum]
  have hpP : p.Prime := 𝔐.S_prime p hpS
  haveI : Fact p.Prime := ⟨hpP⟩
  haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  obtain ⟨hAD, hAfin, hAinj, hAcst, hloc⟩ := GlobalTheory.T.arith_variety_coord_ideal E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hV A
  haveI := hAD
  haveI := hAfin
  obtain ⟨hOint, hOfn⟩ := hloc m O
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨-, hModel, hVert⟩ := GlobalTheory.T.localization_model_over_place K J Ω y A hAinj hAcst d hV m O
  have hT2 := hT
  obtain ⟨hS₀, hvb, hsub, e₀, e, hR₀, hR, hfg, hvo⟩ := hT2
  have hTv := hVert ϖ hϖ _ _ T hvo
  have hOinj : Function.Injective (algebraMap O Ω) := hOint.1
  have hb : ∀ t, LinearIndependent Ω (Fl.b t) ∧ Submodule.span Ω (Set.range (Fl.b t)) = 𝔐.Vgen t :=
    GlobalTheory.T.flag_basis_lin_indep_span E H D l Xo c O₀ β Y S Ω K J y 𝔐 Fl
  have hfam := hF E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hV hpos Fl.b hb p hpS hHT hp2 hdisc φ hφ A m hm O
  choose Sg hSg ε φ' F hF1 hF2 hF3 w σ Df hDf using hfam
  have hFc : ∀ t, 0 < Fintype.card (F t) - 1 := fun t => by
    have := Fintype.one_lt_card (α := F t)
    omega
  have hN0 : 0 < ∏ t, (Fintype.card (F t) - 1) := Finset.prod_pos fun t _ => hFc t
  obtain ⟨O', _, _, _, _, _, _, Ω', _, _, _, _, _, _, ζ, hO'inj, hζ, hadj⟩ := GlobalTheory.T.exists_dvr_extension_field O Ω hOinj _ hN0
  have hζt : ∀ t, IsPrimitiveRoot (ζ ^ ((∏ t, (Fintype.card (F t) - 1)) / (Fintype.card (F t) - 1)))
      (Fintype.card (F t) - 1) := fun t =>
    hζ.pow hN0 (Nat.div_mul_cancel
      (Finset.dvd_prod_of_mem (fun t => Fintype.card (F t) - 1) (Finset.mem_univ t))).symm
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible O'
  haveI : CharZero Ω' := charZero_of_injective_ringHom (algebraMap Ω Ω').injective
  haveI : CharZero O' := (algebraMap O' Ω').charZero
  have hModel' := (GlobalTheory.T.model_over_dvr_extension O Ω K J y d hModel hOint O' Ω' hO'inj).2
  have hfn' := GlobalTheory.T.function_field_dvr_extension O Ω K J y hOfn O' Ω' ζ hadj
  have hTwin : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O'
      (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O' (fun v => algebraMap Ω Ω' (y v))) d :=
    (GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples.isModelOver_iff O' _ d).2 ⟨hV.1, hModel'⟩
  have hagree : ∀ s (q : Cpt 𝔐.ξ), (∀ p' : ℕ, p'.Prime → ¬ InFibre 𝔐.ξ p' q) → 𝔐.HT p s q = 𝔐.dR s q :=
    GlobalTheory.T.hodge_flag_outside_prime_fibres E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS
  have hLat := GlobalTheory.T.hodge_flag_cm_type_degree E H D l Xo c O₀ β Y S Ω K J y 𝔐 Fl S₀ T hT p hpS hpS₀ hagree
  have hag2 : ∀ s, ∀ q : Cpt 𝔐.ξ, q ∈ overPrime 𝔐.ξ p → ¬ InFibre 𝔐.ξ p q → 𝔐.dR s q = 𝔐.HT p s q := by
    intro s q hq hqp
    refine (hagree s q fun p' hp' => ?_).symm
    by_cases h : p' = p
    · subst h; exact hqp
    · exact hq p' hp' h
  have hB := fun s => GlobalTheory.T.arith_variety_dedekind_constants 𝔐.X Ω 𝔐.ξ K J y 𝔐.tie d hV A hAinj hAcst p hpP m hm O ϖ hϖ 𝔐.Li
    (labelRk D s) (Fl.b s) (hb s).1 (𝔐.dR s) (𝔐.HT p s) (labelPair D T s) (hLat s) (hag2 s)
  choose B B' v v' hBlat hBfp using hB
  have hC := fun s : CMType H ⊕ CMType H => GlobalTheory.T.flag_pair_chart_bundle_compat O Ω K J y ϖ _ (B s.swap) (B' s.swap) (v s.swap) (v' s.swap) _ _ _ _
    (hBfp s.swap)
  choose C C' u u' hClat hCfp using hC
  have hmm : ∀ {σ' : Type} (Q : LocPair J ℤ σ'),
      (Q.map (Int.castRingHom O)).map (algebraMap O O') = Q.map (Int.castRingHom O') := by
    intro σ' Q
    rw [map_map]
    congr 1
    exact RingHom.ext_int _ _
  have hE := fun s => GlobalTheory.T.model_descent_valuation_fibre O Ω K J y d hModel hOint O' Ω' hO'inj ϖ ϖ' hϖ hϖ' _ (B s) (B' s) (v s)
    (v' s) ((labelPair D T s).map (Int.castRingHom O)) (hBfp s)
  choose LB LB' lv lv' hLBlat hLBfp using hE
  have hE2 := fun s => GlobalTheory.T.model_descent_valuation_fibre O Ω K J y d hModel hOint O' Ω' hO'inj ϖ ϖ' hϖ hϖ' _ (C s) (C' s) (u s)
    (u' s) ((omPair D T s).map (Int.castRingHom O)) (hCfp s)
  choose LC LC' lu lu' hLClat hLCfp using hE2
  have hRel : ∀ t, Relations (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) d p (φ' t)
      (fun τ => (labelPair D T (ε t τ)).map (Int.castRingHom O'))
      (fun τ => (omPair D T (ε t τ)).map (Int.castRingHom O')) := by
    intro t
    obtain ⟨-, -, hpre, hfamOf⟩ := hDf t
    obtain ⟨χ, Df', hM3, hspan⟩ := GlobalTheory.T.model_descent_generic_fibre O Ω K J y d hModel hOint O' Ω' hO'inj (F t) p _ (hζt t)
      (D.p + D.q) (Sg t) _ _ (w t) (σ t) (φ' t) (Df t) hpre
    refine GlobalTheory.T.arithmetic_relations_statement_holds O' Ω' K J (fun v => algebraMap Ω Ω' (y v)) ϖ' hϖ' d hTwin hfn' p hpP
      (algebraMap O O' (w t)) χ (φ' t) Df' hM3
      (fun τ => LB (ε t τ)) (fun τ => LB' (ε t τ)) (fun τ => LC (ε t τ)) (fun τ => LC' (ε t τ)) ?_ _ _ ?_
    · intro τ c hc
      have hc' : segreVec y c ≠ 0 := by
        intro h
        apply hc
        show ∏ k, algebraMap Ω Ω' (y ⟨k, c k⟩) = 0
        rw [← map_prod]
        exact (congrArg (algebraMap Ω Ω') h).trans (map_zero _)
      obtain ⟨hl, hW, ho, hoh⟩ := hfamOf c hc' τ
      obtain ⟨s1, s2, s3, s4⟩ := hspan c hc' τ
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [(hLBlat _ c hc').1, (hBlat _ c hc').1, s1, hl]; rfl
      · rw [(hLBlat _ c hc').2, (hBlat _ c hc').2, s2, hW]; rfl
      · rw [(hLClat _ c hc').1, (hClat _ c hc').1, (hBlat _ c hc').1, s3, ho]; rfl
      · rw [(hLClat _ c hc').2, (hClat _ c hc').2, (hBlat _ c hc').2, s4, hoh]; rfl
    · intro τ
      refine ⟨⟨lv (ε t τ), lv' (ε t τ), ?_⟩, ⟨lu (ε t τ), lu' (ε t τ), ?_⟩⟩
      · have h := hLBfp (ε t τ)
        rw [hmm] at h
        exact h
      · have h := hLCfp (ε t τ)
        rw [hmm] at h
        exact h
  have hLoc : LabelChernComparison (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) d p φ
      (fun s => (labelPair D T s).map (Int.castRingHom O')) (fun s => (omPair D T s).map (Int.castRingHom O')) := by
    refine GlobalTheory.T.local_comparison_of_orbits_holds O' K J (CMType H ⊕ CMType H) _ d p hpP.two_le φ _ _ _ _ fun τ => ?_
    obtain ⟨hrange, hcomm, -, -⟩ := hDf τ
    exact ⟨Sg τ, inferInstance, ε τ, φ' τ, hrange, hcomm, hRel τ⟩
  have hLoc2 : LabelChernComparison (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) d p φ
      (fun s => (labelPair D T s).map (Int.castRingHom O')) (fun s => (omPairM D T s).map (Int.castRingHom O')) := by
    intro k hk Q hQ τ
    rcases τ with τ | τ
    · exact hLoc k hk Q hQ (.inl τ)
    · exact hLoc k hk Q hQ (.inr τ)
  have hp0' : (p : O') ≠ 0 := Nat.cast_ne_zero.2 hpP.ne_zero
  have hFlag' := GlobalTheory.T.flag_m3_from_local O' ϖ' hϖ' K J _ d hModel' p hp0' (CMType H) D.p D.q φ (T.map (Int.castRingHom O'))
    (fun s => (labelPair D T s).map (Int.castRingHom O')) (fun s => (omPairM D T s).map (Int.castRingHom O'))
    (fun τ => rfl)
    (fun τ => by
      show (dualRev (dualRev (T.comp _))).map _ = _
      rw [dualRev_dualRev]
      rfl)
    (fun τ k Q _ => (GlobalTheory.T.local_number_permutation_invariant O' K J D.q Fin.revPerm _ k Q).1 (p : O')
      (fun i => -(T.map (Int.castRingHom O')).x (τ, Fin.natAdd D.p i)))
    hLoc2
  have hT' : FlagChernComparison (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) d p D.p φ
      ((T.map (Int.castRingHom O)).map (algebraMap O O')) := by
    rw [hmm]
    exact hFlag'
  exact (GlobalTheory.T.model_descent_integral_closure O Ω K J y d hModel hOint O' Ω' hO'inj ϖ hϖ p).1 hpP.ne_zero (CMType H) (D.p + D.q) D.p φ
    (T.map (Int.castRingHom O)) hTv hT'

end GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelOnHodgeFromFamilyStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_on_hodge_from_family : GlobalTheory.CompanionTheory.Ar.Num.FamilyExistsPos → HodgeLatticeFlagBound := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.model_on_hodge_of_family_pos | exact GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.model_on_hodge_of_family_pos | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.model_on_hodge_of_family_pos <;> assumption)
end
