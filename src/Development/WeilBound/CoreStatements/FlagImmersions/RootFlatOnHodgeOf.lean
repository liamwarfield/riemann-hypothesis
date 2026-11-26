module

public import Development.WeilBound.CoreStatements.FlagImmersions.FibSandwich
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatTheoremOfResolutionGaga
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CptFlatInputsOfPropZ
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeCmTypeWeight
public import Development.WeilBound.CoreStatements.VolumeEquality.ChartMeetsPoint
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalSystemSplitFibres
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatHermRootLineDegree

@[expose] public section

attribute [-instance] GlobalTheory.CompHt.fintypePsi

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFlatHermHodgeCptConst
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_flatHerm_hodgeCpt_const : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω) (τ : CMType H) (F' : Type) [Field F'] [NumberField F'] (ψ : F' →+* Ω) (A : HermLine J) (c₀ : Ω) (r : HeightOneSpectrum (𝓞 F') →₀ ℚ) (cinf : (F' →+* ℂ) → ℝ), Fl.RootLines xdeg e → A.a = ∑ i, xdeg (τ, i) → Birational y → IsConjInvariantH A → c₀ ≠ 0 → (∀ p ∈ genFibre ℤ 𝔐.ξ, (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ)) (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))).IsGenAt p (c₀ * ∏ i, e (τ, i))) → (∀ (v : HeightOneSpectrum (𝓞 F')) (π : F'), v.valuation F' π = WithZero.exp (-1 : ℤ) → ∃ (m : ℕ) (k : ℤ), 0 < m ∧ (k : ℚ) = m * r v ∧ ∀ p : Cpt 𝔐.ξ, (∀ a : F', v.valuation F' a ≤ 1 → ψ a ∈ regAt 𝔐.ξ p) → OrderAt (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ)) (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))) (c₀ * ∏ i, e (τ, i)) (ψ π) m k p) → (∀ σ, 0 < cinf σ) → (∀ (σ : F' →+* ℂ) z (g h : MRing J) (dg dh : K → ℕ), PtOver y ψ σ z → IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) - dh k = A.a k) → aeval y g = c₀ * aeval y h → ‖evC z g‖ = cinf σ * A.h z * ‖evC z h‖) → OverInt y ψ ∧ ∃ Sf : FlatHerm y ψ A, Sf.ht = ((r.sum fun v q => (q : ℝ) * Real.log (Ideal.absNorm v.asIdeal)) - ∑ σ : F' →+* ℂ, Real.log (cinf σ)) / (Module.finrank ℚ F' : ℝ) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 Fl xdeg e τ F' _ _ ψ A c₀ r cinf hR hA hB hC hc₀ hgen hZ hcinf hnorm
  have hN : NormalCpt 𝔐.ξ := XR.normalCpt_of_isCptGen 𝔐.tie.gen (fun x => ⟨𝔐.normal.1 x, 𝔐.normal.2 x⟩)
  have hO : OverInt y ψ := overInt_of_normalCpt 𝔐.tie hN ψ
  have hD := GlobalTheory.T.hodge_cpt_flag_degree E H D l Xo c O β Y S Ω K J y 𝔐 Fl xdeg e τ hR
  rw [← hA] at hD
  refine ⟨hO, GlobalTheory.T.birational_lattice_height_formula K J Ω F' y ψ 𝔐.X 𝔐.ξ Ω _ (∏ i, e (τ, i)) c₀ A r cinf hO hB hC 𝔐.tie hN hD hc₀
    (fun p => ?_) hcinf hnorm⟩
  by_cases hp : p ∈ genFibre ℤ 𝔐.ξ
  · exact Or.inl ⟨cst_mem_regAt_of_genFibre hN ψ hp, orderAt_one_zero.2 (hgen p hp)⟩
  · obtain ⟨v, hv⟩ := exists_place_of_notMem_genFibre hN ψ hp
    obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F'
    obtain ⟨m, n, hm, hn, h⟩ := hZ v π hπ
    exact Or.inr ⟨v, π, m, n, hv, hπ, hm, hn, h p hv⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PropZProved
section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FunctionOnConnectedFibreUnit
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsUnitOfBasicOpenNonemptyOfUniversallyClosed
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_pow_mul_unit_add_eq_zero_of_integral {K A : Type*} [Field K] [CommRing A]
    (φ : K →+* A) (a : A) (ha : φ.IsIntegralElem a) :
    ∃ (m : ℕ) (u b : A), IsUnit u ∧ a ^ m * (u + a * b) = 0 := by
  obtain ⟨p, hp, hpa⟩ := ha
  obtain ⟨q, hpq, hq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp.ne_zero 0
  rw [map_zero, sub_zero] at hpq hq
  have hq0 : q.coeff 0 ≠ 0 := fun h => hq (Polynomial.X_dvd_iff.2 h)
  refine ⟨p.rootMultiplicity 0, φ (q.coeff 0), q.divX.eval₂ φ a, (Ne.isUnit hq0).map φ, ?_⟩
  have hsplit : p.eval₂ φ a = a ^ p.rootMultiplicity 0 * q.eval₂ φ a := by
    conv_lhs => rw [hpq]
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X]
  have hq' : q.eval₂ φ a = φ (q.coeff 0) + a * q.divX.eval₂ φ a := by
    conv_lhs => rw [← Polynomial.X_mul_divX_add q]
    rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C,
      add_comm]
  rw [← hq', ← hsplit, hpa]

theorem isUnit_of_pow_mul_unit_add_eq_zero (X : Scheme.{0}) [ConnectedSpace X]
    (a u b : Γ(X, ⊤)) (m : ℕ) (hu : IsUnit u) (h : a ^ m * (u + a * b) = 0)
    (hne : ((X.basicOpen a : X.Opens) : Set X).Nonempty) : IsUnit a := by
  have hcover : ∀ x : X, x ∈ X.basicOpen a ∨ x ∈ X.basicOpen (u + a * b) := by
    intro x
    rw [Scheme.mem_basicOpen_top, Scheme.mem_basicOpen_top]
    by_cases hxa : IsUnit (X.presheaf.germ ⊤ x trivial a)
    · exact Or.inl hxa
    · right
      have hU : IsUnit (X.presheaf.germ ⊤ x trivial u) := hu.map _
      have hsum : X.presheaf.germ ⊤ x trivial u =
          X.presheaf.germ ⊤ x trivial (u + a * b) +
            -(X.presheaf.germ ⊤ x trivial a * X.presheaf.germ ⊤ x trivial b) := by
        rw [map_add (f := _), map_mul]; ring
      rw [hsum] at hU
      rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hU with h1 | h1
      · exact h1
      · exact absurd (isUnit_of_mul_isUnit_left (IsUnit.neg_iff _ |>.1 h1)) hxa
  have hdisj : ∀ x : X, x ∈ X.basicOpen a → x ∈ X.basicOpen (u + a * b) → False := by
    intro x hxa hxg
    rw [Scheme.mem_basicOpen_top] at hxa hxg
    have hx : x ∈ X.basicOpen (a ^ m * (u + a * b)) := by
      rw [Scheme.mem_basicOpen_top, map_mul, map_pow]
      exact (hxa.pow m).mul hxg
    rw [h, Scheme.basicOpen_zero] at hx
    exact hx
  have hall : ∀ x : X, x ∈ X.basicOpen a := by
    intro x
    by_contra hx
    have hxg := (hcover x).resolve_left hx
    obtain ⟨y, -, hy1, hy2⟩ := isPreconnected_univ
      ((X.basicOpen a : X.Opens) : Set X) ((X.basicOpen (u + a * b) : X.Opens) : Set X)
      (X.basicOpen a).isOpen (X.basicOpen (u + a * b)).isOpen
      (fun z _ => hcover z) (by simpa using hne) ⟨x, Set.mem_univ _, hxg⟩
    exact hdisj y hy1 hy2
  exact X.toRingedSpace.isUnit_of_isUnit_germ ⊤ a
    (fun x _ => (X.mem_basicOpen_top a x).1 (hall x))

theorem isUnit_of_basicOpen_nonempty_of_universallyClosed :
    ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k))
      [UniversallyClosed f] [ConnectedSpace X] (a : Γ(X, ⊤)),
      ((X.basicOpen a : X.Opens) : Set X).Nonempty → IsUnit a := by
  intro k _ X f _ _ a hne
  let F := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop
  have hF : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed f
  obtain ⟨m, u, b, hu, h⟩ := exists_pow_mul_unit_add_eq_zero_of_integral F.hom a (hF a)
  exact isUnit_of_pow_mul_unit_add_eq_zero X a u b m hu h hne

end GlobalTheory.CompanionTheory.Ar.Flat
end

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.FibreFunctionConstant

theorem exists_section_of_germs (Y : Scheme.{0}) (g : ∀ y : Y, Y.presheaf.stalk y)
    (hg : ∀ y : Y, ∃ (W : Y.Opens) (_ : y ∈ W) (t : Γ(Y, W)),
      ∀ z (hz : z ∈ W), Y.presheaf.germ W z hz t = g z) :
    ∃ a : Γ(Y, ⊤), ∀ y, Y.presheaf.germ ⊤ y trivial a = g y := by
  choose W hW t ht using hg
  have compat : TopCat.Presheaf.IsCompatible Y.sheaf.obj W t := by
    intro i j
    apply TopCat.Presheaf.section_ext Y.sheaf (W i ⊓ W j)
    rintro y ⟨hi, hj⟩
    exact (TopCat.Presheaf.germ_res_apply Y.presheaf
      (TopologicalSpace.Opens.infLELeft (W i) (W j)) y ⟨hi, hj⟩ (t i)).trans
      ((ht i y hi).trans ((ht j y hj).symm.trans
        (TopCat.Presheaf.germ_res_apply Y.presheaf
          (TopologicalSpace.Opens.infLERight (W i) (W j)) y ⟨hi, hj⟩ (t j)).symm))
  have hcov : (⊤ : Y.Opens) ≤ iSup W := fun y _ =>
    TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hW y⟩
  obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' W ⊤ (fun i => homOfLE le_top) hcov t compat
  refine ⟨a, fun q => ?_⟩
  have e := TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE (le_top : W q ≤ ⊤)) q (hW q) a
  have e2 : (Y.presheaf.map (homOfLE (le_top : W q ≤ ⊤)).op).hom a = t q := ha q
  exact e.symm.trans ((congrArg (fun z => (Y.presheaf.germ (W q) q (hW q)).hom z) e2).trans (ht q q (hW q)))

theorem unit_of_cover {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (hc : IsCptGen ξ)
    (π : Γ(X, ⊤)) (ϖ : Ω) (h0 : ϖ ≠ 0)
    (hπ : ∀ p : Cpt ξ, genMap ξ p (X.presheaf.germ ⊤ p.1 trivial π) = ϖ)
    (k : Type) [Field k] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of k)) [UniversallyClosed f]
    [ConnectedSpace Y] (ι : Y ⟶ X) (hι : ι.appTop π = 0) (hr : Set.range ι = zeroSet ξ ϖ)
    (h : Cpt ξ → Ω)
    (H : ∀ p : Cpt ξ, ¬ unitAt ξ p ϖ → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ¬ unitAt ξ q ϖ →
      h p ∈ regAt ξ q ∧ (h p - h q) / ϖ ∈ regAt ξ q)
    (hex : ∃ p, ¬ unitAt ξ p ϖ ∧ unitAt ξ p (h p)) : ∀ p, ¬ unitAt ξ p ϖ → unitAt ξ p (h p) := by
  have hy : ∀ y : Y, ι y ∈ zeroSet ξ ϖ := fun y => hr ▸ ⟨y, rfl⟩
  choose hs hn using hy
  have hreg : ∀ y : Y, ∃ c : X.presheaf.stalk (ι y), genMap ξ ⟨ι y, hs y⟩ c = h ⟨ι y, hs y⟩ := fun y => by
    obtain ⟨U, hU, HU⟩ := H ⟨ι y, hs y⟩ (hn y)
    exact (HU _ hU (hn y)).1
  choose c hcv using hreg
  have hzero : ∀ y : Y, (ι.stalkMap y).hom (X.presheaf.germ ⊤ (ι y) trivial π) = 0 := fun y => by
    have := Scheme.Hom.germ_stalkMap_apply ι ⊤ y trivial π
    rw [this]
    have e : (ι.app ⊤).hom π = 0 := hι
    erw [e]
    exact map_zero _
  obtain ⟨a, ha⟩ := exists_section_of_germs Y (fun y => (ι.stalkMap y).hom (c y)) (fun y => by
    obtain ⟨U, hU, HU⟩ := H ⟨ι y, hs y⟩ (hn y)
    obtain ⟨W, hW, t, ht⟩ := X.presheaf.exists_germ_eq (c y)
    refine ⟨ι ⁻¹ᵁ (W ⊓ U), ⟨hW, hU⟩, ι.app (W ⊓ U) (X.presheaf.map (homOfLE inf_le_left).op t), fun z hz => ?_⟩
    have hz' : ι z ∈ W ⊓ U := hz
    rw [← Scheme.Hom.germ_stalkMap_apply ι (W ⊓ U) z hz']
    have e1 := TopCat.Presheaf.germ_res_apply X.presheaf
      (homOfLE inf_le_left : W ⊓ U ⟶ W) (ι z) hz' t
    erw [e1]
    obtain ⟨d, hd⟩ := (HU ⟨ι z, hs z⟩ hz'.2 (hn z)).2
    have e2 : genMap ξ ⟨ι z, hs z⟩ (X.presheaf.germ W (ι z) hz'.1 t) = h ⟨ι y, hs y⟩ := by
      rw [← hcv y, ← ht]
      exact genMap_germ_eq_genMap_germ ξ W ⟨ι z, hs z⟩ ⟨ι y, hs y⟩ hz'.1 hW t
    have e3 : X.presheaf.germ W (ι z) hz'.1 t = c z + X.presheaf.germ ⊤ (ι z) trivial π * d := by
      apply hc.inj ⟨ι z, hs z⟩
      have e4 := hπ ⟨ι z, hs z⟩
      refine e2.trans ?_
      rw [map_add (f := _), map_mul]
      erw [hcv z, e4, hd]
      field_simp
      ring
    erw [e3]
    rw [map_add (f := _), map_mul, hzero, zero_mul, add_zero])
  have hiff : ∀ y : Y, y ∈ Y.basicOpen a ↔ unitAt ξ ⟨ι y, hs y⟩ (h ⟨ι y, hs y⟩) := fun y => by
    rw [Scheme.mem_basicOpen_top]
    erw [ha y]
    rw [isUnit_map_iff]
    refine Iff.trans ?_ (unitAt_iff_of_isCptGen ξ hc ⟨ι y, hs y⟩ _).symm
    constructor
    · intro hu
      exact ⟨c y, hu, hcv y⟩
    · rintro ⟨u, hu, e⟩
      rwa [← hc.inj ⟨ι y, hs y⟩ (e.trans (hcv y).symm)]
  have lift : ∀ p : Cpt ξ, ¬ unitAt ξ p ϖ → ∃ y : Y, p = ⟨ι y, hs y⟩ := fun p hp => by
    obtain ⟨y, hy⟩ : p.1 ∈ Set.range ι := hr ▸ (coe_mem_zeroSet p).2 hp
    exact ⟨y, Subtype.ext hy.symm⟩
  obtain ⟨p₀, hp₀, hu₀⟩ := hex
  obtain ⟨y₀, rfl⟩ := lift p₀ hp₀
  have hu := isUnit_of_basicOpen_nonempty_of_universallyClosed k Y f a ⟨y₀, (hiff y₀).2 hu₀⟩
  intro p hp
  obtain ⟨y, rfl⟩ := lift p hp
  refine (hiff y).1 ?_
  rw [Y.basicOpen_of_isUnit hu]
  trivial

end PositivityTheory.Xgn.FibreFunctionConstant

open PositivityTheory.Xgn.FibreFunctionConstant in
theorem PositivityTheory.Xgn.function_on_connected_fibre_unit : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) → ∀ h : Cpt ξ → Ω, (∀ p : Cpt ξ, ¬ unitAt ξ p (algebraMap O Ω ϖ) → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ¬ unitAt ξ q (algebraMap O Ω ϖ) → h p ∈ regAt ξ q ∧ (h p - h q) / algebraMap O Ω ϖ ∈ regAt ξ q) → (∃ p, ¬ unitAt ξ p (algebraMap O Ω ϖ) ∧ unitAt ξ p (h p)) → ∀ p, ¬ unitAt ξ p (algebraMap O Ω ϖ) → unitAt ξ p (h p) := by
  intro X Ω _ ξ O _ _ _ _ s _ ϖ hϖ hinj hs hc hconn h H hex
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  obtain ⟨U, hU, hUc, -⟩ := cpt_open_integral X Ω ξ hc
  haveI : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion _ (by simpa using hUc)
  let r : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶ Spec (CommRingCat.of O) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))
  haveI : IsClosedImmersion r :=
    IsClosedImmersion.spec_of_surjective _ (IsLocalRing.residue_surjective (R := O))
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hrr : ∀ x : Spec (CommRingCat.of O), x ∈ Set.range r ↔ ϖ ∈ x.asIdeal := fun x => by
    have e : Set.range r = PrimeSpectrum.zeroLocus (RingHom.ker (IsLocalRing.residue O) : Set O) :=
      range_comap_of_surjective _ _ (IsLocalRing.residue_surjective (R := O))
    rw [e, IsLocalRing.ker_residue, hmax, PrimeSpectrum.zeroLocus_span]
    exact Set.singleton_subset_iff
  let ι : pullback (U.ι ≫ s) r ⟶ X := pullback.fst _ _ ≫ U.ι
  have hr : Set.range ι = zeroSet ξ (algebraMap O Ω ϖ) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      have h1 : genPt ξ ⤳ ι y := (hU _).1 (pullback.fst (U.ι ≫ s) r y).2
      refine ⟨h1, ?_⟩
      rw [(ConstReg.regular_const X Ω ξ O s hs ⟨_, h1⟩ ϖ).2 hc, not_not, ← hrr]
      refine ⟨pullback.snd (U.ι ≫ s) r y, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← pullback.condition]
      simp [ι]
    · rintro ⟨h1, h2⟩
      rw [(ConstReg.regular_const X Ω ξ O s hs ⟨_, h1⟩ ϖ).2 hc, not_not, ← hrr] at h2
      have h3 : (⟨x, (hU x).2 h1⟩ : U.toScheme) ∈ Set.range (pullback.fst (U.ι ≫ s) r) := by
        rw [Scheme.Pullback.range_fst]
        exact h2
      obtain ⟨y, hy⟩ := h3
      refine ⟨y, ?_⟩
      simp [ι, hy]
  haveI : ConnectedSpace (pullback (U.ι ≫ s) r : Scheme.{0}) := by
    rw [← hr, ← Set.image_univ] at hconn
    rw [connectedSpace_iff_univ]
    exact ⟨hconn.1.of_image, ι.isEmbedding.isInducing.isPreconnected_image.1 hconn.2⟩
  refine unit_of_cover ξ hc (s.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ)) _
    ((map_ne_zero_iff _ hinj).2 hϖ.ne_zero) (fun p => ConstReg.genMap_germ_const ξ s hs p ϖ)
    (IsLocalRing.ResidueField O) _ (pullback.snd (U.ι ≫ s) r) ι ?_ hr h H hex
  have e : ι ≫ s = pullback.snd (U.ι ≫ s) r ≫ r := by
    rw [← pullback.condition]; simp [ι]
  have e1 : r.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ) = 0 := by
    have h3 := congrArg (fun q => q.hom ϖ)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (IsLocalRing.residue O)))
    have h3' : (Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField O))).inv.hom (IsLocalRing.residue O ϖ) =
      r.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ϖ) := h3
    rw [← h3', (IsLocalRing.residue_eq_zero_iff ϖ).2 (hmax ▸ Ideal.mem_span_singleton_self ϖ), map_zero]
  have e2 : (ι ≫ s).appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ) = 0 := by
    rw [e, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, e1, map_zero]
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at e2
  exact e2
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConnectedSpecialFibreConstant
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConnectedSpecialFibreConstant
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem unitAt_of_localLifts_of_unitAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) → ∀ h : Cpt ξ → Ω, (∀ p : Cpt ξ, ¬ unitAt ξ p (algebraMap O Ω ϖ) → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ¬ unitAt ξ q (algebraMap O Ω ϖ) → h p ∈ regAt ξ q ∧ (h p - h q) / algebraMap O Ω ϖ ∈ regAt ξ q) → (∃ p, ¬ unitAt ξ p (algebraMap O Ω ϖ) ∧ unitAt ξ p (h p)) → ∀ p, ¬ unitAt ξ p (algebraMap O Ω ϖ) → unitAt ξ p (h p) :=
  @PositivityTheory.Xgn.function_on_connected_fibre_unit

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConnectedSpecialFibreConstantStatement
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connected_special_fibre_constant : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) → ∀ h : Cpt ξ → Ω, (∀ p : Cpt ξ, ¬ unitAt ξ p (algebraMap O Ω ϖ) → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ¬ unitAt ξ q (algebraMap O Ω ϖ) → h p ∈ regAt ξ q ∧ (h p - h q) / algebraMap O Ω ϖ ∈ regAt ξ q) → (∃ p, ¬ unitAt ξ p (algebraMap O Ω ϖ) ∧ unitAt ξ p (h p)) → ∀ p, ¬ unitAt ξ p (algebraMap O Ω ϖ) → unitAt ξ p (h p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.unitAt_of_localLifts_of_unitAt | exact GlobalTheory.CompanionTheory.Ar.Flat.unitAt_of_localLifts_of_unitAt | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.unitAt_of_localLifts_of_unitAt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PropZProved
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.PropZPf

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem div_sub_mem {L : Lat ξ Ω} {q : Cpt ξ} {w σ tp tq y : Ω} (a : ℤ) (M : ℕ) (hw0 : w ≠ 0)
    (hwq : w ∈ regAt ξ q) (hσ : σ ≠ 0) (hgq : L.IsGenAt q tq) (htp : tp ≠ 0)
    (hhq : w ^ a / (σ / tq) ^ M ∈ regAt ξ q) (hy : y ∈ L q) (hd : tp - tq = w • y) :
    (w ^ a / (σ / tp) ^ M - w ^ a / (σ / tq) ^ M) / w ∈ regAt ξ q := by
  rw [hgq.2, Submodule.mem_span_singleton] at hy
  obtain ⟨r, rfl⟩ := hy
  have hr : ((r • tq : Ω)) = (r : Ω) * tq := rfl
  rw [hr, smul_eq_mul] at hd
  have htq := hgq.1
  have e1 : tp = tq * (1 + w * r) := by linear_combination hd
  have hu : (1 + w * (r : Ω)) ≠ 0 := by
    intro h0; apply htp; rw [e1, h0, mul_zero]
  have e2 : w ^ a / (σ / tp) ^ M = w ^ a / (σ / tq) ^ M * (1 + w * r) ^ M := by
    rw [e1, div_pow, div_pow, mul_pow]
    field_simp
  have g := geom_sum_mul (1 + w * (r : Ω)) M
  have e3 : (w ^ a / (σ / tp) ^ M - w ^ a / (σ / tq) ^ M) / w =
      w ^ a / (σ / tq) ^ M * (r : Ω) * ∑ i ∈ Finset.range M, (1 + w * (r : Ω)) ^ i := by
    rw [e2, div_eq_iff hw0]
    linear_combination (-(w ^ a / (σ / tq) ^ M)) * g
  rw [e3]
  refine mul_mem (mul_mem hhq r.2) (Subring.sum_mem _ fun i _ => pow_mem ?_ i)
  exact add_mem (one_mem _) (mul_mem hwq r.2)

end GlobalTheory.CompanionTheory.Ar.Flat.PropZPf


open GlobalTheory.CompanionTheory.Ar.Flat.PropZPf in
theorem GlobalTheory.CompanionTheory.Ar.Flat.PropZ_holds : GlobalTheory.CompanionTheory.Ar.Flat.PropZ := by
  intro X Ω _ ξ O _ _ _ _ s _ ϖ hϖ hinj hs hg hn hconn L σ hvb htriv hgen
  obtain ⟨M, a, hM, hreg, p₀, hp₀, -, hord₀⟩ :=
    GlobalTheory.CompanionTheory.Ar.Flat.exists_regular_section_generator X Ω ξ O s ϖ hϖ hinj hs hg hn hconn.nonempty L σ hvb hgen
  have hw0 : algebraMap O Ω ϖ ≠ 0 := fun e => hϖ.ne_zero (hinj (by rw [map_zero]; exact e))
  have hwreg : ∀ p : Cpt ξ, algebraMap O Ω ϖ ∈ regAt ξ p := fun p =>
    (GlobalTheory.CompanionTheory.Ar.Flat.ConstReg.regular_const X Ω ξ O s hs p ϖ).1
  have hunit : ∀ (p : Cpt ξ) (o : O), unitAt ξ p (algebraMap O Ω o) ↔ o ∉ (s p.1).asIdeal :=
    fun p o => (GlobalTheory.CompanionTheory.Ar.Flat.ConstReg.regular_const X Ω ξ O s hs p o).2 hg
  have hgf : ∀ q : Cpt ξ, unitAt ξ q (algebraMap O Ω ϖ) → q ∈ genFibre O ξ := by
    intro q hq o ho
    rw [hunit]
    intro hmem
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ho hϖ
    have hP : (s q.1).asIdeal.IsPrime := (s q.1).isPrime
    rw [hu] at hmem
    rcases hP.mem_or_mem hmem with h1 | h1
    · exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (by
        have := Ideal.mul_mem_left _ ((u⁻¹ : Oˣ) : O) h1
        rwa [Units.inv_mul] at this))
    · exact (hunit q ϖ).1 hq (hP.mem_of_pow_mem n h1)
  have hσ : σ ≠ 0 := hord₀.ne_zero hM.ne'
  obtain ⟨t, ht⟩ := htriv
  have htq : ∀ q : Cpt ξ, ¬ unitAt ξ q (algebraMap O Ω ϖ) → L.IsGenAt q (t q) := fun q hq => by
    obtain ⟨U, hU, H⟩ := ht q hq
    obtain ⟨h0, h1, -⟩ := H q hU hq
    exact ⟨h0, h1⟩
  have hloc : ∀ p : Cpt ξ, ¬ unitAt ξ p (algebraMap O Ω ϖ) → ∃ U : X.Opens, p.1 ∈ U ∧
      ∀ q : Cpt ξ, q.1 ∈ U → ¬ unitAt ξ q (algebraMap O Ω ϖ) →
        (fun p : Cpt ξ => algebraMap O Ω ϖ ^ a / (σ / t p) ^ M) p ∈ regAt ξ q ∧
        ((fun p : Cpt ξ => algebraMap O Ω ϖ ^ a / (σ / t p) ^ M) p -
          (fun p : Cpt ξ => algebraMap O Ω ϖ ^ a / (σ / t p) ^ M) q) / algebraMap O Ω ϖ ∈ regAt ξ q := by
    intro p hp
    obtain ⟨U, hU, H⟩ := ht p hp
    refine ⟨U, hU, fun q hqU hq => ?_⟩
    obtain ⟨h0, h1, y, hy, hd⟩ := H q hqU hq
    exact ⟨hreg q (t p) ⟨h0, h1⟩, div_sub_mem a M hw0 (hwreg q) hσ (htq q hq) h0
      (hreg q (t q) (htq q hq)) hy hd⟩
  have hu₀ : unitAt ξ p₀ ((fun p : Cpt ξ => algebraMap O Ω ϖ ^ a / (σ / t p) ^ M) p₀) := by
    have := ZUnit.inv ((orderAt_iff_div (htq p₀ hp₀).1 (htq p₀ hp₀).2).1 hord₀)
    rwa [inv_div] at this
  have key := GlobalTheory.T.connected_special_fibre_constant X Ω ξ O s ϖ hϖ hinj hs hg hconn
    (fun p : Cpt ξ => algebraMap O Ω ϖ ^ a / (σ / t p) ^ M) hloc ⟨p₀, hp₀, hu₀⟩
  refine ⟨M, a, hM, fun p => ?_⟩
  by_cases hp : unitAt ξ p (algebraMap O Ω ϖ)
  · have hgp := hgen p (hgf p hp)
    rw [orderAt_iff_div hgp.1 hgp.2, div_self hσ, one_pow, one_div]
    refine ZUnit.inv ⟨zpow_ne_zero a hw0, ZLat.zpow_mem_regAt hp a, ?_⟩
    rw [← zpow_neg]
    exact ZLat.zpow_mem_regAt hp (-a)
  · rw [orderAt_iff_div (htq p hp).1 (htq p hp).2]
    have h1 : unitAt ξ p (algebraMap O Ω ϖ ^ a / (σ / t p) ^ M) := key p hp
    have := ZUnit.inv h1
    rwa [inv_div] at this
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PropZProvedStatement
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.PropZ_proved : GlobalTheory.CompanionTheory.Ar.Flat.PropZ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.PropZ_holds | exact GlobalTheory.CompanionTheory.Ar.Flat.PropZ_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.PropZ_holds <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.TauInInjective
section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.SpecMapFactorisation
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map (CommRingCat.ofHom (g.comp f)) = _
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_inj {R S : Type} [CommRing R] [CommRing S] {f g : R →+* S} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem spec_map_factorisation {X : Scheme.{0}} {A A' B B' : CommRingCat.{0}} (u : A ⟶ B) [IsIso u] (r : A ⟶ A') (v : A' ⟶ B')
    (a : Spec A ⟶ X) (a' : Spec A' ⟶ X) (x : Spec B ⟶ X) (x' : Spec B' ⟶ X) (e : Spec.map u ≫ a = x)
    (e' : Spec.map v ≫ a' = x') (e₂ : Spec.map r ≫ a = a') : Spec.map (inv u ≫ r ≫ v) ≫ x = x' := by
  subst e e' e₂
  rw [← Category.assoc (Spec.map _), ← Spec.map_comp, IsIso.hom_inv_id_assoc, Spec.map_comp, Category.assoc]

theorem exists_factor {X : Scheme.{0}} {Ω₀ Ω₁ : Type} [Field Ω₀] [Field Ω₁] {ξ₀ : Sp Ω₀ ⟶ X} (ξ₁ : Sp Ω₁ ⟶ X)
    (h₀ : IsCptGen ξ₀) (h : genPt ξ₁ ⤳ genPt ξ₀) : ∃ i : Ω₀ →+* Ω₁, spMap i ≫ ξ₀ = ξ₁ := by
  haveI : IsIso (Scheme.stalkClosedPointTo ξ₀) := (ConcreteCategory.isIso_iff_bijective _).2 h₀.bij
  refine ⟨(inv (Scheme.stalkClosedPointTo ξ₀) ≫ X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo ξ₁).hom, ?_⟩
  exact spec_map_factorisation (Scheme.stalkClosedPointTo ξ₀) (X.presheaf.stalkSpecializes h) (Scheme.stalkClosedPointTo ξ₁) _ _ ξ₀ ξ₁
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ₀) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ₁)
    (Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := X) h)

theorem genPt_spMap {X : Scheme.{0}} {Ω₀ Ω₁ : Type} [Field Ω₀] [Field Ω₁] (i : Ω₀ →+* Ω₁) (ξ : Sp Ω₀ ⟶ X) :
    genPt (spMap i ≫ ξ) = genPt ξ :=
  congrArg (fun x => ξ x) (Subsingleton.elim (α := PrimeSpectrum Ω₀) _ _)

theorem int_frac (F : Type) [Field F] [NumberField F] : Function.Injective (algebraMap (𝓞 F) F) ∧ IsNoetherianRing (𝓞 F) ∧
    ∀ x : F, ∃ a b : 𝓞 F, algebraMap (𝓞 F) F b ≠ 0 ∧ x * algebraMap (𝓞 F) F b = algebraMap (𝓞 F) F a := by
  refine ⟨IsFractionRing.injective _ _, inferInstance, fun x => ?_⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  have : algebraMap (𝓞 F) F b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  exact ⟨a, b, this, div_mul_cancel₀ _ this⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem isGeom_of {l : Level H} {Xo : Moduli D l} {c : Coeff l} [NumberField c.F]
    {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {M : Top.RootModel (CMType H) (D.p + D.q)}
    {Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} {Fx : FixedData Y Sys}
    (o : RootOrigin Y S M Fx) {U : Set (Xo.XF c)} (Z : CptOver Y U)
    (h : genPt o.𝔐.ξ₀ = genPt (Z.ξ₀ ≫ Y.j)) : Z.IsGeom := by
  have e1 : genPt Fx.ξf = genPt (Z.ξ₀ ≫ Y.j) := by
    rw [← h, ← genPt_spMap o.g Fx.ξf, ← o.g_over, ← genPt_spMap o.𝔐.fn o.𝔐.ξ₀]
    exact congrArg genPt o.𝔐.fn_over
  obtain ⟨i, hi⟩ := exists_factor Fx.ξf Z.gen (e1 ▸ specializes_rfl)
  have hb : (o.g.comp i).comp Z.inc = o.𝔐.cst := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) (spMap_inj ?_)
    rw [← o.𝔐.cst_over, ← Category.assoc, o.g_over, ← hi, spMap_comp', spMap_comp', spMap_comp', ← Z.over_inc,
      ← Y.jQ_over]
    simp only [Model.j, Category.assoc, pullback.condition]
  rintro x ⟨f, hf, hx⟩
  letI : Algebra c.F Z.Ω := Z.inc.toAlgebra
  haveI : CharZero Z.Ω := charZero_of_injective_ringHom Z.inc.injective
  haveI : Algebra.IsAlgebraic ℤ c.F := (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ)).2 inferInstance
  have h0 : IsAlgebraic c.F x := ⟨f, hf, hx⟩
  have h1 : IsAlgebraic ℤ x := h0.restrictScalars ℤ
  obtain ⟨b, hb'⟩ := o.g_const (i x) (h1.algHom i.toIntAlgHom)
  refine ⟨b, (o.g.comp i).injective ?_⟩
  rw [← hb] at hb'
  exact hb'

theorem exists_norms (hG : Top.Given) (hFD : FlatDegree) (hP : PeriodOf) (hχ : ChiEx) (Xo : ∀ l : Level H, Moduli D l)
    (l : Level H) (c : Coeff l) [NumberField c.F] (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F))
    (U : Set ((Xo l).XF c)) (Z : CptOver Y U) (τ : CMType H) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (hp : 1 ≤ D.p)
    (hq : 1 ≤ D.q) (hU : IsClopen U) (hUi : IsIrreducible U) (hZ : Z.IsGeom) :
    ∃ (φ : FrameFn (Xo l) c) (N : LogNorms c.F), FlatOnModel Z τ.1 φ ∧ (∀ s, HasInfNorm U τ.1 φ s (N.inf s)) ∧
      (∀ s, N.inf (ComplexEmbedding.conjugate s) = N.inf s) ∧ (∀ p κ, HasFinNorm U τ.1 φ p κ (N.fin p κ)) ∧
      N.IsAdelic ∧ N.deg = ((D.p : ℝ) - D.q) / 2 *
        (Real.eulerMascheroniConstant + Real.log (2 * Real.pi) - Real.log (hostRd E) - hostLval H) := by
  obtain ⟨g, ty, FU, i, hty, hper⟩ := hP hG E H D l (Xo l) c Y U Z hp hq hU hUi hZ
  obtain ⟨⟨hI, -⟩, -, -, -, hRes, -, -, hGa, -⟩ := hG
  have hpq : 1 ≤ D.p + D.q := by omega
  obtain ⟨φ, hl, hf, -⟩ := GlobalTheory.T.flat_zero_from_resolution_and_gaga hRes hGa E H D l (Xo l) c _ _ Y U Z τ.1 (int_frac c.F) hpq τ.2 hZ
  obtain ⟨hinf, hfg⟩ := GlobalTheory.T.flat_first_from_resolution_and_gaga hRes hGa E H D l (Xo l) c _ _ Y U Z τ.1 φ (int_frac c.F) hpq τ.2 hZ hl hf
  have hφ : IsFlatGen U τ.1 φ FU i := hfg g ty FU i hty fun P y hPer hu hy => (hper y hy).2 ⟨P, hPer, hu⟩
  obtain ⟨φ', N', hφ', hN', -⟩ := GlobalTheory.T.flat_theorem_of_resolution_gaga hRes hGa hI E H D Xo l c U τ.1 g ty FU i hpq τ.2 hg hty hU hUi hper
  obtain ⟨a, ha, he⟩ := GlobalTheory.T.flat_gen_frame_complex_compat E H D l (Xo l) c U τ.1 φ' φ g ty FU i hty hφ' hφ fun y hy hr => (hper y hy).1 hr
  have hfin : ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), ∃ t, HasFinNorm U τ.1 φ p κ t := fun p κ =>
    ⟨_, TopA.hasFinNorm_of_eq hl ha he (hN'.2 p κ)⟩
  choose t ht ht' using hinf
  choose tf htf using hfin
  let N : LogNorms c.F := ⟨fun s => t (InfinitePlace.mk s).embedding, tf⟩
  have hN : ∀ s, HasInfNorm U τ.1 φ s (N.inf s) := fun s => by
    show HasInfNorm U τ.1 φ s (t (InfinitePlace.mk s).embedding)
    rcases InfinitePlace.embedding_mk_eq s with h | h
    · rw [h]; exact ht s
    · rw [h]
      have e : (starRingEnd ℂ).comp (ComplexEmbedding.conjugate s) = s := by
        ext x; simp [ComplexEmbedding.conjugate_coe_eq]
      have := ht' (ComplexEmbedding.conjugate s)
      rwa [e] at this
  haveI : NeZero H.d := ⟨H.d_prime.ne_zero⟩
  obtain ⟨χ, hχ1, hχ2⟩ := hχ E H
  obtain ⟨h1, h2⟩ := GlobalTheory.T.kronecker_character_period_formula hFD E H D l (Xo l) c g ty FU i U τ.1 φ N χ hχ1 hty τ.2 hφ hN htf
  refine ⟨φ, N, hf, hN, fun s => ?_, htf, h1, by rw [h2, hχ2]⟩
  show t _ = t _
  rw [InfinitePlace.mk_conjugate_eq]

end RootFieldNumerics.RF
end
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem tauIn_injective {l : Level H} (c : Coeff l) (τ : E →+* ℂ) : Function.Injective (tauIn c τ) := by
  intro a b hab
  have h : τ (a : E) = τ (b : E) := by
    have := congrArg (fun x : c.F => (x : ℂ)) hab
    simpa [tauIn] using this
  exact RingOfIntegers.ext (τ.injective h)

set_option maxHeartbeats 1600000 in
theorem core (hSm : SmoothLine) (hLc : LocalCmp) (hNu : Numerics) (hF : HT.FarguesHodgeTate) {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} [NumberField c.F] {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {U : Set (Xo.XF c)}
    (Z : CptOver Y U) (φ : FrameFn Xo c) (τ : CMType H) (N : LogNorms c.F) {S : Finset ℕ} {Ω : Type} [Field Ω]
    {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)
    (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω)
    (hx : CMType H × Fin (D.p + D.q) → HermLine J) (n : ℕ) (hflat : FlatOnModel Z τ.1 φ)
    (hinf : ∀ s, HasInfNorm U τ.1 φ s (N.inf s)) (hconj : ∀ s, N.inf (ComplexEmbedding.conjugate s) = N.inf s)
    (hfin : ∀ p κ, HasFinNorm U τ.1 φ p κ (N.fin p κ)) (had : N.IsAdelic)
    (hNdeg : N.deg = ((D.p : ℝ) - D.q) / 2 *
      (Real.eulerMascheroniConstant + Real.log (2 * Real.pi) - Real.log (hostRd E) - hostLval H))
    (hgp : genPt 𝔐.ξ₀ = genPt (Z.ξ₀ ≫ Y.j)) (hbir : Birational y) (hvar : IsArithVar (mCoordIdeal y) n)
    (hroot : Fl.RootLines xdeg e) (hhod : ∀ r, Fl.IsHodgeLine r (e r) (hx r)) (hxa : ∀ r, (hx r).a = xdeg r)
    (h2S : 2 ∈ S) (hdS : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) (hfree : ∀ p ∈ S, HT.HTFree 𝔐 p)
    (hpq : 0 < D.p + D.q)
    (hnum : ∀ p : ℕ, p.Prime → p ∉ S → ∀ (a : ⋀[Ω]^D.p 𝔐.Li) (b : ⋀[Ω]^D.q 𝔐.Li), a ≠ 0 → b ≠ 0 →
      (∃ x f, IsCoeffAt (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) D.p D.q a b x f) →
      NumTrivMod (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) D.p D.q a b) (p : Ω)) :
    ∃ (F' : Type) (_ : Field F') (_ : NumberField F') (ψ : F' →+* Ω) (A : HermLine J) (Sf : FlatHerm y ψ A),
      OverInt y ψ ∧ IsSmoothHerm A ∧ A.a = ∑ i, xdeg (τ, i) ∧
      (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), w ∈ mcPts (mCoordIdeal y) → CoordsAt 𝔐.ξ y z w →
        𝔐.Interior z → A.h w = ∏ i, (hx (τ, i)).h w) ∧
      NearRecord (D.p + D.q) S (hostRd E) (hostLval H) Sf.ht := by
  obtain ⟨F', _, _, ι, ψ, hψ, hcl⟩ := CptInputs.exists_constants hbir 𝔐.cst
  haveI : Nonempty K := hvar.1
  have hN : NormalCpt 𝔐.ξ := XR.normalCpt_of_isCptGen 𝔐.tie.gen (fun x => ⟨𝔐.normal.1 x, 𝔐.normal.2 x⟩)
  obtain ⟨hφ, a, b, hgen, hrep⟩ := id hflat
  obtain ⟨i, j, hT⟩ := GlobalTheory.T.hodge_component_matches_model_component E H D l Xo c Y U Z S Ω K J y 𝔐 hgp
  obtain ⟨a', b', d₁, d₂, h₁, h₂, ha0, hb0, ha', hb', ea, eb⟩ :=
    GlobalTheory.T.flag_cm_type_lattice_comparison E H D l Xo c Y U Z S Ω K J y 𝔐 Fl τ i j a b hT hgen
  have hdeg := GlobalTheory.T.hodge_cpt_flag_degree E H D l Xo c _ _ Y S Ω K J y 𝔐 Fl xdeg e τ hroot
  have he : ∏ i, e (τ, i) ≠ 0 := hdeg.1
  have hchar : CharZero Ω := charZero_of_injective_ringHom ψ.injective
  have hfr : ∀ p ∈ genFibre ℤ 𝔐.ξ, IsCoeffAt (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) D.p D.q a' b' p 1 := by
    intro p hp
    obtain ⟨⟨x₀, hx₀, ex⟩, hs₁, hs₂⟩ := GlobalTheory.T.cm_type_lattice_comparison E H D l Xo c Y U Z S Ω K J y 𝔐 τ i j hT p hp
    obtain ⟨hv₁, hv₂, -, -⟩ := GlobalTheory.CompanionTheory.Ar.Flat.isVBOn_eig_genFib E H D l Xo c _ _ Y U Z τ.1 (int_frac c.F) τ.2
    obtain ⟨W₁, hW₁, u₁, -, hu₁⟩ := hv₁ x₀ hx₀
    obtain ⟨W₂, hW₂, u₂, -, hu₂⟩ := hv₂ x₀ hx₀
    exact GlobalTheory.T.exterior_coeff_base_change_compat _ _ _ _ _ _ 𝔐.f i _ _ j _ _ _ _ D.p D.q a b a' b' p x₀ u₁ u₂ Z.gen 𝔐.tie.gen hT.1 hT.2.2.1 ex
      (hu₁ x₀ hx₀ hW₁) (hu₂ x₀ hx₀ hW₂) hs₁ hs₂ (hgen.2.2 x₀ hx₀) ha' hb'
  let x₀ : Cpt 𝔐.ξ := ⟨genPt 𝔐.ξ, specializes_rfl⟩
  have hx₀ : x₀ ∈ genFibre ℤ 𝔐.ξ := fun o ho =>
    ⟨by simpa using ho, CoordBase.mem_regAt_gen 𝔐.tie.gen _, CoordBase.mem_regAt_gen 𝔐.tie.gen _⟩
  have haF : exteriorPower.ιMulti Ω _ (Fl.b (.inl τ)) ≠ 0 := fun h => ha0 (by
    have e2 : d₁ • (exteriorPower.ιMulti Ω (labelRk D (.inl τ)) (Fl.b (.inl τ))) = 0 := by rw [h, smul_zero]
    exact ea.trans e2)
  have hbF : exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)) ≠ 0 := fun h => hb0 (by
    have e2 : d₂ • (exteriorPower.ιMulti Ω (labelRk D (.inr τ)) (Fl.b (.inr τ))) = 0 := by rw [h, smul_zero]
    exact eb.trans e2)
  have hVA : (𝔐.V (.inl τ)).IsVB (labelRk D (.inl τ)) _ := 𝔐.vb (.inl τ)
  have hVB : (𝔐.V (.inr τ)).IsVB (labelRk D (.inr τ)) _ := 𝔐.vb (.inr τ)
  have hco : ∀ p ∈ genFibre ℤ 𝔐.ξ, IsCoeffAt (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ))
      (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ))) p (d₁ / d₂)⁻¹ :=
    fun p hp => CptIn.isCoeffAt_of_smul h₁ h₂ ea eb (hfr p hp)
  obtain ⟨hL1, hL2, -⟩ := GlobalTheory.T.wedge_line_lattice_vector_bundle 𝔐.X Ω 𝔐.ξ 𝔐.Li (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) _ _ _ _ Set.univ
    (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ))) hVA hVB haF hbF
    ⟨x₀, trivial, _, hco x₀ hx₀⟩
  have hd0 : d₁ / d₂ ≠ 0 := div_ne_zero h₁ h₂
  have hc₁ : (d₁ / d₂ / ∏ i, e (τ, i)) * ∏ i, e (τ, i) = d₁ / d₂ := div_mul_cancel₀ _ he
  have hgn : ∀ p ∈ genFibre ℤ 𝔐.ξ, (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ))
      (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))).IsGenAt p (d₁ / d₂) :=
    fun p hp => (hL2 p trivial _).2 ⟨hd0, hco p hp⟩
  have htriv : ∀ ℓ : ℕ, ℓ.Prime → TrivMod (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ))
      (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))) (ℓ : Ω) ∨
      NumTrivMod (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ))
      (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))) (ℓ : Ω) := by
    intro ℓ hℓ
    by_cases hS : ℓ ∈ S
    · haveI : Fact ℓ.Prime := ⟨hℓ⟩
      refine Or.inl (GlobalTheory.T.wedge_line_lattice_trivial_mod 𝔐.X Ω 𝔐.ξ 𝔐.Li _ _ _ _ _ _ _ _ (ℓ : Ω) 𝔐.tie.gen (Nat.cast_ne_zero.2 hℓ.ne_zero)
        (fun q => ?_) hVA hVB haF hbF ⟨x₀, _, hco x₀ hx₀⟩
        (GlobalTheory.T.hodge_tate_free_cm_type_weight hF E H D l Xo c _ _ Y S Ω K J y 𝔐 ℓ hS hpq (hfree ℓ hS) τ))
      exact natCast_mem _ _
    · exact Or.inr (hnum ℓ hℓ hS _ _ haF hbF ⟨x₀, _, hco x₀ hx₀⟩)
  obtain ⟨r, hr⟩ := CptIn.exists_orders GlobalTheory.T.PropZ_proved ψ hcl 𝔐.all 𝔐.tie hN _ (d₁ / d₂) hL1 hgn htriv
  have hO : OverInt y ψ := overInt_of_normalCpt 𝔐.tie hN ψ
  obtain ⟨A, hAa, hAs, hAc, hAn, hAf⟩ := hSm 𝔐.X Ω 𝔐.ξ K J y F' ψ _ _ _ (d₁ / d₂ / ∏ i, e (τ, i))
    (fun σ => Real.exp (N.inf (σ.comp ι))) n 𝔐.all 𝔐.tie hN hO hbir hvar hdeg (by rw [hc₁]; exact hgn)
    (fun _ => Real.exp_pos _) (fun σ => congrArg Real.exp (hconj (σ.comp ι)))
  obtain ⟨-, Sf, hSf⟩ := exists_flatHerm_hodgeCpt_const E H D l Xo c _ _ Y S Ω K J y 𝔐 Fl xdeg e τ F' ψ A
    (d₁ / d₂ / ∏ i, e (τ, i)) r (fun σ => Real.exp (N.inf (σ.comp ι))) hroot hAa hbir hAc (div_ne_zero hd0 he)
    (by rw [hc₁]; exact hgn) (by rw [hc₁]; exact hr) (fun _ => Real.exp_pos _) hAn
  refine ⟨F', inferInstance, inferInstance, ψ, A, Sf, hO, hAs, hAa, fun z w hw hz hint => ?_, ?_⟩
  · obtain ⟨σ, hσ, -⟩ := GlobalTheory.T.complex_point_existsUnique_embedding K J Ω F' y ψ hO w hw
    obtain ⟨g, h, dg, dh, hg, hh, hdg, hgh, hne⟩ := hAf w hw
    let A₀ : HermLine J := Top.combLine (fun i => hx (τ, i)) fun _ => 1
    have hA₀a : A₀.a = ∑ i, xdeg (τ, i) := by
      show ∑ i, (1 : ℤ) • (hx (τ, i)).a = _
      simp only [one_smul, hxa]
    have hA₀h : ∀ w', A₀.h w' = ∏ i, (hx (τ, i)).h w' := fun w' => by
      show ∏ i, (hx (τ, i)).h w' ^ (1 : ℤ) = _
      simp only [zpow_one]
    have hlies := GlobalTheory.T.point_over_number_field_value 𝔐.X Ω 𝔐.ξ K J y F' ψ σ z w hN 𝔐.tie hz hσ (𝔐.all _)
    have k1 := hAn σ w g h dg dh hσ hg hh (by rw [hAa]; exact hdg) hgh
    have k2 : ‖evC w g‖ = Real.exp (N.inf (σ.comp ι)) * A₀.h w * ‖evC w h‖ := by
      refine GlobalTheory.T.hermitian_norm_section_value 𝔐.X Ω 𝔐.ξ K J y z w A₀ (d₁ / d₂ / ∏ i, e (τ, i)) _ g h dg dh 𝔐.tie.gen hz ?_ hg hh
        (by rw [hA₀a]; exact hdg) hgh hne
      intro cc u hcc hu
      refine GlobalTheory.T.flag_weighted_degree_section E H D l Xo c Y S Ω K J y 𝔐 Fl xdeg e hx A₀ τ (N.inf (σ.comp ι)) (d₁ / d₂) z w hroot hhod hA₀a
        (fun w'' _ => hA₀h w'') hz hint hd0 ?_ cc u hcc (by rw [mul_comm, ← div_div]; exact hu)
      intro hc bp bq Γ Δ α κ u' h1 h2 h3 h4 h5 h6 h7 h8 h9
      refine GlobalTheory.T.cm_type_exterior_lattice_comparison E H D l Xo c Y U Z S Ω K J y 𝔐 τ i j a b a' b' φ (σ.comp ι) _ z hc bp bq Γ Δ (d₁ * α) (d₂ * κ)
        u' hT hφ hgen hrep (hinf _) ha' hb' hint (fun a => ?_) h1 h2 h3 h4 h5 h6 ?_ ?_ ?_
      · rw [← hψ]
        exact hlies (ι a)
      · rw [mul_smul]
        exact ea.trans (congrArg (d₁ • ·) h7)
      · rw [mul_smul]
        exact eb.trans (congrArg (d₂ • ·) h8)
      · rw [← div_mul_div_comm, ← mul_div_assoc]
        exact h9
    rw [← hA₀h]
    exact mul_left_cancel₀ (Real.exp_pos _).ne' (mul_right_cancel₀ (norm_ne_zero_iff.2 hne) (k1.symm.trans k2))
  · rw [hSf]
    simp only [Real.log_exp]
    refine hNu E H D.p D.q c.F F' ι (tauIn c τ.1) N r S (tauIn_injective c τ.1) h2S 𝔐.S_prime had hNdeg ?_
    intro ℓ κ' v π hv hπ
    obtain ⟨m, k, hm, hk, hord⟩ := hr v π hπ
    have hπ0 : π ≠ 0 := by
      rintro rfl
      simp at hπ
      exact WithZero.exp_ne_zero hπ.symm
    have hrv : (r v : ℝ) = (k : ℝ) / m := by
      have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
      have : (k : ℝ) = m * (r v : ℝ) := by exact_mod_cast hk
      rw [this]; field_simp
    obtain ⟨c1, c2⟩ := hLc E H D l Xo c Y U Z S Ω K J y 𝔐 Fl τ i j a b a' b' d₁ d₂ φ F' ι ψ ℓ κ' π m k _ hgp hT hφ hgen
      hrep ha' hb' h₁ h₂ ea eb ha0 hb0 hψ hπ0 hm (fun x hx => hord x fun u hu => hx u ((hv u).1 hu)) (hfin ℓ _)
    rw [hrv]
    refine ⟨fun hS => c1 hS fun hd => hS (hdS ℓ ℓ.2 hd), fun hS => ?_⟩
    obtain ⟨κ, hκ1, hκ2⟩ := GlobalTheory.T.exists_sandwich_of_hodge_tate_free hF E H D l Xo c _ _ Y S Ω K J y 𝔐 ℓ hS hpq (hfree ℓ hS)
    exact c2 hS (hfree ℓ hS) κ hκ1 hκ2

end RootFieldNumerics.RF
end
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

theorem sum_Iic_step {M : Type} [AddCommGroup M] {N : ℕ} (f : Fin N → M) (i : Fin N) :
    f i + -∑ k ∈ Finset.Iic i, f k =
      if h : 0 < (i : ℕ) then -∑ k ∈ Finset.Iic (⟨i - 1, by omega⟩ : Fin N), f k else 0 := by
  rw [← Finset.Iio_insert, Finset.sum_insert Finset.notMem_Iio_self]
  split_ifs with h
  · have : Finset.Iio i = Finset.Iic (⟨i - 1, by omega⟩ : Fin N) := by
      ext k
      simp only [Finset.mem_Iio, Finset.mem_Iic, Fin.lt_def, Fin.le_def]
      omega
    rw [this]; abel
  · have : Finset.Iio i = ∅ := by
      ext k
      simp only [Finset.mem_Iio, Fin.lt_def, Finset.notMem_empty, iff_false]
      omega
    rw [this]; simp

theorem rootFlatOnHodge_of (h1 : CptEx) (h2 : PeriodOf) (h3 : SmoothLine) (h4 : LocalCmp) (h5 : ChiEx) (h6 : Numerics)
    (hFD : FlatDegree) (hG : Top.Given) : RootFlatOnHodge := by
  intro E _ _ _ _ H D Xo l c Y bad M Sys Fx o hY hp hq hbad hom τ
  classical
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := {}
  obtain ⟨Yl, hg, hYl, -, -, hdom⟩ := hY
  obtain ⟨U, Z, hU, hUi, hgp⟩ := h1 E H D l (Xo l) c Y bad M.Ω M.K M.ι M.y o.𝔐
  obtain ⟨φ, N, k1, k2, k3, k4, k5, k6⟩ := exists_norms hG hFD h2 h5 Xo l c Y U Z τ hg hp hq hU hUi (isGeom_of o Z hgp)
  have hdS : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ bad := fun p hp hd =>
    (hbad p).2 ⟨hp, (hd.mul_left 2).mul_right _⟩
  obtain ⟨-, -, -, -, -, -, hF, -, -, hIn, -⟩ := hG
  obtain ⟨F', _, _, ψ, A, Sf, hO, hAs, hAa, hAh, hnr⟩ := core h3 h4 h6 hF Z φ τ N o.𝔐 o.Fl M.xdeg o.e o.sing _ k1 k2 k3
    k4 k5 k6 hgp M.birational M.arith o.lines o.hodge o.sing_deg
    ((hbad 2).2 ⟨Nat.prime_two, by exact_mod_cast (dvd_mul_right (2 : ℤ) _).mul_right _⟩) hdS hom (by omega)
    (fun p hp hS => GlobalTheory.T.local_system_split_fibres E H D Xo Yl (fun p W hp hW i => ⟨((hYl p W hp hW).2 i).1, ((hYl p W hp hW).2 i).2.1⟩)
      l c hg Y hdom bad M.Ω M.K M.ι M.y o.𝔐 p hp hS (fun hd => hS (hdS p hp hd)) τ)
  let i₀ : Fin (D.p + D.q) := ⟨D.p + D.q - 1, by omega⟩
  have hi₀ : Finset.Iic i₀ = Finset.univ := by
    ext k
    simp only [Finset.mem_Iic, Fin.le_def, Finset.mem_univ, iff_true, i₀]
    omega
  obtain ⟨R, hR⟩ := GlobalTheory.T.flat_herm_root_line_degree hIn (CMType H) (D.p + D.q) M Sys o.Re τ i₀ F' ψ A Sf hO hAs
    (by show D.p + D.q - 1 + 1 = _; omega) (Sys.reg none).1 hAa (fun σ i => by
      rw [o.fund_deg, sum_Iic_step (fun k => M.xdeg (σ, k)) i]
      split_ifs with h
      · rw [o.fund_deg]
      · rfl) (fun t ht ht' σ i z hz => by
      have p1 := (M.x t (σ, i)).pos z hz.1
      have p2 := (o.Re.line (some (σ, i)) t).pos z hz.1
      have e := sum_Iic_step (fun k => Real.log ((M.x t (σ, k)).h z)) i
      rw [← o.fund_reg σ i t ht ht' z hz, ← Real.log_mul p1.ne' p2.ne'] at e
      split_ifs at e ⊢ with h
      · rw [← o.fund_reg σ _ t ht ht' z hz] at e
        exact Real.log_injOn_pos (mul_pos p1 p2) ((o.Re.line _ t).pos z hz.1) e
      · exact Real.log_injOn_pos (mul_pos p1 p2) (Set.mem_Ioi.2 one_pos) (e.trans Real.log_one.symm)) (fun x hx => by
      have hw : o.Re.R.lift x x ∈ mcPts (mCoordIdeal M.y) := o.Re.R.mem x x (o.Re.R.mem_U x)
      obtain ⟨z, -, hz⟩ := SheetDecomposition.ChartForm.exists_point o.𝔐.tie (o.Re.R.lift x x)
        (fun k => (hw.1 k).imp fun _ h => Ne.isUnit h) fun g hg => by
          have := hw.2 g hg
          rwa [MvPolynomial.eval_map] at this
      rw [o.fund_sing τ i₀ x hx, hi₀, hAh z _ hw hz ((o.interior x z hz).2 hx),
        Real.log_prod fun i _ => ((o.sing (τ, i)).pos _ hw.1).ne'])
  exact ⟨R, hR ▸ hnr⟩

end RootFieldNumerics.RF
