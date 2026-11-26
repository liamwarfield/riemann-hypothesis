module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusToAbelianVarietyConst
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfIsPullbackOfSurjective
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.JacobsonClosedPointsToolsInt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfProperGenericTorusExtensionSpecialFiber
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem isPullback_overPullback_map_left {S S' : Scheme.{0}} (f : S' ⟶ S) {X Y : Over S} (q : X ⟶ Y) :
    IsPullback (pullback.fst X.hom f) ((Over.pullback f).map q).left q.left (pullback.fst Y.hom f) := by
  refine IsPullback.of_bot (h₃₁ := f) (v₂₁ := pullback.snd Y.hom f) (v₂₂ := Y.hom) ?_ ?_
    (IsPullback.of_hasPullback Y.hom f)
  · have h₁ : ((Over.pullback f).map q).left ≫ pullback.snd Y.hom f = pullback.snd X.hom f :=
      Over.w ((Over.pullback f).map q)
    have h₂ : q.left ≫ Y.hom = X.hom := Over.w q
    rw [h₁, h₂]
    exact IsPullback.of_hasPullback X.hom f
  · exact (pullback.lift_fst _ _ _).symm

theorem nonempty_torusExtension_pullback {k Ω : Type} [Field k] [Field Ω] (f : Sp Ω ⟶ Sp k)
    (G : Over (Sp k)) [GrpObj G] (h : Nonempty (TorusExtension G)) :
    Nonempty (TorusExtension ((Over.pullback f).obj G)) := by
  obtain ⟨T⟩ := h
  letI := T.grpB
  letI := T.addCommGroup
  haveI := T.q_hom
  haveI := T.i_hom
  obtain ⟨e, he, -⟩ := GlobalTheory.splitTorus_baseChange (Sp k) (Sp Ω) f T.X
  have hq := isPullback_overPullback_map_left f T.q
  refine ⟨{ X := T.X
            addCommGroup := T.addCommGroup
            free := T.free
            finite := T.finite
            B := (Over.pullback f).obj T.B
            grpB := inferInstance
            isAbelian := GlobalTheory.isAbelianScheme_pullback_obj f T.B T.isAbelian
            q := (Over.pullback f).map T.q
            q_hom := inferInstance
            q_flat := MorphismProperty.of_isPullback (P := @Flat) hq T.q_flat
            q_surjective := MorphismProperty.of_isPullback (P := @Surjective) hq T.q_surjective
            q_quasiCompact := MorphismProperty.of_isPullback (P := @QuasiCompact) hq T.q_quasiCompact
            i := e.hom ≫ (Over.pullback f).map T.i
            i_hom := inferInstance
            isKernel := ?_ }⟩
  have hk := T.isKernel.map (Over.pullback f)
  refine IsPullback.of_iso hk e.symm (Iso.refl _) (Functor.Monoidal.εIso (Over.pullback f)).symm (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp
  · exact toUnit_unique _ _
  · simp
  · simp

theorem exists_ringHom_comp_eq_of_isIntegral {W k Ω : Type} [CommRing W] [IsLocalRing W] [Field k] [Field Ω]
    [IsAlgClosed Ω] (ρ : W →+* k) (hρ : RingHom.ker ρ = IsLocalRing.maximalIdeal W) (hi : ρ.IsIntegral)
    (φ : W →+* Ω) (hφ : RingHom.ker φ = IsLocalRing.maximalIdeal W) : ∃ ψ : k →+* Ω, ψ.comp ρ = φ := by
  let ρ' : IsLocalRing.ResidueField W →+* k :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal W) ρ fun a ha => (RingHom.mem_ker).1 (hρ ▸ ha)
  let φ' : IsLocalRing.ResidueField W →+* Ω :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal W) φ fun a ha => (RingHom.mem_ker).1 (hφ ▸ ha)
  letI := ρ'.toAlgebra
  letI := φ'.toAlgebra
  have hi' : ρ'.IsIntegral := RingHom.IsIntegral.tower_top (IsLocalRing.residue W) ρ' hi
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField W) k := ⟨hi'⟩
  let ψ : k →ₐ[IsLocalRing.ResidueField W] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨ψ.toRingHom, RingHom.ext fun x => ?_⟩
  exact ψ.commutes (IsLocalRing.residue W x)

theorem isSemiAbelian_of_proper_generic_of_torusExtension : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G], SmConn G → IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom → ∀ (k : Type) [Field k] (ρ : W →+* k), RingHom.ker ρ = IsLocalRing.maximalIdeal W → ρ.IsIntegral → Nonempty (TorusExtension ((Over.pullback (spMap ρ)).obj G)) → IsSemiAbelian G := by
  intro W L _ _ _ _ _ _ G _ hG hp k _ ρ hρ hi hT
  obtain ⟨hc, hs, hsep, hqc, hgc⟩ := hG
  have key : ∀ (Ω F : Type) [Field Ω] [Field F] (a : W →+* F) (ψ : F →+* Ω),
      Nonempty (TorusExtension ((Over.pullback (spMap a)).obj G)) →
      Nonempty (TorusExtension ((Over.pullback (spMap (ψ.comp a))).obj G)) := by
    intro Ω F _ _ a ψ h
    obtain ⟨E⟩ := nonempty_torusExtension_pullback (spMap ψ) _ h
    have e : spMap (ψ.comp a) = spMap ψ ≫ spMap a := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [e]
    have : IsMonHom (pullCompIso (spMap ψ) (spMap a) G).symm.hom :=
      inferInstanceAs (IsMonHom (pullCompIso (spMap ψ) (spMap a) G).inv)
    exact ⟨torusExtOfIso (pullCompIso (spMap ψ) (spMap a) G).symm E⟩
  have hA : IsAbelianScheme ((Over.pullback (spMap (algebraMap W L))).obj G) :=
    { comm := inferInstance
      smooth := by change Smooth (pullback.snd G.hom _); infer_instance
      proper := hp
      geomConnected := by change GeometricallyConnected (pullback.snd G.hom _); infer_instance }
  refine ⟨hc, hs, hsep, hqc, hgc, fun Ω _ _ q => ?_⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective q
  change Nonempty (TorusExtension ((Over.pullback (spMap φ.hom)).obj G))
  by_cases h : RingHom.ker φ.hom = ⊥
  · have hinj := (RingHom.injective_iff_ker_eq_bot _).2 h
    have e : (IsFractionRing.lift (K := L) hinj).comp (algebraMap W L) = φ.hom :=
      RingHom.ext fun x => IsFractionRing.lift_algebraMap hinj x
    rw [← e]
    exact key Ω L _ _ ⟨GlobalTheory.torusExtensionOfAbelian _ hA⟩
  · have hm : RingHom.ker φ.hom = IsLocalRing.maximalIdeal W :=
      IsLocalRing.eq_maximalIdeal ((RingHom.ker_isPrime φ.hom).isMaximal h)
    obtain ⟨ψ, e⟩ := exists_ringHom_comp_eq_of_isIntegral ρ hρ hi φ.hom hm
    rw [← e]
    exact key Ω k _ _ hT

end GlobalTheory.SS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianVarietyTorsionFiniteEndomorphismDivisible
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianVarietyTorsionFiniteEndomorphismDivisible
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.TorsionDivisible

theorem hom_ext_of_rationalPoints {K : Type} [Field K] [IsAlgClosed K] {X Y : Over (Sp K)}
    [IsReduced X.left] [LocallyOfFiniteType X.hom] [IsProper Y.hom] (f g : X ⟶ Y)
    (h : ∀ x : 𝟙_ (Over (Sp K)) ⟶ X, x ≫ f = x ≫ g) : f = g := by
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w]; infer_instance
  refine Over.OverMorphism.ext (ext_of_apply_eq (K := K) Y.hom Set.univ
    isOpen_univ.isLocallyClosed dense_univ (fun x _ hx => ?_) (by rw [Over.w, Over.w]))
  let p : 𝟙_ (Over (Sp K)) ⟶ X :=
    Over.homMk (pointOfClosedPoint (K := K) X.hom x hx) (pointOfClosedPoint_comp (K := K) X.hom x hx)
  have h1 : pointOfClosedPoint (K := K) X.hom x hx ≫ f.left =
      pointOfClosedPoint (K := K) X.hom x hx ≫ g.left := congrArg CommaMorphism.left (h p)
  have h2 : f.left (pointOfClosedPoint (K := K) X.hom x hx (IsLocalRing.closedPoint K)) =
      g.left (pointOfClosedPoint (K := K) X.hom x hx (IsLocalRing.closedPoint K)) :=
    congrArg (fun φ => φ (IsLocalRing.closedPoint K)) h1
  have h3 := pointOfClosedPoint_apply (K := K) X.hom x hx (IsLocalRing.closedPoint K)
  exact (congrArg f.left h3).symm.trans (h2.trans (congrArg g.left h3))

theorem finite_fibre_points {K : Type} [Field K] [IsAlgClosed K]
    {X Y : Over (Sp K)} [LocallyOfFiniteType X.hom] (f : X ⟶ Y)
    [IsFinite f.left] (y : 𝟙_ (Over (Sp K)) ⟶ Y) :
    Finite {x : 𝟙_ (Over (Sp K)) ⟶ X // x ≫ f = y} := by
  have hfin : (f.left ⁻¹' {y.left (IsLocalRing.closedPoint K)}).Finite :=
    f.left.finite_preimage_singleton _
  have := hfin.to_subtype
  refine Finite.of_injective
    (fun x => (⟨x.1.left (IsLocalRing.closedPoint K), by
      have h := congrArg (fun u => u.left (IsLocalRing.closedPoint K)) x.2
      exact h⟩ : (f.left ⁻¹' {y.left (IsLocalRing.closedPoint K)}))) ?_
  intro a b hab
  refine Subtype.ext (Over.OverMorphism.ext ?_)
  exact ext_of_apply_closedPoint_eq (K := K) X.hom (Over.w a.1) (Over.w b.1)
    (congrArg Subtype.val hab)

theorem finite_torsion_and_divisible :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, (n : k) ≠ 0 → Finite {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} ∧ ∀ f : B ⟶ B, IsMonHom f → (∀ x : (𝟙_ (Over (Sp k)) ⟶ B), x ^ n = 1 → x ≫ f = 1) → ∃ g : B ⟶ B, IsMonHom g ∧ f = g ^ n := by
  intro k _ _ B _ hB n hn
  have := hB.comm
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have hu : IsUnit (n : Γ(Sp k, ⊤)) := by
    simpa using (isUnit_iff_ne_zero.2 hn).map (Scheme.ΓSpecIso (.of k)).inv.hom
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := GrpTangent.finiteEtale_mulN_torsion B hu
  refine ⟨?_, fun f hf hker => ?_⟩
  · have := finite_fibre_points (mulN B n) 1
    exact Finite.of_equiv _ (Equiv.subtypeEquivRight (p := fun x => x ≫ mulN B n = 1) fun x => by
      rw [GrpTangent.comp_mulN])
  · have : ConnectedSpace B.left := GeometricallyConnected.connectedSpace_of_subsingleton B.hom
    have hc : IsClopen (Set.range (mulN B n).left) :=
      ⟨(mulN B n).left.isClosedMap.isClosed_range, (mulN B n).left.isOpenMap.isOpen_range⟩
    have h5 : Surjective (mulN B n).left :=
      ⟨Set.range_eq_univ.mp (hc.eq_univ (Set.range_nonempty _))⟩
    have : IsReduced (torsion B n).left := isReduced_of_smooth_of_isReduced (torsion B n).hom
    have hι : torsion.ι B n ≫ mulN B n = 1 := by
      rw [Hom.one_def]
      exact pullback.condition.trans (congrArg (· ≫ η[B]) (toUnit_unique _ _))
    have h6 : torsion.ι B n ≫ f = 1 := hom_ext_of_rationalPoints _ _ fun x => by
      rw [← Category.assoc, MonObj.comp_one]
      refine hker _ ?_
      rw [← GrpTangent.comp_mulN, Category.assoc, hι, MonObj.comp_one]
    have h7 : ∀ (T : Over (Sp k)) (x : T ⟶ B), x ^ n = 1 → x ≫ f = 1 := fun T x hx => by
      have e : x ≫ mulN B n = toUnit T ≫ η[B] := by rw [GrpTangent.comp_mulN, hx, Hom.one_def]
      obtain ⟨y, e'⟩ : ∃ y : T ⟶ torsion B n, y ≫ torsion.ι B n = x :=
        ⟨pullback.lift x (toUnit T) e, pullback.lift_fst _ _ _⟩
      rw [← e', Category.assoc, h6, MonObj.comp_one]
    have hm : Out.mulA B n = mulN B n := (GrpTangent.mulN_eq_pow B n).symm
    have : Etale (Out.mulA B n).left := hm ▸ h2
    have : IsFinite (Out.mulA B n).left := hm ▸ h1
    have : Surjective (Out.mulA B n).left := hm ▸ h5
    obtain ⟨φ, hφ⟩ := DivisibleHom.exists_factor n f h7
    have : IsMonHom (Out.mulA B n ≫ φ) := hφ ▸ hf
    have : IsMonHom φ := DivisibleHom.isMonHom_of_factor n φ
    exact ⟨φ, this, by rw [← hφ, DivisibleHom.mulA_comp]⟩

end GlobalTheory.TorsionDivisible
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianVarietyTorsionFiniteEndomorphismDivisibleStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_torsion_finite_endomorphism_divisible : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, (n : k) ≠ 0 → Finite {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} ∧ ∀ f : B ⟶ B, IsMonHom f → (∀ x : (𝟙_ (Over (Sp k)) ⟶ B), x ^ n = 1 → x ≫ f = 1) → ∃ g : B ⟶ B, IsMonHom g ∧ f = g ^ n := by
  first | exact @GlobalTheory.TorsionDivisible.finite_torsion_and_divisible | exact GlobalTheory.TorsionDivisible.finite_torsion_and_divisible | (intros; apply GlobalTheory.TorsionDivisible.finite_torsion_and_divisible <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PullPullAndSplitPull
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section
namespace GlobalTheory.ZJ.SplitPull

theorem free_of_isField {R M : Type} [CommRing R] (hR : IsField R) [AddCommGroup M] [Module R M] :
    Module.Free R M := by
  letI := hR.toField
  exact Module.Free.of_divisionRing R M

theorem exists_basis_pushout {R R' : CommRingCat.{0}} (hR : IsField R) (b : R ⟶ R') :
    ∃ (J : Type) (e : J → R'), ∀ (A A' : CommRingCat.{0}) (a : R ⟶ A) (p : A ⟶ A') (q : R' ⟶ A'),
      IsPushout a b p q →
      (∀ u : A', ∃ (s : Finset J) (x : J → A), u = ∑ l ∈ s, p.hom (x l) * q.hom (e l)) ∧
      ∀ (s : Finset J) (x : J → A), ∑ l ∈ s, p.hom (x l) * q.hom (e l) = 0 → ∀ l ∈ s, x l = 0 := by
  letI := b.hom.toAlgebra
  haveI : Module.Free R R' := free_of_isField hR
  let e := Module.Free.chooseBasis R R'
  refine ⟨_, e, fun A A' a p q h => ?_⟩
  letI := a.hom.toAlgebra
  letI := p.hom.toAlgebra
  letI := q.hom.toAlgebra
  letI := (p.hom.comp a.hom).toAlgebra
  haveI : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R R' A' := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h.w)
  have hp : Algebra.IsPushout R A R' A' := CommRingCat.isPushout_iff_isPushout.mp h
  let B := hp.out.basis e
  have hB : ∀ l, B l = q.hom (e l) := fun l => hp.out.basis_apply e l
  refine ⟨fun u => ⟨(B.repr u).support, B.repr u, ?_⟩, fun s x hx => ?_⟩
  · conv_lhs => rw [← B.linearCombination_repr u]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    exact Finset.sum_congr rfl fun l _ => by rw [hB, Algebra.smul_def]; rfl
  · refine linearIndependent_iff'.1 B.linearIndependent s x ?_
    rw [← hx]
    exact Finset.sum_congr rfl fun l _ => by rw [hB, Algebra.smul_def]; rfl

theorem exists_basis_sections {K K' : Type} [Field K] [Field K'] (f : Sp K' ⟶ Sp K) :
    ∃ (J : Type) (e : J → Γ(Sp K', ⊤)), ∀ (X Y : Scheme.{0}) (g : Y ⟶ X) (iX : X ⟶ Sp K) (iY : Y ⟶ Sp K'),
      IsPullback g iY iX f →
      (∀ U : X.Opens, IsAffineOpen U → ∀ u : Γ(Y, g ⁻¹ᵁ U), ∃ (s : Finset J) (x : J → Γ(X, U)),
        u = ∑ l ∈ s, (g.app U).hom (x l) * (iY.appLE ⊤ (g ⁻¹ᵁ U) le_top).hom (e l)) ∧
      ∀ (s : Finset J) (x : J → Γ(X, ⊤)), ∑ l ∈ s, g.appTop.hom (x l) * iY.appTop.hom (e l) = 0 →
        ∀ l ∈ s, x l = 0 := by
  have hR : IsField Γ(Sp K, ⊤) :=
    MulEquiv.isField (Field.toIsField K) (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv
  obtain ⟨J, e, he⟩ := exists_basis_pushout hR (f.appLE ⊤ ⊤ le_top)
  refine ⟨J, e, fun X Y g iX iY h => ?_⟩
  have po : ∀ U : X.Opens, IsAffineOpen U → _ := fun U hU => he _ _ _ _ _
    ((isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := U) (UY := g ⁻¹ᵁ U) le_top
      le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
        (isAffineOpen_top _) hU))
  refine ⟨fun U hU u => ?_, fun s x hx l hl => ?_⟩
  · have := (po U hU).1 u
    rwa [Scheme.Hom.appLE_eq_app] at this
  · refine X.IsSheaf.section_ext fun y _ => ?_
    obtain ⟨_, ⟨U, hU, rfl⟩, hy, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    refine ⟨U, le_top, hy, ?_⟩
    rw [map_zero]
    refine (po U hU).2 s (fun l => resG X le_top (x l)) ?_ l hl
    have := congrArg (resG Y (le_top : g ⁻¹ᵁ U ≤ ⊤)) hx
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul]
    congr 1
    exact congrArg (fun q : Γ(X, ⊤) ⟶ Γ(Y, g ⁻¹ᵁ U) => q.hom (x l)) (g.map_appLE le_rfl (homOfLE le_top).op)

open GlobalTheory.UU

theorem appLE_app {A B C : Scheme.{0}} (r : A ⟶ B) (φ : B ⟶ C) (s : A ⟶ C) (hs : s = r ≫ φ) (V : C.Opens)
    (k : ⊤ ≤ r ⁻¹ᵁ φ ⁻¹ᵁ V) (k' : ⊤ ≤ s ⁻¹ᵁ V) (u : Γ(C, V)) :
    (r.appLE (φ ⁻¹ᵁ V) ⊤ k).hom ((φ.app V).hom u) = (s.appLE V ⊤ k').hom u := by
  subst hs
  rw [Scheme.Hom.comp_appLE]
  rfl

theorem appTop_appLE {A B C : Scheme.{0}} (r : A ⟶ B) (φ : B ⟶ C) (s : A ⟶ C) (hs : s = r ≫ φ) (V : C.Opens)
    (k : ⊤ ≤ φ ⁻¹ᵁ V) (k' : ⊤ ≤ s ⁻¹ᵁ V) (u : Γ(C, V)) :
    r.appTop.hom ((φ.appLE V ⊤ k).hom u) = (s.appLE V ⊤ k').hom u := by
  subst hs
  have := Scheme.Hom.appLE_comp_appLE r φ V ⊤ ⊤ k le_top
  rw [← this]
  erw [r.appLE_eq_app]
  rfl

theorem appLE_appLE_top {A B C : Scheme.{0}} (r : A ⟶ B) (φ : B ⟶ C) (s : A ⟶ C) (hs : r ≫ φ = s) (V : B.Opens)
    (k : ⊤ ≤ r ⁻¹ᵁ V) (u : Γ(C, ⊤)) :
    (r.appLE V ⊤ k).hom ((φ.appLE ⊤ V le_top).hom u) = s.appTop.hom u := by
  subst hs
  have := Scheme.Hom.appLE_comp_appLE r φ ⊤ V ⊤ le_top k
  erw [(r ≫ φ).appLE_eq_app] at this
  exact congrArg (fun q => q.hom u) this

section
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {X : Type} [AddCommGroup X] {G : Over S} {G' : Over S'} [GrpObj G]
  [GrpObj G'] {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) {i : splitTorus S X ⟶ G}
  {i' : splitTorus S' X ⟶ G'} (hi : TorusCompat f F i' i)
include hF hi

theorem stable_pull {V : G.left.Opens} (hV : Stable i V) : Stable i' (F ⁻¹ᵁ V) := by
  obtain ⟨τ, hτ, hχ, hc⟩ := hi
  intro Z t g h
  have ht : (pushPt hτ t ≫ i).left = (t ≫ i').left ≫ F := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, ← hc, ← Category.assoc]; rfl
  have := hV _ (pushPt hτ t) (pushPt hF.1.w g) h
  rwa [hF.2 Z (t ≫ i') g _ (pushPt hF.1.w g) ht rfl] at this

theorem hasWt_pull {V : G.left.Opens} {u : Γ(G.left, V)} {χ : X} (hu : HasWt i V u χ) :
    HasWt i' (F ⁻¹ᵁ V) ((F.app V).hom u) χ := by
  obtain ⟨τ, hτ, hχ, hc⟩ := hi
  intro Z t g h h'
  have ht : (pushPt hτ t ≫ i).left = (t ≫ i').left ≫ F := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, ← hc, ← Category.assoc]; rfl
  have e := hF.2 Z (t ≫ i') g _ (pushPt hF.1.w g) ht rfl
  rw [appLE_app _ F _ e V h' (by rw [e]; exact h'), appLE_app _ F (pushPt hF.1.w g).left rfl V h h, ← hχ]
  refine (hu _ (pushPt hτ t) (pushPt hF.1.w g) _ _).trans (congrArg (· * _) ?_)
  show (t.left ≫ τ).appTop.hom _ = _
  rw [Scheme.Hom.comp_appTop]
  rfl

theorem hasWt_coeff {J : Type} (e : J → Γ(S', ⊤))
    (he : ∀ (Y : Over S) (s : Finset J) (x : J → Γ(Y.left, ⊤)),
      ∑ l ∈ s, (pullback.fst Y.hom f).appTop.hom (x l) * (pullback.snd Y.hom f).appTop.hom (e l) = 0 →
        ∀ l ∈ s, x l = 0)
    {V : G.left.Opens} (s : Finset J) (x : J → Γ(G.left, V))
    (hu : HasWt i' (F ⁻¹ᵁ V) (∑ l ∈ s, (F.app V).hom (x l) * (G'.hom.appLE ⊤ (F ⁻¹ᵁ V) le_top).hom (e l)) 0) :
    ∀ l ∈ s, HasWt i V (x l) 0 := by
  intro l hl Y t g h h'
  rw [torusCompat_iff] at hi
  let Y' : Over S' := Over.mk (pullback.snd Y.hom f)
  let p : Y'.left ⟶ Y.left := pullback.fst Y.hom f
  have hp : p ≫ Y.hom = Y'.hom ≫ f := pullback.condition
  let p' : Over.mk (Y'.hom ≫ f) ⟶ Y := Over.homMk p hp
  have hT := SplitTorus.isPullback_bcMap f X
  have wt : (p ≫ t.left) ≫ (splitTorus S X).hom = Y'.hom ≫ f := by rw [Category.assoc, Over.w, hp]
  have wg : (p ≫ g.left) ≫ G.hom = Y'.hom ≫ f := by rw [Category.assoc, Over.w, hp]
  let t' : Y' ⟶ splitTorus S' X := Over.homMk (hT.lift _ _ wt) (hT.lift_snd _ _ wt)
  let g' : Y' ⟶ G' := Over.homMk (hF.1.lift _ _ wg) (hF.1.lift_snd _ _ wg)
  have ht' : t'.left ≫ SplitTorus.bcMap f X = p ≫ t.left := hT.lift_fst _ _ wt
  have hg' : p ≫ g.left = g'.left ≫ F := (hF.1.lift_fst _ _ wg).symm
  have hm : p ≫ ((t ≫ i) * g).left = ((t' ≫ i') * g').left ≫ F := by
    rw [← hF.2 Y' (t' ≫ i') g' (p' ≫ t ≫ i) (p' ≫ g) ?_ hg', ← MonObj.comp_mul]
    · rfl
    · change p ≫ t.left ≫ i.left = (t'.left ≫ i'.left) ≫ F
      rw [Category.assoc, ← hi, ← Category.assoc t'.left, ht', Category.assoc]
  have key : ∀ (r : Y ⟶ G) (r' : Y' ⟶ G') (_ : p ≫ r.left = r'.left ≫ F) (k : ⊤ ≤ r.left ⁻¹ᵁ V),
      ∃ k' : ⊤ ≤ r'.left ⁻¹ᵁ F ⁻¹ᵁ V, (r'.left.appLE _ ⊤ k').hom
        (∑ l ∈ s, (F.app V).hom (x l) * (G'.hom.appLE ⊤ (F ⁻¹ᵁ V) le_top).hom (e l)) =
        ∑ l ∈ s, p.appTop.hom ((r.left.appLE V ⊤ k).hom (x l)) * Y'.hom.appTop.hom (e l) := by
    intro r r' hr k
    have k₁ : ⊤ ≤ (p ≫ r.left) ⁻¹ᵁ V := p.preimage_mono k
    have k₂ : ⊤ ≤ (r'.left ≫ F) ⁻¹ᵁ V := hr ▸ k₁
    refine ⟨k₂, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, appLE_app _ F _ hr V k₂ k₁, appTop_appLE p r.left _ rfl V k k₁]
    exact congrArg (_ * ·) (appLE_appLE_top _ _ _ (Over.w r') _ _ _)
  obtain ⟨k₁, e₁⟩ := key _ _ hm h'
  obtain ⟨k₂, e₂⟩ := key _ _ hg' h
  have h0 := hu Y' t' g' k₂ k₁
  rw [e₁, e₂, charUnit_zero_val, map_one, _root_.one_mul, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h0
  rw [charUnit_zero_val, map_one, _root_.one_mul, ← sub_eq_zero]
  refine he Y s (fun l => (((t ≫ i) * g).left.appLE V ⊤ h').hom (x l) - (g.left.appLE V ⊤ h).hom (x l)) ?_ l hl
  rw [← h0]
  exact Finset.sum_congr rfl fun l _ => by rw [map_sub, sub_mul]; rfl

end

theorem pull_pull_and_split_pull : (∀ (X Y Y' : Scheme.{0}) (C : Charts X) (φ : Y ⟶ X) (ψ : Y' ⟶ Y) [IsAffineHom φ] [IsAffineHom ψ], (C.pull φ).pull ψ = C.pull (ψ ≫ φ)) ∧ ∀ (K K' : Type) [Field K] [Field K'] (H : Over (Sp K)) [GrpObj H] (H' : Over (Sp K')) [GrpObj H'] (f : Sp K' ⟶ Sp K) (φ : H'.left ⟶ H.left) [IsAffineHom φ], IsGrpPullback H' H f φ → ∀ (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl), C.Split c → Charts.Split (C.pull φ) c := by
  refine ⟨fun X Y Y' C φ ψ _ _ => rfl, ?_⟩
  rintro K K' _ _ H _ H' _ f φ _ hφ C d c ⟨hc, i, hT⟩
  obtain ⟨i', hi, -⟩ := existsUnique_torusCompat hφ.1 i
  have := hT.hom
  refine ⟨MorphismProperty.of_isPullback (P := @GeometricallyConnected) hφ.1 hc, i', hi.isMonHom hφ,
    fun a => stable_pull hφ hi (hT.stable a), fun a j hj => hasWt_pull hφ hi (hT.inv a j hj),
    fun a j k hj => hasWt_pull hφ hi (hT.wt a j k hj), fun k x => ?_, fun a u hu => ?_⟩
  · obtain ⟨a, j, hj, hx⟩ := hT.bpf k (φ x)
    refine ⟨a, j, hj, ?_⟩
    change x ∈ H'.left.basicOpen ((φ.app (C.W a)).hom (C.r a j))
    rw [← Scheme.preimage_basicOpen]
    exact hx
  · obtain ⟨J, e, he⟩ := exists_basis_sections f
    obtain ⟨s, x, rfl⟩ := (he _ _ φ _ _ hφ.1).1 (C.W a) (C.aff a) u
    have hx := hasWt_coeff hφ hi e (fun Y => (he _ _ _ _ _ (IsPullback.of_hasPullback Y.hom f)).2) s x hu
    refine Subring.sum_mem _ fun l hl => Subring.mul_mem _ ?_ (Subring.subset_closure (Or.inl ⟨e l, rfl⟩))
    have h1 := hT.gen a (x l) (hx l hl)
    refine Subring.mem_comap.1 (Subring.closure_le.2 ?_ h1)
    rintro v (⟨w, rfl⟩ | ⟨j, hj, rfl⟩)
    · refine Subring.subset_closure (Or.inl ⟨f.appTop.hom w, ?_⟩)
      have e₁ := Scheme.Hom.appLE_comp_appLE φ H.hom ⊤ (C.W a) (φ ⁻¹ᵁ C.W a) le_top le_rfl
      have e₂ := Scheme.Hom.appLE_comp_appLE H'.hom f ⊤ ⊤ (φ ⁻¹ᵁ C.W a) le_top le_top
      simp only [hφ.1.w] at e₁
      rw [φ.appLE_eq_app] at e₁
      erw [f.appLE_eq_app] at e₂
      exact congrArg (fun q => q.hom w) (e₂.trans e₁.symm)
    · exact Subring.subset_closure (Or.inr ⟨j, hj, rfl⟩)

end GlobalTheory.ZJ.SplitPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMonHomPointedSplitExtToAbelianVariety
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMonHomPointedSplitExtToAbelianVariety
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ExtensionRigidity

theorem hom_ext_of_rationalPoints {K : Type} [Field K] [IsAlgClosed K] {X Y : Over (Sp K)}
    [Smooth X.hom] [IsProper Y.hom] (f g : X ⟶ Y)
    (h : ∀ x : 𝟙_ (Over (Sp K)) ⟶ X, x ≫ f = x ≫ g) : f = g := by
  have := isNormalScheme_of_smooth (S := Spec (.of K)) X.hom
  have : IsReduced X.left := IsNormalScheme.isReduced
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w]; infer_instance
  refine Over.OverMorphism.ext (ext_of_apply_eq (K := K) Y.hom Set.univ
    isOpen_univ.isLocallyClosed dense_univ (fun x _ hx => ?_) (by rw [Over.w, Over.w]))
  let p : 𝟙_ (Over (Sp K)) ⟶ X :=
    Over.homMk (pointOfClosedPoint (K := K) X.hom x hx) (pointOfClosedPoint_comp (K := K) X.hom x hx)
  have h1 : pointOfClosedPoint (K := K) X.hom x hx ≫ f.left =
      pointOfClosedPoint (K := K) X.hom x hx ≫ g.left := congrArg CommaMorphism.left (h p)
  have h2 : f.left (pointOfClosedPoint (K := K) X.hom x hx (IsLocalRing.closedPoint K)) =
      g.left (pointOfClosedPoint (K := K) X.hom x hx (IsLocalRing.closedPoint K)) :=
    congrArg (fun φ => φ (IsLocalRing.closedPoint K)) h1
  have h3 := pointOfClosedPoint_apply (K := K) X.hom x hx (IsLocalRing.closedPoint K)
  exact (congrArg f.left h3).symm.trans (h2.trans (congrArg g.left h3))

theorem exists_factor {S : Scheme.{0}} {X Y Z : Over S} (p : X ⟶ Y) [Flat p.left]
    [Surjective p.left] [QuasiCompact p.left] (f : X ⟶ Z)
    (h : ∀ (W : Over S) (a b : W ⟶ X), a ≫ p = b ≫ p → a ≫ f = b ≫ f) :
    ∃ β : Y ⟶ Z, p ≫ β = f := by
  have hc : ∀ {W : Scheme.{0}} (g g' : W ⟶ X.left), g ≫ p.left = g' ≫ p.left →
      g ≫ f.left = g' ≫ f.left := by
    intro W g g' hg
    have hw : g' ≫ X.hom = g ≫ X.hom := by
      rw [← Over.w p, ← Category.assoc, ← hg, Category.assoc]
    have := h (Over.mk (g ≫ X.hom)) (Over.homMk g rfl) (Over.homMk g' hw)
      (Over.OverMorphism.ext hg)
    exact congrArg CommaMorphism.left this
  have hfac := EffectiveEpi.fac p.left f.left hc
  exact ⟨Over.homMk (EffectiveEpi.desc p.left f.left hc) (by
    rw [← cancel_epi p.left, ← Category.assoc, hfac, Over.w, Over.w]),
    Over.OverMorphism.ext hfac⟩

theorem isMonHom_of_pointed :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (E : SplitExt (Sp K)) (G : Over (Sp K)) [GrpObj G], E.IsGt G → ∀ (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ f : G ⟶ B, η[G] ≫ f = η[B] → IsMonHom f := by
  intro K _ _ E G _ hG B _ hB f hf
  have := (UnitRigidity.smooth_geometricallyConnected_of_isGt E G hG).1
  obtain ⟨D⟩ := hG
  have := D.q_hom
  have := D.i_hom
  have := D.q_flat
  have := D.q_surjective
  have := D.q_affine
  have := E.free
  have := E.finite
  have := hB.proper
  obtain ⟨-, -, -, -, h1, -⟩ := (splitTorus_properties (Sp K)).1 E.X
  have : Smooth (splitTorus (Sp K) E.X).hom :=
    SmoothOfRelativeDimension.smooth (Module.finrank ℤ E.X) _
  have : Smooth (splitTorus (Sp K) E.X ⊗ G).hom :=
    inferInstanceAs (Smooth (pullback.fst (splitTorus (Sp K) E.X).hom G.hom ≫
      (splitTorus (Sp K) E.X).hom))
  have hact : ((fst (splitTorus (Sp K) E.X) G ≫ D.i) * snd _ G) ≫ f = snd _ G ≫ f := by
    refine hom_ext_of_rationalPoints _ _ fun x => ?_
    obtain ⟨b, hb⟩ := GlobalTheory.T.splitTorus_to_abelianVariety_const K E.X B hB ((D.i * (toUnit _ ≫ x ≫ snd _ G)) ≫ f)
    have e : ∀ t : 𝟙_ (Over (Sp K)) ⟶ splitTorus (Sp K) E.X,
        ((t ≫ D.i) * (x ≫ snd _ G)) ≫ f = b := by
      intro t
      have := congrArg (t ≫ ·) hb
      simp only [← Category.assoc, MonObj.comp_mul] at this
      rw [toUnit_unique (t ≫ toUnit _) (𝟙 _), Category.id_comp, Category.id_comp] at this
      exact this
    have e1 := e 1
    rw [MonObj.one_comp, _root_.one_mul] at e1
    rw [← Category.assoc, MonObj.comp_mul, ← Category.assoc, e, ← Category.assoc, e1]
  obtain ⟨β, hβ⟩ := exists_factor D.q f fun W a c h => by
    have H := UnitRigidity.isPullback_act D.i D.q D.isKernel
    rw [← H.lift_fst a c h, Category.assoc, hact, ← Category.assoc, H.lift_snd]
  have : IsMonHom β := rigidity_holds _ _ _ E.isAbelian hB β (by
    rw [← IsMonHom.one_hom D.q, Category.assoc, hβ, hf])
  rw [← hβ]
  infer_instance

end GlobalTheory.ExtensionRigidity
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMonHomPointedSplitExtToAbelianVarietyStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.isMonHom_pointed_splitExt_to_abelianVariety : ∀ (K : Type) [Field K] [IsAlgClosed K] (E : SplitExt (Sp K)) (G : Over (Sp K)) [GrpObj G], E.IsGt G → ∀ (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ f : G ⟶ B, η[G] ≫ f = η[B] → IsMonHom f := by
  first | exact @GlobalTheory.ExtensionRigidity.isMonHom_of_pointed | exact GlobalTheory.ExtensionRigidity.isMonHom_of_pointed | (intros; apply GlobalTheory.ExtensionRigidity.isMonHom_of_pointed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataIsoOfTwoWitnesses
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataIsoOfTwoWitnesses
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.WitnessData

theorem value_of_genRel {F : Type} [Field F] {B B' B₀ : Scheme.{0}} {M : LB B} {M' : LB B'} {M₀ : LB B₀} {K : Type}
    [Fintype K] {ε : K → ℤ} {φ : B ⟶ B₀} {Φ : B' ⟶ B} {w : LB.Iso M (M₀.pull φ)} {wD : LB.Iso M' (M.pull Φ)}
    {w' : LB.Iso M' (M₀.pull (Φ ≫ φ))} (T : Tri w wD w') (hM₀ : M₀.IsLB) {pt : K → (Sp F ⟶ B)}
    {pt' : K → (Sp F ⟶ B')} {pt₀ : K → (Sp F ⟶ B₀)} (hc : ∀ k, pt' k ≫ Φ = pt k)
    {t : LB.Gen (LB.LinComb M pt ε)} {t' : LB.Gen (LB.LinComb M' pt' ε)} {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} {x : F}
    (h : GenRel w t t₀ x) (h' : GenRel w' t' t₀ x) (z : Sp F) (p : K → M.ι) (q : K → M'.ι)
    (hp : ∀ k, Φ (pt' k z) ∈ M.U (p k)) (hq : ∀ k, pt' k z ∈ M'.U (q k)) :
    gm (𝟙 _) z (LB.wchart M pt p) (t.s p) =
      (∏ k, gw wD (pt' k) z (p k) (q k) ^ ε k) * gm (𝟙 _) z (LB.wchart M' pt' q) (t'.s q) := by
  have pe : ∀ k, pt k z = Φ (pt' k z) := fun k => congrArg (fun g => g z) (hc k).symm
  choose j hj using fun k => exists_chart hM₀ (φ (Φ (pt' k z)))
  have a := T.prod (ε := ε) (h' := 𝟙 _) (fun k => (hc k).trans (Category.id_comp _).symm) _ (𝟙 _) z j p q hj hp hq
  simp only [Category.id_comp] at a
  have b := ((genRel_iff w t t₀ x z).1 h).2 p j (fun k => by rw [pe]; exact hj k) (fun k => by rw [pe]; exact hp k)
  have b' := ((genRel_iff w' t' t₀ x z).1 h').2 q j hj hq
  have e := Units.ext (b.trans b'.symm)
  rw [a, _root_.mul_assoc] at e
  exact mul_left_cancel e

theorem unit_ext_field {K F : Type} [Field K] [Field F] (i : K →+* F) {V : (Sp K).Opens} {a b : Γ(Sp K, V)ˣ}
    (h : ∀ z, spMap i z ∈ V → gm (spMap i) z V a = gm (spMap i) z V b) : a = b := by
  have : QuasiCompact (spMap i) := inferInstanceAs (QuasiCompact (Spec.map _))
  have : IsDominant (spMap i) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 i.injective).le.trans bot_le)⟩
  have : IsReduced (Sp K) := inferInstanceAs (IsReduced (Spec _))
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap i)
  have e : pullU (spMap i) V a = pullU (spMap i) V b := unit_ext fun z hz => by
    rw [gm_pull (𝟙 _) _ z V hz, gm_pull (𝟙 _) _ z V hz, Category.id_comp]
    exact h z hz
  exact Units.ext ((spMap i).app_injective V (congrArg Units.val e))

theorem exists_psi_pull {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {Φ : D'.P.A.left ⟶ D.P.A.left}
    (w : LB.Iso D'.P.L (D.P.L.pull Φ)) {W : (Spec (CommRingCat.of R)).Opens} (ψW : PsiOn D W)
    {g : (TK R).left ⟶ (TW W).left} (hg : g ≫ W.ι = jK R) {x : D'.X} {y : D.X} (hx : D'.xK x ≫ Φ = D.xK y)
    (F : Type) [Field F] [Algebra (FractionRing R) F]
    (H : ∀ (z : Sp F) (p : D.P.L.ι) (q : D'.P.L.ι), Φ (D'.xK x (jFK (R := R) F z)) ∈ D.P.L.U p →
      D'.xK x (jFK (R := R) F z) ∈ D'.P.L.U q →
      gm (jFK (R := R) F) z (LB.wchart D.P.L (fun _ : PUnit => D.xK y) (fun _ => p)) ((D.psi y).s (fun _ => p)) =
        gw w (jFK (R := R) F ≫ D'.xK x) z p q ^ (-1 : ℤ) *
          gm (jFK (R := R) F) z (LB.wchart D'.P.L (fun _ : PUnit => D'.xK x) (fun _ => q)) ((D'.psi x).s (fun _ => q))) :
    ∃ b : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => D'.xK x ≫ Φ) (fun _ => -1)),
      GeneratorPullback.MapsAt D.P.L D'.P.L (J := PUnit) (fun _ => Φ) w (D'.xK x) (-1) (D'.psi x) b ∧
      LB.Gen.Corr D.P.L _ _ _ _ b (LB.pullGen D.P.L _ _ (ψW.psi y) g) := by
  have hc : g ≫ (toUnit (TW W) ≫ D.c y).left = D'.xK x ≫ Φ := by
    rw [hx]
    show g ≫ W.ι ≫ (D.c y).left = jK R ≫ (D.c y).left
    rw [← Category.assoc, hg]
  obtain ⟨b, -, vb⟩ := exists_gen D.P.isLB (K' := PUnit) (φ' := fun _ => D'.xK x ≫ Φ) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) hc)
    (LB.pullGen D.P.L _ _ (ψW.psi y) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen y) g)
  refine ⟨b, fun jN jL => ?_, corr_of_val D.P.isLB fun z J hJ => vb _ _ z J hJ⟩
  have hW : jFK (R := R) F ≫ jK R = (jFK (R := R) F ≫ g) ≫ W.ι := by rw [Category.assoc, hg]
  obtain ⟨lam, l₁, l₂⟩ : ∃ lam : Sp F ⟶ (jK R ⁻¹ᵁ W).toScheme, lam ≫ (jK R ⁻¹ᵁ W).ι = jFK (R := R) F ∧
      lam ≫ (jK R ∣_ W) = jFK (R := R) F ≫ g :=
    ⟨(isPullback_morphismRestrict (jK R) W).lift _ _ hW.symm,
      (isPullback_morphismRestrict (jK R) W).lift_snd _ _ _,
      (isPullback_morphismRestrict (jK R) W).lift_fst _ _ _⟩
  refine unit_ext_field (algebraMap (FractionRing R) F) fun z hz => ?_
  have hp : Φ (D'.xK x (jFK (R := R) F z)) ∈ D.P.L.U (jN PUnit.unit) := mem_pull.1 hz.1
  have hq : D'.xK x (jFK (R := R) F z) ∈ D'.P.L.U jL := hz.2
  obtain ⟨J, hJ, eJ⟩ := exists_good D.P.L D.P.isLB z (fun _ : PUnit => jFK (R := R) F ≫ D'.xK x ≫ Φ) jN
    (fun _ _ _ => rfl) (fun _ => hp)
  have v : val b (jFK (R := R) F) z J = val (D.psi y) (jFK (R := R) F) z J := by
    have e := val_corr hJ (ψW.psi_eq y) lam
    rw [val_pull hJ, val_pull hJ, l₁, l₂] at e
    exact (vb _ _ z J hJ).trans ((val_pull hJ _ _ _).trans e)
  rw [val_of b _ z J jN eJ, val_of (D.psi y) _ z J jN (fun k => by rw [← eJ k, hx])] at v
  refine (gm_res _ z _ hz _).trans (v.trans ((H z (jN PUnit.unit) jL hp hq).trans (Eq.symm
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (gm_res _ z _ hz _))))))
  exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull _ _ z _ hz _))

theorem exists_generic_lift {R : Type} [CommRing R] [IsDomain R] {Wo : (Spec (CommRingCat.of R)).Opens}
    (hWo : genericPoint (Spec (CommRingCat.of R)) ∈ Wo) : ∃ g : (TK R).left ⟶ (TW Wo).left, g ≫ Wo.ι = jK R :=
  ⟨IsOpenImmersion.lift Wo.ι (jK R) (by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hy : jK R y = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine]
      apply PrimeSpectrum.ext
      show Ideal.comap (algebraMap R (FractionRing R)) (PrimeSpectrum.asIdeal y) = ⊥
      rw [@Ideal.eq_bot_of_prime _ _ (PrimeSpectrum.asIdeal y) (PrimeSpectrum.isPrime y)]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))
    show jK R y ∈ Wo
    rw [hy]; exact hWo), IsOpenImmersion.lift_fac _ _ _⟩

theorem exists_isPullDeg_pre {O' R : Type} [CommRing O'] [IsDomain O'] [CommRing R] [IsDomain R] {f : O' →+* R}
    {D₀ : DegPre O'} {D D' : DegPre R} {φ : D.P.A.left ⟶ D₀.P.A.left} {φ' : D'.P.A.left ⟶ D₀.P.A.left}
    (he : eSec D.P.A ≫ φ = spMap f ≫ eSec D₀.P.A) (he' : eSec D'.P.A ≫ φ' = spMap f ≫ eSec D₀.P.A)
    {w : LB.Iso D.P.L (D₀.P.L.pull φ)} {w' : LB.Iso D'.P.L (D₀.P.L.pull φ')} (ε : D₀.X ≃+ D.X) (ε' : D₀.X ≃+ D'.X)
    (s1 : IsGrpPullback D.P.A D₀.P.A (spMap f) φ) (s1' : IsGrpPullback D'.P.A D₀.P.A (spMap f) φ')
    (s2 : w.IsGen) (s2' : w'.IsGen)
    (s3 : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec D.P.A) (fun _ => 1)) D.rig
      (rigPullOf φ (spMap f) he D₀.P.L D₀.rig))
    (s3' : LB.Gen.Maps (LB.linCombIso w' (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
      (rigPullOf φ' (spMap f) he' D₀.P.L D₀.rig))
    (s5 : ∀ y, (D.c (ε y)).left ≫ φ = spMap f ≫ (D₀.c y).left)
    (s5' : ∀ y, (D'.c (ε' y)).left ≫ φ' = spMap f ≫ (D₀.c y).left)
    (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F] (v : D₀.X → F)
    (k : ∀ y, GenRel w (LB.pullGen _ _ _ (D.psi (ε y)) (jFK (R := R) F))
      (LB.pullGen _ _ _ (D₀.psi y) (jFK (R := O') F)) (v y))
    (k' : ∀ y, GenRel w' (LB.pullGen _ _ _ (D'.psi (ε' y)) (jFK (R := R) F))
      (LB.pullGen _ _ _ (D₀.psi y) (jFK (R := O') F)) (v y))
    {Wo : (Spec (CommRingCat.of R)).Opens} (hWo : genericPoint (Spec (CommRingCat.of R)) ∈ Wo) (ψW : PsiOn D Wo) :
    ∃ hD : IsPullDeg (RingHom.id R) D D', (∀ y, hD.xe (ε' y) = ε y) ∧
      ∃ w'' : LB.Iso D'.P.L (D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R))) ≫ φ)),
        φ' = (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R))) ≫ φ ∧ HEq w' w'' ∧ Tri w hD.w w'' := by
  have hs := specOf_id R
  have hsf : specOf (RingHom.id R) ≫ spMap f = spMap f := by rw [hs, Category.id_comp]
  obtain ⟨e, e_hom, hφ⟩ := grpPullback_iso s1'
    (((isGrpPullback_pullback D.P.A (specOf (RingHom.id R))).comp s1).congr hsf rfl)
  let Φ := e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R))
  replace hφ : Φ ≫ φ = φ' := (Category.assoc _ _ _).trans hφ
  subst hφ
  have gp : IsGrpPullback D'.P.A D.P.A (specOf (RingHom.id R)) Φ :=
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback D.P.A (specOf (RingHom.id R)))).congr
      (Category.id_comp _) rfl
  have hE : eSec D'.P.A ≫ Φ = specOf (RingHom.id R) ≫ eSec D.P.A := (cubeMapOf gp).e_comm
  have hw : Φ ≫ D.P.A.hom = D'.P.A.hom := by rw [gp.1.w, hs, Category.comp_id]
  have g0 := (isGen_iff w).1 s2
  have g' := (isGen_iff w').1 s2'
  obtain ⟨wD, T⟩ := exists_cancel D₀.P.isLB w w' g0 g' D.P.isLB D'.P.isLB
  let xe : D'.X ≃+ D.X := ε'.symm.trans ε
  have hxe : ∀ y, xe (ε' y) = ε y := fun y => congrArg ε (ε'.symm_apply_apply y)
  have hc : ∀ y, (D'.c (ε' y)).left ≫ Φ = (D.c (ε y)).left := fun y => by
    apply s1.1.hom_ext
    · rw [Category.assoc, s5' y, s5 y]
    · rw [Category.assoc, hw, Over.w, Over.w]
  obtain ⟨g, hg⟩ := exists_generic_lift hWo
  refine ⟨⟨e, e_hom, wD, (isGen_iff wD).2 (T.pgen_cancel D₀.P.isLB g0 g'), hE, ?_, xe, fun x => ?_, Wo, ψW, g,
    by rw [hg, hs, Category.comp_id], fun x => ?_⟩, hxe, w', rfl, HEq.rfl, T⟩
  · have r₀ := (maps_iff w _ (fun _ => eSec D₀.P.A) _ D.rig D₀.rig (spMap f) _
      (rigPull_le φ (spMap f) he D₀.P.L) (fun _ => rfl)).1 s3
    have r₁ := (maps_iff w' _ (fun _ => eSec D₀.P.A) _ D'.rig D₀.rig (spMap f) _
      (rigPull_le (Φ ≫ φ) (spMap f) he' D₀.P.L) (fun _ => rfl)).1 s3'
    rw [← hsf] at r₁
    exact (maps_iff wD _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf (RingHom.id R)) _
      (rigPull_le Φ (specOf (RingHom.id R)) hE D.P.L) (fun _ => rfl)).2
      (T.pmaps_cancel D₀.P.isLB (fun _ => hE) r₀ r₁)
  · obtain ⟨y, rfl⟩ := ε'.surjective x
    rw [hxe]
    exact (hc y).trans ((Category.id_comp _).symm.trans (congrArg (· ≫ _) hs.symm))
  · obtain ⟨y, rfl⟩ := ε'.surjective x
    rw [hxe]
    have hx : D'.xK (ε' y) ≫ Φ = D.xK (ε y) :=
      (Category.assoc _ _ _).trans (congrArg (jK R ≫ ·) (hc y))
    refine exists_psi_pull wD ψW hg hx F fun z p q hp hq => ?_
    have v := value_of_genRel T D₀.P.isLB (fun _ => (Category.assoc _ _ _).trans (congrArg (jFK (R := R) F ≫ ·) hx))
      (k y) (k' y) z (fun _ => p) (fun _ => q) (fun _ => hp) (fun _ => hq)
    have hp' : D.xK (ε y) (jFK (R := R) F z) ∈ D.P.L.U p :=
      (congrArg (fun h => h (jFK (R := R) F z) ∈ D.P.L.U p) hx).mp hp
    have a₁ := gm_pullGen D.P.L _ _ (D.psi (ε y)) (jFK (R := R) F) (𝟙 _) z (fun _ => p) (Set.mem_iInter.2 fun _ => hp')
    have a₂ := gm_pullGen D'.P.L _ _ (D'.psi (ε' y)) (jFK (R := R) F) (𝟙 _) z (fun _ => q)
      (Set.mem_iInter.2 fun _ => hq)
    rw [Category.id_comp] at a₁ a₂
    rw [Fintype.prod_unique] at v
    exact a₁.symm.trans (v.trans (congrArg _ a₂))

theorem comm_of_pullback {S S₀ : Scheme.{0}} {B B' : Over S} {B₀ : Over S₀} {f : S ⟶ S₀} {i : S ⟶ S} (hi : i = 𝟙 S)
    {φ : B.left ⟶ B₀.left} (hφ : IsPullback φ B.hom B₀.hom f) (e : B' ⟶ (Over.pullback i).obj B)
    {φ' : B'.left ⟶ B₀.left} (hφ' : φ' = (e.left ≫ pullback.fst B.hom i) ≫ φ) {x : B ⟶ B} {x' : B' ⟶ B'}
    {x₀ : B₀.left ⟶ B₀.left} (h : x.left ≫ φ = φ ≫ x₀) (h' : x'.left ≫ φ' = φ' ≫ x₀) :
    x' ≫ e = e ≫ (Over.pullback i).map x := by
  have a : e.left ≫ pullback.snd B.hom i = B'.hom := Over.w e
  have hw : (e.left ≫ pullback.fst B.hom i) ≫ B.hom = B'.hom := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, a, hi, Category.comp_id]
  have e₁ : x'.left ≫ e.left ≫ pullback.fst B.hom i = (e.left ≫ pullback.fst B.hom i) ≫ x.left := by
    apply hφ.hom_ext
    · rw [Category.assoc, ← hφ', h', Category.assoc, h, ← Category.assoc, ← hφ']
    · rw [Category.assoc, hw, Over.w, Category.assoc, Over.w, hw]
  have e₂ : ((Over.pullback i).map x).left ≫ pullback.fst B.hom i = pullback.fst _ _ ≫ x.left :=
    pullback.lift_fst _ _ _
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · show (x'.left ≫ e.left) ≫ _ = (e.left ≫ ((Over.pullback i).map x).left) ≫ _
    rw [Category.assoc, Category.assoc, e₂, ← Category.assoc e.left]
    exact e₁
  · exact (Over.w (x' ≫ e)).trans (Over.w (e ≫ (Over.pullback i).map x)).symm

theorem witness_data_iso : Laws → Laws2 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (I : Ideal R) (f : O' →+* R) (u : R), AdmBase R I → I ≠ ⊤ → Function.Injective f → ∀ (χ χ' : Sp R ⟶ Y.X) (W : ArcWit Y a I f u χ) (W' : ArcWit Y a I f u χ'), ∃ hD : IsPullDeg (RingHom.id R) W.P.D.toPre W'.P.D.toPre, (∀ y, hD.xe (W'.e y) = W.e y) ∧ (∀ x, (letI := H.starRing; W'.P.oD.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (W.P.oD.onB.act x))) ∧ ∃ w' : LB.Iso W'.P.D.toPre.P.L (a.D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (specOf (RingHom.id R))) ≫ W.φ)), W'.φ = (hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (specOf (RingHom.id R))) ≫ W.φ ∧ HEq W'.w w' ∧ Tri W.w hD.w w' := by
  intro _ _ h5 E _ _ _ H D l Xo c W₀ Y O' _ _ _ b a R _ _ _ _ I f u hR _ hf χ χ' W W'
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := W.spec
  obtain ⟨s1', s2', s3', s4', s5', s6'⟩ := W'.spec
  obtain ⟨Wo, hWo, ⟨ψW⟩⟩ := h5.psiOnExists R I hR W.P.D
  let F := AlgebraicClosure (FractionRing R)
  have hi : Function.Injective (((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))).comp f) :=
    ((algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective R _)).comp hf
  letI : Algebra (FractionRing O') F := (IsFractionRing.lift (K := FractionRing O') hi).toAlgebra
  have hF : ∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) =
      algebraMap (FractionRing R) F (algebraMap R _ (f x)) := fun x => IsFractionRing.lift_algebraMap hi x
  obtain ⟨hD, h₁, w', h₂, h₃, h₄⟩ := exists_isPullDeg_pre W.he W'.he W.e.toAddEquiv W'.e.toAddEquiv s1 s1' s2 s2'
    s3 s3' s5 s5' F _ (s6 F _ hF rfl).1 (s6' F _ hF rfl).1 hWo ψW
  exact ⟨hD, h₁, fun x => comm_of_pullback (specOf_id R) s1.1 hD.e.hom h₂ (s4 x) (s4' x), w', h₂, h₃, h₄⟩

end GlobalTheory.WitnessData
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataIsoOfTwoWitnessesStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerationData_iso_of_two_witnesses : Laws → Laws2 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (I : Ideal R) (f : O' →+* R) (u : R), AdmBase R I → I ≠ ⊤ → Function.Injective f → ∀ (χ χ' : Sp R ⟶ Y.X) (W : ArcWit Y a I f u χ) (W' : ArcWit Y a I f u χ'), ∃ hD : IsPullDeg (RingHom.id R) W.P.D.toPre W'.P.D.toPre, (∀ y, hD.xe (W'.e y) = W.e y) ∧ (∀ x, (letI := H.starRing; W'.P.oD.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (W.P.oD.onB.act x))) ∧ ∃ w' : LB.Iso W'.P.D.toPre.P.L (a.D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (specOf (RingHom.id R))) ≫ W.φ)), W'.φ = (hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (specOf (RingHom.id R))) ≫ W.φ ∧ HEq W'.w w' ∧ Tri W.w hD.w w' := by
  first | exact @GlobalTheory.WitnessData.witness_data_iso | exact GlobalTheory.WitnessData.witness_data_iso | (intros; apply GlobalTheory.WitnessData.witness_data_iso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedBasePointFreeGenericFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedBasePointFreeGenericFibre
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.GenericSplit

theorem geometricallyConnected_snd_of_range_subset {X S T T' : Scheme.{0}} (f : X ⟶ S) (t : T ⟶ S) (t' : T' ⟶ S)
    (hr : Set.range t' ⊆ Set.range t) (h : GeometricallyConnected (pullback.snd f t)) :
    GeometricallyConnected (pullback.snd f t') := by
  refine ⟨fun L _ y Z fst snd H ↦ ?_⟩
  have H' : IsPullback (fst ≫ pullback.fst f t') snd f (y ≫ t') :=
    H.paste_horiz (.of_hasPullback f t')
  obtain ⟨s, hs⟩ := hr ⟨y (default : PrimeSpectrum L), rfl⟩
  obtain ⟨w, -⟩ := Scheme.exists_preimage_of_isPullback (.of_hasPullback (y ≫ t') t)
    (default : PrimeSpectrum L) s ((Scheme.Hom.comp_apply _ _ _).trans hs.symm)
  let m := (pullback (y ≫ t') t).fromSpecResidueField w
  let m₁ := m ≫ pullback.fst (y ≫ t') t
  let m₂ := m ≫ pullback.snd (y ≫ t') t
  have hm : m₁ ≫ y ≫ t' = m₂ ≫ t := by
    simp only [m₁, m₂, Category.assoc, pullback.condition]
  have H1 : IsPullback (pullback.fst snd m₁ ≫ fst ≫ pullback.fst f t') (pullback.snd snd m₁) f (m₂ ≫ t) := by
    rw [← hm]
    exact (IsPullback.of_hasPullback snd m₁).paste_horiz H'
  have H2 : IsPullback (pullback.lift _ _ (H1.w.trans (Category.assoc _ _ _).symm)) (pullback.snd snd m₁)
      (pullback.snd f t) m₂ := by
    refine IsPullback.of_right (h₁₂ := pullback.fst f t) (v₁₃ := f) (h₂₂ := t) ?_
      (pullback.lift_snd _ _ _) (.of_hasPullback _ _)
    rw [pullback.lift_fst]
    exact H1
  have hc : ConnectedSpace ↥(pullback snd m₁) := h.geometrically_connectedSpace _ _ _ H2
  have : Surjective m₁ := ⟨fun z ↦ ⟨(default : PrimeSpectrum _), Subsingleton.elim (α := PrimeSpectrum L) _ _⟩⟩
  have hsurj : Function.Surjective (pullback.fst snd m₁) := (pullback.fst snd m₁).surjective
  exact hsurj.connectedSpace (pullback.fst snd m₁).continuous

theorem jK_asIdeal (R : Type) [CommRing R] [IsDomain R] (z : Sp (FractionRing R)) :
    (Out.jK R z).asIdeal = ⊥ := by
  have hz : z.asIdeal = ⊥ := congrArg PrimeSpectrum.asIdeal
    (Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) z ⟨⊥, Ideal.isPrime_bot⟩)
  change Ideal.comap (algebraMap R (FractionRing R)) z.asIdeal = ⊥
  rw [hz]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R _)

theorem geometricallyConnected_and_basePointFree_generic :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → GeometricallyConnected ((Over.pullback (Out.jK R)).obj G).hom ∧ ∀ (n : Fin d) (x : ((Over.pullback (Out.jK R)).obj G).left), ∃ a j, C.wt j = c n ∧ x ∈ ((Over.pullback (Out.jK R)).obj G).left.basicOpen ((C.pull (pullback.fst G.hom (Out.jK R))).r a j) := by
  intro R _ _ _ G _ _ _ _ _ C d c Sg _ hD hS
  constructor
  · have h := geometricallyConnected_genericFibre_of_dense G.left (Sp R) G.hom Sg hD fun x hx ↦ by
      obtain ⟨K, _, t, _, ht, hc, -⟩ := hS x hx
      exact geometricallyConnected_snd_of_range_subset G.hom t _
        (by rw [Scheme.range_fromSpecResidueField, ht]) hc
    refine geometricallyConnected_snd_of_range_subset G.hom _ _ ?_ h
    rw [Scheme.range_fromSpecResidueField]
    rintro _ ⟨z, rfl⟩
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext (jK_asIdeal R z)
  · intro n x
    let V : G.left.Opens := ⨆ (a) (j) (_ : C.wt j = c n), G.left.basicOpen (C.r a j)
    obtain ⟨b, hb0, hb⟩ := GenericEq.exists_mem_of_not_mem R G Sg hD V fun y hy ↦ by
      obtain ⟨K, _, t, _, ht, -, i, hi⟩ := hS _ hy
      obtain ⟨s, hs⟩ : G.hom y ∈ Set.range t := ht ▸ rfl
      obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback (.of_hasPullback G.hom t) y s hs.symm
      obtain ⟨a, j, hj, hz'⟩ := hi.bpf n z
      have : z ∈ pullback.fst G.hom t ⁻¹ᵁ G.left.basicOpen (C.r a j) := by
        rw [Scheme.preimage_basicOpen]
        exact hz'
      simp only [V, TopologicalSpace.Opens.mem_iSup]
      exact ⟨a, j, hj, hz ▸ this⟩
    have hx := hb (pullback.fst G.hom (Out.jK R) x) (by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, jK_asIdeal]
      exact hb0)
    simp only [V, TopologicalSpace.Opens.mem_iSup] at hx
    obtain ⟨a, j, hj, hx⟩ := hx
    refine ⟨a, j, hj, ?_⟩
    have : x ∈ pullback.fst G.hom (Out.jK R) ⁻¹ᵁ G.left.basicOpen (C.r a j) := hx
    rw [Scheme.preimage_basicOpen] at this
    exact this

end GlobalTheory.GenericSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedBasePointFreeGenericFibreStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricallyConnected_basePointFree_generic_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → GeometricallyConnected ((Over.pullback (Out.jK R)).obj G).hom ∧ ∀ (n : Fin d) (x : ((Over.pullback (Out.jK R)).obj G).left), ∃ a j, C.wt j = c n ∧ x ∈ ((Over.pullback (Out.jK R)).obj G).left.basicOpen ((C.pull (pullback.fst G.hom (Out.jK R))).r a j) := by
  first | exact @GlobalTheory.GenericSplit.geometricallyConnected_and_basePointFree_generic | exact GlobalTheory.GenericSplit.geometricallyConnected_and_basePointFree_generic | (intros; apply GlobalTheory.GenericSplit.geometricallyConnected_and_basePointFree_generic <;> assumption)
end
end
