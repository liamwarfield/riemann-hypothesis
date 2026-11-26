module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
public import Development.WeilBound.CoreStatements.HodgeTatePoints.CdUniv
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordOverIntOfFiniteOrder

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductMapIff
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductMapIff
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace TripleHodge

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
  {φ : G'.left ⟶ G.left}

theorem one_left_comp (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = (1 : Over.mk (T.hom ≫ f) ⟶ G).left :=
  congrArg (fun p => p.left) (map_one (pushHom h T))

theorem isTanAt_iff (h : IsGrpPullback G' G f φ) (z : Spec (CommRingCat.of ℂ) ⟶ S') (v' : epsAt z ⟶ G')
    (v : epsAt (z ≫ f) ⟶ G) (e : v.left = v'.left ≫ φ) : IsTanAt G' z v' ↔ IsTanAt G (z ≫ f) v := by
  have one := one_left_comp h (Over.mk z)
  have wv := Over.w v'
  constructor
  · intro hv
    unfold IsTanAt at hv ⊢
    rw [e, ← Category.assoc, hv]
    exact one
  · intro hv
    unfold IsTanAt at hv ⊢
    apply h.1.hom_ext
    · rw [Category.assoc, ← e, hv]
      exact one.symm
    · have w1 := Over.w (1 : Over.mk z ⟶ G')
      rw [Category.assoc, w1, wv]
      show Spec.map _ ≫ Spec.map _ ≫ z = z
      rw [← Category.assoc, ← Spec.map_comp]
      have e₁ : CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) ≫
          CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom = 𝟙 _ := by
        ext x
        simp
      rw [e₁, Spec.map_id, Category.id_comp]

variable {X X' : Scheme.{0}}

theorem exists_iso_comp {Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) (p : Y ⟶ X') :
    ∃ w₂ : LB.Iso (L'.pull p) (L.pull (p ≫ F)), w₂.IsGen := by
  have hP : (L'.pull p).IsLB := pull_isLB hL' p
  have hr := (isGen_iff _).1 (GlobalTheory.TorsionTauCompare.isGen_refl hP)
  have hw' := (isGen_iff _).1 hw
  obtain ⟨w₂, T⟩ := exists_comp hL' w _ hw' hr hL hP
  exact ⟨w₂, (isGen_iff _).2 (T.pgen_comp hL' hw' hr)⟩

theorem exists_iso_cancel {Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) (p : Y ⟶ X') :
    ∃ w₂ : LB.Iso (L.pull (p ≫ F)) (L'.pull p), w₂.IsGen := by
  have hP : (L.pull (p ≫ F)).IsLB := pull_isLB hL (p ≫ F)
  have hr := (isGen_iff _).1 (GlobalTheory.TorsionTauCompare.isGen_refl hP)
  have hw' := (isGen_iff _).1 hw
  obtain ⟨w₂, T⟩ := exists_cancel hL w _ hw' hr hL' hP
  exact ⟨w₂, (isGen_iff _).2 (T.pgen_cancel hL hw' hr)⟩

end TripleHodge

theorem hodgeInnerProduct_tripleMap_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0})
    (t : SAB H X) (X' : Scheme.{0}) (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f)
    (z : Spec (CommRingCat.of ℂ) ⟶ X') (v' w' : epsAt z ⟶ t'.G) (v w : epsAt (z ≫ f) ⟶ t.G) (c : ℂ),
    v.left = v'.left ≫ m.φ → w.left = w'.left ≫ m.φ →
      (HodgeIP t'.G t'.PP.L z v' w' c ↔ HodgeIP t.G t.PP.L (z ≫ f) v w c) := by
  intro E _ _ _ H X t X' t' f m z v' w' v w c hv hw
  obtain ⟨i, hi, -, -⟩ := m.lin
  have tv := TripleHodge.isTanAt_iff m.cart z v' v hv
  have tw := TripleHodge.isTanAt_iff m.cart z w' w hw
  have hL := t.PP.isLB
  have hL' := t'.PP.isLB
  constructor
  · rintro ⟨-, h₁, h₂, A, _, φ, g, u, Hm, χ, a', b', a, b, p₁, p₂, p₃, p₄, p₅, p₆, rfl⟩
    obtain ⟨i₂, hi₂⟩ := TripleHodge.exists_iso_comp hL hL' hi φ
    have hP := pull_isLB hL' φ
    have hQ := pull_isLB hL (φ ≫ m.φ)
    refine ⟨hL, tv.1 h₁, tw.1 h₂, A, inferInstance, φ ≫ m.φ, g, GlobalTheory.TorsionTauCompare.transport hP hQ hi₂ u, Hm, χ,
      a', b', a, b, p₁.comp m.cart, GlobalTheory.TorsionTauCompare.isAH_transport hP hQ hi₂ u p₂, ?_, ?_, p₅, p₆, rfl⟩
    · rw [hv, ← p₃, Category.assoc]
    · rw [hw, ← p₄, Category.assoc]
  · rintro ⟨-, h₁, h₂, A, _, ψ, g, u, Hm, χ, a', b', a, b, p₁, p₂, p₃, p₄, p₅, p₆, rfl⟩
    obtain ⟨φ, rfl, hφ⟩ : ∃ φ : A.left ⟶ t'.G.left, φ ≫ m.φ = ψ ∧ φ ≫ t'.G.hom = A.hom ≫ z :=
      ⟨m.cart.1.lift ψ (A.hom ≫ z) (by rw [p₁.1.w, Category.assoc]), m.cart.1.lift_fst _ _ _, m.cart.1.lift_snd _ _ _⟩
    obtain ⟨i₂, hi₂⟩ := TripleHodge.exists_iso_cancel hL hL' hi φ
    have hP := pull_isLB hL (φ ≫ m.φ)
    have hQ := pull_isLB hL' φ
    have lift : ∀ (x : epsR ℂ ⟶ A) (y : epsAt z ⟶ t'.G) (y₀ : epsAt (z ≫ f) ⟶ t.G), y₀.left = y.left ≫ m.φ →
        x.left ≫ φ ≫ m.φ = y₀.left → x.left ≫ φ = y.left := by
      intro x y y₀ e e'
      apply m.cart.1.hom_ext
      · rw [Category.assoc, e', e]
      · rw [Category.assoc, hφ, ← Category.assoc, Over.w x, Over.w y]
        rfl
    exact ⟨hL', tv.2 h₁, tw.2 h₂, A, inferInstance, φ, g, GlobalTheory.TorsionTauCompare.transport hP hQ hi₂ u, Hm, χ,
      a', b', a, b, IsGrpPullback.cancel m.cart p₁ hφ, GlobalTheory.TorsionTauCompare.isAH_transport hP hQ hi₂ u p₂,
      lift a' v' v hv p₃, lift b' w' w hw p₄, p₅, p₆, rfl⟩

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductMapIffStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_inner_product_map_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (X' : Scheme.{0}) (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f) (z : Spec (CommRingCat.of ℂ) ⟶ X') (v' w' : epsAt z ⟶ t'.G) (v w : epsAt (z ≫ f) ⟶ t.G) (c : ℂ), v.left = v'.left ≫ m.φ → w.left = w'.left ≫ m.φ → (HodgeIP t'.G t'.PP.L z v' w' c ↔ HodgeIP t.G t.PP.L (z ≫ f) v w c) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.hodgeInnerProduct_tripleMap_iff | exact GlobalTheory.CompanionTheory.Ar.hodgeInnerProduct_tripleMap_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.hodgeInnerProduct_tripleMap_iff <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermDimensionUnique
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermDimensionUnique
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GermUniv

theorem germ_chart_universal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] [IsLocalRing S] (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d), (∀ (d₂ : ℕ) (_ : GermAt t x d₂), d = d₂) ∧ ∀ (J : Type) [Finite J] (m : ℕ) (y : overAt x (Jet S J m) ⟶ t.G), homAt x (jetAug : Jet S J m →ₐ[S] S) ≫ y = 1 → ∃! χ : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S J m, (∀ q, (jetAug : Jet S J m →ₐ[S] S) (χ (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0) ∧ y = homAt x χ ≫ g.x m :=
  PositivityTheory.HtPt.Cd.germ_univ

end GlobalTheory.CompanionTheory.Ar.GermUniv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermDimensionUniqueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_germ_dimension_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] [IsLocalRing S] (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d), (∀ (d₂ : ℕ) (_ : GermAt t x d₂), d = d₂) ∧ ∀ (J : Type) [Finite J] (m : ℕ) (y : overAt x (Jet S J m) ⟶ t.G), homAt x (jetAug : Jet S J m →ₐ[S] S) ≫ y = 1 → ∃! χ : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S J m, (∀ q, (jetAug : Jet S J m →ₐ[S] S) (χ (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0) ∧ y = homAt x χ ≫ g.x m := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GermUniv.germ_chart_universal | exact GlobalTheory.CompanionTheory.Ar.GermUniv.germ_chart_universal | (intros; apply GlobalTheory.CompanionTheory.Ar.GermUniv.germ_chart_universal <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPointsDefinedGeneric
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPointsDefinedGeneric
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem level_parametrisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) (t : SAB H S) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ S) (n : ℕ), 1 ≤ n → 0 < D.p + D.q → IsProper (Limits.pullback.snd t.G.hom ξ) → (∀ (k : Type) [Field k] (f : Ω →+* k) (g : Over.mk (spMap f ≫ ξ) ⟶ t.G), g ^ n = 1 → ∃ x : Over.mk ξ ⟶ t.G, g.left = spMap f ≫ x.left) → (∀ (k : Type) [Field k] [IsAlgClosed k] (f : Ω →+* k), Nonempty (TateIso D k (Over.mk (spMap f ≫ ξ) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)))) → ∃ (ev : D.La → (Over.mk ξ ⟶ t.G)) (ζ₀ : Ωˣ), IsPrimitiveRoot ζ₀ n ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (f : Ω →+* k), ∃ I : TateIso D k (Over.mk (spMap f ≫ ξ) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)), (I.ζ n : k) = f ζ₀ ∧ ∀ a, (I.ev n a).left = spMap f ≫ (ev a).left :=
  @PositivityTheory.HtPt.Htat.level_param

end GlobalTheory.CompanionTheory.Ar.HT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPointsDefinedGenericStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_points_defined_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) (t : SAB H S) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ S) (n : ℕ), 1 ≤ n → 0 < D.p + D.q → IsProper (Limits.pullback.snd t.G.hom ξ) → (∀ (k : Type) [Field k] (f : Ω →+* k) (g : Over.mk (spMap f ≫ ξ) ⟶ t.G), g ^ n = 1 → ∃ x : Over.mk ξ ⟶ t.G, g.left = spMap f ≫ x.left) → (∀ (k : Type) [Field k] [IsAlgClosed k] (f : Ω →+* k), Nonempty (TateIso D k (Over.mk (spMap f ≫ ξ) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)))) → ∃ (ev : D.La → (Over.mk ξ ⟶ t.G)) (ζ₀ : Ωˣ), IsPrimitiveRoot ζ₀ n ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (f : Ω →+* k), ∃ I : TateIso D k (Over.mk (spMap f ≫ ξ) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)), (I.ζ n : k) = f ζ₀ ∧ ∀ a, (I.ev n a).left = spMap f ≫ (ev a).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.level_parametrisation | exact GlobalTheory.CompanionTheory.Ar.HT.level_parametrisation | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.level_parametrisation <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeFormOfIsHodgeGram
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem hodgeForm_of_isHodgeGram (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (x : Sp ℂ ⟶ S) (n : ℕ)
    (v : Fin n → (epsAt x ⟶ G)) (Γ : Matrix (Fin n) (Fin n) ℂ) (hL : L.IsLB) (hv : ∀ i, IsTanAt G x (v i))
    (h : Fl.IsHodgeGram G L x v Γ) (i j : Fin n) : HodgeForm G L x (v i) (v j) (Γ i j) := by
  obtain ⟨Q, ψ, v', u, Hm, χ, W, hp, hiso, hAH, hvW, hΓ⟩ := h
  have hM := pull_isLB hL ψ
  obtain ⟨w, hw⟩ := LBIso.symm hiso
  exact ⟨hL, hv i, hv j, Q.A, inferInstance, ψ, Q.g, GlobalTheory.TorsionTauCompare.transport Q.isLB hM hw u, Hm, χ, v' i, v' j,
    W i, W j, hp, GlobalTheory.TorsionTauCompare.isAH_transport Q.isLB hM hw u hAH, (hvW i).1, (hvW j).1, (hvW i).2, (hvW j).2,
    hΓ i j⟩

end GlobalTheory.CompanionTheory.Ar.Fl
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ClosedInProductProjective
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ClosedInProductProjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Segre

theorem isProjOver_of_closed_product : ∀ (K : Type) [Field K] (M r : ℕ) (X' : Scheme.{0}) (j : X' ⟶ pullback (PSpace.str K M) (PSpace.str K r)), IsClosedImmersion j → IsProjOver (j ≫ pullback.fst _ _ ≫ PSpace.str K M) := by
  intro K _ M r X' j hj
  have := hj
  exact GlobalTheory.ProjSpace.isProjOver_comp_of_isClosedImmersion j
    (GlobalTheory.ProjSpace.isProjOver_pullback_str K M r)

end GlobalTheory.CompanionTheory.Ar.SncBase.Segre
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ClosedInProductProjectiveStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_in_product_projective : ∀ (K : Type) [Field K] (M r : ℕ) (X' : Scheme.{0}) (j : X' ⟶ pullback (PSpace.str K M) (PSpace.str K r)), IsClosedImmersion j → IsProjOver (j ≫ pullback.fst _ _ ≫ PSpace.str K M) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.Segre.isProjOver_of_closed_product | exact GlobalTheory.CompanionTheory.Ar.SncBase.Segre.isProjOver_of_closed_product | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.Segre.isProjOver_of_closed_product <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermLieBasis
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermLieBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GermLie

theorem germ_lie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d) (V : Type) [AddCommGroup V] [Module S V] (M : GlobalTheory.CompanionTheory.Ar.LieModel t.G x V), ∃ e : V ≃ₗ[S] (Fin d → S), (∀ v, IsCombAtG t x g.tg (e v) (M.pt v).left) ∧ ∀ r : 𝓞 E →+* Module.End S V, M.IsActOf t.act.act r → ∀ a v, e (r a v) = (rho g.B a).mulVec (e v) :=
  PositivityTheory.HtPt.Cd.germ_lie

end GlobalTheory.CompanionTheory.Ar.GermLie
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermLieBasisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_germ_lie_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d) (V : Type) [AddCommGroup V] [Module S V] (M : GlobalTheory.CompanionTheory.Ar.LieModel t.G x V), ∃ e : V ≃ₗ[S] (Fin d → S), (∀ v, IsCombAtG t x g.tg (e v) (M.pt v).left) ∧ ∀ r : 𝓞 E →+* Module.End S V, M.IsActOf t.act.act r → ∀ a v, e (r a v) = (rho g.B a).mulVec (e v) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GermLie.germ_lie | exact GlobalTheory.CompanionTheory.Ar.GermLie.germ_lie | (intros; apply GlobalTheory.CompanionTheory.Ar.GermLie.germ_lie <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionTowerWeilPairing
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeilPairingCubical
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem weil_pairing_cubical : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S) (n : ℕ), 1 ≤ n → ∃ (w : ∀ (T : Over S) (x z : T ⟶ t.G), x ^ n = 1 → z ^ n = 1 → Γ(T.left, ⊤)ˣ), (∀ (T T' : Over S) (f : T' ⟶ T) (x z : T ⟶ t.G) (hx : x ^ n = 1) (hz : z ^ n = 1) (hx' : (f ≫ x) ^ n = 1) (hz' : (f ≫ z) ^ n = 1), (w T' (f ≫ x) (f ≫ z) hx' hz' : Γ(T'.left, ⊤)) = f.left.appTop.hom (w T x z hx hz)) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ S), IsProper (Limits.pullback.snd t.G.hom g) → ∀ (x z : Over.mk g ⟶ t.G) (hx : x ^ n = 1) (hz : z ^ n = 1) (c : kˣ), Out.WeilIs t.G t.PP.L n x z (unitOn c) → w (Over.mk g) x z hx hz = unitOn c :=
  PositivityTheory.HtPt.Weilfun.weil_fun

end GlobalTheory.CompanionTheory.Ar.HT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionTowerWeilPairing
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem weil_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S) (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsAlgClosed (FractionRing O)] (y : Sp O ⟶ S) (La : Type) [AddCommGroup La] (X : TorsTower p t.G y La) (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : ℕ → Oˣ), IsProper (Limits.pullback.snd t.G.hom ((BT.genPt O).hom ≫ y)) → (∀ n (a b : La) (ga gb : Over.mk ((BT.genPt O).hom ≫ y) ⟶ t.G), ga.left = ((X.Γ n).pt (lev p n a)).left ≫ X.i n → gb.left = ((X.Γ n).pt (lev p n b)).left ≫ X.i n → Out.WeilIs t.G t.PP.L ((p ^ n : ℕ) : ℤ) ga gb (unitOn (Units.map (algebraMap O (FractionRing O) : O →* FractionRing O) (ζ n ^ B a b)))) → X.PairingRegular B ζ :=
  PositivityTheory.HtPt.Weilreg.weil_regular_of_fun weil_pairing_cubical

end GlobalTheory.CompanionTheory.Ar.HT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionTowerWeilPairingStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_tower_weil_pairing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S) (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsAlgClosed (FractionRing O)] (y : Sp O ⟶ S) (La : Type) [AddCommGroup La] (X : TorsTower p t.G y La) (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : ℕ → Oˣ), IsProper (Limits.pullback.snd t.G.hom ((BT.genPt O).hom ≫ y)) → (∀ n (a b : La) (ga gb : Over.mk ((BT.genPt O).hom ≫ y) ⟶ t.G), ga.left = ((X.Γ n).pt (lev p n a)).left ≫ X.i n → gb.left = ((X.Γ n).pt (lev p n b)).left ≫ X.i n → Out.WeilIs t.G t.PP.L ((p ^ n : ℕ) : ℤ) ga gb (unitOn (Units.map (algebraMap O (FractionRing O) : O →* FractionRing O) (ζ n ^ B a b)))) → X.PairingRegular B ζ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.weil_regular | exact GlobalTheory.CompanionTheory.Ar.HT.weil_regular | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.weil_regular <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFibreProjectiveEmbedding
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFibreProjectiveEmbedding
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem genericFibre_reduced_noetherian_closed : ∀ (F : Type) [Field F] [NumberField F] (P : Scheme.{0}) (s : P ⟶ Sp (𝓞 F)), IsProjOver s → Tor.IsNormalScheme P → IsReduced (pullback s (spMap (algebraMap (𝓞 F) F))) ∧ IsLocallyNoetherian (pullback s (spMap (algebraMap (𝓞 F) F))) ∧ ∃ (M : ℕ) (i : pullback s (spMap (algebraMap (𝓞 F) F)) ⟶ PSpace F M), IsClosedImmersion i ∧ i ≫ PSpace.str F M = pullback.snd _ _ := by
  intro F _ _ P s hs hn
  have hp : IsProjOver (pullback.snd s (spMap (algebraMap (𝓞 F) F))) :=
    GlobalTheory.ProjSpace.isProjOver_pullback_snd _ hs
  have hb : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (R := CommRingCat.of (𝓞 F)) (S := F) (nonZeroDivisors (𝓞 F))
  have hbf : Flat (spMap (algebraMap (𝓞 F) F)) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat F (nonZeroDivisors (𝓞 F)))
  have h1 : IsPreimmersion (pullback.fst s (spMap (algebraMap (𝓞 F) F))) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hb
  have hiso := GlobalTheory.isIso_stalkMap_of_flat_of_surjectiveOnStalks (pullback.fst s (spMap (algebraMap (𝓞 F) F)))
  have := GlobalTheory.SchemeWords.isProper_of_isProjOver hp
  refine ⟨?_, LocallyOfFiniteType.isLocallyNoetherian (pullback.snd s (spMap (algebraMap (𝓞 F) F))), hp⟩
  have : ∀ x, _root_.IsReduced ((pullback s (spMap (algebraMap (𝓞 F) F))).presheaf.stalk x) := fun x => by
    have := hiso x
    have i := (asIso ((pullback.fst s (spMap (algebraMap (𝓞 F) F))).stalkMap x)).commRingCatIsoToRingEquiv
    obtain ⟨_, _⟩ := hn (pullback.fst s (spMap (algebraMap (𝓞 F) F)) x)
    exact isReduced_of_injective i.symm i.symm.injective
  exact isReduced_of_isReduced_stalk _

end GlobalTheory.CompanionTheory.Ar.SncBase
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFibreProjectiveEmbeddingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_fibre_projective_embedding : ∀ (F : Type) [Field F] [NumberField F] (P : Scheme.{0}) (s : P ⟶ Sp (𝓞 F)), IsProjOver s → Tor.IsNormalScheme P → IsReduced (pullback s (spMap (algebraMap (𝓞 F) F))) ∧ IsLocallyNoetherian (pullback s (spMap (algebraMap (𝓞 F) F))) ∧ ∃ (M : ℕ) (i : pullback s (spMap (algebraMap (𝓞 F) F)) ⟶ PSpace F M), IsClosedImmersion i ∧ i ≫ PSpace.str F M = pullback.snd _ _ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.genericFibre_reduced_noetherian_closed | exact GlobalTheory.CompanionTheory.Ar.SncBase.genericFibre_reduced_noetherian_closed | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.genericFibre_reduced_noetherian_closed <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsResolutionGenericFibre
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsResolutionGenericFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.GenRes

theorem genericFibre_closed {O K : Type} [CommRing O] [Field K] (β : O →+* K)
    (hinj : Function.Injective β) (hfr : ∀ x : K, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a)
    (P : Scheme.{0}) (s : P ⟶ Sp O) (hs : IsProjOver s) (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme P) :
    IsReduced (pullback s (spMap β)) ∧ IsLocallyNoetherian (pullback s (spMap β)) ∧
      ∃ (M : ℕ) (i : pullback s (spMap β) ⟶ PSpace K M), IsClosedImmersion i ∧
        i ≫ PSpace.str K M = pullback.snd s (spMap β) := by
  letI : Algebra O K := β.toAlgebra
  haveI : IsDomain O := hinj.isDomain β
  haveI : IsFractionRing O K :=
    { map_units := fun y => by
        have hy : β y.1 ≠ 0 := fun h => nonZeroDivisors.ne_zero y.2 (hinj (by rw [h, map_zero]))
        exact (IsUnit.mk0 _ hy)
      surj := fun z => by
        obtain ⟨a, b, hb, h⟩ := hfr z
        have hb0 : b ≠ 0 := fun h0 => hb (by rw [h0, map_zero])
        exact ⟨⟨a, ⟨b, mem_nonZeroDivisors_of_ne_zero hb0⟩⟩, h⟩
      exists_of_eq := fun {x y} h => ⟨1, by rw [hinj h]⟩ }
  have hp : IsProjOver (pullback.snd s (spMap β)) := GlobalTheory.ProjSpace.isProjOver_pullback_snd _ hs
  have hb : IsPreimmersion (spMap β) :=
    IsPreimmersion.of_isLocalization (R := CommRingCat.of O) (S := K) (nonZeroDivisors O)
  have hbf : Flat (spMap β) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors O))
  have h1 : IsPreimmersion (pullback.fst s (spMap β)) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hb
  have hiso := GlobalTheory.isIso_stalkMap_of_flat_of_surjectiveOnStalks (pullback.fst s (spMap β))
  have := GlobalTheory.SchemeWords.isProper_of_isProjOver hp
  refine ⟨?_, LocallyOfFiniteType.isLocallyNoetherian (pullback.snd s (spMap β)), hp⟩
  have : ∀ x, _root_.IsReduced ((pullback s (spMap β)).presheaf.stalk x) := fun x => by
    have := hiso x
    have i := (asIso ((pullback.fst s (spMap β)).stalkMap x)).commRingCatIsoToRingEquiv
    obtain ⟨_, _⟩ := hn (pullback.fst s (spMap β) x)
    exact isReduced_of_injective i.symm i.symm.injective
  exact isReduced_of_isReduced_stalk _

theorem isProper_of_closed {K : Type} [Field K] {M r : ℕ} {X X' : Scheme.{0}} (i : X ⟶ PSpace K M)
    [IsClosedImmersion i] (j : X' ⟶ pullback (PSpace.str K M) (PSpace.str K r)) [IsClosedImmersion j]
    (f : X' ⟶ X) (h : f ≫ i = j ≫ pullback.fst _ _) : IsProper f ∧ IsProper (f ≫ i ≫ PSpace.str K M) := by
  have := isProper_str K M
  have := isProper_str K r
  have hfst : IsProper (pullback.fst (PSpace.str K M) (PSpace.str K r)) :=
    MorphismProperty.of_isPullback (P := @IsProper) (IsPullback.of_hasPullback _ _).flip inferInstance
  have hfi : IsProper (f ≫ i) := by rw [h]; infer_instance
  have hf : IsProper f := IsProper.of_comp f i
  refine ⟨hf, ?_⟩
  rw [← Category.assoc]
  infer_instance

end GlobalTheory.CompanionTheory.Ar.Flat.GenRes

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_resolution_genericFibre : Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → IsLocallyNoetherian (pullback Y.s (spMap β)) ∧ ∃ (X' : Scheme.{0}) (f : X' ⟶ pullback Y.s (spMap β)) (d : ℕ) (W' : X'.Opens) (jW : W'.toScheme ⟶ Xo.XF c), IsIso jW ∧ jW ≫ Y.jQ = W'.ι ≫ f ∧ IsProper f ∧ IsProper (f ≫ pullback.snd Y.s (spMap β)) ∧ SmoothOfRelativeDimension d (f ≫ pullback.snd Y.s (spMap β)) ∧ Geo.ResK.HasSncCoords (f ≫ pullback.snd Y.s (spMap β)) d (W' : Set X')ᶜ := by
  rintro hRes E _ _ _ H D l Xo c O _ β Y ⟨hinj, -, hfr⟩
  obtain ⟨hred, hln, M, i, hi, his⟩ := GenRes.genericFibre_closed β hinj hfr Y.X Y.s Y.proj Y.normal
  refine ⟨hln, ?_⟩
  have := Y.jQ_open
  let U : (pullback Y.s (spMap β)).Opens := Y.jQ.opensRange
  have hd : Dense (U : Set (pullback Y.s (spMap β) : Scheme.{0})) := by
    have : (U : Set (pullback Y.s (spMap β) : Scheme.{0})) = Set.range Y.jQ := Scheme.Hom.coe_opensRange _
    rw [this]; exact Y.jQ_dense
  have hιe : Y.jQ.isoOpensRange.inv ≫ Y.jQ = U.ι := by
    rw [Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι]
  have hXF : SmoothOfRelativeDimension D.dim
      (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := by
    have := Xo.smooth
    have := smoothOfRelativeDimension_isStableUnderBaseChange D.dim
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension D.dim)
      (IsPullback.of_hasPullback _ _) Xo.smooth
  have hU : SmoothOfRelativeDimension D.dim (U.ι ≫ pullback.snd Y.s (spMap β)) := by
    rw [← hιe, Category.assoc, Y.jQ_over]
    have := smoothOfRelativeDimension_isStableUnderBaseChange D.dim
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension D.dim)
      (IsPullback.of_horiz_isIso ⟨by simp⟩ :
        IsPullback Y.jQ.isoOpensRange.inv (Y.jQ.isoOpensRange.inv ≫ pullback.snd _ _) (pullback.snd _ _) (𝟙 _)) hXF
  have hin : Geo.ResK.IsResInput M i U D.dim := ⟨hi, hred, hd, by rw [his]; exact hU⟩
  haveI : CharZero c.F := inferInstance
  obtain ⟨r, X', j, f, hj, hfj, hsm, hiso, hdense, hsnc⟩ := hRes c.F M D.dim _ i U hin
  obtain ⟨hp1, hp2⟩ := GenRes.isProper_of_closed i j f hfj
  rw [his] at hp2 hsm hsnc
  refine ⟨X', f, D.dim, f ⁻¹ᵁ U, (f ∣_ U) ≫ Y.jQ.isoOpensRange.inv, inferInstance, ?_, hp1, hp2, hsm, hsnc⟩
  rw [Category.assoc, hιe, morphismRestrict_ι]

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsResolutionGenericFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_resolution_generic_fibre : Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → IsLocallyNoetherian (pullback Y.s (spMap β)) ∧ ∃ (X' : Scheme.{0}) (f : X' ⟶ pullback Y.s (spMap β)) (d : ℕ) (W' : X'.Opens) (jW : W'.toScheme ⟶ Xo.XF c), IsIso jW ∧ jW ≫ Y.jQ = W'.ι ≫ f ∧ IsProper f ∧ IsProper (f ≫ pullback.snd Y.s (spMap β)) ∧ SmoothOfRelativeDimension d (f ≫ pullback.snd Y.s (spMap β)) ∧ Geo.ResK.HasSncCoords (f ≫ pullback.snd Y.s (spMap β)) d (W' : Set X')ᶜ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_resolution_genericFibre | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_resolution_genericFibre | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_resolution_genericFibre <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModelOverBase
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModelOverBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ProjModel

open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem sec_ext (hg : IsCptGen ξ) (hall : ∀ q : X, genPt ξ ⤳ q) {W : X.Opens} {s t : Γ(X, W)}
    (h : ∀ hW : genPt ξ ∈ W, CoordBase.val (ξ := ξ) W hW s = CoordBase.val (ξ := ξ) W hW t) : s = t := by
  refine TopCat.Presheaf.section_ext X.sheaf W s t fun p hp => ?_
  have hW : genPt ξ ∈ W := (hall p).mem_open W.isOpen hp
  refine hg.inj ⟨p, hall p⟩ ?_
  exact (CoordBase.genMap_germ_val W hW ⟨p, hall p⟩ hp s).trans
    ((h hW).trans (CoordBase.genMap_germ_val W hW ⟨p, hall p⟩ hp t).symm)

theorem val_resG {U V : X.Opens} (h : V ≤ U) (hV : genPt ξ ∈ V) (s : Γ(X, U)) :
    CoordBase.val (ξ := ξ) V hV (resG X h s) = CoordBase.val (ξ := ξ) U (h hV) s := by
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ_res_apply (homOfLE h).op.unop _ hV s)

theorem exists_charts {κ : Type} {x : κ → Ω} (hT : CoordTie ℤ ξ x) (hall : ∀ q : X, genPt ξ ⤳ q) :
    ∃ U : κ → X.Opens, (∀ c, IsAffineOpen (U c)) ∧ ∀ c q, q ∈ U c ↔ InChart ξ x c ⟨q, hall q⟩ := by
  have : ∀ c, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ q, q ∈ U ↔ InChart ξ x c ⟨q, hall q⟩ := by
    intro c
    by_cases hc : x c = 0
    · exact ⟨⊥, isAffineOpen_bot X, fun q => ⟨fun h => h.elim, fun h => (h.1 hc).elim⟩⟩
    · obtain ⟨U, hU, hm⟩ := hT.affine c hc
      exact ⟨U, hU, fun q => (hm q).trans ⟨fun ⟨_, h⟩ => h, fun h => ⟨hall q, h⟩⟩⟩
  choose U hU using this
  exact ⟨U, fun c => (hU c).1, fun c => (hU c).2⟩

theorem eval₂Hom_surjective {A J : Type} [CommRing A] (b : ℤ →+* A) (ρ : J → A) (v : A →+* Ω)
    (hv : Function.Injective v) (y : J → Ω) (hρ : ∀ j, v (ρ j) = y j)
    (hA : ∀ a, v a ∈ Algebra.adjoin ℤ (Set.range y)) :
    Function.Surjective (MvPolynomial.eval₂Hom b ρ) := by
  intro g
  have hg := hA g
  rw [Algebra.adjoin_range_eq_range_aeval] at hg
  obtain ⟨P, hP⟩ := hg
  refine ⟨P, hv ?_⟩
  have key : v.comp (MvPolynomial.eval₂Hom b ρ) =
      (MvPolynomial.aeval y : MvPolynomial J ℤ →ₐ[ℤ] Ω).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · simp
    · simp [hρ]
  exact (congrArg (fun φ : MvPolynomial J ℤ →+* Ω => φ P) key).trans hP

theorem isProjOver_of_coordTie {N : ℕ} {x : Fin (N + 1) → Ω} (hT : CoordTie ℤ ξ x)
    (hall : ∀ q : X, genPt ξ ⤳ q) (s : X ⟶ Sp ℤ) : IsProjOver s := by
  classical
  obtain ⟨U, hU, hm⟩ := exists_charts hT hall
  have hmem : ∀ c q, q ∈ U c ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c ⟨q, h⟩ := fun c q =>
    (hm c q).trans ⟨fun h => ⟨hall q, h⟩, fun ⟨_, h⟩ => h⟩
  have hgen : ∀ c, genPt ξ ∈ U c → x c ≠ 0 := fun c h => ((hm c _).1 h).1
  have hr : ∀ c j, ∃ b : Γ(X, U c), ∀ hW : genPt ξ ∈ U c,
      CoordBase.val (ξ := ξ) (U c) hW b = x j / x c := by
    intro c j
    by_cases hW : genPt ξ ∈ U c
    · obtain ⟨b, hb⟩ := (CoordBase.mem_adjoin_iff hT (hgen c hW) (hU c) (hmem c) hW (x j / x c)).1
        (Algebra.subset_adjoin ⟨j, rfl⟩)
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun h => (hW h).elim⟩
  choose r hr using hr
  have H : IsCoordFamily U r :=
    { cover := by
        rw [eq_top_iff]
        intro q _
        obtain ⟨c, hc⟩ := hT.cover ⟨q, hall q⟩
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨c, (hm c q).2 hc⟩
      self := fun i => sec_ext hT.gen hall fun hW => by
        rw [hr, map_one, div_self (hgen i hW)]
      mul := fun i j k => sec_ext hT.gen hall fun hW => by
        have hi := hgen i hW.1
        have hj := hgen j hW.2
        rw [map_mul, val_resG, val_resG, val_resG, hr, hr, hr]
        field_simp
      basicOpen_le := fun i j p hp => by
        have hpi : p ∈ U i := X.basicOpen_le _ hp
        obtain ⟨u, hu⟩ : IsUnit (X.presheaf.germ (U i) p hpi (r i j)) :=
          (X.mem_basicOpen _ p hpi).1 hp
        have hW : genPt ξ ∈ U i := (hall p).mem_open (U i).isOpen hpi
        have hxi := hgen i hW
        have hv : genMap ξ ⟨p, hall p⟩ (u : X.presheaf.stalk p) = x j / x i := by
          rw [hu]
          exact (CoordBase.genMap_germ_val (U i) hW ⟨p, hall p⟩ hpi _).trans (hr _ _ _)
        have hinv : (x j / x i) * genMap ξ ⟨p, hall p⟩ ((u⁻¹ : (X.presheaf.stalk p)ˣ) : X.presheaf.stalk p) = 1 := by
          rw [← hv, ← map_mul, Units.mul_inv, map_one]
        have hxj : x j ≠ 0 := by
          intro h
          rw [h, zero_div, zero_mul] at hinv
          exact zero_ne_one hinv
        have hi := (hm i p).1 hpi
        refine (hm j p).2 ⟨hxj, fun c' => ?_⟩
        have e : x c' / x j = (x c' / x i) *
            genMap ξ ⟨p, hall p⟩ ((u⁻¹ : (X.presheaf.stalk p)ˣ) : X.presheaf.stalk p) := by
          have e' : genMap ξ ⟨p, hall p⟩ ((u⁻¹ : (X.presheaf.stalk p)ˣ) : X.presheaf.stalk p) = x i / x j := by
            field_simp at hinv ⊢
            linear_combination hinv
          rw [e']
          field_simp
        rw [e]
        exact (regAt ξ _).mul_mem (hi.2 c') ⟨_, rfl⟩ }
  refine ⟨N, H.toHom s, ?_, H.toHom_str s⟩
  refine (isClosedImmersion_iff_pullRatio (H.toHom s) (H.toHom_preimage s)).2 fun i => ⟨hU i, ?_⟩
  have hρ : pullRatio (H.toHom s) (U i) i (H.toHom_preimage s i).ge = r i :=
    funext (H.pullRatio_toHom s i)
  rw [hρ]
  by_cases hW : genPt ξ ∈ U i
  · refine eval₂Hom_surjective _ _ (CoordBase.val (ξ := ξ) (U i) hW) ?_ (fun j => x j / x i) (hr i · hW) ?_
    · intro a a' e
      exact sec_ext hT.gen hall fun _ => e
    · intro a
      exact (CoordBase.mem_adjoin_iff hT (hgen i hW) (hU i) (hmem i) hW _).2 ⟨a, rfl⟩
  · exact fun g => ⟨0, sec_ext hT.gen hall fun h => (hW h).elim⟩

theorem isProjOver_pModel {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel ℤ x) : IsProjOver M.s := by
  obtain ⟨N, x', h⟩ := coordTie_int_of_finite M.X Ω M.ξ ℤ κ x M.tie
  exact isProjOver_of_coordTie h M.all M.s

theorem isProjOver_of_map {O : Type} [CommRing O] {Z : Scheme.{0}} {s : Z ⟶ Sp ℤ} (h : IsProjOver s)
    (g : Z ⟶ Sp O) : IsProjOver g := by
  have hp := isProjOver_pullback_snd (Int.castRingHom O) h
  let σ : Z ⟶ pullback s (spMap (Int.castRingHom O)) :=
    pullback.lift (𝟙 Z) g (specZIsTerminal.hom_ext _ _)
  have hσ : IsClosedImmersion σ := by
    have : IsClosedImmersion (σ ≫ pullback.fst s (spMap (Int.castRingHom O))) := by
      rw [pullback.lift_fst]
      infer_instance
    exact .of_comp σ (pullback.fst s (spMap (Int.castRingHom O)))
  have := isProjOver_comp_of_isClosedImmersion σ hp
  rwa [pullback.lift_snd] at this

theorem isProjOver_comp_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω]
    (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel ℤ x) (f : M.X ⟶ Y.X), IsProjOver (f ≫ Y.s) :=
  fun _ _ _ _ _ _ _ _ _ Y _ _ _ _ _ M f => isProjOver_of_map (isProjOver_pModel M) (f ≫ Y.s)

end GlobalTheory.CompanionTheory.Ar.ProjModel
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModelOverBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_model_over_base : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel ℤ x) (f : M.X ⟶ Y.X), IsProjOver (f ≫ Y.s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ProjModel.isProjOver_comp_model | exact GlobalTheory.CompanionTheory.Ar.ProjModel.isProjOver_comp_model | (intros; apply GlobalTheory.CompanionTheory.Ar.ProjModel.isProjOver_comp_model <;> assumption)
end
end
