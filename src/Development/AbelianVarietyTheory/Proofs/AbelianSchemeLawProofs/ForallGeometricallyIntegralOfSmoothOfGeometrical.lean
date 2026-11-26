module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlatOfFormallyUnramifiedGrpEnd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
public import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem forall_geometricallyIntegral_of_smooth_of_geometricallyConnected :
    ∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f →
      GeometricallyIntegral f :=
  fun _ _ f _ _ ↦ geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres f

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem isRegularLocalRing_atPrime_of_etale' (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.Etale R S] (q : Ideal S) [q.IsPrime]
    (h : IsRegularLocalRing (Localization.AtPrime (q.under R))) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  have hlo : q.LiesOver (q.under R) := ⟨rfl⟩
  let _ := Localization.AtPrime.algebraOfLiesOver (q.under R) q
  have hmax : (q.under R).map (algebraMap R (Localization.AtPrime q)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q) :=
    ((Algebra.isUnramifiedAt_iff_map_eq R (q.under R) q).mp inferInstance).2
  have hsf : (IsLocalRing.maximalIdeal (Localization.AtPrime q)).spanFinrank ≤
      (IsLocalRing.maximalIdeal (Localization.AtPrime (q.under R))).spanFinrank := by
    have heq : IsLocalRing.maximalIdeal (Localization.AtPrime q) =
        (IsLocalRing.maximalIdeal (Localization.AtPrime (q.under R))).map
          (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q)) := by
      rw [← hmax, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
        ← IsScalarTower.algebraMap_eq]
    rw [heq]
    exact Ideal.spanFinrank_map_le_of_fg _ (IsLocalRing.maximalIdeal _).fg_of_isNoetherianRing
  have hht : (q.under R).height ≤ q.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (q.under R) q]
    exact le_self_add
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  calc ((IsLocalRing.maximalIdeal (Localization.AtPrime q)).spanFinrank : WithBot ℕ∞)
      ≤ ((IsLocalRing.maximalIdeal (Localization.AtPrime (q.under R))).spanFinrank : WithBot ℕ∞) := by
        exact_mod_cast hsf
    _ = ringKrullDim (Localization.AtPrime (q.under R)) := h.spanFinrank_maximalIdeal
    _ = ((q.under R).height : WithBot ℕ∞) :=
        IsLocalization.AtPrime.ringKrullDim_eq_height (q.under R) _
    _ ≤ (q.height : WithBot ℕ∞) := by exact_mod_cast hht
    _ = ringKrullDim (Localization.AtPrime q) :=
        (IsLocalization.AtPrime.ringKrullDim_eq_height q _).symm

theorem isRegularRing_of_etale (R S : Type*) [CommRing R] [IsRegularRing R] [CommRing S]
    [Algebra R S] [Algebra.Etale R S] : IsRegularRing S := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  exact isRegularRing_iff.mpr fun q _ => isRegularLocalRing_atPrime_of_etale' R S q inferInstance

theorem isRegularRing_of_smooth :
    ∀ (V B : Type) [CommRing V] [IsRegularRing V] [CommRing B] [Algebra V B] [Algebra.Smooth V B],
      IsRegularRing B := by
  intro V B _ _ _ _ _
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing V B
  refine isRegularRing_iff.mpr fun Q _ => ?_
  obtain ⟨f, hf, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := V) (p := Q)
  have hT : IsRegularRing (Localization.Away f) :=
    isRegularRing_of_etale (MvPolynomial (Fin n) V) (Localization.Away f)
  have disj : Disjoint (Submonoid.powers f : Set B) (Q : Set B) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hf
  let Q' := Q.map (algebraMap B (Localization.Away f))
  have : Q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (.powers f) _ _ ‹_› disj
  have : IsLocalization.AtPrime (Localization.AtPrime Q') Q := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (.powers f)
      (Localization.AtPrime Q') Q'
    exact (IsLocalization.under_map_of_isPrime_disjoint (.powers f) _ ‹_› disj).symm
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv Q.primeCompl
    (Localization.AtPrime Q') (Localization.AtPrime Q)).toRingEquiv

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatAndSurjectiveOfIsFiniteAbelianEnd
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace FiniteEndFlat

theorem strictMono_of_locallyQuasiFinite {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyQuasiFinite f] :
    StrictMono (f : X → Y) := by
  intro x y hxy
  have h : y ⤳ x := hxy.le
  refine lt_of_le_not_ge (show f y ⤳ f x from h.map f.continuous) fun h' => hxy.not_ge ?_
  have e : f y = f x := ((h.map f.continuous).antisymm h').eq
  have hd := (f.isDiscrete_preimage_singleton (f x)).to_subtype
  have h2 : (⟨y, e⟩ : f ⁻¹' {f x}) ⤳ ⟨x, rfl⟩ := (subtype_specializes_iff _ _).mpr h
  have : y = x := congrArg Subtype.val h2.eq
  exact this.le

theorem apply_genericPoint {X : Scheme.{0}} [IrreducibleSpace X] [IsLocallyNoetherian X]
    (f : X ⟶ X) [LocallyQuasiFinite f] {o : X} (ho : f o = o) :
    f (genericPoint X) = genericPoint X := by
  have hs := strictMono_of_locallyQuasiFinite f
  let g : Set.Ici o → Set.Ici o := fun x =>
    ⟨f x, ho.ge.trans (show f x ⤳ f o from Specializes.map (show x.1 ⤳ o from x.2) f.continuous)⟩
  have hg : StrictMono g := fun x y h => hs h
  let ξ : Set.Ici o := ⟨genericPoint X, genericPoint_specializes o⟩
  have hfin : Order.height (g ξ) < ⊤ := by
    have h1 := Order.height_le_krullDim (g ξ)
    rw [← Order.coheight_eq_krullDim_Ici, ← ringKrullDim_stalk_eq_coheight] at h1
    have h2 := h1.trans_lt ringKrullDim_lt_top
    exact WithBot.coe_lt_coe.mp h2
  have hle : g ξ ≤ ξ := genericPoint_specializes (f (genericPoint X))
  have hge : ξ ≤ g ξ := by
    by_contra h
    exact (Order.height_strictMono (lt_of_le_not_ge hle h) hfin).not_ge
      (Order.height_le_height_apply_of_strictMono g hg ξ)
  exact (Specializes.antisymm (show f (genericPoint X) ⤳ genericPoint X from hge)
    (genericPoint_specializes _)).eq

theorem exists_flat_away {A B : Type} [CommRing A] [CommRing B] [IsDomain A] [IsNoetherianRing A]
    (φ : A →+* B) (hφ : φ.Finite) :
    ∃ r : A, r ≠ 0 ∧ ∀ (C : Type) [CommRing C] [Algebra B C] [IsLocalization.Away (φ r) C],
      ((algebraMap B C).comp φ).Flat := by
  algebraize [φ]
  have : Module.FinitePresentation A B := Module.finitePresentation_of_finite A B
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (nonZeroDivisors A) (LocalizedModule.mkLinearMap (nonZeroDivisors A) B) (FractionRing A)
  refine ⟨r, nonZeroDivisors.ne_zero hr, fun C _ _ _ => ?_⟩
  letI : Algebra A C := ((algebraMap B C).comp φ).toAlgebra
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers r)) C := by
    rw [Algebra.algebraMapSubmonoid_powers]; assumption
  have h1 : Module.Flat A (LocalizedModule (Submonoid.powers r) B) :=
    Module.Flat.trans A (Localization (Submonoid.powers r)) _
  exact Module.Flat.of_linearEquiv
    (IsLocalizedModule.iso (Submonoid.powers r) (IsScalarTower.toAlgHom A B C).toLinearMap).symm

open UnramifiedEndFlat in
theorem exists_open_flat {X Y : Scheme.{0}} [IrreducibleSpace X] [IsIntegral Y]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsFinite f]
    (hf : f (genericPoint X) = genericPoint Y) :
    ∃ W : X.Opens, (W : Set X).Nonempty ∧ ∀ x ∈ W, (f.stalkMap x).hom.Flat := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hξ, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint Y)) isOpen_univ
  have : Nonempty U := ⟨⟨_, hξ⟩⟩
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨r, hr, H⟩ := exists_flat_away (f.app U).hom (f.finite_app U hU)
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  refine ⟨X.basicOpen (f.app U r), ⟨genericPoint X, ?_⟩, fun x hx => ?_⟩
  · rw [← Scheme.preimage_basicOpen, SetLike.mem_coe, Scheme.Hom.mem_preimage, hf]
    refine ((genericPoint_spec Y).mem_open_set_iff (Y.basicOpen r).2).mpr ?_
    rw [Set.univ_inter]
    exact (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp (by simpa using hr)
  · have := hV.isLocalization_basicOpen (f.app U r)
    have h1 := H Γ(X, X.basicOpen (f.app U r))
    have hxU : x ∈ f ⁻¹ᵁ U := X.basicOpen_le _ hx
    have h2 : (X.presheaf.germ _ x hx).hom.Flat := by
      rw [← Category.comp_id (X.presheaf.germ _ x hx), ← flat_iff_comp_germ (hV.basicOpen _)]
      exact RingHom.Flat.id _
    rw [flat_iff_comp_germ hU (x := f x) hxU, f.germ_stalkMap U x hxU,
      ← X.presheaf.germ_res (homOfLE (X.basicOpen_le (f.app U r))) x hx]
    exact h1.comp h2

end FiniteEndFlat

open UnramifiedEndFlat FiniteEndFlat in
theorem flat_and_surjective_of_isFinite_grpEnd (K : Type) [Field K] [IsAlgClosed K]
    (G : Over (Spec (CommRingCat.of K))) [GrpObj G] [IsIntegral G.left]
    [LocallyOfFiniteType G.hom] (φ : G ⟶ G) [IsMonHom φ] [IsFinite φ.left] :
    Flat φ.left ∧ Surjective φ.left := by
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  let o : G.left := η[G].left (IsLocalRing.closedPoint K)
  have hfo : φ.left o = o := by
    have : η[G] ≫ φ = η[G] := IsMonHom.one_hom φ
    exact congr(($this).left (IsLocalRing.closedPoint K))
  have hξ := apply_genericPoint φ.left hfo
  refine ⟨?_, ⟨fun y => ?_⟩⟩
  · obtain ⟨W, hW, H⟩ := exists_open_flat φ.left hξ
    obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints hW W.2.isLocallyClosed
    refine flat_of_closedPoints _ fun x hx => ?_
    let x' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨x, hx⟩).2
    let y' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨y, hyc⟩).2
    let α := GrpObj.mulRight (A := G) (y'⁻¹ * x')
    let β := GrpObj.mulRight (A := G) ((y'⁻¹ * x') ≫ φ)
    have hαβ : α.hom ≫ φ = φ ≫ β.hom := by
      simp only [α, β]
      generalize y'⁻¹ * x' = z
      simp [comp_lift_assoc]
    have hα : y' ≫ α.hom = x' := by
      have : y' ≫ α.hom = y' * (y'⁻¹ * x') := by
        simp [α, comp_lift_assoc, Hom.mul_def]
      rw [this, mul_inv_cancel_left]
    have hα' : α.hom.left y = x := by
      have h := congr(($hα).left (IsLocalRing.closedPoint K))
      rw [← pointOfClosedPoint_apply G.hom x hx (IsLocalRing.closedPoint K),
        ← pointOfClosedPoint_apply G.hom y hyc (IsLocalRing.closedPoint K)]
      exact h
    have : IsIso α.hom.left := inferInstanceAs (IsIso ((Over.forget _).map α.hom))
    have : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map β.hom))
    have h1 : ((φ.left ≫ β.hom.left).stalkMap y).hom.Flat := by
      rw [Scheme.Hom.stalkMap_comp]
      exact (Flat.stalkMap β.hom.left _).comp (H y hy)
    rw [← Over.comp_left, ← hαβ, Over.comp_left, Scheme.Hom.stalkMap_comp] at h1
    rw [← hα']
    exact (RingHom.Flat.respectsIso.cancel_right_isIso
      (φ.left.stalkMap (α.hom.left y)) (α.hom.left.stalkMap y)).mp h1
  · exact (genericPoint_specializes y).mem_closed φ.left.isClosedMap.isClosed_range ⟨_, hξ⟩

theorem flat_and_surjective_of_isFinite_abelianEnd :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S),
      Smooth f → GeometricallyConnected f → GeometricallyIntegral f) →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A],
      IsAbelianScheme A → ∀ f : A ⟶ A, IsMonHom f → IsFinite f.left →
        Flat f.left ∧ Surjective f.left := by
  intro h K _ _ A _ hA f _ _
  have := hA.smooth
  have := h _ _ A.hom hA.smooth hA.geomConnected
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  exact flat_and_surjective_of_isFinite_grpEnd K A f

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulAFiniteFlatSurjectiveEtale
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

open scoped CategoryTheory.Obj

namespace GlobalTheory.AbLaw.MulN

theorem isMonHom_mulA {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    IsMonHom (mulA A n) := by
  induction n with
  | zero =>
    change IsMonHom (𝟙 A ^ 0)
    rw [pow_zero]
    exact inferInstanceAs (IsMonHom (toUnit A ≫ η[A]))
  | succ n ih =>
    change IsMonHom (𝟙 A ^ (n + 1))
    rw [pow_succ]
    exact inferInstanceAs (IsMonHom (lift (mulA A n) (𝟙 A) ≫ μ[A]))

theorem isPullback_baseChange {S T : Scheme.{0}} (t : T ⟶ S) {X Y : Over S} (f : X ⟶ Y) :
    IsPullback (pullback.fst X.hom t) ((Over.pullback t).map f).left f.left
      (pullback.fst Y.hom t) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd Y.hom t) (v₂₂ := Y.hom) (h₃₁ := t) ?_ ?_
    (IsPullback.of_hasPullback Y.hom t)
  · have h1 : ((Over.pullback t).map f).left ≫ pullback.snd Y.hom t = pullback.snd X.hom t :=
      pullback.lift_snd _ _ _
    rw [h1, Over.w f]
    exact IsPullback.of_hasPullback X.hom t
  · exact (pullback.lift_fst _ _ _).symm

theorem surjective_of_geomFibres {S : Scheme.{0}} {X Y : Over S} (f : X ⟶ Y)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      Surjective ((Over.pullback t).map f).left) : Surjective f.left := by
  refine ⟨fun y => ?_⟩
  let K := AlgebraicClosure (Y.left.residueField y)
  let u : Spec (CommRingCat.of K) ⟶ Y.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.left.residueField y) K)) ≫
      Y.left.fromSpecResidueField y
  let t := u ≫ Y.hom
  have hs := h K t
  let p : Spec (CommRingCat.of K) := (⊥ : PrimeSpectrum K)
  let v : Spec (CommRingCat.of K) ⟶ pullback Y.hom t := pullback.lift u (𝟙 _) (by simp [t])
  obtain ⟨x, hx⟩ := ((Over.pullback t).map f).left.surjective (v p)
  refine ⟨pullback.fst X.hom t x, ?_⟩
  have e := (isPullback_baseChange t f).w
  have e1 : f.left (pullback.fst X.hom t x) =
      pullback.fst Y.hom t (((Over.pullback t).map f).left x) := by
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
  rw [e1, hx, ← Scheme.Hom.comp_apply]
  have : v ≫ pullback.fst Y.hom t = u := pullback.lift_fst _ _ _
  rw [this]
  exact (Scheme.Hom.comp_apply _ _ p).trans (Scheme.fromSpecResidueField_apply y _)

theorem mulA_finite_flat_surjective_etale :
    (∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left) → (∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A], IsAbelianScheme A → ∀ f : A ⟶ A, IsMonHom f → IsFinite f.left → Flat f.left ∧ Surjective f.left) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (X Y : Over S) (f : X ⟶ Y), Flat X.hom → LocallyOfFiniteType Y.hom → IsFinite f.left → (∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S), Flat ((Over.pullback t).map f).left) → Flat f.left) → (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ), IsUnit (n : Γ(S, ⊤)) → FormallyUnramified (mulA G n).left) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left) := by
  intro hfin hK hfib hunr S _ P n hn
  have hc := P.isAb.comm
  have hsm := P.isAb.smooth
  have hf := hfin S P n hn
  have hm := isMonHom_mulA P.A n
  have hgeo : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      Flat ((Over.pullback t).map (mulA P.A n)).left ∧
        Surjective ((Over.pullback t).map (mulA P.A n)).left := fun K _ _ t =>
    hK K _ (TLinPf.isAb_pullback t P.A P.isAb) _ inferInstance
      (MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_baseChange t _) hf)
  have hflat : Flat (mulA P.A n).left :=
    hfib S _ _ _ inferInstance inferInstance hf fun K _ _ t => (hgeo K t).1
  refine ⟨hf, hflat, surjective_of_geomFibres _ fun K _ _ t => (hgeo K t).2, fun hu => ?_⟩
  have := hunr S P.A n hu
  have : IsLocallyNoetherian P.A.left := LocallyOfFiniteType.isLocallyNoetherian P.A.hom
  exact Etale.of_formallyUnramified_of_flat _

end GlobalTheory.AbLaw.MulN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfIsDiscreteValuationRing
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExtendRig

theorem isRegularRing_of_isLocalization {B : Type} [CommRing B] [IsRegularRing B]
    (M : Submonoid B) (R : Type) [CommRing R] [Algebra B R] [IsLocalization M R] :
    IsRegularRing R := by
  have : IsNoetherianRing R := IsLocalization.isNoetherianRing M R inferInstance
  rw [isRegularRing_iff]
  intro q hq
  have h : IsLocalization.AtPrime (Localization.AtPrime q) (q.comap (algebraMap B R)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime q) q
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (q.comap (algebraMap B R)).primeCompl
      (Localization.AtPrime (q.comap (algebraMap B R))) (Localization.AtPrime q)).toRingEquiv

theorem isRegularRing_of_isDiscreteValuationRing (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] : IsRegularRing V :=
  have : IsDedekindDomain V := IsPrincipalIdealRing.isDedekindDomain V
  inferInstance

theorem isLocalization_away_of_irreducible (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K]
    {π : V} (hπ : Irreducible π) : IsLocalization.Away π K := by
  refine (IsLocalization.iff_of_le_of_exists_dvd (M := Submonoid.powers π) (S := K)
    (nonZeroDivisors V) (powers_le_nonZeroDivisors_of_noZeroDivisors hπ.ne_zero) ?_).mpr
    inferInstance
  intro a ha
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
    (nonZeroDivisors.ne_zero ha) hπ
  exact ⟨π ^ n, ⟨n, rfl⟩, hn.dvd⟩

theorem isOpenImmersion_etaK (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] :
    IsOpenImmersion (etaK V K) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have := isLocalization_away_of_irreducible V K hπ
  exact IsOpenImmersion.of_isLocalization π

theorem isRegularRing_stalk
    (hreg : ∀ (V B : Type) [CommRing V] [IsRegularRing V] [CommRing B] [Algebra V B]
      [Algebra.Smooth V B], IsRegularRing B)
    (V : Type) [CommRing V] [IsRegularRing V] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of V))
    [Smooth f] (x : X) : IsRegularRing (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hs : (f.appLE ⊤ U le_top).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have : IsRegularRing Γ(Spec (CommRingCat.of V), ⊤) :=
    IsRegularRing.of_ringEquiv
      (Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.symm
  algebraize [(f.appLE ⊤ U le_top).hom]
  have : IsRegularRing Γ(X, U) := hreg Γ(Spec (CommRingCat.of V), ⊤) Γ(X, U)
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  exact isRegularRing_of_isLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl _

theorem extend_exists :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f) → (∀ (V B : Type) [CommRing V] [IsRegularRing V] [CommRing B] [Algebra V B] [Algebra.Smooth V B], IsRegularRing B) → (∀ (R : Type) [CommRing R] [IsRegularRing R] [IsLocalRing R] [IsDomain R], UniqueFactorizationMonoid R) → (∀ (X Y : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X] (j : Y ⟶ X), IsOpenImmersion j → (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∀ L : LB Y, L.IsLB → ∃ L' : LB X, L'.IsLB ∧ ∃ φ : LB.Iso (L'.pull j) L, φ.IsGen) → Semi.extend_existsSt.{0} := by
  intro hint hreg hufd hext V _ _ _ K _ _ _ G _ _ _ _ _ _ eA _ L hL _ _
  have hV : IsRegularRing V := isRegularRing_of_isDiscreteValuationRing V
  have : GeometricallyIntegral G.hom := hint _ _ _ inferInstance inferInstance
  have : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian G.hom
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have := isOpenImmersion_etaK V K
  have hj : IsOpenImmersion (jA V K G) := inferInstance
  have hst : ∀ x : G.left, UniqueFactorizationMonoid (G.left.presheaf.stalk x) := fun x =>
    have := isRegularRing_stalk hreg V G.hom x
    hufd _
  obtain ⟨L', hL', φ, hφ⟩ := hext G.left _ (jA V K G) hj hst L hL
  obtain ⟨e, he⟩ := DVR.exists_gen_of_local (V := V) L' hL' (K := PUnit)
    (fun _ => eSec G) (fun _ => 1)
  exact ⟨⟨L', e, hL', he⟩, φ, hφ⟩

end GlobalTheory.ExtendRig
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FormallyUnramifiedMulInvertibleInteger
section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FormallyUnramifiedMulInvertibleInteger
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem formallyUnramified_mulA (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ)
    (hn : IsUnit (n : Γ(S, ⊤))) : FormallyUnramified (mulA G n).left := by
  have h : mulN G n = mulA G n :=
    (Category.id_comp _).symm.trans (MulUnramified.comp_mulN G (𝟙 G) n)
  rw [← h]
  exact formallyUnramified_mulN S G n hn

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FormallyUnramifiedMulInvertibleIntegerStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.formallyUnramified_mul_invertible_integer : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ), IsUnit (n : Γ(S, ⊤)) → FormallyUnramified (mulA G n).left := by
  first | exact @GlobalTheory.formallyUnramified_mulA | exact GlobalTheory.formallyUnramified_mulA | (intros; apply GlobalTheory.formallyUnramified_mulA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.UniqueFactorizationMonoidOfIsRegularRingOfIsLoca
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace RegularFactorial

open IsLocalRing

end RegularFactorial

attribute [local instance] Over.cartesianMonoidalCategory in
open IsLocalRing in
private lemma prime_of_mem_maximalIdeal_of_not_mem_sq {A : Type} [CommRing A] [IsRegularLocalRing A]
    {x : A} (hx : x ∈ maximalIdeal A) (hx2 : x ∉ maximalIdeal A ^ 2) : Prime x := by
  have hx0 : x ≠ 0 := by rintro rfl; exact hx2 (Ideal.zero_mem _)
  haveI := _root_.ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.quotient_span_singleton hx hx2
  haveI : IsDomain (A ⧸ Ideal.span {x}) := _root_.ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain _
  rw [← Ideal.span_singleton_prime hx0]
  exact (Ideal.Quotient.isDomain_iff_prime _).1 inferInstance

attribute [local instance] Over.cartesianMonoidalCategory in
private lemma isPrincipal_of_isPrincipal_map_away_prime {A : Type} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] {x : A} (hx : Prime x) {p : Ideal A} [hp : p.IsPrime] (hxp : x ∉ p)
    (h : (p.map (algebraMap A (Localization.Away x))).IsPrincipal) : p.IsPrincipal := by
  obtain ⟨f, hf⟩ := h
  have hfmem : f ∈ p.map (algebraMap A (Localization.Away x)) := by
    rw [hf]; exact Submodule.mem_span_singleton_self f
  obtain ⟨⟨a, m⟩, ham⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers x) (Localization.Away x)).1 hfmem
  have hx0 : x ≠ 0 := hx.ne_zero
  have hinj : Function.Injective (algebraMap A (Localization.Away x)) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hx0)
  have hmul : ∀ y ∈ p, ∃ (s : ℕ) (c : A), x ^ s * y = (a : A) * c := by
    intro y hy
    have hy' : algebraMap A (Localization.Away x) y ∈ p.map (algebraMap A (Localization.Away x)) :=
      Ideal.mem_map_of_mem _ hy
    rw [hf] at hy'
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 hy'
    obtain ⟨⟨e, k⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers x) d
    obtain ⟨j, hj⟩ := k.2
    obtain ⟨i, hi⟩ := m.2
    refine ⟨j + i, e, hinj ?_⟩
    simp only [smul_eq_mul] at hd
    have h1 := IsLocalization.mk'_spec (Localization.Away x) e k
    dsimp only at ham hj hi
    rw [map_mul, map_mul, ← hd, ← ham, pow_add, map_mul, hj, hi, ← h1]
    ring
  by_cases ha0 : (a : A) = 0
  · refine ⟨0, le_antisymm (fun y hy => ?_) ?_⟩
    · obtain ⟨s, c, hsc⟩ := hmul y hy
      rw [ha0, zero_mul] at hsc
      have hy0 : y = 0 := (mul_eq_zero.1 hsc).resolve_left (pow_ne_zero _ hx0)
      rw [hy0]; exact Submodule.zero_mem _
    · rw [Submodule.span_le, Set.singleton_subset_iff]; exact p.zero_mem
  · obtain ⟨g, hag, hxg⟩ :=
      (FiniteMultiplicity.of_not_isUnit hx.not_unit ha0).exists_eq_pow_mul_and_not_dvd
    have hxr : x ^ multiplicity x (a : A) ∉ p := fun h => hxp (hp.mem_of_pow_mem _ h)
    have hg : g ∈ p := (hp.mem_or_mem (hag ▸ a.2)).resolve_left hxr
    refine ⟨g, le_antisymm (fun y hy => ?_) ?_⟩
    · obtain ⟨s, c, hsc⟩ := hmul y hy
      rw [hag] at hsc
      obtain ⟨c', hc'⟩ := hx.pow_dvd_of_dvd_mul_left s hxg
        (⟨y, by linear_combination -hsc⟩ : x ^ s ∣ g * (x ^ multiplicity x (a : A) * c))
      have hy : y = g * c' :=
        mul_left_cancel₀ (pow_ne_zero s hx0) (by linear_combination hsc + g * hc')
      rw [hy]
      exact Submodule.mem_span_singleton.2 ⟨c', by rw [smul_eq_mul, mul_comm]⟩
    · rw [Submodule.span_le, Set.singleton_subset_iff]; exact hg

attribute [local instance] Over.cartesianMonoidalCategory in
open IsLocalRing in
private lemma uniqueFactorizationMonoid_localization_of_height_le
    (hPD : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (M : Type) [AddCommGroup M] [Module R M]
      [Module.Finite R M], ∃ n : ℕ, HasProjectiveDimensionLE (ModuleCat.of R M) n)
    (hPrin : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R] (x : R)
      (R' : Type) [CommRing R'] [Algebra R R'] [IsLocalization.Away x R'] (I : Ideal R) (n : ℕ),
      HasProjectiveDimensionLE (ModuleCat.of R I) n →
      Module.Projective R' (I.map (algebraMap R R')) → (I.map (algebraMap R R')).IsPrincipal)
    {R : Type} [CommRing R] [IsRegularRing R] (n : ℕ) :
    ∀ (Q : Ideal R) [Q.IsPrime], Q.height ≤ n → UniqueFactorizationMonoid (Localization.AtPrime Q) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Q _ hQ
  rw [UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one]
  intro p _ hph
  by_cases hm : ∃ x ∈ maximalIdeal (Localization.AtPrime Q), x ∉ maximalIdeal (Localization.AtPrime Q) ^ 2
  · obtain ⟨x, hx, hx2⟩ := hm
    have hxp := prime_of_mem_maximalIdeal_of_not_mem_sq hx hx2
    by_cases hxmem : x ∈ p
    · exact ⟨x, Ideal.eq_span_singleton_of_height_eq_one hph hxmem hxp⟩
    · refine isPrincipal_of_isPrincipal_map_away_prime hxp hxmem ?_
      obtain ⟨N, hN⟩ := hPD (Localization.AtPrime Q) p
      refine hPrin _ x (Localization.Away x) p N hN ?_
      haveI : Module.FinitePresentation (Localization.Away x)
          (p.map (algebraMap (Localization.AtPrime Q) (Localization.Away x))) :=
        Module.finitePresentation_of_finite _ _
      refine Module.projective_of_localization_maximal (fun q hq => ?_)
      haveI := hq.isPrime
      haveI hloc₁ : IsLocalization.AtPrime (Localization.AtPrime q)
          (q.comap (algebraMap (Localization.AtPrime Q) (Localization.Away x))) :=
        IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (Submonoid.powers x) _ q
      set q₁ := q.comap (algebraMap (Localization.AtPrime Q) (Localization.Away x)) with hq₁
      haveI hloc₂ : IsLocalization.AtPrime (Localization.AtPrime q) (q₁.comap (algebraMap R (Localization.AtPrime Q))) :=
        IsLocalization.isLocalization_isLocalization_atPrime_isLocalization Q.primeCompl _ q₁
      set q₂ := q₁.comap (algebraMap R (Localization.AtPrime Q)) with hq₂
      have hxq₁ : x ∉ q₁ := fun h => hq.ne_top (Ideal.eq_top_of_isUnit_mem _ h
        (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away x) x))
      have hq₁m : q₁ ≤ maximalIdeal (Localization.AtPrime Q) :=
        IsLocalRing.le_maximalIdeal (Ideal.comap_ne_top _ hq.ne_top)
      have hq₂Q : q₂ < Q := by
        refine lt_of_le_of_ne ?_ ?_
        · rw [← IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime Q) Q]
          exact Ideal.comap_mono hq₁m
        · intro h
          apply hxq₁
          have := IsLocalization.map_under Q.primeCompl (Localization.AtPrime Q) q₁
          rw [← this]
          change x ∈ Ideal.map _ q₂
          rw [h, IsLocalization.AtPrime.map_eq_maximalIdeal]
          exact hx
      have hlt : q₂.height < n := lt_of_lt_of_le (Ideal.height_strict_mono_of_isPrime hq₂Q) hQ
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt hlt)
      have hmn : m < n := by rw [← hm] at hlt; exact_mod_cast hlt
      haveI := ih m hmn q₂ hm.symm.le
      haveI : UniqueFactorizationMonoid (Localization.AtPrime q) :=
        (IsLocalization.algEquiv q₂.primeCompl (Localization.AtPrime q₂)
          (Localization.AtPrime q)).toMulEquiv.uniqueFactorizationMonoid inferInstance
      haveI : IsDomain (Localization.AtPrime q) :=
        (IsLocalization.algEquiv q₂.primeCompl (Localization.AtPrime q₂)
          (Localization.AtPrime q)).toRingEquiv.symm.injective.isDomain _
      have hJ : (p.map (algebraMap (Localization.AtPrime Q) (Localization.Away x))).map
          (algebraMap (Localization.Away x) (Localization.AtPrime q)) =
          p.map (algebraMap (Localization.AtPrime Q) (Localization.AtPrime q)) := by
        rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
      have hJprin : (p.map (algebraMap (Localization.AtPrime Q) (Localization.AtPrime q))).IsPrincipal := by
        by_cases hdisj : p ≤ q₁
        · have hd : Disjoint (q₁.primeCompl : Set (Localization.AtPrime Q)) p :=
            Set.disjoint_left.2 fun a ha hap => ha (hdisj hap)
          haveI := IsLocalization.isPrime_of_isPrime_disjoint q₁.primeCompl (Localization.AtPrime q) p ‹_› hd
          exact UniqueFactorizationMonoid.isPrincipal_of_height_eq_one
            (by rw [IsLocalization.height_map_of_disjoint q₁.primeCompl p hd, hph])
        · obtain ⟨a, hap, haq⟩ := Set.not_subset.1 hdisj
          have htop : p.map (algebraMap (Localization.AtPrime Q) (Localization.AtPrime q)) = ⊤ :=
            Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hap)
              (IsLocalization.map_units (Localization.AtPrime q) (⟨a, haq⟩ : q₁.primeCompl))
          rw [htop]
          exact ⟨1, Ideal.span_singleton_one.symm⟩
      obtain ⟨g, hg⟩ := hJprin
      haveI : Module.Free (Localization.AtPrime q)
          (p.map (algebraMap (Localization.AtPrime Q) (Localization.AtPrime q))) := by
        by_cases hg0 : g = 0
        · have hbot : p.map (algebraMap (Localization.AtPrime Q) (Localization.AtPrime q)) = ⊥ := by
            rw [hg, hg0]; exact Submodule.span_singleton_eq_bot.2 rfl
          rw [hbot]; infer_instance
        · rw [hg]; exact Module.Free.of_equiv (LinearEquiv.toSpanNonzeroSingleton _ _ g hg0)
      have heq : Submodule.localized' (Localization.AtPrime q) q.primeCompl
          (Algebra.linearMap (Localization.Away x) (Localization.AtPrime q))
          (p.map (algebraMap (Localization.AtPrime Q) (Localization.Away x))) =
          p.map (algebraMap (Localization.AtPrime Q) (Localization.AtPrime q)) := by
        rw [Ideal.localized'_eq_map, hJ]
      exact Module.Projective.of_equiv (((IsLocalizedModule.iso q.primeCompl
        (Submodule.toLocalized' (Localization.AtPrime q) q.primeCompl
          (Algebra.linearMap (Localization.Away x) (Localization.AtPrime q))
          (p.map (algebraMap (Localization.AtPrime Q) (Localization.Away x))))).extendScalarsOfIsLocalization
        q.primeCompl (Localization.AtPrime q)).trans (LinearEquiv.ofEq _ _ heq)).symm
  · push_neg at hm
    have hbot := _root_.ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.maximalIdeal_eq_bot_of_le_sq (Localization.AtPrime Q) hm
    have hp : p = ⊥ := le_bot_iff.1 (hbot ▸ IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›))
    exact absurd hph (by rw [hp, Ideal.height_bot]; exact zero_ne_one)

attribute [local instance] Over.cartesianMonoidalCategory in
open IsLocalRing in
theorem _root_.GlobalTheory.uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing :
    (∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (M : Type) [AddCommGroup M] [Module R M]
      [Module.Finite R M], ∃ n : ℕ, HasProjectiveDimensionLE (ModuleCat.of R M) n) →
    (∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R] (x : R)
      (R' : Type) [CommRing R'] [Algebra R R'] [IsLocalization.Away x R'] (I : Ideal R) (n : ℕ),
      HasProjectiveDimensionLE (ModuleCat.of R I) n →
      Module.Projective R' (I.map (algebraMap R R')) → (I.map (algebraMap R R')).IsPrincipal) →
    ∀ (R : Type) [CommRing R] [IsRegularRing R] [IsLocalRing R] [IsDomain R],
      UniqueFactorizationMonoid R := by
  intro hPD hPrin R _ _ _ _
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (Ideal.height_ne_top (maximalIdeal.isMaximal R).ne_top)
  haveI := uniqueFactorizationMonoid_localization_of_height_le hPD hPrin n (maximalIdeal R) hn.symm.le
  exact (IsLocalization.atUnits R (maximalIdeal R).primeCompl
    (S := Localization.AtPrime (maximalIdeal R))
    (fun y hy => IsLocalRing.notMem_maximalIdeal.1 hy)).symm.toMulEquiv.uniqueFactorizationMonoid
    inferInstance

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsHasProjectiveDimensionLEOfResidueField
open CategoryTheory IsLocalRing

namespace GlobalTheory

universe u

theorem projectiveDimension_quotient_maximalIdeal_ne_top (R : Type u) [CommRing R]
    [IsRegularLocalRing R] :
    projectiveDimension (ModuleCat.of R (R ⧸ maximalIdeal R)) ≠ ⊤ := by
  obtain ⟨xs, h, hd⟩ := exists_ofList_eq_maximalIdeal_length_eq R
  have hreg := isRegular_of_ofList_eq_maximalIdeal h hd.le
  have key := ModuleCat.projectiveDimension_quotient_eq_length.{u} xs hreg
  rw [projectiveDimension_eq_of_iso (Shrink.linearEquiv R _).toModuleIso, h] at key
  rw [key]
  exact ne_of_beq_false rfl

theorem exists_hasProjectiveDimensionLE_of_residueField (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    (hk : projectiveDimension (ModuleCat.of R (R ⧸ maximalIdeal R)) ≠ ⊤)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ n : ℕ, HasProjectiveDimensionLE (ModuleCat.of R M) n := by
  suffices H : ∀ (I : Ideal R) (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N],
      I ≤ Module.annihilator R N → ∃ n : ℕ, HasProjectiveDimensionLE (ModuleCat.of R N) n from
    H ⊥ M bot_le
  intro I
  induction I using IsNoetherian.induction with
  | hgt I ih =>
  intro N _ _ hN
  induction hN using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R with
  | subsingleton N =>
    intro _
    have := (ModuleCat.isZero_of_subsingleton (ModuleCat.of R N)).hasProjectiveDimensionLT_zero
    exact ⟨0, hasProjectiveDimensionLT_of_ge _ 0 _ (Nat.zero_le _)⟩
  | quotient N p f =>
    intro hI
    rw [f.annihilator_eq, Ideal.annihilator_quotient] at hI
    rw [← projectiveDimension_ne_top_iff, projectiveDimension_eq_of_iso f.toModuleIso]
    by_cases hp : p.asIdeal = maximalIdeal R
    · rw [hp]
      exact hk
    have hlt : p.asIdeal < maximalIdeal R := lt_of_le_of_ne (le_maximalIdeal p.2.ne_top) hp
    obtain ⟨x, hx, hxp⟩ := SetLike.exists_of_lt hlt
    have hreg : IsSMulRegular (R ⧸ p.asIdeal) x := by
      intro a b hab
      have hx0 : Ideal.Quotient.mk p.asIdeal x ≠ 0 := by
        rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
      refine mul_left_cancel₀ hx0 ?_
      simpa only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq] using hab
    have hJ : I < p.asIdeal ⊔ Ideal.span {x} := by
      refine lt_of_le_of_lt hI (lt_of_le_of_ne le_sup_left fun e => hxp ?_)
      rw [e]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)
    have hq := ih _ hJ (QuotSMulTop x (R ⧸ p.asIdeal)) (sup_le
      (Ideal.annihilator_quotient.ge.trans
        (LinearMap.annihilator_le_of_surjective _ (Submodule.mkQ_surjective _)))
      ((Ideal.span_singleton_le_iff_mem _).mpr (QuotSMulTop.mem_annihilator _ x)))
    rw [← projectiveDimension_ne_top_iff] at hq
    have key := ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular
      (ModuleCat.of R (R ⧸ p.asIdeal)) x hreg hx
    intro htop
    apply hq
    rw [htop] at key
    exact key.trans rfl
  | exact N₁ N₂ N₃ f g hf hg hfg h₁ h₃ =>
    intro hI
    obtain ⟨a, ha⟩ := h₁ (hI.trans (f.annihilator_le_of_injective hf))
    obtain ⟨b, hb⟩ := h₃ (hI.trans (g.annihilator_le_of_surjective hg))
    have hS : (ModuleCat.shortComplexOfCompEqZero f g hfg.linearMap_comp_eq_zero).ShortExact :=
      ModuleCat.shortComplex_shortExact _ hfg hf hg
    exact ⟨a + b, hS.hasProjectiveDimensionLT_X₂ _
      (hasProjectiveDimensionLT_of_ge (ModuleCat.of R N₁) (a + 1) _ (by omega))
      (hasProjectiveDimensionLT_of_ge (ModuleCat.of R N₃) (b + 1) _ (by omega))⟩

theorem exists_hasProjectiveDimensionLE_of_isRegularLocalRing :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (M : Type) [AddCommGroup M] [Module R M]
      [Module.Finite R M], ∃ n : ℕ, HasProjectiveDimensionLE (ModuleCat.of R M) n :=
  fun R _ _ M _ _ _ => exists_hasProjectiveDimensionLE_of_residueField R
    (projectiveDimension_quotient_maximalIdeal_ne_top R) M

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsPrincipalMapAwayOfHasProjectiveDimensionLE
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open scoped TensorProduct

theorem nonempty_equiv_prod_of_exact_of_projective {A : Type*} [CommRing A] {K F M : Type*}
    [AddCommGroup K] [Module A K] [AddCommGroup F] [Module A F] [AddCommGroup M] [Module A M]
    [Module.Projective A M] (g : K →ₗ[A] F) (f : F →ₗ[A] M) (hg : Function.Injective g)
    (hf : Function.Surjective f) (h : Function.Exact g f) : Nonempty (F ≃ₗ[A] K × M) := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  exact ⟨(h.splitSurjectiveEquiv hg ⟨s, hs⟩).1⟩

theorem isStablyFree_baseChange_of_hasProjectiveDimensionLE (R : Type) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (A : Type) [CommRing A] [Algebra R A] [Module.Flat R A]
    (n : ℕ) : ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M],
      HasProjectiveDimensionLE (ModuleCat.of R M) n → Module.Projective A (A ⊗[R] M) →
        Module.IsStablyFree A (A ⊗[R] M) := by
  induction n with
  | zero =>
    intro M _ _ _ h _
    have h1 : Projective (ModuleCat.of R M) :=
      (projective_iff_hasProjectiveDimensionLE_zero _).2 h
    have h2 : Module.Projective R M := (IsProjective.iff_projective M).2 h1
    have h3 : Module.Free R M := Module.free_of_flat_of_isLocalRing
    infer_instance
  | succ n ih =>
    intro M _ _ _ h hp
    obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' R M
    have hS := LinearMap.shortExact_shortComplexKer hf
    have hK : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker f)) n := by
      have hP : Projective (ModuleCat.of R (Fin m → R)) := inferInstance
      exact (hS.hasProjectiveDimensionLT_X₃_iff n hP).1 h
    have hex : Function.Exact ((LinearMap.ker f).subtype.baseChange A) (f.baseChange A) :=
      lTensor_exact A f.exact_subtype_ker_map hf
    have hinj : Function.Injective ((LinearMap.ker f).subtype.baseChange A) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ (LinearMap.ker f).injective_subtype
    have hsurj : Function.Surjective (f.baseChange A) := LinearMap.lTensor_surjective A hf
    obtain ⟨e⟩ := nonempty_equiv_prod_of_exact_of_projective _ _ hinj hsurj hex
    have hfree : Module.Free A ((A ⊗[R] LinearMap.ker f) × (A ⊗[R] M)) := Module.Free.of_equiv e
    have hKp : Module.Projective A (A ⊗[R] LinearMap.ker f) :=
      Module.Projective.of_split (LinearMap.inl A _ (A ⊗[R] M)) (LinearMap.fst A _ _)
        (LinearMap.ext fun _ ↦ rfl)
    have hKs := ih (LinearMap.ker f) hK hKp
    obtain ⟨N, _, _, _, _, _⟩ := Module.IsStablyFree.exist_free_prod A (A ⊗[R] LinearMap.ker f)
    have : Module.Free A ((A ⊗[R] M) × ((A ⊗[R] LinearMap.ker f) × N)) :=
      Module.Free.of_equiv (M := ((A ⊗[R] LinearMap.ker f) × (A ⊗[R] M)) × N)
        (((LinearEquiv.prodComm A _ _).prodCongr (LinearEquiv.refl A N)).trans
          (LinearEquiv.prodAssoc A _ _ _))
    exact Module.IsStablyFree.of_free_prod A _ ((A ⊗[R] LinearMap.ker f) × N)

section cofactor

variable {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N] {n : ℕ}

theorem exists_surjective_exteriorPower_prod (bN : Module.Basis (Fin n) A N) :
    ∃ φ : ⋀[A]^(n + 1) (M × N) →ₗ[A] M, Function.Surjective φ := by
  let c : M × N →ₗ[A] (M × N) [⋀^Fin n]→ₗ[A] M :=
    { toFun := fun x ↦ (bN.det.compLinearMap (LinearMap.snd A M N)).smulRight x.1
      map_add' := fun x y ↦ AlternatingMap.ext fun _ ↦ by simp
      map_smul' := fun c x ↦ AlternatingMap.ext fun _ ↦ by simp [smul_smul, mul_comm] }
  refine ⟨exteriorPower.alternatingMapLinearEquiv (AlternatingMap.alternatizeUncurryFin c),
    fun m ↦ ⟨exteriorPower.ιMulti A (n + 1) (Fin.cons (m, 0) fun i ↦ (0, bN i)), ?_⟩⟩
  simp [c, AlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ, Module.Basis.det_self]

end cofactor

theorem isPrincipal_of_isStablyFree {A : Type} [CommRing A] (J : Ideal A) [Module.Finite A J]
    [Module.IsStablyFree A J] : J.IsPrincipal := by
  rcases subsingleton_or_nontrivial A with _ | _
  · rw [Subsingleton.elim J ⊥]
    exact bot_isPrincipal
  obtain ⟨N, _, _, _, _, _⟩ := Module.IsStablyFree.exist_free_prod A J
  let n := Module.finrank A N
  have hp : Module.finrank A (J × N) ≤ n + 1 := by
    have := LinearMap.finrank_le_finrank_of_injective
      (f := J.subtype.prodMap (LinearMap.id : N →ₗ[A] N))
      (Function.Injective.prodMap J.injective_subtype Function.injective_id)
    rwa [Module.finrank_prod (M := A), Module.finrank_self, add_comm] at this
  have h1 : Module.finrank A (⋀[A]^(n + 1) (J × N)) ≤ 1 := by
    rw [exteriorPower.finrank_eq]
    simpa using Nat.choose_le_choose (n + 1) hp
  obtain ⟨v, hv⟩ := finrank_le_one_iff.1 h1
  obtain ⟨φ, hφ⟩ := exists_surjective_exteriorPower_prod (M := J) (Module.finBasis A N)
  refine ⟨(φ v : A), le_antisymm (fun y hy ↦ ?_) ?_⟩
  · obtain ⟨w, hw⟩ := hφ ⟨y, hy⟩
    obtain ⟨c, rfl⟩ := hv w
    rw [map_smul] at hw
    exact Submodule.mem_span_singleton.2 ⟨c, congrArg Subtype.val hw⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    exact (φ v).2

theorem isPrincipal_map_away_of_hasProjectiveDimensionLE :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R] (x : R) (R' : Type) [CommRing R'] [Algebra R R'] [IsLocalization.Away x R'] (I : Ideal R) (n : ℕ), HasProjectiveDimensionLE (ModuleCat.of R I) n → Module.Projective R' (I.map (algebraMap R R')) → (I.map (algebraMap R R')).IsPrincipal := by
  intro R _ _ _ _ x R' _ _ _ I n h hp
  have hflat : Module.Flat R R' := IsLocalization.flat R' (Submonoid.powers x)
  have hb : IsBaseChange R' (Algebra.idealMap R' I) :=
    IsLocalizedModule.isBaseChange (Submonoid.powers x) R' _
  have hp' : Module.Projective R' (R' ⊗[R] I) := Module.Projective.of_equiv hb.equiv.symm
  have hs := isStablyFree_baseChange_of_hasProjectiveDimensionLE R R' n I h hp'
  have := Module.IsStablyFree.equiv hb.equiv
  have := Module.Finite.equiv hb.equiv
  exact isPrincipal_of_isStablyFree _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SmoothDense
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem smooth_smoothLocus_ι_comp {X Y : Scheme.{0}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] : Smooth (f.smoothLocus.ι ≫ f) := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
  simp

theorem smoothDense : SmoothDenseSt := by
  intro K _ _ X f hX hf
  have : LocallyOfFinitePresentation f := inferInstance
  exact f.dense_smoothLocus_of_perfectField.mono
    fun x hx => ⟨f.smoothLocus, hx, smooth_smoothLocus_ι_comp f⟩

end GlobalTheory
end
