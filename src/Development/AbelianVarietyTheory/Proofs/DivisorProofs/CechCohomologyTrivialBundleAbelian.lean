module

public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsRegularOfFnOfRingKrullDimQuotientAddLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeComplexMumfordBundleOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivAtZeroReindexEqTaylorCoefficient
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFinitenessAutomorphicGLOfEigen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOnMemGoodPart

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSubgroupSchemeIdealGeneratedByDimElements
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanMaximalIdealMapOfFlatRegular
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanMaximalIdealMapOfFlatRegular
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
open IsLocalRing

theorem maximalIdeal_map_span_of_flat_of_isArtinianRing_fibre :
    ∀ (O' O : Type) [CommRing O'] [IsRegularLocalRing O'] [CommRing O] [IsLocalRing O]
      [IsNoetherianRing O] (σ : O' →+* O), IsLocalHom σ → σ.Flat →
      IsArtinianRing (O ⧸ (IsLocalRing.maximalIdeal O').map σ) → ∀ g : ℕ, ringKrullDim O = g →
      ∃ f : Fin g → O, Ideal.span (Set.range f) = (IsLocalRing.maximalIdeal O').map σ := by
  intro O' O _ _ _ _ _ σ hloc hflat hart g hg
  letI := σ.toAlgebra
  haveI : Module.Flat O' O := hflat
  haveI : Algebra.HasGoingDown O' O := Algebra.HasGoingDown.of_flat
  haveI : IsLocalHom (algebraMap O' O) := hloc
  haveI : IsLocalHom σ := hloc
  set I : Ideal O := (maximalIdeal O').map σ with hI
  have hIle : I ≤ maximalIdeal O := IsLocalRing.map_maximalIdeal_le _
  haveI : Nontrivial (O ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal O).ne_top hIle)
  haveI : IsLocalRing (O ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hmap : (maximalIdeal O).map (Ideal.Quotient.mk I) = maximalIdeal (O ⧸ I) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hF : (maximalIdeal (O ⧸ I)).height = 0 := by
    rw [Ideal.height_eq_zero_iff]
    refine ⟨⟨inferInstance, bot_le⟩, fun q ⟨hq, _⟩ hle => ?_⟩
    exact ((IsArtinianRing.isMaximal_of_isPrime q).eq_of_le (maximalIdeal.isMaximal _).ne_top
      hle).ge
  have H := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal O') (maximalIdeal O)
  have hIalg : (maximalIdeal O').map (algebraMap O' O) = I := rfl
  rw [hIalg, hmap, hF, add_zero] at H
  have hdim : ((maximalIdeal O').spanFinrank : WithBot ℕ∞) = g := by
    rw [IsRegularLocalRing.spanFinrank_maximalIdeal, ← maximalIdeal_height_eq_ringKrullDim, ← H,
      maximalIdeal_height_eq_ringKrullDim, hg]
  have hg' : (maximalIdeal O').spanFinrank = g := by exact_mod_cast hdim
  have hfg : (maximalIdeal O').FG := IsNoetherian.noetherian _
  obtain ⟨t, htcard, htspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  rw [hg'] at htcard
  let u : Fin g → O' := fun i => (t.equivFin.symm (Fin.cast htcard.symm i) : O')
  have hu : Set.range u = (t : Set O') := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩; exact (t.equivFin.symm _).2
    · intro hx; exact ⟨Fin.cast htcard (t.equivFin ⟨x, hx⟩), by simp [u]⟩
  refine ⟨fun i => σ (u i), ?_⟩
  rw [hI, ← htspan, Ideal.map_span, ← hu, ← Set.range_comp]
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanMaximalIdealMapOfFlatRegularStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_span_maximalIdeal_map_of_flat_regular : ∀ (O' O : Type) [CommRing O'] [IsRegularLocalRing O'] [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (σ : O' →+* O), IsLocalHom σ → σ.Flat → IsArtinianRing (O ⧸ (IsLocalRing.maximalIdeal O').map σ) → ∀ g : ℕ, ringKrullDim O = g → ∃ f : Fin g → O, Ideal.span (Set.range f) = (IsLocalRing.maximalIdeal O').map σ := by
  first | exact @GlobalTheory.maximalIdeal_map_span_of_flat_of_isArtinianRing_fibre | exact GlobalTheory.maximalIdeal_map_span_of_flat_of_isArtinianRing_fibre | (intros; apply GlobalTheory.maximalIdeal_map_span_of_flat_of_isArtinianRing_fibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSubgroupSchemeIdealGeneratedByDimElements
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.FinSubGen

theorem pullback_lift_iff : ∀ (K : Type) [Field K] (A A' H : Over (Sp K)) [GrpObj A'] (j : H ⟶ A) (q : A ⟶ A'), IsPullback j (toUnit H) q η[A'] → ∀ (T : Scheme.{0}) (y' : T ⟶ A.left), (∃ y : T ⟶ H.left, y ≫ j.left = y') ↔ ∃ z : T ⟶ Sp K, z ≫ (η[A']).left = y' ≫ q.left := by
  intro K _ A A' H _ j q hpb T y'
  have h2 := hpb.map (Over.forget (Sp K))
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y ≫ (toUnit H).left, ?_⟩
    simp only [Category.assoc, ← Over.comp_left, hpb.w]
  · rintro ⟨z, hz⟩
    exact ⟨h2.lift y' z hz.symm, h2.lift_fst _ _ _⟩

theorem section_factor_iff : ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Sp K) (s : Sp K ⟶ X), s ≫ f = 𝟙 _ → ∀ x : X, x ∈ Set.range s.base → ∀ (R' : Type) [CommRing R'] (φ : X.presheaf.stalk x →+* R'), (∃ z : Sp R' ⟶ Sp K, z ≫ s = Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk x) ↔ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ≤ RingHom.ker φ := by
  intro K _ X f s hs x hx R' _ φ
  obtain ⟨p, rfl⟩ := hx
  obtain rfl : p = IsLocalRing.closedPoint (CommRingCat.of K) := Subsingleton.elim _ _
  set r := Scheme.stalkClosedPointTo s
  have hr : Spec.map r ≫ X.fromSpecStalk _ = s := Scheme.Spec_stalkClosedPointTo_fromSpecStalk s
  set c : K →+* X.presheaf.stalk (s.base (IsLocalRing.closedPoint (CommRingCat.of K))) :=
    (Spec.preimage (X.fromSpecStalk _ ≫ f)).hom with hcdef
  have hc : Spec.map (CommRingCat.ofHom c) = X.fromSpecStalk _ ≫ f := by simp [c]
  have hrc : ∀ t : K, r.hom (c t) = t := by
    have h1 : Spec.map (CommRingCat.ofHom c ≫ r) = Spec.map (𝟙 (CommRingCat.of K)) := by
      rw [Spec.map_comp, hc, ← Category.assoc, hr, hs, Spec.map_id]
    have h2 := Spec.map_injective h1
    intro t
    exact congrArg (fun u : CommRingCat.of K ⟶ CommRingCat.of K => u.hom t) h2
  have hm : ∀ a, a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (s.base (IsLocalRing.closedPoint (CommRingCat.of K)))) → r.hom a = 0 := by
    intro a ha
    by_contra h
    exact (IsLocalRing.mem_maximalIdeal _).mp ha (isUnit_of_map_unit r.hom a (isUnit_iff_ne_zero.mpr h))
  constructor
  · rintro ⟨z, hz⟩ a ha
    have hz2 : (z ≫ Spec.map r) ≫ X.fromSpecStalk _ = Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk _ := by
      rw [Category.assoc, hr]; exact hz
    have hz' := (cancel_mono _).mp hz2
    rw [← Spec.map_preimage z, ← Spec.map_comp] at hz'
    have h3 := Spec.map_injective hz'
    have h4 : φ a = (Spec.preimage z).hom (r.hom a) :=
      (congrArg (fun u : _ ⟶ CommRingCat.of R' => u.hom a) h3).symm
    rw [RingHom.mem_ker, h4, hm a ha, map_zero]
  · intro hφ
    refine ⟨Spec.map (CommRingCat.ofHom (φ.comp c)), ?_⟩
    have e1 : Spec.map (CommRingCat.ofHom (φ.comp c)) ≫ Spec.map r ≫ X.fromSpecStalk _ = Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk _ := by
      rw [← Category.assoc, ← Spec.map_comp]
      congr 2
      ext a
      show φ (c (r.hom a)) = φ a
      have hmem : c (r.hom a) - a ∈ IsLocalRing.maximalIdeal _ := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        have := hu.map r.hom
        rw [map_sub, hrc, sub_self] at this
        exact not_isUnit_zero this
      have := hφ hmem
      rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
      exact this
    rwa [hr] at e1

theorem stalk_regular_of_section : ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Sp K) [IsSeparated f] (g : ℕ), SmoothOfRelativeDimension g f → ∀ (s : Sp K ⟶ X), s ≫ f = 𝟙 _ → ∀ x : X, x ∈ Set.range s.base → IsNoetherianRing (X.presheaf.stalk x) ∧ IsRegularLocalRing (X.presheaf.stalk x) ∧ ringKrullDim (X.presheaf.stalk x) = g := by
  intro K _ X f _ g hg s hs x hx
  have hci : IsClosedImmersion s := isClosedImmersion_of_comp_eq_id f s hs
  have hcl : IsClosed ({x} : Set X) := by
    have e : Set.range s.base = {x} := by
      obtain ⟨p, rfl⟩ := hx
      ext y
      constructor
      · rintro ⟨p', rfl⟩
        rw [Subsingleton.elim p' p]
        rfl
      · rintro rfl
        exact ⟨p, rfl⟩
    rw [← e]
    exact s.isClosedEmbedding.isClosed_range
  set σ : K →+* X.presheaf.stalk x := (Spec.preimage (X.fromSpecStalk x ≫ f)).hom with hσdef
  have hσ : X.fromSpecStalk x ≫ f = Spec.map (CommRingCat.ofHom σ) := by
    simp [σ]
  haveI : IsLocalHom σ := ⟨fun a ha => isUnit_iff_ne_zero.mpr (by rintro rfl; simp at ha)⟩
  obtain ⟨h1, -, h3, h4⟩ := GlobalTheory.StabFlat.stalk_of_smooth_local K X f g hg x hcl σ hσ inferInstance
  have hb : (IsLocalRing.maximalIdeal K).map σ = ⊥ := by
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.map_bot]
  let e : (X.presheaf.stalk x ⧸ (IsLocalRing.maximalIdeal K).map σ) ≃+* X.presheaf.stalk x :=
    (Ideal.quotEquivOfEq hb).trans (RingEquiv.quotientBot _)
  exact ⟨h1, IsRegularLocalRing.of_ringEquiv e, (ringKrullDim_eq_of_ringEquiv e).symm.trans h4⟩

theorem ideal_eq_span_fin : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (H : Over (Sp K)) [GrpObj H] (j : H ⟶ A), IsMonHom j → IsClosedImmersion j.left → IsFinite H.hom → ∀ x₀ : A.left, x₀ ∈ Set.range (η[A]).left.base → ∀ J : Ideal (A.left.presheaf.stalk x₀), (∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'), (∃ y : Sp R' ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) ↔ J ≤ RingHom.ker ψ) → ∃ f : Fin g → A.left.presheaf.stalk x₀, Ideal.span (Set.range f) = J := by
  intro K _ _ A _ g hA hg H _ j hj hci hfin x₀ hx₀ J hJ
  have hmono : Mono j := Over.mono_of_mono_left j
  obtain ⟨A', _, hA', q, hq, hqfin, hqflat, hqsurj, hpb⟩ := GlobalTheory.T.exists_quotient_abelianVariety_finite_subgroupScheme K A hA H j hj hmono hfin
  have hη : η[A] ≫ q = η[A'] := IsMonHom.one_hom q
  have hsA : (η[A]).left ≫ A.hom = 𝟙 _ := Over.w η[A]
  have hsA' : (η[A']).left ≫ A'.hom = 𝟙 _ := Over.w η[A']
  obtain ⟨p, hp⟩ := hx₀
  have hx' : q.left.base x₀ ∈ Set.range (η[A']).left.base := ⟨p, by
    rw [← hp, ← hη]; rfl⟩
  have hAs := hA.smooth
  have hAp := hA.proper
  have hA's := hA'.smooth
  have hA'p := hA'.proper
  have hA'c := hA'.geomConnected
  have : ConnectedSpace A'.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := A'.hom) (𝟙 _) (𝟙 _) A'.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨n, hn⟩ := exists_dim_of_preconnected A'.hom (q.left.base x₀)
  have Lreg : IsRegularLocalRing (A'.left.presheaf.stalk (q.left.base x₀)) :=
    (stalk_regular_of_section K A'.left A'.hom n hn _ hsA' _ hx').2.1
  have Ldim := stalk_regular_of_section K A.left A.hom g hg _ hsA x₀ ⟨p, hp⟩
  set σ := (q.left.stalkMap x₀).hom
  have key : ∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'), J ≤ RingHom.ker ψ ↔ (IsLocalRing.maximalIdeal (A'.left.presheaf.stalk (q.left.base x₀))).map σ ≤ RingHom.ker ψ := by
    intro R' _ ψ
    rw [← hJ, pullback_lift_iff K A A' H j q hpb, Ideal.map_le_iff_le_comap, RingHom.comap_ker,
      ← section_factor_iff K A'.left A'.hom _ hsA' _ hx' R' (ψ.comp σ)]
    have e : Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀ ≫ q.left =
        Spec.map (CommRingCat.ofHom (ψ.comp σ)) ≫ A'.left.fromSpecStalk (q.left.base x₀) := by
      rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, ← Spec.map_comp]
      rfl
    simp only [Category.assoc, e]
  have Lgeo : J = (IsLocalRing.maximalIdeal (A'.left.presheaf.stalk (q.left.base x₀))).map σ := by
    apply le_antisymm
    · simpa using (key _ (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (A'.left.presheaf.stalk (q.left.base x₀))).map σ))).2 (by simp)
    · simpa using (key _ (Ideal.Quotient.mk J)).1 (by simp)
  obtain ⟨_, hart⟩ := GlobalTheory.T.closed_subfunctor_stalk_ideal_criterion K A H j hj hci hfin x₀ ⟨p, hp⟩ J hJ
  have hflat : σ.Flat := Flat.stalkMap q.left x₀
  haveI := Ldim.1
  rw [Lgeo] at hart ⊢
  exact GlobalTheory.T.exists_span_maximalIdeal_map_of_flat_regular _ _ σ inferInstance hflat hart g Ldim.2.2

end GlobalTheory.FinSubGen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSubgroupSchemeIdealGeneratedByDimElementsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteSubgroupScheme_ideal_generated_by_dim_elements : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (H : Over (Sp K)) [GrpObj H] (j : H ⟶ A), IsMonHom j → IsClosedImmersion j.left → IsFinite H.hom → ∀ x₀ : A.left, x₀ ∈ Set.range (η[A]).left.base → ∀ J : Ideal (A.left.presheaf.stalk x₀), (∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'), (∃ y : Sp R' ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) ↔ J ≤ RingHom.ker ψ) → ∃ f : Fin g → A.left.presheaf.stalk x₀, Ideal.span (Set.range f) = J := by
  first | exact @GlobalTheory.FinSubGen.ideal_eq_span_fin | exact GlobalTheory.FinSubGen.ideal_eq_span_fin | (intros; apply GlobalTheory.FinSubGen.ideal_eq_span_fin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHomologyOneTwoDualResolution
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KoszulResolutionThreeTermsExact
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeaklyRegularRelationsEqKoszulRelations
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeaklyRegularRelationsEqKoszulRelations
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open RingTheory.Sequence in
theorem weaklyRegular_relations_koszul :
    ∀ (O : Type) [CommRing O] (g : ℕ) (f : Fin g → O), RingTheory.Sequence.IsWeaklyRegular O (List.ofFn f) → ∀ a : Fin g → O, ∑ i, a i * f i = 0 → ∃ c : Matrix (Fin g) (Fin g) O, (∀ i, c i i = 0) ∧ (∀ i j, c i j = - c j i) ∧ a = c.mulVec f := by
  intro O _ g
  induction g with
  | zero =>
    intro f _ a _
    exact ⟨0, by simp, by simp, funext fun i => i.elim0⟩
  | succ g ih =>
    intro f hf a ha
    have hsplit : List.ofFn f =
        List.ofFn (fun i : Fin g => f i.castSucc) ++ [f (Fin.last g)] := by
      rw [List.ofFn_succ_last]
    rw [hsplit, isWeaklyRegular_append_iff, isWeaklyRegular_singleton_iff] at hf
    obtain ⟨hf1, hf2⟩ := hf
    rw [Fin.sum_univ_castSucc] at ha
    have hIt : (Ideal.ofList (List.ofFn fun i : Fin g => f i.castSucc) • ⊤ : Submodule O O) =
        Ideal.ofList (List.ofFn fun i : Fin g => f i.castSucc) := by
      rw [smul_eq_mul, Ideal.mul_top]
    have hmem : a (Fin.last g) ∈
        (Ideal.ofList (List.ofFn fun i : Fin g => f i.castSucc) • ⊤ : Submodule O O) := by
      rw [← Submodule.Quotient.mk_eq_zero]
      apply hf2
      simp only [smul_zero]
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hIt, smul_eq_mul, mul_comm,
        eq_neg_of_add_eq_zero_right ha, neg_mem_iff]
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    rw [hIt, Ideal.ofList, show {r | r ∈ List.ofFn fun i : Fin g => f i.castSucc}
        = Set.range (fun i : Fin g => f i.castSucc) by ext; simp [List.mem_ofFn],
      Ideal.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨b, hb⟩ := hmem
    obtain ⟨c', hc0, hcs, hca⟩ := ih (fun i => f i.castSucc) hf1
      (fun i => a i.castSucc + b i * f (Fin.last g)) (by
        simp only [add_mul, Finset.sum_add_distrib]
        rw [← ha, ← hb, Finset.sum_mul, add_right_inj]
        exact Finset.sum_congr rfl fun i _ => by ring)
    refine ⟨fun i j => Fin.lastCases (Fin.lastCases 0 (fun j => b j) j)
      (fun i => Fin.lastCases (-b i) (fun j => c' i j) j) i, ?_, ?_, ?_⟩
    · intro i
      cases i using Fin.lastCases with
      | last => simp
      | cast i => simp [hc0]
    · intro i j
      cases i using Fin.lastCases <;> cases j using Fin.lastCases <;> simp <;> exact hcs _ _
    · funext i
      cases i using Fin.lastCases with
      | last => simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hb]
      | cast i =>
        have := congrFun hca i
        simp only [Matrix.mulVec, dotProduct] at this
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.lastCases_castSucc,
          Fin.lastCases_last]
        rw [← this]
        ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeaklyRegularRelationsEqKoszulRelationsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weaklyRegular_relations_eq_koszulRelations : ∀ (O : Type) [CommRing O] (g : ℕ) (f : Fin g → O), RingTheory.Sequence.IsWeaklyRegular O (List.ofFn f) → ∀ a : Fin g → O, ∑ i, a i * f i = 0 → ∃ c : Matrix (Fin g) (Fin g) O, (∀ i, c i i = 0) ∧ (∀ i j, c i j = - c j i) ∧ a = c.mulVec f := by
  first | exact @GlobalTheory.weaklyRegular_relations_koszul | exact GlobalTheory.weaklyRegular_relations_koszul | (intros; apply GlobalTheory.weaklyRegular_relations_koszul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KoszulResolutionThreeTermsExact
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Koszul

noncomputable def pairEquiv (g : ℕ) : {z : Sym2 (Fin g) // ¬ z.IsDiag} ≃ Fin (g.choose 2) :=
  Fintype.equivFinOfCardEq (by rw [Sym2.card_subtype_not_diag, Fintype.card_fin])

variable {O : Type} [CommRing O] {g : ℕ}

noncomputable def upper (x : Fin (g.choose 2) → O) : Matrix (Fin g) (Fin g) O :=
  fun i j => if h : i < j then
    x (pairEquiv g ⟨s(i, j), by rw [Sym2.mk_isDiag_iff]; exact h.ne⟩) else 0

noncomputable def skew (x : Fin (g.choose 2) → O) : Matrix (Fin g) (Fin g) O :=
  fun i j => upper x i j - upper x j i

lemma upper_add (x x' : Fin (g.choose 2) → O) : upper (x + x') = upper x + upper x' := by
  ext i j; simp only [upper, Matrix.add_apply]; split_ifs <;> simp

lemma upper_smul (a : O) (x : Fin (g.choose 2) → O) : upper (a • x) = a • upper x := by
  ext i j; simp only [upper, Matrix.smul_apply]; split_ifs <;> simp

lemma skew_add (x x' : Fin (g.choose 2) → O) : skew (x + x') = skew x + skew x' := by
  ext i j; simp only [skew, upper_add, Matrix.add_apply]; ring

lemma skew_smul (a : O) (x : Fin (g.choose 2) → O) : skew (a • x) = a • skew x := by
  ext i j; simp only [skew, upper_smul, Matrix.smul_apply, smul_eq_mul]; ring

noncomputable def d₂ (f : Fin g → O) : (Fin (g.choose 2) → O) →ₗ[O] (Fin g → O) where
  toFun x := (skew x).mulVec f
  map_add' x x' := by rw [skew_add, Matrix.add_mulVec]
  map_smul' a x := by
    rw [skew_smul]; ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

lemma d₂_apply (f : Fin g → O) (x : Fin (g.choose 2) → O) : d₂ f x = (skew x).mulVec f := rfl

lemma sum_skew_mulVec (f : Fin g → O) (x : Fin (g.choose 2) → O) :
    ∑ i, (skew x).mulVec f i * f i = 0 := by
  simp only [Matrix.mulVec, dotProduct, skew, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [sub_eq_zero, Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma exists_skew_eq (c : Matrix (Fin g) (Fin g) O) (hd : ∀ i, c i i = 0)
    (hs : ∀ i j, c i j = - c j i) : ∃ x : Fin (g.choose 2) → O, skew x = c := by
  let F : Sym2 (Fin g) → O :=
    Sym2.lift ⟨fun i j => c (min i j) (max i j), fun i j => show c (min i j) (max i j) = c (min j i) (max j i) by rw [min_comm, max_comm]⟩
  refine ⟨fun k => F ((pairEquiv g).symm k).1, ?_⟩
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · simp [skew, upper, h, lt_asymm h, F, min_eq_left h.le, max_eq_right h.le]
  · simp [skew, upper, hd]
  · simp [skew, upper, h, lt_asymm h, F, min_eq_left h.le, max_eq_right h.le, ← hs i j]

end GlobalTheory.Koszul


open GlobalTheory.Koszul in
theorem GlobalTheory.koszul_resolution_three_terms : ∀ (O : Type) [CommRing O] (g : ℕ) (f : Fin g → O), RingTheory.Sequence.IsWeaklyRegular O (List.ofFn f) → ∃ (e₁ : (Fin g → O) →ₗ[O] O) (e₂ : (Fin (g.choose 2) → O) →ₗ[O] (Fin g → O)), Function.Exact e₁ (Ideal.span (Set.range f)).mkQ ∧ Function.Exact e₂ e₁ ∧ (∀ x, e₁ x ∈ Ideal.span (Set.range f)) ∧ ∀ x i, e₂ x i ∈ Ideal.span (Set.range f) := by
  intro O _ g f hreg
  refine ⟨Fintype.linearCombination O f, d₂ f, ?_, ?_, ?_, ?_⟩
  · rw [LinearMap.exact_iff, Submodule.ker_mkQ, Fintype.range_linearCombination]
  · intro y
    constructor
    · intro hy
      rw [Fintype.linearCombination_apply] at hy
      obtain ⟨c, hd, hs, rfl⟩ := GlobalTheory.T.weaklyRegular_relations_eq_koszulRelations O g f hreg y (by simpa [smul_eq_mul] using hy)
      obtain ⟨x, hx⟩ := exists_skew_eq c hd hs
      exact ⟨x, by rw [d₂_apply, hx]⟩
    · rintro ⟨x, rfl⟩
      rw [Fintype.linearCombination_apply, d₂_apply]
      simpa [smul_eq_mul] using sum_skew_mulVec f x
  · intro x
    show _ ∈ Submodule.span O (Set.range f)
    rw [← Fintype.range_linearCombination]
    exact LinearMap.mem_range_self _ x
  · intro x i
    rw [d₂_apply]
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self j))
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KoszulResolutionThreeTermsExactStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.koszul_resolution_three_terms_exact : ∀ (O : Type) [CommRing O] (g : ℕ) (f : Fin g → O), RingTheory.Sequence.IsWeaklyRegular O (List.ofFn f) → ∃ (e₁ : (Fin g → O) →ₗ[O] O) (e₂ : (Fin (g.choose 2) → O) →ₗ[O] (Fin g → O)), Function.Exact e₁ (Ideal.span (Set.range f)).mkQ ∧ Function.Exact e₂ e₁ ∧ (∀ x, e₁ x ∈ Ideal.span (Set.range f)) ∧ ∀ x i, e₂ x i ∈ Ideal.span (Set.range f) := by
  first | exact @GlobalTheory.koszul_resolution_three_terms | exact GlobalTheory.koszul_resolution_three_terms | (intros; apply GlobalTheory.koszul_resolution_three_terms <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHomologyResolutionsResidueField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFreeResolutionsHomotopyEquivalent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFreeResolutionsHomotopyEquivalent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem resolution_lift_of_exact {O : Type} [CommRing O] {P A B C : Type}
    [AddCommGroup P] [Module O P] [Module.Projective O P]
    [AddCommGroup A] [Module O A] [AddCommGroup B] [Module O B] [AddCommGroup C] [Module O C]
    {u : A →ₗ[O] B} {v : B →ₗ[O] C} (huv : Function.Exact u v) (w : P →ₗ[O] B)
    (hw : v ∘ₗ w = 0) : ∃ l : P →ₗ[O] A, u ∘ₗ l = w := by
  have hr : ∀ x, w x ∈ LinearMap.range u := fun x => by
    rw [← LinearMap.exact_iff.mp huv, LinearMap.mem_ker]
    exact LinearMap.congr_fun hw x
  obtain ⟨l, hl⟩ := Module.projective_lifting_property u.rangeRestrict (w.codRestrict _ hr)
    u.surjective_rangeRestrict
  refine ⟨l, ?_⟩
  ext x
  have := congrArg Subtype.val (LinearMap.congr_fun hl x)
  simpa using this

theorem resolutions_homotopy_equivalent : ∀ (O : Type) [CommRing O] (N : Type) [AddCommGroup N] [Module O N] (F₀ : Type) [AddCommGroup F₀] [Module O F₀] [Module.Free O F₀] [Module.Finite O F₀] (F₁ : Type) [AddCommGroup F₁] [Module O F₁] [Module.Free O F₁] [Module.Finite O F₁] (F₂ : Type) [AddCommGroup F₂] [Module O F₂] [Module.Free O F₂] [Module.Finite O F₂] (F₃ : Type) [AddCommGroup F₃] [Module O F₃] [Module.Free O F₃] [Module.Finite O F₃] (G₀ : Type) [AddCommGroup G₀] [Module O G₀] [Module.Free O G₀] [Module.Finite O G₀] (G₁ : Type) [AddCommGroup G₁] [Module O G₁] [Module.Free O G₁] [Module.Finite O G₁] (G₂ : Type) [AddCommGroup G₂] [Module O G₂] [Module.Free O G₂] [Module.Finite O G₂] (ε : F₀ →ₗ[O] N) (d₁ : F₁ →ₗ[O] F₀) (d₂ : F₂ →ₗ[O] F₁) (d₃ : F₃ →ₗ[O] F₂) (ν : G₀ →ₗ[O] N) (e₁ : G₁ →ₗ[O] G₀) (e₂ : G₂ →ₗ[O] G₁), Function.Surjective ε → Function.Exact d₁ ε → Function.Exact d₂ d₁ → Function.Exact d₃ d₂ → Function.Surjective ν → Function.Exact e₁ ν → Function.Exact e₂ e₁ → ∃ (a₀ : F₀ →ₗ[O] G₀) (a₁ : F₁ →ₗ[O] G₁) (a₂ : F₂ →ₗ[O] G₂) (b₀ : G₀ →ₗ[O] F₀) (b₁ : G₁ →ₗ[O] F₁) (b₂ : G₂ →ₗ[O] F₂) (h₀ : F₀ →ₗ[O] F₁) (h₁ : F₁ →ₗ[O] F₂) (h₂ : F₂ →ₗ[O] F₃) (k₀ : G₀ →ₗ[O] G₁) (k₁ : G₁ →ₗ[O] G₂), e₁ ∘ₗ a₁ = a₀ ∘ₗ d₁ ∧ e₂ ∘ₗ a₂ = a₁ ∘ₗ d₂ ∧ d₁ ∘ₗ b₁ = b₀ ∘ₗ e₁ ∧ d₂ ∘ₗ b₂ = b₁ ∘ₗ e₂ ∧ LinearMap.id - b₁ ∘ₗ a₁ = d₂ ∘ₗ h₁ + h₀ ∘ₗ d₁ ∧ LinearMap.id - b₂ ∘ₗ a₂ = d₃ ∘ₗ h₂ + h₁ ∘ₗ d₂ ∧ LinearMap.id - a₁ ∘ₗ b₁ = e₂ ∘ₗ k₁ + k₀ ∘ₗ e₁ := by
  intro O _ N _ _ F₀ _ _ _ _ F₁ _ _ _ _ F₂ _ _ _ _ F₃ _ _ _ _ G₀ _ _ _ _ G₁ _ _ _ _ G₂ _ _ _ _
    ε d₁ d₂ d₃ ν e₁ e₂ hε hd1 hd2 hd3 hν he1 he2
  obtain ⟨a₀, ha₀⟩ := Module.projective_lifting_property ν ε hν
  obtain ⟨b₀, hb₀⟩ := Module.projective_lifting_property ε ν hε
  have ha₀' : ∀ x, ν (a₀ x) = ε x := fun x => LinearMap.congr_fun ha₀ x
  have hb₀' : ∀ x, ε (b₀ x) = ν x := fun x => LinearMap.congr_fun hb₀ x
  obtain ⟨a₁, ha₁⟩ := resolution_lift_of_exact he1 (a₀ ∘ₗ d₁) (by
    ext x; simp [ha₀', Function.Exact.apply_apply_eq_zero hd1])
  have ha₁' : ∀ x, e₁ (a₁ x) = a₀ (d₁ x) := fun x => LinearMap.congr_fun ha₁ x
  obtain ⟨a₂, ha₂⟩ := resolution_lift_of_exact he2 (a₁ ∘ₗ d₂) (by
    ext x; simp [ha₁', Function.Exact.apply_apply_eq_zero hd2])
  obtain ⟨b₁, hb₁⟩ := resolution_lift_of_exact hd1 (b₀ ∘ₗ e₁) (by
    ext x; simp [hb₀', Function.Exact.apply_apply_eq_zero he1])
  have hb₁' : ∀ x, d₁ (b₁ x) = b₀ (e₁ x) := fun x => LinearMap.congr_fun hb₁ x
  obtain ⟨b₂, hb₂⟩ := resolution_lift_of_exact hd2 (b₁ ∘ₗ e₂) (by
    ext x; simp [hb₁', Function.Exact.apply_apply_eq_zero he2])
  obtain ⟨h₀, hh₀⟩ := resolution_lift_of_exact hd1 (LinearMap.id - b₀ ∘ₗ a₀) (by
    ext x; simp [hb₀', ha₀'])
  have hh₀' : ∀ x, d₁ (h₀ x) = x - b₀ (a₀ x) := fun x => by
    simpa using LinearMap.congr_fun hh₀ x
  obtain ⟨h₁, hh₁⟩ := resolution_lift_of_exact hd2 (LinearMap.id - b₁ ∘ₗ a₁ - h₀ ∘ₗ d₁) (by
    ext x; simp [hb₁', ha₁', hh₀'])
  have hh₁' : ∀ x, d₂ (h₁ x) = x - b₁ (a₁ x) - h₀ (d₁ x) := fun x => by
    simpa using LinearMap.congr_fun hh₁ x
  obtain ⟨h₂, hh₂⟩ := resolution_lift_of_exact hd3 (LinearMap.id - b₂ ∘ₗ a₂ - h₁ ∘ₗ d₂) (by
    ext x
    have e1 := LinearMap.congr_fun hb₂ (a₂ x)
    have e2 := LinearMap.congr_fun ha₂ x
    simp only [LinearMap.comp_apply] at e1 e2
    simp [hh₁', e1, e2, Function.Exact.apply_apply_eq_zero hd2])
  obtain ⟨k₀, hk₀⟩ := resolution_lift_of_exact he1 (LinearMap.id - a₀ ∘ₗ b₀) (by
    ext x; simp [hb₀', ha₀'])
  have hk₀' : ∀ x, e₁ (k₀ x) = x - a₀ (b₀ x) := fun x => by
    simpa using LinearMap.congr_fun hk₀ x
  obtain ⟨k₁, hk₁⟩ := resolution_lift_of_exact he2 (LinearMap.id - a₁ ∘ₗ b₁ - k₀ ∘ₗ e₁) (by
    ext x; simp [hb₁', ha₁', hk₀'])
  refine ⟨a₀, a₁, a₂, b₀, b₁, b₂, h₀, h₁, h₂, k₀, k₁, ha₁, ha₂, hb₁, hb₂, ?_, ?_, ?_⟩
  · rw [hh₁, sub_add_cancel]
  · rw [hh₂, sub_add_cancel]
  · rw [hk₁, sub_add_cancel]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFreeResolutionsHomotopyEquivalentStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialFreeResolutions_homotopyEquivalent : ∀ (O : Type) [CommRing O] (N : Type) [AddCommGroup N] [Module O N] (F₀ : Type) [AddCommGroup F₀] [Module O F₀] [Module.Free O F₀] [Module.Finite O F₀] (F₁ : Type) [AddCommGroup F₁] [Module O F₁] [Module.Free O F₁] [Module.Finite O F₁] (F₂ : Type) [AddCommGroup F₂] [Module O F₂] [Module.Free O F₂] [Module.Finite O F₂] (F₃ : Type) [AddCommGroup F₃] [Module O F₃] [Module.Free O F₃] [Module.Finite O F₃] (G₀ : Type) [AddCommGroup G₀] [Module O G₀] [Module.Free O G₀] [Module.Finite O G₀] (G₁ : Type) [AddCommGroup G₁] [Module O G₁] [Module.Free O G₁] [Module.Finite O G₁] (G₂ : Type) [AddCommGroup G₂] [Module O G₂] [Module.Free O G₂] [Module.Finite O G₂] (ε : F₀ →ₗ[O] N) (d₁ : F₁ →ₗ[O] F₀) (d₂ : F₂ →ₗ[O] F₁) (d₃ : F₃ →ₗ[O] F₂) (ν : G₀ →ₗ[O] N) (e₁ : G₁ →ₗ[O] G₀) (e₂ : G₂ →ₗ[O] G₁), Function.Surjective ε → Function.Exact d₁ ε → Function.Exact d₂ d₁ → Function.Exact d₃ d₂ → Function.Surjective ν → Function.Exact e₁ ν → Function.Exact e₂ e₁ → ∃ (a₀ : F₀ →ₗ[O] G₀) (a₁ : F₁ →ₗ[O] G₁) (a₂ : F₂ →ₗ[O] G₂) (b₀ : G₀ →ₗ[O] F₀) (b₁ : G₁ →ₗ[O] F₁) (b₂ : G₂ →ₗ[O] F₂) (h₀ : F₀ →ₗ[O] F₁) (h₁ : F₁ →ₗ[O] F₂) (h₂ : F₂ →ₗ[O] F₃) (k₀ : G₀ →ₗ[O] G₁) (k₁ : G₁ →ₗ[O] G₂), e₁ ∘ₗ a₁ = a₀ ∘ₗ d₁ ∧ e₂ ∘ₗ a₂ = a₁ ∘ₗ d₂ ∧ d₁ ∘ₗ b₁ = b₀ ∘ₗ e₁ ∧ d₂ ∘ₗ b₂ = b₁ ∘ₗ e₂ ∧ LinearMap.id - b₁ ∘ₗ a₁ = d₂ ∘ₗ h₁ + h₀ ∘ₗ d₁ ∧ LinearMap.id - b₂ ∘ₗ a₂ = d₃ ∘ₗ h₂ + h₁ ∘ₗ d₂ ∧ LinearMap.id - a₁ ∘ₗ b₁ = e₂ ∘ₗ k₁ + k₀ ∘ₗ e₁ := by
  first | exact @GlobalTheory.resolutions_homotopy_equivalent | exact GlobalTheory.resolutions_homotopy_equivalent | (intros; apply GlobalTheory.resolutions_homotopy_equivalent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHomologyResolutionsResidueField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem finrank_add_le_of_image_mem {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (A : V →ₗ[K] W) (Z R : Submodule K V) (Z' R' : Submodule K W) (hR' : R' ≤ Z')
    (hZ : ∀ x ∈ Z, A x ∈ Z') (hk : ∀ x ∈ Z, A x ∈ R' → x ∈ R) :
    Module.finrank K Z + Module.finrank K R' ≤ Module.finrank K Z' + Module.finrank K R := by
  let g : (Z × R') →ₗ[K] W := LinearMap.coprod (A ∘ₗ Z.subtype) R'.subtype
  have h1 := LinearMap.finrank_range_add_finrank_ker g
  rw [Module.finrank_prod] at h1
  have h2 : Module.finrank K (LinearMap.range g) ≤ Module.finrank K Z' := by
    apply Submodule.finrank_mono
    rintro _ ⟨⟨x, r⟩, rfl⟩
    simp only [g, LinearMap.coprod_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    exact Z'.add_mem (hZ x x.2) (hR' r.2)
  have h3 : Module.finrank K (LinearMap.ker g) ≤ Module.finrank K R := by
    let φ : LinearMap.ker g →ₗ[K] R :=
      LinearMap.codRestrict R (Z.subtype ∘ₗ LinearMap.fst K Z R' ∘ₗ (LinearMap.ker g).subtype) (by
        rintro ⟨⟨x, r⟩, hx⟩
        simp only [LinearMap.mem_ker, g, LinearMap.coprod_apply, LinearMap.comp_apply,
          Submodule.subtype_apply] at hx
        simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.fst_apply]
        apply hk x x.2
        have : A x = -(r : W) := eq_neg_of_add_eq_zero_left hx
        rw [this]; exact R'.neg_mem r.2)
    refine LinearMap.finrank_le_finrank_of_injective (f := φ) ?_
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    rintro ⟨⟨x, r⟩, hx⟩ h0
    simp only [LinearMap.mem_ker, g, LinearMap.coprod_apply, LinearMap.comp_apply,
      Submodule.subtype_apply] at hx
    have hx0 : x = 0 := by
      apply Subtype.ext
      have := congrArg Subtype.val h0
      simpa [φ] using this
    subst hx0
    have hr : r = 0 := by
      apply Subtype.ext
      simpa using hx
    subst hr
    rfl
  omega

theorem finrank_homology_base_change_resolutions : ∀ (O : Type) [CommRing O] (K : Type) [Field K] [Algebra O K] (N : Type) [AddCommGroup N] [Module O N] (F₀ : Type) [AddCommGroup F₀] [Module O F₀] [Module.Free O F₀] [Module.Finite O F₀] (F₁ : Type) [AddCommGroup F₁] [Module O F₁] [Module.Free O F₁] [Module.Finite O F₁] (F₂ : Type) [AddCommGroup F₂] [Module O F₂] [Module.Free O F₂] [Module.Finite O F₂] (F₃ : Type) [AddCommGroup F₃] [Module O F₃] [Module.Free O F₃] [Module.Finite O F₃] (G₀ : Type) [AddCommGroup G₀] [Module O G₀] [Module.Free O G₀] [Module.Finite O G₀] (G₁ : Type) [AddCommGroup G₁] [Module O G₁] [Module.Free O G₁] [Module.Finite O G₁] (G₂ : Type) [AddCommGroup G₂] [Module O G₂] [Module.Free O G₂] [Module.Finite O G₂] (ε : F₀ →ₗ[O] N) (d₁ : F₁ →ₗ[O] F₀) (d₂ : F₂ →ₗ[O] F₁) (d₃ : F₃ →ₗ[O] F₂) (ν : G₀ →ₗ[O] N) (e₁ : G₁ →ₗ[O] G₀) (e₂ : G₂ →ₗ[O] G₁), Function.Surjective ε → Function.Exact d₁ ε → Function.Exact d₂ d₁ → Function.Exact d₃ d₂ → Function.Surjective ν → Function.Exact e₁ ν → Function.Exact e₂ e₁ → Module.finrank K (LinearMap.ker (d₁.baseChange K)) + Module.finrank K (LinearMap.range (e₂.baseChange K)) = Module.finrank K (LinearMap.ker (e₁.baseChange K)) + Module.finrank K (LinearMap.range (d₂.baseChange K)) ∧ Module.finrank K (LinearMap.ker (d₂.baseChange K)) ≤ Module.finrank K (LinearMap.range (d₃.baseChange K)) + Module.finrank K (K ⊗[O] G₂) := by
  intro O _ K _ _ N _ _ F₀ _ _ _ _ F₁ _ _ _ _ F₂ _ _ _ _ F₃ _ _ _ _ G₀ _ _ _ _ G₁ _ _ _ _
    G₂ _ _ _ _ ε d₁ d₂ d₃ ν e₁ e₂ hε hd₁ hd₂ hd₃ hν he₁ he₂
  obtain ⟨a₀, a₁, a₂, b₀, b₁, b₂, h₀, h₁, h₂, k₀, k₁, c1, c2, c3, c4, c5, c6, c7⟩ :=
    GlobalTheory.T.partialFreeResolutions_homotopyEquivalent O N F₀ F₁ F₂ F₃ G₀ G₁ G₂ ε d₁ d₂ d₃ ν e₁ e₂ hε hd₁ hd₂ hd₃ hν he₁ he₂
  have bc : ∀ {P Q : Type} [AddCommGroup P] [Module O P] [AddCommGroup Q] [Module O Q]
      {f g : P →ₗ[O] Q}, f = g → ∀ x, f.baseChange K x = g.baseChange K x := by
    intro P Q _ _ _ _ f g h x; rw [h]
  have z12 : ∀ x, d₁.baseChange K (d₂.baseChange K x) = 0 := by
    intro x; have := bc hd₂.linearMap_comp_eq_zero x
    simpa [LinearMap.baseChange_comp] using this
  have ze12 : ∀ x, e₁.baseChange K (e₂.baseChange K x) = 0 := by
    intro x; have := bc he₂.linearMap_comp_eq_zero x
    simpa [LinearMap.baseChange_comp] using this
  have q1 : ∀ x, e₁.baseChange K (a₁.baseChange K x) = a₀.baseChange K (d₁.baseChange K x) := by
    intro x; have := bc c1 x; simpa [LinearMap.baseChange_comp] using this
  have q2 : ∀ x, e₂.baseChange K (a₂.baseChange K x) = a₁.baseChange K (d₂.baseChange K x) := by
    intro x; have := bc c2 x; simpa [LinearMap.baseChange_comp] using this
  have q3 : ∀ x, d₁.baseChange K (b₁.baseChange K x) = b₀.baseChange K (e₁.baseChange K x) := by
    intro x; have := bc c3 x; simpa [LinearMap.baseChange_comp] using this
  have q4 : ∀ x, d₂.baseChange K (b₂.baseChange K x) = b₁.baseChange K (e₂.baseChange K x) := by
    intro x; have := bc c4 x; simpa [LinearMap.baseChange_comp] using this
  have q5 : ∀ x, x - b₁.baseChange K (a₁.baseChange K x) =
      d₂.baseChange K (h₁.baseChange K x) + h₀.baseChange K (d₁.baseChange K x) := by
    intro x; have := bc c5 x
    simpa [LinearMap.baseChange_comp, LinearMap.baseChange_sub, LinearMap.baseChange_add,
      LinearMap.baseChange_id] using this
  have q6 : ∀ x, x - b₂.baseChange K (a₂.baseChange K x) =
      d₃.baseChange K (h₂.baseChange K x) + h₁.baseChange K (d₂.baseChange K x) := by
    intro x; have := bc c6 x
    simpa [LinearMap.baseChange_comp, LinearMap.baseChange_sub, LinearMap.baseChange_add,
      LinearMap.baseChange_id] using this
  have q7 : ∀ x, x - a₁.baseChange K (b₁.baseChange K x) =
      e₂.baseChange K (k₁.baseChange K x) + k₀.baseChange K (e₁.baseChange K x) := by
    intro x; have := bc c7 x
    simpa [LinearMap.baseChange_comp, LinearMap.baseChange_sub, LinearMap.baseChange_add,
      LinearMap.baseChange_id] using this
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · refine finrank_add_le_of_image_mem (a₁.baseChange K) _ _ _ _ ?_ ?_ ?_
    · rintro _ ⟨y, rfl⟩; exact ze12 y
    · intro x hx; rw [LinearMap.mem_ker] at hx ⊢; rw [q1, hx, map_zero]
    · rintro x hx ⟨y, hy⟩
      rw [LinearMap.mem_ker] at hx
      refine ⟨b₂.baseChange K y + h₁.baseChange K x, ?_⟩
      have := q5 x
      rw [hx, map_zero, add_zero, ← hy, ← q4] at this
      rw [map_add (f := _), ← this]; abel
  · refine finrank_add_le_of_image_mem (b₁.baseChange K) _ _ _ _ ?_ ?_ ?_
    · rintro _ ⟨y, rfl⟩; exact z12 y
    · intro x hx; rw [LinearMap.mem_ker] at hx ⊢; rw [q3, hx, map_zero]
    · rintro x hx ⟨y, hy⟩
      rw [LinearMap.mem_ker] at hx
      refine ⟨a₂.baseChange K y + k₁.baseChange K x, ?_⟩
      have := q7 x
      rw [hx, map_zero, add_zero, ← hy, ← q2] at this
      rw [map_add (f := _), ← this]; abel
  · have := finrank_add_le_of_image_mem (a₂.baseChange K) (LinearMap.ker (d₂.baseChange K))
      (LinearMap.range (d₃.baseChange K)) ⊤ ⊥ bot_le (fun _ _ => Submodule.mem_top) (by
        intro x hx h0
        rw [LinearMap.mem_ker] at hx
        rw [Submodule.mem_bot] at h0
        refine ⟨h₂.baseChange K x, ?_⟩
        have := q6 x
        rw [hx, h0, map_zero, map_zero, add_zero, sub_zero] at this
        exact this.symm)
    simp only [finrank_top, finrank_bot, add_zero] at this
    omega

end GlobalTheory.AbCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHomologyResolutionsResidueFieldStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_homology_resolutions_residueField : ∀ (O : Type) [CommRing O] (K : Type) [Field K] [Algebra O K] (N : Type) [AddCommGroup N] [Module O N] (F₀ : Type) [AddCommGroup F₀] [Module O F₀] [Module.Free O F₀] [Module.Finite O F₀] (F₁ : Type) [AddCommGroup F₁] [Module O F₁] [Module.Free O F₁] [Module.Finite O F₁] (F₂ : Type) [AddCommGroup F₂] [Module O F₂] [Module.Free O F₂] [Module.Finite O F₂] (F₃ : Type) [AddCommGroup F₃] [Module O F₃] [Module.Free O F₃] [Module.Finite O F₃] (G₀ : Type) [AddCommGroup G₀] [Module O G₀] [Module.Free O G₀] [Module.Finite O G₀] (G₁ : Type) [AddCommGroup G₁] [Module O G₁] [Module.Free O G₁] [Module.Finite O G₁] (G₂ : Type) [AddCommGroup G₂] [Module O G₂] [Module.Free O G₂] [Module.Finite O G₂] (ε : F₀ →ₗ[O] N) (d₁ : F₁ →ₗ[O] F₀) (d₂ : F₂ →ₗ[O] F₁) (d₃ : F₃ →ₗ[O] F₂) (ν : G₀ →ₗ[O] N) (e₁ : G₁ →ₗ[O] G₀) (e₂ : G₂ →ₗ[O] G₁), Function.Surjective ε → Function.Exact d₁ ε → Function.Exact d₂ d₁ → Function.Exact d₃ d₂ → Function.Surjective ν → Function.Exact e₁ ν → Function.Exact e₂ e₁ → Module.finrank K (LinearMap.ker (d₁.baseChange K)) + Module.finrank K (LinearMap.range (e₂.baseChange K)) = Module.finrank K (LinearMap.ker (e₁.baseChange K)) + Module.finrank K (LinearMap.range (d₂.baseChange K)) ∧ Module.finrank K (LinearMap.ker (d₂.baseChange K)) ≤ Module.finrank K (LinearMap.range (d₃.baseChange K)) + Module.finrank K (K ⊗[O] G₂) := by
  first | exact @GlobalTheory.AbCoh.finrank_homology_base_change_resolutions | exact GlobalTheory.AbCoh.finrank_homology_base_change_resolutions | (intros; apply GlobalTheory.AbCoh.finrank_homology_base_change_resolutions <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeBaseChangeEqFinrankRangeDualMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeBaseChangeEqFinrankRangeDualMap
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem finrank_range_baseChange_eq_dualMap_and_finrank_dual :
    ∀ (O : Type) [CommRing O] (K : Type) [Field K] [Algebra O K] (M₁ : Type) [AddCommGroup M₁] [Module O M₁] [Module.Free O M₁] [Module.Finite O M₁] (M₂ : Type) [AddCommGroup M₂] [Module O M₂] [Module.Free O M₂] [Module.Finite O M₂] (f : M₁ →ₗ[O] M₂), Module.finrank K (LinearMap.range (f.baseChange K)) = Module.finrank K (LinearMap.range (f.dualMap.baseChange K)) ∧ Module.finrank K (K ⊗[O] M₁) = Module.finrank K (K ⊗[O] Module.Dual O M₁) := by
  intro O _ K _ _ M₁ _ _ _ _ M₂ _ _ _ _ f
  obtain ⟨h1, h2⟩ := GlobalTheory.DualFibreRank.finrank_dual_and_range_dualMap_baseChange O M₁ M₂ K f
  exact ⟨h2.symm, h1.symm⟩

end GlobalTheory.AbCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeBaseChangeEqFinrankRangeDualMapStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_range_baseChange_eq_finrank_range_dualMap : ∀ (O : Type) [CommRing O] (K : Type) [Field K] [Algebra O K] (M₁ : Type) [AddCommGroup M₁] [Module O M₁] [Module.Free O M₁] [Module.Finite O M₁] (M₂ : Type) [AddCommGroup M₂] [Module O M₂] [Module.Free O M₂] [Module.Finite O M₂] (f : M₁ →ₗ[O] M₂), Module.finrank K (LinearMap.range (f.baseChange K)) = Module.finrank K (LinearMap.range (f.dualMap.baseChange K)) ∧ Module.finrank K (K ⊗[O] M₁) = Module.finrank K (K ⊗[O] Module.Dual O M₁) := by
  first | exact @GlobalTheory.AbCoh.finrank_range_baseChange_eq_dualMap_and_finrank_dual | exact GlobalTheory.AbCoh.finrank_range_baseChange_eq_dualMap_and_finrank_dual | (intros; apply GlobalTheory.AbCoh.finrank_range_baseChange_eq_dualMap_and_finrank_dual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHomologyOneTwoDualResolution
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FirstBetti

theorem finrank_homology_succ_add (O : Type) [CommRing O] (K : Type) [Field K] [Algebra O K]
    (C : CochainComplex (ModuleCat.{0} O) ℕ) [∀ i, Module.Finite O (C.X i)] (n : ℕ) :
    Module.finrank K ((((ModuleCat.extendScalars (algebraMap O K)).mapHomologicalComplex _).obj
        C).homology (n + 1))
      + Module.finrank K (LinearMap.range ((C.d n (n + 1)).hom.baseChange K))
      + Module.finrank K (LinearMap.range ((C.d (n + 1) (n + 2)).hom.baseChange K))
      = Module.finrank K (K ⊗[O] C.X (n + 1)) := by
  let D := ((ModuleCat.extendScalars (algebraMap O K)).mapHomologicalComplex _).obj C
  have e1 := (D.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).toLinearEquiv
  obtain ⟨e2⟩ := GlobalTheory.Semicont.nonempty_homology_map_extendScalars_equiv K (C.sc' n (n + 1) (n + 2))
  have h := GlobalTheory.Semicont.finrank_homology_add_finrank_range
    ((C.d n (n + 1)).hom.baseChange K) ((C.d (n + 1) (n + 2)).hom.baseChange K)
    (by rw [← LinearMap.baseChange_comp, ← ModuleCat.hom_comp, C.d_comp_d, ModuleCat.hom_zero,
      LinearMap.baseChange_zero])
  rw [(e1.trans e2).finrank_eq]
  exact h

theorem smul_eq_zero_of_algebraMap_eq_zero {O : Type} [CommRing O] {K : Type} [Field K]
    [Algebra O K] {M : Type} [AddCommGroup M] [Module O M] {r : O} (hr : algebraMap O K r = 0)
    (z : K ⊗[O] M) : r • z = 0 := by
  rw [← algebraMap_smul K r z, hr, zero_smul]

theorem baseChange_eq_zero_of_ring {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
    {M : Type} [AddCommGroup M] [Module O M] (e : M →ₗ[O] O)
    (he : ∀ x, algebraMap O K (e x) = 0) : e.baseChange K = 0 := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul k x =>
    rw [LinearMap.baseChange_tmul, LinearMap.zero_apply, ← mul_one (e x), ← smul_eq_mul,
      TensorProduct.tmul_smul, smul_eq_zero_of_algebraMap_eq_zero (he x)]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, LinearMap.zero_apply, add_zero]

theorem baseChange_eq_zero_of_pi {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
    {M : Type} [AddCommGroup M] [Module O M] {n : ℕ} (e : M →ₗ[O] (Fin n → O))
    (he : ∀ x i, algebraMap O K (e x i) = 0) : e.baseChange K = 0 := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul k x =>
    rw [LinearMap.baseChange_tmul, LinearMap.zero_apply, pi_eq_sum_univ (e x),
      TensorProduct.tmul_sum]
    exact Finset.sum_eq_zero fun i _ => by
      rw [TensorProduct.tmul_smul, smul_eq_zero_of_algebraMap_eq_zero (he x i)]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, LinearMap.zero_apply, add_zero]

end GlobalTheory.FirstBetti

namespace GlobalTheory


open FirstBetti in
theorem finrank_homology_one_two_of_dual_resolution : ∀ (O : Type) [CommRing O] [IsRegularLocalRing O] (g : ℕ), ringKrullDim O = g → ∀ (f : Fin g → O), Ideal.span (Set.range f) ≠ ⊤ → IsArtinianRing (O ⧸ Ideal.span (Set.range f)) → ∀ (C : CochainComplex (ModuleCat.{0} O) ℕ), (∀ i, Module.Free O (C.X i) ∧ Module.Finite O (C.X i)) → (∀ i, Function.Exact (C.d (i + 1) (i + 2)).hom.dualMap (C.d i (i + 1)).hom.dualMap) → Nonempty ((Module.Dual O (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[O] (O ⧸ Ideal.span (Set.range f))) → ∀ (K : Type) [Field K] (φ : O →+* K), RingHom.ker φ = IsLocalRing.maximalIdeal O → Module.finrank K ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology 1) = g ∧ Module.finrank K ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology 2) ≤ g.choose 2 := by
  intro O _ _ g hdim f hne hart C hC hex hN K _ φ hker
  obtain ⟨eN⟩ := hN
  letI := φ.toAlgebra
  haveI : ∀ i, Module.Free O (C.X i) := fun i => (hC i).1
  haveI : ∀ i, Module.Finite O (C.X i) := fun i => (hC i).2
  have hIm : Ideal.span (Set.range f) ≤ IsLocalRing.maximalIdeal O := IsLocalRing.le_maximalIdeal hne
  have hIφ : ∀ x ∈ Ideal.span (Set.range f), algebraMap O K x = 0 := fun x hx => by
    have : x ∈ RingHom.ker φ := hker ▸ hIm hx
    exact this

  have hreg : RingTheory.Sequence.IsRegular O (List.ofFn f) := by
    refine GlobalTheory.isRegular_ofFn_of_ringKrullDim_quotient_add_le O g g f hdim
      (fun i => hIm (Ideal.subset_span ⟨i, rfl⟩)) ?_
    have h0 : ringKrullDim (O ⧸ Ideal.span (Set.range f)) ≤ 0 := Ring.krullDimLE_iff.1 inferInstance
    calc ringKrullDim (O ⧸ Ideal.span (Set.range f)) + (g : WithBot ℕ∞) ≤ 0 + (g : WithBot ℕ∞) :=
          add_le_add_left h0 _
      _ = g := zero_add _
  obtain ⟨e₁, e₂, hx1, hx2, he1, he2⟩ := GlobalTheory.T.koszul_resolution_three_terms_exact O g f hreg.toIsWeaklyRegular

  let ε : Module.Dual O (C.X 0) →ₗ[O] O ⧸ Ideal.span (Set.range f) :=
    eN.toLinearMap ∘ₗ (LinearMap.range (C.d 0 1).hom.dualMap).mkQ
  have hεs : Function.Surjective ε := eN.surjective.comp (Submodule.mkQ_surjective _)
  have hεx : Function.Exact (C.d 0 1).hom.dualMap ε := by
    rw [LinearMap.exact_iff, LinearEquiv.ker_comp, Submodule.ker_mkQ]
  obtain ⟨hA, hB⟩ := GlobalTheory.T.finrank_homology_resolutions_residueField O K (O ⧸ Ideal.span (Set.range f))
    (Module.Dual O (C.X 0)) (Module.Dual O (C.X 1)) (Module.Dual O (C.X 2)) (Module.Dual O (C.X 3))
    O (Fin g → O) (Fin (g.choose 2) → O) ε (C.d 0 1).hom.dualMap (C.d 1 2).hom.dualMap
    (C.d 2 3).hom.dualMap (Ideal.span (Set.range f)).mkQ e₁ e₂ hεs hεx (hex 0) (hex 1)
    (Submodule.mkQ_surjective _) hx1 hx2

  have hz1 : e₁.baseChange K = 0 := baseChange_eq_zero_of_ring e₁ fun x => hIφ _ (he1 x)
  have hz2 : e₂.baseChange K = 0 := baseChange_eq_zero_of_pi e₂ fun x i => hIφ _ (he2 x i)
  have hk1 : Module.finrank K (LinearMap.ker (e₁.baseChange K)) = g := by
    rw [hz1, LinearMap.ker_zero, finrank_top, GlobalTheory.Semicont.finrank_baseChange_fin]
  have hr2 : Module.finrank K (LinearMap.range (e₂.baseChange K)) = 0 := by
    rw [hz2, LinearMap.range_zero, finrank_bot]
  have hc2 : Module.finrank K (K ⊗[O] (Fin (g.choose 2) → O)) = g.choose 2 :=
    GlobalTheory.Semicont.finrank_baseChange_fin _ _

  obtain ⟨r0, n0⟩ := GlobalTheory.T.finrank_range_baseChange_eq_finrank_range_dualMap O K (C.X 0) (C.X 1) (C.d 0 1).hom
  obtain ⟨r1, n1⟩ := GlobalTheory.T.finrank_range_baseChange_eq_finrank_range_dualMap O K (C.X 1) (C.X 2) (C.d 1 2).hom
  obtain ⟨r2, n2⟩ := GlobalTheory.T.finrank_range_baseChange_eq_finrank_range_dualMap O K (C.X 2) (C.X 3) (C.d 2 3).hom
  have k1 := LinearMap.finrank_range_add_finrank_ker ((C.d 0 1).hom.dualMap.baseChange K)
  have k2 := LinearMap.finrank_range_add_finrank_ker ((C.d 1 2).hom.dualMap.baseChange K)

  have h1 : Module.finrank K ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology 1)
      + Module.finrank K (LinearMap.range ((C.d 0 1).hom.baseChange K))
      + Module.finrank K (LinearMap.range ((C.d 1 2).hom.baseChange K))
      = Module.finrank K (K ⊗[O] C.X 1) := finrank_homology_succ_add O K C 0
  have h2 : Module.finrank K ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology 2)
      + Module.finrank K (LinearMap.range ((C.d 1 2).hom.baseChange K))
      + Module.finrank K (LinearMap.range ((C.d 2 3).hom.baseChange K))
      = Module.finrank K (K ⊗[O] C.X 2) := finrank_homology_succ_add O K C 1
  constructor <;> omega

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHomologyOneTwoDualResolutionStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_homology_one_two_dualResolution : ∀ (O : Type) [CommRing O] [IsRegularLocalRing O] (g : ℕ), ringKrullDim O = g → ∀ (f : Fin g → O), Ideal.span (Set.range f) ≠ ⊤ → IsArtinianRing (O ⧸ Ideal.span (Set.range f)) → ∀ (C : CochainComplex (ModuleCat.{0} O) ℕ), (∀ i, Module.Free O (C.X i) ∧ Module.Finite O (C.X i)) → (∀ i, Function.Exact (C.d (i + 1) (i + 2)).hom.dualMap (C.d i (i + 1)).hom.dualMap) → Nonempty ((Module.Dual O (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[O] (O ⧸ Ideal.span (Set.range f))) → ∀ (K : Type) [Field K] (φ : O →+* K), RingHom.ker φ = IsLocalRing.maximalIdeal O → Module.finrank K ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology 1) = g ∧ Module.finrank K ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology 2) ≤ g.choose 2 := by
  first | exact @GlobalTheory.finrank_homology_one_two_of_dual_resolution | exact GlobalTheory.finrank_homology_one_two_of_dual_resolution | (intros; apply GlobalTheory.finrank_homology_one_two_of_dual_resolution <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCohomologyTrivialBundleAbelian
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.FDim

theorem fromSpecStalk_comp_spec {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (z : Y) :
    Y.fromSpecStalk z ≫ p =
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop ≫ Y.presheaf.germ ⊤ z trivial) := by
  rw [Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ, Category.assoc, Category.assoc,
    ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem isClosed_origin (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (p : Sp K) :
    IsClosed ({(η[A]).left.base p} : Set A.left) := by
  have hr : Set.range (η[A]).left.base = {(η[A]).left.base p} := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      have hs : Subsingleton (Sp K) := inferInstance
      obtain rfl : q = p := hs.elim q p
      rfl
    · rintro rfl
      exact ⟨p, rfl⟩
  rw [← hr]
  exact (η[A]).left.isClosedEmbedding.isClosed_range

theorem cechLB_triv_finrank_one_two : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → A.left.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (∀ i, Module.Finite K ((cechLB A.hom (LB.triv A.left) D).homology i)) ∧ Module.finrank K ((cechLB A.hom (LB.triv A.left) D).homology 1) = g ∧ Module.finrank K ((cechLB A.hom (LB.triv A.left) D).homology 2) ≤ g.choose 2 := by
  intro K _ _ A _ g hA hsm κ _ _ D hD hcov
  obtain ⟨L, H, _, j, hL, hproj, hgen, hj, hci, hfin, hK⟩ := GlobalTheory.T.exists_ample_kernel_finite_subgroupScheme K A hA
  obtain ⟨p⟩ : Nonempty (Sp K) := inferInstance
  have hx₀ : (η[A]).left.base p ∈ Set.range (η[A]).left.base := ⟨p, rfl⟩
  obtain ⟨J, C, φ, hJ, hφ, hfree, hbdd, hcok, hfib, hiso⟩ :=
    GlobalTheory.T.exists_free_complex_structureSheaf_cech_origin K A g hA hsm L H j hL hproj hgen hj hci hfin hK _ hx₀
  obtain ⟨f, hf⟩ := GlobalTheory.T.finiteSubgroupScheme_ideal_generated_by_dim_elements K A g hA hsm H j hj hci hfin _ hx₀ J hJ
  obtain ⟨hJt, hart⟩ := GlobalTheory.T.closed_subfunctor_stalk_ideal_criterion K A H j hj hci hfin _ hx₀ J hJ
  subst hf
  let σ : K →+* A.left.presheaf.stalk ((η[A]).left.base p) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ A.hom.appTop ≫
      A.left.presheaf.germ ⊤ ((η[A]).left.base p) trivial).hom
  have hσ : A.left.fromSpecStalk ((η[A]).left.base p) ≫ A.hom = Spec.map (CommRingCat.ofHom σ) := by
    rw [fromSpecStalk_comp_spec]
    rfl
  have hloc : IsLocalHom σ := ⟨fun a ha => by
    rcases eq_or_ne a 0 with rfl | h
    · simp at ha
    · exact h.isUnit⟩
  obtain ⟨-, -, hreg, hdim⟩ := GlobalTheory.T.stalk_regular_flat_of_smooth K A.left A.hom g hsm _ (isClosed_origin K A p) σ hσ hloc
  have hbot : (IsLocalRing.maximalIdeal K).map σ = ⊥ := by
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.map_bot]
  let e := (Ideal.quotEquivOfEq hbot).trans (RingEquiv.quotientBot (A.left.presheaf.stalk ((η[A]).left.base p)))
  haveI : IsRegularLocalRing (A.left.presheaf.stalk ((η[A]).left.base p)) :=
    IsRegularLocalRing.of_ringEquiv e
  have hdim' : ringKrullDim (A.left.presheaf.stalk ((η[A]).left.base p)) = g := by
    rw [← ringKrullDim_eq_of_ringEquiv e]
    exact hdim
  have hex := GlobalTheory.T.exact_dualMap_of_exactAt_extendScalars_fibres _ g hdim' C hfree hbdd hfib
  obtain ⟨h1, h2⟩ := GlobalTheory.T.finrank_homology_one_two_dualResolution _ g hdim' f hJt hart C hfree hex hcok K φ hφ
  haveI := hA.proper
  refine ⟨fun i => ?_, ?_, ?_⟩
  · exact GlobalTheory.AbLaw.cechLB_homology_finite_of_affine_cover K A.left A.hom (LB.triv A.left) κ D
      (LB.isLB_triv _) inferInstance hproj hD hcov i
  · obtain ⟨e1⟩ := hiso κ D hD hcov 1
    rw [← e1.finrank_eq]
    exact h1
  · obtain ⟨e2⟩ := hiso κ D hD hcov 2
    rw [← e2.finrank_eq]
    exact h2

end GlobalTheory.AbCoh.FDim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCohomologyTrivialBundleAbelianStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_cohomology_trivial_bundle_abelian : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → A.left.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (∀ i, Module.Finite K ((cechLB A.hom (LB.triv A.left) D).homology i)) ∧ Module.finrank K ((cechLB A.hom (LB.triv A.left) D).homology 1) = g ∧ Module.finrank K ((cechLB A.hom (LB.triv A.left) D).homology 2) ≤ g.choose 2 := by
  first | exact @GlobalTheory.AbCoh.FDim.cechLB_triv_finrank_one_two | exact GlobalTheory.AbCoh.FDim.cechLB_triv_finrank_one_two | (intros; apply GlobalTheory.AbCoh.FDim.cechLB_triv_finrank_one_two <;> assumption)
end
