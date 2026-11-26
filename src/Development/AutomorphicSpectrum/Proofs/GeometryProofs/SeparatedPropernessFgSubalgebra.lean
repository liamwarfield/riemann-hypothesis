module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsProjOverIsIsoMorphismRestrict

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.QuasiProjectiveProperCover
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChowLemmaQuasiProjective
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChowLemmaQuasiProjective
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem exists_lift_of_isDominant {D Y V A : Scheme.{0}} [IsReduced Y] (σ : D ⟶ Y) [IsDominant σ]
    (r : Y ⟶ V) (k : A ⟶ V) [IsClosedImmersion k] (a : D ⟶ A) (h : σ ≫ r = a ≫ k) :
    ∃ φ : Y ⟶ A, φ ≫ k = r := by
  have hl : pullback.lift σ a h ≫ pullback.fst r k = σ := pullback.lift_fst _ _ _
  have : IsDominant (pullback.lift σ a h ≫ pullback.fst r k) := by rw [hl]; infer_instance
  have : IsDominant (pullback.fst r k) := IsDominant.of_comp (pullback.lift σ a h) _
  have : Surjective (pullback.fst r k) :=
    surjective_of_isDominant_of_isClosed_range _ (pullback.fst r k).isClosedEmbedding.isClosed_range
  have : IsIso (pullback.fst r k) := isIso_of_isClosedImmersion_of_surjective _
  exact ⟨inv (pullback.fst r k) ≫ pullback.snd r k, by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]⟩

theorem isClosedImmersion_morphismRestrict {S X B X' T D : Scheme.{0}} (f : X ⟶ S) [IsSeparated f]
    (u : B ⟶ S) [IsReduced X'] (π : X' ⟶ X) (b : X' ⟶ B) (hπb : π ≫ f = b ≫ u)
    [IsClosedImmersion (pullback.lift π b hπb)] (A : X.Opens) (O : B.Opens) (τ : T ⟶ S)
    (ρ : O.toScheme ⟶ T) (hρ : ρ ≫ τ = O.ι ≫ u) (k : A.toScheme ⟶ T) [IsClosedImmersion k]
    (hk : k ≫ τ = A.ι ≫ f) (σ : D ⟶ (b ⁻¹ᵁ O).toScheme) [IsDominant σ] (a : D ⟶ A.toScheme)
    (h₁ : σ ≫ b ∣_ O ≫ ρ = a ≫ k) (h₂ : a ≫ A.ι = σ ≫ (b ⁻¹ᵁ O).ι ≫ π) :
    IsClosedImmersion (b ∣_ O) := by
  obtain ⟨φ, hφ⟩ := exists_lift_of_isDominant σ (b ∣_ O ≫ ρ) k a h₁
  have hσφ : σ ≫ φ = a := by
    rw [← cancel_mono k, Category.assoc, hφ, h₁]
  have hφι : φ ≫ A.ι = (b ⁻¹ᵁ O).ι ≫ π := by
    refine ext_of_isDominant_of_isSeparated f ?_ σ ?_
    · rw [Category.assoc, Category.assoc, ← hk, reassoc_of% hφ, hρ, morphismRestrict_ι_assoc,
        hπb]
    · rw [reassoc_of% hσφ, h₂]
  have hc : (pullback.snd ρ k ≫ A.ι) ≫ f = (pullback.fst ρ k ≫ O.ι) ≫ u := by
    rw [Category.assoc, Category.assoc, ← hk, ← hρ, pullback.condition_assoc]
  let c : pullback ρ k ⟶ pullback f u := pullback.lift _ _ hc
  have c₁ : c ≫ pullback.fst f u = pullback.snd ρ k ≫ A.ι := pullback.lift_fst _ _ _
  have c₂ : c ≫ pullback.snd f u = pullback.fst ρ k ≫ O.ι := pullback.lift_snd _ _ _
  have : Mono c := by
    have : Mono (c ≫ pullback.snd f u) := by rw [c₂]; infer_instance
    exact mono_of_mono c (pullback.snd f u)
  let m : (b ⁻¹ᵁ O).toScheme ⟶ pullback ρ k := pullback.lift (b ∣_ O) φ hφ.symm
  have m₁ : m ≫ pullback.fst ρ k = b ∣_ O := pullback.lift_fst _ _ _
  have m₂ : m ≫ pullback.snd ρ k = φ := pullback.lift_snd _ _ _
  have hw : (b ⁻¹ᵁ O).ι ≫ pullback.lift π b hπb = m ≫ c := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, c₁, reassoc_of% m₂, hφι]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, c₂, reassoc_of% m₁,
        morphismRestrict_ι]
  have sq : IsPullback (b ⁻¹ᵁ O).ι m (pullback.lift π b hπb) c := by
    have hr : ∀ {Z : Scheme.{0}} (x : Z ⟶ X') (y : Z ⟶ pullback ρ k),
        x ≫ pullback.lift π b hπb = y ≫ c → Set.range x ⊆ Set.range (b ⁻¹ᵁ O).ι := by
      intro Z x y e
      have e' : x ≫ b = (y ≫ pullback.fst ρ k) ≫ O.ι := by
        have := congr($e ≫ pullback.snd f u)
        simpa only [Category.assoc, pullback.lift_snd, c₂] using this
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      change (x ≫ b) z ∈ O
      rw [e']
      exact ((y ≫ pullback.fst ρ k) z).2
    refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw
      (fun s ↦ IsOpenImmersion.lift (b ⁻¹ᵁ O).ι s.fst (hr _ _ s.condition)) (fun s ↦ ?_)
      (fun s ↦ ?_) (fun s n h₃ _ ↦ ?_)⟩⟩
    · exact IsOpenImmersion.lift_fac _ _ _
    · rw [← cancel_mono c, Category.assoc, ← hw, IsOpenImmersion.lift_fac_assoc, s.condition]
    · rw [← cancel_mono (b ⁻¹ᵁ O).ι, IsOpenImmersion.lift_fac, h₃]
  have : IsClosedImmersion m := MorphismProperty.of_isPullback (P := @IsClosedImmersion) sq ‹_›
  rw [← m₁]
  infer_instance

theorem exists_isProper_surjective_isQProjOver : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), IsSeparated p → LocallyOfFiniteType p → QuasiCompact p → ∃ (X' : Scheme.{0}) (π : X' ⟶ X), IsProper π ∧ Surjective π ∧ IsQProjOver (π ≫ p) := by
  intro R _ _ X _ f _ _ _
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hA : ∀ y : X, ∃ A : X.Opens, IsAffineOpen A ∧ y ∈ A := fun y ↦ by
    obtain ⟨A, h₁, h₂, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
    exact ⟨A, h₁, h₂⟩
  choose A₀ hA₀ hyA using hA
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun y ↦ (A₀ y : Set X))
    (fun y ↦ (A₀ y).isOpen) (fun y _ ↦ Set.mem_iUnion.2 ⟨y, hyA y⟩)
  let A : T → X.Opens := fun i ↦ A₀ i
  have hcov : ∀ y : X, ∃ i : T, y ∈ A i := fun y ↦ by
    obtain ⟨i, hi, h⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ y))
    exact ⟨⟨i, hi⟩, h⟩
  have hP := fun i : T ↦ (have : IsAffine (A i).toScheme := hA₀ i
    (isAmpleLB_of_isAffine (LB.isLB_triv (A i).toScheme)).isQProjOver ((A i).ι ≫ f))
  choose N j hj _ hjt using hP
  let U : X.Opens := Finset.univ.inf A
  have hUA : ∀ i, U ≤ A i := fun i ↦ Finset.inf_le (Finset.mem_univ i)
  have hU : genericPoint X ∈ U := by
    have : ∀ i, genericPoint X ∈ A i := fun i ↦
      ((genericPoint_spec X).mem_open_set_iff (A i).isOpen).2 ⟨i, trivial, hyA i⟩
    refine Finset.inf_induction (p := fun V : X.Opens ↦ genericPoint X ∈ V) trivial
      (fun _ h _ h' ↦ ⟨h, h'⟩) fun i _ ↦ this i
  have hps : ∀ n, IsProjOver (PSpace.str R n) := fun n ↦ ⟨n, 𝟙 _, inferInstance, Category.id_comp _⟩
  obtain ⟨P, s, p, hP, hp, hu⟩ := ProjFinProd.exists_isProjOver_finite_prod R T (Sp R) (𝟙 _)
    (fun i ↦ PSpace R (N i)) (fun i ↦ PSpace.str R (N i))
    ((isAmpleLB_of_isAffine (LB.isLB_triv (Sp R))).isProjOver (𝟙 _)) (fun i ↦ hps _)
  rw [Category.comp_id] at hP hp
  obtain ⟨h, ⟨hs, hh⟩, -⟩ := hu U.toScheme (U.ι ≫ f) (fun i ↦ X.homOfLE (hUA i) ≫ j i)
    (fun i ↦ by rw [Category.assoc, hjt, X.homOfLE_ι_assoc, Category.comp_id])
  have : IsProper s := ((isProjOver_iff_isProper_and_exists_isAmpleLB s).1 hP).1
  let g : U.toScheme ⟶ pullback f s := pullback.lift U.ι h hs.symm
  have g₁ : g ≫ pullback.fst f s = U.ι := pullback.lift_fst _ _ _
  have g₂ : g ≫ pullback.snd f s = h := pullback.lift_snd _ _ _
  have : IsImmersion (g ≫ pullback.fst f s) := by rw [g₁]; infer_instance
  have : IsImmersion g := IsImmersion.of_comp g (pullback.fst f s)
  have : QuasiCompact (g ≫ pullback.fst f s) := by rw [g₁]; infer_instance
  have : QuasiCompact g := QuasiCompact.of_comp g (pullback.fst f s)
  have := isSchemeTheoreticallyDominant_toImage g
  have : IsReduced g.image := IsSchemeTheoreticallyDominant.isReduced g.toImage
  let π : g.image ⟶ X := g.imageι ≫ pullback.fst f s
  let q : g.image ⟶ P := g.imageι ≫ pullback.snd f s
  have hπ : g.toImage ≫ π = U.ι := by rw [g.toImage_imageι_assoc, g₁]
  have hq : g.toImage ≫ q = h := by rw [g.toImage_imageι_assoc, g₂]
  have hπq : π ≫ f = q ≫ s := by
    rw [Category.assoc, Category.assoc, pullback.condition]
  have key : ∀ i, (π ⁻¹ᵁ A i).ι ≫ q ≫ p i = π ∣_ A i ≫ j i := by
    intro i
    obtain ⟨σ, _, e₁, e₂⟩ := GlobalTheory.ChowLemma.exists_dominant_lift π (hUA i) g.toImage hπ
    have := isProper_str R (N i)
    refine ext_of_isDominant_of_isSeparated (PSpace.str R (N i)) ?_ σ ?_
    · rw [Category.assoc, Category.assoc, hp, ← hπq, Category.assoc (π ∣_ A i), hjt,
        morphismRestrict_ι_assoc]
    · rw [reassoc_of% e₁, reassoc_of% hq, hh, reassoc_of% e₂]
  have : ∀ i, IsImmersion (j i) := hj
  let V : ∀ i, (PSpace R (N i)).Opens := fun i ↦ (j i).coborderRange
  have hV : ∀ i (x : g.image), π x ∈ A i → (q ≫ p i) x ∈ V i := by
    intro i x hx
    have e : ((π ⁻¹ᵁ A i).ι ≫ q ≫ p i) ⟨x, hx⟩ = (π ∣_ A i ≫ j i) ⟨x, hx⟩ := by rw [key i]
    change ((π ⁻¹ᵁ A i).ι ≫ q ≫ p i) ⟨x, hx⟩ ∈ V i
    rw [e]
    exact subset_coborder ⟨_, rfl⟩
  let W : P.Opens := ⨆ i, p i ⁻¹ᵁ V i
  have hW : Set.range q ⊆ Set.range W.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    obtain ⟨i, hi⟩ := hcov (π x)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hV i x hi⟩
  let q' : g.image ⟶ W.toScheme := IsOpenImmersion.lift W.ι q hW
  have hq' : q' ≫ W.ι = q := IsOpenImmersion.lift_fac _ _ _
  have hπq' : π ≫ f = q' ≫ W.ι ≫ s := by rw [reassoc_of% hq', hπq]
  have hcl : IsClosedImmersion (pullback.lift π q' hπq') := by
    let e : pullback f (W.ι ≫ s) ⟶ pullback f s :=
      pullback.lift (pullback.fst f (W.ι ≫ s)) (pullback.snd f (W.ι ≫ s) ≫ W.ι)
        (by rw [pullback.condition, Category.assoc])
    have e₁ : e ≫ pullback.fst f s = pullback.fst f (W.ι ≫ s) := pullback.lift_fst _ _ _
    have e₂ : e ≫ pullback.snd f s = pullback.snd f (W.ι ≫ s) ≫ W.ι := pullback.lift_snd _ _ _
    have : Mono e := by
      refine ⟨fun a b hab ↦ pullback.hom_ext ?_ ?_⟩
      · simpa only [Category.assoc, e₁] using congr($hab ≫ pullback.fst f s)
      · rw [← cancel_mono W.ι]
        simpa only [Category.assoc, e₂] using congr($hab ≫ pullback.snd f s)
    have he : pullback.lift π q' hπq' ≫ e = g.imageι := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, e₁, pullback.lift_fst]
      · rw [Category.assoc, e₂, pullback.lift_snd_assoc, hq']
    have : IsClosedImmersion (pullback.lift π q' hπq' ≫ e) := by rw [he]; infer_instance
    exact IsClosedImmersion.of_comp _ e
  let O : T → W.toScheme.Opens := fun i ↦ (W.ι ≫ p i) ⁻¹ᵁ V i
  have hO : iSup O = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 y.2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  have hloc : ∀ i, IsClosedImmersion (q' ∣_ O i) := by
    intro i
    have hr : Set.range g.toImage ⊆ Set.range (q' ⁻¹ᵁ O i).ι := by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      have hx : (g.toImage ≫ π) x ∈ A i := by
        rw [hπ]
        exact hUA i x.2
      change (q' ≫ W.ι ≫ p i) (g.toImage x) ∈ V i
      rw [reassoc_of% hq']
      exact hV i _ hx
    have hσ := IsOpenImmersion.lift_fac (q' ⁻¹ᵁ O i).ι g.toImage hr
    have : IsDominant (IsOpenImmersion.lift (q' ⁻¹ᵁ O i).ι g.toImage hr ≫ (q' ⁻¹ᵁ O i).ι) := by
      rw [hσ]; infer_instance
    have : IsDominant (IsOpenImmersion.lift (q' ⁻¹ᵁ O i).ι g.toImage hr) :=
      IsDominant.of_comp_of_isOpenImmersion _ (q' ⁻¹ᵁ O i).ι
    refine isClosedImmersion_morphismRestrict f (W.ι ≫ s) π q' hπq' (A i) (O i)
      ((V i).ι ≫ PSpace.str R (N i)) ((W.ι ≫ p i) ∣_ V i) ?_ (j i).liftCoborder ?_
      (IsOpenImmersion.lift (q' ⁻¹ᵁ O i).ι g.toImage hr) (X.homOfLE (hUA i)) ?_ ?_
    · rw [morphismRestrict_ι_assoc, Category.assoc, hp]
    · rw [Scheme.Hom.liftCoborder_ι_assoc, hjt]
    · rw [← cancel_mono (V i).ι, Category.assoc, Category.assoc, Category.assoc,
        morphismRestrict_ι, Scheme.Hom.liftCoborder_ι, morphismRestrict_ι_assoc, reassoc_of% hσ,
        reassoc_of% hq', reassoc_of% hq, hh]
    · rw [X.homOfLE_ι, reassoc_of% hσ, hπ]
  have : IsClosedImmersion q' :=
    IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion) O hO hloc
  have : IsImmersion q := by rw [← hq']; infer_instance
  have : IsProper π := by infer_instance
  have : IsDominant U.ι := ⟨by
    rw [DenseRange, Scheme.Opens.range_ι]
    exact U.isOpen.dense ⟨_, hU⟩⟩
  have : IsDominant (g.toImage ≫ π) := by rw [hπ]; infer_instance
  have : IsDominant π := IsDominant.of_comp g.toImage π
  have : QuasiCompact (q ≫ s) := by rw [← hπq]; infer_instance
  have : QuasiCompact q := QuasiCompact.of_comp q s
  obtain ⟨n, i₀, hi₀, e₀⟩ := hP
  exact ⟨g.image, π, inferInstance,
    surjective_of_isDominant_of_isClosed_range π π.isClosedMap.isClosed_range, n, q ≫ i₀,
    inferInstance, inferInstance, by rw [Category.assoc, e₀, hπq]⟩

end GlobalTheory.CompanionTheory.Ar.Approx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChowLemmaQuasiProjectiveStatement
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chow_lemma_quasi_projective : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), IsSeparated p → LocallyOfFiniteType p → QuasiCompact p → ∃ (X' : Scheme.{0}) (π : X' ⟶ X), IsProper π ∧ Surjective π ∧ IsQProjOver (π ≫ p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.exists_isProper_surjective_isQProjOver | exact GlobalTheory.CompanionTheory.Ar.Approx.exists_isProper_surjective_isQProjOver | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.exists_isProper_surjective_isQProjOver <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NoetherianIntegralClosedCover
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NoetherianIntegralClosedCover
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx


open TopologicalSpace in
theorem isIntegral_subscheme_vanishingIdeal {X : Scheme.{0}} (Z : Closeds X)
    (h : IsIrreducible (Z : Set X)) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  haveI : IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    GlobalTheory.ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
  have hr : Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = (Z : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  haveI : IrreducibleSpace (Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι) :=
    Subtype.irreducibleSpace (by rw [hr]; exact h)
  let f := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph
  haveI : IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    Function.Surjective.irreducibleSpace f.symm.continuous f.symm.surjective
  exact isIntegral_of_irreducibleSpace_of_isReduced _


open TopologicalSpace in
theorem exists_integral_closed_cover :
    ∀ (X : Scheme.{0}) [IsNoetherian X], ∃ (n : ℕ) (Z : Fin n → Scheme.{0}) (j : ∀ i, Z i ⟶ X),
      (∀ i, IsIntegral (Z i) ∧ IsClosedImmersion (j i)) ∧ ∀ x : X, ∃ i, x ∈ Set.range (j i) := by
  intro X _
  haveI : Finite (irreducibleComponents X) :=
    (finite_irreducibleComponents_of_isNoetherian (X := X)).to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (irreducibleComponents X)
  let C : Fin n → Closeds X := fun i =>
    ⟨(e.symm i).1, isClosed_of_mem_irreducibleComponents _ (e.symm i).2⟩
  refine ⟨n, fun i => (Scheme.IdealSheafData.vanishingIdeal (C i)).subscheme,
    fun i => (Scheme.IdealSheafData.vanishingIdeal (C i)).subschemeι,
    fun i => ⟨GlobalTheory.CompanionTheory.Ar.Approx.isIntegral_subscheme_vanishingIdeal (C i) (e.symm i).2.1, inferInstance⟩,
    fun x => ⟨e ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩⟩
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  show x ∈ (e.symm (e _)).1
  rw [Equiv.symm_apply_apply]
  exact mem_irreducibleComponent

end GlobalTheory.CompanionTheory.Ar.Approx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NoetherianIntegralClosedCoverStatement
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noetherian_integral_closed_cover : ∀ (X : Scheme.{0}) [IsNoetherian X], ∃ (n : ℕ) (Z : Fin n → Scheme.{0}) (j : ∀ i, Z i ⟶ X), (∀ i, IsIntegral (Z i) ∧ IsClosedImmersion (j i)) ∧ ∀ x : X, ∃ i, x ∈ Set.range (j i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.exists_integral_closed_cover | exact GlobalTheory.CompanionTheory.Ar.Approx.exists_integral_closed_cover | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.exists_integral_closed_cover <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.QuasiProjectiveProperCover
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem exists_proper_qproj_cover : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsSeparated p → LocallyOfFiniteType p → QuasiCompact p → ∃ (n : ℕ) (Y : Fin n → Scheme.{0}) (π : ∀ i, Y i ⟶ X), (∀ i, IsProper (π i) ∧ IsQProjOver (π i ≫ p)) ∧ ∀ x : X, ∃ i, x ∈ Set.range (π i) := by
  intro k _ _ X p hs hl hq
  have hLN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have hC : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have hN : IsNoetherian X := { }
  obtain ⟨n, Z, j, hj, hcov⟩ := GlobalTheory.T.noetherian_integral_closed_cover X
  have key : ∀ i, ∃ (X' : Scheme.{0}) (π : X' ⟶ Z i), IsProper π ∧ Surjective π ∧
      IsQProjOver (π ≫ j i ≫ p) := by
    intro i
    have := (hj i).1
    have := (hj i).2
    exact GlobalTheory.T.chow_lemma_quasi_projective k (Z i) (j i ≫ p) inferInstance inferInstance inferInstance
  choose Y π hp hsurj hqp using key
  refine ⟨n, Y, fun i => π i ≫ j i, fun i => ?_, fun x => ?_⟩
  · have := (hj i).2
    have := hp i
    refine ⟨inferInstance, ?_⟩
    rw [Category.assoc]
    exact hqp i
  · obtain ⟨i, z, rfl⟩ := hcov x
    obtain ⟨y, rfl⟩ := (hsurj i).surj z
    exact ⟨i, y, by simp⟩

end GlobalTheory.CompanionTheory.Ar.Approx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.QuasiProjectiveProperCoverStatement
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
theorem _root_.GlobalTheory.T.quasi_projective_proper_cover : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsSeparated p → LocallyOfFiniteType p → QuasiCompact p → ∃ (n : ℕ) (Y : Fin n → Scheme.{0}) (π : ∀ i, Y i ⟶ X), (∀ i, IsProper (π i) ∧ IsQProjOver (π i ≫ p)) ∧ ∀ x : X, ∃ i, x ∈ Set.range (π i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.exists_proper_qproj_cover | exact GlobalTheory.CompanionTheory.Ar.Approx.exists_proper_qproj_cover | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.exists_proper_qproj_cover <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PropernessDescendsFgSubalgebra
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFgIsClosedPreimageRange
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.Ar.Approx


open GlobalTheory.Spread GlobalTheory.SpreadSep in
theorem exists_fg_isClosed_preimage_range (k V : Type) [CommRing k] [IsNoetherianRing k] [CommRing V]
    [Algebra k V] (X P : Scheme.{0}) (j : X ⟶ P) (q : P ⟶ Sp k) (hj : IsImmersion j)
    (h₁ : LocallyOfFiniteType q) (h₂ : QuasiCompact q)
    (h : IsClosed (pullback.fst q (spMap (algebraMap k V)) ⁻¹' Set.range j)) :
    ∃ R : Subalgebra k V, R.FG ∧
      IsClosed (pullback.fst q (spMap (algebraMap k R)) ⁻¹' Set.range j) := by
  classical
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace ↥P := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian P := {}
  have : QuasiSeparated q := (quasiSeparated_iff_quasiSeparatedSpace q).mpr inferInstance
  obtain ⟨U, Z, hU, hZ, eΔ⟩ := j.isLocallyClosed_range
  let s : (Finset V)ᵒᵖ := .op ∅
  let π : (bcDiagram q V).obj s ⟶ P := pullback.fst q _
  have : QuasiCompact π := inferInstanceAs (QuasiCompact (pullback.fst q _))
  let O : P.Opens := ⟨U, hU⟩
  let O' : P.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
  have key : ((π ⁻¹ᵁ O : Set _) \ (π ⁻¹ᵁ O' : Set _)) = π ⁻¹' Set.range j := by
    rw [eΔ]
    ext x
    change π x ∈ U ∧ ¬ π x ∉ Z ↔ π x ∈ U ∧ π x ∈ Z
    rw [not_not]
  obtain ⟨i, f, hi⟩ := exists_isClosed_preimage_diff (bcDiagram q V) (bcCone q V) (isLimitBcCone q V)
    (π ⁻¹ᵁ O) (π ⁻¹ᵁ O')
    (QuasiCompact.isCompact_preimage (f := π) _ O.2 (TopologicalSpace.NoetherianSpace.isCompact _))
    (QuasiCompact.isCompact_preimage (f := π) _ O'.2 (TopologicalSpace.NoetherianSpace.isCompact _))
    (by
      have e : (bcCone q V).π.app s ≫ π = pullback.fst q _ := bcMap_fst _ _
      rw [key, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, e]
      exact h)
  refine ⟨Algebra.adjoin k (i.unop : Set V), Subalgebra.fg_adjoin_finset _, ?_⟩
  have e : (bcDiagram q V).map f ≫ π = pullback.fst q _ := bcMap_fst _ _
  rw [key, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, e] at hi
  exact hi

end GlobalTheory.CompanionTheory.Ar.Approx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PropernessDescendsFgSubalgebra
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

noncomputable def baseChangeMap {X P T B : Scheme.{0}} (i : X ⟶ P) (q : P ⟶ B) (g : T ⟶ B) :
    pullback (i ≫ q) g ⟶ pullback q g :=
  pullback.lift (pullback.fst (i ≫ q) g ≫ i) (pullback.snd (i ≫ q) g)
    (by rw [Category.assoc, pullback.condition])

theorem baseChangeMap_snd {X P T B : Scheme.{0}} (i : X ⟶ P) (q : P ⟶ B) (g : T ⟶ B) :
    baseChangeMap i q g ≫ pullback.snd q g = pullback.snd (i ≫ q) g :=
  pullback.lift_snd _ _ _

theorem baseChangeMap_fst {X P T B : Scheme.{0}} (i : X ⟶ P) (q : P ⟶ B) (g : T ⟶ B) :
    baseChangeMap i q g ≫ pullback.fst q g = pullback.fst (i ≫ q) g ≫ i :=
  pullback.lift_fst _ _ _

theorem isPullback_baseChangeMap {X P T B : Scheme.{0}} (i : X ⟶ P) (q : P ⟶ B) (g : T ⟶ B) :
    IsPullback (baseChangeMap i q g) (pullback.fst (i ≫ q) g) (pullback.fst q g) i := by
  refine IsPullback.of_right (h₁₂ := pullback.snd q g) (h₂₂ := q) (v₁₃ := g) ?_
    (baseChangeMap_fst i q g) (IsPullback.of_hasPullback q g).flip
  rw [baseChangeMap_snd]
  exact (IsPullback.of_hasPullback (i ≫ q) g).flip

theorem range_baseChangeMap {X P T B : Scheme.{0}} (i : X ⟶ P) (q : P ⟶ B) (g : T ⟶ B) :
    Set.range (baseChangeMap i q g) = pullback.fst q g ⁻¹' Set.range i := by
  have h := isPullback_baseChangeMap i q g
  rw [← Scheme.Pullback.range_fst, ← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, h.isoPullback.hom.surjective.range_eq, Set.image_univ]

theorem exists_fg_isProper_of_isQProjOver (k V : Type) [CommRing k] [IsNoetherianRing k] [CommRing V] [Algebra k V]
    (X : Scheme.{0}) (p : X ⟶ Sp k) (hp : IsQProjOver p)
    (hV : IsProper (pullback.snd p (spMap (algebraMap k V)))) :
    ∃ R : Subalgebra k V, R.FG ∧ IsProper (pullback.snd p (spMap (algebraMap k R))) := by
  obtain ⟨N, i, hi, -, rfl⟩ := hp
  have hq : IsProper (PSpace.str k N) := isProper_str k N

  have hcl : IsClosed (pullback.fst (PSpace.str k N) (spMap (algebraMap k V)) ⁻¹' Set.range i) := by
    rw [← range_baseChangeMap]
    have h1 : IsProper (baseChangeMap i (PSpace.str k N) (spMap (algebraMap k V)) ≫
        pullback.snd (PSpace.str k N) (spMap (algebraMap k V))) := by
      rw [baseChangeMap_snd]; exact hV
    have h2 : IsProper (baseChangeMap i (PSpace.str k N) (spMap (algebraMap k V))) :=
      IsProper.of_comp _ (pullback.snd (PSpace.str k N) (spMap (algebraMap k V)))
    exact (baseChangeMap i (PSpace.str k N) (spMap (algebraMap k V))).isClosedMap.isClosed_range
  obtain ⟨R, hR, hclR⟩ := exists_fg_isClosed_preimage_range k V X (PSpace k N) i (PSpace.str k N) hi inferInstance inferInstance hcl
  refine ⟨R, hR, ?_⟩
  rw [← range_baseChangeMap] at hclR
  have hb : IsImmersion (baseChangeMap i (PSpace.str k N) (spMap (algebraMap k R))) :=
    MorphismProperty.of_isPullback (P := @IsImmersion)
      (isPullback_baseChangeMap i (PSpace.str k N) (spMap (algebraMap k R))).flip hi
  have hc : IsClosedImmersion (baseChangeMap i (PSpace.str k N) (spMap (algebraMap k R))) :=
    IsClosedImmersion.of_isPreimmersion _ hclR
  rw [← baseChangeMap_snd]
  infer_instance

end GlobalTheory.CompanionTheory.Ar.Approx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PropernessDescendsFgSubalgebraStatement
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.properness_descends_fg_subalgebra : ∀ (k V : Type) [CommRing k] [IsNoetherianRing k] [CommRing V] [Algebra k V] (X : Scheme.{0}) (p : X ⟶ Sp k), IsQProjOver p → IsProper (pullback.snd p (spMap (algebraMap k V))) → ∃ R : Subalgebra k V, R.FG ∧ IsProper (pullback.snd p (spMap (algebraMap k R))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.exists_fg_isProper_of_isQProjOver | exact GlobalTheory.CompanionTheory.Ar.Approx.exists_fg_isProper_of_isQProjOver | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.exists_fg_isProper_of_isQProjOver <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperOfProperCover
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperOfProperCover
open CategoryTheory AlgebraicGeometry Limits

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem isProper_of_finite_cover (X S : Scheme.{0}) (p : X ⟶ S) (n : ℕ) (Y : Fin n → Scheme.{0})
    (π : ∀ i, Y i ⟶ X) (hsep : IsSeparated p) (hft : LocallyOfFiniteType p)
    (hprop : ∀ i, IsProper (π i ≫ p)) (hcov : ∀ x : X, ∃ i, x ∈ Set.range (π i)) :
    IsProper p := by
  have huc : UniversallyClosed p := by
    constructor
    intro X' Y' i₁ i₂ f' hpb Z hZ
    have hW : ∀ i, IsPullback (pullback.fst i₁ (π i) ≫ f') (pullback.snd i₁ (π i)) i₂
        (π i ≫ p) := fun i => (IsPullback.of_hasPullback i₁ (π i)).paste_horiz hpb
    have hc : ∀ i, IsClosedMap ⇑(pullback.fst i₁ (π i) ≫ f') := fun i =>
      @UniversallyClosed.universally_isClosedMap _ _ _ (hprop i).toUniversallyClosed
        _ _ _ _ _ (hW i)
    have key : ⇑f' '' Z =
        ⋃ i, ⇑(pullback.fst i₁ (π i) ≫ f') '' (⇑(pullback.fst i₁ (π i)) ⁻¹' Z) := by
      ext y
      simp only [Set.mem_image, Set.mem_iUnion, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨i, y', hy'⟩ := hcov (i₁ x)
        obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback x y' hy'.symm
        refine ⟨i, w, ?_, ?_⟩
        · rw [hw]
          exact hx
        · show f' (pullback.fst i₁ (π i) w) = f' x
          rw [hw]
      · rintro ⟨i, w, hw, rfl⟩
        exact ⟨pullback.fst i₁ (π i) w, hw, rfl⟩
    convert isClosed_iUnion_of_finite fun i =>
      hc i _ (hZ.preimage (pullback.fst i₁ (π i)).continuous) using 1
  exact @IsProper.mk _ _ _ hsep huc hft

end GlobalTheory.CompanionTheory.Ar.Approx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperOfProperCoverStatement
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_of_proper_cover : ∀ (X S : Scheme.{0}) (p : X ⟶ S) (n : ℕ) (Y : Fin n → Scheme.{0}) (π : ∀ i, Y i ⟶ X), IsSeparated p → LocallyOfFiniteType p → (∀ i, IsProper (π i ≫ p)) → (∀ x : X, ∃ i, x ∈ Set.range (π i)) → IsProper p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.isProper_of_finite_cover | exact GlobalTheory.CompanionTheory.Ar.Approx.isProper_of_finite_cover | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.isProper_of_finite_cover <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SeparatedPropernessFgSubalgebra
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

noncomputable def baseMap {Y X S T : Scheme.{0}} (π : Y ⟶ X) (p : X ⟶ S) (f : T ⟶ S) :
    pullback (π ≫ p) f ⟶ pullback p f :=
  pullback.lift (pullback.fst _ _ ≫ π) (pullback.snd _ _) (by simp [pullback.condition])

theorem baseMap_snd {Y X S T : Scheme.{0}} (π : Y ⟶ X) (p : X ⟶ S) (f : T ⟶ S) :
    baseMap π p f ≫ pullback.snd p f = pullback.snd (π ≫ p) f :=
  pullback.lift_snd _ _ _

theorem baseMap_isPullback {Y X S T : Scheme.{0}} (π : Y ⟶ X) (p : X ⟶ S) (f : T ⟶ S) :
    IsPullback (baseMap π p f) (pullback.fst (π ≫ p) f) (pullback.fst p f) π := by
  refine IsPullback.of_right (h₁₂ := pullback.snd p f) (h₂₂ := p) (v₁₃ := f) ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback p f).flip
  rw [baseMap_snd]
  exact (IsPullback.of_hasPullback (π ≫ p) f).flip

theorem isProper_snd_comp {Y X S T : Scheme.{0}} (π : Y ⟶ X) (p : X ⟶ S) (f : T ⟶ S)
    [IsProper π] [IsProper (pullback.snd p f)] : IsProper (pullback.snd (π ≫ p) f) := by
  have : IsProper (baseMap π p f) :=
    MorphismProperty.of_isPullback (P := @IsProper) (baseMap_isPullback π p f).flip inferInstance
  rw [← baseMap_snd π p f]
  infer_instance

theorem isProper_snd_of_comp {X S T T' : Scheme.{0}} (q : X ⟶ S) (f : T ⟶ S) (h : T' ⟶ T)
    [IsProper (pullback.snd q f)] : IsProper (pullback.snd q (h ≫ f)) := by
  let g : pullback q (h ≫ f) ⟶ pullback q f :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ h) (by simp [pullback.condition])
  have hg : g ≫ pullback.fst q f = pullback.fst q (h ≫ f) :=
    pullback.lift_fst _ _ _
  have hsq : IsPullback g (pullback.snd q (h ≫ f)) (pullback.snd q f) h := by
    refine IsPullback.of_right (h₁₂ := pullback.fst q f) (h₂₂ := f) (v₁₃ := q) ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback q f)
    rw [hg]
    exact IsPullback.of_hasPullback q (h ≫ f)
  exact MorphismProperty.of_isPullback (P := @IsProper) hsq inferInstance

theorem mem_range_baseMap {Y X S T : Scheme.{0}} (π : Y ⟶ X) (p : X ⟶ S) (f : T ⟶ S)
    (x : ↥(pullback p f)) (h : pullback.fst p f x ∈ Set.range π) :
    x ∈ Set.range (baseMap π p f) := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.fst p f) (g := π) x y hy.symm
  have hpb := baseMap_isPullback π p f
  refine ⟨hpb.isoPullback.inv z, ?_⟩
  rw [← Scheme.Hom.comp_apply, hpb.isoPullback_inv_fst, hz]

theorem isProper_descends (k V : Type) [CommRing k] [IsNoetherianRing k] [CommRing V] [Algebra k V]
    (X : Scheme.{0}) (p : X ⟶ Sp k) (hs : IsSeparated p) (hl : LocallyOfFiniteType p)
    (hq : QuasiCompact p) (hP : IsProper (pullback.snd p (spMap (algebraMap k V)))) :
    ∃ R : Subalgebra k V, R.FG ∧ IsProper (pullback.snd p (spMap (algebraMap k R))) := by
  obtain ⟨n, Y, π, hπ, hcov⟩ := GlobalTheory.T.quasi_projective_proper_cover k X p hs hl hq
  have hi : ∀ i, ∃ R : Subalgebra k V, R.FG ∧
      IsProper (pullback.snd (π i ≫ p) (spMap (algebraMap k R))) := by
    intro i
    have := (hπ i).1
    exact GlobalTheory.T.properness_descends_fg_subalgebra k V (Y i) (π i ≫ p) (hπ i).2 (isProper_snd_comp (π i) p _)
  choose Ri hRfg hRp using hi
  let R : Subalgebra k V := Finset.univ.sup Ri
  have hFG : R.FG :=
    Finset.sup_induction (p := Subalgebra.FG) Subalgebra.fg_bot (fun _ h _ h' => h.sup h')
      (fun i _ => hRfg i)
  refine ⟨R, hFG, ?_⟩
  have hle : ∀ i, Ri i ≤ R := fun i => Finset.le_sup (Finset.mem_univ i)
  have hmap : ∀ i, spMap (algebraMap k R) =
      spMap (Subalgebra.inclusion (hle i)).toRingHom ≫ spMap (algebraMap k (Ri i)) := by
    intro i
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  have hprop : ∀ i, IsProper (pullback.snd (π i ≫ p) (spMap (algebraMap k R))) := by
    intro i
    have := hRp i
    rw [hmap i]
    exact isProper_snd_of_comp _ _ _
  refine GlobalTheory.T.proper_of_proper_cover (pullback p (spMap (algebraMap k R))) (Sp R)
    (pullback.snd p (spMap (algebraMap k R))) n
    (fun i => pullback (π i ≫ p) (spMap (algebraMap k R)))
    (fun i => baseMap (π i) p (spMap (algebraMap k R))) inferInstance inferInstance ?_ ?_
  · intro i
    rw [baseMap_snd]
    exact hprop i
  · intro x
    obtain ⟨i, hi⟩ := hcov (pullback.fst p (spMap (algebraMap k R)) x)
    exact ⟨i, mem_range_baseMap _ _ _ x hi⟩

end GlobalTheory.CompanionTheory.Ar.Approx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SeparatedPropernessFgSubalgebraStatement
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
theorem _root_.GlobalTheory.T.separated_properness_fg_subalgebra : ∀ (k V : Type) [CommRing k] [IsNoetherianRing k] [CommRing V] [Algebra k V] (X : Scheme.{0}) (p : X ⟶ Sp k), IsSeparated p → LocallyOfFiniteType p → QuasiCompact p → IsProper (pullback.snd p (spMap (algebraMap k V))) → ∃ R : Subalgebra k V, R.FG ∧ IsProper (pullback.snd p (spMap (algebraMap k R))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.isProper_descends | exact GlobalTheory.CompanionTheory.Ar.Approx.isProper_descends | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.isProper_descends <;> assumption)
end
