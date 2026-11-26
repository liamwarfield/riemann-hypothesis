module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.ClopProjFiniteEtaleOfIsClosed

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsClopRepOfIsSplitOfRank
section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsClopRepOfDisjointOpenCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace UpperTheory.ClopSum

variable {S : Scheme.{0}}

private theorem isPullback_wl (T : Over S) {A B : Over S} (i : A ⟶ B) :
    IsPullback (T ◁ i).left (snd T A).left (snd T B).left i.left := by
  have eq1 : (T ◁ i).left ≫ (fst T B).left = (fst T A).left := Over.whiskerLeft_left_fst i
  have eq2 : i.left ≫ B.hom = A.hom := Over.w i
  have s : IsPullback ((T ◁ i).left ≫ (fst T B).left) (snd T A).left T.hom (i.left ≫ B.hom) := by
    rw [eq1, eq2]
    exact IsPullback.of_hasPullback T.hom A.hom
  exact IsPullback.of_right s (Over.whiskerLeft_left_snd i) (IsPullback.of_hasPullback T.hom B.hom)

private theorem range_wl (T : Over S) {A B : Over S} (i : A ⟶ B) :
    Set.range (T ◁ i).left = (snd T B).left ⁻¹' Set.range i.left := by
  have h := isPullback_wl T i
  rw [← Scheme.Pullback.range_fst, ← h.isoPullback_hom_fst]
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨h.isoPullback.hom a, rfl⟩
  · rintro ⟨b, rfl⟩
    refine ⟨h.isoPullback.inv b, ?_⟩
    show (h.isoPullback.inv ≫ h.isoPullback.hom ≫ pullback.fst _ _) b = _
    rw [Iso.inv_hom_id_assoc]

private theorem opens_ext {C A₁ A₂ : Scheme.{0}} (j₁ : A₁ ⟶ C) (j₂ : A₂ ⟶ C)
    (hr : Set.range j₁ = (Set.range j₂)ᶜ) {V V' : C.Opens}
    (h₁ : j₁ ⁻¹ᵁ V = j₁ ⁻¹ᵁ V') (h₂ : j₂ ⁻¹ᵁ V = j₂ ⁻¹ᵁ V') : V = V' := by
  ext x
  by_cases hx : x ∈ Set.range j₁
  · obtain ⟨a, rfl⟩ := hx
    have := SetLike.ext_iff.mp h₁ a
    simpa using this
  · have hx2 : x ∈ Set.range j₂ := by
      rw [hr] at hx
      simpa using hx
    obtain ⟨b, rfl⟩ := hx2
    have := SetLike.ext_iff.mp h₂ b
    simpa using this

private theorem glue {C A₁ A₂ : Scheme.{0}} (j₁ : A₁ ⟶ C) (j₂ : A₂ ⟶ C)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] (hr : Set.range j₁ = (Set.range j₂)ᶜ)
    (V₁ : A₁.Opens) (V₂ : A₂.Opens) (h₁ : IsClosed (V₁ : Set A₁)) (h₂ : IsClosed (V₂ : Set A₂)) :
    ∃ V : C.Opens, IsClosed (V : Set C) ∧ j₁ ⁻¹ᵁ V = V₁ ∧ j₂ ⁻¹ᵁ V = V₂ := by
  have hc1 : IsClosed (Set.range j₁) := by
    rw [hr]
    exact j₂.isOpenEmbedding.isOpen_range.isClosed_compl
  have hc2 : IsClosed (Set.range j₂) := by
    have e : Set.range j₂ = (Set.range j₁)ᶜ := by rw [hr, compl_compl]
    rw [e]
    exact j₁.isOpenEmbedding.isOpen_range.isClosed_compl
  have e1 : Topology.IsClosedEmbedding j₁ := ⟨j₁.isOpenEmbedding.isEmbedding, hc1⟩
  have e2 : Topology.IsClosedEmbedding j₂ := ⟨j₂.isOpenEmbedding.isEmbedding, hc2⟩
  have hopen : IsOpen (j₁ '' (V₁ : Set A₁) ∪ j₂ '' (V₂ : Set A₂)) :=
    (j₁.isOpenEmbedding.isOpenMap _ V₁.isOpen).union (j₂.isOpenEmbedding.isOpenMap _ V₂.isOpen)
  refine ⟨⟨_, hopen⟩, (e1.isClosedMap _ h₁).union (e2.isClosedMap _ h₂), ?_, ?_⟩
  · ext a
    show j₁ a ∈ j₁ '' (V₁ : Set A₁) ∪ j₂ '' (V₂ : Set A₂) ↔ a ∈ V₁
    constructor
    · rintro (⟨a', ha', he⟩ | ⟨b, hb, he⟩)
      · rw [← j₁.isOpenEmbedding.injective he]
        exact ha'
      · exfalso
        have hm : j₁ a ∈ Set.range j₁ := ⟨a, rfl⟩
        rw [hr] at hm
        exact hm ⟨b, he⟩
    · intro ha
      exact Or.inl ⟨a, ha, rfl⟩
  · ext b
    show j₂ b ∈ j₁ '' (V₁ : Set A₁) ∪ j₂ '' (V₂ : Set A₂) ↔ b ∈ V₂
    constructor
    · rintro (⟨a, ha, he⟩ | ⟨b', hb', he⟩)
      · exfalso
        have hm : j₂ b ∈ Set.range j₁ := ⟨a, he⟩
        rw [hr] at hm
        exact hm ⟨b, rfl⟩
      · rw [← j₂.isOpenEmbedding.injective he]
        exact hb'
    · intro hb
      exact Or.inr ⟨b, hb, rfl⟩

end UpperTheory.ClopSum

private theorem UpperTheory.preimage_comp_scheme_opens {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (W : Z.Opens) :
    (f ≫ g) ⁻¹ᵁ W = f ⁻¹ᵁ (g ⁻¹ᵁ W) := by
  simp

private theorem UpperTheory.preimage_whisker_left_right_comm {S : Scheme.{0}} {T Y G' G : Over S} (y : T ⟶ Y) (i : G' ⟶ G)
    (W : (Y ⊗ G).left.Opens) :
    (T ◁ i).left ⁻¹ᵁ ((y ▷ G).left ⁻¹ᵁ W) = (y ▷ G').left ⁻¹ᵁ ((Y ◁ i).left ⁻¹ᵁ W) := by
  rw [← UpperTheory.preimage_comp_scheme_opens, ← UpperTheory.preimage_comp_scheme_opens, ← Over.comp_left, ← Over.comp_left,
    whisker_exchange]

private theorem UpperTheory.preimage_whiskerRight_whiskerRight_comp {S : Scheme.{0}} {T Y Z G : Over S} (y : T ⟶ Y) (f : Y ⟶ Z)
    (W : (Z ⊗ G).left.Opens) :
    (y ▷ G).left ⁻¹ᵁ ((f ▷ G).left ⁻¹ᵁ W) = ((y ≫ f) ▷ G).left ⁻¹ᵁ W := by
  rw [← UpperTheory.preimage_comp_scheme_opens, ← Over.comp_left, comp_whiskerRight]

open UpperTheory.ClopSum in
theorem UpperTheory.exists_clopRep_of_disjoint_open_cover :
    ∀ {S : Scheme.{0}} (G G₁ G₂ Y₁ Y₂ : Over S) (i₁ : G₁ ⟶ G) (i₂ : G₂ ⟶ G) (U₁ : (Y₁ ⊗ G₁).left.Opens) (U₂ : (Y₂ ⊗ G₂).left.Opens), IsOpenImmersion i₁.left → IsOpenImmersion i₂.left → Set.range i₁.left = (Set.range i₂.left)ᶜ → UpperTheory.RepresentationRank.Rep G₁ Y₁ U₁ → UpperTheory.RepresentationRank.Rep G₂ Y₂ U₂ → ∃ U : ((Y₁ ⊗ Y₂) ⊗ G).left.Opens, UpperTheory.RepresentationRank.Rep G (Y₁ ⊗ Y₂) U := by
  intro S G G₁ G₂ Y₁ Y₂ i₁ i₂ U₁ U₂ ho₁ ho₂ hr hU₁ hU₂
  have o1 : ∀ T : Over S, IsOpenImmersion (T ◁ i₁).left := fun T =>
    MorphismProperty.of_isPullback (UpperTheory.ClopSum.isPullback_wl T i₁).flip ho₁
  have o2 : ∀ T : Over S, IsOpenImmersion (T ◁ i₂).left := fun T =>
    MorphismProperty.of_isPullback (UpperTheory.ClopSum.isPullback_wl T i₂).flip ho₂
  have rr : ∀ T : Over S, Set.range (T ◁ i₁).left = (Set.range (T ◁ i₂).left)ᶜ := by
    intro T
    rw [UpperTheory.ClopSum.range_wl, UpperTheory.ClopSum.range_wl, hr]
    rfl
  haveI := o1 (Y₁ ⊗ Y₂)
  haveI := o2 (Y₁ ⊗ Y₂)
  obtain ⟨U, hUc, hU1, hU2⟩ := UpperTheory.ClopSum.glue ((Y₁ ⊗ Y₂) ◁ i₁).left ((Y₁ ⊗ Y₂) ◁ i₂).left
    (rr _) ((fst Y₁ Y₂ ▷ G₁).left ⁻¹ᵁ U₁) ((snd Y₁ Y₂ ▷ G₂).left ⁻¹ᵁ U₂)
    (hU₁.1.preimage (Scheme.Hom.continuous _)) (hU₂.1.preimage (Scheme.Hom.continuous _))
  refine ⟨U, hUc, ?_⟩
  intro T V hV
  have c1 : ∀ y : T ⟶ Y₁ ⊗ Y₂,
      (T ◁ i₁).left ⁻¹ᵁ ((y ▷ G).left ⁻¹ᵁ U) = ((y ≫ fst Y₁ Y₂) ▷ G₁).left ⁻¹ᵁ U₁ := by
    intro y
    rw [UpperTheory.preimage_whisker_left_right_comm, hU1, UpperTheory.preimage_whiskerRight_whiskerRight_comp]
  have c2 : ∀ y : T ⟶ Y₁ ⊗ Y₂,
      (T ◁ i₂).left ⁻¹ᵁ ((y ▷ G).left ⁻¹ᵁ U) = ((y ≫ snd Y₁ Y₂) ▷ G₂).left ⁻¹ᵁ U₂ := by
    intro y
    rw [UpperTheory.preimage_whisker_left_right_comm, hU2, UpperTheory.preimage_whiskerRight_whiskerRight_comp]
  obtain ⟨y₁, hy₁, hu₁⟩ := hU₁.2 T ((T ◁ i₁).left ⁻¹ᵁ V) (hV.preimage (Scheme.Hom.continuous _))
  obtain ⟨y₂, hy₂, hu₂⟩ := hU₂.2 T ((T ◁ i₂).left ⁻¹ᵁ V) (hV.preimage (Scheme.Hom.continuous _))
  refine ⟨lift y₁ y₂, ?_, ?_⟩
  · show ((lift y₁ y₂) ▷ G).left ⁻¹ᵁ U = V
    apply UpperTheory.ClopSum.opens_ext (T ◁ i₁).left (T ◁ i₂).left (rr T)
    · rw [c1, lift_fst]
      exact hy₁
    · rw [c2, lift_snd]
      exact hy₂
  · intro y hy
    have hy' : (y ▷ G).left ⁻¹ᵁ U = V := hy
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst]
      exact hu₁ _ (by
        show ((y ≫ fst Y₁ Y₂) ▷ G₁).left ⁻¹ᵁ U₁ = _
        rw [← c1, hy'])
    · rw [lift_snd]
      exact hu₂ _ (by
        show ((y ≫ snd Y₁ Y₂) ▷ G₂).left ⁻¹ᵁ U₂ = _
        rw [← c2, hy'])
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsClopRepTrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace UpperTheory.TwoTorsionInclusion

private noncomputable abbrev Two (S : Scheme.{0}) : Scheme.{0} := ∐ fun _ : Fin 2 ↦ S

private noncomputable abbrev inc (S : Scheme.{0}) (i : Fin 2) : S ⟶ Two S :=
  Sigma.ι (fun _ : Fin 2 ↦ S) i

private noncomputable abbrev cd (S : Scheme.{0}) : Two S ⟶ S := Sigma.desc fun _ ↦ 𝟙 S

private lemma mem_zero_iff (S : Scheme.{0}) (x : Two S) :
    x ∈ (inc S 0).opensRange ↔ x ∉ (inc S 1).opensRange := by
  obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk (fun _ : Fin 2 ↦ S)).surjective x
  simp only [sigmaMk_mk, Scheme.Hom.mem_opensRange, inc, sigmaι_eq_iff]
  fin_cases i <;> simp

private lemma isClosed_one (S : Scheme.{0}) : IsClosed ((inc S 1).opensRange : Set (Two S)) := by
  rw [← isOpen_compl_iff]
  have : ((inc S 1).opensRange : Set (Two S))ᶜ = ((inc S 0).opensRange : Set (Two S)) := by
    ext x
    exact (mem_zero_iff S x).symm
  rw [this]
  exact (inc S 0).opensRange.isOpen

private lemma restrict_eq {S X Z : Scheme.{0}} (y : X ⟶ Two S) (i : Fin 2) (j : Z ⟶ X)
    (h : ∀ z, y (j z) ∈ (inc S i).opensRange) : j ≫ y = j ≫ y ≫ cd S ≫ inc S i := by
  have hr : Set.range (j ≫ y).base ⊆ Set.range (inc S i).base := by
    rintro _ ⟨z, rfl⟩
    exact h z
  set L := IsOpenImmersion.lift (inc S i) (j ≫ y) hr
  have e : L ≫ inc S i = j ≫ y := IsOpenImmersion.lift_fac _ _ _
  rw [← reassoc_of% e, ← e]
  simp [inc, cd]

private lemma core {S X : Scheme.{0}} (f : X ⟶ S) (W : X.Opens) (hW : IsClosed (W : Set X)) :
    ∃! y : X ⟶ Two S, y ≫ cd S = f ∧ y ⁻¹ᵁ (inc S 1).opensRange = W := by
  let W' : X.Opens := ⟨(W : Set X)ᶜ, hW.isOpen_compl⟩
  have hc : IsCompl W'.ι.opensRange W.ι.opensRange := by
    simp only [Scheme.Opens.opensRange_ι]
    constructor
    · rw [disjoint_iff, ← SetLike.coe_set_eq]
      ext x
      simp [W']
    · rw [codisjoint_iff, ← SetLike.coe_set_eq]
      ext x
      simp [W']
  obtain ⟨hcol⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl W'.ι W.ι hc
  have ext : ∀ {T : Scheme.{0}} (a b : X ⟶ T), W'.ι ≫ a = W'.ι ≫ b → W.ι ≫ a = W.ι ≫ b → a = b :=
    fun a b h0 h1 ↦ BinaryCofan.IsColimit.hom_ext hcol h0 h1
  have key : ∀ y' : X ⟶ Two S, y' ≫ cd S = f → y' ⁻¹ᵁ (inc S 1).opensRange = W →
      W'.ι ≫ y' = W'.ι ≫ f ≫ inc S 0 ∧ W.ι ≫ y' = W.ι ≫ f ≫ inc S 1 := by
    intro y' h1 h2
    constructor
    · rw [restrict_eq y' 0 W'.ι, reassoc_of% h1]
      intro z
      rw [mem_zero_iff]
      intro hz
      have hm : W'.ι z ∈ y' ⁻¹ᵁ (inc S 1).opensRange := hz
      rw [h2] at hm
      have hz' : z.1 ∉ W := z.2
      exact hz' hm
    · rw [restrict_eq y' 1 W.ι, reassoc_of% h1]
      intro z
      have hm : W.ι z ∈ y' ⁻¹ᵁ (inc S 1).opensRange := by
        rw [h2]
        exact z.2
      exact hm
  obtain ⟨y0, hy0, hy1⟩ := BinaryCofan.IsColimit.desc' hcol (W'.ι ≫ f ≫ inc S 0) (W.ι ≫ f ≫ inc S 1)
  obtain ⟨y, rfl⟩ : ∃ y : X ⟶ Two S, y = y0 := ⟨y0, rfl⟩
  change W'.ι ≫ y = _ at hy0
  change W.ι ≫ y = _ at hy1
  refine ⟨y, ⟨ext (y ≫ cd S) f (by rw [reassoc_of% hy0]; simp [inc, cd])
    (by rw [reassoc_of% hy1]; simp [inc, cd]), ?_⟩, ?_⟩
  · ext x
    by_cases hx : x ∈ W
    · obtain ⟨z, rfl⟩ : ∃ z : W.toScheme, W.ι z = x := ⟨⟨x, hx⟩, rfl⟩
      have e : y (W.ι z) = inc S 1 (f (W.ι z)) := by
        rw [show y (W.ι z) = (W.ι ≫ y) z from rfl, hy1] <;> rfl
      refine iff_of_true ?_ hx
      show y (W.ι z) ∈ (inc S 1).opensRange
      rw [e]
      exact ⟨_, rfl⟩
    · obtain ⟨z, rfl⟩ : ∃ z : W'.toScheme, W'.ι z = x := ⟨⟨x, hx⟩, rfl⟩
      have e : y (W'.ι z) = inc S 0 (f (W'.ι z)) := by
        rw [show y (W'.ι z) = (W'.ι ≫ y) z from rfl, hy0] <;> rfl
      refine iff_of_false ?_ hx
      show y (W'.ι z) ∉ (inc S 1).opensRange
      rw [e, ← mem_zero_iff]
      exact ⟨_, rfl⟩
  · rintro y' ⟨h1, h2⟩
    obtain ⟨k0, k1⟩ := key y' h1 h2
    exact ext _ _ (k0.trans hy0.symm) (k1.trans hy1.symm)

private lemma isIso_fst {S : Scheme.{0}} (T : Over S) : IsIso (fst T (Over.mk (𝟙 S))) := by
  have ht : IsTerminal (Over.mk (𝟙 S)) := Over.mkIdTerminal
  refine ⟨⟨lift (𝟙 T) (ht.from T), ?_, by simp⟩⟩
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · exact ht.hom_ext _ _

end UpperTheory.TwoTorsionInclusion

open UpperTheory.TwoTorsionInclusion in
theorem UpperTheory.exists_clopRep_trivial :
    ∀ (S : Scheme.{0}), ∃ (Y : Over S) (U : (Y ⊗ Over.mk (𝟙 S)).left.Opens), UpperTheory.RepresentationRank.Rep (Over.mk (𝟙 S)) Y U ∧ IsFinite Y.hom ∧ Etale Y.hom := by
  intro S
  refine ⟨Over.mk (cd S), (fst (Over.mk (cd S)) (Over.mk (𝟙 S))).left ⁻¹ᵁ (inc S 1).opensRange,
    ⟨(isClosed_one S).preimage (Scheme.Hom.continuous _), ?_⟩,
    (GlobalTheory.FinEt.isSplitOfRank_sigmaDesc S 2).isFinite, (GlobalTheory.FinEt.isSplitOfRank_sigmaDesc S 2).etale⟩
  intro T V hV
  have hiso : IsIso (fst T (Over.mk (𝟙 S))).left := by
    have := isIso_fst T
    exact (inferInstance : IsIso ((Over.forget S).map (fst T (Over.mk (𝟙 S)))))
  set φ := (fst T (Over.mk (𝟙 S))).left with hφ
  have h1 : ∀ x, inv φ (φ x) = x := fun x ↦ by
    rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
    rfl
  have h2 : ∀ t, φ (inv φ t) = t := fun t ↦ by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  have hpre : ∀ (y : T ⟶ Over.mk (cd S)) x,
      x ∈ (y ▷ Over.mk (𝟙 S)).left ⁻¹ᵁ
        ((fst (Over.mk (cd S)) (Over.mk (𝟙 S))).left ⁻¹ᵁ (inc S 1).opensRange) ↔
        y.left (φ x) ∈ (inc S 1).opensRange := by
    intro y x
    show (fst (Over.mk (cd S)) (Over.mk (𝟙 S))).left ((y ▷ Over.mk (𝟙 S)).left x) ∈
      (inc S 1).opensRange ↔ _
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, whiskerRight_fst, Over.comp_left,
      Scheme.Hom.comp_apply]
  let W : T.left.Opens := (inv φ) ⁻¹ᵁ V
  have hW : IsClosed (W : Set T.left) := hV.preimage (Scheme.Hom.continuous _)
  have hiff : ∀ y : T ⟶ Over.mk (cd S), (y ▷ Over.mk (𝟙 S)).left ⁻¹ᵁ
      ((fst (Over.mk (cd S)) (Over.mk (𝟙 S))).left ⁻¹ᵁ (inc S 1).opensRange) = V ↔
      y.left ⁻¹ᵁ (inc S 1).opensRange = W := by
    intro y
    constructor
    · intro h
      refine SetLike.ext fun t ↦ ?_
      show y.left t ∈ (inc S 1).opensRange ↔ inv φ t ∈ V
      rw [← h, hpre, h2]
    · intro h
      refine SetLike.ext fun x ↦ ?_
      rw [hpre]
      show φ x ∈ y.left ⁻¹ᵁ (inc S 1).opensRange ↔ x ∈ V
      rw [h]
      show inv φ (φ x) ∈ V ↔ x ∈ V
      rw [h1]
  obtain ⟨y0, ⟨e0, e1⟩, hu⟩ := core T.hom W hW
  refine ⟨Over.homMk y0 e0, (hiff _).2 e1, fun y hy ↦ ?_⟩
  exact Over.OverMorphism.ext (hu y.left ⟨Over.w y, (hiff y).1 hy⟩)
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

private lemma tensor_fe {S : Scheme.{0}} (Y₁ Y₂ : Over S) (h1 : IsFinite Y₁.hom) (e1 : Etale Y₁.hom)
    (h2 : IsFinite Y₂.hom) (e2 : Etale Y₂.hom) :
    IsFinite (Y₁ ⊗ Y₂).hom ∧ Etale (Y₁ ⊗ Y₂).hom := by
  have hY : (Y₁ ⊗ Y₂).hom = pullback.fst Y₁.hom Y₂.hom ≫ Y₁.hom := rfl
  rw [hY]
  exact ⟨inferInstance, inferInstance⟩

private lemma rep_empty {S : Scheme.{0}} (G : Over S) (hG : IsEmpty G.left) :
    UpperTheory.RepresentationRank.Rep G (Over.mk (𝟙 S)) (⊥ : ((Over.mk (𝟙 S)) ⊗ G).left.Opens) := by
  refine ⟨by simp, fun T V _ => ?_⟩
  have hE : IsEmpty (T ⊗ G).left := ⟨fun x => hG.false ((CartesianMonoidalCategory.snd T G).left x)⟩
  have hV : V = ⊥ := by
    ext x
    exact hE.elim x
  subst hV
  refine ⟨Over.homMk T.hom (by simp), ?_, ?_⟩
  · ext x
    exact hE.elim x
  · intro y _
    ext
    simpa using Over.w y

theorem UpperTheory.exists_clopRep_of_isSplitOfRank :
    ∀ {S : Scheme.{0}} (G : Over S) (n : ℕ), GlobalTheory.FinEt.IsSplitOfRank G.hom n → ∃ (Y : Over S) (U : (Y ⊗ G).left.Opens), UpperTheory.RepresentationRank.Rep G Y U ∧ IsFinite Y.hom ∧ Etale Y.hom := by
  intro S G n
  induction n generalizing G with
  | zero =>
    intro h
    have hG : IsEmpty G.left := (GlobalTheory.FinEt.isSplitOfRank_zero_iff G.hom).1 h
    refine ⟨Over.mk (𝟙 S), ⊥, rep_empty G hG, ?_, ?_⟩
    · show IsFinite (𝟙 S)
      infer_instance
    · show Etale (𝟙 S)
      infer_instance
  | succ n ih =>
    intro h
    obtain ⟨σ, hσ, V, hσp, hrange, hV⟩ := h.exists_of_succ
    obtain ⟨Y₁, U₁, hR₁, hf₁, he₁⟩ := UpperTheory.exists_clopRep_trivial S
    obtain ⟨Y₂, U₂, hR₂, hf₂, he₂⟩ := ih (Over.mk (V.ι ≫ G.hom)) hV
    obtain ⟨U, hU⟩ := UpperTheory.exists_clopRep_of_disjoint_open_cover G (Over.mk (𝟙 S)) (Over.mk (V.ι ≫ G.hom)) Y₁ Y₂
      (Over.homMk σ hσp) (Over.homMk V.ι rfl) U₁ U₂ hσ (show IsOpenImmersion V.ι from inferInstance)
      (show Set.range σ = (Set.range V.ι)ᶜ by rw [hrange, compl_compl]) hR₁ hR₂
    exact ⟨Y₁ ⊗ Y₂, U, hU, tensor_fe Y₁ Y₂ hf₁ he₁ hf₂ he₂⟩
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ClopRepUnique
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

private theorem UpperTheory.preimage_whiskerRight_comp_over {S : Scheme.{0}} {A B C G : Over S} (f : A ⟶ B) (g : B ⟶ C)
    (W : (C ⊗ G).left.Opens) :
    ((f ≫ g) ▷ G).left ⁻¹ᵁ W = (f ▷ G).left ⁻¹ᵁ ((g ▷ G).left ⁻¹ᵁ W) := by
  simp

theorem UpperTheory.clopRep_unique :
    ∀ {S : Scheme.{0}} (G Y Y' : Over S) (U : (Y ⊗ G).left.Opens) (U' : (Y' ⊗ G).left.Opens), UpperTheory.RepresentationRank.Rep G Y U → UpperTheory.RepresentationRank.Rep G Y' U' → Nonempty (Y ≅ Y') := by
  intro S G Y Y' U U' hU hU'
  obtain ⟨φ, hφ, -⟩ := hU'.2 Y U hU.1
  obtain ⟨ψ, hψ, -⟩ := hU.2 Y' U' hU'.1
  have hid : ∀ {Z : Over S} (W : (Z ⊗ G).left.Opens), ((𝟙 Z) ▷ G).left ⁻¹ᵁ W = W := by
    intro Z W
    simp
  have e1 : φ ≫ ψ = 𝟙 Y := by
    obtain ⟨y, -, huniq⟩ := hU.2 Y U hU.1
    have a := huniq (φ ≫ ψ) (by
      show ((φ ≫ ψ) ▷ G).left ⁻¹ᵁ U = U
      rw [UpperTheory.preimage_whiskerRight_comp_over, hψ, hφ])
    have b := huniq (𝟙 Y) (hid U)
    rw [a, b]
  have e2 : ψ ≫ φ = 𝟙 Y' := by
    obtain ⟨y, -, huniq⟩ := hU'.2 Y' U' hU'.1
    have a := huniq (ψ ≫ φ) (by
      show ((ψ ≫ φ) ▷ G).left ⁻¹ᵁ U' = U'
      rw [UpperTheory.preimage_whiskerRight_comp_over, hφ, hψ])
    have b := huniq (𝟙 Y') (hid U')
    rw [a, b]
  exact ⟨⟨φ, ψ, e1, e2⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.IsFiniteOfIsPullbackFpqc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

theorem UpperTheory.isFinite_of_isPullback_fpqc :
    ∀ {X Y X' Y' : Scheme.{0}} (a : X' ⟶ X) (q : X' ⟶ Y') (p : X ⟶ Y) (t : Y' ⟶ Y), IsPullback a q p t → Surjective t → Flat t → QuasiCompact t → IsFinite q → IsFinite p := by
  intro X Y X' Y' a q p t h h₁ h₂ h₃ hq
  have := GlobalTheory.isAffineHom_descendsAlong_fpqc.{0}
  have ht : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) t :=
    ⟨⟨h₁, h₂⟩, h₃⟩
  have hA : IsAffineHom p :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @IsAffineHom) h.flip ht inferInstance
  have hU : UniversallyClosed p :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed) h.flip ht inferInstance
  have hL : LocallyOfFiniteType p :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @LocallyOfFiniteType) h.flip ht inferInstance
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).2
    ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨hU, hA⟩, hL⟩
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

theorem UpperTheory.clopRep_finite_etale_of_constant_rank :
    ∀ {S : Scheme.{0}} (G Y : Over S) (U : (Y ⊗ G).left.Opens) (n : ℕ), IsFinite G.hom → Etale G.hom → (∀ s, G.hom.finrank s = n) → UpperTheory.RepresentationRank.Rep G Y U → IsFinite Y.hom ∧ Etale Y.hom := by
  intro S G Y U n hf he hn hR
  obtain ⟨S', t, h1, h2, h3, hs⟩ := GlobalTheory.FinEt.exists_isSplitOfRank_pullback G.hom hn
  obtain ⟨Y'', U'', hR'', hf'', he''⟩ := UpperTheory.exists_clopRep_of_isSplitOfRank ((Over.pullback t).obj G) n hs
  obtain ⟨U', hR'⟩ := UpperTheory.exists_clopRep_pullback t G Y U hR
  obtain ⟨e⟩ := UpperTheory.clopRep_unique _ _ _ _ _ hR' hR''
  have hcomp : pullback.snd Y.hom t = e.hom.left ≫ Y''.hom := (Over.w e.hom).symm
  have hiso : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S').map e.hom))
  have hqf : IsFinite (pullback.snd Y.hom t) := by
    rw [hcomp]; infer_instance
  have hqe : Etale (pullback.snd Y.hom t) := by
    rw [hcomp]; infer_instance
  have hpb := IsPullback.of_hasPullback Y.hom t
  refine ⟨UpperTheory.isFinite_of_isPullback_fpqc _ _ _ _ hpb h3 inferInstance inferInstance hqf, ?_⟩
  exact MorphismProperty.of_isPullback_of_descendsAlong (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hpb.flip ⟨⟨h3, inferInstance⟩, inferInstance⟩ hqe
