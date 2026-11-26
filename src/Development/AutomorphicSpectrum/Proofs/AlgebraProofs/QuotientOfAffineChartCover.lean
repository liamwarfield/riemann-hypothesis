module

public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SesqSesquilinearSkewHermitian

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HasAffineChartIff
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

namespace GlobalTheory.CompanionTheory.FreeQuotGlue

def IsChart {P X Y : Scheme.{0}} (a b : P ⟶ X) (V : X.Opens) (q : V.toScheme ⟶ Y) : Prop :=
  a ⁻¹ᵁ V = b ⁻¹ᵁ V ∧ IsFinite q ∧ Flat q ∧ LocallyOfFinitePresentation q ∧ Surjective q ∧
    ∃ a' : (b ⁻¹ᵁ V).toScheme ⟶ V.toScheme,
      a' ≫ V.ι = (b ⁻¹ᵁ V).ι ≫ a ∧ IsPullback a' (b ∣_ V) q q

theorem hasAffineChart_iff {P X : Scheme.{0}} (a b : P ⟶ X) (V : X.Opens) :
    HasAffineChart a b V ↔ ∃ (Y : Scheme.{0}) (q : V.toScheme ⟶ Y), IsAffine Y ∧ IsChart a b V q := by
  constructor
  · rintro ⟨h, Y, q, a', hY, h1, h2, h3, h4, h5, h6⟩
    exact ⟨Y, q, hY, h, h1, h2, h3, h4, a', h5, h6⟩
  · rintro ⟨Y, q, hY, h, h1, h2, h3, h4, a', h5, h6⟩
    exact ⟨h, Y, q, a', hY, h1, h2, h3, h4, h5, h6⟩

variable {P X Y : Scheme.{0}} {a b : P ⟶ X} {V : X.Opens} {q : V.toScheme ⟶ Y}

theorem IsChart.stable (h : IsChart a b V q) : a ⁻¹ᵁ V = b ⁻¹ᵁ V := h.1
theorem IsChart.isFinite (h : IsChart a b V q) : IsFinite q := h.2.1
theorem IsChart.flat (h : IsChart a b V q) : Flat q := h.2.2.1
theorem IsChart.lfp (h : IsChart a b V q) : LocallyOfFinitePresentation q := h.2.2.2.1
theorem IsChart.surjective (h : IsChart a b V q) : Surjective q := h.2.2.2.2.1

theorem IsChart.effectiveEpi (h : IsChart a b V q) : EffectiveEpi q := by
  have := h.isFinite; have := h.flat; have := h.surjective
  infer_instance

theorem IsChart.comp_eq_iff (h : IsChart a b V q) {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ V.toScheme) :
    g₁ ≫ q = g₂ ≫ q ↔ ∃ l : Z ⟶ P, l ≫ a = g₁ ≫ V.ι ∧ l ≫ b = g₂ ≫ V.ι := by
  obtain ⟨hs, -, -, -, -, a', ha, hp⟩ := h
  constructor
  · intro e
    refine ⟨hp.lift g₁ g₂ e ≫ (b ⁻¹ᵁ V).ι, ?_, ?_⟩
    · rw [Category.assoc, ← ha, hp.lift_fst_assoc]
    · rw [Category.assoc, ← morphismRestrict_ι, hp.lift_snd_assoc]
  · rintro ⟨l, h1, h2⟩
    have hr : Set.range l ⊆ Set.range (b ⁻¹ᵁ V).ι := by
      rintro _ ⟨z, rfl⟩
      have : b (l z) ∈ V := by
        have : b (l z) = V.ι (g₂ z) := congr($h2 z)
        rw [this]; exact (g₂ z).2
      simpa using this
    let l' : Z ⟶ (b ⁻¹ᵁ V).toScheme := IsOpenImmersion.lift _ l hr
    have hl : l' ≫ (b ⁻¹ᵁ V).ι = l := IsOpenImmersion.lift_fac _ _ _
    have e1 : l' ≫ a' = g₁ := by
      rw [← cancel_mono V.ι, Category.assoc, ha, reassoc_of% hl, h1]
    have e2 : l' ≫ (b ∣_ V) = g₂ := by
      rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, reassoc_of% hl, h2]
    rw [← e1, ← e2, Category.assoc, Category.assoc, hp.w]

theorem IsChart.apply_eq_iff (h : IsChart a b V q) (u v : V.toScheme) :
    q u = q v ↔ ∃ p : P, a p = V.ι u ∧ b p = V.ι v := by
  obtain ⟨hs, -, -, -, -, a', ha, hp⟩ := id h
  constructor
  · intro e
    obtain ⟨z, h1, h2⟩ := Scheme.Pullback.exists_preimage_pullback u v e
    let p : (b ⁻¹ᵁ V).toScheme := hp.isoPullback.inv z
    have e1 : a' p = u := by
      rw [← h1]
      exact congr($(hp.isoPullback_inv_fst) z)
    have e2 : (b ∣_ V) p = v := by
      rw [← h2]
      exact congr($(hp.isoPullback_inv_snd) z)
    refine ⟨(b ⁻¹ᵁ V).ι p, ?_, ?_⟩
    · rw [← e1]; exact (congr($ha p)).symm
    · rw [← e2]; exact (congr($(morphismRestrict_ι b V) p)).symm
  · rintro ⟨p, h1, h2⟩
    have hp' : p ∈ b ⁻¹ᵁ V := by
      change b p ∈ V
      rw [h2]; exact v.2
    let p' : (b ⁻¹ᵁ V).toScheme := ⟨p, hp'⟩
    have hi : (b ⁻¹ᵁ V).ι p' = p := rfl
    have e1 : a' p' = u := V.ι.isOpenEmbedding.injective (by
      rw [← h1, ← hi]; exact congr($ha p'))
    have e2 : (b ∣_ V) p' = v := V.ι.isOpenEmbedding.injective (by
      rw [← h2, ← hi]; exact congr($(morphismRestrict_ι b V) p'))
    rw [← e1, ← e2]
    exact congr($(hp.w) p')

end GlobalTheory.CompanionTheory.FreeQuotGlue
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GlueQuotientChartsCover
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GlueQuotientChartsCover
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue

namespace GlobalTheory.CompanionTheory.FreeQuotGlue


set_option backward.isDefEq.respectTransparency false in
theorem exists_colimit_of_quotient_charts : ∀ {X : Scheme.{0}} (R : X → X → Prop) (𝒰 : Set X.Opens), (∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ x : X, x ∈ U → x ∈ V → ∃ W ∈ 𝒰, x ∈ W ∧ W ≤ U ∧ W ≤ V) → (∀ x : X, ∃ U : 𝒰, x ∈ U.1) → ∀ (Y : 𝒰 → Scheme.{0}) (q : ∀ U : 𝒰, U.1.toScheme ⟶ Y U), (∀ U, Epi (q U)) → (∀ U, Function.Surjective (q U)) → (∀ (U : 𝒰) (u v : U.1.toScheme), q U u = q U v ↔ R (U.1.ι u) (U.1.ι v)) → (∀ (U : 𝒰) (x y : X), R x y → x ∈ U.1 → y ∈ U.1) → ∀ (k : ∀ U V : 𝒰, U.1 ≤ V.1 → (Y U ⟶ Y V)), (∀ U V h, IsOpenImmersion (k U V h)) → (∀ U V h, q U ≫ k U V h = X.homOfLE h ≫ q V) → ∃ (Y' : Scheme.{0}) (π : X ⟶ Y') (em : ∀ U, Y U ⟶ Y') (_ : ∀ U, IsOpenImmersion (em U)), (∀ U, U.1.ι ≫ π = q U ≫ em U) ∧ (∀ U, π ⁻¹ᵁ (em U).opensRange = U.1) ∧ ∀ y : Y', ∃ U, ∃ z : Y U, em U z = y := by
  intro X R 𝒰 hbas hc Y q hepi hsurj hfib hst k hko hqk
  have hr (U : 𝒰) : U.1.ι.opensRange = U.1 := Scheme.Opens.opensRange_ι _
  have hmem (U : 𝒰) (x : U.1.toScheme) : U.1.ι x ∈ U.1 := by
    have : U.1.ι x ∈ U.1.ι.opensRange := ⟨x, rfl⟩
    rwa [hr U] at this
  have hex (U : 𝒰) (x : X) (hx : x ∈ U.1) : ∃ y, U.1.ι y = x := by
    rw [← hr U] at hx; exact hx
  have hinj (U : 𝒰) : Function.Injective U.1.ι := U.1.ι.isOpenEmbedding.injective
  have hm {U V : 𝒰} (h : U.1 ≤ V.1) : X.homOfLE h ≫ V.1.ι = U.1.ι := X.homOfLE_ι h
  have hm' {U V : 𝒰} (h : U.1 ≤ V.1) (x : U.1.toScheme) : V.1.ι (X.homOfLE h x) = U.1.ι x :=
    congr($(hm h) x)
  have hmo {U V : 𝒰} (h : U.1 ≤ V.1) : IsOpenImmersion (X.homOfLE h) := by
    have : IsOpenImmersion (X.homOfLE h ≫ V.1.ι) := by rw [hm]; infer_instance
    exact .of_comp _ V.1.ι
  let F : 𝒰 ⥤ Scheme.{0} :=
    { obj := Y
      map {U V} f := k U V f.le
      map_id U := by
        have := hepi U
        rw [← cancel_epi (q U), hqk]
        have : X.homOfLE (show U.1 ≤ U.1 from (𝟙 U : U ⟶ U).le) = 𝟙 _ := by
          rw [← cancel_mono U.1.ι, hm, Category.id_comp]
        rw [this, Category.id_comp]
        exact (Category.comp_id _).symm
      map_comp {U V W} f g := by
        have := hepi U
        rw [← cancel_epi (q U), hqk, reassoc_of% (hqk U V f.le), hqk]
        have : X.homOfLE (show U.1 ≤ W.1 from (f ≫ g).le) =
            X.homOfLE (show U.1 ≤ V.1 from f.le) ≫ X.homOfLE (show V.1 ≤ W.1 from g.le) := by
          rw [← cancel_mono W.1.ι, Category.assoc, hm, hm, hm]
        rw [this, Category.assoc] }
  let e (U : 𝒰) : U.1.toScheme ⟶ F.obj U := q U
  have hnat {U V : 𝒰} (f : U ⟶ V) :
      e U ≫ F.map f = X.homOfLE (show U.1 ≤ V.1 from f.le) ≫ e V := hqk U V f.le
  have hnat' {U V : 𝒰} (f : U ⟶ V) (x : U.1.toScheme) :
      F.map f (e U x) = e V (X.homOfLE (show U.1 ≤ V.1 from f.le) x) := congr($(hnat f) x)
  have hF {U V : 𝒰} (f : U ⟶ V) : IsOpenImmersion (F.map f) := hko U V f.le
  have hsurj' (U : 𝒰) : Function.Surjective (e U) := hsurj U
  have hfib' (U : 𝒰) (x y : U.1.toScheme) : e U x = e U y ↔ R (U.1.ι x) (U.1.ι y) := hfib U x y
  have key {U V : 𝒰} (x : U.1.toScheme) (y : V.1.toScheme) (h : U.1.ι x = V.1.ι y) :
      ∃ (W : 𝒰) (f : W ⟶ U) (g : W ⟶ V) (z : F.obj W),
        F.map f z = e U x ∧ F.map g z = e V y := by
    obtain ⟨W, hW, hxW, h1, h2⟩ := hbas U.1 U.2 V.1 V.2 _ (hmem U x) (h ▸ hmem V y)
    obtain ⟨z, hz⟩ := hex ⟨W, hW⟩ _ hxW
    refine ⟨⟨W, hW⟩, homOfLE h1, homOfLE h2, e ⟨W, hW⟩ z, ?_, ?_⟩
    · rw [hnat']; congr 1; apply hinj; rw [hm', hz]
    · rw [hnat']; congr 1; apply hinj; rw [hm', hz, h]
  have : (F ⋙ Scheme.forget).IsLocallyDirected := by
    constructor
    intro U V W f g x y h
    obtain ⟨x, rfl⟩ := hsurj' U x
    obtain ⟨y, rfl⟩ := hsurj' V y
    have h' : F.map f (e U x) = F.map g (e V y) := h
    rw [hnat', hnat'] at h'
    have hR := (hfib' _ _ _).mp h'
    rw [hm', hm'] at hR
    obtain ⟨y', hy'⟩ := hex U _ (hst U _ _ hR (hmem U x))
    have hxy : e U x = e U y' := (hfib' U _ _).mpr (by rw [hy']; exact hR)
    have := key _ _ hy'
    rwa [← hxy] at this
  have key2 {U V : 𝒰} (x : U.1.toScheme) (y : V.1.toScheme)
      (h : colimit.ι F U (e U x) = colimit.ι F V (e V y)) : V.1.ι y ∈ U.1 := by
    obtain ⟨W, f, g, z, -, h2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff F).mp h
    obtain ⟨z, rfl⟩ := hsurj' W z
    rw [hnat'] at h2
    have hR := (hfib' _ _ _).mp h2
    rw [hm'] at hR
    exact hst U _ _ hR ((show W.1 ≤ U.1 from f.le) (hmem W _))
  let 𝒱 : X.OpenCover := Scheme.Cover.mkOfCovers 𝒰 (fun U ↦ U.1.toScheme) (fun U ↦ U.1.ι)
    (fun x ↦ by
      obtain ⟨U, hU⟩ := hc x
      exact ⟨U, hex U x hU⟩)
  let j : X ⟶ colimit F := 𝒱.glueMorphisms (fun U ↦ e U ≫ colimit.ι F U) (by
    intro U V
    change 𝒰 at U V
    change pullback.fst U.1.ι V.1.ι ≫ (e U ≫ colimit.ι F U) =
      pullback.snd U.1.ι V.1.ι ≫ (e V ≫ colimit.ι F V)
    apply Scheme.hom_ext_of_forall
    intro x
    have hx : U.1.ι (pullback.fst U.1.ι V.1.ι x) = V.1.ι (pullback.snd U.1.ι V.1.ι x) :=
      congr($(pullback.condition (f := U.1.ι) (g := V.1.ι)) x)
    obtain ⟨W, hW, hxW, h1, h2⟩ := hbas U.1 U.2 V.1 V.2 _ (hmem U _) (hx ▸ hmem V _)
    let α : W.toScheme ⟶ pullback U.1.ι V.1.ι :=
      pullback.lift (X.homOfLE h1) (X.homOfLE h2) ((hm (U := ⟨W, hW⟩) h1).trans (hm (U := ⟨W, hW⟩) h2).symm)
    have hα1 : α ≫ pullback.fst _ _ = X.homOfLE h1 := pullback.lift_fst _ _ _
    have hα2 : α ≫ pullback.snd _ _ = X.homOfLE h2 := pullback.lift_snd _ _ _
    have : IsOpenImmersion (α ≫ pullback.fst _ _) := by rw [hα1]; exact hmo (U := ⟨W, hW⟩) _
    have : IsOpenImmersion α := .of_comp _ (pullback.fst _ _)
    obtain ⟨z, hz⟩ := hex ⟨W, hW⟩ _ hxW
    refine ⟨α.opensRange, ⟨z, ?_⟩, ?_⟩
    · apply (pullback.fst U.1.ι V.1.ι).isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hα1]
      apply hinj
      rw [hm' (U := ⟨W, hW⟩), hz]
    · rw [← cancel_epi α.isoOpensRange.hom]
      simp only [Scheme.Hom.isoOpensRange_hom_ι_assoc]
      change α ≫ pullback.fst U.1.ι V.1.ι ≫ e U ≫ colimit.ι F U =
        α ≫ pullback.snd U.1.ι V.1.ι ≫ e V ≫ colimit.ι F V
      rw [reassoc_of% hα1, reassoc_of% hα2,
        ← reassoc_of% (hnat (U := ⟨W, hW⟩) (V := U) (homOfLE h1)),
        ← reassoc_of% (hnat (U := ⟨W, hW⟩) (V := V) (homOfLE h2)), colimit.w, colimit.w])
  have hj (U : 𝒰) : U.1.ι ≫ j = e U ≫ colimit.ι F U := 𝒱.ι_glueMorphisms _ _ U
  have hj' (U : 𝒰) (x : U.1.toScheme) : j (U.1.ι x) = colimit.ι F U (e U x) := congr($(hj U) x)
  have hpre (U : 𝒰) : j ⁻¹ᵁ (colimit.ι F U).opensRange = U.1 := by
    ext x
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := hsurj' U y
      obtain ⟨V, hV⟩ := hc x
      obtain ⟨z, rfl⟩ := hex V x hV
      exact key2 y z (hy.trans (hj' V z))
    · intro hx
      obtain ⟨z, rfl⟩ := hex U x hx
      exact ⟨_, (hj' U z).symm⟩
  refine ⟨colimit F, j, fun U ↦ colimit.ι F U, fun U ↦ inferInstance, hj, hpre, fun y ↦ ?_⟩
  obtain ⟨U, x, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective F y
  exact ⟨U, x, rfl⟩

end GlobalTheory.CompanionTheory.FreeQuotGlue
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GlueQuotientChartsCoverStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glue_quotient_charts_cover : ∀ {X : Scheme.{0}} (R : X → X → Prop) (𝒰 : Set X.Opens), (∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ x : X, x ∈ U → x ∈ V → ∃ W ∈ 𝒰, x ∈ W ∧ W ≤ U ∧ W ≤ V) → (∀ x : X, ∃ U : 𝒰, x ∈ U.1) → ∀ (Y : 𝒰 → Scheme.{0}) (q : ∀ U : 𝒰, U.1.toScheme ⟶ Y U), (∀ U, Epi (q U)) → (∀ U, Function.Surjective (q U)) → (∀ (U : 𝒰) (u v : U.1.toScheme), q U u = q U v ↔ R (U.1.ι u) (U.1.ι v)) → (∀ (U : 𝒰) (x y : X), R x y → x ∈ U.1 → y ∈ U.1) → ∀ (k : ∀ U V : 𝒰, U.1 ≤ V.1 → (Y U ⟶ Y V)), (∀ U V h, IsOpenImmersion (k U V h)) → (∀ U V h, q U ≫ k U V h = X.homOfLE h ≫ q V) → ∃ (Y' : Scheme.{0}) (π : X ⟶ Y') (em : ∀ U, Y U ⟶ Y') (_ : ∀ U, IsOpenImmersion (em U)), (∀ U, U.1.ι ≫ π = q U ≫ em U) ∧ (∀ U, π ⁻¹ᵁ (em U).opensRange = U.1) ∧ ∀ y : Y', ∃ U, ∃ z : Y U, em U z = y := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotGlue.exists_colimit_of_quotient_charts | exact GlobalTheory.CompanionTheory.FreeQuotGlue.exists_colimit_of_quotient_charts | (intros; apply GlobalTheory.CompanionTheory.FreeQuotGlue.exists_colimit_of_quotient_charts <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartRestrictPreimageOpen
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartRestrictPreimageOpen
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue

noncomputable section

namespace GlobalTheory.CompanionTheory.FreeQuotGlue.ChartRestrict

theorem opensRange_homOfLE_eq {X : Scheme.{0}} {U V : X.Opens} (h : U ≤ V) :
    (X.homOfLE h).opensRange = V.ι ⁻¹ᵁ U := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    show V.ι (X.homOfLE h y) ∈ U
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
    exact y.2
  · intro x hx
    exact ⟨⟨x.1, hx⟩, Subtype.ext (Scheme.homOfLE_apply h _)⟩

theorem isChart_of_le {P X Y : Scheme.{0}} {a b : P ⟶ X} {V : X.Opens} {q : V.toScheme ⟶ Y}
    (h : IsChart a b V q) (D : Y.Opens) (W : X.Opens) (hle : W ≤ V)
    (hW : ∀ u : V.toScheme, V.ι u ∈ W ↔ q u ∈ D) :
    ∃ q' : W.toScheme ⟶ D.toScheme, IsChart a b W q' ∧ q' ≫ D.ι = X.homOfLE hle ≫ q := by
  obtain ⟨hst, hfin, hflat, hlfp, hsurj, a', ha', hpbV⟩ := h

  have hrange : Set.range (X.homOfLE hle ≫ q) ⊆ Set.range D.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    show q (X.homOfLE hle w) ∈ D
    rw [← hW, ← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
    exact w.2
  let q' : W.toScheme ⟶ D.toScheme := IsOpenImmersion.lift D.ι (X.homOfLE hle ≫ q) hrange
  have hq' : q' ≫ D.ι = X.homOfLE hle ≫ q := IsOpenImmersion.lift_fac _ _ _

  have hS2 : IsPullback q' (X.homOfLE hle) D.ι q := by
    refine IsOpenImmersion.isPullback q' (X.homOfLE hle) D.ι q hq'.symm ?_
    rw [Scheme.Opens.opensRange_ι, opensRange_homOfLE_eq hle]
    ext u
    exact (hW u).symm

  have hstW : a ⁻¹ᵁ W = b ⁻¹ᵁ W := by
    ext p
    show a p ∈ W ↔ b p ∈ W
    by_cases hpa : a p ∈ V
    · have hpb : b p ∈ V := by
        have : p ∈ a ⁻¹ᵁ V := hpa
        rw [hst] at this
        exact this
      obtain ⟨u, hu⟩ : a p ∈ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact hpa
      obtain ⟨u', hu'⟩ : b p ∈ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact hpb
      have hq : q u = q u' :=
        (IsChart.apply_eq_iff ⟨hst, hfin, hflat, hlfp, hsurj, a', ha', hpbV⟩ u u').mpr ⟨p, hu.symm, hu'.symm⟩
      have e1 := hW u
      have e2 := hW u'
      rw [hu] at e1
      rw [hu'] at e2
      rw [e1, e2, hq]
    · have hpb : b p ∉ V := fun hb => hpa (by
        have : p ∈ b ⁻¹ᵁ V := hb
        rw [← hst] at this
        exact this)
      exact ⟨fun hw => absurd (hle hw) hpa, fun hw => absurd (hle hw) hpb⟩

  have hrange' : Set.range ((b ⁻¹ᵁ W).ι ≫ a) ⊆ Set.range W.ι := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : p.1 ∈ a ⁻¹ᵁ W := by rw [hstW]; exact p.2
    exact this
  let a'' : (b ⁻¹ᵁ W).toScheme ⟶ W.toScheme := IsOpenImmersion.lift W.ι ((b ⁻¹ᵁ W).ι ≫ a) hrange'
  have ha'' : a'' ≫ W.ι = (b ⁻¹ᵁ W).ι ≫ a := IsOpenImmersion.lift_fac _ _ _
  let ιK : (b ⁻¹ᵁ W).toScheme ⟶ (b ⁻¹ᵁ V).toScheme := P.homOfLE (b.preimage_mono hle)
  have hL : IsPullback (b ∣_ W) ιK (X.homOfLE hle) (b ∣_ V) := by
    refine IsOpenImmersion.isPullback (b ∣_ W) ιK (X.homOfLE hle) (b ∣_ V) ?_ ?_
    · rw [← cancel_mono V.ι, Category.assoc, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι,
        morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
    · rw [opensRange_homOfLE_eq hle, opensRange_homOfLE_eq (b.preimage_mono hle)]
      ext p
      show (b ∣_ V) p ∈ V.ι ⁻¹ᵁ W ↔ (b ⁻¹ᵁ V).ι p ∈ b ⁻¹ᵁ W
      rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply,
        morphismRestrict_ι, Scheme.Hom.comp_apply]
  have hcomm : ιK ≫ a' = a'' ≫ X.homOfLE hle := by
    rw [← cancel_mono V.ι, Category.assoc, ha', Category.assoc, Scheme.homOfLE_ι, ha'',
      ← Category.assoc, Scheme.homOfLE_ι]
  have hs : IsPullback (a'' ≫ X.homOfLE hle) (b ∣_ W) q (q' ≫ D.ι) := by
    have := hL.flip.paste_horiz hpbV
    rw [hcomm, ← hq'] at this
    exact this
  have hpW : IsPullback a'' (b ∣_ W) q' q' := by
    refine hs.of_right ?_ hS2.flip
    rw [← cancel_mono D.ι, Category.assoc, Category.assoc, hq']
    simpa [hq'] using hs.w
  exact ⟨q', ⟨hstW, MorphismProperty.of_isPullback hS2.flip hfin,
    MorphismProperty.of_isPullback hS2.flip hflat, MorphismProperty.of_isPullback hS2.flip hlfp,
    MorphismProperty.of_isPullback hS2.flip hsurj, a'', ha'', hpW⟩, hq'⟩

end GlobalTheory.CompanionTheory.FreeQuotGlue.ChartRestrict

namespace GlobalTheory.CompanionTheory.FreeQuotGlue

theorem isChart_restrict_quotient_open :
    ∀ {P X Y : Scheme.{0}} {a b : P ⟶ X} {V : X.Opens} {q : V.toScheme ⟶ Y},
      IsChart a b V q → ∀ D : Y.Opens, ∃ (hle : V.ι ''ᵁ (q ⁻¹ᵁ D) ≤ V)
        (q' : (V.ι ''ᵁ (q ⁻¹ᵁ D)).toScheme ⟶ D.toScheme),
        IsChart a b (V.ι ''ᵁ (q ⁻¹ᵁ D)) q' ∧ q' ≫ D.ι = X.homOfLE hle ≫ q := by
  intro P X Y a b V q h D
  have hle : V.ι ''ᵁ (q ⁻¹ᵁ D) ≤ V := V.ι_image_le _
  have hW : ∀ u : V.toScheme, V.ι u ∈ V.ι ''ᵁ (q ⁻¹ᵁ D) ↔ q u ∈ D := fun u =>
    (Scheme.Opens.mem_ι_image_iff (x := u) (V := q ⁻¹ᵁ D))
  obtain ⟨q', hq', hfac⟩ := ChartRestrict.isChart_of_le h D _ hle hW
  exact ⟨hle, q', hq', hfac⟩

end GlobalTheory.CompanionTheory.FreeQuotGlue
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartRestrictPreimageOpenStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_restrict_preimage_open : ∀ {P X Y : Scheme.{0}} {a b : P ⟶ X} {V : X.Opens} {q : V.toScheme ⟶ Y}, IsChart a b V q → ∀ D : Y.Opens, ∃ (hle : V.ι ''ᵁ (q ⁻¹ᵁ D) ≤ V) (q' : (V.ι ''ᵁ (q ⁻¹ᵁ D)).toScheme ⟶ D.toScheme), IsChart a b (V.ι ''ᵁ (q ⁻¹ᵁ D)) q' ∧ q' ≫ D.ι = X.homOfLE hle ≫ q := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotGlue.isChart_restrict_quotient_open | exact GlobalTheory.CompanionTheory.FreeQuotGlue.isChart_restrict_quotient_open | (intros; apply GlobalTheory.CompanionTheory.FreeQuotGlue.isChart_restrict_quotient_open <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.InvariantOpenChartPreimage
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.InvariantOpenChartPreimage
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue

namespace GlobalTheory.CompanionTheory.FreeQuotGlue

theorem IsChart.exists_opens_image_preimage {P X Y : Scheme.{0}} {a b : P ⟶ X} {V : X.Opens}
    {q : V.toScheme ⟶ Y} (h : IsChart a b V q) (V' : X.Opens) (hV : V' ≤ V)
    (hs : a ⁻¹ᵁ V' = b ⁻¹ᵁ V') : ∃ D : Y.Opens, V.ι ''ᵁ (q ⁻¹ᵁ D) = V' := by
  have := h.isFinite
  have hsat : ∀ u v : V.toScheme, q u = q v → V.ι u ∈ V' → V.ι v ∈ V' := by
    intro u v huv hu
    obtain ⟨p, hpa, hpb⟩ := (h.apply_eq_iff u v).1 huv
    have hp : p ∈ a ⁻¹ᵁ V' := by
      show a p ∈ V'
      rw [hpa]
      exact hu
    rw [hs] at hp
    have hb : b p ∈ V' := hp
    rwa [hpb] at hb
  let C : Set V.toScheme := ((V.ι ⁻¹ᵁ V' : V.toScheme.Opens) : Set V.toScheme)ᶜ
  have hC : IsClosed C := (V.ι ⁻¹ᵁ V').isOpen.isClosed_compl
  have hqC : IsClosed (q '' C) := q.isClosedMap C hC
  refine ⟨⟨(q '' C)ᶜ, hqC.isOpen_compl⟩, ?_⟩
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    by_contra hx
    exact hu ⟨u, hx, rfl⟩
  · intro hx
    obtain ⟨u, rfl⟩ : ∃ u, V.ι u = x := by
      rw [← Set.mem_range, Scheme.Opens.range_ι]
      exact hV hx
    refine ⟨u, ?_, rfl⟩
    rintro ⟨v, hv, hvu⟩
    exact hv (hsat u v hvu.symm hx)

end GlobalTheory.CompanionTheory.FreeQuotGlue
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.InvariantOpenChartPreimageStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_open_chart_preimage : ∀ {P X Y : Scheme.{0}} {a b : P ⟶ X} {V : X.Opens} {q : V.toScheme ⟶ Y}, IsChart a b V q → ∀ (V' : X.Opens), V' ≤ V → a ⁻¹ᵁ V' = b ⁻¹ᵁ V' → ∃ D : Y.Opens, V.ι ''ᵁ (q ⁻¹ᵁ D) = V' := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotGlue.IsChart.exists_opens_image_preimage | exact GlobalTheory.CompanionTheory.FreeQuotGlue.IsChart.exists_opens_image_preimage | (intros; apply GlobalTheory.CompanionTheory.FreeQuotGlue.IsChart.exists_opens_image_preimage <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PullbackOfGluedCharts
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PullbackOfGluedCharts
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue

noncomputable section

namespace GlobalTheory.CompanionTheory.FreeQuotGlue

theorem isPullback_of_preimage_opensRange {X Y Y' : Scheme.{0}} (π : X ⟶ Y') (V : X.Opens)
    (q : V.toScheme ⟶ Y) (em : Y ⟶ Y') [IsOpenImmersion em] (hc : V.ι ≫ π = q ≫ em)
    (hpre : π ⁻¹ᵁ em.opensRange = V) : IsPullback q V.ι em π :=
  IsOpenImmersion.isPullback q V.ι em π hc (by rw [hpre, Scheme.Opens.opensRange_ι])

theorem IsChart.isIso_restrict_lift {P X Y Y' : Scheme.{0}} {a b : P ⟶ X} {π : X ⟶ Y'} {V : X.Opens}
    {q : V.toScheme ⟶ Y} {em : Y ⟶ Y'} [IsOpenImmersion em] (h : IsChart a b V q)
    (hc : V.ι ≫ π = q ≫ em) (hpre : π ⁻¹ᵁ em.opensRange = V) (w : a ≫ π = b ≫ π) :
    IsIso (pullback.lift a b w ∣_ (pullback.snd π π ⁻¹ᵁ V)) := by
  obtain ⟨-, -, -, -, -, a', ha', hsq⟩ := h

  have h1 : IsPullback (b ∣_ V) (a' ≫ V.ι) (V.ι ≫ π) π := by
    have h0 := hsq.paste_horiz (isPullback_of_preimage_opensRange π V q em hc hpre).flip
    rw [← hc] at h0
    exact h0.flip

  have h2 : IsPullback (pullback.snd π π ∣_ V) ((pullback.snd π π ⁻¹ᵁ V).ι ≫ pullback.fst π π)
      (V.ι ≫ π) π :=
    (isPullback_morphismRestrict (pullback.snd π π) V).paste_vert (IsPullback.of_hasPullback π π).flip
  have hdom : pullback.lift a b w ⁻¹ᵁ (pullback.snd π π ⁻¹ᵁ V) = b ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, pullback.lift_snd]

  have key : pullback.lift a b w ∣_ (pullback.snd π π ⁻¹ᵁ V) =
      (P.isoOfEq hdom).hom ≫ (h1.isoIsPullback _ _ h2).hom := by
    apply h2.hom_ext
    · rw [← cancel_mono V.ι]
      simp only [Category.assoc]
      rw [IsPullback.isoIsPullback_hom_fst_assoc]
      simp only [morphismRestrict_ι, morphismRestrict_ι_assoc, pullback.lift_snd,
        Scheme.isoOfEq_hom_ι_assoc]
    · rw [morphismRestrict_ι_assoc, pullback.lift_fst, Category.assoc,
        IsPullback.isoIsPullback_hom_snd, ha', Scheme.isoOfEq_hom_ι_assoc]
  rw [key]
  infer_instance

theorem isPullback_of_isChart {P X Y' : Scheme.{0}} (a b : P ⟶ X) (π : X ⟶ Y') {J : Type}
    (V : J → X.Opens) (Y : J → Scheme.{0}) (q : ∀ j, (V j).toScheme ⟶ Y j) (em : ∀ j, Y j ⟶ Y')
    [∀ j, IsOpenImmersion (em j)] (hch : ∀ j, IsChart a b (V j) (q j))
    (hc : ∀ j, (V j).ι ≫ π = q j ≫ em j) (hpre : ∀ j, π ⁻¹ᵁ (em j).opensRange = V j)
    (hcov : ∀ y : Y', ∃ j, ∃ z : Y j, em j z = y) : IsPullback a b π π := by

  have hV : iSup V = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨j, z, hz⟩ := hcov (π x)
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨j, ?_⟩
    rw [← hpre j, Scheme.Hom.mem_preimage]
    exact ⟨z, hz⟩

  have hw : a ≫ π = b ≫ π := by
    refine Scheme.Cover.hom_ext
      (P.openCoverOfIsOpenCover (fun j => b ⁻¹ᵁ V j)
        (by unfold TopologicalSpace.IsOpenCover; exact b.iSup_preimage_eq_top hV)) _ _ fun j => ?_
    obtain ⟨-, -, -, -, -, a', ha', hsq⟩ := hch j
    change (b ⁻¹ᵁ V j).ι ≫ a ≫ π = (b ⁻¹ᵁ V j).ι ≫ b ≫ π
    calc (b ⁻¹ᵁ V j).ι ≫ a ≫ π = a' ≫ (V j).ι ≫ π := by
          rw [← Category.assoc, ← ha', Category.assoc]
      _ = a' ≫ q j ≫ em j := by rw [hc j]
      _ = (b ∣_ V j) ≫ q j ≫ em j := by rw [← Category.assoc, hsq.w, Category.assoc]
      _ = (b ∣_ V j) ≫ (V j).ι ≫ π := by rw [hc j]
      _ = (b ⁻¹ᵁ V j).ι ≫ b ≫ π := by rw [morphismRestrict_ι_assoc]

  have hiso : IsIso (pullback.lift a b hw) := by
    rw [← MorphismProperty.isomorphisms.iff,
      IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
        (fun j => pullback.snd π π ⁻¹ᵁ V j) ((pullback.snd π π).iSup_preimage_eq_top hV)]
    intro j
    rw [MorphismProperty.isomorphisms.iff]
    exact IsChart.isIso_restrict_lift (hch j) (hc j) (hpre j) hw
  exact IsPullback.of_iso_pullback ⟨hw⟩ (asIso (pullback.lift a b hw))
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end GlobalTheory.CompanionTheory.FreeQuotGlue
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PullbackOfGluedChartsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_of_glued_charts : ∀ {P X Y' : Scheme.{0}} (a b : P ⟶ X) (π : X ⟶ Y') {J : Type} (V : J → X.Opens) (Y : J → Scheme.{0}) (q : ∀ j, (V j).toScheme ⟶ Y j) (em : ∀ j, Y j ⟶ Y') [∀ j, IsOpenImmersion (em j)], (∀ j, IsChart a b (V j) (q j)) → (∀ j, (V j).ι ≫ π = q j ≫ em j) → (∀ j, π ⁻¹ᵁ (em j).opensRange = V j) → (∀ y : Y', ∃ j, ∃ z : Y j, em j z = y) → IsPullback a b π π := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotGlue.isPullback_of_isChart | exact GlobalTheory.CompanionTheory.FreeQuotGlue.isPullback_of_isChart | (intros; apply GlobalTheory.CompanionTheory.FreeQuotGlue.isPullback_of_isChart <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.QuotientOfAffineChartCover
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue

namespace GlobalTheory.CompanionTheory.FreeQuotGlue

theorem exists_iso_of_effectiveEpi {T Y₁ Y₂ : Scheme.{0}} (q₁ : T ⟶ Y₁) (q₂ : T ⟶ Y₂)
    [EffectiveEpi q₁] [EffectiveEpi q₂]
    (h : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ T), g₁ ≫ q₁ = g₂ ≫ q₁ ↔ g₁ ≫ q₂ = g₂ ≫ q₂) :
    ∃ e : Y₁ ≅ Y₂, q₁ ≫ e.hom = q₂ := by
  let f : Y₁ ⟶ Y₂ := EffectiveEpi.desc q₁ q₂ fun {Z} g₁ g₂ e ↦ (h Z g₁ g₂).1 e
  let g : Y₂ ⟶ Y₁ := EffectiveEpi.desc q₂ q₁ fun {Z} g₁ g₂ e ↦ (h Z g₁ g₂).2 e
  have hf : q₁ ≫ f = q₂ := EffectiveEpi.fac _ _ _
  have hg : q₂ ≫ g = q₁ := EffectiveEpi.fac _ _ _
  refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
  · rw [← cancel_epi q₁, reassoc_of% hf, hg, Category.comp_id]
  · rw [← cancel_epi q₂, reassoc_of% hg, hf, Category.comp_id]

theorem IsChart.exists_isOpenImmersion {P X Y Y' : Scheme.{0}} {a b : P ⟶ X} {V V' : X.Opens}
    {q : V.toScheme ⟶ Y} {q' : V'.toScheme ⟶ Y'} (h : IsChart a b V q) (h' : IsChart a b V' q')
    (hle : V' ≤ V) : ∃ k : Y' ⟶ Y, IsOpenImmersion k ∧ q' ≫ k = X.homOfLE hle ≫ q := by
  obtain ⟨D, rfl⟩ := GlobalTheory.T.invariant_open_chart_preimage h V' hle h'.stable
  obtain ⟨hle₂, q'', hc, hq⟩ := GlobalTheory.T.chart_restrict_preimage_open h D
  have := h'.effectiveEpi
  have := hc.effectiveEpi
  obtain ⟨e, he⟩ := exists_iso_of_effectiveEpi q' q'' fun Z g₁ g₂ ↦ by
    rw [h'.comp_eq_iff, hc.comp_eq_iff]
  refine ⟨e.hom ≫ D.ι, inferInstance, ?_⟩
  rw [reassoc_of% he, hq]

theorem exists_common {P X : Scheme.{0}} {a b : P ⟶ X} {U V : X.Opens}
    (hU : HasAffineChart a b U) (hV : HasAffineChart a b V) (x : X) (hxU : x ∈ U) (hxV : x ∈ V) :
    ∃ W, HasAffineChart a b W ∧ x ∈ W ∧ W ≤ U ∧ W ≤ V := by
  obtain ⟨Y, q, hY, hq⟩ := (hasAffineChart_iff a b U).1 hU
  obtain ⟨D, hD⟩ := GlobalTheory.T.invariant_open_chart_preimage hq (U ⊓ V) inf_le_left (by
    have h1 := hq.stable
    have h2 := hV.1
    ext p
    have h1' := SetLike.ext_iff.1 h1 p
    have h2' := SetLike.ext_iff.1 h2 p
    exact and_congr h1' h2')
  have hx : x ∈ U.ι ''ᵁ (q ⁻¹ᵁ D) := hD ▸ ⟨hxU, hxV⟩
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨D', hD', hm, hle⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := q u) (U := D) hu
  obtain ⟨hW, q', hc, hq'⟩ := GlobalTheory.T.chart_restrict_preimage_open hq D'
  have hle' : U.ι ''ᵁ (q ⁻¹ᵁ D') ≤ U ⊓ V := by
    rw [← hD]
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨v, hle hv, rfl⟩
  have : IsAffine D'.toScheme := hD'
  exact ⟨_, (hasAffineChart_iff a b _).2 ⟨_, q', this, hc⟩, ⟨u, hm, rfl⟩, hW, hle'.trans inf_le_right⟩

theorem prop_of_charts (Q : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget Q]
    {X Y' : Scheme.{0}} (π : X ⟶ Y') {J : Type} (V : J → X.Opens)
    (Y : J → Scheme.{0}) (q : ∀ j, (V j).toScheme ⟶ Y j) (em : ∀ j, Y j ⟶ Y')
    [∀ j, IsOpenImmersion (em j)] (hcomm : ∀ j, (V j).ι ≫ π = q j ≫ em j)
    (hpre : ∀ j, π ⁻¹ᵁ (em j).opensRange = V j) (hsurj : ∀ y : Y', ∃ j, ∃ z : Y j, em j z = y)
    (hq : ∀ j, Q (q j)) : Q π := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun j ↦ (em j).opensRange) ?_ fun j ↦ ?_
  · rw [eq_top_iff]
    rintro y -
    obtain ⟨j, z, rfl⟩ := hsurj y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, z, rfl⟩
  · refine (Q.arrow_mk_iso_iff (morphismRestrictOpensRange π (em j))).mpr ?_
    have H : IsPullback (q j) (V j).ι (em j) π :=
      IsOpenImmersion.isPullback _ _ _ _ (hcomm j) (by
        rw [Scheme.Opens.opensRange_ι, hpre])
    have e : H.flip.isoPullback.hom ≫ pullback.snd π (em j) = q j := H.flip.isoPullback_hom_snd
    have h' := hq j
    rw [← e] at h'
    exact (Q.cancel_left_of_respectsIso _ _).1 h'

end GlobalTheory.CompanionTheory.FreeQuotGlue


set_option backward.isDefEq.respectTransparency false in
theorem GlobalTheory.CompanionTheory.FreeQuotGlue.exists_of_affineCharts : ∀ {P X : Scheme.{0}} (a b : P ⟶ X), (∀ x : X, ∃ V : X.Opens, x ∈ V ∧ HasAffineChart a b V) → ∃ (Y : Scheme.{0}) (q : X ⟶ Y), IsFinite q ∧ Flat q ∧ LocallyOfFinitePresentation q ∧ Surjective q ∧ IsPullback a b q q := by
  intro P X a b h
  let 𝒰 : Set X.Opens := {V | HasAffineChart a b V}
  have hU (U : 𝒰) := (hasAffineChart_iff a b U.1).1 U.2
  choose Y q hY hq using hU
  let R : X → X → Prop := fun x y ↦ ∃ p : P, a p = x ∧ b p = y
  have hk (U V : 𝒰) (h : U.1 ≤ V.1) := (hq V).exists_isOpenImmersion (hq U) h
  choose k hk hqk using hk
  obtain ⟨Y', π, em, hem, hcomm, hpre, hsurj⟩ := GlobalTheory.T.glue_quotient_charts_cover R 𝒰
    (fun U hU V hV x hx hx' ↦ by
      obtain ⟨W, h1, h2, h3, h4⟩ := exists_common hU hV x hx hx'
      exact ⟨W, h1, h2, h3, h4⟩)
    (fun x ↦ by
      obtain ⟨V, h1, h2⟩ := h x
      exact ⟨⟨V, h2⟩, h1⟩)
    Y q (fun U ↦ by have := (hq U).effectiveEpi; infer_instance)
    (fun U ↦ by have := (hq U).surjective; exact Surjective.surj)
    (fun U u v ↦ (hq U).apply_eq_iff u v)
    (fun U x y ⟨p, h1, h2⟩ hx ↦ by
      have : p ∈ a ⁻¹ᵁ U.1 := by change a p ∈ U.1; rwa [h1]
      rw [(hq U).stable] at this
      rw [← h2]; exact this)
    k hk hqk
  refine ⟨Y', π, ?_, ?_, ?_, ?_, ?_⟩
  · exact prop_of_charts (@IsFinite.{0}) π _ Y q em hcomm hpre hsurj fun U ↦ (hq U).isFinite
  · exact prop_of_charts @Flat.{0} π _ Y q em hcomm hpre hsurj fun U ↦ (hq U).flat
  · exact prop_of_charts @LocallyOfFinitePresentation.{0} π _ Y q em hcomm hpre hsurj fun U ↦ (hq U).lfp
  · exact prop_of_charts @Surjective.{0} π _ Y q em hcomm hpre hsurj fun U ↦ (hq U).surjective
  · exact GlobalTheory.T.pullback_of_glued_charts a b π _ Y q em hq hcomm hpre hsurj
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.QuotientOfAffineChartCoverStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_of_affine_chart_cover : ∀ {P X : Scheme.{0}} (a b : P ⟶ X), (∀ x : X, ∃ V : X.Opens, x ∈ V ∧ HasAffineChart a b V) → ∃ (Y : Scheme.{0}) (q : X ⟶ Y), IsFinite q ∧ Flat q ∧ LocallyOfFinitePresentation q ∧ Surjective q ∧ IsPullback a b q q := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotGlue.exists_of_affineCharts | exact GlobalTheory.CompanionTheory.FreeQuotGlue.exists_of_affineCharts | (intros; apply GlobalTheory.CompanionTheory.FreeQuotGlue.exists_of_affineCharts <;> assumption)
end
