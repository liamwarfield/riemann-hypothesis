module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.StrictModelTranslatesTwistCompatible
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNonzeroLocusEqOfIsAffineOpen

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GlueModelsOverSubfield
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GlueModelsOverSubfield
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GlueModels

set_option backward.isDefEq.respectTransparency false

theorem exists_glue {X U V W Y : Scheme.{0}} {u : U ⟶ X} {v : V ⟶ X} {p : W ⟶ U} {q : W ⟶ V}
    [IsOpenImmersion u] [IsOpenImmersion v] (h : IsPullback p q u v)
    (hc : ∀ x : X, x ∈ Set.range u ∨ x ∈ Set.range v) (a : U ⟶ Y) (b : V ⟶ Y) (hab : p ≫ a = q ≫ b) :
    ∃ φ : X ⟶ Y, u ≫ φ = a ∧ v ≫ φ = b := by
  let T : Bool → Scheme.{0} := fun i => Bool.rec U V i
  let t : ∀ i, T i ⟶ X := fun i => Bool.rec (motive := fun i => T i ⟶ X) u v i
  let m : ∀ i, T i ⟶ Y := fun i => Bool.rec (motive := fun i => T i ⟶ Y) a b i
  have ht : ∀ i, IsOpenImmersion (t i) := fun i => by cases i <;> assumption
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers Bool T t (fun x => by
    rcases hc x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨false, y, hy⟩
    · exact ⟨true, y, hy⟩)
  suffices hm : _ from ⟨𝒰.glueMorphisms m hm, 𝒰.ι_glueMorphisms m hm false, 𝒰.ι_glueMorphisms m hm true⟩
  · rintro (_ | _) (_ | _)
    · change pullback.fst u u ≫ a = pullback.snd u u ≫ a
      rw [fst_eq_snd_of_mono_eq]
    · change pullback.fst u v ≫ a = pullback.snd u v ≫ b
      rw [← h.isoPullback_inv_fst, ← h.isoPullback_inv_snd, Category.assoc, Category.assoc, hab]
    · change pullback.fst v u ≫ b = pullback.snd v u ≫ a
      rw [← h.flip.isoPullback_inv_fst, ← h.flip.isoPullback_inv_snd, Category.assoc, Category.assoc, hab]
    · change pullback.fst v v ≫ b = pullback.snd v v ≫ b
      rw [fst_eq_snd_of_mono_eq]

theorem isPullback_of_two {W X Y Z U V U' V' : Scheme.{0}} {a : W ⟶ X} {b : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    {u : U ⟶ X} {v : V ⟶ X} [IsOpenImmersion u] [IsOpenImmersion v]
    (hc : ∀ x : X, x ∈ Set.range u ∨ x ∈ Set.range v)
    {u' : U' ⟶ W} {v' : V' ⟶ W} {aU : U' ⟶ U} {aV : V' ⟶ V}
    (hU : IsPullback aU u' u a) (hV : IsPullback aV v' v a)
    (hU' : IsPullback aU (u' ≫ b) (u ≫ f) g) (hV' : IsPullback aV (v' ≫ b) (v ≫ f) g) :
    IsPullback a b f g := by
  let T : Bool → Scheme.{0} := fun i => Bool.rec U V i
  let t : ∀ i, T i ⟶ X := fun i => Bool.rec u v i
  have ht : ∀ i, IsOpenImmersion (t i) := fun i => by cases i <;> assumption
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers Bool T t (fun x => by
    rcases hc x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨false, y, hy⟩
    · exact ⟨true, y, hy⟩)
  refine Scheme.isPullback_of_openCover _ _ _ _ 𝒰 ?_
  rintro (_ | _)
  · change IsPullback (pullback.snd a u) (pullback.fst a u ≫ b) (u ≫ f) g
    refine hU'.of_iso hU.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp
  · change IsPullback (pullback.snd a v) (pullback.fst a v ≫ b) (v ≫ f) g
    refine hV'.of_iso hV.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp

theorem isOpenImmersion_inl {W U V : Scheme.{0}} (p : W ⟶ U) (q : W ⟶ V) [IsOpenImmersion p]
    [IsOpenImmersion q] : IsOpenImmersion (pushout.inl p q) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span p q) WalkingSpan.left))

theorem isOpenImmersion_inr {W U V : Scheme.{0}} (p : W ⟶ U) (q : W ⟶ V) [IsOpenImmersion p]
    [IsOpenImmersion q] : IsOpenImmersion (pushout.inr p q) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span p q) WalkingSpan.right))

theorem pushout_cover {W U V : Scheme.{0}} (p : W ⟶ U) (q : W ⟶ V) [IsOpenImmersion p]
    [IsOpenImmersion q] (z : (pushout p q : Scheme.{0})) :
    z ∈ Set.range (pushout.inl p q) ∨ z ∈ Set.range (pushout.inr p q) := by
  obtain ⟨i, x, hx⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span p q) z
  rcases i with _ | _ | _
  · refine Or.inl ⟨p x, Eq.trans ?_ hx⟩
    exact congrArg (fun g => g x) (colimit.w (span p q) WalkingSpan.Hom.fst)
  · exact Or.inl ⟨x, hx⟩
  · exact Or.inr ⟨x, hx⟩

theorem exists_of_inl_eq_inr {W U V : Scheme.{0}} (p : W ⟶ U) (q : W ⟶ V) [IsOpenImmersion p]
    [IsOpenImmersion q] {x : U} {y : V} (h : pushout.inl p q x = pushout.inr p q y) :
    ∃ w : W, p w = x ∧ q w = y := by
  obtain ⟨k, fi, fj, w, h1, h2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (span p q)
    (i := WalkingSpan.left) (j := WalkingSpan.right)).1 h
  rcases fi with _ | _
  · rcases fj with _ | _
  · rcases fj with _ | _
    exact ⟨w, h1, h2⟩

theorem model_open {k K : Type} [Field k] [Field K] (β : k →+* K) {U W : Over (Sp K)} (p : W ⟶ U)
    [IsOpenImmersion p.left] {U₀ W₀ : Over (Sp k)} {φU : U.left ⟶ U₀.left} {φW : W.left ⟶ W₀.left}
    (hU : IsPullback φU U.hom U₀.hom (spMap β)) (hW : IsPullback φW W.hom W₀.hom (spMap β))
    (p₀ : W₀ ⟶ U₀) (hp : φW ≫ p₀.left = p.left ≫ φU) :
    IsPullback φW p.left p₀.left φU ∧ IsOpenImmersion p₀.left := by
  have H : IsPullback φW p.left p₀.left φU := by
    refine IsPullback.of_bot ?_ hp hU
    rwa [Over.w p, Over.w p₀]
  refine ⟨H, ?_⟩
  have hβ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (spMap β) := by
    refine ⟨⟨⟨fun x => ⟨(default : PrimeSpectrum K), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩, ?_⟩,
      inferInstanceAs (QuasiCompact (spMap β))⟩
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    algebraize [β]
    exact RingHom.flat_algebraMap_iff.2 (inferInstanceAs (Module.Flat k K))
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @IsOpenImmersion)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) H.flip (MorphismProperty.of_isPullback hU.flip hβ) ‹_›

theorem glue_models : ∀ (k K : Type) [Field k] [Field K] (β : k →+* K) (X U V W : Over (Sp K)) (u : U ⟶ X) (v : V ⟶ X) (p : W ⟶ U) (q : W ⟶ V), IsOpenImmersion u.left → IsOpenImmersion v.left → IsPullback p.left q.left u.left v.left → (∀ x : X.left, x ∈ Set.range u.left ∨ x ∈ Set.range v.left) → ∀ (U₀ V₀ W₀ : Over (Sp k)) (φU : U.left ⟶ U₀.left) (φV : V.left ⟶ V₀.left) (φW : W.left ⟶ W₀.left), IsPullback φU U.hom U₀.hom (spMap β) → IsPullback φV V.hom V₀.hom (spMap β) → IsPullback φW W.hom W₀.hom (spMap β) → ∀ (p₀ : W₀ ⟶ U₀) (q₀ : W₀ ⟶ V₀), φW ≫ p₀.left = p.left ≫ φU → φW ≫ q₀.left = q.left ≫ φV → ∃ (X₀ : Over (Sp k)) (φ : X.left ⟶ X₀.left), IsPullback φ X.hom X₀.hom (spMap β) := by
  intro k K _ _ β X U V W u v p q hu hv h hc U₀ V₀ W₀ φU φV φW hU hV hW p₀ q₀ hp hq
  have : IsOpenImmersion p.left := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h.flip hv
  have : IsOpenImmersion q.left := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h hu
  obtain ⟨Hp, _⟩ := model_open β p hU hW p₀ hp
  obtain ⟨Hq, _⟩ := model_open β q hV hW q₀ hq
  have := isOpenImmersion_inl p₀.left q₀.left
  have := isOpenImmersion_inr p₀.left q₀.left
  obtain ⟨φ, h1, h2⟩ := exists_glue h hc (φU ≫ pushout.inl p₀.left q₀.left) (φV ≫ pushout.inr p₀.left q₀.left) (by
    rw [← Category.assoc, ← Category.assoc, ← hp, ← hq, Category.assoc, Category.assoc, pushout.condition])
  have e1 (x : U.left) : φ (u.left x) = pushout.inl p₀.left q₀.left (φU x) := congrArg (fun g => g x) h1
  have e2 (x : V.left) : φ (v.left x) = pushout.inr p₀.left q₀.left (φV x) := congrArg (fun g => g x) h2
  have e3 (w : W.left) : u.left (p.left w) = v.left (q.left w) := congrArg (fun g => g w) h.w
  refine ⟨Over.mk (pushout.desc U₀.hom V₀.hom ((Over.w p₀).trans (Over.w q₀).symm)), φ, ?_⟩
  refine isPullback_of_two (pushout_cover p₀.left q₀.left) (u' := u.left) (v' := v.left) (aU := φU) (aV := φV)
    ?_ ?_ ?_ ?_
  · refine IsOpenImmersion.isPullback _ _ _ _ h1 ?_
    ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with hx | ⟨x, rfl⟩
      · exact hx
      · obtain ⟨w, -, hw⟩ := exists_of_inl_eq_inr _ _ (hy.trans (e2 x))
        obtain ⟨z, -, rfl⟩ := Scheme.exists_preimage_of_isPullback Hq w x hw
        exact ⟨p.left z, e3 z⟩
    · rintro ⟨y, rfl⟩
      exact ⟨φU y, (e1 y).symm⟩
  · refine IsOpenImmersion.isPullback _ _ _ _ h2 ?_
    ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with ⟨x, rfl⟩ | hx
      · obtain ⟨w, hw, -⟩ := exists_of_inl_eq_inr _ _ (hy.trans (e1 x)).symm
        obtain ⟨z, -, rfl⟩ := Scheme.exists_preimage_of_isPullback Hp w x hw
        exact ⟨q.left z, (e3 z).symm⟩
      · exact hx
    · rintro ⟨y, rfl⟩
      exact ⟨φV y, (e2 y).symm⟩
  · simpa only [Over.w u, Over.mk_hom, pushout.inl_desc] using hU
  · simpa only [Over.w v, Over.mk_hom, pushout.inr_desc] using hV

end GlobalTheory.GlueModels
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GlueModelsOverSubfieldStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.glue_models_over_subfield : ∀ (k K : Type) [Field k] [Field K] (β : k →+* K) (X U V W : Over (Sp K)) (u : U ⟶ X) (v : V ⟶ X) (p : W ⟶ U) (q : W ⟶ V), IsOpenImmersion u.left → IsOpenImmersion v.left → IsPullback p.left q.left u.left v.left → (∀ x : X.left, x ∈ Set.range u.left ∨ x ∈ Set.range v.left) → ∀ (U₀ V₀ W₀ : Over (Sp k)) (φU : U.left ⟶ U₀.left) (φV : V.left ⟶ V₀.left) (φW : W.left ⟶ W₀.left), IsPullback φU U.hom U₀.hom (spMap β) → IsPullback φV V.hom V₀.hom (spMap β) → IsPullback φW W.hom W₀.hom (spMap β) → ∀ (p₀ : W₀ ⟶ U₀) (q₀ : W₀ ⟶ V₀), φW ≫ p₀.left = p.left ≫ φU → φW ≫ q₀.left = q.left ≫ φV → ∃ (X₀ : Over (Sp k)) (φ : X.left ⟶ X₀.left), IsPullback φ X.hom X₀.hom (spMap β) := by
  first | exact @GlobalTheory.GlueModels.glue_models | exact GlobalTheory.GlueModels.glue_models | (intros; apply GlobalTheory.GlueModels.glue_models <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.StrictModelTranslatesTwistCompatibleStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strictModel_translates_twist_compatible : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : Model R A, Strict M → ∀ a b : (𝟙_ (Over (Sp K)) ⟶ A), GenIso M M (transl a).hom → GenIso M M (transl b).hom → Compat (M.twist (transl a)) (M.twist (transl b)) := by
  first | exact @GlobalTheory.SS.compat_twist_transl | exact GlobalTheory.SS.compat_twist_transl | (intros; apply GlobalTheory.SS.compat_twist_transl <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GrpSchemePointsModelOverField
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GrpSchemePointsModelOverField
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.ModelPoints

theorem exists_push_equiv {S S' : Scheme.{0}} (f : S' ⟶ S) (H : Over S) [GrpObj H] (T : Over S')
    (s : T.left ⟶ S) (hs : s = T.hom ≫ f) :
    ∃ π : (T ⟶ (Over.pullback f).obj H) ≃* (Over.mk s ⟶ H),
      ∀ x, (π x).left = x.left ≫ pullback.fst H.hom f := by
  subst hs
  have h := isGrpPullback_pullback H f
  refine ⟨MulEquiv.ofBijective (pushHom h T) ⟨fun x y e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun y => ?_⟩, fun x => rfl⟩
  exact ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem exists_comp_equiv {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] (e : G ≅ H) [IsMonHom e.hom]
    (T : Over S) : ∃ π : (T ⟶ G) ≃* (T ⟶ H), ∀ y, π.symm y = y ≫ e.inv :=
  ⟨{ toFun := fun x => x ≫ e.hom
     invFun := fun y => y ≫ e.inv
     left_inv := fun x => by simp
     right_inv := fun x => by simp
     map_mul' := fun x y => MonObj.mul_comp x y e.hom }, fun _ => rfl⟩

theorem exists_equiv {S₁ S₂ S : Scheme.{0}} (f : S ⟶ S₁) (g : S ⟶ S₂) (A : Over S₁) [GrpObj A]
    (G : Over S₂) [GrpObj G] (e : (Over.pullback g).obj G ≅ (Over.pullback f).obj A) [IsMonHom e.hom]
    {T : Scheme.{0}} (t : T ⟶ S) (s₁ : T ⟶ S₁) (s₂ : T ⟶ S₂) (h₁ : s₁ = t ≫ f) (h₂ : s₂ = t ≫ g) :
    ∃ θ : (Over.mk s₁ ⟶ A) ≃* (Over.mk s₂ ⟶ G), ∀ (x : Over.mk s₁ ⟶ A) (z : T ⟶ pullback A.hom f),
      z ≫ pullback.fst A.hom f = x.left → z ≫ pullback.snd A.hom f = t →
      (θ x).left = z ≫ e.inv.left ≫ pullback.fst G.hom g := by
  obtain ⟨π₁, p₁⟩ := exists_push_equiv f A (Over.mk t) s₁ h₁
  obtain ⟨π₂, p₂⟩ := exists_push_equiv g G (Over.mk t) s₂ h₂
  obtain ⟨π, p⟩ := exists_comp_equiv e (Over.mk t)
  refine ⟨π₁.symm.trans (π.symm.trans π₂), fun x z hz hz' => ?_⟩
  have hx : π₁.symm x = Over.homMk z hz' := by
    rw [MulEquiv.symm_apply_eq]
    exact Over.OverMorphism.ext (hz.symm.trans (p₁ (Over.homMk z hz')).symm)
  show (π₂ (π.symm (π₁.symm x))).left = _
  rw [p₂, p, hx, Over.comp_left, Category.assoc]
  rfl

theorem spMap_comp_of_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {f : A →+* B} {g : B →+* C}
    {h : A →+* C} (e : g.comp f = h) : spMap h = spMap g ≫ spMap f := by
  subst e
  exact Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)

theorem spMap_cancel {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {g : B →+* C}
    (hg : Function.Injective g) {a b : Sp B ⟶ Sp A} (e : spMap g ≫ a = spMap g ≫ b) : a = b := by
  obtain ⟨a, rfl⟩ := Spec.map_surjective a
  obtain ⟨b, rfl⟩ := Spec.map_surjective b
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at e
  congr 1
  ext x
  exact hg (congrArg (fun q => q.hom x) e)

theorem points_model : ∀ (K W L : Type) [Field K] [CommRing W] [Field L] [Algebra K L] [Algebra W L] (A : Over (Sp K)) [GrpObj A] (G : Over (Sp W)) [GrpObj G], IsModel (L := L) A G → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra W Ω] (j : L →+* Ω), j.comp (algebraMap K L) = algebraMap K Ω → j.comp (algebraMap W L) = algebraMap W Ω → ∃ θ : (Over.mk (spMap (algebraMap K Ω)) ⟶ A) ≃* (Over.mk (spMap (algebraMap W Ω)) ⟶ G), (∀ τ : Ω →+* Ω, τ.comp j = j → ∀ x x', x'.left = spMap τ ≫ x.left → (θ x').left = spMap τ ≫ (θ x).left) ∧ ∀ (K' : Type) [Field K'] (i : L →+* K') (j' : K' →+* Ω), j'.comp i = j → ∀ (x : Over.mk (spMap (algebraMap K Ω)) ⟶ A) (y : Sp K' ⟶ A.left), spMap j' ≫ y = x.left → ∀ ρ : W →+* K', ρ = i.comp (algebraMap W L) → ∃ y' : Over.mk (spMap ρ) ⟶ G, ∀ c : ℕ, spMap j' ≫ (y' ^ c).left = (θ (x ^ c)).left := by
  intro K W L _ _ _ _ _ A _ G _ ⟨e, he⟩ Ω _ _ _ j hK hW
  obtain ⟨θ, hθ⟩ := exists_equiv (spMap (algebraMap K L)) (spMap (algebraMap W L)) A G e (spMap j)
    _ _ (spMap_comp_of_eq hK) (spMap_comp_of_eq hW)
  refine ⟨θ, fun τ hτ x x' hx => ?_, fun K' _ i j' hj x y hy ρ hρ => ?_⟩
  · have w : x.left ≫ A.hom = spMap j ≫ spMap (algebraMap K L) :=
      (Over.w x).trans (spMap_comp_of_eq hK)
    rw [hθ x (pullback.lift x.left (spMap j) w) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _),
      hθ x' (spMap τ ≫ pullback.lift x.left (spMap j) w)
        (by rw [Category.assoc, pullback.lift_fst, hx])
        (by rw [Category.assoc, pullback.lift_snd, ← spMap_comp_of_eq hτ]), Category.assoc]
  · have w : y ≫ A.hom = spMap i ≫ spMap (algebraMap K L) := by
      apply spMap_cancel j'.injective
      rw [← Category.assoc, hy, ← Category.assoc, ← spMap_comp_of_eq hj]
      exact (Over.w x).trans (spMap_comp_of_eq hK)
    have w' : (pullback.lift y (spMap i) w ≫ e.inv.left ≫ pullback.fst G.hom (spMap (algebraMap W L))) ≫ G.hom
        = spMap ρ := by
      have h₁ : e.inv.left ≫ pullback.snd G.hom (spMap (algebraMap W L))
          = pullback.snd A.hom (spMap (algebraMap K L)) := Over.w e.inv
      simp only [Category.assoc]
      rw [pullback.condition, reassoc_of% h₁, pullback.lift_snd_assoc]
      exact (spMap_comp_of_eq hρ.symm).symm
    have hU : spMap j' ≫ spMap ρ = spMap (algebraMap W Ω) :=
      (spMap_comp_of_eq (by rw [hρ, ← RingHom.comp_assoc, hj, hW])).symm
    let U : Over.mk (spMap (algebraMap W Ω)) ⟶ Over.mk (spMap ρ) := Over.homMk (spMap j') hU
    let y' : Over.mk (spMap ρ) ⟶ G := Over.homMk _ w'
    have hxy : θ x = U ≫ y' := by
      apply Over.OverMorphism.ext
      rw [hθ x (spMap j' ≫ pullback.lift y (spMap i) w)
        (by rw [Category.assoc, pullback.lift_fst, hy])
        (by rw [Category.assoc, pullback.lift_snd, ← spMap_comp_of_eq hj]), Category.assoc]
      rfl
    refine ⟨y', fun c => ?_⟩
    rw [map_pow, hxy, ← MonObj.comp_pow]
    rfl

end GlobalTheory.SS.ModelPoints
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GrpSchemePointsModelOverFieldStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grpScheme_points_model_over_field : ∀ (K W L : Type) [Field K] [CommRing W] [Field L] [Algebra K L] [Algebra W L] (A : Over (Sp K)) [GrpObj A] (G : Over (Sp W)) [GrpObj G], IsModel (L := L) A G → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra W Ω] (j : L →+* Ω), j.comp (algebraMap K L) = algebraMap K Ω → j.comp (algebraMap W L) = algebraMap W Ω → ∃ θ : (Over.mk (spMap (algebraMap K Ω)) ⟶ A) ≃* (Over.mk (spMap (algebraMap W Ω)) ⟶ G), (∀ τ : Ω →+* Ω, τ.comp j = j → ∀ x x', x'.left = spMap τ ≫ x.left → (θ x').left = spMap τ ≫ (θ x).left) ∧ ∀ (K' : Type) [Field K'] (i : L →+* K') (j' : K' →+* Ω), j'.comp i = j → ∀ (x : Over.mk (spMap (algebraMap K Ω)) ⟶ A) (y : Sp K' ⟶ A.left), spMap j' ≫ y = x.left → ∀ ρ : W →+* K', ρ = i.comp (algebraMap W L) → ∃ y' : Over.mk (spMap ρ) ⟶ G, ∀ c : ℕ, spMap j' ≫ (y' ^ c).left = (θ (x ^ c)).left := by
  first | exact @GlobalTheory.SS.ModelPoints.points_model | exact GlobalTheory.SS.ModelPoints.points_model | (intros; apply GlobalTheory.SS.ModelPoints.points_model <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcQuotientTwoVariableCoords
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcQuotientTwoVariableCoords
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
noncomputable section
namespace GlobalTheory.SS.ArcInf.TwoVarSetup

theorem exists_liftAway {k R F : Type} [CommRing k] [CommRing R] [Algebra k R] [CommRing F] [Algebra k F]
    (x : R) (τ : R →ₐ[k] F) (h : IsUnit (τ x)) :
    ∃ τ' : Localization.Away x →ₐ[k] F, ∀ y, τ' (algebraMap R _ y) = τ y := by
  have hu : ∀ y : Submonoid.powers x, IsUnit (τ y) := by
    rintro ⟨y, n, rfl⟩
    show IsUnit (τ (x ^ n))
    rw [map_pow]; exact h.pow n
  exact ⟨IsLocalization.liftAlgHom (S := Localization.Away x) hu, fun x => by simp⟩

variable {k : Type} [Field k]

theorem laurent_ext {F : Type} [CommRing F] [Algebra k F] {a b : FractionRing (PowerSeries k) →ₐ[k] F}
    (h : ∀ x : PowerSeries k, a (algebraMap _ _ x) = b (algebraMap _ _ x)) : a = b := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (nonZeroDivisors (PowerSeries k))
  exact RingHom.ext h

theorem hasSubst_diag :
    MvPowerSeries.HasSubst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro s
  fin_cases s <;> exact PowerSeries.constantCoeff_X

theorem hasSubst_var (i : Fin 2) :
    PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) k) :=
  PowerSeries.HasSubst.of_constantCoeff_zero (by simp)

theorem diag_var (i : Fin 2) :
    MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k)
      (MvPowerSeries.X i : MvPowerSeries (Fin 2) k) = PowerSeries.X := by
  rw [MvPowerSeries.subst_X hasSubst_diag]
  fin_cases i <;> rfl

theorem diag_subst (i : Fin 2) (x : PowerSeries k) :
    MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k)
      (x.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) k)) = x := by
  rw [PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply (hasSubst_var i).const hasSubst_diag]
  simp only [diag_var]
  rw [← PowerSeries.subst_def]
  simp

theorem exists_diag : ∃ τ : MvPowerSeries (Fin 2) k →ₐ[k] FractionRing (PowerSeries k), ∀ y,
    τ y = algebraMap (PowerSeries k) _
      (MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k) y) :=
  ⟨(IsScalarTower.toAlgHom k (PowerSeries k) _).comp (MvPowerSeries.substAlgHom hasSubst_diag), fun y => by
    rw [AlgHom.comp_apply, MvPowerSeries.coe_substAlgHom]; rfl⟩

theorem exists_copy (i : Fin 2) : ∃ s : FractionRing (PowerSeries k) →ₐ[k]
      Localization.Away (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k),
    ∀ x : PowerSeries k, s (algebraMap _ _ x) = algebraMap (MvPowerSeries (Fin 2) k) _
      (x.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) k)) := by
  have hu := IsLocalization.Away.algebraMap_isUnit
    (S := Localization.Away (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k))
    (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k)
  rw [map_mul] at hu
  obtain ⟨s, hs⟩ := exists_lift ((IsScalarTower.toAlgHom k (MvPowerSeries (Fin 2) k)
    (Localization.Away (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k))).comp
      (PowerSeries.substAlgHom (hasSubst_var i))) (by
    rw [AlgHom.comp_apply, PowerSeries.substAlgHom_X]
    fin_cases i
    · exact isUnit_of_mul_isUnit_left hu
    · exact isUnit_of_mul_isUnit_right hu)
  refine ⟨s, fun x => ?_⟩
  rw [hs, AlgHom.comp_apply, PowerSeries.coe_substAlgHom]; rfl

theorem point_one {G : Over (Sp k)} [GrpObj G] {A : Type} [CommRing A] [Algebra k A] {j : algOver k A ⟶ G}
    {ε : A →ₐ[k] k} (h : algOverHom ε ≫ j = 1) (F : Type) [CommRing F] [Algebra k F] :
    algOverHom ((Algebra.ofId k F).comp ε) ≫ j = 1 := by
  rw [algOverHom_comp, Category.assoc, h, MonObj.comp_one]

theorem exists_twoVar : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] (A : Type) [CommRing A] [Algebra k A] (j : algOver k A ⟶ G) (ε : A →ₐ[k] k) (r : ℕ) (f : Fin r → A), IsChart G j ε f → ∀ a : algOver k (FractionRing (PowerSeries k)) ⟶ G, ∃ (h : Fin r → MvPowerSeries (Fin 2) k) (d : MvPowerSeries (Fin 2) k), MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k) d ≠ 0 ∧ (∀ i, MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k) (h i) = 0) ∧ TwoVar j f a h d := by
  intro k _ G _ A _ _ j ε r f hc a
  obtain ⟨τ₀, hτ₀⟩ := exists_diag (k := k)
  obtain ⟨s₀, hs₀⟩ := exists_copy (k := k) 0
  obtain ⟨s₁, hs₁⟩ := exists_copy (k := k) 1
  have hinj := IsFractionRing.injective (PowerSeries k) (FractionRing (PowerSeries k))
  have hX : ∀ i, τ₀ (MvPowerSeries.X i) ≠ 0 := fun i => by
    rw [hτ₀, diag_var]
    exact (map_ne_zero_iff _ hinj).2 PowerSeries.X_ne_zero
  have hx : τ₀ (MvPowerSeries.X 0 * MvPowerSeries.X 1) ≠ 0 := by
    rw [map_mul]; exact mul_ne_zero (hX 0) (hX 1)
  generalize (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) = x at s₀ s₁ hs₀ hs₁ hx
  obtain ⟨δ, hδ⟩ := exists_liftAway x τ₀ hx.isUnit
  have hδ₀ : δ.comp s₀ = AlgHom.id k _ := laurent_ext fun y => by
    rw [AlgHom.comp_apply, hs₀, hδ, hτ₀, diag_subst]; rfl
  have hδ₁ : δ.comp s₁ = AlgHom.id k _ := laurent_ext fun y => by
    rw [AlgHom.comp_apply, hs₁, hδ, hτ₀, diag_subst]; rfl
  obtain ⟨e, he, hfac⟩ := GlobalTheory.SS.ArcInf.exists_basicOpen_factor k G A _ (FractionRing (PowerSeries k)) j
    ((algOverHom s₁ ≫ a) * (algOverHom s₀ ≫ a)⁻¹) δ ((Algebra.ofId k _).comp ε) hc.1 (by
      rw [point_one hc.2.1, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc,
        ← algOverHom_comp, ← algOverHom_comp, hδ₀, hδ₁, mul_inv_cancel])
  obtain ⟨n, e₀, he₀⟩ := IsLocalization.Away.surj x e
  have hτe : τ₀ e₀ ≠ 0 := by
    rw [← hδ, ← he₀, map_mul, map_pow, hδ]
    exact mul_ne_zero he (pow_ne_zero _ hx)
  have hu := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (x * e₀)) (x * e₀)
  rw [map_mul] at hu
  obtain ⟨ρ, hρ⟩ := exists_liftAway x
    (IsScalarTower.toAlgHom k (MvPowerSeries (Fin 2) k) (Localization.Away (x * e₀)))
    (isUnit_of_mul_isUnit_left hu)
  simp only [IsScalarTower.coe_toAlgHom'] at hρ
  have hρe : IsUnit (ρ e) := by
    have h1 := isUnit_of_mul_isUnit_right hu
    rw [← hρ, ← he₀, map_mul] at h1
    exact isUnit_of_mul_isUnit_left h1
  obtain ⟨χ, hχ⟩ := hfac _ ρ hρe
  obtain ⟨⟨b, M, rfl⟩, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers (x * e₀)) (fun i => χ (f i))
  choose h hh using hb
  simp only [Algebra.smul_def] at hh
  have hd : τ₀ ((x * e₀) * (x * e₀) ^ M) ≠ 0 := by
    rw [← pow_succ', map_pow, map_mul]
    exact pow_ne_zero _ (mul_ne_zero hx hτe)
  have htv : TwoVar j f a (fun i => (x * e₀) * h i) ((x * e₀) * (x * e₀) ^ M) := by
    intro F _ _ τ σ₀ σ₁ hτ hσ₀ hσ₁
    have h0 : τ (x * e₀) ≠ 0 := by
      rw [map_mul] at hτ; exact left_ne_zero_of_mul hτ
    obtain ⟨τ', hτ'⟩ := exists_liftAway (x * e₀) τ h0.isUnit
    have e0 : τ'.comp (ρ.comp s₀) = σ₀ := laurent_ext fun y => by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, hs₀, hρ, hτ', hσ₀]
    have e1 : τ'.comp (ρ.comp s₁) = σ₁ := laurent_ext fun y => by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, hs₁, hρ, hτ', hσ₁]
    refine ⟨τ'.comp χ, fun i => ?_, ?_⟩
    · rw [map_mul τ (x * e₀) (h i), ← hτ' (h i), hh, map_mul τ', hτ', map_mul τ (x * e₀),
        AlgHom.comp_apply]
      ring
    · rw [algOverHom_comp, Category.assoc, hχ, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv,
        GrpObj.comp_inv]
      simp only [← Category.assoc, ← algOverHom_comp]
      rw [e0, e1, inv_mul_cancel_right]
  refine ⟨_, _, ?_, fun i => ?_, htv⟩
  · intro h0
    apply hd
    rw [hτ₀, h0, map_zero]
  · obtain ⟨χ', h1, h2⟩ := htv _ τ₀ (AlgHom.id k _) (AlgHom.id k _) hd
      (fun y => by rw [hτ₀, diag_subst]; rfl) (fun y => by rw [hτ₀, diag_subst]; rfl)
    have h3 : χ' = (Algebra.ofId k _).comp ε := by
      apply eq_of_comp_eq hc.1
      rw [point_one hc.2.1]
      exact right_eq_mul.1 h2
    apply hinj
    rw [← hτ₀, map_zero, ← h1 i, h3, AlgHom.comp_apply, hc.2.2.2 i, map_zero, zero_mul]

end GlobalTheory.SS.ArcInf.TwoVarSetup
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcQuotientTwoVariableCoordsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_arcQuotient_twoVariable_coords : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] (A : Type) [CommRing A] [Algebra k A] (j : algOver k A ⟶ G) (ε : A →ₐ[k] k) (r : ℕ) (f : Fin r → A), IsChart G j ε f → ∀ a : algOver k (FractionRing (PowerSeries k)) ⟶ G, ∃ (h : Fin r → MvPowerSeries (Fin 2) k) (d : MvPowerSeries (Fin 2) k), MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k) d ≠ 0 ∧ (∀ i, MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k) (h i) = 0) ∧ TwoVar j f a h d := by
  first | exact @GlobalTheory.SS.ArcInf.TwoVarSetup.exists_twoVar | exact GlobalTheory.SS.ArcInf.TwoVarSetup.exists_twoVar | (intros; apply GlobalTheory.SS.ArcInf.TwoVarSetup.exists_twoVar <;> assumption)
end
end
