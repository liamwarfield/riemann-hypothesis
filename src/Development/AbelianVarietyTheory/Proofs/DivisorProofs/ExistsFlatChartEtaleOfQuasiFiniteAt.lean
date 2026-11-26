module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreUniformisationEvenTorusCompleteNormal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoFinitePieceFlatConnectedChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoFinitePieceFlatConnectedChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FlatChartDeg

theorem isIso_app_of_flat {X Y S T : Scheme.{0}} {p : X ⟶ S} {f : T ⟶ S} {g : Y ⟶ X} {q : Y ⟶ T}
    (H : IsPullback g q p f) [Flat f] [QuasiCompact p] [QuasiSeparated p]
    (hp : ∀ V : S.Opens, IsIso (p.app V)) (U : T.Opens) : IsIso (q.app U) := by
  refine GlobalTheory.ProperFunctions.isIso_app_of_isBasis q
    (fun V : {V : T.affineOpens // ∃ W : S.affineOpens, V.1 ≤ f ⁻¹ᵁ W.1} ↦ V.1.1) ?_ ?_ U
  · rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro U x hx
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      T.isBasis_affineOpens.exists_subset_of_mem_open (a := x) (u := (U ⊓ f ⁻¹ᵁ W : T.Opens))
        ⟨hx, hxW⟩ (U ⊓ f ⁻¹ᵁ W).2
    exact ⟨V, ⟨⟨⟨V, hV⟩, ⟨W, hW⟩, fun y hy ↦ (hVU hy).2⟩, rfl⟩, hxV, fun y hy ↦ (hVU hy).1⟩
  · rintro ⟨V, W, hVW⟩
    have : IsAffine V.1 := V.2
    have : IsAffine W.1 := W.2
    have H1 := (isPullback_morphismRestrict q V.1).flip.paste_horiz H
    have hw : ((q ⁻¹ᵁ V.1).ι ≫ g) ≫ p = (q ∣_ V.1 ≫ f.resLE W.1 V.1 hVW) ≫ W.1.ι := by
      rw [H1.w, Category.assoc, Scheme.Hom.resLE_comp_ι]
    let H2 := (isPullback_morphismRestrict p W.1).flip
    have : IsIso (p ∣_ W.1).appTop := by
      rw [morphismRestrict_appTop]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ (hp (W.1.ι ''ᵁ ⊤)) (by rw [eqToHom_op]; exact Functor.map_isIso _ _)
    refine GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback (p := p ∣_ W.1) (f := f.resLE W.1 V.1 hVW)
      (g := H2.lift _ _ hw) (IsPullback.of_right ?_ (H2.lift_snd _ _ _) H2)
    rw [H2.lift_fst, Scheme.Hom.resLE_comp_ι]
    exact H1

theorem preconnectedSpace_of_surjective_appTop {Z T : Scheme.{0}} (r : Z ⟶ T) [PreconnectedSpace T]
    (hr : Function.Bijective r.appTop.hom) : PreconnectedSpace Z := by
  rw [preconnectedSpace_iff_clopen]
  intro s hs
  obtain ⟨e, he, hes⟩ := GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen Z s hs
  obtain ⟨e, rfl⟩ := hr.2 e
  have he' : e * e = e := hr.1 (by rw [map_mul, he])
  have h1 : T.basicOpen e ⊓ T.basicOpen (1 - e) = ⊥ := by
    rw [← Scheme.basicOpen_mul, mul_sub, _root_.mul_one, he', sub_self, Scheme.basicOpen_zero]
  have h2 : T.basicOpen e ⊔ T.basicOpen (1 - e) = ⊤ := by
    refine top_le_iff.mp ?_
    have := T.basicOpen_add_le e (1 - e)
    rwa [add_sub_cancel, T.basicOpen_of_isUnit isUnit_one] at this
  have hcl : IsClopen (T.basicOpen e : Set T) := by
    refine ⟨⟨?_⟩, (T.basicOpen e).2⟩
    have : (T.basicOpen e : Set T)ᶜ = T.basicOpen (1 - e) := by
      ext x
      constructor
      · intro hx
        have : x ∈ T.basicOpen e ⊔ T.basicOpen (1 - e) := by rw [h2]; trivial
        exact (TopologicalSpace.Opens.mem_sup.mp this).resolve_left hx
      · intro hx hx'
        have : x ∈ T.basicOpen e ⊓ T.basicOpen (1 - e) := ⟨hx', hx⟩
        rw [h1] at this
        exact this
    rw [this]
    exact (T.basicOpen (1 - e)).2
  have h3 : s = r ⁻¹' (T.basicOpen e : Set T) := by
    rw [← hes]
    exact congrArg (fun O : Z.Opens => (O : Set Z)) (Scheme.preimage_basicOpen_top r e).symm
  rcases isClopen_iff.mp hcl with h | h
  · left; rw [h3, h, Set.preimage_empty]
  · right; rw [h3, h, Set.preimage_univ]

theorem isIso_of_isAffineHom {Z T : Scheme.{0}} (f : Z ⟶ T) [IsAffineHom f] (hf : ∀ V : T.Opens, IsIso (f.app V)) :
    IsIso f := by
  rw [← MorphismProperty.isomorphisms.iff, IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    _ (iSup_affineOpens_eq_top T)]
  intro V
  have : IsAffine V.1 := V.2
  have : IsAffine (f ⁻¹ᵁ V.1) := V.2.preimage f
  have : IsIso (f ∣_ V.1).appTop := by
    rw [morphismRestrict_appTop]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (hf (V.1.ι ''ᵁ ⊤)) (by rw [eqToHom_op]; exact Functor.map_isIso _ _)
  refine (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme) (arrowIsoSpecΓOfIsAffine _)).2 ?_
  exact inferInstanceAs (IsIso (Spec.map (f ∣_ V.1).appTop))

theorem flat_affineSpace (S : Scheme.{0}) (n : ℕ) : Flat (𝔸(Fin n; S) ↘ S) := by
  have hF : MorphismProperty.IsStableUnderBaseChange @Flat.{0} := inferInstance
  refine hF.of_isPullback (IsPullback.of_hasPullback _ _).flip ?_
  have := isIso_of_isTerminal specULiftZIsTerminal.{0} terminalIsTerminal (terminal.from _)
  have : Flat (Spec.map (CommRingCat.ofHom (MvPolynomial.C : ULift.{0} ℤ →+* MvPolynomial (Fin n) (ULift.{0} ℤ)))) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2
      ((RingHom.flat_algebraMap_iff (R := ULift ℤ) (S := MvPolynomial (Fin n) (ULift ℤ))).2 inferInstance)
  rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom MvPolynomial.C))]
  infer_instance

theorem exists_geometricPoint (Z : Scheme.{0}) (z : Z) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (s : Sp Ω ⟶ Z), ∀ y, s y = z := by
  refine ⟨AlgebraicClosure (Z.residueField z), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) (AlgebraicClosure (Z.residueField z)))) ≫
      Z.fromSpecResidueField z, fun y => ?_⟩
  rw [Scheme.Hom.comp_apply]
  exact Scheme.fromSpecResidueField_apply _ _

theorem isIso_finite_piece : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → ∀ (T : Scheme.{0}) (h : T ⟶ 𝔸(Fin g; Sp R)) (W : (pullback τ h).Opens) (p : ↥(pullback τ h)), Flat h → PreconnectedSpace T → p ∈ W → pullback.fst τ h p = x → IsFinite (W.ι ≫ pullback.snd τ h) → (∀ w ∈ W, pullback.snd τ h w = pullback.snd τ h p → w = p) → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ T), Set.range t = {pullback.snd τ h p} → ∃! w : Sp Ω ⟶ W.toScheme, w ≫ W.ι ≫ pullback.snd τ h = t) → IsIso (W.ι ≫ pullback.snd τ h) := by
  intro R _ _ _ _ S X π U a b g τ c hπ hπs hπb hUft hUsep ha haO hτ hc1 hc2 hc x hx hinj hsurj T h W p hh hT hpW hpx hfin hone huniq
  let α := 𝔸(Fin g; Sp R) ↘ Sp R
  have hbπ : b ≫ π = a ≫ τ ≫ α := by
    rw [← hc2, Category.assoc, ← pullback.condition, ← Category.assoc, hc1, Category.assoc]
  let s₁ := pullback.fst π (h ≫ α)
  let s₂ := pullback.snd π (h ≫ α)
  have HS : IsPullback s₁ s₂ π (h ≫ α) := .of_hasPullback _ _
  let m : pullback π (h ≫ α) ⟶ pullback α π := pullback.lift (s₂ ≫ h) s₁ (by rw [Category.assoc, HS.w])
  have Hm : IsPullback m s₂ (pullback.fst α π) h := by
    refine IsPullback.of_right (h₁₂ := pullback.snd α π) (v₁₃ := π) (h₂₂ := α) ?_ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback α π).flip
    rw [pullback.lift_snd]
    exact HS
  let x₁ := pullback.fst a (pullback.fst τ h)
  let x₂ := pullback.snd a (pullback.fst τ h)
  have HX : IsPullback x₁ x₂ a (pullback.fst τ h) := .of_hasPullback _ _
  have HX' : IsPullback x₁ (x₂ ≫ pullback.snd τ h) (a ≫ τ) h := HX.paste_vert (.of_hasPullback τ h)
  let n : pullback a (pullback.fst τ h) ⟶ pullback π (h ≫ α) := pullback.lift (x₁ ≫ b) (x₂ ≫ pullback.snd τ h) (by
    rw [Category.assoc, hbπ, ← Category.assoc a, ← Category.assoc x₁, HX'.w, Category.assoc])
  have hn1 : n ≫ s₁ = x₁ ≫ b := pullback.lift_fst _ _ _
  have hn2 : n ≫ s₂ = x₂ ≫ pullback.snd τ h := pullback.lift_snd _ _ _
  have Hn : IsPullback x₁ n c m := by
    refine IsPullback.of_bot (v₂₁ := s₂) (v₂₂ := pullback.fst α π) (h₃₁ := h) ?_ ?_ Hm
    · rw [hn2, hc1]
      exact HX'
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hc1, pullback.lift_fst, HX'.w, ← hn2, Category.assoc]
      · rw [Category.assoc, Category.assoc, hc2, pullback.lift_snd, hn1]
  have : Etale n := MorphismProperty.of_isPullback Hn hc
  let w₁ := pullback.fst x₂ W.ι
  let w₂ := pullback.snd x₂ W.ι
  have HW₀ : IsPullback w₁ w₂ x₂ W.ι := .of_hasPullback _ _
  have HW : IsPullback (w₁ ≫ x₁) w₂ a (W.ι ≫ pullback.fst τ h) := HW₀.paste_horiz HX
  have hq1 : (w₁ ≫ n) ≫ s₁ = (w₁ ≫ x₁) ≫ b := by rw [Category.assoc, hn1, Category.assoc]
  have hq2 : (w₁ ≫ n) ≫ s₂ = w₂ ≫ W.ι ≫ pullback.snd τ h := by
    rw [Category.assoc, hn2, ← Category.assoc, HW₀.w, Category.assoc]
  have hqe : Etale (w₁ ≫ n) := inferInstance
  have : IsProper w₂ := MorphismProperty.of_isPullback HW ha
  have : IsProper s₂ := MorphismProperty.of_isPullback HS hπ
  have : IsProper ((w₁ ≫ n) ≫ s₂) := by rw [hq2]; infer_instance
  have : IsProper (w₁ ≫ n) := IsProper.of_comp _ s₂
  have := GlobalTheory.TangentCrit.locallyQuasiFinite_of_formallyUnramified (w₁ ≫ n)
  have hqf : IsFinite (w₁ ≫ n) := IsFinite.of_isProper_of_locallyQuasiFinite _
  have : Flat α := flat_affineSpace _ _
  have hs₂ := GlobalTheory.Mum.app_bijective_of_flat_baseChange R S T _ π (h ≫ α) s₂ s₁ inferInstance inferInstance hπb
    inferInstance HS.flip
  have hconn := preconnectedSpace_of_surjective_appTop s₂ (hs₂ ⊤)
  have hs₂s : Surjective s₂ := MorphismProperty.of_isPullback HS hπs
  obtain ⟨z, hz⟩ := s₂.surjective (pullback.snd τ h p)
  obtain ⟨Ω, _, _, s, hs⟩ := exists_geometricPoint _ z
  obtain ⟨o⟩ : Nonempty (Sp Ω) := inferInstance
  have hrange : ∀ {Y : Scheme.{0}} (u : Sp Ω ⟶ Y) (y : Y), (∀ o', u o' = y) → Set.range u = {y} := by
    intro Y u y hu
    ext y'
    constructor
    · rintro ⟨o', rfl⟩
      exact hu o'
    · rintro rfl
      exact ⟨o, hu o⟩
  obtain ⟨w, hw, hwu⟩ := huniq Ω (s ≫ s₂) (hrange _ _ fun o' => by rw [Scheme.Hom.comp_apply, hs, hz])
  have hwp : ∀ o', W.ι (w o') = p := fun o' => by
    refine hone _ (w o').2 ?_
    change pullback.snd τ h (W.ι (w o')) = _
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply, hs, hz]
  have hξ : Set.range (w ≫ W.ι ≫ pullback.fst τ h) = {x} := hrange _ _ fun o' => by
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hwp, hpx]
  obtain ⟨y, hy1, hy2⟩ := hsurj Ω (w ≫ W.ι ≫ pullback.fst τ h) (s ≫ s₁) hξ (by
    rw [← hτ, Category.assoc s, HS.w, ← Category.assoc s, ← hw]
    simp only [Category.assoc]
    rw [pullback.condition_assoc])
  have hiso : IsIso (w₁ ≫ n) := by
    refine GlobalTheory.Mum.isIso_of_finite_etale_of_existsUnique_lift _ _ _ hqf hqe hconn Ω s ⟨HW.lift y w hy1, ?_, ?_⟩
    · apply HS.hom_ext
      · rw [Category.assoc, hq1, HW.lift_fst_assoc, hy2]
      · rw [Category.assoc, hq2, HW.lift_snd_assoc, hw]
    · intro y' hy'
      have e1 : y' ≫ w₂ = w := hwu _ (by
        change (y' ≫ w₂) ≫ _ = _
        rw [Category.assoc, ← hq2, ← hy', Category.assoc y'])
      have e2 : (y' ≫ w₁ ≫ x₁) ≫ a = w ≫ W.ι ≫ pullback.fst τ h := by
        rw [Category.assoc, HW.w, ← e1, Category.assoc]
      apply HW.hom_ext
      · rw [HW.lift_fst]
        refine hinj Ω _ _ (by rw [e2]; exact hξ) (e2.trans hy1.symm) ?_
        rw [hy2, Category.assoc, ← hq1, ← hy', Category.assoc y']
      · rw [HW.lift_snd, e1]
  have hw₂ := isIso_app_of_flat HW (fun V => (ConcreteCategory.isIso_iff_bijective _).mpr (haO V))
  refine isIso_of_isAffineHom _ fun V => ?_
  have h1 : IsIso ((w₂ ≫ W.ι ≫ pullback.snd τ h).app V) := by
    rw [← hq2, Scheme.Hom.comp_app]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ ((ConcreteCategory.isIso_iff_bijective _).mpr (hs₂ V))
      (inferInstanceAs (IsIso ((w₁ ≫ n).app (s₂ ⁻¹ᵁ V))))
  rw [Scheme.Hom.comp_app] at h1
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (hw₂ ((W.ι ≫ pullback.snd τ h) ⁻¹ᵁ V)) h1

end GlobalTheory.Mum.FlatChartDeg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoFinitePieceFlatConnectedChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIso_finite_piece_flat_connected_chart : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → ∀ (T : Scheme.{0}) (h : T ⟶ 𝔸(Fin g; Sp R)) (W : (pullback τ h).Opens) (p : ↥(pullback τ h)), Flat h → PreconnectedSpace T → p ∈ W → pullback.fst τ h p = x → IsFinite (W.ι ≫ pullback.snd τ h) → (∀ w ∈ W, pullback.snd τ h w = pullback.snd τ h p → w = p) → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ T), Set.range t = {pullback.snd τ h p} → ∃! w : Sp Ω ⟶ W.toScheme, w ≫ W.ι ≫ pullback.snd τ h = t) → IsIso (W.ι ≫ pullback.snd τ h) := by
  first | exact @GlobalTheory.Mum.FlatChartDeg.isIso_finite_piece | exact GlobalTheory.Mum.FlatChartDeg.isIso_finite_piece | (intros; apply GlobalTheory.Mum.FlatChartDeg.isIso_finite_piece <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleNeighbourhoodFinitePieceIsolatedPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleNeighbourhoodFinitePieceIsolatedPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.EtaleFinitePiece


open Polynomial in
theorem exists_etale_algebra (R L : Type) [CommRing R] [Field L] [Algebra R L] [Algebra.QuasiFinite R L] :
    ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (_ : Algebra.Etale R R₁) (ψ : R₁ →ₐ[R] L),
      ∀ (Ω : Type) [Field Ω] (a₁ a₂ : L →+* Ω),
        a₁.comp ψ.toRingHom = a₂.comp ψ.toRingHom → a₁ = a₂ := by
  let p : Ideal R := RingHom.ker (algebraMap R L)
  haveI : p.IsPrime := RingHom.ker_isPrime _
  let K := p.ResidueField
  letI : Algebra K L := (Ideal.ResidueField.lift p (algebraMap R L) le_rfl (by
    intro r hr
    exact (IsUnit.mem_submonoid_iff _).2 (isUnit_iff_ne_zero.2 (by simpa [p] using hr)))).toAlgebra
  haveI : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq fun r =>
    (Ideal.ResidueField.lift_algebraMap _ _ _ _ r).symm
  haveI : Algebra.QuasiFinite K L := .of_restrictScalars R K L
  haveI : Module.Finite K L := .of_quasiFinite
  let Ks := separableClosure K L
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element K Ks
  have hint : IsIntegral K θ := .of_finite K θ
  have hfrac : ∀ k : K, ∃ a c : R, algebraMap R K c ≠ 0 ∧ k * algebraMap R K c = algebraMap R K a := by
    intro k
    obtain ⟨a, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := R ⧸ p) k
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    have hc' : algebraMap (R ⧸ p) K (Ideal.Quotient.mk p c) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hc
    exact ⟨a, c, hc', div_mul_cancel₀ _ hc'⟩
  obtain ⟨c, hc, hcf⟩ : ∃ c : R, algebraMap R K c ≠ 0 ∧ ∀ i,
      (minpoly K θ).coeff i * algebraMap R K c ∈ (algebraMap R K).range := by
    choose a c hc hac using hfrac
    refine ⟨∏ i ∈ (minpoly K θ).support, c ((minpoly K θ).coeff i), ?_, fun i => ?_⟩
    · rw [map_prod]; exact Finset.prod_ne_zero_iff.2 fun i _ => hc _
    · by_cases hi : i ∈ (minpoly K θ).support
      · rw [← Finset.mul_prod_erase _ _ hi, map_mul, ← _root_.mul_assoc, hac, ← map_mul]
        exact ⟨_, rfl⟩
      · rw [notMem_support_iff.1 hi, zero_mul]; exact zero_mem _
  set c' := algebraMap R K c with hc'
  have hmin : minpoly K (c' • θ) = (minpoly K θ).scaleRoots c' :=
    IsIntegrallyClosed.minpoly_smul hc hint
  have hint' : IsIntegral K (c' • θ) := .of_finite K _
  have hl : minpoly K (c' • θ) ∈ lifts (algebraMap R K) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    rcases lt_trichotomy n (minpoly K θ).natDegree with h | h | h
    · rw [hmin, coeff_scaleRoots]
      obtain ⟨m, hm⟩ : ∃ m, (minpoly K θ).natDegree - n = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
      obtain ⟨u, hu⟩ := hcf n
      refine ⟨u * c ^ m, ?_⟩
      rw [hm, map_mul, hu, map_pow, pow_succ]; ring
    · rw [hmin, coeff_scaleRoots, h, Nat.sub_self, pow_zero, _root_.mul_one, (minpoly.monic hint).coeff_natDegree]
      exact ⟨1, map_one _⟩
    · rw [hmin, coeff_scaleRoots, coeff_eq_zero_of_natDegree_lt h, zero_mul]
      exact ⟨0, map_zero _⟩
  obtain ⟨F, hF, -, hFm⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hint')
  let P : StandardEtalePair R := ⟨F, hFm, derivative F, ⟨1, 0, 1, by simp⟩⟩
  have hsep : (minpoly K (c' • θ)).Separable := Algebra.IsSeparable.isSeparable K _
  have hP : P.HasMap (c' • θ) := by
    constructor
    · change aeval _ F = 0
      rw [← aeval_map_algebraMap K, hF, minpoly.aeval]
    · change IsUnit (aeval _ (derivative F))
      rw [← aeval_map_algebraMap K, ← derivative_map, hF]
      exact (hsep.aeval_derivative_ne_zero (minpoly.aeval _ _)).isUnit
  refine ⟨P.Ring, inferInstance, inferInstance, inferInstance,
    (Ks.val.restrictScalars R).comp (P.lift _ hP), fun Ω _ a₁ a₂ h => ?_⟩
  have hR : ∀ r : R, a₁ (algebraMap R L r) = a₂ (algebraMap R L r) := fun r => by
    have := congr($h (algebraMap R P.Ring r))
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, AlgHom.commutes] at this
    exact this
  have hK : ∀ k : K, a₁ (algebraMap K L k) = a₂ (algebraMap K L k) := fun k => by
    obtain ⟨a, d, hd, e⟩ := hfrac k
    have h2 : a₂ (algebraMap K L (algebraMap R K d)) ≠ 0 := by simpa using hd
    apply mul_right_cancel₀ h2
    rw [← map_mul, ← map_mul, e, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ← hR, ← hR,
      IsScalarTower.algebraMap_apply R K L, ← map_mul, ← map_mul, e, ← IsScalarTower.algebraMap_apply]
  have hX : a₁ ((c' • θ : Ks) : L) = a₂ ((c' • θ : Ks) : L) := by
    simpa using congr($h P.X)
  have hθ' : a₁ (θ : L) = a₂ (θ : L) := by
    have h2 : a₂ (algebraMap K L c') ≠ 0 := by simpa using hc
    apply mul_left_cancel₀ h2
    rw [← map_mul, ← hK, ← map_mul]
    simpa [Algebra.smul_def] using hX
  have hKs : a₁.comp (algebraMap Ks L) = a₂.comp (algebraMap Ks L) := by
    ext z
    have hz : z ∈ IntermediateField.adjoin K {θ} := hθ ▸ IntermediateField.mem_top
    induction hz using IntermediateField.adjoin_induction with
    | mem x hx => obtain rfl := hx; exact hθ'
    | algebraMap k => exact hK k
    | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    | inv x _ hx => rw [map_inv₀, map_inv₀, hx]
    | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]
  exact IsPurelyInseparable.injective_comp_algebraMap Ks L Ω hKs


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open TensorProduct in
theorem exists_finite_piece {X S : Scheme.{0}} (f : X ⟶ S) [LocallyOfFiniteType f]
    {x : X} (hx : f.QuasiFiniteAt x) :
    ∃ (T : Scheme.{0}) (g : T ⟶ S) (Z : Scheme.{0}) (io : Z ⟶ pullback f g) (z : Z), Etale g ∧
      IsOpenImmersion io ∧ IsFinite (io ≫ pullback.snd f g) ∧ (io ≫ pullback.fst f g) z = x ∧
      ∀ w, (io ≫ pullback.snd f g) w = (io ≫ pullback.snd f g) z → w = z := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hUV : V ≤ f ⁻¹ᵁ U⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).2
  have : (f.appLE U V hUV).hom.FiniteType := f.finiteType_appLE hU hV hUV
  algebraize [(f.appLE U V hUV).hom]
  have : (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.LiesOver (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal := by
    suffices hU.primeIdealOf ⟨f x, hxU⟩ = Spec.map (f.appLE U V hUV) (hV.primeIdealOf ⟨x, hxV⟩) from
      ⟨congr(($this).1)⟩
    apply hU.isoSpec.inv.homeomorph.injective
    apply Subtype.ext
    simp only [IsAffineOpen.primeIdealOf, Scheme.Hom.homeomorph_apply,
      ← Scheme.Hom.comp_apply, ← Scheme.Opens.ι_apply, IsAffineOpen.isoSpec_hom]
    simp
  have : Algebra.QuasiFiniteAt Γ(S, U) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    hx.quasiFiniteAt hV hU hUV hxV
  obtain ⟨R, _, _, _, P, _, _, e, _, P', _, hP'P, hP', heP', -, _, huniq⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq
    (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have hfin : (algebraMap R (Localization.Away e)).Finite := RingHom.finite_algebraMap.mpr ‹_›
  let φ : Γ(S, U) ⟶ .of R := CommRingCat.ofHom <| algebraMap Γ(S, U) R
  have hφ : φ.hom.Etale := RingHom.etale_algebraMap.mpr ‹_›
  have : Etale (Spec.map φ) := HasRingHomProperty.Spec_iff.mpr hφ
  let e₁ : Spec (.of (R ⊗[Γ(S, U)] Γ(X, V))) ≅ pullback (Spec.map (f.appLE U V hUV)) (Spec.map φ) :=
    (pullbackSpecIso _ _ _).symm ≪≫ pullbackSymmetry _ _
  have he₁ : e₁.hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) := by
    dsimp [e₁, RingHom.algebraMap_toAlgebra]
    rw [Category.assoc, pullbackSymmetry_hom_comp_fst]
    exact pullbackSpecIso_inv_snd ..
  let g : Spec (.of (R ⊗[Γ(S, U)] Γ(X, V))) ⟶ pullback f (Spec.map φ ≫ hU.fromSpec) :=
    e₁.hom ≫ pullback.map _ _ _ _ hV.fromSpec (𝟙 _) hU.fromSpec
      (IsAffineOpen.SpecMap_appLE_fromSpec ..) (by simp)
  let l : Spec (.of (Localization.Away e)) ⟶ Spec (.of (R ⊗[Γ(S, U)] Γ(X, V))) :=
    Spec.map (CommRingCat.ofHom <| algebraMap _ _)
  have hl : Set.range l = ((PrimeSpectrum.basicOpen e : TopologicalSpace.Opens (PrimeSpectrum _)) : Set (PrimeSpectrum _)) := PrimeSpectrum.localization_away_comap_range _ _
  have hg : g ≫ pullback.snd f _ = Spec.map (CommRingCat.ofHom (algebraMap R _)) := by
    have H : (pullbackSpecIso _ R _).inv ≫ pullback.fst _ (Spec.map (f.appLE U V hUV)) = _ :=
      pullbackSpecIso_inv_fst ..
    simp [g, e₁, RingHom.algebraMap_toAlgebra, φ, H]
    rfl
  obtain ⟨z, hz⟩ : (⟨P', ‹_›⟩ : PrimeSpectrum _) ∈ Set.range l := by rw [hl]; exact heP'
  refine ⟨Spec (.of R), Spec.map φ ≫ hU.fromSpec, _, l ≫ g, z, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · rw [Category.assoc, hg, ← Spec.map_comp, IsFinite.SpecMap_iff]
    exact hfin
  · rw [Category.assoc, Scheme.Hom.comp_apply, hz]
    trans hV.fromSpec ⟨P'.comap Algebra.TensorProduct.includeRight.toRingHom, inferInstance⟩
    · simp [-Scheme.Hom.comp_base, g, reassoc_of% he₁]; rfl
    convert! hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  · intro w hw
    rw [Category.assoc, hg, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hz] at hw
    apply l.isOpenEmbedding.injective
    rw [hz]
    have h1 : l w ∈ ((PrimeSpectrum.basicOpen e : TopologicalSpace.Opens (PrimeSpectrum _)) : Set (PrimeSpectrum _)) := hl ▸ Set.mem_range_self w
    refine PrimeSpectrum.ext (huniq _ inferInstance ⟨?_⟩ h1)
    exact hP'P.over.trans congr(($hw).1).symm

theorem exists_factor_of_isPreimmersion {A X : Scheme.{0}} (j : A ⟶ X) [IsPreimmersion j]
    {Ω : Type} [Field Ω] (w : Spec (.of Ω) ⟶ X) (h : ∀ s, w s ∈ Set.range j) :
    ∃ c : Spec (.of Ω) ⟶ A, c ≫ j = w := by
  have : IsClosedImmersion (pullback.snd j w) := .of_isPreimmersion _ (isClosed_discrete _)
  have : Surjective (pullback.snd j w) := ⟨fun s => by
    obtain ⟨a, ha⟩ := h s
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback _ _ ha
    exact ⟨z, hz⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective (pullback.snd j w)
  exact ⟨inv (pullback.snd j w) ≫ pullback.fst j w, by simp [pullback.condition]⟩

theorem exists_lift_of_isAlgClosed {Z T : Scheme.{0}} (b : Z ⟶ T) [LocallyOfFiniteType b]
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) (s) (h : t s ∈ Set.range b) :
    ∃ w : Spec (.of Ω) ⟶ Z, w ≫ b = t := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ ha
  have : JacobsonSpace ↥(pullback b t) := LocallyOfFiniteType.jacobsonSpace (pullback.snd b t)
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback b t))) ⟨z, trivial⟩
    isOpen_univ.isLocallyClosed
  have hx' : IsClosed {x} := hx
  exact ⟨pointOfClosedPoint (pullback.snd b t) x hx' ≫ pullback.fst b t, by rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]⟩

theorem exists_etale_point {Y : Scheme.{0}} {L : Type} [Field L] (y : Spec (.of L) ⟶ Y)
    [LocallyQuasiFinite y] :
    ∃ (T : Scheme.{0}) (h : T ⟶ Y) (s : Spec (.of L) ⟶ T), Etale h ∧ s ≫ h = y ∧
      ∀ (Ω : Type) [Field Ω] (c₁ c₂ : Spec (.of Ω) ⟶ Spec (.of L)), c₁ ≫ s = c₂ ≫ s → c₁ = c₂ := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (y (closedPoint L))) isOpen_univ
  obtain ⟨R, io, _, hio⟩ : ∃ (R : CommRingCat.{0}) (io : Spec R ⟶ Y) (_ : IsOpenImmersion io),
      y (closedPoint L) ∈ Set.range io := ⟨_, hV.fromSpec, hV.isOpenImmersion_fromSpec, by rwa [hV.range_fromSpec]⟩
  obtain ⟨c, rfl⟩ := exists_factor_of_isPreimmersion io y fun s => by
    rwa [Subsingleton.elim s (closedPoint L)]
  obtain ⟨φ, rfl⟩ := Spec.map_surjective c
  have hq : LocallyQuasiFinite (Spec.map φ) := .of_comp _ io
  rw [HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)] at hq
  algebraize [φ.hom]
  obtain ⟨R₁, _, _, _, ψ, hψ⟩ := exists_etale_algebra R L
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap R R₁))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr ‹_›)
  refine ⟨Spec (.of R₁), Spec.map (CommRingCat.ofHom (algebraMap R R₁)) ≫ io,
    Spec.map (CommRingCat.ofHom ψ.toRingHom), inferInstance, ?_, fun Ω _ c₁ c₂ h => ?_⟩
  · rw [← Spec.map_comp_assoc]
    congr 2
    ext r
    exact ψ.commutes r
  · obtain ⟨a₁, rfl⟩ := Spec.map_surjective c₁
    obtain ⟨a₂, rfl⟩ := Spec.map_surjective c₂
    rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at h
    congr 1
    exact CommRingCat.hom_ext (hψ Ω _ _ congr(($h).hom))

theorem quasiFiniteAt_of_isolated {H X : Scheme.{0}} (φ : H ⟶ X) [LocallyOfFiniteType φ]
    (z : H) (O : H.Opens) (hzO : z ∈ O) (hO : ∀ w ∈ O, φ w = φ z → w = z) : φ.QuasiFiniteAt z := by
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber, ← (φ.fiberHomeo (φ z)).isOpen_image]
  simp only [Set.image_singleton, Scheme.Hom.asFiber, Homeomorph.apply_symm_apply]
  rw [isOpen_induced_iff]
  refine ⟨O, O.isOpen, ?_⟩
  ext ⟨w, hw⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    exact Subtype.ext (hO w h hw)
  · intro h
    have : w = z := congrArg Subtype.val h
    exact this ▸ hzO


set_option backward.isDefEq.respectTransparency false in
theorem main : ∀ (U Y : Scheme.{0}) (τ : U ⟶ Y), IsLocallyNoetherian Y → LocallyOfFiniteType τ → IsSeparated τ →
    ∀ x : U, (∃ O : U.Opens, x ∈ O ∧ ∀ u ∈ O, τ u = τ x → u = x) →
    ∃ (T : Scheme.{0}) (h : T ⟶ Y) (W : (pullback τ h).Opens) (p : ↥(pullback τ h)),
      Etale h ∧ PreconnectedSpace T ∧ p ∈ W ∧ pullback.fst τ h p = x ∧ IsFinite (W.ι ≫ pullback.snd τ h) ∧
      (∀ w ∈ W, pullback.snd τ h w = pullback.snd τ h p → w = p) ∧
      ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ T), Set.range t = {pullback.snd τ h p} →
        ∃! w : Sp Ω ⟶ W.toScheme, w ≫ W.ι ≫ pullback.snd τ h = t := by
  intro U Y τ _ _ _ x ⟨O, hxO, hO⟩
  have hx : τ.QuasiFiniteAt x := quasiFiniteAt_of_isolated τ x O hxO hO

  let Q : U.Opens := τ.quasiFiniteLocus
  have hxQ : x ∈ Q := hx
  have hQ : LocallyQuasiFinite (Q.ι ≫ τ) := by
    rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff, Scheme.Hom.quasiFiniteLocus_comp]
    exact top_le_iff.mp fun u _ => by
      show Q.ι u ∈ Q
      simpa using u.2
  have hfx : ∀ a : Spec (.of (U.residueField x)), U.fromSpecResidueField x a = x :=
    fun a => Scheme.fromSpecResidueField_apply x a

  let y₀ : Spec (.of (U.residueField x)) ⟶ Y := U.fromSpecResidueField x ≫ τ
  have : LocallyQuasiFinite y₀ := by
    rw [Scheme.Hom.quasiFiniteAt_iff] at hx
    dsimp only [y₀, Scheme.fromSpecResidueField]
    rw [Category.assoc]
    infer_instance
  obtain ⟨T₁, h₁, s, _, hs, hsep⟩ := exists_etale_point y₀
  let j : Spec (.of (U.residueField x)) ⟶ pullback τ h₁ :=
    pullback.lift (U.fromSpecResidueField x) s (by rw [hs])
  have hjf : j ≫ pullback.fst τ h₁ = U.fromSpecResidueField x := pullback.lift_fst ..
  have hjs : j ≫ pullback.snd τ h₁ = s := pullback.lift_snd ..
  haveI : IsPreimmersion (j ≫ pullback.fst τ h₁) := by rw [hjf]; infer_instance
  haveI : IsPreimmersion j := AmpUniq.isPreimmersion_of_comp j (pullback.fst τ h₁)
  let x₁ := j (closedPoint _)

  let σ : Spec (.of (U.residueField x)) ⟶ Q :=
    IsOpenImmersion.lift Q.ι (U.fromSpecResidueField x) (by
      rintro _ ⟨a, rfl⟩
      exact ⟨⟨x, hxQ⟩, (hfx a).symm⟩)
  let j' : Spec (.of (U.residueField x)) ⟶ pullback (Q.ι ≫ τ) h₁ :=
    pullback.lift σ s (by rw [← Category.assoc, IsOpenImmersion.lift_fac, hs])
  let m := pullback.map (Q.ι ≫ τ) h₁ τ h₁ Q.ι (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hjm : j' ≫ m = j := by
    apply pullback.hom_ext
    · simp [m, j', j, σ]
    · simp [m, j', j]
  have hqf : (pullback.snd τ h₁).QuasiFiniteAt x₁ := by
    have hms : m ≫ pullback.snd τ h₁ = pullback.snd (Q.ι ≫ τ) h₁ := by simp [m]
    have : x₁ = m (j' (closedPoint _)) := by
      simp only [x₁, ← hjm, Scheme.Hom.comp_apply]
    rw [this, ← Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion, hms]
    exact Scheme.Hom.quasiFiniteAt _ _

  obtain ⟨T₂, g₂, Z, io, z, _, _, hfin, hz, huniq⟩ := exists_finite_piece (pullback.snd τ h₁) hqf
  let b := io ≫ pullback.snd (pullback.snd τ h₁) g₂
  have hbg : ∀ {V : Scheme.{0}} (u : V ⟶ Z), u ≫ io ≫ pullback.fst _ _ ≫ pullback.snd τ h₁ = u ≫ b ≫ g₂ := by
    intro V u; simp [b, pullback.condition]

  have G : ∀ (Ω : Type) [Field Ω] (u₁ u₂ : Spec (.of Ω) ⟶ Z), u₁ ≫ b = u₂ ≫ b →
      (∀ a, u₁ a = z) → (∀ a, u₂ a = z) → u₁ = u₂ := by
    intro Ω _ u₁ u₂ hb h₁' h₂'
    have hr : ∀ u : Spec (.of Ω) ⟶ Z, (∀ a, u a = z) →
        ∃ c : Spec (.of Ω) ⟶ Spec (.of (U.residueField x)), c ≫ j = u ≫ io ≫ pullback.fst _ _ :=
      fun u hu => exists_factor_of_isPreimmersion j _ fun a => ⟨closedPoint _, by
        simp only [Scheme.Hom.comp_apply, hu]
        exact hz.symm⟩
    obtain ⟨c₁, hc₁⟩ := hr u₁ h₁'
    obtain ⟨c₂, hc₂⟩ := hr u₂ h₂'
    have hcs : ∀ (c : Spec (.of Ω) ⟶ Spec (.of (U.residueField x))) (u : Spec (.of Ω) ⟶ Z),
        c ≫ j = u ≫ io ≫ pullback.fst _ _ → c ≫ s = u ≫ b ≫ g₂ := by
      intro c u hcu
      rw [← hjs, ← Category.assoc, hcu, Category.assoc, Category.assoc, hbg]
    have hc : c₁ = c₂ := hsep Ω c₁ c₂ (by rw [hcs c₁ u₁ hc₁, hcs c₂ u₂ hc₂, reassoc_of% hb])
    rw [← cancel_mono io]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, ← hc₁, ← hc₂, hc]
    · simpa [b] using hb

  haveI : IsLocallyNoetherian T₂ := LocallyOfFiniteType.isLocallyNoetherian (g₂ ≫ h₁)
  let C : T₂.Opens := ⟨connectedComponent (b z),
    GlobalTheory.isOpen_connectedComponent_of_isLocallyNoetherian T₂ inferInstance (b z)⟩
  have hzC : b z ∈ C := mem_connectedComponent
  let h : C.toScheme ⟶ Y := C.ι ≫ g₂ ≫ h₁
  let Z' : Z.Opens := b ⁻¹ᵁ C
  let b' : Z'.toScheme ⟶ C.toScheme := b ∣_ C
  have hb' : b' ≫ C.ι = Z'.ι ≫ b := morphismRestrict_ι b C
  let io' : Z'.toScheme ⟶ pullback τ h :=
    pullback.lift (Z'.ι ≫ io ≫ pullback.fst _ _ ≫ pullback.fst τ h₁) b' (by
      simp only [h, Category.assoc, pullback.condition]
      rw [reassoc_of% hb']
      simpa using congr($(hbg Z'.ι) ≫ h₁))
  have hio'f : io' ≫ pullback.fst τ h = Z'.ι ≫ io ≫ pullback.fst _ _ ≫ pullback.fst τ h₁ := pullback.lift_fst ..
  have hio's : io' ≫ pullback.snd τ h = b' := pullback.lift_snd ..
  let mC := pullback.map τ h τ (g₂ ≫ h₁) (𝟙 _) C.ι (𝟙 _) (by simp) (by simp [h])
  have hmC : io' ≫ mC = Z'.ι ≫ io ≫ (pullbackLeftPullbackSndIso τ h₁ g₂).hom := by
    apply pullback.hom_ext
    · simp [mC, hio'f]
    · simp only [mC, Category.assoc, pullback.lift_snd, pullbackLeftPullbackSndIso_hom_snd]
      rw [← Category.assoc, hio's, hb']
  haveI : IsOpenImmersion (io' ≫ mC) := by rw [hmC]; infer_instance
  haveI : IsOpenImmersion io' := IsOpenImmersion.of_comp io' mC
  let z' : Z' := ⟨z, hzC⟩
  haveI : IsFinite b := hfin
  have hb'inj : ∀ w : Z', b' w = b' z' → w = z' := by
    intro w hw
    apply Subtype.ext
    apply huniq
    have := congr(C.ι $hw)
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hb', Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply] at this
    simp only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] at this ⊢
    exact this
  have he : io'.opensRange.ι = io'.isoOpensRange.inv ≫ io' := by
    rw [Iso.eq_inv_comp, Scheme.Hom.isoOpensRange_hom_ι]
  refine ⟨C.toScheme, h, io'.opensRange, io' z', inferInstance, ?_, ⟨z', rfl⟩, ?_, ?_, ?_, ?_⟩
  · exact isPreconnected_iff_preconnectedSpace.mp isPreconnected_connectedComponent
  · rw [← Scheme.Hom.comp_apply, hio'f]
    simp only [Scheme.Hom.comp_apply]
    change pullback.fst τ h₁ ((io ≫ pullback.fst _ _) z) = x
    rw [hz, ← Scheme.Hom.comp_apply, hjf]
    exact hfx _
  · rw [he, Category.assoc, hio's, MorphismProperty.cancel_left_of_respectsIso @IsFinite]
    infer_instance
  · rintro _ ⟨w, rfl⟩ hw
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hio's] at hw
    rw [hb'inj w hw]
  · intro Ω _ _ t ht
    have hpt : pullback.snd τ h (io' z') = b' z' := by rw [← Scheme.Hom.comp_apply, hio's]
    have htz : ∀ a, t a = b' z' := fun a => by
      rw [← hpt]
      have : t a ∈ Set.range t := Set.mem_range_self a
      rwa [ht] at this
    have hpts : ∀ u : Spec (.of Ω) ⟶ Z', u ≫ b' = t → ∀ a, (u ≫ Z'.ι) a = z := fun u hu a => by
      have : b' (u a) = b' z' := by rw [← Scheme.Hom.comp_apply, hu, htz]
      rw [Scheme.Hom.comp_apply, hb'inj _ this]
      simp [z']
    obtain ⟨w₀, hw₀⟩ := exists_lift_of_isAlgClosed b' t (closedPoint Ω) ⟨z', (htz _).symm⟩
    refine ⟨w₀ ≫ io'.isoOpensRange.hom, ?_, fun w hw => ?_⟩
    · rw [he]
      simp [hio's, hw₀]
    · have hv : w ≫ io'.isoOpensRange.inv ≫ b' = t := by
        rw [← hw, ← hio's, he]
        simp only [Category.assoc]
      have key : (w ≫ io'.isoOpensRange.inv) ≫ Z'.ι = w₀ ≫ Z'.ι :=
        G Ω _ _ (by simp only [Category.assoc]; rw [← hb', reassoc_of% hv, reassoc_of% hw₀])
          (hpts _ (by rw [Category.assoc]; exact hv)) (hpts _ hw₀)
      have hv' : w ≫ io'.isoOpensRange.inv = w₀ := by rw [← cancel_mono Z'.ι]; exact key
      rw [← hv']
      simp

end GlobalTheory.EtaleFinitePiece
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleNeighbourhoodFinitePieceIsolatedPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etale_neighbourhood_finite_piece_isolated_point : ∀ (U Y : Scheme.{0}) (τ : U ⟶ Y), IsLocallyNoetherian Y → LocallyOfFiniteType τ → IsSeparated τ → ∀ x : U, (∃ O : U.Opens, x ∈ O ∧ ∀ u ∈ O, τ u = τ x → u = x) → ∃ (T : Scheme.{0}) (h : T ⟶ Y) (W : (pullback τ h).Opens) (p : ↥(pullback τ h)), Etale h ∧ PreconnectedSpace T ∧ p ∈ W ∧ pullback.fst τ h p = x ∧ IsFinite (W.ι ≫ pullback.snd τ h) ∧ (∀ w ∈ W, pullback.snd τ h w = pullback.snd τ h p → w = p) ∧ ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ T), Set.range t = {pullback.snd τ h p} → ∃! w : Sp Ω ⟶ W.toScheme, w ≫ W.ι ≫ pullback.snd τ h = t := by
  first | exact @GlobalTheory.EtaleFinitePiece.main | exact GlobalTheory.EtaleFinitePiece.main | (intros; apply GlobalTheory.EtaleFinitePiece.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatChartEtaleOfQuasiFiniteAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.exists_flat_chart_etale_of_quasiFiniteAt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, IsClosed ({x} : Set U.left) → U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → (∃ O : U.left.Opens, x ∈ O ∧ ∀ u ∈ O, τ u = τ x → u = x) → ∃ (T : Scheme.{0}) (h : T ⟶ 𝔸(Fin g; Sp R)) (W : (pullback τ h).Opens) (p : ↥(pullback τ h)), Flat h ∧ p ∈ W ∧ pullback.fst τ h p = x ∧ Etale (W.ι ≫ pullback.snd τ h) := by
  intro R _ _ _ hR S X π U a b g τ c hπp hπs hπΓ hUf hUs ha haΓ hτ hc1 hc2 hc x hxc hxm hinj hsurj hqf
  have hτf : LocallyOfFiniteType τ := by
    have : LocallyOfFiniteType (τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R)) := by rw [hτ]; exact hUf
    exact locallyOfFiniteType_of_comp τ (𝔸(Fin g; Sp R) ↘ Sp R)
  have hτs : IsSeparated τ := by
    have : IsSeparated (τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R)) := by rw [hτ]; exact hUs
    exact IsSeparated.of_comp τ (𝔸(Fin g; Sp R) ↘ Sp R)
  have : IsNoetherianRing R := hR.1
  have hA : IsLocallyNoetherian 𝔸(Fin g; Sp R) := LocallyOfFiniteType.isLocallyNoetherian (𝔸(Fin g; Sp R) ↘ Sp R)
  obtain ⟨T, h, W, p, het, hcon, hpW, hpx, hfin, hone, hgeo⟩ := GlobalTheory.T.exists_etale_neighbourhood_finite_piece_isolated_point _ _ τ hA hτf hτs x hqf
  have hiso := GlobalTheory.T.isIso_finite_piece_flat_connected_chart R hR S X π U a b g τ c hπp hπs hπΓ hUf hUs ha haΓ hτ hc1 hc2 hc x hxm hinj hsurj
    T h W p inferInstance hcon hpW hpx hfin hone hgeo
  exact ⟨T, h, W, p, inferInstance, hpW, hpx, inferInstance⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatChartEtaleOfQuasiFiniteAtStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flat_chart_etale_of_quasiFiniteAt_alt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, IsClosed ({x} : Set U.left) → U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → (∃ O : U.left.Opens, x ∈ O ∧ ∀ u ∈ O, τ u = τ x → u = x) → ∃ (T : Scheme.{0}) (h : T ⟶ 𝔸(Fin g; Sp R)) (W : (pullback τ h).Opens) (p : ↥(pullback τ h)), Flat h ∧ p ∈ W ∧ pullback.fst τ h p = x ∧ Etale (W.ι ≫ pullback.snd τ h) := by
  first | exact @GlobalTheory.Mum.exists_flat_chart_etale_of_quasiFiniteAt | exact GlobalTheory.Mum.exists_flat_chart_etale_of_quasiFiniteAt | (intros; apply GlobalTheory.Mum.exists_flat_chart_etale_of_quasiFiniteAt <;> assumption)
end
