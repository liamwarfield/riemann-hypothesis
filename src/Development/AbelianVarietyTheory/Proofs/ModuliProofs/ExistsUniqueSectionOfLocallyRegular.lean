module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsInvariantSectionMemBasicOpenIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueSectionOfLocallyRegular
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueSectionOfLocallyRegular
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.GlueFn

end GlobalTheory.GlueFn

namespace GlobalTheory

private lemma exists_complex_section_through_closed_point (X : Scheme) (p : X ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFiniteType p] (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ q : Spec (CommRingCat.of ℂ) ⟶ X, q ≫ p = 𝟙 _ ∧ ∀ s, q.base s = x := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  have h1 : LocallyOfFiniteType (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hx
  have h2 : LocallyOfFiniteType (X.fromSpecResidueField x ≫ p) := inferInstance
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = X.fromSpecResidueField x ≫ p :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  rw [← hφ] at h2
  have hft : φ.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp h2
  letI := φ.hom.toAlgebra
  haveI : Algebra.FiniteType ℂ (X.residueField x) := hft
  haveI : Module.Finite ℂ (X.residueField x) := finite_of_finite_type_of_isJacobsonRing ℂ _
  have hsurj : Function.Surjective (algebraMap ℂ (X.residueField x)) := by
    apply IsSepClosed.algebraMap_surjective
  let e := RingEquiv.ofBijective (algebraMap ℂ (X.residueField x))
    ⟨(algebraMap ℂ _).injective, hsurj⟩
  refine ⟨Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ X.fromSpecResidueField x, ?_, ?_⟩
  · rw [Category.assoc, ← hφ, ← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of ℂ)
    ext a
    exact e.symm_apply_apply a
  · intro s
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

private lemma valAt'_sub_of_top_le {X : Scheme} (q : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X) (U : X.Opens) (hU : ⊤ ≤ q ⁻¹ᵁ U)
    (a b : Γ(X, U)) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' q U (a - b) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' q U a - _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' q U b := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt'
  rw [dite_eq_left hU, dite_eq_left hU, dite_eq_left hU]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt
  simp only [map_sub]

private lemma not_mem_basicOpen_of_valAt'_eq_zero {X : Scheme} (q : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X)
    (U : X.Opens) (hU : ⊤ ≤ q ⁻¹ᵁ U) (f : Γ(X, U)) (hf : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' q U f = 0)
    (s : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) : q.base s ∉ X.basicOpen f := by
  intro hs
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' at hf
  rw [dite_eq_left hU] at hf
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt at hf
  have h0 : q.appLE U ⊤ hU f = 0 := by
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom hf
    simpa using this
  have hmem : s ∈ q ⁻¹ᵁ X.basicOpen f := hs
  rw [Scheme.Hom.preimage_basicOpen] at hmem
  have hres : (Spec (CommRingCat.of ℂ)).basicOpen (q.appLE U ⊤ hU f) =
      ⊤ ⊓ (Spec (CommRingCat.of ℂ)).basicOpen (q.app U f) := by
    rw [← Scheme.basicOpen_res]
    rfl
  rw [h0, Scheme.basicOpen_zero] at hres
  have : s ∈ (⊤ ⊓ (Spec (CommRingCat.of ℂ)).basicOpen (q.app U f) :
      (Spec (CommRingCat.of ℂ)).Opens) := ⟨trivial, hmem⟩
  rw [← hres] at this
  exact this

private lemma valAt'_presheaf_map {X : Scheme} (q : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X) {U V : X.Opens} (i : V ⟶ U)
    (hV : ⊤ ≤ q ⁻¹ᵁ V) (a : Γ(X, U)) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' q V (X.presheaf.map i.op a) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' q U a := by
  have hU : ⊤ ≤ q ⁻¹ᵁ U := fun s hs => i.le (hV hs)
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt'
  rw [dite_eq_left hU, dite_eq_left hV]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt
  rw [← Scheme.Hom.map_appLE q hV i.op]
  rfl

theorem _root_.GlobalTheory.existsUnique_section_of_locally_regular :
    ∀ (P₀ : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)) (u : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), _root_.GlobalTheory.KS.GoodU u Hm χ → ∀ (O : P₀.A.left.Opens) (h : (Fin P₀.g → ℂ) → ℂ), (∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O → ∃ (O' : P₀.A.left.Opens) (a : Γ(P₀.A.left, O')), O' ≤ O ∧ ⊤ ≤ (u.ex z).left ⁻¹ᵁ O' ∧ ∀ z', ⊤ ≤ (u.ex z').left ⁻¹ᵁ O' → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex z').left O' a = h z') → ∃! a : Γ(P₀.A.left, O), ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex z).left O a = h z := by
  intro P₀ u Hm χ _ O h H
  haveI := P₀.smoothDim
  have hsm : Smooth P₀.A.hom := SmoothOfRelativeDimension.smooth P₀.g P₀.A.hom
  haveI := hsm
  haveI : IsReduced P₀.A.left := _root_.GlobalTheory.isReduced_of_smooth_complex _ _ hsm
  haveI : JacobsonSpace P₀.A.left := LocallyOfFiniteType.jacobsonSpace P₀.A.hom
  have hpt : ∀ y : P₀.A.left, IsClosed ({y} : Set P₀.A.left) →
      ∃ z, ∀ s, (u.ex z).left.base s = y := by
    intro y hy
    obtain ⟨q, hq, hqy⟩ := exists_complex_section_through_closed_point P₀.A.left P₀.A.hom y hy
    obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk q hq : 𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)) ⟶ P₀.A)
    exact ⟨z, fun s => by rw [hz]; exact hqy s⟩
  have hs₀ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ := IsLocalRing.closedPoint ℂ
  have huniq : ∀ (V : P₀.A.left.Opens) (a b : Γ(P₀.A.left, V)), (∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ V →
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex z).left V a = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex z).left V b) → a = b := by
    intro V a b hab
    rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
    by_contra hne
    obtain ⟨y, hyB, hyc⟩ := nonempty_inter_closedPoints
      ((TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp hne)
      (P₀.A.left.basicOpen (a - b)).isOpen.isLocallyClosed
    obtain ⟨z, hz⟩ := hpt y (mem_closedPoints_iff.mp hyc)
    have hzV : ⊤ ≤ (u.ex z).left ⁻¹ᵁ V := fun s _ => by
      show (u.ex z).left.base s ∈ V
      rw [hz]
      exact P₀.A.left.basicOpen_le _ hyB
    have h0 : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex z).left V (a - b) = 0 := by
      rw [valAt'_sub_of_top_le _ _ hzV, hab z hzV, sub_self]
    exact not_mem_basicOpen_of_valAt'_eq_zero _ _ hzV _ h0 hs₀ (by rw [hz]; exact hyB)
  have hloc : ∀ w : {z // ⊤ ≤ (u.ex z).left ⁻¹ᵁ O}, ∃ (O' : P₀.A.left.Opens)
      (a : Γ(P₀.A.left, O')), O' ≤ O ∧ ⊤ ≤ (u.ex w.1).left ⁻¹ᵁ O' ∧ ∀ z', ⊤ ≤ (u.ex z').left ⁻¹ᵁ O' →
        _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex z').left O' a = h z' := fun w => H w.1 w.2
  choose W aW hWO hWz hWv using hloc
  have hcover : O ≤ iSup W := by
    by_contra hle
    have hZ : ((O : Set P₀.A.left) ∩ ((iSup W : P₀.A.left.Opens) : Set P₀.A.left)ᶜ).Nonempty := by
      rw [← Set.diff_eq, Set.diff_nonempty]
      exact hle
    have hZlc : IsLocallyClosed ((O : Set P₀.A.left) ∩ ((iSup W : P₀.A.left.Opens) : Set P₀.A.left)ᶜ) :=
      ⟨O, ((iSup W : P₀.A.left.Opens) : Set P₀.A.left)ᶜ, O.isOpen, (iSup W).isOpen.isClosed_compl, rfl⟩
    obtain ⟨y, ⟨hyO, hyW⟩, hyc⟩ := nonempty_inter_closedPoints hZ hZlc
    obtain ⟨z, hz⟩ := hpt y (mem_closedPoints_iff.mp hyc)
    have hzO : ⊤ ≤ (u.ex z).left ⁻¹ᵁ O := fun s _ => by
      show (u.ex z).left.base s ∈ O
      rw [hz]
      exact hyO
    have hyz : y ∈ W ⟨z, hzO⟩ := by
      rw [← hz hs₀]
      exact hWz ⟨z, hzO⟩ (show hs₀ ∈ (⊤ : (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ).Opens) from trivial)
    exact hyW (TopologicalSpace.Opens.mem_iSup.mpr ⟨_, hyz⟩)
  have hcompat : TopCat.Presheaf.IsCompatible P₀.A.left.sheaf.obj W aW := by
    intro i j
    apply huniq
    intro z hz
    have hi : ⊤ ≤ (u.ex z).left ⁻¹ᵁ W i := fun s hs => (inf_le_left : W i ⊓ W j ≤ W i) (hz hs)
    have hj : ⊤ ≤ (u.ex z).left ⁻¹ᵁ W j := fun s hs => (inf_le_right : W i ⊓ W j ≤ W j) (hz hs)
    erw [valAt'_presheaf_map _ _ hz, valAt'_presheaf_map _ _ hz]
    rw [hWv i z hi, hWv j z hj]
  obtain ⟨a, ha, -⟩ := P₀.A.left.sheaf.existsUnique_gluing' W O (fun i => homOfLE (hWO i))
    hcover aW hcompat
  have hval : ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex z).left O a = h z := by
    intro z hz
    rw [← valAt'_presheaf_map (u.ex z).left (homOfLE (hWO ⟨z, hz⟩)) (hWz ⟨z, hz⟩) a]
    erw [ha ⟨z, hz⟩]
    exact hWv ⟨z, hz⟩ z (hWz ⟨z, hz⟩)
  refine ⟨a, hval, fun b hb => huniq O b a fun z hz => ?_⟩
  rw [hb z hz, hval z hz]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueSectionOfLocallyRegularStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
theorem _root_.GlobalTheory.T.existsUnique_section_of_locally_given_values : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (O : P₀.A.left.Opens) (h : (Fin P₀.g → ℂ) → ℂ), (∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O → ∃ (O' : P₀.A.left.Opens) (a : Γ(P₀.A.left, O')), O' ≤ O ∧ ⊤ ≤ (u.ex z).left ⁻¹ᵁ O' ∧ ∀ z', ⊤ ≤ (u.ex z').left ⁻¹ᵁ O' → valAt' (u.ex z').left O' a = h z') → ∃! a : Γ(P₀.A.left, O), ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O → valAt' (u.ex z).left O a = h z := by
  first | exact @GlobalTheory.existsUnique_section_of_locally_regular | exact GlobalTheory.existsUnique_section_of_locally_regular | (intros; apply GlobalTheory.existsUnique_section_of_locally_regular <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientOfFiniteGroup
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

namespace QuotientGluing

variable {G : Type} [Group G] [Finite G] {X : Scheme.{0}}

theorem isOpenImmersion_desc {T T' Y Y' : Scheme.{0}} {σ : G →* Aut T} {σ' : G →* Aut T'}
    {q : T ⟶ Y} {q' : T' ⟶ Y'} (h : IsAffineQuotient σ q) (h' : IsAffineQuotient σ' q')
    (m : T ⟶ T') [IsOpenImmersion m] (hm : ∀ g, (σ g).asIso.hom ≫ m = m ≫ (σ' g).asIso.hom)
    (k : Y ⟶ Y') (hk : q ≫ k = m ≫ q') : IsOpenImmersion k := by
  obtain ⟨W, hW⟩ := h'.exists_preimage_eq (U := m.opensRange) (fun g ↦ by
    rintro _ ⟨x, rfl⟩
    exact ⟨(σ g).asIso.hom x, congr($(hm g) x)⟩)
  have hr : Set.range (m ≫ q') ⊆ Set.range W.ι := by
    rintro _ ⟨x, rfl⟩
    have : m x ∈ q' ⁻¹ᵁ W := hW ▸ ⟨x, rfl⟩
    exact ⟨⟨q' (m x), this⟩, rfl⟩
  let l : T ⟶ W := IsOpenImmersion.lift W.ι (m ≫ q') hr
  have hl : l ≫ W.ι = m ≫ q' := IsOpenImmersion.lift_fac _ _ _
  have H : IsPullback l m W.ι q' :=
    IsOpenImmersion.isPullback _ _ _ _ hl.symm (by rw [Scheme.Opens.opensRange_ι, hW])
  have hq : IsAffineQuotient σ l := h'.of_isPullback H.flip hm fun g ↦ by
    rw [← cancel_mono W.ι, Category.assoc, hl, reassoc_of% hm, h'.comp_eq]
  have : k = (h.uniqueIso hq).hom ≫ W.ι := h.hom_ext (by simp [hk, hl])
  rw [this]
  infer_instance

omit [Finite G] in
theorem app_of_chart {T Y Y' : Scheme.{0}} {ρ : G →* Aut X} {σ : G →* Aut T}
    {q : T ⟶ Y'} (h : IsAffineQuotient σ q) (π : X ⟶ Y) (i : T ⟶ X) [IsOpenImmersion i]
    (hi : ∀ g, (σ g).asIso.hom ≫ i = i ≫ (ρ g).asIso.hom) (κ : Y' ⟶ Y) [IsOpenImmersion κ]
    (hκ : i ≫ π = q ≫ κ) (W : Y.Opens) (hW : W ≤ κ.opensRange) (hW' : π ⁻¹ᵁ W ≤ i.opensRange) :
    Function.Injective (π.app W) ∧
      ∀ s : Γ(X, π ⁻¹ᵁ W), IsInvariantSection ρ _ s → s ∈ Set.range (π.app W) := by
  have e : q ⁻¹ᵁ κ ⁻¹ᵁ W = i ⁻¹ᵁ π ⁻¹ᵁ W := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hκ]
  have h1 : IsIso (κ.app W) := κ.isIso_app W hW
  have h2 : IsIso (i.appLE (π ⁻¹ᵁ W) (q ⁻¹ᵁ κ ⁻¹ᵁ W) e.le) := by
    have := i.isIso_app _ hW'
    have : IsIso (homOfLE e.le) := homOfLE_isIso_of_eq _ e
    rw [Scheme.Hom.appLE]
    infer_instance
  have sq : π.app W ≫ i.appLE (π ⁻¹ᵁ W) (q ⁻¹ᵁ κ ⁻¹ᵁ W) e.le = κ.app W ≫ q.app _ := by
    simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, hκ]
  have sq' (r : Γ(Y, W)) : i.appLE (π ⁻¹ᵁ W) (q ⁻¹ᵁ κ ⁻¹ᵁ W) e.le (π.app W r) =
      q.app _ (κ.app W r) := by
    rw [← CommRingCat.comp_apply, sq, CommRingCat.comp_apply]
  have b1 := ConcreteCategory.bijective_of_isIso (κ.app W)
  have b2 := ConcreteCategory.bijective_of_isIso (i.appLE (π ⁻¹ᵁ W) (q ⁻¹ᵁ κ ⁻¹ᵁ W) e.le)
  refine ⟨fun a b hab ↦ b1.1 (h.app_injective _ ?_), fun s hs ↦ ?_⟩
  · rw [← sq', ← sq', hab]
  · obtain ⟨t, ht⟩ := h.mem_range_app (κ ⁻¹ᵁ W) _ (hs.appLE i hi (h.preimage_le _) e.le)
    obtain ⟨r, rfl⟩ := b1.2 t
    exact ⟨r, b2.1 ((sq' r).trans ht)⟩

set_option backward.isDefEq.respectTransparency false in
theorem exists_of_charts (ρ : G →* Aut X) (𝒰 : Set X.Opens)
    (hbas : ∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ x : X, x ∈ U → x ∈ V → ∃ W ∈ 𝒰, x ∈ W ∧ W ≤ U ∧ W ≤ V)
    (hc : ∀ x : X, ∃ U : 𝒰, x ∈ U.1)
    (T : 𝒰 → Scheme.{0}) (i : ∀ U, T U ⟶ X) [∀ U, IsOpenImmersion (i U)]
    (hr : ∀ U, (i U).opensRange = U.1) (haff : ∀ U : 𝒰, IsAffineOpen U.1)
    (σ : ∀ U, G →* Aut (T U)) (hσ : ∀ U g, (σ U g).asIso.hom ≫ i U = i U ≫ (ρ g).asIso.hom)
    (Y : 𝒰 → Scheme.{0}) [∀ U, IsAffine (Y U)] (q : ∀ U, T U ⟶ Y U)
    (hq : ∀ U, IsAffineQuotient (σ U) (q U)) :
    ∃ (X' : Scheme.{0}) (π : X ⟶ X'), IsAffineQuotient ρ π := by
  have hmem (U : 𝒰) (x : T U) : i U x ∈ U.1 := hr U ▸ ⟨x, rfl⟩
  have hex (U : 𝒰) (x : X) (hx : x ∈ U.1) : ∃ y, i U y = x := by
    rw [← hr U] at hx; exact hx
  have hinj (U : 𝒰) : Function.Injective (i U) := (i U).isOpenEmbedding.injective
  have hσ' (U : 𝒰) (g : G) (x : T U) : i U ((σ U g).asIso.hom x) = (ρ g).asIso.hom (i U x) :=
    congr($(hσ U g) x)
  have hqσ (U : 𝒰) (g : G) (x : T U) : q U ((σ U g).asIso.hom x) = q U x :=
    congr($((hq U).comp_eq g) x)
  let m {U V : 𝒰} (h : U.1 ≤ V.1) : T U ⟶ T V := IsOpenImmersion.lift (i V) (i U) (by
    rintro _ ⟨x, rfl⟩
    exact hex V _ (h (hmem U x)))
  have hm {U V : 𝒰} (h : U.1 ≤ V.1) : m h ≫ i V = i U := IsOpenImmersion.lift_fac _ _ _
  clear_value m
  have hm' {U V : 𝒰} (h : U.1 ≤ V.1) (x : T U) : i V (m h x) = i U x := congr($(hm h) x)
  have hmo {U V : 𝒰} (h : U.1 ≤ V.1) : IsOpenImmersion (m h) := by
    have : IsOpenImmersion (m h ≫ i V) := by rw [hm]; infer_instance
    exact .of_comp _ (i V)
  have hmσ {U V : 𝒰} (h : U.1 ≤ V.1) (g : G) :
      (σ U g).asIso.hom ≫ m h = m h ≫ (σ V g).asIso.hom := by
    rw [← cancel_mono (i V), Category.assoc, Category.assoc, hm, hσ, hσ, reassoc_of% hm]
  let F : 𝒰 ⥤ Scheme.{0} :=
    { obj := Y
      map {U V} f := (hq U).desc (m (show U.1 ≤ V.1 from f.le) ≫ q V) fun g ↦ by
        rw [reassoc_of% hmσ, (hq V).comp_eq]
      map_id U := (hq U).hom_ext (by
        have : m (le_refl U.1) = 𝟙 _ := by rw [← cancel_mono (i U), hm, Category.id_comp]
        rw [IsAffineQuotient.comp_desc, this, Category.id_comp, Category.comp_id])
      map_comp {U V W} f g := (hq U).hom_ext (by
        have : m (show U.1 ≤ W.1 from (f ≫ g).le) =
            m (show U.1 ≤ V.1 from f.le) ≫ m (show V.1 ≤ W.1 from g.le) := by
          rw [← cancel_mono (i W), Category.assoc, hm, hm, hm]
        rw [IsAffineQuotient.comp_desc, IsAffineQuotient.comp_desc_assoc, Category.assoc,
          IsAffineQuotient.comp_desc, this, Category.assoc]) }
  let e (U : 𝒰) : T U ⟶ F.obj U := q U
  have hnat {U V : 𝒰} (f : U ⟶ V) : e U ≫ F.map f = m (show U.1 ≤ V.1 from f.le) ≫ e V :=
    (hq U).comp_desc _ fun g ↦ by rw [reassoc_of% hmσ, (hq V).comp_eq]
  have hnat' {U V : 𝒰} (f : U ⟶ V) (x : T U) :
      F.map f (e U x) = e V (m (show U.1 ≤ V.1 from f.le) x) := congr($(hnat f) x)
  have hF {U V : 𝒰} (f : U ⟶ V) : IsOpenImmersion (F.map f) :=
    have := hmo (show U.1 ≤ V.1 from f.le)
    isOpenImmersion_desc (hq U) (hq V) _ (hmσ _) _ (hnat f)
  have hsurj (U : 𝒰) : Function.Surjective (e U) := (hq U).surjective.surj
  have hfib (U : 𝒰) (x y : T U) (h : e U x = e U y) : ∃ g, (ρ g).asIso.hom (i U x) = i U y := by
    obtain ⟨g, rfl⟩ := ((hq U).apply_eq_iff x y).mp h
    exact ⟨g, (hσ' U g x).symm⟩
  have key {U V : 𝒰} (x : T U) (y : T V) (h : i U x = i V y) :
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
    obtain ⟨x, rfl⟩ := hsurj U x
    obtain ⟨y, rfl⟩ := hsurj V y
    have h' : F.map f (e U x) = F.map g (e V y) := h
    rw [hnat', hnat'] at h'
    obtain ⟨k, hk⟩ := hfib _ _ _ h'
    rw [hm', hm', ← hσ'] at hk
    have := key _ _ hk
    rwa [show e U ((σ U k).asIso.hom x) = e U x from hqσ U k x] at this
  have key2 {U V : 𝒰} (x : T U) (y : T V)
      (h : colimit.ι F U (e U x) = colimit.ι F V (e V y)) : i V y ∈ U.1 := by
    obtain ⟨W, f, g, z, -, h2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff F).mp h
    obtain ⟨z, rfl⟩ := hsurj W z
    rw [hnat'] at h2
    obtain ⟨k, hk⟩ := hfib _ _ _ h2
    rw [hm', ← hσ'] at hk
    exact hk ▸ (show W.1 ≤ U.1 from f.le) (hmem W _)
  let 𝒱 : X.OpenCover := Scheme.Cover.mkOfCovers 𝒰 T i (fun x ↦ by
    obtain ⟨U, hU⟩ := hc x
    exact ⟨U, hex U x hU⟩)
  let j : X ⟶ colimit F := 𝒱.glueMorphisms (fun U ↦ e U ≫ colimit.ι F U) (by
    intro U V
    apply Scheme.hom_ext_of_forall
    intro x
    have hx : i U (pullback.fst (i U) (i V) x) = i V (pullback.snd (i U) (i V) x) :=
      congr($(pullback.condition (f := i U) (g := i V)) x)
    obtain ⟨W, hW, hxW, h1, h2⟩ := hbas U.1 U.2 V.1 V.2 _ (hmem U _) (hx ▸ hmem V _)
    let α : T ⟨W, hW⟩ ⟶ pullback (i U) (i V) :=
      pullback.lift (m h1) (m h2) ((hm h1).trans (hm h2).symm)
    have hα1 : α ≫ pullback.fst _ _ = m h1 := pullback.lift_fst _ _ _
    have hα2 : α ≫ pullback.snd _ _ = m h2 := pullback.lift_snd _ _ _
    have : IsOpenImmersion (α ≫ pullback.fst _ _) := by rw [hα1]; exact hmo _
    have : IsOpenImmersion α := .of_comp _ (pullback.fst _ _)
    obtain ⟨z, hz⟩ := hex ⟨W, hW⟩ _ hxW
    refine ⟨α.opensRange, ⟨z, ?_⟩, ?_⟩
    · apply (pullback.fst (i U) (i V)).isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hα1]
      apply hinj
      rw [hm', hz]
    · rw [← cancel_epi α.isoOpensRange.hom]
      simp only [Scheme.Hom.isoOpensRange_hom_ι_assoc]
      change α ≫ pullback.fst (i U) (i V) ≫ e U ≫ colimit.ι F U =
        α ≫ pullback.snd (i U) (i V) ≫ e V ≫ colimit.ι F V
      rw [reassoc_of% hα1, reassoc_of% hα2,
        ← reassoc_of% (hnat (U := ⟨W, hW⟩) (V := U) (homOfLE h1)),
        ← reassoc_of% (hnat (U := ⟨W, hW⟩) (V := V) (homOfLE h2)), colimit.w, colimit.w])
  have hj (U : 𝒰) : i U ≫ j = e U ≫ colimit.ι F U := 𝒱.ι_glueMorphisms _ _ U
  have hj' (U : 𝒰) (x : T U) : j (i U x) = colimit.ι F U (e U x) := congr($(hj U) x)
  have hpre (U : 𝒰) : j ⁻¹ᵁ (colimit.ι F U).opensRange = U.1 := by
    ext x
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := hsurj U y
      obtain ⟨V, hV⟩ := hc x
      obtain ⟨z, rfl⟩ := hex V x hV
      exact key2 y z (hy.trans (hj' V z))
    · intro hx
      obtain ⟨z, rfl⟩ := hex U x hx
      exact ⟨_, (hj' U z).symm⟩
  refine ⟨colimit F, j, .of_cover (fun g ↦ 𝒱.hom_ext _ _ fun U ↦ ?_) fun y ↦ ?_⟩
  · change i U ≫ _ = i U ≫ _
    have : (σ U g).asIso.hom ≫ e U = e U := (hq U).comp_eq g
    rw [← reassoc_of% hσ, hj, reassoc_of% this]
  · obtain ⟨U, x, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective F y
    have : IsAffine (F.obj U) := inferInstanceAs (IsAffine (Y U))
    refine ⟨(colimit.ι F U).opensRange, isAffineOpen_opensRange _, ⟨x, rfl⟩,
      by rw [hpre]; exact haff U, ?_⟩
    exact app_of_chart (hq U) j (i U) (hσ U) (colimit.ι F U) (hj U) _ le_rfl
      (by rw [hpre, hr])

theorem exists_isAffineQuotient (ρ : G →* Aut X) [OrbitsInAffineOpens ρ] :
    ∃ (X' : Scheme.{0}) (π : X ⟶ X'), IsAffineQuotient ρ π := by
  let 𝒰 : Set X.Opens := {U | IsAffineOpen U ∧ ∀ g, U ≤ (ρ g).asIso.hom ⁻¹ᵁ U}
  refine exists_of_charts ρ 𝒰 (fun U hU V hV x hxU hxV ↦ ?_) (fun x ↦ ?_)
    (fun U ↦ Spec Γ(X, U.1)) (fun U ↦ U.2.1.fromSpec) (fun U ↦ U.2.1.opensRange_fromSpec)
    (fun U ↦ U.2.1)
    (fun U ↦ letI := sectionsAction ρ U.1 U.2.2; specAction G Γ(X, U.1))
    (fun U ↦ specAction_fromSpec ρ U.2.1 U.2.2)
    (fun U ↦ letI := sectionsAction ρ U.1 U.2.2; Spec (.of (FixedPoints.subring Γ(X, U.1) G)))
    (fun U ↦ letI := sectionsAction ρ U.1 U.2.2
      Spec.map (CommRingCat.ofHom (algebraMap (FixedPoints.subring Γ(X, U.1) G) Γ(X, U.1))))
    (fun U ↦ ?_)
  · obtain ⟨t, ht, hx, hle⟩ := exists_isInvariantSection_basicOpen_le hU.1 hU.2 hxU V
      (fun g ↦ hV.2 g hxV)
    exact ⟨_, ⟨hU.1.basicOpen t, ht.basicOpen_le⟩, hx, X.basicOpen_le t, hle⟩
  · obtain ⟨V, h1, h2, h3⟩ := exists_stable_isAffineOpen ρ x
    exact ⟨⟨V, h1, h2⟩, h3⟩
  · let := sectionsAction ρ U.1 U.2.2
    exact isAffineQuotient_spec (FixedPoints.subring Γ(X, U.1) G) Γ(X, U.1)

end QuotientGluing

theorem exists_quotient_of_finite_group : ∀ (Γ : Type) [Group Γ] [Finite Γ] (X : Scheme.{0}) [X.IsSeparated] (ρ : Γ →* Aut X), (∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ g, (ρ g).asIso.hom x ∈ U) → ∃ (X' : Scheme.{0}) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) := by
  intro Γ _ _ X _ ρ h
  have : OrbitsInAffineOpens ρ := ⟨h⟩
  obtain ⟨X', π, hπ⟩ := QuotientGluing.exists_isAffineQuotient ρ
  exact ⟨X', π, hπ.isAffineHom, hπ.comp_eq, fun V ↦ ⟨hπ.app_injective V, fun f hf ↦
    hπ.mem_range_app V f fun g ↦ ⟨hπ.preimage_le V g, hf g _⟩⟩⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsCobOfIsAffineOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS
open GlobalTheory.AbLaw GlobalTheory.AbLaw.SecOn GlobalTheory.AbLaw.CechOne

private lemma resG_resG_divisors {Y : Scheme.{0}} {A B C : Y.Opens} (h₁ : A ≤ B) (h₂ : B ≤ C)
    (s : Γ(Y, C)) : resG Y h₁ (resG Y h₂ s) = resG Y (h₁.trans h₂) s := by
  change _ = (Y.presheaf.map ((homOfLE h₂).op ≫ (homOfLE h₁).op)).hom s
  rw [Functor.map_comp]
  rfl

private lemma resG_self_moduli {Y : Scheme.{0}} {A : Y.Opens} (h : A ≤ A) (s : Γ(Y, A)) :
    resG Y h s = s := by
  change (Y.presheaf.map (𝟙 _)).hom s = s
  rw [CategoryTheory.Functor.map_id]
  rfl

private lemma rsT_eq_resG {Y : Scheme.{0}} {A B : Y.Opens} (s : Γ(Y, A)) (h : B ≤ A) :
    rsT s B = resG Y h s := by
  unfold rsT
  rw [dite_eq_left h]

private lemma triv_secOn_ext {X : Scheme.{0}} {W : X.Opens} (σ τ : SecOn (LB.triv X) W)
    (h : (show LB.secGroup (LB.triv X) W from σ).1 PUnit.unit =
      (show LB.secGroup (LB.triv X) W from τ).1 PUnit.unit) : σ = τ :=
  Subtype.ext (funext fun _ => h)

theorem isCob_of_isAffineOpen : ∀ (X : Scheme.{0}) (J : Type) (U : J → X.Opens) (c : C1 U),
    IsAffineOpen (⨆ α, U α) → IsCoc U c → IsCob U c := by
  intro X J U c hA hc

  let φ : ∀ a b, SecOn (LB.triv X) (U a ⊓ U b) := fun a b =>
    show LB.secGroup (LB.triv X) (U a ⊓ U b) from
      ⟨fun _ => resG X inf_le_left (c a b), by
        simp only [LB.secGroup, LB.triv]
        show _ ∈ secOn _ _
        simp only [secOn, Set.mem_ofPred_eq]
        intro i j
        rw [Units.val_one, map_one, _root_.one_mul, resG_resG_divisors]⟩
  have hφ : IsCocycle (LB.triv X) U φ := by
    intro a b d W ha hb hd
    apply triv_secOn_ext
    have h0 := hc a b d
    rw [rsT_eq_resG (c a b) (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)),
      rsT_eq_resG (c b d) (le_inf (inf_le_left.trans inf_le_right) inf_le_right),
      rsT_eq_resG (c a d) (le_inf (inf_le_left.trans inf_le_left) inf_le_right)] at h0
    have e := congrArg (resG X (inf_le_left.trans (le_inf (le_inf ha hb) hd) :
      W ⊓ (LB.triv X).U PUnit.unit ≤ U a ⊓ U b ⊓ U d)) h0
    rw [map_add (f := _), resG_resG_divisors, resG_resG_divisors, resG_resG_divisors] at e
    change resG X _ (resG X _ (c a b)) + resG X _ (resG X _ (c b d)) = resG X _ (resG X _ (c a d))
    rw [resG_resG_divisors, resG_resG_divisors, resG_resG_divisors]
    exact e

  obtain ⟨ψ, hψ⟩ := cechHOneVanishesOnOpen_of_isAffineOpen (LB.isLB_triv X) hA J U (fun a => le_iSup U a) le_rfl φ hφ
  refine ⟨fun i => -resG X (le_inf le_rfl le_top : U i ≤ U i ⊓ (LB.triv X).U PUnit.unit)
    ((show LB.secGroup (LB.triv X) (U i) from ψ i).1 PUnit.unit), ?_⟩
  intro i j
  have e := congrArg (fun σ : SecOn (LB.triv X) (U i ⊓ U j) =>
    (show LB.secGroup (LB.triv X) (U i ⊓ U j) from σ).1 PUnit.unit) (hψ i j)
  change resG X inf_le_left (c i j) =
    resG X (inf_le_inf_right _ inf_le_left) ((show LB.secGroup (LB.triv X) (U i) from ψ i).1 PUnit.unit) -
      resG X (inf_le_inf_right _ inf_le_right)
        ((show LB.secGroup (LB.triv X) (U j) from ψ j).1 PUnit.unit) at e
  have e' := congrArg (resG X (le_inf le_rfl le_top :
    U i ⊓ U j ≤ U i ⊓ U j ⊓ (LB.triv X).U PUnit.unit)) e
  rw [map_sub, resG_resG_divisors, resG_resG_divisors, resG_resG_divisors, resG_self_moduli] at e'
  rw [rsT_eq_resG _ inf_le_right, rsT_eq_resG _ inf_le_left, map_neg, map_neg, resG_resG_divisors,
    resG_resG_divisors, e']
  abel

end GlobalTheory.KS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSubgroupEqRangeOfLists
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam.ListedSubgroup

variable {S : Scheme.{0}}

theorem eq_comp_section {X : Scheme.{0}} (f : X ⟶ S) [IsSeparated f] (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
    {k : Type} [Field k] (z : Sp k ⟶ X) (q : Sp k) (hz : z q ∈ Set.range s) : z = (z ≫ f) ≫ s := by
  have := isClosedImmersion_of_section_of_isSeparated f s hs
  have hsurj : Surjective (pullback.fst z s) := by
    refine ⟨fun y => ?_⟩
    obtain rfl : y = q := Subsingleton.elim _ _
    have h : y ∈ Set.range (pullback.fst z s) := by
      rw [Scheme.Pullback.range_fst]
      exact hz
    exact h
  have : IsIso (pullback.fst z s) := isIso_of_isClosedImmersion_of_surjective _
  rw [← cancel_epi (pullback.fst z s)]
  simp only [pullback.condition_assoc, pullback.condition, Category.assoc, reassoc_of% hs]

theorem section_eq [ConnectedSpace S] (G : Over S) [GrpObj G] [IsAbelianScheme G] {N : ℕ}
    (hN : IsUnit (N : Γ(S, ⊤))) {a b : 𝟙_ (Over S) ⟶ G} (ha : a ^ N = 1) (hb : b ^ N = 1)
    {k : Type} [Field k] (x : Sp k ⟶ S) (h : x ≫ a.left = x ≫ b.left) : a = b := by
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion G hN
  obtain ⟨a', rfl, -⟩ := LatticeTorsion.existsUnique_torsion G N a ha
  obtain ⟨b', rfl, -⟩ := LatticeTorsion.existsUnique_torsion G N b hb
  have hx : ((toUnit (Over.mk x) ≫ a') ≫ torsion.ι G N) = (toUnit (Over.mk x) ≫ b') ≫ torsion.ι G N := by
    rw [Category.assoc, Category.assoc]
    exact Over.OverMorphism.ext h
  have hpow : ((toUnit (Over.mk x) ≫ a') ≫ torsion.ι G N) ^ N = 1 := by
    rw [Category.assoc, ← MonObj.comp_pow, ha, MonObj.comp_one]
  have hab : toUnit (Over.mk x) ≫ a' = toUnit (Over.mk x) ≫ b' :=
    (LatticeTorsion.existsUnique_torsion G N _ hpow).unique rfl hx.symm
  have : a' = b' := Over.OverMorphism.ext
    (eq_of_preconnected_of_unramified (T := S) (torsion G N).hom ((Over.w a').trans (Over.w b').symm) x
      (congrArg CommaMorphism.left hab))
  rw [this]

end GlobalTheory.HkFam.ListedSubgroup

namespace GlobalTheory.HkFam

open ListedSubgroup in
theorem exists_subgroup_eq_range_of_lists :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (S : Scheme.{0}) [ConnectedSpace S] (t : SAB H S) (σ : Fin n → (𝟙_ (Over S) ⟶ t.G)) (K : Set t.G.left), IsProper t.G.hom → IsUnit (p : Γ(S, ⊤)) → Lists (p ^ 2) σ K → HeckeSet D t 𝔓 p i K → ∃ C : Subgroup (𝟙_ (Over S) ⟶ t.G), (C : Set _) = Set.range σ := by
  intro E _ _ _ H D 𝔓 p i n S _ t σ K hpr hp ⟨hσ, hK, _⟩ hH
  have hab : IsAbelianScheme t.G := ⟨t.comm, t.semi.smooth, hpr, t.semi.geomConnected⟩
  have hN : IsUnit ((p ^ 2 : ℕ) : Γ(S, ⊤)) := by
    rw [Nat.cast_pow]
    exact hp.pow 2
  obtain ⟨s₀⟩ : Nonempty S := inferInstance
  let k : Type := AlgebraicClosure (S.residueField s₀)
  let x : Sp k ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s₀) k)) ≫ S.fromSpecResidueField s₀
  obtain ⟨C, hC, -⟩ := hH k x
  obtain ⟨q⟩ : Nonempty (Sp k) := inferInstance
  have hmem : ∀ j, toUnit (Over.mk x) ≫ σ j ∈ C := fun j => by
    rw [hC, hK]
    rintro _ ⟨y, rfl⟩
    exact Set.mem_iUnion.2 ⟨j, x y, (Scheme.Hom.comp_apply x (σ j).left y).symm⟩
  have key : ∀ a : 𝟙_ (Over S) ⟶ t.G, a ^ (p ^ 2) = 1 → toUnit (Over.mk x) ≫ a ∈ C → a ∈ Set.range σ := by
    intro a ha h
    rw [hC, hK] at h
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (h ⟨q, rfl⟩)
    have h1 := eq_comp_section t.G.hom (σ j).left (Over.w (σ j)) _ q hj
    rw [Over.w (toUnit (Over.mk x) ≫ a)] at h1
    exact ⟨j, (section_eq t.G hN ha (hσ j) x h1).symm⟩
  refine ⟨{ carrier := Set.range σ, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, rfl⟩
  · rintro _ _ ⟨j, rfl⟩ ⟨j', rfl⟩
    refine key _ (by rw [mul_pow, hσ, hσ, _root_.one_mul]) ?_
    rw [MonObj.comp_mul]
    exact C.mul_mem (hmem j) (hmem j')
  · refine key _ (one_pow _) ?_
    rw [MonObj.comp_one]
    exact C.one_mem
  · rintro _ ⟨j, rfl⟩
    refine key _ (by rw [inv_pow, hσ, inv_one]) ?_
    rw [GrpObj.comp_inv]
    exact C.inv_mem (hmem j)

end GlobalTheory.HkFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteAffineCharts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.FinAffineCharts

variable {X : Scheme.{0}}

theorem res_res {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)ˣ) :
    res h₂ (res h₁ s) = res (h₂.trans h₁) s := by
  apply Units.ext
  change (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom s) =
    (X.presheaf.map (homOfLE (h₂.trans h₁)).op).hom s
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

theorem cocycle_on {L : LB X} (hL : L.IsLB) (i j k : L.ι) {W : X.Opens}
    (h₁ : W ≤ L.U i ⊓ L.U j) (h₂ : W ≤ L.U j ⊓ L.U k) (h₃ : W ≤ L.U i ⊓ L.U k) :
    res h₁ (L.g i j) * res h₂ (L.g j k) = res h₃ (L.g i k) := by
  have := congrArg (res (le_inf h₁ (h₂.trans inf_le_right) : W ≤ L.U i ⊓ L.U j ⊓ L.U k))
    (hL.cocycle i j k)
  rwa [map_mul, res_res, res_res, res_res] at this

noncomputable def refineLB (L : LB X) {κ : Type} (W : κ → X.Opens) (c : κ → L.ι)
    (h : ∀ a, W a ≤ L.U (c a)) : LB X :=
  ⟨κ, W, fun a b => res (inf_le_inf (h a) (h b)) (L.g (c a) (c b))⟩

theorem refineLB_isLB {L : LB X} (hL : L.IsLB) {κ : Type} (W : κ → X.Opens) (c : κ → L.ι)
    (h : ∀ a, W a ≤ L.U (c a)) (hc : ⨆ a, W a = ⊤) : (refineLB L W c h).IsLB := {
  cover := hc
  g_self a := by
    have := congrArg (res (h a)) (hL.g_self (c a))
    rw [res_res, map_one] at this
    exact (res_res _ _ _).trans this
  cocycle a b d :=
    (congrArg₂ (· * ·) (res_res _ _ _) (res_res _ _ _)).trans
      ((cocycle_on hL _ _ _ _ _ _).trans (res_res _ _ _).symm) }

theorem iso_refineLB {L : LB X} (hL : L.IsLB) {κ : Type} (W : κ → X.Opens) (c : κ → L.ι)
    (h : ∀ a, W a ≤ L.U (c a)) : LBIso L (refineLB L W c h) := by
  refine ⟨⟨fun p => res (inf_le_inf_right _ (h p.1) : W p.1 ⊓ L.U p.2 ≤ L.U (c p.1) ⊓ L.U p.2)
    (L.g (c p.1) p.2)⟩, ?_⟩
  have key : ∀ (a b : κ) (i j : L.ι),
      res (inf_le_left : W a ⊓ L.U i ⊓ (W b ⊓ L.U j) ≤ W a ⊓ L.U i)
        (res (inf_le_inf_right _ (h a) : W a ⊓ L.U i ≤ L.U (c a) ⊓ L.U i) (L.g (c a) i)) =
      res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          W a ⊓ L.U i ⊓ (W b ⊓ L.U j) ≤ W a ⊓ W b)
        (res (inf_le_inf (h a) (h b)) (L.g (c a) (c b))) *
      (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          W a ⊓ L.U i ⊓ (W b ⊓ L.U j) ≤ L.U i ⊓ L.U j) (L.g i j))⁻¹ *
      res (inf_le_right : W a ⊓ L.U i ⊓ (W b ⊓ L.U j) ≤ W b ⊓ L.U j)
        (res (inf_le_inf_right _ (h b) : W b ⊓ L.U j ≤ L.U (c b) ⊓ L.U j) (L.g (c b) j)) := by
    intro a b i j
    rw [res_res, res_res, res_res, mul_right_comm, cocycle_on hL (c a) (c b) j _ _
      (le_inf (inf_le_left.trans (inf_le_left.trans (h a))) (inf_le_right.trans inf_le_right)),
      eq_mul_inv_iff_mul_eq]
    exact cocycle_on hL _ _ _ _ _ _
  exact fun p q => key p.1 q.1 p.2 q.2

theorem exists_finite_affine_cover [CompactSpace X] (M : LB X) (hM : M.IsLB) :
    ∃ (κ : Type) (_ : Finite κ) (W : κ → X.Opens) (c : κ → M.ι),
      (∀ a, IsAffineOpen (W a)) ∧ (∀ a, W a ≤ M.U (c a)) ∧ ⨆ a, W a = ⊤ := by
  have h : ∀ x : X, ∃ (W : X.Opens) (c : M.ι), IsAffineOpen W ∧ x ∈ W ∧ W ≤ M.U c := by
    intro x
    obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.1
      (hM.cover.ge (TopologicalSpace.Opens.mem_top x))
    obtain ⟨_, ⟨W, hW, rfl⟩, hx, hle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hc (M.U c).isOpen
    exact ⟨W, c, hW, hx, hle⟩
  choose W c hW hx hle using h
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (W x : Set X))
    (fun x => (W x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩)
  refine ⟨s, inferInstance, fun a => W a, fun a => c a, fun a => hW a, fun a => hle a,
    top_le_iff.1 ?_⟩
  intro x _
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ha⟩, hxa⟩

theorem exists_finite_affine_charts : ∀ (X : Scheme.{0}) (L : LB X), CompactSpace X → L.IsLB → ∃ L' : LB X, Finite L'.ι ∧ L'.IsLB ∧ (∀ i, IsAffineOpen (L'.U i)) ∧ LBIso L L' := by
  intro X L _ hL
  obtain ⟨κ, hκ, W, c, hW, h, hc⟩ := exists_finite_affine_cover L hL
  exact ⟨refineLB L W c h, hκ, refineLB_isLB hL W c h hc, hW, iso_refineLB hL W c h⟩

end GlobalTheory.FinAffineCharts
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalDerivationExtensionOfAffine
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalDerivationExtensionOfAffine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.LocDerExt

theorem der_unique {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] (f : A)
    [IsLocalization.Away f B] (φ : B →+* C) (δ₁ δ₂ : B → C)
    (h₁ : ∀ a b, δ₁ (a * b) = φ a * δ₁ b + φ b * δ₁ a)
    (h₂ : ∀ a b, δ₂ (a * b) = φ a * δ₂ b + φ b * δ₂ a)
    (h : ∀ a, δ₁ (algebraMap A B a) = δ₂ (algebraMap A B a)) (s : B) : δ₁ s = δ₂ s := by
  obtain ⟨⟨a, t⟩, e⟩ := IsLocalization.surj (Submonoid.powers f) s
  have hu : IsUnit (φ (algebraMap A B t)) := (IsLocalization.map_units B t).map φ
  have e₁ := h₁ s (algebraMap A B t)
  have e₂ := h₂ s (algebraMap A B t)
  dsimp only at e
  rw [e] at e₁ e₂
  rw [h, e₂, h] at e₁
  exact (hu.mul_left_cancel (add_left_cancel e₁)).symm

theorem der_exists {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] (f : A)
    [IsLocalization.Away f B] (φ : B →+* C) (d : A → C)
    (hadd : ∀ a b, d (a + b) = d a + d b)
    (hmul : ∀ a b, d (a * b) = φ (algebraMap A B a) * d b + φ (algebraMap A B b) * d a) :
    ∃ δ : B → C, (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = φ a * δ b + φ b * δ a) ∧
      ∀ a, δ (algebraMap A B a) = d a := by
  have h0 : d 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  have h1 : d 1 = 0 := by
    have := hmul 1 1
    simp only [_root_.mul_one, map_one, _root_.one_mul] at this
    exact left_eq_add.mp this
  obtain ⟨ψ, hψ1, hψ2⟩ : ∃ ψ : A →+* DualNumber C, (∀ a, (ψ a).fst = φ (algebraMap A B a)) ∧
      ∀ a, (ψ a).snd = d a :=
    ⟨{ toFun := fun a => TrivSqZeroExt.inl (φ (algebraMap A B a)) + TrivSqZeroExt.inr (d a)
       map_one' := by ext <;> simp [h1]
       map_zero' := by ext <;> simp [h0]
       map_add' := fun a b => by ext <;> simp [hadd]
       map_mul' := fun a b => by ext <;> simp [hmul, mul_comm] }, fun a => by simp, fun a => by simp⟩
  have hu : IsUnit (ψ f) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hψ1]
    exact (IsLocalization.Away.algebraMap_isUnit f).map φ
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : B →+* DualNumber C, ∀ a, Ψ (algebraMap A B a) = ψ a :=
    ⟨IsLocalization.Away.lift f hu, fun a => IsLocalization.Away.lift_eq f hu a⟩
  obtain ⟨π, hπ⟩ : ∃ π : DualNumber C →+* C, ∀ x, π x = x.fst :=
    ⟨(TrivSqZeroExt.fstHom C C C).toRingHom, fun _ => rfl⟩
  have hf : π.comp Ψ = φ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext a
    simp only [RingHom.comp_apply, hΨ, hπ, hψ1]
  have hf' : ∀ b, (Ψ b).fst = φ b := fun b => by rw [← hf, RingHom.comp_apply, hπ]
  refine ⟨fun b => (Ψ b).snd, fun a b => by simp only [map_add (f := _), TrivSqZeroExt.snd_add],
    fun a b => ?_, fun a => by simp only [hΨ, hψ2]⟩
  simp only [map_mul, DualNumber.snd_mul, hf']
  ring

theorem res_res (X : Scheme.{0}) {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V) (s : Γ(X, U)) :
    resG X k (resG X h s) = resG X (k.trans h) s := by
  change (X.presheaf.map _ ≫ X.presheaf.map _).hom s = _
  rw [← Functor.map_comp]
  rfl

theorem res_const {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (h : V ≤ U) (a : R) : resG X h (constFn p U a) = constFn p V a :=
  congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map p (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)

theorem pre_le {Y X : Scheme.{0}} (m : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) : m ⁻¹ᵁ V ≤ m ⁻¹ᵁ U :=
  fun _ hy => h hy

theorem app_res {Y X : Scheme.{0}} (m : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (s : Γ(X, U)) :
    (m.app V).hom (resG X h s) = resG Y (pre_le m h) ((m.app U).hom s) :=
  congrArg (fun φ => φ.hom s) (Scheme.Hom.naturality m (homOfLE h).op)

theorem cover {Y X : Scheme.{0}} (m : Y ⟶ X) {W₀ : X.Opens} (hW : IsAffineOpen W₀) {W : X.Opens}
    (h : W ≤ W₀) :
    m ⁻¹ᵁ W ≤ ⨆ i : {f : Γ(X, W₀) // X.basicOpen f ≤ W}, m ⁻¹ᵁ X.basicOpen i.1 := by
  intro y hy
  obtain ⟨f, hf, hx⟩ := hW.exists_basicOpen_le (V := W) ⟨m y, hy⟩ (h hy)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hf⟩, hx⟩

theorem sep {Y X : Scheme.{0}} (m : Y ⟶ X) {W₀ : X.Opens} (hW : IsAffineOpen W₀) {W : X.Opens}
    (h : W ≤ W₀) (s t : Γ(Y, m ⁻¹ᵁ W))
    (e : ∀ (f : Γ(X, W₀)) (k : X.basicOpen f ≤ W), resG Y (pre_le m k) s = resG Y (pre_le m k) t) :
    s = t :=
  Y.sheaf.eq_of_locally_eq' (fun i : {f : Γ(X, W₀) // X.basicOpen f ≤ W} => m ⁻¹ᵁ X.basicOpen i.1)
    (m ⁻¹ᵁ W) (fun i => homOfLE (pre_le m i.2)) (cover m hW h) s t (fun i => e i.1 i.2)

theorem exists_locDer : ∀ (R : Type) [CommRing R] (Y X : Scheme.{0}) (q : Y ⟶ Sp ℂ) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → ℂ) (W₀ : X.Opens), IsAffineOpen W₀ → ∀ d₀ : Γ(X, W₀) → Γ(Y, m ⁻¹ᵁ W₀), (∀ a b, d₀ (a + b) = d₀ a + d₀ b) → (∀ a b, d₀ (a * b) = (m.app W₀).hom a * d₀ b + (m.app W₀).hom b * d₀ a) → (∀ r, d₀ (constFn p W₀ r) = constFn q (m ⁻¹ᵁ W₀) (D r)) → ∃ d, LocDer q p m D W₀ d ∧ d W₀ = d₀ := by
  intro R _ Y X q p m D W₀ hW d₀ hadd hmul hbase
  have H : ∀ f : Γ(X, W₀), ∃ δ : Γ(X, X.basicOpen f) → Γ(Y, m ⁻¹ᵁ X.basicOpen f),
      (∀ a b, δ (a + b) = δ a + δ b) ∧
      (∀ a b, δ (a * b) = (m.app _).hom a * δ b + (m.app _).hom b * δ a) ∧
      ∀ a, δ (resG X (X.basicOpen_le f) a) = resG Y (pre_le m (X.basicOpen_le f)) (d₀ a) := by
    intro f
    haveI := hW.isLocalization_basicOpen f
    refine der_exists f (m.app (X.basicOpen f)).hom
      (fun a => resG Y (pre_le m (X.basicOpen_le f)) (d₀ a)) (fun a b => by simp only [hadd, map_add (f := _)])
      (fun a b => ?_)
    have e : ∀ a, (m.app (X.basicOpen f)).hom (algebraMap Γ(X, W₀) Γ(X, X.basicOpen f) a) =
        resG Y (pre_le m (X.basicOpen_le f)) ((m.app W₀).hom a) :=
      fun a => app_res m (X.basicOpen_le f) a
    rw [e, e]
    simp only [hmul, map_add (f := _), map_mul]
  choose δ δadd δmul δres using H
  have compat : ∀ (f g : Γ(X, W₀)) (k : X.basicOpen g ≤ X.basicOpen f) (s : Γ(X, X.basicOpen f)),
      resG Y (pre_le m k) (δ f s) = δ g (resG X k s) := by
    intro f g k s
    haveI := hW.isLocalization_basicOpen f
    refine der_unique f ((m.app (X.basicOpen g)).hom.comp (resG X k))
      (fun s => resG Y (pre_le m k) (δ f s)) (fun s => δ g (resG X k s)) (fun a b => ?_)
      (fun a b => ?_) (fun a => ?_) s
    · simp only [δmul, map_add (f := _), map_mul, RingHom.comp_apply, app_res m k]
    · simp only [δmul, map_mul, RingHom.comp_apply]
    · change resG Y (pre_le m k) (δ f (resG X (X.basicOpen_le f) a)) =
        δ g (resG X k (resG X (X.basicOpen_le f) a))
      rw [res_res X, δres, δres, res_res Y]
  have G : ∀ (W : X.Opens), W ≤ W₀ → ∀ s : Γ(X, W), ∃ t : Γ(Y, m ⁻¹ᵁ W),
      ∀ (f : Γ(X, W₀)) (k : X.basicOpen f ≤ W), resG Y (pre_le m k) t = δ f (resG X k s) := by
    intro W h s
    obtain ⟨t, ht, -⟩ := Y.sheaf.existsUnique_gluing'
      (fun i : {f : Γ(X, W₀) // X.basicOpen f ≤ W} => m ⁻¹ᵁ X.basicOpen i.1)
      (m ⁻¹ᵁ W) (fun i => homOfLE (pre_le m i.2)) (cover m hW h)
      (fun i => δ i.1 (resG X i.2 s)) (fun i j => by
        have e : X.basicOpen (i.1 * j.1) = X.basicOpen i.1 ⊓ X.basicOpen j.1 := X.basicOpen_mul _ _
        have ki : X.basicOpen (i.1 * j.1) ≤ X.basicOpen i.1 := e.le.trans inf_le_left
        have kj : X.basicOpen (i.1 * j.1) ≤ X.basicOpen j.1 := e.le.trans inf_le_right
        have k : m ⁻¹ᵁ X.basicOpen i.1 ⊓ m ⁻¹ᵁ X.basicOpen j.1 ≤ m ⁻¹ᵁ X.basicOpen (i.1 * j.1) :=
          fun y hy => e.ge hy
        have e' : resG Y (pre_le m ki) (δ i.1 (resG X i.2 s)) =
            resG Y (pre_le m kj) (δ j.1 (resG X j.2 s)) := by
          rw [compat _ _ ki, compat _ _ kj, res_res X, res_res X]
        have e'' := congrArg (resG Y k) e'
        rw [res_res Y, res_res Y] at e''
        exact e'')
    exact ⟨t, fun f k => ht ⟨f, k⟩⟩
  choose t ht using G
  classical
  refine ⟨fun W s => if h : W ≤ W₀ then t W h s else 0, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro W h a b
    simp only [dif_pos h]
    refine sep m hW h _ _ (fun f k => ?_)
    rw [map_add (f := _), ht W h _ f k, ht W h _ f k, ht W h _ f k, map_add (f := _), δadd]
  · intro W h a b
    simp only [dif_pos h]
    refine sep m hW h _ _ (fun f k => ?_)
    rw [map_add (f := _), map_mul, map_mul, ht W h _ f k, ht W h _ f k, ht W h _ f k, map_mul, δmul, app_res m k, app_res m k]
  · intro W W' h' h a
    simp only [dif_pos h, dif_pos (h'.trans h)]
    refine sep m hW (h'.trans h) _ _ (fun f k => ?_)
    refine Eq.trans ?_ (res_res Y (pre_le m h') (pre_le m k) _).symm
    rw [ht W' _ _ f k, ht W h a f (k.trans h'), res_res X]
  · intro W h r
    simp only [dif_pos h]
    refine sep m hW h _ _ (fun f k => ?_)
    rw [ht W h _ f k, res_const, res_const, ← res_const p (X.basicOpen_le f), δres, hbase, res_const]
  · funext a
    simp only [dif_pos (le_refl W₀)]
    refine sep m hW le_rfl _ _ (fun f k => ?_)
    rw [ht W₀ _ _ f k, δres]

end GlobalTheory.LocDerExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalDerivationExtensionOfAffineStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
theorem _root_.GlobalTheory.T.exists_local_derivation_extension_of_affine : ∀ (R : Type) [CommRing R] (Y X : Scheme.{0}) (q : Y ⟶ Sp ℂ) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → ℂ) (W₀ : X.Opens), IsAffineOpen W₀ → ∀ d₀ : Γ(X, W₀) → Γ(Y, m ⁻¹ᵁ W₀), (∀ a b, d₀ (a + b) = d₀ a + d₀ b) → (∀ a b, d₀ (a * b) = (m.app W₀).hom a * d₀ b + (m.app W₀).hom b * d₀ a) → (∀ r, d₀ (constFn p W₀ r) = constFn q (m ⁻¹ᵁ W₀) (D r)) → ∃ d, LocDer q p m D W₀ d ∧ d W₀ = d₀ := by
  first | exact @GlobalTheory.LocDerExt.exists_locDer | exact GlobalTheory.LocDerExt.exists_locDer | (intros; apply GlobalTheory.LocDerExt.exists_locDer <;> assumption)
end
end
