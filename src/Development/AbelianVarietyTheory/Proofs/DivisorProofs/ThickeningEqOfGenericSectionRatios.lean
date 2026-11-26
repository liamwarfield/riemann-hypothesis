module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingClosedFibreOfThreeLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupMorphismsAgreeOfSectionRatios
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackOfIsPullbackOnOpenCoverTarget
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOpenPartProductMapIrreducibleFibres

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBasicOpenOfSectionRatioEqBasePoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBasicOpenOfSectionRatioEqBasePoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem thick_apply_eq_closedPoint {R : Type} [CommRing R] [IsLocalRing R] (e : ℕ)
    (p : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))) :
    thick R (maximalIdeal R) e p = closedPoint R := by
  haveI : p.asIdeal.IsPrime := p.isPrime
  apply PrimeSpectrum.ext
  show Ideal.comap (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))) p.asIdeal = maximalIdeal R
  have hle : maximalIdeal R ^ (e + 1) ≤ Ideal.comap (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))) p.asIdeal := by
    intro a ha
    simp [Ideal.Quotient.eq_zero_iff_mem.2 ha]
  have hm : maximalIdeal R ≤ Ideal.comap (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))) p.asIdeal :=
    (Ideal.IsPrime.comap _).le_of_pow_le hle
  exact ((maximalIdeal.isMaximal R).eq_of_le (Ideal.IsPrime.comap _).ne_top hm).symm

theorem exists_thick_zero {R : Type} [CommRing R] [IsLocalRing R] (e : ℕ) (G : Over (Sp R))
    (y : (thickObj R (maximalIdeal R) e G).left) :
    ∃ y₀ : (thickObj R (maximalIdeal R) 0 G).left,
      (fstG (maximalIdeal R) 0 G).left y₀ = (fstG (maximalIdeal R) e G).left y := by
  have hne : maximalIdeal R ^ (0 + 1) ≠ ⊤ := by
    rw [zero_add, pow_one]; exact (maximalIdeal.isMaximal R).ne_top
  haveI : Nontrivial (R ⧸ maximalIdeal R ^ (0 + 1)) := Ideal.Quotient.nontrivial_iff.2 hne
  haveI : IsLocalRing (R ⧸ maximalIdeal R ^ (0 + 1)) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have h1 : G.hom (pullback.fst G.hom (thick R (maximalIdeal R) e) y) = closedPoint R := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, thick_apply_eq_closedPoint]
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := thick R (maximalIdeal R) 0)
    (pullback.fst G.hom (thick R (maximalIdeal R) e) y) (closedPoint _)
    (h1.trans (thick_apply_eq_closedPoint 0 _).symm)
  exact ⟨z, hz⟩

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem mem_basicOpen_of_secRatioEq : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (e k k' : ℕ), 3 ≤ k → ∀ (x : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G) (T : H0 U.LG.L k → H0 U.LG.L k'), (∀ s₁ s₂ : H0 U.LG.L k, SecRatioEq U.LG.L (x.left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (T s₁) (T s₂)) → ∀ (y : (thickObj R (maximalIdeal R) e G).left) (s₀ : H0 U.LG.L k) (i' : Fin 1 → U.LG.L.ι), y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen (((fstG (maximalIdeal R) e G).left.app (secChart U.LG.L i')).hom ((T s₀).f i')) → ∃ i : Fin 1 → U.LG.L.ι, y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen ((((x).left ≫ (fstG (maximalIdeal R) e G).left).app (secChart U.LG.L i)).hom (s₀.f i)) := by
  intro R _ _ _ hB D A G _ _ hG U e k k' hk x T hT y s₀ i' hy
  obtain ⟨y₀, hy₀⟩ := exists_thick_zero e G (x.left y)
  obtain ⟨s₁, j, hs₁⟩ := GlobalTheory.T.exists_section_nonvanishing_closedFibre_of_three_le R hB D A G hG U k hk y₀
  refine ⟨j, ?_⟩
  have hs₁' : (fstG (maximalIdeal R) 0 G).left y₀ ∈ G.left.basicOpen (s₁.f j) :=
    (Scheme.preimage_basicOpen (fstG (maximalIdeal R) 0 G).left (s₁.f j)).ge hs₁
  have hu : y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen
      (((x.left ≫ (fstG (maximalIdeal R) e G).left).app (secChart U.LG.L j)).hom (s₁.f j)) := by
    refine (Scheme.preimage_basicOpen (x.left ≫ (fstG (maximalIdeal R) e G).left) (s₁.f j)).le ?_
    show (x.left ≫ (fstG (maximalIdeal R) e G).left) y ∈ G.left.basicOpen (s₁.f j)
    rw [Scheme.Hom.comp_apply, ← hy₀]
    exact hs₁'
  by_contra hn
  have hE := congrArg (thickObj R (maximalIdeal R) e G).left.basicOpen (hT s₁ s₀ j i')
  simp only [Scheme.basicOpen_mul, Scheme.basicOpen_res] at hE
  have hmem : y ∈ ((x.left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L j ⊓
      (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i') := by
    rw [TopologicalSpace.Opens.mem_inf]
    exact ⟨Scheme.basicOpen_le _ _ hu, Scheme.basicOpen_le _ _ hy⟩
  have h2 := hE.le (by
    simp only [TopologicalSpace.Opens.mem_inf] at hmem ⊢
    exact ⟨⟨hmem, hu⟩, ⟨hmem, hy⟩⟩)
  simp only [TopologicalSpace.Opens.mem_inf] at h2
  exact hn h2.1.2

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBasicOpenOfSectionRatioEqBasePointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_basicOpen_of_sectionRatioEq_basePoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (e k k' : ℕ), 3 ≤ k → ∀ (x : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G) (T : H0 U.LG.L k → H0 U.LG.L k'), (∀ s₁ s₂ : H0 U.LG.L k, SecRatioEq U.LG.L (x.left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (T s₁) (T s₂)) → ∀ (y : (thickObj R (maximalIdeal R) e G).left) (s₀ : H0 U.LG.L k) (i' : Fin 1 → U.LG.L.ι), y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen (((fstG (maximalIdeal R) e G).left.app (secChart U.LG.L i')).hom ((T s₀).f i')) → ∃ i : Fin 1 → U.LG.L.ι, y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen ((((x).left ≫ (fstG (maximalIdeal R) e G).left).app (secChart U.LG.L i)).hom (s₀.f i)) := by
  first | exact @GlobalTheory.Mum.mem_basicOpen_of_secRatioEq | exact GlobalTheory.Mum.mem_basicOpen_of_secRatioEq | (intros; apply GlobalTheory.Mum.mem_basicOpen_of_secRatioEq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianThickeningHomEqOfEqOnOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianThickeningHomEqOfEqOnOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumAgree

theorem subsingleton_thick (R : Type) [CommRing R] [IsLocalRing R] (e : ℕ) :
    Subsingleton (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))) := by
  have key : ∀ P : PrimeSpectrum (R ⧸ maximalIdeal R ^ (e + 1)),
      P.asIdeal.comap (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))) = maximalIdeal R := by
    intro P
    have hp : (P.asIdeal.comap (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1)))).IsPrime :=
      Ideal.comap_isPrime _ _
    have hle : maximalIdeal R ^ (e + 1) ≤ P.asIdeal.comap (Ideal.Quotient.mk _) := by
      intro r hr
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hr]
      exact P.asIdeal.zero_mem
    have hm : maximalIdeal R ≤ _ := hp.le_of_pow_le hle
    exact ((maximalIdeal.isMaximal R).eq_of_le hp.ne_top hm).symm
  constructor
  intro P Q
  change PrimeSpectrum _ at P Q
  exact PrimeSpectrum.ext (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
    ((key P).trans (key Q).symm))

theorem eq_of_eq_on_open : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (e : ℕ) (x x' : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), IsMonHom x → IsMonHom x' → ∀ (W : (thickObj R (maximalIdeal R) e G).left.Opens) (y : (thickObj R (maximalIdeal R) e G).left), y ∈ W → W.ι ≫ x.left = W.ι ≫ x'.left → x = x' := by
  intro R _ _ _ _ D A G _ _ hG U e x x' hx hx' W y hy hW
  have hH : IsSemiAbelian (thickObj R (maximalIdeal R) e G) :=
    IsSemiAbelian.pullback (thick R (maximalIdeal R) e) G hG
  have := hH.smooth
  have hflat : Flat (thickObj R (maximalIdeal R) e G).hom := inferInstance
  let V : Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))) :=
    Over.mk (W.ι ≫ (thickObj R (maximalIdeal R) e G).hom)
  let j : V ⟶ thickObj R (maximalIdeal R) e G := Over.homMk W.ι rfl
  have hsub := subsingleton_thick R e
  have hVs : Surjective V.hom := ⟨fun s => ⟨⟨y, hy⟩, Subsingleton.elim _ _⟩⟩
  have hj : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion W.ι)
  have hF := GlobalTheory.Mum.FlatMul.main _ _ V j hj hflat
  have hS := GlobalTheory.Mum.surjective_mul_of_open_of_irreducible_fibres _ _ V j hj hVs
    (fun K _ t => GlobalTheory.SemiAbFibre.irreducibleSpace_fibre _ _ hH K t)
  have : Epi ((fst V V ≫ j) * (snd V V ≫ j)).left := Flat.epi_of_flat_of_surjective _
  have : Epi ((fst V V ≫ j) * (snd V V ≫ j)) := Over.epi_of_epi_left _
  have hjx : j ≫ x = j ≫ x' := Over.OverMorphism.ext hW
  rw [← cancel_epi ((fst V V ≫ j) * (snd V V ≫ j)), MonObj.mul_comp, MonObj.mul_comp,
    Category.assoc, Category.assoc, Category.assoc, Category.assoc, hjx]

end GlobalTheory.MumAgree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianThickeningHomEqOfEqOnOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_thickening_hom_eq_of_eq_on_open : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (e : ℕ) (x x' : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), IsMonHom x → IsMonHom x' → ∀ (W : (thickObj R (maximalIdeal R) e G).left.Opens) (y : (thickObj R (maximalIdeal R) e G).left), y ∈ W → W.ι ≫ x.left = W.ι ≫ x'.left → x = x' := by
  first | exact @GlobalTheory.MumAgree.eq_of_eq_on_open | exact GlobalTheory.MumAgree.eq_of_eq_on_open | (intros; apply GlobalTheory.MumAgree.eq_of_eq_on_open <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalEndSecCoNonzeroLift
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem mem_basicOpen_of_comp {X Y Y' : Scheme.{0}} (c : Y ⟶ Y') (f : Y' ⟶ X) {U : X.Opens} (r : Γ(X, U))
    {y : Y} (h : y ∈ Y.basicOpen ((c ≫ f).app U r)) : c y ∈ Y'.basicOpen (f.app U r) := by
  rw [← Scheme.preimage_basicOpen] at h ⊢
  exact h

theorem secCoNonzero_of_comp {X Y Y' : Scheme.{0}} (L : LB X) {k k' : ℕ} (c : Y ⟶ Y') (u v : Y' ⟶ X)
    (s : H0 L k) (t : H0 L k') (h : SecCoNonzero L (c ≫ u) (c ≫ v) s t) : SecCoNonzero L u v s t := by
  obtain ⟨y, i, i', h1, h2⟩ := h
  exact ⟨c y, i, i', mem_basicOpen_of_comp c u _ h1, mem_basicOpen_of_comp c v _ h2⟩

theorem formalEnd_secCoNonzero_lift : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X) (b : ∀ e : ℕ, thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), FormalEnd U.toUnifPre a h' b → ∀ (k k' : ℕ) (s : H0 U.LG.L k) (t : H0 U.LG.L k'), SecCoNonzero U.LG.L ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left s t → ∀ e : ℕ, SecCoNonzero U.LG.L ((b e).left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s t := by
  intro R _ _ _ _ D A G _ _ _ U a h' b hb k k' s t h0 e
  induction e with
  | zero => exact h0
  | succ e ih =>
    apply secCoNonzero_of_comp U.LG.L (thickMap R (maximalIdeal R) e G)
    have hf : thickMap R (maximalIdeal R) e G ≫ (fstG (maximalIdeal R) (e + 1) G).left =
        (fstG (maximalIdeal R) e G).left := (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    rw [hf, ← Category.assoc, hb.2.1 e, Category.assoc, hf]
    exact ih

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioAppRestrict
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem secRatio_app_restrict {Y Z : Scheme.{0}} (h : Z ⟶ Y) {U W : Y.Opens} (hle : W ≤ U)
    (hle' : h ⁻¹ᵁ W ≤ h ⁻¹ᵁ U) (x : Γ(Y, U)) :
    (Z.presheaf.map (homOfLE hle').op).hom ((h.app U).hom x) =
      (h.app W).hom ((Y.presheaf.map (homOfLE hle).op).hom x) := by
  have := congrArg (fun φ => φ.hom x) (h.naturality (homOfLE hle).op)
  simpa using this.symm

theorem secRatioEq_comp : ∀ {X Y Z : Scheme.{0}} (L : LB X) {k k' : ℕ} (u v : Y ⟶ X) (h : Z ⟶ Y) (s₁ s₂ : H0 L k) (t₁ t₂ : H0 L k'), SecRatioEq L u v s₁ s₂ t₁ t₂ → SecRatioEq L (h ≫ u) (h ≫ v) s₁ s₂ t₁ t₂ := by
  intro X Y Z L k k' u v h s₁ s₂ t₁ t₂ hR i i'
  have e := congrArg (h.app (u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i')).hom (hR i i')
  simp only [map_mul] at e
  simp only [Scheme.Hom.comp_app, CommRingCat.hom_comp, RingHom.comp_apply]
  erw [secRatio_app_restrict h (inf_le_left : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ u ⁻¹ᵁ secChart L i),
    secRatio_app_restrict h (inf_le_right : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ v ⁻¹ᵁ secChart L i'),
    secRatio_app_restrict h (inf_le_left : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ u ⁻¹ᵁ secChart L i),
    secRatio_app_restrict h (inf_le_right : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ v ⁻¹ᵁ secChart L i')]
  exact e

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningEqOfGenericSectionRatios
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem fstG_comm_thick (R : Type) [CommRing R] (I : Ideal R) (e : ℕ) (G : Over (Sp R)) (g : G ⟶ G) :
    ((Over.pullback (thick R I e)).map g).left ≫ (fstG I e G).left = (fstG I e G).left ≫ g.left := by
  first
    | (have := congrArg CommaMorphism.left ((Over.mapPullbackAdj (thick R I e)).counit.naturality g)
       simpa [fstG] using this)
    | (simp [fstG]; exact pullback.lift_fst _ _ _)

theorem thick_eq_of_ratios : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (N : ℕ) (S : ∀ k : ℕ, H0 U.LG.L k → H0 U.LG.L (N * k)), (∀ (k e : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L ((b e).left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (S k s₁) (S k s₂)) → (∀ k : ℕ, 3 ≤ k → ∃ s₀ : H0 U.LG.L k, SecCoNonzero U.LG.L ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left s₀ (S k s₀)) → ∀ φ : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G, (∀ (k : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L (φ.left ≫ pullback.fst G.hom (jK R)) (pullback.fst G.hom (jK R)) s₁ s₂ (S k s₁) (S k s₂)) → ∀ g : G ⟶ G, IsMonHom g → (Over.pullback (jK R)).map g = φ → ∀ e, (Over.pullback (thick R (maximalIdeal R) e)).map g = b e := by
  intro R _ _ _ hB D A G _ _ hG U a a' h h' hE b hb N S hS hC φ hφ g hg hgφ e
  have hcomm : φ.left ≫ pullback.fst G.hom (jK R) = pullback.fst G.hom (jK R) ≫ g.left := by
    subst hgφ
    first
      | (simp; done)
      | (simp; exact pullback.lift_fst _ _ _)
      | exact pullback.lift_fst _ _ _
  have hGI : GeometricallyIntegral G.hom := GlobalTheory.geometricallyIntegral_of_isSemiAbelian G (h := hG)
  have hfin : Finite (irreducibleComponents (Sp R)) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  have hfl : Flat G.hom := by
    obtain ⟨_, hsm, -, -, -, -⟩ := hG
    infer_instance
  have hred : IsReduced G.left :=
    GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents G.hom
  have hdom : IsDominant (pullback.fst G.hom (jK R)) :=
    isDominant_genericFibre_of_flat R (FractionRing R) G.hom

  have hGrat : ∀ (k : ℕ) (s₁ s₂ : H0 U.LG.L k),
      SecRatioEq U.LG.L g.left (𝟙 G.left) s₁ s₂ (S k s₁) (S k s₂) := by
    intro k s₁ s₂
    apply SecRatioEq.of_isDominant (pullback.fst G.hom (jK R))
    rw [← hcomm, Category.comp_id]
    exact hφ k s₁ s₂

  have hxc : ((Over.pullback (thick R (maximalIdeal R) e)).map g).left ≫ (fstG (maximalIdeal R) e G).left =
      (fstG (maximalIdeal R) e G).left ≫ g.left := fstG_comm_thick R (maximalIdeal R) e G g
  have hxrat : ∀ (k : ℕ) (s₁ s₂ : H0 U.LG.L k),
      SecRatioEq U.LG.L (((Over.pullback (thick R (maximalIdeal R) e)).map g).left ≫ (fstG (maximalIdeal R) e G).left)
        (fstG (maximalIdeal R) e G).left s₁ s₂ (S k s₁) (S k s₂) := by
    intro k s₁ s₂
    have := secRatioEq_comp U.LG.L g.left (𝟙 G.left) (fstG (maximalIdeal R) e G).left s₁ s₂ (S k s₁) (S k s₂)
      (hGrat k s₁ s₂)
    rwa [Category.comp_id, ← hxc] at this
  have hxmon : IsMonHom ((Over.pullback (thick R (maximalIdeal R) e)).map g) := inferInstance
  obtain ⟨k₀, hk₀, hnear⟩ := GlobalTheory.T.uniformisedGroup_morphisms_agree_of_sectionRatios R hB D A G hG U
  obtain ⟨s₀, hs₀⟩ := hC k₀ hk₀

  obtain ⟨y, i'', i', hy1, hy2⟩ :=
    formalEnd_secCoNonzero_lift R hB D A G hG U a h' b hb k₀ (N * k₀) s₀ (S k₀ s₀) hs₀ e
  obtain ⟨i, hy0⟩ := GlobalTheory.T.mem_basicOpen_of_sectionRatioEq_basePoint R hB D A G hG U e k₀ (N * k₀) hk₀
    ((Over.pullback (thick R (maximalIdeal R) e)).map g) (S k₀) (hxrat k₀) y s₀ i' hy2
  obtain ⟨W, hyW, hW⟩ := hnear e k₀ (N * k₀) le_rfl ((Over.pullback (thick R (maximalIdeal R) e)).map g) (b e)
    (S k₀) (hxrat k₀) (fun s₁ s₂ => hS k₀ e s₁ s₂) y s₀ i i' i'' hy0 hy2 hy1
  exact GlobalTheory.T.semiAbelian_thickening_hom_eq_of_eq_on_open R hB D A G hG U e _ (b e) hxmon (hb.1 e) W y hyW hW

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningEqOfGenericSectionRatiosStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_eq_of_generic_section_ratios : (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (N : ℕ) (S : ∀ k : ℕ, H0 U.LG.L k → H0 U.LG.L (N * k)), (∀ (k e : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L ((b e).left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (S k s₁) (S k s₂)) → (∀ k : ℕ, 3 ≤ k → ∃ s₀ : H0 U.LG.L k, SecCoNonzero U.LG.L ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left s₀ (S k s₀)) → ∀ φ : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G, (∀ (k : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L (φ.left ≫ pullback.fst G.hom (jK R)) (pullback.fst G.hom (jK R)) s₁ s₂ (S k s₁) (S k s₂)) → ∀ g : G ⟶ G, IsMonHom g → (Over.pullback (jK R)).map g = φ → ∀ e, (Over.pullback (thick R (maximalIdeal R) e)).map g = b e) := by
  first | exact @GlobalTheory.Mum.thick_eq_of_ratios | exact GlobalTheory.Mum.thick_eq_of_ratios | (intros; apply GlobalTheory.Mum.thick_eq_of_ratios <;> assumption)
end
