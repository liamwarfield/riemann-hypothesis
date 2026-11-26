module

public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibAmpleD
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FlatAndSurjectiveOfSurjectivePointsStatement

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.KerMemKL
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)

namespace PositivityTheory.PrwZar.Z2

set_option synthInstance.maxHeartbeats 400000 in
theorem ker_memKL {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {P : LB (A ⊗ B).left} (hD : IsDual A B P)
    (l : A ⟶ B) [IsMonHom l] {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S) [IsCommMonObj ((Over.pullback s).obj A)]
    (L : LB ((Over.pullback s).obj A).left)
    (hL : L.IsLB) (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
    {T : Over (Sp Ω)} (x : T ⟶ (Over.pullback s).obj A) (hx : x ≫ (Over.pullback s).map l = 1) :
    GlobalTheory.MemKL ((Over.pullback s).obj A) L x := by
  have hx0 : lam (cls L hL) (fst T ((Over.pullback s).obj A) ≫ x) (snd T ((Over.pullback s).obj A)) = 0 := by
    rw [lam_comm, lam_cL_pt s hD.isLB l L hL e, ← toBase_map, Category.assoc, hx, MonObj.comp_one, toBase_one]
    exact evc_one_right hD.isLB hD.zero _
  have hD' : (Out.translDiff ((Over.pullback s).obj A) L x).IsLB := LB.isLB_linComb hL _ _
  intro p
  obtain ⟨V, hV, hc⟩ := exists_pull_eq_zero
    (GlobalTheory.CechPic.pull x.left (cls L hL) - GlobalTheory.CechPic.pull (1 : T ⟶ (Over.pullback s).obj A).left (cls L hL)) p
  refine ⟨V, hV, (cls_eq_zero_iff (pull_isLB hD' _)).1 ?_⟩
  have e₁ := pull_translDiff hL x hD' (fst T _) (snd T _)
  rw [lift_fst_snd, Over.id_left, pull_id] at e₁
  have e₂ : cls _ hD' = GlobalTheory.CechPic.pull (fst T ((Over.pullback s).obj A)).left
      (GlobalTheory.CechPic.pull x.left (cls L hL) - GlobalTheory.CechPic.pull (1 : T ⟶ (Over.pullback s).obj A).left (cls L hL)) := by
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_one,
      ← sub_eq_zero, ← hx0, lam]
    abel
  rw [cls_pull hD', e₂, ← pull_comp]
  exact pull_eq_zero_of_mem V (((fst T _).left ⁻¹ᵁ V).ι ≫ (fst T _).left) (fun z ↦ z.2) hc

end PositivityTheory.PrwZar.Z2
end
end

section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.PfiFRangeFiniteClosed
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)

namespace PositivityTheory.PrwZar.Z2

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

private theorem pfiF_fib_subset_lemma {G' : Over (Sp Ω)} (σ : 𝟙_ (Over (Sp Ω)) ⟶ G') {K : Type} [Field K]
    (a : Spec (CommRingCat.of K) ⟶ G'.left) (p : (𝟙_ (Over (Sp Ω))).left)
    (ha : a (IsLocalRing.closedPoint K) = σ.left p) :
    a = (a ≫ G'.hom) ≫ σ.left := by
  have sec : σ.left ≫ G'.hom = 𝟙 _ := by simpa using Over.w σ
  obtain ⟨τ, hτ⟩ := GlobalTheory.exists_factor_of_lift_fromSpecResidueField G'.hom p
    (Scheme.fromSpecResidueField _ p ≫ σ.left)
    (by rw [Category.assoc, sec, Category.comp_id]; rfl) a
    (ha.trans (congrArg (fun q => σ.left q) (Scheme.fromSpecResidueField_apply p _)).symm)
  rw [← hτ]
  simp only [Category.assoc, sec, Category.comp_id]

theorem pfiF_range_finite_closed {G : Over (Sp Ω)} [GrpObj G] (hG : IsAbelianScheme G) (H : Over (Sp Ω))
    (j : H ⟶ G) (hH : IsFinite H.hom) :
    (Set.range j.left).Finite ∧ ∀ z ∈ Set.range j.left, IsClosed ({z} : Set G.left) := by
  haveI : IsFinite H.hom := hH
  haveI : IsProper G.hom := hG.proper
  haveI : IsLocallyArtinian H.left := .of_locallyQuasiFinite H.hom
  haveI : CompactSpace H.left := QuasiCompact.compactSpace_of_compactSpace H.hom
  haveI : IsProper (j.left ≫ G.hom) := by rw [Over.w j]; infer_instance
  haveI : IsProper j.left := IsProper.of_comp j.left G.hom
  haveI : Finite H.left := finite_of_compact_of_discrete
  refine ⟨Set.finite_range _, ?_⟩
  rintro _ ⟨h, rfl⟩
  have hc := j.left.isClosedMap {h} (isClosed_discrete _)
  simpa [Set.image_singleton] using hc

private theorem pfiF_fib_closed_lemma_2 {G G' : Over (Sp Ω)} [GrpObj G] [GrpObj G'] (f : G ⟶ G')
    [IsMonHom f] (H : Over (Sp Ω)) (j : H ⟶ G)
    (hj : ∀ (T : Over (Sp Ω)) (x : T ⟶ G), x ≫ f = 1 → ∃ z : T ⟶ H, z ≫ j = x)
    (s : 𝟙_ (Over (Sp Ω)) ⟶ G) (p : (𝟙_ (Over (Sp Ω))).left) (y : G.left)
    (hy : f.left y = f.left (s.left p)) : y ∈ Set.range (j * (toUnit H ≫ s)).left := by
  let T : Over (Sp Ω) := Over.mk (G.left.fromSpecResidueField y ≫ G.hom)
  let x : T ⟶ G := Over.homMk (G.left.fromSpecResidueField y) rfl
  let c : T ⟶ G := toUnit T ≫ s
  have e1 := Scheme.fromSpecResidueField_apply y (IsLocalRing.closedPoint (G.left.residueField y))
  have hfy : (G.left.fromSpecResidueField y ≫ f.left) (IsLocalRing.closedPoint _) =
      (s ≫ f).left p :=
    (congrArg f.left e1).trans hy
  have key := pfiF_fib_subset_lemma (s ≫ f) (G.left.fromSpecResidueField y ≫ f.left) p hfy
  have hxc : x ≫ f = c ≫ f := by
    apply Over.OverMorphism.ext
    change G.left.fromSpecResidueField y ≫ f.left = (toUnit T ≫ (s ≫ f)).left
    have hb : (G.left.fromSpecResidueField y ≫ f.left) ≫ G'.hom = (toUnit T).left := by
      simp [T]
    rw [Over.comp_left]
    exact key.trans (congrArg (· ≫ (s ≫ f).left) hb)
  have hx' : (x * c⁻¹) ≫ f = 1 := by
    change (IsMonHom.monoidHom f T) (x * c⁻¹) = 1
    rw [map_mul, map_inv]
    change (x ≫ f) * (c ≫ f)⁻¹ = 1
    rw [hxc, mul_inv_cancel]
  obtain ⟨z, hz⟩ := hj T _ hx'
  have hxz : x = z ≫ (j * (toUnit H ≫ s)) := by
    have hm : z ≫ (j * (toUnit H ≫ s)) = (z ≫ j) * c := by
      rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift, ← Category.assoc z (toUnit H) s,
        toUnit_unique (z ≫ toUnit H) (toUnit T)]
    rw [hm, hz, inv_mul_cancel_right]
  refine ⟨z.left (IsLocalRing.closedPoint (G.left.residueField y)), ?_⟩
  have h2 := congrArg
    (fun g : T ⟶ G => g.left (IsLocalRing.closedPoint (G.left.residueField y))) hxz
  exact h2.symm.trans e1

theorem pfiF_fib_closed {G G' : Over (Sp Ω)} [GrpObj G] [GrpObj G'] (hG : IsAbelianScheme G) (f : G ⟶ G')
    [IsMonHom f] (H : Over (Sp Ω)) (j : H ⟶ G) (hH : IsFinite H.hom)
    (hj : ∀ (T : Over (Sp Ω)) (x : T ⟶ G), x ≫ f = 1 → ∃ z : T ⟶ H, z ≫ j = x)
    (x : G.left) (hx : IsClosed ({x} : Set G.left)) :
    (f.left ⁻¹' {f.left x}).Finite ∧ ∀ z ∈ f.left ⁻¹' {f.left x}, IsClosed ({z} : Set G.left) := by
  haveI : LocallyOfFiniteType G.hom := by haveI := hG.smooth; infer_instance
  obtain ⟨s, hs⟩ := GlobalTheory.RationalPoint.exists_pt_mem (X := G) hx ⟨x, rfl⟩
  have hsx : s.left (IsLocalRing.closedPoint Ω) = x := hs
  have hsub : f.left ⁻¹' {f.left x} ⊆ Set.range (j * (toUnit H ≫ s)).left := fun y hy =>
    pfiF_fib_closed_lemma_2 f H j hj s (IsLocalRing.closedPoint Ω) y
      ((hy : f.left y = f.left x).trans (congrArg f.left hsx).symm)
  obtain ⟨hfin, hcl⟩ := pfiF_range_finite_closed hG H (j * (toUnit H ≫ s)) hH
  exact ⟨hfin.subset hsub, fun z hz => hcl z (hsub hz)⟩

theorem isFinite_of_ker {Ω : Type} [Field Ω] [IsAlgClosed Ω] {G G' : Over (Sp Ω)} [GrpObj G] [GrpObj G']
    (hG : IsAbelianScheme G) (hG' : IsAbelianScheme G') (f : G ⟶ G') [IsMonHom f] (H : Over (Sp Ω))
    (j : H ⟶ G) (hH : IsFinite H.hom)
    (hj : ∀ (T : Over (Sp Ω)) (x : T ⟶ G), x ≫ f = 1 → ∃ z : T ⟶ H, z ≫ j = x) : IsFinite f.left := by
  haveI : IsProper G.hom := hG.proper
  haveI : IsProper G'.hom := hG'.proper
  haveI : IsProper (f.left ≫ G'.hom) := by rw [Over.w f]; infer_instance
  haveI : IsProper f.left := IsProper.of_comp f.left G'.hom
  haveI : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace (Y := Spec _) G.hom
  haveI : LocallyQuasiFinite f.left :=
    GlobalTheory.locallyQuasiFinite_of_finite_fibres_closedPoints f.left fun y hy =>
      (pfiF_fib_closed hG f H j hH hj y hy).1
  exact IsFinite.of_isProper_of_locallyQuasiFinite f.left

end PositivityTheory.PrwZar.Z2
end
end

section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.SurjOfFiniteDimS
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)

namespace PositivityTheory.PrwZar.Z2

theorem surj_of_finite_dimS {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsFinite f] (g : ℕ)
    (hX : ∀ x : X, IsClosed ({x} : Set X) → ringKrullDim (X.presheaf.stalk x) = g)
    (hY : ∀ y : Y, IsClosed ({y} : Set Y) → ringKrullDim (Y.presheaf.stalk y) = g)
    (o : X) (ho : IsClosed ({o} : Set X)) : Surjective f := by
  refine ⟨fun y => ?_⟩
  have hcl : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
  suffices hη : genericPoint Y ∈ Set.range f by
    have hsub : closure ({genericPoint Y} : Set Y) ⊆ Set.range f :=
      closure_minimal (Set.singleton_subset_iff.mpr hη) hcl
    have hc : closure ({genericPoint Y} : Set Y) = Set.univ := genericPoint_spec Y
    rw [hc] at hsub
    exact hsub (Set.mem_univ y)
  by_contra hη
  have hmono : StrictMono f := GlobalTheory.FiniteEndFlat.strictMono_of_locallyQuasiFinite f
  let F : WithTop X → Y := fun a => WithTop.recTopCoe (genericPoint Y) (fun x => f x) a
  have hF : StrictMono F := by
    intro a b hab
    induction a using WithTop.recTopCoe with
    | top => exact absurd hab (not_top_lt)
    | coe a =>
      induction b using WithTop.recTopCoe with
      | top =>
        refine lt_of_le_of_ne (genericPoint_specializes (f a)) ?_
        intro h
        have hi : Inseparable (f a) (genericPoint Y) := h.symm
        exact hη ⟨a, hi.eq⟩
      | coe b => exact hmono (WithTop.coe_lt_coe.mp hab)
  have h1 := Order.coheight_le_coheight_apply_of_strictMono F hF (o : WithTop X)
  rw [Order.coheight_coe_withTop] at h1
  have hfo : IsClosed ({f o} : Set Y) := by
    have := f.isClosedMap _ ho
    rwa [Set.image_singleton] at this
  have e1 := hX o ho
  have e2 := hY (f o) hfo
  rw [ringKrullDim_stalk_eq_coheight] at e1 e2
  have e1' : Order.coheight o = g := by exact_mod_cast e1
  have e2' : Order.coheight (f o) = g := by exact_mod_cast e2
  change Order.coheight o + 1 ≤ Order.coheight (f o) at h1
  rw [e1', e2'] at h1
  exact absurd h1 (by norm_cast; omega)

theorem isClosed_originS {Ω : Type} [Field Ω] {G : Over (Sp Ω)} [GrpObj G] [IsProper G.hom] :
    IsClosed ({η[G].left (IsLocalRing.closedPoint Ω)} : Set G.left) := by
  have hc : IsClosed ({IsLocalRing.closedPoint Ω} : Set (Sp Ω)) := isClosed_singleton
  have h1 := (η[G].left).isClosedEmbedding.isClosedMap _ hc
  convert h1 using 1
  exact (Set.image_singleton).symm

theorem flat_surj_of_finite {Ω : Type} [Field Ω] [IsAlgClosed Ω] {G G' : Over (Sp Ω)} [GrpObj G] [GrpObj G']
    (hG : IsAbelianScheme G) (hG' : IsAbelianScheme G') (g : ℕ) (hgG : SmoothOfRelativeDimension g G.hom)
    (hgG' : SmoothOfRelativeDimension g G'.hom) (f : G ⟶ G') [IsMonHom f] (hf : IsFinite f.left) :
    Flat f.left ∧ Surjective f.left := by
  haveI := hG.smooth
  haveI := hG'.smooth
  haveI := hG.proper
  haveI := hG'.proper
  haveI := hf
  haveI : AlgebraicGeometry.IsIntegral G.left := GlobalTheory.isIntegral_of_isAbelianScheme_field Ω G hG
  haveI : AlgebraicGeometry.IsIntegral G'.left := GlobalTheory.isIntegral_of_isAbelianScheme_field Ω G' hG'
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  haveI : IsLocallyNoetherian G'.left := LocallyOfFiniteType.isLocallyNoetherian G'.hom
  have hsurj : Surjective f.left :=
    surj_of_finite_dimS f.left g
      (fun x hx => GlobalTheory.CutDegree.ringKrullDim_stalk hgG hx)
      (fun y hy => GlobalTheory.CutDegree.ringKrullDim_stalk hgG' hy)
      _ (isClosed_originS (G := G))
  haveI := hsurj
  exact ⟨GlobalTheory.SS.flat_of_isDominant_grpHom Ω G G' f, hsurj⟩

end PositivityTheory.PrwZar.Z2
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)

namespace PositivityTheory.PrwZar.Z2

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Ar.GR

theorem polFibreIsogAny : PositivityTheory.PrwZar.PolFibreIsogAny := by
  intro C _ _ v R _ _ hv A B _ _ P l g hA hB hgA hgB hD hD' hp Ω _ _ s
  have : IsMonHom l := hp.1
  obtain ⟨L, hL, ha, e⟩ := hp.2 Ω s
  have hA' := GlobalTheory.isAbelianScheme_pullback_obj s A hA
  have hB' := GlobalTheory.isAbelianScheme_pullback_obj s B hB
  have hgA' := GlobalTheory.FiniteData.relDim_pullback s A hgA
  have hgB' := GlobalTheory.FiniteData.relDim_pullback s B hgB
  haveI := hA'.comm
  obtain ⟨H, j, -, hH, hK⟩ := GlobalTheory.T.exists_finite_closed_subscheme_represents_kernel_ample GlobalTheory.globalFns_holds Ω ((Over.pullback s).obj A) hA' L hL ha
  have hfin : IsFinite ((Over.pullback s).map l).left :=
    isFinite_of_ker hA' hB' _ H j hH fun T x hx => (hK T x).1 (ker_memKL hD l s L hL e x hx)
  obtain ⟨hfl, hsu⟩ := flat_surj_of_finite hA' hB' g hgA' hgB' _ hfin
  exact ⟨hfin, hfl, hsu⟩

end PositivityTheory.PrwZar.Z2
