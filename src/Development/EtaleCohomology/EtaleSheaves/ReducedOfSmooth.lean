module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.EtaleCohomology.EtaleSheaves.LeafSHNbSys
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MorphismDescendsToSubring
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.ReducedOfSmooth
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.E4

namespace LateralTheory.E.ReducedOfSmooth

theorem LeafReducedSmooth_of : LateralTheory.E.QuasiFiniteDescent.LeafReducedSmooth := by
  intro k _ Ω _ _ R _ D q hq
  have : Smooth q := hq.smooth
  have : _root_.IsReduced R := isReduced_of_injective R.val Subtype.val_injective
  have : AlgebraicGeometry.IsReduced (Spec (CommRingCat.of R)) := inferInstance
  exact GlobalTheory.isReduced_of_smooth_of_isReduced q

end LateralTheory.E.ReducedOfSmooth
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafClosedImmSpreadPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafSpreadSeparatedPf

namespace LateralTheory.E.LeafClosedImmSpreadPf

theorem bc_sq {X Y Z T : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (t : T ⟶ Z) :
    IsPullback (pullback.fst (f ≫ g) t) (BC f g (f ≫ g) rfl t) f (pullback.fst g t) := by
  have e : BC f g (f ≫ g) rfl t ≫ pullback.snd g t = pullback.snd (f ≫ g) t := by
    simp only [BC, pullback.map, pullback.lift_snd, Category.comp_id]
  refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback g t)
  · rw [e]; exact IsPullback.of_hasPullback (f ≫ g) t
  · simp only [BC, pullback.map, pullback.lift_fst]

theorem toR_eq {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) :
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap R.toSubring.subtype : Sp Ω ⟶ Sp R) = toR R := rfl

theorem incl_eq {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R S : Subalgebra k Ω} (h : R ≤ S)
    (h' : R.toSubring ≤ S.toSubring) :
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (Subring.inclusion h') : Sp S ⟶ Sp R) = incl h := rfl

theorem LeafClosedImmSpread_of : LeafClosedImmSpread := by
  intro k _ Ω _ _ R hR X Y f g hg hfg hci
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hp1, hp2, hp3⟩ := hfg
  have := hg1; have := hg2; have := hg3; have := hp1; have := hp2; have := hp3
  have : QuasiSeparated f := QuasiSeparated.of_comp f g
  have : QuasiCompact f := QuasiCompact.of_comp f g
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f g
  have hY : IsPullback (pullback.fst g (toR R)) (pullback.snd g (toR R)) (g : Y ⟶ Sp R.toSubring)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap R.toSubring.subtype) := by
    rw [toR_eq]; exact IsPullback.of_hasPullback g (toR R)
  have : QuasiCompact (g : Y ⟶ Sp R.toSubring) := hg2
  obtain ⟨F, hF⟩ := GlobalTheory.isClosedImmersion_descends_to_subring Ω R.toSubring X Y _ _ f g
    (BC f g (f ≫ g) rfl (toR R)) (pullback.fst _ _) (pullback.fst _ _) (pullback.snd _ _) hY (bc_sq f g _) hci
  let S : Subalgebra k Ω := R ⊔ Algebra.adjoin k (F : Set Ω)
  have h : R ≤ S := le_sup_left
  have h' : R.toSubring ≤ S.toSubring := fun x hx => h hx
  have hsub : (F : Set Ω) ⊆ S.toSubring := fun x hx =>
    (le_sup_right : Algebra.adjoin k (F : Set Ω) ≤ S) (Algebra.subset_adjoin hx)
  refine ⟨S, h, hR.sup (Subalgebra.fg_adjoin_finset F), ?_⟩
  have hY1 : IsPullback (pullback.fst g (incl h)) (pullback.snd g (incl h)) (g : Y ⟶ Sp R.toSubring)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (Subring.inclusion h')) := by
    rw [incl_eq h h']; exact IsPullback.of_hasPullback g (incl h)
  exact hF S.toSubring h' hsub _ _ (BC f g (f ≫ g) rfl (incl h)) (pullback.fst _ _) (pullback.fst _ _)
    (pullback.snd _ _) hY1 (bc_sq f g _)

end LateralTheory.E.LeafClosedImmSpreadPf

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.StalkContPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ZLGPf LateralTheory.E.StalkGermPf GlobalTheory.StalkLimit

namespace LateralTheory.E.StalkContPf

set_option backward.isDefEq.respectTransparency false

variable {X S : Scheme.{0}}

theorem diagram_map_eq (p : X ⟶ S) (s : S) {V W : AffNhd s} (i : V ⟶ W) :
    (diagram s p).map i = resO p i.le := by
  apply pullback.hom_ext <;> simp [diagram, resO]

theorem cone_app_eq (p : X ⟶ S) (s : S) (V : AffNhd s) :
    (cone (IsPullback.of_hasPullback p (S.fromSpecStalk s))).π.app V = toO p s V.1 V.2.1 := by
  apply pullback.hom_ext <;> simp [cone, toO]

theorem pull_cone {q : ℕ} {n i : ℤ} (p : X ⟶ S) (s : S) (V : AffNhd s) (y : Ht q (sch.obj (overO p V.1)) n i) :
    pull _ (sch.map ((cone (IsPullback.of_hasPullback p (S.fromSpecStalk s))).π.app V)) (tw q i) n y =
      pull _ (sch.map (toO p s V.1 V.2.1)) (tw q i) n y := by
  rw [cone_app_eq]; rfl

theorem pull_diag {q : ℕ} {n i : ℤ} (p : X ⟶ S) (s : S) {V W : AffNhd s} (f : V ⟶ W)
    (y : Ht q (sch.obj (overO p W.1)) n i) :
    pull _ (sch.map ((diagram s p).map f)) (tw q i) n y = pull _ (sch.map (resO p f.le)) (tw q i) n y := by
  rw [diagram_map_eq]; rfl

theorem exists_aff (s : S) (U : S.Opens) (hs : s ∈ U) : ∃ V : AffNhd s, V.1 ≤ U := by
  obtain ⟨W, h₁, h₂, h₃⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens hs
  exact ⟨⟨W, h₂, h₁⟩, h₃⟩

theorem StalkCont_of : StalkCont := by
  intro hC hH q X S p _ _ _ _ hq i n s
  have hc := (nonempty_isLimit (IsPullback.of_hasPullback p (S.fromSpecStalk s))).some
  have hcpt : ∀ V : AffNhd s, CompactSpace ((diagram s p).obj V) := fun V => by
    have : IsAffine V.1.toScheme := V.2.2
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd p V.1.ι)
  have hqs : ∀ V : AffNhd s, QuasiSeparatedSpace ((diagram s p).obj V) := fun V => by
    have : IsAffine V.1.toScheme := V.2.2
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd p V.1.ι)
  have hu : ∀ V : AffNhd s, IsUnit (q : Γ((diagram s p).obj V, ⊤)) := fun V => by
    have := hq.map ((pullback.fst p V.1.ι ≫ p).appTop).hom
    simp only [map_natCast] at this
    exact this
  obtain ⟨hsurj, hkill⟩ := hC hH q (diagram s p) _ hc (fun f => inferInstance) hcpt hqs hu n i
  constructor
  · intro U hs x hx
    obtain ⟨V0, hV0⟩ := exists_aff s U hs
    have h0 : pull _ (sch.map ((cone (IsPullback.of_hasPullback p (S.fromSpecStalk s))).π.app V0)) _ _
        (pull _ (sch.map (resO p hV0)) _ _ x) = 0 := by
      rw [pull_cone, ← pull_mc, toO_res]; exact hx
    obtain ⟨k, f, hf⟩ := hkill V0 _ h0
    have hkV : k.1 ≤ V0.1 := f.le
    refine ⟨k.1, hkV.trans hV0, k.2.1, ?_⟩
    rw [pull_diag, ← pull_mc, res_res] at hf
    exact hf
  · intro z
    obtain ⟨j, y, hy⟩ := hsurj z
    exact ⟨j.1, j.2.1, y, (pull_cone p s j y).symm.trans hy⟩

end LateralTheory.E.StalkContPf
end
end
