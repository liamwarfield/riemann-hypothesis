module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.StrictTransformClosedImmersion
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.StrictTransformTower
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceChartPresentation

@[expose] public section

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ChartPushforward
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]

structure ChartPushforward (S S' : EmbeddedBlowupSequence k Y pY) where
  ambientMap : S.ambient ⟶ S'.ambient
  isClosedImmersion_ambientMap : AlgebraicGeometry.IsClosedImmersion ambientMap
  emb_ambientMap : S.emb ≫ ambientMap = S'.emb
  len_eq : S.length = S'.length
  levelMap : ∀ i : ℕ, i ≤ S'.length → (S.schemeAt i ⟶ S'.schemeAt i)
  isClosedImmersion_levelMap :
    ∀ (i : ℕ) (hi : i ≤ S'.length), AlgebraicGeometry.IsClosedImmersion (levelMap i hi)
  levelMap_zero :
    levelMap 0 (Nat.zero_le _) ≫ S'.ambientSeq.isoZero.hom =
      S.ambientSeq.isoZero.hom ≫ ambientMap
  levelMap_blowdown :
    ∀ (i : ℕ) (hi : i < S'.length),
      levelMap (i + 1) hi ≫ S'.blowdown i = S.blowdown i ≫ levelMap i hi.le
  ambientCenter_eq :
    ∀ (i : ℕ) (hi : i < S'.length),
      S'.ambientCenter i = imageIdealSheaf (levelMap i hi.le) (S.ambientCenter i)
  ker_levelMap_succ :
    ∀ (i : ℕ) (hi : i < S'.length),
      (levelMap (i + 1) hi).ker =
        Blowup.strictTransform (S'.blowdown i) (S'.ambientCenter i) (levelMap i hi.le).ker

namespace ChartPushforward

section

variable {S S' : EmbeddedBlowupSequence k Y pY}

instance instIsClosedImmersionLevelMap (P : ChartPushforward S S') (i : ℕ) (hi : i ≤ S'.length) :
    AlgebraicGeometry.IsClosedImmersion (P.levelMap i hi) :=
  P.isClosedImmersion_levelMap i hi

theorem le_length (P : ChartPushforward S S') {i : ℕ} (hi : i ≤ S'.length) : i ≤ S.length :=
  hi.trans_eq P.len_eq.symm

end

section

variable (S S' : EmbeddedBlowupSequence k Y pY) (f : S.ambient ⟶ S'.ambient)
  [AlgebraicGeometry.IsClosedImmersion f]

theorem isClosedImmersion_of_isPushforwardBlowupSeq
    (h : IsPushforwardBlowupSeq f S.ambientSeq S'.ambientSeq) (i : ℕ) (hi : i ≤ S'.length) :
    AlgebraicGeometry.IsClosedImmersion (h.2.choose i (hi.trans_eq h.1.symm)) :=
  h.2.choose_spec.1 i (hi.trans_eq h.1.symm)

theorem isoObjZero_comm_of_isPushforwardBlowupSeq
    (h : IsPushforwardBlowupSeq f S.ambientSeq S'.ambientSeq) :
    h.2.choose 0 ((Nat.zero_le S'.length).trans_eq h.1.symm) ≫ S'.ambientSeq.isoZero.hom =
      S.ambientSeq.isoZero.hom ≫ f := by
  exact h.2.choose_spec.2.1

theorem blowdown_comm_of_isPushforwardBlowupSeq
    (h : IsPushforwardBlowupSeq f S.ambientSeq S'.ambientSeq) (i : ℕ) (hi : i < S'.length) :
    h.2.choose (i + 1) (hi.trans_eq h.1.symm) ≫ S'.blowdown i =
      S.blowdown i ≫ h.2.choose i (hi.le.trans_eq h.1.symm) :=
  h.2.choose_spec.2.2.1 i (hi.trans_eq h.1.symm)

theorem ambientCenter_eq_imageIdealSheaf_of_isPushforwardBlowupSeq
    (h : IsPushforwardBlowupSeq f S.ambientSeq S'.ambientSeq) (i : ℕ) (hi : i < S'.length) :
    S'.ambientCenter i =
      imageIdealSheaf (h.2.choose i (hi.le.trans_eq h.1.symm)) (S.ambientCenter i) :=
  h.2.choose_spec.2.2.2.1 i (hi.trans_eq h.1.symm)

theorem ker_succ_eq_strictTransform_of_isPushforwardBlowupSeq
    (h : IsPushforwardBlowupSeq f S.ambientSeq S'.ambientSeq) (i : ℕ) (hi : i < S'.length) :
    (h.2.choose (i + 1) (hi.trans_eq h.1.symm)).ker =
      Blowup.strictTransform (S'.blowdown i) (S'.ambientCenter i)
        (h.2.choose i (hi.le.trans_eq h.1.symm)).ker :=
  h.2.choose_spec.2.2.2.2 i (hi.trans_eq h.1.symm)

def ofIsPushforwardSeq (hemb : S.emb ≫ f = S'.emb)
    (h : IsPushforwardBlowupSeq f S.ambientSeq S'.ambientSeq) : ChartPushforward S S' where
  ambientMap := f
  isClosedImmersion_ambientMap := inferInstance
  emb_ambientMap := hemb
  len_eq := h.1
  levelMap := fun i hi => h.2.choose i (hi.trans_eq h.1.symm)
  isClosedImmersion_levelMap := fun i hi => isClosedImmersion_of_isPushforwardBlowupSeq S S' f h i hi
  levelMap_zero := isoObjZero_comm_of_isPushforwardBlowupSeq S S' f h
  levelMap_blowdown := fun i hi => blowdown_comm_of_isPushforwardBlowupSeq S S' f h i hi
  ambientCenter_eq := fun i hi => ambientCenter_eq_imageIdealSheaf_of_isPushforwardBlowupSeq S S' f h i hi
  ker_levelMap_succ := fun i hi => ker_succ_eq_strictTransform_of_isPushforwardBlowupSeq S S' f h i hi

end

section

variable {S S' : EmbeddedBlowupSequence k Y pY}

private theorem map_strictTransformIdeal_levelMap {T T' : EmbeddedBlowupSequence k Y pY}
    (P : ChartPushforward T T') (i : ℕ) :
    ∀ hi : i ≤ T'.length, (T.strictTransformIdeal i).map (P.levelMap i hi) = T'.strictTransformIdeal i := by
  induction i with
  | zero =>
    intro hi
    have key : T.ambientSeq.isoZero.inv ≫ P.levelMap 0 hi
        = P.ambientMap ≫ T'.ambientSeq.isoZero.inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, ← P.levelMap_zero, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    have hcomp : (T.emb ≫ T.ambientSeq.isoZero.inv) ≫ P.levelMap 0 hi
        = T'.emb ≫ T'.ambientSeq.isoZero.inv := by
      rw [Category.assoc, key, ← Category.assoc, P.emb_ambientMap]
    rw [EmbeddedBlowupSequence.strictTransformIdeal_zero, EmbeddedBlowupSequence.strictTransformIdeal_zero, ← Scheme.Hom.ker_comp, hcomp]
  | succ n ih =>
    intro hi
    have hn : n < T'.length := Nat.lt_of_succ_le hi
    have : AlgebraicGeometry.IsNoetherian (T.schemeAt (n + 1)) :=
      T.isNoetherian_schemeAt (n + 1) (P.le_length hi)
    have : AlgebraicGeometry.IsNoetherian (T'.schemeAt (n + 1)) :=
      T'.isNoetherian_schemeAt (n + 1) hi
    have hsq : P.levelMap (n + 1) hi ≫ T'.blowdown n = T.blowdown n ≫ P.levelMap n hn.le :=
      P.levelMap_blowdown n hn
    have hcenter : (T.ambientCenter n).map (P.levelMap n hn.le) = T'.ambientCenter n := by
      rw [map_eq_ker_subschemeι_comp, P.ambientCenter_eq n hn, imageIdealSheaf_eq_ker]
    have hker : Scheme.Hom.ker (P.levelMap (n + 1) hi)
        = Blowup.strictTransform (T'.blowdown n) ((T.ambientCenter n).map (P.levelMap n hn.le))
            (Scheme.Hom.ker (P.levelMap n hn.le)) := by
      rw [hcenter]
      exact P.ker_levelMap_succ n hn
    have hmain := map_strictTransform_eq_strictTransform_map (P.levelMap n hn.le)
      (T.ambientCenter n) (T.strictTransformIdeal n) (T.blowdown n) (T'.blowdown n)
      (P.levelMap (n + 1) hi) hsq hker
    rw [EmbeddedBlowupSequence.strictTransformIdeal_succ, EmbeddedBlowupSequence.strictTransformIdeal_succ, hmain, ih hn.le, hcenter]

theorem exists_strictTransform_iso (P : ChartPushforward S S') (i : ℕ) (hi : i ≤ S'.length) :
    ∃ e : S.strictTransform i ≅ S'.strictTransform i,
      e.hom ≫ S'.strictTransformι i = S.strictTransformι i ≫ P.levelMap i hi := by
  have hmap := map_strictTransformIdeal_levelMap P i hi
  have hA : Scheme.Hom.ker (S.strictTransformι i) = S.strictTransformIdeal i := by
    rw [S.strictTransformι_eq_subschemeι]
    exact Scheme.IdealSheafData.ker_subschemeι _
  have hA' : Scheme.Hom.ker (S'.strictTransformι i) = S'.strictTransformIdeal i := by
    rw [S'.strictTransformι_eq_subschemeι]
    exact Scheme.IdealSheafData.ker_subschemeι _
  have : AlgebraicGeometry.IsClosedImmersion (S.strictTransformι i ≫ P.levelMap i hi) := inferInstance
  have hker : Scheme.Hom.ker (S'.strictTransformι i) = Scheme.Hom.ker (S.strictTransformι i ≫ P.levelMap i hi) := by
    rw [Scheme.Hom.ker_comp, hA, hA', hmap]
  have := AlgebraicGeometry.IsClosedImmersion.isIso_lift (S'.strictTransformι i)
    (S.strictTransformι i ≫ P.levelMap i hi) hker
  refine ⟨asIso (AlgebraicGeometry.IsClosedImmersion.lift (S'.strictTransformι i)
    (S.strictTransformι i ≫ P.levelMap i hi) (le_of_eq hker)), ?_⟩
  rw [asIso_hom, AlgebraicGeometry.IsClosedImmersion.lift_fac]

def strictTransformIso (P : ChartPushforward S S') (i : ℕ) (hi : i ≤ S'.length) :
    S.strictTransform i ≅ S'.strictTransform i :=
  (P.exists_strictTransform_iso i hi).choose

theorem strictTransformIso_hom_comp_strictTransformι (P : ChartPushforward S S') (i : ℕ) (hi : i ≤ S'.length) :
    (P.strictTransformIso i hi).hom ≫ S'.strictTransformι i = S.strictTransformι i ≫ P.levelMap i hi :=
  (P.exists_strictTransform_iso i hi).choose_spec

@[reassoc]
theorem strictTransformIso_hom_comp_strictTransformMap (P : ChartPushforward S S') (i : ℕ) (hi : i < S'.length) :
    (P.strictTransformIso (i + 1) hi).hom ≫ S'.strictTransformMap i =
      S.strictTransformMap i ≫ (P.strictTransformIso i hi.le).hom := by
  have hmono : Mono (S'.strictTransformι i) := by
    rw [EmbeddedBlowupSequence.strictTransformι_eq_subschemeι]
    infer_instance
  rw [← cancel_mono (S'.strictTransformι i)]
  simp only [Category.assoc]
  rw [strictTransformIso_hom_comp_strictTransformι P i hi.le, EmbeddedBlowupSequence.strictTransformMap_comp_strictTransformι S' i, ← Category.assoc,
    strictTransformIso_hom_comp_strictTransformι P (i + 1) hi, Category.assoc, P.levelMap_blowdown i hi,
    ← Category.assoc, ← EmbeddedBlowupSequence.strictTransformMap_comp_strictTransformι S i, Category.assoc]

theorem strictTransformIso_zero_hom_comp_strictTransformZeroIso_hom (P : ChartPushforward S S') :
    (P.strictTransformIso 0 (Nat.zero_le _)).hom ≫ S'.strictTransformZeroIso.hom = S.strictTransformZeroIso.hom := by
  have key : ((P.strictTransformIso 0 (Nat.zero_le _)).hom ≫ S'.strictTransformZeroIso.hom) ≫ S'.emb
      = S.strictTransformZeroIso.hom ≫ S'.emb := by
    calc ((P.strictTransformIso 0 (Nat.zero_le _)).hom ≫ S'.strictTransformZeroIso.hom) ≫ S'.emb
        = (P.strictTransformIso 0 (Nat.zero_le _)).hom ≫ (S'.strictTransformZeroIso.hom ≫ S'.emb) := by
          rw [Category.assoc]
      _ = (P.strictTransformIso 0 (Nat.zero_le _)).hom ≫ (S'.strictTransformι 0 ≫ S'.ambientSeq.isoZero.hom) := by
          rw [S'.strictTransformZeroIso_hom_emb]
      _ = ((P.strictTransformIso 0 (Nat.zero_le _)).hom ≫ S'.strictTransformι 0) ≫ S'.ambientSeq.isoZero.hom := by
          rw [Category.assoc]
      _ = (S.strictTransformι 0 ≫ P.levelMap 0 (Nat.zero_le _)) ≫ S'.ambientSeq.isoZero.hom := by
          rw [P.strictTransformIso_hom_comp_strictTransformι 0 (Nat.zero_le _)]
      _ = S.strictTransformι 0 ≫ (P.levelMap 0 (Nat.zero_le _) ≫ S'.ambientSeq.isoZero.hom) := by
          rw [Category.assoc]
      _ = S.strictTransformι 0 ≫ (S.ambientSeq.isoZero.hom ≫ P.ambientMap) := by
          rw [P.levelMap_zero]
      _ = (S.strictTransformι 0 ≫ S.ambientSeq.isoZero.hom) ≫ P.ambientMap := by
          rw [Category.assoc]
      _ = (S.strictTransformZeroIso.hom ≫ S.emb) ≫ P.ambientMap := by
          rw [S.strictTransformZeroIso_hom_emb]
      _ = S.strictTransformZeroIso.hom ≫ (S.emb ≫ P.ambientMap) := by
          rw [Category.assoc]
      _ = S.strictTransformZeroIso.hom ≫ S'.emb := by
          rw [P.emb_ambientMap]
  exact (cancel_mono S'.emb).mp key

private theorem range_subset_range_of_ker_le {U V W : Scheme.{u}} (f : U ⟶ W) (g : V ⟶ W)
    [AlgebraicGeometry.IsClosedImmersion f] [AlgebraicGeometry.IsClosedImmersion g]
    (hle : Scheme.Hom.ker g ≤ Scheme.Hom.ker f) :
    Set.range ⇑f ⊆ Set.range ⇑g := by
  obtain ⟨e, he⟩ : ∃ e : U ⟶ V, e ≫ g = f :=
    ⟨AlgebraicGeometry.IsClosedImmersion.lift g f hle, by rw [IsClosedImmersion.lift_fac]⟩
  rintro y ⟨x, rfl⟩
  refine ⟨e.base x, ?_⟩
  have hx : ⇑(e ≫ g) x = ⇑f x := by rw [he]
  exact hx

private theorem support_ker_eq_range {U W : Scheme.{u}} (h : U ⟶ W)
    [AlgebraicGeometry.IsClosedImmersion h] :
    ((Scheme.Hom.ker h).support : Set ↥W) = Set.range ⇑h := by
  have hker : Scheme.Hom.ker ((Scheme.Hom.ker h).subschemeι) = Scheme.Hom.ker h :=
    Scheme.IdealSheafData.ker_subschemeι _
  have h1 : Set.range ⇑((Scheme.Hom.ker h).subschemeι)
      = ((Scheme.Hom.ker h).support : Set ↥W) :=
    Scheme.IdealSheafData.range_subschemeι _
  rw [← h1]
  exact Set.Subset.antisymm (range_subset_range_of_ker_le _ h (le_of_eq hker.symm))
    (range_subset_range_of_ker_le h _ (le_of_eq hker))

theorem support_ambientCenter_eq_image (P : ChartPushforward S S') (i : ℕ) (hi : i < S'.length) :
    ((S'.ambientCenter i).support : Set ↥(S'.schemeAt i)) =
      ⇑(P.levelMap i hi.le) '' ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) := by
  have hJ := P.ambientCenter_eq i hi
  rw [imageIdealSheaf_eq_ker] at hJ
  have hI : ((S.ambientCenter i).support : Set ↥(S.schemeAt i))
      = Set.range ⇑((S.ambientCenter i).subschemeι) := by
    have h2 := support_ker_eq_range ((S.ambientCenter i).subschemeι)
    rwa [Scheme.IdealSheafData.ker_subschemeι] at h2
  have hcomp : ⇑((S.ambientCenter i).subschemeι ≫ P.levelMap i hi.le)
      = ⇑(P.levelMap i hi.le) ∘ ⇑((S.ambientCenter i).subschemeι) := rfl
  rw [hJ, support_ker_eq_range, hI, hcomp, Set.range_comp]

end

end ChartPushforward

end FunctorialResolution.EmbeddedResolution

end
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.InactiveTotalSpacePushforward
section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.DetachedLocusPushforward
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace ChartPushforward

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
  {S S' : EmbeddedBlowupSequence k Y pY}

private theorem mem_irreducibleComponents_iff_image {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] (f : α → β) (g : β → α) (hf : Continuous f) (hg : Continuous g)
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) (C : Set α) :
    C ∈ irreducibleComponents α ↔ f '' C ∈ irreducibleComponents β := by
  have hinj : Function.Injective f := by
    intro a b hab
    have h := congrArg g hab
    rwa [hgf, hgf] at h
  have hirrf : ∀ s : Set α, IsIrreducible s → IsIrreducible (f '' s) := fun s hs =>
    hs.image f hf.continuousOn
  have hirrg : ∀ t : Set β, IsIrreducible t → IsIrreducible (g '' t) := fun t ht =>
    ht.image g hg.continuousOn
  have himg : g '' (f '' C) = C := by
    apply Set.Subset.antisymm
    · rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      rwa [hgf]
    · intro x hx
      exact ⟨f x, ⟨x, hx, rfl⟩, hgf x⟩
  constructor
  · intro hC0
    have hC : IsIrreducible C ∧ ∀ ⦃b : Set α⦄, IsIrreducible b → C ≤ b → b ≤ C := hC0
    show IsIrreducible (f '' C) ∧ ∀ ⦃b : Set β⦄, IsIrreducible b → f '' C ≤ b → b ≤ f '' C
    refine ⟨hirrf C hC.1, ?_⟩
    intro t ht hsub
    have hsub' : f '' C ⊆ t := hsub
    have hCt : C ⊆ g '' t := fun x hx => ⟨f x, hsub' ⟨x, hx, rfl⟩, hgf x⟩
    have hle : g '' t ⊆ C := hC.2 (hirrg t ht) hCt
    intro y hy
    exact ⟨g y, hle ⟨y, hy, rfl⟩, hfg y⟩
  · intro hC0
    have hC : IsIrreducible (f '' C) ∧
        ∀ ⦃b : Set β⦄, IsIrreducible b → f '' C ≤ b → b ≤ f '' C := hC0
    show IsIrreducible C ∧ ∀ ⦃b : Set α⦄, IsIrreducible b → C ≤ b → b ≤ C
    refine ⟨?_, ?_⟩
    · have h1 := hirrg _ hC.1
      rwa [himg] at h1
    · intro t ht hsub
      have hsub' : C ⊆ t := hsub
      have himt : f '' C ⊆ f '' t := by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨x, hsub' hx, rfl⟩
      have hle : f '' t ⊆ f '' C := hC.2 (hirrf t ht) himt
      intro x hx
      obtain ⟨x', hx', hxx⟩ := hle ⟨x, hx, rfl⟩
      have hx'x : x' = x := hinj hxx
      rwa [← hx'x]

theorem mem_detachedComponents_iff (P : ChartPushforward S S') (i : ℕ) (hi : i < S'.length)
    (C : Set ↥(S.strictTransform i)) :
    C ∈ S.detachedComponents i ↔
      ⇑((P.strictTransformIso i hi.le).hom) '' C ∈ S'.detachedComponents i := by
  have hgf : ∀ x : ↥(S.strictTransform i),
      ((P.strictTransformIso i hi.le).inv).base (((P.strictTransformIso i hi.le).hom).base x) = x := fun x =>
    Scheme.hom_inv_apply (P.strictTransformIso i hi.le) x
  have hfg : ∀ y : ↥(S'.strictTransform i),
      ((P.strictTransformIso i hi.le).hom).base (((P.strictTransformIso i hi.le).inv).base y) = y := fun y =>
    Scheme.inv_hom_apply (P.strictTransformIso i hi.le) y
  have hcomm : ∀ x : ↥(S.strictTransform i),
      (S'.strictTransformι i).base (((P.strictTransformIso i hi.le).hom).base x)
        = (P.levelMap i hi.le).base ((S.strictTransformι i).base x) := fun x =>
    congrArg (fun g : S.strictTransform i ⟶ S'.schemeAt i => g.base x)
      (P.strictTransformIso_hom_comp_strictTransformι i hi.le)
  have hinj :=
    (AlgebraicGeometry.Scheme.Hom.isClosedEmbedding (P.levelMap i hi.le)).injective
  have hsupp := P.support_ambientCenter_eq_image i hi
  simp only [EmbeddedBlowupSequence.mem_detachedComponents]
  refine and_congr (mem_irreducibleComponents_iff_image (⇑((P.strictTransformIso i hi.le).hom))
    (⇑((P.strictTransformIso i hi.le).inv)) (P.strictTransformIso i hi.le).hom.base.hom.continuous
    (P.strictTransformIso i hi.le).inv.base.hom.continuous hgf hfg C) ?_
  constructor
  · intro h z hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨x, hxC, rfl⟩ := hy
    rw [hsupp]
    exact ⟨(S.strictTransformι i).base x, h ⟨x, hxC, rfl⟩, (hcomm x).symm⟩
  · intro h z hz
    obtain ⟨x, hxC, rfl⟩ := hz
    have hmem : (S'.strictTransformι i).base (((P.strictTransformIso i hi.le).hom).base x)
        ∈ ((S'.ambientCenter i).support : Set ↥(S'.schemeAt i)) :=
      h ⟨((P.strictTransformIso i hi.le).hom).base x, ⟨x, hxC, rfl⟩, rfl⟩
    rw [hsupp] at hmem
    obtain ⟨w, hw, hweq⟩ := hmem
    have hweq' : (P.levelMap i hi.le).base w
        = (P.levelMap i hi.le).base ((S.strictTransformι i).base x) := hweq.trans (hcomm x)
    have hwx : w = (S.strictTransformι i).base x := hinj hweq'
    rwa [hwx] at hw

private theorem sUnion_eq_image_sUnion {α β : Type u} (f : α → β)
    (hf : Function.Surjective f) (A : Set (Set α)) (B : Set (Set β))
    (h : ∀ C : Set α, C ∈ A ↔ f '' C ∈ B) :
    ⋃₀ B = f '' (⋃₀ A) := by
  apply Set.Subset.antisymm
  · rintro x ⟨D, hD, hxD⟩
    obtain ⟨y, rfl⟩ := hf x
    refine ⟨y, ⟨f ⁻¹' D, ?_, hxD⟩, rfl⟩
    refine (h (f ⁻¹' D)).mpr ?_
    rw [Set.image_preimage_eq D hf]
    exact hD
  · rintro z ⟨y, hy, rfl⟩
    obtain ⟨C, hC, hyC⟩ := hy
    exact ⟨f '' C, (h C).mp hC, ⟨y, hyC, rfl⟩⟩

theorem detachedLocus_eq_image (P : ChartPushforward S S') (i : ℕ) (hi : i < S'.length) :
    S'.detachedLocus i = ⇑((P.strictTransformIso i hi.le).hom) '' S.detachedLocus i := by
  have hsurj : Function.Surjective ⇑((P.strictTransformIso i hi.le).hom) :=
    (Scheme.homeoOfIso (P.strictTransformIso i hi.le)).surjective
  rw [S'.detachedLocus_eq_sUnion i, S.detachedLocus_eq_sUnion i]
  exact sUnion_eq_image_sUnion _ hsurj _ _
    (fun C => P.mem_detachedComponents_iff i hi C)

theorem coe_detachedClosure_eq_image (P : ChartPushforward S S') (i : ℕ) (hi : i < S'.length) :
    (↑(S'.detachedClosure i) : Set ↥(S'.strictTransform i)) =
      ⇑((P.strictTransformIso i hi.le).hom) '' (↑(S.detachedClosure i) : Set ↥(S.strictTransform i)) := by
  have h1 : (↑(S'.detachedClosure i) : Set ↥(S'.strictTransform i)) = closure (S'.detachedLocus i) := rfl
  have h2 : (↑(S.detachedClosure i) : Set ↥(S.strictTransform i)) = closure (S.detachedLocus i) := rfl
  rw [h1, h2, P.detachedLocus_eq_image i hi]
  exact ((Scheme.homeoOfIso (P.strictTransformIso i hi.le)).image_closure (S.detachedLocus i)).symm

theorem preimage_coe_detachedClosure (P : ChartPushforward S S') (i : ℕ) (hi : i < S'.length) :
    ⇑((P.strictTransformIso i hi.le).hom) ⁻¹' (↑(S'.detachedClosure i) : Set ↥(S'.strictTransform i)) =
      (↑(S.detachedClosure i) : Set ↥(S.strictTransform i)) := by
  rw [P.coe_detachedClosure_eq_image i hi]
  exact Set.preimage_image_eq _ (Scheme.homeoOfIso (P.strictTransformIso i hi.le)).injective

theorem comap_detachedIdeal (P : ChartPushforward S S') [AlgebraicGeometry.IsReduced Y] (i : ℕ)
    (hi : i < S'.length) :
    (S'.detachedIdeal i).comap (P.strictTransformIso i hi.le).hom = S.detachedIdeal i := by
  have hn' : TopologicalSpace.NoetherianSpace ↥(S'.strictTransform i) :=
    S'.noetherianSpace_strictTransform i hi.le
  have hn : TopologicalSpace.NoetherianSpace ↥(S.strictTransform i) :=
    S.noetherianSpace_strictTransform i (P.le_length hi.le)
  have hr' : AlgebraicGeometry.IsReduced (S'.strictTransform i) :=
    S'.isReduced_strictTransform i hi.le
  have hr : AlgebraicGeometry.IsReduced (S.strictTransform i) :=
    S.isReduced_strictTransform i (P.le_length hi.le)
  have hfl : AlgebraicGeometry.Flat (P.strictTransformIso i hi.le).hom := inferInstance
  have hS : S'.detachedComponents i ⊆ irreducibleComponents ↥(S'.strictTransform i) :=
    fun C hC => ((S'.mem_detachedComponents i C).mp hC).1
  have hZ : (↑(S'.detachedClosure i) : Set ↥(S'.strictTransform i)) = ⋃₀ (S'.detachedComponents i) :=
    (S'.detachedClosure_coe i).trans (S'.detachedLocus_eq_sUnion i)
  have hZ' : (↑(S.detachedClosure i) : Set ↥(S.strictTransform i)) =
      ⇑((P.strictTransformIso i hi.le).hom).base ⁻¹' (⋃₀ (S'.detachedComponents i)) := by
    rw [← hZ]
    exact (P.preimage_coe_detachedClosure i hi).symm
  rw [S'.detachedIdeal_eq i, S.detachedIdeal_eq i]
  exact comap_vanishingIdeal_sUnion (P.strictTransformIso i hi.le).hom hS hZ hZ'

private theorem exists_subschemeIso_of_comap_eq {X Z : Scheme.{u}} (e : X ≅ Z)
    (I : X.IdealSheafData) (J : Z.IdealSheafData) (h : J.comap e.hom = I) :
    ∃ u : I.subscheme ≅ J.subscheme, u.hom ≫ J.subschemeι = I.subschemeι ≫ e.hom := by
  have h1 : J ≤ I.map e.hom :=
    Scheme.IdealSheafData.le_map_iff_comap_le.mpr (le_of_eq h)
  have hcomp : I.comap e.inv = J := by
    rw [← h, ← Scheme.IdealSheafData.comap_comp, e.inv_hom_id,
      Scheme.IdealSheafData.comap_id]
  have h2 : I ≤ J.map e.inv :=
    Scheme.IdealSheafData.le_map_iff_comap_le.mpr (le_of_eq hcomp)
  obtain ⟨a, ha⟩ : ∃ a : I.subscheme ⟶ J.subscheme,
      a ≫ J.subschemeι = I.subschemeι ≫ e.hom :=
    ⟨I.subschemeMap J e.hom h1, Scheme.IdealSheafData.subschemeMap_subschemeι I J e.hom h1⟩
  obtain ⟨b, hb⟩ : ∃ b : J.subscheme ⟶ I.subscheme,
      b ≫ I.subschemeι = J.subschemeι ≫ e.inv :=
    ⟨J.subschemeMap I e.inv h2, Scheme.IdealSheafData.subschemeMap_subschemeι J I e.inv h2⟩
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  · refine (cancel_mono I.subschemeι).mp ?_
    rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc, e.hom_inv_id,
      Category.comp_id, Category.id_comp]
  · refine (cancel_mono J.subschemeι).mp ?_
    rw [Category.assoc, ha, ← Category.assoc, hb, Category.assoc, e.inv_hom_id,
      Category.comp_id, Category.id_comp]

theorem exists_iso_detachedScheme (P : ChartPushforward S S') [AlgebraicGeometry.IsReduced Y] (i : ℕ)
    (hi : i < S'.length) :
    ∃ e : S.detachedScheme i ≅ S'.detachedScheme i,
      e.hom ≫ S'.detachedι i = S.detachedι i ≫ (P.strictTransformIso i hi.le).hom := by
  exact exists_subschemeIso_of_comap_eq (P.strictTransformIso i hi.le) (S.detachedIdeal i)
    (S'.detachedIdeal i) (P.comap_detachedIdeal i hi)

def detachedSchemeIso (P : ChartPushforward S S') [AlgebraicGeometry.IsReduced Y] (i : ℕ)
    (hi : i < S'.length) : S.detachedScheme i ≅ S'.detachedScheme i :=
  (P.exists_iso_detachedScheme i hi).choose

@[reassoc]
theorem detachedSchemeIso_hom_comp_detachedι (P : ChartPushforward S S') [AlgebraicGeometry.IsReduced Y] (i : ℕ)
    (hi : i < S'.length) :
    (P.detachedSchemeIso i hi).hom ≫ S'.detachedι i = S.detachedι i ≫ (P.strictTransformIso i hi.le).hom :=
  (P.exists_iso_detachedScheme i hi).choose_spec

theorem preimage_detachedClosureCompl (P : ChartPushforward S S') (i : ℕ) (hi : i < S'.length) :
    (P.strictTransformIso i hi.le).hom ⁻¹ᵁ (S'.detachedClosureCompl i) = S.detachedClosureCompl i := by
  have h : ⇑((P.strictTransformIso i hi.le).hom) ⁻¹' (↑(S'.detachedClosure i) : Set ↥(S'.strictTransform i)) =
      (↑(S.detachedClosure i) : Set ↥(S.strictTransform i)) := P.preimage_coe_detachedClosure i hi
  have h2 : ⇑((P.strictTransformIso i hi.le).hom) ⁻¹'
      ((↑(S'.detachedClosure i) : Set ↥(S'.strictTransform i))ᶜ) =
      ((↑(S.detachedClosure i) : Set ↥(S.strictTransform i))ᶜ) := by
    rw [Set.preimage_compl, h]
  exact TopologicalSpace.Opens.ext h2

theorem comap_comapAmbientCenter (P : ChartPushforward S S') (i : ℕ) (hi : i < S'.length) :
    (S'.comapAmbientCenter i).comap (P.strictTransformIso i hi.le).hom = S.comapAmbientCenter i := by
  have hmap : S'.ambientCenter i = (S.ambientCenter i).map (P.levelMap i hi.le) := by
    rw [P.ambientCenter_eq i hi, map_eq_imageIdealSheaf]
  simp only [EmbeddedBlowupSequence.comapAmbientCenter_eq]
  rw [← Scheme.IdealSheafData.comap_comp, P.strictTransformIso_hom_comp_strictTransformι i hi.le,
    Scheme.IdealSheafData.comap_comp, hmap, Blowup.comap_map_of_isClosedImmersion]

private theorem exists_isIso_of_preimage_opens_eq {X Z : Scheme.{u}} (e : X ≅ Z) (U : X.Opens)
    (U' : Z.Opens) (hU : e.hom ⁻¹ᵁ U' = U) :
    ∃ ψ : U.toScheme ⟶ U'.toScheme, IsIso ψ ∧ ψ ≫ U'.ι = U.ι ≫ e.hom := by
  have hfwd : ∀ y : ↥X, y ∈ (U : Set ↥X) → ⇑e.hom.base y ∈ (U' : Set ↥Z) := by
    intro y hy
    have h : y ∈ (↑(e.hom ⁻¹ᵁ U') : Set ↥X) := by rw [hU]; exact hy
    exact h
  have hbwd : ∀ y : ↥X, ⇑e.hom.base y ∈ (U' : Set ↥Z) → y ∈ (U : Set ↥X) := by
    intro y hy
    have h : y ∈ (↑(e.hom ⁻¹ᵁ U') : Set ↥X) := hy
    rwa [hU] at h
  have h1 : Set.range ⇑(U.ι ≫ e.hom).base ⊆ Set.range ⇑U'.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    show ⇑e.hom.base (⇑U.ι.base x) ∈ (U' : Set ↥Z)
    exact hfwd _ x.2
  have h2 : Set.range ⇑(U'.ι ≫ e.inv).base ⊆ Set.range ⇑U.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    show ⇑e.inv.base (⇑U'.ι.base y) ∈ (U : Set ↥X)
    refine hbwd _ ?_
    have hy : ⇑e.hom.base (⇑e.inv.base (⇑U'.ι.base y)) = ⇑U'.ι.base y :=
      Scheme.inv_hom_apply e (⇑U'.ι.base y)
    rw [hy]
    exact y.2
  refine ⟨IsOpenImmersion.lift U'.ι (U.ι ≫ e.hom) h1, ?_, ?_⟩
  · refine ⟨⟨IsOpenImmersion.lift U.ι (U'.ι ≫ e.inv) h2, ?_, ?_⟩⟩
    · rw [← cancel_mono U.ι, Category.assoc, IsOpenImmersion.lift_fac, ← Category.assoc,
        IsOpenImmersion.lift_fac, Category.assoc, e.hom_inv_id, Category.comp_id,
        Category.id_comp]
    · rw [← cancel_mono U'.ι, Category.assoc, IsOpenImmersion.lift_fac, ← Category.assoc,
        IsOpenImmersion.lift_fac, Category.assoc, e.inv_hom_id, Category.comp_id,
        Category.id_comp]
  · rw [IsOpenImmersion.lift_fac]

theorem comap_centerOffDetached (P : ChartPushforward S S') (i : ℕ) (hi : i < S'.length) :
    (S'.centerOffDetached i).comap (P.strictTransformIso i hi.le).hom = S.centerOffDetached i := by
  have hns' : TopologicalSpace.NoetherianSpace ↥(S'.strictTransform i) :=
    S'.noetherianSpace_strictTransform i hi.le
  have hnU : TopologicalSpace.NoetherianSpace ↥((S'.detachedClosureCompl i).toScheme) :=
    Blowup.noetherianSpace_toScheme (S'.strictTransform i) (S'.detachedClosureCompl i)
  have hqc : AlgebraicGeometry.QuasiCompact (S'.detachedClosureCompl i).ι :=
    ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hfl : AlgebraicGeometry.Flat (P.strictTransformIso i hi.le).hom := inferInstance
  obtain ⟨ψ, hψ, hψc⟩ := exists_isIso_of_preimage_opens_eq (P.strictTransformIso i hi.le) (S.detachedClosureCompl i)
    (S'.detachedClosureCompl i) (P.preimage_detachedClosureCompl i hi)
  have := hψ
  have H : IsPullback ψ (S.detachedClosureCompl i).ι (S'.detachedClosureCompl i).ι (P.strictTransformIso i hi.le).hom :=
    IsPullback.of_horiz_isIso ⟨hψc⟩
  have key := comap_map_eq_map_comap_of_isPullback H
    ((S'.comapAmbientCenter i).comap (S'.detachedClosureCompl i).ι)
  have hW : ((S'.comapAmbientCenter i).comap (S'.detachedClosureCompl i).ι).comap ψ
      = (S.comapAmbientCenter i).comap (S.detachedClosureCompl i).ι := by
    rw [← Scheme.IdealSheafData.comap_comp, hψc, Scheme.IdealSheafData.comap_comp,
      P.comap_comapAmbientCenter i hi]
  rw [hW] at key
  have hS' : S'.centerOffDetached i
      = ((S'.comapAmbientCenter i).comap (S'.detachedClosureCompl i).ι).map (S'.detachedClosureCompl i).ι :=
    (S'.centerOffDetached_eq i).trans (map_eq_ker_subschemeι_comp _ _).symm
  have hS : S.centerOffDetached i
      = ((S.comapAmbientCenter i).comap (S.detachedClosureCompl i).ι).map (S.detachedClosureCompl i).ι :=
    (S.centerOffDetached_eq i).trans (map_eq_ker_subschemeι_comp _ _).symm
  rw [hS', hS]
  exact key

end ChartPushforward

end FunctorialResolution.EmbeddedResolution

end
end

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace ChartPushforward

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
  {S S' : EmbeddedBlowupSequence k Y pY}

theorem le_length_of_le_length (P : ChartPushforward S S') {i : ℕ} (hi : i ≤ S.length) : i ≤ S'.length := by
  rw [← P.len_eq]
  exact hi

theorem lt_length_of_lt_length (P : ChartPushforward S S') {i : ℕ} (hi : i < S.length) : i < S'.length := by
  rw [← P.len_eq]
  exact hi

private def detachedCoprodIsoOfLE (P : ChartPushforward S S') [AlgebraicGeometry.IsReduced Y] :
    ∀ i : ℕ, i ≤ S'.length → (S.detachedCoprod i ≅ S'.detachedCoprod i) := fun i =>
  Nat.rec (motive := fun n => n ≤ S'.length → (S.detachedCoprod n ≅ S'.detachedCoprod n))
    (fun _ => eqToIso (S.detachedCoprod_zero.trans S'.detachedCoprod_zero.symm))
    (fun n ih hn => coprod.mapIso (ih (Nat.le_of_succ_le hn))
      (P.detachedSchemeIso n (lt_of_lt_of_le (Nat.lt_succ_self n) hn))) i

theorem exists_iso_detachedCoprod_compatible (P : ChartPushforward S S')
    [AlgebraicGeometry.IsReduced Y] :
    ∃ e : ∀ i : ℕ, i ≤ S'.length → (S.detachedCoprod i ≅ S'.detachedCoprod i),
      (∀ h : (0 : ℕ) ≤ S'.length,
          (e 0 h).hom = eqToHom (S.detachedCoprod_zero.trans S'.detachedCoprod_zero.symm)) ∧
      (∀ (i : ℕ) (hi : i < S'.length),
          S.detachedCoprodInl i ≫ (e (i + 1) hi).hom = (e i hi.le).hom ≫ S'.detachedCoprodInl i) ∧
      (∀ (i : ℕ) (hi : i < S'.length),
          S.detachedCoprodInr i ≫ (e (i + 1) hi).hom =
            (P.detachedSchemeIso i hi).hom ≫ S'.detachedCoprodInr i) := by
  refine ⟨detachedCoprodIsoOfLE P, fun _ => rfl, ?_, ?_⟩
  · intro i hi
    show (coprod.inl : S.detachedCoprod i ⟶ S.detachedCoprod i ⨿ S.detachedScheme i) ≫
        coprod.map (detachedCoprodIsoOfLE P i hi.le).hom (P.detachedSchemeIso i hi).hom =
      (detachedCoprodIsoOfLE P i hi.le).hom ≫
        (coprod.inl : S'.detachedCoprod i ⟶ S'.detachedCoprod i ⨿ S'.detachedScheme i)
    simp
  · intro i hi
    show (coprod.inr : S.detachedScheme i ⟶ S.detachedCoprod i ⨿ S.detachedScheme i) ≫
        coprod.map (detachedCoprodIsoOfLE P i hi.le).hom (P.detachedSchemeIso i hi).hom =
      (P.detachedSchemeIso i hi).hom ≫
        (coprod.inr : S'.detachedScheme i ⟶ S'.detachedCoprod i ⨿ S'.detachedScheme i)
    simp

def inactiveTotalIso (P : ChartPushforward S S') [AlgebraicGeometry.IsReduced Y] (i : ℕ)
    (hi : i ≤ S'.length) : S.detachedCoprod i ≅ S'.detachedCoprod i :=
  P.exists_iso_detachedCoprod_compatible.choose i hi

@[reassoc]
theorem detachedCoprodInl_inactiveTotalIso_hom (P : ChartPushforward S S')
    [AlgebraicGeometry.IsReduced Y] (i : ℕ) (hi : i < S'.length) :
    S.detachedCoprodInl i ≫ (P.inactiveTotalIso (i + 1) hi).hom =
      (P.inactiveTotalIso i hi.le).hom ≫ S'.detachedCoprodInl i :=
  P.exists_iso_detachedCoprod_compatible.choose_spec.2.1 i hi

@[reassoc]
theorem detachedCoprodInr_inactiveTotalIso_hom (P : ChartPushforward S S')
    [AlgebraicGeometry.IsReduced Y] (i : ℕ) (hi : i < S'.length) :
    S.detachedCoprodInr i ≫ (P.inactiveTotalIso (i + 1) hi).hom =
      (P.detachedSchemeIso i hi).hom ≫ S'.detachedCoprodInr i :=
  P.exists_iso_detachedCoprod_compatible.choose_spec.2.2 i hi

def totalSpaceIso (P : ChartPushforward S S') [AlgebraicGeometry.IsReduced Y] (i : ℕ)
    (hi : i ≤ S'.length) : S.totalSpace i ≅ S'.totalSpace i :=
  coprod.mapIso (P.strictTransformIso i hi) (P.inactiveTotalIso i hi)

theorem totalSpaceIso_hom_eq_coprodMap (P : ChartPushforward S S') [AlgebraicGeometry.IsReduced Y] (i : ℕ)
    (hi : i ≤ S'.length) :
    (P.totalSpaceIso i hi).hom =
      coprod.map (P.strictTransformIso i hi).hom (P.inactiveTotalIso i hi).hom := rfl

@[reassoc]
theorem inl_totalSpaceIso_hom (P : ChartPushforward S S') [AlgebraicGeometry.IsReduced Y] (i : ℕ)
    (hi : i ≤ S'.length) :
    (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) ≫ (P.totalSpaceIso i hi).hom =
      (P.strictTransformIso i hi).hom ≫ (coprod.inl : S'.strictTransform i ⟶ S'.totalSpace i) := by
  rw [P.totalSpaceIso_hom_eq_coprodMap i hi]
  simp

@[reassoc]
theorem inr_totalSpaceIso_hom (P : ChartPushforward S S') [AlgebraicGeometry.IsReduced Y] (i : ℕ)
    (hi : i ≤ S'.length) :
    (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) ≫ (P.totalSpaceIso i hi).hom =
      (P.inactiveTotalIso i hi).hom ≫ (coprod.inr : S'.detachedCoprod i ⟶ S'.totalSpace i) := by
  rw [P.totalSpaceIso_hom_eq_coprodMap i hi]
  simp

private theorem comap_hom_comap_inv {A B : Scheme.{u}} (e : A ≅ B) (I : B.IdealSheafData) :
    (I.comap e.hom).comap e.inv = I := by
  rw [← Scheme.IdealSheafData.comap_comp, e.inv_hom_id, Scheme.IdealSheafData.comap_id]

private theorem comap_inv_comap_hom {A B : Scheme.{u}} (e : A ≅ B) (I : A.IdealSheafData) :
    (I.comap e.inv).comap e.hom = I := by
  rw [← Scheme.IdealSheafData.comap_comp, e.hom_inv_id, Scheme.IdealSheafData.comap_id]

private theorem comap_map_of_comm_iso {A B A' B' : Scheme.{u}} (eA : A ≅ A') (eB : B ≅ B')
    (u : A ⟶ B) (u' : A' ⟶ B') (hcomm : u ≫ eB.hom = eA.hom ≫ u')
    (J : A'.IdealSheafData) :
    (J.map u').comap eB.hom = (J.comap eA.hom).map u := by
  have hcomm' : u' ≫ eB.inv = eA.inv ≫ u := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hcomm, Category.assoc, eB.hom_inv_id,
      Category.comp_id]
  refine le_antisymm ?_ ?_
  · rw [Scheme.IdealSheafData.le_map_iff_comap_le, ← Scheme.IdealSheafData.comap_comp, hcomm,
      Scheme.IdealSheafData.comap_comp]
    exact Scheme.IdealSheafData.comap_mono _
      (Scheme.IdealSheafData.le_map_iff_comap_le.mp le_rfl)
  · have key : ((J.comap eA.hom).map u).comap eB.inv ≤ J.map u' := by
      rw [Scheme.IdealSheafData.le_map_iff_comap_le, ← Scheme.IdealSheafData.comap_comp, hcomm',
        Scheme.IdealSheafData.comap_comp]
      have h2 : (((J.comap eA.hom).map u).comap u).comap eA.inv ≤
          (J.comap eA.hom).comap eA.inv :=
        Scheme.IdealSheafData.comap_mono eA.inv
          (Scheme.IdealSheafData.le_map_iff_comap_le.mp
            (le_rfl : (J.comap eA.hom).map u ≤ (J.comap eA.hom).map u))
      rw [comap_hom_comap_inv eA J] at h2
      exact h2
    have h3 : (((J.comap eA.hom).map u).comap eB.inv).comap eB.hom ≤
        (J.map u').comap eB.hom :=
      Scheme.IdealSheafData.comap_mono eB.hom key
    rwa [comap_inv_comap_hom eB] at h3

theorem comap_totalCenter (P : ChartPushforward S S') [AlgebraicGeometry.IsReduced Y] (i : ℕ)
    (hi : i < S'.length) :
    (S'.totalCenter i).comap (P.totalSpaceIso i hi.le).hom = S.totalCenter i := by
  have h := comap_map_of_comm_iso (P.strictTransformIso i hi.le) (P.totalSpaceIso i hi.le)
      (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)
      (coprod.inl : S'.strictTransform i ⟶ S'.totalSpace i)
      (P.inl_totalSpaceIso_hom i hi.le) (S'.centerOffDetached i)
  rw [P.comap_centerOffDetached i hi] at h
  exact h

private theorem totalSpaceIso_hom_totalTransition (P : ChartPushforward S S')
    [AlgebraicGeometry.IsReduced Y] (i : ℕ) (hi : i < S'.length) :
    (P.totalSpaceIso (i + 1) hi).hom ≫ S'.totalTransition i
      = S.totalTransition i ≫ (P.totalSpaceIso i hi.le).hom := by
  refine coprod.hom_ext ?_ ?_
  · rw [P.inl_totalSpaceIso_hom_assoc (i + 1) hi, S'.inl_totalTransition_eq_strictTransformMap_inl i, S.inl_totalTransition_assoc i,
      P.inl_totalSpaceIso_hom i hi.le]
    exact P.strictTransformIso_hom_comp_strictTransformMap_assoc i hi _
  · refine S.detachedCoprod_succ_hom_ext i ?_ ?_
    · rw [P.inr_totalSpaceIso_hom_assoc (i + 1) hi, P.detachedCoprodInl_inactiveTotalIso_hom_assoc i hi,
        S'.detachedCoprodInl_inr_totalTransition i, S.detachedCoprodInl_inr_totalTransition_assoc i,
        P.inr_totalSpaceIso_hom i hi.le]
    · rw [P.inr_totalSpaceIso_hom_assoc (i + 1) hi, P.detachedCoprodInr_inactiveTotalIso_hom_assoc i hi,
        S'.detachedCoprodInr_inr_totalTransition i, S.detachedCoprodInr_inr_totalTransition_assoc i,
        P.inl_totalSpaceIso_hom i hi.le]
      exact P.detachedSchemeIso_hom_comp_detachedι_assoc i hi _

theorem inducedBlowups_isomorphic (P : ChartPushforward S S') [AlgebraicGeometry.IsReduced Y]
    (h : S.TransitionsAreBlowups) (h' : S'.TransitionsAreBlowups) :
    (S.inducedBlowups h).Isomorphic (S'.inducedBlowups h') := by
  refine ⟨P.len_eq, fun i hi => P.totalSpaceIso i (P.le_length_of_le_length hi), ?_, ?_, ?_⟩
  · show (P.totalSpaceIso 0 (Nat.zero_le _)).hom ≫ S'.totalSpaceZeroIso.hom = S.totalSpaceZeroIso.hom
    refine coprod.hom_ext ?_ ?_
    · rw [P.inl_totalSpaceIso_hom_assoc 0 (Nat.zero_le _), S'.inl_totalSpaceZeroIso_hom,
        S.inl_totalSpaceZeroIso_hom]
      exact P.strictTransformIso_zero_hom_comp_strictTransformZeroIso_hom
    · have hB : IsInitial (S.detachedCoprod 0) := initialIsInitial
      exact hB.hom_ext _ _
  · intro i hi
    rw [inducedBlowups_blowupMorphism S' h' i, inducedBlowups_blowupMorphism S h i]
    exact P.totalSpaceIso_hom_totalTransition i (P.lt_length_of_lt_length hi)
  · intro i hi
    exact P.comap_totalCenter i (P.lt_length_of_lt_length hi)

theorem inducedBlowupsWithoutIso_isomorphic (P : ChartPushforward S S') [AlgebraicGeometry.IsReduced Y]
    (h : S.TransitionsAreBlowups) (h' : S'.TransitionsAreBlowups) :
    (S.inducedBlowupsWithoutIso h).Isomorphic (S'.inducedBlowupsWithoutIso h') := by
  let B := S.inducedBlowups h
  let B' := S'.inducedBlowups h'
  have he : B.Isomorphic B' := P.inducedBlowups_isomorphic h h'
  obtain ⟨hlen, e, hzero, hstep, hcen⟩ := he
  have htop : ∀ i : ℕ, i < B'.length → (B.center i = ⊤ ↔ B'.center i = ⊤) := by
    intro i hi
    have hi' : i < B.length := by rwa [hlen]
    constructor
    · intro ht
      have hc := (hcen i hi').trans ht
      have hc' := congrArg (fun I => I.comap (e i hi'.le).inv) hc
      simpa only [comap_hom_comap_inv, Scheme.IdealSheafData.comap_top] using hc'
    · intro ht
      rw [← hcen i hi', ht, Scheme.IdealSheafData.comap_top]
  have hindex := SequenceOfBlowups.nontrivialIndex_congr B B' hlen htop
  have hlength := SequenceOfBlowups.lengthWithoutIsoBlowups_congr B B' hlen htop
  let retainedHom (i : ℕ) (hi : i ≤ B.lengthWithoutIsoBlowups) :
      B.schemeAt (B.nontrivialIndex i) ⟶ B'.schemeAt (B'.nontrivialIndex i) :=
    (e (B.nontrivialIndex i) (B.nontrivialIndex_le_length hi)).hom ≫
      eqToHom (congrArg B'.schemeAt (hindex i))
  let retainedIso (i : ℕ) (hi : i ≤ B.withoutIsoBlowups.length) :
      B.withoutIsoBlowups.schemeAt i ≅ B'.withoutIsoBlowups.schemeAt i := by
    have hi' : i ≤ B.lengthWithoutIsoBlowups := B.withoutIsoBlowups_length ▸ hi
    change B.schemeAt (B.nontrivialIndex i) ≅ B'.schemeAt (B'.nontrivialIndex i)
    exact (e (B.nontrivialIndex i) (B.nontrivialIndex_le_length hi')).trans
      (eqToIso (congrArg B'.schemeAt (hindex i)))
  change B.withoutIsoBlowups.Isomorphic B'.withoutIsoBlowups
  refine ⟨hlength, retainedIso, ?_, ?_, ?_⟩
  · have projection_eq {a b : ℕ} (hab : a = b) :
        eqToHom (congrArg B'.schemeAt hab) ≫ B'.projectionToBase b = B'.projectionToBase a := by
      subst b
      simp
    rw [B.withoutIsoBlowups_isoObjZero, B'.withoutIsoBlowups_isoObjZero,
      B.objNontrivialIndexZeroIso_hom, B'.objNontrivialIndexZeroIso_hom]
    have hi := B.nontrivialIndex_le_length (Nat.zero_le B.lengthWithoutIsoBlowups)
    let e0 := (e (B.nontrivialIndex 0) hi).hom
    change (e0 ≫ eqToHom (congrArg B'.schemeAt (hindex 0))) ≫
      B'.projectionToBase (B'.nontrivialIndex 0) = B.projectionToBase (B.nontrivialIndex 0)
    rw [Category.assoc, projection_eq (hindex 0)]
    exact SequenceOfBlowups.iso_hom_comp_projectionToBase B B' B.length e hstep hzero
      (B.nontrivialIndex 0) hi
  · intro i hi
    have transition_eq {a b a' b' : ℕ} (ha : a = a') (hb : b = b') (hab : a ≤ b)
        (hab' : a' ≤ b') :
        eqToHom (congrArg B'.schemeAt hb) ≫ B'.transitionMap hab' =
          B'.transitionMap hab ≫ eqToHom (congrArg B'.schemeAt ha) := by
      subst a'
      subst b'
      simp
    rw [B.withoutIsoBlowups_blowupMorphism, B'.withoutIsoBlowups_blowupMorphism]
    have hi' : i < B.lengthWithoutIsoBlowups := B.withoutIsoBlowups_length ▸ hi
    have hle := B.nontrivialIndex_monotone (Nat.le_succ i)
    have hle' := B'.nontrivialIndex_monotone (Nat.le_succ i)
    change retainedHom (i + 1) hi' ≫ B'.transitionMap hle' =
      B.transitionMap hle ≫ retainedHom i hi'.le
    have hcomm := SequenceOfBlowups.iso_hom_comp_transitionMap B B' B.length e hstep
      (B.nontrivialIndex i) (B.nontrivialIndex (i + 1)) hle (B.nontrivialIndex_le_length hi')
    dsimp only [retainedHom]
    rw [Category.assoc, transition_eq (hindex i) (hindex (i + 1)) hle hle', ← Category.assoc,
      hcomm, Category.assoc]
  · intro i hi
    have center_eq {a b : ℕ} (hab : a = b) :
        (B'.center b).comap (eqToHom (congrArg B'.schemeAt hab)) = B'.center a := by
      subst b
      simp
    have hi' : i < B.lengthWithoutIsoBlowups := B.withoutIsoBlowups_length ▸ hi
    change (B'.center (B'.nontrivialIndex i)).comap (retainedHom i hi'.le) =
      B.center (B.nontrivialIndex i)
    dsimp only [retainedHom]
    rw [Scheme.IdealSheafData.comap_comp, center_eq (hindex i)]
    exact hcen _ (B.nontrivialIndex_lt_length hi)

end ChartPushforward

end FunctorialResolution.EmbeddedResolution

end
end

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace EmbeddingDatum

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
  {p : Y ⟶ Spec (CommRingCat.of k)}

theorem emb_comp_comp_eq_of_comp_eq (G : EmbeddingDatum k Y p) {A' : Scheme.{u}}
    (q : A' ⟶ Spec (CommRingCat.of k)) (τ : G.ambient ⟶ A')
    (hτ : τ ≫ q = G.ambientStruct) :
    (G.emb ≫ τ) ≫ q = p := by
  rw [Category.assoc, hτ, G.comp_eq]

def enlargeAmbient (G : EmbeddingDatum k Y p) (A' : Scheme.{u}) [AlgebraicGeometry.IsAffine A']
    (q : A' ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth q]
    [AlgebraicGeometry.LocallyOfFiniteType q] [AlgebraicGeometry.QuasiCompact q]
    (τ : G.ambient ⟶ A') [AlgebraicGeometry.IsClosedImmersion τ]
    (hτ : τ ≫ q = G.ambientStruct)
    (hker : NonzeroOnComponents (G.emb ≫ τ).ker)
    (hsnc : InStrictNormalCrossingPosition q ([] : List A'.IdealSheafData)) :
    EmbeddingDatum k Y p :=
  embeddingDatumOfClosedImmersion A' q (G.emb ≫ τ) hker (emb_comp_comp_eq_of_comp_eq G q τ hτ) hsnc

private theorem imageIdealSheaf_ker_eq_ker_comp {Yc A A' : Scheme.{u}} (e : Yc ⟶ A)
    [AlgebraicGeometry.IsClosedImmersion e] (σ : A ⟶ A') :
    imageIdealSheaf σ (Scheme.Hom.ker e) = Scheme.Hom.ker (e ≫ σ) :=
  (Scheme.Hom.ker_comp e σ).symm

theorem isPushforwardBlowupSeq_ambientBlowups_enlargeAmbient [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.LocallyOfFiniteType p]
    (G : EmbeddingDatum k Y p) (Alg : PrincipalizationAlgorithm.{u}) (hAlg : IsFunctorialPrincipalization Alg)
    (A' : Scheme.{u}) [AlgebraicGeometry.IsAffine A']
    (q : A' ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth q]
    [AlgebraicGeometry.LocallyOfFiniteType q] [AlgebraicGeometry.QuasiCompact q]
    (τ : G.ambient ⟶ A') [AlgebraicGeometry.IsClosedImmersion τ]
    (hτ : τ ≫ q = G.ambientStruct)
    (hker : NonzeroOnComponents (G.emb ≫ τ).ker)
    (hsnc : InStrictNormalCrossingPosition q ([] : List A'.IdealSheafData))
    (c : ℕ) (hc : 1 ≤ c) (hcodim : HasEtaleCoordCodim q τ c) :
    IsPushforwardBlowupSeq τ (G.toEmbeddedBlowupSequence Alg).ambientSeq
      ((G.enlargeAmbient A' q τ hτ hker hsnc).toEmbeddedBlowupSequence Alg).ambientSeq := by
  have himg : imageIdealSheaf τ (Scheme.Hom.ker G.emb) = Scheme.Hom.ker (G.emb ≫ τ) :=
    imageIdealSheaf_ker_eq_ker_comp G.emb τ
  have hJ : NonzeroOnComponents (imageIdealSheaf τ (Scheme.Hom.ker G.emb)) := by
    rw [himg]; exact hker
  have key : ∀ (J : A'.IdealSheafData) (hJ' : NonzeroOnComponents J),
      J = Scheme.Hom.ker (G.emb ≫ τ) →
      IsPushforwardBlowupSeq τ (G.toEmbeddedBlowupSequence Alg).ambientSeq
        (Alg k A' q J hJ' ([] : List A'.IdealSheafData) hsnc).toSequenceOfBlowups →
      IsPushforwardBlowupSeq τ (G.toEmbeddedBlowupSequence Alg).ambientSeq
        ((G.enlargeAmbient A' q τ hτ hker hsnc).toEmbeddedBlowupSequence Alg).ambientSeq := by
    rintro J hJ' rfl h
    exact h
  exact key _ hJ himg
    (hAlg.pushforward k G.ambient A' G.ambientStruct q τ hτ c hc hcodim
      (Scheme.Hom.ker G.emb) G.nonzeroOnComponents_ker hJ G.sncEmpty hsnc)

theorem isomorphic_embeddedResolutionRule_enlargeAmbient [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p]
    (G : EmbeddingDatum k Y p) (Alg : PrincipalizationAlgorithm.{u}) (hAlg : IsFunctorialPrincipalization Alg)
    (hw : TransitionsAreBlowupsForEmbeddings Alg)
    (A' : Scheme.{u}) [AlgebraicGeometry.IsAffine A']
    (q : A' ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth q]
    [AlgebraicGeometry.LocallyOfFiniteType q] [AlgebraicGeometry.QuasiCompact q]
    (τ : G.ambient ⟶ A') [AlgebraicGeometry.IsClosedImmersion τ]
    (hτ : τ ≫ q = G.ambientStruct)
    (hker : NonzeroOnComponents (G.emb ≫ τ).ker)
    (hsnc : InStrictNormalCrossingPosition q ([] : List A'.IdealSheafData))
    (c : ℕ) (hc : 1 ≤ c) (hcodim : HasEtaleCoordCodim q τ c) :
    (embeddedResolutionRuleOfPrincipalization Alg hw k Y p G).Isomorphic
      (embeddedResolutionRuleOfPrincipalization Alg hw k Y p (G.enlargeAmbient A' q τ hτ hker hsnc)) := by
  have P : ChartPushforward (G.toEmbeddedBlowupSequence Alg)
      ((G.enlargeAmbient A' q τ hτ hker hsnc).toEmbeddedBlowupSequence Alg) :=
    @ChartPushforward.ofIsPushforwardSeq k _ _ Y _ p _ (G.toEmbeddedBlowupSequence Alg)
      ((G.enlargeAmbient A' q τ hτ hker hsnc).toEmbeddedBlowupSequence Alg) τ
      (inferInstanceAs (AlgebraicGeometry.IsClosedImmersion τ)) rfl
      (isPushforwardBlowupSeq_ambientBlowups_enlargeAmbient G Alg hAlg A' q τ hτ hker hsnc c hc hcodim)
  exact P.inducedBlowupsWithoutIso_isomorphic (hw k Y p G) (hw k Y p (G.enlargeAmbient A' q τ hτ hker hsnc))

end EmbeddingDatum

end FunctorialResolution.EmbeddedResolution

end
