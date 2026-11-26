module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGenerated
public import Development.AutomorphicArithmetic.CommutativeAlgebra.CohomologyPuncturedAffineLine
public import Development.AutomorphicArithmetic.CommutativeAlgebra.SupportDoubleComplexTotalRepresentsVanishingCoch
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleFinitePresentationModelExists
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CofilteredSchemeLimitExistsLocally
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FiniteOverHenselianFibreIdempotentsLift
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TateTwistFinitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceChainsMayerVietorisShortExact
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AugmentationMapBijective
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SepClosedPointFilteredEtaleColimit
public import Development.EtaleCohomology.EtaleSheaves.IterCompPf
public import Development.EtaleCohomology.EtaleSheaves.BaseIntPf
public import Development.EtaleCohomology.EtaleSheaves.LeafRelDimOnePf
public import Development.EtaleCohomology.EtaleSheaves.AffinePf
public import Development.EtaleCohomology.EtaleSheaves.LeafObjAffPf
public import Development.EtaleCohomology.EtaleSheaves.PointwisePf
public import Development.EtaleCohomology.EtaleSheaves.ChasePf
public import Development.EtaleCohomology.EtaleSheaves.ColimHensPf
public import Development.EtaleCohomology.EtaleSheaves.SecPrePf
public import Development.EtaleCohomology.EtaleSheaves.EmbedNonDegOf
public import Development.EtaleCohomology.EtaleSheaves.LeafVanWPf
public import Development.EtaleCohomology.EtaleSheaves.TwGenNZACPf
public import Development.EtaleCohomology.EtaleSheaves.ImageInPf
public import Development.EtaleCohomology.EtaleSheaves.LocSHPf
public import Development.EtaleCohomology.EtaleSheaves.H0Lifting
public import Development.EtaleCohomology.EtaleSheaves.LZHensFinitePf
public import Development.EtaleCohomology.EtaleSheaves.LZIdemSumApproxYDDUPf
public import Development.EtaleCohomology.EtaleSheaves.IntegralNormalization.AicSubsingleton
public import Development.EtaleCohomology.EtaleSheaves.DescentPf
public import Development.EtaleCohomology.EtaleSheaves.LeafDescendMapPf
public import Development.EtaleCohomology.EtaleSheaves.ResBijPf
public import Development.EtaleCohomology.EtaleSheaves.ReducedOfSmooth

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.DiagNatPf
namespace LateralTheory.E.DiagNatPf
open LateralTheory.E.PartDiagCut

theorem DiagNat_of : LateralTheory.E.PartDiagCut.DiagNat := by
  intro B _ I P Q h
  apply RingHom.ext
  intro b
  funext e
  simp only [stageMap, βP, RingHom.comp_apply, RingHom.pi_apply, Pi.evalRingHom_apply]
  exact (IsLocalization.map_eq (S := Localization (S I (par h e).1)) _ b).trans (by rfl)

end LateralTheory.E.DiagNatPf
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.DiagramChase.StepSOfChase
namespace LateralTheory.E.StepSPf

theorem StepS_of_chase (hC : DiagramChase₂) : LateralTheory.E.ContStepPf.StepS := S_of_restr_chase restr hC

end LateralTheory.E.StepSPf
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ImgOf
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.ImgPf

theorem Img_of : LateralTheory.E.ChowCut.Img := by
  intro A _ Z X h p _ hh hZ
  have := hh
  have := hZ
  have : QuasiCompact h := inferInstance
  have : IsIntegralHom (h.toImage ≫ h.imageι) := by rw [Scheme.Hom.toImage_imageι]; exact hh
  refine ⟨h.image, h.toImage, h.imageι ≫ p, inferInstance, inferInstance,
    IsIntegralHom.of_comp h.toImage h.imageι, inferInstance, ?_⟩
  rw [Scheme.Hom.toImage_imageι_assoc]

end LateralTheory.E.ImgPf
end

section -- merged from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleMayerVietorisShortExact
theorem UpperTheory.Cb.etale_mayer_vietoris_short_exact :
    LateralTheory.E.MayerVietorisSequence.SES := by
  intro R _ U V E f g h
  exact GlobalTheory.T.etaleSpaceChains_mayerVietoris_shortExact R f g h
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.FibMapRange
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.FiberCover
open LateralTheory.E.LineOneCut

lemma fibMap_eq {A : Type} [CommRing A] [IsLocalRing A] {U Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι : U ⟶ Z) :
    fibMap p ι = (pullbackRightPullbackFstIso p (cpt A) ι).inv ≫ pullback.snd ι (pullback.fst p (cpt A)) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackRightPullbackFstIso_inv_snd_fst]; exact pullback.lift_fst _ _ _
  · rw [Category.assoc, pullbackRightPullbackFstIso_inv_snd_snd]
    simp [fibMap]

lemma fibMap_open {A : Type} [CommRing A] [IsLocalRing A] {U Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι : U ⟶ Z)
    [IsOpenImmersion ι] : IsOpenImmersion (fibMap p ι) := by
  rw [fibMap_eq]; infer_instance

lemma fibMap_range {A : Type} [CommRing A] [IsLocalRing A] {U Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι : U ⟶ Z) :
    Set.range (fibMap p ι) = (pullback.fst p (cpt A)) ⁻¹' Set.range ι := by
  rw [fibMap_eq, ← Scheme.Pullback.range_snd]
  ext x; constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, (Scheme.Hom.comp_apply _ _ y).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨(pullbackRightPullbackFstIso p (cpt A) ι).hom y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

theorem FibCover_of : FibCover := by
  intro A _ _ Z U V p ι₁ ι₂ h1 h2 hcov
  refine ⟨fibMap_open p ι₁, fibMap_open p ι₂, ?_⟩
  rw [fibMap_range, fibMap_range, ← Set.preimage_union, hcov, Set.preimage_univ]

end LateralTheory.E.FiberCover
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ContIndPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.ContIndPf

section lists
variable {X : Scheme.{0}}

def lsup (l : List X.Opens) : X.Opens := l.foldr (· ⊔ ·) ⊥

lemma lsup_cons (a : X.Opens) (l : List X.Opens) : lsup (a :: l) = a ⊔ lsup l := rfl
lemma lsup_nil : lsup ([] : List X.Opens) = ⊥ := rfl

lemma le_lsup {l : List X.Opens} {B : X.Opens} (h : B ∈ l) : B ≤ lsup l := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rw [lsup_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_sup_left
    · exact (ih h).trans le_sup_right

lemma lsup_le {l : List X.Opens} {W : X.Opens} (h : ∀ B ∈ l, B ≤ W) : lsup l ≤ W := by
  induction l with
  | nil => simp [lsup_nil]
  | cons a l ih =>
    rw [lsup_cons]
    exact sup_le (h a (by simp)) (ih fun B hB => h B (by simp [hB]))

lemma isCompact_lsup (l : List X.Opens) (h : ∀ B ∈ l, IsCompact (B : Set X)) : IsCompact (lsup l : Set X) := by
  induction l with
  | nil => simp [lsup_nil]
  | cons a l ih =>
    rw [lsup_cons, TopologicalSpace.Opens.coe_sup]
    exact (h a (by simp)).union (ih fun B hB => h B (by simp [hB]))

lemma preimage_lsup {Y : Scheme.{0}} (f : Y ⟶ X) (l : List X.Opens) :
    f ⁻¹ᵁ lsup l = lsup (l.map (f ⁻¹ᵁ ·)) := by
  induction l with
  | nil => simp [lsup_nil]
  | cons a l ih =>
    rw [lsup_cons, List.map_cons, lsup_cons, ← ih]
    rfl

lemma lsup_inf (l : List X.Opens) (A : X.Opens) : lsup l ⊓ A = lsup (l.map (· ⊓ A)) := by
  induction l with
  | nil => simp [lsup_nil]
  | cons a l ih => rw [List.map_cons, lsup_cons, lsup_cons, inf_sup_right, ih]

end lists

section opens
variable {X : Scheme.{0}}

lemma image_le_range {Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f] (A : Y.Opens) : f ''ᵁ A ≤ f.opensRange := by
  rw [← Scheme.Hom.image_top_eq_opensRange]
  exact (f.image_le_image_iff _ _).2 le_top

lemma image_inf {Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f] (A B : Y.Opens) :
    f ''ᵁ (A ⊓ B) = f ''ᵁ A ⊓ f ''ᵁ B := by
  apply le_antisymm
  · exact le_inf ((f.image_le_image_iff _ _).2 inf_le_left) ((f.image_le_image_iff _ _).2 inf_le_right)
  · have hC : f ''ᵁ A ⊓ f ''ᵁ B = f ''ᵁ (f ⁻¹ᵁ (f ''ᵁ A ⊓ f ''ᵁ B)) := by
      rw [f.image_preimage_eq_opensRange_inf, inf_eq_right.2 (inf_le_left.trans (image_le_range f A))]
    rw [hC, f.image_le_image_iff]
    have : f ⁻¹ᵁ (f ''ᵁ A ⊓ f ''ᵁ B) = f ⁻¹ᵁ (f ''ᵁ A) ⊓ f ⁻¹ᵁ (f ''ᵁ B) := rfl
    rw [this, f.preimage_image_eq, f.preimage_image_eq]

lemma image_le (W : X.Opens) (A : W.toScheme.Opens) : W.ι ''ᵁ A ≤ W :=
  (image_le_range W.ι A).trans (Scheme.Opens.opensRange_ι W).le

lemma affine_preimage (W : X.Opens) {B : X.Opens} (h : B ≤ W) (hB : IsAffineOpen B) :
    IsAffineOpen (W.ι ⁻¹ᵁ B) := by
  apply (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion W.ι).mp
  rwa [W.ι.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.2 h]

def Good (Y : Scheme.{0}) : Prop :=
  ∀ A B : Y.Opens, IsAffineOpen A → IsAffineOpen B → IsAffineOpen (A ⊓ B)

def Good2 (Y : Scheme.{0}) : Prop :=
  ∀ A B : Y.Opens, IsAffineOpen A → IsAffineOpen B → IsCompact ((A ⊓ B : Y.Opens) : Set Y)

lemma good_of (W : X.Opens)
    (h : ∀ C D : X.Opens, C ≤ W → D ≤ W → IsAffineOpen C → IsAffineOpen D → IsAffineOpen (C ⊓ D)) :
    Good W.toScheme := by
  intro A B hA hB
  apply (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion W.ι).mp
  rw [image_inf]
  exact h _ _ (image_le W A) (image_le W B) (hA.image_of_isOpenImmersion _) (hB.image_of_isOpenImmersion _)

lemma good_open (hX : Good X) (W : X.Opens) : Good W.toScheme :=
  good_of W (fun C D _ _ hC hD => hX C D hC hD)

lemma good_affine (A W : X.Opens) (hA : IsAffineOpen A) (hW : W ≤ A) : Good W.toScheme := by
  apply good_of W
  intro C D hC hD hC' hD'
  have : IsAffine A.toScheme := hA
  have h1 := (affine_preimage A (hC.trans hW) hC').inf (affine_preimage A (hD.trans hW) hD')
  have h2 := h1.image_of_isOpenImmersion A.ι
  rwa [image_inf, A.ι.image_preimage_eq_opensRange_inf, A.ι.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι, inf_eq_right.2 (hC.trans hW), inf_eq_right.2 (hD.trans hW)] at h2

lemma hasCompactAffineIntersections_open_subscheme (hX : Good2 X) (W : X.Opens) : Good2 W.toScheme := by
  intro A B hA hB
  have h := hX _ _ (hA.image_of_isOpenImmersion W.ι) (hB.image_of_isOpenImmersion W.ι)
  rw [← image_inf] at h
  rw [W.ι.isOpenEmbedding.isEmbedding.isCompact_iff]
  convert h using 1
  simp

lemma exists_cover (W : X.Opens) (hW : IsCompact (W : Set X)) :
    ∃ l : List X.Opens, (∀ B ∈ l, IsAffineOpen B ∧ B ≤ W) ∧ lsup l = W := by
  let ι := {B : X.Opens // IsAffineOpen B ∧ B ≤ W}
  obtain ⟨t, ht⟩ := hW.elim_finite_subcover (fun i : ι => ((i.1 : X.Opens) : Set X)) (fun i => i.1.isOpen)
    (by
      intro x hx
      have hb : ∀ {U : X.Opens} {x : X}, x ∈ U → ∃ U' ∈ X.affineOpens, x ∈ U' ∧ U' ≤ U :=
        TopologicalSpace.Opens.isBasis_iff_nbhd.1 (Scheme.isBasis_affineOpens X)
      obtain ⟨B, hB, hxB, hBW⟩ := hb (U := W) hx
      exact Set.mem_iUnion.2 ⟨⟨B, hB, hBW⟩, hxB⟩)
  refine ⟨t.toList.map Subtype.val, ?_, ?_⟩
  · intro B hB
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hB
    exact i.2
  · apply le_antisymm
    · apply lsup_le
      intro B hB
      obtain ⟨i, _, rfl⟩ := List.mem_map.1 hB
      exact i.2.2
    · intro x hx
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht hx)
      exact le_lsup (List.mem_map.2 ⟨i, Finset.mem_toList.2 hi, rfl⟩) hxi

end opens

section ind
variable (P : Scheme.{0} → Prop) (hA : ∀ (X : Scheme.{0}) [IsAffine X], P X)
  (hS : ∀ (X : Scheme.{0}) (U V : X.Opens), IsCompact (U : Set X) → IsCompact (V : Set X) → U ⊔ V = ⊤ →
    P U.toScheme → P V.toScheme → P (U ⊓ V).toScheme → P X)
include hA hS

omit hS in
lemma empty_case (Y : Scheme.{0}) (htop : lsup ([] : List Y.Opens) = ⊤) : P Y := by
  have : IsEmpty Y := by
    constructor
    intro x
    have hx : x ∈ (⊤ : Y.Opens) := trivial
    rw [← htop, lsup_nil] at hx
    exact hx
  exact hA Y

lemma stage1 (n : ℕ) : ∀ (Y : Scheme.{0}) (l : List Y.Opens), l.length = n → Good Y →
    (∀ B ∈ l, IsAffineOpen B) → lsup l = ⊤ → P Y := by
  induction n with
  | zero =>
    intro Y l hl _ _ htop
    rw [List.eq_nil_of_length_eq_zero hl] at htop
    exact empty_case P hA Y htop
  | succ n ih =>
    intro Y l hl hG hl' htop
    cases l with
    | nil => simp at hl
    | cons A l =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      have hAff : IsAffineOpen A := hl' A (by simp)
      have hlA : ∀ B ∈ l, IsAffineOpen B := fun B hB => hl' B (by simp [hB])
      have htop' : lsup l ⊔ A = ⊤ := by rw [sup_comm, ← lsup_cons]; exact htop
      apply hS Y (lsup l) A (isCompact_lsup l fun B hB => (hlA B hB).isCompact) hAff.isCompact htop'
      · apply ih (lsup l).toScheme (l.map ((lsup l).ι ⁻¹ᵁ ·)) (by simp [hl]) (good_open hG _)
        · intro B hB
          obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
          exact affine_preimage _ (le_lsup hC) (hlA C hC)
        · rw [← preimage_lsup, Scheme.Opens.ι_preimage_self]
      · have : IsAffine A.toScheme := hAff
        exact hA A.toScheme
      · apply ih (lsup l ⊓ A).toScheme ((l.map (· ⊓ A)).map ((lsup l ⊓ A).ι ⁻¹ᵁ ·)) (by simp [hl])
          (good_open hG _)
        · intro B hB
          obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
          obtain ⟨D, hD, rfl⟩ := List.mem_map.1 hC
          refine affine_preimage _ ?_ (hG D A (hlA D hD) hAff)
          rw [lsup_inf]
          exact le_lsup (List.mem_map.2 ⟨D, hD, rfl⟩)
        · rw [← preimage_lsup, ← lsup_inf, Scheme.Opens.ι_preimage_self]

lemma stage2 (n : ℕ) : ∀ (Y : Scheme.{0}) (l : List Y.Opens), l.length = n → Good2 Y →
    (∀ B ∈ l, IsAffineOpen B) → lsup l = ⊤ → P Y := by
  induction n with
  | zero =>
    intro Y l hl _ _ htop
    rw [List.eq_nil_of_length_eq_zero hl] at htop
    exact empty_case P hA Y htop
  | succ n ih =>
    intro Y l hl hG hl' htop
    cases l with
    | nil => simp at hl
    | cons A l =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      have hAff : IsAffineOpen A := hl' A (by simp)
      have hlA : ∀ B ∈ l, IsAffineOpen B := fun B hB => hl' B (by simp [hB])
      have htop' : lsup l ⊔ A = ⊤ := by rw [sup_comm, ← lsup_cons]; exact htop
      apply hS Y (lsup l) A (isCompact_lsup l fun B hB => (hlA B hB).isCompact) hAff.isCompact htop'
      · apply ih (lsup l).toScheme (l.map ((lsup l).ι ⁻¹ᵁ ·)) (by simp [hl]) (hasCompactAffineIntersections_open_subscheme hG _)
        · intro B hB
          obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
          exact affine_preimage _ (le_lsup hC) (hlA C hC)
        · rw [← preimage_lsup, Scheme.Opens.ι_preimage_self]
      · have : IsAffine A.toScheme := hAff
        exact hA A.toScheme
      · have hc : IsCompact ((lsup l ⊓ A : Y.Opens) : Set Y) := by
          rw [lsup_inf]
          apply isCompact_lsup
          intro B hB
          obtain ⟨D, hD, rfl⟩ := List.mem_map.1 hB
          exact hG D A (hlA D hD) hAff
        obtain ⟨l2, hl2, hs2⟩ := exists_cover _ hc
        apply stage1 P hA hS l2.length (lsup l ⊓ A).toScheme (l2.map ((lsup l ⊓ A).ι ⁻¹ᵁ ·)) (by simp)
          (good_affine A _ hAff inf_le_right)
        · intro B hB
          obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
          exact affine_preimage _ (hl2 C hC).2 (hl2 C hC).1
        · rw [← preimage_lsup, hs2, Scheme.Opens.ι_preimage_self]

end ind

theorem ContInd_of : LateralTheory.E.ContPf.ContInd := by
  intro P hA hS X _ _
  have hc : IsCompact ((⊤ : X.Opens) : Set X) := by simpa using isCompact_univ
  obtain ⟨l, hl, hs⟩ := exists_cover (⊤ : X.Opens) hc
  refine stage2 P hA hS l.length X l rfl ?_ (fun B hB => (hl B hB).1) hs
  intro A B hA' hB'
  rw [TopologicalSpace.Opens.coe_inf]
  exact QuasiSeparatedSpace.inter_isCompact _ _ A.isOpen hA'.isCompact B.isOpen hB'.isCompact

end LateralTheory.E.ContIndPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ContAffPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ContPf

namespace LateralTheory.E.ContAffPf

lemma isoSpec_inv_nat {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    Spec.map f.appTop ≫ Y.isoSpec.inv = X.isoSpec.inv ≫ f := by
  rw [Iso.comp_inv_eq, Category.assoc, ← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]

lemma pp {R : Type} [CommRing R] {A B C E : Spc} (a : A ⟶ B) (b : B ⟶ E) (c : A ⟶ C) (d : C ⟶ E) (h : a ≫ b = c ≫ d)
    (F : Shv R) (n : ℤ) (x : H R E F n) : pull R a F n (pull R b F n x) = pull R c F n (pull R d F n x) := by
  rw [← pull_comp, h, pull_comp]

theorem aff_case (hB1 : B1) (q : ℕ) {I : Type} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{0}) (c : Cone D)
    (hc : IsLimit c) (ha : ∀ {j k : I} (f : j ⟶ k), IsAffineHom (D.map f)) (hcs : ∀ j, CompactSpace (D.obj j))
    (hqs : ∀ j, QuasiSeparatedSpace (D.obj j)) (hu : ∀ j, IsUnit (q : Γ(D.obj j, ⊤)))
    (hA : ∀ j, IsAffine (D.obj j)) (hP : IsAffine c.pt) (n i : ℤ) :
    (∀ x : Ht q (sch.obj c.pt) n i, ∃ j y, pull _ (sch.map (c.π.app j)) _ _ y = x) ∧
    ∀ j (y : Ht q (sch.obj (D.obj j)) n i), pull _ (sch.map (c.π.app j)) _ _ y = 0 →
      ∃ (k : I) (f : k ⟶ j), pull _ (sch.map (D.map f)) _ _ y = 0 := by
  obtain ⟨hE⟩ := nonempty_isColimit_Γ_mapCocone D c hc
  have hP' : ∀ j, IsAffine (((Functor.const I).obj c.pt).obj j) := fun _ => hP
  have B := hB1 q (D.op ⋙ Scheme.Γ) (Scheme.Γ.mapCocone c.op) hE n i
  obtain ⟨j0⟩ := IsCofiltered.nonempty (C := I)
  have huP : IsUnit (q : Γ(c.pt, ⊤)) := by
    have := (hu j0).map (c.π.app j0).appTop.hom
    simpa using this
  constructor
  · intro x
    obtain ⟨j, y, hy⟩ := B.1 (pull _ (sch.map c.pt.isoSpec.inv) _ _ x) huP
    refine ⟨j.unop, pull _ (sch.map (D.obj j.unop).isoSpec.hom) _ _ y, ?_⟩
    have key := pp (R := ZMod q) (sch.map (c.π.app j.unop)) (sch.map (D.obj j.unop).isoSpec.hom)
      (sch.map c.pt.isoSpec.hom) (sch.map (Spec.map (c.π.app j.unop).appTop))
      (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]; exact congrArg sch.map (Scheme.isoSpec_hom_naturality _).symm) (tw q i) n y
    refine key.trans ?_
    have hy' : pull (ZMod q) (sch.map (Spec.map (c.π.app j.unop).appTop)) (tw q i) n y =
      pull (ZMod q) (sch.map c.pt.isoSpec.inv) (tw q i) n x := hy
    rw [hy', ← pull_comp, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id]
    erw [CategoryTheory.Functor.map_id, pull_id]
  · intro j y hy
    obtain ⟨k, f, hk⟩ := B.2 (Opposite.op j) (pull _ (sch.map (D.obj j).isoSpec.inv) _ _ y) (hu j) (by
      have key2 := pp (R := ZMod q) (sch.map (Spec.map (c.π.app j).appTop)) (sch.map (D.obj j).isoSpec.inv)
        (sch.map c.pt.isoSpec.inv) (sch.map (c.π.app j))
        (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]; exact congrArg sch.map (isoSpec_inv_nat _)) (tw q i) n y
      exact key2.trans (by rw [hy]; exact map_zero _))
    refine ⟨k.unop, f.unop, ?_⟩
    have e1 : y = pull _ (sch.map (D.obj j).isoSpec.hom) _ _ (pull _ (sch.map (D.obj j).isoSpec.inv) _ _ y) := by
      rw [← pull_comp, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
    rw [e1]
    have key3 := pp (R := ZMod q) (sch.map (D.map f.unop)) (sch.map (D.obj j).isoSpec.hom)
      (sch.map (D.obj k.unop).isoSpec.hom) (sch.map (Spec.map (D.map f.unop).appTop))
      (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]; exact congrArg sch.map (Scheme.isoSpec_hom_naturality _).symm) (tw q i) n
      (pull _ (sch.map (D.obj j).isoSpec.inv) _ _ y)
    refine key3.trans ?_
    have hk' : pull (ZMod q) (sch.map (Spec.map (D.map f.unop).appTop)) (tw q i) n
      (pull _ (sch.map (D.obj j).isoSpec.inv) _ _ y) = 0 := hk
    rw [hk', map_zero]

theorem ContAff_of : ContAff := by
  intro h X _ q J _ _ D c hc ha hcs hqs hu j0 ⟨e⟩ n i
  have : IsAffine (D.obj j0) := IsAffine.of_isIso e.hom
  have hc' : IsLimit (c.whisker (Over.forget j0)) := (Functor.Initial.isLimitWhiskerEquiv (Over.forget j0) c).symm hc
  have hA : ∀ k : Over j0, IsAffine ((Over.forget j0 ⋙ D).obj k) := fun k => by
    have i1 := ha k.hom
    have i2 : IsAffine (D.obj ((Functor.fromPUnit j0).obj k.right)) := ‹IsAffine (D.obj j0)›
    exact @isAffine_of_isAffineHom _ _ (D.map k.hom) (ha k.hom) i2
  have hP : IsAffine c.pt := by
    have : ∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f) := ha
    have := hcs; have := hqs
    have := isAffineHom_π_app D c hc j0
    exact isAffine_of_isAffineHom (c.π.app j0)
  have R := aff_case h.b1 q (Over.forget j0 ⋙ D) (c.whisker (Over.forget j0)) hc' (fun f => ha _)
    (fun k => hcs _) (fun k => hqs _) (fun k => hu _) hA hP n i
  refine ⟨fun x => ?_, fun j y hy => ?_⟩
  · obtain ⟨k, y, hy⟩ := R.1 x
    exact ⟨k.left, y, hy⟩
  · obtain ⟨k, g, h0, -⟩ := IsCofilteredOrEmpty.cone_objs j j0
    obtain ⟨l, f, hf⟩ := R.2 (Over.mk h0) (pull _ (sch.map (D.map g)) _ _ y) (by
      show pull _ (sch.map (c.π.app k)) _ _ _ = 0
      rw [← pull_comp, ← CategoryTheory.Functor.map_comp, c.w]
      exact hy)
    refine ⟨l.left, f.left ≫ g, ?_⟩
    rw [D.map_comp, CategoryTheory.Functor.map_comp, pull_comp]
    exact hf

end LateralTheory.E.ContAffPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.RelNormPf
section -- merged from Development.EtaleCohomology.EtaleSheaves.RelNormPfAff
section -- merged from Development.EtaleCohomology.EtaleSheaves.RelNormPfGlue
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.RelNormPf

def ClosedAt {X T : Scheme.{0}} (c : X ⟶ T) (W : T.Opens) : Prop :=
  ∀ b : Γ(X, c ⁻¹ᵁ W), (c.app W).hom.IsIntegralElem b → ∃ a, c.app W a = b

def NormClosed : Prop := ∀ {Z S : Scheme.{0}} (g : Z ⟶ S) [QuasiCompact g] [QuasiSeparated g], IsIntegral Z →
  ∀ V : g.normalization.Opens, IsAffineOpen V → ∀ b : Γ(Z, g.toNormalization ⁻¹ᵁ V),
    (g.toNormalization.app V).hom.IsIntegralElem b → ∃ a, g.toNormalization.app V a = b

theorem RelNorm_of_closed (hN : NormClosed) : LateralTheory.E.SteinPf.RelNorm := by
  intro Z S g _ _ hZ
  haveI : IsIntegral Z := hZ.1
  refine ⟨g.normalization, g.toNormalization, g.fromNormalization, inferInstance, inferInstance, inferInstance,
    g.toNormalization_fromNormalization, fun V hV hne => ⟨?_, ?_, hN g hZ.1 V hV⟩⟩
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨z, hz⟩ := g.toNormalization.denseRange.exists_mem_open V.isOpen ⟨x, hx⟩
    exact ⟨z, hz⟩
  · haveI : IsSchemeTheoreticallyDominant g.toNormalization := .of_isDominant _
    exact g.toNormalization.app_injective V

end LateralTheory.E.RelNormPf
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.RelNormPf

open AlgebraicGeometry.Scheme.Hom in
theorem closedAt_preimage {Z S : Scheme.{0}} (g : Z ⟶ S) [QuasiCompact g] [QuasiSeparated g]
    (U : S.Opens) (hU : IsAffineOpen U) : ClosedAt g.toNormalization (g.fromNormalization ⁻¹ᵁ U) := by
  intro b hb
  letI := (g.app U).hom.toAlgebra
  have hle : g ⁻¹ᵁ U ≤ g.toNormalization ⁻¹ᵁ g.fromNormalization ⁻¹ᵁ U := by
    simp [← Scheme.Hom.comp_preimage]
  have hle' : g.toNormalization ⁻¹ᵁ g.fromNormalization ⁻¹ᵁ U ≤ g ⁻¹ᵁ U := by
    simp [← Scheme.Hom.comp_preimage]
  set ρ := Z.presheaf.map (homOfLE hle).op with hρ
  have key := g.normalizationObjIso_hom_val hU
  have hρinj : Function.Injective ρ := by
    intro u v huv
    have := congrArg (Z.presheaf.map (homOfLE hle').op) huv
    have h1 : (homOfLE hle).op ≫ (homOfLE hle').op = 𝟙 (Opposite.op (g.toNormalization ⁻¹ᵁ g.fromNormalization ⁻¹ᵁ U)) :=
      Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    simpa [hρ, ← CommRingCat.comp_apply, ← Functor.map_comp, h1] using this

  have hint : IsIntegral (integralClosure Γ(S, U) Γ(Z, g ⁻¹ᵁ U)) (ρ b) := by
    obtain ⟨p, hm, hp⟩ := hb
    refine ⟨p.map (g.normalizationObjIso hU).hom.hom, hm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have e : (algebraMap (integralClosure Γ(S, U) Γ(Z, g ⁻¹ᵁ U)) Γ(Z, g ⁻¹ᵁ U)).comp
        (g.normalizationObjIso hU).hom.hom = ρ.hom.comp (g.toNormalization.app _).hom := by
      have := congrArg CommRingCat.Hom.hom key
      rw [Scheme.Hom.appLE] at this
      exact this
    rw [e, ← Polynomial.hom_eval₂, hp, map_zero]
  have hmem : ρ b ∈ (⊥ : Subalgebra (integralClosure Γ(S, U) Γ(Z, g ⁻¹ᵁ U)) Γ(Z, g ⁻¹ᵁ U)) := by
    rw [← integralClosure_idem]; exact hint
  obtain ⟨z, hz⟩ := Algebra.mem_bot.mp hmem
  refine ⟨(g.normalizationObjIso hU).inv z, hρinj ?_⟩
  have := congrArg (fun φ => φ ((g.normalizationObjIso hU).inv z)) (congrArg CommRingCat.Hom.hom key)
  simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply] at this
  rw [← this, ← hz]
  simp

end LateralTheory.E.RelNormPf
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.RelNormPf

theorem closedAt_comp {X N T : Scheme.{0}} (c' : X ⟶ N) (k' : N ⟶ T) (V : T.Opens)
    (h : ClosedAt c' (k' ⁻¹ᵁ V)) (hs : Function.Surjective (k'.app V)) : ClosedAt (c' ≫ k') V := by
  intro b hb
  obtain ⟨p, hm, hp⟩ := hb
  obtain ⟨a', ha'⟩ := h b ⟨p.map (k'.app V).hom, hm.map _, (Polynomial.eval₂_map (p := p) (k'.app V).hom (c'.app (k' ⁻¹ᵁ V)).hom b).trans hp⟩
  obtain ⟨a, rfl⟩ := hs a'
  exact ⟨a, ha'⟩

theorem normClosed : NormClosed := by
  intro Z S g _ _ _ V hV
  have H : g = g.toNormalization.toNormalization ≫
      (g.toNormalization.fromNormalization ≫ g.fromNormalization) := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization,
      Scheme.Hom.toNormalization_fromNormalization]
  let h := g.normalizationDesc _ _ H
  have e1 : g.toNormalization ≫ h = g.toNormalization.toNormalization :=
    g.toNormalization_normalizationDesc _ _ H
  have e2 : h ≫ g.toNormalization.fromNormalization ≫ g.fromNormalization = g.fromNormalization :=
    g.normalizationDesc_comp _ _ H
  have i1 : h ≫ g.toNormalization.fromNormalization = 𝟙 _ :=
    Scheme.Hom.normalization.hom_ext g _ _ g.fromNormalization
      (by rw [reassoc_of% e1, Scheme.Hom.toNormalization_fromNormalization, Category.comp_id])
      (by rw [Category.assoc, e2]) (Category.id_comp _)
  have i2 : g.toNormalization.fromNormalization ≫ h = 𝟙 _ :=
    Scheme.Hom.normalization.hom_ext g.toNormalization _ _ g.toNormalization.fromNormalization
      (by rw [Scheme.Hom.toNormalization_fromNormalization_assoc, e1, Category.comp_id])
      (by rw [Category.assoc, i1, Category.comp_id]) (Category.id_comp _)
  have : IsIso g.toNormalization.fromNormalization := ⟨h, i2, i1⟩
  have e := g.toNormalization.toNormalization_fromNormalization
  rw [← e]
  exact closedAt_comp _ _ V (closedAt_preimage _ V hV)
    (ConcreteCategory.bijective_of_isIso (g.toNormalization.fromNormalization.app V)).2

theorem RelNorm_of : LateralTheory.E.SteinPf.RelNorm := RelNorm_of_closed normClosed

end LateralTheory.E.RelNormPf
end
end

namespace UpperTheory.Et.E2

theorem n3 : LateralTheory.E.TruncationPieces.Piece := @LateralTheory.E.SimplicialPieceDiscrete.Piece_of

theorem n6 : LateralTheory.E.FiltPf.TowerFin := @LateralTheory.E.FiltPf.TowerFin_of

theorem n8 : LateralTheory.E.TruncPf.TruncBij := @LateralTheory.E.TruncPf.TruncBij_of

theorem n7 : LateralTheory.E.FiltPf.Trunc := @LateralTheory.E.TruncationInclusionIso.Trunc_of @n8

theorem n5 : LateralTheory.E.FiltPf.Tower := @LateralTheory.E.FiltPf.tower_of @n6 @n7

theorem n4 : LateralTheory.E.TruncationPieces.Filt := @LateralTheory.E.TruncationPieces.Filt_of_tower @n5

theorem n2 : LateralTheory.E.DescIntPf.EtaleRelativeIsoTruncationFromLevels := @LateralTheory.E.TruncationPieces.etale_relK_single_degree_pieces_of_piece_and_filtration @n3 @n4

theorem n1 : LateralTheory.E.t_E2Cut.Desc := @UpperTheory.descent_of_integral_descent_truncation @n2

theorem n11 : LateralTheory.E.BuildCut.Pts := @LateralTheory.E.PtsPf.Pts_of

theorem n12 : LateralTheory.E.BuildCut.LimInt := @LateralTheory.E.LimIntPf.LimInt_of

theorem n20 : LateralTheory.E.MayerVietorisSequence.SES := @UpperTheory.Cb.etale_mayer_vietoris_short_exact

theorem n21 : LateralTheory.E.MayerVietorisSequence.LES := @UpperTheory.Cb.etale_mayer_vietoris_long_exact

theorem n19 : LateralTheory.E.MayerVietorisSequence.MVSpc := @LateralTheory.E.MayerVietorisSequence.mvSpc_of @n20 @n21

theorem n22 : LateralTheory.E.MayerVietorisSequence.OpenCov := @LateralTheory.E.OpenCov_ptaPf.openCov

theorem n23 : LateralTheory.E.MayerVietorisSequence.SchPB := @LateralTheory.E.MayerVietorisSequence.schPB

theorem n18 : LateralTheory.E.t_E2Cut.MV := LateralTheory.E.t_E2Cut.MV_of_three n19 n22 n23

theorem n24 : LateralTheory.E.ContPf.ContAff := @LateralTheory.E.ContAffPf.ContAff_of

theorem n27 : LateralTheory.E.StepSPf.DiagramChase₂ := @LateralTheory.E.ChasePf.Chase_of

theorem n26 : LateralTheory.E.ContStepPf.StepS := @LateralTheory.E.StepSPf.StepS_of_chase @n27

theorem n29 : LateralTheory.E.StepKPf.Restr := @LateralTheory.E.RestrPf.Restr_of

theorem n30 : LateralTheory.E.StepKPf.ChasePf.ChaseB := @LateralTheory.E.ChaseBPf.ChaseB_of

theorem n28 : LateralTheory.E.ContStepPf.StepK := @LateralTheory.E.StepKPf.ChasePf.StepK_of' @n29 @n30

theorem n25 : LateralTheory.E.ContPf.ContStep := @LateralTheory.E.ContStepPf.ContStep_of @n26 @n28

theorem n31 : LateralTheory.E.ContPf.ContInd := @LateralTheory.E.ContIndPf.ContInd_of

theorem n17 : LateralTheory.E.t_E2Cut.Cont := @LateralTheory.E.ContPf.Cont_of @n18 @n24 @n25 @n31

theorem n16 : LateralTheory.E.HasLimPf.Loc := UpperTheory.Cb.cofiltered_scheme_limit_exists_locally n12 n17 n18

theorem n15 : LateralTheory.E.SysPf.HasLim := LateralTheory.E.HasLimPf.HasLim_of n16

theorem n34 : LateralTheory.E.SysFMPfSys.IdemSec := @LateralTheory.E.IdemSecPf.IdemSec_of

theorem n35 : LateralTheory.E.SysFMPf.FMex := UpperTheory.Cb.etale_finite_presentation_model_exists n12 n17 n18

theorem n37 : LateralTheory.E.FMrangePf.IdemLift := @LateralTheory.E.IdempotentLifting.IdemLift_of

theorem n36 : LateralTheory.E.SysFMPf.FMrange := LateralTheory.E.FMrangePfQc.FMrange_of n37

theorem n33 : LateralTheory.E.NbIsoPf.SysFM := LateralTheory.E.SysFMPfSys.SysFM_of n34 n35 n36

theorem n38 : LateralTheory.E.NbIsoPf.FlatMonoLim := @LateralTheory.E.FlatMonoLimPf.FlatMonoLim_of

theorem n32 : LateralTheory.E.SysPf.NbIso := LateralTheory.E.NbIsoPf.NbIso_of n33 n38

theorem n14 : LateralTheory.E.CompCut.Sys := LateralTheory.E.SysPf.Sys_of n15 n32

theorem n39 : LateralTheory.E.CompCut.LocAC := @LateralTheory.E.LocACPf.LocAC_of

theorem n41 : LateralTheory.E.NormACPf.Loc := @LateralTheory.E.LocPf.loc

theorem n40 : LateralTheory.E.CompCut.NormAC := @LateralTheory.E.NormACPf.NormAC_of @n41

theorem n13 : LateralTheory.E.BuildCut.Comp := LateralTheory.E.CompCut.goal_of n14 n39 n40

theorem n10 : LateralTheory.E.CoverCut.Build := LateralTheory.E.BuildCut.goal_of n11 n12 n13

theorem n43 : LateralTheory.E.ProEqvPf.StageB := @LateralTheory.E.StageBPf.StageB_of

theorem n44 : LateralTheory.E.ProEqvPf.Glue := @LateralTheory.E.GluePf.glue_of

theorem n42 : LateralTheory.E.CoverCut.ProEqv := @LateralTheory.E.ProEqvPf.etale_pro_equivalence_of_continuity_mayer_vietoris_lifting_stage_glue @n17 @n18 @n43 @n44

theorem n9 : LateralTheory.E.t_E2Cut.Cover := LateralTheory.E.CoverCut.goal_of n10 n42

theorem n46 : LateralTheory.E.HZeroPf.RootAIC := @LateralTheory.E.RootAICPf.RootAIC_of

theorem n48 : LateralTheory.E.ResBijPf.TwSec := @GlobalTheory.T.tateTwist_sections_locally_generated

theorem n47 : LateralTheory.E.HZeroPf.ResBij := @LateralTheory.E.ResBijPf.ResBij_of @n48

theorem n45 : LateralTheory.E.t_E2Cut.HZero := @LateralTheory.E.HZeroPf.HZero_of @n46 @n47

theorem n50 : LateralTheory.E.AICAcycPf.Step := @LateralTheory.E.StepPf.Step_of

theorem n51 : LateralTheory.E.AICAcycPf.Cov := @LateralTheory.E.CovPf.Cov_of

theorem n49 : LateralTheory.E.t_E2Cut.AICAcyc := @LateralTheory.E.AICAcycPf.AICAcyc_of @n45 @n18 @n50 @n51

theorem n56 : LateralTheory.E.GeometricData.TopInt := @LateralTheory.E.GeometricData.topInt

theorem n60 : LateralTheory.E.LZHensFinitePf.HensIdemLift := @LateralTheory.E.LZHensFinitePf.hensIdemLift

theorem n59 : LateralTheory.E.LZProperCut.LZHensFinite := @LateralTheory.E.LZHensFinitePf.LZHensFinite_of_lift @n60

theorem n58 : LateralTheory.E.ProjectiveLineCharts₂.ProjectiveLineTwoAffineChartsPolynomialGenerated := @UpperTheory.Cb.projectiveLineCharts_of_henselianFinite @n59

theorem n61 : LateralTheory.E.ProjectiveLineCharts₂.ChartBC := @LateralTheory.E.ChartBC_nnmPf.ChartBC_of

theorem n57 : LateralTheory.E.GeometricData.LineOpens := @LateralTheory.E.ProjectiveLineCharts₂.LineOpens_of @n58 @n61

theorem n62 : LateralTheory.E.GeometricData.EmbedNonDeg := @LateralTheory.E.EmbedNonDeg₂.EmbedNonDeg_of

theorem n63 : LateralTheory.E.GeometricData.EmbedAffine := @LateralTheory.E.GeometricData.embedAffine

theorem n55 : LateralTheory.E.ChartsGeom_vpaPf.GeoData := @LateralTheory.E.GeometricData.GeoData_of @n56 @n57 @n62 @n63

theorem n65 : LateralTheory.E.ChartsGeom_vpaPf.Overlap := @LateralTheory.E.ChartOverlap₂.Overlap_of

theorem n64 : LateralTheory.E.ChartsGeom_vpaPf.CoverOfData := @LateralTheory.E.ChartsGeom_vpaPf.coverOfData_of @n65

theorem n54 : LateralTheory.E.StdChartsProof.ChartsGeom := @LateralTheory.E.ChartsGeom_vpaPf.ChartsGeom_of' @n55 @n64

theorem n66 : LateralTheory.E.StdChartsProof.FibreIdem := @UpperTheory.Cb.finite_over_henselian_fibre_idempotents_lift @n59

theorem n53 : LateralTheory.E.StandardEtaleChartsIdempotentGluing.StdCharts := @LateralTheory.E.StdChartsProof.StdCharts_of @n54 @n66

theorem n70 : LateralTheory.E.LZIdemSumNoetherian.NoetherianLocalChartOverlapFiniteComplement := @LateralTheory.E.NoetherianChartOverlapFiniteComplement.noetherian_local_chart_overlap_finite_complement

theorem n71 : LateralTheory.E.LZIdemSumNoetherian.LZIdemPow := @LateralTheory.E.LZIdemPowProof.LZIdemPow_of

theorem n72 : LateralTheory.E.LZIdemSumNoetherian.LZARStep := @LateralTheory.E.LZARFacts.LZARStep_of

theorem n69 : LateralTheory.E.IdempotentLiftingAlt.LZIdemSumNoeth := @LateralTheory.E.LZIdemSumNoetherian.goal_of @n70 @n71 @n72

theorem n73 : LateralTheory.E.IdempotentLiftingAlt.LZIdemSumApprox := @LateralTheory.E.LZIdemSumApproxYDDUPf.LZIdemSumApprox_of

theorem n68 : LateralTheory.E.StandardEtaleChartsIdempotentGluing.IdemLift := @LateralTheory.E.IdempotentLiftingAlt.IdemLift_of @n69 @n73

theorem n67 : LateralTheory.E.StandardEtaleChartsIdempotentGluing.AlgGlue := @LateralTheory.E.AlgGlue₂.AlgGlue_of @n68 @n59

theorem n52 : LateralTheory.E.t_E2Cut.LineZero := @LateralTheory.E.StandardEtaleChartsIdempotentGluing.goal_of @n53 @n67

theorem n75 : LateralTheory.E.StandardEtaleChartsMultivariableHensel.StdCharts := @LateralTheory.E.StdChartsProof₂.StdCharts_of

theorem n76 : LateralTheory.E.LineOneCut.FibCover := @LateralTheory.E.FiberCover.FibCover_of

theorem n81 : LateralTheory.E.BinPf.DescEqv := @LateralTheory.E.BinPf.DescEqv_of

theorem n80 : LateralTheory.E.ProdAcycPf.Bin := @LateralTheory.E.BinPfChains.bin_of @n81

theorem n79 : LateralTheory.E.QuotAcycCut.ProdAcyc := @LateralTheory.E.ProdAcycPf.prod_of @n80

theorem n83 : LateralTheory.E.HensCut.LocAIC := @LateralTheory.E.LocalizationIntegralClosure.LocAIC_of

theorem n84 : LateralTheory.E.HensCut.MonicSplits := @LateralTheory.E.MonicSplitsPf.MonicSplits_of

theorem n85 : LateralTheory.E.HensCut.IdemPart := @LateralTheory.E.IdemPartPf.IdemPart_of

theorem n86 : LateralTheory.E.HensCut.ColimHens := @LateralTheory.E.ColimHensPf.ColimHens_of

theorem n88 : LateralTheory.E.PartDiagCut.PartDirected := @LateralTheory.E.PartDirectedPf.PartDirected_of

theorem n89 : LateralTheory.E.PartDiagCut.DiagId := @LateralTheory.E.DiagIdPf.DiagId_of

theorem n90 : LateralTheory.E.PartDiagCut.DiagComp := @LateralTheory.E.DiagCompPf.DiagComp_of

theorem n91 : LateralTheory.E.PartDiagCut.DiagNat := @LateralTheory.E.DiagNatPf.DiagNat_of

theorem n92 : LateralTheory.E.PartDiagCut.StageProd := @LateralTheory.E.StageProdPf.StageProd_of @n83

theorem n93 : LateralTheory.E.PartDiagCut.PartA := @LateralTheory.E.PartAPf.PartA_of

theorem n94 : LateralTheory.E.PartDiagCut.PartB := @LateralTheory.E.PartBPf.PartB_of

theorem n96 : LateralTheory.E.PartCPf.Lift := @LateralTheory.E.LiftPf.Lift_of

theorem n95 : LateralTheory.E.PartDiagCut.PartC := @LateralTheory.E.PartCPfSplit.PartC_of @n83 @n84 @n85 @n93 @n96

theorem n87 : LateralTheory.E.HensCut.PartDiag := @LateralTheory.E.PartDiagCut.goal_of @n88 @n89 @n90 @n91 @n92 @n93 @n94 @n95

theorem n82 : LateralTheory.E.QuotAcycCut.Hens := @LateralTheory.E.HensCut.goal_of @n83 @n84 @n85 @n86 @n87

theorem n78 : LateralTheory.E.t_E2Cut.QuotAcyc := @LateralTheory.E.QuotAcycCut.goal_of @n79 @n82

theorem n77 : LateralTheory.E.LineOneCut.ChartAcyc := @LateralTheory.E.ChartAcycPf.ChartAcyc_of @n78

theorem n97 : LateralTheory.E.ChartSurjCut.Root := @LateralTheory.E.RootPf.Root_of

theorem multiplicative_root_pow_etale : LateralTheory.E.MulPf.RootPow := @LateralTheory.E.RootPowPf.RootPow_of

theorem multiplicative_generator_etale : LateralTheory.E.MulPf.Gen := @LateralTheory.E.GenPf.Gen_of @multiplicative_root_pow_etale

theorem multiplicative_local_generator_etale : LateralTheory.E.MulPf.LocGen := @LateralTheory.E.MulPf.LocGen_of @multiplicative_root_pow_etale

theorem twist_trivial_multiplicative : LateralTheory.E.TwistTrivial.Mul := @LateralTheory.E.MulPf.Mul_of @multiplicative_generator_etale @multiplicative_local_generator_etale

theorem locally_constant_iso_twist_trivial : LateralTheory.E.LCIsoPf.TwTriv := @LateralTheory.E.TwistTrivial.TwTriv_of @twist_trivial_multiplicative

theorem augmentation_bijective_separable : LateralTheory.E.AugBijPf.Sep := @LateralTheory.E.AugBijPf.Sep_holds

theorem augmentation_bijective_of_local_pieces : LateralTheory.E.AugBijPf.Glue := @LateralTheory.E.AugBijPf.Glue_holds

theorem augmentation_bijective_at_strictly_henselian_root : LateralTheory.E.AugBijPf.Root := @UpperTheory.Cb.augmentation_map_bijective

theorem augmentation_surjective_on_local_sections : LateralTheory.E.AugBijPf.LocSurj := @LateralTheory.E.AugBijPf.LocSurj_of @augmentation_bijective_at_strictly_henselian_root

theorem sections_localization_augmentation_compat : LateralTheory.E.AugBijPf.SecLoc := @LateralTheory.E.AugBijPf.secLoc'

theorem augmentation_localization_pow_compat : LateralTheory.E.AugBijPf.LocPow := @LateralTheory.E.LocPowPf.LocPow_of

theorem augmentation_zariski_localization_pow_compat : LateralTheory.E.AugBijPf.ZarPow := @LateralTheory.E.AugBijPf.ZarPow_of @augmentation_localization_pow_compat

theorem augmentation_generic_point_eq : LateralTheory.E.AugBijPf.GenEq := @LateralTheory.E.AugBijPf.GenEq_of @augmentation_zariski_localization_pow_compat

theorem augmentation_injective_on_local_sections : LateralTheory.E.AugBijPf.LocInj := @LateralTheory.E.AugBijPf.LocInj_of @augmentation_bijective_at_strictly_henselian_root @sections_localization_augmentation_compat @augmentation_generic_point_eq

theorem untwisted_pushforward_of_augmentation_bijective : LateralTheory.E.TateTwistZeroAugmentationBijective.AugBij := @LateralTheory.E.AugBijPf.AugBij_of_loc @augmentation_bijective_separable @augmentation_bijective_of_local_pieces @augmentation_surjective_on_local_sections @augmentation_injective_on_local_sections

theorem untwisted_pushforward_of_localized_cohomology_iso : LateralTheory.E.LCIsoPf.Tw0 := @LateralTheory.E.TateTwistZeroAugmentationSheaf.Tw0_of @untwisted_pushforward_of_augmentation_bijective

theorem secIso : LateralTheory.E.LCIsoPf.SecIso := @LateralTheory.E.LCIsoPf.SecIso_of @locally_constant_iso_twist_trivial @untwisted_pushforward_of_localized_cohomology_iso

theorem n98 : LateralTheory.E.ChartSurjCut.LCIso := @LateralTheory.E.LCIsoPf.SecIso_LCIso @secIso

theorem proper_base_change_affine_line_of_stalk_iso : LateralTheory.E.StandardEtaleChartsMultivariableHensel.Heart := @UpperTheory.cohomology_punctured_affine_line

theorem n74 : LateralTheory.E.t_E2Cut.LineOne := @LateralTheory.E.StandardEtaleChartsMultivariableHensel.goal_of @n18 @n75 @n76 @n77 @n97 @n98 @proper_base_change_affine_line_of_stalk_iso

theorem higher_affine_space_zariski_cover : LateralTheory.E.LineHighPf.ZCov := @LateralTheory.E.ZCovPf.projectiveLine_integers_affine_cover_absolutely_integrally_closed

theorem higher_affine_space_fibrewise_cover : LateralTheory.E.LineHighPf.FibCov := @LateralTheory.E.FibCovPf.FibCov_of

theorem higher_affine_space_cover_by_lines : LateralTheory.E.LineHighPf.Cover2 := @LateralTheory.E.LineHighPf.Cover2_of @higher_affine_space_zariski_cover @higher_affine_space_fibrewise_cover

theorem proper_base_change_affine_space : LateralTheory.E.t_E2Cut.LineHigh := @LateralTheory.E.LineHighPf.LineHigh_of @n78 @n18 @higher_affine_space_cover_by_lines

theorem integral_pullback_henselian_lift : LateralTheory.E.IntPBPf.IntHens := @LateralTheory.E.IntHensPf.IntHens_of

theorem integral_pullback_fibre_iso : LateralTheory.E.IntPBPf.IntFib := @LateralTheory.E.IntFibPf.IntFib_of

theorem proper_base_change_integral_pullback : LateralTheory.E.t_E2Cut.IntPB := @LateralTheory.E.IntPBPf.IntPB_of @integral_pullback_henselian_lift @integral_pullback_fibre_iso

theorem stein_factorization_relative_normalization : LateralTheory.E.SteinPf.RelNorm := @LateralTheory.E.RelNormPf.RelNorm_of

theorem stein_factorization_integral_closure_open : LateralTheory.E.SteinPf.AICOpen := @LateralTheory.E.AICOpenPf.AICOpen_of

theorem proper_base_change_stein_factorization : LateralTheory.E.t_E2Cut.Stein := LateralTheory.E.SteinPf.Stein_of stein_factorization_relative_normalization stein_factorization_integral_closure_open

theorem stalk_pushforward_continuous_limit : LateralTheory.E.StalkGermPf.StalkCont := @LateralTheory.E.StalkContPf.StalkCont_of

theorem stalk_eq_germ_of_zariski_local : LateralTheory.E.ZLGPf.StalkGerm := @LateralTheory.E.StalkGermPf.StalkGerm_of @stalk_pushforward_continuous_limit

theorem zariski_induction_injective_mayer_vietoris : LateralTheory.E.InjStepPf.OverMV := @LateralTheory.E.OverMVPf.OverMV_of

theorem zariski_induction_injective_two_open_cover : LateralTheory.E.InjStepPf.TwoStep := @LateralTheory.E.InjStepPf.TwoStep_of @zariski_induction_injective_mayer_vietoris

theorem zariski_induction_empty_cohomology : LateralTheory.E.InjStepPf.EmptyH := @LateralTheory.E.EmptyH₂.EmptyH_of

theorem zariski_induction_injectivity_of_etale_comparison : LateralTheory.E.ZarIndPf.InjStep := @LateralTheory.E.InjStepPf.InjStep_of @zariski_induction_injective_two_open_cover @zariski_induction_empty_cohomology

theorem zariski_induction_surjectivity_of_etale_comparison : LateralTheory.E.ZarIndPf.SurjStep := @LateralTheory.E.SurjStepPf.SurjStep_of

theorem zariski_induction_step_bijective : LateralTheory.E.ZarIndPf.Step := @LateralTheory.E.ZarIndPf.Step_of @zariski_induction_injectivity_of_etale_comparison @zariski_induction_surjectivity_of_etale_comparison

theorem zariski_local_to_global_induction : LateralTheory.E.ZLGPf.ZarInd := @LateralTheory.E.ZarIndPf.ZarInd_of_step @zariski_induction_step_bijective

theorem proper_base_change_zariski_local_to_global : LateralTheory.E.t_E2Cut.ZLG := @LateralTheory.E.ZLGPf.ZLG_of @n17 @n18 @stalk_eq_germ_of_zariski_local @zariski_local_to_global_induction

theorem fibre_closed_quasi_compact_quasi_separated : LateralTheory.E.FibClosedPf.FibQCQS := @LateralTheory.E.FibClosedPf.fibQCQS

theorem fibre_stalk_absolutely_integrally_closed : LateralTheory.E.FibStalkPf.StalkAIC := @LateralTheory.E.StalkSHSPf.stalkAIC

theorem fibre_stalk_strictly_henselian_sep_closed : LateralTheory.E.FibStalkPf.StalkSHS := @LateralTheory.E.FibStalkPf.stalkSHS_of @fibre_stalk_absolutely_integrally_closed

theorem strictly_henselian_quotient : LateralTheory.E.FibStalkPf.QuotSH := @LateralTheory.E.FibStalkPf.quotSH

theorem fibre_stalk_strictly_henselian : LateralTheory.E.FibStalkPf.StalkSH := @LateralTheory.E.FibStalkPf.StalkSH_of @fibre_stalk_strictly_henselian_sep_closed @strictly_henselian_quotient

theorem base_absolutely_integrally_closed_integral : LateralTheory.E.BaseAICPf.BaseInt := @LateralTheory.E.BaseIntPf.BaseInt_of

theorem base_absolutely_integrally_closed_localization_localization : LateralTheory.E.BaseAICPf.BaseLocLoc := @LateralTheory.E.BaseLocLocPf.BaseLocLoc_of

theorem base_absolutely_integrally_closed_localization : LateralTheory.E.BaseAICPf.BaseLoc := LateralTheory.E.BaseAICPf.BaseLoc_of base_absolutely_integrally_closed_localization_localization

theorem fibre_equivalence_base_absolutely_integrally_closed : LateralTheory.E.FibreEqvPf.BaseAIC := LateralTheory.E.BaseAICPf.BaseAIC_of base_absolutely_integrally_closed_integral base_absolutely_integrally_closed_localization

theorem stalk_ring_absolutely_integrally_closed : LateralTheory.E.FibreEqvPf.StalkAICRing := @LateralTheory.E.StalkAICRingPf.StalkAICRing_of

theorem spec_absolutely_integrally_closed_cohomology : LateralTheory.E.FibreEqvPf.SpecAIC := @LateralTheory.E.SpecAICPf.SpecAIC_of

theorem fibre_equivalence_stalk_absolutely_integrally_closed : LateralTheory.E.FibreEqvPf.StalkAIC := @LateralTheory.E.FibreEqvPf.StalkAIC_of @stalk_ring_absolutely_integrally_closed @spec_absolutely_integrally_closed_cohomology

theorem fibre_equivalence_stalk_fibre : LateralTheory.E.FibreEqvPf.StalkFib := LateralTheory.E.FibreEqvPf.StalkFib_of fibre_equivalence_base_absolutely_integrally_closed fibre_equivalence_stalk_absolutely_integrally_closed

theorem fibre_stalk_equivalence : LateralTheory.E.FibStalkPf.FibreEqv := @LateralTheory.E.FibreEqvPf.FibreEqv_of @fibre_stalk_strictly_henselian_sep_closed @fibre_equivalence_stalk_fibre

theorem closed_fibre_stalk_cohomology : LateralTheory.E.FibClosedPf.FibStalk := @LateralTheory.E.FibStalkPf.FibStalk_of @fibre_stalk_strictly_henselian @fibre_stalk_equivalence

theorem proper_base_change_closed_fibre : LateralTheory.E.FibPf.FibClosed := @LateralTheory.E.FibClosedPf.FibClosed_of @proper_base_change_zariski_local_to_global @n45 @n49 @fibre_closed_quasi_compact_quasi_separated @closed_fibre_stalk_cohomology

theorem proper_base_change_fibre : LateralTheory.E.t_E2Cut.Fib := @LateralTheory.E.FibPf.Fib_of @proper_base_change_closed_fibre @n45 @n49

theorem chow_lemma_image : LateralTheory.E.ChowCut.Img := @LateralTheory.E.ImgPf.Img_of

theorem chow_lemma_iterated_base_change : LateralTheory.E.ChowLCut.IterBC := @LateralTheory.E.IterBCPf.IterBC_of

theorem chow_graph_open_cover : LateralTheory.E.ChowGraphCut.Cover := @LateralTheory.E.CoverExistence.Cover_of

theorem embedding_affine_closed_immersion : LateralTheory.E.EmbedPf.AffClosed := @LateralTheory.E.EmbedPf.affClosed

theorem chow_lemma_projective_line_extension : LateralTheory.E.ChowLCut.LineEx := @LateralTheory.E.LineExPf.LineEx_of

theorem embedding_projective_line_chart : LateralTheory.E.EmbedPf.LineChart := @LateralTheory.E.LineChartPf.LineChart_of

theorem embedding_affine_chart : LateralTheory.E.EmbedPf.Chart := LateralTheory.E.EmbedPf.chart_of chow_lemma_projective_line_extension embedding_projective_line_chart

theorem chow_graph_projective_embedding : LateralTheory.E.ChowGraphCut.Embed := @LateralTheory.E.EmbedPf.Embed_of @embedding_affine_closed_immersion @embedding_affine_chart

theorem chow_graph_iterated_composition : LateralTheory.E.ChowGraphCut.IterComp := @LateralTheory.E.IterCompPf.IterComp_of

theorem chow_graph_fibre_product : LateralTheory.E.ChowGraphCut.Prod := LateralTheory.E.ProdPf.Prod_of chow_graph_iterated_composition

theorem chow_graph_projective_reduction : LateralTheory.E.ChowGraphCut.Core := @LateralTheory.E.ImageInPf.Core_of

theorem chow_lemma_graph_construction : LateralTheory.E.ChowLCut.ChowGraph := LateralTheory.E.ChowGraphCut.goal_of chow_graph_open_cover chow_graph_projective_embedding chow_graph_fibre_product chow_graph_projective_reduction

theorem chow_lemma_projective_cover : LateralTheory.E.ChowCut.ChowL := LateralTheory.E.ChowLCut.goal_of chow_lemma_iterated_base_change chow_lemma_graph_construction

theorem normalization_affine_absolutely_integrally_closed : LateralTheory.E.NormPf.AICPf.AffAIC := @LateralTheory.E.NormPf.AffPf.affAIC

theorem normalization_local_absolutely_integrally_closed : LateralTheory.E.NormPf.AICPf.LocAIC := @LateralTheory.E.LocalIntegralClosureRoots.LocAIC_of

theorem chow_lemma_normalization : LateralTheory.E.ChowCut.Norm := @LateralTheory.E.NormPf.AICPf.norm_full @normalization_affine_absolutely_integrally_closed @normalization_local_absolutely_integrally_closed

theorem e2Cut_chow : LateralTheory.E.t_E2Cut.Chow := LateralTheory.E.ChowCut.goal_of chow_lemma_image chow_lemma_projective_cover chow_lemma_normalization


open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut in
theorem towers (H : Hyp) (q : ℕ) (i : ℤ) (B : Type) [CommRing B] [IsLocalRing B] (hB : SH B) (hq : IsUnit (q : B))
    {Y : Scheme.{0}} (r : Y ⟶ Spec (CommRingCat.of B)) (hr : IT r) : PB q i r := by
  have h := tower H n1 n9 n45 n49 n52 n74 proper_base_change_affine_space proper_base_change_integral_pullback proper_base_change_stein_factorization proper_base_change_fibre q i B hB hq r hr (𝟙 Y) inferInstance
  simpa using h


open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut in
theorem main (H : Hyp) : E2 := by
  intro q A _ _ hA hq X p _ i
  show PB q i p
  refine reduce H n1 n9 q i A hq p ?_
  intro Z h hh hZ
  obtain ⟨Z', c, hZ', hdom, hc, hcomp⟩ := e2Cut_chow A h p hh hZ
  obtain ⟨hcqc, hcqs⟩ := IT.qc hc
  have hT : PB q i (c ≫ h ≫ p) := towers H q i A hA hq (c ≫ h ≫ p) hcomp
  refine (proper_base_change_fibre H q i A hq c (h ≫ p) hZ' hZ ?_).1 hT
  intro B _ _ hB hqB t
  exact towers H q i B hB hqB (pullback.snd c t) (IT.bc hc t (IsPullback.of_hasPullback c t))

end UpperTheory.Et.E2
