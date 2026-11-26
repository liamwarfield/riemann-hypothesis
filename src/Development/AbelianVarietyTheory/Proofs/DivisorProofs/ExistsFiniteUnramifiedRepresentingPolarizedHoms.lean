module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeRepresentingPolarizedHomsLocNoet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerUniversalObjectAtModelStalk

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfFiniteType
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuativeExistenceOfDvrLiftsLocallyNoetherian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuativeExistenceOfDvrLiftsLocallyNoetherian
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DvrCriterion

open Scheme.IdealSheafData TopologicalSpace

theorem universallyClosed_of_finite_jointly_surjective {ι : Type} [Finite ι] {X Z : Scheme.{0}}
    (A : ι → Scheme.{0}) (g : ∀ i, A i ⟶ X) (k : X ⟶ Z) (hcov : ∀ x : X, ∃ i, ∃ a, g i a = x)
    (h : ∀ i, UniversallyClosed (g i ≫ k)) : UniversallyClosed k := by
  constructor
  intro X' Y' i₁ i₂ f' H
  have c := fun i ↦ (h i).universally_isClosedMap _ _ _
    ((IsPullback.of_hasPullback i₁ (g i)).paste_horiz H)
  intro Zs hZ
  have e : f' '' Zs = ⋃ i, (pullback.fst i₁ (g i) ≫ f') '' (pullback.fst i₁ (g i) ⁻¹' Zs) := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨i, a, ha⟩ := hcov (i₁ x)
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x a ha.symm
      exact Set.mem_iUnion.2 ⟨i, z, by simpa [hz] using hx, by simp [hz]⟩
    · intro y hy
      obtain ⟨i, z, hz, rfl⟩ := Set.mem_iUnion.1 hy
      exact ⟨_, hz, by simp⟩
  rw [e]
  exact isClosed_iUnion_of_finite fun i ↦ c i _ (hZ.preimage (Scheme.Hom.continuous _))

theorem universallyClosed_snd_of_lift {Y S : Scheme.{0}} (π : Y ⟶ S) [LocallyOfFiniteType π]
    [QuasiCompact π] [IsSeparated π] (R : Type) [CommRing R] [IsNoetherianRing R] (u : Sp R ⟶ S)
    (H : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
      (x : Sp (FractionRing V) ⟶ Y) (y : Sp V ⟶ S), x ≫ π = Out.jK V ≫ y →
        ∃ x' : Sp V ⟶ Y, Out.jK V ≫ x' = x ∧ x' ≫ π = y) :
    UniversallyClosed (pullback.snd π u) := by
  classical
  set s := pullback.snd π u with hs
  have : CompactSpace (pullback π u : Scheme.{0}) := QuasiCompact.compactSpace_of_compactSpace s
  have : IsLocallyNoetherian (pullback π u : Scheme.{0}) := LocallyOfFiniteType.isLocallyNoetherian s
  have : IsNoetherian (pullback π u : Scheme.{0}) := {}
  let C : irreducibleComponents (pullback π u : Scheme.{0}) → Closeds (pullback π u : Scheme.{0}) :=
    fun c ↦ ⟨c.1, isClosed_of_mem_irreducibleComponents _ c.2⟩
  have : Finite (irreducibleComponents (pullback π u : Scheme.{0})) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  have hr : ∀ c, Set.range (vanishingIdeal (C c)).subschemeι = c.1 := fun c ↦ by
    rw [range_subschemeι, coe_support_vanishingIdeal]; rfl
  refine universallyClosed_of_finite_jointly_surjective (fun c ↦ (vanishingIdeal (C c)).subscheme)
    (fun c ↦ (vanishingIdeal (C c)).subschemeι) s (fun x ↦ ?_) (fun c ↦ ?_)
  · refine ⟨⟨_, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩
    have : x ∈ Set.range (vanishingIdeal (C ⟨_, irreducibleComponent_mem_irreducibleComponents x⟩)).subschemeι := by
      rw [hr]; exact mem_irreducibleComponent
    exact this
  set I := vanishingIdeal (C c)
  have : IsReduced I.subscheme := GlobalTheory.ReducedSubgroup.isReduced_subscheme_vanishingIdeal _
  have : IrreducibleSpace (Set.range I.subschemeι) := by
    have h1 : IsIrreducible (Set.range I.subschemeι) := by rw [hr]; exact c.2.1
    exact Subtype.irreducibleSpace h1
  have : IrreducibleSpace I.subscheme :=
    I.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph.irreducibleSpace_iff.2 this
  have : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have hP : IsProper (I.subschemeι ≫ s) := by
    refine GlobalTheory.TraitProper.isProper_of_lift_genericPoint R I.subscheme (I.subschemeι ≫ s) ?_
    intro V K _ _ _ _ _ _ _ x y _ hxy
    let e : FractionRing V ≃ₐ[V] K := IsLocalization.algEquiv (nonZeroDivisors V) (FractionRing V) K
    let ε : K →+* FractionRing V := e.symm.toRingEquiv.toRingHom
    let ε' : FractionRing V →+* K := e.toRingEquiv.toRingHom
    have he1 : Spec.map (CommRingCat.ofHom ε) ≫ spMap (algebraMap V K) = Out.jK V := by
      rw [spMap, ← Spec.map_comp]
      congr 2
      ext a
      exact e.symm.commutes a
    have he2 : Spec.map (CommRingCat.ofHom ε') ≫ Out.jK V = spMap (algebraMap V K) := by
      rw [spMap, Out.jK, ← Spec.map_comp]
      congr 2
      ext a
      exact e.commutes a
    have he3 : Spec.map (CommRingCat.ofHom ε') ≫ Spec.map (CommRingCat.ofHom ε) = 𝟙 _ := by
      rw [← Spec.map_comp, ← Spec.map_id]
      congr 2
      ext a
      exact e.apply_symm_apply a
    let xF : Sp (FractionRing V) ⟶ Y :=
      Spec.map (CommRingCat.ofHom ε) ≫ x ≫ I.subschemeι ≫ pullback.fst π u
    have hxF : xF ≫ π = Out.jK V ≫ (y ≫ u) := by
      have : xF ≫ π = Spec.map (CommRingCat.ofHom ε) ≫ (x ≫ I.subschemeι ≫ s) ≫ u := by
        simp [xF, hs, pullback.condition]
      rw [this, hxy, ← he1]
      simp
    obtain ⟨x'', hx1, hx2⟩ := H V xF (y ≫ u) hxF
    let x3 : Sp V ⟶ pullback π u := pullback.lift x'' y hx2
    have h3 : Out.jK V ≫ x3 = Spec.map (CommRingCat.ofHom ε) ≫ x ≫ I.subschemeι := by
      apply pullback.hom_ext
      · simp only [x3, Category.assoc, pullback.lift_fst]
        exact hx1
      · have : Spec.map (CommRingCat.ofHom ε) ≫ (x ≫ I.subschemeι ≫ s) = Out.jK V ≫ y := by
          rw [hxy, ← he1]; simp
        simp only [x3, Category.assoc, pullback.lift_snd]
        exact this.symm
    have hdom : IsDominant (Out.jK V) := by
      have hinj : Function.Injective (algebraMap V (FractionRing V)) := IsFractionRing.injective _ _
      refine ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_⟩
      exact ((RingHom.injective_iff_ker_eq_bot _).mp hinj).le.trans bot_le
    have hrange : Set.range x3 ⊆ (C c : Set (pullback π u : Scheme.{0})) := by
      rintro _ ⟨v, rfl⟩
      have hv : v ∈ closure (Set.range (Out.jK V)) := (Out.jK V).denseRange v
      have := map_mem_closure x3.continuous hv (t := (C c : Set (pullback π u : Scheme.{0}))) (by
        rintro _ ⟨w, rfl⟩
        change x3 (Out.jK V w) ∈ c.1
        rw [← Scheme.Hom.comp_apply, h3, ← hr c]
        exact ⟨(Spec.map (CommRingCat.ofHom ε) ≫ x) w, by rw [← Scheme.Hom.comp_apply, Category.assoc]⟩)
      rwa [(C c).isClosed.closure_eq] at this
    have hker : I.subschemeι.ker ≤ x3.ker := by
      rw [I.ker_subschemeι]
      exact GlobalTheory.ReducedSubgroup.vanishingIdeal_le_ker x3 (C c) hrange
    refine ⟨IsClosedImmersion.lift I.subschemeι x3 hker, ?_⟩
    rw [← cancel_mono I.subschemeι, Category.assoc, IsClosedImmersion.lift_fac, ← he2,
      Category.assoc, h3, ← Category.assoc, ← Category.assoc, he3, Category.id_comp]
  exact inferInstance

theorem existence_of_lift_discreteValuationRing : ∀ {Y S : Scheme.{0}} [IsLocallyNoetherian S] (π : Y ⟶ S), LocallyOfFiniteType π → QuasiCompact π → IsSeparated π → (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (x : Sp (FractionRing V) ⟶ Y) (y : Sp V ⟶ S), x ≫ π = Out.jK V ≫ y → ∃ x' : Sp V ⟶ Y, Out.jK V ≫ x' = x ∧ x' ≫ π = y) → ValuativeCriterion.Existence π := by
  intro Y S _ π _ _ _ H
  have hUC : UniversallyClosed π := by
    rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @UniversallyClosed) S.affineOpenCover.openCover]
    intro i
    have := S.affineOpenCover.map_prop i
    have hR : IsNoetherianRing (S.affineOpenCover.X i) :=
      isLocallyNoetherian_Spec.1 (isLocallyNoetherian_of_isOpenImmersion (S.affineOpenCover.f i))
    exact @universallyClosed_snd_of_lift Y S π _ _ _ (S.affineOpenCover.X i) _ hR
      (S.affineOpenCover.openCover.f i) H
  have h := hUC
  rw [UniversallyClosed.eq_valuativeCriterion] at h
  exact h.1

end GlobalTheory.DvrCriterion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuativeExistenceOfDvrLiftsLocallyNoetherianStatement
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuativeExistence_of_dvr_lifts_locallyNoetherian : ∀ {Y S : Scheme.{0}} [IsLocallyNoetherian S] (π : Y ⟶ S), LocallyOfFiniteType π → QuasiCompact π → IsSeparated π → (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (x : Sp (FractionRing V) ⟶ Y) (y : Sp V ⟶ S), x ≫ π = Out.jK V ≫ y → ∃ x' : Sp V ⟶ Y, Out.jK V ≫ x' = x ∧ x' ≫ π = y) → ValuativeCriterion.Existence π := by
  first | exact @GlobalTheory.DvrCriterion.existence_of_lift_discreteValuationRing | exact GlobalTheory.DvrCriterion.existence_of_lift_discreteValuationRing | (intros; apply GlobalTheory.DvrCriterion.existence_of_lift_discreteValuationRing <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.EndLoc.HomFixProper

theorem lbIso_pull_eq {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {f g : Y ⟶ X} (h : f = g) :
    LBIso (L.pull f) (L.pull g) := h ▸ GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hL f)

theorem lbIso_pull_pull {X Y : Scheme.{0}} {L L' : LB X} (h : LBIso L L') (f : Y ⟶ X) :
    LBIso (L.pull f) (L'.pull f) :=
  LBIso.chartPull (chartPullPull L f) (chartPullPull L' f) h

theorem isProper_of_finiteType : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (R : HomFixRep A B L M), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → QuasiCompact R.π → IsSeparated R.π → LocallyOfFiniteType R.π → IsProper R.π := by
  intro S _ A B _ _ _ _ L M R hA hB hL hM _ _ hqc hsep hlft
  have hex : ValuativeCriterion.Existence R.π := by
    refine GlobalTheory.T.valuativeExistence_of_dvr_lifts_locallyNoetherian R.π hlft hqc hsep fun V _ _ _ x y hxy => ?_
    haveI := R.hom

    let AV := (Over.pullback y).obj A
    let ψA : AV.left ⟶ A.left := pullback.fst A.hom y
    have hVA : IsGrpPullback AV A y ψA := isGrpPullback_pullback A y
    have hAV : IsAbelianScheme AV := GlobalTheory.isAbelianScheme_pullback_obj y A hA
    let BV := (Over.pullback y).obj B
    let ψB : BV.left ⟶ B.left := pullback.fst B.hom y
    have hVB : IsGrpPullback BV B y ψB := isGrpPullback_pullback B y
    have hBV : IsAbelianScheme BV := GlobalTheory.isAbelianScheme_pullback_obj y B hB

    let AK := (Over.pullback x).obj R.AH
    let pA : AK.left ⟶ R.AH.left := pullback.fst R.AH.hom x
    have hK1A : IsGrpPullback AK R.AH x pA := isGrpPullback_pullback R.AH x
    have hKA : IsGrpPullback AK A (x ≫ R.π) (pA ≫ R.φA) := hK1A.comp R.pbA
    have hKA' : IsGrpPullback AK A (Out.jK V ≫ y) (pA ≫ R.φA) := hKA.congr hxy rfl
    let BK := (Over.pullback x).obj R.BH
    let pB : BK.left ⟶ R.BH.left := pullback.fst R.BH.hom x
    have hK1B : IsGrpPullback BK R.BH x pB := isGrpPullback_pullback R.BH x
    have hKB : IsGrpPullback BK B (x ≫ R.π) (pB ≫ R.φB) := hK1B.comp R.pbB
    have hKB' : IsGrpPullback BK B (Out.jK V ≫ y) (pB ≫ R.φB) := hKB.congr hxy rfl
    let κA : AK.left ⟶ AV.left := hVA.1.lift (pA ≫ R.φA) (AK.hom ≫ Out.jK V)
      ((Category.assoc _ _ _).symm.trans (hKA'.1.w.trans (Category.assoc _ _ _).symm))
    have hκA1 : κA ≫ ψA = pA ≫ R.φA := hVA.1.lift_fst _ _ _
    have hκA2 : κA ≫ AV.hom = AK.hom ≫ Out.jK V := hVA.1.lift_snd _ _ _
    have hκA : IsGrpPullback AK AV (Out.jK V) κA := IsGrpPullback.cancel hVA (hKA'.congr rfl hκA1.symm) hκA2
    let κB : BK.left ⟶ BV.left := hVB.1.lift (pB ≫ R.φB) (BK.hom ≫ Out.jK V)
      ((Category.assoc _ _ _).symm.trans (hKB'.1.w.trans (Category.assoc _ _ _).symm))
    have hκB1 : κB ≫ ψB = pB ≫ R.φB := hVB.1.lift_fst _ _ _
    have hκB2 : κB ≫ BV.hom = BK.hom ≫ Out.jK V := hVB.1.lift_snd _ _ _
    have hκB : IsGrpPullback BK BV (Out.jK V) κB := IsGrpPullback.cancel hVB (hKB'.congr rfl hκB1.symm) hκB2

    let ΦK : AK ⟶ BK := (Over.pullback x).map R.Φ
    have hΦK : IsMonHom ΦK := inferInstance
    have hΦK1 : ΦK.left ≫ pB = pA ≫ R.Φ.left := pullback.lift_fst _ _ _
    obtain ⟨ΦV, hΦV, hΦV1, -⟩ := GlobalTheory.abelianScheme_hom_extends_dedekind_of_isGrpPullback
      GlobalTheory.homExtension_semiAbelian_dvr V (FractionRing V) AV BV AK BK κA κB hAV hBV hκA hκB ΦK hΦK

    have iso : LBIso (L.pull ψA) ((M.pull ψB).pull ΦV.left) := by
      have hS := GlobalTheory.isSemiAbelian_of_isAbelianScheme AV hAV
      refine GlobalTheory.Poinc.Eq8.StalkPow.lbIso_of_generic_fibre V AV hS _ _ (pull_isLB hL _)
        (pull_isLB (pull_isLB hM _) _) ?_
      have P := hκA.1
      have e : pullback.fst AV.hom (Out.jK V) = P.isoPullback.inv ≫ κA := by simp
      rw [e]
      set u := P.isoPullback.inv
      have i0 := lbIso_pull_pull R.iso (u ≫ pA)
      have hm := pull_isLB hM R.φB
      have eqM : ((u ≫ pA) ≫ R.Φ.left) ≫ R.φB = ((u ≫ κA) ≫ ΦV.left) ≫ ψB := by
        calc ((u ≫ pA) ≫ R.Φ.left) ≫ R.φB = u ≫ (ΦK.left ≫ pB) ≫ R.φB := by
                rw [hΦK1]; simp only [Category.assoc]
            _ = u ≫ ΦK.left ≫ κB ≫ ψB := by rw [hκB1]; simp only [Category.assoc]
            _ = ((u ≫ κA) ≫ ΦV.left) ≫ ψB := by
                rw [← Category.assoc ΦK.left, hΦV1]; simp only [Category.assoc]
      refine LBIso.trans (B := L.pull ((u ≫ κA) ≫ ψA)) ?_ ?_ ?_
        (GlobalTheory.OriginCohom.lbIso_pull_pull_comp hL _ _) ?_
      rotate_left 3
      refine LBIso.trans (B := L.pull ((u ≫ pA) ≫ R.φA)) ?_ ?_ ?_
        (lbIso_pull_eq hL (by simp only [Category.assoc, hκA1])) ?_
      rotate_left 3
      refine LBIso.trans (B := (L.pull R.φA).pull (u ≫ pA)) ?_ ?_ ?_
        (LBIso.symm (GlobalTheory.OriginCohom.lbIso_pull_pull_comp hL _ _)) ?_
      rotate_left 3
      refine LBIso.trans (B := ((M.pull R.φB).pull R.Φ.left).pull (u ≫ pA)) ?_ ?_ ?_ i0 ?_
      rotate_left 3
      refine LBIso.trans (B := (M.pull R.φB).pull ((u ≫ pA) ≫ R.Φ.left)) ?_ ?_ ?_
        (GlobalTheory.OriginCohom.lbIso_pull_pull_comp hm _ _) ?_
      rotate_left 3
      refine LBIso.trans (B := M.pull (((u ≫ pA) ≫ R.Φ.left) ≫ R.φB)) ?_ ?_ ?_
        (GlobalTheory.OriginCohom.lbIso_pull_pull_comp hM _ _) ?_
      rotate_left 3
      refine LBIso.trans (B := M.pull (((u ≫ κA) ≫ ΦV.left) ≫ ψB)) ?_ ?_ ?_
        (lbIso_pull_eq hM eqM) ?_
      rotate_left 3
      refine LBIso.symm (LBIso.trans (B := (M.pull ψB).pull ((u ≫ κA) ≫ ΦV.left)) ?_ ?_ ?_
        (GlobalTheory.OriginCohom.lbIso_pull_pull_comp (pull_isLB hM _) _ _) ?_)
      rotate_left 3
      exact GlobalTheory.OriginCohom.lbIso_pull_pull_comp hM _ _
      all_goals (first | assumption | (apply pull_isLB; first | assumption | (apply pull_isLB; first | assumption | (apply pull_isLB; assumption))))

    obtain ⟨g, ⟨hg, χA, χB, hχA, hχB, hχA1, hχB1, hχΦ⟩, -⟩ :=
      R.rep (Sp V) y AV BV ψA ψB ΦV hVA hVB hΦV iso
    have isoK : LBIso (L.pull (pA ≫ R.φA)) ((M.pull (pB ≫ R.φB)).pull ΦK.left) := by
      have hm := pull_isLB hM R.φB
      refine LBIso.trans (B := (L.pull R.φA).pull pA) ?_ ?_ ?_
        (LBIso.symm (GlobalTheory.OriginCohom.lbIso_pull_pull_comp hL _ _)) ?_
      rotate_left 3
      refine LBIso.trans (B := ((M.pull R.φB).pull R.Φ.left).pull pA) ?_ ?_ ?_
        (lbIso_pull_pull R.iso pA) ?_
      rotate_left 3
      refine LBIso.trans (B := (M.pull R.φB).pull (pA ≫ R.Φ.left)) ?_ ?_ ?_
        (GlobalTheory.OriginCohom.lbIso_pull_pull_comp hm _ _) ?_
      rotate_left 3
      refine LBIso.trans (B := M.pull ((pA ≫ R.Φ.left) ≫ R.φB)) ?_ ?_ ?_
        (GlobalTheory.OriginCohom.lbIso_pull_pull_comp hM _ _) ?_
      rotate_left 3
      refine LBIso.trans (B := M.pull (ΦK.left ≫ pB ≫ R.φB)) ?_ ?_ ?_
        (lbIso_pull_eq hM (by rw [← Category.assoc, hΦK1])) ?_
      rotate_left 3
      exact LBIso.symm (GlobalTheory.OriginCohom.lbIso_pull_pull_comp hM _ _)
      all_goals (first | assumption | (apply pull_isLB; first | assumption | (apply pull_isLB; first | assumption | (apply pull_isLB; assumption))))
    obtain ⟨g0, -, huniq⟩ := R.rep (Sp (FractionRing V)) (x ≫ R.π) AK BK (pA ≫ R.φA) (pB ≫ R.φB) ΦK hKA hKB hΦK isoK
    have e1 : x = g0 := huniq x ⟨rfl, pA, pB, hK1A, hK1B, rfl, rfl, hΦK1⟩
    have e2 : Out.jK V ≫ g = g0 := huniq _ ⟨by rw [Category.assoc, hg, hxy], κA ≫ χA, κB ≫ χB,
      hκA.comp hχA, hκB.comp hχB,
      by rw [Category.assoc, hχA1, hκA1], by rw [Category.assoc, hχB1, hκB1],
      by rw [← Category.assoc, hΦV1, Category.assoc, hχΦ, Category.assoc]⟩
    exact ⟨g, e2.trans e1.symm, hg⟩
  haveI : UniversallyClosed R.π := UniversallyClosed.of_valuativeCriterion R.π hex
  exact IsProper.mk

end GlobalTheory.EndLoc.HomFixProper
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedHomWithFixedPullbackScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedHomWithFixedPullbackScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc.HomFixUnr

theorem base_eq {X Y Z Y' Z' : Scheme.{0}} (b : Y ⟶ X) (c : Z ⟶ Y) (b' : Y' ⟶ X) (c' : Z' ⟶ Y')
    (h : Z' ⟶ Z) (e : c' ≫ b' = h ≫ c ≫ b) (y : Z') : b' (c' y) = b (c (h y)) := by
  have := congrArg (fun k => k.base y) e
  simpa only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] using this

def chartPullPullPull {X Y Z Y' Z' : Scheme.{0}} (M : LB X) (b : Y ⟶ X) (c : Z ⟶ Y) (b' : Y' ⟶ X) (c' : Z' ⟶ Y')
    (h : Z' ⟶ Z) (e : c' ≫ b' = h ≫ c ≫ b) : ChartPull ((M.pull b').pull c') ((M.pull b).pull c) h where
  idx J := J
  le J y hy := by
    have h1 := mem_pull.1 (mem_pull.1 hy)
    show h y ∈ ((M.pull b).pull c).U J
    refine mem_pull.2 (mem_pull.2 ?_)
    rw [← base_eq b c b' c' h e y]; exact h1
  g y J J' hj hj' := by
    have hj2 : (𝟙 Z' ≫ c') y ∈ (M.pull b').U (J PUnit.unit) := mem_pull.1 hj
    have hj2' : (𝟙 Z' ≫ c') y ∈ (M.pull b').U (J' PUnit.unit) := mem_pull.1 hj'
    have hk : ∀ K : PUnit → PUnit → M.ι, y ∈ ((M.pull b').pull c').U K → h y ∈ ((M.pull b).pull c).U K := fun K hK =>
      mem_pull.2 (mem_pull.2 (by rw [← base_eq b c b' c' h e y]; exact mem_pull.1 (mem_pull.1 hK)))
    have hk2 : (h ≫ c) y ∈ (M.pull b).U (J PUnit.unit) := by
      have := mem_pull.1 (hk J hj); simpa using this
    have hk2' : (h ≫ c) y ∈ (M.pull b).U (J' PUnit.unit) := by
      have := mem_pull.1 (hk J' hj'); simpa using this
    rw [gm_pull_g (M.pull b') c' (𝟙 Z') y J J' hj hj', gm_pull_g M b' (𝟙 Z' ≫ c') y _ _ hj2 hj2',
      gm_pull_g (M.pull b) c h y J J' (hk J hj) (hk J' hj'), gm_pull_g M b (h ≫ c) y _ _ hk2 hk2']
    have e' : (𝟙 Z' ≫ c') ≫ b' = (h ≫ c) ≫ b := by rw [Category.id_comp, e, Category.assoc]
    rw [e']

theorem lbIso_pull_square {XA XB YA YB ZA ZB : Scheme.{0}} (L : LB XA) (M : LB XB) (φA : YA ⟶ XA) (φB : YB ⟶ XB)
    (Φ : YA ⟶ YB) (ψA : ZA ⟶ XA) (ψB : ZB ⟶ XB) (v : ZA ⟶ ZB) (χA : ZA ⟶ YA) (χB : ZB ⟶ YB)
    (hA : χA ≫ φA = ψA) (hB : χB ≫ φB = ψB) (hv : v ≫ χB = χA ≫ Φ)
    (H : LBIso (L.pull φA) ((M.pull φB).pull Φ)) : LBIso (L.pull ψA) ((M.pull ψB).pull v) :=
  LBIso.chartPull (chartPullSame L (fun _ => ψA) (fun _ => φA) (fun _ => 1) χA fun _ => hA.symm)
    (chartPullPullPull M φB Φ ψB v χA (by rw [← hB, ← Category.assoc, hv, Category.assoc])) H

end GlobalTheory.EndLoc.HomFixUnr

namespace GlobalTheory.EndLoc


open GlobalTheory.EndLoc.HomFixUnr in
theorem formallyUnramified_homFixRep : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B]
    [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (R : HomFixRep A B L M), IsAbelianScheme A → IsAbelianScheme B →
    FormallyUnramified R.π := by
  intro S A B _ _ _ _ L M Rp hA _
  refine FormallyUnramified.of_hom_ext _ fun R R₀ q hq hsq g₁ g₂ hi hg ↦ ?_
  let f : Spec R ⟶ S := g₁ ≫ Rp.π
  let AT : Over (Spec R) := (Over.pullback f).obj A
  let BT : Over (Spec R) := (Over.pullback f).obj B
  let ψA : AT.left ⟶ A.left := pullback.fst A.hom f
  let ψB : BT.left ⟶ B.left := pullback.fst B.hom f
  have hAT : IsGrpPullback AT A f ψA := isGrpPullback_pullback A f
  have hBT : IsGrpPullback BT B f ψB := isGrpPullback_pullback B f
  have hAbT : IsAbelianScheme AT := GlobalTheory.isAbelianScheme_pullback_obj f A hA
  have tr : ∀ (g : Spec R ⟶ Rp.H), g ≫ Rp.π = f → ∀ (G : Over S) [GrpObj G] (GH : Over Rp.H) [GrpObj GH]
      (φ : GH.left ⟶ G.left), IsGrpPullback GH G Rp.π φ →
      ∃ e : (Over.pullback f).obj G ≅ (Over.pullback g).obj GH, IsMonHom e.hom ∧
        IsGrpPullback ((Over.pullback f).obj G) GH g (e.hom.left ≫ pullback.fst GH.hom g) ∧
        (e.hom.left ≫ pullback.fst GH.hom g) ≫ φ = pullback.fst G.hom f := by
    intro g hgf G _ GH _ φ hG
    have h' : IsGrpPullback ((Over.pullback g).obj GH) G f (pullback.fst GH.hom g ≫ φ) :=
      ((isGrpPullback_pullback GH g).comp hG).congr hgf rfl
    obtain ⟨e, he, heφ⟩ := grpPullback_iso (isGrpPullback_pullback G f) h'
    haveI := he
    exact ⟨e, he, ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback GH g)).congr (Category.id_comp _) rfl,
      by rw [Category.assoc, heφ]⟩
  have build : ∀ g : Spec R ⟶ Rp.H, g ≫ Rp.π = f → ∃ (v : AT ⟶ BT) (χA : AT.left ⟶ Rp.AH.left)
      (χB : BT.left ⟶ Rp.BH.left), IsMonHom v ∧ IsGrpPullback AT Rp.AH g χA ∧ IsGrpPullback BT Rp.BH g χB ∧
        χA ≫ Rp.φA = ψA ∧ χB ≫ Rp.φB = ψB ∧ v.left ≫ χB = χA ≫ Rp.Φ.left := by
    intro g hgf
    obtain ⟨eA, heA, hpA, hφA⟩ := tr g hgf A Rp.AH Rp.φA Rp.pbA
    obtain ⟨eB, heB, hpB, hφB⟩ := tr g hgf B Rp.BH Rp.φB Rp.pbB
    haveI := heA
    haveI := heB
    haveI := Rp.hom
    have hie : eB.inv.left ≫ eB.hom.left = 𝟙 _ := by rw [← Over.comp_left, eB.inv_hom_id, Over.id_left]
    refine ⟨eA.hom ≫ (Over.pullback g).map Rp.Φ ≫ eB.inv, _, _, inferInstance, hpA, hpB, hφA, hφB, ?_⟩
    have hm : ((Over.pullback g).map Rp.Φ).left ≫ pullback.fst Rp.BH.hom g =
        pullback.fst Rp.AH.hom g ≫ Rp.Φ.left := pullback.lift_fst _ _ _
    simp only [Over.comp_left, Category.assoc]
    rw [reassoc_of% hie, hm]
  obtain ⟨v₁, χA₁, χB₁, hv₁, hpA₁, hpB₁, hχA₁, hχB₁, hχ₁⟩ := build g₁ rfl
  obtain ⟨v₂, χA₂, χB₂, hv₂, hpA₂, hpB₂, hχA₂, hχB₂, hχ₂⟩ := build g₂ hg.symm
  let I : Ideal R := RingHom.ker q.hom
  have hI : IsNilpotent I := ⟨2, hsq⟩
  let j : Sp (R ⧸ I) ⟶ Sp R := spMap (Ideal.Quotient.mk I)
  have hj : j ≫ g₁ = j ≫ g₂ := by
    let ε : (R ⧸ I) ≃+* R₀ := RingHom.quotientKerEquivOfSurjective hq
    have hε : Spec.map q = Spec.map (CommRingCat.ofHom ε.toRingHom) ≫ j := by
      rw [← Spec.map_comp]
      congr 1
    haveI : IsIso (CommRingCat.ofHom ε.toRingHom) := ε.toCommRingCatIso.isIso_hom
    rw [hε, Category.assoc, Category.assoc] at hi
    exact (cancel_epi _).1 hi
  have hχA : pullback.fst AT.hom j ≫ χA₁ = pullback.fst AT.hom j ≫ χA₂ := by
    apply Rp.pbA.1.hom_ext
    · rw [Category.assoc, Category.assoc, hχA₁, hχA₂]
    · rw [Category.assoc, Category.assoc, hpA₁.1.w, hpA₂.1.w, pullback.condition_assoc, pullback.condition_assoc, hj]
  have hv : v₁ = v₂ := by
    refine GlobalTheory.NilRigidity.eq_of_pullback_quotient_eq I hI AT BT hAbT v₁ v₂ ?_
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [show ((Over.pullback j).map v₁).left ≫ pullback.fst BT.hom j =
          pullback.fst AT.hom j ≫ v₁.left from pullback.lift_fst _ _ _,
        show ((Over.pullback j).map v₂).left ≫ pullback.fst BT.hom j =
          pullback.fst AT.hom j ≫ v₂.left from pullback.lift_fst _ _ _]
      apply hBT.1.hom_ext
      · calc (pullback.fst AT.hom j ≫ v₁.left) ≫ ψB
            = pullback.fst AT.hom j ≫ v₁.left ≫ χB₁ ≫ Rp.φB := by rw [hχB₁, Category.assoc]
          _ = pullback.fst AT.hom j ≫ χA₁ ≫ Rp.Φ.left ≫ Rp.φB := by rw [reassoc_of% hχ₁]
          _ = pullback.fst AT.hom j ≫ χA₂ ≫ Rp.Φ.left ≫ Rp.φB := by rw [reassoc_of% hχA]
          _ = pullback.fst AT.hom j ≫ v₂.left ≫ χB₂ ≫ Rp.φB := by rw [reassoc_of% hχ₂]
          _ = (pullback.fst AT.hom j ≫ v₂.left) ≫ ψB := by rw [hχB₂, Category.assoc]
      · rw [Category.assoc, Category.assoc, Over.w v₁, Over.w v₂]
    · rw [show ((Over.pullback j).map v₁).left ≫ pullback.snd BT.hom j =
          pullback.snd AT.hom j from pullback.lift_snd _ _ _,
        show ((Over.pullback j).map v₂).left ≫ pullback.snd BT.hom j =
          pullback.snd AT.hom j from pullback.lift_snd _ _ _]
  have hL : LBIso (L.pull ψA) ((M.pull ψB).pull v₁.left) :=
    lbIso_pull_square L M Rp.φA Rp.φB Rp.Φ.left ψA ψB v₁.left χA₁ χB₁ hχA₁ hχB₁ hχ₁ Rp.iso
  obtain ⟨g, -, hg'⟩ := Rp.rep (Spec R) f AT BT ψA ψB v₁ hAT hBT hv₁ hL
  have e1 := hg' g₁ ⟨rfl, χA₁, χB₁, hpA₁, hpB₁, hχA₁, hχB₁, hχ₁⟩
  have e2 := hg' g₂ ⟨hg.symm, χA₂, χB₂, hpA₂, hpB₂, hχA₂, hχB₂, by rw [hv]; exact hχ₂⟩
  rw [e1, e2]

end GlobalTheory.EndLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedHomWithFixedPullbackSchemeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formallyUnramified_homWithFixedPullback_scheme : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (R : HomFixRep A B L M), IsAbelianScheme A → IsAbelianScheme B → FormallyUnramified R.π := by
  first | exact @GlobalTheory.EndLoc.formallyUnramified_homFixRep | exact GlobalTheory.EndLoc.formallyUnramified_homFixRep | (intros; apply GlobalTheory.EndLoc.formallyUnramified_homFixRep; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteOfIsProperOfFormallyUnramified
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.PropFin

theorem isFinite_of_isProper_of_formallyUnramified :
    ∀ (X S : Scheme.{0}) (f : X ⟶ S) [IsLocallyNoetherian S],
      IsProper f → FormallyUnramified f → IsFinite f := by
  intro X S f _ hp hu
  have hlqf : LocallyQuasiFinite f := by
    refine ⟨fun {U} hU {V} hV e => ?_⟩
    have h₁ := f.formallyUnramified_appLE hU hV e
    have h₂ := f.finiteType_appLE hU hV e
    algebraize [(f.appLE U V e).hom]
    exact inferInstanceAs (Algebra.QuasiFinite _ _)
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end GlobalTheory.PropFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteUnramifiedRepresentingPolarizedHoms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc.HomFixFinite

theorem exists_finite_unramified : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → Out.RelAmple A L → Out.RelAmple B M → ∃ R : HomFixRep A B L M, IsFinite R.π ∧ FormallyUnramified R.π := by
  intro S _ A B _ _ _ _ L M hA hB hL hM rA rB aA aB
  obtain ⟨R, hqc, hsep, hlft⟩ := GlobalTheory.T.exists_finiteType_representing_polarizedHoms_locNoeth S A B L M hA hB hL hM rA rB aA aB
  have hpr : IsProper R.π :=
    GlobalTheory.EndLoc.HomFixProper.isProper_of_finiteType S A B L M R hA hB hL hM rA rB hqc hsep hlft
  have hun : FormallyUnramified R.π := GlobalTheory.T.formallyUnramified_homWithFixedPullback_scheme S A B L M R hA hB
  exact ⟨R, GlobalTheory.PropFin.isFinite_of_isProper_of_formallyUnramified _ _ R.π hpr hun, hun⟩

end GlobalTheory.EndLoc.HomFixFinite
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteUnramifiedRepresentingPolarizedHomsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_unramified_representing_polarizedHoms : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → Out.RelAmple A L → Out.RelAmple B M → ∃ R : HomFixRep A B L M, IsFinite R.π ∧ FormallyUnramified R.π := by
  first | (exact @GlobalTheory.EndLoc.HomFixFinite.exists_finite_unramified) | (exact GlobalTheory.EndLoc.HomFixFinite.exists_finite_unramified) | (intros; apply GlobalTheory.EndLoc.HomFixFinite.exists_finite_unramified  <;> assumption)
end
