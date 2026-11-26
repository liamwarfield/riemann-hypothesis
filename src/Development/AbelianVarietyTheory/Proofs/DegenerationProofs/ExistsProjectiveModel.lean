module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfPullbackId
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOpenNonzeroLocusOfUniversallyClosed

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.GenSpread

set_option backward.isDefEq.respectTransparency false

section Bundles

variable {W X Y : Scheme.{0}}

theorem lbIso_pullback {L M : LB X} (h : LBIso L M) (j : Y ⟶ X) : LBIso (L.pull j) (M.pull j) :=
  LBIso.chartPull (GlobalTheory.chartPullPull L j) (GlobalTheory.chartPullPull M j) h

theorem lbIso_pull_pull {L : LB X} (hL : L.IsLB) {a : Y ⟶ X} (j : W ⟶ Y) {a' : W ⟶ X} (ha : a' = j ≫ a) :
    LBIso (L.pull a') ((L.pull a).pull j) :=
  LBIso.chartPull (chartPullSame L _ _ _ j fun _ => ha) (GlobalTheory.chartPullPull _ j) (lbIso_refl (pull_isLB hL a))

theorem lbIso_pull_comp {Z : Scheme.{0}} {L : LB X} {M : LB Z} {a : Y ⟶ X} {b : Y ⟶ Z} (j : W ⟶ Y) {a' : W ⟶ X}
    {b' : W ⟶ Z} (ha : a' = j ≫ a) (hb : b' = j ≫ b) (h : LBIso (L.pull a) (M.pull b)) :
    LBIso (L.pull a') (M.pull b') :=
  LBIso.chartPull (chartPullSame L _ _ _ j fun _ => ha) (chartPullSame M _ _ _ j fun _ => hb) h

theorem lbIso_pull_of_lbIso {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : W ⟶ Y) {a' : W ⟶ X}
    (ha : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (GlobalTheory.chartPullPull M j) (chartPullSame L _ _ _ j fun _ => ha) h

end Bundles

variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem exists_forall_mem {V : (Sp R).Opens} (hV : genericPoint (Sp R) ∈ V) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ z : Sp R', spMap g z ∈ V := by
  obtain ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩, ha, hle⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hV V.isOpen
  refine ⟨a, ?_, fun R' _ g hg z => hle ?_⟩
  · rintro rfl
    simp at ha
  · exact fun h => z.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h hg)

theorem exists_forall_notMem {C : Set (Sp R)} (hC : IsClosed C)
    (h : ∀ z : Sp K, spMap (algebraMap R K) z ∉ C) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ z : Sp R', spMap g z ∉ C := by
  have hg : genericPoint (Sp R) ∈ Set.range (spMap (algebraMap R K)) := by
    rw [(IsGenericPointHom.fractionField R K).range_eq]; rfl
  obtain ⟨z, hz⟩ := hg
  exact exists_forall_mem (V := ⟨Cᶜ, hC.isOpen_compl⟩) (hz ▸ h z)

theorem exists_isPullback_stalk {Y Y₀ : Scheme.{0}} {p : Y ⟶ Sp R} {φ : Y₀ ⟶ Y} {p₀ : Y₀ ⟶ Sp K}
    (h : IsPullback φ p₀ p (spMap (algebraMap R K))) :
    ∃ p₁, IsPullback φ p₁ p ((Sp R).fromSpecStalk (genericPoint (Sp R))) := by
  obtain ⟨e, he⟩ := IsGenericPointHom.fractionField R K
  refine ⟨p₀ ≫ e.hom, h.of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _) (by simp) (by simp) (by simp) ?_⟩
  simpa using he.symm

theorem exists_lift_open {S S' Y Y' : Scheme.{0}} (p : Y ⟶ S) (V : S.Opens) {π : Y' ⟶ Y} {p' : Y' ⟶ S'}
    {t : S' ⟶ S} (w : π ≫ p = p' ≫ t) (ht : ∀ z, t z ∈ V) :
    ∃ l : Y' ⟶ pullback p V.ι, l ≫ pullback.fst p V.ι = π := by
  refine ⟨pullback.lift π (IsOpenImmersion.lift V.ι (p' ≫ t) ?_) ?_, pullback.lift_fst _ _ _⟩
  · rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    exact ht _
  · exact w.trans (IsOpenImmersion.lift_fac _ _ _).symm

theorem exists_hom {Y X Y₀ : Scheme.{0}} (p : Y ⟶ Sp R) [QuasiCompact p] [QuasiSeparated p] (q : X ⟶ Sp R)
    [LocallyOfFinitePresentation q] {φ : Y₀ ⟶ Y} {p₀ : Y₀ ⟶ Sp K}
    (h : IsPullback φ p₀ p (spMap (algebraMap R K))) (u₀ : Y₀ ⟶ X) (hu : u₀ ≫ q = φ ≫ p) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
      ∀ (Y' : Scheme.{0}) (π : Y' ⟶ Y) (p' : Y' ⟶ Sp R'), π ≫ p = p' ≫ spMap g →
        ∃ u : Y' ⟶ X, u ≫ q = π ≫ p ∧ ∀ φ' : Y₀ ⟶ Y', φ' ≫ π = φ → φ' ≫ u = u₀ := by
  obtain ⟨p₁, h₁⟩ := exists_isPullback_stalk h
  obtain ⟨V, hV, -, w, u, hw, hwu, hq⟩ := StalkLimit.exists_spread h₁ q u₀ hu
  obtain ⟨a, ha, H⟩ := exists_forall_mem hV
  refine ⟨a, ha, fun R' _ g hg Y' π p' e => ?_⟩
  obtain ⟨l, hl⟩ := exists_lift_open p V e (H R' g hg)
  refine ⟨l ≫ u, by rw [Category.assoc, hq, reassoc_of% hl], fun φ' hφ' => ?_⟩
  have : φ' ≫ l = w := by
    rw [← cancel_mono (pullback.fst p V.ι), Category.assoc, hl, hφ', hw]
  rw [reassoc_of% this, hwu]

theorem exists_lbIso {Y Y₀ : Scheme.{0}} (p : Y ⟶ Sp R) [QuasiCompact p] [QuasiSeparated p]
    {φ : Y₀ ⟶ Y} {p₀ : Y₀ ⟶ Sp K} (h : IsPullback φ p₀ p (spMap (algebraMap R K))) {M N : LB Y}
    (hM : M.IsLB) (hN : N.IsLB) (H : LBIso (M.pull φ) (N.pull φ)) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
      ∀ (Y' : Scheme.{0}) (π : Y' ⟶ Y) (p' : Y' ⟶ Sp R'), π ≫ p = p' ≫ spMap g →
        LBIso (M.pull π) (N.pull π) := by
  obtain ⟨p₁, h₁⟩ := exists_isPullback_stalk h
  obtain ⟨hc⟩ := StalkLimit.nonempty_isLimit h₁
  obtain ⟨V₀⟩ : Nonempty (StalkLimit.AffNhd (genericPoint (Sp R))) := IsCofiltered.nonempty
  have : IsAffine V₀.1.toScheme := V₀.2.2
  have : CompactSpace ((StalkLimit.diagram _ p).obj V₀) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd p V₀.1.ι)
  have : QuasiSeparatedSpace ((StalkLimit.diagram _ p).obj V₀) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd p V₀.1.ι)
  let ι₀ : (StalkLimit.diagram _ p).obj V₀ ⟶ Y := pullback.fst p V₀.1.ι
  have e₀ : φ = (StalkLimit.cone h₁).π.app V₀ ≫ ι₀ := (StalkLimit.cone_π_fst h₁ V₀).symm
  obtain ⟨V, i, HV⟩ := exists_lbIso_of_isLimit (StalkLimit.diagram _ p) (fun V => (StalkLimit.cone h₁).π.app V)
    (fun i => (StalkLimit.cone h₁).w i) hc (M.pull ι₀) (N.pull ι₀) (pull_isLB hM _) (pull_isLB hN _)
    (LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) (pull_isLB (pull_isLB hN _) _)
      (lbIso_pull_pull hM _ e₀).symm
      (LBIso.trans (pull_isLB hM _) (pull_isLB hN _) (pull_isLB (pull_isLB hN _) _) H (lbIso_pull_pull hN _ e₀)))
  have e₁ : pullback.fst p V.1.ι = (StalkLimit.diagram _ p).map i ≫ ι₀ := (StalkLimit.diagram_map_fst _ p i).symm
  have HV' : LBIso (M.pull (pullback.fst p V.1.ι)) (N.pull (pullback.fst p V.1.ι)) :=
    LBIso.trans (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hN _) (lbIso_pull_pull hM _ e₁)
      (LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB (pull_isLB hN _) _) (pull_isLB hN _) HV
        (lbIso_pull_pull hN _ e₁).symm)
  obtain ⟨a, ha, Ha⟩ := exists_forall_mem V.2.1
  refine ⟨a, ha, fun R' _ g hg Y' π p' e => ?_⟩
  obtain ⟨l, hl⟩ := exists_lift_open p V.1 e (Ha R' g hg)
  exact lbIso_pull_comp l hl.symm hl.symm HV'

theorem exists_projective_model {X₀ : Scheme.{0}} (f₀ : X₀ ⟶ Sp K) [IsProper f₀] {L₀ : LB X₀}
    (hL : IsAmpleLB L₀) (hL' : L₀.IsLB) :
    ∃ (X : Scheme.{0}) (f : X ⟶ Sp R) (φ : X₀ ⟶ X) (H : LB X) (N : ℕ), IsProper f ∧
      IsPullback φ f₀ f (spMap (algebraMap R K)) ∧ H.IsLB ∧ IsAmpleLB H ∧ 1 ≤ N ∧ LBIso (lbPow L₀ N) (H.pull φ) := by
  obtain ⟨N, hN, M, s, hs⟩ := hL.exists_veryAmpleBy f₀
  obtain ⟨hs, hc⟩ := (ProjSpace.veryAmpleBy_iff f₀ s).1 hs
  let c := ProjSpace.toProj f₀ s hs
  let u := ProjSpace.baseChange M (algebraMap R K)
  have hu := ProjSpace.isPullback_baseChange M (algebraMap R K)
  have : Flat (spMap (algebraMap R K)) := flat_specMap_localization (nonZeroDivisors R) K
  have : Mono (spMap (algebraMap R K)) := mono_specMap_localization (nonZeroDivisors R) K
  have : Flat u := MorphismProperty.of_isPullback (P := @Flat) hu.flip inferInstance
  have : Mono u := MorphismProperty.of_isPullback (P := .monomorphisms _) hu.flip
    (inferInstanceAs (Mono (spMap (algebraMap R K))))
  have : QuasiCompact u := MorphismProperty.of_isPullback (P := @QuasiCompact) hu.flip inferInstance
  have hp := isPullback_toImage_of_isClosedImmersion (c ≫ u) c u rfl
  have := isProper_str R M
  refine ⟨(c ≫ u).image, (c ≫ u).imageι ≫ PSpace.str R M, (c ≫ u).toImage,
    (ProjSpace.O1 R M).pull (c ≫ u).imageι, N, inferInstance, ?_, pull_isLB (ProjSpace.O1_isLB R M) _,
    (isAmple_projective_O_one R M).pull_of_isClosedImmersion _, hN, ?_⟩
  · have := hp.flip.paste_vert hu
    rwa [ProjSpace.toProj_str] at this
  · have h1 {Y : Scheme.{0}} (F : Y ⟶ PSpace R M) := pull_isLB (ProjSpace.O1_isLB R M) F
    refine LBIso.trans (isLB_lbPow hL' _) (pull_isLB (ProjSpace.O1_isLB K M) c) (pull_isLB (h1 _) _)
      (ProjSpace.lbIso_pullback_O1_toProj f₀ s hs).symm ?_
    refine LBIso.trans (pull_isLB (ProjSpace.O1_isLB K M) c) (h1 (c ≫ u)) (pull_isLB (h1 _) _)
      (lbIso_pull_of_lbIso (ProjSpace.lbIso_pull_O1 M (algebraMap R K)).symm c rfl) ?_
    exact lbIso_pull_pull (ProjSpace.O1_isLB R M) _ (Scheme.Hom.toImage_imageι _).symm

theorem exists_isAmpleLB {X X₀ : Scheme.{0}} (f : X ⟶ Sp R) [QuasiCompact f] [QuasiSeparated f]
    {φ : X₀ ⟶ X} {f₀ : X₀ ⟶ Sp K} (h : IsPullback φ f₀ f (spMap (algebraMap R K))) {L H : LB X} {L₀ : LB X₀}
    (hL : L.IsLB) (hH : H.IsLB) (hL₀ : L₀.IsLB) (hA : IsAmpleLB H) {N : ℕ} (hN : 1 ≤ N)
    (e : LBIso L₀ (L.pull φ)) (e' : LBIso (lbPow L₀ N) (H.pull φ)) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
      ∀ (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Sp R'), IsPullback π f' f (spMap g) →
        IsAmpleLB (L.pull π) := by
  obtain ⟨a, ha, Ha⟩ := exists_lbIso f h (isLB_lbPow hL N) hH
    (LBIso.trans (pull_isLB (isLB_lbPow hL N) _) (isLB_lbPow (pull_isLB hL _) N) (pull_isLB hH _)
      (lbIso_lbPow_pull hL φ N).symm
      (LBIso.trans (isLB_lbPow (pull_isLB hL _) N) (isLB_lbPow hL₀ N) (pull_isLB hH _) (lbIso_lbPow e N).symm e'))
  refine ⟨a, ha, fun R' _ g hg X' π f' hp => ?_⟩
  have : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) hp.flip inferInstance
  refine (isAmpleLB_pow_iff (pull_isLB hL π) hN).1 ((hA.pull_of_isAffineHom π).of_lbIso
    (isLB_lbPow (pull_isLB hL _) N) ?_)
  exact LBIso.trans (isLB_lbPow (pull_isLB hL _) N) (pull_isLB (isLB_lbPow hL N) _) (pull_isLB hH _)
    (lbIso_lbPow_pull hL π N) (Ha R' g hg X' π f' hp.w)

end GlobalTheory.GenSpread
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericPointMemModuliOfMeetsAbelianLocus
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericPointMemModuliOfMeetsAbelianLocus
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory.LN.GenericPoint

theorem exists_extend {F K : Type} [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F] [Field K] [CharZero K]
    (V : ValuationSubring F) (g : V →+* K) : ∃ g' : F →+* K, g'.comp V.subtype = g := by
  have hinj : Function.Injective g := by
    rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
    intro a ha
    by_contra h0
    have hF : IsAlgebraic ℤ (a : F) :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic _)
    have hV : IsAlgebraic ℤ a :=
      (isAlgebraic_algHom_iff (V.subtype.toIntAlgHom) Subtype.val_injective).1 hF
    refine Ideal.comap_ne_bot_of_algebraic_mem h0 ha hV (eq_bot_iff.2 fun n hn => ?_)
    have e : (n : K) = 0 := by simpa using hn
    exact_mod_cast e
  exact ⟨IsFractionRing.lift hinj, RingHom.ext fun a => IsFractionRing.lift_algebraMap hinj a⟩

theorem jK_mem {R : Type} [CommRing R] [IsDomain R] {U : Set (Sp R)} (hU : IsOpen U) (h : U.Nonempty)
    (q : Sp (FractionRing R)) : jK R q ∈ U := by
  obtain ⟨x, hx⟩ := h
  refine Specializes.mem_open (x := jK R q) (y := x) ?_ hU hx
  refine (PrimeSpectrum.le_iff_specializes (R := R) _ _).1 fun a ha => ?_
  have hq : q.asIdeal = ⊥ := (Ideal.eq_bot_or_top q.asIdeal).resolve_right q.isPrime.ne_top
  have h1 : algebraMap R (FractionRing R) a ∈ q.asIdeal := ha
  rw [hq, Ideal.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))] at h1
  rw [h1]; exact Ideal.zero_mem _

theorem lbIso_pull {W X Y : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : W ⟶ Y)
    {a' : W ⟶ X} (ha : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (Geo.Tor.chartPullPull M j j rfl) (chartPullSame L _ _ _ j fun _ => ha) h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem lbIso_of_sabMap {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) :
    LBIso t'.PP.L (t.PP.L.pull m.φ) := by
  obtain ⟨w, hw, -⟩ := m.lin
  exact ⟨w, hw⟩

theorem polAt_of_lift {X S Z : Scheme.{0}} {T : SAB H X} {t : SAB H S} {t' : SAB H Z} {ξ : S ⟶ X} {j : Z ⟶ X}
    (m : SABMap t T ξ) (m' : SABMap t' T j) (hp : IsProper t'.G.hom) (hA : RelAmple t'.G t'.PP.L)
    (hK : KTriv t'.G t'.PP.L) {K : Type} [Field K] (x : Sp K ⟶ S) (y : Sp K ⟶ Z) (h : y ≫ j = x ≫ ξ) : PolAt t x := by
  have g₁ : IsGrpPullback ((Over.pullback x).obj t.G) T.G (x ≫ ξ) (pullback.fst t.G.hom x ≫ m.φ) :=
    (isGrpPullback_pullback t.G x).comp m.cart
  have w : (pullback.fst t.G.hom x ≫ m.φ) ≫ T.G.hom = (pullback.snd t.G.hom x ≫ y) ≫ j :=
    g₁.1.w.trans (by rw [Category.assoc, h]; rfl)
  obtain ⟨ψ, h₁, h₂⟩ : ∃ ψ : pullback t.G.hom x ⟶ t'.G.left,
      ψ ≫ m'.φ = pullback.fst t.G.hom x ≫ m.φ ∧ ψ ≫ t'.G.hom = pullback.snd t.G.hom x ≫ y :=
    ⟨_, m'.cart.1.lift_fst _ _ w, m'.cart.1.lift_snd _ _ w⟩
  have g₂ : IsGrpPullback ((Over.pullback x).obj t.G) t'.G y ψ :=
    m'.cart.cancel (g₁.congr h.symm h₁.symm) h₂
  have e : LBIso (t.PP.L.pull (pullback.fst t.G.hom x)) (t'.PP.L.pull ψ) :=
    LBIso.trans (pull_isLB t.PP.isLB _) (pull_isLB T.PP.isLB _) (pull_isLB t'.PP.isLB _)
      (lbIso_pull (lbIso_of_sabMap m) _ rfl) (lbIso_pull (lbIso_of_sabMap m') _ h₁.symm).symm
  have hp' : IsProper (pullback.snd t.G.hom x) := MorphismProperty.of_isPullback (P := @IsProper) g₂.1 hp
  have hq := amplePt Z K y t'.G ((Over.pullback x).obj t.G) ψ g₂ t'.PP.L (t.PP.L.pull (pullback.fst t.G.hom x))
    t'.PP.isLB (pull_isLB t.PP.isLB (pullback.fst t.G.hom x)) e hA hK
  exact ⟨hp', hq.1, hq.2⟩

end GlobalTheory.LN.GenericPoint


open GlobalTheory.LN.GenericPoint in
theorem GlobalTheory.LN.generic_point_of_meets_abLocus : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (p : ℕ), Y.LevelStructureConditions p → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (ξ : Sp R ⟶ Y.X) (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ), (ξ ⁻¹' abLocus Y.t.G).Nonempty → (∃ y : Sp (FractionRing R) ⟶ Xo.XF c, y ≫ Y.j = jK R ≫ ξ) ∧ PolAt t (jK R) ∧ ξ ⁻¹' abLocus Y.t.G = abLocus t.G := by
  intro _ _ E _ _ _ H D l Xo c W₀ Y p ⟨_, _, _, ⟨U, hU, _⟩, _⟩ R _ _ _ ξ t m hne
  have hop : IsOpen (ξ ⁻¹' abLocus Y.t.G) := by
    rw [← hU]; exact U.isOpen.preimage ξ.continuous
  have := c.fin
  obtain ⟨g, hg⟩ := exists_extend (K := FractionRing R) (c.V W₀) (Spec.preimage ((jK R ≫ ξ) ≫ Y.s)).hom
  have sq : (jK R ≫ ξ) ≫ Y.s = spMap g ≫ spMap (c.V W₀).subtype := by
    rw [← Geo.Tor.spMap_comp, hg]
    exact (Spec.map_preimage _).symm
  have := Y.jQ_open
  have hr : Set.range (pullback.lift _ _ sq) ⊆ Set.range Y.jQ := by
    rintro _ ⟨q, rfl⟩
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply]
    exact jK_mem hop hne q
  have hy : IsOpenImmersion.lift Y.jQ _ hr ≫ Y.j = jK R ≫ ξ := by
    rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]
  exact ⟨⟨_, hy⟩, polAt_of_lift m Y.m Y.oF.proper Y.oF.ample Y.oF.ktriv _ _ hy,
    Set.ext fun x => abLocus_pullback abLocusOne Y.t.semi m.cart.1 x⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericPointMemModuliOfMeetsAbelianLocusStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_point_mem_moduli_of_meets_abelian_locus : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (p : ℕ), Y.LevelStructureConditions p → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (ξ : Sp R ⟶ Y.X) (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ), (ξ ⁻¹' abLocus Y.t.G).Nonempty → (∃ y : Sp (FractionRing R) ⟶ Xo.XF c, y ≫ Y.j = jK R ≫ ξ) ∧ PolAt t (jK R) ∧ ξ ⁻¹' abLocus Y.t.G = abLocus t.G := by
  first | exact @GlobalTheory.LN.generic_point_of_meets_abLocus | exact GlobalTheory.LN.generic_point_of_meets_abLocus | (intros; apply GlobalTheory.LN.generic_point_of_meets_abLocus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalBasisAlong
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LN.PolFrames

variable {S : Scheme.{0}} (G : Over S) (L : LB G.left) (N : ℕ) {T T' : Over S} (h : T' ⟶ T)

theorem exists_pullSec [GrpObj G] (s : LB.Sec (LPow G L (N : ℤ) T)) : ∃ s' : LB.Sec (LPow G L (N : ℤ) T'),
    IsPullSec G L N (h ▷ G) (whiskerRight_snd h G) s s' ∧
    ∀ (z : (T' ⊗ G).left) (J), Good L z J →
      sval (L := L) (φ := fun _ : Fin 1 => (snd T' G).left) (ε := fun _ => (N : ℤ)) s' (𝟙 _) z J =
        sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) s (h ▷ G).left z J := by
  obtain ⟨s', h0, h1⟩ := SectionLimit.exists_pull (K := Fin 1) s (h ▷ G).left (fun _ => (snd T' G).left)
    (fun _ => congrArg CommaMorphism.left (whiskerRight_snd h G))
  exact ⟨s', fun j => h0 j _, fun z J hJ => (h1 _ _ z J hJ).trans (by rw [Category.id_comp])⟩

theorem sval_of_isPullSec [GrpObj G] {s : LB.Sec (LPow G L (N : ℤ) T)} {s' : LB.Sec (LPow G L (N : ℤ) T')}
    (hs : IsPullSec G L N (h ▷ G) (whiskerRight_snd h G) s s') (z : (T' ⊗ G).left) (J) (hJ : Good L z J) :
    sval (L := L) (φ := fun _ : Fin 1 => (snd T' G).left) (ε := fun _ => (N : ℤ)) s' (𝟙 _) z J =
      sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) s (h ▷ G).left z J := by
  obtain ⟨s'', h0, h1⟩ := exists_pullSec G L N h s
  obtain rfl : s' = s'' := SecOps.sec_ext fun j => (hs j).trans (h0 j).symm
  exact h1 z J hJ

theorem lin_iff [GrpObj G] (hL : L.IsLB) {n : ℕ} {b : Fin n → LB.Sec (LPow G L (N : ℤ) T)}
    {b' : Fin n → LB.Sec (LPow G L (N : ℤ) T')} (hb : ∀ i, IsPullSec G L N (h ▷ G) (whiskerRight_snd h G) (b i) (b' i))
    (c : Fin n → Γ(T'.left, ⊤)) (s : LB.Sec (LPow G L (N : ℤ) T')) :
    Lin G L N h b c s ↔ ∑ i, c i • (SecM.ofSec G (b' i) : SecM G L N T') = SecM.ofSec G s := by
  let σ := SectionLimit.linSec (fun i => (fst T' G).left.appTop.hom (c i)) b'
  have ev : ∀ j, (∑ i, c i • (SecM.ofSec G (b' i) : SecM G L N T')).1 j = σ.f j := fun j => by
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  have hv : Lin G L N h b c σ := fun z J hJ => by
    rw [SectionScalarValuation.sval_lin (s := σ) (fun i => (fst T' G).left.appTop.hom (c i)) b' (fun _ => rfl) (𝟙 _) z hJ]
    refine Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) ?_ (sval_of_isPullSec G L N h (hb i) z J hJ)
    exact (gs_pull (𝟙 _) (fst T' G).left z ⊤ trivial (c i)).trans (by rw [Category.id_comp])
  constructor
  · intro H
    refine Subtype.ext (funext fun j => (ev j).trans ?_)
    exact sec_ext_val hL (fun y J hJ => (hv y J hJ).trans (H y J hJ).symm) j
  · intro H
    obtain rfl : s = σ := SecOps.sec_ext fun j => (congrFun (congrArg Subtype.val H) j).symm.trans (ev j)
    exact hv

theorem basisAlong_iff [GrpObj G] (hL : L.IsLB) {n : ℕ} {b : Fin n → LB.Sec (LPow G L (N : ℤ) T)}
    {b' : Fin n → LB.Sec (LPow G L (N : ℤ) T')} (hb : ∀ i, IsPullSec G L N (h ▷ G) (whiskerRight_snd h G) (b i) (b' i)) :
    BasisAlong G L N h b ↔
      LinearIndependent Γ(T'.left, ⊤) (fun i => (SecM.ofSec G (b' i) : SecM G L N T')) ∧
        Submodule.span Γ(T'.left, ⊤) (Set.range fun i => (SecM.ofSec G (b' i) : SecM G L N T')) = ⊤ := by
  unfold BasisAlong
  simp only [lin_iff G L N h hL hb]
  constructor
  · intro H
    refine ⟨Fintype.linearIndependent_iffₛ.2 fun c c' e i => ?_, eq_top_iff.2 fun x _ => ?_⟩
    · exact congrFun ((H (SecM.toSec G (∑ i, c' i • (SecM.ofSec G (b' i) : SecM G L N T')))).unique e rfl) i
    · exact (Submodule.mem_span_range_iff_exists_fun _).2 (H (SecM.toSec G x)).exists
  · rintro ⟨hli, hsp⟩ s
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hsp.ge (Submodule.mem_top : SecM.ofSec G s ∈ ⊤))
    exact ⟨r, hr, fun r' hr' => funext fun i => Fintype.linearIndependent_iffₛ.1 hli _ _ (hr'.trans hr.symm) i⟩

theorem exists_local_basisAlong (hS : SecBaseChangeSt) [IsLocallyNoetherian S] (P : PolAV S) (hN : 1 ≤ N) (p : S) :
    ∃ V : S.Opens, p ∈ V ∧ ∃ b : Fin (N ^ P.g) → LB.Sec (LPow P.A P.L (N : ℤ) (Over.mk V.ι)),
      ∀ (R : Type) [CommRing R] (χ : Sp R ⟶ V.toScheme),
        BasisAlong P.A P.L N (Over.homMk χ rfl : Over.mk (χ ≫ V.ι) ⟶ Over.mk V.ι) b := by
  obtain ⟨V, hV, b, hb⟩ := hS S P N hN p
  have key : ∀ f : V.toScheme ⟶ S, (overRes (T := baseOver S) V).hom = f →
      ∃ b : Fin (N ^ P.g) → LB.Sec (LPow P.A P.L (N : ℤ) (Over.mk f)), ∀ (R : Type) [CommRing R] (χ : Sp R ⟶ V.toScheme),
        BasisAlong P.A P.L N (Over.homMk χ rfl : Over.mk (χ ≫ f) ⟶ Over.mk f) b := by
    rintro _ rfl
    refine ⟨b, fun R _ χ => ?_⟩
    choose b' hb' _ using fun i => exists_pullSec P.A P.L N (homAt χ) (b i)
    exact (basisAlong_iff P.A P.L N (homAt χ) P.isLB hb').2 (hb R χ b' hb')
  exact ⟨V, hV, key V.ι (Category.comp_id _)⟩

end GlobalTheory.LN.PolFrames
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericSectionExtendsNormal
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

noncomputable section

namespace GlobalTheory.ExtLB

open IsLocalRing

variable {X : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B]

abbrev cp (A : Type) [CommRing A] [IsLocalRing A] : Sp A := closedPoint A

theorem top_le [IsLocalRing A] (f : Sp A ⟶ X) {U : X.Opens} (h : f (cp A) ∈ U) : ⊤ ≤ f ⁻¹ᵁ U :=
  (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of A) f h).ge

def ev (f : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ f ⁻¹ᵁ U) : Γ(X, U) →+* A :=
  (f.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (.of A)).hom).hom

def toSt (y : Sp A) : A →+* (Sp A).presheaf.stalk y :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫ (Sp A).presheaf.germ ⊤ y trivial).hom

theorem gs_eq_toSt (f : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ f ⁻¹ᵁ U) (y : Sp A) (a : Γ(X, U)) :
    gs f y U a = toSt y (ev f U h a) := by
  rw [gs_eq f y U (h (Set.mem_univ y))]
  change _ = ((f.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (.of A)).hom) ≫ (Scheme.ΓSpecIso (.of A)).inv ≫
    (Sp A).presheaf.germ ⊤ y trivial).hom a
  rw [Category.assoc, Iso.hom_inv_id_assoc, Scheme.Hom.appLE, Category.assoc]
  exact (TopCat.Presheaf.germ_res_apply (Sp A).presheaf (homOfLE h) y (Set.mem_univ y) _).symm

theorem ev_comp (g : A →+* B) (f : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ f ⁻¹ᵁ U) (h' : ⊤ ≤ (spMap g ≫ f) ⁻¹ᵁ U)
    (a : Γ(X, U)) : ev (spMap g ≫ f) U h' a = g (ev f U h a) := by
  change _ = ((f.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (.of A)).hom) ≫ CommRingCat.ofHom g).hom a
  rw [Category.assoc, ← Scheme.ΓSpecIso_naturality, ← Category.assoc, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  exact congrArg (fun q => (q ≫ (Scheme.ΓSpecIso (.of B)).hom).hom a)
    (Scheme.Hom.appLE_comp_appLE (spMap g) f U ⊤ ⊤ h le_top).symm

theorem toSt_bijective [IsLocalRing A] : Function.Bijective (toSt (cp A)) := by
  have : toSt (cp A) = (stalkClosedPointIso (.of A)).inv.hom := by
    rw [toSt, ← ΓSpecIso_hom_stalkClosedPointIso_inv, Iso.inv_hom_id_assoc]
  rw [this]
  exact (stalkClosedPointIso (.of A)).symm.commRingCatIsoToRingEquiv.bijective

theorem isUnit_toSt [IsLocalRing A] (a : A) : IsUnit (toSt (cp A) a) ↔ IsUnit a :=
  MulEquiv.isUnit_map (RingEquiv.ofBijective _ toSt_bijective)

theorem exists_lift (g : A →+* B) (hg : Function.Injective g) (x : Sp B ⟶ X) {U : X.Opens} (hU : IsAffineOpen U)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (hr : ∀ a, ∃ r, g r = ev x U h a) : ∃ χ : Sp A ⟶ X, spMap g ≫ χ = x := by
  let e : A ≃+* g.range := RingEquiv.ofBijective g.rangeRestrict
    ⟨fun a b hab => hg (congrArg Subtype.val hab), g.rangeRestrict_surjective⟩
  let ρ : Γ(X, U) →+* A := e.symm.toRingHom.comp ((ev x U h).codRestrict g.range hr)
  have hρ : g.comp ρ = ev x U h := RingHom.ext fun a =>
    congrArg Subtype.val (e.apply_symm_apply ((ev x U h).codRestrict g.range hr a))
  refine ⟨Spec.map (CommRingCat.ofHom ρ) ≫ hU.fromSpec, ?_⟩
  have e₁ := IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top _) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at e₁
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ, ev, CommRingCat.ofHom_hom, Spec.map_comp,
    Category.assoc, e₁, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.id_comp]

variable {L : LB X}

theorem le_chart {x : Sp A ⟶ X} {i : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U i) :
    ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) := fun _ hy => Set.mem_iInter.2 fun _ => h hy

theorem le_chart' {x : Sp A ⟶ X} {i : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U i) :
    ⊤ ≤ (𝟙 (Sp A) : Sp A ⟶ Sp A) ⁻¹ᵁ LB.wchart L (fun _ : PUnit => x) (fun _ => i) :=
  fun _ hy => Set.mem_iInter.2 fun _ => h hy

def sv {d : ℕ} (s : H0 L d) (x : Sp A ⟶ X) {i : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U i) : A :=
  ev x _ (le_chart h) (s.f fun _ => i)

def gv {x : Sp A ⟶ X} (e : LB.Gen (L.pull x)) {i : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U i) : Aˣ :=
  Units.map (ev (𝟙 (Sp A)) _ (le_chart' h)).toMonoidHom (e.s fun _ => i)

theorem isUnit_sv [IsLocalRing A] {d : ℕ} (s : H0 L d) (x : Sp A ⟶ X) {i : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U i) :
    IsUnit (sv s x h) ↔ x (cp A) ∈ nonzeroLocus s := by
  rw [mem_nonzeroLocus_iff_pull s x (cp A) (k := fun _ => i) (le_chart h (Set.mem_univ _)), ← isUnit_toSt]
  exact (congrArg IsUnit (gs_eq_toSt x _ (le_chart h) _ _)).to_iff.symm

theorem gs_sv {d : ℕ} (s : H0 L d) (g : A →+* B) (x : Sp A ⟶ X) {i : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U i) (y : Sp B) :
    gs (spMap g ≫ x) y (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i)) (s.f fun _ => i) = toSt y (g (sv s x h)) :=
  (gs_eq_toSt (spMap g ≫ x) _ (fun z _ => le_chart h (Set.mem_univ (spMap g z))) y _).trans
    (congrArg _ (ev_comp g x _ (le_chart h) _ _))

theorem gm_gv (g : A →+* B) {x : Sp A ⟶ X} (e : LB.Gen (L.pull x)) {i : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U i) (y : Sp B) :
    (gm (spMap g) y (LB.wchart L (fun _ : PUnit => x) (fun _ => i)) (e.s fun _ => i)).val = toSt y (g (gv e h).val) := by
  have hm : ⊤ ≤ (spMap g ≫ 𝟙 _) ⁻¹ᵁ LB.wchart L (fun _ : PUnit => x) (fun _ => i) :=
    fun _ _ => le_chart' h (Set.mem_univ _)
  refine (gs_unit (spMap g) y (LB.wchart L (fun _ : PUnit => x) (fun _ => i)) (hm (Set.mem_univ y)) _).symm.trans ?_
  refine (congrArg (fun q => gs q y _ _) (Category.comp_id (spMap g)).symm).trans ?_
  exact (gs_eq_toSt _ _ hm _ _).trans (congrArg _ (ev_comp g (𝟙 _) _ (le_chart' h) _ _))

theorem quot_eq (hL : L.IsLB) {C : Type} [CommRing C] [IsLocalRing C] (g : A →+* C) (g' : B →+* C)
    {x : Sp A ⟶ X} {χ : Sp B ⟶ X} (hc : spMap g ≫ x = spMap g' ≫ χ) (e : LB.Gen (L.pull x)) (he : e.IsGen)
    (e' : LB.Gen (L.pull χ))
    (hv : ∀ z J, Good L z J → val (L := L) (φ := fun _ : PUnit => x) (ε := fun _ => 1) e (spMap g) z J =
      val (L := L) (φ := fun _ : PUnit => χ) (ε := fun _ => 1) e' (spMap g') z J)
    {i i' : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U i) (h' : ⊤ ≤ χ ⁻¹ᵁ L.U i') {d : ℕ} (s : H0 L d) :
    g (sv s x h * ((gv e h)⁻¹ ^ d).val) = g' (sv s χ h' * ((gv e' h')⁻¹ ^ d).val) := by
  have m : (spMap g ≫ x) (cp C) ∈ L.U i := h (Set.mem_univ _)
  have m' : (spMap g ≫ x) (cp C) ∈ L.U i' := by rw [hc]; exact h' (Set.mem_univ _)
  obtain ⟨J, hJ, hJi⟩ := exists_good L hL (cp C) (fun _ : PUnit => spMap g ≫ x) (fun _ => i') (fun _ _ _ => rfl)
    (fun _ => m')
  have v := hv _ J hJ
  rw [val_of (L := L) (φ := fun _ : PUnit => x) e _ _ J (fun _ => i') (fun _ => hJi PUnit.unit),
    val_of (L := L) (φ := fun _ : PUnit => χ) e' _ _ J (fun _ => i') (fun _ => hc ▸ hJi PUnit.unit),
    gen_trans (L := L) (φ := fun _ : PUnit => x) he (spMap g) (cp C) (j := fun _ => i') (j' := fun _ => i)
      (Set.mem_iInter.2 fun _ => m') (Set.mem_iInter.2 fun _ => m), trF, Fintype.prod_unique, zpow_one] at v
  have v' := congrArg Units.val v
  rw [Units.val_mul, gm_gv g e h, gm_gv g' e' h'] at v'
  have w := sec_trans s (spMap g ≫ x) (cp C) (j := fun _ => i') (j' := fun _ => i)
      (Set.mem_iInter.2 fun _ => m') (Set.mem_iInter.2 fun _ => m)
  rw [trF, Fintype.prod_unique, zpow_natCast, Category.comp_id, gs_sv s g x h, Units.val_pow_eq_pow_val] at w
  have w' := gs_sv s g' χ h' (cp C)
  rw [← hc, w] at w'
  apply toSt_bijective.1
  have u : toSt (cp C) (g (gv e h).val) * toSt (cp C) (g (gv e h)⁻¹.val) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have u' : toSt (cp C) (g' (gv e' h').val) * toSt (cp C) (g' (gv e' h')⁻¹.val) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  simp only [map_mul, map_pow, Units.val_pow_eq_pow_val]
  rw [← w', mul_comm (_ ^ d), _root_.mul_assoc, ← mul_pow]
  congr 2
  rw [← v'] at u'
  linear_combination (-toSt (cp C) (g (gv e h)⁻¹.val)) * u' + ((gm (spMap g ≫ x) (cp C) _ (L.g i' i)).val *
    toSt (cp C) (g' (gv e' h')⁻¹.val)) * u

theorem exists_sv_eq [CompactSpace X] [QuasiSeparatedSpace X] (hL : L.IsLB) [IsLocalRing A] {d : ℕ} (s : H0 L d)
    (x : Sp A ⟶ X) {i : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U i) (hs : ⊤ ≤ x ⁻¹ᵁ nonzeroLocus s) (a : Γ(X, nonzeroLocus s)) :
    ∃ (m : ℕ) (t : H0 L (d * m)), sv t x h = sv s x h ^ m * ev x _ hs a := by
  obtain ⟨m, t, ht⟩ := (sec_extend_of_nonzeroLocus X L hL d s).1 a
  refine ⟨m, t, toSt_bijective.1 ?_⟩
  have e := congrArg (x.stalkMap (cp A)).hom (ht (x (cp A)) (fun _ => i) (hs (Set.mem_univ _)) (h (Set.mem_univ _)))
  rw [map_mul, map_pow] at e
  have k : ∀ (U : X.Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U) (b : Γ(X, U)),
      (x.stalkMap (cp A)).hom (gs (𝟙 X) (x (cp A)) U b) = toSt (cp A) (ev x U hU b) := fun U hU b =>
    (gs_stalkMap x (cp A) U (hU (Set.mem_univ _)) b).symm.trans (gs_eq_toSt x U hU _ b)
  rw [map_mul, map_pow]
  exact (k _ (le_chart h) _).symm.trans (e.trans (congrArg₂ (· * ·) (congrArg (· ^ m) (k _ (le_chart h) _)) (k _ hs _)))

theorem exists_eq_of_traits {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [CharZero R] (q : FractionRing R)
    (H : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (φ : R →+* W)
      (gam : FractionRing R →+* FractionRing W), (∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) →
      ∃ w : W, gam q = algebraMap W _ w) : ∃ r : R, algebraMap R _ r = q := by
  refine exists_algebraMap_eq_of_forall_discreteValuationSubring fun V hV h1 _ => ?_
  let W := AdicCompletion (maximalIdeal V) V
  have inj : Function.Injective ((algebraMap W (FractionRing W)).comp (algebraMap V W)) :=
    (IsFractionRing.injective W _).comp (algebraMap_adicCompletion_injective_of_dvr V)
  let φ : R →+* W := (algebraMap V W).comp ((algebraMap R (FractionRing R)).codRestrict V h1)
  let gam : FractionRing R →+* FractionRing W := IsFractionRing.lift (A := V) inj
  have hg : ∀ v : V, gam v = algebraMap W _ (algebraMap V W v) := fun v => IsFractionRing.lift_algebraMap inj v
  have hφ : Function.Injective φ := (algebraMap_adicCompletion_injective_of_dvr V).comp
    fun a b hab => IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val hab)
  obtain ⟨w, hw⟩ := H W ⟨inferInstance, inferInstance, charZero_of_injective_ringHom hφ⟩ φ gam
    (fun r => hg ⟨_, h1 r⟩)
  by_contra hq
  have hq0 : q ≠ 0 := fun h => hq (h ▸ V.zero_mem)
  have hi : q⁻¹ ∈ V := (V.mem_or_inv_mem q).resolve_left hq
  have hu : IsUnit (algebraMap V W ⟨_, hi⟩) := IsUnit.of_mul_eq_one w (IsFractionRing.injective W (FractionRing W) (by
    rw [map_mul, ← hg, ← hw, ← map_mul, map_one]
    exact (congrArg gam (inv_mul_cancel₀ hq0)).trans (map_one _)))
  obtain ⟨b, hb⟩ := ((isUnit_map_iff (algebraMap V W) _).1 hu).exists_right_inv
  have : q⁻¹ * b = 1 := congrArg Subtype.val hb
  have e : (b : FractionRing R) = q := by rw [eq_inv_of_mul_eq_one_right this, inv_inv]
  exact hq (e ▸ b.2)

theorem exists_extension : ∀ (Z : Scheme.{0}) [CompactSpace Z] [QuasiSeparatedSpace Z] (AA : LB Z), AA.IsLB → (∀ z : Z, ∃ (d : ℕ) (s : H0 AA d), 1 ≤ d ∧ z ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s)) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (x : Sp (FractionRing R) ⟶ Z) (e : LB.Gen (AA.pull x)), e.IsGen → (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (φ : R →+* W) (gam : FractionRing R →+* FractionRing W), (∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) → ∃ χ : Sp W ⟶ Z, spMap gam ≫ x = jK W ≫ χ ∧ ∃ e' : LB.Gen (AA.pull χ), e'.IsGen ∧ ∀ z J, Good AA z J → val (L := AA) (φ := fun _ : PUnit => x) (ε := fun _ => 1) e (spMap gam) z J = val (L := AA) (φ := fun _ : PUnit => χ) (ε := fun _ => 1) e' (jK W) z J) → ∃ χ : Sp R ⟶ Z, jK R ≫ χ = x := by
  intro Z _ _ AA hL amp R _ _ _ _ _ _ x e he H
  by_cases hR : IsField R
  · obtain ⟨d, s, -, hz, hs⟩ := amp (x (cp _))
    refine exists_lift _ (IsFractionRing.injective R _) x hs (top_le x hz) fun a => ?_
    exact (IsField.localization_map_bijective (M := nonZeroDivisors R) zero_notMem_nonZeroDivisors hR).2 _
  obtain ⟨i, hi⟩ := exists_chart hL (x (cp _))
  have h := top_le x hi
  have key : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (φ : R →+* W)
      (gam : FractionRing R →+* FractionRing W), (∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) →
      ∃ z : Z, ∀ (d : ℕ) (s : H0 AA d), ∃ w : W, gam (sv s x h * ((gv e h)⁻¹ ^ d).val) = algebraMap W _ w ∧
        (z ∈ nonzeroLocus s → IsUnit w) := by
    intro W _ _ _ hW φ gam hg
    obtain ⟨χ, hc, e', -, hv⟩ := H W hW φ gam hg
    obtain ⟨i', hi'⟩ := exists_chart hL (χ (cp _))
    exact ⟨χ (cp _), fun d s => ⟨_, quot_eq hL gam (algebraMap W _) hc e he e' hv h (top_le χ hi') s,
      fun hz => ((isUnit_sv s χ _).2 hz).mul (Units.isUnit _)⟩⟩
  have int : ∀ (d : ℕ) (s : H0 AA d), ∃ r : R, algebraMap R _ r = sv s x h * ((gv e h)⁻¹ ^ d).val := fun d s =>
    exists_eq_of_traits _ fun W _ _ _ hW φ gam hg => by
      obtain ⟨z, hz⟩ := key W hW φ gam hg
      exact (hz d s).imp fun _ => And.left
  obtain ⟨W, _, _, _, _, φ, hφ, _⟩ := exists_complete_discreteValuationRing_dominating R hR
  have inj : Function.Injective ((algebraMap W (FractionRing W)).comp φ) := (IsFractionRing.injective W _).comp hφ
  have hg : ∀ r, IsFractionRing.lift (K := FractionRing R) inj (algebraMap R _ r) = algebraMap W _ (φ r) :=
    fun r => IsFractionRing.lift_algebraMap inj r
  obtain ⟨z, hz⟩ := key W ⟨inferInstance, inferInstance, charZero_of_injective_ringHom hφ⟩ φ _ hg
  obtain ⟨d, s, -, hzs, hs⟩ := amp z
  obtain ⟨w, hw, hu⟩ := hz d s
  obtain ⟨r, hr⟩ := int d s
  rw [← hr, hg] at hw
  have hru : IsUnit r := (isUnit_map_iff φ r).1 (IsFractionRing.injective W _ hw ▸ hu hzs)
  have hx : x (cp _) ∈ nonzeroLocus s :=
    (isUnit_sv s x h).1 (isUnit_of_mul_isUnit_left (hr ▸ hru.map (algebraMap R (FractionRing R))))
  refine exists_lift _ (IsFractionRing.injective R _) x hs (top_le x hx) fun a => ?_
  obtain ⟨m, t, ht⟩ := exists_sv_eq hL s x h (top_le x hx) a
  obtain ⟨r', hr'⟩ := int _ t
  obtain ⟨u, rfl⟩ := hru
  refine ⟨r' * (u⁻¹ ^ m).val, ?_⟩
  rw [map_mul, hr', ht, pow_mul, Units.val_pow_eq_pow_val _ m, mul_right_comm (_ ^ m), ← mul_pow, ← hr, ← map_pow,
    mul_right_comm, ← map_mul, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, mul_inv_cancel, one_pow,
    Units.val_one, map_one, _root_.one_mul]

end GlobalTheory.ExtLB
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibrewiseNonvanishingOfInvertiblePushforward
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibrewiseNonvanishingOfInvertiblePushforward
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory.ThetaLocal

open GlobalTheory.LB

variable {X Y : Scheme.{0}}

theorem mem_basicOpen_resG {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) (x : X) :
    x ∈ X.basicOpen (resG X h a) ↔ x ∈ V ∧ x ∈ X.basicOpen a := by
  have : X.basicOpen (resG X h a) = V ⊓ X.basicOpen a := X.basicOpen_res a (homOfLE h).op
  rw [this]; rfl

theorem mem_basicOpen_appLE (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U)
    (a : Γ(X, U)) (y : Y) :
    y ∈ Y.basicOpen ((f.appLE U V h).hom a) ↔ y ∈ V ∧ f y ∈ X.basicOpen a := by
  have : Y.basicOpen ((f.appLE U V h).hom a) = V ⊓ f ⁻¹ᵁ X.basicOpen a :=
    Scheme.basicOpen_appLE f V U h a
  rw [this]; rfl

theorem mem_basicOpen_mul {U : X.Opens} (a b : Γ(X, U)) (x : X) :
    x ∈ X.basicOpen (a * b) ↔ x ∈ X.basicOpen a ∧ x ∈ X.basicOpen b := by
  rw [Scheme.basicOpen_mul]; rfl

theorem nonvanishing_of_iso {L M : LB X} (hL : L.IsLB) (hM : M.IsLB) (w : LB.Iso L M) (hw : w.IsGen)
    {V : X.Opens} (s : Γ(toMod L, V)) (x : X) (p : M.ι)
    (hp : x ∈ X.basicOpen (coord ((isoOfGen hL hM w hw).hom.app V s) p)) :
    ∃ q, x ∈ X.basicOpen (coord s q) := by
  have hp' := X.basicOpen_le _ hp
  obtain ⟨q, hq⟩ := exists_chart hL x
  have e := coord_isoOfGen_hom_app hL hM w hw s p q (W := (V ⊓ M.U p) ⊓ (V ⊓ L.U q))
    inf_le_left inf_le_right (inf_le_inf inf_le_right inf_le_right)
  have e' := congrArg (fun a => x ∈ X.basicOpen a) e
  simp only [mem_basicOpen_mul, mem_basicOpen_resG, eq_iff_iff] at e'
  have hx : x ∈ (V ⊓ M.U p) ⊓ (V ⊓ L.U q) := ⟨hp', hp'.1, hq⟩
  exact ⟨q, (e'.1 ⟨hx, hp⟩).2.2⟩

theorem exists_sec_pull {L : LB X} {L' : LB Y} (hL : L.IsLB) (hL' : L'.IsLB) (F : Y ⟶ X) (w : LB.Iso L' (L.pull F))
    (hw : w.IsGen) {O : X.Opens} (hO : ⊤ ≤ F ⁻¹ᵁ O) (θ : ∀ i, Γ(X, O ⊓ L.U i)) (hθ : θ ∈ secOn L O) :
    ∃ θ' : L'.Sec, ∀ (y : Y) (i : L.ι), F y ∈ X.basicOpen (θ i) → ∃ k, y ∈ Y.basicOpen (θ'.f k) := by
  have hP : (L.pull F).IsLB := Semi.LB.isLB_pull hL F
  let e := isoOfGen hL' hP w hw
  let s : Γ(toMod (L.pull F), F ⁻¹ᵁ O) := mkSec
    (fun j => (F.appLE _ _ (pull_inf_le F O j)).hom (θ (j PUnit.unit))) (by
      intro i j
      have e : F ⁻¹ᵁ O ⊓ (L.pull F).U i ⊓ (L.pull F).U j ≤
          F ⁻¹ᵁ (O ⊓ L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) :=
        inf_le_inf (pull_inf_le F O i) (pull_U_le F j)
      have h := congrArg (F.appLE _ _ e).hom (hθ (i PUnit.unit) (j PUnit.unit))
      rw [map_mul, appLE_resG, appLE_resG, appLE_resG] at h
      rw [resG_appLE, resG_appLE, resG_pull_g]
      exact h)
  have hcoord (j : (L.pull F).ι) : coord s j =
      (F.appLE _ _ (pull_inf_le F O j)).hom (θ (j PUnit.unit)) := by
    exact congrFun (coord_mkSec _ _) j
  let s' : Γ(toMod L', F ⁻¹ᵁ O) := e.inv.app _ s
  have hs : e.hom.app _ s' = s := by
    have := congrArg (fun q => q.app (F ⁻¹ᵁ O) s) e.inv_hom_id
    exact this
  let t : Γ(toMod L', ⊤) := (toMod L').presheaf.map (homOfLE hO).op s'
  refine ⟨⟨fun k => resG Y (le_inf le_top le_rfl) (coord t k), fun i j => ?_⟩, fun y i hy => ?_⟩
  · change resG Y _ (resG Y _ _) = _ * resG Y _ (resG Y _ _)
    rw [resG_resG, resG_resG, coord_rel t i j _ _ le_rfl, resG_self]
  obtain ⟨k, hk⟩ := nonvanishing_of_iso hL' hP w hw s' y (fun _ => i) (by
    change y ∈ Y.basicOpen (coord (e.hom.app _ s') _)
    rw [hs]
    rw [hcoord (fun _ => i)]
    exact (mem_basicOpen_appLE F (pull_inf_le F O (fun _ => i)) (θ i) y).2
      ⟨⟨(X.basicOpen_le _ hy).1, mem_pull.2 (X.basicOpen_le _ hy).2⟩, hy⟩)
  refine ⟨k, ?_⟩
  dsimp only [t]
  rw [coord_map, mem_basicOpen_resG, mem_basicOpen_resG]
  have := (Y.basicOpen_le _ hk).2
  exact ⟨this, ⟨trivial, this⟩, hk⟩

theorem thetaNZ_of_pushInvertible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t₀ : SAB H S), PushInvertible t₀.G t₀.PP.L → ∀ (R : Type) [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ S) (t : SAB H (Sp R)) (_ : SABMap t t₀ ξ), ThetaNZ t.G t.PP.L := by
  intro E _ _ _ H S t₀ h R _ _ ξ t m
  obtain ⟨V, hV, θ, hθ, -, h2⟩ := h (ξ (IsLocalRing.closedPoint R))
  have hall : ∀ y : Sp R, ξ y ∈ V := fun y =>
    ((IsLocalRing.specializes_closedPoint y).map ξ.continuous).mem_open V.isOpen hV
  have hc : IsPullback m.cm.F t.G.hom t₀.G.hom ξ := m.cart.1
  have hpt : ∀ g : t.G.left, t₀.G.hom (m.cm.F g) = ξ (t.G.hom g) := fun g =>
    congrArg (fun q => q g) hc.w
  obtain ⟨w, hw, -⟩ := m.lin
  obtain ⟨θ', h'⟩ := exists_sec_pull t₀.PP.isLB t.PP.isLB m.cm.F w hw (O := t₀.G.hom ⁻¹ᵁ V)
    (fun g _ => by
      change t₀.G.hom (m.cm.F g) ∈ V
      rw [hpt]; exact hall _) θ hθ
  refine ⟨θ', fun y => ?_⟩
  obtain ⟨g, i, hg, hi⟩ := h2 (ξ y) (hall y)
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.exists_preimage_of_isPullback hc g y hg
  obtain ⟨k, hk⟩ := h' z i (by rw [hz₁]; exact hi)
  exact ⟨z, k, hz₂, hk⟩

end GlobalTheory.ThetaLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibrewiseNonvanishingOfInvertiblePushforwardStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
theorem _root_.GlobalTheory.T.fibrewise_nonvanishing_of_invertible_pushforward : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t₀ : SAB H S), PushInvertible t₀.G t₀.PP.L → ∀ (R : Type) [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ S) (t : SAB H (Sp R)) (_ : SABMap t t₀ ξ), ThetaNZ t.G t.PP.L := by
  first | exact @GlobalTheory.ThetaLocal.thetaNZ_of_pushInvertible | exact GlobalTheory.ThetaLocal.thetaNZ_of_pushInvertible | (intros; apply GlobalTheory.ThetaLocal.thetaNZ_of_pushInvertible <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAffineOpenOfLocalSectionCombinationLocus
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAffineOpenOfLocalSectionCombinationLocus
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out

noncomputable section
namespace GlobalTheory.ZH.CombLocus

def secComb {X : Scheme.{0}} {H : LB X} {J : Type} [Fintype J] (a : J → Γ(X, ⊤)) (s : J → H.Sec) : H.Sec where
  f l := ∑ k, resG X le_top (a k) * (s k).f l
  compat i j := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e : ∀ (U V : X.Opens) (h : V ≤ U),
        (X.presheaf.map (homOfLE h).op).hom (resG X (le_top : U ≤ ⊤) (a k)) = resG X (le_top : V ≤ ⊤) (a k) := by
      intro U V h
      change (X.presheaf.map (homOfLE _).op ≫ X.presheaf.map (homOfLE h).op).hom (a k) = _
      rw [← Functor.map_comp]
      rfl
    rw [map_mul, map_mul, (s k).compat i j, e, e, mul_left_comm]

theorem exists_crd_secComb {X Y : Scheme.{0}} (h : X ⟶ Y) {H : LB Y} {J : Type} [Fintype J] (σ : J → H.Sec)
    (hcov : ⨆ k, nonzeroLocus (σ k) = ⊤) (a : J → Γ(X, ⊤)) {K : Type} [Field K] (y : Sp K ⟶ X) :
    ∃ w, Crd H σ (y ≫ h) w ∧ (⊤ ≤ y ⁻¹ᵁ nonzeroLocus (secComb a fun k => GlobalTheory.secPull (σ k) h) ↔
      ∑ k, valR y ⊤ (a k) * w k ≠ 0) := by
  have h₀ : (y ≫ h) (IsLocalRing.closedPoint K) ∈ ⨆ k, nonzeroLocus (σ k) := by rw [hcov]; trivial
  obtain ⟨k₀, hk₀⟩ := TopologicalSpace.Opens.mem_iSup.1 h₀
  obtain ⟨l, hl⟩ := exists_chart_of_mem_nonzeroLocus hk₀
  have h₁ : ⊤ ≤ (y ≫ h) ⁻¹ᵁ H.U l := (CrdCalc.top_le_iff _ _).2 hl
  have h₂ : ⊤ ≤ y ⁻¹ᵁ (H.pull h).U (fun _ => l) := fun p hp => Set.mem_iInter.2 fun _ => h₁ hp
  refine ⟨fun k => valR (y ≫ h) (H.U l) ((σ k).f l), ⟨l, 1, h₁, fun k => by simp⟩, ?_⟩
  have h₃ : Crd (H.pull h) (fun _ : Unit => secComb a fun k => GlobalTheory.secPull (σ k) h) y
      (fun _ => ∑ k, valR y ⊤ (a k) * valR (y ≫ h) (H.U l) ((σ k).f l)) := by
    refine ⟨fun _ => l, 1, h₂, fun _ => ?_⟩
    rw [Units.val_one, one_mul, CrdCalc.valR_eq y _ h₂]
    refine Eq.symm ((map_sum _ _ _).trans (Finset.sum_congr rfl fun k _ => ?_))
    rw [map_mul, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq, CrdCalc.valR_res y _ h₂]
    exact congrArg _ (GlobalTheory.Points.valR_appLE y h _ h₂ _)
  exact (CrdCalc.crd_isUnit_iff () h₃).symm.trans isUnit_iff_ne_zero

theorem opens_eq_of_field_points {X : Scheme.{0}} {U V : X.Opens}
    (h : ∀ (K : Type) [Field K] (y : Sp K ⟶ X), ⊤ ≤ y ⁻¹ᵁ U ↔ ⊤ ≤ y ⁻¹ᵁ V) : U = V := by
  have e : ∀ (p : X) (O : X.Opens), ⊤ ≤ X.fromSpecResidueField p ⁻¹ᵁ O ↔ p ∈ O := fun p O =>
    ⟨fun H => by
      have := H (Set.mem_univ (IsLocalRing.closedPoint (X.residueField p)))
      have h' : X.fromSpecResidueField p (IsLocalRing.closedPoint (X.residueField p)) ∈ O := this
      exact (Scheme.fromSpecResidueField_apply p (IsLocalRing.closedPoint (X.residueField p))) ▸ h',
    fun H s _ => by
      change X.fromSpecResidueField p s ∈ O
      rwa [Scheme.fromSpecResidueField_apply]⟩
  ext p
  exact (e p U).symm.trans ((h _ (X.fromSpecResidueField p)).trans (e p V))

theorem isAffineHom_homOfLE {P Z : Scheme.{0}} (π : P ⟶ Z) {V W : Z.Opens} (e : V ≤ W) (hV : IsAffineOpen V)
    (hW : IsAffineOpen W) : IsAffineHom (P.homOfLE (π.preimage_mono e)) := by
  have : IsAffine V := hV
  have : IsAffine W := hW
  have sq : IsPullback (P.homOfLE (π.preimage_mono e)) (π ∣_ V) (π ∣_ W) (Z.homOfLE e) := by
    refine IsPullback.of_right (h₁₂ := (π ⁻¹ᵁ W).ι) (h₂₂ := W.ι) (v₁₃ := π) ?_ ?_ (isPullback_morphismRestrict π W).flip
    · rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι]
      exact (isPullback_morphismRestrict π V).flip
    · rw [← cancel_mono W.ι]
      simp
  exact MorphismProperty.of_isPullback (P := @IsAffineHom) sq.flip (inferInstance : IsAffineHom (Z.homOfLE e))

theorem isAffineOpen_of_comb : ∀ (P Z : Scheme.{0}) (π : P ⟶ Z) [IsProper π] (J : Type) [Fintype J] (D : P.Opens) (W : Z.Opens), IsAffineOpen W → D ≤ π ⁻¹ᵁ W → (∀ z ∈ W, ∃ (W' : Z.Opens) (H : LB (π ⁻¹ᵁ W').toScheme) (σ : J → H.Sec) (m : J → Γ(Z, W ⊓ W')), z ∈ W' ∧ IsAffineOpen W' ∧ ⨆ k, nonzeroLocus (σ k) = ⊤ ∧ (∀ k, IsAffineOpen (nonzeroLocus (σ k))) ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ (π ⁻¹ᵁ W').toScheme) (w : J → K), ⊤ ≤ (y ≫ (π ⁻¹ᵁ W').ι ≫ π) ⁻¹ᵁ W → Crd H σ y w → (⊤ ≤ (y ≫ (π ⁻¹ᵁ W').ι) ⁻¹ᵁ D ↔ ∑ k, valR (y ≫ (π ⁻¹ᵁ W').ι ≫ π) (W ⊓ W') (m k) * w k ≠ 0)) → IsAffineOpen D := by
  intro P Z π _ J _ D W hW hD H
  have : IsAffine W := hW
  have : IsAffineHom (π.resLE W D hD) := by
    refine isAffineHom_of_forall_exists_isAffineOpen _ fun z => ?_
    obtain ⟨W', H, σ, m, hz, hW', hcov, haff, hiff⟩ := H z.1 z.2
    obtain ⟨V, hV, hzV, hle⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (x := z.1) (U := W ⊓ W') ⟨z.2, hz⟩
    have hle' : V ≤ W ⊓ W' := hle
    have : IsAffine V := hV
    refine ⟨W.ι ⁻¹ᵁ V, hzV, hV.preimage_of_isOpenImmersion _ (by simpa using hle'.trans inf_le_left), ?_⟩
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_preimage,
      ← D.ι.isAffineOpen_iff_of_isOpenImmersion, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι]
    have e : V ≤ W' := hle'.trans inf_le_right
    have := isAffineHom_homOfLE π e hV hW'
    set h := P.homOfLE (π.preimage_mono e) with hh
    have hι : h ≫ (π ⁻¹ᵁ W').ι = (π ⁻¹ᵁ V).ι := Scheme.homOfLE_ι _ _
    have ha : ⊤ ≤ ((π ⁻¹ᵁ V).ι ≫ π) ⁻¹ᵁ (W ⊓ W') := fun p _ => hle' p.2
    let a : J → Γ((π ⁻¹ᵁ V).toScheme, ⊤) := fun k => (((π ⁻¹ᵁ V).ι ≫ π).appLE (W ⊓ W') ⊤ ha).hom (m k)
    have ht := isAffineOpen_nonzeroLocus_of_universallyClosed (π ∣_ V) (fun k => GlobalTheory.secPull (σ k) h)
      (by simp only [GlobalTheory.nonzeroLocus_secPull]; rw [← Scheme.Hom.preimage_iSup, hcov]; rfl)
      (fun k => by rw [GlobalTheory.nonzeroLocus_secPull]; exact (haff k).preimage h)
      (secComb a fun k => GlobalTheory.secPull (σ k) h)
    have hE : nonzeroLocus (secComb a fun k => GlobalTheory.secPull (σ k) h) = (π ⁻¹ᵁ V).ι ⁻¹ᵁ D := by
      have key : ∀ (K : Type) [Field K] (y : Sp K ⟶ (π ⁻¹ᵁ V).toScheme),
          ⊤ ≤ y ⁻¹ᵁ nonzeroLocus (secComb a fun k => GlobalTheory.secPull (σ k) h) ↔ ⊤ ≤ y ⁻¹ᵁ ((π ⁻¹ᵁ V).ι ⁻¹ᵁ D) := by
        intro K _ y
        obtain ⟨w, hw, hiff'⟩ := exists_crd_secComb h σ hcov a y
        have e₁ : (y ≫ h) ≫ (π ⁻¹ᵁ W').ι = y ≫ (π ⁻¹ᵁ V).ι := by rw [Category.assoc, hι]
        have e₂ : (y ≫ h) ≫ (π ⁻¹ᵁ W').ι ≫ π = y ≫ (π ⁻¹ᵁ V).ι ≫ π := by
          rw [← Category.assoc, e₁, Category.assoc]
        have h₄ := hiff K (y ≫ h) w (by rw [e₂]; exact fun p _ => (hle' (y p).2).1) hw
        rw [e₁, e₂] at h₄
        refine hiff'.trans (Iff.trans ?_ h₄.symm)
        have e₃ : ∀ k, valR y ⊤ (a k) = valR (y ≫ (π ⁻¹ᵁ V).ι ≫ π) (W ⊓ W') (m k) := fun k =>
          GlobalTheory.Points.valR_appLE y _ ha le_top _
        simp only [e₃]
      exact opens_eq_of_field_points key
    rw [hE] at ht
    have h₆ := ht.image_of_isOpenImmersion (π ⁻¹ᵁ V).ι
    rwa [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm] at h₆
  exact isAffine_of_isAffineHom (π.resLE W D hD)

end GlobalTheory.ZH.CombLocus
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAffineOpenOfLocalSectionCombinationLocusStatement
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAffineOpen_of_local_sectionCombination_locus : ∀ (P Z : Scheme.{0}) (π : P ⟶ Z) [IsProper π] (J : Type) [Fintype J] (D : P.Opens) (W : Z.Opens), IsAffineOpen W → D ≤ π ⁻¹ᵁ W → (∀ z ∈ W, ∃ (W' : Z.Opens) (H : LB (π ⁻¹ᵁ W').toScheme) (σ : J → H.Sec) (m : J → Γ(Z, W ⊓ W')), z ∈ W' ∧ IsAffineOpen W' ∧ ⨆ k, nonzeroLocus (σ k) = ⊤ ∧ (∀ k, IsAffineOpen (nonzeroLocus (σ k))) ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ (π ⁻¹ᵁ W').toScheme) (w : J → K), ⊤ ≤ (y ≫ (π ⁻¹ᵁ W').ι ≫ π) ⁻¹ᵁ W → Crd H σ y w → (⊤ ≤ (y ≫ (π ⁻¹ᵁ W').ι) ⁻¹ᵁ D ↔ ∑ k, valR (y ≫ (π ⁻¹ᵁ W').ι ≫ π) (W ⊓ W') (m k) * w k ≠ 0)) → IsAffineOpen D := by
  first | exact @GlobalTheory.ZH.CombLocus.isAffineOpen_of_comb | exact GlobalTheory.ZH.CombLocus.isAffineOpen_of_comb | (intros; apply GlobalTheory.ZH.CombLocus.isAffineOpen_of_comb <;> assumption)
end
end
