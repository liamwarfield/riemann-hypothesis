module

public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOpenNonzeroLocusOfUniversallyClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProj
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRingEquiv
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ConstantThetaDeformationZero
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FiniteOfNotLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsBasisMemOfSpanEqTopOfSemilocal
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsResMEqMulSecOfEqZpowSec

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AmpleDescent

theorem isAmpleLB_of_pull {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') [Flat (specOf g)]
    [Surjective (specOf g)] {X X' : Scheme.{0}} [CompactSpace X] [QuasiSeparatedSpace X]
    {f : X ⟶ Spec (CommRingCat.of R)} {π : X' ⟶ X} {f' : X' ⟶ Spec (CommRingCat.of R')} [UniversallyClosed f']
    (H : IsPullback π f' f (specOf g)) {L : LB X} (hL : L.IsLB) (h : IsAmpleLB (L.pull π)) : IsAmpleLB L := by
  have hg : g.Flat := (HasRingHomProperty.Spec_iff (P := @Flat)).1 (inferInstance : Flat (specOf g))
  have : Surjective π := MorphismProperty.of_isPullback (P := @Surjective) H.flip inferInstance
  refine ⟨hL, inferInstance, fun x => ?_⟩
  obtain ⟨z, rfl⟩ := π.surjective x
  obtain ⟨n, hn, s, hs, -⟩ := h.exists_affine z
  have hM := isLB_lbPow hL n
  obtain ⟨σ, hσ⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_pull hM π) (isLB_lbPow h.isLB n)
    (lbIso_lbPow_pull hL π n).symm s
  obtain ⟨m, c, u, hu⟩ := FlatSec.exists_comb_of_flat R R' g hg X f X' π f' H _ hM σ
  obtain ⟨k, hk⟩ := exists_chart hM (π z)
  have hz : IsUnit (gs (𝟙 X') z _ (σ.f fun _ => k)) :=
    (mem_nonzeroLocus_iff_isUnit σ (k := fun _ => k) (mem_pull.2 hk)).1 (hσ.ge hs)
  rw [hu z k hk] at hz
  obtain ⟨j, -, hj⟩ := IsLocalRing.exists_of_isUnit_sum hz
  refine ⟨n, hn, u j, (mem_nonzeroLocus_iff_pull (u j) π z hk).2 (isUnit_of_mul_isUnit_right hj), ?_⟩
  have ha := h.isAffineOpen_nonzeroLocus f' hn (secPowPull (u j) π)
  rw [nonzeroLocus_secPowPull] at ha
  have : IsAffine (π ⁻¹ᵁ nonzeroLocus (u j)) := ha
  exact isAffine_of_isPullback_of_flat_surjective
    ((isPullback_morphismRestrict π (nonzeroLocus (u j))).paste_vert H)

theorem kTriv_of_pull {S S' : Scheme.{0}} [IsAffine S] [IsAffine S'] {f : S' ⟶ S} [Flat f] [Surjective f]
    {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}
    (h : IsGrpPullback A' A f φ) (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (hK : KTriv A' L') :
    KTriv A L := by
  obtain ⟨w, hw⟩ := hw
  intro R _ t x hx
  obtain ⟨R', g, t', hg, sq⟩ : ∃ (R' : CommRingCat.{0}) (g : Spec R' ⟶ Spec (CommRingCat.of R)) (t' : Spec R' ⟶ S'),
      Epi g ∧ g ≫ t = t' ≫ f := by
    refine ⟨Γ(pullback t f, ⊤), (pullback t f).isoSpec.inv ≫ pullback.fst t f,
      (pullback t f).isoSpec.inv ≫ pullback.snd t f, Flat.epi_of_flat_of_surjective _, ?_⟩
    rw [Category.assoc, Category.assoc, pullback.condition]
  let T : Over S := Over.mk t
  let T' : Over S' := Over.mk t'
  have hxw : (g ≫ x.left) ≫ A.hom = t' ≫ f := by rw [Category.assoc, Over.w x]; exact sq
  let x' : T' ⟶ A' := Over.homMk (h.1.lift _ _ hxw) (h.1.lift_snd _ _ _)
  have hx' : x'.left ≫ φ = g ≫ x.left := h.1.lift_fst _ _ _
  have key : x' = toUnit _ ≫ η[A'] := hK R' t' x' fun p => by
    obtain ⟨V, hV, c, hc⟩ := hx (g p)
    refine ⟨g ⁻¹ᵁ V, hV, ?_⟩
    let a : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ T := Over.homMk ((fst T' A').left ≫ g)
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) sq).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ f) (Over.w (fst T' A'))))))
    let b : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ A := pushPt h.1.w (snd T' A')
    have k₁ : (lift a b).left ≫ (fst T A).left = (fst T' A').left ≫ g := congrArg (fun q => q.left) (lift_fst a b)
    have k₂ : (lift a b).left ≫ (snd T A).left = (snd T' A').left ≫ φ := congrArg (fun q => q.left) (lift_snd a b)
    have k₃ : (lift a b).left ≫ ((fst T A ≫ x) * snd T A).left = ((fst T' A' ≫ x') * snd T' A').left ≫ φ := by
      have e : lift a b ≫ ((fst T A ≫ x) * snd T A) = (a ≫ x) * b := by
        rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
      refine (congrArg (fun q => q.left) e).trans (h.2 (T' ⊗ A') _ _ _ _ ?_ rfl)
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hx'.symm).trans (Category.assoc _ _ _).symm)
    have le : (fst T' A').left ⁻¹ᵁ g ⁻¹ᵁ V ≤ (lift a b).left ⁻¹ᵁ (fst T A).left ⁻¹ᵁ V := fun y hy =>
      (congrArg (fun q => q y ∈ V) k₁).mpr hy
    have hn := Scheme.Hom.resLE_comp_ι (lift a b).left le
    obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn L _ _ _) c hc
    obtain ⟨c₂, h₂⟩ := gen_chartPull (chartPullSame L (fun k : Fin 2 => (((fst T' A').left ⁻¹ᵁ g ⁻¹ᵁ V).ι ≫
      ![(lift (fst T' A' ≫ x') (snd T' A') ≫ μ[A']).left, (snd T' A').left] k) ≫ φ) _ _
      ((lift a b).left.resLE _ _ le) fun k => by
        rw [← Category.assoc, hn, Category.assoc, Category.assoc]
        fin_cases k
        exacts [congrArg (_ ≫ ·) k₃.symm, congrArg (_ ≫ ·) k₂.symm]) c₁ h₁
    obtain ⟨c₃, h₃⟩ := exists_down ((isGen_iff w).1 hw) hL hL' c₂ h₂
    exact gen_chartPull (chartPullOut L' _ _ _ _ fun _ => rfl) c₃ h₃
  let U : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk g sq
  have e₁ : U ≫ x = pushHom h T' x' := Over.OverMorphism.ext hx'.symm
  have e₂ : U ≫ x = U ≫ (1 : T ⟶ A) := by
    rw [e₁, MonObj.comp_one]
    exact (congrArg (pushHom h T') key).trans (map_one (pushHom h T'))
  exact Over.OverMorphism.ext ((cancel_epi g).1 (congrArg (fun q => q.left) e₂))

theorem proper_relAmple_kTriv_of_fieldExtension : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K') (G : Over (Spec (CommRingCat.of K))) [GrpObj G] [QuasiCompact G.hom] [IsSeparated G.hom] [Smooth G.hom] (G' : Over (Spec (CommRingCat.of K'))) [GrpObj G'] (Ψ : G'.left ⟶ G.left), Geo.Tor.IsGrpPullback G' G (specOf i) Ψ → ∀ (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → Geo.Tor.LBIso L' (L.pull Ψ) → IsProper G'.hom → RelAmple G' L' → KTriv G' L' → IsProper G.hom ∧ RelAmple G L ∧ KTriv G L := by
  intro K K' _ _ i G _ _ _ _ G' _ Ψ h L L' hL hL' hw hP hA hK
  have : Subsingleton (Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : Nonempty (Spec (CommRingCat.of K')) := inferInstanceAs (Nonempty (PrimeSpectrum K'))
  have : Flat (specOf i) := inferInstance
  have : Surjective (specOf i) := inferInstance
  have : UniversallyClosed G.hom := MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) h.1.flip ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  have hG : IsProper G.hom := ⟨⟩
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : QuasiSeparatedSpace G.left := quasiSeparatedSpace_of_quasiSeparated G.hom
  refine ⟨hG, (relAmple_iff_isAmpleLB_of_isAffine G hL).2 (isAmpleLB_of_pull i h.1 hL ?_),
    kTriv_of_pull h hL hL' hw hK⟩
  exact (isAmpleLB_of_relAmple_of_isAffine G' hL' hA).of_lbIso (LB.isLB_pull hL Ψ) hw.symm

end GlobalTheory.AmpleDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenThetaAbelianVariety
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw.CubeProj

open CubeGen

theorem isProjBy_baseChange {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of R)} (hf : IsProjBy f) {φ : X' ⟶ X} {f' : X' ⟶ Spec (CommRingCat.of R')}
    {t : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} (h : IsPullback φ f' f t) : IsProjBy f' := by
  obtain ⟨g, rfl⟩ := Spec.map_surjective t
  obtain ⟨H, hH, n, s, hs⟩ := hf
  have hH' : (H.pull φ).IsLB := DVR.linComb_isLB _ hH _ _
  obtain ⟨w, hw⟩ := GlobalTheory.PolBaseChange.lbIso_refl hH'
  choose s' hs' using fun (j : Fin (n + 1)) => (GlobalTheory.SecPullIso.section_pull X X' φ H _ w hH hH' hw (s j)).1.exists
  refine ⟨_, hH', n, s', GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull R X f H n s hH hs R' g.hom X' f' φ h.w ?_
    _ w s' hH' hw hs'⟩
  have e : pullback.lift φ f' h.w = h.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, IsPullback.isoPullback_hom_fst]
    · rw [pullback.lift_snd, IsPullback.isoPullback_hom_snd]
  have : IsClosedImmersion (pullback.lift φ f' h.w) := by rw [e]; infer_instance
  exact this

theorem exists_gen_theta_of_isProjBy (hG : GlobalFnsSt) (R₀ : Type) [CommRing R₀]
    (A : Over (Spec (CommRingCat.of R₀))) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (hp : IsProjBy A.hom) (M : LB A.left) (hM : M.IsLB) : ∃ t : LB.Gen (Theta A M), t.IsGen := by
  have hI := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
  have hPerf := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj
  have hSegre := GlobalTheory.AbLaw.isProjBy_tensor
  have hClosed := GlobalTheory.TrivLocus.isClosed_trivLocus
  have hOpen := GlobalTheory.AbLaw.CubeOpen.triv_basicOpen_of_triv_fibre hG GlobalTheory.AbLaw.Seesaw.seesaw
    (GlobalTheory.SmallExtLift.exists_gen_of_small_extension hG GlobalTheory.KuennethOne.kuenneth_injective)
  have := hA.geomConnected
  have H := fibTriv_clopen M (thφ A (x3 A)) thε (x3 A 2).left (fun R _ j => by
    obtain ⟨q, hq, q₀, q₁⟩ := exists_cube_chart A j
    have hB := isAb_baseChange hA (j ≫ A.hom)
    have one := one_left_fst (A := A) (j ≫ A.hom)
    have pB : IsProjBy ((Over.pullback (j ≫ A.hom)).obj A).hom :=
      isProjBy_baseChange hp (IsPullback.of_hasPullback A.hom (j ≫ A.hom))
    let B := (Over.pullback (j ≫ A.hom)).obj A
    have : Smooth B.hom := hB.smooth
    have : IsProper B.hom := hB.proper
    have : GeometricallyConnected B.hom := hB.geomConnected
    have sm : Smooth (B ⊗ B).hom := by
      change Smooth (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
    have pr : IsProper (B ⊗ B).hom := by
      change IsProper (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
    have gc : GeometricallyConnected (B ⊗ B).hom := by
      change GeometricallyConnected (pullback.fst B.hom B.hom ≫ B.hom)
      exact GeometricallyConnected.comp _ _
    have hN : (LB.LinComb M (fun k => q ≫ thφ A (x3 A) k) thε).IsLB := DVR.linComb_isLB _ hM _ _
    have pf := hPerf R _ _ sm (hSegre R B B pB pB)
    refine ⟨_, q, (B ⊗ B).hom, hq, hClosed R _ _ _ hN (pf _ hN) (pf _ (isLB_pw hN _)) pr (hI _ _ _ sm gc),
      fun F _ g Z π f' => hOpen R B hB _ hN (pf _ hN) ?_ ?_ F g Z π f'⟩
    · rw [triv_pull_comp_iff]
      refine trivAt_of_formal hM _ (prod_face _ 1 (B.hom ≫ j ≫ A.hom) ?_)
      rw [Category.assoc, q₁, ← Category.assoc, ← Over.comp_left, lift_snd]
      exact one B
    · rw [triv_pull_comp_iff]
      refine trivAt_of_formal hM _ (prod_face _ 0 (B.hom ≫ j ≫ A.hom) ?_)
      rw [Category.assoc, q₀, ← Category.assoc, ← Over.comp_left, lift_fst]
      exact one B)
  have hclopen : IsClopen (fibTriv M (thφ A (x3 A)) thε (x3 A 2).left) :=
    ⟨H.2, by rw [H.1.antisymm (locTriv_subset _ _ _ _)]; exact isOpen_locTriv _ _ _ _⟩
  have all : ∀ t, t ∈ fibTriv M (thφ A (x3 A)) thε (x3 A 2).left := fun t => by
    have hr : Set.range ((Spec (CommRingCat.of R₀)).fromSpecResidueField (A.hom t)) = {A.hom t} := Scheme.range_fromSpecResidueField _
    obtain ⟨y, hy⟩ := hr.ge rfl
    let g := (Spec (CommRingCat.of R₀)).fromSpecResidueField (A.hom t) ≫ η[A].left
    have gw : g ≫ A.hom = (Spec (CommRingCat.of R₀)).fromSpecResidueField (A.hom t) := by
      rw [Category.assoc, Over.w]; exact Category.comp_id _
    refine (A.hom.isConnected_preimage_singleton (A.hom t)).isPreconnected.subset_isClopen hclopen
      ⟨g y, (congrArg (fun m : Spec ((Spec (CommRingCat.of R₀)).residueField (A.hom t)) ⟶ Spec (CommRingCat.of R₀) => m y) gw).trans hy, ?_⟩ rfl
    exact ⟨(Spec (CommRingCat.of R₀)).residueField (A.hom t), inferInstance, g, _, _, _, ⟨y, rfl⟩,
      IsPullback.of_hasPullback (x3 A 2).left g,
      trivAt_of_formal hM _ (prod_face _ 2 (pullback.snd _ g ≫ (Spec (CommRingCat.of R₀)).fromSpecResidueField (A.hom t))
        (pullback.condition.trans (Category.assoc _ _ _).symm))⟩
  let e : A ⟶ G3 A := lift 1 (lift 1 (𝟙 _))
  have e₀ : e ≫ x3 A 0 = 1 := by simp [e, x3]
  have e₂ : e ≫ x3 A 2 = 𝟙 _ := by simp [e, x3]
  refine triv_of_local hM (thφ A (x3 A)) thε (x3 A 2).left e.left (congrArg (fun q => q.left) e₂)
    (fun Z b => prod_face _ 0 (b ≫ A.hom) ?_) (fun V => ?_) (fun s => H.1 (all s))
  · rw [Category.assoc, ← Over.comp_left, e₀, Category.assoc]
    rfl
  · obtain ⟨q, hq, -⟩ := exists_cube_chart A V.ι
    have hB := isAb_baseChange hA (V.ι ≫ A.hom)
    refine ⟨_, q, _, hq, ?_⟩
    rw [← Over.w (snd _ _)]
    exact surj_comp (surj_snd hG hB _) (hG _ _ hB).2

theorem exists_gen_theta_abelianVariety : GlobalFnsSt → ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ M : LB B.left, M.IsLB → ∃ t : LB.Gen (Theta B M), t.IsGen :=
  fun hG K _ _ B _ _ hB hp M hM => exists_gen_theta_of_isProjBy hG K B hB hp M hM

end GlobalTheory.AbLaw.CubeProj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfVeryAmpleBy
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace MapToProj

open MvPolynomial TopologicalSpace SecRingIso LBGerm

variable {R : Type} [CommRing R] {X X' Y Z : Scheme.{0}} {H : LB X} {H' : LB X'} {n : ℕ}
  {s : Fin (n + 1) → H.Sec} {s' : Fin (n + 1) → H'.Sec}

theorem exists_isRatioFamily (s : Fin (n + 1) → H.Sec) (i : Fin (n + 1)) : ∃ r, IsRatioFamily s i r := by
  choose r hr using fun j => exists_quot (s j) (s i) _ le_rfl
  refine ⟨r, fun j k => fn_ext fun y hy => ?_⟩
  rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy, hr j y k hy.1 hy.2, mul_comm]

theorem ratio_gs {i : Fin (n + 1)} {r : Fin (n + 1) → Γ(X, nonzeroLocus (s i))} (hr : IsRatioFamily s i r)
    (φ : Z ⟶ X) (z : Z) (hy : φ z ∈ nonzeroLocus (s i)) {k : H.ι} (hk : φ z ∈ H.U k) (j : Fin (n + 1)) :
    gs φ z _ ((s j).f k) = gs φ z _ (r j) * gs φ z _ ((s i).f k) := by
  have h : φ z ∈ nonzeroLocus (s i) ⊓ H.U k := ⟨hy, hk⟩
  have e := congrArg (gs φ z _) (hr j k)
  rwa [gs_res _ z _ h, gs_mul _ z _ h, gs_res _ z _ h, gs_res _ z _ h] at e

theorem gs_cst (f : X ⟶ Spec (CommRingCat.of R)) (φ : Z ⟶ X) (z : Z) (U : X.Opens) (h : φ z ∈ U) (c : R) :
    gs φ z U (cst f U c) =
      gs (𝟙 Z) z ⊤ ((φ ≫ f).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) := by
  have e := gs_pull (𝟙 Z) φ z ⊤ trivial (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c))
  rw [Category.id_comp] at e
  exact (gs_res φ z le_top h _).trans e.symm

theorem ker_le (f : X ⟶ Spec (CommRingCat.of R)) (f' : X' ⟶ Spec (CommRingCat.of R))
    (hc : ⨆ i, nonzeroLocus (s i) = ⊤) (ha : ∀ i, IsAffineOpen (nonzeroLocus (s i)))
    (r : ∀ i, Fin (n + 1) → Γ(X, nonzeroLocus (s i))) (hr' : ∀ i, IsRatioFamily s i (r i))
    (hv : ∀ d, vanishingForms f s d ⊆ vanishingForms f' s' d) (i : Fin (n + 1))
    {r' : Fin (n + 1) → Γ(X', nonzeroLocus (s' i))} (h' : IsRatioFamily s' i r') :
    RingHom.ker (eval₂Hom (cst f _) (r i)) ≤ RingHom.ker (eval₂Hom (cst f' _) r') := by
  intro p hp
  rw [RingHom.mem_ker] at hp ⊢
  obtain ⟨e, F, hF, G, hG⟩ := (ThetaDeform.exists_homogeneous i p).exists
  have hFi : eval₂Hom (cst f _) (r i) F = 0 := by
    rw [eq_add_of_sub_eq hG, map_add (f := _), hp, map_mul, map_sub, map_one, eval₂Hom_X', (hr' i).self_eq_one]
    simp
  have hn : ∀ j, ∃ n, r j i ^ n * eval₂Hom (cst f _) (r j) F = 0 := fun j => by
    refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X (ha j) _ _ (fn_ext fun y hy => ?_)
    have hj : y ∈ nonzeroLocus (s j) := X.basicOpen_le _ hy
    obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus hj
    have uj := (mem_nonzeroLocus_iff_isUnit _ hk).1 hj
    have hi : y ∈ nonzeroLocus (s i) := by
      rw [mem_nonzeroLocus_iff_isUnit _ hk, (hr' j).gs_eq hj hk i]
      exact ((LBGerm.isUnit_gs_iff (𝟙 X) y _ hj _).2 hy).mul uj
    have e₁ := ((hr' j).gs_form f hj hk hF).symm.trans ((hr' i).gs_form f hi hk hF)
    rw [hFi, LBGerm.gs_zero _ y _ hi, mul_zero] at e₁
    rw [LBGerm.gs_zero _ y _ hy]
    exact (gs_res _ y (X.basicOpen_le _) hy _).trans ((uj.pow e).mul_right_eq_zero.1 e₁)
  choose m hm using hn
  have hx : MvPolynomial.X i ^ Finset.univ.sup m * F ∈ vanishingForms f s (Finset.univ.sup m + e) := by
    refine mem_vanishingForms_of_ratios f hc r hr' ((isHomogeneous_X_pow i _).mul hF) fun j => ?_
    obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := m) (Finset.mem_univ j))
    rw [hb, map_mul, map_pow, eval₂Hom_X', pow_add, _root_.mul_assoc, hm j, mul_zero]
  have e₂ := h'.eval_eq_zero f' (hv _ hx)
  rw [eq_add_of_sub_eq hG, map_mul, map_pow, map_add (f := _), map_mul, map_sub, map_one, eval₂Hom_X', h'.self_eq_one] at e₂
  simpa using e₂

def Propor (s : Fin (n + 1) → H.Sec) (s' : Fin (n + 1) → H'.Sec) (φ : Z ⟶ X) (ψ : Z ⟶ X') : Prop :=
  ∀ z : Z, (∀ a, φ z ∈ nonzeroLocus (s a) ↔ ψ z ∈ nonzeroLocus (s' a)) ∧
    ∀ a b k k', φ z ∈ H.U k → ψ z ∈ H'.U k' →
      gs φ z _ ((s a).f k) * gs ψ z _ ((s' b).f k') = gs φ z _ ((s b).f k) * gs ψ z _ ((s' a).f k')

theorem Propor.comp {φ : Z ⟶ X} {ψ : Z ⟶ X'} (h : Propor s s' φ ψ) (r : Y ⟶ Z) : Propor s s' (r ≫ φ) (r ≫ ψ) :=
  fun y => ⟨(h (r y)).1, fun a b j j' hj hj' => by
    rw [gs_comp r φ y _ hj, gs_comp r φ y _ hj, gs_comp r ψ y _ hj', gs_comp r ψ y _ hj', ← map_mul, ← map_mul]
    exact congrArg _ ((h (r y)).2 a b j j' hj hj')⟩

theorem Propor.of_local {φ : Z ⟶ X} {ψ : Z ⟶ X'}
    (h : ∀ z : Z, ∃ U : Z.Opens, z ∈ U ∧ Propor s s' (U.ι ≫ φ) (U.ι ≫ ψ)) : Propor s s' φ ψ := fun z => by
  obtain ⟨U, hz, H⟩ := h z
  obtain ⟨y, rfl⟩ : ∃ y : U.toScheme, U.ι y = z := ⟨⟨z, hz⟩, rfl⟩
  refine ⟨(H y).1, fun a b j j' hj hj' => ?_⟩
  have e := (H y).2 a b j j' hj hj'
  rw [gs_comp U.ι φ y _ hj, gs_comp U.ι φ y _ hj, gs_comp U.ι ψ y _ hj', gs_comp U.ι ψ y _ hj',
    ← map_mul, ← map_mul] at e
  exact (ConcreteCategory.bijective_of_isIso (U.ι.stalkMap y)).1 e

theorem Propor.unique (f : X ⟶ Spec (CommRingCat.of R)) {φ₁ φ₂ : Z ⟶ X} {ψ : Z ⟶ X'} (h₁ : Propor s s' φ₁ ψ)
    (h₂ : Propor s s' φ₂ ψ) (e : φ₁ ≫ f = φ₂ ≫ f) {i : Fin (n + 1)} (ha : IsAffineOpen (nonzeroLocus (s i)))
    {r : Fin (n + 1) → Γ(X, nonzeroLocus (s i))} (hr : IsRatioFamily s i r)
    (hs : Function.Surjective (eval₂Hom (cst f _) r)) (hψ : ∀ z, ψ z ∈ nonzeroLocus (s' i)) : φ₁ = φ₂ := by
  have m₁ := fun z => ((h₁ z).1 i).2 (hψ z)
  have m₂ := fun z => ((h₂ z).1 i).2 (hψ z)
  refine hom_ext_affine ha m₁ m₂ fun g z => ?_
  obtain ⟨p, rfl⟩ := hs g
  obtain ⟨k', hk'⟩ := exists_chart_of_mem_nonzeroLocus (hψ z)
  have key : ∀ χ : Z ⟶ X, Propor s s' χ ψ → ∀ j,
      gs χ z _ (r j) * gs ψ z _ ((s' i).f k') = gs ψ z _ ((s' j).f k') := fun χ hχ j => by
    have m := ((hχ z).1 i).2 (hψ z)
    obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus m
    refine ((mem_nonzeroLocus_iff_pull _ χ z hk).1 m).mul_left_cancel ?_
    rw [← (hχ z).2 j i k k' hk hk', ratio_gs hr χ z m hk j]
    ring
  induction p using MvPolynomial.induction_on with
  | C a => rw [eval₂Hom_C, gs_cst f _ z _ (m₁ z), gs_cst f _ z _ (m₂ z), e]
  | add p q hp hq => rw [map_add (f := _), gs_add _ z _ (m₁ z), gs_add _ z _ (m₂ z), hp, hq]
  | mul_X p j hp =>
    rw [map_mul, gs_mul _ z _ (m₁ z), gs_mul _ z _ (m₂ z), hp, eval₂Hom_X']
    exact congrArg _ (((mem_nonzeroLocus_iff_pull _ ψ z hk').1 (hψ z)).mul_right_cancel
      ((key _ h₁ j).trans (key _ h₂ j).symm))

theorem exists_local (f : X ⟶ Spec (CommRingCat.of R)) (f' : X' ⟶ Spec (CommRingCat.of R)) {i : Fin (n + 1)}
    (ha : IsAffineOpen (nonzeroLocus (s i))) {r : Fin (n + 1) → Γ(X, nonzeroLocus (s i))}
    (hr : IsRatioFamily s i r) (hs : Function.Surjective (eval₂Hom (cst f _) r))
    {r' : Fin (n + 1) → Γ(X', nonzeroLocus (s' i))} (hr' : IsRatioFamily s' i r')
    (hk : RingHom.ker (eval₂Hom (cst f _) r) ≤ RingHom.ker (eval₂Hom (cst f' _) r')) :
    ∃ φ : (nonzeroLocus (s' i)).toScheme ⟶ X, φ ≫ f = (nonzeroLocus (s' i)).ι ≫ f' ∧
      Propor s s' φ (nonzeroLocus (s' i)).ι := by
  obtain ⟨φ, hφ, hg⟩ := exists_hom_of_ringHom ha (nonzeroLocus (s' i))
    ((eval₂Hom (cst f _) r).liftOfSurjective hs ⟨_, hk⟩)
  have hp : ∀ p z, gs φ z _ (eval₂Hom (cst f _) r p) =
      gs (nonzeroLocus (s' i)).ι z _ (eval₂Hom (cst f' _) r' p) := fun p z => by
    rw [hg, RingHom.liftOfSurjective_comp_apply]
  have hz : ∀ z : (nonzeroLocus (s' i)).toScheme, (nonzeroLocus (s' i)).ι z ∈ nonzeroLocus (s' i) := fun z => z.2
  refine ⟨φ, hom_ext_spec fun c z => ?_, fun z => ?_⟩
  · have e := hp (C c) z
    rwa [eval₂Hom_C, eval₂Hom_C, gs_cst f _ z _ (hφ z), gs_cst f' _ z _ (hz z)] at e
  · have e : ∀ j, gs φ z _ (r j) = gs (nonzeroLocus (s' i)).ι z _ (r' j) := fun j => by
      have e := hp (MvPolynomial.X j) z
      rwa [eval₂Hom_X', eval₂Hom_X'] at e
    refine ⟨fun a => ?_, fun a b k k' hk hk' => ?_⟩
    · obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus (hφ z)
      obtain ⟨k', hk'⟩ := exists_chart_of_mem_nonzeroLocus (hz z)
      rw [mem_nonzeroLocus_iff_pull _ φ z hk, mem_nonzeroLocus_iff_pull _ _ z hk', ratio_gs hr φ z (hφ z) hk a,
        ratio_gs hr' _ z (hz z) hk' a, IsUnit.mul_iff, IsUnit.mul_iff, e,
        and_iff_left ((mem_nonzeroLocus_iff_pull _ φ z hk).1 (hφ z)),
        and_iff_left ((mem_nonzeroLocus_iff_pull _ _ z hk').1 (hz z))]
    · rw [ratio_gs hr φ z (hφ z) hk a, ratio_gs hr φ z (hφ z) hk b, ratio_gs hr' _ z (hz z) hk' a,
        ratio_gs hr' _ z (hz z) hk' b, e, e]
      ring

theorem exists_unit {φ : X' ⟶ X} (h : Propor s s' φ (𝟙 X')) (hc : ⨆ i, nonzeroLocus (s' i) = ⊤) (k : H.ι)
    (k' : H'.ι) : ∃ u : Γ(X', (H.pull φ).U (fun _ => k) ⊓ H'.U k')ˣ, ∀ j z, φ z ∈ H.U k → z ∈ H'.U k' →
      gs φ z _ ((s j).f k) = (gm (𝟙 X') z _ u).val * gs (𝟙 X') z _ ((s' j).f k') := by
  let V : X'.Opens := (H.pull φ).U (fun _ => k) ⊓ H'.U k'
  let W : Fin (n + 1) → X'.Opens := fun i => V ⊓ nonzeroLocus (s' i)
  have l₁ : ∀ i, W i ≤ φ ⁻¹ᵁ H.U k := fun i x hx => mem_pull.1 hx.1.1
  have l₂ : ∀ i, W i ≤ H'.U k' := fun i x hx => hx.1.2
  have un : ∀ i y, y ∈ W i → IsUnit (gs (𝟙 X') y _ ((s' i).f k')) := fun i y hy =>
    (mem_nonzeroLocus_iff_isUnit _ (l₂ i hy)).1 hy.2
  have hu : ∀ i, IsUnit (resG X' (l₂ i) ((s' i).f k')) := fun i =>
    X'.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
      have := un i y hy
      rw [← gs_res (𝟙 X') y (l₂ i) hy, gs_eq _ y _ hy] at this
      exact this
  obtain ⟨v, hv⟩ : ∃ v : ∀ i, Γ(X', W i), ∀ j (y : X') i, y ∈ W i →
      gs φ y _ ((s j).f k) = gs (𝟙 X') y _ (v i) * gs (𝟙 X') y _ ((s' j).f k') := by
    refine ⟨fun i => resG X' (l₁ i) ((φ.app _).hom ((s i).f k)) * ((hu i).unit⁻¹).val, fun j y i hy => ?_⟩
    have e : gs (𝟙 X') y _ (resG X' (l₁ i) ((φ.app _).hom ((s i).f k)) * ((hu i).unit⁻¹).val) *
        gs (𝟙 X') y _ ((s' i).f k') = gs φ y _ ((s i).f k) := by
      rw [← gs_res (𝟙 X') y (l₂ i) hy ((s' i).f k'), ← gs_mul _ y _ hy, _root_.mul_assoc, (hu i).val_inv_mul,
        _root_.mul_one, gs_res _ y _ hy, gs_pull (𝟙 X') φ y _ (l₁ i hy), Category.id_comp]
    refine (un i y hy).mul_right_cancel ?_
    rw [(h y).2 j i k k' (l₁ i hy) (l₂ i hy), ← e]
    ring
  have cov : ∀ y ∈ V, ∃ i, y ∈ W i := fun y hy => by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hc.ge (Set.mem_univ y))
    exact ⟨i, hy, hi⟩
  obtain ⟨c, hc', -⟩ := DVR.sec_glue V W (fun _ => inf_le_left) (fun y hy => Opens.mem_iSup.2 (cov y hy)) v
    (fun a b => fn_ext fun y hy => by
      rw [gs_res _ y _ hy, gs_res _ y _ hy]
      exact (un a y hy.1).mul_right_cancel ((hv a y a hy.1).symm.trans (hv a y b hy.2)))
  have hcv : ∀ j y, y ∈ V → gs φ y _ ((s j).f k) = gs (𝟙 X') y V c * gs (𝟙 X') y _ ((s' j).f k') :=
    fun j y hy => by
      obtain ⟨i, hi⟩ := cov y hy
      rw [hv j y i hi, ← hc' i, gs_res _ y _ hi]
  have uc : IsUnit c := X'.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨i, hi⟩ := cov y hy
    have := (mem_nonzeroLocus_iff_pull _ φ y (l₁ i hi)).1 (((h y).1 i).2 hi.2)
    rw [hcv i y hy] at this
    have := isUnit_of_mul_isUnit_left this
    rw [gs_eq _ y _ hy] at this
    exact this
  refine ⟨uc.unit, fun j z hk hk' => ?_⟩
  have hz : z ∈ V := ⟨mem_pull.2 hk, hk'⟩
  rw [← gs_unit _ z V hz]
  exact hcv j z hz

theorem exists_iso {φ : X' ⟶ X} (h : Propor s s' φ (𝟙 X')) (hc : ⨆ i, nonzeroLocus (s' i) = ⊤) :
    ∃ w : LB.Iso H' (H.pull φ), w.IsGen ∧ ∀ j z k k', φ z ∈ H.U k → z ∈ H'.U k' →
      gs φ z _ ((s j).f k) = (gw w (𝟙 X') z k k').val * gs (𝟙 X') z _ ((s' j).f k') := by
  choose u hu using fun k k' => exists_unit h hc k k'
  refine ⟨⟨fun p => u (p.1 PUnit.unit) p.2⟩, ?_, fun j z k k' hk hk' => hu k k' j z hk hk'⟩
  rintro ⟨J, k⟩ ⟨J', k'⟩
  apply unit_ext
  intro x hx
  have hj := mem_pull.1 hx.1.1
  have hj' := mem_pull.1 hx.2.1
  have this : gm (𝟙 X') x _ (u (J PUnit.unit) k) = gm (𝟙 X' ≫ φ) x _ (H.g (J PUnit.unit) (J' PUnit.unit)) *
      (gm (𝟙 X') x _ (H'.g k k'))⁻¹ * gm (𝟙 X') x _ (u (J' PUnit.unit) k') := by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hc.ge (Set.mem_univ x))
    have e := hu _ k i x hj hx.1.2
    rw [gs_compat (s i) φ x hj hj', gs_compat (s' i) (𝟙 X') x hx.1.2 hx.2.2, hu _ k' i x hj' hx.2.2,
      ← _root_.mul_assoc, ← _root_.mul_assoc] at e
    have e' := ((mem_nonzeroLocus_iff_isUnit _ hx.2.2).1 hi).mul_right_cancel e
    rw [Category.id_comp, mul_right_comm, eq_mul_inv_iff_mul_eq]
    exact Units.ext e'.symm
  rw [← gm_div_g (𝟙 X') x _ _ k k' hj hj' hx.1.2 hx.2.2] at this
  exact (gm_res _ x _ hx _).trans (this.trans ((map_mul _ _ _).trans (congrArg _ (gm_res _ x _ hx _))).symm)

end MapToProj


open MapToProj in
theorem exists_hom_of_veryAmpleBy : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (X' : Scheme.{0}) (f' : X' ⟶ Spec (CommRingCat.of R)) (H' : LB X') (s' : Fin (n + 1) → LB.Sec H'), H'.IsLB → (⨆ i, nonzeroLocus (s' i) = ⊤) → (∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → (∀ k : (H).ι, MvPolynomial.eval₂Hom (cst (f) ((H).U k)) (fun j => (s j).f k) (F) = 0) → (∀ k : (H').ι, MvPolynomial.eval₂Hom (cst (f') ((H').U k)) (fun j => (s' j).f k) (F) = 0)) → ∃ (φ : X' ⟶ X) (w : LB.Iso H' (H.pull φ)), φ ≫ f = f' ∧ w.IsGen ∧ (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) := by
  intro R _ X f H n s _ ⟨hc, hs⟩ X' f' H' s' _ hc' hv
  choose ha r hr hsur using hs
  have hv' : ∀ d, vanishingForms f s d ⊆ vanishingForms f' s' d := fun d F hF => ⟨hF.1, hv d F hF.1 hF.2⟩
  choose r' hr' using exists_isRatioFamily s'
  choose φ hf hφ using fun i => exists_local f f' (ha i) (hr i) (hsur i) (hr' i) (ker_le f f' hc ha r hr hv' i (hr' i))
  let 𝒰 := X'.openCoverOfIsOpenCover (fun i => nonzeroLocus (s' i)) hc'
  have hcomp : ∀ i j : Fin (n + 1), pullback.fst (nonzeroLocus (s' i)).ι (nonzeroLocus (s' j)).ι ≫ φ i =
      pullback.snd _ _ ≫ φ j := fun i j =>
    ((hφ i).comp _).unique f (by rw [pullback.condition]; exact (hφ j).comp _)
      (by rw [Category.assoc, Category.assoc, hf, hf, pullback.condition_assoc]) (ha i) (hr i) (hsur i)
      fun z => (pullback.fst (nonzeroLocus (s' i)).ι (nonzeroLocus (s' j)).ι z).2
  have hΦ : ∀ i : Fin (n + 1), (nonzeroLocus (s' i)).ι ≫ 𝒰.glueMorphisms φ hcomp = φ i :=
    fun i => 𝒰.ι_glueMorphisms φ hcomp i
  have hP : Propor s s' (𝒰.glueMorphisms φ hcomp) (𝟙 X') := Propor.of_local fun x => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc'.ge (Set.mem_univ x))
    exact ⟨_, hi, by rw [hΦ, Category.comp_id]; exact hφ i⟩
  obtain ⟨w, hw, H⟩ := exists_iso hP hc'
  refine ⟨_, w, 𝒰.hom_ext _ _ fun i => ?_, hw, H⟩
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) (hΦ i))).trans (hf i)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPwOfAffineLoci
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw

theorem veryAmpleBy_pw_of_affine_loci : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] (H : LB X) (n : ℕ) (t : Fin (n + 1) → LB.Sec H), H.IsLB → (⨆ i, nonzeroLocus (t i) = ⊤) → (∀ i, IsAffineOpen (nonzeroLocus (t i))) → ∃ d : ℕ, 1 ≤ d ∧ ∃ (n' : ℕ) (s : Fin (n' + 1) → LB.Sec (pw H d)), VeryAmpleBy f (pw H d) s := by
  intro R _ X f _ H n t hH hc ha
  have h : IsAmpleLB H :=
    isAmpleLB_of_cover hH le_rfl (fun i => secToPow (t i) 1)
      (by simp only [nonzeroLocus_secToPow _ le_rfl, hc])
      fun i => (nonzeroLocus_secToPow (t i) le_rfl).symm ▸ ha i
  have : IsProper (Over.mk f).hom := ‹IsProper f›
  exact (Unif.relAmple_iff_veryAmpleBy R (Over.mk f) H hH).1
    ((relAmple_iff_isAmpleLB_of_isAffine (Over.mk f) hH).2 h)

end GlobalTheory.AbLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FiniteMonotoneGrowth
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.VeryAmpleGrowth

variable {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K))

theorem top_add {M : LB X} (a b : SecOnR f M ⊤) (k : M.ι) :
    (SecOnR.topEquiv f M (a + b)).f k = (SecOnR.topEquiv f M a).f k + (SecOnR.topEquiv f M b).f k := by
  rw [SecOnR.topEquiv_f, SecOnR.topEquiv_f, SecOnR.topEquiv_f, SecOnR.coord_add, map_add (f := _)]

theorem top_smul {M : LB X} (c : K) (a : SecOnR f M ⊤) (k : M.ι) :
    (SecOnR.topEquiv f M (c • a)).f k = cst f (M.U k) c * (SecOnR.topEquiv f M a).f k := by
  rw [SecOnR.topEquiv_f, SecOnR.topEquiv_f, SecOnR.coord_base_smul, map_mul, rs_cst]

theorem top_ext {M : LB X} {a b : SecOnR f M ⊤}
    (h : ∀ k, (SecOnR.topEquiv f M a).f k = (SecOnR.topEquiv f M b).f k) : a = b :=
  (SecOnR.topEquiv f M).injective (by
    generalize SecOnR.topEquiv f M a = x at h ⊢
    generalize SecOnR.topEquiv f M b = y at h ⊢
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    obtain rfl : x = y := funext h
    rfl)

theorem top_zero {M : LB X} (k : M.ι) : (SecOnR.topEquiv f M 0).f k = 0 := by
  rw [SecOnR.topEquiv_f, SecOnR.coord_zero, map_zero]

def linTop {M : LB X} {V : Type} [AddCommGroup V] [Module K V] (φ : V → LB.Sec M)
    (hadd : ∀ a b k, (φ (a + b)).f k = (φ a).f k + (φ b).f k)
    (hsmul : ∀ (c : K) a k, (φ (c • a)).f k = cst f (M.U k) c * (φ a).f k) :
    V →ₗ[K] SecOnR f M ⊤ where
  toFun a := (SecOnR.topEquiv f M).symm (φ a)
  map_add' a b := top_ext f fun k => by
    simp only [top_add, LinearEquiv.apply_symm_apply, hadd]
  map_smul' c a := top_ext f fun k => by
    simp only [top_smul, LinearEquiv.apply_symm_apply, hsmul, RingHom.id_apply]

theorem top_linTop {M : LB X} {V : Type} [AddCommGroup V] [Module K V] (φ : V → LB.Sec M) (hadd hsmul)
    (a : V) : SecOnR.topEquiv f M (linTop f φ hadd hsmul a) = φ a :=
  (SecOnR.topEquiv f M).apply_symm_apply _

def mulPw {H : LB X} (s : LB.Sec H) (t : ℕ) (σ : LB.Sec (pw H t)) : LB.Sec (pw H (t + 1 : ℕ)) where
  f := fun k => s.f k * (show Γ(X, H.U k) from σ.f k)
  compat := fun k l => by
    have h₁ : rs X (inf_le_left : H.U k ⊓ H.U l ≤ H.U k) (s.f k) =
      (H.g k l).val * rs X (inf_le_right : H.U k ⊓ H.U l ≤ H.U l) (s.f l) := s.compat k l
    have h₂ : rs X (inf_le_left : H.U k ⊓ H.U l ≤ H.U k) (σ.f k) =
      (H.g k l ^ (t : ℤ)).val * rs X (inf_le_right : H.U k ⊓ H.U l ≤ H.U l) (σ.f l) := σ.compat k l
    change rs X (inf_le_left : H.U k ⊓ H.U l ≤ H.U k) (s.f k * (show Γ(X, H.U k) from σ.f k)) =
      (H.g k l ^ ((t + 1 : ℕ) : ℤ)).val *
        rs X (inf_le_right : H.U k ⊓ H.U l ≤ H.U l) (s.f l * (show Γ(X, H.U l) from σ.f l))
    rw [map_mul, map_mul, h₁, h₂, zpow_natCast, zpow_natCast, pow_succ, Units.val_mul]
    ring

def mulLin {H : LB X} (s : LB.Sec H) (t : ℕ) :
    SecOnR f (pw H t) ⊤ →ₗ[K] SecOnR f (pw H (t + 1 : ℕ)) ⊤ :=
  linTop f (fun a => mulPw s t (SecOnR.topEquiv f _ a))
    (fun a b k => (congrArg (fun y : Γ(X, H.U k) => s.f k * y) (top_add f a b k)).trans
      (mul_add (s.f k) (show Γ(X, H.U k) from (SecOnR.topEquiv f (pw H t) a).f k)
        (show Γ(X, H.U k) from (SecOnR.topEquiv f (pw H t) b).f k)))
    (fun c a k => (congrArg (fun y : Γ(X, H.U k) => s.f k * y) (top_smul f c a k)).trans
      (mul_left_comm _ _ _))

theorem top_mulLin {H : LB X} (s : LB.Sec H) (t : ℕ) (a : SecOnR f (pw H t) ⊤) :
    SecOnR.topEquiv f (pw H (t + 1 : ℕ)) (mulLin f s t a) = mulPw s t (SecOnR.topEquiv f (pw H t) a) :=
  top_linTop f _ _ _ a

theorem mulLin_injective [IsIntegral X] {H : LB X} (s : LB.Sec H) {x : X} (hx : x ∈ nonzeroLocus s) (t : ℕ) :
    Function.Injective (mulLin f s t) := by
  obtain ⟨k₀, hk₀⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  let W : X.Opens := X.basicOpen (s.f k₀)
  have hWU : W ≤ H.U k₀ := X.basicOpen_le _
  haveI : Nonempty W := ⟨⟨x, hk₀⟩⟩
  have hu : IsUnit (rs X hWU (s.f k₀)) := X.toRingedSpace.isUnit_res_basicOpen _
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  have h : s.f k₀ * (show Γ(X, H.U k₀) from (SecOnR.topEquiv f (pw H t) a).f k₀) = 0 := by
    have e := top_mulLin f s t a
    rw [ha] at e
    exact (congrArg (fun σ : LB.Sec (pw H (t + 1 : ℕ)) => σ.f k₀) e).symm.trans
      (top_zero f (M := pw H (t + 1 : ℕ)) k₀)
  have h' := congrArg (rs X hWU) h
  rw [map_mul, map_zero, hu.mul_right_eq_zero] at h'
  exact top_ext f fun k =>
    (SecGrowth.sec_eq_zero (M := pw H t) (SecOnR.topEquiv f _ a) (k₀ := k₀) hWU h' k).trans
      (top_zero f k).symm

theorem finite_of_polynomial {H : LB X} {m : ℕ} (s : Fin (m + 1) → LB.Sec H) (t : ℕ)
    (h : ∀ σ : LB.Sec (pw H t), ∃ F : MvPolynomial (Fin (m + 1)) K, F.IsHomogeneous t ∧
      ∀ k : H.ι, σ.f k = MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k) F) :
    Module.Finite K (SecOnR f (pw H t) ⊤) := by
  haveI : Module.Finite K (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K t) :=
    Submodule.finiteDimensional_of_le (S₂ := MvPolynomial.restrictTotalDegree (Fin (m + 1)) K t)
      fun F hF => (MvPolynomial.mem_restrictTotalDegree _ _ _).2
        (MvPolynomial.IsHomogeneous.totalDegree_le hF)
  refine Module.Finite.of_surjective
    (linTop f (V := MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K t)
      (fun F => SecGrowth.polySec f s F.2)
      (fun a b k => map_add (MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k)) a.1 b.1)
      (fun c a k => ?_)) fun a => ?_
  · change MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k) (c • a.1) =
      cst f (H.U k) c * MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k) a.1
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval₂Hom_C]
  · obtain ⟨F, hF, hFa⟩ := h (SecOnR.topEquiv f _ a)
    refine ⟨⟨F, hF⟩, top_ext f fun k => ?_⟩
    exact (congrArg (fun σ : LB.Sec (pw H t) => σ.f k) (top_linTop f _ _ _ _)).trans (hFa k).symm

theorem finite_monotone_growth : ∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K)) (g : ℕ), SmoothOfRelativeDimension g f → ∀ (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → (∀ t : ℕ, Module.Finite K (SecOnR f (pw H t) ⊤)) ∧ (∀ t t' : ℕ, t ≤ t' → Module.finrank K (SecOnR (f) (pw H t) ⊤) ≤ Module.finrank K (SecOnR (f) (pw H t') ⊤)) ∧ ∃ c C : ℕ, 1 ≤ c ∧ ∀ t : ℕ, 1 ≤ t → t ^ g ≤ c * Module.finrank K (SecOnR (f) (pw H t) ⊤) ∧ Module.finrank K (SecOnR (f) (pw H t) ⊤) ≤ C * t ^ g := by
  intro K _ X _ f g hf H n s hH hs
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.exists_homogeneousForm_eq_highPowerSection K X f H n s hH hs
  obtain ⟨x⟩ : Nonempty X := inferInstance
  have hx : x ∈ ⨆ i, nonzeroLocus (s i) := by rw [hs.1]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have hinj := mulLin_injective f (s i) hi
  have hfin : ∀ t : ℕ, Module.Finite K (SecOnR f (pw H t) ⊤) := fun t => by
    have h : ∀ d t : ℕ, t₀ ≤ t + d → Module.Finite K (SecOnR f (pw H t) ⊤) := by
      intro d
      induction d with
      | zero => exact fun t ht => finite_of_polynomial f s t (ht₀ t ht)
      | succ d ih =>
        intro t ht
        haveI := ih (t + 1) (by omega)
        exact Module.Finite.of_injective _ (hinj t)
    exact h t₀ t (Nat.le_add_left _ _)
  refine ⟨hfin, fun t t' h => ?_, ?_⟩
  · exact monotone_nat_of_le_succ (f := fun t : ℕ => Module.finrank K (SecOnR f (pw H t) ⊤))
      (fun t => LinearMap.finrank_le_finrank_of_injective (hinj t)) h
  · exact SecGrowth.growth_of_veryAmpleBy f s hs g t₀ ht₀
      (fun B _ _ _ r => finrank_totalDegree_image_growth K B _ _ r)
      (trdeg_eq_of_smoothOfRelativeDimension K X f g hf)
      (fun t => SecOnR f (pw H t) ⊤) (fun t => SecOnR.topEquiv f _)
      (fun t a b k => top_add f a b k) (fun t c a k => top_smul f c a k)
      (fun t a ha => top_ext f fun k => (ha k).trans (top_zero f k).symm)
      (fun t σ => ⟨(SecOnR.topEquiv f _).symm σ, fun k => by rw [LinearEquiv.apply_symm_apply]⟩)

end GlobalTheory.VeryAmpleGrowth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSec
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SecAlg

variable {X X₁ X₂ Z : Scheme.{0}} {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂]

def germCst (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (a : R) : Z.presheaf.stalk z :=
  gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)

theorem germCst_comp (q : Z ⟶ Spec (CommRingCat.of R₂)) (h : R₁ →+* R₂) (z : Z) (a : R₁) :
    germCst (q ≫ Spec.map (CommRingCat.ofHom h)) z a = germCst q z (h a) := by
  refine (gs_pull q (Spec.map (CommRingCat.ofHom h)) z ⊤ trivial _).symm.trans ?_
  exact congrArg (gs q z ⊤) (congrArg (fun t => t.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom h))).symm

theorem gs_cst (p : X ⟶ Spec (CommRingCat.of R)) (W : X.Opens) (r : Z ⟶ X) (z : Z) (hz : r z ∈ W) (a : R) :
    gs r z W (GlobalTheory.AbLaw.cst p W a) = germCst (r ≫ p) z a :=
  (gs_res r z le_top hz _).trans (gs_pull r p z ⊤ trivial _)

variable {p : X ⟶ Spec (CommRingCat.of R)} {N : LB X} (P : Perf p N)

def Given (π : X₁ ⟶ X) (f : X₁ ⟶ Spec (CommRingCat.of R₁)) (v : Fin P.a → R₁) (s : LB.Sec (N.pull π)) : Prop :=
  ∀ i, rs X₁ (le_pull N π (P.le i)) (s.f (fun _ => P.ch i)) =
    ∑ k, GlobalTheory.AbLaw.cst f (π ⁻¹ᵁ P.W i) (v k) * (π.app (P.W i)).hom (P.u k i)

def comb (ψ : Z ⟶ X) (z : Z) (J : (Z ⟶ X) → N.ι) (i : P.I) (c : Fin P.a → Z.presheaf.stalk z) :
    Z.presheaf.stalk z :=
  (gm ψ z (N.U (J ψ) ⊓ N.U (P.ch i)) (N.g (J ψ) (P.ch i))).val * ∑ k, c k * gs ψ z (P.W i) (P.u k i)

variable {P}

theorem Given.sval {π : X₁ ⟶ X} {f : X₁ ⟶ Spec (CommRingCat.of R₁)} {v : Fin P.a → R₁} {s : LB.Sec (N.pull π)}
    (hs : Given P π f v s) (r : Z ⟶ X₁) (z : Z) {J : (Z ⟶ X) → N.ι} (hJ : Good N z J) (i : P.I)
    (hi : (r ≫ π) z ∈ P.W i) :
    sval s r z J = comb P (r ≫ π) z J i (fun k => germCst (r ≫ f) z (v k)) := by
  have hm : r z ∈ π ⁻¹ᵁ P.W i := hi
  refine (sec_trans s r z (hJ.mem _ r) (le_pull N π (P.le i) hm)).trans (congrArg₂ (· * ·) ?_ ?_)
  · simp only [trF, Finset.univ_unique, Finset.prod_singleton, zpow_one]
  · refine (gs_res r z (le_pull N π (P.le i)) hm _).symm.trans ((congrArg (gs r z _) (hs i)).trans ?_)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [gs_eq r z _ hm, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => (gs_eq r z _ hm _).symm.trans ((gs_mul r z _ hm _ _).trans ?_)
    exact congrArg₂ (· * ·) (gs_cst f _ r z hm _) (gs_pull r π z _ hi _)

theorem Given.sval_eq {π₁ : X₁ ⟶ X} {f₁ : X₁ ⟶ Spec (CommRingCat.of R₁)} {v : Fin P.a → R₁}
    {s₁ : LB.Sec (N.pull π₁)} {π₂ : X₂ ⟶ X} {f₂ : X₂ ⟶ Spec (CommRingCat.of R₂)} {s₂ : LB.Sec (N.pull π₂)}
    (h : R₁ →+* R₂) (r : X₂ ⟶ X₁) (hπ : r ≫ π₁ = π₂) (hf : r ≫ f₁ = f₂ ≫ Spec.map (CommRingCat.ofHom h))
    (h₁ : Given P π₁ f₁ v s₁) (h₂ : Given P π₂ f₂ (fun k => h (v k)) s₂) (z : X₂) {J : (X₂ ⟶ X) → N.ι}
    (hJ : Good N z J) : Geo.Tor.sval s₁ r z J = Geo.Tor.sval s₂ (𝟙 _) z J := by
  subst hπ
  have hz : (r ≫ π₁) z ∈ ⨆ i, P.W i := by rw [P.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  rw [h₁.sval r z hJ i hi, h₂.sval (𝟙 _) z hJ i hi, Category.id_comp, Category.id_comp, hf]
  simp only [germCst_comp]

theorem sec_ext {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  obtain ⟨a, ha⟩ := s
  obtain ⟨b, hb⟩ := s'
  obtain rfl : a = b := funext h
  rfl

theorem mulVec_map {a b : ℕ} (D : Matrix (Fin b) (Fin a) R) (g : R →+* R₁) (h : R₁ →+* R₂) {g' : R →+* R₂}
    (hg : h.comp g = g') (v : Fin a → R₁) (j : Fin b) :
    (D.map g').mulVec (fun k => h (v k)) j = h ((D.map g).mulVec v j) := by
  subst hg
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, RingHom.comp_apply]

theorem sval_eq_iff (hN : N.IsLB) {g₁ : R →+* R₁} {g₂ : R →+* R₂}
    {π₁ : X₁ ⟶ X} {f₁ : X₁ ⟶ Spec (CommRingCat.of R₁)} {π₂ : X₂ ⟶ X} {f₂ : X₂ ⟶ Spec (CommRingCat.of R₂)}
    {E₁ : {v : Fin P.a → R₁ // (P.D₀.map g₁).mulVec v = 0} ≃ LB.Sec (N.pull π₁)}
    {E₂ : {v : Fin P.a → R₂ // (P.D₀.map g₂).mulVec v = 0} ≃ LB.Sec (N.pull π₂)}
    (H₁ : ∀ v, Given P π₁ f₁ v.1 (E₁ v)) (H₂ : ∀ v, Given P π₂ f₂ v.1 (E₂ v))
    (h : R₁ →+* R₂) (hg : h.comp g₁ = g₂) (r : X₂ ⟶ X₁) (hπ : r ≫ π₁ = π₂)
    (hf : r ≫ f₁ = f₂ ≫ Spec.map (CommRingCat.ofHom h)) (s₁ : LB.Sec (N.pull π₁)) (s₂ : LB.Sec (N.pull π₂)) :
    (∀ z J, Good N z J → sval s₁ r z J = sval s₂ (𝟙 _) z J) ↔
      ∀ k, h ((E₁.symm s₁).1 k) = (E₂.symm s₂).1 k := by
  obtain ⟨v₁, rfl⟩ := E₁.surjective s₁
  obtain ⟨v₂, rfl⟩ := E₂.surjective s₂
  rw [E₁.symm_apply_apply, E₂.symm_apply_apply]
  let w : {v : Fin P.a → R₂ // (P.D₀.map g₂).mulVec v = 0} := ⟨fun k => h (v₁.1 k), funext fun j => by
    rw [mulVec_map P.D₀ g₁ h hg, v₁.2, Pi.zero_apply, Pi.zero_apply, map_zero]⟩
  have key : ∀ z J, Good N z J → sval (E₁ v₁) r z J = sval (E₂ w) (𝟙 _) z J :=
    fun z J hJ => Given.sval_eq h r hπ hf (H₁ v₁) (H₂ w) z hJ
  constructor
  · intro H k
    have : E₂ w = E₂ v₂ := sec_ext (sec_ext_val hN fun y J hJ => (key y J hJ).symm.trans (H y J hJ))
    exact congrFun (congrArg Subtype.val (E₂.injective this)) k
  · intro H
    obtain rfl : w = v₂ := Subtype.ext (funext H)
    exact key

theorem eq_of_forall_mk (I : Ideal R) [IsHausdorff I R] {x y : R}
    (h : ∀ e : ℕ, Ideal.Quotient.mk (I ^ (e + 1)) x = Ideal.Quotient.mk (I ^ (e + 1)) y) : x = y := by
  refine sub_eq_zero.1 (IsHausdorff.haus' (I := I) _ fun n => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.Quotient.eq.1 (h n))

theorem exists_lim (I : Ideal R) [IsPrecomplete I R] (x : ∀ e : ℕ, R ⧸ I ^ (e + 1))
    (hx : ∀ e, Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) (x (e + 1)) = x e) :
    ∃ y : R, ∀ e, Ideal.Quotient.mk (I ^ (e + 1)) y = x e := by
  choose a ha using fun e => Ideal.Quotient.mk_surjective (x e)
  have step : ∀ e, a e - a (e + 1) ∈ I ^ (e + 1) := fun e => by
    refine Ideal.Quotient.eq.1 ?_
    rw [ha, ← hx e, ← ha (e + 1), Ideal.Quotient.factor_mk]
  have cau : ∀ m n, m ≤ n → a m - a n ∈ I ^ (m + 1) := fun m n hmn => by
    induction n, hmn using Nat.le_induction with
    | base => rw [sub_self]; exact zero_mem _
    | succ n hmn ih =>
      have := add_mem ih (Ideal.pow_le_pow_right (Nat.succ_le_succ hmn) (step n))
      rwa [sub_add_sub_cancel] at this
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) a (fun {m n} hmn => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    exact Ideal.pow_le_pow_right (Nat.le_succ m) (cau m n hmn))
  refine ⟨L, fun e => ?_⟩
  have := hL (e + 1)
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  have h₂ := add_mem (step e) this
  rw [sub_add_sub_cancel] at h₂
  rw [← ha e]
  exact (Ideal.Quotient.eq.2 h₂).symm

theorem existsUnique_sec : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : Over (Spec (CommRingCat.of R))), Smooth Y.hom → IsProjBy Y.hom → ∀ N : LB Y.left, N.IsLB → ∀ f : ∀ e, LB.Sec (N.pull (fstG I e Y).left), (∀ e z J, Good N z J → sval (f (e + 1)) (thickMap R I e Y) z J = sval (f e) (𝟙 _) z J) → ∃! s : LB.Sec (N.pull (𝟙 Y.left)), ∀ e z J, Good N z J → sval s (fstG I e Y).left z J = sval (f e) (𝟙 _) z J := by
  intro R _ _ I hI Y hs hp N hN f hf
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj R Y.left Y.hom hs hp N hN
  have pb₀ : IsPullback (𝟙 Y.left) Y.hom Y.hom (Spec.map (CommRingCat.ofHom (RingHom.id R))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨E₀, H₀⟩ := P.sec R (RingHom.id R) Y.left (𝟙 _) Y.hom pb₀
  choose E H using fun e => P.sec (R ⧸ I ^ (e + 1)) (Ideal.Quotient.mk _) _ (fstG I e Y).left
    (thickObj R I e Y).hom (IsPullback.of_hasPullback Y.hom (thick R I e))
  have c₁ : ∀ e k, Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)))
      (((E (e + 1)).symm (f (e + 1))).1 k) = ((E e).symm (f e)).1 k := fun e =>
    (sval_eq_iff (P := P) hN (H (e + 1)) (H e) _ (Ideal.Quotient.factor_comp_mk _) (thickMap R I e Y)
      ((pullback.lift_fst _ _ _).trans (Category.comp_id _)) (pullback.lift_snd _ _ _) _ _).1 (hf e)
  have c₂ : ∀ e (s : LB.Sec (N.pull (𝟙 Y.left))),
      (∀ z J, Good N z J → sval s (fstG I e Y).left z J = sval (f e) (𝟙 _) z J) ↔
        ∀ k, Ideal.Quotient.mk (I ^ (e + 1)) ((E₀.symm s).1 k) = ((E e).symm (f e)).1 k := fun e s =>
    sval_eq_iff (P := P) hN H₀ (H e) _ (RingHom.comp_id _) (fstG I e Y).left (Category.comp_id _)
      pullback.condition _ _
  choose v hv using fun k => exists_lim I (fun e => ((E e).symm (f e)).1 k) (fun e => c₁ e k)
  have hv₀ : (P.D₀.map (RingHom.id R)).mulVec v = 0 := funext fun j => eq_of_forall_mk I fun e => by
    rw [← mulVec_map P.D₀ (RingHom.id R) _ (RingHom.comp_id _), Pi.zero_apply, map_zero]
    simp only [hv]
    exact congrFun ((E e).symm (f e)).2 j
  refine ⟨E₀ ⟨v, hv₀⟩, fun e => (c₂ e _).2 fun k => ?_, fun s hs => ?_⟩
  · rw [E₀.symm_apply_apply]
    exact hv k e
  · refine (E₀.symm_apply_eq).1 (Subtype.ext (funext fun k => eq_of_forall_mk I fun e => ?_))
    exact ((c₂ e s).1 (hs e) k).trans (hv k e).symm

end GlobalTheory.SecAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSymmetricVeryAmpleBy
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymVeryAmple


open GlobalTheory.CechPic in
theorem exists_of_involution {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (σ : X ⟶ X) (hσ : σ ≫ σ = 𝟙 X) (h : IsProjBy f) :
    ∃ (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB ∧ VeryAmpleBy f H s ∧
      Triv (LB.LinComb H (K := Fin 2) ![σ, 𝟙 X] ![1, -1]) := by
  obtain ⟨L, hL, m, s, hs⟩ := h
  have : IsProper f := isProper_of_veryAmpleBy hs
  have : IsIso σ := ⟨σ, hσ, hσ⟩
  have hA : IsAmpleLB L := isAmpleLB_of_veryAmpleBy hs
  have hP : IsAmpleLB (L.pull σ) := hA.pull_of_isAffineHom σ
  have hN : (tens L (L.pull σ)).IsLB := isLB_tens hL hP.isLB
  have hT : IsAmpleLB (tens L (L.pull σ)) := by
    refine hA.tensor hP hN ((cls_eq_zero_iff (LB.isLB_div (LB.isLB_div hN hL) hP.isLB)).1 ?_)
    rw [cls_div (LB.isLB_div hN hL) hP.isLB, cls_div hN hL, cls_tens hL hP.isLB]
    abel
  obtain ⟨n, -, M, t, ht⟩ := hT.exists_veryAmpleBy f
  have hH := isLB_lbPow hN n
  refine ⟨_, M, t, hH, ht, (cls_eq_zero_iff (LB.isLB_linComb hH _ _)).1 ?_⟩
  rw [cls_linComb hH, Fin.sum_univ_two, cls_lbPow hN, cls_tens hL hP.isLB, cls_pull hL]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_id, map_nsmul, map_add (f := _), ← pull_comp, hσ]
  rw [add_comm (pull σ (cls L hL)), one_zsmul, neg_one_zsmul, Category.id_comp, add_neg_cancel]

theorem exists_symmetric_veryAmpleBy : ∀ (R : Type) [CommRing R] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∃ (H : LB B.left) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB ∧ VeryAmpleBy B.hom H s ∧ Triv (LB.LinComb H (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]) := by
  intro R _ B _ _ _ h
  refine exists_of_involution B.hom _ ?_ h
  rw [← Over.comp_left, GrpObj.inv_comp_inv, Over.id_left]

end GlobalTheory.SymVeryAmple
end
