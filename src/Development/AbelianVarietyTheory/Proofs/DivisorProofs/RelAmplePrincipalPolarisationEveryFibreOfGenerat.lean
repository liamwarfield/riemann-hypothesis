module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithAmbientVerticalOrArithmeticVariety

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleKernelTrivialOfSameImagePoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleKernelTrivialOfSameImagePoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.FibreTransfer

theorem exists_residueField_factor (S : Scheme.{0}) (p : S) (K : Type) [Field K] (x : Sp K ⟶ S)
    (hx : x (closedPoint K) = p) :
    ∃ θ : S.residueField p ⟶ CommRingCat.of K, Spec.map θ ≫ S.fromSpecResidueField p = x := by
  subst hx
  exact ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K S x⟩

theorem isGrpPullback_fibre {S : Scheme.{0}} (G : Over S) [GrpObj G] (p : S) (K : Type) [Field K]
    (θ : S.residueField p ⟶ CommRingCat.of K) :
    IsGrpPullback ((Over.pullback (Spec.map θ ≫ S.fromSpecResidueField p)).obj G)
      ((Over.pullback (S.fromSpecResidueField p)).obj G) (Spec.map θ)
      (pullback.lift (pullback.fst G.hom _) (pullback.snd G.hom _ ≫ Spec.map θ)
        (by rw [pullback.condition, Category.assoc])) := by
  refine (isGrpPullback_pullback G (S.fromSpecResidueField p)).cancel
    ((isGrpPullback_pullback G (Spec.map θ ≫ S.fromSpecResidueField p)).congr rfl
      (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)

theorem lbIso_fibre {S : Scheme.{0}} (G : Over S) {L : LB G.left} (hL : L.IsLB) (p : S) (K : Type) [Field K]
    (θ : S.residueField p ⟶ CommRingCat.of K) :
    LBIso (L.pull (pullback.fst G.hom (Spec.map θ ≫ S.fromSpecResidueField p)))
      ((L.pull (pullback.fst G.hom (S.fromSpecResidueField p))).pull
        (pullback.lift (pullback.fst G.hom _) (pullback.snd G.hom _ ≫ Spec.map θ)
          (by rw [pullback.condition, Category.assoc]))) := by
  have e := GlobalTheory.FibreAmple.lbIso_pull_pull hL
    (pullback.lift (pullback.fst G.hom (Spec.map θ ≫ S.fromSpecResidueField p))
      (pullback.snd G.hom _ ≫ Spec.map θ) (by rw [pullback.condition, Category.assoc]))
    (pullback.fst G.hom (S.fromSpecResidueField p))
  rw [pullback.lift_fst] at e
  exact e.symm

end GlobalTheory.FibreTransfer


open GlobalTheory.FibreTransfer in
theorem GlobalTheory.FibreTransfer.relAmple_kTriv_of_same_point : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], QuasiCompact G.hom → IsSeparated G.hom → Smooth G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (K₁ : Type) [Field K₁] (z : Sp K₁ ⟶ S), IsProper (pullback.snd G.hom z) → RelAmple ((Over.pullback z).obj G) (L.pull (pullback.fst G.hom z)) → KTriv ((Over.pullback z).obj G) (L.pull (pullback.fst G.hom z)) → ∀ (K : Type) [Field K] (x : Sp K ⟶ S), x (closedPoint K) = z (closedPoint K₁) → RelAmple ((Over.pullback x).obj G) (L.pull (pullback.fst G.hom x)) ∧ KTriv ((Over.pullback x).obj G) (L.pull (pullback.fst G.hom x)) := by
  intro S G _ hqc hsep hsm L hL K₁ _ z hP hA hK K _ x hx
  generalize hy : z (closedPoint K₁) = y at hx
  obtain ⟨θ₁, hz⟩ := exists_residueField_factor S y K₁ z hy
  obtain ⟨θ, rfl⟩ := exists_residueField_factor S y K x hx
  clear hy
  subst hz
  haveI := hqc; haveI := hsep; haveI := hsm
  have hLy := pull_isLB hL (pullback.fst G.hom (S.fromSpecResidueField y))
  have i₁ : QuasiCompact ((Over.pullback (S.fromSpecResidueField y)).obj G).hom :=
    show QuasiCompact (pullback.snd G.hom _) from inferInstance
  have i₂ : IsSeparated ((Over.pullback (S.fromSpecResidueField y)).obj G).hom :=
    show IsSeparated (pullback.snd G.hom _) from inferInstance
  have i₃ : Smooth ((Over.pullback (S.fromSpecResidueField y)).obj G).hom :=
    show Smooth (pullback.snd G.hom _) from inferInstance
  have hd := GlobalTheory.AmpleDescent.proper_relAmple_kTriv_of_fieldExtension (S.residueField y) K₁ θ₁.hom
    ((Over.pullback (S.fromSpecResidueField y)).obj G) ((Over.pullback (Spec.map θ₁ ≫ S.fromSpecResidueField y)).obj G) _
    (isGrpPullback_fibre G y K₁ θ₁) _ _ hLy (pull_isLB hL _) (lbIso_fibre G hL y K₁ θ₁) hP hA hK
  have h₂ := isGrpPullback_fibre G y K θ
  obtain ⟨w, hw⟩ := lbIso_fibre G hL y K θ
  exact ⟨relAmple_pull h₂.1 hLy (pull_isLB hL _) ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) hd.2.1,
    kTriv_pull h₂ hLy (pull_isLB hL _) ((isGen_iff w).1 hw) hd.2.2⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleKernelTrivialOfSameImagePointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_kernelTrivial_of_same_image_point : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], QuasiCompact G.hom → IsSeparated G.hom → Smooth G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (K₁ : Type) [Field K₁] (z : Sp K₁ ⟶ S), IsProper (pullback.snd G.hom z) → RelAmple ((Over.pullback z).obj G) (L.pull (pullback.fst G.hom z)) → KTriv ((Over.pullback z).obj G) (L.pull (pullback.fst G.hom z)) → ∀ (K : Type) [Field K] (x : Sp K ⟶ S), x (closedPoint K) = z (closedPoint K₁) → RelAmple ((Over.pullback x).obj G) (L.pull (pullback.fst G.hom x)) ∧ KTriv ((Over.pullback x).obj G) (L.pull (pullback.fst G.hom x)) := by
  first | exact @GlobalTheory.FibreTransfer.relAmple_kTriv_of_same_point | exact GlobalTheory.FibreTransfer.relAmple_kTriv_of_same_point | (intros; apply GlobalTheory.FibreTransfer.relAmple_kTriv_of_same_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFieldPointPolarisedFibreUniformised
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFieldPointPolarisedFibreUniformised
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PolPoint

theorem isProper_of_image {S T : Scheme.{0}} (A : Over S) (B : Over T) (g : T ⟶ S) (φ : B.left ⟶ A.left)
    (h : IsPullback φ B.hom A.hom g) (W : S.Opens) (hg : ∀ t, g t ∈ W) (hpr : IsProper (A.hom ∣_ W)) :
    IsProper B.hom := by
  have hr : Set.range g ⊆ Set.range W.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hg y
  have hr' : Set.range φ ⊆ Set.range (A.hom ⁻¹ᵁ W).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    show A.hom (φ y) ∈ W
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
    exact hg _
  let l := IsOpenImmersion.lift W.ι _ hr
  let ψ := IsOpenImmersion.lift (A.hom ⁻¹ᵁ W).ι φ hr'
  have hl : l ≫ W.ι = g := IsOpenImmersion.lift_fac _ _ hr
  have hψ : ψ ≫ (A.hom ⁻¹ᵁ W).ι = φ := IsOpenImmersion.lift_fac _ _ hr'
  have big : IsPullback (ψ ≫ (A.hom ⁻¹ᵁ W).ι) B.hom A.hom (l ≫ W.ι) := by rw [hψ, hl]; exact h
  have sq : IsPullback ψ B.hom (A.hom ∣_ W) l := by
    refine IsPullback.of_right big ?_ (isPullback_morphismRestrict A.hom W).flip
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hψ, h.w, Category.assoc, hl]
  exact MorphismProperty.of_isPullback (P := @IsProper) sq hpr

theorem exists_field_point_polarised : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ W : (Sp R).Opens, IsProper (G.hom ∣_ W) → ∀ y : PrimeSpectrum R, y ∈ W → y.asIdeal ≠ ⊥ → ∃ (K₁ : Type) (_ : Field K₁) (z : Sp K₁ ⟶ Sp R), z (closedPoint K₁) = y ∧ IsProper (pullback.snd G.hom z) ∧ RelAmple ((Over.pullback z).obj G) (U.LG.L.pull (pullback.fst G.hom z)) ∧ KTriv ((Over.pullback z).obj G) (U.LG.L.pull (pullback.fst G.hom z)) := by
  intro R _ _ _ hR D A G _ _ hG U W hW y hyW hy
  obtain ⟨⟨hN, -, -, -⟩, -⟩ := hR
  let O := Localization.AtPrime y.asIdeal
  have hiO : Function.Injective (algebraMap R O) :=
    IsLocalization.injective O y.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : IsDomain O := IsLocalization.isDomain_localization y.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : IsNoetherianRing O := IsLocalization.isNoetherianRing y.asIdeal.primeCompl O hN
  have hf : ¬ IsField O := by
    intro hfO
    apply hy
    have h1 : maximalIdeal O = ⊥ := (IsLocalRing.isField_iff_maximalIdeal_eq).1 hfO
    have h2 := Localization.AtPrime.under_maximalIdeal (I := y.asIdeal)
    rw [← h2, Ideal.under, h1]
    exact Ideal.comap_bot_of_injective _ hiO
  obtain ⟨V, _, _, _, ρ, hρ, hloc⟩ := GlobalTheory.KTrivSpread.exists_dvr O hf
  let a : R →+* V := ρ.comp (algebraMap R O)
  have ha : Function.Injective a := hρ.comp hiO
  have hgen : ∀ q : PrimeSpectrum V, spMap a q ∈ W := by
    intro q
    have hle : PrimeSpectrum.comap a q ≤ y := by
      show Ideal.comap a q.asIdeal ≤ y.asIdeal
      intro s hs
      rw [← Localization.AtPrime.under_maximalIdeal (I := y.asIdeal)]
      exact IsLocalRing.le_maximalIdeal (q.isPrime.comap ρ).ne_top hs
    exact ((PrimeSpectrum.le_iff_specializes _ _).1 hle).mem_open W.isOpen hyW
  let B := (Over.pullback (spMap a)).obj G
  have hcart : IsPullback (pullback.fst G.hom (spMap a)) B.hom G.hom (spMap a) := IsPullback.of_hasPullback _ _
  have hpB : IsProper B.hom := isProper_of_image G B (spMap a) _ hcart W hgen hW
  have hsB := IsSemiAbelian.pullback (spMap a) G hG
  have hAb : IsAbelianScheme B := ⟨hsB.comm, hsB.smooth, hpB, hsB.geomConnected⟩
  obtain ⟨hL, hL2, -⟩ := GlobalTheory.allSixLaws
  let M := GlobalTheory.ValueForm.modelCP U.toUnifPre hL.globalFns
  let φ := U.gen.inv.left ≫ pullback.fst G.hom (jK R)
  have hφ : IsGrpPullback A.A G (spMap (algebraMap R (FractionRing R))) φ :=
    GlobalTheory.ThetaBaseChange.grp_generic U.toUnifPre
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hLφ : LBIso A.L (M.L.L.pull φ) := LBIso.chartPull (h := U.gen.inv.left) (chartPullSec A.L _ _ hgi)
    (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => rfl) U.ext
  obtain ⟨P', M', φ', hφ', hL', hM'⟩ :=
    GlobalTheory.PolExtendDVR.exists_baseChange (K' := FractionRing V) hL.polBaseChange a ha A G M φ hφ hLφ
  obtain ⟨hAB, hKB⟩ := GlobalTheory.polarisation_extends_dvr hL hL2 V (FractionRing V) P' B M' φ' hAb hφ' hL'
  let r := IsLocalRing.residue V
  obtain ⟨z, hz0⟩ : ∃ z : Sp (IsLocalRing.ResidueField V) ⟶ Sp R, z = spMap (r.comp a) := ⟨_, rfl⟩
  have hz : z = spMap r ≫ spMap a := by
    rw [hz0]
    unfold spMap
    rw [← Spec.map_comp]
    rfl
  let ψ : pullback G.hom z ⟶ B.left := pullback.lift (pullback.fst G.hom z) (pullback.snd G.hom z ≫ spMap r)
    (by rw [pullback.condition, hz, Category.assoc])
  have hψ : ψ ≫ pullback.fst G.hom (spMap a) = pullback.fst G.hom z := pullback.lift_fst _ _ _
  have hψ2 : ψ ≫ B.hom = ((Over.pullback z).obj G).hom ≫ spMap r := pullback.lift_snd _ _ _
  have hgz : IsGrpPullback ((Over.pullback z).obj G) B (spMap r) ψ :=
    (isGrpPullback_pullback G (spMap a)).cancel ((isGrpPullback_pullback G z).congr hz hψ.symm) hψ2
  have hiso : LBIso (U.LG.L.pull (pullback.fst G.hom z)) (M'.L.L.pull ψ) := by
    have e := GlobalTheory.PolExtendDVR.lbIso_pull_comp hM' ψ
    rw [hψ] at e
    exact e.symm
  obtain ⟨w, hw⟩ := hiso
  have hw' := (isGen_iff w).1 hw
  refine ⟨IsLocalRing.ResidueField V, inferInstance, z, ?_, ?_, ?_, ?_⟩
  · have e1 : PrimeSpectrum.comap r (IsLocalRing.closedPoint (IsLocalRing.ResidueField V)) =
        IsLocalRing.closedPoint V := IsLocalRing.comap_closedPoint r
    have e2 : PrimeSpectrum.comap ρ (IsLocalRing.closedPoint V) = IsLocalRing.closedPoint O :=
      IsLocalRing.comap_closedPoint ρ
    have e3 : PrimeSpectrum.comap (algebraMap R O) (IsLocalRing.closedPoint O) = y :=
      PrimeSpectrum.ext Localization.AtPrime.under_maximalIdeal
    rw [hz0]
    show PrimeSpectrum.comap (algebraMap R O) (PrimeSpectrum.comap ρ
      (PrimeSpectrum.comap r (IsLocalRing.closedPoint (IsLocalRing.ResidueField V)))) = y
    rw [e1, e2, e3]
  · exact MorphismProperty.of_isPullback (P := @IsProper) hgz.1 hpB
  · exact relAmple_pull hgz.1 M'.L.isLB (pull_isLB U.LG.isLB _) hw' ⊤ (isAffineOpen_top _) (fun _ => trivial) hAB
  · exact kTriv_pull hgz M'.L.isLB (pull_isLB U.LG.isLB _) hw' hKB

end GlobalTheory.PolPoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFieldPointPolarisedFibreUniformisedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fieldPoint_polarised_fibre_uniformised : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ W : (Sp R).Opens, IsProper (G.hom ∣_ W) → ∀ y : PrimeSpectrum R, y ∈ W → y.asIdeal ≠ ⊥ → ∃ (K₁ : Type) (_ : Field K₁) (z : Sp K₁ ⟶ Sp R), z (closedPoint K₁) = y ∧ IsProper (pullback.snd G.hom z) ∧ RelAmple ((Over.pullback z).obj G) (U.LG.L.pull (pullback.fst G.hom z)) ∧ KTriv ((Over.pullback z).obj G) (U.LG.L.pull (pullback.fst G.hom z)) := by
  first | exact @GlobalTheory.PolPoint.exists_field_point_polarised | exact GlobalTheory.PolPoint.exists_field_point_polarised | (intros; apply GlobalTheory.PolPoint.exists_field_point_polarised <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmplePrincipalPolarisationEveryFibreOfGenerat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.PolFibre

theorem generic_fibre {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : Unif (maximalIdeal R) D A G) :
    IsProper (pullback.snd G.hom (jK R)) ∧
      RelAmple ((Over.pullback (jK R)).obj G) (U.LG.L.pull (pullback.fst G.hom (jK R))) ∧
      KTriv ((Over.pullback (jK R)).obj G) (U.LG.L.pull (pullback.fst G.hom (jK R))) := by
  have := U.gen_hom
  have hiso := isGrpPullback_of_iso U.gen
  have hLG : U.LG.L.IsLB := U.LG.isLB
  obtain ⟨w, hw⟩ : LBIso (U.LG.L.pull (pullback.fst G.hom (jK R))) (A.L.pull U.gen.hom.left) := by
    obtain ⟨w, hw⟩ := U.ext
    exact LBIso.symm ⟨w, hw⟩
  have hpw := (isGen_iff w).1 hw
  have : IsIso U.gen.hom.left := ((Over.forget _).mapIso U.gen).isIso_hom
  have := A.isAb.proper
  refine ⟨?_, relAmple_pull hiso.1 A.isLB (pull_isLB hLG _) hpw ⊤ (isAffineOpen_top _) (fun _ => trivial) A.ample,
    kTriv_pull hiso A.isLB (pull_isLB hLG _) hpw A.ktriv⟩
  have e : U.gen.hom.left ≫ A.A.hom = pullback.snd G.hom (jK R) := Over.w U.gen.hom
  rw [← e]
  infer_instance

theorem eq_generic {R : Type} [CommRing R] [IsDomain R] {K : Type} [Field K] (x : Sp K ⟶ Sp R)
    (h0 : (x (closedPoint K) : PrimeSpectrum R).asIdeal = ⊥) : x (closedPoint K) = jK R (closedPoint (FractionRing R)) := by
  refine PrimeSpectrum.ext ?_
  rw [h0]
  show ⊥ = Ideal.comap (algebraMap R (FractionRing R)) (maximalIdeal (FractionRing R))
  rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot,
    (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]

theorem relAmple_kTriv_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → ∀ (K : Type) [Field K] (x : Sp K ⟶ Sp R), Set.range x ⊆ (W : Set (Sp R)) → RelAmple ((Over.pullback x).obj G) (U.LG.L.pull (pullback.fst G.hom x)) ∧ KTriv ((Over.pullback x).obj G) (U.LG.L.pull (pullback.fst G.hom x)) := by
  intro R _ _ _ hR D A G _ _ hG U W hW K _ x hx
  obtain ⟨-, hp⟩ := GlobalTheory.T.abelian_proper_uniformised_where_trivialisations_generate R hR D A G hG U W hW
  have hLG : U.LG.L.IsLB := U.LG.isLB
  have hy : x (closedPoint K) ∈ W := hx ⟨_, rfl⟩
  by_cases h0 : (x (closedPoint K) : PrimeSpectrum R).asIdeal = ⊥
  · obtain ⟨h1, h2, h3⟩ := generic_fibre U
    exact GlobalTheory.T.relAmple_kernelTrivial_of_same_image_point (Sp R) G hG.quasiCompact hG.separated U.smooth U.LG.L hLG (FractionRing R) (jK R) h1 h2 h3 K x
      (eq_generic x h0)
  · obtain ⟨K₁, _, z, hz, h1, h2, h3⟩ := GlobalTheory.T.exists_fieldPoint_polarised_fibre_uniformised R hR D A G hG U W hp (x (closedPoint K)) hy h0
    exact GlobalTheory.T.relAmple_kernelTrivial_of_same_image_point (Sp R) G hG.quasiCompact hG.separated U.smooth U.LG.L hLG K₁ z h1 h2 h3 K x hz.symm

end GlobalTheory.Mum.PolFibre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmplePrincipalPolarisationEveryFibreOfGeneratStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_principal_polarisation_every_fibre_of_generate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → ∀ (K : Type) [Field K] (x : Sp K ⟶ Sp R), Set.range x ⊆ (W : Set (Sp R)) → RelAmple ((Over.pullback x).obj G) (U.LG.L.pull (pullback.fst G.hom x)) ∧ KTriv ((Over.pullback x).obj G) (U.LG.L.pull (pullback.fst G.hom x)) := by
  first | exact @GlobalTheory.Mum.PolFibre.relAmple_kTriv_fibre | exact GlobalTheory.Mum.PolFibre.relAmple_kTriv_fibre | (intros; apply GlobalTheory.Mum.PolFibre.relAmple_kTriv_fibre <;> assumption)
end
