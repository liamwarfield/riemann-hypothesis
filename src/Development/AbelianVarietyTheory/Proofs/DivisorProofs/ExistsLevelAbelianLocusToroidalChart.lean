module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NondegeneratePairingOfGenericFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightSectionsNonvanishingOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackSelf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NondegOfFieldExtension
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart.AbPol

theorem relAmple_lam_diag {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) :
    haveI := P.isAb.comm
    RelAmple P.A ((abelian₂ P.A P.L).pull (lift (𝟙 P.A) (𝟙 P.A)).left) := by
  haveI := P.isAb.comm
  have hL : Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hA := P.isAb
  have hLB := P.isLB
  have hΔ := GlobalTheory.FullSiegel.cls_diag hL.mulPull P
  have hΔ' := pull_isLB (GlobalTheory.FullSiegel.isLB_lam hLB) (lift (𝟙 P.A) (𝟙 P.A)).left
  have R := GlobalTheory.relAmple_finite_pow_iso S P.A P.A (𝟙 _) P.L 2 two_pos hA hA hLB (inferInstanceAs (IsFinite (𝟙 _)))
  have R' := GlobalTheory.relAmple_finite_pow_iso S P.A P.A (𝟙 _) (lbPow P.L 2) 2 two_pos hA hA (isLB_lbPow hLB 2)
    (inferInstanceAs (IsFinite (𝟙 _)))
  exact R'.2.2.2 _ hΔ' ((CechPic.cls_eq_iff (isLB_lbPow hLB 2) hΔ').1 ((CechPic.cls_lbPow hLB 2 _).trans hΔ.symm))
    (R.2.1.2 P.ample)

theorem isBiRig_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] {P : LB (G2 A).left}
    (h : IsBiRig A P) : IsBiRig ((Over.pullback f).obj A) (P.pull (Pdiv.PullbackComparison.pφ₂ f A)) := by
  obtain ⟨hP, ⟨t₁, ht₁⟩, ⟨t₂, ht₂⟩, hs⟩ := h
  exact ⟨pull_isLB hP _,
    gen_chartPull (chartPullLinComb P _ _ _ _ (Pdiv.PullbackComparison.pφ f A) (fun _ => Pdiv.PullbackComparison.lift_one_id f A)) t₁ ht₁,
    gen_chartPull (chartPullLinComb P _ _ _ _ (Pdiv.PullbackComparison.pφ f A) (fun _ => Pdiv.PullbackComparison.lift_id_one f A)) t₂ ht₂,
    LBIso.chartPull (Geo.Tor.chartPullPull P _ _ rfl)
      (chartPullLinComb P _ _ _ _ (Pdiv.PullbackComparison.pφ₂ f A) (fun _ => Pdiv.PullbackComparison.lift_swap f A)) hs⟩

theorem nondeg_of_fieldExtension {K K' : Type} [Field K] [Field K'] (i : K →+* K') (A : Over (Sp K)) [GrpObj A]
    (A' : Over (Sp K')) [GrpObj A'] {φ : A'.left ⟶ A.left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}
    (h : IsGrpPullback A' A (spMap i) φ) (sq : IsSquare φ φ₂) {P : LB (A ⊗ A).left} {P' : LB (A' ⊗ A').left}
    (hP : P.IsLB) (hP' : P'.IsLB) (e : LBIso P' (P.pull φ₂))
    (hn : ∀ (T : Over (Sp K')) (x : T ⟶ A'),
      (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x = 1)
    (T : Over (Sp K)) (x : T ⟶ A) (hx : ∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) : x = 1 := by
  letI := i.toAlgebra
  have : Subsingleton (Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : Nonempty (Spec (CommRingCat.of K')) := inferInstanceAs (Nonempty (PrimeSpectrum K'))
  have : Flat (spMap i) := inferInstanceAs (Flat (specOf i))
  have : Surjective (spMap i) := inferInstanceAs (Surjective (specOf i))
  let T' : Over (Sp K) := Over.mk (pullback.fst T.hom (spMap i) ≫ T.hom)
  let q : T' ⟶ T := Over.homMk (pullback.fst T.hom (spMap i)) rfl
  have hq : Epi q.left := Flat.epi_of_flat_of_surjective (pullback.fst T.hom (spMap i))
  have key : q ≫ x = 1 := by
    refine GlobalTheory.NondegSpread.eq_one_of_generic_nondeg K K' A A' φ φ₂ h sq P P' hP hP' e hn T'
      (pullback.snd T.hom (spMap i)) pullback.condition (q ≫ x) ?_
    have z := (CechPic.cls_eq_zero_iff (pull_isLB hP _)).2 hx
    refine (CechPic.cls_eq_zero_iff (pull_isLB hP _)).1 ?_
    rw [CechPic.cls_pull hP] at z ⊢
    have e' : lift (snd A T' ≫ q ≫ x) (fst A T') = (A ◁ q) ≫ lift (snd A T ≫ x) (fst A T) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [e', Over.comp_left, CechPic.pull_comp, z, map_zero]
  have e₂ : q ≫ x = q ≫ (1 : T ⟶ A) := by rw [key, MonObj.comp_one]
  exact Over.OverMorphism.ext ((cancel_epi q.left).1 (congrArg (fun r => r.left) e₂))

theorem relAmple_of_generic (O K : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [Field K]
    [Algebra O K] [IsFractionRing O K] (A : Over (Sp O)) [GrpObj A] (hA : IsAbelianScheme A) {M : LB A.left} (hM : M.IsLB)
    (hamp : RelAmple ((Over.pullback (spMap (algebraMap O K))).obj A) (M.pull (pullback.fst A.hom _))) :
    RelAmple A M := by
  haveI := hA.proper
  haveI := hA.smooth
  refine GlobalTheory.ProperFinite.relAmple_of_geometricFibres A hM fun K' _ _ y => ?_
  obtain ⟨g, rfl⟩ : ∃ g : O →+* K', spMap g = y := ⟨(Spec.preimage y).hom, by simp [spMap]⟩
  haveI : (RingHom.ker g).IsPrime := RingHom.ker_isPrime g
  let Op := Localization.AtPrime (RingHom.ker g)
  haveI : IsDomain Op := IsLocalization.isDomain_localization (RingHom.ker g).primeCompl_le_nonZeroDivisors
  haveI : IsNoetherianRing Op := IsLocalization.isNoetherianRing (RingHom.ker g).primeCompl _ inferInstance
  haveI : IsIntegrallyClosed Op := isIntegrallyClosed_of_isLocalization Op (RingHom.ker g).primeCompl
    (RingHom.ker g).primeCompl_le_nonZeroDivisors
  letI : Algebra Op K := IsLocalization.localizationAlgebraOfSubmonoidLe Op K (RingHom.ker g).primeCompl
    (nonZeroDivisors O) (RingHom.ker g).primeCompl_le_nonZeroDivisors
  haveI : IsScalarTower O Op K := IsLocalization.localization_isScalarTower_of_submonoid_le Op K
    (RingHom.ker g).primeCompl (nonZeroDivisors O) (RingHom.ker g).primeCompl_le_nonZeroDivisors
  haveI : IsFractionRing Op K := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (RingHom.ker g).primeCompl Op K
  have e₁ : spMap (algebraMap Op K) ≫ spMap (algebraMap O Op) = spMap (algebraMap O K) := by
    rw [← spMap_comp, ← IsScalarTower.algebraMap_eq]
  have hu : ∀ x : (RingHom.ker g).primeCompl, IsUnit (g x) := fun x => isUnit_iff_ne_zero.2 x.2
  let g' : Op →+* K' := IsLocalization.lift hu
  have e₂ : spMap g' ≫ spMap (algebraMap O Op) = spMap g := by
    rw [← spMap_comp]
    exact congrArg spMap (IsLocalization.lift_comp hu)
  let Ap := (Over.pullback (spMap (algebraMap O Op))).obj A
  have pp := isGrpPullback_pullback A (spMap (algebraMap O Op))
  have pK := isGrpPullback_pullback A (spMap (algebraMap O K))
  let φ := pp.1.lift (pullback.fst A.hom (spMap (algebraMap O K)))
    (((Over.pullback (spMap (algebraMap O K))).obj A).hom ≫ spMap (algebraMap Op K))
    (by rw [Category.assoc, e₁]; exact pK.1.w)
  have hφ : φ ≫ pullback.fst A.hom (spMap (algebraMap O Op)) = pullback.fst A.hom (spMap (algebraMap O K)) :=
    pp.1.lift_fst _ _ _
  have hpb : IsGrpPullback _ Ap (spMap (algebraMap Op K)) φ :=
    pp.cancel (pK.congr e₁.symm hφ.symm) (pp.1.lift_snd _ _ _)
  have hp : RelAmple Ap (M.pull (pullback.fst A.hom _)) :=
    GlobalTheory.AmpleGenericLocal.relAmple_of_generic Op K Ap _ φ (Out.TLinPf.isAb_pullback _ A hA) hpb _ _ (pull_isLB hM _)
      (pull_isLB hM _) (GlobalTheory.FibreAmple.lbIso_pull_comp hφ.symm (GlobalTheory.lbIso_refl (pull_isLB hM _))) hamp
  exact GlobalTheory.isAmpleLB_of_relAmple_of_isAffine (Over.mk (pullback.snd A.hom (spMap g))) (pull_isLB hM _)
    (GlobalTheory.FibreAmple.relAmple_of_factor hM pp.1 (IsPullback.of_hasPullback A.hom (spMap g)) (spMap g') e₂
      (pull_isLB hM _) (GlobalTheory.lbIso_refl (pull_isLB hM _)) hp)

theorem isSquare_comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left}
    {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} {ψ : G''.left ⟶ G'.left} {ψ₂ : (G'' ⊗ G'').left ⟶ (G' ⊗ G').left}
    (h' : IsSquare ψ ψ₂) (h : IsSquare φ φ₂) : IsSquare (ψ ≫ φ) (ψ₂ ≫ φ₂) :=
  ⟨by rw [Category.assoc, h.1, ← Category.assoc, h'.1, Category.assoc],
    by rw [Category.assoc, h.2, ← Category.assoc, h'.2, Category.assoc]⟩

theorem isPPol_of_field (O K' : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [Field K']
    (j : O →+* K') (hj : Function.Injective j) (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (A' : Over (Sp K')) [GrpObj A'] {φ : A'.left ⟶ A.left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}
    (h : IsGrpPullback A' A (spMap j) φ) (sq : IsSquare φ φ₂) {P : LB (A ⊗ A).left} {P' : LB (A' ⊗ A').left}
    (hP : IsBiRig A P) (hP' : P'.IsLB) (e : LBIso P' (P.pull φ₂))
    (ha : RelAmple A' (P'.pull (lift (𝟙 A') (𝟙 A')).left))
    (hn : ∀ (T : Over (Sp K')) (x : T ⟶ A'),
      (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x = 1) : IsPPol A P := by
  haveI := hA.proper
  let K := FractionRing O
  let i : K →+* K' := IsFractionRing.lift hj
  have e₁ : spMap i ≫ spMap (algebraMap O K) = spMap j := by
    rw [← spMap_comp]
    exact congrArg spMap (RingHom.ext fun x => IsFractionRing.lift_algebraMap hj x)
  let f := spMap (algebraMap O K)
  let AK := (Over.pullback f).obj A
  have pK := Pdiv.PullbackComparison.isGrpPullback f A
  have sK := Pdiv.PullbackComparison.isSquare f A
  let ψ := pK.1.lift φ (A'.hom ≫ spMap i) (by rw [Category.assoc, e₁]; exact h.1.w)
  have hψ : ψ ≫ Pdiv.PullbackComparison.pφ f A = φ := pK.1.lift_fst _ _ _
  have hpb : IsGrpPullback A' AK (spMap i) ψ := pK.cancel (h.congr e₁.symm hψ.symm) (pK.1.lift_snd _ _ _)
  have sψ := GlobalTheory.LamPull.exists_isSquare hpb.1.w
  have e₂ := GlobalTheory.LamPull.isSquare_unique sq (hψ ▸ isSquare_comp sψ sK)
  have hM := pull_isLB hP.1 (lift (𝟙 A) (𝟙 A)).left
  haveI : IsProper A'.hom := MorphismProperty.of_isPullback h.1 hA.proper
  have ha' : RelAmple A' ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull φ) :=
    (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A' (pull_isLB hM φ)).2
      ((GlobalTheory.isAmpleLB_congr (pull_isLB hP' _) (pull_isLB hM φ) (GlobalTheory.SiegelPull.diag_iso sq e)).1
        ((GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A' (pull_isLB hP' _)).1 ha))
  have hamp : RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) :=
    relAmple_of_generic O K A hA hM (GlobalTheory.FibreAmple.relAmple_of_fieldExtension hM i (IsPullback.of_hasPullback A.hom f)
      (e₁ ▸ h.1) (pull_isLB hM _) (GlobalTheory.lbIso_refl (pull_isLB hM _)) ha')
  have hPK := pull_isLB hP.1 (Pdiv.PullbackComparison.pφ₂ f A)
  refine ⟨hP, hamp, GlobalTheory.NondegSpread.nondeg_of_generic O K A AK _ _ hA pK sK P _ hP.1 hPK (GlobalTheory.lbIso_refl hPK)
    hP.2.1 hP.2.2.1 hP.2.2.2 hamp (nondeg_of_fieldExtension i AK A' hpb sψ hPK hP' ?_ hn)⟩
  exact LBIso.trans hP' (pull_isLB hP.1 _) (pull_isLB hPK _) e
    (GlobalTheory.FibreAmple.lbIso_pull_comp e₂ (GlobalTheory.lbIso_refl hPK))

theorem exists_isPPol_away : ∀ (g n : ℕ) (φ : InvFun ℤ), 3 ≤ n → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → (∀ p : Sp C.R, p ∈ abLocus G₁ ↔ ∏ k, C.t k ∉ p.asIdeal) → ∃ (A : Over (Sp (Localization.Away (∏ k, C.t k)))) (_ : GrpObj A) (_ : IsCommMonObj A) (π₀ : A.left ⟶ G₁.left) (π₂ : (G2 A).left ⟶ (G2 G₁).left), IsGrpPullback A G₁ (spMap (algebraMap C.R (Localization.Away (∏ k, C.t k)))) π₀ ∧ IsSquare π₀ π₂ ∧ IsAbelianScheme A ∧ IsPPol A (P.pull π₂) := by
  intro g n φ hn C G₁ _ _ P ⟨hCN, _, hG, hP, hU⟩ hab
  obtain ⟨hmono, -, hcone, hdef, ht⟩ := GlobalTheory.TChart.Taut.monomial_chart g n φ (by omega) C
  have hn' : (0 : ℤ) < n := by omega
  obtain ⟨R', _, _, _, ρ, -, D, ε, hCN', hρ, hfin, -, -, href, -⟩ :=
    GlobalTheory.PolDeg.refine_monomial_of_polarised C.R C.Q C.m C.t (fun k => (n : ℤ) • C.δ k) hCN hmono C.bd ht
      (fun k y z => by simp only [LinearMap.smul_apply, (hcone.mem k).1 y z])
      (fun k y => by simpa only [LinearMap.smul_apply, smul_eq_mul] using mul_nonneg hn'.le (hcone.nonneg k y))
      (fun y hy => by
        obtain ⟨k, hk⟩ := hdef y hy
        exact ⟨k, by simpa only [LinearMap.smul_apply, smul_eq_mul] using mul_pos hn' hk⟩)
  obtain ⟨G', _, _, π, π₂, B, U, hπ, sπ, eπ⟩ := hU R' ρ hCN' hρ hfin D ε href
  set t := ∏ k, C.t k with htd
  have ht0 : t ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => ht k
  let O := Localization.Away t
  haveI := hCN.1
  haveI := hCN.2.1
  have hle : Submonoid.powers t ≤ nonZeroDivisors C.R := powers_le_nonZeroDivisors_of_noZeroDivisors ht0
  haveI : IsDomain O := IsLocalization.isDomain_localization hle
  haveI : IsNoetherianRing O := IsLocalization.isNoetherianRing (Submonoid.powers t) _ inferInstance
  haveI : IsIntegrallyClosed O := isIntegrallyClosed_of_isLocalization O (Submonoid.powers t) hle
  let f := spMap (algebraMap C.R O)
  let A := (Over.pullback f).obj G₁
  have hG' : IsSemiAbelian A := IsSemiAbelian.pullback f G₁ hG
  have habA : abLocus A = Set.univ := Set.eq_univ_of_forall fun z =>
    (abLocus_pullback abLocusOne hG (IsPullback.of_hasPullback G₁.hom f) z).1 ((hab _).2 fun hz =>
      z.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hz (IsLocalization.Away.algebraMap_isUnit t)))
  have hA : IsAbelianScheme A :=
    { comm := hG'.comm
      smooth := hG'.smooth
      proper := GlobalTheory.AbLocusProperNormal.isProper_of_abLocus_eq_univ _ _ hG' habA
      geomConnected := hG'.geomConnected }
  have pA := Pdiv.PullbackComparison.isGrpPullback f G₁
  have sA := Pdiv.PullbackComparison.isSquare f G₁
  refine ⟨A, inferInstance, inferInstance, _, _, pA, sA, hA, ?_⟩

  let κ : C.R →+* FractionRing R' := (algebraMap R' (FractionRing R')).comp ρ
  have hκ : Function.Injective κ := (IsFractionRing.injective R' (FractionRing R')).comp hρ
  have hu : IsUnit (κ t) := isUnit_iff_ne_zero.2 ((map_ne_zero_iff κ hκ).2 ht0)
  let j : O →+* FractionRing R' := IsLocalization.Away.lift t hu
  have hjκ : j.comp (algebraMap C.R O) = κ := IsLocalization.Away.lift_comp t hu
  have hj : Function.Injective j := by
    refine (IsLocalization.lift_injective_iff _).2 fun x x' => ?_
    rw [(IsLocalization.injective O hle).eq_iff, hκ.eq_iff]
  have e₁ : spMap j ≫ f = (𝟙 _ ≫ jK R') ≫ spMap ρ := by
    rw [Category.id_comp, ← spMap_comp, hjκ, spMap_comp]
  haveI := U.gen_hom
  haveI := B.isAb.comm
  haveI : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have ha : IsGrpPullback B.A G' (𝟙 _ ≫ jK R') (U.gen.inv.left ≫ pullback.fst G'.hom (jK R')) :=
    (isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G' (jK R'))
  have sa := GlobalTheory.LamPull.exists_isSquare ha.1.w
  have hb := ha.comp hπ
  let ψ := pA.1.lift _ (B.A.hom ≫ spMap j) (by rw [Category.assoc _ _ f, e₁]; exact hb.1.w)
  have hψ : ψ ≫ Pdiv.PullbackComparison.pφ f G₁ = _ := pA.1.lift_fst _ _ _
  have hpb : IsGrpPullback B.A A (spMap j) ψ := pA.cancel (hb.congr e₁.symm hψ.symm) (pA.1.lift_snd _ _ _)
  have sψ := GlobalTheory.LamPull.exists_isSquare hpb.1.w
  have e₂ := GlobalTheory.LamPull.isSquare_unique (isSquare_comp sa sπ) (hψ ▸ isSquare_comp sψ sA)
  have hLG : U.LG.L.IsLB := U.LG.isLB
  have eL : LBIso B.L (U.LG.L.pull (U.gen.inv.left ≫ pullback.fst G'.hom (jK R'))) := by
    have e := (CechPic.cls_eq_iff (pull_isLB B.isLB _) (pull_isLB hLG _)).2 U.ext
    rw [CechPic.cls_pull B.isLB, CechPic.cls_pull hLG] at e
    rw [← CechPic.cls_eq_iff B.isLB (pull_isLB hLG _), CechPic.cls_pull hLG, CechPic.pull_comp, ← e,
      ← CechPic.pull_comp, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, CechPic.pull_id]
  have hΛ := GlobalTheory.FullSiegel.isLB_lam (G := B.A) B.isLB
  have hΛ' := GlobalTheory.FullSiegel.isLB_lam (G := G') hLG
  refine isPPol_of_field O _ j hj A hA B.A hpb sψ (isBiRig_pullback f G₁ hP) hΛ ?_ (relAmple_lam_diag B)
    (GlobalTheory.FullSiegel.eq_one_of_lam_triv B.isLB B.rigid B.ktriv)
  have c₁ := (CechPic.cls_eq_iff hΛ (pull_isLB hΛ' _)).2 (GlobalTheory.LamPull.lbIso_lam_pull ha hLG B.isLB eL sa)
  have c₂ := (CechPic.cls_eq_iff hΛ' (pull_isLB hP.1 _)).2 eπ
  rw [← CechPic.cls_eq_iff hΛ (pull_isLB (pull_isLB hP.1 _) _), c₁, CechPic.cls_pull hΛ', c₂,
    CechPic.cls_pull hP.1, CechPic.cls_pull (pull_isLB hP.1 _), CechPic.cls_pull hP.1, ← CechPic.pull_comp,
    ← CechPic.pull_comp, e₂]

end GlobalTheory.TChart.AbPol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelAbelianLocusToroidalChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TChart.AbLevel

theorem torsRat_of_isGrpPullback {R O : Type} [CommRing R] [IsDomain R] [CommRing O] [IsDomain O] (ρ : R →+* O)
    (hρ : Function.Injective ρ) {G : Over (Sp R)} [GrpObj G] {A : Over (Sp O)} [GrpObj A] {π : A.left ⟶ G.left}
    (hπ : IsGrpPullback A G (spMap ρ) π) {n : ℕ} (h : TorsRat G n) : TorsRat A n := by
  intro K _ _ κ x hx
  have hj : Function.Injective ((algebraMap O (FractionRing O)).comp ρ) :=
    (IsFractionRing.injective O (FractionRing O)).comp hρ
  let i : FractionRing R →+* FractionRing O := IsFractionRing.lift hj
  have hsq : spMap i ≫ jK R = jK O ≫ spMap ρ := by
    show spMap i ≫ spMap (algebraMap R (FractionRing R)) = spMap (algebraMap O (FractionRing O)) ≫ spMap ρ
    rw [← spMap_comp, ← spMap_comp]
    have hi : ∀ r, i (algebraMap R (FractionRing R) r) = algebraMap O (FractionRing O) (ρ r) := fun r =>
      IsFractionRing.lift_algebraMap (K := FractionRing R) hj r
    exact congrArg spMap (RingHom.ext hi)
  let x0 := GlobalTheory.ObjPull.pushEquiv hπ _ x
  have hx0 : x0 ^ n = 1 := by simp only [x0, ← map_pow, hx, map_one]
  have hT : spMap (κ.comp i) ≫ jK R = (Over.mk (spMap κ ≫ jK O)).hom ≫ spMap ρ := by
    show _ = (spMap κ ≫ jK O) ≫ spMap ρ
    rw [spMap_comp, Category.assoc, hsq, Category.assoc]
  let e : Over.mk (spMap (κ.comp i) ≫ jK R) ⟶ Over.mk ((Over.mk (spMap κ ≫ jK O)).hom ≫ spMap ρ) :=
    Over.homMk (𝟙 _) ((Category.id_comp _).trans hT.symm)
  obtain ⟨y, hy⟩ := h K (κ.comp i) (e ≫ x0) (by rw [← MonObj.comp_pow, hx0, MonObj.comp_one])
  have hy' : x.left ≫ π = spMap κ ≫ spMap i ≫ y.left := by
    have e₁ : x.left ≫ π = (e ≫ x0).left := (Category.id_comp _).symm
    exact e₁.trans (hy.trans ((congrArg (· ≫ y.left) (spMap_comp i κ)).trans (Category.assoc _ _ _)))
  have hz : (spMap i ≫ y.left) ≫ G.hom = jK O ≫ spMap ρ := by
    rw [Category.assoc, Over.w y]
    exact hsq
  refine ⟨Over.homMk (hπ.1.lift _ (jK O) hz) (hπ.1.lift_snd _ _ _), hπ.1.hom_ext ?_ ?_⟩
  · show x.left ≫ π = (spMap κ ≫ hπ.1.lift _ (jK O) hz) ≫ π
    rw [Category.assoc, hπ.1.lift_fst, hy']
  · show x.left ≫ A.hom = (spMap κ ≫ hπ.1.lift _ (jK O) hz) ≫ A.hom
    rw [Category.assoc, hπ.1.lift_snd]
    exact Over.w x

theorem exists_factor {S S' T : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A] {H : Over T} [GrpObj H]
    {f : S' ⟶ S} {t : T ⟶ S'} {u : T ⟶ S} (hu : t ≫ f = u) {π : A.left ⟶ G.left} {π₂ : (A ⊗ A).left ⟶ (G ⊗ G).left}
    (hπ : IsGrpPullback A G f π) (sπ : IsSquare π π₂) {a : H.left ⟶ G.left} {a₂ : (H ⊗ H).left ⟶ (G ⊗ G).left}
    (ha : IsGrpPullback H G u a) (sa : IsSquare a a₂) :
    ∃ (ψ : H.left ⟶ A.left) (ψ₂ : (H ⊗ H).left ⟶ (A ⊗ A).left), IsGrpPullback H A t ψ ∧ IsSquare ψ ψ₂ ∧ a₂ = ψ₂ ≫ π₂ := by
  let ψ := hπ.1.lift a (H.hom ≫ t) (by rw [Category.assoc, hu]; exact ha.1.w)
  have hψ : ψ ≫ π = a := hπ.1.lift_fst _ _ _
  have hpb : IsGrpPullback H A t ψ := hπ.cancel (ha.congr hu.symm hψ.symm) (hπ.1.lift_snd _ _ _)
  have sψ := GlobalTheory.LamPull.exists_isSquare hpb.1.w
  exact ⟨ψ, _, hpb, sψ, GlobalTheory.LamPull.isSquare_unique sa (hψ ▸ AbPol.isSquare_comp sψ sπ)⟩

theorem sameFib_factor {S₁ S₂ S₁' S₂' T : Scheme.{0}} {G₁ : Over S₁} [GrpObj G₁] [IsCommMonObj G₁] {P₁ : LB (G2 G₁).left}
    {G₂ : Over S₂} [GrpObj G₂] [IsCommMonObj G₂] {P₂ : LB (G2 G₂).left} (h₁ : P₁.IsLB) (h₂ : P₂.IsLB)
    {A₁ : Over S₁'} [GrpObj A₁] [IsCommMonObj A₁] {A₂ : Over S₂'} [GrpObj A₂] [IsCommMonObj A₂]
    {f₁ : S₁' ⟶ S₁} {t₁ : T ⟶ S₁'} {u₁ : T ⟶ S₁} (e₁ : t₁ ≫ f₁ = u₁)
    {f₂ : S₂' ⟶ S₂} {t₂ : T ⟶ S₂'} {u₂ : T ⟶ S₂} (e₂ : t₂ ≫ f₂ = u₂)
    {π₁ : A₁.left ⟶ G₁.left} {q₁ : (G2 A₁).left ⟶ (G2 G₁).left} (p₁ : IsGrpPullback A₁ G₁ f₁ π₁) (s₁ : IsSquare π₁ q₁)
    {π₂ : A₂.left ⟶ G₂.left} {q₂ : (G2 A₂).left ⟶ (G2 G₂).left} (p₂ : IsGrpPullback A₂ G₂ f₂ π₂) (s₂ : IsSquare π₂ q₂)
    (h : SameFib G₁ P₁ u₁ G₂ P₂ u₂) : SameFib A₁ (P₁.pull q₁) t₁ A₂ (P₂.pull q₂) t₂ := by
  obtain ⟨H, _, _, a, a₂, a', a₂', ha, sa, ha', sa', e⟩ := h
  obtain ⟨ψ, ψ₂, hψ, sψ, rfl⟩ := exists_factor e₁ p₁ s₁ ha sa
  obtain ⟨χ, χ₂, hχ, sχ, rfl⟩ := exists_factor e₂ p₂ s₂ ha' sa'
  refine ⟨H, inferInstance, inferInstance, ψ, ψ₂, χ, χ₂, hψ, sψ, hχ, sχ, ?_⟩
  have c := (CechPic.cls_eq_iff (pull_isLB h₁ _) (pull_isLB h₂ _)).2 e
  apply (CechPic.cls_eq_iff (pull_isLB (pull_isLB h₁ _) _) (pull_isLB (pull_isLB h₂ _) _)).1
  rw [CechPic.cls_pull (pull_isLB h₁ _), CechPic.cls_pull (pull_isLB h₂ _), CechPic.cls_pull h₁, CechPic.cls_pull h₂,
    ← CechPic.pull_comp, ← CechPic.pull_comp]
  rwa [CechPic.cls_pull h₁, CechPic.cls_pull h₂] at c

theorem lbIso_comp {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {N : LB Z} (hL : L.IsLB) (hM : M.IsLB) (hN : N.IsLB)
    {a : Y ⟶ X} {b : Z ⟶ Y} (e : LBIso M (L.pull a)) (e' : LBIso N (M.pull b)) : LBIso N (L.pull (b ≫ a)) := by
  have c := (CechPic.cls_eq_iff hM (pull_isLB hL _)).2 e
  have c' := (CechPic.cls_eq_iff hN (pull_isLB hM _)).2 e'
  apply (CechPic.cls_eq_iff hN (pull_isLB hL _)).1
  rw [c', CechPic.cls_pull hM, c, CechPic.cls_pull hL, CechPic.cls_pull hL,
    CechPic.pull_comp]

theorem siegPB_trans {h n : ℕ} {B : Type} [CommRing B] {ζ : B} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B}
    {s'' : S'' ⟶ Sp B} {u : SiegPre h n ζ s} {c : SiegPre h n ζ s'} {c' : SiegPre h n ζ s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
    (m' : SiegPB c' c f') (m : SiegPB c u f) : SiegPB c' u (f' ≫ f) := by
  obtain ⟨φ, φ₂, hφ, hs, hw, hl⟩ := m
  obtain ⟨ψ, ψ₂, hψ, hs', hw', hl'⟩ := m'
  exact ⟨ψ ≫ φ, ψ₂ ≫ φ₂, hψ.comp hφ, AbPol.isSquare_comp hs' hs, lbIso_comp u.isLB c.isLB c'.isLB hw hw', fun a =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) (hl' a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (f' ≫ ·) (hl a)).trans (Category.assoc _ _ _).symm)))⟩

theorem exists_level : ∀ {g n : ℕ} {φ : InvFun ℤ}, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → (∀ p : Sp C.R, p ∈ abLocus G₁ ↔ ∏ k, C.t k ∉ p.asIdeal) → TorsRat G₁ n → ∀ (K : Type) [Field K] (κ : Localization.Away (∏ k, C.t k) →+* K) (x₀ : Sp K ⟶ F.X), x₀ ≫ F.s = spMap ((κ.comp (algebraMap C.R (Localization.Away (∏ k, C.t k)))).comp C.b) → SameFib F.univ.A F.univ.P x₀ G₁ P (spMap (κ.comp (algebraMap C.R (Localization.Away (∏ k, C.t k))))) → ∃ c : SiegPre g n (zetaAway n) (spMap ((algebraMap C.R (Localization.Away (∏ k, C.t k))).comp C.b)), c.Principal ∧ (∃ (a : c.A.left ⟶ G₁.left) (a₂ : (G2 c.A).left ⟶ (G2 G₁).left), IsGrpPullback c.A G₁ (spMap (algebraMap C.R (Localization.Away (∏ k, C.t k)))) a ∧ IsSquare a a₂ ∧ LBIso c.P (P.pull a₂)) ∧ ∀ yU : Sp (Localization.Away (∏ k, C.t k)) ⟶ F.X, SiegPB c F.univ yU → yU ≫ F.s = spMap ((algebraMap C.R (Localization.Away (∏ k, C.t k))).comp C.b) → spMap κ ≫ yU = x₀ := by
  intro g n φ hn hodd F C G₁ _ _ P hM hab hT K _ κ x₀ hx₀ hsf
  obtain ⟨A, _, _, π₀, π₂, hπ, sπ, hA, hP⟩ := AbPol.exists_isPPol_away g n φ hn C G₁ P hM hab
  have hCN := hM.1
  have hPG := hM.2.2.2.1.1
  let t := ∏ k, C.t k
  let O := Localization.Away t
  have ht0 : t ≠ 0 := fun h0 => by
    have hu := (IsLocalization.Away.algebraMap_isUnit (S := O) t).map κ
    have : algebraMap C.R O t = 0 := (congrArg (algebraMap C.R O) h0).trans (map_zero _)
    rw [this, map_zero] at hu
    exact not_isUnit_zero hu
  haveI := hCN.1
  haveI := hCN.2.1
  have hle : Submonoid.powers t ≤ nonZeroDivisors C.R := powers_le_nonZeroDivisors_of_noZeroDivisors ht0
  haveI : IsDomain O := IsLocalization.isDomain_localization hle
  haveI : IsNoetherianRing O := IsLocalization.isNoetherianRing (Submonoid.powers t) _ inferInstance
  haveI : IsIntegrallyClosed O := isIntegrallyClosed_of_isLocalization O (Submonoid.powers t) hle
  have hTA : TorsRat A n := torsRat_of_isGrpPullback _ (IsLocalization.injective O hle) hπ hT
  let b : cycAway n →+* O := (algebraMap C.R O).comp C.b
  let c₀ : SiegPre g n (zetaAway n) (spMap (κ.comp b)) := GlobalTheory.LowChart.siegPull F.univ x₀ _ hx₀
  have pb₀ : SiegPB c₀ F.univ x₀ := GlobalTheory.LowChart.siegPB_siegPull _ _ _ _
  have hs₀ : SameFib c₀.A c₀.P (𝟙 _) A (P.pull π₂) (spMap κ) := by
    dsimp only [c₀, GlobalTheory.LowChart.siegPull]
    exact sameFib_factor F.univ.isLB hPG (Category.id_comp x₀) (spMap_comp _ _).symm
      (Pdiv.PullbackComparison.isGrpPullback x₀ F.univ.A) (Pdiv.PullbackComparison.isSquare x₀ F.univ.A) hπ sπ hsf
  obtain ⟨c, hc, hcc, a, a₂, ha, sa, ea⟩ := GlobalTheory.LevSpread.level_spreads n hn hodd O b A (P.pull π₂) hA hP hTA g K κ c₀
    (GlobalTheory.LowChart.principal_siegPull _ _ _ _ F.princ) hs₀
  refine ⟨c, hc, ⟨a ≫ π₀, a₂ ≫ π₂, (ha.comp hπ).congr (Category.id_comp _) rfl, AbPol.isSquare_comp sa sπ,
    lbIso_comp hPG (pull_isLB hPG _) c.isLB (GlobalTheory.lbIso_refl (pull_isLB hPG _)) ea⟩, fun yU hy hys => ?_⟩
  refine F.inj K _ _ _ c₀ ?_ (siegPB_trans hcc hy) pb₀
  rw [Category.assoc, hys, hx₀, ← spMap_comp, RingHom.comp_assoc]

end GlobalTheory.TChart.AbLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelAbelianLocusToroidalChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_abelianLocus_toroidalChart : ∀ {g n : ℕ} {φ : InvFun ℤ}, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → (∀ p : Sp C.R, p ∈ abLocus G₁ ↔ ∏ k, C.t k ∉ p.asIdeal) → TorsRat G₁ n → ∀ (K : Type) [Field K] (κ : Localization.Away (∏ k, C.t k) →+* K) (x₀ : Sp K ⟶ F.X), x₀ ≫ F.s = spMap ((κ.comp (algebraMap C.R (Localization.Away (∏ k, C.t k)))).comp C.b) → SameFib F.univ.A F.univ.P x₀ G₁ P (spMap (κ.comp (algebraMap C.R (Localization.Away (∏ k, C.t k))))) → ∃ c : SiegPre g n (zetaAway n) (spMap ((algebraMap C.R (Localization.Away (∏ k, C.t k))).comp C.b)), c.Principal ∧ (∃ (a : c.A.left ⟶ G₁.left) (a₂ : (G2 c.A).left ⟶ (G2 G₁).left), IsGrpPullback c.A G₁ (spMap (algebraMap C.R (Localization.Away (∏ k, C.t k)))) a ∧ IsSquare a a₂ ∧ LBIso c.P (P.pull a₂)) ∧ ∀ yU : Sp (Localization.Away (∏ k, C.t k)) ⟶ F.X, SiegPB c F.univ yU → yU ≫ F.s = spMap ((algebraMap C.R (Localization.Away (∏ k, C.t k))).comp C.b) → spMap κ ≫ yU = x₀ := by
  first | exact @GlobalTheory.TChart.AbLevel.exists_level | exact GlobalTheory.TChart.AbLevel.exists_level | (intros; apply GlobalTheory.TChart.AbLevel.exists_level <;> assumption)
end
