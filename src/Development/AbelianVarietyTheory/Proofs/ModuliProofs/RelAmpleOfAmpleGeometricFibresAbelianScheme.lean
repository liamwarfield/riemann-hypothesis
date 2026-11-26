module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RelAmpleNearFibreFlatProjective
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationDegenerationDataUnique
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBasicOpenKTrivOfFibre
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjDescendLowerLevel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescended

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianScheme
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.FibreAmple

variable {S X T₁ T₂ X₁ X₂ : Scheme.{0}} {f : X ⟶ S} {M : LB X} {π₁ : X₁ ⟶ X} {f₁ : X₁ ⟶ T₁} {t₁ : T₁ ⟶ S}
  {π₂ : X₂ ⟶ X} {f₂ : X₂ ⟶ T₂} {t₂ : T₂ ⟶ S}

theorem exists_isPullback (h₁ : IsPullback π₁ f₁ f t₁) (h₂ : IsPullback π₂ f₂ f t₂) (u : T₂ ⟶ T₁)
    (hu : u ≫ t₁ = t₂) : ∃ φ : X₂ ⟶ X₁, π₂ = φ ≫ π₁ ∧ IsPullback φ f₂ f₁ u := by
  have w : π₂ ≫ f = (f₂ ≫ u) ≫ t₁ := by rw [Category.assoc, hu, h₂.w]
  refine ⟨h₁.lift _ _ w, (h₁.lift_fst _ _ _).symm, IsPullback.of_right ?_ (h₁.lift_snd _ _ _) h₁⟩
  rw [h₁.lift_fst, hu]
  exact h₂

theorem lbIso_pull_comp {φ : X₂ ⟶ X₁} (hφ : π₂ = φ ≫ π₁) {L₁ : LB X₁} (e : LBIso L₁ (M.pull π₁)) :
    LBIso (M.pull π₂) (L₁.pull φ) :=
  LBIso.chartPull (chartPullSame M (fun _ : PUnit => π₂) (fun _ => π₁) (fun _ => 1) φ fun _ => hφ)
    (Geo.Tor.chartPullPull L₁ φ φ rfl) e.symm

theorem lbIso_pull_pull (hM : M.IsLB) (φ : X₂ ⟶ X₁) (π₁ : X₁ ⟶ X) :
    LBIso ((M.pull π₁).pull φ) (M.pull (φ ≫ π₁)) :=
  (lbIso_pull_comp rfl (GlobalTheory.lbIso_refl (LB.isLB_pull hM π₁))).symm

theorem relAmple_of_factor [IsProper f] (hM : M.IsLB) (h₁ : IsPullback π₁ f₁ f t₁) (h₂ : IsPullback π₂ f₂ f t₂)
    (u : T₂ ⟶ T₁) (hu : u ≫ t₁ = t₂) {L₁ : LB X₁} (hL₁ : L₁.IsLB) (e : LBIso L₁ (M.pull π₁))
    (hA : Out.RelAmple (Over.mk f₁) L₁) : Out.RelAmple (Over.mk f₂) (M.pull π₂) := by
  obtain ⟨φ, hφ, H⟩ := exists_isPullback h₁ h₂ u hu
  have hp : IsProper (Over.mk f₂).hom := MorphismProperty.of_isPullback (P := @IsProper) h₂ ‹_›
  refine AmpleLocal.relAmple_of_locally T₂ (Over.mk f₂) (M.pull π₂) (LB.isLB_pull hM π₂)
    inferInstance inferInstance fun s => ?_
  obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := T₁) (U := ⊤) (x := u s) trivial
  exact ⟨u ⁻¹ᵁ V, hs, PolPull.relAmple_restrict (G := Over.mk f₁) (G' := Over.mk f₂) H hL₁ (LB.isLB_pull hM π₂)
    (lbIso_pull_comp hφ e) hA V hV⟩

theorem relAmple_of_fieldExtension [IsProper f] (hM : M.IsLB) {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K)
    {f₁ : X₁ ⟶ Sp K₀} {t₁ : Sp K₀ ⟶ S} {f₂ : X₂ ⟶ Sp K} (h₁ : IsPullback π₁ f₁ f t₁)
    (h₂ : IsPullback π₂ f₂ f (spMap i ≫ t₁)) {L₁ : LB X₁} (hL₁ : L₁.IsLB) (e : LBIso L₁ (M.pull π₁))
    (hA : Out.RelAmple (Over.mk f₂) (M.pull π₂)) : Out.RelAmple (Over.mk f₁) L₁ := by
  obtain ⟨φ, hφ, H⟩ := exists_isPullback h₁ h₂ _ rfl
  have : Subsingleton (Spec (CommRingCat.of K₀)) := inferInstanceAs (Subsingleton (PrimeSpectrum K₀))
  have : Nonempty (Spec (CommRingCat.of K)) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  have : Flat (Out.specOf i) := inferInstance
  have : Surjective (Out.specOf i) := inferInstance
  have hp : IsProper f₁ := MorphismProperty.of_isPullback (P := @IsProper) h₁ ‹_›
  have : IsProper (Over.mk f₁).hom := hp
  have : IsProper f₂ := MorphismProperty.of_isPullback (P := @IsProper) h₂ ‹_›
  have : CompactSpace X₁ := QuasiCompact.compactSpace_of_compactSpace f₁
  have : QuasiSeparatedSpace X₁ := quasiSeparatedSpace_of_quasiSeparated f₁
  refine (relAmple_iff_isAmpleLB_of_isAffine (Over.mk f₁) hL₁).2 (AmpleDescent.isAmpleLB_of_pull i H hL₁ ?_)
  exact (isAmpleLB_of_relAmple_of_isAffine (Over.mk f₂) (LB.isLB_pull hM π₂) hA).of_lbIso (LB.isLB_pull hL₁ φ)
    (lbIso_pull_comp hφ e).symm

theorem residueField_fraction {R : Type} [CommRing R] (p : Ideal R) [p.IsPrime] (y : p.ResidueField) :
    ∃ a b : R, algebraMap R p.ResidueField b ≠ 0 ∧
      y * algebraMap R p.ResidueField b = algebraMap R p.ResidueField a := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R ⧸ p) y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hb' : algebraMap (R ⧸ p) p.ResidueField (Ideal.Quotient.mk p b) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  exact ⟨a, b, hb', div_mul_cancel₀ _ hb'⟩

theorem relAmple_of_geometricFibres : Out.Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → (∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S), Out.RelAmple (Over.mk (pullback.snd P.A.hom y)) (M.pull (pullback.fst P.A.hom y))) → Out.RelAmple P.A M := by
  intro _ S _ P M hM hfib
  have := P.isAb.proper
  have := P.isAb.smooth
  refine AmpleLocal.relAmple_of_locally S P.A M hM inferInstance inferInstance fun s => ?_
  obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := s) trivial
  have : IsNoetherianRing Γ(S, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let t : Spec (CommRingCat.of Γ(S, V)) ⟶ S := hV.fromSpec
  obtain ⟨p, hp⟩ : s ∈ Set.range t := by rw [hV.range_fromSpec]; exact hs
  have hB := IsPullback.of_hasPullback P.A.hom t
  have hL := LB.isLB_pull hM (pullback.fst P.A.hom t)
  have := p.isPrime
  let g := algebraMap Γ(S, V) p.asIdeal.ResidueField
  let i := algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)
  obtain ⟨r, hr, hA⟩ := GlobalTheory.T.relAmple_near_fibre_flat_projective Γ(S, V) (Over.mk (pullback.snd P.A.hom t)) (M.pull (pullback.fst P.A.hom t))
    (inferInstanceAs (Flat (pullback.snd P.A.hom t)))
    (AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral S P.A P.L P.isAb P.isLB P.ample _ t _ _ _ hB).1
    hL _ g (residueField_fraction p.asIdeal)
    (relAmple_of_fieldExtension hM i
      ((IsPullback.of_hasPullback (pullback.snd P.A.hom t) (spMap g)).paste_horiz hB)
      (IsPullback.of_hasPullback P.A.hom _) (LB.isLB_pull hL _) (lbIso_pull_pull hM _ _) (hfib _ _))
  let D : (Spec (CommRingCat.of Γ(S, V))).Opens := PrimeSpectrum.basicOpen r
  have hD : p ∈ D := fun h => hr (Ideal.algebraMap_residueField_eq_zero.2 h)
  have hrange : Set.range (t ''ᵁ D).ι ⊆ Set.range (D.ι ≫ t) := by
    rintro _ ⟨⟨_, x, hx, rfl⟩, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨t ''ᵁ D, ⟨p, hD, hp⟩, ?_⟩
  exact relAmple_of_factor hM ((IsPullback.of_hasPullback (pullback.snd P.A.hom t) D.ι).paste_horiz hB)
    (isPullback_morphismRestrict P.A.hom (t ''ᵁ D)).flip (IsOpenImmersion.lift (D.ι ≫ t) _ hrange)
    (IsOpenImmersion.lift_fac _ _ _) (LB.isLB_pull hL _) (lbIso_pull_pull hM _ _) hA

end GlobalTheory.FibreAmple
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianSchemeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_of_ample_geometricFibres_abelianScheme : Out.Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → (∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S), Out.RelAmple (Over.mk (pullback.snd P.A.hom y)) (M.pull (pullback.fst P.A.hom y))) → Out.RelAmple P.A M := by
  first | exact @GlobalTheory.FibreAmple.relAmple_of_geometricFibres | exact GlobalTheory.FibreAmple.relAmple_of_geometricFibres | (intros; apply GlobalTheory.FibreAmple.relAmple_of_geometricFibres <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfUnifOfSubsingleton
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.NoTorus

theorem pmaps_id {X Y : Scheme.{0}} {L : LB X} {F : X ⟶ X} (hF : F = 𝟙 X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) :
    PMaps (isoPullId (Geo.Tor.idIso L) hF) φ φ ε t t (𝟙 Y) := by
  intro Z r z p q hp hq
  subst hF
  have hp' : ∀ k, φ k (r z) ∈ L.U (p k) := hp
  rw [Category.comp_id]
  refine (gen_trans ht r z (Set.mem_iInter.2 hp') (Set.mem_iInter.2 hq)).trans
    (congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_))
  change _ = (gm (r ≫ φ k) z _ (res _ (L.g (p k) (q k)))) ^ ε k
  have hm : (r ≫ φ k) z ∈ (L.pull (𝟙 X)).U (fun _ => p k) ⊓ L.U (q k) := ⟨mem_pull.2 (hp' k), hq k⟩
  exact congrArg (fun u => u ^ ε k) (gm_res (r ≫ φ k) z _ hm (L.g (p k) (q k))).symm

theorem nonempty_isPullDeg_self {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (hR : AdmBase R I)
    (D : DegData R I) : Nonempty (IsPullDeg (RingHom.id R) D.toPre D.toPre) := by
  have hgen {F : D.toPre.P.A.left ⟶ D.toPre.P.A.left} (hF : F = 𝟙 _) : PGen (isoPullId (Geo.Tor.idIso D.toPre.P.L) hF) := by
    subst F
    intro Y f y j j' k k' hj hj' hk hk'
    have hgw : ∀ a b, f y ∈ D.toPre.P.L.U a → f y ∈ D.toPre.P.L.U b →
        gw (isoPullId (Geo.Tor.idIso D.toPre.P.L) rfl) f y a b =
          gm f y _ (D.toPre.P.L.g a b) := by
      intro a b ha hb
      have hm : f y ∈ (D.toPre.P.L.pull (𝟙 _)).U (fun _ => a) ⊓ D.toPre.P.L.U b := ⟨mem_pull.2 ha, hb⟩
      exact gm_res f y _ hm _
    rw [hgw j k hj hk, hgw j' k' hj' hk', Category.comp_id]
    have hV : f y ∈ (D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') := ⟨⟨hj, hk⟩, ⟨hj', hk'⟩⟩
    have hw' : res (inf_le_left : (D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') ≤ D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) (D.toPre.P.L.g j k) =
      res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        (D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') ≤ D.toPre.P.L.U j ⊓ D.toPre.P.L.U j') (D.toPre.P.L.g j j') *
      (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
        (D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') ≤ D.toPre.P.L.U k ⊓ D.toPre.P.L.U k') (D.toPre.P.L.g k k'))⁻¹ *
      res (inf_le_right : (D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') ≤ D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') (D.toPre.P.L.g j' k') :=
      (idIso_isGen D.toPre.P.isLB) (j, k) (j', k')
    have key := congrArg (gm f y ((D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k'))) hw'
    simp only [map_mul, map_inv, gm_res f y _ hV] at key
    exact key
  have : IsMonHom (Iso.refl D.toPre.P.A).hom := inferInstanceAs (IsMonHom (𝟙 D.toPre.P.A))
  have gp : IsGrpPullback D.toPre.P.A D.toPre.P.A (specOf (RingHom.id R)) (Iso.refl D.toPre.P.A).hom.left :=
    (isGrpPullback_of_iso (Iso.refl D.toPre.P.A)).congr (specOf_id R).symm rfl
  obtain ⟨e, me, hF⟩ := grpPullback_iso gp (isGrpPullback_pullback D.toPre.P.A (specOf (RingHom.id R)))
  have hF' : e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) = 𝟙 _ := hF
  obtain ⟨W, hW, ⟨ψW⟩⟩ := psiOnExists R I hR D
  obtain ⟨hD, -⟩ := UnifUniq.exists_isPullDeg_id D.toPre D.toPre W hW ψW e me
    (isoPullId (Geo.Tor.idIso D.toPre.P.L) hF') ((isGen_iff _).2 (hgen hF'))
    ((congrArg (_ ≫ ·) hF').trans (Category.comp_id _))
    (pmaps_id hF' (K := PUnit) (fun _ => eSec D.toPre.P.A) (fun _ => 1) D.toPre.rig_gen) (AddEquiv.refl _)
    (fun x => (congrArg (_ ≫ ·) hF').trans (Category.comp_id _))
    (fun x => pmaps_id hF' (K := PUnit) (fun _ => D.toPre.xK x) (fun _ => -1) (D.toPre.psi_gen x))
  exact ⟨hD⟩

end GlobalTheory.NoTorus

namespace GlobalTheory

theorem isAbelianScheme_of_unif_of_subsingleton : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (IsLocalRing.maximalIdeal V) D A G → Subsingleton D.toPre.X → IsAbelianScheme G := by
  intro hL hL₂ V _ _ _ _ hc D A G _ hG hsa U hX
  have hR : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  obtain ⟨A', eA, hA, hw⟩ := GoodReductionUnif.exists_baseChange hL.polBaseChange (jK V) D.toPre.P
  obtain ⟨hD⟩ := NoTorus.nonempty_isPullDeg_self hR D
  have hsemi : IsSemiAbelian D.toPre.P.A := by
    let B := D.toPre.P.A
    have hB := D.toPre.P.isAb
    have := hB.proper
    refine ⟨hB.comm, hB.smooth, inferInstance, inferInstance, hB.geomConnected, ?_⟩
    intro Ω _ _ p
    have hAb : IsAbelianScheme ((Over.pullback p).obj B) := by
      have := hB.comm
      have := hB.smooth
      have := hB.proper
      have := hB.geomConnected
      refine ⟨inferInstance, ?_, ?_, ?_⟩
      · change Smooth (pullback.snd B.hom p); infer_instance
      · change IsProper (pullback.snd B.hom p); infer_instance
      · change GeometricallyConnected (pullback.snd B.hom p); infer_instance
    let A := (Over.pullback p).obj B
    have : IsIso (toUnit (splitTorus (Sp Ω) PUnit)) := by
      have h : 𝟙 (splitTorus (Sp Ω) PUnit) = 1 := by
        rw [← Diag.diagMap_id, ← Diag.diagMap_zero]
        congr 1
      exact ⟨η, h.symm, toUnit_unique _ _⟩
    exact ⟨{
      X := PUnit
      B := A
      isAbelian := hAb
      q := 𝟙 A
      q_hom := inferInstance
      q_flat := by rw [Over.id_left]; infer_instance
      q_surjective := by rw [Over.id_left]; infer_instance
      q_quasiCompact := by rw [Over.id_left]; infer_instance
      i := toUnit _ ≫ η
      i_hom := by have := hAb.comm; infer_instance
      isKernel := IsPullback.of_vert_isIso ⟨Category.comp_id _⟩ }⟩
  obtain ⟨ψ, -⟩ := GlobalTheory.T.exists_iso_uniformisations_of_iso_degeneration_data hL hL₂ V _ hR rfl D D A A' G D.toPre.P.A hsa
    hsemi U
    ⟨SelfUnif.selfPre D A' eA hA hw, fun k _ =>
      SelfUnif.expBij D A' eA hA hw hL.globalFns (IsAdicComplete.le_jacobson_bot _) k⟩ hD
  have e : G.hom = ψ.inv.left ≫ D.toPre.P.A.hom := (Over.w ψ.inv).symm
  have := D.toPre.P.isAb.proper
  have : IsIso ψ.inv.left := inferInstanceAs (IsIso ((Over.forget _).map ψ.inv))
  exact ⟨hG, hsa.smooth, by rw [e]; infer_instance, hsa.geomConnected⟩

end GlobalTheory

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.KernelTrivialOfEveryPointCovered
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.KernelTrivialOfEveryPointCovered
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.KTrivGlob

private theorem mul_left_congr_of_base_eq {S T : Scheme.{0}} {G : Over S} [GrpObj G] {a b : T ⟶ S} (hab : a = b)
    (u v : Over.mk a ⟶ G) (u' v' : Over.mk b ⟶ G) (hu : u.left = u'.left) (hv : v.left = v'.left) :
    (u * v).left = (u' * v').left := by
  subst hab
  have h1 : u = u' := Over.OverMorphism.ext hu
  have h2 : v = v' := Over.OverMorphism.ext hv
  subst h1 h2
  rfl

private theorem exists_isGrpPullback_factor {S S₁ S₂ : Scheme.{0}} {G : Over S} {G₁ : Over S₁} {G₂ : Over S₂}
    [GrpObj G] [GrpObj G₁] [GrpObj G₂] {f₁ : S₁ ⟶ S} {g : S₂ ⟶ S₁} {φ₁ : G₁.left ⟶ G.left}
    {φ₂ : G₂.left ⟶ G.left} (h₁ : IsGrpPullback G₁ G f₁ φ₁) (h₂ : IsGrpPullback G₂ G (g ≫ f₁) φ₂) :
    ∃ ψ : G₂.left ⟶ G₁.left, ψ ≫ φ₁ = φ₂ ∧ IsGrpPullback G₂ G₁ g ψ := by
  obtain ⟨hp₁, hm₁⟩ := h₁
  obtain ⟨hp₂, hm₂⟩ := h₂
  have hw : φ₂ ≫ G.hom = (G₂.hom ≫ g) ≫ f₁ := by rw [hp₂.w]; simp
  refine ⟨hp₁.lift φ₂ (G₂.hom ≫ g) hw, hp₁.lift_fst _ _ _, ?_, ?_⟩
  · refine IsPullback.of_right ?_ (hp₁.lift_snd _ _ _) hp₁
    rw [hp₁.lift_fst]
    exact hp₂
  · intro T x y x₀ y₀ hx hy
    apply hp₁.hom_ext
    · have ex : (x₀.left ≫ φ₁) ≫ G.hom = (T.hom ≫ g) ≫ f₁ := by
        rw [Category.assoc, hp₁.w, ← Category.assoc, Over.w x₀]; rfl
      have ey : (y₀.left ≫ φ₁) ≫ G.hom = (T.hom ≫ g) ≫ f₁ := by
        rw [Category.assoc, hp₁.w, ← Category.assoc, Over.w y₀]; rfl
      have fx : (x.left ≫ φ₂) ≫ G.hom = T.hom ≫ g ≫ f₁ := by
        rw [Category.assoc, hp₂.w, ← Category.assoc, Over.w x]
      have fy : (y.left ≫ φ₂) ≫ G.hom = T.hom ≫ g ≫ f₁ := by
        rw [Category.assoc, hp₂.w, ← Category.assoc, Over.w y]
      have A := hm₁ (Over.mk (T.hom ≫ g)) x₀ y₀ (Over.homMk (x₀.left ≫ φ₁) ex) (Over.homMk (y₀.left ≫ φ₁) ey) rfl rfl
      have B := hm₂ T x y (Over.homMk (x.left ≫ φ₂) fx) (Over.homMk (y.left ≫ φ₂) fy) rfl rfl
      have C := mul_left_congr_of_base_eq (Category.assoc T.hom g f₁) (Over.homMk (x₀.left ≫ φ₁) ex)
        (Over.homMk (y₀.left ≫ φ₁) ey) (Over.homMk (x.left ≫ φ₂) fx) (Over.homMk (y.left ≫ φ₂) fy)
        (by simp [hx, hp₁.lift_fst]) (by simp [hy, hp₁.lift_fst])
      rw [← A, C, B, Category.assoc, hp₁.lift_fst]
    · rw [Over.w (x₀ * y₀), Category.assoc, hp₁.lift_snd, ← Category.assoc, Over.w (x * y)]
      rfl

private theorem isGrpPullback_comp' {S S₁ S₂ : Scheme.{0}} {G : Over S} {G₁ : Over S₁} {G₂ : Over S₂}
    [GrpObj G] [GrpObj G₁] [GrpObj G₂] {f : S₁ ⟶ S} {g : S₂ ⟶ S₁} {φ : G₁.left ⟶ G.left}
    {ψ : G₂.left ⟶ G₁.left} (h₂ : IsGrpPullback G₂ G₁ g ψ) (h₁ : IsGrpPullback G₁ G f φ) :
    IsGrpPullback G₂ G (g ≫ f) (ψ ≫ φ) := by
  obtain ⟨hp₁, hm₁⟩ := h₁
  obtain ⟨hp₂, hm₂⟩ := h₂
  refine ⟨hp₂.paste_horiz hp₁, ?_⟩
  intro T x y x₀ y₀ hx hy
  have ex : (x.left ≫ ψ) ≫ G₁.hom = T.hom ≫ g := by
    rw [Category.assoc, hp₂.w, ← Category.assoc, Over.w x]
  have ey : (y.left ≫ ψ) ≫ G₁.hom = T.hom ≫ g := by
    rw [Category.assoc, hp₂.w, ← Category.assoc, Over.w y]
  have ex' : ((x.left ≫ ψ) ≫ φ) ≫ G.hom = (T.hom ≫ g) ≫ f := by
    rw [Category.assoc, hp₁.w, ← Category.assoc, ex]
  have ey' : ((y.left ≫ ψ) ≫ φ) ≫ G.hom = (T.hom ≫ g) ≫ f := by
    rw [Category.assoc, hp₁.w, ← Category.assoc, ey]
  have A := hm₂ T x y (Over.homMk (x.left ≫ ψ) ex) (Over.homMk (y.left ≫ ψ) ey) rfl rfl
  have B := hm₁ (Over.mk (T.hom ≫ g)) (Over.homMk (x.left ≫ ψ) ex) (Over.homMk (y.left ≫ ψ) ey)
    (Over.homMk ((x.left ≫ ψ) ≫ φ) ex') (Over.homMk ((y.left ≫ ψ) ≫ φ) ey') rfl rfl
  have C := mul_left_congr_of_base_eq (Category.assoc T.hom g f).symm x₀ y₀ (Over.homMk ((x.left ≫ ψ) ≫ φ) ex')
    (Over.homMk ((y.left ≫ ψ) ≫ φ) ey') (by simp [hx]) (by simp [hy])
  rw [C, B, A, Category.assoc]

theorem kTriv_transfer {S S₁ S₂ : Scheme.{0}} {G : Over S} {G₁ : Over S₁} {G₂ : Over S₂} [GrpObj G] [GrpObj G₁]
    [GrpObj G₂] {f₁ : S₁ ⟶ S} {g : S₂ ⟶ S₁} {φ₁ : G₁.left ⟶ G.left} {φ₂ : G₂.left ⟶ G.left} {L : LB G.left}
    {L₁ : LB G₁.left} {L₂ : LB G₂.left} (hL : L.IsLB) (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB)
    (h₁ : IsGrpPullback G₁ G f₁ φ₁) (h₂ : IsGrpPullback G₂ G (g ≫ f₁) φ₂)
    (e₁ : LBIso L₁ (L.pull φ₁)) (e₂ : LBIso L₂ (L.pull φ₂)) (hK : Out.KTriv G₁ L₁) : Out.KTriv G₂ L₂ := by
  obtain ⟨ψ, hψ, hG⟩ := exists_isGrpPullback_factor h₁ h₂
  have e₃ : LBIso (L₁.pull ψ) (L.pull φ₂) := GlobalTheory.GenSpread.lbIso_pull_of_lbIso e₁ ψ hψ.symm
  have hψL : (L₁.pull ψ).IsLB := pull_isLB hL₁ ψ
  have e₄ : LBIso L₂ (L₁.pull ψ) := LBIso.trans hL₂ (pull_isLB hL φ₂) hψL e₂ (LBIso.symm e₃)
  obtain ⟨w, hw⟩ := e₄
  exact kTriv_pull hG hL₁ hL₂ ((isGen_iff w).1 hw) hK

set_option maxHeartbeats 400000 in
private theorem exists_open_kTriv_restrict_of_kTriv_fibre {S S' : Scheme.{0}} [IsLocallyNoetherian S] {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hG : IsAbelianScheme G) (hA : Out.RelAmple G L) (h : IsGrpPullback G' G f φ) (e : LBIso L' (L.pull φ))
    (hK : Out.KTriv G' L') (q : S') :
    ∃ U : S.Opens, f q ∈ U ∧ Out.KTriv ((Over.pullback U.ι).obj G) (L.pull (pullback.fst G.hom U.ι)) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hfqV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f q)) isOpen_univ
  replace hV : IsAffineOpen V := hV
  haveI : IsNoetherianRing Γ(S, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hAp : IsGrpPullback ((Over.pullback hV.fromSpec).obj G) G hV.fromSpec (pullback.fst G.hom hV.fromSpec) :=
    isGrpPullback_pullback G hV.fromSpec
  have hLA : (L.pull (pullback.fst G.hom hV.fromSpec)).IsLB := pull_isLB hL _
  obtain ⟨hAb, hAamp, -⟩ := GlobalTheory.pol_pull S _ G ((Over.pullback hV.fromSpec).obj G) hV.fromSpec _ L _ hL hLA hG hAp
    (PolBaseChange.lbIso_refl hLA)
  have hrange : Set.range (S'.fromSpecResidueField q ≫ f) ⊆ Set.range hV.fromSpec := by
    rintro _ ⟨z, rfl⟩
    rw [hV.range_fromSpec]
    simpa using hfqV
  obtain ⟨m, hm⟩ : ∃ m : Spec (S'.residueField q) ⟶ Spec Γ(S, V),
      m ≫ hV.fromSpec = S'.fromSpecResidueField q ≫ f :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hrange⟩
  have hx : spMap (Spec.preimage m).hom = m := Spec.map_preimage m
  have hpt : spMap (Spec.preimage m).hom ≫ hV.fromSpec = S'.fromSpecResidueField q ≫ f := by rw [hx, hm]
  have h₂ := IsGrpPullback.congr (isGrpPullback_comp'
    (isGrpPullback_pullback ((Over.pullback hV.fromSpec).obj G) (spMap (Spec.preimage m).hom)) hAp) hpt rfl
  have hK₀ := kTriv_transfer hL hL' (pull_isLB hLA _) h h₂ e
    (LBIso.symm (GlobalTheory.GenSpread.lbIso_pull_pull hL _ rfl)) hK
  obtain ⟨r, hr, hsp⟩ := GlobalTheory.T.exists_basicOpen_kTriv_of_fibre Γ(S, V) ((Over.pullback hV.fromSpec).obj G)
    (L.pull (pullback.fst G.hom hV.fromSpec)) (S'.residueField q) (Spec.preimage m).hom
    ((Over.pullback (spMap (Spec.preimage m).hom)).obj ((Over.pullback hV.fromSpec).obj G))
    (pullback.fst ((Over.pullback hV.fromSpec).obj G).hom (spMap (Spec.preimage m).hom)) hAb hLA (hAamp hA)
    (isGrpPullback_pullback ((Over.pullback hV.fromSpec).obj G) (spMap (Spec.preimage m).hom)) hK₀
  have hmem : f q ∈ S.basicOpen r := by
    let z : Spec (S'.residueField q) := IsLocalRing.closedPoint (S'.residueField q)
    have e1 : (m ≫ hV.fromSpec) z = (S'.fromSpecResidueField q ≫ f) z := by rw [hm]
    simp only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] at e1
    rw [← e1]
    show m z ∈ hV.fromSpec ⁻¹ᵁ S.basicOpen r
    rw [hV.fromSpec_preimage_basicOpen]
    have hmz : m z = PrimeSpectrum.comap (Spec.preimage m).hom z :=
      (congrArg (fun k : Spec (S'.residueField q) ⟶ Spec Γ(S, V) => k z) (Spec.map_preimage m)).symm
    rw [hmz]
    show r ∉ (PrimeSpectrum.comap (Spec.preimage m).hom z).asIdeal
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    intro hin
    apply hr
    have : ¬ IsUnit ((Spec.preimage m).hom r) := (IsLocalRing.mem_maximalIdeal _).1 hin
    simpa using this
  have hU := hV.basicOpen r
  refine ⟨S.basicOpen r, hmem, ?_⟩
  have hunit : IsUnit ((S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom r) :=
    S.toRingedSpace.isUnit_res_basicOpen r
  have hK' := hsp Γ(S, S.basicOpen r) (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom
    ((Over.pullback (spMap (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom)).obj
      ((Over.pullback hV.fromSpec).obj G))
    (pullback.fst ((Over.pullback hV.fromSpec).obj G).hom (spMap (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom))
    hunit (isGrpPullback_pullback ((Over.pullback hV.fromSpec).obj G) (spMap (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom))
  have h₁' := isGrpPullback_comp' (isGrpPullback_pullback ((Over.pullback hV.fromSpec).obj G)
    (spMap (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom)) hAp
  have hιeq : (S.basicOpen r).ι = hU.isoSpec.hom ≫
      (spMap (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom ≫ hV.fromSpec) := by
    rw [show spMap (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom ≫ hV.fromSpec = hU.fromSpec from
      hV.map_fromSpec hU (homOfLE (S.basicOpen_le r)).op, hU.isoSpec_hom_fromSpec]
  have h₂' := IsGrpPullback.congr (isGrpPullback_pullback G (S.basicOpen r).ι) hιeq rfl
  exact kTriv_transfer hL (pull_isLB hLA _) (pull_isLB hL _) h₁' h₂'
    (LBIso.symm (GlobalTheory.GenSpread.lbIso_pull_pull hL _ rfl)) (PolBaseChange.lbIso_refl (pull_isLB hL _)) hK'

theorem exists_open {S S' : Scheme.{0}} [IsLocallyNoetherian S] {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hG : IsAbelianScheme G) (hA : Out.RelAmple G L) (h : IsGrpPullback G' G f φ) (e : LBIso L' (L.pull φ))
    (hK : Out.KTriv G' L') (q : S') :
    ∃ U : S.Opens, f q ∈ U ∧ Out.KTriv ((Over.pullback U.ι).obj G) (L.pull (pullback.fst G.hom U.ι)) := exists_open_kTriv_restrict_of_kTriv_fibre hL hL' hG hA h e hK q

theorem kTriv_of_forall_point : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → (∀ p : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S) (t' : SAB H S') (_ : SABMap t' t f), p ∈ Set.range f ∧ Out.KTriv t'.G t'.PP.L) → Out.KTriv t.G t.PP.L := by
  intro hLaws E _ _ _ H S _ t hP hA h
  haveI : IsProper t.G.hom := hP
  have hAb : IsAbelianScheme t.G := AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi
  have hL : t.PP.L.IsLB := t.PP.isLB
  have hU : ∀ p : S, ∃ U : S.Opens, p ∈ U ∧
      Out.KTriv ((Over.pullback U.ι).obj t.G) (t.PP.L.pull (pullback.fst t.G.hom U.ι)) := by
    intro p
    obtain ⟨S', f, t', ⟨cm, cart, -, -, lin⟩, ⟨q, rfl⟩, hk⟩ := h p
    obtain ⟨w, hw, -⟩ := lin
    exact exists_open hL t'.PP.isLB hAb hA cart ⟨w, hw⟩ hk q
  choose U hpU hKU using hU
  exact GlobalTheory.CoverGlue.kTriv_of_cover S S U t.G (fun p => (Over.pullback (U p).ι).obj t.G)
    (fun p => pullback.fst t.G.hom (U p).ι)
    (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hpU x⟩)
    (fun p => isGrpPullback_pullback t.G (U p).ι) t.PP.L (fun p => t.PP.L.pull (pullback.fst t.G.hom (U p).ι))
    hL (fun p => pull_isLB hL _) (fun p => PolBaseChange.lbIso_refl (pull_isLB hL _)) hAb
    (fun p => (GlobalTheory.pol_pull S (U p).toScheme t.G _ (U p).ι _ t.PP.L _ hL (pull_isLB hL _) hAb
      (isGrpPullback_pullback t.G (U p).ι) (PolBaseChange.lbIso_refl (pull_isLB hL _))).1) hKU

end GlobalTheory.KTrivGlob
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.KernelTrivialOfEveryPointCoveredStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelTrivial_of_every_point_covered : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → (∀ p : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S) (t' : SAB H S') (_ : SABMap t' t f), p ∈ Set.range f ∧ Out.KTriv t'.G t'.PP.L) → Out.KTriv t.G t.PP.L := by
  first | exact @GlobalTheory.KTrivGlob.kTriv_of_forall_point | exact GlobalTheory.KTrivGlob.kTriv_of_forall_point | (intros; apply GlobalTheory.KTrivGlob.kTriv_of_forall_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPointOfIsPeriod
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.Moduli

theorem exists_point_of_isPeriod : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (P : D'.La →+ (Fin g → ℂ)), (D'.p = D.p ∧ D'.q = D.q ∧ ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧ σ (baseKA l).ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (ν l.A : ℂ) / l.A) ∧ t = f l.M') → IsPeriod D' ty P → ∃ (y : Sp ℂ ⟶ Xo.X) (e : (Fin g → ℂ) → (Over.mk y ⟶ Xo.univ.t.G)), (y ≫ Xo.s = spMap σ ∧ IsPeriod D' ty P ∧ ((∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ (∀ w, ∃! v : epsPt y ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ (∀ v : epsPt y ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) ∧ (∀ z, e z = 1 ↔ z ∈ (P).range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ Xo.univ.eta a = e ((l.M : ℂ)⁻¹ • P (t a))) ∧ ∀ a, toUnit _ ≫ Xo.univ.etaA a = e ((l.A : ℂ)⁻¹ • P (t a))) := by
  intro hT hL
  have hG : Out.GlobalFnsSt := hL.globalFns
  exact GlobalTheory.exists_point_of_period hT hL GlobalTheory.Moduli.cube_of_isLB GlobalTheory.principalTorus_algebraic
    (GlobalTheory.exists_isMonHom_of_map_lattice hT hL) (GlobalTheory.T.lambdaBundle_adjoint_of_weilPairing_adjoint hL)
    (GlobalTheory.PrimNorm.exists_primitive_normalisation hG) (GlobalTheory.kTriv_of_descent hL)
    GlobalTheory.relAmple_finite_pow_iso (GlobalTheory.moduli_rep_of_base GlobalTheory.ObjMaps.id_comp_cancel)

end GlobalTheory.Moduli
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.KTrivAwayOfKTrivFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

private theorem isGrpPullback_pullback_obj {S S' : Scheme.{0}} (G : Over S) [GrpObj G] (f : S' ⟶ S) :
    IsGrpPullback ((Over.pullback f).obj G) G f (pullback.fst G.hom f) := by
  refine ⟨IsPullback.of_hasPullback _ _, ?_⟩
  intro T x y x₀ y₀ hx hy
  have e : (lift x₀ y₀).left =
      (lift x y).left ≫ (Functor.LaxMonoidal.μ (Over.pullback f) G G).left ≫
        pullback.fst (G ⊗ G).hom f := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [Over.μ_pullback_left_fst_fst]
      simp only [Over.lift_left, pullback.lift_fst, pullback.lift_fst_assoc, hx]
    · simp only [Category.assoc]
      rw [Over.μ_pullback_left_fst_snd]
      simp only [Over.lift_left, pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_fst_assoc, hy]
  rw [Hom.mul_def, Hom.mul_def, Over.comp_left, Over.comp_left, e, Functor.obj.μ_def, Over.comp_left]
  simp only [Category.assoc]
  refine congrArg (_ ≫ ·) (congrArg (_ ≫ ·) ?_)
  first
    | exact (pullback.lift_fst _ _ _).symm
    | (erw [Over.pullback_map_left]; simp)

theorem kTriv_away_of_kTriv_fibre : Out.GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (L : LB A.left) (K : Type) [Field K] (x : R →+* K), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → Out.KTriv ((Over.pullback (spMap x)).obj A) (L.pull (pullback.fst A.hom (spMap x))) → ∃ f : R, x f ≠ 0 ∧ Out.KTriv ((Over.pullback (spMap (algebraMap R (Localization.Away f)))).obj A) (L.pull (pullback.fst A.hom (spMap (algebraMap R (Localization.Away f))))) := by
  intro _ R _ _ A _ L K _ x hA hL hR hK
  obtain ⟨f, hf, H⟩ := GlobalTheory.T.exists_basicOpen_kTriv_of_fibre R A L K x ((Over.pullback (spMap x)).obj A)
    (pullback.fst A.hom (spMap x)) hA hL hR (isGrpPullback_pullback_obj A (spMap x)) hK
  exact ⟨f, hf, H (Localization.Away f) (algebraMap R (Localization.Away f)) _ _
    (IsLocalization.Away.algebraMap_isUnit f) (isGrpPullback_pullback_obj A _)⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaClosureOpenFamilyQprojFlatReducedExt
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaClosureOpenFamilyQprojFlatReducedExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem isQProjOver_opens_of_noetherian {o : Type} [CommRing o] [IsNoetherianRing o] {X : Scheme.{0}} {s : X ⟶ Sp o}
    (h : IsQProjOver s) (U : X.Opens) : IsQProjOver (U.ι ≫ s) := by
  obtain ⟨N, i, hi, hq, rfl⟩ := h
  have : IsProper (PSpace.str o N) := isProper_str o N
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (i ≫ PSpace.str o N)
  exact ⟨N, U.ι ≫ i, inferInstance, inferInstance, by simp⟩

theorem isIso_of_closedPoint_mem_range {R : Type} [CommRing R] [IsLocalRing R] {Z : Scheme.{0}} (z : Z ⟶ Sp R)
    [IsOpenImmersion z] (h : (IsLocalRing.closedPoint R : Sp R) ∈ Set.range z) : IsIso z := by
  have hs : Function.Surjective z := by
    intro p
    exact (IsLocalRing.specializes_closedPoint (R := R) p).mem_open z.isOpenEmbedding.isOpen_range h
  have : Epi z.base := (TopCat.epi_iff_surjective _).2 hs
  exact IsOpenImmersion.isIso z

theorem TObj.exists_hasTh_of_isLocalRing (h1 : Out.Laws) (h2 : Out.Laws2) {o : Type} [CommRing o] {g N' : ℕ} {J : Type}
    {b : TBase o (N' ^ 2)} (hN : Odd N') {R : Type} [CommRing R] [IsLocalRing R] {s' : Sp R ⟶ Sp o}
    (t : TObj g (N' ^ 2) J b s') : ∃ v, t.HasTh (𝟙 (Sp R)) v := by
  obtain ⟨R', _, z, v, hz, hp, hv⟩ := GlobalTheory.T.exists_thetaConstants_locally_on_base h1 h2 o g N' J b _ s' t hN (IsLocalRing.closedPoint R)
  have := isIso_of_closedPoint_mem_range z hp
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (inv z)
  have := GlobalTheory.T.hasThetaConstants_ring_baseChange h2 o g N' J b _ s' t R' R φ.hom z v hv
  have e : spMap φ.hom ≫ z = 𝟙 (Sp R) := by
    change Spec.map φ ≫ z = _
    rw [hφ, IsIso.inv_hom_id]
  rw [e] at this
  exact ⟨_, this⟩

theorem WFam.qproj_flat_reduced_ext : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g n N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) Mat κ (F : WFam n em C Mat κ), Odd N' → (IsQProjOver (F.U.ι ≫ F.Y.s) ∨ ¬ IsNoetherianRing o) ∧ Flat (F.U.ι ≫ F.Y.s) ∧ IsReduced F.U.toScheme ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (x y : Sp R ⟶ F.U.toScheme) (s' : Sp R ⟶ Sp o) (t : TObj g (N' ^ 2) J b s'), x ≫ F.U.ι ≫ F.Y.s = y ≫ F.U.ι ≫ F.Y.s → TMap t F.univ x → TMap t F.univ y → x = y := by
  intro h1 h2 o _ g n N' J b em C Mat κ F hN
  have := F.Y.flat
  have := F.Y.reduced
  refine ⟨?_, inferInstance, isReduced_of_isOpenImmersion F.U.ι, ?_⟩
  · by_cases hn : IsNoetherianRing o
    · exact Or.inl (isQProjOver_opens_of_noetherian F.Y.qproj F.U)
    · exact Or.inr hn
  · intro R _ _ x y s' t hxy hx hy
    obtain ⟨v, hv⟩ := TObj.exists_hasTh_of_isLocalRing h1 h2 hN t
    have vx := (GlobalTheory.T.hasThetaConstants_iff_of_thetaLevelPullback o g N' J b _ _ F.univ _ s' t x R (𝟙 _) v hx).1 hv
    have vy := (GlobalTheory.T.hasThetaConstants_iff_of_thetaLevelPullback o g N' J b _ _ F.univ _ s' t y R (𝟙 _) v hy).1 hv
    rw [Category.id_comp] at vx vy
    have cx := (F.th R x v).1 vx
    have cy := (F.th R y v).1 vy
    obtain ⟨β, hβ⟩ := Spec.map_surjective (x ≫ F.U.ι ≫ F.Y.s)
    have bx : (x ≫ F.U.ι) ≫ F.Y.s = spMap β.hom := by rw [Category.assoc, ← hβ]; rfl
    have by' : (y ≫ F.U.ι) ≫ F.Y.s = spMap β.hom := by rw [Category.assoc, ← hxy, ← hβ]; rfl
    have hin := F.Y.loc R β.hom _ v bx cx
    have := (F.Y.pts R β.hom v hin).unique ⟨bx, cx⟩ ⟨by', cy⟩
    exact (cancel_mono F.U.ι).1 this

end GlobalTheory.ZM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaClosureOpenFamilyQprojFlatReducedExtStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaClosureOpenFamily_qproj_flat_reduced_ext : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g n N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) Mat κ (F : WFam n em C Mat κ), Odd N' → (IsQProjOver (F.U.ι ≫ F.Y.s) ∨ ¬ IsNoetherianRing o) ∧ Flat (F.U.ι ≫ F.Y.s) ∧ IsReduced F.U.toScheme ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (x y : Sp R ⟶ F.U.toScheme) (s' : Sp R ⟶ Sp o) (t : TObj g (N' ^ 2) J b s'), x ≫ F.U.ι ≫ F.Y.s = y ≫ F.U.ι ≫ F.Y.s → TMap t F.univ x → TMap t F.univ y → x = y := by
  first | exact @GlobalTheory.ZM.WFam.qproj_flat_reduced_ext | exact GlobalTheory.ZM.WFam.qproj_flat_reduced_ext | (intros; apply GlobalTheory.ZM.WFam.qproj_flat_reduced_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelIsometryOfDenseGeometricPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelIsometryOfDenseGeometricPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LevelSpread

theorem exists_closed_eq {S : Scheme.{0}} {Z A : Over S} [IsSeparated A.hom] (u u' : Z ⟶ A) :
    ∃ C : Set Z.left, IsClosed C ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ S) (h : Over.mk x ⟶ Z),
      h ≫ u = h ≫ u' ↔ Set.range h.left ⊆ C := by
  have : IsClosedImmersion (equalizer.ι u u').left := inferInstance
  refine ⟨Set.range (equalizer.ι u u').left, (Scheme.Hom.isClosedEmbedding _).isClosed_range,
    fun K _ x h => ⟨fun e => ?_, fun e => ?_⟩⟩
  · rintro _ ⟨p, rfl⟩
    refine ⟨(equalizer.lift h e).left p, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, equalizer.lift_ι]
  · have : IsReduced (Over.mk x).left := inferInstanceAs (IsReduced (Sp K))
    obtain ⟨f, hf⟩ := exists_lift_closedImmersion_of_dense (equalizer.ι u u').left h.left Set.univ dense_univ
      fun p _ => e ⟨p, rfl⟩
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left, ← hf, Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left,
      equalizer.condition]

theorem appTop_eq_zero_iff {Z : Scheme.{0}} (f : Γ(Z, ⊤)) {K : Type} [Field K] (h : Sp K ⟶ Z) :
    h.appTop.hom f = 0 ↔ Set.range h ⊆ (Z.basicOpen f : Set Z)ᶜ := by
  rw [← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen_top, eq_bot_iff]
  constructor
  · rintro e _ ⟨p, rfl⟩ hp
    exact e hp
  · intro e p hp
    exact e ⟨p, rfl⟩ hp

theorem map_fnOn_apply {L k : Type} [CommRing L] [CommRing k] {T : Scheme.{0}} (g : T ⟶ Sp L) (h : Sp k ⟶ T)
    (β : L →+* k) (e : h ≫ g = spMap β) (c : L) :
    h.appTop.hom (LevCover.fnOn g c) = (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (β c) := by
  have h1 : (h ≫ g).appTop = g.appTop ≫ h.appTop := Scheme.Hom.comp_appTop _ _
  have h2 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β)
  have h3 := congrArg (fun φ => φ.hom c) h2
  rw [e] at h1
  have h4 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom c)) h1
  exact h4.symm.trans h3.symm

theorem exists_unitOn {K : Type} [CommRing K] (c : Γ(Sp K, ⊤)ˣ) : ∃ ζ : Kˣ, c = unitOn ζ := by
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.toMonoidHom c, Units.ext ?_⟩
  exact ((Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id_apply c).symm

theorem pow_eq_iff {L K : Type} [CommRing L] [Field K] {T : Scheme.{0}} (g : T ⟶ Sp L) (h : Sp K ⟶ T)
    (β : L →+* K) (e : h ≫ g = spMap β) (z : L) (c : Γ(T, ⊤)ˣ) (ζ : Kˣ) (m : ℕ)
    (hc : Units.map h.appTop.hom.toMonoidHom c = unitOn ζ) :
    (ζ : K) ^ m = β z ↔ Set.range h ⊆ (T.basicOpen ((c : Γ(T, ⊤)) ^ m - LevCover.fnOn g z) : Set T)ᶜ := by
  have h1 : h.appTop.hom c = (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom ζ := congrArg Units.val hc
  rw [← appTop_eq_zero_iff, map_sub, map_pow, h1, map_fnOn_apply g h β e, ← map_pow, sub_eq_zero]
  exact ((Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.injective.eq_iff).symm

end GlobalTheory.LevelSpread

namespace GlobalTheory

open LevelSpread

theorem exists_levelIsometry_of_dense : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) (P : Out.PolAV S) (act : 𝓞 E → (P.A ⟶ P.A)) (o : Type) [CommRing o] (s : S ⟶ Sp o) (z : o) (κ : Type) (lam : κ → D.La) (pt : κ → (Out.baseOver S ⟶ P.A)) (n m : ℕ), 0 < n → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (β : o →+* K) (ζ : Kˣ) (ev : D.La → (Over.mk x ⟶ P.A)), (n : K) ≠ 0 ∧ p ∈ Set.range x ∧ x ≫ s = spMap β ∧ IsPrimitiveRoot ζ n ∧ (∀ a c, ev (a + c) = ev a * ev c) ∧ (∀ a, ev a ^ n = 1) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = ev a ≫ act c) ∧ (∀ a c, Out.WeilIs P.A P.L n (ev a) (ev c) (unitOn (ζ ^ D.EF a c))) ∧ (ζ : K) ^ m = β z ∧ ∀ i, ev (lam i) ^ m = (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ pt i} → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (β : o →+* K), (n : K) ≠ 0 → x ≫ s = spMap β → ∃ (ζ : Kˣ) (ev : D.La → (Over.mk x ⟶ P.A)), IsPrimitiveRoot ζ n ∧ (∀ a c, ev (a + c) = ev a * ev c) ∧ (∀ a, ev a ^ n = 1) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = ev a ≫ act c) ∧ (∀ a c, Out.WeilIs P.A P.L n (ev a) (ev c) (unitOn (ζ ^ D.EF a c))) ∧ (ζ : K) ^ m = β z ∧ ∀ i, ev (lam i) ^ m = (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ pt i := by
  intro hL E _ _ _ H D S P act o _ s z κ lam pt n m hn hD K _ _ x β hK hx
  obtain ⟨hfree, hfin⟩ := LevCover.datum_free D
  have := P.isAb.comm
  have := P.isAb.proper
  obtain ⟨Z, et, c, hu, hadd, hpow, hc, hprim, hrep, hlast⟩ := GlobalTheory.T.exists_finite_scheme_latticeTorsionHom_primitiveRoot S P.A n D.La P.isAb hn
  choose C1 hC1 HC1 using fun (b : 𝓞 E) (a : D.La) => exists_closed_eq (et (b • a)) (et a ≫ act b)
  choose C2 hC2 HC2 using fun (a a' : D.La) => GlobalTheory.exists_clopen_weilIs_iff hL S P n Z (et a) (et a')
    (c ^ D.EF a a') hn hu (hpow _) (hpow _)
    (by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc, one_zpow])
  let q : Z ⟶ Out.baseOver S := Over.homMk Z.hom (by simp)
  choose C4 hC4 HC4 using fun i : κ => exists_closed_eq (et (lam i) ^ m) (q ≫ pt i)
  let C3 : Set Z.left := (Z.left.basicOpen ((c : Γ(Z.left, ⊤)) ^ m - LevCover.fnOn (Z.hom ≫ s) z) : Set Z.left)ᶜ
  let C : Set Z.left := (⋂ b, ⋂ a, C1 b a) ∩ (⋂ a, ⋂ a', (C2 a a' : Set Z.left)) ∩ C3 ∩ ⋂ i, C4 i
  have hC : IsClosed C :=
    (((isClosed_iInter fun b => isClosed_iInter fun a => hC1 b a).inter
      (isClosed_iInter fun a => isClosed_iInter fun a' => hC2 a a')).inter
      (Z.left.basicOpen _).isOpen.isClosed_compl).inter (isClosed_iInter hC4)
  have key : ∀ (K : Type) [Field K] (x : Sp K ⟶ S) (β : o →+* K) (ζ : Kˣ) (h : Over.mk x ⟶ Z), x ≫ s = spMap β →
      Units.map h.left.appTop.hom.toMonoidHom c = unitOn ζ →
      (((∀ (b : 𝓞 E) a, h ≫ et (b • a) = (h ≫ et a) ≫ act b) ∧
        (∀ a a', Out.WeilIs P.A P.L n (h ≫ et a) (h ≫ et a') (unitOn (ζ ^ D.EF a a'))) ∧ (ζ : K) ^ m = β z ∧
        ∀ i, (h ≫ et (lam i)) ^ m = (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ pt i) ↔
        Set.range h.left ⊆ C) := by
    intro K _ x β ζ h hx hζ
    have hw : h.left ≫ Z.hom = x := Over.w h
    have hq : h ≫ q = (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) := Over.OverMorphism.ext hw
    have h3 := pow_eq_iff (Z.hom ≫ s) h.left β (by rw [← Category.assoc, hw, hx]) z c ζ m hζ
    have hz : ∀ k : ℤ, unitOn (ζ ^ k) = Units.map h.left.appTop.hom.toMonoidHom (c ^ k) := fun k => by
      rw [map_zpow, hζ, unitOn, unitOn, map_zpow]
    simp only [C, Set.subset_inter_iff, Set.subset_iInter_iff, and_assoc]
    refine and_congr (forall₂_congr fun b a => ?_) (and_congr (forall₂_congr fun a a' => ?_)
      (and_congr h3 (forall_congr' fun i => ?_)))
    · rw [← HC1 b a K x h, Category.assoc]
    · rw [← HC2 a a' _ h, hz]
    · rw [← HC4 i K x h, ← hq, Category.assoc, MonObj.comp_pow]
  have hdense : Dense (Z.hom '' C) := by
    refine hD.mono ?_
    rintro _ ⟨K, _, x, β, ζ, ev, hK, ⟨p, rfl⟩, hx, h1, h2, h3, h4⟩
    obtain ⟨h, hh, hζ⟩ := hrep K x ev ζ hK h2 h3 h1
    obtain rfl : (fun a => h ≫ et a) = ev := funext hh
    have hw : h.left ≫ Z.hom = x := Over.w h
    exact ⟨h.left p, (key K x β ζ h hx hζ).1 h4 ⟨p, rfl⟩, by rw [← Scheme.Hom.comp_apply, hw]⟩
  obtain ⟨h, hh⟩ := hlast C hC K x hK (by rw [hdense.closure_eq]; exact Set.subset_univ _)
  obtain ⟨ζ, hζ⟩ := exists_unitOn (K := K) (Units.map h.left.appTop.hom.toMonoidHom c)
  exact ⟨ζ, fun a => h ≫ et a, hprim K h.left ζ hζ, fun a a' => by beta_reduce; rw [hadd, MonObj.comp_mul],
    fun a => by beta_reduce; rw [← MonObj.comp_pow, hpow, MonObj.comp_one], (key K x β ζ h hx hζ).2 hh⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelIsometryOfDenseGeometricPointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_isometry_of_dense_geometric_points : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) (P : Out.PolAV S) (act : 𝓞 E → (P.A ⟶ P.A)) (o : Type) [CommRing o] (s : S ⟶ Sp o) (z : o) (κ : Type) (lam : κ → D.La) (pt : κ → (Out.baseOver S ⟶ P.A)) (n m : ℕ), 0 < n → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (β : o →+* K) (ζ : Kˣ) (ev : D.La → (Over.mk x ⟶ P.A)), (n : K) ≠ 0 ∧ p ∈ Set.range x ∧ x ≫ s = spMap β ∧ IsPrimitiveRoot ζ n ∧ (∀ a c, ev (a + c) = ev a * ev c) ∧ (∀ a, ev a ^ n = 1) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = ev a ≫ act c) ∧ (∀ a c, Out.WeilIs P.A P.L n (ev a) (ev c) (unitOn (ζ ^ D.EF a c))) ∧ (ζ : K) ^ m = β z ∧ ∀ i, ev (lam i) ^ m = (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ pt i} → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (β : o →+* K), (n : K) ≠ 0 → x ≫ s = spMap β → ∃ (ζ : Kˣ) (ev : D.La → (Over.mk x ⟶ P.A)), IsPrimitiveRoot ζ n ∧ (∀ a c, ev (a + c) = ev a * ev c) ∧ (∀ a, ev a ^ n = 1) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = ev a ≫ act c) ∧ (∀ a c, Out.WeilIs P.A P.L n (ev a) (ev c) (unitOn (ζ ^ D.EF a c))) ∧ (ζ : K) ^ m = β z ∧ ∀ i, ev (lam i) ^ m = (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ pt i := by
  first | exact @GlobalTheory.exists_levelIsometry_of_dense | exact GlobalTheory.exists_levelIsometry_of_dense | (intros; apply GlobalTheory.exists_levelIsometry_of_dense <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPolarisationDescentMulOddVeryDense
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPolarisationDescentMulOddVeryDense
noncomputable section

namespace GlobalTheory.MulDescent

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem comp_eq_one_of_kTriv_pull {S S' : Scheme.{0}} {f : S' ⟶ S}
    {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}
    (h : IsGrpPullback A' A f φ) (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (hK : KTriv A' L')
    {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S) (x : Over.mk t ⟶ A)
    (hx : ∀ p : Spec (CommRingCat.of R), ∃ V : (Spec (CommRingCat.of R)).Opens, p ∈ V ∧
      ∃ c : LB.Gen ((translDiff A L x).pull ((fst (Over.mk t) A).left ⁻¹ᵁ V).ι), c.IsGen)
    {R' : CommRingCat.{0}} (g : Spec R' ⟶ Spec (CommRingCat.of R)) (t' : Spec R' ⟶ S') (sq : g ≫ t = t' ≫ f) :
    g ≫ x.left = g ≫ (1 : Over.mk t ⟶ A).left := by
  obtain ⟨w, hw⟩ := hw
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
  exact congrArg (fun q => q.left) e₂

theorem kTriv_of_locally {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    (H : ∀ s : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S), IsOpenImmersion f ∧ IsAffineHom f ∧ s ∈ Set.range f ∧
      KTriv ((Over.pullback f).obj A) (L.pull (pullback.fst A.hom f))) : KTriv A L := by
  intro R _ t x hx
  refine Over.OverMorphism.ext (Scheme.hom_ext_of_forall x.left (1 : Over.mk t ⟶ A).left fun p => ?_)
  obtain ⟨S', f, h₁, h₂, ⟨s, hs⟩, hK⟩ := H (t p)
  have : IsAffine (pullback t f) := isAffine_of_isAffineHom (pullback.fst t f)
  let g := (pullback t f).isoSpec.inv ≫ pullback.fst t f
  have e := comp_eq_one_of_kTriv_pull (isGrpPullback_pullback A f) hL (LB.isLB_pull hL _)
    (PolBaseChange.lbIso_refl (LB.isLB_pull hL _)) hK t x hx g ((pullback t f).isoSpec.inv ≫ pullback.snd t f)
    (by rw [Category.assoc, Category.assoc, pullback.condition])
  have e' : pullback.fst t f ≫ x.left = pullback.fst t f ≫ (1 : Over.mk t ⟶ A).left := by
    rw [← cancel_epi (pullback t f).isoSpec.inv, ← Category.assoc, ← Category.assoc]
    exact e
  refine ⟨(pullback.fst t f).opensRange, ?_, ?_⟩
  · show p ∈ Set.range (pullback.fst t f)
    rw [Scheme.Pullback.range_fst]
    exact ⟨s, hs⟩
  · rw [← cancel_epi (pullback.fst t f).isoOpensRange.hom, ← Category.assoc, ← Category.assoc]
    erw [Scheme.Hom.isoOpensRange_hom_ι]
    exact e'

theorem kTriv_of_lbIso {S : Scheme.{0}} {A : Over S} [GrpObj A] {L L' : LB A.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (h : LBIso L L') (hK : KTriv A L) : KTriv A L' := by
  obtain ⟨w, hw⟩ : LBIso L' (L.pull (Iso.refl A).hom.left) :=
    h.symm.chartPull (Geo.Tor.chartPullId L') (Geo.Tor.chartPullPull L (𝟙 _) (𝟙 _) rfl)
  have : IsMonHom (Iso.refl A).hom := inferInstanceAs (IsMonHom (𝟙 A))
  exact kTriv_pull (isGrpPullback_of_iso (Iso.refl A)) hL hL' ((isGen_iff w).1 hw) hK

end GlobalTheory.MulDescent

namespace GlobalTheory.MulDescent

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem exists_polarisation_of_veryDense : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (A : Over (Sp R)) [GrpObj A] (g m : ℕ) (M : LB A.left) (P : Set (Ideal R)) (pt : Fin (2 * g) → (𝟙_ (Over (Sp R)) ⟶ A)), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Odd m → IsUnit (m : R) → M.IsLB → Out.RelAmple A M → (∀ (q₀ : Ideal R) (f₀ : R), q₀.IsPrime → f₀ ∉ q₀ → ∃ p₀ ∈ P, p₀.IsPrime ∧ q₀ ≤ p₀ ∧ f₀ ∉ p₀) → (∀ i, pt i ^ m = 1) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (y : Over.mk x ⟶ A), y ^ m = 1 → ∃! c : Fin (2 * g) → ZMod m, Out.linComb (fun i => toUnit (Over.mk x) ≫ pt i) (fun i => (c i).val) = y) → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K) (Pl : Out.PolAV (Sp K)) (φ : Pl.A.left ⟶ A.left), RingHom.ker x = q ∧ IsGrpPullback Pl.A A (spMap x) φ ∧ LBIso (lbPow Pl.L (m ^ 2)) (M.pull φ)) → ∃ L : LB A.left, L.IsLB ∧ Out.Rigidified A L ∧ Out.Sym A L ∧ Out.RelAmple A L ∧ Out.KTriv A L ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (Pl : Out.PolAV (Sp K)) (φ : Pl.A.left ⟶ A.left), IsGrpPullback Pl.A A (spMap x) φ → LBIso (lbPow Pl.L (m ^ 2)) (M.pull φ) → LBIso Pl.L (L.pull φ) := by
  intro h₁ h₂ R _ _ _ A _ g m M P pt hA hg hm hu hM hamp hP hpt hbas hfib
  obtain ⟨L, hL, hrig, hsym, hLa, hiso⟩ := GlobalTheory.OddDescent.exists_descended h₁ h₂ R A g m M pt hA hg hm hu hM hamp hpt hbas (by
    intro f hf
    refine IsNilpotent.eq_zero (nilpotent_iff_mem_prime.2 fun q hq => ?_)
    by_contra hn
    obtain ⟨p, hp, hp', -, hfp⟩ := hP q f hq hn
    exact hfp (hf p (hfib p hp) hp'))
  refine ⟨L, hL, hrig, hsym, hLa, kTriv_of_locally hL fun s => ?_, hiso⟩
  have hs : (s : PrimeSpectrum R).asIdeal.IsPrime := (s : PrimeSpectrum R).isPrime
  obtain ⟨p, hp, -, hle, -⟩ := hP (s : PrimeSpectrum R).asIdeal 1 hs
    (fun h => hs.ne_top ((Ideal.eq_top_iff_one _).2 h))
  obtain ⟨K, _, _, x, Pl, φ, hker, hφ, hw⟩ := hfib p hp
  obtain ⟨f, hf, H⟩ := GlobalTheory.KTrivSpread.exists_kTriv_of_isUnit R A L K x Pl.A φ hA hL hLa hφ
    (kTriv_of_lbIso Pl.isLB (LB.isLB_pull hL _) (hiso K x Pl φ hφ hw) Pl.ktriv)
  have hfs : f ∉ (s : PrimeSpectrum R).asIdeal := fun h => hf (by
    have := hle h
    rwa [← hker, RingHom.mem_ker] at this)
  have ho : IsOpenImmersion (spMap (algebraMap R (Localization.Away f))) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))))
  refine ⟨_, spMap (algebraMap R (Localization.Away f)), ho, inferInstance, ?_,
    H (Localization.Away f) (algebraMap R _) _ _ (IsLocalization.Away.algebraMap_isUnit f)
      (isGrpPullback_pullback A _)⟩
  have : s ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
    exact hfs
  exact this

end GlobalTheory.MulDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPolarisationDescentMulOddVeryDenseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polarisation_descent_mul_odd_veryDense : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (A : Over (Sp R)) [GrpObj A] (g m : ℕ) (M : LB A.left) (P : Set (Ideal R)) (pt : Fin (2 * g) → (𝟙_ (Over (Sp R)) ⟶ A)), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Odd m → IsUnit (m : R) → M.IsLB → Out.RelAmple A M → (∀ (q₀ : Ideal R) (f₀ : R), q₀.IsPrime → f₀ ∉ q₀ → ∃ p₀ ∈ P, p₀.IsPrime ∧ q₀ ≤ p₀ ∧ f₀ ∉ p₀) → (∀ i, pt i ^ m = 1) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (y : Over.mk x ⟶ A), y ^ m = 1 → ∃! c : Fin (2 * g) → ZMod m, Out.linComb (fun i => toUnit (Over.mk x) ≫ pt i) (fun i => (c i).val) = y) → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K) (Pl : Out.PolAV (Sp K)) (φ : Pl.A.left ⟶ A.left), RingHom.ker x = q ∧ IsGrpPullback Pl.A A (spMap x) φ ∧ LBIso (lbPow Pl.L (m ^ 2)) (M.pull φ)) → ∃ L : LB A.left, L.IsLB ∧ Out.Rigidified A L ∧ Out.Sym A L ∧ Out.RelAmple A L ∧ Out.KTriv A L ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (Pl : Out.PolAV (Sp K)) (φ : Pl.A.left ⟶ A.left), IsGrpPullback Pl.A A (spMap x) φ → LBIso (lbPow Pl.L (m ^ 2)) (M.pull φ) → LBIso Pl.L (L.pull φ) := by
  first | exact @GlobalTheory.MulDescent.exists_polarisation_of_veryDense | exact GlobalTheory.MulDescent.exists_polarisation_of_veryDense | (intros; apply GlobalTheory.MulDescent.exists_polarisation_of_veryDense <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleDeeperLevelCover
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleDeeperLevelCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LevCover

theorem levelCover_closed : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B : Type) [Field B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), 1 ≤ D.p + D.q → l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (S₂ : Scheme.{0}) (π : S₂ ⟶ S) (o₂ : Obj D l₂ b₂ (π ≫ s)) (m : SABMap o₂.t o.t π), IsFinite π ∧ Etale π ∧ Surjective π ∧ ((∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = π ≫ (o.eta a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = π ≫ (o.etaA a).left)) ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (o' : Obj D l₂ b₂ (f ≫ s)) (m' : SABMap o'.t o.t f), (∀ a, (o'.eta a ^ (l₂.M / l.M)).left ≫ m'.φ = f ≫ (o.eta a).left) ∧ (∀ a, (o'.etaA a ^ (l₂.A / l.A)).left ≫ m'.φ = f ≫ (o.etaA a).left) → ∃! h : T ⟶ S₂, h ≫ π = f ∧ ∃ u : ObjMap o' o₂ h, u.toSABMap.φ ≫ m.φ = m'.φ :=
  fun hL => GlobalTheory.LevCover.levelCover_field hL GlobalTheory.LiePull.lieMult_pull GlobalTheory.pol_pull
    GlobalTheory.obj_isAbelianScheme_dim_rigidified_sym GlobalTheory.SimAlg.sim_group GlobalTheory.exists_sim_lift
    GlobalTheory.tateIso_differ_by_similitude GlobalTheory.exists_finiteEtale_latticeTorsionHom
    (GlobalTheory.exists_clopen_weilIs_iff hL)
    (GlobalTheory.SimMult.exists_sim_trivial_of_mult GlobalTheory.SimAlg.sim_group GlobalTheory.exists_sim_lift)

end GlobalTheory.LevCover
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleDeeperLevelCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteEtale_deeper_level_cover : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B : Type) [Field B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), 1 ≤ D.p + D.q → l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (S₂ : Scheme.{0}) (π : S₂ ⟶ S) (o₂ : Obj D l₂ b₂ (π ≫ s)) (m : SABMap o₂.t o.t π), IsFinite π ∧ Etale π ∧ Surjective π ∧ ((∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = π ≫ (o.eta a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = π ≫ (o.etaA a).left)) ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (o' : Obj D l₂ b₂ (f ≫ s)) (m' : SABMap o'.t o.t f), (∀ a, (o'.eta a ^ (l₂.M / l.M)).left ≫ m'.φ = f ≫ (o.eta a).left) ∧ (∀ a, (o'.etaA a ^ (l₂.A / l.A)).left ≫ m'.φ = f ≫ (o.etaA a).left) → ∃! h : T ⟶ S₂, h ≫ π = f ∧ ∃ u : ObjMap o' o₂ h, u.toSABMap.φ ≫ m.φ = m'.φ := by
  first | exact @GlobalTheory.LevCover.levelCover_closed | exact GlobalTheory.LevCover.levelCover_closed | (intros; apply GlobalTheory.LevCover.levelCover_closed <;> assumption)
end
end
