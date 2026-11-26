module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftValuationSubring
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.InVVwIffOfNotTorsion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Desc

variable {R : Type} [CommRing R] [IsDomain R]

abbrev SecF (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) : Type :=
  GlobalTheory.FieldBaseChange.SecOver (fst (TFK (R := R) F) A.A).left
    (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A.A).left) (fun _ => (N : ℤ)))

def baseEm {F : Type} [Field F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) :
    TFK (R := R) F ⟶ TFK (R := R) (Kb R) :=
  Over.homMk (Spec.map (CommRingCat.ofHom em.toRingHom)) (by
    show Spec.map (CommRingCat.ofHom em.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (Kb R))) =
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    exact em.commutes r)

def famExt (D : DegPre R) {F : Type} [Field F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ) :
    Fam D (Kb R) N →ₛₗ[em.toRingHom] Fam D F N :=
  letI : Algebra (Kb R) F := em.toRingHom.toAlgebra
  haveI : IsScalarTower (FractionRing R) (Kb R) F := IsScalarTower.of_algebraMap_eq fun r => (em.commutes r).symm
  GlobalTheory.FieldBaseChange.famPull D (Kb R) F GlobalTheory.allSixLaws.1.globalFns N

def secExt (A : PolAV (Sp (FractionRing R))) {F : Type} [Field F] [Algebra (FractionRing R) F]
    (em : Kb R →ₐ[FractionRing R] F) (N : ℕ) : SecF A (Kb R) N →ₛₗ[em.toRingHom] SecF A F N :=
  GlobalTheory.FieldBaseChange.pullOver A.L (fun _ => (N : ℤ))
    (p := (baseEm em ▷ A.A).left)
    (congrArg (fun q => q.left) (whiskerRight_fst (baseEm em) A.A))
    (fun _ => (congrArg (fun q => q.left) (whiskerRight_snd (baseEm em) A.A)).symm)

end GlobalTheory.Mum.Desc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOperatorSymmetricFrameFieldExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOperatorSymmetricFrameFieldExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

noncomputable section

namespace GlobalTheory.Mum.Desc

open GlobalTheory.FieldBaseChange

theorem phiRel_famExt : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), Odd N → ∀ (p : QkPt D.toPre (Kb R) N) (w : GlobalTheory.UT.Frm D.toPre (Kb R) N p.g.b) (p' : QkPt D.toPre F N) (w' : GlobalTheory.UT.Frm D.toPre F N p'.g.b), GlobalTheory.UT.TXFrame N p w → GlobalTheory.UT.TXFrame N p' w' → QkExt em.toRingHom p p' → ∀ s s₁, PhiRel D.toPre (Kb R) N p w s s₁ → PhiRel D.toPre F N p' w' (famExt D.toPre em N s) (famExt D.toPre em N s₁) := by
  intro R _ _ _ I hI D F _ _ _ em N hN p w p' w' hw hw' hp s s₁ H
  letI : Algebra (Kb R) F := em.toRingHom.toAlgebra
  haveI : IsScalarTower (FractionRing R) (Kb R) F := IsScalarTower.of_algebraMap_eq fun r => (em.commutes r).symm
  have hL : GlobalTheory.UT.LL := ⟨GlobalTheory.allSixLaws.1, GlobalTheory.allSixLaws.2.1, GlobalTheory.allSixLaws.2.2.1, GlobalTheory.allSixLaws.2.2.2.1,
    GlobalTheory.allSixLaws.2.2.2.2.1⟩
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  obtain ⟨hy, hb, hs⟩ := hp
  have hb' : p'.g.b = baseMap (R := R) (Kb R) F ≫ p.g.b := Over.OverMorphism.ext hb
  have hb2 : (baseMap (R := R) (Kb R) F).left ≫ p.g.b.left = p'.g.b.left := hb.symm
  have h0 : (baseMap (R := R) (Kb R) F).left ≫ (DegPre.zeroF D.toPre (Kb R)).left = (DegPre.zeroF D.toPre F).left :=
    congrArg (fun q : TF (R := R) F ⟶ D.toPre.P.A => q.left) (MonObj.comp_one (M := D.toPre.P.A) (baseMap (R := R) (Kb R) F))
  have j1 : (baseMap (R := R) (Kb R) F).left ≫ jFK (R := R) (Kb R) = jFK (R := R) F := specMap_jFK (R := R) (Kb R) F
  have j2 : (baseMap (R := R) (Kb R) F).left ≫ (TF (R := R) (Kb R)).hom = (TF (R := R) F).hom := Over.w _
  obtain ⟨w'', hw'', hv⟩ := exists_gen D.toPre.P.isLB (φ' := DegPre.lineφ D.toPre F p'.g.b) (ε' := DegPre.lineε N)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by
      fin_cases i
      · exact congrArg (fun q => h q ^ _) h0
      · exact congrArg (fun q => h q ^ _) hb.symm)
    (LB.pullGen D.toPre.P.L _ _ w (baseMap (R := R) (Kb R) F).left) (pullGen_isGen _ _ _ _ hw.1 _)
  have hX : GlobalTheory.UT.TXFrame N p' w'' := by
    refine ⟨hw'', fun ν hν z J hJ => ?_, fun κ hκ z J hJ => ?_⟩
    · have C : LB.Gen.Corr D.toPre.P.L _ _ _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ w 2)
          (LB.mulGen D.toPre.P.L _ _ _ _ (p.g.s p.y) (LB.pullGen D.toPre.P.L _ _ ν p.g.b.left)) :=
        corr_of_val D.toPre.P.isLB fun y J hJ => by
          rw [val_mul hJ, val_pull hJ, Category.id_comp]
          exact (map_pow _ _ _).trans (hw.2.1 ν hν y J hJ)
      have e := val_corr hJ C (baseMap (R := R) (Kb R) F).left
      rw [val_mul hJ, val_pull hJ, hb2] at e
      rw [hv _ _ z J hJ, val_pull hJ, val_corr hJ (hs p'.y), val_pull hJ, hy, Category.id_comp, Category.id_comp]
      exact (map_pow _ _ _).symm.trans e
    · have C : LB.Gen.Corr D.toPre.P.L _ _ _ _
          (LB.mulGen D.toPre.P.L _ _ _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ w N) (LB.pullGen D.toPre.P.L _ _ κ p.g.b.left))
          (LB.mulGen D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ (D.toPre.psi p.y) (jFK (R := R) (Kb R)))
            (LB.pullGen D.toPre.P.L (fun _ : PUnit => eSec D.toPre.P.A) (fun _ => 1) D.toPre.rig
              (TF (R := R) (Kb R)).hom)) :=
        corr_of_val D.toPre.P.isLB fun y J hJ => by
          rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp,
            Category.id_comp]
          exact (congrArg₂ (· * ·) (map_pow _ _ _) rfl).trans (hw.2.2 κ hκ y J hJ)
      have e := val_corr hJ C (baseMap (R := R) (Kb R) F).left
      rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ, hb2, j1, j2] at e
      rw [hv _ _ z J hJ, val_pull hJ, Category.id_comp, hy]
      exact (congrArg₂ (· * ·) (map_pow _ _ _).symm rfl).trans e
  have Cw : LB.Gen.Corr D.toPre.P.L _ _ _ _ w' (LB.pullGen D.toPre.P.L _ _ w (baseMap (R := R) (Kb R) F).left) :=
    corr_of_val D.toPre.P.isLB fun y J hJ =>
      ((GlobalTheory.UT.SymFrame.main hL R I hI D F N hN p').2 w'' w' hX hw' y J hJ).symm.trans (hv _ _ y J hJ)
  rw [phiRel_iff hG p w hw.1] at H
  refine (phiRel_iff hG p' w' hw'.1 _ _).2 ?_
  intro α β hβ T ρ z J hJ
  have e₁ : DegPre.trPt D.toPre F p'.g.b ≫ famMap D.toPre (Kb R) F =
      famMap D.toPre (Kb R) F ≫ DegPre.trPt D.toPre (Kb R) p.g.b := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, Category.assoc, famMap_fst, tr_fst, ← Category.assoc, tr_fst, famMap_fst]
    · refine ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (famMap_snd D.toPre (Kb R) F)).trans (tr_pr D.toPre F _))).trans
        (Eq.symm ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (tr_pr D.toPre (Kb R) _)).trans ?_)))
      rw [MonObj.comp_mul, famMap_snd, ← Category.assoc, famMap_fst, hb', Category.assoc]
  have e₂ : ((ρ ≫ famMap D.toPre (Kb R) F) ≫ fst _ _).left = (ρ ≫ fst _ _).left ≫ (baseMap (R := R) (Kb R) F).left := by
    rw [Category.assoc, famMap_fst, ← Category.assoc]; rfl
  have e₃ : uVal D.toPre (Kb R) N α p.g.b (ρ ≫ famMap D.toPre (Kb R) F) z J = uVal D.toPre F N α p'.g.b ρ z J := by
    have : famMap D.toPre (Kb R) F ≫ fst _ _ ≫ p.g.b = fst _ _ ≫ p'.g.b := by
      rw [← Category.assoc, famMap_fst, hb', Category.assoc]
    simp only [uVal, Category.assoc, famMap_snd, this]
  refine (sval_pullOver _ _ _ _ hJ).trans ((H α β (hy ▸ hβ) T (ρ ≫ famMap D.toPre (Kb R) F) z J hJ).trans
    (congrArg₂ (· * ·) (Eq.trans ?_ (sval_pullOver _ _ _ _ hJ).symm) (congrArg Units.val ?_)))
  · rw [Category.assoc, ← e₁, ← Category.assoc]; rfl
  · rw [e₃, val_mul hJ, val_mul hJ, val_corr hJ Cw, val_pull hJ, val_corr hJ (hs α), val_pull hJ, e₂]
    rfl

end GlobalTheory.Mum.Desc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOperatorSymmetricFrameFieldExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPointOperator_symmetricFrame_fieldExtension : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), Odd N → ∀ (p : QkPt D.toPre (Kb R) N) (w : GlobalTheory.UT.Frm D.toPre (Kb R) N p.g.b) (p' : QkPt D.toPre F N) (w' : GlobalTheory.UT.Frm D.toPre F N p'.g.b), GlobalTheory.UT.TXFrame N p w → GlobalTheory.UT.TXFrame N p' w' → QkExt em.toRingHom p p' → ∀ s s₁, PhiRel D.toPre (Kb R) N p w s s₁ → PhiRel D.toPre F N p' w' (famExt D.toPre em N s) (famExt D.toPre em N s₁) := by
  first | exact @GlobalTheory.Mum.Desc.phiRel_famExt | exact GlobalTheory.Mum.Desc.phiRel_famExt | (intros; apply GlobalTheory.Mum.Desc.phiRel_famExt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsSurjectiveOfLargerAlgClosedField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsSurjectiveOfLargerAlgClosedField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

theorem GlobalTheory.Mum.Desc.lab_onto_of_labExt : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (N : ℕ), 1 ≤ N → ∀ (lab : QkPt D (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (lab' : QkPt D F N → (TFK (R := R) F ⟶ A.A)), LabExt em lab lab' → (∀ x : TFK (R := R) F ⟶ A.A, x ^ N = 1 ↔ ∃ p, lab' p = x) → ∀ x : TFK (R := R) (Kb R) ⟶ A.A, x ^ N = 1 ↔ ∃ p, lab p = x := by
  intro R _ _ _ D A N hN lab F _ _ _ em lab' hext hon x
  obtain ⟨h1, h2⟩ := GlobalTheory.T.levelPoints_algClosure_fractionRing_bijective R D F em N hN
  have cancel : ∀ y y' : TFK (R := R) (Kb R) ⟶ A.A, baseEm em ≫ y = baseEm em ≫ y' → y = y' := by
    intro y y' h
    apply Over.OverMorphism.ext
    have spec_map_field_cancel {K C : Type} [Field K] [Field C] (gam : K →+* C)
        {X : Scheme} (y y' : Sp K ⟶ X)
        (h : spMap gam ≫ y = spMap gam ≫ y') : y = y' := by
      obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
      obtain ⟨⟨p', φ'⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y'
      simp only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢
      have e : ∀ (q : X) (ψ : X.residueField q ⟶ CommRingCat.of K),
          spMap gam ≫ (Spec.map ψ ≫ X.fromSpecResidueField q) =
            (Scheme.SpecToEquivOfField C X).symm ⟨q, ψ ≫ CommRingCat.ofHom gam⟩ := by
        intro q ψ
        simp only [Scheme.SpecToEquivOfField_symm_apply, spMap, Spec.map_comp, Category.assoc]
      rw [e, e] at h
      have h2 := (Scheme.SpecToEquivOfField C X).symm.injective h
      simp only [Sigma.mk.inj_iff] at h2
      obtain ⟨rfl, h3⟩ := h2
      have h4 : φ = φ' := by
        have h5 : φ ≫ CommRingCat.ofHom gam = φ' ≫ CommRingCat.ofHom gam := eq_of_heq h3
        ext x
        apply gam.injective
        have := congrArg (fun f => f.hom x) h5
        simpa using this
      rw [h4]
    exact spec_map_field_cancel em.toRingHom y.left y'.left (congrArg CommaMorphism.left h)
  have hlab : ∀ p p', QkExt em.toRingHom p p' → lab' p' = baseEm em ≫ lab p := by
    intro p p' hp
    apply Over.OverMorphism.ext
    exact hext p p' hp
  constructor
  · intro hx
    have hx' : (baseEm em ≫ x) ^ N = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
    obtain ⟨p', hp'⟩ := (hon _).1 hx'
    obtain ⟨p, hp, -⟩ := h2 p'
    refine ⟨p, cancel _ _ ?_⟩
    rw [← hlab p p' hp, hp']
  · rintro ⟨p, rfl⟩
    obtain ⟨p', hp', -⟩ := h1 p
    have h3 := (hon (lab' p')).2 ⟨p', rfl⟩
    rw [hlab p p' hp'] at h3
    apply cancel
    rw [MonObj.comp_pow, h3, MonObj.comp_one]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsSurjectiveOfLargerAlgClosedFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionLabels_surjective_of_larger_algClosed_field : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (N : ℕ), 1 ≤ N → ∀ (lab : QkPt D (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (lab' : QkPt D F N → (TFK (R := R) F ⟶ A.A)), LabExt em lab lab' → (∀ x : TFK (R := R) F ⟶ A.A, x ^ N = 1 ↔ ∃ p, lab' p = x) → ∀ x : TFK (R := R) (Kb R) ⟶ A.A, x ^ N = 1 ↔ ∃ p, lab p = x := by
  first | exact @GlobalTheory.Mum.Desc.lab_onto_of_labExt | exact GlobalTheory.Mum.Desc.lab_onto_of_labExt | (intros; apply GlobalTheory.Mum.Desc.lab_onto_of_labExt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearMapThetaGroupActionSections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearMapThetaGroupActionSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

noncomputable section

namespace GlobalTheory.Mum.Desc

open GlobalTheory.FieldBaseChange

theorem exists_linear_isActOf : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)), ∃ b : SecF A F N →ₗ[F] SecF A F N, ∀ t t' : SecF A F N, IsActOf A.A A.L N θ t t' ↔ t' = b t := by
  intro R _ _ A F _ _ N θ
  have hex : ∀ t : SecF A F N, ∃ u : SecF A F N, IsActOf A.A A.L N θ t u :=
    fun t => GlobalTheory.VVCompare.exists_isActOf A.A A.isLB θ t
  choose Θ hΘ using hex
  have hb : (translT A.A θ.pt).left ≫ (fst (TFK (R := R) F) A.A).left = (fst (TFK (R := R) F) A.A).left :=
    congrArg (fun q => q.left) (lift_fst _ _ : translT A.A θ.pt ≫ fst _ _ = _)
  have hv := fun (t u : SecF A F N) (h : IsActOf A.A A.L N θ t u) y J hJ =>
    GlobalTheory.VVCompare.sv_of_isTwistPull A.A h (𝟙 _) y (J := J) hJ
  refine ⟨⟨⟨Θ, fun s s' => sec_ext' A.isLB fun y J hJ => ?_⟩,
    fun c s => sec_ext' A.isLB fun y J hJ => ?_⟩, fun t t' => ⟨fun h => sec_ext' A.isLB fun y J hJ => ?_, ?_⟩⟩
  · refine (hv _ _ (hΘ _) y J hJ).trans ?_
    refine Eq.symm ((sval_add' hJ _ _ _).trans (Eq.trans ?_ (congrArg _ (sval_add' hJ _ s s')).symm))
    exact (congrArg₂ (· + ·) (hv _ _ (hΘ s) y J hJ) (hv _ _ (hΘ s') y J hJ)).trans (mul_add _ _ _).symm
  · refine (hv _ _ (hΘ _) y J hJ).trans ?_
    refine Eq.symm ((sval_smul' hJ _ _ _).trans (Eq.trans ?_ (congrArg _ (sval_smul' hJ _ c s)).symm))
    rw [Category.assoc, hb]
    exact (congrArg _ (hv _ _ (hΘ s) y J hJ)).trans (mul_left_comm _ _ _)
  · exact (hv _ _ h y J hJ).trans (hv _ _ (hΘ t) y J hJ).symm
  · rintro rfl
    exact hΘ t

end GlobalTheory.Mum.Desc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearMapThetaGroupActionSectionsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearMap_thetaGroup_action_sections : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)), ∃ b : SecF A F N →ₗ[F] SecF A F N, ∀ t t' : SecF A F N, IsActOf A.A A.L N θ t t' ↔ t' = b t := by
  first | exact @GlobalTheory.Mum.Desc.exists_linear_isActOf | exact GlobalTheory.Mum.Desc.exists_linear_isActOf | (intros; apply GlobalTheory.Mum.Desc.exists_linear_isActOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearMapTorsionPointSymmetricFrameOperato
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearMapTorsionPointSymmetricFrameOperato
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

noncomputable section

namespace GlobalTheory.Mum.PhiLinear

theorem exists_linear_phi : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : ℕ), Odd N → ∀ (p : QkPt D.toPre F N) (w : GlobalTheory.UT.Frm D.toPre F N p.g.b), GlobalTheory.UT.TXFrame N p w → ∃ a : Fam D.toPre F N →ₗ[F] Fam D.toPre F N, ∀ s s', PhiRel D.toPre F N p w s s' ↔ s' = a s := by
  intro R _ _ _ I _ D F _ _ _ N hN p w hw
  exact ReciprocityTheory.ChartRestriction.G.DVR.phiFun_of_globalFns GlobalTheory.globalFns_holds R I D F N hN.pos p w hw.1

end GlobalTheory.Mum.PhiLinear
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearMapTorsionPointSymmetricFrameOperatoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearMap_torsionPoint_symmetricFrame_operator : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : ℕ), Odd N → ∀ (p : QkPt D.toPre F N) (w : GlobalTheory.UT.Frm D.toPre F N p.g.b), GlobalTheory.UT.TXFrame N p w → ∃ a : Fam D.toPre F N →ₗ[F] Fam D.toPre F N, ∀ s s', PhiRel D.toPre F N p w s s' ↔ s' = a s := by
  first | exact @GlobalTheory.Mum.PhiLinear.exists_linear_phi | exact GlobalTheory.Mum.PhiLinear.exists_linear_phi | (intros; apply GlobalTheory.Mum.PhiLinear.exists_linear_phi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupSymmetricLiftActionFieldExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupSymmetricLiftActionFieldExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

namespace GlobalTheory.Mum.Desc

theorem isActOf_secExt : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), Odd N → ∀ (x : TFK (R := R) (Kb R) ⟶ A.A) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) (Kb R))) (θ' : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)), SymLift A.A A.L N N x θ → SymLift A.A A.L N N (baseEm em ≫ x) θ' → ∀ t t' : SecF A (Kb R) N, IsActOf A.A A.L N θ t t' → IsActOf A.A A.L N θ' (secExt A em N t) (secExt A em N t') := by
  intro R _ _ A F _ _ em N hN x θ θ' H H' t t' a
  exact GlobalTheory.WeightProbe.act_pull A hN (baseEm em) H H' a

end GlobalTheory.Mum.Desc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupSymmetricLiftActionFieldExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGroup_symmetricLift_action_fieldExtension : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), Odd N → ∀ (x : TFK (R := R) (Kb R) ⟶ A.A) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) (Kb R))) (θ' : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)), SymLift A.A A.L N N x θ → SymLift A.A A.L N N (baseEm em ≫ x) θ' → ∀ t t' : SecF A (Kb R) N, IsActOf A.A A.L N θ t t' → IsActOf A.A A.L N θ' (secExt A em N t) (secExt A em N t') := by
  first | exact @GlobalTheory.Mum.Desc.isActOf_secExt | exact GlobalTheory.Mum.Desc.isActOf_secExt | (intros; apply GlobalTheory.Mum.Desc.isActOf_secExt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundlePowSectionsAlgClosureFieldBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundlePowSectionsAlgClosureFieldBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

noncomputable section

namespace GlobalTheory.Mum.Desc

section
variable {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R)))

theorem noetherianSpace_prod_field (F : Type) [Field F] [Algebra (FractionRing R) F] :
    TopologicalSpace.NoetherianSpace (TFK (R := R) F ⊗ A.A).left := by
  have := A.isAb.proper
  let b : (TFK (R := R) F ⊗ A.A).left ⟶ Spec (CommRingCat.of F) := (fst (TFK (R := R) F) A.A).left
  have : IsProper b := inferInstanceAs (IsProper (pullback.fst _ _))
  have : IsLocallyNoetherian (TFK (R := R) F ⊗ A.A).left := LocallyOfFiniteType.isLocallyNoetherian b
  have : CompactSpace (TFK (R := R) F ⊗ A.A).left := QuasiCompact.compactSpace_of_compactSpace b
  have : IsNoetherian (TFK (R := R) F ⊗ A.A).left := {}
  infer_instance

theorem isPullback_baseEm_whiskerRight {F : Type} [Field F] [Algebra (FractionRing R) F]
    (em : Kb R →ₐ[FractionRing R] F) :
    IsPullback (baseEm em ▷ A.A).left (fst (TFK (R := R) F) A.A).left (fst (TFK (R := R) (Kb R)) A.A).left
      (baseEm em).left := by
  have h₁ : IsPullback (snd (TFK (R := R) (Kb R)) A.A).left (fst (TFK (R := R) (Kb R)) A.A).left
      A.A.hom (TFK (R := R) (Kb R)).hom := (IsPullback.of_hasPullback _ _).flip
  have h₂ : IsPullback (snd (TFK (R := R) F) A.A).left (fst (TFK (R := R) F) A.A).left
      A.A.hom (TFK (R := R) F).hom := (IsPullback.of_hasPullback _ _).flip
  refine IsPullback.of_right ?_ (congrArg (fun q => q.left) (whiskerRight_fst (baseEm em) A.A)) h₁
  have e₁ : (baseEm em ▷ A.A).left ≫ (snd (TFK (R := R) (Kb R)) A.A).left =
      (snd (TFK (R := R) F) A.A).left := congrArg (fun q => q.left) (whiskerRight_snd (baseEm em) A.A)
  have e₂ : (baseEm em).left ≫ (TFK (R := R) (Kb R)).hom = (TFK (R := R) F).hom := Over.w (baseEm em)
  rw [e₁, e₂]
  exact h₂

end

theorem isExtension_secExt : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), letI : Algebra (Kb R) F := em.toRingHom.toAlgebra; GlobalTheory.FieldBaseChange.IsExtension (secExt A em N) := by
  intro R _ _ A F _ _ em N
  letI : Algebra (Kb R) F := em.toRingHom.toAlgebra
  have := noetherianSpace_prod_field A (Kb R)
  exact GlobalTheory.FieldBaseChange.isExtension_pullOver (K := Kb R) (F := F) (isPullback_baseEm_whiskerRight A em) A.isLB _ _

end GlobalTheory.Mum.Desc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundlePowSectionsAlgClosureFieldBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundlePowSections_algClosure_fieldBaseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), letI : Algebra (Kb R) F := em.toRingHom.toAlgebra; GlobalTheory.FieldBaseChange.IsExtension (secExt A em N) := by
  first | exact @GlobalTheory.Mum.Desc.isExtension_secExt | exact GlobalTheory.Mum.Desc.isExtension_secExt | (intros; apply GlobalTheory.Mum.Desc.isExtension_secExt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntertwiningBijectiveOfFieldBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntertwiningBijectiveOfFieldBaseChange
noncomputable section

namespace GlobalTheory.FieldBaseChange

variable {K F : Type} [Field K] [Field F] [Algebra K F]

theorem exists_functional_det_map_ne_zero [Infinite K] {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n F) (hM : M.det ≠ 0) : ∃ ℓ : F →ₗ[K] K, (M.map ℓ).det ≠ 0 := by
  classical
  let e := Module.Basis.ofVectorSpace K F
  let φ : F →ₗ[K] MvPolynomial (Module.Basis.ofVectorSpaceIndex K F) K := e.constr K MvPolynomial.X
  by_contra h
  push Not at h
  have hP : (M.map φ).det = 0 := by
    refine MvPolynomial.funext fun c => ?_
    have hc : ∀ x, MvPolynomial.aeval c (φ x) = e.constr K c x := fun x =>
      LinearMap.congr_fun (e.ext (f₁ := (MvPolynomial.aeval c).toLinearMap ∘ₗ φ) (f₂ := e.constr K c)
        (fun i => by simp [φ])) x
    rw [map_zero, ← h (e.constr K c), RingHom.map_det]
    congr 1
    ext i j
    exact hc _
  have hc : ∀ x, MvPolynomial.aeval e (φ x) = x := fun x =>
    LinearMap.congr_fun (e.ext (f₁ := (MvPolynomial.aeval e).toLinearMap ∘ₗ φ) (f₂ := LinearMap.id)
      (fun i => by simp [φ])) x
  apply hM
  have := congrArg (MvPolynomial.aeval (R := K) e) hP
  rw [map_zero, AlgHom.map_det] at this
  rw [← this]
  congr 1
  ext i j
  exact (hc _).symm

variable {V W V' W' : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup V'] [Module F V'] [AddCommGroup W'] [Module F W']

theorem IsExtension.exists_basis {a : V →ₛₗ[algebraMap K F] V'} (h : IsExtension a) {ι : Type}
    (v : Module.Basis ι K V) : ∃ v' : Module.Basis ι F V', ∀ i, v' i = a (v i) := by
  have li : LinearIndependent F (fun i => a (v i)) := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    refine (Module.forall_dual_apply_eq_zero_iff K (g i)).1 fun ℓ => ?_
    obtain ⟨Λ, hΛ⟩ := h.coord ℓ
    have := congrArg Λ hg
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at this
    simp only [hΛ _ _] at this
    exact linearIndependent_iff'.1 v.linearIndependent s (fun j => ℓ (g j)) this i hi
  have sp : ⊤ ≤ Submodule.span F (Set.range fun i => a (v i)) := by
    rw [← h.span, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ Submodule.span K (Set.range v) := v.span_eq ▸ Submodule.mem_top
    show a x ∈ Submodule.span F _
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul d y _ hy => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hy
  exact ⟨Module.Basis.mk li sp, fun i => by simp⟩

theorem IsCoord.map_algebraMap_smul {a : V →ₛₗ[algebraMap K F] V'}
    (h : Submodule.span F (Set.range a) = ⊤) {ℓ : F →ₗ[K] K} {Λ : V' →+ V} (hΛ : IsCoord a ℓ Λ)
    (k : K) (x : V') : Λ (algebraMap K F k • x) = k • Λ x :=
  IsCoord.natural h hΛ hΛ (k • LinearMap.id) (algebraMap K F k • LinearMap.id)
    (fun v => by simp [map_smulₛₗ]) x

theorem exists_intertwining_bijective_of_extension (K F : Type) [Field K] [Field F] [Algebra K F]
    [Infinite K] (V W V' W' : Type) [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module F V'] [AddCommGroup W'] [Module F W'] [FiniteDimensional F V']
    (iV : V →ₛₗ[algebraMap K F] V') (iW : W →ₛₗ[algebraMap K F] W')
    (hV : IsExtension iV) (hW : IsExtension iW)
    (J : Type) (a : J → V →ₗ[K] V) (b : J → W →ₗ[K] W) (a' : J → V' →ₗ[F] V') (b' : J → W' →ₗ[F] W')
    (ha : ∀ i v, a' i (iV v) = iV (a i v)) (hb : ∀ i w, b' i (iW w) = iW (b i w))
    (E' : V' →ₗ[F] W') (hE' : Function.Bijective E') (hc : ∀ i v, E' (a' i v) = b' i (E' v)) :
    ∃ E : V →ₗ[K] W, Function.Bijective E ∧ ∀ i v, E (a i v) = b i (E v) := by
  classical
  let v := Module.Basis.ofVectorSpace K V
  let w₀ := Module.Basis.ofVectorSpace K W
  obtain ⟨v', hv'⟩ := hV.exists_basis v
  obtain ⟨w₀', -⟩ := hW.exists_basis w₀
  let e := LinearEquiv.ofBijective E' hE'
  let w := w₀.reindex (w₀'.indexEquiv (v'.map e))
  obtain ⟨w', hw'⟩ := hW.exists_basis w
  haveI := Module.Finite.finite_basis v'
  letI := Fintype.ofFinite (Module.Basis.ofVectorSpaceIndex K V)
  have hdet : (LinearMap.toMatrix v' w' E').det ≠ 0 := (LinearEquiv.isUnit_det e v' w').ne_zero
  obtain ⟨ℓ, hℓ⟩ := exists_functional_det_map_ne_zero (K := K) _ hdet
  obtain ⟨Λ, hΛ⟩ := hW.coord ℓ
  let E : V →ₗ[K] W :=
    { toFun := fun x => Λ (E' (iV x))
      map_add' := fun x y => by simp only [map_add (f := _)]
      map_smul' := fun k x => by
        rw [map_smulₛₗ, map_smul, hΛ.map_algebraMap_smul hW.span]; rfl }
  have hM : LinearMap.toMatrix v w E = (LinearMap.toMatrix v' w' E').map ℓ := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply]
    have : E (v j) = ∑ k, ℓ (w'.repr (E' (v' j)) k) • w k := by
      show Λ (E' (iV (v j))) = _
      rw [← hv']
      set_option synthInstance.maxHeartbeats 100000 in
        conv_lhs => rw [← w'.sum_repr (E' (v' j)), map_sum]
      simp only [hw', hΛ _ _]
    rw [this, w.repr_sum_self]
  refine ⟨E, ?_, fun i x => ?_⟩
  · have hu : IsUnit (LinearMap.toMatrix v w E).det := by rw [hM]; exact hℓ.isUnit
    exact (LinearEquiv.ofIsUnitDet hu).bijective
  · show Λ (E' (iV (a i x))) = b i (Λ (E' (iV x)))
    rw [← ha, hc]
    exact IsCoord.natural hW.span hΛ hΛ (b i) (b' i) (hb i) _

end GlobalTheory.FieldBaseChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntertwiningBijectiveOfFieldBaseChangeStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_intertwining_bijective_of_fieldBaseChange : ∀ (K F : Type) [Field K] [Field F] [Algebra K F] [Infinite K] (V W V' W' : Type) [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [AddCommGroup V'] [Module F V'] [AddCommGroup W'] [Module F W'] [FiniteDimensional F V'] (iV : V →ₛₗ[algebraMap K F] V') (iW : W →ₛₗ[algebraMap K F] W'), GlobalTheory.FieldBaseChange.IsExtension iV → GlobalTheory.FieldBaseChange.IsExtension iW → ∀ (J : Type) (a : J → V →ₗ[K] V) (b : J → W →ₗ[K] W) (a' : J → V' →ₗ[F] V') (b' : J → W' →ₗ[F] W'), (∀ i v, a' i (iV v) = iV (a i v)) → (∀ i w, b' i (iW w) = iW (b i w)) → ∀ E' : V' →ₗ[F] W', Function.Bijective E' → (∀ i v, E' (a' i v) = b' i (E' v)) → ∃ E : V →ₗ[K] W, Function.Bijective E ∧ ∀ i v, E (a i v) = b i (E v) := by
  first | exact @GlobalTheory.FieldBaseChange.exists_intertwining_bijective_of_extension | exact GlobalTheory.FieldBaseChange.exists_intertwining_bijective_of_extension | (intros; apply GlobalTheory.FieldBaseChange.exists_intertwining_bijective_of_extension <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.Desc

theorem lawsLL : GlobalTheory.UT.LL :=
  ⟨GlobalTheory.allSixLaws.1, GlobalTheory.allSixLaws.2.1, GlobalTheory.allSixLaws.2.2.1, GlobalTheory.allSixLaws.2.2.2.1, GlobalTheory.allSixLaws.2.2.2.2.1⟩

theorem eqv_down : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A))
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) lab' E',
    LabExt em lab lab' → Eqv D.toPre A F N lab' E' → ∃ E, Eqv D.toPre A (Kb R) N lab E := by
  intro R _ _ _ hB D A N hN lab F _ _ _ em lab' E' hL hE
  obtain ⟨hAdm, hC⟩ := hB
  have hN1 : 1 ≤ N := hN.pos
  have honto := GlobalTheory.T.torsionLabels_surjective_of_larger_algClosed_field R D.toPre A N hN1 lab F em lab' hL hE.onto
  have hframe : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing R) K] (p : QkPt D.toPre K N),
      ∃ w, GlobalTheory.UT.TXFrame N p w := fun K _ _ _ p =>
    (GlobalTheory.UT.SymFrame.main lawsLL R (maximalIdeal R) hAdm D K N hN p).1
  let J := {q : (p : QkPt D.toPre (Kb R) N) × GlobalTheory.UT.Frm D.toPre (Kb R) N p.g.b ×
      ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) (Kb R)) // GlobalTheory.UT.TXFrame N q.1 q.2.1 ∧ SymLift A.A A.L N N (lab q.1) q.2.2}
  choose a ha using fun i : J => GlobalTheory.T.exists_linearMap_torsionPoint_symmetricFrame_operator R (maximalIdeal R) hAdm D (Kb R) N hN i.1.1 i.1.2.1 i.2.1
  choose b hb using fun i : J => GlobalTheory.T.exists_linearMap_thetaGroup_action_sections R A (Kb R) N i.1.2.2
  have hq := (GlobalTheory.T.levelPoints_algClosure_fractionRing_bijective R D.toPre F em N hN1).1
  choose p' hp' using fun i : J => (hq i.1.1).exists
  choose w' hw' using fun i : J => hframe F (p' i)
  have hlab : ∀ i : J, lab' (p' i) = baseEm em ≫ lab i.1.1 := fun i =>
    Over.OverMorphism.ext (by rw [hL _ _ (hp' i)]; rfl)
  choose θ' hθ' using fun i : J =>
    GlobalTheory.WeightProbe.exists_symLift_top A hN (lab' (p' i)) ((hE.onto _).2 ⟨_, rfl⟩)
  choose a' ha' using fun i : J => GlobalTheory.T.exists_linearMap_torsionPoint_symmetricFrame_operator R (maximalIdeal R) hAdm D F N hN (p' i) (w' i) (hw' i)
  choose b' hb' using fun i : J => GlobalTheory.T.exists_linearMap_thetaGroup_action_sections R A F N (θ' i)
  letI : Algebra (Kb R) F := em.toRingHom.toAlgebra
  haveI : IsScalarTower (FractionRing R) (Kb R) F := IsScalarTower.of_algebraMap_eq fun r => (em.commutes r).symm
  haveI : FiniteDimensional F (Fam D.toPre F N) :=
    (GlobalTheory.UU.finrank_fam_of_laws GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1 R D.toPre D.tau_bimult F N hN1).1
  have hfamExt : GlobalTheory.FieldBaseChange.IsExtension (famExt D.toPre em N) :=
    GlobalTheory.FieldBaseChange.isExtension_famPull D.toPre (Kb R) F _ hN1
  have hsecExt := GlobalTheory.T.lineBundlePowSections_algClosure_fieldBaseChange R A F em N
  have ca : ∀ i v, a' i (famExt D.toPre em N v) = famExt D.toPre em N (a i v) := fun i v =>
    ((ha' i _ _).1 (GlobalTheory.T.torsionPointOperator_symmetricFrame_fieldExtension R (maximalIdeal R) hAdm D F em N hN i.1.1 i.1.2.1 (p' i) (w' i) i.2.1 (hw' i) (hp' i) v _
      ((ha i v _).2 rfl))).symm
  have cb : ∀ i t, b' i (secExt A em N t) = secExt A em N (b i t) := fun i t =>
    ((hb' i _ _).1 (GlobalTheory.T.thetaGroup_symmetricLift_action_fieldExtension R A F em N hN (lab i.1.1) i.1.2.2 (θ' i) i.2.2 (by rw [← hlab i]; exact hθ' i) t _
      ((hb i t _).2 rfl))).symm
  let E'' : Fam D.toPre F N →ₗ[F] SecF A F N :=
    { toFun := E'
      map_add' := fun s t => GlobalTheory.FieldBaseChange.SecOver.ext _ _ fun j => hE.add s t (s + t) (fun _ _ => rfl) j
      map_smul' := fun c s => GlobalTheory.FieldBaseChange.SecOver.ext _ _ fun j =>
        hE.smul c s (c • s) ((ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff _ _ _).2 rfl) j }
  have cE : ∀ i v, E'' (a' i v) = b' i (E'' v) := fun i v =>
    (hb' i _ _).1 (hE.act (p' i) (w' i) (θ' i) v (a' i v) (hw' i) (hθ' i) ((ha' i v _).2 rfl))
  obtain ⟨E, hEb, hEc⟩ := GlobalTheory.T.exists_intertwining_bijective_of_fieldBaseChange (Kb R) F _ _ _ _ (famExt D.toPre em N) (secExt A em N) hfamExt hsecExt J a b a' b'
    ca cb E'' hE.bij cE
  refine ⟨fun s => E s, ⟨hEb, ?_, ?_, honto, hframe (Kb R),
    fun p => GlobalTheory.WeightProbe.exists_symLift_top A hN (lab p) ((honto _).2 ⟨p, rfl⟩), ?_⟩⟩
  · intro s s' s'' h j
    have : s'' = s + s' := ReciprocityTheory.ChartRestriction.G.DVR.fam_ext h
    subst this
    exact congrArg (fun q : SecF A (Kb R) N => LB.Sec.f q j) (map_add E s s')
  · intro c s s' h j
    rw [(ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff _ _ _).1 h]
    exact congrArg (fun q : SecF A (Kb R) N => LB.Sec.f q j) (map_smul E c s)
  · intro p w θ s s' hw hθ hP
    let i : J := ⟨⟨p, w, θ⟩, hw, hθ⟩
    have e1 : s' = a i s := (ha i s s').1 hP
    have e2 : E s' = b i (E s) := by rw [e1]; exact hEc i s
    exact (hb i (E s) (E s')).2 e2

end GlobalTheory.Mum.Desc
