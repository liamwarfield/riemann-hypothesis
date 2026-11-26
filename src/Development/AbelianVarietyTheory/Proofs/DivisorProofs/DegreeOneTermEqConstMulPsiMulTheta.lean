module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiZeroMulRigidificationConstantNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiZeroMulRigidificationConstantNeZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section

namespace GlobalTheory.Poinc.IntTerm

theorem psi_zero_rig_const : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), ∃ c₀ : FractionRing V, c₀ ≠ 0 ∧ ∀ (z : (TF (R := V) (FractionRing V)).left) (J : ((TF (R := V) (FractionRing V)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi 0) (jFK (R := V) (FractionRing V)) z J)).val * (rigV D (TF (R := V) (FractionRing V)).hom z J).val = GlobalTheory.UT.cst (FractionRing V) z c₀ := by
  intro V _ _ D
  obtain ⟨z⟩ := GlobalTheory.UT.CoefBasic.exists_pt (R := V) (F := FractionRing V)
  obtain ⟨J', hJ'⟩ := GlobalTheory.UT.CoefBasic.exists_good' D.P.isLB z
  obtain ⟨c, hc⟩ := GlobalTheory.UT.CoefBasic.cstH_surj z
    ((@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi 0) (jFK (R := V) (FractionRing V)) z J')).val * (rigV D (TF (R := V) (FractionRing V)).hom z J').val)
  refine ⟨c, fun h => ?_, fun z' J hJ => ?_⟩
  · rw [h, map_zero] at hc
    rw [← Units.val_mul] at hc
    exact Units.ne_zero _ hc.symm
  · obtain rfl := GlobalTheory.UT.CoefBasic.pt_eq z z'
    have a₁ := GlobalTheory.UT.CoefBasic.val_tr (D.psi_gen 0) (jFK (R := V) (FractionRing V)) hJ hJ'
    have a₂ : rigV D (TF (R := V) (FractionRing V)).hom z J =
        GlobalTheory.UT.CoefBasic.trU D.P.L z J J' ((TF (R := V) (FractionRing V)).hom ≫ eSec D.P.A) *
        rigV D (TF (R := V) (FractionRing V)).hom z J' := by
      refine (GlobalTheory.UT.CoefBasic.val_tr (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig_gen
        (TF (R := V) (FractionRing V)).hom hJ hJ').trans ?_
      rw [Fintype.prod_unique, zpow_one]; rfl
    have e : jFK (R := V) (FractionRing V) ≫ ptK (D.c 0) = (TF (R := V) (FractionRing V)).hom ≫ eSec D.P.A := by
      rw [GlobalTheory.Poinc.ThetaOne.c_zero]
      rfl
    simp only [e] at a₁
    rw [GlobalTheory.UT.CoefBasic.cst_eq, hc]
    show (Geo.Tor.val (D.psi 0) (jFK (R := V) (FractionRing V)) z J).val * _ = _
    rw [a₁, a₂, ← Units.val_mul, ← Units.val_mul]
    congr 1
    simp only [Fintype.prod_unique, Finset.prod_const, Finset.card_univ, Fintype.card_unique, pow_one, zpow_neg,
      zpow_one, id]
    rw [_root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul]

end GlobalTheory.Poinc.IntTerm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiZeroMulRigidificationConstantNeZeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_zero_mul_rigidification_constant_ne_zero : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), ∃ c₀ : FractionRing V, c₀ ≠ 0 ∧ ∀ (z : (TF (R := V) (FractionRing V)).left) (J : ((TF (R := V) (FractionRing V)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi 0) (jFK (R := V) (FractionRing V)) z J)).val * (rigV D (TF (R := V) (FractionRing V)).hom z J).val = GlobalTheory.UT.cst (FractionRing V) z c₀ := by
  first | exact @GlobalTheory.Poinc.IntTerm.psi_zero_rig_const | exact GlobalTheory.Poinc.IntTerm.psi_zero_rig_const | (intros; apply GlobalTheory.Poinc.IntTerm.psi_zero_rig_const <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeOneFamilyTermEqPsiThetaValueCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeOneFamilyTermEqPsiThetaValueCharacter
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Poinc.IntTerm


open GlobalTheory.Poinc.ThetaOne in
theorem coef_eq_theta_value : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (θ : D.SecB 1 0), IntTerm.IsTheta D θ → ∀ s : Fam D (FractionRing V) 1, ∃ κ₀ : FractionRing V, ∀ (g' : GtPtF D (FractionRing V)) (w : Frm D (FractionRing V) 1 g'.b), w.IsGen → ∀ (mu : D.X) (z : (TF (R := V) (FractionRing V)).left) (J : ((TF (R := V) (FractionRing V)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → GlobalTheory.UT.cst (FractionRing V) z (coef s g' w mu) * (rigV D (TF (R := V) (FractionRing V)).hom z J).val * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi 0) (jFK (R := V) (FractionRing V)) z J)).val = GlobalTheory.UT.cst (FractionRing V) z κ₀ * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi mu) (jFK (R := V) (FractionRing V)) z J)).val * sval θ (padd D.P.A (DegPre.cT D _ mu) g'.b).left z J * (Geo.Tor.val (g'.s mu) (𝟙 _) z J).val * (Geo.Tor.val w (𝟙 _) z J).val := by
  intro V _ _ D θ hθ s
  obtain ⟨κ₀, hκ, -⟩ := existsUnique_scalar D θ hθ (FractionRing V) s
  refine ⟨κ₀, fun g' w hw mu z J hJ => ?_⟩
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  let ρ : TF (R := V) (FractionRing V) ⟶ DegPre.BF D (FractionRing V) := lift (𝟙 _) g'.b
  have hρ₁ : ρ ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have hρ₂ : ρ ≫ DegPre.prB D (FractionRing V) = g'.b := lift_snd _ _

  have s0 : ∀ (r : (TF (R := V) (FractionRing V)).left ⟶ (DegPre.BF D (FractionRing V)).left),
      sval (s.s 0) r z J = GlobalTheory.FieldBaseChange.constVal (r ≫ GlobalTheory.FieldBaseChange.famBase D (FractionRing V)) z κ₀ *
        sval θ (r ≫ (DegPre.prB D (FractionRing V)).left) z J := by
    intro r
    have h1 : (GlobalTheory.FieldBaseChange.famProj D (FractionRing V) 1 0 s) = κ₀ • termF D (FractionRing V) 1 0 θ := hκ
    have h2 := congrArg (fun t : GlobalTheory.FieldBaseChange.FamTerm D (FractionRing V) 1 0 => sval (L := D.P.L) t r z J) h1
    refine h2.trans ?_
    rw [GlobalTheory.FieldBaseChange.sval_smul' hJ]
    congr 1
    exact GlobalTheory.FieldBaseChange.sval_pullOver _ _ _ _ hJ
  have key : ∀ x, x = 0 + 1 • mu →
      GlobalTheory.UT.cst (FractionRing V) z (coef s g' w x) * (rigV D (TF (R := V) (FractionRing V)).hom z J).val *
        (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi 0) (jFK (R := V) (FractionRing V)) z J)).val =
      GlobalTheory.UT.cst (FractionRing V) z κ₀ *
        (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi mu) (jFK (R := V) (FractionRing V)) z J)).val *
        sval θ (padd D.P.A (DegPre.cT D _ mu) g'.b).left z J * (Geo.Tor.val (g'.s x) (𝟙 _) z J).val *
        (Geo.Tor.val w (𝟙 _) z J).val := by
    rintro x rfl
    have a := GlobalTheory.UT.CoefBasic.isCoef_coef g' hw (0 + 1 • mu) s z J hJ
    rw [pow_one] at a
    obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D) (F := FractionRing V) hG 1 mu 0
    have e := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (s.fe mu 0 u hu hc) _ ρ.left z J hJ
    have v := hv u hu hc _ ρ z J hJ
    rw [GlobalTheory.UU.uVal_one D (FractionRing V) _ _ _ hJ, _root_.one_mul, hρ₁] at v
    have m := GlobalTheory.UU.val_famMult_one D (FractionRing V) (𝟙 _) hJ mu 0
    rw [Over.id_left, Category.id_comp] at m
    have m' := congrArg Units.val m
    rw [Units.val_mul] at m'
    have ps : ∀ y, y = mu → (Geo.Tor.val (D.psi y) (jFK (R := V) (FractionRing V)) z J).val =
        (Geo.Tor.val (D.psi mu) (jFK (R := V) (FractionRing V)) z J).val := by
      rintro _ rfl; rfl
    rw [ps _ (add_zero mu)] at m'
    have b₁ : ρ.left ≫ (DegPre.trF D (FractionRing V) mu).left ≫ GlobalTheory.FieldBaseChange.famBase D (FractionRing V) = 𝟙 _ := by
      rw [GlobalTheory.FieldBaseChange.trF_famBase]
      exact congrArg (fun q => q.left) hρ₁
    have b₂ : (ρ.left ≫ (DegPre.trF D (FractionRing V) mu).left) ≫ (DegPre.prB D (FractionRing V)).left =
        (padd D.P.A (DegPre.cT D _ mu) g'.b).left := by
      rw [← Over.comp_left, ← Over.comp_left, Category.assoc, DegPre.trF, lift_snd,
        GlobalTheory.IntFam.TermLift.comp_padd, hρ₂, ← Category.assoc, toUnit_unique (ρ ≫ toUnit _) (toUnit _)]
      exact congrArg (fun q => Over.Hom.left q)
        (show padd D.P.A g'.b (DegPre.cT D _ mu) = padd D.P.A (DegPre.cT D _ mu) g'.b from mul_comm _ _)
    rw [s0, Category.assoc, b₁, b₂] at e
    rw [a, e, v]
    have c₀ : GlobalTheory.FieldBaseChange.constVal (𝟙 (TF (R := V) (FractionRing V)).left) z κ₀ = GlobalTheory.UT.cst (FractionRing V) z κ₀ := rfl
    rw [c₀]
    simp only [id]
    linear_combination (GlobalTheory.UT.cst (FractionRing V) z κ₀ * sval θ (padd D.P.A (DegPre.cT D _ mu) g'.b).left z J *
      (Geo.Tor.val (g'.s (0 + 1 • mu)) (𝟙 _) z J).val * (Geo.Tor.val w (𝟙 _) z J).val) * m'
  have := key mu (by rw [zero_add, one_smul])
  exact this

end GlobalTheory.Poinc.IntTerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeOneFamilyTermEqPsiThetaValueCharacterStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degreeOneFamily_term_eq_psi_thetaValue_character : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (θ : D.SecB 1 0), IntTerm.IsTheta D θ → ∀ s : Fam D (FractionRing V) 1, ∃ κ₀ : FractionRing V, ∀ (g' : GtPtF D (FractionRing V)) (w : Frm D (FractionRing V) 1 g'.b), w.IsGen → ∀ (mu : D.X) (z : (TF (R := V) (FractionRing V)).left) (J : ((TF (R := V) (FractionRing V)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → GlobalTheory.UT.cst (FractionRing V) z (coef s g' w mu) * (rigV D (TF (R := V) (FractionRing V)).hom z J).val * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi 0) (jFK (R := V) (FractionRing V)) z J)).val = GlobalTheory.UT.cst (FractionRing V) z κ₀ * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi mu) (jFK (R := V) (FractionRing V)) z J)).val * sval θ (padd D.P.A (DegPre.cT D _ mu) g'.b).left z J * (Geo.Tor.val (g'.s mu) (𝟙 _) z J).val * (Geo.Tor.val w (𝟙 _) z J).val := by
  first | exact @GlobalTheory.Poinc.IntTerm.coef_eq_theta_value | exact GlobalTheory.Poinc.IntTerm.coef_eq_theta_value | (intros; apply GlobalTheory.Poinc.IntTerm.coef_eq_theta_value <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGeneratorOfPsiCoordinate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGeneratorOfPsiCoordinate
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.PsiIntGen

theorem gs_specMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (z : Spec (CommRingCat.of B)) (a : A) :
    gs (Spec.map (CommRingCat.ofHom f)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) =
      gs (𝟙 (Spec (CommRingCat.of B))) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (f a)) := by
  have e := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  have e' : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (f a) =
      ((Spec.map (CommRingCat.ofHom f)).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) := e
  rw [e']
  have := gs_pull (𝟙 (Spec (CommRingCat.of B))) (Spec.map (CommRingCat.ofHom f)) z ⊤ trivial
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)
  rw [Category.id_comp] at this
  exact this.symm

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (mu : D.X) (r : V), Formalism.L2.Pj.PsiCoord D mu r → ∃ gam : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c mu).left) (fun _ => -1)), gam.IsGen ∧ ∀ (z : (TF (R := V) (FractionRing V)).left) (J : ((TF (R := V) (FractionRing V)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi mu) (jFK (R := V) (FractionRing V)) z J)).val = GlobalTheory.UT.cst (FractionRing V) z (algebraMap V (FractionRing V) r) * (Geo.Tor.val gam (toUnit (TF (R := V) (FractionRing V))).left z J).val := by
  intro V _ _ D mu r hr
  obtain ⟨j, hj, h, e⟩ := hr
  obtain ⟨t, ht, vt⟩ := PsiSpread.exists_gen_of_chart D.P.isLB (K := PUnit) (fun _ => (D.c mu).left) (fun _ => -1)
    j (fun y => Set.mem_iInter.2 fun _ => hj trivial) ⊤ (fun _ => trivial) 1
  refine ⟨t, ht, fun z J hJ => ?_⟩
  have q : jFK (R := V) (FractionRing V) ≫ ptK (D.c mu) =
      (toUnit (TF (R := V) (FractionRing V))).left ≫ (D.c mu).left := (Category.assoc _ _ _).symm
  have a := gen_trans (D.psi_gen mu) (jFK (R := V) (FractionRing V)) z (j' := j) (hJ.mem _ _) (h trivial)
  have b := vt _ (toUnit (TF (R := V) (FractionRing V))).left z _ (hJ.mem _ _)
  rw [map_one, _root_.mul_one] at b
  have c : (gm (jFK (R := V) (FractionRing V)) z (LB.wchart D.P.L (K := PUnit) (fun _ => ptK (D.c mu)) j)
      ((D.psi mu).s j)).val = GlobalTheory.UT.cst (FractionRing V) z (algebraMap V (FractionRing V) r) := by
    refine (gs_unit _ _ _ (h trivial) _).symm.trans ?_
    refine (gs_res (jFK (R := V) (FractionRing V)) z h trivial ((D.psi mu).s j).val).symm.trans ?_
    refine (congrArg (gs (jFK (R := V) (FractionRing V)) z _) e.symm).trans ?_
    refine (gs_pull (jFK (R := V) (FractionRing V)) (jK V) z ⊤ trivial _).trans ?_
    refine (gs_res _ z (le_top : (⊤ : (Spec (CommRingCat.of V)).Opens) ≤ ⊤) trivial _).trans ?_
    have s : jFK (R := V) (FractionRing V) ≫ jK V = Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) := by
      rw [← Spec.map_comp]; rfl
    rw [s]
    exact gs_specMap _ z r
  have d : trF (L := D.P.L) (K := PUnit) (fun _ => ptK (D.c mu)) (fun _ => -1) (jFK (R := V) (FractionRing V)) z
      (fun _ => J (jFK (R := V) (FractionRing V) ≫ ptK (D.c mu))) j =
      trF (L := D.P.L) (K := PUnit) (fun _ => (D.c mu).left) (fun _ => -1) (toUnit (TF (R := V) (FractionRing V))).left z
      (fun _ => J ((toUnit (TF (R := V) (FractionRing V))).left ≫ (D.c mu).left)) j :=
    congrArg (fun ψ => ∏ k : PUnit.{1}, gm ψ z (D.P.L.U (J ψ) ⊓ D.P.L.U (j k)) (D.P.L.g (J ψ) (j k)) ^ (-1 : ℤ)) q
  refine (congrArg Units.val a).trans ((Units.val_mul _ _).trans ((_root_.mul_comm _ _).trans ?_))
  exact congrArg₂ (· * ·) c (congrArg Units.val (d.trans b.symm))

end GlobalTheory.Poinc.PsiIntGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGeneratorOfPsiCoordinateStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralGenerator_of_psiCoordinate : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (mu : D.X) (r : V), Formalism.L2.Pj.PsiCoord D mu r → ∃ gam : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c mu).left) (fun _ => -1)), gam.IsGen ∧ ∀ (z : (TF (R := V) (FractionRing V)).left) (J : ((TF (R := V) (FractionRing V)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi mu) (jFK (R := V) (FractionRing V)) z J)).val = GlobalTheory.UT.cst (FractionRing V) z (algebraMap V (FractionRing V) r) * (Geo.Tor.val gam (toUnit (TF (R := V) (FractionRing V))).left z J).val := by
  first | exact @GlobalTheory.Poinc.PsiIntGen.main | exact GlobalTheory.Poinc.PsiIntGen.main | (intros; apply GlobalTheory.Poinc.PsiIntGen.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseElementThetaTermIntegralPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseElementThetaTermIntegralPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section

namespace GlobalTheory.Poinc.IntTerm.IntPoint

theorem cst_toUnit (V : Type) [CommRing V] [IsDomain V] (z : (TF (R := V) (FractionRing V)).left) (a : V) :
    Geo.Tor.cst (toUnit (TF (R := V) (FractionRing V))).left z a =
      GlobalTheory.UT.cst (FractionRing V) z (algebraMap V (FractionRing V) a) := by
  have hx : (toUnit (TF (R := V) (FractionRing V))).left = jFK (R := V) (FractionRing V) ≫ jK V := by
    simpa using Over.w (toUnit (TF (R := V) (FractionRing V)))
  rw [hx]
  erw [GlobalTheory.ExpansionValueZero.cst_comp]
  erw [H1.gs_spec]
  rfl

theorem formEq_prod {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) (g : GtPt D (𝟙_ (Over (Sp V)))) (mu : D.X) :
    FormEq (fun k => (D.c mu * g.b).left ≫ D.famφB 0 k) (DegPre.famε 1)
      (Sum.elim (Sum.elim (fun _ : PUnit => (D.c mu).left) (DegPre.gtφT D (𝟙_ _) g.b mu)) ![(η[D.P.A]).left, g.b.left])
      (fun k => -(Sum.elim (Sum.elim (fun _ : PUnit => (-1 : ℤ)) DegPre.gtε) (DegPre.lineε 1)) k) := by
    have hu : toUnit (𝟙_ (Over (Sp V))) = 𝟙 _ := toUnit_unique _ _
    have c0 := ThetaOne.c_zero D
    have e2 : (toUnit D.P.A ≫ D.c 0) = toUnit D.P.A ≫ η[D.P.A] := by
      rw [c0, MonObj.comp_one, Hom.one_def]
    have e1 : (padd D.P.A (𝟙 D.P.A) (toUnit D.P.A ≫ η[D.P.A])) = 𝟙 D.P.A := by
      rw [← e2, c0, MonObj.comp_one, padd, ← Hom.mul_def, _root_.mul_one]
    have e3 : padd D.P.A (DegPre.cT D (𝟙_ _) mu) g.b = D.c mu * g.b := by
      rw [padd, ← Hom.mul_def, DegPre.cT, hu, Category.id_comp]
    have e4 : DegPre.cT D (𝟙_ _) mu = D.c mu := by rw [DegPre.cT, hu, Category.id_comp]
    have e5 : DegPre.zeroT D (𝟙_ (Over (Sp V))) = η[D.P.A] := by rw [DegPre.zeroT, hu, Category.id_comp]
    intro U _ h
    simp [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_two, DegPre.famφB, DegPre.gtφT, DegPre.famε, DegPre.gtε,
      DegPre.lineε, e1, e2, e3, e4, e5]
    have e6 : padd D.P.A (D.c mu) g.b = D.c mu * g.b := by rw [padd, ← Hom.mul_def]
    rw [e6]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (θ : D.SecB 1 0) (g : GtPt D (𝟙_ (Over (Sp V)))) (g' : GtPtF D (FractionRing V)) (w : Frm D (FractionRing V) 1 g'.b) (l : FractionRing V), GtPt.IsPullF (FractionRing V) (toUnit (TF (R := V) (FractionRing V))).left g g' → IntTerm.IntFrm D g.b w l → ∀ (mu : D.X) (gam : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c mu).left) (fun _ => -1))), gam.IsGen → ∃ a : V, (∀ (z : (TF (R := V) (FractionRing V)).left) (J : ((TF (R := V) (FractionRing V)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → GlobalTheory.UT.cst (FractionRing V) z l * (Geo.Tor.val gam (toUnit (TF (R := V) (FractionRing V))).left z J).val * sval θ (padd D.P.A (DegPre.cT D _ mu) g'.b).left z J * (Geo.Tor.val (g'.s mu) (𝟙 _) z J).val * (Geo.Tor.val w (𝟙 _) z J).val = GlobalTheory.UT.cst (FractionRing V) z (algebraMap V (FractionRing V) a)) ∧ (IntTerm.UnitAt D θ (D.c mu * g.b) → IsUnit (Geo.Tor.cst (𝟙 (Sp V)) (closedPoint V) a)) := by
  intro V _ _ _ D θ g g' w l hP hI mu gam hgam
  obtain ⟨t, ht, htv⟩ := hI
  have hL := D.P.isLB
  have hp := mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hgam (g.isGen mu)) ht
  obtain ⟨a, ha⟩ := GlobalTheory.ExpansionValueZero.exists_coeff (A := V) hL θ (D.c mu * g.b).left _ (invGen_isGen _ _ _ _ hp)
    (formEq_prod D g mu)
  refine ⟨a, fun z J hJ => ?_, fun ⟨J, hJ, hU⟩ => ?_⟩
  · have hg' : g'.b = toUnit (TF (R := V) (FractionRing V)) ≫ g.b := Over.OverMorphism.ext hP.1
    have hb : (padd D.P.A (DegPre.cT D _ mu) g'.b).left =
        (toUnit (TF (R := V) (FractionRing V))).left ≫ (D.c mu * g.b).left := by
      rw [← Over.comp_left, hg', Hom.mul_def, padd, ← Category.assoc, comp_lift]
    have hs : Geo.Tor.val (g'.s mu) (𝟙 _) z J = Geo.Tor.val (g.s mu) (toUnit (TF (R := V) (FractionRing V))).left z J :=
      (val_corr hJ (hP.2 mu) (𝟙 _)).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]))
    have e₁ := ha _ (toUnit (TF (R := V) (FractionRing V))).left z J hJ
    rw [hb, e₁, hs, cst_toUnit, val_inv, val_mul hJ, val_mul hJ]
    have h₁ := htv z J hJ
    generalize GlobalTheory.UT.cst (FractionRing V) z l = c₁ at h₁ ⊢
    generalize GlobalTheory.UT.cst (FractionRing V) z (algebraMap V (FractionRing V) a) = c₂
    generalize Geo.Tor.val w (𝟙 _) z J = u₁ at h₁ ⊢
    generalize Geo.Tor.val t (toUnit (TF (R := V) (FractionRing V))).left z J = u₂ at h₁ ⊢
    generalize Geo.Tor.val gam (toUnit (TF (R := V) (FractionRing V))).left z J = u₃
    generalize Geo.Tor.val (g.s mu) (toUnit (TF (R := V) (FractionRing V))).left z J = u₄
    calc c₁ * u₃.val * (c₂ * ((u₃ * u₄ * u₂)⁻¹).val) * u₄.val * u₁.val
        = c₂ * ((c₁ * u₁.val) * (u₃.val * u₄.val) * ((u₃ * u₄ * u₂)⁻¹).val) := by ring
      _ = c₂ := by
        rw [h₁, mul_comm u₂.val, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          _root_.mul_one]
  · have e₁ := ha (Sp V) (𝟙 _) (closedPoint V) J hJ
    rw [Category.id_comp] at e₁
    rw [e₁] at hU
    exact isUnit_of_mul_isUnit_left hU

end GlobalTheory.Poinc.IntTerm.IntPoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseElementThetaTermIntegralPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_base_element_theta_term_integralPoint : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (θ : D.SecB 1 0) (g : GtPt D (𝟙_ (Over (Sp V)))) (g' : GtPtF D (FractionRing V)) (w : Frm D (FractionRing V) 1 g'.b) (l : FractionRing V), GtPt.IsPullF (FractionRing V) (toUnit (TF (R := V) (FractionRing V))).left g g' → IntTerm.IntFrm D g.b w l → ∀ (mu : D.X) (gam : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c mu).left) (fun _ => -1))), gam.IsGen → ∃ a : V, (∀ (z : (TF (R := V) (FractionRing V)).left) (J : ((TF (R := V) (FractionRing V)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → GlobalTheory.UT.cst (FractionRing V) z l * (Geo.Tor.val gam (toUnit (TF (R := V) (FractionRing V))).left z J).val * sval θ (padd D.P.A (DegPre.cT D _ mu) g'.b).left z J * (Geo.Tor.val (g'.s mu) (𝟙 _) z J).val * (Geo.Tor.val w (𝟙 _) z J).val = GlobalTheory.UT.cst (FractionRing V) z (algebraMap V (FractionRing V) a)) ∧ (IntTerm.UnitAt D θ (D.c mu * g.b) → IsUnit (Geo.Tor.cst (𝟙 (Sp V)) (closedPoint V) a)) := by
  first | exact @GlobalTheory.Poinc.IntTerm.IntPoint.main | exact GlobalTheory.Poinc.IntTerm.IntPoint.main | (intros; apply GlobalTheory.Poinc.IntTerm.IntPoint.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitOfIsUnitConstantClosedPointLocalRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitOfIsUnitConstantClosedPointLocalRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem GlobalTheory.unit_of_isUnit_cst_closedPoint : ∀ (V : Type) [CommRing V] [IsLocalRing V] (a : V), IsUnit (Geo.Tor.cst (𝟙 (Sp V)) (closedPoint V) a) → IsUnit a := by
  intro V _ _ a h
  have e := gs_eq (𝟙 (Sp V)) (closedPoint V) ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a)
  have h' : IsUnit ((Sp V).presheaf.germ ⊤ (closedPoint V) trivial ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a)) := by
    have h2 : IsUnit (gs (𝟙 (Sp V)) (closedPoint V) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a)) := h
    rw [e] at h2
    simp only [Scheme.Hom.id_app, CommRingCat.hom_id, RingHom.id_apply] at h2
    exact h2
  have hm := (Scheme.mem_basicOpen_top (X := Sp V) ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) (closedPoint V)).mpr h'
  rw [basicOpen_eq_of_affine] at hm
  by_contra ha
  exact ((PrimeSpectrum.mem_basicOpen _ _).mp hm) ((IsLocalRing.mem_maximalIdeal a).mpr ha)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitOfIsUnitConstantClosedPointLocalRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_of_isUnit_constant_closedPoint_localRing : ∀ (V : Type) [CommRing V] [IsLocalRing V] (a : V), IsUnit (Geo.Tor.cst (𝟙 (Sp V)) (closedPoint V) a) → IsUnit a := by
  first | exact @GlobalTheory.unit_of_isUnit_cst_closedPoint | exact GlobalTheory.unit_of_isUnit_cst_closedPoint | (intros; apply GlobalTheory.unit_of_isUnit_cst_closedPoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeOneTermEqConstMulPsiMulTheta
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.IntTerm

theorem term_eq_const_psi_theta : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (θ : D.SecB 1 0), IntTerm.IsTheta D θ → ∀ s : Fam D (FractionRing V) 1, ∃ κ : FractionRing V, ∀ (g : GtPt D (𝟙_ (Over (Sp V)))) (g' : GtPtF D (FractionRing V)) (w : Frm D (FractionRing V) 1 g'.b) (l : FractionRing V), GtPt.IsPullF (FractionRing V) (toUnit (TF (R := V) (FractionRing V))).left g g' → w.IsGen → IntTerm.IntFrm D g.b w l → ∀ (mu : D.X) (r : V), Formalism.L2.Pj.PsiCoord D mu r → ∃ a : V, l * coef s g' w mu = κ * algebraMap V (FractionRing V) (r * a) ∧ (IntTerm.UnitAt D θ (D.c mu * g.b) → IsUnit a) := by
  intro V _ _ _ D θ hθ s
  obtain ⟨c₀, hc₀, hc⟩ := GlobalTheory.T.psi_zero_mul_rigidification_constant_ne_zero V D
  obtain ⟨κ₀, hκ⟩ := GlobalTheory.T.degreeOneFamily_term_eq_psi_thetaValue_character V D θ hθ s
  refine ⟨κ₀ / c₀, fun g g' w l hpull hw hint mu r hr => ?_⟩
  obtain ⟨gam, hgam, vgam⟩ := GlobalTheory.T.exists_integralGenerator_of_psiCoordinate V D mu r hr
  obtain ⟨a, ha, hu⟩ := GlobalTheory.T.exists_base_element_theta_term_integralPoint V D θ g g' w l hpull hint mu gam hgam
  refine ⟨a, ?_, fun h => GlobalTheory.T.isUnit_of_isUnit_constant_closedPoint_localRing V a (hu h)⟩
  obtain ⟨z⟩ := CoefBasic.exists_pt (R := V) (F := FractionRing V)
  obtain ⟨J, hJ⟩ := CoefBasic.exists_good' D.P.isLB z
  have e₁ := hκ g' w hw mu z J hJ
  have e₂ := hc z J hJ
  have e₃ := vgam z J hJ
  have e₄ := ha z J hJ
  rw [_root_.mul_assoc (GlobalTheory.UT.cst _ z _), mul_comm (rigV D _ z J).val, e₂, e₃] at e₁
  have e₅ : GlobalTheory.UT.cst (FractionRing V) z (l * coef s g' w mu * c₀) =
      GlobalTheory.UT.cst (FractionRing V) z (κ₀ * (algebraMap V (FractionRing V) r * algebraMap V (FractionRing V) a)) := by
    simp only [CoefBasic.cst_eq, map_mul] at e₁ e₄ ⊢
    rw [← e₄]
    linear_combination CoefBasic.cstH z l * e₁
  have e₆ := CoefBasic.cstH_inj z ((CoefBasic.cst_eq _ _).symm.trans (e₅.trans (CoefBasic.cst_eq _ _)))
  rw [map_mul]
  field_simp
  linear_combination e₆

end GlobalTheory.Poinc.IntTerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeOneTermEqConstMulPsiMulThetaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_one_term_eq_const_mul_psi_mul_theta : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (θ : D.SecB 1 0), IntTerm.IsTheta D θ → ∀ s : Fam D (FractionRing V) 1, ∃ κ : FractionRing V, ∀ (g : GtPt D (𝟙_ (Over (Sp V)))) (g' : GtPtF D (FractionRing V)) (w : Frm D (FractionRing V) 1 g'.b) (l : FractionRing V), GtPt.IsPullF (FractionRing V) (toUnit (TF (R := V) (FractionRing V))).left g g' → w.IsGen → IntTerm.IntFrm D g.b w l → ∀ (mu : D.X) (r : V), Formalism.L2.Pj.PsiCoord D mu r → ∃ a : V, l * coef s g' w mu = κ * algebraMap V (FractionRing V) (r * a) ∧ (IntTerm.UnitAt D θ (D.c mu * g.b) → IsUnit a) := by
  first | exact @GlobalTheory.Poinc.IntTerm.term_eq_const_psi_theta | exact GlobalTheory.Poinc.IntTerm.term_eq_const_psi_theta | (intros; apply GlobalTheory.Poinc.IntTerm.term_eq_const_psi_theta <;> assumption)
end
