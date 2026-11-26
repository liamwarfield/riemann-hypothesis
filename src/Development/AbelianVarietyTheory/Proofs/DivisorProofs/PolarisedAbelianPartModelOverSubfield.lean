module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionThetaSectionIntegralPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTautologicalBaseNsmulDegenerationData

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricFibreThetaConstantsRatiosMemSubfield
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedThetaConstantsEqScalarMulRoot
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGeneratorTorsionFrameValueEqScalarMulRoot
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralThetaTermsTorsionPointsFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFamilyTermZeroIntegralTorusPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFamilyTermZeroIntegralTorusPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

noncomputable section

namespace GlobalTheory.UT.CoefZeroInt

theorem coef_zero_int : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))), (∀ (R' : Type) [CommRing R'] (f : V →+* R') θ', IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' → ThetaOne.OneBasisAt D f θ') → ∀ (th : Fam D (FractionRing V) 1), ∃ lam : FractionRing V, ∀ (g : GtPtF D (FractionRing V)) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A), g.b = toUnit _ ≫ b → ∀ (w : Frm D (FractionRing V) 1 g.b) (x : FractionRing V), IsCoef 1 g w 0 (th.s 0) x → ∀ z J, Good D.P.L z J → cst (FractionRing V) z x * (rigV D (TF (R := V) (FractionRing V)).hom z J).val = cst (FractionRing V) z lam * sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) ((toUnit (TF (R := V) (FractionRing V))).left ≫ b.left) z J * (val w (𝟙 _) z J).val := by
  intro V _ _ D θ hθ th
  obtain ⟨lam, hlam, -⟩ := existsUnique_scalar D θ hθ (FractionRing V) th
  refine ⟨lam, fun g b hb w x hx z J hJ => ?_⟩
  have h1 := hx z J hJ
  rw [pow_one] at h1
  rw [h1]
  have hs : sval (th.s 0) (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left z J =
      sval (famProj D (FractionRing V) 1 0 th) (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left z J := rfl
  have hfst : (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left ≫ famBase D (FractionRing V) = 𝟙 _ := by
    show (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left ≫ (fst (TF (R := V) (FractionRing V)) D.P.A).left = _
    rw [← Over.comp_left, lift_fst]; rfl
  have hsnd : (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left ≫ (DegPre.prB D (FractionRing V)).left =
      (toUnit (TF (R := V) (FractionRing V))).left ≫ b.left := by
    show (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left ≫ (snd (TF (R := V) (FractionRing V)) D.P.A).left = _
    rw [← Over.comp_left, lift_snd, hb, Over.comp_left]
  have hv : (Geo.Tor.val (g.s 0) (𝟙 (TF (R := V) (FractionRing V)).left) z J).val = 1 := by
    rw [val_corr hJ g.s_zero, val_one]; rfl
  have e1 := sval_smul' (π := famBase D (FractionRing V)) hJ (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left lam (termF D (FractionRing V) 1 0 θ)
  have e2 := sval_pullOver (L := D.P.L) (ε := DegPre.famε 1) (prB_hom' D (FractionRing V)) (famφ_prB D (FractionRing V) 0) θ (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left hJ
  have hc : constVal (𝟙 (TF (R := V) (FractionRing V)).left) z lam = cst (FractionRing V) z lam := rfl
  rw [hs, hlam, e1, hfst]
  erw [e2]
  rw [hsnd, hv, _root_.mul_one, hc]

end GlobalTheory.UT.CoefZeroInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFamilyTermZeroIntegralTorusPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFamily_term_zero_integral_torusPoint : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))), (∀ (R' : Type) [CommRing R'] (f : V →+* R') θ', IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' → ThetaOne.OneBasisAt D f θ') → ∀ (th : Fam D (FractionRing V) 1), ∃ lam : FractionRing V, ∀ (g : GtPtF D (FractionRing V)) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A), g.b = toUnit _ ≫ b → ∀ (w : Frm D (FractionRing V) 1 g.b) (x : FractionRing V), IsCoef 1 g w 0 (th.s 0) x → ∀ z J, Good D.P.L z J → cst (FractionRing V) z x * (rigV D (TF (R := V) (FractionRing V)).hom z J).val = cst (FractionRing V) z lam * sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) ((toUnit (TF (R := V) (FractionRing V))).left ≫ b.left) z J * (val w (𝟙 _) z J).val := by
  first | exact @GlobalTheory.UT.CoefZeroInt.coef_zero_int | exact GlobalTheory.UT.CoefZeroInt.coef_zero_int | (intros; apply GlobalTheory.UT.CoefZeroInt.coef_zero_int <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTranslatedBundleIntegralPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTranslatedBundleIntegralPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

namespace GlobalTheory.GenLocal

theorem exists_gen_unit_point : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A), ∃ t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1)), t.IsGen := by
  intro V _ _ _ D b
  choose i hi using fun k : Fin 2 =>
    exists_chart D.P.isLB ((![(η[D.P.A]).left, b.left] k) (closedPoint V))
  exact AbSquare.exists_gen_of_mem_chart D.P.isLB _ _ i fun k y => by
    have : (![(η[D.P.A]).left, b.left] k) ⁻¹ᵁ D.P.L.U (i k) = ⊤ :=
      (IsLocalRing.closedPoint_mem_iff _).1 (hi k)
    exact (this.ge trivial : y ∈ (![(η[D.P.A]).left, b.left] k) ⁻¹ᵁ D.P.L.U (i k))

end GlobalTheory.GenLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTranslatedBundleIntegralPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_translatedBundle_integralPoint : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A), ∃ t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1)), t.IsGen := by
  first | exact @GlobalTheory.GenLocal.exists_gen_unit_point | exact GlobalTheory.GenLocal.exists_gen_unit_point | (intros; apply GlobalTheory.GenLocal.exists_gen_unit_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralThetaTermsTorsionPointsFrames
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

noncomputable section
namespace GlobalTheory.Poinc.Sep.FrameInt

theorem exists_rescale_gen {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (u : Γ(Y, ⊤)ˣ) :
    ∃ t' : LB.Gen (LB.LinComb L φ ε), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      val t' r z J = gm r z ⊤ u * val t r z J := by
  refine ⟨⟨fun j => t.s j * res le_top u⟩, fun i j => ?_, fun Z r z J hJ => ?_⟩
  · rw [map_mul, map_mul, ht i j, _root_.mul_assoc]
    refine congrArg (fun q => _ * (_ * q)) (unit_ext fun y hy => ?_)
    exact ((gm_res _ y _ hy _).trans (gm_res _ y le_top hy.1 _)).trans
      ((gm_res _ y _ hy _).trans (gm_res _ y le_top hy.2 _)).symm
  · exact (map_mul _ _ _).trans ((mul_comm _ _).trans (congrArg (· * _) (gm_res r z le_top (hJ.mem φ r) u)))

end GlobalTheory.Poinc.Sep.FrameInt

namespace GlobalTheory.Poinc.Sep.FrameInt

theorem gs_top_eq {V : Type} [CommRing V] [IsDomain V] (a : V) (z : (TF (R := V) (FractionRing V)).left) :
    gs (toUnit (TF (R := V) (FractionRing V))).left z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) =
      cst (FractionRing V) z (algebraMap V (FractionRing V) a) := by
  rw [toUnit_left_eq, GlobalTheory.RatioVal.gs_specMap, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  exact (GlobalTheory.RatioVal.gs_id_const z _).symm

theorem map_map_unit {V : Type} [CommRing V] (ε : Vˣ) :
    ((Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom.toMonoidHom
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom.toMonoidHom ε) : Vˣ) : V) = ε := by
  show (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ε) = ε
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

end GlobalTheory.Poinc.Sep.FrameInt


open GlobalTheory.Poinc.Sep.FrameInt in
theorem GlobalTheory.Poinc.Sep.FrameInt.integral_terms : ∀ (m : ℕ), Odd m → 3 ≤ m → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ k : ℕ, k ≠ 0 → IsUnit (k : V₁)) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D (m ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))), (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ', IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' → ThetaOne.OneBasisAt D f θ') → ∀ (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∃ (b : C → (𝟙_ (Over (Sp V₁)) ⟶ D.P.A)) (t : ∀ c, LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1))) (s₀ : V₁), (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp V₁) (p : Over.mk x ⟶ D.P.A), p ^ (m ^ 2) = 1 → ∃ c, p = toUnit _ ≫ b c) ∧ (∀ c, (t c).IsGen) ∧ (∀ c (κ : LB.Gen (kapLB D (𝟙 D.P.A ^ (m ^ 2)) ((m ^ 2) ^ 2) 1)), Normd κ → ∀ (Z : Scheme) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J → val (t c) r z J ^ ((m ^ 2) ^ 2) * val κ (r ≫ (b c).left) z J = 1) ∧ (∀ c (Z : Scheme) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J → sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b c).left) z J * (val (t c) r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom (s₀ * u 0 c)) * (val ρ₀ r z J).val) := by
  intro m hm hm3 V₁ _ _ _ hV hk D X C _ e u mo hmo hT θ hθ ρ₀ hρ₀
  haveI : IsNoetherianRing V₁ := hV.1
  haveI : IsIntegrallyClosed V₁ := hV.2.1
  have hN1 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ (by omega)
  obtain ⟨th, g, b, w, hgb, -, hcov, hw, hcoef, ⟨c₀, hc₀⟩, hbN, hfr, -⟩ :=
    thetaTerms_integral D hN1 e _ hT

  have ht : ∀ c, ∃ t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1)), t.IsGen ∧
      ∀ z J, Good D.P.L z J → val t (toUnit (TF (R := V₁) (FractionRing V₁))).left z J = val (w c) (𝟙 _) z J := by
    intro c
    obtain ⟨t', ht'⟩ := GlobalTheory.T.exists_generator_translatedBundle_integralPoint V₁ D (b c)
    obtain ⟨ε, hε⟩ := hfr c t' ht'
    obtain ⟨t, htg, htv⟩ := exists_rescale_gen D.P.L _ _ t' ht'
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom.toMonoidHom ε)
    refine ⟨t, htg, fun z J hJ => Units.ext ?_⟩
    rw [htv _ _ z J hJ, Units.val_mul, hε z J hJ, gm_top_eq, map_map_unit]
  choose t htg htv using ht

  obtain ⟨ν, hν⟩ := exists_ratio (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.P.isLB rfl ρ₀ D.rig hρ₀ D.rig_gen
  obtain ⟨lam, hlam⟩ := GlobalTheory.T.thetaFamily_term_zero_integral_torusPoint V₁ D θ hθ th
  choose f hf using fun c => GlobalTheory.T.exists_function_thetaSection_integralPoint V₁ D θ (b c) (t c) (htg c) ρ₀ hρ₀
  obtain ⟨z⟩ := exists_pt (R := V₁) (F := FractionRing V₁)
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB z
  have hTF : (TF (R := V₁) (FractionRing V₁)).hom = (toUnit (TF (R := V₁) (FractionRing V₁))).left := by
    simpa using (Over.w (toUnit (TF (R := V₁) (FractionRing V₁)))).symm
  set ν' : V₁ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of V₁)).hom.hom.toMonoidHom ν with hν'
  have key : ∀ c, algebraMap V₁ (FractionRing V₁) (u 0 c * mo 0) =
      lam * algebraMap V₁ (FractionRing V₁) (f c) * algebraMap V₁ (FractionRing V₁) ν' := by
    intro c
    have h0 := hcoef 0 c
    rw [show e 0 = 0 from map_zero e] at h0
    have a := hlam (g c) (b c) (hgb c) (w c) _ h0 z J hJ
    rw [← htv c z J hJ, _root_.mul_assoc, hf c _ _ z J hJ, gs_top_eq,
      hν _ _ z J hJ, Units.val_mul, gm_top_eq, rigV, hTF] at a
    have a' : cst (FractionRing V₁) z (algebraMap V₁ (FractionRing V₁) (u 0 c * mo 0)) *
        (val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
          (toUnit (TF (R := V₁) (FractionRing V₁))).left z J).val =
        cst (FractionRing V₁) z (lam * algebraMap V₁ (FractionRing V₁) (f c) * algebraMap V₁ (FractionRing V₁) ν') *
        (val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
          (toUnit (TF (R := V₁) (FractionRing V₁))).left z J).val := by
      rw [a, cst_eq, cst_eq, cst_eq, cst_eq, map_mul, map_mul]
      ring
    exact cst_inj z ((Units.isUnit _).mul_left_inj.1 a')

  obtain ⟨c₁, hc₁⟩ := (hmo 0).2
  have hinj := IsFractionRing.injective V₁ (FractionRing V₁)
  have hlam0 : lam ≠ 0 := by
    intro h
    have := key c₀
    rw [h, zero_mul, zero_mul] at this
    have h1 : u 0 c₀ * mo 0 = 1 := hc₀
    rw [h1, map_one] at this
    exact one_ne_zero this
  have hν0 : algebraMap V₁ (FractionRing V₁) (ν' : V₁) ≠ 0 :=
    (IsUnit.map (algebraMap V₁ (FractionRing V₁)) ν'.isUnit).ne_zero
  have cross : ∀ c, f c * u 0 c₁ = f c₁ * u 0 c := by
    intro c
    apply hinj
    have k1 := key c
    have k2 := key c₁
    have : lam * algebraMap V₁ (FractionRing V₁) ν' *
        algebraMap V₁ (FractionRing V₁) (f c * u 0 c₁) =
        lam * algebraMap V₁ (FractionRing V₁) ν' * algebraMap V₁ (FractionRing V₁) (f c₁ * u 0 c) := by
      rw [map_mul, map_mul]
      have e1 : lam * algebraMap V₁ (FractionRing V₁) (f c) * algebraMap V₁ (FractionRing V₁) ν' *
          algebraMap V₁ (FractionRing V₁) (u 0 c₁) = algebraMap V₁ (FractionRing V₁) (u 0 c * mo 0) *
          algebraMap V₁ (FractionRing V₁) (u 0 c₁) := by rw [k1]
      have e2 : lam * algebraMap V₁ (FractionRing V₁) (f c₁) * algebraMap V₁ (FractionRing V₁) ν' *
          algebraMap V₁ (FractionRing V₁) (u 0 c) = algebraMap V₁ (FractionRing V₁) (u 0 c₁ * mo 0) *
          algebraMap V₁ (FractionRing V₁) (u 0 c) := by rw [k2]
      simp only [map_mul] at e1 e2
      linear_combination e1 - e2
    exact mul_left_cancel₀ (mul_ne_zero hlam0 hν0) this
  refine ⟨b, t, f c₁ * ↑(hc₁.unit⁻¹), hcov, htg, ?_, ?_⟩
  · intro c κ hκ Z r z' J' hJ'
    refine GlobalTheory.T.integralFrame_identity_of_genericPoint V₁ D (m ^ 2) (b c) (hbN c) (t c) (htg c) κ hκ (fun y I hI => ?_) Z r z' J' hJ'
    rw [htv c y I hI]
    have := (hw c).2 κ hκ y I hI
    rwa [show (g c).b.left = (toUnit (TF (R := V₁) (FractionRing V₁))).left ≫ (b c).left from
      congrArg (fun q => q.left) (hgb c)] at this
  · intro c Z r z' J' hJ'
    have hs : f c = f c₁ * ↑(hc₁.unit⁻¹) * u 0 c := by
      rw [mul_right_comm, ← cross c, _root_.mul_assoc, IsUnit.mul_val_inv, _root_.mul_one]
    rw [hf c Z r z' J' hJ', hs]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralThetaTermsTorsionPointsFramesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_thetaTerms_torsionPoints_frames : ∀ (m : ℕ), Odd m → 3 ≤ m → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ k : ℕ, k ≠ 0 → IsUnit (k : V₁)) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D (m ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))), (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ', IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' → ThetaOne.OneBasisAt D f θ') → ∀ (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∃ (b : C → (𝟙_ (Over (Sp V₁)) ⟶ D.P.A)) (t : ∀ c, LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1))) (s₀ : V₁), (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp V₁) (p : Over.mk x ⟶ D.P.A), p ^ (m ^ 2) = 1 → ∃ c, p = toUnit _ ≫ b c) ∧ (∀ c, (t c).IsGen) ∧ (∀ c (κ : LB.Gen (kapLB D (𝟙 D.P.A ^ (m ^ 2)) ((m ^ 2) ^ 2) 1)), Normd κ → ∀ (Z : Scheme) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J → val (t c) r z J ^ ((m ^ 2) ^ 2) * val κ (r ≫ (b c).left) z J = 1) ∧ (∀ c (Z : Scheme) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J → sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b c).left) z J * (val (t c) r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom (s₀ * u 0 c)) * (val ρ₀ r z J).val) := by
  first | exact @GlobalTheory.Poinc.Sep.FrameInt.integral_terms | exact GlobalTheory.Poinc.Sep.FrameInt.integral_terms | (intros; apply GlobalTheory.Poinc.Sep.FrameInt.integral_terms <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFrameMulIntegralFrameEqRootMulRig
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFrameMulIntegralFrameEqRootMulRig
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT

namespace GlobalTheory.USep.FrameRoot

theorem exists_normd {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) (ρ : LB.Gen (D.P.L.pull (eSec D.P.A)))
    (hρ : ρ.IsGen) (n : ℕ)
    (α : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![𝟙 D.P.A.left, (mulA D.P.A n).left] ![(n : ℤ) ^ 2, -1]))
    (hα : α.IsGen) (hn : IsNormMul D.P.A D.P.L ρ n α) :
    ∃ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ n) (n ^ 2) 1), Normd κ ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
        val κ r z J = val α r z J * val ρ (r ≫ D.P.A.hom) z J * (val ρ (r ≫ D.P.A.hom) z J ^ (n ^ 2))⁻¹ := by
  have hL := D.P.isLB
  let p := LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) ρ D.P.A.hom
  have hp : p.IsGen := DVR.pullGen_isGen _ _ _ _ hρ _
  let u := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ α p) (LB.invGen D.P.L _ _ (GeneratorPullback.powGen D.P.L _ _ p (n ^ 2)))
  have hu : u.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hα hp)
    (DVR.invGen_isGen _ _ _ _ (DVR.SectionScalarValuation.powGen_isGen' _ _ _ _ hp _))
  have h1 : (1 : D.P.A ⟶ D.P.A).left = D.P.A.hom ≫ eSec D.P.A := rfl
  obtain ⟨κ, hκ, hv⟩ := exists_gen hL
    (φ' := (![𝟙 _, (𝟙 D.P.A ^ n).left, (1 : D.P.A ⟶ D.P.A).left] : Fin 3 → (D.P.A.left ⟶ D.P.A.left)))
    (ε' := ![((n ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ), ((1 : ℕ) : ℤ) - ((n ^ 2 : ℕ) : ℤ)]) (by
      intro U _ h
      rw [h1]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, Fintype.prod_sum_type, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module) u hu
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
      val κ r z J = val α r z J * val ρ (r ≫ D.P.A.hom) z J * (val ρ (r ≫ D.P.A.hom) z J ^ (n ^ 2))⁻¹ :=
    fun Z r z J hJ => by
      have a : val p r z J = val ρ (r ≫ D.P.A.hom) z J := val_pull hJ _ _ _
      refine (hv Z r z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg _ a)) ((val_inv _ _).trans (congrArg (·⁻¹) ?_))))
      exact (GlobalTheory.RatioVal.val_powGen _ _ _ _ _).trans (congrArg (· ^ (n ^ 2)) a)
  refine ⟨κ, ⟨hκ, corr_of_val hL fun y J hJ => ?_⟩, key⟩
  have a₃ : val (rigPow D.P.A D.P.L ρ ((n : ℤ) ^ 2)) (𝟙 _) y J = val ρ (𝟙 _) y J ^ ((n : ℤ) ^ 2) := map_zpow _ _ _
  have e₁ : (𝟙 _ ≫ eSec D.P.A) ≫ D.P.A.hom = 𝟙 _ := by
    rw [Category.id_comp]; exact Over.w η[D.P.A]
  have b := (val_pull hJ α (eSec D.P.A) (𝟙 _)).symm.trans ((val_corr hJ hn (𝟙 _)).trans ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) a₃ (val_inv ρ (𝟙 _)))))
  refine (val_pull hJ κ _ _).trans ((key _ _ y J hJ).trans (Eq.trans ?_ (val_one _).symm))
  rw [b]
  refine (congrArg (fun q => val ρ (𝟙 _) y J ^ ((n : ℤ) ^ 2) * (val ρ (𝟙 _) y J)⁻¹ * val ρ q y J *
    (val ρ q y J ^ (n ^ 2))⁻¹) e₁).trans ?_
  rw [← Nat.cast_pow, zpow_natCast, inv_mul_cancel_right, mul_inv_cancel]

theorem val_rigT {S : Scheme.{0}} (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))) (T : Over S) (k : ℤ) {Z : Scheme.{0}}
    (r : Z ⟶ T.left) {z : Z} {J : (Z ⟶ P.A.left) → P.L.ι} (hJ : Good P.L z J) :
    val (rigT P.A P.L rig T k) r z J = val rig (r ≫ T.hom) z J ^ k := by
  rw [val_of rig (r ≫ T.hom) z J (fun _ => J (r ≫ T.hom ≫ eSec P.A))
    (fun _ => by rw [Category.assoc])]
  have hm := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec P.A) r
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ?_)
  exact (gm_res r z _ hm _).trans (gm_pull r T.hom z
    (LB.wchart P.L (fun _ : PUnit => eSec P.A) (fun _ => J (r ≫ T.hom ≫ eSec P.A)))
    (Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hm 0) _)

theorem exists_root {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) (T : Over (Sp V))
    (ρ : LB.Gen (D.P.L.pull (eSec D.P.A))) (hρ : ρ.IsGen) (n : ℕ) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A)
    (τ : LB.Gen (LB.LinComb D.P.L (Y := T.left) (K := Fin 1) (fun _ => (toUnit T ≫ b).left) (fun _ => 1)))
    (hτ : IsTorsFrame D.P ρ n (toUnit T ≫ b) τ)
    (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))) (ht : t.IsGen)
    (H : ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ n) (n ^ 2) 1), Normd κ → ∀ (z : T.left) J, Good D.P.L z J →
      val t T.hom z J ^ (n ^ 2) * val κ (T.hom ≫ b.left) z J = 1) :
    ∃ c : Γ(T.left, ⊤)ˣ, c ^ (n ^ 2) = 1 ∧ ∀ (z : T.left) J, Good D.P.L z J →
      val τ (𝟙 _) z J * val t T.hom z J = gm (𝟙 T.left) z ⊤ c * val ρ T.hom z J := by
  have hL := D.P.isLB
  obtain ⟨-, hτg, α, hα, hn, hc⟩ := hτ
  obtain ⟨κ, hκ, hv⟩ := exists_normd D ρ hρ n α hα hn
  have hx : (toUnit T ≫ b).left = T.hom ≫ b.left := rfl
  let p := LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) ρ T.hom
  have hp : p.IsGen := DVR.pullGen_isGen _ _ _ _ hρ _
  let q := LB.pullGen D.P.L _ _ t T.hom
  have hq : q.IsGen := DVR.pullGen_isGen _ _ _ _ ht _
  obtain ⟨u, hu, hw⟩ := exists_gen hL (φ' := fun _ : PUnit => T.hom ≫ eSec D.P.A) (ε' := fun _ => 1) (by
      intro U _ h
      rw [hx]
      simp [Fin.prod_univ_succ, Fintype.prod_sum_type, DegPre.lineε, eSec, mul_comm, mul_left_comm])
    (LB.mulGen D.P.L _ _ _ _ τ q) (DVR.mulGen_isGen _ _ _ _ _ _ _ hτg hq)
  obtain ⟨c, hcv⟩ := GlobalTheory.CoordSep.exists_ratio_base hL (𝟙 T.left) (𝟙 T.left) (Category.comp_id _)
    (fun a => ⟨a, rfl⟩) hu hp
  have key : ∀ (z : T.left) J, Good D.P.L z J →
      val τ (𝟙 _) z J * val t T.hom z J = gm (𝟙 T.left) z ⊤ c * val ρ T.hom z J := fun z J hJ => by
    have a : val p (𝟙 _) z J = val ρ T.hom z J := (val_pull hJ _ _ _).trans (by rw [Category.id_comp])
    have a' : val q (𝟙 _) z J = val t T.hom z J := (val_pull hJ _ _ _).trans (by rw [Category.id_comp])
    have e := hcv _ (𝟙 _) z J hJ
    rw [hw _ _ z J hJ, val_mul hJ, a, a', Category.id_comp, mul_comm (val ρ T.hom z J)] at e
    exact e
  refine ⟨c, unit_ext fun z _ => ?_, key⟩
  choose J hJ using fun χ : T.left ⟶ D.P.A.left => exists_chart hL (χ z)
  replace hJ : Good D.P.L z J := hJ
  have e₁ : (T.hom ≫ b.left) ≫ D.P.A.hom = T.hom := Over.w (toUnit T ≫ b)
  have h₁ := H κ hκ z J hJ
  rw [hv _ _ z J hJ, e₁] at h₁
  have a₃ : val (powFrame D.P.A D.P.L _ τ ((n : ℤ) ^ 2)) (𝟙 _) z J = val τ (𝟙 _) z J ^ ((n : ℤ) ^ 2) := map_zpow _ _ _
  have h₂ := a₃.symm.trans ((val_corr hJ hc (𝟙 _)).trans ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (val_pull hJ α _ _) (val_rigT D.P ρ T 1 _ hJ))))
  replace h₂ : val τ (𝟙 _) z J ^ (n ^ 2) = val α (T.hom ≫ b.left) z J * val ρ T.hom z J := by
    rw [← zpow_natCast, Nat.cast_pow, h₂, zpow_one, Category.id_comp, Category.id_comp, hx]
  have h₃ := congrArg (· ^ (n ^ 2)) (key z J hJ)
  simp only [mul_pow] at h₃
  rw [map_pow, map_one]
  have aux : ∀ {U : Type} [CommGroup U] (a s g r r' w : U), s * (w * r' * r⁻¹) = 1 → a = w * r' → a * s = g * r →
      g = 1 := by
    rintro U _ a s g r r' w h rfl h'
    rw [← h, ← _root_.mul_assoc, mul_comm s, h', mul_inv_cancel_right]
  exact aux _ _ _ _ _ _ h₁ h₂ h₃

theorem frame_mul_eq_root : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (K : Type) [Field K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∀ (n : ℕ), 1 ≤ n → ∀ (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A) (τ : LB.Gen (LB.LinComb D.P.L (Y := (Over.mk (spMap ev)).left) (K := Fin 1) (fun _ => (toUnit (Over.mk (spMap ev)) ≫ b).left) (fun _ => 1))), IsTorsFrame D.P ρ₀ n (toUnit (Over.mk (spMap ev)) ≫ b) τ → ∀ (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))), t.IsGen → (∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ n) (n ^ 2) 1), Normd κ → ∀ (z : (Over.mk (spMap ev)).left) J, Good D.P.L z J → val t (Over.mk (spMap ev)).hom z J ^ (n ^ 2) * val κ ((Over.mk (spMap ev)).hom ≫ b.left) z J = 1) → ∃ ζ : K, ζ ^ (n ^ 2) = 1 ∧ ∀ (z : (Over.mk (spMap ev)).left) J, Good D.P.L z J → (val τ (𝟙 _) z J).val * (val t (Over.mk (spMap ev)).hom z J).val = gs (𝟙 (Over.mk (spMap ev)).left) z ⊤ (GlobalTheory.Ex.fnOf ζ) * (val ρ₀ (Over.mk (spMap ev)).hom z J).val := by
  intro V₁ _ _ D K _ ev ρ₀ hρ n _ b τ hτ t ht H
  obtain ⟨c, hc, hv⟩ := exists_root D (Over.mk (spMap ev)) ρ₀ hρ n b τ hτ t ht H
  let e : Γ((Over.mk (spMap ev)).left, ⊤) ≃+* K := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have he : ∀ a : K, GlobalTheory.Ex.fnOf a = e.symm a := fun _ => rfl
  refine ⟨e c.val, ?_, fun z J hJ => ?_⟩
  · rw [← map_pow, ← Units.val_pow_eq_pow_val, hc, Units.val_one, map_one]
  · rw [he, e.symm_apply_apply, gs_unit _ _ ⊤ trivial, ← Units.val_mul, ← Units.val_mul]
    exact congrArg Units.val (hv z J hJ)

end GlobalTheory.USep.FrameRoot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFrameMulIntegralFrameEqRootMulRigStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionFrame_mul_integralFrame_eq_root_mul_rig : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (K : Type) [Field K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∀ (n : ℕ), 1 ≤ n → ∀ (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A) (τ : LB.Gen (LB.LinComb D.P.L (Y := (Over.mk (spMap ev)).left) (K := Fin 1) (fun _ => (toUnit (Over.mk (spMap ev)) ≫ b).left) (fun _ => 1))), IsTorsFrame D.P ρ₀ n (toUnit (Over.mk (spMap ev)) ≫ b) τ → ∀ (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))), t.IsGen → (∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ n) (n ^ 2) 1), Normd κ → ∀ (z : (Over.mk (spMap ev)).left) J, Good D.P.L z J → val t (Over.mk (spMap ev)).hom z J ^ (n ^ 2) * val κ ((Over.mk (spMap ev)).hom ≫ b.left) z J = 1) → ∃ ζ : K, ζ ^ (n ^ 2) = 1 ∧ ∀ (z : (Over.mk (spMap ev)).left) J, Good D.P.L z J → (val τ (𝟙 _) z J).val * (val t (Over.mk (spMap ev)).hom z J).val = gs (𝟙 (Over.mk (spMap ev)).left) z ⊤ (GlobalTheory.Ex.fnOf ζ) * (val ρ₀ (Over.mk (spMap ev)).hom z J).val := by
  first | exact @GlobalTheory.USep.FrameRoot.frame_mul_eq_root | exact GlobalTheory.USep.FrameRoot.frame_mul_eq_root | (intros; apply GlobalTheory.USep.FrameRoot.frame_mul_eq_root <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFibreSectionEqScalarMulIntegralTheta
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFibreSectionEqScalarMulIntegralTheta
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT

noncomputable section

namespace GlobalTheory.ThetaFibreScalar

theorem famφB_zero {V₁ : Type} [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) :
    D.famφB 0 = ![𝟙 _, 𝟙 _, (toUnit D.P.A ≫ η[D.P.A]).left, (toUnit D.P.A ≫ η[D.P.A]).left] := by
  have h0 := GlobalTheory.Mum.degPre_c_zero D
  have e1 : toUnit D.P.A ≫ D.c 0 = toUnit D.P.A ≫ η[D.P.A] := by
    rw [h0, comp_one, Hom.one_def]
  have e2 : padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c 0) = 𝟙 D.P.A := by
    rw [h0, comp_one, padd, ← Hom.mul_def, _root_.mul_one]
  have e2' : padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ η[D.P.A]) = 𝟙 D.P.A := by rw [← e1]; exact e2
  funext i
  fin_cases i <;> simp [DegPre.famφB, e1, e2']

theorem thetaFibre_scalar : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))), (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ', IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' → ThetaOne.OneBasisAt D f θ') → ∀ (K : Type) [Field K] (ev : V₁ →+* K) (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))), ∃ Λ : K, ∀ (Z : Scheme) (r : Z ⟶ (Over.mk (spMap ev) ⊗ D.P.A).left) (z : Z) J, Good D.P.L z J → sval th r z J = gs (r ≫ (fst (Over.mk (spMap ev)) D.P.A).left) z ⊤ (GlobalTheory.Ex.fnOf Λ) * sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (snd (Over.mk (spMap ev)) D.P.A).left) z J := by
  intro V₁ _ _ D θ hθ K _ ev th
  have hF : FormEq (fun _ : Fin 1 => (snd (Over.mk (spMap ev)) D.P.A).left) (fun _ => ((1 : ℕ) : ℤ))
      (fun i => (snd (Over.mk (spMap ev)) D.P.A).left ≫ D.famφB 0 i) (DegPre.famε 1) := by
    intro U _ h
    rw [famφB_zero]
    simp [Fin.prod_univ_four, DegPre.famε]
  obtain ⟨th', hth'⟩ := exists_sec D.P.isLB hF th
  obtain ⟨r, hr, -⟩ := hθ K ev (pullTo D ev θ) (isPullSecLC_pullTo D ev θ) th'
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (r 0), fun Z rr z J hJ => ?_⟩
  refine (hth' Z rr z J hJ).symm.trans ?_
  have hm := hJ.mem (fun i => (snd (Over.mk (spMap ev)) D.P.A).left ≫ D.famφB 0 i) rr
  have h2 := sval_of (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (rr ≫ (snd (Over.mk (spMap ev)) D.P.A).left) z J
      (fun k => J (rr ≫ (snd (Over.mk (spMap ev)) D.P.A).left ≫ D.famφB 0 k)) (fun k => by rw [Category.assoc])
  erw [h2]
  rw [sval]
  erw [hr]
  rw [Fin.sum_univ_one]
  erw [gs_mul _ _ _ hm]
  congr 1
  · erw [gs_res rr z le_top hm]
    have := gs_pull rr (fst (Over.mk (spMap ev)) D.P.A).left z ⊤ trivial (r 0)
    refine this.trans ?_
    congr 1
    simp [GlobalTheory.Ex.fnOf]
  · have hle := wchart_comp_le D.P.L (D.famφB 0) (snd (Over.mk (spMap ev)) D.P.A).left
      (fun k => J (rr ≫ (snd (Over.mk (spMap ev)) D.P.A).left ≫ D.famφB 0 k))
    erw [isPullSecLC_pullTo D ev θ, gs_res rr z hle hm]
    exact gs_pull rr (snd (Over.mk (spMap ev)) D.P.A).left z
      (LB.wchart D.P.L (D.famφB 0) (fun k => J (rr ≫ (snd (Over.mk (spMap ev)) D.P.A).left ≫ D.famφB 0 k))) (hle hm)
      (θ.f (fun k => J (rr ≫ (snd (Over.mk (spMap ev)) D.P.A).left ≫ D.famφB 0 k)))

end GlobalTheory.ThetaFibreScalar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFibreSectionEqScalarMulIntegralThetaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFibre_section_eq_scalar_mul_integralTheta : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))), (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ', IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' → ThetaOne.OneBasisAt D f θ') → ∀ (K : Type) [Field K] (ev : V₁ →+* K) (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))), ∃ Λ : K, ∀ (Z : Scheme) (r : Z ⟶ (Over.mk (spMap ev) ⊗ D.P.A).left) (z : Z) J, Good D.P.L z J → sval th r z J = gs (r ≫ (fst (Over.mk (spMap ev)) D.P.A).left) z ⊤ (GlobalTheory.Ex.fnOf Λ) * sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (snd (Over.mk (spMap ev)) D.P.A).left) z J := by
  first | exact @GlobalTheory.ThetaFibreScalar.thetaFibre_scalar | exact GlobalTheory.ThetaFibreScalar.thetaFibre_scalar | (intros; apply GlobalTheory.ThetaFibreScalar.thetaFibre_scalar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGeneratorTorsionFrameValueEqScalarMulRoot
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT

noncomputable section

namespace GlobalTheory.USep.FrameInt

theorem frameValue_eq_lam_root_mul : ∀ (m : ℕ), Odd m → 3 ≤ m → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ k : ℕ, k ≠ 0 → IsUnit (k : V₁)) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D (m ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∀ (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))), IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th → ∃ (M : ℕ) (lam : K), 1 ≤ M ∧ ∀ (x : Over.mk (spMap ev) ⟶ D.P.A) (τ : LB.Gen (LB.LinComb D.P.L (Y := (Over.mk (spMap ev)).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))) (c : K), IsTorsFrame D.P ρ₀ (m ^ 2) x τ → IsValueAt D.P.A D.P.L ((1 : ℕ) : ℤ) th x (powFrame D.P.A D.P.L x τ ((1 : ℕ) : ℤ)) (GlobalTheory.Ex.fnOf c) → ∃ (c₀ : C) (ζ : K), ζ ^ M = 1 ∧ c = lam * ζ * ev (u 0 c₀) := by
  intro m hm hm3 V₁ _ _ _ hV hunit D X C _ e u mo hmo hT K _ _ ev ρ₀ hρ₀ th hth
  obtain ⟨θ, hθ, -⟩ := ThetaOne.main hV D
  obtain ⟨b, t, s₀, hcov, htg, hκ, hid⟩ := GlobalTheory.T.integral_thetaTerms_torsionPoints_frames m hm hm3 V₁ hV hunit D X C e u mo hmo hT θ hθ ρ₀ hρ₀
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.T.thetaFibre_section_eq_scalar_mul_integralTheta V₁ D θ hθ K ev th
  refine ⟨(m ^ 2) ^ 2, Λ * ev s₀, Nat.one_le_pow _ _ (by positivity), ?_⟩
  intro x τ c hτ hval
  obtain ⟨c₀, rfl⟩ := hcov K (spMap ev) x hτ.1
  obtain ⟨ζ, hζ, hζv⟩ := GlobalTheory.T.torsionFrame_mul_integralFrame_eq_root_mul_rig V₁ D K ev ρ₀ hρ₀ (m ^ 2) (Nat.one_le_pow _ _ (by omega)) (b c₀) τ hτ (t c₀) (htg c₀)
    (fun κ hκn z J hJ => hκ c₀ κ hκn _ _ z J hJ)
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by positivity)] at hζ
    exact zero_ne_one hζ
  refine ⟨c₀, ζ⁻¹, by rw [inv_pow, hζ, inv_one], ?_⟩
  let z : (Over.mk (spMap ev)).left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  choose J hJ using fun χ : (Over.mk (spMap ev)).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
  have hG : Good D.P.L z J := hJ
  have h1 := GlobalTheory.CoordSep.sv_value hval hG
  have h2 := hΛ _ (lift (𝟙 _) (toUnit _ ≫ b c₀)).left z J hG
  have h3 := hid c₀ _ (Over.mk (spMap ev)).hom z J hG
  have h4 := hζv z J hG
  have eT : (toUnit (Over.mk (spMap ev))).left = (Over.mk (spMap ev)).hom := by
    simpa using Over.w (toUnit (Over.mk (spMap ev)))
  have e1 : (lift (𝟙 (Over.mk (spMap ev))) (toUnit _ ≫ b c₀)).left ≫ (fst (Over.mk (spMap ev)) D.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]; rfl
  have e2 : (lift (𝟙 (Over.mk (spMap ev))) (toUnit _ ≫ b c₀)).left ≫ (snd (Over.mk (spMap ev)) D.P.A).left =
      (Over.mk (spMap ev)).hom ≫ (b c₀).left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left, eT]
  rw [e1, e2] at h2
  rw [GlobalTheory.UT.NonVan.val_powFrame] at h1
  have e11 : val τ (𝟙 (Over.mk (spMap ev)).left) z J ^ (((1 : ℕ) : ℤ)) = val τ (𝟙 (Over.mk (spMap ev)).left) z J := zpow_one _
  rw [e11] at h1
  dsimp only [GlobalTheory.VVRank.sv] at h1
  let G : K →+* (Over.mk (spMap ev)).left.presheaf.stalk z := RatioVal.germConst K z
  have g1 : ∀ a : K, gs (𝟙 (Over.mk (spMap ev)).left) z ⊤ (GlobalTheory.Ex.fnOf a) = G a := fun a => RatioVal.gs_id_const z a
  have g2 : ∀ a : V₁, gs (Over.mk (spMap ev)).hom z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom a) = G (ev a) :=
    fun a => (RatioVal.gs_specMap ev z _).trans (congrArg (fun y => G (ev y))
      (by rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]))
  have g3 : gs (𝟙 (Over.mk (spMap ev)).left) z ⊤ (GlobalTheory.Ex.fnOf Λ) = G Λ := g1 Λ
  rw [g1] at h1 h4
  rw [g3] at h2
  rw [g2] at h3
  have key : G (c * ζ) * ↑(val ρ₀ (Over.mk (spMap ev)).hom z J) =
      G (Λ * ev (s₀ * u 0 c₀)) * ↑(val ρ₀ (Over.mk (spMap ev)).hom z J) := by
    rw [map_mul, map_mul, _root_.mul_assoc, ← h4, ← _root_.mul_assoc, ← h1, h2, _root_.mul_assoc, h3, _root_.mul_assoc]
  have key2 := (Units.mul_left_inj _).1 key
  have key3 : c * ζ = Λ * ev (s₀ * u 0 c₀) := G.injective key2
  rw [map_mul] at key3
  field_simp
  linear_combination key3

end GlobalTheory.USep.FrameInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGeneratorTorsionFrameValueEqScalarMulRootStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGenerator_torsionFrame_value_eq_scalar_mul_root : ∀ (m : ℕ), Odd m → 3 ≤ m → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ k : ℕ, k ≠ 0 → IsUnit (k : V₁)) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D (m ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∀ (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))), IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th → ∃ (M : ℕ) (lam : K), 1 ≤ M ∧ ∀ (x : Over.mk (spMap ev) ⟶ D.P.A) (τ : LB.Gen (LB.LinComb D.P.L (Y := (Over.mk (spMap ev)).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))) (c : K), IsTorsFrame D.P ρ₀ (m ^ 2) x τ → IsValueAt D.P.A D.P.L ((1 : ℕ) : ℤ) th x (powFrame D.P.A D.P.L x τ ((1 : ℕ) : ℤ)) (GlobalTheory.Ex.fnOf c) → ∃ (c₀ : C) (ζ : K), ζ ^ M = 1 ∧ c = lam * ζ * ev (u 0 c₀) := by
  first | exact @GlobalTheory.USep.FrameInt.frameValue_eq_lam_root_mul | exact GlobalTheory.USep.FrameInt.frameValue_eq_lam_root_mul | (intros; apply GlobalTheory.USep.FrameInt.frameValue_eq_lam_root_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedThetaConstantsEqScalarMulRoot
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

theorem GlobalTheory.USep.thetaConst_eq_lam_root_mul : ∀ (n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∀ (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))), IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th → ∃ (M : ℕ) (lam : K), 1 ≤ M ∧ ∀ (y : Over.mk (spMap ev) ⟶ D.P.A) (c : K), GlobalTheory.Ex.OneGen.ThG D.P.A D.P.L ρ₀ (n ^ j) th y (GlobalTheory.Ex.fnOf c) → ∃ (c₀ : C) (ζ : K), ζ ^ M = 1 ∧ c = lam * ζ * ev (u 0 c₀) := by
  intro n hn hodd
  refine ⟨1, fun j hj V₁ _ _ _ hV hunit D X C _ e u mo hmo hT K _ _ ev ρ₀ hρ₀ th hth => ?_⟩
  have hn3 : 3 ≤ n := by
    have h2 := hn.two_le
    rcases hodd with ⟨k, rfl⟩
    omega
  have hm3 : 3 ≤ n ^ j := le_trans hn3 (Nat.le_self_pow (by omega) n)
  obtain ⟨M, lam, hM, H⟩ := GlobalTheory.T.thetaGenerator_torsionFrame_value_eq_scalar_mul_root (n ^ j) (hodd.pow) hm3 V₁ hV hunit D X C e u mo hmo hT K ev ρ₀ hρ₀ th hth
  refine ⟨M, lam, hM, fun y c hc => ?_⟩
  haveI : IsNoetherianRing V₁ := hV.1
  obtain ⟨τ, hτ, hv⟩ := GlobalTheory.T.exists_torsionFrame_isValueAt_thetaConstant (Sp V₁) D.P ρ₀ hρ₀ (n ^ j) (hodd.pow) _ th y _ hc
  exact H (y ^ n ^ j) τ c (GlobalTheory.T.isTorsionFrame_sq_of_torsion _ D.P ρ₀ (n ^ j) _ (y ^ n ^ j) τ hτ) hv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedThetaConstantsEqScalarMulRootStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalised_thetaConstants_eq_scalar_mul_root : ∀ (n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∀ (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))), IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th → ∃ (M : ℕ) (lam : K), 1 ≤ M ∧ ∀ (y : Over.mk (spMap ev) ⟶ D.P.A) (c : K), GlobalTheory.Ex.OneGen.ThG D.P.A D.P.L ρ₀ (n ^ j) th y (GlobalTheory.Ex.fnOf c) → ∃ (c₀ : C) (ζ : K), ζ ^ M = 1 ∧ c = lam * ζ * ev (u 0 c₀) := by
  first | exact @GlobalTheory.USep.thetaConst_eq_lam_root_mul | exact GlobalTheory.USep.thetaConst_eq_lam_root_mul | (intros; apply GlobalTheory.USep.thetaConst_eq_lam_root_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricFibreThetaConstantsRatiosMemSubfield
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

noncomputable section

namespace GlobalTheory.Poinc.Sep.ModelRatio

theorem main : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (o : Type) [CommRing o] (J : Type) (b : ZM.TBase o ((n ^ j) ^ 2)) (s : Sp K ⟶ Sp o) (t : ZM.TObj g ((n ^ j) ^ 2) J b s) (π₁ : t.A.left ⟶ D.P.A.left), IsGrpPullback t.A D.P.A (spMap ev) π₁ → LBIso t.L (D.P.L.pull π₁) → ∀ v : ZM.Ix g ((n ^ j) ^ 2) → K, t.HasTh (𝟙 _) v → ∀ a a', v a' ≠ 0 → ∃ r ∈ k₀, v a = r * v a' := by
  intro g n hn hodd
  obtain ⟨j₀, hcore⟩ := GlobalTheory.T.normalised_thetaConstants_eq_scalar_mul_root n hn hodd
  refine ⟨j₀, fun j hj V₁ _ _ _ hV hunit D hg X C _ e u mo hmo hT K _ _ ev k₀ hk₀ hrat o _ J b s t π₁ hp hL v hv a a' hne => ?_⟩
  haveI : IsAlgClosed k₀ := hk₀
  have := t.ab.comm
  obtain ⟨ρ₀, hρ₀⟩ := D.P.rigid
  obtain ⟨w, hw⟩ := hL
  obtain ⟨ρ, hρ, hr⟩ := GlobalTheory.Ex.OneGen.exists_rigidificationPullbackCompatibleIso hp hw D.P.isLB t.isLB hρ₀
  let x : ZM.Ix g ((n ^ j) ^ 2) → (baseOver (Sp K) ⟶ t.pol.A) :=
    fun a => (Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) ≫ t.lab a
  have hx : ∀ i, x i ^ ((n ^ j) ^ 2) = 1 := fun i => by
    show ((Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) ≫ t.lab i) ^ ((n ^ j) ^ 2) = 1
    rw [← MonObj.comp_pow, GlobalTheory.ThetaPtUp.lab_pow t i, MonObj.comp_one]
  obtain ⟨thP, hg, hth⟩ := GlobalTheory.T.exists_generator_thetaPoint_normalised_thetaConstants K t.pol ρ hρ (n ^ j) _ x v hx hv
  let τ : (baseOver (Sp K)).left ⟶ (Over.mk (spMap ev)).left := 𝟙 (Sp K)
  haveI : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp K)))
  have hτ : τ ≫ (Over.mk (spMap ev)).hom = (baseOver (Sp K)).hom ≫ spMap ev := rfl
  have hi : inv τ = 𝟙 (Sp K) := IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)
  obtain ⟨th, hrel⟩ := GlobalTheory.ThetaPtMove.exists_secRel_up hp τ hτ hw D.P.isLB t.isLB thP
  have hgen := GlobalTheory.ThetaPtUp.isGenSec_up hp τ hτ hw D.P.isLB t.isLB hrel hg
  obtain ⟨M, lam, hM, hval⟩ := hcore j hj V₁ hV hunit D X C e u mo hmo hT K ev ρ₀ hρ₀ th hgen
  have up : ∀ i, ∃ c₀ : C, ∃ ζ : K, ζ ^ M = 1 ∧ v i = lam * ζ * ev (u 0 c₀) := fun i => by
    obtain ⟨y, hy, hy'⟩ := GlobalTheory.Ex.OneGen.exists_torsion_up hp τ hτ (x i) (hx i)
    have q := GlobalTheory.Ex.OneGen.ThG.up hp τ hτ hw D.P.isLB t.isLB hr hy hy' hrel (hth i)
    rw [hi] at q
    exact hval y (v i) q
  obtain ⟨c₁, hc₁⟩ := (hmo 0).2
  obtain ⟨c₀, ζ, hζ, hva⟩ := up a
  obtain ⟨c₀', ζ', hζ', hva'⟩ := up a'
  obtain ⟨s₁, hs₁, hs₁e⟩ := hrat 0 c₀ c₁ hc₁
  obtain ⟨s₂, hs₂, hs₂e⟩ := hrat 0 c₀' c₁ hc₁
  have hζk : ζ ∈ k₀ := GlobalTheory.Poinc.Sep.Frames.mem_of_pow_mem k₀ hM (by rw [hζ]; exact k₀.one_mem)
  have hζk' : ζ' ∈ k₀ := GlobalTheory.Poinc.Sep.Frames.mem_of_pow_mem k₀ hM (by rw [hζ']; exact k₀.one_mem)
  rw [hva', hs₂e] at hne
  have h₁ : ζ' * s₂ ≠ 0 := fun h => hne (by rw [show lam * ζ' * (s₂ * ev (u 0 c₁)) = lam * (ζ' * s₂) * ev (u 0 c₁) by ring, h]; ring)
  refine ⟨ζ * s₁ * (ζ' * s₂)⁻¹, k₀.mul_mem (k₀.mul_mem hζk hs₁) (k₀.inv_mem (k₀.mul_mem hζk' hs₂)), ?_⟩
  rw [hva, hva', hs₁e, hs₂e]
  have e₁ : ζ * s₁ * (ζ' * s₂)⁻¹ * (lam * ζ' * (s₂ * ev (u 0 c₁))) =
      ζ * s₁ * ((ζ' * s₂)⁻¹ * (ζ' * s₂)) * (lam * ev (u 0 c₁)) := by ring
  rw [e₁, inv_mul_cancel₀ h₁]
  ring

end GlobalTheory.Poinc.Sep.ModelRatio
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricFibreThetaConstantsRatiosMemSubfieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_fibre_thetaConstants_ratios_mem_subfield : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (o : Type) [CommRing o] (J : Type) (b : ZM.TBase o ((n ^ j) ^ 2)) (s : Sp K ⟶ Sp o) (t : ZM.TObj g ((n ^ j) ^ 2) J b s) (π₁ : t.A.left ⟶ D.P.A.left), IsGrpPullback t.A D.P.A (spMap ev) π₁ → LBIso t.L (D.P.L.pull π₁) → ∀ v : ZM.Ix g ((n ^ j) ^ 2) → K, t.HasTh (𝟙 _) v → ∀ a a', v a' ≠ 0 → ∃ r ∈ k₀, v a = r * v a' := by
  first | exact @GlobalTheory.Poinc.Sep.ModelRatio.main | exact GlobalTheory.Poinc.Sep.ModelRatio.main | (intros; apply GlobalTheory.Poinc.Sep.ModelRatio.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianPartModelOverSubfield
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.USep.DescentBaseChange

theorem unitS_subfield {K : Type} [Field K] (k₀ : Subfield K) (u : k₀ˣ) :
    ZM.unitS (spMap k₀.subtype ≫ spMap (RingHom.id k₀)) u = unitOn (Units.map k₀.subtype.toMonoidHom u) := by
  ext
  simp only [ZM.unitS, unitOn, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (k₀.subtype.comp (RingHom.id k₀)))
  exact (congrArg (fun f => f.hom (u : k₀)) this).symm

theorem tObj_of_baseChange : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K) (N : ℕ), (N : K) ≠ 0 → ∀ (J : Type) (b : ZM.TBase k₀ N), ∃ (t : ZM.TObj D.P.g N J b (spMap k₀.subtype ≫ spMap (RingHom.id k₀))) (π₁ : t.A.left ⟶ D.P.A.left), IsGrpPullback t.A D.P.A (spMap ev) π₁ ∧ LBIso t.L (D.P.L.pull π₁) := by
  intro V₁ _ _ D K _ _ ev k₀ N hN J b
  obtain ⟨L1, -⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨P, φ, hφ, hg, hm, w, hw⟩ := L1.polBaseChange _ _ (spMap ev) D.P
  have hpb : IsGrpPullback P.A D.P.A (spMap ev) φ := by
    refine ⟨hφ, fun T x y x₀ y₀ hx hy => ?_⟩
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = toBase hφ.w y), ← hm]
    rfl
  let ze : Kˣ := Units.map k₀.subtype.toMonoidHom b.ζ
  have hze : IsPrimitiveRoot ze N := IsPrimitiveRoot.coe_units_iff.1 (b.prim K k₀.subtype)
  obtain ⟨pt, hpt, hpw⟩ := GlobalTheory.EllipticLevel.exists_symplectic_system L1 P N hN ze hze
  have hu := unitS_subfield k₀ b.ζ
  have key : ∀ g', P.g = g' → ∃ (t : ZM.TObj g' N J b (spMap k₀.subtype ≫ spMap (RingHom.id k₀)))
      (π₁ : t.A.left ⟶ D.P.A.left), IsGrpPullback t.A D.P.A (spMap ev) π₁ ∧ LBIso t.L (D.P.L.pull π₁) := by
    rintro _ rfl
    exact ⟨{ A := P.A, ab := P.isAb, dim := P.smoothDim, L := P.L, isLB := P.isLB, rigid := P.rigid, sym := P.sym
             ample := P.ample, ktriv := P.ktriv, pt := pt, torsion := hpt
             bij := GlobalTheory.symplectic_system_torsion_basis L1 K P N ze pt hN hze hpt hpw
             pairing := hu ▸ hpw
             act := fun _ => 𝟙 _, hom := fun _ => inferInstance }, φ, hpb, LBIso.symm ⟨w, hw⟩⟩
  exact key _ hg

theorem tBase_of_isAlgClosed (k₀ : Type) [Field k₀] [IsAlgClosed k₀] [CharZero k₀] (N : ℕ) (hN : N ≠ 0) : Nonempty (ZM.TBase k₀ N) := by
  haveI : NeZero (N : k₀) := ⟨Nat.cast_ne_zero.2 hN⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic N k₀)
    (Polynomial.degree_cyclotomic_pos N k₀ (Nat.pos_of_ne_zero hN)).ne'
  have hp : IsPrimitiveRoot z N := (Polynomial.isRoot_cyclotomic_iff).1 hz
  exact ⟨⟨(hp.isUnit (Nat.pos_of_ne_zero hN).ne').unit, (Nat.cast_ne_zero.2 hN : (N : k₀) ≠ 0).isUnit,
    fun K _ β => hp.map_of_injective β.injective⟩⟩

theorem polarised_part_model : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∃ (B₀ : Over (Sp k₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (B' : Over (Sp K)) (_ : GrpObj B') (π₁ : B'.left ⟶ D.P.A.left) (π₀ : B'.left ⟶ B₀.left) (w : LB.Iso (D.P.L.pull π₁) (M₀.pull π₀)), IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback B' D.P.A (spMap ev) π₁ ∧ IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ ∧ w.IsGen := by
  intro g n hn hodd
  obtain ⟨L1, L2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.T.exists_theta_family_from_very_dense_points L1 L2 g Empty (fun x => x.elim) 0 n hn hodd
  obtain ⟨j₂, hj₂⟩ := GlobalTheory.T.geometric_fibre_thetaConstants_ratios_mem_subfield g n hn hodd
  refine ⟨max (max j₁ j₂) 1, ?_⟩
  intro j hj V₁ _ _ _ hCN hunit D hDg X C _ e u mo hmo hT K _ _ ev k₀ hk₀ hu
  have hj1 : j₁ ≤ j := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hj
  have hj2 : j₂ ≤ j := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hj
  have hj3 : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hK : ∀ m : ℕ, m ≠ 0 → (m : K) ≠ 0 := fun m hm => by
    rw [← map_natCast ev]; exact ((hunit m hm).map ev).ne_zero
  haveI : CharZero k₀ := charZero_of_inj_zero fun m hm => by
    by_contra h
    exact hK m h (by simpa using congrArg k₀.subtype hm)
  have hN0 : (n ^ j) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)
  obtain ⟨b⟩ := tBase_of_isAlgClosed k₀ ((n ^ j) ^ 2) hN0
  obtain ⟨t, π₁, hπ, hL⟩ := tObj_of_baseChange V₁ D K ev k₀ ((n ^ j) ^ 2) (hK _ hN0) Empty b
  subst hDg
  obtain ⟨v, hv⟩ := ZM.TObj.exists_hasTh_of_isLocalRing L1 L2 (hodd.pow) t
  have hspan := ZM.FamilyScheme.span_theta L1 L2 t n v hn.two_le (dvd_pow_self n (by omega)) hv
  obtain ⟨a', ha'⟩ : ∃ a', v a' ≠ 0 := by
    by_contra h
    push_neg at h
    have : Set.range v ⊆ {0} := by rintro _ ⟨a, rfl⟩; exact h a
    rw [Ideal.span_eq_bot.2 (fun x hx => this hx)] at hspan
    exact bot_ne_top hspan
  have hr := hj₂ j hj2 V₁ hCN hunit D rfl X C e u mo hmo hT K ev k₀ hk₀ hu k₀ Empty b _ t π₁ hπ hL v hv
  choose r hrk hr using fun a => hr a a' ha'
  let w : ZM.Ix D.P.g ((n ^ j) ^ 2) → k₀ := fun a => ⟨r a, hrk a⟩
  have hw : t.HasTh (𝟙 _) (fun a => k₀.subtype (w a)) :=
    GlobalTheory.GenericObject.hasTh_unit_mul t _ v _ (v a')⁻¹ (isUnit_iff_ne_zero.2 (inv_ne_zero ha')) (fun a => by
      show r a = (v a')⁻¹ * v a
      rw [hr a, mul_comm (r a), ← _root_.mul_assoc, inv_mul_cancel₀ ha', _root_.one_mul]) hv
  have hd : ZM.VeryDense (ZM.objPrimes b (fun x : Empty => x.elim) 0 (RingHom.id k₀) w) := by
    intro q f hq hf
    have hq0 : q = ⊥ := by
      rcases Ideal.eq_bot_or_top q with h | h
      · exact h
      · exact absurd h hq.ne_top
    subst hq0
    exact ⟨⊥, ⟨K, inferInstance, inferInstance, k₀.subtype, t, (RingHom.injective_iff_ker_eq_bot _).1 k₀.subtype_injective,
      fun x => x.elim, hw⟩, hq, le_rfl, hf⟩
  obtain ⟨t₀, -, hmap⟩ := hj₁ j hj1 k₀ b k₀ (RingHom.id k₀) w hd
  obtain ⟨φ, hφ, hφL, -, -⟩ := hmap K k₀.subtype t (fun x => x.elim) hw
  obtain ⟨w', hw'⟩ := LBIso.trans (pull_isLB D.P.isLB π₁) t.isLB (pull_isLB t₀.isLB φ) (LBIso.symm hL) hφL
  exact ⟨t₀.A, inferInstance, t₀.ab.comm, t₀.L, t.A, inferInstance, π₁, φ, w', t₀.ab, t₀.isLB, hπ, hφ, hw'⟩

end GlobalTheory.USep.DescentBaseChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianPartModelOverSubfieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedAbelianPart_model_over_subfield : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∃ (B₀ : Over (Sp k₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (B' : Over (Sp K)) (_ : GrpObj B') (π₁ : B'.left ⟶ D.P.A.left) (π₀ : B'.left ⟶ B₀.left) (w : LB.Iso (D.P.L.pull π₁) (M₀.pull π₀)), IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback B' D.P.A (spMap ev) π₁ ∧ IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ ∧ w.IsGen := by
  first | exact @GlobalTheory.USep.DescentBaseChange.polarised_part_model | exact GlobalTheory.USep.DescentBaseChange.polarised_part_model | (intros; apply GlobalTheory.USep.DescentBaseChange.polarised_part_model <;> assumption)
end
