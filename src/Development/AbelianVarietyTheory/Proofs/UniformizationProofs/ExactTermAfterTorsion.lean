module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingHenselianAndSmoothPointsLift
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceOfSection
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIntegralTensorLeftOfSmoothGrpObj

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExactTermAfterTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExactTermAfterTorsion
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.ExactTerm
open TWM TWO

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

theorem comp_generic_injective :
    Function.Injective fun q : (TO hϖ hv).left ⟶ D.toPre.P.A.left => (ιS hϖ hv).left ≫ q := fun f g h => by
  have : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  have e : f ≫ D.toPre.P.A.hom = g ≫ D.toPre.P.A.hom := by
    obtain ⟨a, ha⟩ := Spec.map_surjective (R := CommRingCat.of V) (S := CommRingCat.of (Ov v)) (f ≫ D.toPre.P.A.hom)
    obtain ⟨b, hb⟩ := Spec.map_surjective (R := CommRingCat.of V) (S := CommRingCat.of (Ov v)) (g ≫ D.toPre.P.A.hom)
    have e₁ : a ≫ CommRingCat.ofHom (algebraMap (Ov v) F) = b ≫ CommRingCat.ofHom (algebraMap (Ov v) F) :=
      Spec.map_injective (by
        rw [Spec.map_comp, Spec.map_comp, ha, hb]
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ D.toPre.P.A.hom) h).trans (Category.assoc _ _ _)))
    have e₂ : a = b := CommRingCat.hom_ext (RingHom.ext fun x => Subtype.ext
      (RingHom.congr_fun (congrArg CommRingCat.Hom.hom e₁) x))
    exact ha.symm.trans ((congrArg Spec.map e₂).trans hb)
  have hU : ValuativeCriterion.Uniqueness D.toPre.P.A.hom := IsSeparated.valuativeCriterion _
  let S : ValuativeCommSq D.toPre.P.A.hom :=
    { R := Ov v, K := F, i₁ := (ιS hϖ hv).left ≫ f, i₂ := f ≫ D.toPre.P.A.hom, commSq := ⟨Category.assoc _ _ _⟩ }
  exact congrArg CommSq.LiftStruct.l ((hU S).elim ⟨f, rfl, rfl⟩ ⟨g, h.symm, e.symm⟩)

theorem exists_unit_const {K : Type} [Fintype K] {φ : K → ((TO hϖ hv).left ⟶ D.toPre.P.A.left)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb D.toPre.P.L φ ε)) (ht : t.IsGen)
    (hf : ∀ (U : Type) [CommGroup U] (h : ((TF (R := V) F).left ⟶ D.toPre.P.A.left) → U),
      ∏ k, h ((ιS hϖ hv).left ≫ φ k) ^ ε k = 1) :
    ∃ u : F, v u = 0 ∧ ∀ z J, Good D.toPre.P.L z J → (val t (ιS hϖ hv).left z J).val = cst F z u := by
  have hI : IsIso (Scheme.Hom.appTop (𝟙 (TO hϖ hv).left)) :=
    inferInstanceAs (IsIso (Scheme.Hom.app (𝟙 (TO hϖ hv).left) ⊤))
  obtain ⟨a, ha⟩ := H1.exists_const D.toPre.P.L D.toPre.P.isLB (𝟙 _) (ConcreteCategory.bijective_of_isIso _).2 t ht
    (fun U _ h => by
      have := hf U (Function.extend (fun q => (ιS hϖ hv).left ≫ q) h 1)
      simpa only [(comp_generic_injective hϖ hv).extend_apply] using this)
  have hu : IsUnit a := (TO hϖ hv).left.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨J, hJ⟩ := CoefBasic.exists_good' D.toPre.P.isLB y
    have q := ha _ (𝟙 _) y J hJ
    rw [Category.comp_id] at q
    exact (congrArg IsUnit (q.trans (gs_eq (𝟙 _) y ⊤ trivial a))).mp (Units.isUnit _)
  refine ⟨ιr (v := v) a, v_unit v (hu.map (Scheme.ΓSpecIso (CommRingCat.of (Ov v))).hom.hom).unit, fun z J hJ => ?_⟩
  rw [ha _ _ z J hJ, Category.comp_id, ← Category.id_comp (ιS hϖ hv).left]
  exact (gs_pull (𝟙 _) (ιS hϖ hv).left z ⊤ trivial a).symm.trans (congrArg (gs (𝟙 _) z ⊤) (appTop_specMap _ a))

theorem cst_gF {Z : Scheme.{0}} (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (c : V) :
    Geo.Tor.cst ((ρ ≫ (DegPre.prB D.toPre F).left) ≫ D.toPre.P.A.hom) z c = gs ρ z ⊤ (gF D.toPre F (algVF c)) := by
  have e : (ρ ≫ (DegPre.prB D.toPre F).left) ≫ D.toPre.P.A.hom =
      (ρ ≫ (fst (TF (R := V) F) D.toPre.P.A).left) ≫ Spec.map (CommRingCat.ofHom (algVF (F := F) (V := V))) := by
    rw [← TF_hom, Category.assoc, Category.assoc, Over.w, Over.w]
  rw [e]
  refine (gs_pull _ _ z ⊤ trivial _).symm.trans (Eq.trans ?_ (gs_pull ρ _ z ⊤ trivial _).symm)
  refine congrArg (gs _ z ⊤) ((appTop_specMap _ _).trans ?_)
  simp


include hϖ hv in
theorem vge_iff {k : ℕ} {χ : D.toPre.X} (b : D.toPre.SecB k χ)
    (hb : ∀ σ : D.toPre.SecB k χ, ∃ c : V, ∀ (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J),
      Good D.toPre.P.L z J → sval σ r z J = Geo.Tor.cst (r ≫ D.toPre.P.A.hom) z c * sval b r z J)
    (s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k))) {r : ℚ} (hs : VGe D F v k χ s r) :
    ∃ a : F, (r : WithTop ℚ) ≤ v a ∧ (∀ r' : ℚ, (r' : WithTop ℚ) ≤ v a → VGe D F v k χ s r') ∧
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
        sval s ρ z J = gs ρ z ⊤ (gF D.toPre F a) * sval b (ρ ≫ (DegPre.prB D.toPre F).left) z J := by
  have hL := D.toPre.P.isLB
  obtain ⟨n, a, σ, σF, hscal, hva, hsum⟩ := hs
  choose c hc using fun i => hb (σ i)
  have key : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
      sval s ρ z J = gs ρ z ⊤ (gF D.toPre F (∑ i, a i * algVF (c i))) *
        sval b (ρ ≫ (DegPre.prB D.toPre F).left) z J := fun Z ρ z J hJ => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [SectionScalarValuation.sval_lin (fun i => gF D.toPre F (a i)) σF (fun j => hsum j) ρ z hJ, map_sum,
      SectionScalarValuation.gs_sum ρ z ⊤ trivial, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← SectionScalarValuation.secScal_sval (hscal i) ρ z hJ, hc i _ _ z J hJ, cst_gF, map_mul, gs_mul ρ z ⊤ trivial, _root_.mul_assoc]
  refine ⟨∑ i, a i * algVF (c i), AddValuation.map_le_sum v fun i _ => ?_, fun r' hr' => ?_, key⟩
  · rw [AddValuation.map_mul]
    exact le_add_of_le_of_nonneg (hva i) (v_of_V v hϖ hv (c i)).1
  · let bF : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k)) :=
      VVRank.pullTo b (DegPre.prB D.toPre F).left fun i => (GC.famφ_eq _ _ _ i).symm
    refine ⟨1, fun _ => _, fun _ => b, fun _ => bF, fun _ => SectionScalarValuation.secScal_of_sval hL fun y J hJ =>
      (VVRank.sval_pullTo _ _ _ _ y hJ).symm, fun _ => hr', fun j => ?_⟩
    rw [Fin.sum_univ_one]
    refine sec_ext_val hL (s' := SecOps.secScale (gF D.toPre F _) bF) (fun y J hJ => ?_) j
    have hm := hJ.mem (DegPre.famφ D.toPre F χ) (𝟙 _)
    exact (key _ _ y J hJ).trans ((gs_mul _ y _ hm _ _).trans (congrArg₂ (· * ·) (gs_res _ y le_top hm _)
      (VVRank.sval_pullTo _ _ _ _ y hJ))).symm

theorem v_coef {χ : D.toPre.X} (b : D.toPre.SecB 1 χ) (s : Fam D.toPre F 1) (a : F)
    (hs : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
        sval (s.s χ) ρ z J = gs ρ z ⊤ (gF D.toPre F a) * sval b (ρ ≫ (DegPre.prB D.toPre F).left) z J)
    (g : GtPtF D.toPre F) (m : TO hϖ hv ⟶ D.toPre.P.A) (hm : ιS hϖ hv ≫ m = g.b)
    (hu : ∀ z J, Good D.toPre.P.L z J → IsUnit (sval b (Spec.map (CommRingCat.ofHom (residue (Ov v))) ≫ m.left) z J))
    (w : Frm D.toPre F 1 g.b) (hw : w.IsGen) {l ω : ℚ} (hl : GenV hϖ hv (g.s χ) l) (hω : GenV hϖ hv w ω) :
    v (coef s g w χ) = v a + l + ω := by
  have hL := D.toPre.P.isLB
  obtain ⟨t₀, h₀, v₀⟩ := exists_gen_of_isUnit hL b m.left hu
  obtain ⟨φ₁, e₁, t₁, h₁, x₁, hx₁, v₁⟩ := hl
  obtain ⟨φ₂, e₂, t₂, h₂, x₂, hx₂, v₂⟩ := hω
  have hm' : (ιS hϖ hv).left ≫ m.left = g.b.left := congrArg (fun q => q.left) hm
  obtain ⟨u, hu₀, vu⟩ := exists_unit_const hϖ hv
    (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ t₀ t₁) t₂) (LB.invGen _ _ _
      (LB.pullGen D.toPre.P.L (fun _ : PUnit => eSec D.toPre.P.A) (fun _ => 1) D.toPre.rig (TO hϖ hv).hom)))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ h₀ h₁) h₂)
      (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.toPre.rig_gen _))) (fun U _ h => by
      have p₀ := SectionScalarValuation.prod_famB D.toPre g.b χ 1 h
      have p₁ := prod_gt g.b χ h
      have p₂ := CoefBasic.prod_line 1 g.b h
      have p₃ : (ιS hϖ hv).left ≫ (TO hϖ hv).hom ≫ eSec D.toPre.P.A = (1 : TF (R := V) F ⟶ D.toPre.P.A).left := by
        rw [← Category.assoc, Over.w]; rfl
      simp only [e₁] at p₁
      simp only [e₂] at p₂
      simp only [← hm', Category.assoc] at p₀
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, p₀, p₁, p₂, p₃]
      rw [mul_comm g.b, hm']
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one, SectionScalarValuation.cQ, cP]
      module)
  have e : coef s g w χ = a * x₁ * x₂ * u := CoefBasic.coef_eq fun z J hJ => by
    have q := vu z J hJ
    rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, Over.w, Units.val_mul, Units.val_mul, Units.val_mul,
      v₀ _ _ z J hJ, hm', Units.mul_inv_eq_iff_eq_mul] at q
    replace q : _ = _ * (rigV D.toPre (TF (R := V) F).hom z J).val := q
    have q₁ : gs (lift (𝟙 (TF (R := V) F)) g.b).left z ⊤ (gF D.toPre F a) = cst F z a := by
      refine (gs_pull _ (fst (TF (R := V) F) D.toPre.P.A).left z ⊤ trivial _).trans ?_
      rw [← Over.comp_left, lift_fst]; rfl
    rw [hs _ _ z J hJ, v₁ z J hJ, v₂ z J hJ, q₁, ← Over.comp_left, lift_snd, pow_one]
    simp only [CoefBasic.cst_eq, map_mul] at q ⊢
    exact Eq.symm (by linear_combination (CoefBasic.cstH z a * CoefBasic.cstH z x₁ * CoefBasic.cstH z x₂) * q)
  rw [e, AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_mul, hx₁, hx₂, hu₀, add_zero]

theorem exact_term_after_torsion : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ ϑ : Fam D.toPre F 1, Prim D Q v ϑ → ∀ (n : ℕ), 2 ≤ n → IsUnit (n : V) → ∀ (g : GtPtF D.toPre F) (χ : D.toPre.X), ∃ (h o g₂ : GtPtF D.toPre F), o.IsZero ∧ GtPtF.IsNsmul n h o ∧ g.IsAdd h g₂ ∧ ∀ (w : Frm D.toPre F 1 g₂.b) l ω, w.IsGen → GtV hϖ hv g₂ l → GenV hϖ hv w ω → v (coef ϑ g₂ w χ) = (((Q χ : ℚ) + l χ + ω : ℚ) : WithTop ℚ) := by
  intro hL _ _ _ _ V _ _ _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv ϑ hϑ n hn hnV g χ
  obtain ⟨b, hb, hb'⟩ := exists_secB_good hL.1 D.toPre χ
  obtain ⟨a, ha₁, ha₂, ha₃⟩ := vge_iff hϖ hv b hb (ϑ.s χ) (hϑ.1 χ)
  have ha : v a = ((Q χ : ℚ) : WithTop ℚ) := by
    simp only [Nat.cast_one, div_one, zero_add] at ha₁
    refine le_antisymm (not_lt.1 fun h => ?_) ha₁
    obtain ⟨q, hq₁, hq₂⟩ := WithTop.lt_iff_exists_coe_btwn.1 h
    refine hϑ.2 (q - Q χ) (sub_pos.2 (WithTop.coe_lt_coe.1 hq₁)) ((n1a V ϖ hϖ D Q hQ F v hv 1 le_rfl {χ}
      (fun χ' => ⟨χ, Finset.mem_singleton_self _, χ' - χ, by simp⟩) ϑ _).2 fun α hα => ?_)
    rw [Finset.mem_singleton] at hα
    subst hα
    refine ha₂ _ ?_
    simpa using hq₂.le
  have : IsAlgClosed (ResidueField (Ov v)) := isAlgClosed_residueField_of_valuationRing_of_isAlgClosed (Ov v) F
  obtain ⟨m, hm⟩ := exists_liftO hϖ hv g.b
  let ρ : Over.mk (Spec.map (CommRingCat.ofHom (residue (Ov v))) ≫ (TO hϖ hv).hom) ⟶ TO hϖ hv := Over.homMk _ rfl
  have hK : (n : ResidueField (Ov v)) ≠ 0 := by
    have := (hnV.map ((residue (Ov v)).comp (fO v hϖ hv))).ne_zero
    rwa [map_natCast] at this
  obtain ⟨x₀, hx₀, hu⟩ := hb' (ResidueField (Ov v)) _ n hn hK (ρ ≫ m)
  obtain ⟨hfin, hflat, -⟩ := hL.1.mulN _ D.toPre.P n (by omega)
  obtain ⟨x, hx, ex⟩ : ∃ x : TO hϖ hv ⟶ D.toPre.P.A, x ^ n = 1 ∧
      Spec.map (CommRingCat.ofHom (residue (Ov v))) ≫ x.left = x₀.left :=
    exists_torsion_lift (Ov v) D.toPre.P.A n (TO hϖ hv).hom x₀ hx₀
  have ex' : ρ ≫ x = x₀ := Over.OverMorphism.ext ex
  letI := TorusExt.gtGroup D.toPre F
  obtain ⟨h, hh₁, hh₂⟩ := TorusExt.exists_nsmul_eq_of_pow_eq (n := n) (by omega) (0 : GtPtF D.toPre F)
    (b := ιS hϖ hv ≫ x) (by rw [← MonObj.comp_pow, hx, MonObj.comp_one, TorusExt.zero_b])
  refine ⟨h, 0, g + h, (TorusExt.isZero_iff_eq _).2 rfl, (TorusExt.isNsmul_iff_eq _ _ _).2 hh₂.symm,
    (TorusExt.isAdd_iff_eq _ _ _).2 rfl, fun w l ω hw hl hω => ?_⟩
  rw [v_coef hϖ hv b ϑ a ha₃ (g + h) (m * x) (by rw [MonObj.comp_mul, hm, TorusExt.add_b, hh₁]) (fun z J hJ => by
    have q := hu z J hJ
    rw [← ex', ← MonObj.comp_mul] at q
    exact q) w hw (hl χ) hω, ha]
  rfl

end GlobalTheory.UT.ExactTerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExactTermAfterTorsionStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.exists_nsmul_add_decomp_with_coef_valuation : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ ϑ : Fam D.toPre F 1, Prim D Q v ϑ → ∀ (n : ℕ), 2 ≤ n → IsUnit (n : V) → ∀ (g : GtPtF D.toPre F) (χ : D.toPre.X), ∃ (h o g₂ : GtPtF D.toPre F), o.IsZero ∧ GtPtF.IsNsmul n h o ∧ g.IsAdd h g₂ ∧ ∀ (w : Frm D.toPre F 1 g₂.b) l ω, w.IsGen → GtV hϖ hv g₂ l → GenV hϖ hv w ω → v (coef ϑ g₂ w χ) = (((Q χ : ℚ) + l χ + ω : ℚ) : WithTop ℚ) := by
  first | exact @GlobalTheory.UT.ExactTerm.exact_term_after_torsion | exact GlobalTheory.UT.ExactTerm.exact_term_after_torsion | (intros; apply GlobalTheory.UT.ExactTerm.exact_term_after_torsion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLiftUnitTensor
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU

theorem exists_lift_unit_tensor {S Z : Scheme.{0}} (X : Over S) (q : Z ⟶ X.left) :
    ∃ r : Z ⟶ (𝟙_ (Over S) ⊗ X).left, r ≫ (snd _ X).left = q ∧ r ≫ (fst _ X).left = q ≫ X.hom := by
  refine ⟨q ≫ (λ_ X).inv.left, ?_, ?_⟩
  · rw [Category.assoc, ← Over.comp_left, leftUnitor_inv_snd, Over.id_left, Category.comp_id]
  · rw [Category.assoc, ← Over.comp_left, leftUnitor_inv_fst]
    rfl

theorem expandsAt_of_expT : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U' : UnifPre I D A G), Match U U' → ∀ (k : ℕ) (σ : H0 U'.LG.L k) (σ₀ : H0 U.P.L.L k) (σ' : U.SecGT (𝟙_ _) k) (f) (f'), HEq σ σ₀ → SameG σ₀ σ' → SameB f f' → U.ExpT (𝟙_ _) k σ' f' → ∀ e, U'.ExpandsAt e k σ f := by
  intro R _ _ I D A G _ _ U U' hM k σ σ₀ σ' f f' hσ hG hB hE e
  obtain ⟨semi, gen, gen_hom, P, wA, wA_gen, gt, gt_q, gt_t, w, w_gen, w_vals, w_compat⟩ := U
  cases P
  obtain ⟨-, hL, -, -, hgt, hw⟩ := hM
  dsimp only at hL hgt hw
  subst hL hgt
  obtain rfl := eq_of_heq hw
  obtain rfl := eq_of_heq hσ
  obtain ⟨S, hS⟩ := hE e
  refine DVR.expandsAt_of_val U' e k σ f S fun y J hJ => ?_
  obtain ⟨rG, hG₁, hG₂⟩ := exists_lift_unit_tensor G (fstG I e G).left
  obtain ⟨rB, hB₁, hB₂⟩ := exists_lift_unit_tensor D.toPre.P.A (U'.gt e).pG.left
  have hc : (U'.gt e).pG.left ≫ D.toPre.P.A.hom = (fstG I e G).left ≫ G.hom :=
    (Over.w (U'.gt e).pG).trans (Over.w (fstG I e G)).symm
  have H := hS _ (𝟙 _) rG rB (hG₁.trans (Category.id_comp _).symm) (hB₁.trans (Category.id_comp _).symm)
    (hB₂.trans (hc.trans hG₂.symm)) y
  have hf : ∀ α, sval (f' α) rB y J = sval (f α) (DVR.pGl U' e) y J := fun α => by
    rw [hB α _ rB y J hJ, hB₁]
  refine ⟨fun α hα => ?_, fun jL hL => ?_⟩
  · choose JG hJG using fun ψ : (thickObj R I e G).left ⟶ G.left => exists_chart U'.LG.isLB (ψ y)
    exact (hf α).symm.trans ((H JG J hJG hJ).1 α hα)
  · obtain ⟨JG, hJG, eJ⟩ := exists_good U'.LG.L U'.LG.isLB y (fun _ : PUnit => (fstG I e G).left) (fun _ => jL)
      (fun _ _ _ => rfl) (fun _ => hL)
    have e₀ : JG (fstG I e G).left = jL := eJ PUnit.unit
    have H₂ := (H JG J hJG hJ).2
    have hs : sval σ' rG y JG = DVR.sv U' k σ (DVR.fGl I G e) y jL := by
      rw [hG _ rG y JG hJG, hG₁]
      exact sval_of σ _ y JG (fun _ => jL) (fun _ => by rw [Category.comp_id]; exact e₀)
    simp only [Category.id_comp, e₀, hs, hf] at H₂
    rw [Units.val_pow_eq_pow_val]
    exact H₂

end GlobalTheory.UU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MatchingSectionsExist
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UnitSec

section Gen
variable {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem exists_pull {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K → (Y' ⟶ X)} (h : Y' ⟶ Y)
    (hφ : ∀ k, φ' k = h ≫ φ k) (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      sval s' r z J = sval s (r ≫ h) z J := by
  obtain rfl : φ' = fun k => h ≫ φ k := funext hφ
  exact ⟨_, fun Z r z J hJ => DVR.SectionScalarValuation.sval_pullSec φ ε s h r z hJ⟩

theorem exists_push {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K → (Y' ⟶ X)} (h : Y' ⟶ Y) (g : Y ⟶ Y')
    (h₁ : g ≫ h = 𝟙 Y) (h₂ : h ≫ g = 𝟙 Y')
    (hφ : ∀ k, φ' k = h ≫ φ k) (s' : LB.Sec (LB.LinComb L φ' ε)) :
    ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      sval s' r z J = sval s (r ≫ h) z J := by
  obtain ⟨s, hs⟩ := exists_pull (φ' := φ) g
    (fun k => by rw [hφ k, ← Category.assoc, h₁, Category.id_comp]) s'
  refine ⟨s, fun Z r z J hJ => ?_⟩
  rw [hs Z _ z J hJ, Category.assoc, h₂, Category.comp_id]

end Gen

theorem unit_inv_snd {S : Scheme.{0}} (G : Over S) :
    (λ_ G).inv.left ≫ (snd (𝟙_ (Over S)) G).left = 𝟙 G.left := by
  rw [← Over.comp_left, leftUnitor_inv_snd, Over.id_left]

theorem snd_unit_inv {S : Scheme.{0}} (G : Over S) :
    (snd (𝟙_ (Over S)) G).left ≫ (λ_ G).inv.left = 𝟙 (𝟙_ (Over S) ⊗ G).left := by
  rw [← Over.comp_left, ← leftUnitor_hom, Iso.hom_inv_id, Over.id_left]

theorem famφT_eq {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (α : D.X) (k : Fin 4) : famφT D T α k = (snd T D.P.A).left ≫ D.famφB α k := by
  fin_cases k
  · change (snd T D.P.A).left = (snd T D.P.A).left ≫ 𝟙 _
    rw [Category.comp_id]
  · change (padd D.P.A (snd T D.P.A) (toUnit _ ≫ D.c α)).left =
      (snd T D.P.A).left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left
    rw [← Over.comp_left]; congr 1
    simp only [padd]
    rw [← Category.assoc, comp_lift, Category.comp_id, ← Category.assoc, comp_toUnit]
  · change (toUnit (T ⊗ D.P.A) ≫ D.c α).left = (snd T D.P.A).left ≫ (toUnit D.P.A ≫ D.c α).left
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]
  · change (toUnit (T ⊗ D.P.A) ≫ η[D.P.A]).left = (snd T D.P.A).left ≫ (toUnit D.P.A ≫ η[D.P.A]).left
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]

theorem same_exists : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (G : Over (Spec (CommRingCat.of R))) (L : LB G.left), L.IsLB → ∀ k : ℕ, (∀ σ : H0 L k, ∃ σ', SameG σ σ') ∧ (∀ σ', ∃ σ : H0 L k, SameG σ σ') ∧ (∀ f : ∀ α, D.SecB k α, ∃ f', SameB f f') ∧ ∀ f', ∃ f : ∀ α, D.SecB k α, SameB f f' := by
  intro R _ _ D G L _ k
  refine ⟨fun σ => ?_, fun σ' => ?_, fun f => ?_, fun f' => ?_⟩
  · exact exists_pull (snd _ G).left (fun _ => (Category.comp_id _).symm) σ
  · exact exists_push (φ := fun _ : Fin 1 => 𝟙 G.left) (snd _ G).left (λ_ G).inv.left (unit_inv_snd G)
      (snd_unit_inv G) (fun _ => (Category.comp_id _).symm) σ'
  · choose f' hf' using fun α => exists_pull (snd _ D.P.A).left (famφT_eq D (𝟙_ _) α) (f α)
    exact ⟨f', hf'⟩
  · choose f hf using fun α => exists_push (snd _ D.P.A).left (λ_ D.P.A).inv.left (unit_inv_snd _)
      (snd_unit_inv _) (famφT_eq D (𝟙_ _) α) (f' α)
    exact ⟨f, hf⟩

end GlobalTheory.UnitSec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultPsiEvenOverExtensionField
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultPsiEvenOverExtensionField
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.TauValues

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem val_tau {Z : Scheme.{0}} (r : Z ⟶ (TK R).left) {z : Z} {J} (hJ : Good D.P.L z J) (a b : D.X) :
    val (D.tau a b) r z J =
      val (D.psi (a + b)) r z J * (val (D.psi a) r z J)⁻¹ * (val (D.psi b) r z J)⁻¹ * (val D.rigK r z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem comp_cT {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) (χ : D.X) :
    κ ≫ toUnit (TK R) ≫ D.c χ = cT D T χ := by
  rw [← Category.assoc, comp_toUnit]

theorem val_rigK {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) {z : T.left} {J} (hJ : Good D.P.L z J) :
    val D.rigK κ.left z J = rigV D z J := by
  refine (val_pull hJ _ _ _).trans ?_
  have e : κ.left ≫ (toUnit (TK R)).left = T.hom := by
    rw [← Over.comp_left, comp_toUnit]; rfl
  exact congrArg (fun q : T.left ⟶ Spec (CommRingCat.of R) =>
    val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig q z J) e

theorem bimult_iff {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) {z : T.left} {J} (hJ : Good D.P.L z J)
    (a b m : D.X) :
    val (D.psi (a + b + m)) κ.left z J * val (D.psi a) κ.left z J * val (D.psi b) κ.left z J *
        val (D.psi m) κ.left z J * rigV D z J * cubV D.cub z J (cT D T a) (cT D T b) (cT D T m) =
      val (D.psi (a + b)) κ.left z J * val (D.psi (a + m)) κ.left z J * val (D.psi (b + m)) κ.left z J ↔
    val (LB.mulGen D.P.L _ _ _ _ (D.tau (a + b) m)
        (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a b m))) κ.left z J =
      val (LB.mulGen D.P.L _ _ _ _ (D.tau a m) (D.tau b m)) κ.left z J := by
  have c : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a b m)) κ.left z J =
      cubV D.cub z J (cT D T a) (cT D T b) (cT D T m) := by
    refine (val_cub D.cub κ hJ (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b) (toUnit (TK R) ≫ D.c m)).trans ?_
    rw [comp_cT, comp_cT, comp_cT]
  have l := (val_mul hJ (D.tau (a + b) m)
    (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a b m)) κ.left).trans
    (congrArg₂ (· * ·) (val_tau D κ.left hJ _ _) c)
  have r := (val_mul hJ (D.tau a m) (D.tau b m) κ.left).trans
    (congrArg₂ (· * ·) (val_tau D κ.left hJ _ _) (val_tau D κ.left hJ _ _))
  rw [val_rigK D κ hJ] at l r
  rw [l, r]
  constructor <;> intro h <;> apply Additive.ofMul.injective <;> have e := congrArg Additive.ofMul h <;>
    simp only [ofMul_mul, ofMul_inv] at e ⊢ <;> linear_combination (norm := abel) e

theorem val_even {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) {z : T.left} {J} (hJ : Good D.P.L z J)
    (m : D.X) :
    val (LB.mulGen D.P.L _ _ _ _ (D.psi (-m)) (LB.pullGen D.P.L _ _ D.sym (D.xK m))) κ.left z J =
      val (D.psi (-m)) κ.left z J * val D.sym (cT D T m).left z J := by
  refine (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans ?_))
  have e : κ.left ≫ D.xK m = (cT D T m).left := by
    rw [← comp_cT D κ m]; rfl
  rw [e]

theorem bimult_iff' {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) [Flat κ.left] [Surjective κ.left] :
    (∀ (z : T.left) J, Good D.P.L z J → ∀ a b m : D.X,
      val (D.psi (a + b + m)) κ.left z J * val (D.psi a) κ.left z J * val (D.psi b) κ.left z J *
        val (D.psi m) κ.left z J * rigV D z J * cubV D.cub z J (cT D T a) (cT D T b) (cT D T m) =
      val (D.psi (a + b)) κ.left z J * val (D.psi (a + m)) κ.left z J * val (D.psi (b + m)) κ.left z J) ↔
    D.TauBimult :=
  ⟨fun h a b m => corr_of_val_flat_surjective κ.left D.P.isLB fun z J hJ => (bimult_iff D κ hJ a b m).1 (h z J hJ a b m),
    fun h _ _ hJ a b m => (bimult_iff D κ hJ a b m).2 (val_corr hJ (h a b m) κ.left)⟩

theorem even_iff {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) [Flat κ.left] [Surjective κ.left] :
    (∀ (z : T.left) J, Good D.P.L z J → ∀ m : D.X,
      val (D.psi (-m)) κ.left z J * val D.sym (cT D T m).left z J = val (D.psi m) κ.left z J) ↔ D.PsiEven :=
  ⟨fun h m => corr_of_val_flat_surjective κ.left D.P.isLB fun z J hJ => (val_even D κ hJ m).trans (h z J hJ m),
    fun h _ _ hJ m => (val_even D κ hJ m).symm.trans (val_corr hJ (h m) κ.left)⟩

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F], ((∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → ∀ a b m : D.X, val (Z := (TF (R := R) F).left) (D.psi (a + b + m)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (a)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (b)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (m)) (jFK (R := R) F) z J * rigV D z J * cubV D.cub z J (cT D _ a) (cT D _ b) (cT D _ m) = val (Z := (TF (R := R) F).left) (D.psi (a + b)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (a + m)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (b + m)) (jFK (R := R) F) z J) ↔ D.TauBimult) ∧ ((∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → ∀ m : D.X, val (Z := (TF (R := R) F).left) (D.psi (-m)) (jFK (R := R) F) z J * val D.sym (cT D (TF (R := R) F) m).left z J = val (Z := (TF (R := R) F).left) (D.psi (m)) (jFK (R := R) F) z J) ↔ D.PsiEven) := by
  intro R _ _ D F _ _
  let κ : TF (R := R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl
  have hκ : κ.left = Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F)) := rfl
  have : Flat κ.left := by
    rw [hκ]
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.Flat.of_isField (Field.toIsField (FractionRing R)) _)
  have : Surjective κ.left := by
    have : Subsingleton (TK R).left := inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
    exact ⟨fun y => ⟨(default : PrimeSpectrum F), Subsingleton.elim _ _⟩⟩
  exact ⟨bimult_iff' D κ, even_iff D κ⟩

end GlobalTheory.TauValues
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultPsiEvenOverExtensionFieldStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.tau_bimult_psi_even_over_extension_field : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F], ((∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → ∀ a b m : D.X, val (Z := (TF (R := R) F).left) (D.psi (a + b + m)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (a)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (b)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (m)) (jFK (R := R) F) z J * rigV D z J * cubV D.cub z J (cT D _ a) (cT D _ b) (cT D _ m) = val (Z := (TF (R := R) F).left) (D.psi (a + b)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (a + m)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (b + m)) (jFK (R := R) F) z J) ↔ D.TauBimult) ∧ ((∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → ∀ m : D.X, val (Z := (TF (R := R) F).left) (D.psi (-m)) (jFK (R := R) F) z J * val D.sym (cT D (TF (R := R) F) m).left z J = val (Z := (TF (R := R) F).left) (D.psi (m)) (jFK (R := R) F) z J) ↔ D.PsiEven) := by
  first | exact @GlobalTheory.TauValues.main | exact GlobalTheory.TauValues.main | (intros; apply GlobalTheory.TauValues.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ChainVal
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.UU

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem GtTors.base_pow {k : ℕ} {g : GtPtF D F} (hg : GtTors D k g) : g.b ^ k = 1 := by
  obtain ⟨h, ⟨gs, h₀, hs, hl⟩, hz⟩ := hg
  have key : ∀ i (hi : i < k + 1), (gs ⟨i, hi⟩).b = g.b ^ i := by
    intro i
    induction i with
    | zero => exact fun _ => h₀.1
    | succ i ih =>
      exact fun hi => (hs ⟨i, by omega⟩).1.trans ((congrArg (· * g.b) (ih (by omega))).trans (pow_succ _ _).symm)
  have hl' : gs ⟨k, Nat.lt_succ_self k⟩ = h := hl
  rw [← key k (Nat.lt_succ_self k), hl']; exact hz.1

theorem GtTors.chain_val {k : ℕ} {g : GtPtF D F} (hg : GtTors D k g) {T : Over (Spec (CommRingCat.of R))}
    (σ : T ⟶ TF (R := R) F) {z : T.left} {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (mu : D.X) :
    1 * cubN (th D z J) k 1 (σ ≫ g.b) (cP D T mu) = val (g.s mu) σ.left z J ^ k := by
  obtain ⟨h, ⟨gs, h₀, hs, hl⟩, hz⟩ := hg
  have C : IsCub (cubV D.cub z J) := isCub_cubV D.cub hJ
  have key : ∀ i (hi : i < k + 1), (gs ⟨i, hi⟩).b = g.b ^ i ∧
      val ((gs ⟨i, hi⟩).s mu) σ.left z J * cubN (th D z J) i 1 (σ ≫ g.b) (cP D T mu) = val (g.s mu) σ.left z J ^ i := by
    intro i
    induction i with
    | zero => exact fun _ => ⟨h₀.1, (_root_.mul_one _).trans ((val_corr hJ (h₀.2 mu) σ.left).trans
        ((val_one _).trans (pow_zero _).symm))⟩
    | succ i ih =>
      intro hi
      obtain ⟨b₁, v₁⟩ := ih (by omega)
      obtain ⟨b₂, v₂⟩ := hs ⟨i, by omega⟩
      refine ⟨b₂.trans ((congrArg (· * g.b) b₁).trans (pow_succ _ _).symm), ?_⟩
      have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub σ hJ _ _ _))).symm.trans
        ((val_corr hJ (v₂ mu) σ.left).trans (val_mul hJ _ _ _))
      have e₁ : σ ≫ (gs (Fin.castSucc ⟨i, by omega⟩)).b = 1 * (σ ≫ g.b) ^ i := by
        rw [_root_.one_mul]; exact (congrArg (σ ≫ ·) b₁).trans (map_pow (preHom σ) _ _)
      have e₂ : σ ≫ DegPre.cF D F mu = cP D T mu := comp_cP D σ mu
      rw [e₁, e₂, C.s01, C.s12] at e
      rw [cubN, Finset.prod_range_succ, mul_comm (∏ _ ∈ _, _), ← _root_.mul_assoc, pow_succ, ← v₁, cubN]
      exact (congrArg₂ (· * ·) e rfl).trans (mul_right_comm _ _ _)
  have hk := (key k (Nat.lt_succ_self k)).2
  have hl' : gs ⟨k, Nat.lt_succ_self k⟩ = h := hl
  rw [hl'] at hk
  rw [← hk]
  exact congrArg₂ (· * ·) ((val_corr hJ (hz.2 mu) σ.left).trans (val_one _)).symm rfl

theorem GtTors.val_phi (hG : GlobalFnsSt) {k : ℕ} {g : GtPtF D F} (hg : GtTors D k g)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))) (hw : w.IsGen) (α : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F 0 α g.b) (DegPre.deltaε k))) (hu : u.IsGen)
    (hc : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (LB.mulGen D.P.L _ _ _ _ (g.s α) w))
    (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J) (hJ : Good D.P.L z J) :
    val u ρ.left z J = uVal D F k α g.b ρ z J * val (LB.mulGen D.P.L _ _ _ _ (g.s α) w) (ρ ≫ fst _ _).left z J :=
  (gen_u D F hG k α (α + 0) g.b (by rw [add_zero, hg.base_pow, _root_.mul_one]) _
    (mulGen_isGen _ _ _ _ _ _ _ (g.isGen α) hw) (fun U _ h => by
    refine (Fintype.prod_sum_type _).trans ?_
    rw [Fin.prod_univ_four, Fin.prod_univ_two]
    show h (cP D _ α * g.b).left ^ (-1 : ℤ) * h (cP D _ α).left ^ (1 : ℤ) * h g.b.left ^ (1 : ℤ) *
      h (1 : TF (R := R) F ⟶ D.P.A).left ^ (-1 : ℤ) *
      (h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h g.b.left ^ (-(k : ℤ))) = _
    simp only [zpow_neg, zpow_one, zpow_natCast]
    ac_rfl)).2 u hu hc T ρ z J hJ

theorem val_delta (hG : GlobalFnsSt) (k : ℕ) (α mu : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F k α mu) (DegPre.deltaε k))) (hu : u.IsGen)
    (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J) (hJ : Good D.P.L z J) :
    val u ρ.left z J = uVal D F k α (cP D _ mu) ρ z J *
      val (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (ρ ≫ fst _ _).left z J := by
  have z₁ : DegPre.zF D F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have z₂ : DegPre.zF D F ≫ DegPre.prB D F = 1 := lift_snd _ _
  have z₃ : (DegPre.zF D F ≫ DegPre.trF D F mu) ≫ DegPre.prB D F = cP D _ mu := by
    rw [trF_eq, Category.assoc, tr_pr, MonObj.comp_mul, z₂, ← Category.assoc, z₁, Category.id_comp, _root_.one_mul]
  have H := gen_u D F hG k α (α + k • mu) (cP D _ mu) (by rw [cPoint_add, cPoint_nsmul])
    (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (pullGen_isGen _ _ _ _ hu _) (fun U _ h => by
      have p₃ := prod_fam D F (DegPre.zF D F) (α + k • mu) k h
      have p₄ := prod_fam D F (DegPre.zF D F ≫ DegPre.trF D F mu) α k h
      rw [z₂, _root_.mul_one] at p₃
      rw [z₃] at p₄
      simp only [Over.comp_left, Category.assoc] at p₄
      refine Eq.trans (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₃ (prod_neg _ _ p₄)) ?_
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
  rw [← trF_eq] at H
  exact H.2 u hu (corr_of_val D.P.isLB fun _ _ _ => rfl) T ρ z J hJ

theorem phi_comm : (GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) (g : GtPtF D F), GtTors D N g → ∀ (α mu : D.X) (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε N))) (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F N α mu) (DegPre.deltaε N))) (p : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F 0 α g.b) (DegPre.deltaε N))) (p' : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F 0 (α + N • mu) g.b) (DegPre.deltaε N))), w.IsGen → u.IsGen → p.IsGen → p'.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ p (DegPre.zF D F).left) (LB.mulGen D.P.L _ _ _ _ (g.s α) w) → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ p' (DegPre.zF D F).left) (LB.mulGen D.P.L _ _ _ _ (g.s (α + N • mu)) w) → ∀ z J, Good D.P.L z J → val p' (𝟙 _) z J * val u (DegPre.trPt D F g.b).left z J = val u (𝟙 _) z J * val p (DegPre.trF D F mu).left z J) := by
  intro hG R _ _ D F _ _ k g hg α mu w u p p' hw hu hp hp' hc hc' y J hJ
  have C : IsCub (th D (T := DegPre.BF D F) y J) := isCub_cubV D.cub hJ
  have hm : fst (TF (R := R) F) D.P.A ≫ cP D _ mu = cP D _ mu := comp_cP D _ mu
  have hy : (fst (TF (R := R) F) D.P.A ≫ g.b) ^ k = 1 :=
    (map_pow (preHom (fst (TF (R := R) F) D.P.A)) _ _).symm.trans
      ((congrArg (preHom (fst (TF (R := R) F) D.P.A)) hg.base_pow).trans (map_one _))
  have t₁ := gt_nsmul (fst (TF (R := R) F) D.P.A) hJ g α mu k
  have t₃ := hg.chain_val (fst (TF (R := R) F) D.P.A) hJ mu
  have key := C.comm k _ _ _ (DegPre.prB D F) _ _ _ 1 1 1 t₁ (by rw [hy, C.face₂]) t₃
  have e₁ := hg.val_phi hG w hw (α + k • mu) p' hp' hc' _ (𝟙 _) y J hJ
  have e₂ := hg.val_phi hG w hw α p hp hc _ (DegPre.trPt D F (cP D _ mu)) y J hJ
  have e₃ := val_delta hG k α mu u hu _ (𝟙 _) y J hJ
  have e₄ := val_delta hG k α mu u hu _ (DegPre.trPt D F g.b) y J hJ
  rw [Category.id_comp, Over.id_left, uVal_id, val_mul hJ, cPoint_add, cPoint_nsmul] at e₁
  rw [tr_fst, uVal_tr, val_mul hJ, hm] at e₂
  rw [Category.id_comp, Over.id_left, uVal_id, hm] at e₃
  rw [tr_fst, uVal_tr, hm] at e₄
  rw [hy, _root_.mul_one (cP D _ α)] at key
  refine (congrArg₂ (· * ·) e₁ e₄).trans (Eq.trans ?_ (congrArg₂ (· * ·) e₃
    ((congrArg (fun q : DegPre.BF D F ⟶ DegPre.BF D F => val p q.left y J) (trF_eq D F mu)).trans e₂)).symm)
  apply Additive.ofMul.injective
  have key' := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at key' ⊢
  linear_combination (norm := abel) key'

end GlobalTheory.UU

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BijectiveOfIso
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.GenericFibreSections

variable {X₁ X₂ Y Y' : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂}

theorem exists_transfer (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) (φ₁ : Y ⟶ X₁) (φ₂ : Y ⟶ X₂) (k : ℤ)
    (V : L₁.ι → L₂.ι → Y.Opens) (hV : ∀ i j y, φ₁ y ∈ L₁.U i → φ₂ y ∈ L₂.U j → y ∈ V i j)
    (u : ∀ i j, Γ(Y, V i j)ˣ)
    (hu : ∀ (y : Y) i i' j j', φ₁ y ∈ L₁.U i → φ₁ y ∈ L₁.U i' → φ₂ y ∈ L₂.U j → φ₂ y ∈ L₂.U j' →
      gm (𝟙 Y) y _ (u i j) * gm (𝟙 Y ≫ φ₁) y _ (L₁.g i i') ^ k =
        gm (𝟙 Y ≫ φ₂) y _ (L₂.g j j') ^ k * gm (𝟙 Y) y _ (u i' j'))
    (s : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => φ₁) (fun _ => k))) :
    ∃ s' : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => φ₂) (fun _ => k)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J₁ J₂, Good L₁ z J₁ → Good L₂ z J₂ →
        sval s' r z J₂ = (gm r z _ (u (J₁ (r ≫ φ₁)) (J₂ (r ≫ φ₂)))).val * sval s r z J₁ := by
  have glue : ∀ j : Fin 1 → L₂.ι, ∃ a : Γ(Y, LB.wchart L₂ (fun _ : Fin 1 => φ₂) j),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : L₁.ι),
      r z ∈ LB.wchart L₂ (fun _ : Fin 1 => φ₂) j → φ₁ (r z) ∈ L₁.U i →
      gs r z _ a = (gm r z _ (u i (j 0))).val *
        gs r z (LB.wchart L₁ (fun _ : Fin 1 => φ₁) (fun _ => i)) (s.f (fun _ => i)) := by
    intro j
    let W : L₁.ι → Y.Opens := fun i =>
      LB.wchart L₂ (fun _ : Fin 1 => φ₂) j ⊓ LB.wchart L₁ (fun _ : Fin 1 => φ₁) (fun _ => i)
    have l : ∀ i, W i ≤ V i (j 0) := fun i y hy =>
      hV i (j 0) y (Set.mem_iInter.1 hy.2 0) (Set.mem_iInter.1 hy.1 0)
    obtain ⟨b, hb⟩ : ∃ b : ∀ i, Γ(Y, W i), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) i, r z ∈ W i →
        gs r z (W i) (b i) = (gm r z _ (u i (j 0))).val *
          gs r z (LB.wchart L₁ (fun _ : Fin 1 => φ₁) (fun _ => i)) (s.f (fun _ => i)) :=
      ⟨fun i => (Y.presheaf.map (homOfLE (l i)).op).hom (u i (j 0)).val *
          (Y.presheaf.map (homOfLE (inf_le_right : W i ≤ LB.wchart L₁ (fun _ : Fin 1 => φ₁) (fun _ => i))).op).hom
            (s.f (fun _ => i)), fun Z r z i hz =>
        (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_res r z _ hz _).trans (gs_unit r z _ (l i hz) _))
          (gs_res r z _ hz _))⟩
    obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' W (LB.wchart L₂ (fun _ : Fin 1 => φ₂) j)
      (fun i => homOfLE inf_le_left) (fun y hy => by
        obtain ⟨i, hi⟩ := exists_chart hL₁ (φ₁ y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hy, Set.mem_iInter.2 fun _ => hi⟩) b
      (fun i i' => fn_ext (V := W i ⊓ W i') fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        have m : φ₂ y ∈ L₂.U (j 0) := Set.mem_iInter.1 hy.1.1 0
        have e := hu y i i' (j 0) (j 0) (Set.mem_iInter.1 hy.1.2 0) (Set.mem_iInter.1 hy.2.2 0) m m
        rw [gm_self hL₂ (𝟙 Y ≫ φ₂) y m, _root_.one_zpow, _root_.one_mul] at e
        rw [hb _ _ y i hy.1, hb _ _ y i' hy.2, sec_trans s (𝟙 Y) y hy.1.2 hy.2.2, ← _root_.mul_assoc, ← Units.val_mul,
          ← e, trF, Fintype.prod_unique])
    refine ⟨a, fun Z r z i h₁ h₂ => ?_⟩
    have hz : r z ∈ W i := ⟨h₁, Set.mem_iInter.2 fun _ => h₂⟩
    exact (gs_res r z inf_le_left hz a).symm.trans ((congrArg (gs r z (W i)) (ha i)).trans (hb Z r z i hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z J₁ J₂ hJ₁ hJ₂ => ?_⟩
  · obtain ⟨i, hi⟩ := exists_chart hL₁ (φ₁ y)
    refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L₂ _ _ (𝟙 Y) y j j' hy.1 hy.2)))
      (gs_res (𝟙 Y) y _ hy _))).symm)
    refine (ha j _ (𝟙 Y) y i hy.1 hi).trans (Eq.trans ?_ (congrArg _ (ha j' _ (𝟙 Y) y i hy.2 hi)).symm)
    have e := hu y i i (j 0) (j' 0) hi hi (Set.mem_iInter.1 hy.1 0) (Set.mem_iInter.1 hy.2 0)
    rw [gm_self hL₁ (𝟙 Y ≫ φ₁) y hi, _root_.one_zpow, _root_.mul_one] at e
    rw [e, Fintype.prod_unique, Units.val_mul, _root_.mul_assoc]
    rfl
  · exact ha _ Z r z (J₁ (r ≫ φ₁)) (hJ₂.mem (fun _ : Fin 1 => φ₂) r) (hJ₁ (r ≫ φ₁))

theorem exists_pull (h : Y' ⟶ Y) (φ : Y ⟶ X₁) (φ' : Y' ⟶ X₁) (e : φ' = h ≫ φ) (k : ℤ)
    (s : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => φ) (fun _ => k))) :
    ∃ s' : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => φ') (fun _ => k)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) J, Good L₁ z J → sval s' r z J = sval s (r ≫ h) z J := by
  subst e
  exact ⟨_, fun Z r z J hJ => H1.SectionArithmetic.sval_pullSec s h r z hJ⟩

theorem sec_ext {M : LB Y} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  obtain ⟨f, _⟩ := s
  obtain ⟨f', _⟩ := s'
  obtain rfl : f = f' := funext h
  rfl

theorem gw_trans {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} {w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)} (hw : w.IsGen) (y : Y)
    {i i' : L₁.ι} {j j' : L₂.ι} (hi : f₁ y ∈ L₁.U i) (hi' : f₁ y ∈ L₁.U i') (hj : f₂ y ∈ L₂.U j) (hj' : f₂ y ∈ L₂.U j') :
    gw w (𝟙 Y) y j (fun _ => i) * gm (𝟙 Y ≫ f₁) y _ (L₁.g i i') =
      gm (𝟙 Y ≫ f₂) y _ (L₂.g j j') * gw w (𝟙 Y) y j' (fun _ => i') := by
  have e := (isGen_iff w).1 hw Y (𝟙 Y) y j j' (fun _ => i) (fun _ => i') hj hj' (mem_pull.2 hi) (mem_pull.2 hi')
  rw [gm_pull_g L₁ f₁ (𝟙 Y) y _ _ (mem_pull.2 hi) (mem_pull.2 hi')] at e
  rw [e, _root_.mul_right_comm, inv_mul_cancel_right]

theorem bijective_of_iso (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (p : Y' ⟶ X₁) [IsIso f₁] [IsIso p]
    (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (hw : w.IsGen) (k : ℕ)
    (Rel : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ))) →
      LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => p) (fun _ => (k : ℤ))) → Prop)
    (hRel : ∀ σ t, Rel σ t ↔ ∀ (Z : Scheme.{0}) (rA : Z ⟶ Y') (y : Z ⟶ Y), rA ≫ p = y ≫ f₁ → ∀ (z : Z) J₁ J₂,
      Good L₁ z J₁ → Good L₂ z J₂ →
      (gw w y z (J₂ (y ≫ f₂)) (fun _ => J₁ (y ≫ f₁))).val ^ k * sval t rA z J₁ = sval σ y z J₂) :
    (∀ σ, ∃! t, Rel σ t) ∧ ∀ t, ∃! σ, Rel σ t := by
  have hV : ∀ i j (y : Y), f₁ y ∈ L₁.U i → f₂ y ∈ L₂.U j →
      y ∈ (L₂.pull f₂).U (fun _ => j) ⊓ (L₁.pull f₁).U (fun _ => i) := fun i j y hi hj => ⟨mem_pull.2 hj, mem_pull.2 hi⟩
  refine ⟨fun σ => ?_, fun t => ?_⟩
  · obtain ⟨s, hs⟩ := exists_transfer hL₂ hL₁ f₂ f₁ k
      (fun j i => (L₂.pull f₂).U (fun _ => j) ⊓ (L₁.pull f₁).U (fun _ => i)) (fun j i y hj hi => hV i j y hi hj)
      (fun j i => ((show Γ(Y, (L₂.pull f₂).U (fun _ => j) ⊓ (L₁.pull f₁).U (fun _ => i))ˣ from
        w.s (fun _ => j, fun _ => i)) ^ k)⁻¹) (fun y j j' i i' hj hj' hi hi' => by
        have e := gw_trans hw y hi hi' hj hj'
        rw [map_inv, map_inv, map_pow, map_pow, zpow_natCast, zpow_natCast]
        change (gw w (𝟙 Y) y j (fun _ => i) ^ k)⁻¹ * _ = _ * (gw w (𝟙 Y) y j' (fun _ => i') ^ k)⁻¹
        rw [inv_mul_eq_iff_eq_mul, ← _root_.mul_assoc, ← mul_pow, e, mul_pow, mul_inv_cancel_right]) σ
    obtain ⟨t, ht⟩ := exists_pull (p ≫ inv f₁) f₁ p (by simp) k s
    refine ⟨t, (hRel _ _).2 fun Z rA y e z J₁ J₂ h₁ h₂ => ?_, fun t' H' => ?_⟩
    · have e' : rA ≫ p ≫ inv f₁ = y := by rw [← Category.assoc, e]; simp
      rw [ht Z rA z J₁ h₁, e', hs Z y z J₂ J₁ h₂ h₁, map_inv, map_pow, ← Units.val_pow_eq_pow_val]
      exact Units.mul_inv_cancel_left _ _
    · refine sec_ext (sec_ext_val hL₁ fun y J₁ h₁ => ?_)
      choose J₂ h₂ using fun χ : Y' ⟶ X₂ => exists_chart hL₂ (χ y)
      have e := (hRel _ _).1 H' Y' (𝟙 _) (p ≫ inv f₁) (by simp) y J₁ J₂ h₁ h₂
      rw [ht _ _ y J₁ h₁, Category.id_comp, hs _ _ y J₂ J₁ h₂ h₁, map_inv, map_pow, ← e, ← Units.val_pow_eq_pow_val]
      exact (Units.inv_mul_cancel_left _ _).symm
  · obtain ⟨s, hs⟩ := exists_pull (f₁ ≫ inv p) p f₁ (by simp) k t
    obtain ⟨σ, hσ⟩ := exists_transfer hL₁ hL₂ f₁ f₂ k
      (fun i j => (L₂.pull f₂).U (fun _ => j) ⊓ (L₁.pull f₁).U (fun _ => i)) hV
      (fun i j => (show Γ(Y, (L₂.pull f₂).U (fun _ => j) ⊓ (L₁.pull f₁).U (fun _ => i))ˣ from
        w.s (fun _ => j, fun _ => i)) ^ k) (fun y i i' j j' hi hi' hj hj' => by
        have e := gw_trans hw y hi hi' hj hj'
        rw [map_pow, map_pow, zpow_natCast, zpow_natCast, ← mul_pow, ← mul_pow]
        exact congrArg (· ^ k) e) s
    refine ⟨σ, (hRel _ _).2 fun Z rA y e z J₁ J₂ h₁ h₂ => ?_, fun σ' H' => ?_⟩
    · have e' : y ≫ f₁ ≫ inv p = rA := by rw [← Category.assoc, ← e]; simp
      rw [hσ Z y z J₁ J₂ h₁ h₂, hs Z y z J₁ h₁, e', map_pow, Units.val_pow_eq_pow_val]
      rfl
    · refine sec_ext (sec_ext_val hL₂ fun y J₂ h₂ => ?_)
      choose J₁ h₁ using fun χ : Y ⟶ X₁ => exists_chart hL₁ (χ y)
      have e := (hRel _ _).1 H' Y (𝟙 Y ≫ f₁ ≫ inv p) (𝟙 _) (by simp) y J₁ J₂ h₁ h₂
      rw [← e, hσ _ _ y J₁ J₂ h₁ h₂, hs _ _ y J₁ h₁, map_pow, Units.val_pow_eq_pow_val]
      rfl

theorem sameK_bijective : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (k : ℕ), (∀ σ, ∃! t, U.SameK (k := k) σ t) ∧ ∀ t, ∃! σ, U.SameK (k := k) σ t := by
  intro R _ _ I D A G _ _ U k
  have h₀ : IsIso (TFK (R := R) (FractionRing R)).hom := by
    show IsIso (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (FractionRing R))))
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    infer_instance
  have h₁ : IsIso (snd (TFK (R := R) (FractionRing R)) A.A).left :=
    inferInstanceAs (IsIso (pullback.snd (TFK (R := R) (FractionRing R)).hom A.A.hom))
  have h₂ : IsIso U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.hom))
  exact bijective_of_iso A.isLB U.P.L.isLB U.gen.hom.left (pullback.fst G.hom (jK R))
    (snd (TFK (R := R) (FractionRing R)) A.A).left U.wA U.wA_gen k (fun σ t => U.SameK (k := k) σ t)
    (fun _ _ => Iff.rfl)

end GlobalTheory.GenericFibreSections
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiMulPsiOfAdditionFirstVariable
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory
namespace FirstSlot
variable {R : Type} [CommRing R] [IsDomain R]

theorem cT_add (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (a b : D.X) :
    cT D T (a + b) = cT D T a * cT D T b := by
  rw [cT, D.c_add]
  exact MonObj.comp_mul _ _ _

theorem comp_cT (D : DegPre R) {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T) (a : D.X) :
    ρ ≫ cT D T a = cT D T' a := by
  rw [cT, cT, ← Category.assoc, toUnit_unique (ρ ≫ toUnit T) (toUnit T')]

theorem kapV_one (D : DegPre R) (a b : D.X) {T : Over (Spec (CommRingCat.of R))} {z : T.left}
    {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (x : T ⟶ D.P.A) :
    kapV D a b z J x 1 = (val D.sym (1 : T ⟶ D.P.A).left z J)⁻¹ * rigV D z J ^ 2 *
      cubV D.cub z J (cT D T a) (cT D T b) x := by
  have h := isCub_cubV D.cub (T := T) (z := z) (J := J) hJ
  rw [kapV, kap0, inv_one]
  simp only [h.face₃, _root_.mul_one, _root_.one_mul, inv_one]
  rfl

theorem compare (D : DegPre R) (T₀ : Over (Spec (CommRingCat.of R))) (s₀ : ∀ α, SecBT D T₀ 1 α) (r : R) {n : ℕ}
    (s s' : Fin n → ∀ α, SecBT D T₀ 2 α) (hA : AddB D T₀ s₀ r s s') (hP : PsiRel D T₀ s₀) (a b mu : D.X)
    (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ T₀) (κ : T ⟶ TK R) (x : T ⟶ D.P.A) (z : T.left) (J)
    (hJ : Good D.P.L z J) [IsDomain (T.left.presheaf.stalk z)] (hr : gs (𝟙 _) z ⊤ (scal T.hom r) ≠ 0)
    (h0 : ∀ χ, sval (s₀ 0) (lift ρ (x * cT D T χ)).left z J ≠ 0) (C U : T.left.presheaf.stalk z)
    (hs : ∀ i, sval (s i (a + b + 2 • mu)) (lift ρ x).left z J =
      C * (sval (s i (a + b)) (lift ρ (x * cT D T mu)).left z J * U)) :
    (cubV D.cub z J (cT D T (a + mu)) (cT D T (b + mu)) x).val *
        ((val (D.psi (a + mu)) κ.left z J).val * (val (D.psi (b + mu)) κ.left z J).val) =
      C * (U * (cubV D.cub z J (cT D T a) (cT D T b) (x * cT D T mu)).val * (val (D.psi a) κ.left z J).val *
        (val (D.psi b) κ.left z J).val) := by
  have e₁ := (hA T ρ x 1 z J hJ).1 (a + mu) (b + mu) (a + b + 2 • mu) (a - b) (by rw [two_smul]; abel) (by abel)
  have e₂ := (hA T ρ (x * cT D T mu) 1 z J hJ).1 a b (a + b) (a - b) rfl rfl
  rw [kapV_one D _ _ hJ, inv_one, _root_.mul_one x, hP _ T ρ κ _ z J hJ, hP (b + mu) T ρ κ _ z J hJ] at e₁
  rw [kapV_one D _ _ hJ, inv_one, _root_.mul_one (x * cT D T mu), hP _ T ρ κ _ z J hJ, hP b T ρ κ _ z J hJ,
    _root_.mul_assoc x, _root_.mul_assoc x, ← cT_add, ← cT_add, add_comm mu a, add_comm mu b] at e₂
  have e₃ : ∑ i, sval (s i (a + b + 2 • mu)) (lift ρ x).left z J * sval (s' i (a - b)) (lift ρ 1).left z J =
      C * U * ∑ i, sval (s i (a + b)) (lift ρ (x * cT D T mu)).left z J * sval (s' i (a - b)) (lift ρ 1).left z J := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hs i]; ring
  rw [e₁, e₂] at e₃
  have hne : gs (𝟙 _) z ⊤ (scal T.hom r) * ((val D.sym (1 : T ⟶ D.P.A).left z J)⁻¹ * rigV D z J ^ 2).val *
      (rigV D z J).val * (rigV D z J).val * sval (s₀ 0) (lift ρ (x * cT D T (a + mu))).left z J *
      sval (s₀ 0) (lift ρ (x * cT D T (b + mu))).left z J ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hr (Units.ne_zero _)) (Units.ne_zero _))
      (Units.ne_zero _)) (h0 _)) (h0 _)
  refine mul_left_cancel₀ hne ?_
  simp only [Units.val_mul] at e₃ ⊢
  linear_combination e₃

theorem gs_scal_ne_zero {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of (FractionRing R))) (z : Y) {r : R}
    (hr : r ≠ 0) : gs (𝟙 _) z ⊤ (scal (q ≫ jK R) r) ≠ 0 := by
  have h2 : ((jK R).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) r) := by
    have e := congrArg (fun φ => φ.hom r)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
    exact e.symm
  have h3 : scal (q ≫ jK R) r = scal q (algebraMap R (FractionRing R) r) := congrArg q.appTop.hom h2
  have hu : IsUnit (algebraMap R (FractionRing R) r) :=
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr)
  rw [h3, gs_eq _ z ⊤ trivial]
  exact ((((hu.map _).map q.appTop.hom).map _).map _).ne_zero

theorem isIso_transl (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (χ : D.X) :
    IsIso (lift (fst T D.P.A) (snd T D.P.A * cT D (T ⊗ D.P.A) χ)) := by
  refine ⟨lift (fst T D.P.A) (snd T D.P.A * (cT D (T ⊗ D.P.A) χ)⁻¹), ?_, ?_⟩
  · ext
    · simp
    · rw [Category.assoc, lift_snd, MonObj.comp_mul, GrpObj.comp_inv, lift_snd, comp_cT, mul_inv_cancel_right,
        Category.id_comp]
  · ext
    · simp
    · rw [Category.assoc, lift_snd, MonObj.comp_mul, lift_snd, comp_cT, inv_mul_cancel_right, Category.id_comp]

end FirstSlot


open FirstSlot in
theorem psi_mul_psi_of_addition_first_variable : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (s₀ : Raw D F 1) (r : R) (n : ℕ) (s s' : Fin n → Raw D F 2), r ≠ 0 → AddB D (TF (R := R) F) s₀ r s s' → PsiRel D (TF (R := R) F) s₀ → (∃ j, (s₀ 0).f j ≠ 0) → ∀ (a b mu α : D.X), α = a + b → ∀ (c : F) (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F 2 α mu) (DegPre.deltaε 2))), (∀ i z J, Good D.P.L z J → sval (s i (α + 2 • mu)) (𝟙 _) z J = gs (𝟙 _) z ⊤ (DegPre.constBF D F c ⊤) * (sval (s i α) (DegPre.trF D F mu).left z J * (val u (𝟙 _) z J).val)) → ∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → (val (Z := (TF (R := R) F).left) (D.psi (a + mu)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (b + mu)) (jFK (R := R) F) z J).val = gs (𝟙 (TF (R := R) F).left) z ⊤ (scal (Y := (TF (R := R) F).left) (𝟙 (Spec (CommRingCat.of F))) c) * (val u (DegPre.zF D F).left z J * cubV D.cub z J (cT D _ a) (cT D _ b) (cT D _ mu) * val (Z := (TF (R := R) F).left) (D.psi (a)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (b)) (jFK (R := R) F) z J).val := by
  intro R _ _ D F _ _ s₀ r n s s' hr hA hP h0 a b mu α hα c u hs z J hJ
  subst hα
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsIntegral (TF (R := R) F).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  have hint : IsIntegral (DegPre.BF D F).left := isIntegral_tensor_left_of_smooth_grpObj _ D.P.A (TF (R := R) F)
  let κF : TF (R := R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl
  have zf : DegPre.zF D F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have zs : DegPre.zF D F ≫ snd _ _ = 1 := lift_snd _ _
  have zκ : (DegPre.zF D F).left ≫ (fst (TF (R := R) F) D.P.A ≫ κF).left = jFK (R := R) F := by
    rw [← Over.comp_left, ← Category.assoc, zf, Category.id_comp]; rfl
  have hJ' : Good D.P.L ((DegPre.zF D F).left z) (fun ψ => J ((DegPre.zF D F).left ≫ ψ)) := fun ψ => hJ _
  have hhom : (DegPre.BF D F).hom = (fst (TF (R := R) F) D.P.A ≫ κF).left ≫ jK R :=
    (Over.w (fst (TF (R := R) F) D.P.A ≫ κF)).symm
  have key := FirstSlot.compare D (TF (R := R) F) s₀ r s s' hA hP a b mu (DegPre.BF D F) (fst _ _) (fst _ _ ≫ κF)
    (snd _ _) ((DegPre.zF D F).left z) _ hJ' (by rw [hhom]; exact gs_scal_ne_zero _ _ hr)
    (fun χ => by
      have := isIso_transl D (TF (R := R) F) χ
      have : IsIso (lift (fst (TF (R := R) F) D.P.A) (snd _ _ * cT D (DegPre.BF D F) χ)).left :=
        (Over.forget _).map_isIso (lift (fst (TF (R := R) F) D.P.A) (snd _ _ * cT D (TF (R := R) F ⊗ D.P.A) χ))
      exact sval_ne_zero_of_isIso _ _ D.P.L D.P.isLB _ _ _ (s₀ 0) h0 _ _ _ _ hJ')
    _ _ (fun i => by
      rw [lift_fst_snd]
      exact hs i _ _ hJ')
  have ψn : ∀ χ, ((DegPre.zF D F).left.stalkMap z).hom (val (D.psi χ) (fst (TF (R := R) F) D.P.A ≫ κF).left
      ((DegPre.zF D F).left z) (fun ψ => J ((DegPre.zF D F).left ≫ ψ))).val =
      (val (Z := (TF (R := R) F).left) (D.psi χ) (jFK (R := R) F) z J).val := fun χ => by
    rw [← zκ]
    exact ((values_natural _ _ _ _ D.P.L _ _ _ _ _ z J hJ).2.2.1 (D.psi χ)).symm
  have cn : ∀ x x' y : DegPre.BF D F ⟶ D.P.A, ((DegPre.zF D F).left.stalkMap z).hom (cubV D.cub
      ((DegPre.zF D F).left z) (fun ψ => J ((DegPre.zF D F).left ≫ ψ)) x x' y).val =
      (cubV D.cub z J (DegPre.zF D F ≫ x) (DegPre.zF D F ≫ x') (DegPre.zF D F ≫ y)).val := fun x x' y => by
    refine ((values_natural _ _ _ _ D.P.L _ _ _ _ _ z J hJ).2.2.1 D.cub.t).symm.trans ?_
    rw [← Over.comp_left, comp_lift, comp_lift]; rfl
  have un : ((DegPre.zF D F).left.stalkMap z).hom (val u (𝟙 _)
      ((DegPre.zF D F).left z) (fun ψ => J ((DegPre.zF D F).left ≫ ψ))).val =
      (val u (DegPre.zF D F).left z J).val := by
    refine ((values_natural _ _ _ _ D.P.L _ _ _ _ _ z J hJ).2.2.1 u).symm.trans ?_
    rw [Category.comp_id]
  have kn : ((DegPre.zF D F).left.stalkMap z).hom (gs (𝟙 _) ((DegPre.zF D F).left z) ⊤ (DegPre.constBF D F c ⊤)) =
      gs (𝟙 (TF (R := R) F).left) z ⊤ (scal (Y := (TF (R := R) F).left) (𝟙 (Spec (CommRingCat.of F))) c) := by
    refine (gs_comp_stalkMap (𝟙 _) (DegPre.zF D F).left z ⊤ trivial _).symm.trans ?_
    refine (gs_res ((DegPre.zF D F).left ≫ 𝟙 _) z (U := ⊤) (V := ⊤) le_top trivial _).trans ?_
    refine (gs_pull ((DegPre.zF D F).left ≫ 𝟙 _) (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _).trans ?_
    rw [Category.comp_id, ← Over.comp_left, zf]
    rfl
  have k2 := congrArg ((DegPre.zF D F).left.stalkMap z).hom key
  simp only [map_mul] at k2
  rw [ψn, ψn, ψn, ψn, cn, cn, un, kn, MonObj.comp_mul, zs, comp_cT, comp_cT, comp_cT, comp_cT, comp_cT,
    _root_.one_mul, (isCub_cubV D.cub (T := TF (R := R) F) (z := z) (J := J) hJ).face₃, Units.val_one,
    _root_.one_mul] at k2
  simp only [Units.val_mul]
  exact k2

end GlobalTheory
end
