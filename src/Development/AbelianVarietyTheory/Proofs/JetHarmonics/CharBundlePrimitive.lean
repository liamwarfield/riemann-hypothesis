module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyGtCoordOfIsGt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CharBundlePrimitive
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusModel

open CoordToExt

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

abbrev charBundle (χ : D.X) : LB D.P.A.left := LB.LinComb D.P.L (D.Oφ (𝟙 D.P.A) χ) Oε

theorem comp_Oφ_id {T : Over (Spec (CommRingCat.of R))} (x : T ⟶ D.P.A) (χ : D.X) (k : Fin 4) :
    x.left ≫ D.Oφ (𝟙 D.P.A) χ k = D.Oφ x χ k :=
  (WeightPf.Oφ_comp x (𝟙 _) χ k).trans (by rw [Category.comp_id])

theorem charBundle_rig (χ : D.X) : ∃ t : LB.Gen ((charBundle D χ).pull (eSec D.P.A)), t.IsGen := by
  refine ((refines_self _ _).linComb (fun _ : PUnit => eSec D.P.A) (fun _ => 1)).exists_gen D.P.isLB
    (fun U _ h => ?_) _ isGen_one
  refine (Fintype.prod_empty _).trans (Eq.symm ?_)
  have e : (η[D.P.A] : 𝟙_ _ ⟶ D.P.A) = 1 := by simp [Hom.one_def]
  rw [Fintype.prod_prod_type, Fintype.prod_unique]
  simp only [_root_.mul_one, eSec, comp_Oφ_id]
  refine (prod_O D η[D.P.A] χ h).trans ?_
  rw [e, _root_.mul_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem charBundle_add (χ χ' : D.X) :
    ∃ t : LB.Iso (charBundle D χ') (LB.div (charBundle D (χ + χ')) (charBundle D χ)), t.IsGen := by
  refine (((refines_self _ _).div (refines_self _ _)).div (refines_self _ _)).exists_gen D.P.isLB (fun U _ h => ?_)
    _ (DVR.pullGen_isGen _ _ _ _ D.cub.isGen (lift (toUnit _ ≫ D.c χ) (lift (toUnit _ ≫ D.c χ') (𝟙 D.P.A))).left)
  refine (prod_cub (toUnit _ ≫ D.c χ) (toUnit _ ≫ D.c χ') (𝟙 D.P.A) h).trans (Eq.symm ?_)
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  refine (congrArg₂ (· * ·) (congrArg₂ (· * ·) (prod_O D (𝟙 D.P.A) _ h) (congrArg (·⁻¹) (prod_O D (𝟙 D.P.A) _ h)))
    (congrArg (·⁻¹) (prod_O D (𝟙 D.P.A) _ h))).trans ?_
  rw [c_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem charBundle_zero : ∃ t : LB.Gen (charBundle D 0), t.IsGen := by
  refine (refines_self _ _).exists_gen D.P.isLB (fun U _ h => ?_) _ isGen_one
  refine (Fintype.prod_empty _).trans (Eq.symm ((prod_O D (𝟙 D.P.A) _ h).trans ?_))
  rw [c_zero, _root_.one_mul]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem charBundle_primitive (χ : D.X) : ∃ t : LB.Gen (abelian₂ D.P.A (charBundle D χ)), t.IsGen := by
  refine ((refines_self _ _).linComb _ _).exists_gen D.P.isLB (fun U _ h => ?_)
    _ (DVR.pullGen_isGen _ _ _ _ D.cub.isGen (lift (toUnit _ ≫ D.c χ) (lift (x2 D.P.A 0) (x2 D.P.A 1))).left)
  refine (prod_cub (toUnit _ ≫ D.c χ) (x2 D.P.A 0) (x2 D.P.A 1) h).trans (Eq.symm ?_)
  rw [Fintype.prod_prod_type]
  simp only [zpow_mul, Finset.prod_zpow, comp_Oφ_id]
  refine (prod_square (x2 D.P.A) (fun x => ∏ k, h (D.Oφ x χ k) ^ Oε k)).trans ?_
  refine (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (prod_O D _ _ h) (congrArg (·⁻¹) (prod_O D _ _ h)))
    (congrArg (·⁻¹) (prod_O D _ _ h))) (prod_O D _ _ h)).trans ?_
  rw [_root_.mul_one, ← _root_.mul_assoc (toUnit _ ≫ D.c χ)]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

def splitExt : SplitExt (Spec (CommRingCat.of R)) where
  B := D.P.A
  isAbelian := D.P.isAb
  X := D.X
  O χ := ⟨charBundle D χ, (charBundle_rig D χ).choose, DVR.linComb_isLB _ D.P.isLB _ _,
    (charBundle_rig D χ).choose_spec⟩
  addIso := charBundle_add D
  zeroTriv := charBundle_zero D
  primitive := charBundle_primitive D

variable {D} {H : Over (Spec (CommRingCat.of R))} [GrpObj H] [IsCommMonObj H]

theorem nonempty_gtCoord (hG : GlobalFnsSt) (h : (splitExt D).IsGt H) (I : Ideal R) (e : ℕ) :
    Nonempty (GtCoord I D e H) := by
  obtain ⟨d⟩ := h
  refine nonempty_gtCoord_of_isGt hG R I D e H (GtBaseChange.extBC (thick R I e) (splitExt D)) (Iso.refl _)
    (AddEquiv.refl _) (inferInstanceAs (IsMonHom (𝟙 (thickObj R I e D.P.A)))) (fun χ => ?_)
    (GtBaseChange.isGt_extBC _ _ H d)
  refine ((refines_self _ _).div ((refines_self (D.Oφ (𝟙 D.P.A) χ) Oε).linComb
    (fun _ : PUnit => pullback.fst D.P.A.hom (thick R I e)) (fun _ => 1))).exists_gen D.P.isLB
    (fun U _ h => ?_) _ isGen_one
  refine (Fintype.prod_empty _).trans (Eq.symm ((Fintype.prod_sum_type _).trans ?_))
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rw [Fintype.prod_prod_type, mul_inv_eq_one, eq_comm, Fintype.prod_unique]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [_root_.mul_one]
  have e₀ : ((Over.map (thick R I e)).map (𝟙 (thickObj R I e D.P.A)) ≫ D.prBe I e).left =
      pullback.fst D.P.A.hom (thick R I e) := Category.id_comp _
  exact congrArg (fun q => h (q ≫ D.Oφ (𝟙 D.P.A) χ k) ^ Oε k) e₀.symm

instance isIso_thick_bot : IsIso (thick R ⊥ 0) := by
  have : IsIso (CommRingCat.ofHom (Ideal.Quotient.mk ((⊥ : Ideal R) ^ (0 + 1)))) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (Ideal.Quotient.mk_bijective_iff_eq_bot _ |>.2 (by simp))
  infer_instance

instance isIso_fstG_bot : IsIso (fstG (⊥ : Ideal R) 0 H).left :=
  inferInstanceAs (IsIso (pullback.fst H.hom (thick R ⊥ 0)))

theorem exists_points (hG : GlobalFnsSt) (h : (splitExt D).IsGt H) :
    ∃ Φ : ∀ T, (T ⟶ H) ≃ GtPt D T,
      (∀ (T' T : Over (Spec (CommRingCat.of R))) (k : T' ⟶ T) (x : T ⟶ H),
        GtPt.IsPull k.left (Φ T x) (Φ T' (k ≫ x))) ∧
      ∀ (T : Over (Spec (CommRingCat.of R))) (x x' : T ⟶ H), GtPt.IsAdd (Φ T x) (Φ T x') (Φ T (x * x')) := by
  obtain ⟨c⟩ := nonempty_gtCoord hG h ⊥ 0
  let j := inv (fstG (⊥ : Ideal R) 0 H).left
  have hj : j ≫ (thickObj R ⊥ 0 H).hom ≫ thick R ⊥ 0 = H.hom :=
    (congrArg (j ≫ ·) (Over.w (fstG (⊥ : Ideal R) 0 H)).symm).trans (IsIso.inv_hom_id_assoc _ _)
  choose φ hφ using fun T (x : T ⟶ H) => TorusCoord.exists_isPointOf c (T := T) (x.left ≫ j)
    (by rw [Category.assoc, hj, Over.w])
  have bij : ∀ T, Function.Bijective (φ T) := fun T => by
    refine ⟨fun x x' e => Over.OverMorphism.ext ((cancel_mono j).1
      ((hφ T x).unique_left c (e ▸ hφ T x'))), fun ξ => ?_⟩
    obtain ⟨y, hy⟩ := TorusCoord.exists_point c (T.hom ≫ inv (thick R ⊥ 0)) (by simp) ξ
    refine ⟨Over.homMk (y ≫ (fstG (⊥ : Ideal R) 0 H).left) ((Category.assoc _ _ _).trans
      ((congrArg (y ≫ ·) (Over.w (fstG (⊥ : Ideal R) 0 H))).trans (hy.comp_hom c))), (hφ T _).unique_right c ?_⟩
    have : (y ≫ (fstG (⊥ : Ideal R) 0 H).left) ≫ j = y := by simp [j]
    exact this.symm ▸ hy
  refine ⟨fun T => Equiv.ofBijective _ (bij T), fun T' T k x => (hφ T x).isPull c ?_, fun T x x' => ?_⟩
  · have := hφ T' (k ≫ x)
    rwa [Over.comp_left, Category.assoc] at this
  · obtain ⟨T, ⟨⟨⟩⟩, s⟩ := T
    change T ⟶ Spec (CommRingCat.of R) at s
    obtain ⟨σ, rfl⟩ : ∃ σ, s = σ ≫ thick R ⊥ 0 := ⟨s ≫ inv (thick R ⊥ 0), by simp⟩
    let Z : Over (Spec (CommRingCat.of (R ⧸ (⊥ : Ideal R) ^ (0 + 1)))) := Over.mk σ
    obtain ⟨a, ha⟩ := FormalPoint.exists_lift_fstG (Z := Z) x
    obtain ⟨a', ha'⟩ := FormalPoint.exists_lift_fstG (Z := Z) x'
    have key : ∀ (b : Z ⟶ thickObj R ⊥ 0 H) (w : (Over.map (thick R ⊥ 0)).obj Z ⟶ H),
        (Over.map (thick R ⊥ 0)).map b ≫ fstG ⊥ 0 H = w → φ _ w = TorusCoord.pointsEquiv c Z b := by
      rintro b _ rfl
      refine ((TorusCoord.toGtPt_eq_iff c b _).2 ?_).symm
      have e : ((Over.map (thick R ⊥ 0)).map b ≫ fstG ⊥ 0 H).left ≫ j = b.left := by
        rw [Over.comp_left, Category.assoc, IsIso.hom_inv_id, Category.comp_id]; rfl
      exact e ▸ hφ _ _
    have e₁ := key a x ha
    have e₂ := key a' x' ha'
    have e₃ := key (a * a') (x * x') (by rw [FormalPoint.map_mul_fstG, ha, ha'])
    have := TorusCoord.isAdd_pointsEquiv c hG a a'
    rw [← e₁, ← e₂, ← e₃] at this
    exact this

end GlobalTheory.TorusModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsShiftedNormalisation
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_shifted_normalisation (k : ℕ) (g : GtPtF D F) (z : D.X) (b' : TF (R := R) F ⟶ D.P.A)
    (hb : b' = g.b * cP D _ z)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))) (hw : w.IsGen) :
    ∃ w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F b') (DegPre.lineε k)), w'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (x : Z) (J), Good D.P.L x J →
        val w' r x J = val (g.s z) r x J ^ k * (val (D.psi z) (r ≫ jFK (R := R) F) x J ^ k *
          val D.rigK (r ≫ jFK (R := R) F) x J ^ k) * val w r x J := by
  obtain ⟨w', hw', hv⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b') (ε' := DegPre.lineε k) (fun U _ h => by
      have a₁ : ∀ χ, jFK (R := R) F ≫ D.xK χ = (cP D (TF (R := R) F) χ).left := fun χ => (Category.assoc _ _ _).symm
      have a₂ : jFK (R := R) F ≫ (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TF (R := R) F ⟶ D.P.A).left :=
        (Category.assoc _ _ _).symm
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₁, a₂]
      rw [Fin.prod_univ_four, Fin.prod_univ_two, Fin.prod_univ_two, hb, mul_comm g.b]
      show h (cP D _ z * g.b).left ^ ((k : ℤ) * (-1 : ℤ)) * h (cP D _ z).left ^ ((k : ℤ) * (1 : ℤ)) *
        h g.b.left ^ ((k : ℤ) * (1 : ℤ)) * h (1 : TF (R := R) F ⟶ D.P.A).left ^ ((k : ℤ) * (-1 : ℤ)) * _ *
        (h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h g.b.left ^ (-(k : ℤ))) =
        h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h (cP D _ z * g.b).left ^ (-(k : ℤ))
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ (g.s z) k)
      (LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ (D.psi z) k)
        (GeneratorPullback.powGen D.P.L _ _ D.rigK k)) (jFK (R := R) F))) w)
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ (g.isGen z) k)
      (pullGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ (D.psi_gen z) k)
        (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _) k)) _)) hw)
  refine ⟨w', hw', fun Z r x J hJ => ?_⟩
  refine (hv Z r x J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (UUA.val_powGen' _ _ _ _ _) ((val_pull hJ _ _ _).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (UUA.val_powGen' _ _ _ _ _) (UUA.val_powGen' _ _ _ _ _)))))) rfl))

theorem phi_value_shift (hG : GlobalFnsSt) (k : ℕ) (g h g' : GtPtF D F) (z : D.X)
    (hι : GtPtF.IsIota z h) (ha : GtPtF.IsAdd g h g')
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k)))
    (w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g'.b) (DegPre.lineε k)))
    (hw' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (x : Z) (J), Good D.P.L x J →
        val w' r x J = val (g.s z) r x J ^ k * (val (D.psi z) (r ≫ jFK (R := R) F) x J ^ k *
          val D.rigK (r ≫ jFK (R := R) F) x J ^ k) * val w r x J)
    (s : Fam D F k) (α : D.X) (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (x : T.left) (J)
    (hJ : Good D.P.L x J) :
    sval (s.s (α + k • z)) (ρ ≫ DegPre.trPt D F g.b).left x J *
      (uVal D F k (α + k • z) g.b ρ x J *
        val (LB.mulGen D.P.L _ _ _ _ (g.s (α + k • z)) w) (ρ ≫ fst _ _).left x J).val =
    sval (s.s α) (ρ ≫ DegPre.trPt D F g'.b).left x J *
      (uVal D F k α g'.b ρ x J * val (LB.mulGen D.P.L _ _ _ _ (g'.s α) w') (ρ ≫ fst _ _).left x J).val := by
  have C : IsCub (th D x J) := isCub_cubV D.cub hJ
  have hh : h.b = cP D _ z := hι.1
  have hb : g'.b = g.b * cP D _ z := ha.1.trans (congrArg (g.b * ·) hh)
  obtain ⟨⟨u, hu, hc⟩, hv'⟩ := gen_fe (D := D) (F := F) hG k z α
  have e := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (s.fe z α u hu hc) _ (ρ ≫ DegPre.trPt D F g.b).left x J hJ
  have htr : (ρ ≫ DegPre.trPt D F g.b) ≫ DegPre.trPt D F (cP D _ z) = ρ ≫ DegPre.trPt D F g'.b := by
    rw [hb, Category.assoc]
    refine congrArg (ρ ≫ ·) ?_
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, tr_fst, tr_fst, tr_fst]
    · have e₁ : (DegPre.trPt D F g.b ≫ DegPre.trPt D F (cP D _ z)) ≫ DegPre.prB D F =
          DegPre.prB D F * (fst _ _ ≫ g.b) * (fst _ _ ≫ cP D _ z) := by
        rw [Category.assoc, tr_pr, MonObj.comp_mul, tr_pr, ← Category.assoc, tr_fst]
      have e₂ : DegPre.trPt D F (g.b * cP D _ z) ≫ DegPre.prB D F =
          DegPre.prB D F * (fst _ _ ≫ g.b) * (fst _ _ ≫ cP D _ z) := by
        rw [tr_pr, MonObj.comp_mul, _root_.mul_assoc]
      exact e₁.trans e₂.symm
  have hf : (ρ ≫ DegPre.trPt D F g.b) ≫ fst (TF (R := R) F) D.P.A = ρ ≫ fst _ _ := by
    rw [Category.assoc, tr_fst]
  have hp : (ρ ≫ DegPre.trPt D F g.b) ≫ DegPre.prB D F = (ρ ≫ DegPre.prB D F) * ((ρ ≫ fst _ _) ≫ g.b) := by
    rw [Category.assoc, tr_pr, MonObj.comp_mul, Category.assoc]
  rw [hv' u hu hc _ (ρ ≫ DegPre.trPt D F g.b) x J hJ, trF_eq, ← Over.comp_left, htr, hf] at e
  rw [e, _root_.mul_assoc, ← Units.val_mul]
  refine congrArg₂ (· * ·) rfl (congrArg Units.val ?_)
  have u1 : uVal D F k α (cP D _ z) (ρ ≫ DegPre.trPt D F g.b) x J =
      hv (th D x J) k (cP D T α) (cP D T z) ((ρ ≫ DegPre.prB D F) * ((ρ ≫ fst _ _) ≫ g.b)) := by
    rw [uVal, hp, ← Category.assoc (ρ ≫ DegPre.trPt D F g.b), hf, comp_cP]; rfl
  have u2 : uVal D F k (α + k • z) g.b ρ x J =
      hv (th D x J) k (cP D T α * cP D T z ^ k) ((ρ ≫ fst _ _) ≫ g.b) (ρ ≫ DegPre.prB D F) := by
    rw [uVal, cPoint_add, cPoint_nsmul, ← Category.assoc ρ]; rfl
  have u3 : uVal D F k α g'.b ρ x J =
      hv (th D x J) k (cP D T α) (cP D T z * ((ρ ≫ fst _ _) ≫ g.b)) (ρ ≫ DegPre.prB D F) := by
    rw [uVal, ← Category.assoc ρ, hb, MonObj.comp_mul, comp_cP, mul_comm (cP D T z)]; rfl
  have hvc := UUA.hv_comp C k (cP D T α) (cP D T z) ((ρ ≫ fst _ _) ≫ g.b) (ρ ≫ DegPre.prB D F)
  have h8 : hv (th D x J) k (cP D T α) (cP D T z) ((ρ ≫ fst _ _) ≫ g.b) =
      cubN (th D x J) k (cP D T α) (cP D T z) ((ρ ≫ fst _ _) ≫ g.b) *
        (th D x J (cP D T α) ((ρ ≫ fst _ _) ≫ g.b) (cP D T z))⁻¹ := rfl
  have t1 := gt_nsmul (ρ ≫ fst _ _) hJ g α z k
  have t2 : val (g'.s α) (ρ ≫ fst _ _).left x J * th D x J (cP D T α) ((ρ ≫ fst _ _) ≫ g.b) (cP D T z) =
      val (g.s α) (ρ ≫ fst _ _).left x J * val (D.tau z α) ((ρ ≫ fst _ _).left ≫ jFK (R := R) F) x J := by
    have e' := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub (ρ ≫ fst _ _) hJ _ _ _))).symm.trans
      ((val_corr hJ (ha.2 α) (ρ ≫ fst _ _).left).trans (val_mul hJ _ _ _))
    have e₂ : (ρ ≫ fst _ _) ≫ DegPre.cF D F α = cP D T α := comp_cP D _ α
    have e₃ : (ρ ≫ fst _ _) ≫ h.b = cP D T z := by rw [hh, comp_cP]
    rw [e₂, e₃] at e'
    exact e'.trans (congrArg₂ (· * ·) rfl ((val_corr hJ (hι.2 α) _).trans (val_pull hJ _ _ _)))
  rw [u1, u2, u3, val_famMult _ hJ, UUA.val_powGen', UUA.val_powGen', val_mul hJ, val_mul hJ, hw' _ _ x J hJ]
  apply Additive.ofMul.injective
  have a1 := congrArg Additive.ofMul hvc
  have a2 := congrArg Additive.ofMul h8
  have a3 := congrArg Additive.ofMul t1
  have a4 := congrArg Additive.ofMul t2
  simp only [ofMul_mul, ofMul_inv] at a1 a2 a3 a4 ⊢
  linear_combination (norm := abel) a1 + a2 + a3 - a4

end

theorem phiRel_of_qkEquiv : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ p p' : QkPt D.toPre F k, QkPt.Equiv D.toPre F p p' → ∀ w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k)), w.IsGen → ∃ w' : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p'.g.b) (DegPre.lineε k)), w'.IsGen ∧ ∀ s t : Fam D.toPre F k, PhiRel D.toPre F k p w s t ↔ PhiRel D.toPre F k p' w' s t := by
  intro hL V _ _ _ D F _ _ k _ p p' ⟨z, hy, h, hι, ha⟩ w hw
  have hG := hL.globalFns
  obtain ⟨w', hw', hv⟩ := exists_shifted_normalisation k p.g z p'.g.b
    (ha.1.trans (congrArg (p.g.b * ·) hι.1)) w hw
  refine ⟨w', hw', fun s t => ?_⟩
  rw [phiRel_iff hG p w hw, phiRel_iff hG p' w' hw']
  constructor
  · intro H α β hβ T ρ x J hJ
    rw [← phi_value_shift hG k p.g h p'.g z hι ha w w' hv s α T ρ x J hJ]
    exact H (α + k • z) β (by rw [← hβ, hy]; abel) T ρ x J hJ
  · intro H α β hβ T ρ x J hJ
    obtain ⟨α, rfl⟩ : ∃ α', α' + k • z = α := ⟨α - k • z, sub_add_cancel _ _⟩
    rw [phi_value_shift hG k p.g h p'.g z hι ha w w' hv s α T ρ x J hJ]
    exact H α β (by rw [← hβ, hy]; abel) T ρ x J hJ

end GlobalTheory
end
end
