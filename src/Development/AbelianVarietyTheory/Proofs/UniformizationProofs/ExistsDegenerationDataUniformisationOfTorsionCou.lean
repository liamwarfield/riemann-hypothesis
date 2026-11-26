module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniformisationDataBeforeChoice
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaSectionSupportEqUniv
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifAssembly

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDegenerationDataFunctionalEquationDegreeOn
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BimultiplicativeTauOfThetaExpansionPsiRelation
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiZeroMulRigV
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem psi_zero_mul_rigV : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (s₀ : Raw D F 1), PsiRel D (TF (R := R) F) s₀ → (∃ j, (s₀ 0).f j ≠ 0) → ∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → val (Z := (TF (R := R) F).left) (D.psi (0)) (jFK (R := R) F) z J * rigV D z J = 1 := by
  intro R _ _ D F _ _ s₀ H hs z J hJ
  have hc : cT D (DegPre.BF D F) 0 = 1 := by
    have h := DVR.cPoint_add D (DegPre.BF D F) 0 0
    rw [add_zero] at h
    exact mul_eq_left.1 h.symm
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsIntegral (TF (R := R) F).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  have : IsIntegral (DegPre.BF D F).left :=
    isIntegral_tensor_left_of_smooth_grpObj _ D.P.A (TF (R := R) F)
  let ζ : (TF (R := R) F).left ⟶ (DegPre.BF D F).left := (DegPre.zF D F).left
  let p : DegPre.BF D F ⟶ TF (R := R) F := fst _ _
  have hζ : ζ ≫ p.left = 𝟙 _ := by
    show (DegPre.zF D F ≫ p).left = _
    rw [show DegPre.zF D F ≫ p = 𝟙 _ from lift_fst _ _]
    rfl
  let κ₀ : TF (R := R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl
  let J' : ((DegPre.BF D F).left ⟶ D.P.A.left) → D.P.L.ι := fun ψ => J (ζ ≫ ψ)
  have hJ' : Good D.P.L (ζ z) J' := fun ψ => hJ (ζ ≫ ψ)
  have e := H 0 (DegPre.BF D F) p (p ≫ κ₀) (snd _ _) (ζ z) J' hJ'
  rw [hc, _root_.mul_one, show lift p (snd _ _) = 𝟙 (DegPre.BF D F) from lift_fst_snd] at e
  have hne : sval (s₀ 0) (𝟙 (DegPre.BF D F).left) (ζ z) J' ≠ 0 :=
    sval_ne_zero_of_isIso _ _ D.P.L D.P.isLB _ _ _ (s₀ 0) hs _ (𝟙 _) (ζ z) J' hJ'
  have e1 : (val (D.psi 0) (p ≫ κ₀).left (ζ z) J' * rigV D (ζ z) J').val = 1 :=
    (mul_eq_right₀ hne).1 e.symm
  have n1 := (values_natural _ _ _ _ D.P.L _ _ _ (p ≫ κ₀).left ζ z J hJ).2.2.1 (D.psi 0)
  have n2 := (values_natural _ _ _ _ D.P.L PUnit (fun _ => eSec D.P.A) (fun _ => 1)
    (DegPre.BF D F).hom ζ z J hJ).2.2.1 D.rig
  have a1 : ζ ≫ (p ≫ κ₀).left = jFK (R := R) F := by
    show ζ ≫ p.left ≫ jFK (R := R) F = _
    rw [← Category.assoc, hζ, Category.id_comp]
  have a2 : ζ ≫ (DegPre.BF D F).hom = (TF (R := R) F).hom := Over.w (DegPre.zF D F)
  rw [a1] at n1
  rw [a2] at n2
  apply Units.ext
  have e2 := congrArg (ζ.stalkMap z).hom e1
  rw [map_one, Units.val_mul, map_mul] at e2
  rw [Units.val_mul, Units.val_one]
  exact (congrArg₂ (· * ·) n1 n2).trans e2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BimultiplicativeTauOfThetaExpansionPsiRelation
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem cubeRel_of_two_comparisons {S : Type} [CommRing S] (c : S) (u k k' r pa pb pm p0 pab pam pbm pabm : Sˣ)
    (h₁ : (pam * pbm).val = c * (u * k * pa * pb).val) (h₂ : (pabm * pm).val = c * (u * k' * pab * p0).val)
    (hk : k' = 1) (h₀ : p0 * r = 1) : pabm * pa * pb * pm * r * k = pab * pam * pbm := by
  subst hk
  have h0 : (p0 : S) * r = 1 := by rw [← Units.val_mul, h₀, Units.val_one]
  ext
  simp only [Units.val_mul, Units.val_one] at h₁ h₂ ⊢
  linear_combination ((pa : S) * pb * k * r) * h₂ + (c * u * pab * pa * pb * k) * h0 - (pab : S) * h₁

theorem tauBimult_of_psiRel : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → PsiRel D (𝟙_ _) f → D.TauBimult) := by
  intro hL hL2 V _ _ _ hV D A G _ _ U θ f hθ hψ
  have hG : GlobalFnsSt := hL.globalFns
  obtain ⟨th, hth, -⟩ := (GlobalTheory.UU.PullSec.pullEx V hV D A G U (Kbar V) (𝟙_ _) (toUnit _) 1).1 θ
  obtain ⟨s₀, hs₀, -⟩ := (GlobalTheory.UU.PullSec.pullEx V hV D A G U (Kbar V) (𝟙_ _) (toUnit _) 1).2 f
  obtain ⟨r, n, t, t', s, s', hr, hexp, -, hadd⟩ := GlobalTheory.T.additionFormula_algClosure_with_expansions hL hL2 V hV D A G U θ f hθ th s₀ hth hs₀
  have hP : PsiRel D (TF (R := V) (Kbar V)) s₀ := psiRel_of_pullB V D (Kbar V) f s₀ hs₀ hψ
  obtain ⟨hf, hsupp⟩ := GlobalTheory.T.thetaSection_support_eq_univ hL hL2 V hV D A G U θ f hθ
  have hne : ∃ j, (s₀ 0).f j ≠ 0 := (pullB_ne_zero_iff V D (Kbar V) 1 f s₀ hs₀ 0).2 (hf 0)
  refine (GlobalTheory.T.tau_bimult_psi_even_over_extension_field V D (Kbar V)).1.1 ?_
  intro z J hJ a b m
  obtain ⟨⟨u, hu, -⟩, -⟩ := ReciprocityTheory.ChartRestriction.G.DVR.gen_fe (D := D) (F := Kbar V) hG 2 m (a + b)
  obtain ⟨c, hc⟩ := GlobalTheory.T.expansionComponents_proportional_shift_multiple hL hL2 V hV D A G U 2 (by norm_num) (a + b) m u hu (hsupp (a + b))
  have hs : ∀ i z J, Good D.P.L z J → sval (s i (a + b + 2 • m)) (𝟙 _) z J =
      gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) c ⊤) *
        (sval (s i (a + b)) (DegPre.trF D (Kbar V) m).left z J * (val u (𝟙 _) z J).val) :=
    fun i => hc (t i) (s i) (hexp i).1
  have h₁ := psi_mul_psi_of_addition_first_variable V D (Kbar V) s₀ r n s s' hr hadd hP hne a b m (a + b) rfl c u hs z J hJ
  have h₂ := psi_mul_psi_of_addition_first_variable V D (Kbar V) s₀ r n s s' hr hadd hP hne (a + b) 0 m (a + b)
    (add_zero _).symm c u hs z J hJ
  rw [zero_add] at h₂
  have h₀ := psi_zero_mul_rigV V D (Kbar V) s₀ hP hne z J hJ
  have hc0 : cT D (TF (R := V) (Kbar V)) 0 = 1 := by
    have h := FirstSlot.cT_add D (TF (R := V) (Kbar V)) 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  have hk : cubV D.cub z J (cT D _ (a + b)) (cT D _ 0) (cT D _ m) = 1 := by
    rw [hc0]
    exact (isCub_cubV D.cub hJ).face₂ _ _
  exact cubeRel_of_two_comparisons _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ hk h₀

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BimultiplicativeTauOfThetaExpansionPsiRelationStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bimultiplicative_tau_of_thetaExpansionPsiRelation : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → PsiRel D (𝟙_ _) f → D.TauBimult) := by
  first | exact @GlobalTheory.tauBimult_of_psiRel | exact GlobalTheory.tauBimult_of_psiRel | (intros; apply GlobalTheory.tauBimult_of_psiRel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EvenPsiOfThetaExpansionPsiRelation
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiMulPsiOfAdditionSecondVariable
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiMulPsiOfAdditionSecondVariable
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory
namespace SecondPosition
open FirstSlot
variable {R : Type} [CommRing R] [IsDomain R]

theorem cT_zero (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) : cT D T 0 = 1 := by
  have h := cT_add D T 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem cT_neg (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (a : D.X) : cT D T (-a) = (cT D T a)⁻¹ := by
  have h := cT_add D T a (-a)
  rw [add_neg_cancel, cT_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem val_sym_one (D : DegPre R) {T : Over (Spec (CommRingCat.of R))} {z : T.left}
    {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) :
    val D.sym (1 : T ⟶ D.P.A).left z J = 1 := by
  have a := val_corr hJ D.sym_rig T.hom
  rw [val_one] at a
  refine Eq.trans ?_ ((val_pull hJ _ _ _).symm.trans a)
  congr 1

theorem one_kapV (D : DegPre R) (a b : D.X) {T : Over (Spec (CommRingCat.of R))} {z : T.left}
    {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (y : T ⟶ D.P.A) :
    kapV D a b z J 1 y = (val D.sym y.left z J)⁻¹ * rigV D z J ^ 2 * cubV D.cub z J (cT D T b) y y⁻¹ *
      (cubV D.cub z J (cT D T (a - b)) (cT D T b) y)⁻¹ := by
  have h := isCub_cubV D.cub (T := T) (z := z) (J := J) hJ
  rw [kapV, kap0]
  simp only [h.face₃, h.face₂, h.face, _root_.mul_one, _root_.one_mul]
  rfl

theorem compare (D : DegPre R) (T₀ : Over (Spec (CommRingCat.of R))) (s₀ : ∀ α, SecBT D T₀ 1 α) (r : R) {n : ℕ}
    (s s' : Fin n → ∀ α, SecBT D T₀ 2 α) (hA : AddB D T₀ s₀ r s s') (hP : PsiRel D T₀ s₀) (mu : D.X)
    (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ T₀) (κ : T ⟶ TK R) (y : T ⟶ D.P.A) (z : T.left) (J)
    (hJ : Good D.P.L z J) [IsDomain (T.left.presheaf.stalk z)] (hr : gs (𝟙 _) z ⊤ (scal T.hom r) ≠ 0)
    (h0 : sval (s₀ 0) (lift ρ (y * cT D T mu)).left z J ≠ 0)
    (h0' : sval (s₀ 0) (lift ρ (y⁻¹ * cT D T (-mu))).left z J ≠ 0) (C U : T.left.presheaf.stalk z)
    (hs : ∀ i, sval (s' i (0 + 2 • mu)) (lift ρ y).left z J =
      C * (sval (s' i 0) (lift ρ (y * cT D T mu)).left z J * U)) :
    (cubV D.cub z J (cT D T (-mu)) y y⁻¹).val *
        ((val (D.psi mu) κ.left z J).val * (val (D.psi (-mu)) κ.left z J).val *
          (val D.sym (y * cT D T mu).left z J).val) =
      C * (U * (val (D.psi 0) κ.left z J).val * (val (D.psi 0) κ.left z J).val) *
        ((cubV D.cub z J (cT D T (mu - -mu)) (cT D T (-mu)) y).val * (val D.sym y.left z J).val) := by
  have h := isCub_cubV D.cub (T := T) (z := z) (J := J) hJ
  have e₁ := (hA T ρ 1 y z J hJ).1 mu (-mu) 0 (0 + 2 • mu) (by abel) (by rw [two_smul]; abel)
  have e₂ := (hA T ρ 1 (y * cT D T mu) z J hJ).1 0 0 0 0 (by abel) (by abel)
  rw [one_kapV D _ _ hJ, _root_.one_mul y, _root_.one_mul y⁻¹, hP _ T ρ κ _ z J hJ,
    hP (-mu) T ρ κ _ z J hJ] at e₁
  rw [one_kapV D _ _ hJ, _root_.one_mul (y * cT D T mu), _root_.one_mul (y * cT D T mu)⁻¹, mul_inv y, ← cT_neg,
    hP 0 T ρ κ (y * cT D T mu) z J hJ, hP 0 T ρ κ (y⁻¹ * cT D T (-mu)) z J hJ, cT_zero, h.face, h.face₂,
    _root_.mul_one (y * cT D T mu), _root_.mul_one (y⁻¹ * cT D T (-mu))] at e₂
  have e₃ : ∑ i, sval (s i 0) (lift ρ 1).left z J * sval (s' i (0 + 2 • mu)) (lift ρ y).left z J =
      C * U * ∑ i, sval (s i 0) (lift ρ 1).left z J * sval (s' i 0) (lift ρ (y * cT D T mu)).left z J := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hs i]; ring
  rw [e₁, e₂] at e₃
  generalize val D.sym y.left z J = A at e₃ ⊢
  generalize val D.sym (y * cT D T mu).left z J = B at e₃ ⊢
  generalize cubV D.cub z J (cT D T (mu - -mu)) (cT D T (-mu)) y = E at e₃ ⊢
  have hne : gs (𝟙 _) z ⊤ (scal T.hom r) * (A⁻¹ * B⁻¹ * E⁻¹ * rigV D z J ^ 4).val *
      sval (s₀ 0) (lift ρ (y * cT D T mu)).left z J *
      sval (s₀ 0) (lift ρ (y⁻¹ * cT D T (-mu))).left z J ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hr (Units.ne_zero _)) h0) h0'
  refine mul_left_cancel₀ hne ?_
  have a := A.mul_inv
  have b := B.mul_inv
  have e := E.mul_inv
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, inv_one, Units.val_one] at e₃ ⊢
  generalize gs (𝟙 _) z ⊤ (scal T.hom r) = g at e₃ ⊢
  generalize sval (s₀ 0) (lift ρ (y * cT D T mu)).left z J = p at e₃ ⊢
  generalize sval (s₀ 0) (lift ρ (y⁻¹ * cT D T (-mu))).left z J = q at e₃ ⊢
  generalize (rigV D z J).val = w at e₃ ⊢
  generalize (val (D.psi mu) κ.left z J).val = m at e₃ ⊢
  generalize (val (D.psi (-mu)) κ.left z J).val = m' at e₃ ⊢
  generalize (val (D.psi 0) κ.left z J).val = o at e₃ ⊢
  generalize (cubV D.cub z J (cT D T (-mu)) y y⁻¹).val = k at e₃ ⊢
  linear_combination e₃ + g * A⁻¹.val * E⁻¹.val * w ^ 4 * p * q * k * m * m' * b -
    g * B⁻¹.val * w ^ 4 * p * q * C * U * o * o * (E.val * E⁻¹.val * a + e)

theorem isIso_refl (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (χ : D.X) :
    IsIso (lift (fst T D.P.A) ((snd T D.P.A)⁻¹ * cT D (T ⊗ D.P.A) χ)) := by
  have e : lift (fst T D.P.A) ((snd T D.P.A)⁻¹ * cT D (T ⊗ D.P.A) χ) ≫
      lift (fst T D.P.A) ((snd T D.P.A)⁻¹ * cT D (T ⊗ D.P.A) χ) = 𝟙 _ := by
    ext
    · simp
    · rw [Category.assoc, lift_snd, MonObj.comp_mul, GrpObj.comp_inv, lift_snd, comp_cT, mul_inv, inv_inv,
        inv_mul_cancel_right, Category.id_comp]
  exact ⟨_, e, e⟩

end SecondPosition


open FirstSlot SecondPosition in
theorem psi_mul_psi_of_addition_second_variable : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (s₀ : Raw D F 1) (r : R) (n : ℕ) (s s' : Fin n → Raw D F 2), r ≠ 0 → AddB D (TF (R := R) F) s₀ r s s' → PsiRel D (TF (R := R) F) s₀ → (∃ j, (s₀ 0).f j ≠ 0) → ∀ (mu α : D.X), α = 0 → ∀ (c : F) (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F 2 α mu) (DegPre.deltaε 2))), (∀ i z J, Good D.P.L z J → sval (s' i (α + 2 • mu)) (𝟙 _) z J = gs (𝟙 _) z ⊤ (DegPre.constBF D F c ⊤) * (sval (s' i α) (DegPre.trF D F mu).left z J * (val u (𝟙 _) z J).val)) → ∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → (val (Z := (TF (R := R) F).left) (D.psi (mu)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (-mu)) (jFK (R := R) F) z J * val D.sym (cT D (TF (R := R) F) mu).left z J).val = gs (𝟙 (TF (R := R) F).left) z ⊤ (scal (Y := (TF (R := R) F).left) (𝟙 (Spec (CommRingCat.of F))) c) * (val u (DegPre.zF D F).left z J * val (Z := (TF (R := R) F).left) (D.psi (0)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (0)) (jFK (R := R) F) z J).val := by
  intro R _ _ D F _ _ s₀ r n s s' hr hA hP h0 mu α hα c u hs z J hJ
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
  have key := SecondPosition.compare D (TF (R := R) F) s₀ r s s' hA hP mu (DegPre.BF D F) (fst _ _) (fst _ _ ≫ κF)
    (snd _ _) ((DegPre.zF D F).left z) _ hJ' (by rw [hhom]; exact gs_scal_ne_zero _ _ hr)
    (by
      have := isIso_transl D (TF (R := R) F) mu
      have : IsIso (lift (fst (TF (R := R) F) D.P.A) (snd _ _ * cT D (DegPre.BF D F) mu)).left :=
        (Over.forget _).map_isIso (lift (fst (TF (R := R) F) D.P.A) (snd _ _ * cT D (TF (R := R) F ⊗ D.P.A) mu))
      exact sval_ne_zero_of_isIso _ _ D.P.L D.P.isLB _ _ _ (s₀ 0) h0 _ _ _ _ hJ')
    (by
      have := isIso_refl D (TF (R := R) F) (-mu)
      have : IsIso (lift (fst (TF (R := R) F) D.P.A) ((snd _ _)⁻¹ * cT D (DegPre.BF D F) (-mu))).left :=
        (Over.forget _).map_isIso
          (lift (fst (TF (R := R) F) D.P.A) ((snd _ _)⁻¹ * cT D (TF (R := R) F ⊗ D.P.A) (-mu)))
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
  have sn : ∀ y : DegPre.BF D F ⟶ D.P.A, ((DegPre.zF D F).left.stalkMap z).hom (val D.sym y.left
      ((DegPre.zF D F).left z) (fun ψ => J ((DegPre.zF D F).left ≫ ψ))).val =
      (val D.sym (DegPre.zF D F ≫ y).left z J).val := fun y =>
    ((values_natural _ _ _ _ D.P.L _ _ _ _ _ z J hJ).2.2.1 D.sym).symm
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
  have h := isCub_cubV D.cub (T := TF (R := R) F) (z := z) (J := J) hJ
  have k2 := congrArg ((DegPre.zF D F).left.stalkMap z).hom key
  simp only [map_mul] at k2
  rw [ψn, ψn, ψn, cn, cn, sn, sn, un, kn, MonObj.comp_mul, zs, h.face₂, h.face₃, comp_cT, _root_.one_mul (cT D _ mu),
    val_sym_one D hJ, Units.val_one, _root_.one_mul, _root_.one_mul, _root_.mul_one] at k2
  simp only [Units.val_mul]
  exact k2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiMulPsiOfAdditionSecondVariableStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.psi_mul_psi_addition_second_variable : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (s₀ : Raw D F 1) (r : R) (n : ℕ) (s s' : Fin n → Raw D F 2), r ≠ 0 → AddB D (TF (R := R) F) s₀ r s s' → PsiRel D (TF (R := R) F) s₀ → (∃ j, (s₀ 0).f j ≠ 0) → ∀ (mu α : D.X), α = 0 → ∀ (c : F) (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F 2 α mu) (DegPre.deltaε 2))), (∀ i z J, Good D.P.L z J → sval (s' i (α + 2 • mu)) (𝟙 _) z J = gs (𝟙 _) z ⊤ (DegPre.constBF D F c ⊤) * (sval (s' i α) (DegPre.trF D F mu).left z J * (val u (𝟙 _) z J).val)) → ∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → (val (Z := (TF (R := R) F).left) (D.psi (mu)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (-mu)) (jFK (R := R) F) z J * val D.sym (cT D (TF (R := R) F) mu).left z J).val = gs (𝟙 (TF (R := R) F).left) z ⊤ (scal (Y := (TF (R := R) F).left) (𝟙 (Spec (CommRingCat.of F))) c) * (val u (DegPre.zF D F).left z J * val (Z := (TF (R := R) F).left) (D.psi (0)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (0)) (jFK (R := R) F) z J).val := by
  first | exact @GlobalTheory.psi_mul_psi_of_addition_second_variable | exact GlobalTheory.psi_mul_psi_of_addition_second_variable | (intros; apply GlobalTheory.psi_mul_psi_of_addition_second_variable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EvenPsiOfThetaExpansionPsiRelation
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem psiEven_of_psiRel : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → PsiRel D (𝟙_ _) f → D.PsiEven) := by
  intro hL hL2 V _ _ _ hV D A G _ _ U θ f hθ hψ
  have hG : GlobalFnsSt := hL.globalFns
  obtain ⟨th, hth, -⟩ := GlobalTheory.UU.PullSec.existsUnique_pullG U (Kbar V) (toUnit _) 1 θ
  obtain ⟨s₀, hs₀, -⟩ := GlobalTheory.UU.PullSec.existsUnique_pullB D (Kbar V) (toUnit _) 1 f
  obtain ⟨r, n, t, t', s, s', hr, hE, -, hB⟩ := GlobalTheory.AddClosure.main hL hL2 V hV D A G U θ f hθ th s₀ hth hs₀
  have hP : PsiRel D (TF (R := V) (Kbar V)) s₀ := GlobalTheory.psiRel_of_pullB V D (Kbar V) f s₀ hs₀ hψ
  have hsupp := GlobalTheory.T.thetaSection_support_eq_univ hL hL2 V hV D A G U θ f hθ
  have h0 : ∃ j, (s₀ 0).f j ≠ 0 := (GlobalTheory.pullB_ne_zero_iff V D (Kbar V) 1 f s₀ hs₀ 0).2 (hsupp.1 0)
  rw [← (GlobalTheory.TauValues.main V D (Kbar V)).2]
  intro z J hJ m
  obtain ⟨⟨u, hu, -⟩, -⟩ := ReciprocityTheory.ChartRestriction.G.DVR.gen_fe (D := D) (F := Kbar V) hG 2 m 0
  obtain ⟨a, ha⟩ := GlobalTheory.T.expansionComponents_proportional_shift_multiple hL hL2 V hV D A G U 2 (by norm_num) 0 m u hu (hsupp.2 0)
  have e1 := GlobalTheory.psi_mul_psi_of_addition_first_variable V D (Kbar V) s₀ r n s s' hr hB hP h0 0 0 m 0
    (add_zero 0).symm a u (fun i z J hJ => ha _ _ (hE i).1 z J hJ) z J hJ
  have e2 := GlobalTheory.T.psi_mul_psi_addition_second_variable V D (Kbar V) s₀ r n s s' hr hB hP h0 m 0 rfl a u
    (fun i z J hJ => ha _ _ (hE i).2 z J hJ) z J hJ
  have hc0 : cT D (TF (R := V) (Kbar V)) 0 = 1 := by
    have h := GlobalTheory.FirstSlot.cT_add D (TF (R := V) (Kbar V)) 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  have hcub : cubV D.cub z J (cT D (TF (R := V) (Kbar V)) 0) (cT D (TF (R := V) (Kbar V)) 0)
      (cT D (TF (R := V) (Kbar V)) m) = 1 := by
    rw [hc0]
    exact (isCub_cubV D.cub hJ).face _ _
  simp only [hcub, _root_.mul_one] at e1
  have e4 := Units.ext (e1.trans e2.symm)
  rw [_root_.mul_assoc] at e4
  erw [_root_.zero_add] at e4
  exact (mul_left_cancel e4).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EvenPsiOfThetaExpansionPsiRelationStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.even_psi_of_thetaExpansionPsiRelation : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → PsiRel D (𝟙_ _) f → D.PsiEven) := by
  first | exact @GlobalTheory.psiEven_of_psiRel | exact GlobalTheory.psiEven_of_psiRel | (intros; apply GlobalTheory.psiEven_of_psiRel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaExpansionFunctionalEquationDegreeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaExpansionFunctionalEquationDegreeOne
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU

theorem fe_one_of_psiRel : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → PsiRel D (𝟙_ _) f → U.FE (Kbar V) 1) := by
  intro h₁ h₂ V _ _ _ hV D A G _ _ U θ f hθ hψ t s hts
  obtain ⟨hp, hq⟩ := PullSec.pullEx V hV D A G U (Kbar V) (𝟙_ _) (toUnit _) 1
  obtain ⟨th, hth, -⟩ := hp θ
  obtain ⟨s₀, hs₀, -⟩ := hq f
  obtain ⟨c, hc⟩ := (GlobalTheory.T.expF_of_theta_degree_one h₁ h₂ V hV D A G U θ f hθ th s₀ hth hs₀).2.2 t s hts
  exact famFE_one_of_psiRel h₁.globalFns V D (Kbar V) s₀ s c (GlobalTheory.T.thetaPsiRelation_of_pullback_extension_field V D (Kbar V) f s₀ hs₀ hψ) hc

end GlobalTheory.UU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaExpansionFunctionalEquationDegreeOneStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaExpansion_functionalEquation_degree_one : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → PsiRel D (𝟙_ _) f → U.FE (Kbar V) 1) := by
  first | exact @GlobalTheory.UU.fe_one_of_psiRel | exact GlobalTheory.UU.fe_one_of_psiRel | (intros; apply GlobalTheory.UU.fe_one_of_psiRel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiTendstoZero
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FromSpecStalkComp
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.LevelVanishing

theorem fromSpecStalk_comp {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (z : Y) :
    Y.fromSpecStalk z ≫ p =
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop ≫ Y.presheaf.germ ⊤ z trivial) := by
  rw [Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ, Category.assoc, Category.assoc,
    ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem sval_mem_map {R : Type} [CommRing R] (I : Ideal R) {X Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R))
    {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (d : LB.Sec (LB.LinComb L φ ε))
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y), (∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I)),
      ρ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = r ≫ p) → ∀ (z : Z) (J), Good L z J → sval d r z J = 0)
    (z : Y) (J) (hJ : Good L z J) :
    sval d (𝟙 _) z J ∈ I.map ((Y.presheaf.germ ⊤ z trivial).hom.comp
      ((p.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) := by
  set ψ := (Y.presheaf.germ ⊤ z trivial).hom.comp
      ((p.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) with hψ
  by_cases htop : I.map ψ = ⊤
  · rw [htop]; trivial
  have : Nontrivial (Y.presheaf.stalk z ⧸ I.map ψ) := Ideal.Quotient.nontrivial_iff.2 htop
  have : IsLocalRing (Y.presheaf.stalk z ⧸ I.map ψ) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  let Q : CommRingCat.{0} := CommRingCat.of (Y.presheaf.stalk z ⧸ I.map ψ)
  let q : Y.presheaf.stalk z ⟶ Q := CommRingCat.ofHom (R := Y.presheaf.stalk z) (Ideal.Quotient.mk (I.map ψ))
  have : IsLocalHom q.hom := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let r : Spec Q ⟶ Y := Spec.map q ≫ Y.fromSpecStalk z
  let w : Spec Q := IsLocalRing.closedPoint Q
  have hw : r w = z := by
    rw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  have hl : ∃ ρ : Spec Q ⟶ Spec (CommRingCat.of (R ⧸ I)),
      ρ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = r ≫ p := by
    refine ⟨Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map ψ) ψ Ideal.le_comap_map)), ?_⟩
    rw [Category.assoc, fromSpecStalk_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
  choose I' hI' using fun χ : Spec Q ⟶ X => exists_chart hL (χ w)
  have hz : z ∈ LB.wchart L φ (fun k => J (𝟙 _ ≫ φ k)) := hJ.mem φ (𝟙 _)
  have hm : r w ∈ LB.wchart L φ (fun k => J (𝟙 _ ≫ φ k)) := hw ▸ hz
  have e := sec_trans d r w (j := fun k => J (𝟙 _ ≫ φ k)) hm (Good.mem hI' φ r)
  have e0 : gs r w (LB.wchart L φ (fun k => I' (r ≫ φ k))) (d.f (fun k => I' (r ≫ φ k))) = 0 := H _ r hl w I' hI'
  rw [e0, mul_zero] at e
  replace e := (Scheme.Hom.germ_stalkMap_apply r _ w hm _).trans ((gs_eq r w _ hm _).symm.trans e)
  have e1 := congrArg (fun t => t.hom (d.f (fun k => J (𝟙 _ ≫ φ k))))
    (Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk q _ hm)
  simp only [Scheme.stalkClosedPointTo, CommRingCat.hom_comp, RingHom.comp_apply] at e1
  refine Ideal.Quotient.eq_zero_iff_mem.1 ((congrArg _ (gs_eq (𝟙 Y) z _ hz _)).trans ?_)
  exact e1.symm.trans ((congrArg (stalkClosedPointIso Q).hom.hom e).trans (map_zero _))

theorem main : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (k : ℕ) (σ : U.SecGT (𝟙_ _) k) f, U.ExpT (𝟙_ _) k σ f → ∀ e : ℕ, ∃ s : Finset D.X, ∀ α ∉ s, ∀ (z : (𝟙_ _ ⊗ D.P.A).left) (J), Good D.P.L z J → sval (f α) (𝟙 _) z J ∈ (IsLocalRing.maximalIdeal V ^ (e + 1)).map (((𝟙_ _ ⊗ D.P.A).left.presheaf.germ ⊤ z trivial).hom.comp (((𝟙_ _ ⊗ D.P.A).hom.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom))) := by
  intro V _ _ _ _ D A G _ _ U k σ f h e
  obtain ⟨s, hs⟩ := h e
  refine ⟨s, fun α hα z J hJ => sval_mem_map _ (𝟙_ _ ⊗ D.P.A).hom D.P.isLB (f α) ?_ z J hJ⟩
  refine GlobalTheory.LiftTest.main V _ D e G (U.gt e) (𝟙_ _ ⊗ D.P.A) (snd _ _) _ D.P.L D.P.isLB _ _ _ (f α) ?_
  intro Z x r hr z J hJ
  choose JG hJG using fun χ : Z ⟶ G.left => exists_chart U.P.L.isLB (χ z)
  have hb : r ≫ (𝟙_ _ ⊗ D.P.A).hom = x ≫ (fstG (IsLocalRing.maximalIdeal V) e G).left ≫ G.hom := by
    rw [← Over.w (snd (𝟙_ _) D.P.A), ← Category.assoc, hr, Category.assoc, Over.w, Over.w]
  let xG : Over.mk (r ≫ (𝟙_ _ ⊗ D.P.A).hom) ⟶ G :=
    Over.homMk (x ≫ (fstG (IsLocalRing.maximalIdeal V) e G).left) (by rw [Category.assoc]; exact hb.symm)
  let rB : Over.mk (r ≫ (𝟙_ _ ⊗ D.P.A).hom) ⟶ 𝟙_ _ ⊗ D.P.A := Over.homMk r
  refine (hs Z x (lift (rB ≫ fst _ _) xG).left r ?_ hr ?_ z JG J hJG hJ).1 α hα
  · exact congrArg CommaMorphism.left (lift_snd (rB ≫ fst _ _) xG)
  · exact (congrArg CommaMorphism.left (lift_fst (rB ≫ fst _ _) xG)).symm

end GlobalTheory.LevelVanishing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsOrderTranslates
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem stalkMap_mem_map_base {R : Type} [CommRing R] (I : Ideal R) {Z Z' : Scheme.{0}}
    (p : Z ⟶ Spec (CommRingCat.of R)) (p' : Z' ⟶ Spec (CommRingCat.of R)) (ρ : Z' ⟶ Z) (h : ρ ≫ p = p') (z : Z')
    (a : Z.presheaf.stalk (ρ z))
    (ha : a ∈ I.map ((Z.presheaf.germ ⊤ (ρ z) trivial).hom.comp
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom))) :
    (ρ.stalkMap z).hom a ∈ I.map ((Z'.presheaf.germ ⊤ z trivial).hom.comp
      (p'.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) := by
  subst h
  have := Ideal.mem_map_of_mem (ρ.stalkMap z).hom ha
  rw [Ideal.map_map] at this
  convert this using 2
  ext r
  exact (Scheme.Hom.germ_stalkMap_apply ρ ⊤ z trivial _).symm

theorem map_base_eq_bot {R : Type} [CommRing R] (I : Ideal R) {Z : Scheme.{0}}
    (ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I))) (z : Z) :
    I.map ((Z.presheaf.germ ⊤ z trivial).hom.comp
      ((ρ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) = ⊥ := by
  rw [Ideal.map_eq_bot_iff_le_ker]
  intro r hr
  have e := congrArg (fun q => q.hom r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk I)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero] at e
  rw [RingHom.mem_ker, Scheme.Hom.comp_appTop]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  erw [← e]
  simp only [map_zero]

theorem exists_order_translates : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegPre V) (k : ℕ) (f₀ : SecBT D (𝟙_ _) k 0), (∃ j, f₀.f j ≠ 0) → ∃ m : ℕ, ∀ χ : D.X, ∃ (z : (𝟙_ _ ⊗ D.P.A).left) (J : _), Good D.P.L z J ∧ sval f₀ (lift (fst (𝟙_ _) D.P.A) (snd (𝟙_ _) D.P.A * cT D _ χ)).left z J ∉ (IsLocalRing.maximalIdeal V ^ (m + 1)).map (((𝟙_ _ ⊗ D.P.A).left.presheaf.germ ⊤ z trivial).hom.comp (((𝟙_ _ ⊗ D.P.A).hom.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)) := by
  intro V _ _ _ hV D k f₀ ⟨j, hj⟩
  haveI := hV.1
  haveI := D.P.isAb.smooth
  haveI := D.P.isAb.geomConnected
  haveI : IsAffine (𝟙_ (Over (Spec (CommRingCat.of V)))).left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of V)))
  haveI : IsNoetherianRing Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤) :=
    isNoetherianRing_of_ringEquiv V (Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.symm
  obtain ⟨m, z₀, J₀, hJ₀, h₀⟩ : ∃ (m : ℕ) (z : (𝟙_ _ ⊗ D.P.A).left) (J : _), Good D.P.L z J ∧
      sval f₀ (𝟙 _) z J ∉ (IsLocalRing.maximalIdeal V ^ (m + 1)).map (((𝟙_ _ ⊗ D.P.A).left.presheaf.germ ⊤ z trivial).hom.comp (((𝟙_ _ ⊗ D.P.A).hom.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)) := by
    by_contra hc
    push Not at hc
    refine hj (sec_eq_zero_of_sval_finite_level V (IsLocalRing.maximalIdeal V) (𝟙_ _) D.P.A ?_ _ D.P.L D.P.isLB
      _ _ _ f₀ ?_ j)
    · intro r hr
      let e : V ≃+* Γ(Spec (CommRingCat.of V), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.symm
      have h1 : r ∈ Ideal.jacobson (⊥ : Ideal V) := by
        rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      have h2 := Ideal.mem_map_of_mem e.toRingHom h1
      rw [Ideal.map_jacobson_of_bijective (f := e.toRingHom) e.bijective, Ideal.map_bot] at h2
      exact h2
    · rintro e Z r ⟨ρ, hρ⟩ z J hJ
      obtain ⟨g, hs, -⟩ := values_natural _ _ _ _ D.P.L _ (famφT D (𝟙_ _) 0) (DegPre.famε k) (𝟙 _) r z J hJ
      have h1 := stalkMap_mem_map_base _ _ _ r hρ.symm z _ (hc e _ _ g)
      rw [← hs f₀, Category.comp_id, map_base_eq_bot] at h1
      exact h1
  refine ⟨m, fun χ => ?_⟩
  let σ : 𝟙_ _ ⊗ D.P.A ⟶ 𝟙_ _ ⊗ D.P.A := lift (fst (𝟙_ _) D.P.A) (snd (𝟙_ _) D.P.A * (cT D _ χ)⁻¹)
  let τ : 𝟙_ _ ⊗ D.P.A ⟶ 𝟙_ _ ⊗ D.P.A := lift (fst (𝟙_ _) D.P.A) (snd (𝟙_ _) D.P.A * cT D _ χ)
  have hστ : σ ≫ τ = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · exact toUnit_unique _ _
    · have : σ ≫ cT D _ χ = cT D _ χ := by
        rw [cT, ← Category.assoc, toUnit_unique (σ ≫ toUnit _) (toUnit _)]
      rw [Category.assoc, lift_snd, MonObj.comp_mul, this, lift_snd, inv_mul_cancel_right, Category.id_comp]
  obtain ⟨g, hs, -⟩ := values_natural _ _ _ _ D.P.L _ (famφT D (𝟙_ _) 0) (DegPre.famε k) τ.left σ.left z₀ J₀ hJ₀
  refine ⟨_, _, g, fun hm => h₀ ?_⟩
  have h1 := stalkMap_mem_map_base _ _ _ σ.left (Over.w σ) z₀ _ hm
  have h2 : σ.left ≫ τ.left = 𝟙 _ := congrArg CommaMorphism.left hστ
  rw [← hs f₀, h2] at h1
  exact h1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMemPowOfRatioOfTorsionFree
namespace GlobalTheory

theorem exists_mem_pow_of_ratio_of_torsionFree :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (O : Type) [CommRing O]
      (io : V →+* O), (∀ v : V, v ≠ 0 → ∀ x : O, io v * x = 0 → x = 0) →
      ∀ (f h : O) (p q : V) (m n : ℕ), q ≠ 0 → io q * f = io p * h →
      f ∈ (IsLocalRing.maximalIdeal V ^ (m + n)).map io →
      h ∉ (IsLocalRing.maximalIdeal V ^ (m + 1)).map io →
      ∃ r ∈ IsLocalRing.maximalIdeal V ^ n, p = r * q := by
  intro V _ _ _ O _ io htf f h p q m n hq e hf hh
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hm : IsLocalRing.maximalIdeal V = Ideal.span {π} := hπ.maximalIdeal_eq
  have hπn : π ^ n ∈ IsLocalRing.maximalIdeal V ^ n := by
    rw [hm, Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _
  have key : π ^ n * q ∣ p → ∃ r ∈ IsLocalRing.maximalIdeal V ^ n, p = r * q := by
    rintro ⟨c, hc⟩
    exact ⟨π ^ n * c, Ideal.mul_mem_right _ _ hπn, by rw [hc]; ring⟩
  rcases ValuationRing.dvd_total (π ^ n * q) p with hd | ⟨c, hc⟩
  · exact key hd
  by_cases hu : IsUnit c
  · apply key
    obtain ⟨u, rfl⟩ := hu
    exact ⟨(u⁻¹ : Vˣ), by rw [hc, mul_assoc, Units.mul_inv, mul_one]⟩
  exfalso
  apply hh
  have hcm : c ∈ IsLocalRing.maximalIdeal V := hu
  rw [hm, Ideal.mem_span_singleton] at hcm
  obtain ⟨d, rfl⟩ := hcm
  have hp : p ≠ 0 := by
    rintro rfl
    exact mul_ne_zero (pow_ne_zero n hπ.ne_zero) hq (by simpa using hc)
  rw [hm, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton] at hf ⊢
  obtain ⟨g, rfl⟩ := hf
  refine ⟨io d * g, ?_⟩
  have h0 := htf p hp (h - io (π ^ (m + 1)) * (io d * g)) (by
    have hc' := congrArg io hc
    simp only [map_mul, map_pow] at hc' e ⊢
    linear_combination (io π ^ m * g) * hc' - e)
  exact sub_eq_zero.mp h0

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiTendstoZero
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem psi_tendsto_zero : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → (∃ j, (f 0).f j ≠ 0) → PsiRel D (𝟙_ _) f → ∀ n : ℕ, {χ : D.X | ¬ D.PsiIn χ (IsLocalRing.maximalIdeal V ^ n)}.Finite) := by
  intro V _ _ _ hV D A G _ _ U θ f hθ h0 hR n
  haveI := hV.1
  obtain ⟨ga, a, hS⟩ := exists_psiScal V D
  obtain ⟨m, hm⟩ := exists_order_translates V hV D 1 (f 0) h0
  obtain ⟨s, hs⟩ := LevelVanishing.main V hV D A G U 1 θ f hθ.1 (m + n)
  refine s.finite_toSet.subset fun χ hχ => ?_
  by_contra hn
  apply hχ
  have hne : IsLocalRing.maximalIdeal V ^ n ≠ ⊥ := pow_ne_zero n (IsDiscreteValuationRing.not_a_field V)
  refine (psiIn_iff_scalar_mem V D ga a hS χ _ hne).2 ?_
  obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors V) (a χ).val
  obtain ⟨z, J, hJ, hz⟩ := hm χ
  have hq : (q : V) ≠ 0 := nonZeroDivisors.coe_ne_zero q
  have e := PsiInt.psiRel_integral V D ga a f hS hR χ p q (by rw [mul_comm]; exact hpq) (𝟙_ _ ⊗ D.P.A) (snd _ _) z J hJ
  have e₁ : lift (toUnit (𝟙_ _ ⊗ D.P.A)) (snd (𝟙_ _) D.P.A) = 𝟙 _ := by
    ext1
    · exact toUnit_unique _ _
    · simp
  have e₂ : toUnit (𝟙_ _ ⊗ D.P.A) = fst (𝟙_ _) D.P.A := toUnit_unique _ _
  haveI : Flat D.P.A.hom := by
    haveI := D.P.isAb.smooth
    infer_instance
  haveI : Flat (𝟙_ _ ⊗ D.P.A).hom := by
    have h : (𝟙_ _ ⊗ D.P.A).hom = (λ_ D.P.A).hom.left ≫ D.P.A.hom := (Over.w _).symm
    haveI : IsIso (λ_ D.P.A).hom.left := inferInstanceAs (IsIso ((Over.forget _).map (λ_ D.P.A).hom))
    rw [h]
    infer_instance
  let io := (((𝟙_ _ ⊗ D.P.A).left.presheaf.germ ⊤ z trivial).hom.comp (((𝟙_ _ ⊗ D.P.A).hom.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom))
  have hio : ∀ v : V, gs (𝟙 _) z ⊤ (scal (𝟙_ _ ⊗ D.P.A).hom v) = io v := fun v => gs_eq _ _ ⊤ trivial _
  have hio' : ∀ v : V, cst (𝟙_ _ ⊗ D.P.A).hom z v = io v := fun v => gs_eq _ _ ⊤ trivial _
  rw [hio, hio, e₁] at e
  have hf := hs χ hn z J hJ
  have hf' := Ideal.map_mono (f := io) (Ideal.pow_le_pow_right (Nat.le_succ (m + n))) hf
  obtain ⟨r, hr, hp⟩ := exists_mem_pow_of_ratio_of_torsionFree V _ io
    (fun v hv x hx => by
      have := cst_regular (𝟙_ _ ⊗ D.P.A).hom z hv
      rw [hio'] at this
      exact this (hx.trans (mul_zero _).symm))
    _ _ p q m n hq e hf' (fun h => hz (by
      rw [← e₂]
      exact (Ideal.unit_mul_mem_iff_mem _ (Units.isUnit _)).1 h))
  refine ⟨r, hr, ?_⟩
  have hq' : algebraMap V (FractionRing V) q ≠ 0 := (IsLocalization.map_units _ q).ne_zero
  apply mul_right_cancel₀ hq'
  rw [← map_mul, ← hp]
  exact hpq.symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiTendstoZeroStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.finite_not_psiIn_maximalIdeal_pow : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → (∃ j, (f 0).f j ≠ 0) → PsiRel D (𝟙_ _) f → ∀ n : ℕ, {χ : D.X | ¬ D.PsiIn χ (IsLocalRing.maximalIdeal V ^ n)}.Finite) := by
  first | exact @GlobalTheory.psi_tendsto_zero | exact GlobalTheory.psi_tendsto_zero | (intros; apply GlobalTheory.psi_tendsto_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInMaximalIdealOfNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubeRelScalarsMemMaximalIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EvenQuadraticPosOfFiniteNonpos
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem cubeRel_even_nsmul {X : Type} [AddCommGroup X] (φ : X → ℤ)
    (h : ∀ a b c, φ (a + b + c) + φ a + φ b + φ c = φ (a + b) + φ (a + c) + φ (b + c))
    (he : ∀ a, φ (-a) = φ a) (a : X) (n : ℕ) : φ (n • a) = (n : ℤ) ^ 2 * φ a := by
  have h0 : φ 0 = 0 := by
    have := h 0 0 0
    simp only [add_zero] at this
    linarith
  have key : ∀ n : ℕ, φ (n • a) = (n : ℤ) ^ 2 * φ a ∧
      φ ((n + 1) • a) = ((n + 1 : ℕ) : ℤ) ^ 2 * φ a := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have h1 := h ((n + 1) • a) a (-a)
      have e1 : (n + 1) • a + a + -a = (n + 1) • a := by abel
      have e2 : (n + 1) • a + a = (n + 1 + 1) • a := (succ_nsmul a (n + 1)).symm
      have e3 : (n + 1) • a + -a = n • a := by rw [succ_nsmul]; abel
      rw [e1, e2, e3, add_neg_cancel, he, h0, ih.1, ih.2] at h1
      push_cast at h1 ⊢
      linear_combination -h1
  exact (key n).1

theorem even_quadratic_pos_of_finite_nonpos : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] (φ : X → ℤ), (∀ a b c, φ (a + b + c) + φ a + φ b + φ c = φ (a + b) + φ (a + c) + φ (b + c)) → (∀ a, φ (-a) = φ a) → {a | φ a ≤ 0}.Finite → ∀ a, a ≠ 0 → 0 < φ a := by
  intro X _ _ φ h he hfin a ha
  by_contra hle
  rw [not_lt] at hle
  have hinj : Function.Injective (fun n : ℕ => n • a) := by
    intro m n hmn
    have h1 : ((m : ℤ) - (n : ℤ)) • a = 0 := by
      rw [sub_smul, natCast_zsmul, natCast_zsmul]
      exact sub_eq_zero.mpr hmn
    rcases smul_eq_zero.mp h1 with h2 | h2
    · exact_mod_cast sub_eq_zero.mp h2
    · exact absurd h2 ha
  refine Set.infinite_of_injective_forall_mem hinj ?_ hfin
  intro n
  show φ (n • a) ≤ 0
  rw [cubeRel_even_nsmul φ h he a n]
  exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hle

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_dvr_fraction_order (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] :
    ∃ o : (FractionRing V)ˣ → ℤ, (∀ x y, o (x * y) = o x + o y) ∧
      (∀ (x y : (FractionRing V)ˣ) (u : Vˣ),
        x.val = algebraMap V (FractionRing V) u.val * y.val → o x = o y) ∧
      ∀ x, 0 < o x ↔ ∃ r ∈ IsLocalRing.maximalIdeal V,
        algebraMap V (FractionRing V) r = x.val := by
  let v := (IsDiscreteValuationRing.maximalIdeal V).valuation (FractionRing V)
  have hne : ∀ x : (FractionRing V)ˣ, v x.val ≠ 0 := fun x =>
    (Valuation.ne_zero_iff v).mpr x.ne_zero
  refine ⟨fun x => - WithZero.log (v x.val), ?_, ?_, ?_⟩
  · intro x y
    simp only [Units.val_mul, map_mul]
    rw [WithZero.log_mul (hne x) (hne y)]
    ring
  · intro x y u h
    have hu : v (algebraMap V (FractionRing V) u.val) = 1 := by
      rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
      simp [IsDiscreteValuationRing.maximalIdeal]
    simp only [h, map_mul, hu, _root_.one_mul]
  · intro x
    show 0 < - WithZero.log (v x.val) ↔ _
    rw [neg_pos, WithZero.log_lt_iff_lt_exp (hne x), WithZero.exp_zero]
    constructor
    · intro h
      obtain ⟨r, hr⟩ := IsDiscreteValuationRing.exists_lift_of_le_one h.le
      refine ⟨r, ?_, hr⟩
      rw [← hr] at h
      exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ r).mp h
    · rintro ⟨r, hr, h⟩
      rw [← h]
      exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ r).mpr hr

theorem cubeRel_scalars_mem_maximalIdeal : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (X : Type) [AddCommGroup X] [Module.Free ℤ X] (a : X → (FractionRing V)ˣ), (∀ x y z, ∃ u : Vˣ, (a (x + y + z) * a x * a y * a z).val = algebraMap V (FractionRing V) u.val * (a (x + y) * a (x + z) * a (y + z)).val) → (∀ x, ∃ u : Vˣ, (a (-x)).val = algebraMap V (FractionRing V) u.val * (a x).val) → {x | ¬ ∃ r ∈ IsLocalRing.maximalIdeal V, algebraMap V (FractionRing V) r = (a x).val}.Finite → ∀ x, x ≠ 0 → ∃ r ∈ IsLocalRing.maximalIdeal V, algebraMap V (FractionRing V) r = (a x).val := by
  intro V _ _ _ X _ _ a hc he hfin x hx
  obtain ⟨o, hmul, hunit, hpos⟩ := exists_dvr_fraction_order V
  rw [← hpos]
  refine even_quadratic_pos_of_finite_nonpos X (fun x => o (a x)) ?_ ?_ ?_ x hx
  · intro x y z
    obtain ⟨u, hu⟩ := hc x y z
    have := hunit _ _ u hu
    simpa only [hmul] using this
  · intro x
    obtain ⟨u, hu⟩ := he x
    exact hunit _ _ u hu
  · refine hfin.subset ?_
    intro x hx
    show ¬ _
    rw [← hpos]
    exact not_lt.mpr hx

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem psiIn_maximalIdeal_of_ne_zero : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegPre V), D.TauBimult → D.PsiEven → {χ : D.X | ¬ D.PsiIn χ (IsLocalRing.maximalIdeal V ^ 1)}.Finite → ∀ χ : D.X, χ ≠ 0 → D.PsiIn χ (IsLocalRing.maximalIdeal V) := by
  intro V _ _ _ hV D hT hE hfin χ hχ
  have : IsDiscreteValuationRing V := hV.1
  obtain ⟨ga, a, ha⟩ := exists_psiScal V D
  have hc := GlobalTheory.T.psiScalars_relations_up_to_baseUnits V D ga a ha
  have hm : IsLocalRing.maximalIdeal V ≠ ⊥ := IsDiscreteValuationRing.not_a_field V
  have hiff := fun x => psiIn_iff_scalar_mem V D ga a ha x _ hm
  rw [hiff]
  refine cubeRel_scalars_mem_maximalIdeal V D.X a (hc.1 hT) (hc.2 hE) ?_ χ hχ
  refine hfin.subset ?_
  intro x hx
  show ¬ _
  rw [pow_one, hiff]
  exact hx

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDegenerationDataFunctionalEquationDegreeOn
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
namespace GlobalTheory.UU

theorem exists_degData_fe_one : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∃ (D' : DegData V (IsLocalRing.maximalIdeal V)) (U' : PreU (IsLocalRing.maximalIdeal V) D'.toPre A G), U'.P = U.P ∧ U'.gen = U.gen ∧ U'.FE (Kbar V) 1) := by
  intro hL hL2 V _ _ _ hV D A G _ _ U

  obtain ⟨θ, f, hθ⟩ := GlobalTheory.T.exists_integral_theta_section_with_expansion hL hL2 V hV D A G U
  have hf := (GlobalTheory.T.thetaSection_support_eq_univ hL hL2 V hV D A G U θ f hθ).1

  obtain ⟨ψ, h, hpsi⟩ := GlobalTheory.T.exists_psi_thetaExpansionPsiRelation hL hL2 V D f hf
  obtain ⟨U', hP, hgen, -, hth⟩ := exists_preU_setPsi V D (IsLocalRing.maximalIdeal V) A G U ψ h
  obtain ⟨θ', hθ'⟩ := hth θ f hθ

  have hev := GlobalTheory.T.even_psi_of_thetaExpansionPsiRelation hL hL2 V hV (setPsi D ψ h) A G U' θ' f hθ' hpsi
  have hbi := GlobalTheory.T.bimultiplicative_tau_of_thetaExpansionPsiRelation hL hL2 V hV (setPsi D ψ h) A G U' θ' f hθ' hpsi
  have hfin := GlobalTheory.T.finite_not_psiIn_maximalIdeal_pow V hV (setPsi D ψ h) A G U' θ' f hθ' (hf 0) hpsi
  have hpos := GlobalTheory.psiIn_maximalIdeal_of_ne_zero V hV (setPsi D ψ h) hbi hev (hfin 1)
  have hfe := GlobalTheory.T.thetaExpansion_functionalEquation_degree_one hL hL2 V hV (setPsi D ψ h) A G U' θ' f hθ' hpsi
  exact ⟨{ toPre := setPsi D ψ h, psi_even := hev, tau_bimult := hbi, psi_pos := hpos, psi_tendsto := hfin }, U', hP, hgen, hfe⟩
end GlobalTheory.UU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDegenerationDataFunctionalEquationDegreeOnStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degenerationData_functionalEquation_degree_one : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∃ (D' : DegData V (IsLocalRing.maximalIdeal V)) (U' : PreU (IsLocalRing.maximalIdeal V) D'.toPre A G), U'.P = U.P ∧ U'.gen = U.gen ∧ U'.FE (Kbar V) 1) := by
  first | exact @GlobalTheory.UU.exists_degData_fe_one | exact GlobalTheory.UU.exists_degData_fe_one | (intros; apply GlobalTheory.UU.exists_degData_fe_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDegenerationDataUniformisationOfTorsionCou
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem exists_degData_unif : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → Laws → Laws2 → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∃ (D : DegData V (IsLocalRing.maximalIdeal V)) (U : Unif (IsLocalRing.maximalIdeal V) D A G), U.LG = s.P.L ∧ U.gen = s.gen ∧ HEq U.cubG s.P.c :=
  fun h0 h1 h2 => GlobalTheory.UU.unif_assembly h1 h2 (GlobalTheory.T.exists_uniformisation_data_before_choice h0 h1) (GlobalTheory.T.exists_degenerationData_functionalEquation_degree_one h1 h2)

end GlobalTheory.UU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDegenerationDataUniformisationOfTorsionCouStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degenerationData_uniformisation_of_torsionCount : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → Laws → Laws2 → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∃ (D : DegData V (IsLocalRing.maximalIdeal V)) (U : Unif (IsLocalRing.maximalIdeal V) D A G), U.LG = s.P.L ∧ U.gen = s.gen ∧ HEq U.cubG s.P.c := by
  first | exact @GlobalTheory.UU.exists_degData_unif | exact GlobalTheory.UU.exists_degData_unif | (intros; apply GlobalTheory.UU.exists_degData_unif <;> assumption)
end
