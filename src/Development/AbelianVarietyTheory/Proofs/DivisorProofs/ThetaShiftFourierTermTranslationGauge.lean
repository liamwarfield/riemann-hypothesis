module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRaynaudPointUnitPartCoordinates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BinomialFlagDimensionDegreeBound

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudSectionIdentityOfGenericFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudSectionIdentityOfGenericFibre
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.RayFlatDesc

theorem gs_sub_of {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a - b) = gs f y U a - gs f y U b := by
  simp only [gs, dif_pos h, map_sub]

theorem gs_zero_of {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (k : ℕ) (ρ τ : SecM Y.q.left Q.P.L k) (a b : R), (∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (r : Z ⟶ Y.H.left), r ≫ Y.H.hom = g ≫ jK R → ∀ (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → gs r z ⊤ (scal Y.H.hom a) * sval ρ r z J = gs r z ⊤ (scal Y.H.hom b) * sval τ r z J) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → gs r z ⊤ (scal Y.H.hom a) * sval ρ r z J = gs r z ⊤ (scal Y.H.hom b) * sval τ r z J := by
  intro R _ _ Q O _ _ _ oa Y k ρ τ a b H Z r z J hJ
  have := GlobalTheory.RayTan.smooth_H R Q O oa Y
  have hL : Q.P.L.IsLB := Q.P.isLB
  have key : ∀ j : Fin 1 → Q.P.L.ι,
      (Y.H.left.presheaf.map (homOfLE le_top).op).hom (scal Y.H.hom a) * ρ.f j -
        (Y.H.left.presheaf.map (homOfLE le_top).op).hom (scal Y.H.hom b) * τ.f j = 0 := by
    intro j
    apply GlobalTheory.Mum.fst_generic_app_injective Y.H.hom _
    rw [map_zero]
    apply fn_ext
    intro y hy
    have hy' : pullback.fst Y.H.hom (jK R) y ∈
        (LB.LinComb Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => (k : ℤ))).U j := hy
    have hw : pullback.fst Y.H.hom (jK R) y ∈ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) j := hy
    obtain ⟨J', hJ', e⟩ := exists_good Q.P.L hL y (fun _ : Unit => pullback.fst Y.H.hom (jK R) ≫ Y.q.left)
      (fun _ => j 0) (fun _ _ _ => rfl) (fun _ => Set.mem_iInter.1 hw 0)
    have ej : ∀ i : Fin 1, J' (pullback.fst Y.H.hom (jK R) ≫ Y.q.left) = j i := fun i => by
      rw [Subsingleton.elim i 0]; exact e ()
    have h1 := H _ (pullback.snd _ _) (pullback.fst _ _) pullback.condition y J' hJ'
    rw [sval_of ρ _ y J' j ej, sval_of τ _ y J' j ej] at h1
    rw [gs_pull (𝟙 _) (pullback.fst Y.H.hom (jK R)) y _ hy', Category.id_comp, gs_zero_of _ _ _,
      gs_sub_of _ _ _ hy', gs_mul _ _ _ hy', gs_mul _ _ _ hy', gs_res _ _ _ hy', gs_res _ _ _ hy']
    exact sub_eq_zero.2 h1
  have hm : r z ∈ (LB.LinComb Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => (k : ℤ))).U
      (fun _ => J (r ≫ Y.q.left)) :=
    Set.mem_iInter.2 fun _ => hJ (r ≫ Y.q.left)
  have e := congrArg (gs r z _) (key fun _ => J (r ≫ Y.q.left))
  rw [gs_sub_of _ _ _ hm, gs_mul _ _ _ hm, gs_mul _ _ _ hm, gs_res _ _ _ hm, gs_res _ _ _ hm, gs_zero_of _ _ _,
    sub_eq_zero] at e
  rw [sval_of ρ r z J _ (fun _ => rfl), sval_of τ r z J _ (fun _ => rfl)]
  exact e

end GlobalTheory.RayFlatDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudSectionIdentityOfGenericFibreStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.raynaud_section_identity_of_generic_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (k : ℕ) (ρ τ : SecM Y.q.left Q.P.L k) (a b : R), (∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (r : Z ⟶ Y.H.left), r ≫ Y.H.hom = g ≫ jK R → ∀ (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → gs r z ⊤ (scal Y.H.hom a) * sval ρ r z J = gs r z ⊤ (scal Y.H.hom b) * sval τ r z J) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → gs r z ⊤ (scal Y.H.hom a) * sval ρ r z J = gs r z ⊤ (scal Y.H.hom b) * sval τ r z J := by
  first | exact @GlobalTheory.RayFlatDesc.main | exact GlobalTheory.RayFlatDesc.main | (intros; apply GlobalTheory.RayFlatDesc.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudShiftUnitIdentityFractionField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudShiftUnitIdentityFractionField
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR

set_option autoImplicit false

namespace GlobalTheory.ShiftUnit

theorem cv_nsmul {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T : Over (Spec (CommRingCat.of R))}
    (g : GtPt D T) {y : T.left} {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L y J) (a mu : D.X) (k : ℕ) :
    GlobalTheory.TorusModel.cv g (a + k • mu) y J * cubN (th D y J) k (cP D T a) (cP D T mu) g.b =
      GlobalTheory.TorusModel.cv g a y J * GlobalTheory.TorusModel.cv g mu y J ^ k := by
  induction k with
  | zero => rw [zero_nsmul, add_zero, pow_zero]; rfl
  | succ k ih =>
    have e := GlobalTheory.TorusModel.cv_add g hJ (a + k • mu) mu
    rw [cPoint_add, cPoint_nsmul] at e
    rw [succ_nsmul, ← add_assoc, cubN, Finset.prod_range_succ, mul_comm (∏ _ ∈ _, _), ← _root_.mul_assoc, e, pow_succ,
      ← _root_.mul_assoc, ← ih, cubN, mul_right_comm]

theorem cst_mul {V : Type} [CommRing V] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of V)) (z : Z) (a b : V) :
    cst q z (a * b) = cst q z a * cst q z b := by
  unfold cst; rw [map_mul]; exact gs_mul q z ⊤ trivial _ _

theorem cst_pow {V : Type} [CommRing V] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of V)) (z : Z) (a : V) (n : ℕ) :
    cst q z (a ^ n) = cst q z a ^ n := by
  induction n with
  | zero => unfold cst; rw [pow_zero, pow_zero, map_one, gs_eq q z ⊤ trivial, map_one, map_one]
  | succ n ih => rw [pow_succ, cst_mul, ih, pow_succ]

end GlobalTheory.ShiftUnit


open GlobalTheory.ShiftUnit in
theorem GlobalTheory.ShiftUnit.shift_unit_identity : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa), Q.TauBimult → ∀ (k : ℕ) (mu α : Q.X) (xp : 𝟙_ (Over (Sp R)) ⟶ Y.H) (A₀ B₀ P₀ : R) (ψ₀ : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c mu).left) fun _ => -1)) (e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ xp⁻¹)).left ≫ Y.q.left] ![1, -1])), xp ≫ Y.q = Q.c mu → (∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → cst (g ≫ jK R) z A₀ * (val ((Y.Φ (Over.mk (g ≫ jK R)) (toUnit _ ≫ xp)).s α) (𝟙 Z) z J).val = cst (g ≫ jK R) z B₀ * (val (Q.tau mu α) g z J).val) → (∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → (val (Q.psi mu) g z J).val = cst (g ≫ jK R) z P₀ * (val ψ₀ (g ≫ jK R) z J).val) → (∀ (T : Over (Sp R)) (y : T ⟶ Y.H) (z : T.left) (J : (T.left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → val e y.left z J * val ψ₀ T.hom z J * val Q.rig T.hom z J * val ((Y.Φ T (y * (toUnit T ≫ xp⁻¹))).s mu) (𝟙 _) z J = 1) → ∀ (u : LB.Gen (LB.LinComb Q.P.L (DegPre.deltaφ Q (FractionRing R) k α mu) (DegPre.deltaε k))), u.IsGen → LB.Gen.Corr Q.P.L _ _ _ _ (LB.pullGen Q.P.L _ _ u (DegPre.zF Q (FractionRing R)).left) (DegPre.famMult Q (FractionRing R) k mu α) → ∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (pp : Over.mk (g ≫ jK R) ⟶ DegPre.BF Q (FractionRing R)) (yp : Over.mk (g ≫ jK R) ⟶ Y.H), (pp ≫ fst _ _).left ≫ jFK (R := R) (FractionRing R) = g → pp ≫ DegPre.prB Q (FractionRing R) = yp ≫ Y.q → ∀ (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → cst (g ≫ jK R) z B₀ * (val u (show Z ⟶ _ from pp.left) z J).val * (val ((Y.Φ _ yp).s (α + k • mu)) (𝟙 Z) z J).val * ((val e (show Z ⟶ Y.H.left from (yp * (toUnit _ ≫ xp)).left) z J) ^ k).val = cst (g ≫ jK R) z (P₀ ^ k * A₀) * (val ((Y.Φ _ (yp * (toUnit _ ≫ xp))).s α) (𝟙 Z) z J).val := by
  intro R _ _ Q O _ _ _ oa Y hB k mu α xp A₀ B₀ P₀ ψ₀ e hxp hA hP he u hu hcorr Z g pp yp hg hpp z J hJ
  have e1 := (gen_fe (D := Q) (F := FractionRing R) GlobalTheory.SemiRigid.globalFns k mu α).2 u hu hcorr _ pp z J hJ
  rw [uVal, val_famMult _ hJ, hg, TWM.val_powGen, TWM.val_powGen] at e1
  have c1 : pp ≫ fst (TF (FractionRing R)) Q.P.A ≫ cP Q (TF (FractionRing R)) mu = cP Q (Over.mk (g ≫ jK R)) mu := by
    rw [← Category.assoc, comp_cP]
  have jr : (toUnit (TK R)).left = jK R := by simpa using Over.w (toUnit (TK R))
  have hr : val (Z := (Over.mk (g ≫ jK R)).left) Q.rigK g z J = val (Z := (Over.mk (g ≫ jK R)).left) Q.rig (g ≫ jK R) z J := by
    rw [DegPre.rigK, val_pull hJ, jr]
  rw [c1, hpp, hr] at e1
  have b1 : (Y.Φ (Over.mk (g ≫ jK R)) yp).b = yp ≫ Y.q := Ray.Φ_b Y yp
  have b2 : (Y.Φ (Over.mk (g ≫ jK R)) (toUnit _ ≫ xp)).b = cP Q (Over.mk (g ≫ jK R)) mu := by
    rw [Ray.Φ_b, Category.assoc, hxp]; rfl
  have e2 : val ((Y.Φ _ yp).s (α + k • mu)) (𝟙 _) z J *
      cubN (th Q z J) k (cP Q (Over.mk (g ≫ jK R)) α) (cP Q (Over.mk (g ≫ jK R)) mu) (yp ≫ Y.q) =
      val ((Y.Φ _ yp).s α) (𝟙 _) z J * val ((Y.Φ _ yp).s mu) (𝟙 _) z J ^ k := by
    have := cv_nsmul (Y.Φ _ yp) hJ α mu k
    rw [b1] at this
    exact this
  have e3 : val ((Y.Φ _ (yp * (toUnit _ ≫ xp))).s α) (𝟙 _) z J *
      th Q z J (cP Q (Over.mk (g ≫ jK R)) α) (yp ≫ Y.q) (cP Q (Over.mk (g ≫ jK R)) mu) =
      val ((Y.Φ _ yp).s α) (𝟙 _) z J * val ((Y.Φ (Over.mk (g ≫ jK R)) (toUnit _ ≫ xp)).s α) (𝟙 _) z J := by
    have := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ yp (toUnit _ ≫ xp))).2 α z J hJ
    rw [b1, b2] at this
    exact this
  have m1 : (yp * (toUnit (Over.mk (g ≫ jK R)) ≫ xp)) * (toUnit (Over.mk (g ≫ jK R)) ≫ xp⁻¹) = yp := by
    rw [GrpObj.comp_inv, mul_inv_cancel_right]
  have e4 : val (Z := (Over.mk (g ≫ jK R)).left) e (yp * (toUnit _ ≫ xp)).left z J * val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J * val (Z := (Over.mk (g ≫ jK R)).left) Q.rig (g ≫ jK R) z J *
      val ((Y.Φ _ yp).s mu) (𝟙 _) z J = 1 := by
    have := he (Over.mk (g ≫ jK R)) (yp * (toUnit _ ≫ xp)) z J hJ
    rw [m1] at this
    exact this
  have e5 : (val (Z := (Over.mk (g ≫ jK R)).left) (Q.psi mu) g z J).val = cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z P₀ * (val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J).val :=
    hP Z g z J hJ
  have e6 : cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z A₀ * (val ((Y.Φ _ (toUnit _ ≫ xp)).s α) (𝟙 _) z J).val =
      cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z B₀ * (val (Z := (Over.mk (g ≫ jK R)).left) (Q.tau mu α) g z J).val :=
    hA Z g z J hJ
  have V : val (Z := (Over.mk (g ≫ jK R)).left) u pp.left z J * val ((Y.Φ _ yp).s (α + k • mu)) (𝟙 _) z J * val (Z := (Over.mk (g ≫ jK R)).left) e (yp * (toUnit _ ≫ xp)).left z J ^ k *
      val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J ^ k =
      (th Q z J (cP Q (Over.mk (g ≫ jK R)) α) (yp ≫ Y.q) (cP Q (Over.mk (g ≫ jK R)) mu))⁻¹ *
        val (Z := (Over.mk (g ≫ jK R)).left) (Q.tau mu α) g z J * val (Z := (Over.mk (g ≫ jK R)).left) (Q.psi mu) g z J ^ k * val ((Y.Φ _ yp).s α) (𝟙 _) z J := by
    apply Additive.ofMul.injective
    have a1 := congrArg Additive.ofMul e1
    have a2 := congrArg Additive.ofMul e2
    have a4 := congrArg Additive.ofMul e4
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at a1 a2 a4 ⊢
    have a4k := congrArg (k • ·) a4
    simp only [smul_add, smul_zero] at a4k
    linear_combination (norm := abel) a1 + a2 + a4k
  have Vv := congrArg Units.val V
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at Vv
  rw [e5, mul_pow] at Vv
  have e3v := congrArg Units.val e3
  simp only [Units.val_mul] at e3v
  have hθ : Units.val (th Q z J (cP Q (Over.mk (g ≫ jK R)) α) (yp ≫ Y.q) (cP Q (Over.mk (g ≫ jK R)) mu)) * (Units.val (th Q z J (cP Q (Over.mk (g ≫ jK R)) α) (yp ≫ Y.q) (cP Q (Over.mk (g ≫ jK R)) mu))⁻¹) = 1 := Units.mul_inv _
  suffices FINAL : cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z B₀ * (val (Z := (Over.mk (g ≫ jK R)).left) u pp.left z J).val * (val ((Y.Φ _ yp).s (α + k • mu)) (𝟙 _) z J).val *
      ((val (Z := (Over.mk (g ≫ jK R)).left) e (yp * (toUnit _ ≫ xp)).left z J) ^ k).val =
    cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z (P₀ ^ k * A₀) * (val ((Y.Φ _ (yp * (toUnit _ ≫ xp))).s α) (𝟙 _) z J).val by exact FINAL
  rw [cst_mul, cst_pow, Units.val_pow_eq_pow_val]
  have hu0 : IsUnit ((val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J).val ^ k) := (Units.isUnit _).pow k
  apply hu0.mul_right_cancel
  linear_combination cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z B₀ * Vv + cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z P₀ ^ k * (val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J).val ^ k * cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z A₀ * (val ((Y.Φ _ (yp * (toUnit _ ≫ xp))).s α) (𝟙 _) z J).val * hθ - cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z P₀ ^ k * (val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J).val ^ k * cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z A₀ * (Units.val (th Q z J (cP Q (Over.mk (g ≫ jK R)) α) (yp ≫ Y.q) (cP Q (Over.mk (g ≫ jK R)) mu))⁻¹) * e3v - cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z P₀ ^ k * (val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J).val ^ k * (val ((Y.Φ _ yp).s α) (𝟙 _) z J).val * (Units.val (th Q z J (cP Q (Over.mk (g ≫ jK R)) α) (yp ≫ Y.q) (cP Q (Over.mk (g ≫ jK R)) mu))⁻¹) * e6
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudShiftUnitIdentityFractionFieldStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.raynaudShift_unitIdentity_fractionField : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa), Q.TauBimult → ∀ (k : ℕ) (mu α : Q.X) (xp : 𝟙_ (Over (Sp R)) ⟶ Y.H) (A₀ B₀ P₀ : R) (ψ₀ : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c mu).left) fun _ => -1)) (e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ xp⁻¹)).left ≫ Y.q.left] ![1, -1])), xp ≫ Y.q = Q.c mu → (∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → cst (g ≫ jK R) z A₀ * (val ((Y.Φ (Over.mk (g ≫ jK R)) (toUnit _ ≫ xp)).s α) (𝟙 Z) z J).val = cst (g ≫ jK R) z B₀ * (val (Q.tau mu α) g z J).val) → (∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → (val (Q.psi mu) g z J).val = cst (g ≫ jK R) z P₀ * (val ψ₀ (g ≫ jK R) z J).val) → (∀ (T : Over (Sp R)) (y : T ⟶ Y.H) (z : T.left) (J : (T.left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → val e y.left z J * val ψ₀ T.hom z J * val Q.rig T.hom z J * val ((Y.Φ T (y * (toUnit T ≫ xp⁻¹))).s mu) (𝟙 _) z J = 1) → ∀ (u : LB.Gen (LB.LinComb Q.P.L (DegPre.deltaφ Q (FractionRing R) k α mu) (DegPre.deltaε k))), u.IsGen → LB.Gen.Corr Q.P.L _ _ _ _ (LB.pullGen Q.P.L _ _ u (DegPre.zF Q (FractionRing R)).left) (DegPre.famMult Q (FractionRing R) k mu α) → ∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (pp : Over.mk (g ≫ jK R) ⟶ DegPre.BF Q (FractionRing R)) (yp : Over.mk (g ≫ jK R) ⟶ Y.H), (pp ≫ fst _ _).left ≫ jFK (R := R) (FractionRing R) = g → pp ≫ DegPre.prB Q (FractionRing R) = yp ≫ Y.q → ∀ (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → cst (g ≫ jK R) z B₀ * (val u (show Z ⟶ _ from pp.left) z J).val * (val ((Y.Φ _ yp).s (α + k • mu)) (𝟙 Z) z J).val * ((val e (show Z ⟶ Y.H.left from (yp * (toUnit _ ≫ xp)).left) z J) ^ k).val = cst (g ≫ jK R) z (P₀ ^ k * A₀) * (val ((Y.Φ _ (yp * (toUnit _ ≫ xp))).s α) (𝟙 Z) z J).val := by
  first | exact @GlobalTheory.ShiftUnit.shift_unit_identity | exact GlobalTheory.ShiftUnit.shift_unit_identity | (intros; apply GlobalTheory.ShiftUnit.shift_unit_identity <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonomialPeriodUnitPartGenerator
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonomialPeriodUnitPartGenerator
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.UnitPart

theorem exists_psi_val_eq_monomial_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : DegPre R) (m : ℕ)
    (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), IsMonomial Q t gam → ∀ (χ : Q.X) (n : Fin m → ℕ),
    (∀ i, gam i χ χ = 2 * n i) → ∃ ψ₀ : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) fun _ => -1),
      ψ₀.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι),
        Good Q.P.L z J → (val (Q.psi χ) r z J).val = cst (r ≫ jK R) z (∏ i, t i ^ n i) * (val ψ₀ (r ≫ jK R) z J).val := by
  intro R _ _ _ Q m t gam hM χ n hn
  obtain ⟨u, n', hn', hc⟩ := hM χ
  obtain rfl : n = n' := funext fun i => by have := (hn' i).symm.trans (hn i); omega
  obtain ⟨j, hj, h, e⟩ := hc
  have hL := Q.P.isLB
  obtain ⟨e₀, he₀⟩ := exists_gen_of_local (V := R) Q.P.L hL (K := PUnit) (fun _ => (Q.c χ).left) (fun _ => -1)
  have le : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ LB.wchart Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) j :=
    fun y hy => Set.mem_iInter.2 fun k => by cases k; exact hj hy
  have hx : Q.xK χ = jK R ≫ (Q.c χ).left := by simp [DegPre.xK, ptK]
  have hto : ∀ a, DegPre.toOpen (R := R) ⊤ a = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a := fun a => by
    simp [DegPre.toOpen]
  let w : Γ(Spec (CommRingCat.of R), ⊤)ˣ :=
    Units.map (DegPre.toOpen (R := R) ⊤).toMonoidHom u * (res le (e₀.s j))⁻¹
  let v : LB.Gen (LB.LinComb Q.P.L (Y := Spec (CommRingCat.of R)) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim) :=
    ⟨fun _ => res le_top w⟩
  have hv : v.IsGen := fun i i' => by
    obtain rfl : i = i' := funext fun k => k.elim
    have e' : (LB.LinComb Q.P.L (Y := Spec (CommRingCat.of R)) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim).g i i = 1 := by
      dsimp only [LB.LinComb]
      erw [Fintype.prod_empty]
      rfl
    rw [e', _root_.one_mul]
  have hf : FormEq (Sum.elim (fun _ : PUnit => (Q.c χ).left) (PEmpty.elim : PEmpty.{1} → _))
      (Sum.elim (fun _ : PUnit => (-1 : ℤ)) (PEmpty.elim : PEmpty.{1} → ℤ))
      (fun _ : PUnit => (Q.c χ).left) (fun _ => -1) := fun U _ g => by
    rw [Fintype.prod_sum_type]
    simp
  obtain ⟨ψ₀, hψ₀, vψ₀⟩ := exists_gen hL hf (LB.mulGen Q.P.L _ _ _ _ e₀ v)
    (mulGen_isGen _ _ _ _ _ _ _ he₀ hv)
  refine ⟨ψ₀, hψ₀, fun Z r z J hJ => ?_⟩
  rw [vψ₀ _ _ z J hJ, val_mul hJ]
  have m₁ : r z ∈ LB.wchart Q.P.L (K := PUnit) (fun _ => Q.xK χ) j := h trivial
  have m₂ : (r ≫ jK R) z ∈ LB.wchart Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) j := le trivial
  have e₁ : val (Q.psi χ) r z J = _ := gen_trans (Q.psi_gen χ) r z (hJ.mem _ r) m₁
  have e₂ : val e₀ (r ≫ jK R) z J = _ := gen_trans he₀ (r ≫ jK R) z (hJ.mem _ _) m₂
  have e₃ : trF (L := Q.P.L) (K := PUnit) (fun _ => Q.xK χ) (fun _ => -1) r z (fun _ => J (r ≫ Q.xK χ)) j =
      trF (L := Q.P.L) (K := PUnit) (fun _ => (Q.c χ).left) (fun _ => -1) (r ≫ jK R) z
        (fun _ => J ((r ≫ jK R) ≫ (Q.c χ).left)) j := by
    have hq : r ≫ Q.xK χ = (r ≫ jK R) ≫ (Q.c χ).left :=
      (congrArg (r ≫ ·) hx).trans (Category.assoc _ _ _).symm
    simp only [trF]
    rw [hq]
  have e₄ : (gm r z (LB.wchart Q.P.L (K := PUnit) (fun _ => Q.xK χ) j) ((Q.psi χ).s j)).val =
      cst (r ≫ jK R) z (u * ∏ i, t i ^ n i) := by
    refine (gs_unit r z _ m₁ _).symm.trans ((gs_res r z h trivial _).symm.trans ?_)
    refine (congrArg (gs r z _) e.symm).trans ((gs_pull r (jK R) z ⊤ trivial _).trans ?_)
    rw [hto]; rfl
  have e₅ : val v (r ≫ jK R) z J = gm (r ≫ jK R) z ⊤ w := gm_res _ z _ (hJ.mem PEmpty.elim _) _
  have e₆ : (gm (r ≫ jK R) z ⊤ (Units.map (DegPre.toOpen (R := R) ⊤).toMonoidHom u)).val = cst (r ≫ jK R) z u := by
    rw [← gs_unit _ z ⊤ trivial, Units.coe_map, cst, ← hto]; rfl
  have e₇ : ∀ a b : R, cst (r ≫ jK R) z (a * b) = cst (r ≫ jK R) z a * cst (r ≫ jK R) z b := fun a b => by
    rw [cst, map_mul, gs_mul _ z ⊤ trivial]; rfl
  have e₈ : gm (r ≫ jK R) z ⊤ (res le (e₀.s j)) =
      gm (r ≫ jK R) z (LB.wchart Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) j) (e₀.s j) := gm_res _ z le trivial _
  have hg := Units.mul_inv (gm (r ≫ jK R) z (LB.wchart Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) j) (e₀.s j))
  rw [e₁, e₂, e₅, Units.val_mul, Units.val_mul, e₄]
  erw [e₃]
  rw [map_mul, map_inv, e₈]
  simp only [Units.val_mul]
  rw [e₆, e₇]
  linear_combination (-((trF (L := Q.P.L) (K := PUnit) (fun _ => (Q.c χ).left) (fun _ => -1) (r ≫ jK R) z
        (fun _ => J ((r ≫ jK R) ≫ (Q.c χ).left)) j).val * cst (r ≫ jK R) z u * cst (r ≫ jK R) z (∏ i, t i ^ n i))) * hg

end GlobalTheory.UnitPart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonomialPeriodUnitPartGeneratorStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_monomialPeriod_unitPart_generator : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : DegPre R) (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), IsMonomial Q t gam → ∀ (χ : Q.X) (n : Fin m → ℕ), (∀ i, gam i χ χ = 2 * n i) → ∃ ψ₀ : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) fun _ => -1), ψ₀.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → (val (Q.psi χ) r z J).val = cst (r ≫ jK R) z (∏ i, t i ^ n i) * (val ψ₀ (r ≫ jK R) z J).val := by
  first | exact @GlobalTheory.UnitPart.exists_psi_val_eq_monomial_mul | exact GlobalTheory.UnitPart.exists_psi_val_eq_monomial_mul | (intros; apply GlobalTheory.UnitPart.exists_psi_val_eq_monomial_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRaynaudGaugeGeneratorWeightNeg
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRaynaudGaugeGeneratorWeightNeg
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Heat.ShiftGauge

theorem toUnit_left {R : Type} [CommRing R] (T : Over (Sp R)) : (toUnit T).left = T.hom := by
  simpa using Over.w (toUnit T)

theorem exists_gauge : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (mu : Q.X) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H), (x ≫ Y.q) * Q.c mu = 1 → ∀ ψ₀ : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c mu).left) fun _ => -1), ψ₀.IsGen → ∃ e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1]), e.IsGen ∧ (∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j → IsWt Y (-mu) (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V))) ∧ ∀ (T : Over (Sp R)) (y : T ⟶ Y.H) (z : T.left) (J : (T.left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → val e y.left z J * val ψ₀ T.hom z J * val Q.rig T.hom z J * val ((Y.Φ T (y * (toUnit T ≫ x))).s mu) (𝟙 _) z J = 1 := by
  intro R _ _ Q O _ _ _ oa Y mu x hx ψ₀ hψ₀
  have hL : Q.P.L.IsLB := Q.P.isLB
  have hq : IsMonHom Y.q := Y.q_linear.isMonHom
  set Tx : Y.H ⟶ Y.H := 𝟙 Y.H * (toUnit Y.H ≫ x) with hTx

  have hTq : Tx ≫ Y.q = Y.q * (toUnit Y.H ≫ x ≫ Y.q) := by
    rw [hTx, MonObj.mul_comp, Category.id_comp, Category.assoc]
  have hcq : cP Q Y.H mu * (Tx ≫ Y.q) = Y.q := by
    rw [hTq, cP, _root_.mul_comm, _root_.mul_assoc, ← MonObj.comp_mul (toUnit Y.H) (x ≫ Y.q) (Q.c mu), hx,
      MonObj.comp_one, _root_.mul_one]
  have e₁ : (cP Q Y.H mu).left = Y.H.hom ≫ (Q.c mu).left := by rw [cP, Over.comp_left, toUnit_left]
  have e₂ : (1 : Y.H ⟶ Q.P.A).left = Y.H.hom ≫ eSec Q.P.A := by rw [Hom.one_def, Over.comp_left, toUnit_left]; rfl
  let s := (Y.Φ Y.H Tx).s mu
  let w := LB.mulGen Q.P.L _ _ _ _ (LB.mulGen Q.P.L _ _ _ _ (LB.pullGen Q.P.L _ _ ψ₀ Y.H.hom)
    (LB.pullGen Q.P.L _ _ Q.rig Y.H.hom)) s
  have hw : w.IsGen := mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hψ₀ _)
    (pullGen_isGen _ _ _ _ Q.rig_gen _)) ((Y.Φ Y.H Tx).isGen mu)
  have hF : FormEq (Sum.elim (Sum.elim (fun _ : PUnit => Y.H.hom ≫ (Q.c mu).left)
      (fun _ : PUnit => Y.H.hom ≫ eSec Q.P.A)) (DegPre.gtφT Q Y.H (Y.Φ Y.H Tx).b mu))
      (fun k => - Sum.elim (Sum.elim (fun _ : PUnit => (-1 : ℤ)) (fun _ : PUnit => (1 : ℤ))) DegPre.gtε k)
      (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) ![1, -1] := by
    intro U _ h
    simp only [zpow_neg, Finset.prod_inv_distrib, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
      Fintype.prod_unique, Fin.prod_univ_two]
    rw [GlobalTheory.TorusModel.prod_pt, Ray.Φ_b, hcq, e₁, e₂]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Over.comp_left]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    abel
  obtain ⟨e, he, hve⟩ := exists_gen hL hF (LB.invGen Q.P.L _ _ w) (invGen_isGen _ _ _ _ hw)
  have hval : ∀ (T : Over (Sp R)) (y : T ⟶ Y.H) (z : T.left) (J : (T.left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J →
      val e y.left z J = (val ψ₀ T.hom z J * val Q.rig T.hom z J *
        val ((Y.Φ T (y * (toUnit T ≫ x))).s mu) (𝟙 _) z J)⁻¹ := by
    intro T y z J hJ
    have hy : y ≫ Tx = y * (toUnit T ≫ x) := by
      rw [hTx, MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (y ≫ toUnit Y.H) (toUnit T)]
    have hp := ((GlobalTheory.TorusModel.isPull_iff y (Y.Φ Y.H Tx) (Y.Φ T (y ≫ Tx))).1 (Y.rep.1 T Y.H y Tx)).2 mu z J hJ
    rw [hve _ _ z J hJ, val_inv, val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, Over.w y, ← hy]
    rw [show val ((Y.Φ T (y ≫ Tx)).s mu) (𝟙 _) z J = _ from hp]
  refine ⟨e, he, ?_, fun T y z J hJ => ?_⟩
  · intro j V hV S _ φ x₁ x₁' c a a' ha ha' hV₁ hV₂ hqq hc
    subst ha ha'
    have hV' : Y.q.left ⁻¹ᵁ V ≤
        (LB.LinComb Q.P.L (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) ![1, -1]).U j := hV
    have germ : ∀ (b : Sp S ⟶ Y.H.left), ⊤ ≤ b ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V) → ∀ z,
        gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
          (valR b (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V)))) =
          gs b z (LB.wchart Q.P.L (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) j)
            (e.s j).val := by
      intro b hb z
      rw [valR, dite_eq_left hb, Iso.hom_inv_id_apply, rsT, dite_eq_left hV']
      refine (gs_res (𝟙 _) z hb trivial _).trans ((gs_pull (𝟙 _) b z _ (hb trivial) _).trans ?_)
      rw [Category.id_comp]
      exact gs_res b z hV (hb trivial) _
    have hq' : x₁'.left ≫ Y.q.left = x₁.left ≫ Y.q.left := congrArg CommaMorphism.left hqq
    have hu : ∀ u : Over.mk (spMap φ) ⟶ Y.H, u ≫ Tx ≫ Y.q = (u ≫ Y.q) * (toUnit _ ≫ x ≫ Y.q) := fun u => by
      rw [hTq, MonObj.comp_mul, ← Category.assoc u (toUnit Y.H), toUnit_unique (u ≫ toUnit Y.H) (toUnit _)]
    have hT₀ : x₁' ≫ Tx ≫ Y.q = x₁ ≫ Tx ≫ Y.q := by rw [hu, hu, hqq]
    have hT : x₁'.left ≫ Tx.left ≫ Y.q.left = x₁.left ≫ Tx.left ≫ Y.q.left := congrArg CommaMorphism.left hT₀
    have hk : ∀ k, x₁'.left ≫ (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) k =
        x₁.left ≫ (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) k :=
      Fin.forall_fin_two.2 ⟨hq', hT⟩
    apply (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.symm.injective
    refine fn_ext fun z _ => ?_
    choose I hI using fun χ : (Over.mk (spMap φ)).left ⟶ Q.P.A.left => exists_chart hL (χ z)
    have hJ : Good Q.P.L z I := hI
    have hgv : ∀ (b : Sp S ⟶ Y.H.left) (hb : ⊤ ≤ b ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V)),
        gs b z (LB.wchart Q.P.L (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) j)
          (e.s j).val = (trF (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) ![1, -1] b z j
            (fun k => I (b ≫ (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) k)) *
            val e b z I).val := fun b hb =>
      (gs_unit b z _ (hV (hb trivial)) _).trans (congrArg Units.val (gen_trans he b z (hV (hb trivial)) (hJ.mem _ b)))
    have htr : trF (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) ![1, -1] x₁'.left z j
          (fun k => I (x₁'.left ≫ (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) k)) =
        trF (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) ![1, -1] x₁.left z j
          (fun k => I (x₁.left ≫ (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) k)) := by
      unfold trF
      exact Finset.prod_congr rfl fun k _ => congrArg (fun ψ => gm ψ z (Q.P.L.U (j k) ⊓ Q.P.L.U (I ψ)) (Q.P.L.g (j k) (I ψ)) ^ (![1, -1] : Fin 2 → ℤ) k) (hk k)
    have ve : val e x₁'.left z I = gm (𝟙 (Over.mk (spMap φ)).left) z ⊤ (unitOn (c (-mu))) * val e x₁.left z I := by
      have hb : (Y.Φ _ x₁').b = (Y.Φ _ x₁).b := by rw [Ray.Φ_b, Ray.Φ_b, hqq]
      have h1 := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ x₁ (toUnit _ ≫ x))).2 mu z I hJ
      have h2 := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ x₁' (toUnit _ ≫ x))).2 mu z I hJ
      rw [hb] at h2
      have h3 := hc mu z I hJ
      have h4 := GlobalTheory.TorusModel.cv_add (Y.Φ _ x₁) hJ mu (-mu)
      have h5 := GlobalTheory.TorusModel.cv_add (Y.Φ _ x₁') hJ mu (-mu)
      rw [add_neg_cancel, GlobalTheory.TorusModel.cv_zero _ hJ] at h4 h5
      rw [hb] at h5
      have h6 := hc (-mu) z I hJ
      rw [hval _ x₁ z I hJ, hval _ x₁' z I hJ]
      apply Additive.ofMul.injective
      have g1 := congrArg Additive.ofMul h1
      have g2 := congrArg Additive.ofMul h2
      have g3 := congrArg Additive.ofMul h3
      have g4 := congrArg Additive.ofMul h4
      have g5 := congrArg Additive.ofMul h5
      have g6 := congrArg Additive.ofMul h6
      simp only [ofMul_mul, ofMul_inv, ofMul_one] at g1 g2 g3 g4 g5 g6 ⊢
      linear_combination (norm := abel) g1 - g2 - g4 + g5 + g6
    show gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom _) =
      gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom _)
    rw [germ _ hV₂ z, map_mul, gs_mul (𝟙 _) z ⊤ trivial, germ _ hV₁ z, hgv _ hV₂, hgv _ hV₁, htr, ve,
      show (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (c (-mu) : S) = (unitOn (c (-mu))).val from rfl,
      gs_unit (𝟙 _) z ⊤ trivial, ← Units.val_mul]
    exact congrArg Units.val (_root_.mul_left_comm _ _ _)
  · rw [hval T y z J hJ]
    simp only [_root_.mul_assoc, inv_mul_cancel]

end GlobalTheory.Heat.ShiftGauge
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRaynaudGaugeGeneratorWeightNegStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_raynaudGauge_generator_weight_neg : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (mu : Q.X) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H), (x ≫ Y.q) * Q.c mu = 1 → ∀ ψ₀ : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c mu).left) fun _ => -1), ψ₀.IsGen → ∃ e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1]), e.IsGen ∧ (∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j → IsWt Y (-mu) (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V))) ∧ ∀ (T : Over (Sp R)) (y : T ⟶ Y.H) (z : T.left) (J : (T.left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → val e y.left z J * val ψ₀ T.hom z J * val Q.rig T.hom z J * val ((Y.Φ T (y * (toUnit T ≫ x))).s mu) (𝟙 _) z J = 1 := by
  first | exact @GlobalTheory.Heat.ShiftGauge.exists_gauge | exact GlobalTheory.Heat.ShiftGauge.exists_gauge | (intros; apply GlobalTheory.Heat.ShiftGauge.exists_gauge <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaShiftFourierTermTranslationGauge
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.HeatShift

theorem good_comp' {X Y Z : Scheme.{0}} {L : LB X} (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Good L (r z) (fun ψ => J (r ≫ ψ)) := fun ψ => by
  have := hJ (r ≫ ψ)
  rwa [Scheme.Hom.comp_apply] at this

theorem gs_scal_eq {R : Type} [CommRing R] {X Z : Scheme.{0}} (p : X ⟶ Sp R) (r : Z ⟶ X) (z : Z) (c : R) :
    gs r z ⊤ (scal p c) = cst (r ≫ p) z c := by
  unfold ReciprocityTheory.ChartRestriction.G.Out.scal
  exact gs_pull r p z ⊤ trivial _

theorem cst_add' {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Sp R) (z : Z) (a b : R) :
    cst q z (a + b) = cst q z a + cst q z b := by
  unfold cst; rw [map_add (f := _), gs_add q z ⊤ trivial]

theorem cst_sub' {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Sp R) (z : Z) (a b : R) :
    cst q z (a - b) = cst q z a - cst q z b := by
  have := cst_add' q z (a - b) b
  rw [sub_add_cancel] at this
  rw [this, add_sub_cancel_right]

theorem cst_zero' {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Sp R) (z : Z) : cst q z 0 = 0 := by
  have := cst_add' q z 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem shiftEq_pt {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {k : ℕ} {mu α : Q.X} {σ : Q.SecB k α}
    {σ₁ σ₂ : Q.SecB k (α + k • mu)} {c : R} (H : ShiftEq Q k mu α σ σ₁ c σ₂)
    (u : LB.Gen (LB.LinComb Q.P.L (DegPre.deltaφ Q (FractionRing R) k α mu) (DegPre.deltaε k))) (hu : u.IsGen)
    (hc : LB.Gen.Corr Q.P.L _ _ _ _ (LB.pullGen Q.P.L _ _ u (DegPre.zF Q (FractionRing R)).left)
      (DegPre.famMult Q (FractionRing R) k mu α))
    {Z : Scheme.{0}} (p : Z ⟶ (DegPre.BF Q (FractionRing R)).left) (z : Z)
    (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι) (hJ : Good Q.P.L z J) :
    sval σ₁ (p ≫ (DegPre.prB Q (FractionRing R)).left) z J =
      (val u p z J).val * sval σ (p ≫ (DegPre.trF Q (FractionRing R) mu ≫ DegPre.prB Q (FractionRing R)).left) z J +
        cst (p ≫ (DegPre.BF Q (FractionRing R)).hom) z c * sval σ₂ (p ≫ (DegPre.prB Q (FractionRing R)).left) z J := by
  have e := congrArg (p.stalkMap z).hom (H u hu hc (p z) _ (good_comp' p z hJ))
  rw [GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ hJ, GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ hJ,
    GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ hJ, e, map_add, map_mul, map_mul]
  congr 2
  · have := GlobalTheory.HeatDefect.val_comp_stalk u (𝟙 _) p z hJ
    rw [Category.comp_id] at this
    exact this.symm
  · rw [← GlobalTheory.HeatDefect.gs_comp_stalk p (𝟙 _) z ⊤ trivial, Category.comp_id]
    exact gs_scal_eq _ p z c

theorem der_prod {R : Type} [CommRing R] {m : ℕ} (D : Derivation ℤ R R) (t d : Fin m → R) (hd : ∀ i, D (t i) = d i * t i)
    (N : Fin m → ℕ) : D (∏ i, t i ^ N i) = (∑ i, (N i : R) * d i) * ∏ i, t i ^ N i := by
  have hpow : ∀ i (n : ℕ), D (t i ^ n) = ((n : R) * d i) * t i ^ n := by
    intro i n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Derivation.leibniz, ih, hd, smul_eq_mul, smul_eq_mul]
      push_cast; ring
  have key : ∀ s : Finset (Fin m), D (∏ i ∈ s, t i ^ N i) = (∑ i ∈ s, (N i : R) * d i) * ∏ i ∈ s, t i ^ N i := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, Derivation.leibniz, ih, hpow, smul_eq_mul, smul_eq_mul]
      ring
  exact key _

end GlobalTheory.HeatShift

open GlobalTheory.HeatShift in
theorem GlobalTheory.HeatShift.shift_term : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Dd.toPre.X), IsMonomial Dd.toPre t gam → (∀ i, t i ≠ 0) → ∀ D : Derivation ℤ R R, (∀ i, D (t i) ∈ Ideal.span {t i}) → ∀ mu : Dd.toPre.X, ∃ (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (e : LB.Gen (LB.LinComb Dd.toPre.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])) (β : Dd.toPre.X) (w : Dd.toPre.X →+ R) (π π' : R), e.IsGen ∧ (∀ (j : Fin 2 → Dd.toPre.P.L.ι) (V : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ LB.wchart Dd.toPre.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j → IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V))) ∧ ∀ (k : ℕ) (α : Dd.toPre.X), 1 ≤ k → ∃ a b : R, a ≠ 0 ∧ ∀ (σ : Dd.toPre.SecB k α) (σ₁ : Dd.toPre.SecB k (α + k • mu)) (τ τ₁ ρ : SecM Y.q.left Dd.toPre.P.L k), ShiftEq Dd.toPre k mu α σ σ₁ 0 σ₁ → IsTerm Y k α σ τ → IsTerm Y k (α + k • mu) σ₁ τ₁ → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Dd.toPre.P.A.left) → Dd.toPre.P.L.ι), Good Dd.toPre.P.L z J → sval ρ r z J = sval τ₁ (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J * ((val e r z J) ^ k).val) → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Dd.toPre.P.A.left) → Dd.toPre.P.L.ι), Good Dd.toPre.P.L z J → gs r z ⊤ (scal Y.H.hom a) * sval ρ r z J = gs r z ⊤ (scal Y.H.hom b) * sval τ r z J) ∧ ∀ (σ'' : Dd.toPre.SecB k α) (σ₁' : Dd.toPre.SecB k (α + k • mu)) (τ'' τ₁' ρ' : SecM Y.q.left Dd.toPre.P.L k), IsTerm Y k α σ'' τ'' → IsTerm Y k (α + k • mu) σ₁' τ₁' → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Dd.toPre.P.A.left) → Dd.toPre.P.L.ι), Good Dd.toPre.P.L z J → sval ρ' r z J = sval τ₁' (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J * ((val e r z J) ^ k).val) → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Dd.toPre.P.A.left) → Dd.toPre.P.L.ι), Good Dd.toPre.P.L z J → gs r z ⊤ (scal Y.H.hom a) * sval ρ' r z J + gs r z ⊤ (scal Y.H.hom (2 * (k : R) * D a)) * sval ρ r z J = gs r z ⊤ (scal Y.H.hom b) * sval τ'' r z J + gs r z ⊤ (scal Y.H.hom (2 * (k : R) * D b)) * sval τ r z J) → ShiftEq Dd.toPre k mu α σ'' σ₁' (2 * (k : R) * w α + 2 * (k : R) ^ 2 * π + 2 * (k : R) * π') σ₁ := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y m t gam hmon ht D hD mu
  have hn : ∀ y, ∃ n : Fin m → ℕ, ∀ i, gam i y y = 2 * n i := fun y => by
    obtain ⟨u, n, h, -⟩ := hmon y
    exact ⟨n, h⟩
  choose n hn using hn
  choose ψ₀ hψ₀g hψ₀v using fun χ => GlobalTheory.T.exists_monomialPeriod_unitPart_generator R Dd.toPre m t gam hmon χ (n χ) (hn χ)
  obtain ⟨xp, hxq, hxv⟩ := GlobalTheory.T.exists_raynaudPoint_unitPart_coordinates R Dd.toPre O oa Y m t gam Dd.tau_bimult ht n hn ψ₀ hψ₀g hψ₀v mu
  have hqm : IsMonHom Y.q := Y.q_linear.isMonHom
  have hx : (xp⁻¹ ≫ Y.q) * Dd.toPre.c mu = 1 := by
    rw [← hxq, ← MonObj.mul_comp, inv_mul_cancel, MonObj.one_comp]
  obtain ⟨e, heg, hew, hev⟩ := GlobalTheory.T.exists_raynaudGauge_generator_weight_neg R Dd.toPre O oa Y mu xp⁻¹ hx (ψ₀ mu) (hψ₀g mu)
  have hd : ∀ i, ∃ d : R, D (t i) = d * t i := fun i => by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (hD i)
    exact ⟨c, by rw [hc, mul_comm]⟩
  choose d hd using hd
  have n0 : ∀ i, n 0 i = 0 := fun i => by
    have := hn 0 i
    simp at this
    omega
  have fadd : ∀ (a b : Dd.toPre.X) i, ((n (mu + (a + b)) i : ℤ) - n mu i - n (a + b) i) =
      ((n (mu + a) i : ℤ) - n mu i - n a i) + ((n (mu + b) i : ℤ) - n mu i - n b i) := by
    intro a b i
    have h1 := hn (mu + (a + b)) i
    have h2 := hn mu i
    have h3 := hn (a + b) i
    have h4 := hn (mu + a) i
    have h5 := hn a i
    have h6 := hn (mu + b) i
    have h7 := hn b i
    simp only [map_add (f := _), LinearMap.add_apply] at h1 h3 h4 h6
    linarith
  let w : Dd.toPre.X →+ R :=
    { toFun := fun a => ∑ i, ((((n (mu + a) i : ℤ) - n mu i - n a i : ℤ)) : R) * d i
      map_zero' := by simp [n0]
      map_add' := fun a b => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [fadd a b i]
        push_cast
        ring }
  refine ⟨xp⁻¹, e, -mu, w, ∑ i, (n mu i : R) * d i, 0, heg, hew, ?_⟩
  intro k α hk

  have ht0 : ∀ N : Fin m → ℕ, (∏ i, t i ^ N i) ≠ 0 := fun N =>
    Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (ht i)
  have hjFK : IsIso (jFK (R := R) (FractionRing R)) := by
    have : IsIso (CommRingCat.ofHom (algebraMap (FractionRing R) (FractionRing R))) := by
      rw [Algebra.algebraMap_self]
      exact inferInstanceAs (IsIso (𝟙 (CommRingCat.of (FractionRing R))))
    infer_instance

  have htr : ∀ (T : Over (Sp R)) (pp : T ⟶ DegPre.BF Dd.toPre (FractionRing R)) (yp : T ⟶ Y.H),
      pp ≫ DegPre.prB Dd.toPre (FractionRing R) = yp ≫ Y.q →
      pp ≫ DegPre.trF Dd.toPre (FractionRing R) mu ≫ DegPre.prB Dd.toPre (FractionRing R) = (yp * (toUnit T ≫ xp)) ≫ Y.q := by
    intro T pp yp h
    rw [DegPre.trF, lift_snd, show ∀ f g : DegPre.BF Dd.toPre (FractionRing R) ⟶ Dd.toPre.P.A, padd Dd.toPre.P.A f g = f * g from
      fun _ _ => rfl, MonObj.comp_mul, MonObj.mul_comp, h, ← Category.assoc, comp_toUnit, Category.assoc, hxq]
  have hsq : ∀ (T : Over (Sp R)) (y : T ⟶ Y.H), (y * (toUnit T ≫ xp⁻¹)) * (toUnit T ≫ xp) = y := by
    intro T y
    rw [_root_.mul_assoc, ← MonObj.comp_mul, _root_.inv_mul_cancel, MonObj.comp_one, _root_.mul_one]
  have hTx : ∀ (T : Over (Sp R)) (y : T ⟶ Y.H), y ≫ (𝟙 Y.H * (toUnit Y.H ≫ xp⁻¹)) = y * (toUnit T ≫ xp⁻¹) := by
    intro T y
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]
  set A₀ : R := ∏ i, t i ^ n (mu + α) i with hA₀
  set B₀ : R := ∏ i, t i ^ (n mu i + n α i) with hB₀
  set P₀ : R := ∏ i, t i ^ n mu i with hP₀
  set b : R := ∏ i, t i ^ (k * n mu i + n (mu + α) i) with hb
  have hb' : b = P₀ ^ k * A₀ := by
    rw [hb, hP₀, hA₀, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [pow_add, mul_comm k, pow_mul]
  refine ⟨B₀, b, ht0 _, ?_⟩
  intro σ σ₁ τ τ₁ ρ hS hT hT₁ hρ

  have key := fun u hu hc => GlobalTheory.T.raynaudShift_unitIdentity_fractionField R Dd.toPre O oa Y Dd.tau_bimult k mu α xp A₀ B₀ P₀ (ψ₀ mu) e hxq
    (fun Z g z J hJ => hxv Z g α z J hJ) (fun Z g z J hJ => hψ₀v mu Z g z J hJ) hev u hu hc
  obtain ⟨⟨u, hu, hc⟩, -⟩ := gen_fe (D := Dd.toPre) (F := FractionRing R) GlobalTheory.SemiRigid.globalFns k mu α
  have C1 : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Dd.toPre.P.A.left) → Dd.toPre.P.L.ι),
      Good Dd.toPre.P.L z J → gs r z ⊤ (scal Y.H.hom B₀) * sval ρ r z J = gs r z ⊤ (scal Y.H.hom b) * sval τ r z J := by
    refine GlobalTheory.T.raynaud_section_identity_of_generic_fibre R Dd.toPre O oa Y k ρ τ B₀ b fun Z g r hr z J hJ => ?_
    let T : Over (Sp R) := Over.mk (g ≫ jK R)
    let y : T ⟶ Y.H := Over.homMk r hr
    let yp : T ⟶ Y.H := y * (toUnit T ≫ xp⁻¹)
    let pp : T ⟶ DegPre.BF Dd.toPre (FractionRing R) :=
      lift (Over.homMk (g ≫ inv (jFK (R := R) (FractionRing R))) (by
        show (g ≫ inv (jFK (R := R) (FractionRing R))) ≫ jFK (R := R) (FractionRing R) ≫ jK R = g ≫ jK R
        rw [Category.assoc, IsIso.inv_hom_id_assoc])) (yp ≫ Y.q)
    have hpp1 : (pp ≫ fst _ _).left ≫ jFK (R := R) (FractionRing R) = g := by
      simp [pp]
    have hpp2 : pp ≫ DegPre.prB Dd.toPre (FractionRing R) = yp ≫ Y.q := lift_snd _ _
    have hK := key u hu hc Z g pp yp hpp1 hpp2 z J hJ
    rw [hsq T y] at hK
    have hsh := shiftEq_pt hS u hu hc pp.left z J hJ
    rw [cst_zero', zero_mul, add_zero, ← Over.comp_left, ← Over.comp_left, hpp2, htr T pp yp hpp2, hsq T y] at hsh
    have e1 := hρ Z r z J hJ
    have e1' : r ≫ (𝟙 Y.H * (toUnit Y.H ≫ xp⁻¹)).left = yp.left := by
      show y.left ≫ _ = _
      rw [← Over.comp_left]; exact congrArg (·.left) (hTx T y)
    rw [e1'] at e1
    have e2 := hT₁ T yp z J hJ
    have e3 : sval τ r z J = _ := hT T y z J hJ
    rw [gs_scal_eq, gs_scal_eq, hr]
    rw [e1, e2, e3, hsh, hb']
    have fin : ∀ {S : Type} [CommRing S] (cA cB U s S' E X : S), cA * U * S' * E = cB * X →
        cA * (U * s * S' * E) = cB * (s * X) := fun cA cB U s S' E X h => by linear_combination s * h
    exact fin _ _ _ _ _ _ _ hK

  refine ⟨C1, ?_⟩
  intro σ'' σ₁' τ'' τ₁' ρ' hT'' hT₁' hρ' hL u' hu' hc' z J hJ
  obtain ⟨Z, p, w0, y0, rfl, hepi, hinj, hyq⟩ := GlobalTheory.T.exists_flat_epi_lift_raynaud_extension_fraction_point R Dd.toPre O oa Y z
  have hJ₁ : ∃ J₁ : (Z ⟶ Dd.toPre.P.A.left) → Dd.toPre.P.L.ι, Good Dd.toPre.P.L w0 J₁ ∧ ∀ ψ, J₁ (p ≫ ψ) = J ψ := by
    classical
    refine ⟨fun φ => if h : ∃ ψ, p ≫ ψ = φ then J h.choose else (exists_chart Dd.toPre.P.isLB (φ w0)).choose,
      fun φ => ?_, fun ψ => ?_⟩
    · by_cases h : ∃ ψ, p ≫ ψ = φ
      · simp only [dif_pos h]
        have e := h.choose_spec
        have : (p ≫ h.choose) w0 ∈ Dd.toPre.P.L.U (J h.choose) := by
          rw [Scheme.Hom.comp_apply]; exact hJ _
        rwa [e] at this
      · simp only [dif_neg h]
        exact (exists_chart Dd.toPre.P.isLB (φ w0)).choose_spec
    · have h : ∃ ψ', p ≫ ψ' = p ≫ ψ := ⟨ψ, rfl⟩
      simp only [dif_pos h]
      exact congrArg J ((cancel_epi p).1 h.choose_spec)
  obtain ⟨J₁, gJ₁, eJ₁⟩ := hJ₁
  have eJ : J = fun ψ => J₁ (p ≫ ψ) := funext fun ψ => (eJ₁ ψ).symm
  subst eJ
  apply hinj
  have hv := GlobalTheory.HeatDefect.val_comp_stalk u' (𝟙 _) p w0 gJ₁
  rw [Category.comp_id] at hv
  rw [map_add (f := _), map_mul, map_mul, ← GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ gJ₁, ← GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ gJ₁,
    ← GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ gJ₁, ← hv, ← GlobalTheory.HeatDefect.gs_comp_stalk p (𝟙 _) w0 ⊤ trivial,
    Category.comp_id, gs_scal_eq]
  clear hv eJ₁ hJ hinj
  set g : Z ⟶ (TK R).left := p ≫ (fst (TF (R := R) (FractionRing R)) Dd.toPre.P.A).left ≫ jFK (R := R) (FractionRing R)
    with hg
  have hpB : p ≫ (DegPre.BF Dd.toPre (FractionRing R)).hom = g ≫ jK R := by
    rw [← Over.w (fst (TF (R := R) (FractionRing R)) Dd.toPre.P.A), hg]
    simp only [Category.assoc]
    rfl
  let T : Over (Sp R) := Over.mk (g ≫ jK R)
  let pp : T ⟶ DegPre.BF Dd.toPre (FractionRing R) := Over.homMk p hpB
  let yp : T ⟶ Y.H := Over.homMk y0 (by
    show y0 ≫ Y.H.hom = g ≫ jK R
    rw [← Over.w Y.q, ← Category.assoc, hyq, Category.assoc, Over.w (DegPre.prB Dd.toPre (FractionRing R)), hpB])
  have hpp1 : (pp ≫ fst _ _).left ≫ jFK (R := R) (FractionRing R) = g := by
    rw [hg]; simp [pp]
  have hpp2 : pp ≫ DegPre.prB Dd.toPre (FractionRing R) = yp ≫ Y.q := Over.OverMorphism.ext hyq.symm
  let y : T ⟶ Y.H := yp * (toUnit T ≫ xp)
  let r : Z ⟶ Y.H.left := y.left
  have hyy : y * (toUnit T ≫ xp⁻¹) = yp := by
    show yp * (toUnit T ≫ xp) * (toUnit T ≫ xp⁻¹) = yp
    rw [_root_.mul_assoc, ← MonObj.comp_mul, _root_.mul_inv_cancel, MonObj.comp_one, _root_.mul_one]
  have rT : r ≫ (𝟙 Y.H * (toUnit Y.H ≫ xp⁻¹)).left = yp.left := by
    show y.left ≫ _ = _
    rw [← Over.comp_left, hTx T y, hyy]
  have hrH : r ≫ Y.H.hom = g ≫ jK R := Over.w y
  have q1 : p ≫ (DegPre.prB Dd.toPre (FractionRing R)).left = (yp ≫ Y.q).left := congrArg (·.left) hpp2
  have q2 : p ≫ (DegPre.trF Dd.toPre (FractionRing R) mu ≫ DegPre.prB Dd.toPre (FractionRing R)).left = (y ≫ Y.q).left :=
    congrArg (·.left) (htr T pp yp hpp2)
  rw [q1, q2, hpB]
  have f1 := hρ' Z r w0 J₁ gJ₁
  rw [rT] at f1
  have f2 := hρ Z r w0 J₁ gJ₁
  rw [rT] at f2
  have f3 := hT₁' T yp w0 J₁ gJ₁
  have f4 := hT₁ T yp w0 J₁ gJ₁
  have f5 := hT'' T y w0 J₁ gJ₁
  have f6 := hT T y w0 J₁ gJ₁
  have f7 := C1 Z r w0 J₁ gJ₁
  have f8 := hL Z r w0 J₁ gJ₁
  have f9 := key u' hu' hc' Z g pp yp hpp1 hpp2 w0 J₁ gJ₁
  simp only [gs_scal_eq, hrH] at f7 f8
  set δa : R := ∑ i, ((n mu i + n α i : ℕ) : R) * d i with hδa
  set δb : R := ∑ i, ((k * n mu i + n (mu + α) i : ℕ) : R) * d i with hδb
  have hDa : 2 * (k : R) * D B₀ = (2 * k * δa) * B₀ := by
    rw [hB₀, der_prod D t d hd (fun i => n mu i + n α i)]; ring
  have hDb : 2 * (k : R) * D b = (2 * k * δb) * b := by
    rw [hb, der_prod D t d hd (fun i => k * n mu i + n (mu + α) i)]; ring
  rw [hDa, hDb, ReciprocityTheory.ChartRestriction.G.H1.cst_mul _ _ (2 * (k : R) * δa) B₀, ReciprocityTheory.ChartRestriction.G.H1.cst_mul _ _ (2 * (k : R) * δb) b] at f8
  have hw : (w α : R) = ∑ i, ((((n (mu + α) i : ℤ) - n mu i - n α i : ℤ)) : R) * d i := rfl
  have hc1 : 2 * (k : R) * w α + 2 * (k : R) ^ 2 * (∑ i, (n mu i : R) * d i) + 2 * (k : R) * 0 =
      2 * k * δb - 2 * k * δa := by
    rw [hw, hδa, hδb]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  have e10 : cst (g ≫ jK R) w0 (2 * (k : R) * w α + 2 * (k : R) ^ 2 * (∑ i, (n mu i : R) * d i) + 2 * (k : R) * 0) =
      cst (g ≫ jK R) w0 (2 * k * δb) - cst (g ≫ jK R) w0 (2 * k * δa) := by
    rw [hc1, cst_sub']
  have hU : IsUnit (cst (g ≫ jK R) w0 B₀ * (val ((Y.Φ T yp).s (α + k • mu)) (𝟙 Z) w0 J₁).val * (val e r w0 J₁ ^ k).val) :=
    ((GlobalTheory.ExpInt.isUnit_cst g w0 (ht0 _)).mul (Units.isUnit _)).mul (Units.isUnit _)
  rw [hb'] at f7 f8
  have fin2 : ∀ {S : Type} [CommRing S] (cA cB C dA dB U S' E X s1' s'' s1 ρ' ρ τ'' τ τ₁' τ₁ : S),
      IsUnit (cA * S' * E) → ρ' = τ₁' * E → ρ = τ₁ * E → τ₁' = s1' * S' → τ₁ = s1 * S' → τ'' = s'' * X →
      cA * ρ = cB * τ → cA * ρ' + (dA * cA) * ρ = cB * τ'' + (dB * cB) * τ → cA * U * S' * E = cB * X →
      C = dB - dA → s1' = U * s'' + C * s1 := by
    intro S _ cA cB C dA dB U S' E X s1' s'' s1 ρ' ρ τ'' τ τ₁' τ₁ hu e1 e3 e2 e4 e5 e7 e8 e9 e10
    have k0 : (cA * S' * E) * (s1' - (U * s'' + C * s1)) = 0 := by
      linear_combination e8 - dB * e7 - cA * ρ * e10 - cA * e1 - cA * E * e2 - s'' * e9 + cB * e5 + C * cA * e3 +
        C * cA * E * e4
    exact sub_eq_zero.1 (hu.mul_right_eq_zero.1 k0)
  exact fin2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hU f1 f2 f3 f4 f5 f7 f8 f9 e10
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaShiftFourierTermTranslationGaugeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaShift_fourierTerm_translation_gauge : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Dd.toPre.X), IsMonomial Dd.toPre t gam → (∀ i, t i ≠ 0) → ∀ D : Derivation ℤ R R, (∀ i, D (t i) ∈ Ideal.span {t i}) → ∀ mu : Dd.toPre.X, ∃ (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (e : LB.Gen (LB.LinComb Dd.toPre.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])) (β : Dd.toPre.X) (w : Dd.toPre.X →+ R) (π π' : R), e.IsGen ∧ (∀ (j : Fin 2 → Dd.toPre.P.L.ι) (V : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ LB.wchart Dd.toPre.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j → IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V))) ∧ ∀ (k : ℕ) (α : Dd.toPre.X), 1 ≤ k → ∃ a b : R, a ≠ 0 ∧ ∀ (σ : Dd.toPre.SecB k α) (σ₁ : Dd.toPre.SecB k (α + k • mu)) (τ τ₁ ρ : SecM Y.q.left Dd.toPre.P.L k), ShiftEq Dd.toPre k mu α σ σ₁ 0 σ₁ → IsTerm Y k α σ τ → IsTerm Y k (α + k • mu) σ₁ τ₁ → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Dd.toPre.P.A.left) → Dd.toPre.P.L.ι), Good Dd.toPre.P.L z J → sval ρ r z J = sval τ₁ (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J * ((val e r z J) ^ k).val) → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Dd.toPre.P.A.left) → Dd.toPre.P.L.ι), Good Dd.toPre.P.L z J → gs r z ⊤ (scal Y.H.hom a) * sval ρ r z J = gs r z ⊤ (scal Y.H.hom b) * sval τ r z J) ∧ ∀ (σ'' : Dd.toPre.SecB k α) (σ₁' : Dd.toPre.SecB k (α + k • mu)) (τ'' τ₁' ρ' : SecM Y.q.left Dd.toPre.P.L k), IsTerm Y k α σ'' τ'' → IsTerm Y k (α + k • mu) σ₁' τ₁' → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Dd.toPre.P.A.left) → Dd.toPre.P.L.ι), Good Dd.toPre.P.L z J → sval ρ' r z J = sval τ₁' (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J * ((val e r z J) ^ k).val) → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Dd.toPre.P.A.left) → Dd.toPre.P.L.ι), Good Dd.toPre.P.L z J → gs r z ⊤ (scal Y.H.hom a) * sval ρ' r z J + gs r z ⊤ (scal Y.H.hom (2 * (k : R) * D a)) * sval ρ r z J = gs r z ⊤ (scal Y.H.hom b) * sval τ'' r z J + gs r z ⊤ (scal Y.H.hom (2 * (k : R) * D b)) * sval τ r z J) → ShiftEq Dd.toPre k mu α σ'' σ₁' (2 * (k : R) * w α + 2 * (k : R) ^ 2 * π + 2 * (k : R) * π') σ₁ := by
  first | exact @GlobalTheory.HeatShift.shift_term | exact GlobalTheory.HeatShift.shift_term | (intros; apply GlobalTheory.HeatShift.shift_term <;> assumption)
end
