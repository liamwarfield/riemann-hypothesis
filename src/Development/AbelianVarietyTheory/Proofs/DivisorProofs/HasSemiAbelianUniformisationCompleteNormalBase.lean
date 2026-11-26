module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedOfDegDataFactor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelledCoverUnitaryPELTypeFiniteExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicFactorOfUnimodularTensor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerRingActionOnTensorDegenerationDataA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegDataUnitaryTypeStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsSecTieFModel
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PtTie

section Move
open GlobalTheory.FieldBaseChange
variable {X' X X₁ X₂ Y Y₁ : Scheme.{0}} {L' : LB X'}

def isoFromPullId {L : LB X} {m : X' ⟶ X} (w : LB.Iso L' (L.pull m)) : LB.Iso (L'.pull (𝟙 X')) (L.pull m) :=
  ⟨fun p => res (fun _ hy => ⟨hy.1, mem_pull.1 hy.2⟩ :
    (L.pull m).U p.1 ⊓ (L'.pull (𝟙 X')).U p.2 ≤ (L.pull m).U p.1 ⊓ L'.U (p.2 PUnit.unit)) (w.s (p.1, p.2 PUnit.unit))⟩

theorem isoVal_isoFromPullId {L : LB X} {m : X' ⟶ X} (w : LB.Iso L' (L.pull m)) {Z : Scheme.{0}} (r : Z ⟶ X') (z : Z)
    (j : L.ι) (k : L'.ι) (hj : m (r z) ∈ L.U j) (hk : r z ∈ L'.U k) :
    isoVal (isoFromPullId w) r z j k = gv w r z (fun _ => j) k := by
  have hm : r z ∈ (L.pull m).U (fun _ => j) ⊓ (L'.pull (𝟙 X')).U (fun _ => k) := ⟨mem_pull.2 hj, mem_pull.2 hk⟩
  show gm r z _ (res _ (w.s (fun _ => j, k))) = _
  exact gm_res r z _ hm _

theorem isoFromPullId_isGen {L : LB X} {m : X' ⟶ X} {w : LB.Iso L' (L.pull m)} (hw : w.IsGen) :
    (isoFromPullId w).IsGen := by
  refine (isGen_iff _).2 fun Z r z j j' k k' hj hj' hk hk' => ?_
  have ik : r z ∈ L'.U (k PUnit.unit) := (mem_pull (F := 𝟙 X') (x := r z)).1 hk
  have ik' : r z ∈ L'.U (k' PUnit.unit) := (mem_pull (F := 𝟙 X') (x := r z)).1 hk'
  have a := isoVal_isoFromPullId w r z j (k PUnit.unit) hj ik
  have a' := isoVal_isoFromPullId w r z j' (k' PUnit.unit) hj' ik'
  have b := (isGen_iff w).1 hw Z r z j j' _ _ hj hj' ik ik'
  have c := (gm_pull_g L' (𝟙 X') r z k k' hk hk').trans
    (congrArg (fun f : Z ⟶ X' => gm f z _ (L'.g (k PUnit.unit) (k' PUnit.unit))) (Category.comp_id r))
  refine a.trans (b.trans ?_)
  exact congrArg₂ (fun s t => _ * s⁻¹ * t) c.symm a'.symm

end Move

section Comparison₂
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {y : letI := io.toAlgebra; FrPt Xo c T.Fr}
  {I : IntData Xo c T io y} {F : Type} [Field F] [Algebra T.Fr F] {xF : Sp F ⟶ Xo.X}

variable (I) (P : PELUnif (maximalIdeal T.V) I.G)

end Comparison₂

end GlobalTheory.PtTie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryPELTypeFactorDegData
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorDegenerationDataOfUnimodularPosDef
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorPreDataRigidificationInvPsiZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorTrivialisationPowerLatticePoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorTrivialisationPowerLatticePoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.tensPsi_exists : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (A' : Over (Spec (CommRingCat.of R))) [GrpObj A'] (L' : LB A'.left), L'.IsLB → ∀ (pr : Fin r → (A' ⟶ D.P.A)) (w : LB.Iso L' (LB.LinComb D.P.L (tensφ pr) (tensε W))), w.IsGen → ∀ (x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ A') (y : Fin r → D.X), (∀ i, x ≫ pr i = D.c (y i)) → ∃ ψ : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => ptK x) (fun _ => -1)), ψ.IsGen ∧ ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι) (J' : ((TK R).left ⟶ A'.left) → L'.ι), Good D.P.L z J → Good L' z J' → val ψ (𝟙 _) z J' = gm (ptK x) z _ (w.s (fun k => J (ptK x ≫ tensφ pr k), J' (ptK x))) * ∏ i, ∏ j, val (D.tau (y i) (y j)) (𝟙 _) z J ^ W i j := by
  intro R _ _ D r W A' _ L' hL pr w hw x y hx
  exact GlobalTheory.Mum.TraitWit.exists_psi D W hL pr hw (toUnit (TK R) ≫ x) y (fun i => by rw [Category.assoc, hx])
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorTrivialisationPowerLatticePointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensorTrivialisation_powerLattice_points : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (A' : Over (Spec (CommRingCat.of R))) [GrpObj A'] (L' : LB A'.left), L'.IsLB → ∀ (pr : Fin r → (A' ⟶ D.P.A)) (w : LB.Iso L' (LB.LinComb D.P.L (tensφ pr) (tensε W))), w.IsGen → ∀ (x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ A') (y : Fin r → D.X), (∀ i, x ≫ pr i = D.c (y i)) → ∃ ψ : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => ptK x) (fun _ => -1)), ψ.IsGen ∧ ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι) (J' : ((TK R).left ⟶ A'.left) → L'.ι), Good D.P.L z J → Good L' z J' → val ψ (𝟙 _) z J' = gm (ptK x) z _ (w.s (fun k => J (ptK x ≫ tensφ pr k), J' (ptK x))) * ∏ i, ∏ j, val (D.tau (y i) (y j)) (𝟙 _) z J ^ W i j := by
  first | exact @GlobalTheory.Mum.tensPsi_exists | exact GlobalTheory.Mum.tensPsi_exists | (intros; apply GlobalTheory.Mum.tensPsi_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorPreDataRigidificationInvPsiZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.TensData

def cpt {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {r : ℕ} {P' : PolAV (Spec (CommRingCat.of R))}
    {pr : Fin r → (P'.A ⟶ D.P.A)} (lim : IsLimit (Fan.mk P'.A pr)) (y : Fin r → D.X) :
    𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P'.A :=
  lim.lift (Fan.mk _ fun i => D.c (y i))

theorem cpt_pr {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {r : ℕ} {P' : PolAV (Spec (CommRingCat.of R))}
    {pr : Fin r → (P'.A ⟶ D.P.A)} (lim : IsLimit (Fan.mk P'.A pr)) (y : Fin r → D.X) (i : Fin r) :
    cpt lim y ≫ pr i = D.c (y i) :=
  lim.fac (Fan.mk _ fun i => D.c (y i)) ⟨i⟩

theorem cpt_add {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {r : ℕ} {P' : PolAV (Spec (CommRingCat.of R))}
    {pr : Fin r → (P'.A ⟶ D.P.A)} (hpr : ∀ i, IsMonHom (pr i)) (lim : IsLimit (Fan.mk P'.A pr)) (a b : Fin r → D.X) :
    cpt lim (a + b) = padd P'.A (cpt lim a) (cpt lim b) := by
  refine lim.hom_ext fun ⟨i⟩ => ?_
  show cpt lim (a + b) ≫ pr i = padd P'.A (cpt lim a) (cpt lim b) ≫ pr i
  have := hpr i
  rw [cpt_pr, padd, Category.assoc, IsMonHom.mul_hom, lift_map_assoc, cpt_pr, cpt_pr]
  exact D.c_add _ _

theorem cpt_zero {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {r : ℕ} {P' : PolAV (Spec (CommRingCat.of R))}
    {pr : Fin r → (P'.A ⟶ D.P.A)} (hpr : ∀ i, IsMonHom (pr i)) (lim : IsLimit (Fan.mk P'.A pr)) :
    cpt lim (0 : Fin r → D.X) = η[P'.A] := by
  refine lim.hom_ext fun ⟨i⟩ => ?_
  show cpt lim 0 ≫ pr i = η[P'.A] ≫ pr i
  have := hpr i
  rw [cpt_pr, IsMonHom.one_hom]
  have h := D.c_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

end GlobalTheory.Mum.TensData
end


open GlobalTheory.Mum.TensData in
theorem GlobalTheory.Mum.TensData.main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∃ (D' : DegPre R) (_ : Tens D.toPre D' W), ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val (D'.psi 0) (𝟙 _) z J * val D'.rigK (𝟙 _) z J = 1 := by
  intro R _ _ _ hA D r W hW hdet
  haveI : IsNoetherianRing R := hA.1
  obtain ⟨P', pr, hpr, ⟨lim⟩, -, ⟨w, hw⟩⟩ := GlobalTheory.Mum.PowPol.exists_pow_polAV R D.toPre.P W hW hdet
  obtain ⟨sym, hsym, hsr⟩ := GlobalTheory.SelfUnif.exists_sym P'
  obtain ⟨rig, hrig, hrv⟩ := GlobalTheory.T.exists_tensorBundleRigidification R D.toPre W P'.A P'.L P'.isLB pr hpr w hw
  have hL : Laws := GlobalTheory.lawsAndExpansions.1.1
  have cub := (hL.cube _ P' ⟨P'.L, rig, P'.isLB, hrig⟩ rfl).1.some
  choose psi hpsi hpv using fun y : Fin r → D.toPre.X =>
    GlobalTheory.T.exists_tensorTrivialisation_powerLattice_points R D.toPre W P'.A P'.L P'.isLB pr w hw (cpt lim y) y (cpt_pr lim y)
  let D' : DegPre R :=
    { P := P'
      rig := rig
      rig_gen := hrig
      cub := cub
      sym := sym
      sym_gen := hsym
      sym_rig := hsr
      X := Fin r → D.toPre.X
      c := cpt lim
      c_add := cpt_add hpr lim
      psi := psi
      psi_gen := hpsi }
  refine ⟨D', ⟨pr, hpr, lim, AddEquiv.refl _, fun y i => cpt_pr lim y i, w, hw, fun y z J J' hJ hJ' => hpv y z J J' hJ hJ'⟩,
    fun z J' hJ' => ?_⟩
  obtain ⟨J, hJ, -⟩ := exists_good D.toPre.P.L D.toPre.P.isLB z (K := PEmpty) PEmpty.elim PEmpty.elim
    (fun a => a.elim) (fun a => a.elim)
  have hτ : ∀ a b : D.toPre.X, a = 0 → b = 0 → val (D.toPre.tau a b) (𝟙 _) z J = 1 := by
    rintro a b rfl rfl
    have vρ : val D.toPre.rigK (𝟙 _) z J = val D.toPre.rig (jK R) z J := by
      refine (val_pull hJ _ _ _).trans ?_
      rw [Category.id_comp]
      rfl
    have hp : ∀ b : D.toPre.X, b = 0 → val (D.toPre.psi b) (𝟙 _) z J = val (D.toPre.psi 0) (𝟙 _) z J := by
      rintro b rfl; rfl
    have e : val (D.toPre.tau 0 0) (𝟙 _) z J = val (D.toPre.psi (0 + 0)) (𝟙 _) z J * (val (D.toPre.psi 0) (𝟙 _) z J)⁻¹ *
        (val (D.toPre.psi 0) (𝟙 _) z J)⁻¹ * (val D.toPre.rigK (𝟙 _) z J)⁻¹ :=
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
    rw [e, hp (0 + 0) (by simp), vρ, GlobalTheory.PsiZero.val_psi_zero D.tau_bimult hJ]
    group
  have h1 := hpv 0 z J J' hJ hJ'
  have h2 := hrv z J J' hJ hJ'
  have hprod : (∏ i, ∏ j, val (D.toPre.tau ((0 : Fin r → D.toPre.X) i) ((0 : Fin r → D.toPre.X) j)) (𝟙 _) z J ^ W i j) = 1 :=
    Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => by rw [hτ ((0 : Fin r → D.toPre.X) i) ((0 : Fin r → D.toPre.X) j) rfl rfl, one_zpow]
  rw [hprod, _root_.mul_one] at h1
  show val (psi 0) (𝟙 _) z J' * val (LB.pullGen P'.L _ _ rig (toUnit (TK R)).left) (𝟙 _) z J' = 1
  rw [h1, _root_.mul_comm]
  have hz := cpt_zero hpr lim (D := D.toPre)
  revert h2
  generalize cpt lim 0 = x at hz ⊢
  subst hz
  exact id
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorPreDataRigidificationInvPsiZeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensorPreData_rigidification_inv_psi_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∃ (D' : DegPre R) (_ : Tens D.toPre D' W), ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val (D'.psi 0) (𝟙 _) z J * val D'.rigK (𝟙 _) z J = 1 := by
  first | exact @GlobalTheory.Mum.TensData.main | exact GlobalTheory.Mum.TensData.main | (intros; apply GlobalTheory.Mum.TensData.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataTauBimultiplicative
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataTauBimultiplicative
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

open ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.TensBimult

theorem alg {U X X' : Type} [CommGroup U] [AddCommGroup X] [AddCommGroup X'] {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (e : X' ≃+ (Fin r → X)) (Ψ : X → U) (ρ : U) (O ψ' : X' → U) (τ' : X' → X' → U) (t : X → X → U) (c' rig' : U)
    (a a' b : X') (ht : ∀ u v, t u v = Ψ (u + v) * (Ψ u)⁻¹ * (Ψ v)⁻¹ * ρ⁻¹)
    (hψ : ∀ u, ψ' u = O u * ∏ i, ∏ j, t (e u i) (e u j) ^ W i j)
    (hτ : ∀ u v, τ' u v = ψ' (u + v) * (ψ' u)⁻¹ * (ψ' v)⁻¹ * rig'⁻¹) (hr : ψ' 0 * rig' = 1)
    (hc : c' * (O (a + a' + b) * (O (a + a'))⁻¹ * (O (a + b))⁻¹ * (O (a' + b))⁻¹ * O a * O a' * O b * (O 0)⁻¹) =
      ∏ k : (Fin r × Fin r) × Fin 4,
        (t (![e a k.1.1 + e a k.1.2, e a k.1.1, e a k.1.2, 0] k.2) (![e b k.1.1 + e b k.1.2, e b k.1.1, e b k.1.2, 0] k.2) *
          t (![e a' k.1.1 + e a' k.1.2, e a' k.1.1, e a' k.1.2, 0] k.2) (![e b k.1.1 + e b k.1.2, e b k.1.1, e b k.1.2, 0] k.2) *
          (t (![e a k.1.1 + e a k.1.2, e a k.1.1, e a k.1.2, 0] k.2 + ![e a' k.1.1 + e a' k.1.2, e a' k.1.1, e a' k.1.2, 0] k.2)
            (![e b k.1.1 + e b k.1.2, e b k.1.1, e b k.1.2, 0] k.2))⁻¹) ^ tensε W k) :
    τ' (a + a') b * c' = τ' a b * τ' a' b := by
  have hr' : rig'⁻¹ = ψ' 0 := (eq_inv_of_mul_eq_one_right hr).symm ▸ inv_inv _
  rw [eq_mul_inv_of_mul_eq hc, hτ, hτ, hτ, hr']
  simp only [hψ, ht, Fintype.prod_prod_type, Fin.prod_univ_four, tensε, Oε, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, map_add, Pi.add_apply, map_zero, Pi.zero_apply,
    add_zero, zero_add]
  have e1 : ∀ x x1, Ψ (e a x + e a x1 + (e a' x + e a' x1) + (e b x + e b x1)) = Ψ (e a x + e a' x + e b x + (e a x1 + e a' x1 + e b x1)) := fun x x1 => congrArg Ψ (by abel)
  have e2 : ∀ x x1, Ψ (e a x + e a x1 + (e a' x + e a' x1)) = Ψ (e a x + e a' x + (e a x1 + e a' x1)) := fun x x1 => congrArg Ψ (by abel)
  have e3 : ∀ x x1, Ψ (e a x + e a x1 + (e b x + e b x1)) = Ψ (e a x + e b x + (e a x1 + e b x1)) := fun x x1 => congrArg Ψ (by abel)
  have e4 : ∀ x x1, Ψ (e a' x + e a' x1 + (e b x + e b x1)) = Ψ (e a' x + e b x + (e a' x1 + e b x1)) := fun x x1 => congrArg Ψ (by abel)
  simp only [e1, e2, e3, e4]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_prod, ofMul_zpow, smul_add, smul_neg, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, _root_.mul_one, mul_neg, neg_smul]
  abel

end GlobalTheory.TensBimult

namespace GlobalTheory.TensBimult

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), Tens D.toPre D' W → (∀ (z : (TK R).left) (J : ((TK R).left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val (D'.psi 0) (𝟙 _) z J * val D'.rigK (𝟙 _) z J = 1) → D'.TauBimult := by
  intro R _ _ _ _ D D' r W T hn a a' b
  have hG : GlobalFnsSt := GlobalTheory.lawsAndExpansions.1.1.globalFns
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ : ∃ J, Good D.toPre.P.L y J :=
    ⟨fun ψ => (exists_chart D.toPre.P.isLB (ψ y)).choose, fun ψ => (exists_chart D.toPre.P.isLB (ψ y)).choose_spec⟩
  have key := GlobalTheory.T.tensorPreData_cubicalStructure_eq_prod_pulled_back hG R D.toPre D' W T (TK R) y J J' hJ hJ' (cP D' _ a) (cP D' _ a') (cP D' _ b)
  have hψ : ∀ u, val (D'.psi u) (𝟙 _) y J' = gm (cP D' (TK R) u).left y _ (T.w.s (fun k => J ((cP D' (TK R) u).left ≫ tensφ T.pr k), J' (cP D' (TK R) u).left)) * ∏ i, ∏ j, val (D.toPre.tau (T.xe u i) (T.xe u j)) (𝟙 _) y J ^ W i j :=
    fun u => T.psi u y J J' hJ hJ'
  have vt : ∀ u v, val (D'.tau u v) (𝟙 _) y J' = val (D'.psi (u + v)) (𝟙 _) y J' * (val (D'.psi u) (𝟙 _) y J')⁻¹ * (val (D'.psi v) (𝟙 _) y J')⁻¹ * (val D'.rigK (𝟙 _) y J')⁻¹ := by
    intro u v; simp only [DegPre.tau, val_mul hJ', val_inv]
  have vtE : ∀ u v, val (D.toPre.tau u v) (𝟙 _) y J = val (D.toPre.psi (u + v)) (𝟙 _) y J * (val (D.toPre.psi u) (𝟙 _) y J)⁻¹ * (val (D.toPre.psi v) (𝟙 _) y J)⁻¹ * (val D.toPre.rigK (𝟙 _) y J)⁻¹ := by
    intro u v; simp only [DegPre.tau, val_mul hJ, val_inv]
  have hB : ∀ u u' v, val (D.toPre.tau (u + u') v) (𝟙 _) y J * cubV D.toPre.cub y J (cP D.toPre _ u) (cP D.toPre _ u') (cP D.toPre _ v) = val (D.toPre.tau u v) (𝟙 _) y J * val (D.toPre.tau u' v) (𝟙 _) y J := fun u u' v =>
    (GlobalTheory.TauBimultBox.val_lhs D.toPre hJ u u' v).symm.trans ((val_corr hJ (D.tau_bimult u u' v) (𝟙 _)).trans (val_mul hJ _ _ _))
  have c0 : ∀ (E : DegPre R) (S : Over (Spec (CommRingCat.of R))), cP E S 0 = 1 := fun E S => by
    have := cPoint_add E S 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hP : ∀ u (k : (Fin r × Fin r) × Fin 4), cP D' (TK R) u ≫ ![T.pr k.1.1 * T.pr k.1.2, T.pr k.1.1, T.pr k.1.2, 1] k.2 = cP D.toPre (TK R) (![T.xe u k.1.1 + T.xe u k.1.2, T.xe u k.1.1, T.xe u k.1.2, 0] k.2) := by
    intro u k
    have e : ∀ i, cP D' (TK R) u ≫ T.pr i = cP D.toPre (TK R) (T.xe u i) := fun i => by
      rw [cP, Category.assoc, T.c_pr]; rfl
    obtain ⟨⟨i, j⟩, m⟩ := k
    fin_cases m
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [MonObj.comp_mul, e, e, cPoint_add]
    · simpa using e i
    · simpa using e j
    · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
      rw [c0]; simp [Hom.one_def]
  rw [GlobalTheory.TauBimultBox.val_lhs D' hJ' a a' b, val_mul hJ']
  have hC : ∀ u u' v, cubV D.toPre.cub y J (cP D.toPre _ u) (cP D.toPre _ u') (cP D.toPre _ v) = val (D.toPre.tau u v) (𝟙 _) y J * val (D.toPre.tau u' v) (𝟙 _) y J * (val (D.toPre.tau (u + u') v) (𝟙 _) y J)⁻¹ := fun u u' v => by
    rw [← hB u u' v, mul_comm, inv_mul_cancel_left]
  simp only [hP, hC] at key
  have h1 : cP D' (TK R) a * cP D' (TK R) a' * cP D' (TK R) b = cP D' (TK R) (a + a' + b) := by rw [cPoint_add, cPoint_add]
  have h2 : cP D' (TK R) a * cP D' (TK R) a' = cP D' (TK R) (a + a') := (cPoint_add _ _ _ _).symm
  have h3 : cP D' (TK R) a * cP D' (TK R) b = cP D' (TK R) (a + b) := (cPoint_add _ _ _ _).symm
  have h4 : cP D' (TK R) a' * cP D' (TK R) b = cP D' (TK R) (a' + b) := (cPoint_add _ _ _ _).symm
  rw [h1, h2, h3, h4, ← c0 D' (TK R)] at key
  refine alg W T.xe (fun u => val (D.toPre.psi u) (𝟙 _) y J) (val D.toPre.rigK (𝟙 _) y J)
    (fun u => gm (cP D' (TK R) u).left y _ (T.w.s (fun k => J ((cP D' (TK R) u).left ≫ tensφ T.pr k), J' (cP D' (TK R) u).left)))
    (fun u => val (D'.psi u) (𝟙 _) y J') (fun u v => val (D'.tau u v) (𝟙 _) y J') (fun u v => val (D.toPre.tau u v) (𝟙 _) y J)
    (cubV D'.cub y J' (cP D' (TK R) a) (cP D' (TK R) a') (cP D' (TK R) b)) (val D'.rigK (𝟙 _) y J') a a' b vtE hψ vt (hn y J' hJ') ?_
  beta_reduce
  exact key

end GlobalTheory.TensBimult
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataTauBimultiplicativeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorData_tau_bimultiplicative : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), Tens D.toPre D' W → (∀ (z : (TK R).left) (J : ((TK R).left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val (D'.psi 0) (𝟙 _) z J * val D'.rigK (𝟙 _) z J = 1) → D'.TauBimult := by
  first | exact @GlobalTheory.TensBimult.main | exact GlobalTheory.TensBimult.main | (intros; apply GlobalTheory.TensBimult.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorDegenerationDataOfUnimodularPosDef
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.TensExist

theorem exists_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∃ D' : DegData R (maximalIdeal R), Nonempty (Tens D.toPre D'.toPre W) := by
  intro R _ _ _ hA D r W hpos hdet
  obtain ⟨D', T, hrig⟩ := GlobalTheory.T.exists_tensorPreData_rigidification_inv_psi_zero R hA D W hpos hdet
  obtain ⟨hp, ht⟩ := GlobalTheory.T.tensorData_psi_mem_maximalIdeal_tendsto_zero R hA D D' W hpos T
  exact ⟨⟨D', GlobalTheory.T.tensorData_psi_isEven R hA D D' W T, GlobalTheory.T.tensorData_tau_bimultiplicative R hA D D' W T hrig, hp, ht⟩, ⟨T⟩⟩

end GlobalTheory.Mum.TensExist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorDegenerationDataOfUnimodularPosDefStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensorDegenerationData_of_unimodular_posDef : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∃ D' : DegData R (maximalIdeal R), Nonempty (Tens D.toPre D'.toPre W) := by
  first | exact @GlobalTheory.Mum.TensExist.exists_tens | exact GlobalTheory.Mum.TensExist.exists_tens | (intros; apply GlobalTheory.Mum.TensExist.exists_tens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnimodLatticeBarBar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmFieldTraceFormGramMatrixPosDef
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmFieldTraceFormGramMatrixPosDef
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TraceLattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

theorem cast_trace_mul_bar (x y : 𝓞 E) :
    ((Algebra.trace ℤ (𝓞 E) (x * H.bar y) : ℤ) : ℝ) = GlobalTheory.LatticeBoundTests.trBil E x y := by
  have h1 := trace_eq_sum_embeddings ℂ (K := ℚ) (L := E) (x := ((x * H.bar y : 𝓞 E) : E))
  rw [← Algebra.coe_trace_int, ← (RingHom.equivRatAlgHom E ℂ).sum_comp] at h1
  rw [GlobalTheory.LatticeBoundTests.trBil_apply, ← Complex.re_sum]
  have h2 : ∑ σ : E →+* ℂ, σ (x : E) * starRingEnd ℂ (σ (y : E))
      = ((Algebra.trace ℤ (𝓞 E) (x * H.bar y) : ℤ) : ℂ) := by
    rw [← map_intCast (algebraMap ℚ ℂ), h1]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← IsCMField.complexEmbedding_complexConj, ← H.bar_eq, ← map_mul]
    rfl
  rw [h2]; simp

theorem bar_bar (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

theorem exists_traceForm_matrix : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), ∃ (m : ℕ) (B0 : Matrix (Fin m) (Fin m) ℤ) (ρ0 : 𝓞 E →+* Matrix (Fin m) (Fin m) ℤ), 1 ≤ m ∧ B0.transpose = B0 ∧ (B0.map (Int.cast : ℤ → ℝ)).PosDef ∧ ∀ a, (ρ0 a).transpose * B0 = B0 * ρ0 (H.bar a) := by
  intro E _ _ _ H
  classical
  let J := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let q : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let e : Module.Basis (Fin (Fintype.card J)) ℤ (𝓞 E) := (RingOfIntegers.basis E).reindex q
  refine ⟨Fintype.card J, Matrix.of fun i j => Algebra.trace ℤ (𝓞 E) (e i * H.bar (e j)),
    (Algebra.leftMulMatrix e).toRingHom, ?_, ?_, ?_, ?_⟩
  · rw [← Module.finrank_eq_card_chooseBasisIndex]
    exact Module.finrank_pos
  · ext i j
    apply Int.cast_injective (α := ℝ)
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    rw [cast_trace_mul_bar, cast_trace_mul_bar, GlobalTheory.LatticeBoundTests.trBil_symm]
  · have h := (GlobalTheory.LatticeBoundTests.trBil_posDef E).submatrix q.symm.injective
    convert h using 1
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.submatrix_apply, cast_trace_mul_bar, e,
      Module.Basis.reindex_apply]
  · intro a
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, Algebra.leftMulMatrix_eq_repr_mul]
    have h1 : ∑ k, e.repr (a * e i) k * Algebra.trace ℤ (𝓞 E) (e k * H.bar (e j))
        = Algebra.trace ℤ (𝓞 E) (a * e i * H.bar (e j)) := by
      conv_rhs => rw [← e.sum_repr (a * e i)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_mul_assoc, map_zsmul, smul_eq_mul]
    have h2 : ∑ k, Algebra.trace ℤ (𝓞 E) (e i * H.bar (e k)) * e.repr (H.bar a * e j) k
        = Algebra.trace ℤ (𝓞 E) (e i * H.bar (H.bar a * e j)) := by
      conv_rhs => rw [← e.sum_repr (H.bar a * e j)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_zsmul, mul_smul_comm, map_zsmul, smul_eq_mul, mul_comm]
    rw [h1, h2, map_mul H.bar, bar_bar]
    congr 1; ring

end GlobalTheory.TraceLattice
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmFieldTraceFormGramMatrixPosDefStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmField_traceForm_gram_matrix_posDef : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), ∃ (m : ℕ) (B0 : Matrix (Fin m) (Fin m) ℤ) (ρ0 : 𝓞 E →+* Matrix (Fin m) (Fin m) ℤ), 1 ≤ m ∧ B0.transpose = B0 ∧ (B0.map (Int.cast : ℤ → ℝ)).PosDef ∧ ∀ a, (ρ0 a).transpose * B0 = B0 * ρ0 (H.bar a) := by
  first | exact @GlobalTheory.TraceLattice.exists_traceForm_matrix | exact GlobalTheory.TraceLattice.exists_traceForm_matrix | (intros; apply GlobalTheory.TraceLattice.exists_traceForm_matrix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnimodularPosDefAdjointAction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnimodularPosDefAdjointAction
open Matrix Kronecker

namespace GlobalTheory

section
variable {n q : Type} [Fintype n] [DecidableEq n] [Fintype q] [DecidableEq q]

theorem zarhinBlock_real_posDef_det (B A : Matrix n n ℝ) (x : Matrix q q ℝ) (s : ℝ)
    (hB : B.PosDef) (hA : A = (1 + s) • B⁻¹) (hx : xᵀ * x = s • (1 : Matrix q q ℝ)) :
    (fromBlocks (A ⊗ₖ (1 : Matrix q q ℝ)) ((1 : Matrix n n ℝ) ⊗ₖ xᵀ) ((1 : Matrix n n ℝ) ⊗ₖ x)
        (B ⊗ₖ (1 : Matrix q q ℝ))).PosDef ∧
      (fromBlocks (A ⊗ₖ (1 : Matrix q q ℝ)) ((1 : Matrix n n ℝ) ⊗ₖ xᵀ) ((1 : Matrix n n ℝ) ⊗ₖ x)
        (B ⊗ₖ (1 : Matrix q q ℝ))).det = 1 := by
  have hdet : IsUnit B.det := hB.det_pos.ne'.isUnit
  have hK : (B ⊗ₖ (1 : Matrix q q ℝ)).PosDef := hB.kronecker PosDef.one
  have hKi : (B⁻¹ ⊗ₖ (1 : Matrix q q ℝ)).PosDef := hB.inv.kronecker PosDef.one
  letI := hK.isUnit.invertible
  have hinv : (B ⊗ₖ (1 : Matrix q q ℝ))⁻¹ = B⁻¹ ⊗ₖ (1 : Matrix q q ℝ) := by
    apply Matrix.inv_eq_left_inv
    rw [← mul_kronecker_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one, one_kronecker_one]
  have hS : A ⊗ₖ (1 : Matrix q q ℝ) - ((1 : Matrix n n ℝ) ⊗ₖ xᵀ) * (B ⊗ₖ (1 : Matrix q q ℝ))⁻¹ *
      ((1 : Matrix n n ℝ) ⊗ₖ x) = B⁻¹ ⊗ₖ (1 : Matrix q q ℝ) := by
    rw [hinv, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_one, hx, hA, kronecker_smul, smul_kronecker, add_smul, one_smul,
      add_sub_cancel_right]
  have hT : ((1 : Matrix n n ℝ) ⊗ₖ xᵀ)ᴴ = (1 : Matrix n n ℝ) ⊗ₖ x := by
    rw [conjTranspose_eq_transpose_of_trivial, ← kroneckerMap_transpose, transpose_one,
      transpose_transpose]
  have hd : (fromBlocks (A ⊗ₖ (1 : Matrix q q ℝ)) ((1 : Matrix n n ℝ) ⊗ₖ xᵀ)
      ((1 : Matrix n n ℝ) ⊗ₖ x) (B ⊗ₖ (1 : Matrix q q ℝ))).det = 1 := by
    rw [det_fromBlocks₂₂, invOf_eq_nonsing_inv, hS, ← det_mul, ← mul_kronecker_mul,
      Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one, one_kronecker_one, det_one]
  refine ⟨?_, hd⟩
  have hps : (fromBlocks (A ⊗ₖ (1 : Matrix q q ℝ)) ((1 : Matrix n n ℝ) ⊗ₖ xᵀ)
      ((1 : Matrix n n ℝ) ⊗ₖ x) (B ⊗ₖ (1 : Matrix q q ℝ))).PosSemidef := by
    have := (PosDef.fromBlocks₂₂ (A ⊗ₖ (1 : Matrix q q ℝ)) ((1 : Matrix n n ℝ) ⊗ₖ xᵀ) hK).mpr
      (by rw [hT, hS]; exact hKi.posSemidef)
    rwa [hT] at this
  exact hps.posDef_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr (by rw [hd]; exact isUnit_one))

def zarhinAction {R : Type} [CommRing R] (σ : R →+* R) (ρ0 : R →+* Matrix n n ℤ) :
    R →+* Matrix ((n × q) ⊕ (n × q)) ((n × q) ⊕ (n × q)) ℤ where
  toFun a := fromBlocks ((ρ0 (σ a))ᵀ ⊗ₖ (1 : Matrix q q ℤ)) 0 0 (ρ0 a ⊗ₖ (1 : Matrix q q ℤ))
  map_one' := by simp
  map_mul' a b := by
    rw [fromBlocks_multiply, mul_comm a b, map_mul σ, map_mul ρ0, transpose_mul, mul_comm b a,
      map_mul ρ0]
    simp [← mul_kronecker_mul]
  map_zero' := by simp
  map_add' a b := by
    simp [fromBlocks_add, add_kronecker, transpose_add]

theorem zarhinAction_adjoint {R : Type} [CommRing R] (σ : R →+* R) (hσ : ∀ a, σ (σ a) = a)
    (ρ0 : R →+* Matrix n n ℤ) (B A : Matrix n n ℤ) (x : Matrix q q ℤ)
    (hB : ∀ a, (ρ0 a)ᵀ * B = B * ρ0 (σ a)) (hA : ∀ a, ρ0 (σ a) * A = A * (ρ0 a)ᵀ) (a : R) :
    (zarhinAction (q := q) σ ρ0 a)ᵀ *
      fromBlocks (A ⊗ₖ (1 : Matrix q q ℤ)) ((1 : Matrix n n ℤ) ⊗ₖ xᵀ) ((1 : Matrix n n ℤ) ⊗ₖ x)
        (B ⊗ₖ (1 : Matrix q q ℤ)) =
      fromBlocks (A ⊗ₖ (1 : Matrix q q ℤ)) ((1 : Matrix n n ℤ) ⊗ₖ xᵀ) ((1 : Matrix n n ℤ) ⊗ₖ x)
        (B ⊗ₖ (1 : Matrix q q ℤ)) * zarhinAction (q := q) σ ρ0 (σ a) := by
  simp only [zarhinAction, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, fromBlocks_transpose,
    fromBlocks_multiply, ← kroneckerMap_transpose, transpose_transpose, transpose_one,
    transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, hσ]
  simp only [← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, hA, hB]

theorem mul_adjugate_eq_adjugate_mul_of_adjoint (B P Q : Matrix n n ℤ) (hd : B.det ≠ 0)
    (h : P * B = B * Q) : Q * B.adjugate = B.adjugate * P := by
  have h1 : B.adjugate * (P * B) * B.adjugate = B.adjugate * (B * Q) * B.adjugate := by rw [h]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ B, mul_adjugate, adjugate_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul] at h1
  exact (smul_right_injective _ hd h1).symm

end

theorem exists_unimodular_posDef_adjoint_action (R : Type) [CommRing R] (σ : R →+* R)
    (hσ : ∀ a, σ (σ a) = a) (m : ℕ) (B0 : Matrix (Fin m) (Fin m) ℤ)
    (ρ0 : R →+* Matrix (Fin m) (Fin m) ℤ) (hm : 1 ≤ m) (hs : B0.transpose = B0)
    (hp : (B0.map (Int.cast : ℤ → ℝ)).PosDef)
    (hadj : ∀ a, (ρ0 a).transpose * B0 = B0 * ρ0 (σ a)) :
    ∃ (r : ℕ) (b : Matrix (Fin r) (Fin r) ℤ) (ρ : R →+* Matrix (Fin r) (Fin r) ℤ),
      1 ≤ r ∧ b.transpose = b ∧ (b.map (Int.cast : ℤ → ℝ)).PosDef ∧ IsUnit b.det ∧
        ∀ a, (ρ a).transpose * b = b * ρ (σ a) := by
  have hcast : ∀ {k : Type} [Fintype k] [DecidableEq k] (M : Matrix k k ℤ),
      (M.map (Int.cast : ℤ → ℝ)).det = (M.det : ℝ) := fun M => by
    simpa using ((Int.castRingHom ℝ).map_det M).symm
  have hDR : (0 : ℝ) < (B0.det : ℝ) := hcast B0 ▸ hp.det_pos
  have hD : 0 < B0.det := by exact_mod_cast hDR
  obtain ⟨s, hsD⟩ : ∃ s : ℕ, B0.det = 1 + s := ⟨(B0.det - 1).toNat, by omega⟩
  obtain ⟨x, hx, -⟩ := exists_int_matrix_transpose_mul_eq_smul_one s
  set b := fromBlocks (B0.adjugate ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℤ))
    ((1 : Matrix (Fin m) (Fin m) ℤ) ⊗ₖ xᵀ) ((1 : Matrix (Fin m) (Fin m) ℤ) ⊗ₖ x)
    (B0 ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℤ)) with hb
  have hsym : bᵀ = b := by
    simp only [hb, fromBlocks_transpose, ← kroneckerMap_transpose, transpose_transpose,
      transpose_one, adjugate_transpose, hs]
  have hk : ∀ (M : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin 4) (Fin 4) ℤ),
      (M ⊗ₖ N).map (Int.cast : ℤ → ℝ) = M.map (Int.cast : ℤ → ℝ) ⊗ₖ N.map (Int.cast : ℤ → ℝ) := by
    intro M N
    ext i j
    simp [kroneckerMap_apply]
  have hxR : (x.map (Int.cast : ℤ → ℝ))ᵀ * x.map (Int.cast : ℤ → ℝ) = (s : ℝ) • 1 := by
    have := congrArg (fun M => (Int.castRingHom ℝ).mapMatrix M) hx
    simp only [map_mul, map_zsmul, map_one] at this
    rw [← Int.cast_smul_eq_zsmul ℝ] at this
    simpa [transpose_map] using this
  have hAR : (B0.adjugate).map (Int.cast : ℤ → ℝ) =
      (1 + (s : ℝ)) • (B0.map (Int.cast : ℤ → ℝ))⁻¹ := by
    have h1 : (B0.adjugate).map (Int.cast : ℤ → ℝ) = (B0.map (Int.cast : ℤ → ℝ)).adjugate := by
      simpa using (Int.castRingHom ℝ).map_adjugate B0
    have h2 : (1 + (s : ℝ)) = (B0.det : ℝ) := by rw [hsD]; push_cast; rfl
    rw [h1, h2, Matrix.inv_def, hcast, smul_smul, Ring.inverse_eq_inv', mul_inv_cancel₀ hDR.ne',
      one_smul]
  have hreal := zarhinBlock_real_posDef_det _ _ _ _ hp hAR hxR
  have hbR : b.map (Int.cast : ℤ → ℝ) =
      fromBlocks (B0.adjugate.map (Int.cast : ℤ → ℝ) ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℝ))
        ((1 : Matrix (Fin m) (Fin m) ℝ) ⊗ₖ (x.map (Int.cast : ℤ → ℝ))ᵀ)
        ((1 : Matrix (Fin m) (Fin m) ℝ) ⊗ₖ x.map (Int.cast : ℤ → ℝ))
        (B0.map (Int.cast : ℤ → ℝ) ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℝ)) := by
    rw [hb, fromBlocks_map, hk, hk, hk, hk, Matrix.map_one _ Int.cast_zero Int.cast_one,
      Matrix.map_one _ Int.cast_zero Int.cast_one, transpose_map]
  rw [← hbR, hcast] at hreal
  have hdet : b.det = 1 := by exact_mod_cast hreal.2
  have hact := zarhinAction_adjoint σ hσ ρ0 B0 B0.adjugate x hadj
    (fun a => mul_adjugate_eq_adjugate_mul_of_adjoint _ _ _ hD.ne' (hadj a))
  rw [← hb] at hact
  let e := Fintype.equivFin ((Fin m × Fin 4) ⊕ (Fin m × Fin 4))
  refine ⟨_, reindex e e b, ((reindexAlgEquiv ℤ ℤ e).toRingEquiv.toRingHom).comp
    (zarhinAction σ ρ0), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]; omega
  · rw [transpose_reindex, hsym]
  · exact hreal.1.submatrix e.symm.injective
  · rw [det_reindex_self, hdet]; exact isUnit_one
  · intro a
    change (reindex e e (zarhinAction σ ρ0 a))ᵀ * _ = _ * reindex e e (zarhinAction σ ρ0 (σ a))
    simp only [reindex_apply, transpose_submatrix, submatrix_mul_equiv, hact]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnimodularPosDefAdjointActionStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unimodular_posDef_form_adjoint_rep_of_posDef : ∀ (R : Type) [CommRing R] (σ : R →+* R), (∀ a, σ (σ a) = a) → ∀ (m : ℕ) (B0 : Matrix (Fin m) (Fin m) ℤ) (ρ0 : R →+* Matrix (Fin m) (Fin m) ℤ), 1 ≤ m → B0.transpose = B0 → (B0.map (Int.cast : ℤ → ℝ)).PosDef → (∀ a, (ρ0 a).transpose * B0 = B0 * ρ0 (σ a)) → ∃ (r : ℕ) (b : Matrix (Fin r) (Fin r) ℤ) (ρ : R →+* Matrix (Fin r) (Fin r) ℤ), 1 ≤ r ∧ b.transpose = b ∧ (b.map (Int.cast : ℤ → ℝ)).PosDef ∧ IsUnit b.det ∧ ∀ a, (ρ a).transpose * b = b * ρ (σ a) := by
  first | exact @GlobalTheory.exists_unimodular_posDef_adjoint_action | exact GlobalTheory.exists_unimodular_posDef_adjoint_action | (intros; apply GlobalTheory.exists_unimodular_posDef_adjoint_action <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem unimodLattice_bar_bar {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (a : 𝓞 E) :
    H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

theorem unimodLattice_bar_rt {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.bar H.rt = -H.rt := by
  apply RingOfIntegers.ext
  rw [H.bar_eq]
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj]
  have hsq : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have := congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq
    simpa using this
  have hd : (7 : ℝ) ≤ H.d := by
    have := H.d_mod
    have : 7 ≤ H.d := by omega
    exact_mod_cast this
  set z := φ (H.rt : E) with hz
  have hre := congrArg Complex.re hsq
  have him := congrArg Complex.im hsq
  simp [pow_two] at hre him
  have hx : z.re = 0 := by
    have hm : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.1 hm with h | h
    · exact h
    · rw [h] at hre; nlinarith [sq_nonneg z.re]
  have key : starRingEnd ℂ z = -z := by apply Complex.ext <;> simp [hx]
  rw [hz] at key
  simpa using key

theorem unimodLattice_w0_add {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.w0 + H.bar H.w0 = 1 := by
  have h1 := H.two_weight_eq_one_add_root
  have h2 : 2 * H.bar H.w0 = 1 - H.rt := by
    have := congrArg H.bar h1
    rw [map_mul, map_add (f := _), map_one, unimodLattice_bar_rt, map_ofNat] at this
    rw [this]; ring
  have h3 : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by
    rw [mul_add, h1, h2]; ring
  exact mul_left_cancel₀ two_ne_zero h3

theorem unimodLattice :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), ∃ (r : ℕ) (W : Matrix (Fin r) (Fin r) ℤ) (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), 1 ≤ r ∧ ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ IsUnit (W + W.transpose).det ∧ (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) ∧ W = (W + W.transpose) * ρ H.w0 := by
  intro E _ _ _ H
  obtain ⟨m, B0, ρ0, hm, hsym, hpd, hadj⟩ := GlobalTheory.T.exists_cmField_traceForm_gram_matrix_posDef E H
  obtain ⟨r, b, ρ, hr, hbs, hbpd, hbu, hbadj⟩ :=
    GlobalTheory.T.exists_unimodular_posDef_form_adjoint_rep_of_posDef (𝓞 E) (H.bar : 𝓞 E →+* 𝓞 E) (unimodLattice_bar_bar H) m B0 ρ0 hm hsym hpd hadj
  have hW : b * ρ H.w0 + (b * ρ H.w0).transpose = b := by
    rw [Matrix.transpose_mul, hbs, hbadj, ← Matrix.mul_add, ← map_add (f := _)]
    erw [unimodLattice_w0_add H]
    rw [map_one, Matrix.mul_one]
  refine ⟨r, b * ρ H.w0, ρ, hr, ?_, ?_, ?_, ?_⟩
  · rw [hW]; exact hbpd
  · rw [hW]; exact hbu
  · intro a; rw [hW]; exact hbadj a
  · rw [hW]

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHost
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_host : ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E), Nonempty (Host E) :=
  ⟨GlobalTheory.HostModel.E21, inferInstance, inferInstance, inferInstance, ⟨GlobalTheory.HostModel.host⟩⟩

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryPELTypeFactorDegData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_pelOK_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ D : DegData R (maximalIdeal R), Nontrivial D.toPre.X → ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : Host E) (Dm : Datum H) (D' : DegData R (maximalIdeal R)) (_ : Module (𝓞 E) D'.toPre.X) (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), PelOK Dm D'.toPre o ∧ (∃ F : Factor D.toPre D'.toPre, F.Alg) := by
  intro R _ _ _ hR D hX
  obtain ⟨E, _, _, _, ⟨H⟩⟩ := GlobalTheory.Mum.exists_host
  obtain ⟨r, W, ρ, hr, hpos, hdet, hadj, hW⟩ := GlobalTheory.Mum.unimodLattice E H
  obtain ⟨D', ⟨T⟩⟩ := GlobalTheory.T.exists_tensorDegenerationData_of_unimodular_posDef R hR.1 D W hpos hdet
  obtain ⟨_, o, hact, hψ⟩ := GlobalTheory.T.exists_ringOfIntegers_module_on_tensor_data R hR.1 E H D D' W hpos hdet T ρ hadj hW
  obtain ⟨Dm, hDm⟩ := GlobalTheory.T.tensorDegData_unitary_type R hR E H D D' W hpos hdet T ρ hadj hW hX hr o hact hψ
  exact ⟨E, _, _, _, H, Dm, D', _, o, hDm, GlobalTheory.T.exists_algebraic_factor_of_unimodular_tensor R hR.1 D D' W hpos hdet T hr⟩

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryPELTypeFactorDegDataStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryPELType_factor_degData : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ D : DegData R (maximalIdeal R), Nontrivial D.toPre.X → ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : Host E) (Dm : Datum H) (D' : DegData R (maximalIdeal R)) (_ : Module (𝓞 E) D'.toPre.X) (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), PelOK Dm D'.toPre o ∧ (∃ F : Factor D.toPre D'.toPre, F.Alg) := by
  first | exact @GlobalTheory.Mum.exists_pelOK_factor | exact GlobalTheory.Mum.exists_pelOK_factor | (intros; apply GlobalTheory.Mum.exists_pelOK_factor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasOfSubsingleton
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem has_of_subsingleton : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ D : DegData R (maximalIdeal R), Subsingleton D.toPre.X → Has D := by
  intro R _ _ _ hR D hX
  haveI : IsNoetherianRing R := hR.1
  let A : PolAV (Spec (CommRingCat.of (FractionRing R))) := GlobalTheory.AmpleSpecialisation.baseChange D.toPre.P (jK R)
  let eA : (Over.pullback (jK R)).obj D.toPre.P.A ≅ A.A := by
    with_unfolding_all exact Iso.refl _
  have hA : IsMonHom eA.hom := by
    refine ⟨?_, ?_⟩
    · exact Category.comp_id _
    · show μ ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ μ
      rw [Category.comp_id, id_tensorHom_id, Category.id_comp]
      rfl
  have hw : ∃ w : LB.Iso (A.L.pull eA.hom.left) (D.toPre.P.L.pull (pullback.fst D.toPre.P.A.hom (jK R))), w.IsGen := by
    obtain ⟨w, hw⟩ := GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB D.toPre.P.isLB (pullback.fst D.toPre.P.A.hom (jK R)))
    exact ⟨GlobalTheory.PtTie.isoFromPullId w, GlobalTheory.PtTie.isoFromPullId_isGen hw⟩
  have hI : maximalIdeal R ≤ Ideal.jacobson ⊥ := (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  exact ⟨D.toPre.P.A, inferInstance, inferInstance, A, GlobalTheory.isSemiAbelian_of_isAbelianScheme _ D.toPre.P.isAb,
    ⟨⟨GlobalTheory.SelfUnif.selfPre D A eA hA hw, fun k _ =>
      GlobalTheory.SelfUnif.expBij D A eA hA hw GlobalTheory.globalFns_holds hI k⟩⟩⟩

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationCompleteNormalBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isSemiAbelian_of_isGrpPullback' {S T : Scheme.{0}} {f : T ⟶ S} {G : Over S} [GrpObj G] {G' : Over T} [GrpObj G']
    [IsCommMonObj G'] {π : G'.left ⟶ G.left} (h : IsGrpPullback G' G f π) (hG : IsSemiAbelian G) : IsSemiAbelian G' := by
  obtain ⟨bc, mbc, -⟩ := grpPullback_iso h (isGrpPullback_pullback G f)
  exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback f G hG)

theorem has_of_base : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ D : DegData R (maximalIdeal R), Has D := by
  intro R _ _ _ hB D
  rcases subsingleton_or_nontrivial D.toPre.X with hX | hX
  · exact GlobalTheory.Mum.has_of_subsingleton R hB.1 D hX
  obtain ⟨E, _, _, _, H, Dm, D', hmod, o, hPel, F, hA⟩ := GlobalTheory.T.exists_unitaryPELType_factor_degData R hB D hX
  have hX' : Nontrivial D'.toPre.X :=
    (Function.LeftInverse.injective (g := F.xp) (f := F.xi) F.xp_xi).nontrivial
  obtain ⟨R', _, _, _, ρ, D'', hρ, hpull, hcov⟩ := GlobalTheory.T.exists_labelledCover_unitaryPELType_finiteExt R hB E H Dm D' o hX' hPel
  have hB' : Base R' := ⟨hρ.1, @charZero_of_injective_ringHom _ _ _ _ ρ hρ.2.1 hB.2⟩
  have hfin'' : HasFin D'' := GlobalTheory.T.hasSemiAbelianUniformisation_of_labelledCover R' hB' D'' hcov
  have hfin' : HasFin D' := GlobalTheory.Mum.hasFin_of_finExt R R' ρ hρ D' D'' hpull hfin''
  obtain ⟨G', _, _, A', hG', ⟨U'⟩⟩ := GlobalTheory.T.hasSemiAbelianUniformisation_of_finiteExt R hB D' hfin'
  obtain ⟨oA, oG, hlin⟩ := GlobalTheory.T.exists_ringAction_extension_to_uniformised_semiAbelian R hB D' A' G' hG' U' F.O F.o
  have hidem : oG.act F.e ≫ oG.act F.e = oG.act F.e := by rw [← oG.map_mul, F.idem]
  obtain ⟨G, _, _, inc, pr, hG, hinc, hpr, hip, hpi⟩ :=
    GlobalTheory.Mum.IdemImage.isSemiAbelian_image (Sp R) G' hG' (oG.act F.e) (oG.hom F.e) hidem
  obtain ⟨R₁, _, _, _, ρ₁, D₁, G₁, _, _, β, β₂, A₁, U₁, hρ₁, hpull₁, hgp, -, -⟩ :=
    GlobalTheory.T.idempotentFactor_uniformised_of_degData_factor R hB D D' F hA A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi
  exact GlobalTheory.T.hasSemiAbelianUniformisation_of_finiteExt R hB D
    ⟨R₁, _, _, _, ρ₁, D₁, hρ₁, hpull₁, G₁, _, _, A₁, isSemiAbelian_of_isGrpPullback' hgp hG, ⟨U₁⟩⟩
end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationCompleteNormalBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSemiAbelianUniformisation_complete_normal_base : (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ D : DegData R (maximalIdeal R), Has D) := by
  first | exact @GlobalTheory.Mum.has_of_base | exact GlobalTheory.Mum.has_of_base | (intros; apply GlobalTheory.Mum.has_of_base <;> assumption)
end
