module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricOnSet
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpCoordinatesTangentFieldHolomorphicPeriodMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OverIx

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitTauCoordinateAddNsmulFirstVariable
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitTauCoordinateAddNsmulFirstVariable
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TauShift

open GlobalTheory.PsiTauCoordRel GlobalTheory.PeriodBalance GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues

variable {R : Type} [CommRing R] [IsDomain R]

abbrev cK (ξ : Spec (CommRingCat.of (FractionRing R))) : Rˣ →* ((TK R).left.presheaf.stalk ξ)ˣ :=
  Units.map (GlobalTheory.PeriodBalance.cst ξ).toMonoidHom

abbrev kK (ξ : Spec (CommRingCat.of (FractionRing R))) : (FractionRing R)ˣ →* ((TK R).left.presheaf.stalk ξ)ˣ :=
  Units.map (kst ξ).toMonoidHom

variable [IsLocalRing R]

theorem coord_val (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) {a b : D.X} {x : (FractionRing R)ˣ} (hx : IsTauCoord D a b x) :
    ∃ u : Rˣ, Units.map (kst ξ).toMonoidHom x =
      cK ξ u * val (D.tau a b) (𝟙 (TK R).left) ξ J := by
  let cU : Rˣ →* ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    Units.map (GlobalTheory.PeriodBalance.cst ξ).toMonoidHom
  obtain ⟨c5, h5⟩ : ∃ w : Rˣ, val D.rigK (𝟙 (TK R).left) ξ J = cU w := by
    unfold DegPre.rigK
    rw [val_pull hJ]
    have : 𝟙 _ ≫ (toUnit (TK R)).left = jK R ≫ 𝟙 _ := by rw [toUnit_left]; simp
    rw [this]
    exact val_int ξ hJc D.rig (𝟙 _) fun _ => by rw [Category.id_comp]; exact Over.w η[D.P.A]
  obtain ⟨j, h, i1, i2, i3, i4, rfl⟩ := hx
  have hm := h (show ξ ∈ (⊤ : (Spec (CommRingCat.of (FractionRing R))).Opens) from trivial)
  have eT := gm_genVal ξ (D.tau a b) j h
  have dT : gm (𝟙 _) ξ (LB.wchart D.P.L _ j) ((D.tau a b).s j) = _ := gm_mulGen _ _ ξ j hm
  rw [gm_mulGen _ _ ξ _ (mem_inl hm), gm_mulGen _ _ ξ _ (mem_inl (mem_inl hm)), gm_invGen, gm_invGen,
    gm_invGen] at dT
  obtain ⟨c1, g1⟩ := val_psi_chart D ξ hJ hJc (a + b) _ i1 (mem_inl (mem_inl (mem_inl hm)))
  obtain ⟨c2, g2⟩ := val_psi_chart D ξ hJ hJc a _ i2 (mem_inr (mem_inl (mem_inl hm)))
  obtain ⟨c3, g3⟩ := val_psi_chart D ξ hJ hJc b _ i3 (mem_inr (mem_inl hm))
  obtain ⟨c4, g4⟩ := gm_rigK D ξ _ i4 (mem_inr hm)
  have vt := GlobalTheory.PeriodBalance.val_tau D ξ hJ a b
  have eT' : gm (𝟙 _) ξ (LB.wchart D.P.L _ j) ((D.tau a b).s j) =
      Units.map (kst ξ).toMonoidHom (genVal (D.tau a b) j h) := Units.ext eT
  refine ⟨c1⁻¹ * c2 * c3 * c4⁻¹ * c5, ?_⟩
  rw [← eT', dT, g4, vt, g1, g2, g3, h5]
  simp only [cU, map_mul, map_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem val_add (D : DegPre R) (hB : D.TauBimult) (ξ : Spec (CommRingCat.of (FractionRing R))) {J}
    (hJ : Good D.P.L ξ J)
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) (a a' b : D.X) :
    ∃ w : Rˣ, val (D.tau (a + a') b) (𝟙 (TK R).left) ξ J = cK ξ w *
      (val (D.tau a b) (𝟙 (TK R).left) ξ J * val (D.tau a' b) (𝟙 (TK R).left) ξ J) := by
  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB a a' b) (𝟙 (TK R).left)).trans (val_mul hJ _ _ _))
  rw [val_pull (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) hJ D.cub.t (D.pt3 a a' b)] at e
  have hp : 𝟙 (TK R).left ≫ D.pt3 a a' b = jK R ≫ (lift (D.c a) (lift (D.c a') (D.c b))).left := by
    simp [DegPre.pt3, ← CartesianMonoidalCategory.comp_lift]
  rw [hp] at e
  obtain ⟨w, hw⟩ := val_int (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) ξ hJc D.cub.t (lift (D.c a) (lift (D.c a') (D.c b))).left fun k => by
    show ((lift (D.c a) (lift (D.c a') (D.c b))).left ≫ (psum D.P.A (x3 D.P.A) k.down).left) ≫ D.P.A.hom = 𝟙 _
    rw [Category.assoc, Over.w, Over.w]; rfl
  refine ⟨w⁻¹, ?_⟩
  have hw' : val D.cub.t (jK R ≫ (lift (D.c a) (lift (D.c a') (D.c b))).left) ξ J = cK ξ w := hw
  rw [← e, map_inv, eq_inv_mul_iff_mul_eq, mul_comm]
  exact congrArg _ hw'.symm

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), D.TauBimult →
    ∀ (a z b : D.X) (k : ℕ) (x x' x'' : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D a b x →
      GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D z b x' → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D (a + k • z) b x'' →
      ∃ u : Rˣ, x'' = Units.map (algebraMap R (FractionRing R)).toMonoidHom u * (x * x' ^ k) := by
  intro R _ _ _ D hB a z b k x x' x'' hx hx' hx''
  haveI : IsProper D.P.A.hom := D.P.isAb.proper
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J, hJ, hJc⟩ := exists_good_integral ξ D.P.isLB D.P.A.hom
  have hind : ∀ n : ℕ, ∃ w : Rˣ, val (D.tau (a + n • z) b) (𝟙 (TK R).left) ξ J =
      cK ξ w * (val (D.tau a b) (𝟙 (TK R).left) ξ J * val (D.tau z b) (𝟙 (TK R).left) ξ J ^ n) := by
    intro n
    induction n with
    | zero => exact ⟨1, by rw [zero_nsmul, add_zero, map_one, pow_zero, _root_.one_mul, _root_.mul_one]⟩
    | succ n ih =>
      obtain ⟨w, hw⟩ := ih
      obtain ⟨w', hw'⟩ := val_add D hB ξ hJ hJc (a + n • z) z b
      refine ⟨w' * w, ?_⟩
      rw [succ_nsmul, ← add_assoc, hw', hw, map_mul, pow_succ]
      ac_rfl
  obtain ⟨w, hw⟩ := hind k
  obtain ⟨u1, e1⟩ := coord_val D ξ hJ hJc hx
  obtain ⟨u2, e2⟩ := coord_val D ξ hJ hJc hx'
  obtain ⟨u3, e3⟩ := coord_val D ξ hJ hJc hx''
  refine ⟨u3 * w * u1⁻¹ * (u2⁻¹) ^ k, ?_⟩
  apply Units.map_injective (f := (kst ξ).toMonoidHom) (kst_injective ξ)
  show kK ξ x'' = kK ξ _
  replace e1 : kK ξ x = _ := e1
  replace e2 : kK ξ x' = _ := e2
  replace e3 : kK ξ x'' = _ := e3
  have hc : ∀ v : Rˣ, kK ξ (Units.map (algebraMap R (FractionRing R)).toMonoidHom v) =
      cK ξ v := fun v => Units.ext rfl
  have f1 : val (D.tau a b) (𝟙 (TK R).left) ξ J = cK ξ u1⁻¹ * kK ξ x := by
    rw [e1, map_inv, inv_mul_cancel_left]
  have f2 : val (D.tau z b) (𝟙 (TK R).left) ξ J = cK ξ u2⁻¹ * kK ξ x' := by
    rw [e2, map_inv, inv_mul_cancel_left]
  rw [map_mul, hc, map_mul, map_pow, e3, hw, f1, f2]
  simp only [map_mul, map_inv, map_pow, mul_pow]
  ac_rfl

end GlobalTheory.TauShift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitTauCoordinateAddNsmulFirstVariableStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_tauCoordinate_add_nsmul_first_variable : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), D.TauBimult →
    ∀ (a z b : D.X) (k : ℕ) (x x' x'' : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D a b x →
      GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D z b x' → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D (a + k • z) b x'' →
      ∃ u : Rˣ, x'' = Units.map (algebraMap R (FractionRing R)).toMonoidHom u * (x * x' ^ k) := by
  first | exact @GlobalTheory.TauShift.main | exact GlobalTheory.TauShift.main | (intros; apply GlobalTheory.TauShift.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.LineNorm

section Closure

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

omit [NumberField F] in
theorem isEqn_sum {α : Type} (s : Finset α) {Δ : α → Y.Dv} {t : α → Y.Fnˣ} (y : Y.X)
    (h : ∀ a, (Δ a).IsEqn y (t a)) : (∑ a ∈ s, Δ a).IsEqn y (∏ a ∈ s, t a) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact CartierDiv.isEqn_zero y
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (h a).add ih

end Closure

section Steps

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {F : Type} [Field F] [NumberField F] {Y : Var F}


open Classical in
def mixLog (ρ : Y.X ⟶ X) {m : ℕ}
    (f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (b : ℕ → Bool) (i : Fin m) : PtFn Y :=
  fun v ε y =>
    if hp : (resP v).Prime then
      haveI := Fact.mk hp
      let ψ : Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v] := (ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom
      (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
        Real.log (GlobalTheory.ShFam.Pad.grNorm t (spMap ψ ≫ stalkPt Y (below y.1) ≫ ρ)
          (lat t (resP v) (spMap ψ ≫ stalkPt Y (below y.1) ≫ ρ) (b (resP v)))
          (fun l => spMap (dualMap ψ) ≫ f (below y.1) l) i)
    else 0

end Steps

section Flags

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (C : FlagCpt Z e)

abbrev fr (y : C.Y.X) := (C.gr_spec y).choose_spec.choose

abbrev dg (y : C.Y.X) : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ := (C.gr_spec y).choose_spec.choose_spec.choose

omit [NumberField F] in
theorem fr_spec (y : C.Y.X) : (fr C y).Tri (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 (dg C y) ∧
    ∀ τ i, (C.gr τ i).IsEqn y (dg C y τ i) := (C.gr_spec y).choose_spec.choose_spec.choose_spec





open Classical in
def symLog (b : ℕ → Bool) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) : PtFn C.Y := fun v ε y =>
  if hp : (resP v).Prime then
    haveI := Fact.mk hp
    let ψ : C.Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v] := (ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom
    (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
      lnStep Z.t (spMap ψ ≫ stalkPt C.Y (below y.1) ≫ C.π ≫ genι Z)
        (fun τ i => spMap (dualMap ψ) ≫ (C.gr_spec (below y.1)).choose_spec.choose.v τ i) (resP v) (b (resP v)) st
  else 0


open Classical in
def lgCopy (w : Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt C.Y) : ℝ :=
  if hp : (resP v).Prime then
    haveI := Fact.mk hp
    let f := (C.gr_spec (below y.1)).choose_spec.choose
    let t := (C.gr_spec (below y.1)).choose_spec.choose_spec.choose
    let ψ : C.Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v] := (ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom
    Real.log (ε.w (valAt y.1 (((∏ x : Letter Dw, t x.1 x.2 ^ expo Dw w x) *
        (eqn (divOf C (expo Dw w)) (below y.1))⁻¹ : C.Y.Fnˣ) : C.Y.Fn))) +
      (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
        w.sum fun a n => (n : ℝ) * lnStep Z.t (spMap ψ ≫ stalkPt C.Y (below y.1) ≫ C.π ≫ genι Z)
          (fun τ i => spMap (dualMap ψ) ≫ f.v τ i) (resP v) (a.1 (resP v)) a.2.2
  else 0

theorem lgOf_eq_lgCopy : @lgOf = @lgCopy := rfl

theorem mul_finsupp_sum {α : Type} (w : α →₀ ℤ) (c : ℝ) (g : α → ℝ) :
    c * w.sum (fun a n => (n : ℝ) * g a) = ∑ a ∈ w.support, (w a : ℝ) * (c * g a) := by
  simp only [Finsupp.sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => mul_left_comm _ _ _

theorem lgCopy_eq (w : Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt C.Y) :
    lgCopy C w v ε y = Real.log (ε.w (valAt y.1 (((∏ x : Letter Dw, dg C (below y.1) x.1 x.2 ^ expo Dw w x) *
      (eqn (divOf C (expo Dw w)) (below y.1))⁻¹ : C.Y.Fnˣ) : C.Y.Fn))) +
      ∑ a ∈ w.support, (w a : ℝ) * symLog C a.1 a.2.2 v ε y := by
  obtain ⟨hp, -⟩ := GlobalTheory.ShFam.Pad.ioOf_spec F v ε
  simp only [lgCopy, symLog, dif_pos hp]
  refine congrArg₂ (fun a b : ℝ => a + b) rfl ?_
  refine (mul_finsupp_sum _ _ _).trans ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  refine congrArg _ (congrArg _ ?_)
  rfl


end Flags

end GlobalTheory.LineNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasBareOfHasPk
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDivStageOfPk
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw

def bkMk {B : Base} {C : Cols B} (W : RowsRest B C) {m : ℕ} (c : Fin m → W.EE)
    (b : ∀ u, (C.fm u).ramSub → (Fin m → B.LL) → B.LL)
    (hb : ∀ u φ x, B.embLL (b u φ x) = W.Bu u (GlobalTheory.Mem.ramForm W u φ) (GlobalTheory.Mem.coordForm B.embLL c x))
    (u : B.Word) : (C.fm u).ramSub →ₗ[B.LL] Module.Dual B.LL (Fin m → B.LL) :=
  LinearMap.mk₂ B.LL (b u)
    (fun φ ψ x => B.embLL.injective (by
      rw [map_add (f := _), hb, hb, hb, map_add (f := _), (W.Bu_linL u _).map_add (f := _)]))
    (fun a φ x => B.embLL.injective (by
      rw [smul_eq_mul, map_mul, hb, hb, map_smulₛₗ, (W.Bu_linL u _).map_smul, smul_eq_mul]))
    (fun φ x y => B.embLL.injective (by
      rw [map_add (f := _), hb, hb, hb, map_add (f := _), (W.Bu_linR u _).map_add (f := _)]))
    (fun a φ x => B.embLL.injective (by
      rw [smul_eq_mul, map_mul, hb, hb, map_smulₛₗ, (W.Bu_linR u _).map_smul, smul_eq_mul]))


open Classical in
def bkOf {B : Base} {C : Cols B} (W : RowsRest B C) {m : ℕ} (c : Fin m → W.EE) (u : B.Word) :
    (C.fm u).ramSub →ₗ[B.LL] Module.Dual B.LL (Fin m → B.LL) :=
  if H : ∀ u (φ : (C.fm u).ramSub) (x : Fin m → B.LL),
      W.Bu u (GlobalTheory.Mem.ramForm W u φ) (GlobalTheory.Mem.coordForm B.embLL c x) ∈ Set.range B.embLL then
    bkMk W c (fun u φ x => (H u φ x).choose) (fun u φ x => (H u φ x).choose_spec) u
  else 0

theorem bkOf_spec {B : Base} {C : Cols B} (W : RowsRest B C) {m : ℕ} (c : Fin m → W.EE)
    (H : ∀ u (φ : (C.fm u).ramSub) (x : Fin m → B.LL),
      W.Bu u (GlobalTheory.Mem.ramForm W u φ) (GlobalTheory.Mem.coordForm B.embLL c x) ∈ Set.range B.embLL)
    (u : B.Word) (φ : (C.fm u).ramSub) (x : Fin m → B.LL) :
    W.Bu u (GlobalTheory.Mem.ramForm W u φ) (GlobalTheory.Mem.coordForm B.embLL c x) = B.embLL (bkOf W c u φ x) := by
  classical
  unfold bkOf
  rw [dite_eq_left H]
  exact (H u φ x).choose_spec.symm

end GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw

def prescribedRowLat {B : Base} {C : Cols B} (W : RowsRest B C) {m : ℕ} (jE : (Fin m → B.LL) →ₛₗ[B.embLL] W.EE) :
    Submodule (𝓞 B.LL) (Fin m → B.LL) where
  carrier := {x | ∀ w : W.what₂.places.Pl, ∃ d : 𝓞 B.LL, d ∉ (w : HeightOneSpectrum (𝓞 B.LL)).asIdeal ∧
    d • x ∈ Submodule.span (𝓞 B.LL) {y | jE y ∈ W.what₂.RRset (W.what₂.muAt w)}}
  add_mem' := by
    intro x y hx hy w
    obtain ⟨a, ha, hax⟩ := hx w
    obtain ⟨b, hb, hby⟩ := hy w
    refine ⟨a * b, fun h => ((w : HeightOneSpectrum (𝓞 B.LL)).isPrime.mem_or_mem h).elim ha hb, ?_⟩
    rw [smul_add]
    refine Submodule.add_mem _ ?_ ?_
    · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hax
    · rw [mul_smul]; exact Submodule.smul_mem _ _ hby
  zero_mem' := fun w => ⟨1, (Ideal.ne_top_iff_one _).1 (w : HeightOneSpectrum (𝓞 B.LL)).isPrime.ne_top, by simp⟩
  smul_mem' := by
    intro s x hx w
    obtain ⟨a, ha, hax⟩ := hx w
    exact ⟨a, ha, by rw [smul_comm]; exact Submodule.smul_mem _ _ hax⟩
end GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw

theorem exists_divStage_of_pk : ∀ (B : Base) (C : Cols B) (G : Type) [Group G] (p : PkB B C G) (e : PerD p) (W₀ : RowsRest B C) (n : Nums p W₀) (η : ℕ → B.places.Pl → ℚ) (hη : ∀ j w, 0 ≤ η j w), (∀ v, IsUnit (p.Xo v).det) → ∀ (Ln : ∀ u, Submodule (𝓞 B.LL) ((C.fm u).lat 0).V) (h : B.Word → ℝ) (etaF : ℝ), ∃ V : DivStage B C (p.what₂ e W₀ n η hη), DivIs p V ∧ (∀ u x, x ∈ (V.div.Nu u).L ↔ V.nuIn u x ∈ Ln u) ∧ V.div.h = h ∧ V.div.etaF = etaF ∧ V.div.HH = sFrame V.div.Nu V.div.h + V.div.RR.muMax ∧ ((∀ u φ x, n.Bu u (V.jN u φ) (V.jEE x) ∈ Set.range B.embLL) → ∀ u φ x, n.Bu u (V.jN u φ) (V.jEE x) = B.embLL (V.div.Bk u φ x)) := by
  intro B C G _ p e W₀ n η hη hXo Ln h etaF
  classical
  obtain ⟨X0, hX0, hX0n⟩ := GlobalTheory.exists_frames_normAt_eq_norm B.LL B.embLL (p.what₂ e W₀ n η hη).EE p.nR p.cR ⊥
  choose m bN XN hXN hXNn using fun u : B.Word =>
    GlobalTheory.Mem.exists_restricted_frames B.LL ((C.fm u).lat 0) (C.fm u).ramSub ⊥ ((C.fm u).lat_good 0).1
  let X : InfinitePlace B.LL → Matrix (Fin p.nR) (Fin p.nR) ℂ := fun v =>
    if v = InfinitePlace.mk B.embLL then X0 v else p.Xo v
  let Lr : Submodule (𝓞 B.LL) (Fin p.nR → B.LL) :=
    prescribedRowLat (p.what₂ e W₀ n η hη) (GlobalTheory.Mem.coordForm B.embLL p.cR)
  let RR : HLat B.LL :=
    { V := Fin p.nR → B.LL, ι := Fin p.nR, b := Pi.basisFun B.LL (Fin p.nR), X := X, L := Lr }
  let Nu : B.Word → HLat B.LL := fun u =>
    { V := (C.fm u).ramSub, ι := Fin (m u), b := bN u, X := XN u,
      L := (Ln u).comap ((C.fm u).ramSub.subtype.restrictScalars (𝓞 B.LL)) }
  let Dd : DivData B.LL B.Word :=
    { RR := RR, Nu := Nu, Bk := bkOf (p.what₂ e W₀ n η hη) p.cR, h := h,
      HH := sFrame Nu h + RR.muMax, HH_ge := le_rfl, etaF := etaF, Dall := p.Dall, delP := p.delp,
      delP_le_one := p.delp_le_one }
  let V : DivStage B C (p.what₂ e W₀ n η hη) :=
    { div := Dd
      div_good := ⟨fun v => by
        show IsUnit (if v = InfinitePlace.mk B.embLL then X0 v else p.Xo v).det
        split_ifs
        · exact hX0 v
        · exact hXo v, fun u v => hXN u v⟩
      jEE := GlobalTheory.Mem.coordForm B.embLL p.cR
      jEE_basis := by
        have : (fun i => GlobalTheory.Mem.coordForm B.embLL p.cR (Pi.basisFun B.LL (Fin p.nR) i)) = p.cR :=
          funext (GlobalTheory.Mem.coordForm_basisFun B.embLL p.cR)
        show LinearIndependent ℂ (fun i => GlobalTheory.Mem.coordForm B.embLL p.cR (Pi.basisFun B.LL (Fin p.nR) i)) ∧
          Submodule.span ℂ (Set.range (fun i => GlobalTheory.Mem.coordForm B.embLL p.cR (Pi.basisFun B.LL (Fin p.nR) i))) = ⊤
        rw [this]
        exact ⟨p.cR.linearIndependent, p.cR.span_eq⟩
      jN := GlobalTheory.Mem.ramForm (p.what₂ e W₀ n η hη)
      jN_basis := fun u => GlobalTheory.Mem.ramForm_basis (p.what₂ e W₀ n η hη) u (bN u)
      Dall_eq := rfl
      delP_eq := rfl
      nuIn := fun u => (C.fm u).ramSub.subtype
      nuIn_inj := fun u => (C.fm u).ramSub.injective_subtype
      nuIn_range := fun u => Submodule.range_subtype _
      nuIn_jN := fun u x => GlobalTheory.Mem.eMu_ramForm (p.what₂ e W₀ n η hη) u x
      nuIn_norm := fun u v x => hXNn u v x
      jEE_norm := fun x => by
        refine Eq.trans ?_ (hX0n x)
        show Formalism.HermitianLatticesTheory.normAt (Pi.basisFun B.LL (Fin p.nR)) X _ x = _
        simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord, X, if_true] }
  refine ⟨V, ⟨⟨LinearEquiv.refl _ _, fun x => rfl, fun v hv x y => ?_⟩, fun S N G' => ?_⟩,
    fun u x => Iff.rfl, rfl, rfl, rfl, fun H u φ x => bkOf_spec (p.what₂ e W₀ n η hη) p.cR H u φ x⟩
  · show Formalism.HermitianLatticesTheory.majAt (Pi.basisFun B.LL (Fin p.nR)) X v x y =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun B.LL (Fin p.nR)) p.Xo v x y
    simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, X, if_neg hv]
  · intro x
    simp only [Formalism.MainNotions.AbsolutelyIrreducibleSpan.sharp_RRset]
    exact Iff.rfl

end GlobalTheory.Mem.R3.Rw

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.Bare


set_option maxHeartbeats 2000000 in
theorem rows_le {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {y : Hd R.toRealDat}
    {mA : Bool → D.what₂.Tup → Mat1 D.what₂.LL G} {p : PkD D G} (t : PkT F y mA p) : (p.ch true).n ≤ p.Dall := by
  rcases Nat.eq_zero_or_pos p.Dall with h0 | hpos
  · have h := p.D_eq
    rw [h0, Nat.cast_zero, mul_zero] at h
    have h' : (p.ch true).n = 0 := by exact_mod_cast h
    omega
  · rw [t.dall] at hpos ⊢
    have hF := Module.finite_of_finrank_pos hpos
    have h1 := LinearMap.finrank_range_of_inj (t.ch true).jE_inj
    have h2 := Module.finrank_eq_card_basis (p.ch true).bs.toBasis
    rw [Fintype.card_fin] at h2
    rw [← h2, ← h1, (t.ch true).jE_range]
    have hle := Mult.goodPart_le R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))
        (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true))) R.e0
    have hf := Submodule.finiteDimensional_of_le hle
    refine le_trans ?_ (Submodule.finrank_mono hle)
    exact Submodule.finrank_map_le (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap
      (Mult.goodPart R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))
        (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true))) R.e0)


set_option maxHeartbeats 2000000 in
theorem frames_unit {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {y : Hd R.toRealDat}
    {mA : Bool → D.what₂.Tup → Mat1 D.what₂.LL G} {p : PkD D G} (t : PkT F y mA p) (v) : IsUnit (p.Xo v).det := by
  obtain ⟨_, -, h⟩ := t.rr
  exact (h v).2

end GlobalTheory.Mem.R3.Rw.Bare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicChartOfExpChartGenericFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicChartOfExpChartGenericFibre
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase

open GlobalTheory.Points Filter Topology

section Transfer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) {X : Var F} {j : X.X ⟶ gen Z}
  (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str)

theorem isOpenEmbedding_cxOf [IsOpenImmersion j] : IsOpenEmbedding (cxOf e σ hj) := by
  have hc : Continuous (cxOf e σ hj) :=
    continuous_induced_rng.2 ((continuous_comp (C := ℂ) j).comp continuous_subtype_val)
  refine ⟨IsEmbedding.of_comp hc continuous_subtype_val
    (((isOpenEmbedding_comp (C := ℂ) j).isEmbedding).comp IsEmbedding.subtypeVal), ?_⟩
  have hr : Set.range (cxOf e σ hj) = Subtype.val ⁻¹' Set.range fun x : Sp ℂ ⟶ X.X => x ≫ j := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, rfl⟩
    · rintro ⟨x, hx⟩
      replace hx : x ≫ j = y.1 := hx
      refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
      rw [← hj, ← Category.assoc, hx, ← Category.assoc, y.2, ← Spec.map_comp]
      rfl
  rw [hr]
  exact (isOpenEmbedding_comp (C := ℂ) j).isOpen_range.preimage continuous_subtype_val

variable [IsOpenImmersion j]

theorem le_preimage_cxOf (W : X.X.Opens) {z : CxPts X.str (σ.comp e.toRingHom)}
    (hz : z ∈ ptsIn X.str (σ.comp e.toRingHom) W) : ⊤ ≤ (cxOf e σ hj z).1 ⁻¹ᵁ (j ''ᵁ W) :=
  le_preimage_comp z.1 j (j.preimage_image_eq W).ge hz

theorem ev_eq_valAt'_cxOf (W : X.X.Opens) (g : Γ(X.X, W)) {z : CxPts X.str (σ.comp e.toRingHom)}
    (hz : z ∈ ptsIn X.str (σ.comp e.toRingHom) W) :
    ev X.str (σ.comp e.toRingHom) W g z = valAt' (cxOf e σ hj z).1 (j ''ᵁ W) ((j.appIso W).inv.hom g) := by
  have hle : W ≤ j ⁻¹ᵁ j ''ᵁ W := (j.preimage_image_eq W).ge
  change valR z.1 W g = valR (z.1 ≫ j) (j ''ᵁ W) _
  rw [← valR_appLE z.1 j hle hz, ← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_appLE]
  exact (valR_res z.1 le_rfl hz g).symm

end Transfer

open GlobalTheory.Points Filter Topology

theorem finrank_eq_of_differentiableAt {E₁ E₂ : Type} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] (Φ : OpenPartialHomeomorph E₁ E₂) {x : E₁} (hx : x ∈ Φ.source)
    (h₁ : DifferentiableAt ℂ Φ x) (h₂ : DifferentiableAt ℂ Φ.symm (Φ x)) :
    Module.finrank ℂ E₁ = Module.finrank ℂ E₂ := by
  have hl : (fderiv ℂ Φ.symm (Φ x)).comp (fderiv ℂ Φ x) = ContinuousLinearMap.id ℂ E₁ :=
    ((h₂.hasFDerivAt.comp x h₁.hasFDerivAt).congr_of_eventuallyEq
      (EventuallyEq.symm (Φ.eventually_left_inverse hx : Φ.symm ∘ Φ =ᶠ[𝓝 x] id))).unique (hasFDerivAt_id x)
  have h₁' : HasFDerivAt Φ (fderiv ℂ Φ x) (Φ.symm (Φ x)) := by
    rw [Φ.left_inv hx]
    exact h₁.hasFDerivAt
  have hr : (fderiv ℂ Φ x).comp (fderiv ℂ Φ.symm (Φ x)) = ContinuousLinearMap.id ℂ E₂ :=
    ((h₁'.comp (Φ x) h₂.hasFDerivAt).congr_of_eventuallyEq
      (EventuallyEq.symm (Φ.eventually_right_inverse' hx : Φ ∘ Φ.symm =ᶠ[𝓝 (Φ x)] id))).unique (hasFDerivAt_id (Φ x))
  exact (ContinuousLinearEquiv.equivOfInverse (fderiv ℂ Φ x) (fderiv ℂ Φ.symm (Φ x))
    (fun v => DFunLike.congr_fun hl v) (fun v => DFunLike.congr_fun hr v)).toLinearEquiv.finrank_eq

section Transfer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ}

theorem differentiableAt_valAt'_symm {n g : ℕ} {ch₀ : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)}
    {ex : ExpMaps Z σ g} (h : IsExpChart ch₀ ex) (U : (gen Z).Opens) (f : Γ(gen Z, U)) {b : Fin n → ℂ}
    (hb : b ∈ ch₀.target) (hU : ⊤ ≤ (ch₀.symm b).1 ⁻¹ᵁ U) :
    DifferentiableAt ℂ (fun b => valAt' (ch₀.symm b).1 U f) b :=
  (h.2.2.1 U f).2.differentiableAt ((h.2.2.1 U f).1.mem_nhds ⟨hb, hU⟩)

end Transfer

theorem exists_holoChart_of_expChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (X : Var F) (j : X.X ⟶ gen T.Z) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → ∀ (y : GlobalTheory.CxPts X.str (σ.comp e.toRingHom)) (n g : ℕ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g), IsExpChart ch₀ ex → cxOf e σ hj y ∈ ch₀.source → ch₀ (cxOf e σ hj y) = 0 → ∀ r : ℝ, 0 < r → ∃ (hn : n = X.dim) (r' : ℝ) (ch : OpenPartialHomeomorph (GlobalTheory.CxPts X.str (σ.comp e.toRingHom)) (ReciprocityTheory.L2DbarEstimates.V X.dim)), 0 < r' ∧ r' < r ∧ r' < 1 ∧ IsHoloChart ch ∧ y ∈ ch.source ∧ ch y = 0 ∧ (∀ z ∈ ch.source, (ch z).ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc X.dim 1) ∧ ∀ z ∈ ch.source, cxOf e σ hj z ∈ ch₀.source ∧ ch₀ (cxOf e σ hj z) = fun k => (r' : ℂ) * (ch z).ofLp (Fin.cast hn k) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ X j hj hji y n g ch₀ ex hex hy0 hy00 r hr
  set κ := cxOf e σ hj with hκdef
  have hκ : IsOpenEmbedding κ := isOpenEmbedding_cxOf e σ hj
  haveI : Nonempty (GlobalTheory.CxPts X.str (σ.comp e.toRingHom)) := ⟨y⟩
  set χ := (hκ.toOpenPartialHomeomorph κ).trans ch₀ with hχdef
  have hχ : ∀ u ∈ χ.target, κ (χ.symm u) = ch₀.symm u := fun u hu => by
    have h2 : ch₀.symm u ∈ Set.range κ := by
      have := hu.2
      rwa [Set.mem_preimage, IsOpenEmbedding.toOpenPartialHomeomorph_target] at this
    rw [OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply]
    exact hκ.toOpenPartialHomeomorph_right_inv κ h2
  have hyχ : y ∈ χ.source := ⟨trivial, hy0⟩
  have hχy : χ y = 0 := hy00
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.AlgChart.exists_mem_source (p := X.str) (σ := σ.comp e.toRingHom) (D := X.dim) y
  have hn : n = X.dim := by
    set Φ := χ.symm.trans c₁.e with hΦ
    have h0 : (0 : Fin n → ℂ) ∈ Φ.source := by
      refine ⟨?_, ?_⟩
      · rw [← hχy]
        exact χ.map_source hyχ
      · show χ.symm 0 ∈ c₁.e.source
        rw [← hχy, χ.left_inv hyχ]
        exact hc₁
    have h0t : (0 : Fin n → ℂ) ∈ χ.target := h0.1
    have h1 : DifferentiableAt ℂ Φ 0 := by
      rw [differentiableAt_euclidean]
      intro a
      have hev : (fun u => Φ u a) =ᶠ[𝓝 0]
          fun u => valAt' (ch₀.symm u).1 (j ''ᵁ c₁.U) ((j.appIso c₁.U).inv.hom (c₁.x a)) := by
        filter_upwards [Φ.open_source.mem_nhds h0] with u hu
        have hs : χ.symm u ∈ c₁.e.source := hu.2
        show c₁.e (χ.symm u) a = _
        rw [c₁.apply_eq _ hs a, ev_eq_valAt'_cxOf e σ hj _ _ (c₁.source_subset hs),
          show cxOf e σ hj (χ.symm u) = ch₀.symm u from hχ u hu.1]
      refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
      refine differentiableAt_valAt'_symm hex _ _ h0t.1 ?_
      rw [← hχ 0 h0t]
      exact le_preimage_cxOf e σ hj _ (c₁.source_subset h0.2)
    have h2 : DifferentiableAt ℂ Φ.symm (Φ 0) := by
      have hB : IsOpen Φ.target := Φ.open_target
      have hΦ0 : Φ 0 ∈ Φ.target := Φ.map_source h0
      have hsub : Φ.target ⊆ c₁.e.target := fun w hw => hw.1
      have hmaps : Set.MapsTo (fun w => κ (c₁.e.symm w)) Φ.target ch₀.source := fun w hw => hw.2.2
      have hhol : IsHolTo Φ.target (fun w => (κ (c₁.e.symm w)).1) := by
        intro U f
        have hset : {b ∈ Φ.target | ⊤ ≤ (κ (c₁.e.symm b)).1 ⁻¹ᵁ U} =
            Φ.target ∩ c₁.e.symm ⁻¹' ptsIn X.str (σ.comp e.toRingHom) (j ⁻¹ᵁ U) := rfl
        refine ⟨?_, ?_⟩
        · rw [hset]
          exact (c₁.e.continuousOn_symm.mono hsub).isOpen_inter_preimage hB (isOpen_ptsIn _)
        · rw [hset]
          refine ((c₁.holo (j ⁻¹ᵁ U) ((j.app U).hom f)).mono fun w (hw : w ∈ Φ.target ∩ c₁.e.symm ⁻¹' ptsIn X.str (σ.comp e.toRingHom) (j ⁻¹ᵁ U)) => ⟨hsub hw.1, hw.2⟩).congr
            fun w _ => ?_
          exact valR_comp (c₁.e.symm w).1 j U f
      rw [differentiableAt_pi]
      intro k
      have hd := (hex.2.1 k (ReciprocityTheory.L2DbarEstimates.V X.dim) Φ.target (fun w => κ (c₁.e.symm w)) hB hhol hmaps).differentiableAt
        (hB.mem_nhds hΦ0)
      exact hd
    have := finrank_eq_of_differentiableAt Φ h0 h1 h2
    simpa [finrank_euclideanSpace_fin] using this
  subst hn
  have hr1 : 0 < min r 1 := lt_min hr one_pos
  set r' : ℝ := min r 1 / 2 with hr'
  have hr'0 : 0 < r' := half_pos hr1
  have hr'r : r' < min r 1 := half_lt_self hr1
  have hr'c : (r' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr'0.ne'
  let L : (Fin X.dim → ℂ) ≃L[ℂ] ReciprocityTheory.L2DbarEstimates.V X.dim :=
    (ContinuousLinearEquiv.smulLeft (Units.mk0 ((r' : ℂ)⁻¹) (inv_ne_zero hr'c))).trans
      (EuclideanSpace.equiv (Fin X.dim) ℂ).symm
  have hL : ∀ u k, (L u).ofLp k = (r' : ℂ)⁻¹ * u k := by
    intro u k
    simp [L]
  let ch := (χ.trans (OpenPartialHomeomorph.ofSet (Metric.ball (0 : Fin X.dim → ℂ) r') Metric.isOpen_ball)).trans
    L.toHomeomorph.toOpenPartialHomeomorph
  have hchs : ∀ v, ch.symm v = χ.symm (L.symm v) := fun v => rfl
  have hch : ∀ z, ch z = L (χ z) := fun z => rfl
  have hsrc : ∀ z ∈ ch.source, z ∈ χ.source ∧ χ z ∈ Metric.ball (0 : Fin X.dim → ℂ) r' := fun z hz => hz.1
  have htgt : ∀ v ∈ ch.target, L.symm v ∈ χ.target := fun v hv => hv.2.2
  refine ⟨rfl, r', ch, hr'0, hr'r.trans_le (min_le_left _ _), hr'r.trans_le (min_le_right _ _), ?_,
    ⟨⟨hyχ, ?_⟩, trivial⟩, ?_, ?_, ?_⟩
  · intro W f v hv
    have hopen : IsOpen (ch.target ∩ ch.symm ⁻¹' ptsIn X.str (σ.comp e.toRingHom) W) :=
      ch.continuousOn_symm.isOpen_inter_preimage ch.open_target (isOpen_ptsIn W)
    refine DifferentiableAt.differentiableWithinAt ?_
    have hev : (ev X.str (σ.comp e.toRingHom) W f ∘ ch.symm) =ᶠ[𝓝 v]
        fun w => valAt' (ch₀.symm (L.symm w)).1 (j ''ᵁ W) ((j.appIso W).inv.hom f) := by
      filter_upwards [hopen.mem_nhds hv] with w hw
      rw [Function.comp_apply, ev_eq_valAt'_cxOf e σ hj W f hw.2, hchs,
        show cxOf e σ hj (χ.symm (L.symm w)) = ch₀.symm (L.symm w) from hχ _ (htgt w hw.1)]
    refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
    have hb := htgt v hv.1
    refine (differentiableAt_valAt'_symm hex (j ''ᵁ W) _ hb.1 ?_).comp v L.symm.differentiableAt
    rw [← hχ _ hb]
    exact le_preimage_cxOf e σ hj W hv.2
  · show χ y ∈ Metric.ball 0 r'
    rw [hχy]
    exact Metric.mem_ball_self hr'0
  · rw [hch, hχy, map_zero]
  · intro z hz
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc, Set.mem_setOf_eq]
    intro k
    rw [hch, hL, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr'0.le]
    have h1 := (hsrc z hz).2
    rw [mem_ball_zero_iff] at h1
    have h2 : ‖χ z k‖ < r' := (norm_le_pi_norm (χ z) k).trans_lt h1
    calc r'⁻¹ * ‖χ z k‖ < r'⁻¹ * r' := mul_lt_mul_of_pos_left h2 (inv_pos.2 hr'0)
      _ = 1 := inv_mul_cancel₀ hr'0.ne'
  · intro z hz
    refine ⟨hz.1.1.2, ?_⟩
    funext k
    show χ z k = _
    rw [hch, hL, Fin.cast_eq_self, ← mul_assoc, mul_inv_cancel₀ hr'c, one_mul]

end GlobalTheory.LieBase
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicChartOfExpChartGenericFibreStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphicChart_of_expChart_genericFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (X : Var F) (j : X.X ⟶ gen T.Z) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → ∀ (y : GlobalTheory.CxPts X.str (σ.comp e.toRingHom)) (n g : ℕ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g), IsExpChart ch₀ ex → cxOf e σ hj y ∈ ch₀.source → ch₀ (cxOf e σ hj y) = 0 → ∀ r : ℝ, 0 < r → ∃ (hn : n = X.dim) (r' : ℝ) (ch : OpenPartialHomeomorph (GlobalTheory.CxPts X.str (σ.comp e.toRingHom)) (ReciprocityTheory.L2DbarEstimates.V X.dim)), 0 < r' ∧ r' < r ∧ r' < 1 ∧ IsHoloChart ch ∧ y ∈ ch.source ∧ ch y = 0 ∧ (∀ z ∈ ch.source, (ch z).ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc X.dim 1) ∧ ∀ z ∈ ch.source, cxOf e σ hj z ∈ ch₀.source ∧ ch₀ (cxOf e σ hj z) = fun k => (r' : ℂ) * (ch z).ofLp (Fin.cast hn k) := by
  first | exact @GlobalTheory.LieBase.exists_holoChart_of_expChart | exact GlobalTheory.LieBase.exists_holoChart_of_expChart | (intros; apply GlobalTheory.LieBase.exists_holoChart_of_expChart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArithmeticNefModelOfAmple
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam
open GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.Points

namespace GlobalTheory.AmpleModelPos

theorem isGenerated_tens {X : Scheme.{0}} {A B : LB X} (hA : IsGenerated A) (hB : IsGenerated B) :
    IsGenerated (tens A B) := by
  obtain ⟨a, s, hs⟩ := hA
  obtain ⟨b, t, ht⟩ := hB
  refine isGenerated_of_finite (fun q : Fin a × Fin b => EndOnTorsion.tensSec (s q.1) (t q.2))
    (top_le_iff.1 fun y _ => ?_)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hs.ge (Set.mem_univ y))
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (ht.ge (Set.mem_univ y))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), (EndOnTorsion.nonzeroLocus_tensSec (s i) (t j)).ge ⟨hi, hj⟩⟩

section Pull

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D N : ℕ}

end Pull

end GlobalTheory.AmpleModelPos
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelativeAmpleSpreadOfPolarizedFiber
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PolNearAmple

theorem relAmple_near_of_polAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsNoetherianRing R] (t : SAB H (Sp R)), IsProper t.G.hom → ∀ (C : Type) [Field C] (g : R →+* C), GlobalTheory.LN.PolAt t (spMap g) → ∃ s : R, g s ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (h : R →+* R'), IsUnit (h s) → ∀ (t' : SAB H (Sp R')), SABMap t' t (spMap h) → RelAmple t'.G t'.PP.L := by
  intro E _ _ _ H R _ _ t hprop C _ g hpol
  have pull_isLB : ∀ {X Y : Scheme.{0}} {L : LB X}, L.IsLB → (F : Y ⟶ X) → (L.pull F).IsLB := by
    intro X Y L hL F
    exact {
      cover := top_le_iff.1 fun y _ => by
        obtain ⟨i, hi⟩ := exists_chart hL (F y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
      g_self := fun J => unit_ext fun y hy => by
        rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
        exact gm_self hL _ y (mem_pull.1 hy)
      cocycle := fun I J K => unit_ext fun y hy => by
        rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy,
          gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
          gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
        exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2) }
  have : Smooth t.G.hom := t.semi.smooth
  have : Flat t.G.hom := inferInstance
  have hL := t.PP.isLB
  let p : Ideal R := RingHom.ker g
  haveI : p.IsPrime := RingHom.ker_isPrime g
  let g₀ := algebraMap R p.ResidueField
  have hf₂ : p.primeCompl ≤ (IsUnit.submonoid C).comap g := fun x hx =>
    show IsUnit (g x) from isUnit_iff_ne_zero.2 fun h0 => hx (RingHom.mem_ker.2 h0)
  let i : p.ResidueField →+* C := Ideal.ResidueField.lift p g le_rfl hf₂
  have hcomp : i.comp g₀ = g := RingHom.ext fun r => Ideal.ResidueField.lift_algebraMap p g le_rfl hf₂ r
  have hsp : spMap i ≫ spMap g₀ = spMap g := by
    rw [← hcomp]
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have h₂ : IsPullback (pullback.fst t.G.hom (spMap g)) (pullback.snd t.G.hom (spMap g)) t.G.hom
      (spMap i ≫ spMap g₀) := by
    rw [hsp]; exact IsPullback.of_hasPullback _ _
  have hA₁ : RelAmple ((Over.pullback (spMap g₀)).obj t.G) (t.PP.L.pull (pullback.fst t.G.hom (spMap g₀))) :=
    FibreAmple.relAmple_of_fieldExtension (f := t.G.hom) hL i (IsPullback.of_hasPullback t.G.hom (spMap g₀)) h₂
      (pull_isLB hL _) (GlobalTheory.lbIso_refl (pull_isLB hL _)) hpol.2.1
  obtain ⟨s, hs, hAs⟩ := ProperFinite.relAmple_near_fibre t.G hL g₀ (FibreAmple.residueField_fraction p) hA₁
  refine ⟨s, fun h0 => hs (Ideal.algebraMap_residueField_eq_zero.2 (RingHom.mem_ker.2 h0)), ?_⟩
  intro R' _ h hu t' m
  let D : (Sp R).Opens := PrimeSpectrum.basicOpen s
  have : IsAffine D.toScheme := IsAffineOpen.Spec_basicOpen (R := CommRingCat.of R) s
  have hrange : Set.range (spMap h) ⊆ Set.range D.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    show s ∉ Ideal.comap h y.asIdeal
    exact fun hy => y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hy hu)
  let u : Sp R' ⟶ D.toScheme := IsOpenImmersion.lift D.ι (spMap h) hrange
  have hu' : u ≫ D.ι = spMap h := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨φ, hφ, Hp⟩ := FibreAmple.exists_isPullback (IsPullback.of_hasPullback t.G.hom D.ι) m.cart.1 u hu'
  have e₀ : LBIso t'.PP.L (t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := (isPullCubical_iff m.cm t.cub t'.cub).1 m.lin
    exact ⟨w, (isGen_iff w).2 hw⟩
  obtain ⟨w, hw⟩ : LBIso t'.PP.L ((t.PP.L.pull (pullback.fst t.G.hom D.ι)).pull φ) :=
    LBIso.trans t'.PP.isLB (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) e₀
      (FibreAmple.lbIso_pull_comp hφ (GlobalTheory.lbIso_refl (pull_isLB hL _)))
  exact relAmple_pull (A := (Over.pullback D.ι).obj t.G) (A' := t'.G) Hp (pull_isLB hL _) t'.PP.isLB
    ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) hAs

end GlobalTheory.PolNearAmple
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackStalkIsDomainEtale
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TraitGeneric

theorem mem_of_dense_of_maximal {X : Type} [TopologicalSpace X] [NoetherianSpace X] [QuasiSober X] {x : X}
    (hx : ∀ y, y ⤳ x → x ⤳ y) {U : Set X} (hU : IsOpen U) (hd : Dense U) : x ∈ U := by
  obtain ⟨o, ho, hne, hs⟩ := NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _
    (irreducibleComponent_mem_irreducibleComponents x)
  obtain ⟨y, hyo, hyU⟩ := hd.inter_open_nonempty o ho hne
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := x)) isClosed_irreducibleComponent
  have e := hx ξ (hξ.specializes mem_irreducibleComponent)
  exact (e.trans (hξ.specializes (hs hyo))).mem_open hU hyU

end GlobalTheory.TraitGeneric
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcIntegral
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef
open MonoidalCategory CartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ArcChartExt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem sabMap_cast_φ {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f₁ f₂ : S' ⟶ S} (h : f₁ = f₂)
    (n : SABMap t' t f₁) : (h ▸ n).φ = n.φ := by
  subst h; rfl

theorem exists_sab_cancel_id {S S' : Scheme.{0}} {t : SAB H S} {t' t'' : SAB H S'} {f : S' ⟶ S}
    (m : SABMap t' t f) (n : SABMap t'' t f) : ∃ m' : SABMap t'' t' (𝟙 S'), n.φ = m'.φ ≫ m.φ := by
  obtain ⟨m', hm'⟩ := GlobalTheory.ObjMaps.exists_sab_cancel (g := 𝟙 S') m ((Category.id_comp f).symm ▸ n)
  exact ⟨m', (sabMap_cast_φ (Category.id_comp f).symm n).symm.trans hm'⟩

end GlobalTheory.ArcChartExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthBoundCongrGermGram
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthBoundCongrGermGram
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.GoodMetric

theorem goodBound_congr_nhds (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (c : ℝ) (N : ℕ)
    (G G' : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n) :
    G =ᶠ[nhds v] G' → GlobalTheory.GoodMetric.GoodBound S c N G v → GlobalTheory.GoodMetric.GoodBound S c N G' v := by
  intro h hb
  have hv : G v = G' v := h.eq_of_nhds
  have hc : ∀ ξ, (fun u => GlobalTheory.HermFrame.conn G u ξ) =ᶠ[nhds v] (fun u => GlobalTheory.HermFrame.conn G' u ξ) :=
    fun ξ => h.eventuallyEq_nhds.mono fun x hx => GlobalTheory.HermFrame.conn_congr hx ξ
  refine ⟨fun i j => ?_, ?_, fun a i j => ?_, fun a b i j => ?_, fun a b i j => ?_⟩
  · rw [← hv]; exact hb.entry i j
  · rw [← hv]; exact hb.det
  · rw [← GlobalTheory.HermFrame.conn_congr h]; exact hb.form a i j
  · rw [← GlobalTheory.HermFrame.curv_congr h]; exact hb.dbar a b i j
  · rw [← GlobalTheory.HermFrame.mdel_congr (hc _), ← GlobalTheory.HermFrame.mdel_congr (hc _)]; exact hb.del a b i j

end GlobalTheory.GoodMetric
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthBoundCongrGermGramStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordGoodGrowthBound_congr_germ_gram : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (c : ℝ) (N : ℕ) (G G' : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n), G =ᶠ[nhds v] G' → GlobalTheory.GoodMetric.GoodBound S c N G v → GlobalTheory.GoodMetric.GoodBound S c N G' v := by
  first | exact @GlobalTheory.GoodMetric.goodBound_congr_nhds | exact GlobalTheory.GoodMetric.goodBound_congr_nhds | (intros; apply GlobalTheory.GoodMetric.goodBound_congr_nhds <;> assumption)
end
end
