module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfI
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import Formalism.LocalToGlobal.Divisibility.RowSideTie
public import Formalism.QuotientMetricDivisors.FinalW
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffCoeffsInIdealSubstOfConstantCoeffZero
public import GroundTheory.GlobalFields.WeilGroups.QuasiCharacterDecomposition
public import GroundTheory.GlobalFields.TateThesis.NonvanishingPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinWeierstrassValuesLatticeTau
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedAdjointRingActionScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryEqAdditiveLeadingTerms

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
noncomputable section

namespace GlobalTheory.UPel.HT.EtLev

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

def IsEtLevOver {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) {T : Over S}
    (l : D.La → (T ⟶ o.A)) : Prop :=
  (∀ x y, l (x + y) = l x * l y) ∧ (∀ (c : D.O) x, l (c • x) = l x ≫ o.act.act c) ∧
    (∀ x ∈ wSub D w0 r, l x = 1) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T.left),
      (∀ y, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ l y = 1 → y ∈ wSub D w0 r) ∧
      ∀ g : Over.mk (x ≫ T.hom) ⟶ o.A, (∀ c ∈ w0 ^ r, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) →
        ∃ y, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ l y = g

def ptOf {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} {T : Scheme.{0}} {t : T ⟶ S} {s₁ : T ⟶ Sp R} {o : Obj b N s}
    {o₁ : Obj b N s₁} (m : ObjMap o₁ o t) (l : 𝟙_ (Over T) ⟶ o₁.A) : Over.mk t ⟶ o.A :=
  Over.homMk (l.left ≫ m.φ) (by
    rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w l]
    exact Category.id_comp t)

def levAct {w0 : Ideal (𝓞 D.F)} {r : ℕ} (g : LevGrp D w0 r) (y : D.La) : D.La :=
  Function.surjInv (Submodule.mkQ_surjective (wSub D w0 r)) (g ((wSub D w0 r).mkQ y))

theorem mkQ_levAct {w0 : Ideal (𝓞 D.F)} {r : ℕ} (g : LevGrp D w0 r) (y : D.La) :
    (wSub D w0 r).mkQ (levAct g y) = g ((wSub D w0 r).mkQ y) :=
  Function.surjInv_eq _ _

end GlobalTheory.UPel.HT.EtLev
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramChartSubFormEntryLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramChartSubFormEntryLe
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

namespace GlobalTheory.GramChartNear

open scoped Matrix ComplexConjugate

theorem gw_sub_jd_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (w : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (τ : X.Ψ) (a b : Fin r), (r : ℝ) * ‖w‖ ≤ 1 → ‖ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.Gw X w τ a b - ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.Jd X a b‖ ≤ 3 * ‖w‖ := by
  intro E _ _ _ r X w τ a b hrw
  set L : Matrix (Fin r) (Fin r) ℂ := mat (nmat X w) τ - 1 with hLdef
  have hL : ∀ i j, ‖L i j‖ ≤ ‖w‖ := fun i j => PoinPf.nmat_entry X w τ i j
  have hs : ∀ c : Fin r, ‖((sgn X.p0 (c : ℕ) : ℝ) : ℂ)‖ = 1 := fun c => by
    rw [Complex.norm_real, Real.norm_eq_abs, PoinPf.abs_sgn]
  have h1 : mat (nmat X w) τ = 1 + L := by rw [hLdef]; abel
  have key : PoinPf.Gw X w τ - PoinPf.Jd X =
      Lᵀ * PoinPf.Jd X + PoinPf.Jd X * L.map (starRingEnd ℂ) + Lᵀ * PoinPf.Jd X * L.map (starRingEnd ℂ) := by
    rw [PoinPf.Gw, h1, Matrix.transpose_add, Matrix.transpose_one,
      Matrix.map_add _ (map_add (starRingEnd ℂ)), Matrix.map_one _ (map_zero _) (map_one _)]
    noncomm_ring
  rw [← Matrix.sub_apply, key, Matrix.add_apply, Matrix.add_apply, PoinPf.Jd, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply]
  have t1 : ‖L b a * ((sgn X.p0 (b : ℕ) : ℝ) : ℂ)‖ ≤ ‖w‖ := by
    rw [norm_mul, hs, mul_one]; exact hL b a
  have t2 : ‖((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * (starRingEnd ℂ) (L a b)‖ ≤ ‖w‖ := by
    rw [norm_mul, hs, one_mul, Complex.norm_conj]; exact hL a b
  have t3 : ‖∑ c, L c a * ((sgn X.p0 (c : ℕ) : ℝ) : ℂ) * (starRingEnd ℂ) (L c b)‖ ≤ ‖w‖ := by
    calc _ ≤ ∑ c : Fin r, ‖L c a * ((sgn X.p0 (c : ℕ) : ℝ) : ℂ) * (starRingEnd ℂ) (L c b)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _c : Fin r, ‖w‖ * ‖w‖ := by
          refine Finset.sum_le_sum fun c _ => ?_
          rw [norm_mul, norm_mul, hs, mul_one, Complex.norm_conj]
          exact mul_le_mul (hL c a) (hL c b) (norm_nonneg _) (norm_nonneg _)
      _ = ‖w‖ * ((r : ℝ) * ‖w‖) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ ‖w‖ * 1 := mul_le_mul_of_nonneg_left hrw (norm_nonneg _)
      _ = ‖w‖ := mul_one _
  calc _ ≤ _ := norm_add₃_le
    _ ≤ ‖w‖ + ‖w‖ + ‖w‖ := add_le_add (add_le_add t1 t2) t3
    _ = 3 * ‖w‖ := by ring

end GlobalTheory.GramChartNear
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramChartSubFormEntryLeStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramChart_sub_form_entry_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (w : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (τ : X.Ψ) (a b : Fin r), (r : ℝ) * ‖w‖ ≤ 1 → ‖ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.Gw X w τ a b - ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.Jd X a b‖ ≤ 3 * ‖w‖ := by
  first | exact @GlobalTheory.GramChartNear.gw_sub_jd_le | exact GlobalTheory.GramChartNear.gw_sub_jd_le | (intros; apply GlobalTheory.GramChartNear.gw_sub_jd_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTangentIffTanS
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieAway

section Basic

variable {R : Type} [CommRing R]

theorem scaleS_toRingHom (c : R) : (Chart.scaleS (S := R) c).toRingHom = epsScaleR c := by
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
  · simp [Chart.scaleS_fst, epsScaleR]
  · simp [Chart.scaleS_snd, epsScaleR]

variable {G : Over (Sp R)} [GrpObj G]

theorem tanS_of_isTangent {v : epsR R ⟶ G} (h : IsTangent v) : Chart.TanS (S := R) (A := R) v :=
  (Chart.isTan_iff v).mpr h

theorem isTangent_of_tanS {v : epsR R ⟶ G} (h : Chart.TanS (S := R) (A := R) v) : IsTangent v :=
  (Chart.isTan_iff v).mp h

theorem isTangent_iff_tanS (r : R) (y : epsR (Localization.Away r) ⟶ Chart.Gs G r) :
    IsTangent y ↔ Chart.TanS (Chart.pushR G y) := by
  rw [← Chart.isTan_iff]
  constructor
  · intro h
    have := congrArg (Chart.pushR G) h
    rw [Chart.pushR_spMap, Chart.pushR_one] at this
    exact this
  · intro h
    apply Chart.pushR_inj G
    rw [Chart.pushR_spMap, Chart.pushR_one]
    exact h

theorem scale_left (c : R) (v : epsR R ⟶ G) :
    Geo.Tor.spMap (epsScaleR c) ≫ v.left = (Chart.spMap (Chart.scaleS (S := R) c) ≫ v).left := by
  rw [Over.comp_left, Chart.spMap_left, ← scaleS_toRingHom]

end Basic

end GlobalTheory.LieAway

namespace GlobalTheory.LieAway

section Res

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] (r : R)

def resA (v : epsR R ⟶ G) : epsR (Localization.Away r) ⟶ Chart.Gs G r :=
  Chart.pullR G (Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away r))) ≫ v)

theorem pushR_resA (v : epsR R ⟶ G) :
    Chart.pushR G (resA r v) = Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away r))) ≫ v :=
  Chart.pushR_pullR G _

variable {O O' : Type} [CommRing O] [CommRing O'] [IsCommMonObj G] (a : OAct O G)
  (a' : OAct O' (Chart.Gs G r))

def resL (v : GlobalTheory.Serre.Lie a) : GlobalTheory.Serre.Lie a' :=
  GlobalTheory.Serre.Lie.mk a' (resA r v.hom) (by
    rw [isTangent_iff_tanS, pushR_resA]
    exact Chart.tanS_restrict _ (tanS_of_isTangent v.isTangent))

theorem pushR_resL (v : GlobalTheory.Serre.Lie a) :
    Chart.pushR G (resL r a a' v).hom = Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away r))) ≫ v.hom :=
  pushR_resA r v.hom

theorem pushR_smul (c : Localization.Away r) (y : GlobalTheory.Serre.Lie a') :
    Chart.pushR G (c • y).hom = Chart.spMap (Chart.scaleS (S := R) c) ≫ Chart.pushR G y.hom := by
  have e : (c • y).hom = Chart.spMap (Chart.scaleS (S := Localization.Away r) c) ≫ y.hom :=
    Over.OverMorphism.ext ((GlobalTheory.Serre.Lie.hom_smul_left c y).trans (scale_left c y.hom))
  rw [e, Chart.pushR_spMap]
  rfl

theorem hom_smul_eq (c : R) (v : GlobalTheory.Serre.Lie a) :
    (c • v).hom = Chart.spMap (Chart.scaleS (S := R) c) ≫ v.hom :=
  Over.OverMorphism.ext ((GlobalTheory.Serre.Lie.hom_smul_left c v).trans (scale_left c v.hom))

theorem pushR_add (y z : GlobalTheory.Serre.Lie a') :
    Chart.pushR G (y + z).hom = Chart.pushR G y.hom * Chart.pushR G z.hom :=
  map_mul (Chart.pushforwardHom G) y.hom z.hom

theorem resL_add (v w : GlobalTheory.Serre.Lie a) : resL r a a' (v + w) = resL r a a' v + resL r a a' w := by
  ext1
  apply Chart.pushR_inj G
  rw [pushR_add, pushR_resL, pushR_resL, pushR_resL, GlobalTheory.Serre.Lie.hom_add, MonObj.comp_mul]

theorem resL_smul (c : R) (v : GlobalTheory.Serre.Lie a) :
    resL r a a' (c • v) = algebraMap R (Localization.Away r) c • resL r a a' v := by
  ext1
  apply Chart.pushR_inj G
  rw [pushR_smul, pushR_resL, pushR_resL, hom_smul_eq, Chart.res_scale]
  rfl

end Res

end GlobalTheory.LieAway

namespace GlobalTheory.LieAway

section Cover

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [∀ s : R, Smooth (Chart.Gs G s).hom]

theorem tan_away_uniq (r : R) {w : Chart.sp (R₀ := R) (DualNumber R) ⟶ G} (hw : Chart.TanS w)
    (h1 : Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away r))) ≫ w = 1) :
    ∃ N : ℕ, Chart.spMap (Chart.scaleS (S := R) (r ^ N)) ≫ w = 1 := by
  classical
  obtain ⟨n, s, hs, hC⟩ := Chart.exists_cover G
  have C : ∀ k, Chart.Chart (Chart.Gs G (s k)) := fun k => (hC k).some
  have hwk : ∀ k, Chart.TanS (Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away (s k)))) ≫ w) :=
    fun k => Chart.tanS_restrict _ hw
  have hone : ∀ (A : Type) [CommRing A] [Algebra R A], Chart.TanS (1 : Chart.sp (R₀ := R) (DualNumber A) ⟶ G) :=
    fun A _ _ => Chart.comp_one' _
  have h2 : ∀ k, ∃ N : ℕ, Chart.spMap (Chart.scaleS (S := R) (algebraMap R (Localization.Away (s k)) r ^ N)) ≫
      Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away (s k)))) ≫ w =
      Chart.spMap (Chart.scaleS (S := R) (algebraMap R (Localization.Away (s k)) r ^ N)) ≫ 1 := by
    intro k
    apply Chart.tanS_away_uniq (C k) (A := Localization.Away (s k)) r (hwk k) (hone _)
    have hu : IsUnit (algebraMap R (Localization.Away (algebraMap R (Localization.Away (s k)) r)) r) :=
      Chart.isUnit_qv (s k) r
    rw [Chart.comp_one', Chart.res_res,
      show (IsScalarTower.toAlgHom R (Localization.Away (s k))
          (Localization.Away (algebraMap R (Localization.Away (s k)) r))).comp
          (Algebra.ofId R (Localization.Away (s k))) =
        (Chart.awayHom r _ hu).comp (Algebra.ofId R (Localization.Away r)) from Chart.ofId_ext _ _,
      ← Chart.res_res, h1, Chart.comp_one']
  choose N hN using h2
  refine ⟨Finset.univ.sup N, Chart.tan_ext_cover s hs fun k => ?_⟩
  rw [Chart.comp_one', Chart.res_scale, Algebra.ofId_apply, map_pow,
    Chart.scale_pow_mono _ (Finset.le_sup (f := N) (Finset.mem_univ k)) (hN k), Chart.comp_one']

theorem tan_away_lift (r : R) (hr : Nonempty (Chart.Chart (Chart.Gs G r)))
    {y : Chart.sp (R₀ := R) (DualNumber (Localization.Away r)) ⟶ G} (hy : Chart.TanS y) :
    ∃ N : ℕ, ∃ w : Chart.sp (R₀ := R) (DualNumber R) ⟶ G, Chart.TanS w ∧
      Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away r))) ≫ w =
        Chart.spMap (Chart.scaleS (S := R) (algebraMap R (Localization.Away r) r ^ N)) ≫ y := by
  obtain ⟨n, s, hs, hC⟩ := Chart.exists_cover G
  let s' : Fin (n + 1) → R := Fin.cons r s
  have hs' : Ideal.span (Set.range s') = ⊤ := by
    rw [eq_top_iff, ← hs]
    apply Ideal.span_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨k.succ, Fin.cons_succ _ _ _⟩
  have C : ∀ k, Chart.Chart (Chart.Gs G (s' k)) := Fin.cases hr.some (fun k => (hC k).some)
  exact Chart.tan_extend s' hs' C 0 hy

end Cover

end GlobalTheory.LieAway

namespace GlobalTheory.LieAway

theorem lie_away {R O O' : Type} [CommRing R] [CommRing O] [CommRing O'] (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] (a : OAct O G) (r : R) (a' : OAct O' (ReciprocityTheory.ChartRestriction.G.Chart.Gs G r)) :
    Nonempty (ReciprocityTheory.ChartRestriction.G.Chart.Chart (ReciprocityTheory.ChartRestriction.G.Chart.Gs G r)) →
    Nonempty (LocalizedModule (Submonoid.powers r) (GlobalTheory.Serre.Lie a) ≃ₗ[Localization.Away r] GlobalTheory.Serre.Lie a') := by
  intro hr
  have : ∀ s : R, Smooth (Chart.Gs G s).hom := fun s => show Smooth (pullback.snd G.hom _) from inferInstance
  letI : Module R (GlobalTheory.Serre.Lie a') := Module.compHom _ (algebraMap R (Localization.Away r))
  haveI : IsScalarTower R (Localization.Away r) (GlobalTheory.Serre.Lie a') :=
    ⟨fun x y z => by rw [Algebra.smul_def]; exact mul_smul _ y z⟩
  let ρ : GlobalTheory.Serre.Lie a →ₗ[R] GlobalTheory.Serre.Lie a' :=
    { toFun := resL r a a'
      map_add' := resL_add r a a'
      map_smul' := resL_smul r a a' }
  have hρ : ∀ v, Chart.pushR G (ρ v).hom =
      Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away r))) ≫ v.hom := pushR_resL r a a'
  haveI : IsLocalizedModule (Submonoid.powers r) ρ := by
    refine ⟨fun x => ?_, fun y => ?_, fun {x₁ x₂} h => ?_⟩
    · rw [Module.End.isUnit_iff]
      obtain ⟨u, hu⟩ := IsLocalization.map_units (Localization.Away r) x
      have hx : ∀ m : GlobalTheory.Serre.Lie a',
          (algebraMap R (Module.End R (GlobalTheory.Serre.Lie a')) x) m = (u : Localization.Away r) • m := fun m => by
        rw [Module.algebraMap_end_apply, hu]; rfl
      refine ⟨fun m₁ m₂ e => ?_, fun m => ⟨(↑u⁻¹ : Localization.Away r) • m, ?_⟩⟩
      · rw [hx, hx] at e
        have := congrArg (fun z => (↑u⁻¹ : Localization.Away r) • z) e
        simp only [smul_smul, Units.inv_mul, one_smul] at this
        exact this
      · rw [hx, smul_smul, Units.mul_inv, one_smul]
    · have hy : Chart.TanS (Chart.pushR G y.hom) := (isTangent_iff_tanS r y.hom).mp y.isTangent
      obtain ⟨N, w, hw, he⟩ := tan_away_lift r hr hy
      refine ⟨(GlobalTheory.Serre.Lie.mk a w (isTangent_of_tanS hw), ⟨r ^ N, N, rfl⟩), ?_⟩
      ext1
      apply Chart.pushR_inj G
      rw [hρ, GlobalTheory.Serre.Lie.hom_mk, he]
      change Chart.pushR G ((algebraMap R (Localization.Away r) (r ^ N)) • y).hom = _
      rw [pushR_smul, map_pow]
    · have h0 : ρ (x₁ - x₂) = 0 := by rw [map_sub, h, sub_self]
      have h1 : Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away r))) ≫ (x₁ - x₂).hom = 1 := by
        rw [← hρ, h0, GlobalTheory.Serre.Lie.hom_zero, Chart.pushR_one]
      obtain ⟨N, hN⟩ := tan_away_uniq r (tanS_of_isTangent (x₁ - x₂).isTangent) h1
      refine ⟨⟨r ^ N, N, rfl⟩, ?_⟩
      rw [← sub_eq_zero, ← smul_sub]
      ext1
      rw [Submonoid.smul_def, hom_smul_eq, hN, GlobalTheory.Serre.Lie.hom_zero]
  exact ⟨(IsLocalizedModule.iso (Submonoid.powers r) ρ).extendScalarsOfIsLocalization (Submonoid.powers r)
    (Localization.Away r)⟩

end GlobalTheory.LieAway
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeGoodProjectorEqRangeGoodCoordinates
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory

theorem range_lvlOp_idemOf_eq_range_lvlPr_mul_V0E {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
    {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms) (X : Finset (G → K)) (P : Subgroup G)
    (ψ : P →* Kˣ) :
    LinearMap.range (S.lvlOp r P ψ (idemOf X)).mulVecLin =
      LinearMap.range (S.lvlPr r P ψ * S.V0E r X P ψ).mulVecLin := by
  have hE : LinearMap.range (S.lvlE r P ψ).mulVecLin =
      LinearMap.range (S.gaMat r (lvlIdem P ψ)).mulVecLin := (image_idempotent_spec K _ _).2
  have hV : LinearMap.range (S.V0E r X P ψ).mulVecLin =
      LinearMap.range (S.gaMat r (goodAt X P ψ)).mulVecLin := (image_idempotent_spec K _ _).2
  have hm : S.gaMat r (goodAt X P ψ) = S.gaMat r (idemOf X) * S.gaMat r (lvlIdem P ψ) :=
    (group_action_matrix_hom K S G r).2 _ _
  unfold CSD.lvlOp
  rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, LinearMap.range_comp, LinearMap.range_comp,
    hE, hV, hm, Matrix.mulVecLin_mul, LinearMap.range_comp, Submodule.map_comp]

theorem range_goodProjector_eq_range_goodCoordinates : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
    (A : FamIn D.what₂.LL G Pl0 T m) (s : ℕ), A.fam.Ok s → ∀ (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (t : T),
    LinearMap.range (rE D A P ψ t).mulVecLin = LinearMap.range (rV0 D A P ψ t).mulVecLin := by
  intro D G _ _ Pl0 T m A s _ P ψ t
  exact range_lvlOp_idemOf_eq_range_lvlPr_mul_V0E (A.fam.R t).S (A.fam.R t).r A.X P ψ

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeOpEqSpanOfFormsTie
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory

theorem range_op_eq_span_of_formsTie :
    ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {n k : ℕ} (σ : K →+* ℂ) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (j : (Fin n → K) →ₛₗ[σ] W) (H E : Matrix (Fin n) (Fin n) K) (op : W →ₗ[ℂ] W) (V : Matrix (Fin n) (Fin k) K), FormsTie σ j H E op → LinearMap.range E.mulVecLin = LinearMap.range V.mulVecLin → LinearMap.range op = Submodule.span ℂ (Set.range fun x => j (V.mulVec x)) := by
  intro K _ _ _ n k σ W _ _ j H E op V h hr
  apply le_antisymm
  · rw [← Submodule.map_top, ← h.span, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    have hm : E.mulVec (Pi.single i 1) ∈ LinearMap.range V.mulVecLin := by
      rw [← hr]
      exact ⟨Pi.single i 1, rfl⟩
    obtain ⟨y, hy⟩ := hm
    refine Submodule.subset_span ⟨y, ?_⟩
    have hy' : V.mulVec y = E.mulVec (Pi.single i 1) := hy
    show j (V.mulVec y) = op (j (Pi.single i 1))
    rw [h.op_eq, hy']
  · rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    have hm : V.mulVec y ∈ LinearMap.range E.mulVecLin := by
      rw [hr]
      exact ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := hm
    have hx' : E.mulVec x = V.mulVec y := hx
    refine ⟨j x, ?_⟩
    show op (j x) = j (V.mulVec y)
    rw [h.op_eq, hx']

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnOfOnWithCanonical
open NumberField IsDedekindDomain Formalism.L2.Indef Formalism.L2.Indef.Tree

namespace GlobalTheory.BigOn

theorem canonical_error_real {ι J : Type} [Fintype J] (T : Finset ι) (I F err err0 J0 : ι → J → ℝ)
    (e c l : ι → ℝ) (D E E' : ℝ) (hD : 0 < D) (he : ∀ w, 0 < e w) (hl : ∀ w, 0 ≤ l w) (hE : 2 * E ≤ E')
    (hJ : ∀ w ∈ T, ∀ j, 0 ≤ J0 w j)
    (h0 : ∀ w j, err0 w j =
      max 0 ((∑ j', I w j') / D - ∑ j', 2 * (e w * F w j') - c w) / (e w * (Fintype.card J : ℝ)))
    (h1 : ∀ w ∈ T, ∑ j, I w j ≤ (∑ j, (2 * (e w * F w j) + e w * err w j) + c w) * D)
    (h2 : ∀ w ∈ T, ∀ j, 0 ≤ err w j)
    (h3 : ∀ j, ∑ w ∈ T, l w * (e w * err w j + e w * J0 w j) ≤ E) :
    (∀ w ∈ T, ∑ j, I w j ≤ (∑ j, (2 * (e w * F w j) + e w * err0 w j) + c w) * D) ∧
    (∀ w ∈ T, ∀ j, 0 ≤ err0 w j) ∧
    ∀ j, ∑ w ∈ T, l w * (e w * err0 w j + e w * J0 w j) ≤ E' := by
  refine ⟨fun w hw => ?_, fun w _ j => ?_, fun j => ?_⟩
  · rcases isEmpty_or_nonempty J with hJe | hJn
    · simpa using h1 w hw
    · have hn : (0 : ℝ) < (Fintype.card J : ℝ) := by exact_mod_cast Fintype.card_pos
      have hew := he w
      have hs : ∑ j, e w * err0 w j =
          max 0 ((∑ j', I w j') / D - ∑ j', 2 * (e w * F w j') - c w) := by
        simp only [h0, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
      rw [Finset.sum_add_distrib, hs, ← div_le_iff₀ hD]
      have := le_max_right 0 ((∑ j', I w j') / D - ∑ j', 2 * (e w * F w j') - c w)
      linarith
  · rw [h0]
    exact div_nonneg (le_max_left _ _) (mul_nonneg (he w).le (Nat.cast_nonneg _))
  · have hn : (0 : ℝ) < (Fintype.card J : ℝ) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr ⟨j⟩)
    have hA : ∀ w ∈ T, (Fintype.card J : ℝ) * (l w * (e w * err0 w j)) ≤ ∑ j', l w * (e w * err w j') := by
      intro w hw
      have hew := he w
      have hs : (Fintype.card J : ℝ) * (l w * (e w * err0 w j)) =
          l w * max 0 ((∑ j', I w j') / D - ∑ j', 2 * (e w * F w j') - c w) := by
        rw [h0]; field_simp
      rw [hs, ← Finset.mul_sum _ _ (l w)]
      refine mul_le_mul_of_nonneg_left (max_le ?_ ?_) (hl w)
      · exact Finset.sum_nonneg fun j' _ => mul_nonneg hew.le (h2 w hw j')
      · have h := h1 w hw
        rw [Finset.sum_add_distrib, ← div_le_iff₀ hD] at h
        linarith
    have hB : ∀ j', ∑ w ∈ T, l w * (e w * err w j') ≤ E := fun j' =>
      le_trans (Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (mul_nonneg (he w).le (hJ w hw j'))) (hl w)) (h3 j')
    have hC : ∑ w ∈ T, l w * (e w * J0 w j) ≤ E :=
      le_trans (Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (mul_nonneg (he w).le (h2 w hw j))) (hl w)) (h3 j)
    have hF : (Fintype.card J : ℝ) * ∑ w ∈ T, l w * (e w * err0 w j) ≤ (Fintype.card J : ℝ) * E := by
      rw [Finset.mul_sum]
      refine le_trans (Finset.sum_le_sum hA) ?_
      rw [Finset.sum_comm]
      refine le_trans (Finset.sum_le_sum fun j' _ => hB j') ?_
      simp
    have hG := le_of_mul_le_mul_left hF hn
    simp only [mul_add, Finset.sum_add_distrib]
    linarith

theorem on_of_onWith_canonical :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (Z : IndefScale Bs) (C C' CH CH' : ℝ) (err : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ), 0 < S.D → 0 ≤ Z.E1u → 2 * C ≤ C' → (∀ w ∈ S.Tw, ∀ j, 0 ≤ Z.J0 (S.μ w) w j) → (∀ w j, S.err0 w j = max 0 ((∑ j', ((S.Iw j' (S.μ w) w : ℝ) + (S.Iw j' (S.μ w) (Formalism.DivisionValues.conjPl w) : ℝ))) / (S.D : ℝ) - ∑ j', 2 * ((Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * Z.F0 w j') - (Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * (2 / (Formalism.EigenvalueLevelCeiling.plc w : ℝ) ^ 2)) / ((Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * (Fintype.card Bs.J : ℝ))) → ONwith S (Z.num C CH) err → S.ON (Z.num C' CH') := by
  intro K _ _ _ Bs Df S Z C C' CH CH' err hD hE hC hJ h0 h
  rw [on_iff_with]
  obtain ⟨h1, h2, h3⟩ := h
  exact canonical_error_real S.Tw
    (fun w j => (S.Iw j (S.μ w) w : ℝ) + (S.Iw j (S.μ w) (Formalism.DivisionValues.conjPl w) : ℝ)) Z.F0 err S.err0
    (fun w j => Z.J0 (S.μ w) w j) (fun w => (Formalism.EigenvalueLevelCeiling.ramw w : ℝ))
    (fun w => (Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * (2 / (Formalism.EigenvalueLevelCeiling.plc w : ℝ) ^ 2)) (fun w => Formalism.DivisionValues.lw w) (S.D : ℝ)
    (C * Z.E1u) (C' * Z.E1u) (by exact_mod_cast hD) (fun w => ramw_pos w) (fun w => (lw_pos w).le)
    (by nlinarith [mul_le_mul_of_nonneg_right hC hE]) hJ h0 h1 h2 h3

end GlobalTheory.BigOn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupFormalChartEvNatMultipleEqConvPower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupFormalChartEvNatMultipleEqConvPower
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

open TensorProduct WithConv Coalgebra

namespace GlobalTheory.NMul

theorem isAdicComplete_ring_of_module {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    (p : ℕ) [h : IsAdicComplete (Ideal.span {(p : O)}) A] :
    IsAdicComplete (Ideal.span {(p : A)}) A := by
  have key : ∀ (n : ℕ) (x : A), x ∈ (Ideal.span {(p : A)} ^ n • ⊤ : Submodule A A) ↔
      x ∈ (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O A) := by
    intro n x
    rw [GlobalTheory.mem_span_singleton_pow_smul_top_iff_exists, GlobalTheory.mem_span_singleton_pow_smul_top_iff_exists]
    simp [Algebra.smul_def]
  exact
    { haus' := fun x hx => IsHausdorff.haus h.toIsHausdorff x fun n =>
        SModEq.sub_mem.2 ((key n _).1 (SModEq.sub_mem.1 (hx n)))
      prec' := fun f hf => by
        obtain ⟨L, hL⟩ := IsPrecomplete.prec h.toIsPrecomplete (f := f) fun {m n} hmn =>
          SModEq.sub_mem.2 ((key _ _).1 (SModEq.sub_mem.1 (hf hmn)))
        exact ⟨L, fun n => SModEq.sub_mem.2 ((key _ _).2 (SModEq.sub_mem.1 (hL n)))⟩ }

end GlobalTheory.NMul

namespace GlobalTheory.NMul

theorem ev_nmul : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (n k : ℕ) (i : Fin d),
      c.ev n (nmul c.μ k i) = PDiv.mulBy O (G.A n) k (c.x n i) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ G d c n k
  haveI : IsAdicComplete (Ideal.span {(p : O)}) (G.A n) :=
    GlobalTheory.isAdicComplete_of_finite_projective _ _
  haveI : IsAdicComplete (Ideal.span {(p : G.A n)}) (G.A n) := isAdicComplete_ring_of_module (O := O) p
  have hT := (GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p O (G.A n) (Fin d) (c.x n) (c.nil n)).2 (c.ev n) (c.isEval n)
  have hsucc : ∀ (k : ℕ) (j : Fin d), nmul c.μ (k + 1) j =
      subst (Sum.elim (nmul c.μ k) fun i => (X i : MvPowerSeries (Fin d) O)) (c.μ j) := by
    intro k j
    simp only [nmul, Function.iterate_succ_apply']
    rfl
  have hmul : ∀ (j : ℕ) (a : G.A n),
      PDiv.mulBy O (G.A n) j a = (toConv (AlgHom.id O (G.A n)) ^ j).ofConv a := fun j a =>
    DFunLike.congr_fun (PDiv.comp_mulBy_pts (AlgHom.id O (G.A n)) j) a
  induction k with
  | zero =>
    intro i
    have h0 : nmul c.μ 0 i = 0 := rfl
    rw [h0, map_zero, hmul]
    simp [c.aug n i]
  | succ k ih =>
    intro i
    have hu : ∀ s, constantCoeff
        (Sum.elim (nmul c.μ k) (fun i => (X i : MvPowerSeries (Fin d) O)) s) = 0 := by
      have hc : ∀ (k : ℕ) (j : Fin d), constantCoeff (nmul c.μ k j) = 0 := by
        intro k
        induction k with
        | zero => intro j; rfl
        | succ k ihk =>
          intro j
          rw [hsucc]
          refine constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ?_) ?_
            (c.isLaw.const j) <;>
          · rintro (l | l)
            · simpa using ihk l
            · simp
      rintro (l | l)
      · simpa using hc k l
      · simp
    let ψ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] G.A n :=
      (Algebra.TensorProduct.lift (PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n)
        (AlgHom.id O (G.A n)) fun _ _ => Commute.all _ _).comp (c.ev₂ n)
    have hψ : IsEval p (fun s => c.ev n
        (Sum.elim (nmul c.μ k) (fun i => (X i : MvPowerSeries (Fin d) O)) s)) ψ := by
      constructor
      · rintro (l | l)
        · simp only [ψ, AlgHom.comp_apply, (c.isEval₂ n).1 (Sum.inl l), Sum.elim_inl,
            Algebra.TensorProduct.lift_tmul, map_one, mul_one, ih]
          rfl
        · simp only [ψ, AlgHom.comp_apply, (c.isEval₂ n).1 (Sum.inr l), Sum.elim_inr,
            Algebra.TensorProduct.lift_tmul, map_one, one_mul, (c.isEval n).1 l]
          rfl
      · intro m
        obtain ⟨N, hN⟩ := (c.isEval₂ n).2 m
        refine ⟨N, fun f hf => ?_⟩
        obtain ⟨y, hy⟩ := hN f hf
        refine ⟨(Algebra.TensorProduct.lift (PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n)
          (AlgHom.id O (G.A n)) fun _ _ => Commute.all _ _) y, ?_⟩
        simp only [ψ, AlgHom.comp_apply, hy, map_mul, map_pow, map_natCast]
    rw [hsucc, hT.1 _ _ ψ hu hψ (c.μ i)]
    simp only [ψ, AlgHom.comp_apply, c.comul n i]
    rw [hmul (k + 1), pow_succ, AlgHom.convMul_apply]
    have e : (toConv (AlgHom.id O (G.A n)) ^ k).ofConv =
        (PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n) := by
      ext a; exact (hmul k a).symm
    simp only [e]

end GlobalTheory.NMul
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupFormalChartEvNatMultipleEqConvPowerStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct WithConv Coalgebra

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivGroupFormalChart_ev_natMultiple_eq_convPower :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
      (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
      [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
      ∀ (G : GlobalTheory.PDivGroup p O) (d : ℕ) (c : GlobalTheory.QLog.Chart G d)
        (n k : ℕ) (i : Fin d),
        c.ev n (nmul c.μ k i) = PDiv.mulBy (R := O) (A := G.A n) k (c.x n i) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ G d c n k
  have : IsAdicComplete (Ideal.span {(p : O)}) (G.A n) :=
    GlobalTheory.isAdicComplete_of_finite_projective _ _
  have : IsAdicComplete (Ideal.span {(p : G.A n)}) (G.A n) :=
    GlobalTheory.NMul.isAdicComplete_ring_of_module (O := O) p
  have heval := ((GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural
    p O (G.A n) (Fin d) (c.x n) (c.nil n)).2 (c.ev n) (c.isEval n)).1
  have hsucc (k : ℕ) (i : Fin d) : nmul c.μ (k + 1) i =
      subst (Sum.elim (nmul c.μ k) fun j => (X j : MvPowerSeries (Fin d) O)) (c.μ i) := by
    rw [nmul, Function.iterate_succ_apply']
    rfl
  have hconstant (k : ℕ) (i : Fin d) : constantCoeff (nmul c.μ k i) = 0 := by
    induction k generalizing i with
    | zero => rfl
    | succ k ih =>
      rw [hsucc]
      have hzero : ∀ j, constantCoeff
          (Sum.elim (nmul c.μ k) (fun i => (X i : MvPowerSeries (Fin d) O)) j) = 0 := by
        rintro (j | j)
        · exact ih j
        · exact constantCoeff_X j
      exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hzero) hzero
        (c.isLaw.const i)
  have hmul (k : ℕ) : (PDiv.mulBy (R := O) (A := G.A n) k : G.A n →ₐ[O] G.A n) =
      (toConv (AlgHom.id O (G.A n)) ^ k).ofConv :=
    PDiv.comp_mulBy_pts (AlgHom.id O (G.A n)) k
  induction k with
  | zero =>
    intro i
    have hzero : nmul c.μ 0 i = 0 := rfl
    change c.ev n (nmul c.μ 0 i) =
      (PDiv.mulBy (R := O) (A := G.A n) 0 : G.A n →ₐ[O] G.A n) (c.x n i)
    rw [hzero, map_zero, hmul]
    simp [c.aug n i]
  | succ k ih =>
    intro i
    let u := Sum.elim (nmul c.μ k) fun j => (X j : MvPowerSeries (Fin d) O)
    let lift : G.A n ⊗[O] G.A n →ₐ[O] G.A n :=
      Algebra.TensorProduct.lift (PDiv.mulBy (R := O) (A := G.A n) k : G.A n →ₐ[O] G.A n)
        (AlgHom.id O (G.A n)) fun _ _ => Commute.all _ _
    have hu : ∀ j, constantCoeff (u j) = 0 := by
      rintro (j | j)
      · exact hconstant k j
      · exact constantCoeff_X j
    have hlift : IsEval p (fun j => c.ev n (u j)) (lift.comp (c.ev₂ n)) := by
      constructor
      · rintro (j | j)
        · simp only [lift, u, AlgHom.comp_apply, (c.isEval₂ n).1 (Sum.inl j), Sum.elim_inl,
            Algebra.TensorProduct.lift_tmul, map_one, mul_one]
          exact (ih j).symm
        · simp only [lift, u, AlgHom.comp_apply, (c.isEval₂ n).1 (Sum.inr j), Sum.elim_inr,
            Algebra.TensorProduct.lift_tmul, map_one, one_mul, (c.isEval n).1 j]
          rfl
      · intro m
        obtain ⟨N, hN⟩ := (c.isEval₂ n).2 m
        refine ⟨N, fun f hf => ?_⟩
        simpa only [AlgHom.comp_apply, map_pow, map_natCast] using map_dvd lift (hN f hf)
    rw [hsucc, heval _ u _ hu hlift, AlgHom.comp_apply, c.comul n i]
    change lift (comul (R := O) (c.x n i)) =
      (PDiv.mulBy (R := O) (A := G.A n) (k + 1) : G.A n →ₐ[O] G.A n) (c.x n i)
    rw [hmul, pow_succ, AlgHom.convMul_apply]
    simp only [lift, hmul]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstSubIn
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstSubIn
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.KatzCongr

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

def coeffIdeal (τ : Type) (J : Ideal B) : Ideal (MvPowerSeries τ B) where
  carrier := {w | ∀ α, coeff α w ∈ J}
  add_mem' ha hb α := by rw [map_add (f := _)]; exact J.add_mem (ha α) (hb α)
  zero_mem' α := by rw [map_zero]; exact J.zero_mem
  smul_mem' c x hx α := by
    classical
    rw [smul_eq_mul, coeff_mul]
    exact J.sum_mem fun _ _ => J.mul_mem_left _ (hx _)

def scaledIdeal (τ : Type) (K : Ideal B) (c : Q) : Ideal (MvPowerSeries τ B) where
  carrier := {x | ∀ γ, ∃ b ∈ K, c * algebraMap B Q (coeff γ x) = algebraMap B Q b}
  add_mem' {x y} hx hy γ := by
    obtain ⟨a, ha, ea⟩ := hx γ
    obtain ⟨b, hb, eb⟩ := hy γ
    exact ⟨a + b, K.add_mem ha hb, by rw [map_add (f := _), map_add (f := _), mul_add, ea, eb, map_add (f := _)]⟩
  zero_mem' γ := ⟨0, K.zero_mem, by simp⟩
  smul_mem' r x hx γ := by
    classical
    set_option synthInstance.maxHeartbeats 100000 in
      rw [smul_eq_mul, coeff_mul, map_sum, Finset.mul_sum]
    have key : ∀ q ∈ Finset.HasAntidiagonal.antidiagonal γ, ∃ b ∈ K,
        c * algebraMap B Q (coeff q.1 r * coeff q.2 x) = algebraMap B Q b := by
      intro q _
      obtain ⟨b, hb, eb⟩ := hx q.2
      exact ⟨coeff q.1 r * b, K.mul_mem_left _ hb, by rw [map_mul, map_mul, ← eb]; ring⟩
    choose! g hg eg using key
    exact ⟨∑ q ∈ Finset.HasAntidiagonal.antidiagonal γ, g q, K.sum_mem hg, by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]; exact Finset.sum_congr rfl eg⟩

end GlobalTheory.KatzCongr

namespace GlobalTheory.KatzCongr

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {τ : Type} {J : Ideal B}

theorem pow_add_sub_pow
    (hdp : ∀ w ∈ coeffIdeal τ J, ∀ n : ℕ, 0 < n → ∃ y ∈ coeffIdeal τ J, w ^ n = (n.factorial : MvPowerSeries τ B) * y)
    (v w : MvPowerSeries τ B) (hw : w ∈ coeffIdeal τ J) (n : ℕ) :
    ∃ z ∈ coeffIdeal τ J, (v + w) ^ n - v ^ n = (n : MvPowerSeries τ B) * z := by
  cases n with
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | succ m =>
    choose! y hy ey using fun k (hk : 0 < k) => hdp w hw k hk
    refine ⟨∑ k ∈ Finset.range (m + 1), (m.descFactorial k : MvPowerSeries τ B) * y (k + 1) * v ^ (m - k),
      Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (hy _ (Nat.succ_pos k))), ?_⟩
    rw [add_comm v w, add_pow, Finset.sum_range_succ', Finset.mul_sum]
    simp only [pow_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul, add_sub_cancel_right]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h : (((k + 1).factorial * (m + 1).choose (k + 1) : ℕ) : MvPowerSeries τ B) =
        ((m + 1 : ℕ) : MvPowerSeries τ B) * (m.descFactorial k : ℕ) := by
      rw [← Nat.descFactorial_eq_factorial_mul_choose, Nat.succ_descFactorial_succ, Nat.cast_mul]
    rw [ey (k + 1) (Nat.succ_pos k), Nat.add_sub_add_right]
    push_cast at h ⊢
    linear_combination (y (k + 1) * v ^ (m - k)) * h

theorem prod_sub_mem {σ : Type} (K : Ideal B) (c : Q) (α : σ →₀ ℕ) (u v : σ → MvPowerSeries τ B)
    (hdp : ∀ w ∈ coeffIdeal τ J, ∀ n : ℕ, 0 < n → ∃ y ∈ coeffIdeal τ J, w ^ n = (n.factorial : MvPowerSeries τ B) * y)
    (huv : ∀ i, u i - v i ∈ coeffIdeal τ J)
    (hsc : ∀ i, ∀ z ∈ coeffIdeal τ J, (α i : MvPowerSeries τ B) * z ∈ scaledIdeal τ K c)
    (s : Finset σ) : ∏ i ∈ s, u i ^ α i - ∏ i ∈ s, v i ^ α i ∈ scaledIdeal τ K c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    obtain ⟨z, hz, ez⟩ := pow_add_sub_pow hdp (v a) (u a - v a) (huv a) (α a)
    rw [add_sub_cancel] at ez
    have e : u a ^ α a * ∏ i ∈ s, u i ^ α i - v a ^ α a * ∏ i ∈ s, v i ^ α i =
        u a ^ α a * (∏ i ∈ s, u i ^ α i - ∏ i ∈ s, v i ^ α i) +
          (u a ^ α a - v a ^ α a) * ∏ i ∈ s, v i ^ α i := by ring
    rw [e, ez]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ih) (Ideal.mul_mem_right _ _ (hsc a z hz))

end GlobalTheory.KatzCongr

namespace GlobalTheory.KatzCongr

theorem subst_sub_in : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ J : Ideal B, (∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) → ∀ (σ τ : Type) [Fintype σ] (N : Ideal B) (f : MvPowerSeries σ Q) (u v : σ → MvPowerSeries τ B), DIn N f → (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ i α, coeff α (u i - v i) ∈ J) →
    In (J * N) (MvPowerSeries.subst (σ := σ) (τ := τ) (R := Q) (S := Q) (up Q u) f -
      MvPowerSeries.subst (σ := σ) (τ := τ) (R := Q) (S := Q) (up Q v) f) := by
  intro p _ B O Q _ _ _ _ θ hF J hJ σ τ _ N f u v hf hu hv huv
  classical
  have hdp : ∀ w ∈ coeffIdeal τ J, ∀ n : ℕ, 0 < n →
      ∃ y ∈ coeffIdeal τ J, w ^ n = (n.factorial : MvPowerSeries τ B) * y := fun w hw n hn => by
    obtain ⟨y, hy, e⟩ := GlobalTheory.T.mvPowerSeries_coeffsInIdeal_pow_eq_factorial_mul p B O Q θ hF J hJ τ w hw n hn
    exact ⟨y, hy, e⟩
  have hsU : HasSubst (up Q u) := hasSubst_of_constantCoeff_zero fun i => by simp [up, hu i]
  have hsV : HasSubst (up Q v) := hasSubst_of_constantCoeff_zero fun i => by simp [up, hv i]
  intro γ
  rw [map_sub, coeff_subst hsU, coeff_subst hsV,
    ← finsum_sub_distrib (coeff_subst_finite hsU f γ) (coeff_subst_finite hsV f γ)]
  refine finsum_induction (fun q => ∃ b ∈ J * N, q = algebraMap B Q b) ⟨0, Submodule.zero_mem _, by simp⟩
    (fun x y ⟨a, ha, ea⟩ ⟨b, hb, eb⟩ => ⟨a + b, Submodule.add_mem _ ha hb, by rw [ea, eb, map_add (f := _)]⟩)
    (fun d => ?_)
  have hprod : ∀ w : σ → MvPowerSeries τ B,
      (d.prod fun s e => up Q w s ^ e) = map (algebraMap B Q) (∏ i, w i ^ d i) := by
    intro w
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), map_prod]
    simp [up, map_pow]
  have hsc : ∀ i, ∀ z ∈ coeffIdeal τ J,
      (d i : MvPowerSeries τ B) * z ∈ scaledIdeal τ (J * N) (coeff d f) := by
    intro i z hz γ'
    obtain ⟨b, hb, eb⟩ := hf d i
    refine ⟨coeff γ' z * b, Ideal.mul_mem_mul (hz γ') hb, ?_⟩
    rw [show ((d i : ℕ) : MvPowerSeries τ B) = C (d i : B) from (map_natCast C _).symm, coeff_C_mul,
      map_mul, map_mul, ← eb, map_natCast]
    ring
  have hmem := prod_sub_mem (J := J) (J * N) (coeff d f) d u v hdp (fun i α => huv i α) hsc Finset.univ
  obtain ⟨b, hb, eb⟩ := hmem γ
  refine ⟨b, hb, ?_⟩
  rw [hprod, hprod, smul_eq_mul, smul_eq_mul, ← mul_sub, ← map_sub (coeff γ), ← map_sub, coeff_map, ← eb]

end GlobalTheory.KatzCongr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstSubInStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subst_sub_subst_mem_mul_of_coeff_sub_mem : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ J : Ideal B, (∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) → ∀ (σ τ : Type) [Fintype σ] (N : Ideal B) (f : MvPowerSeries σ Q) (u v : σ → MvPowerSeries τ B), DIn N f → (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ i α, coeff α (u i - v i) ∈ J) → In (J * N) (subst (up Q u) f - subst (up Q v) f) := by
  first | exact @GlobalTheory.KatzCongr.subst_sub_in | exact GlobalTheory.KatzCongr.subst_sub_in | (intros; apply GlobalTheory.KatzCongr.subst_sub_in <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterAbsoluteValuePower
open NumberField IsDedekindDomain Formalism.L2.Host

noncomputable section

namespace GlobalTheory.HeckeNormPow

def toQC {K : Type} [Field K] [NumberField K] (χ : HChar K) : GroundTheory.Global.QuasiCharacter K where
  toMonoidHom := QuotientGroup.lift _ χ.1 (by
    rintro _ ⟨a, rfl⟩
    exact χ.2.2 a)
  continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 χ.2.1

theorem norm_val_eq_rpow : ∀ (K : Type) [Field K] [NumberField K] (χ : HChar K), ∃ s : ℝ,
    ∀ w : HeightOneSpectrum (𝓞 K), ‖((χ.val w : ℂˣ) : ℂ)‖ = (Ideal.absNorm w.asIdeal : ℝ) ^ s := by
  intro K _ _ χ
  obtain ⟨s, hs⟩ := GroundTheory.Global.QuasiCharacter.exists_norm_eq_rpow (toQC χ)
  refine ⟨-s, fun w => ?_⟩
  have h1 := hs
    (GroundTheory.Global.IdeleClassGroup.mk K (GroundTheory.Global.IdeleGroup.finiteEmbedding w (atFin w (unif w))))
  rw [GroundTheory.Global.IdeleClassGroup.ideleModule_mk,
    GroundTheory.Global.ideleModule_finiteEmbedding_of_uniformizer (unif_spec w)] at h1
  have h2 : ((χ.val w : ℂˣ) : ℂ) = (((toQC χ) (GroundTheory.Global.IdeleClassGroup.mk K
      (GroundTheory.Global.IdeleGroup.finiteEmbedding w (atFin w (unif w)))) : ℂˣ) : ℂ) := rfl
  rw [h2, h1, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity)]

end GlobalTheory.HeckeNormPow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationCoeffEqZeroOfDegreeLt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationCoeffEqZeroOfDegreeLt
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

namespace GlobalTheory

theorem invDer_coeff_eq_zero_of_degree_lt :
    ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
      (∀ i, constantCoeff (μ i) = 0) → ∀ (u : Fin d → R) (F : MvPowerSeries (Fin d) R) (r : ℕ),
      (∀ α : Fin d →₀ ℕ, α.degree < r + 1 → coeff α F = 0) →
      ∀ α : Fin d →₀ ℕ, α.degree < r → coeff α (invDer μ u F) = 0 := by
  intro R _ d μ hμ u F r hF α hα
  unfold invDer
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_smul]
  unfold atZero
  rw [(coeff_subst_restrict_sum (pderiv (R := R) (Sum.inr i) (subst μ F))).1 α, coeff_pderiv]
  have h := coeff_subst_eq_zero_of_degree_lt R (Fin d) (Fin d ⊕ Fin d) μ F (r + 1) hμ hF
    (α.mapDomain Sum.inl + Finsupp.single (Sum.inr i) 1) (by
      rw [map_add (f := _), Finsupp.degree_mapDomain, Finsupp.degree_single]; omega)
  rw [h, zero_mul, smul_zero]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationCoeffEqZeroOfDegreeLtStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantDerivation_coeff_eq_zero_of_degree_lt : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ (u : Fin d → R) (F : MvPowerSeries (Fin d) R) (r : ℕ), (∀ α : Fin d →₀ ℕ, α.degree < r + 1 → coeff α F = 0) → ∀ α : Fin d →₀ ℕ, α.degree < r → coeff α (invDer μ u F) = 0 := by
  first | exact @GlobalTheory.invDer_coeff_eq_zero_of_degree_lt | exact GlobalTheory.invDer_coeff_eq_zero_of_degree_lt | (intros; apply GlobalTheory.invDer_coeff_eq_zero_of_degree_lt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VactVmul
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFamGL

theorem vact_vmul (N : ℕ) (D α : GL (Fin 2) (ZMod N)) (e : Fin 2 → ZMod N) (γ : SL(2, ℤ)) :
    vact N (vmul e (α * D)) γ = vmul e (gact N D α γ * D) := by
  have h : gact N D α γ * D = α * D * redGL N γ := by
    simp only [gact]
    group
  rw [h]
  simp only [vact, vmul, Units.val_mul, Matrix.vecMul_vecMul]

theorem main : ∀ (N : ℕ) [NeZero N] (D : GL (Fin 2) (ZMod N)) (e : Fin 2 → ZMod N), IsFam (gact N D) 2 (fun α => wp N (vmul e (α * D))) ∧ IsFam (gact N D) 3 (fun α => wpd N (vmul e (α * D))) := by
  intro N _ D e
  obtain ⟨h2, h3⟩ := GlobalTheory.T.weierstrassP_torsion_isModularFamily N
  refine ⟨fun α γ => ?_, fun α γ => ?_⟩
  · have h := h2 (vmul e (α * D)) γ
    rw [vact_vmul] at h
    exact h
  · have h := h3 (vmul e (α * D)) γ
    rw [vact_vmul] at h
    exact h

end GlobalTheory.WpFamGL
end
