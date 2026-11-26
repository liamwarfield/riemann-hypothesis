module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrank

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralChernFormPolynomialEqIntersectionNumber
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormOfWeightIsFormDbarEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormOfWeightIsFormDbarEqZero
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ChernCalc.FirstChernW

open GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.LineForm.FirstChern

theorem smoothOn_atlas {F : Type} [Field F] {X : Var F} {σ : F →+* ℂ} {m : Type} {U : Set (CxPts X.str σ)}
    {G : CxPts X.str σ → Matrix m m ℂ} (H : ∀ y ∈ U, MInfAt G y) (i j : m) :
    (atlas X σ).SmoothOn U fun y => G y i j := fun c v hv => by
  have := (H _ hv.2 i j).contDiffAt_chart c (c.e.map_target hv.1)
  erw [c.e.right_inv hv.1] at this
  exact this.contDiffWithinAt

theorem c1W_isForm_and_dbar_eq_zero : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (L : LB X.X) (ψ : Weight X.str σ L),
    ψ.IsCInf → (atlas X σ).IsForm (fld (atlas X σ) (c1W ψ)) ∧ (atlas X σ).dbar (fld (atlas X σ) (c1W ψ)) = 0 := by
  intro F _ σ X L ψ hψ
  have hφ : ∀ a (x : (atlas X σ).Pt), x.pt ∈ ptsIn X.str σ (L.U a) →
      ContDiffAt ℝ 2 (fun v => ψ.φ a (x.ch.symm v)) x.crd := by
    intro a x hx
    exact ((vInfAt_iff_cInfAt.2 (hψ a _ hx)).contDiffAt_chart x.1.1 x.2).of_le (by norm_cast)
  obtain ⟨hfr, hP⟩ := GlobalTheory.T.chernForms_frame_independent_closed (atlas X σ) (ι := Unit) (fun a => ptsIn X.str σ (L.U a)) (fun _ => isOpen_ptsIn _)
    (fun y => ⟨_, mem_pick ψ.isLB y⟩) (fun a b y => Matrix.of fun _ _ => gv X.str σ L a b y)
    (fun a b _ _ c => (AlgChart.holo c _ _).mono fun _ hv => ⟨hv.1, mem_ptsIn_inf.2 ⟨hv.2.1, hv.2.2⟩⟩)
    (fun a y => Matrix.of fun _ _ => ((Real.exp (-ψ.φ a y) : ℝ) : ℂ))
    (fun a => smoothOn_atlas fun y hy _ _ => (vInfAt_iff_cInfAt.2 (hψ a y hy)).comp_contDiff
      (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp contDiff_neg)))
    (fun a y _ => by
      have : (Matrix.of fun _ _ : Unit => ((Real.exp (-ψ.φ a y) : ℝ) : ℂ)) =
          Matrix.diagonal fun _ => ((Real.exp (-ψ.φ a y) : ℝ) : ℂ) := by
        ext; simp
      rw [this, Matrix.posDef_diagonal_iff]
      exact fun _ => Complex.zero_lt_real.2 (Real.exp_pos _))
    (fun a b y hy => by
      ext
      have h0 : 0 < ‖gv X.str σ L a b y‖ ^ 2 := by have := gv_ne_zero hy.1 hy.2; positivity
      rw [ψ.trans a b y hy.1 hy.2, neg_sub, sub_eq_add_neg, Real.exp_add, Real.exp_log h0]
      simp only [chg, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply,
        Fintype.sum_unique, Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj', Complex.star_def]
      ring) 1
  obtain ⟨h1, -, h3⟩ := hP (fld _ (c1W ψ)) fun a x hx => by
    rw [hfr a _ x hx (mem_pick ψ.isLB x.pt)]
    exact congrArg Subtype.val (chernAt_exp_neg (hφ _ x (mem_pick _ _))).symm
  exact ⟨h1, h3⟩

end GlobalTheory.ChernCalc.FirstChernW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormOfWeightIsFormDbarEqZeroStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstChernFormOfWeight_isForm_dbar_eq_zero : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (L : LB X.X) (ψ : Weight X.str σ L), ψ.IsCInf → (atlas X σ).IsForm (fld (atlas X σ) (c1W ψ)) ∧ (atlas X σ).dbar (fld (atlas X σ) (c1W ψ)) = 0 := by
  first | exact @GlobalTheory.ChernCalc.FirstChernW.c1W_isForm_and_dbar_eq_zero | exact GlobalTheory.ChernCalc.FirstChernW.c1W_isForm_and_dbar_eq_zero | (intros; apply GlobalTheory.ChernCalc.FirstChernW.c1W_isForm_and_dbar_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothWeightIntegralCombination
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothWeightIntegralCombination
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc.CombW

variable {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F}

theorem firstChernFormOfWeight_eq_hessianForm_chart {L : LB X.X} (ψ : Weight X.str σ L) (hψ : ψ.IsCInf) (c : AlgChart X.str σ X.dim)
    {y : CxPts X.str σ} (hy : y ∈ c.e.source) :
    c1W ψ ⟨(c, y), hy⟩ = GlobalTheory.ChernTop.matForm X.dim (c.hess ψ (pick ψ.isLB y) y) := by
  have hd := hψ.contDiffAt c hy (mem_pick ψ.isLB y)
  change ofValues _ = kappa • ∑ a, GlobalTheory.ChernTop.rowForm a _
  simp only [ofValues, GlobalTheory.ChernTop.rowForm, Fintype.linearCombination_apply, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  exact congrArg (kappa * ·) (GlobalTheory.CurveDens.cHess_apply_eq_ddbar (contDiffAt_ofReal_comp hd) a b).symm

theorem firstChernFormOfWeight_tensor {A B : LB X.X} (ψ : Weight X.str σ A) (φ : Weight X.str σ B) (hψ : ψ.IsCInf) (hφ : φ.IsCInf) :
    c1W (ψ.tens φ) = c1W ψ + c1W φ := by
  funext x
  obtain ⟨⟨c, y⟩, hy⟩ := x
  have ha := mem_pick ψ.isLB y
  have hb := mem_pick φ.isLB y
  show c1W (ψ.tens φ) ⟨(c, y), hy⟩ = c1W ψ ⟨(c, y), hy⟩ + c1W φ ⟨(c, y), hy⟩
  rw [firstChernFormOfWeight_eq_hessianForm_chart _ (hψ.tens hφ) c hy, firstChernFormOfWeight_eq_hessianForm_chart _ hψ c hy, firstChernFormOfWeight_eq_hessianForm_chart _ hφ c hy,
    c.hess_eq (hψ.tens hφ) hy (i := (pick ψ.isLB y, pick φ.isLB y)) (mem_ptsIn_inf.2 ⟨ha, hb⟩) (mem_pick _ y),
    GlobalTheory.FlatMass.hess_tens hψ hφ hy ha hb, map_add]

theorem firstChernFormOfWeight_dual {B : LB X.X} (φ : Weight X.str σ B) (hφ : φ.IsCInf) :
    c1W φ.dual = -c1W φ := by
  funext x
  obtain ⟨⟨c, y⟩, hy⟩ := x
  have hb := mem_pick φ.isLB y
  show c1W φ.dual ⟨(c, y), hy⟩ = -c1W φ ⟨(c, y), hy⟩
  rw [firstChernFormOfWeight_eq_hessianForm_chart _ hφ.dual c hy, firstChernFormOfWeight_eq_hessianForm_chart _ hφ c hy,
    c.hess_eq hφ.dual hy (i := (pick φ.isLB y : B.ι)) hb (mem_pick _ y),
    GlobalTheory.FlatMass.hess_dual hφ hy hb, map_neg]

theorem firstChernFormOfWeight_trivial_zero : c1W (Weight.ofFun (p := X.str) (σ := σ) fun _ => 0) = 0 := by
  funext x
  obtain ⟨⟨c, y⟩, hy⟩ := x
  have h0 : (Weight.ofFun (p := X.str) (σ := σ) fun _ => (0:ℝ)).IsCInf := Weight.isCInf_ofFun (cInfAt_const 0)
  show c1W _ ⟨(c, y), hy⟩ = 0
  rw [firstChernFormOfWeight_eq_hessianForm_chart _ h0 c hy]
  have e : c.hess (Weight.ofFun (p := X.str) (σ := σ) fun _ => (0:ℝ)) (pick (Weight.ofFun (p := X.str) (σ := σ) fun _ => (0:ℝ)).isLB y) y = 0 :=
    GlobalTheory.FlatMass.cHess_zero _
  rw [e, map_zero]

def combSub (X : Var F) (σ : F →+* ℂ) : AddSubgroup (X.Dv × ((atlas X σ).Pt → Ev X.dim)) where
  carrier := {x | ∃ (L' : LB X.X) (r' : L'.ι → X.Fnˣ) (ψ' : Weight X.str σ L'),
    Presents x.1 L' r' ∧ ψ'.IsCInf ∧ c1W ψ' = x.2}
  zero_mem' := ⟨LB.triv X.X, fun _ => 1, Weight.ofFun fun _ => 0, presents_zero,
    Weight.isCInf_ofFun (cInfAt_const 0), firstChernFormOfWeight_trivial_zero⟩
  add_mem' := by
    rintro ⟨D, w⟩ ⟨E, u⟩ ⟨L, r, ψ, h1, h2, h3⟩ ⟨M, r', φ, h1', h2', h3'⟩
    exact ⟨_, _, ψ.tens φ, h1.tens h1', h2.tens h2', by rw [firstChernFormOfWeight_tensor _ _ h2 h2', h3, h3']; rfl⟩
  neg_mem' := by
    rintro ⟨D, w⟩ ⟨L, r, ψ, h1, h2, h3⟩
    have hdual : Presents (-D) (CechPic.dual L) (fun i => (r i)⁻¹) := by
      refine ⟨CechPic.isLB_dual h1.isLB, fun i j hij => ?_, fun i x hx => (h1.isEqn i x hx).neg⟩
      change (↑((r i)⁻¹) : X.Fn) =
        fnOf (L.U i ⊓ L.U j) hij ↑((L.g i j)⁻¹) * ↑((r j)⁻¹)
      rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_units_inv,
        h1.isRatSec i j hij, mul_inv]
    exact ⟨_, _, ψ.dual, hdual, h2.dual, by rw [firstChernFormOfWeight_dual _ h2, h3]; rfl⟩

end GlobalTheory.ChernCalc.CombW

open GlobalTheory.ChernCalc.CombW in
theorem GlobalTheory.ChernCalc.exists_comb_smoothWeight : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (κ : Type) [Fintype κ] (Δ : κ → X.Dv) (L : κ → LB X.X) (r : ∀ a, (L a).ι → X.Fnˣ) (ψ : ∀ a, Weight X.str σ (L a)), (∀ a, Presents (Δ a) (L a) (r a) ∧ (ψ a).IsCInf) → ∀ c : κ → ℤ, ∃ (L' : LB X.X) (r' : L'.ι → X.Fnˣ) (ψ' : Weight X.str σ L'), Presents (∑ a, c a • Δ a) L' r' ∧ ψ'.IsCInf ∧ c1W ψ' = ∑ a, (c a : ℂ) • c1W (ψ a) := by
  intro F _ σ X κ _ Δ L r ψ h c
  have hm : (∑ a, c a • ((Δ a, c1W (ψ a)) : X.Dv × ((atlas X σ).Pt → Ev X.dim))) ∈ combSub X σ :=
    AddSubgroup.sum_mem _ fun a _ => AddSubgroup.zsmul_mem _ (show ((Δ a, c1W (ψ a)) : X.Dv × ((atlas X σ).Pt → Ev X.dim)) ∈ combSub X σ from ⟨L a, r a, ψ a, (h a).1, (h a).2, rfl⟩) _
  obtain ⟨L', r', ψ', h1, h2, h3⟩ := hm
  refine ⟨L', r', ψ', ?_, h2, ?_⟩
  · simpa [Prod.fst_sum] using h1
  · rw [h3, Prod.snd_sum]
    simp only [Prod.smul_snd]
    exact Finset.sum_congr rfl fun a _ => (Int.cast_smul_eq_zsmul ℂ (c a) _).symm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothWeightIntegralCombinationStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smoothWeight_integral_combination : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (κ : Type) [Fintype κ] (Δ : κ → X.Dv) (L : κ → LB X.X) (r : ∀ a, (L a).ι → X.Fnˣ) (ψ : ∀ a, Weight X.str σ (L a)), (∀ a, Presents (Δ a) (L a) (r a) ∧ (ψ a).IsCInf) → ∀ c : κ → ℤ, ∃ (L' : LB X.X) (r' : L'.ι → X.Fnˣ) (ψ' : Weight X.str σ L'), Presents (∑ a, c a • Δ a) L' r' ∧ ψ'.IsCInf ∧ c1W ψ' = ∑ a, (c a : ℂ) • c1W (ψ a) := by
  first | exact @GlobalTheory.ChernCalc.exists_comb_smoothWeight | exact GlobalTheory.ChernCalc.exists_comb_smoothWeight | (intros; apply GlobalTheory.ChernCalc.exists_comb_smoothWeight <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartFirstChernFormOfWeightPowEqChernPart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartFirstChernFormOfWeightPowEqChernPart
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc.TopPow

open ReciprocityTheory.L2DbarEstimates (cHess)
open GlobalTheory.HermFrame (ddc kappa)
open GlobalTheory.GoodMetric (coordVec)

theorem ddc_coordVec (n : ℕ) (u : V n → ℝ) (v : V n) (hu : ContDiffAt ℝ 2 u v) (a b : Fin n) :
    ddc u v (coordVec a) (coordVec b) = kappa * cHess n (fun w => (u w : ℂ)) v a b := by
  rw [GlobalTheory.HermFrame.ddc, GlobalTheory.leviForm, GlobalTheory.ddbar_eq_del_dbar (contDiffAt_ofReal_comp hu)]
  congr 1
  have hg : (fun x => GlobalTheory.dbar (fun w => (u w : ℂ)) x (coordVec b)) =
      ReciprocityTheory.L2DbarEstimates.wdb n b (fun w => (u w : ℂ)) := by
    funext x
    simp only [GlobalTheory.dbar, GlobalTheory.antilinPart, ReciprocityTheory.L2DbarEstimates.wdb, ReciprocityTheory.L2DbarEstimates.bas,
      ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
    ring
  rw [hg]
  simp only [GlobalTheory.del, GlobalTheory.linPart, cHess, Matrix.of_apply, ReciprocityTheory.L2DbarEstimates.wd, ReciprocityTheory.L2DbarEstimates.bas,
    ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
  ring

theorem dens_ofValues_ddc_pow (n : ℕ) (u : V n → ℝ) (v : V n) (hu : ContDiffAt ℝ 2 u v) :
    (dens ((ofValues (ddc u v) ^ n : Ev n) : Alt n)).re =
      n.factorial / Real.pi ^ n * (cHess n (fun w => (u w : ℂ)) v).det.re := by
  have e : ofValues (ddc u v) = ∑ a, ∑ b, (kappa • cHess n (fun w => (u w : ℂ)) v) a b • sym (a, b) := by
    simp only [ofValues, ddc_coordVec n u v hu, Matrix.smul_apply, smul_eq_mul]
  rw [e, GlobalTheory.CxForm.DensPow.dens_pow, Matrix.det_smul, Fintype.card_fin]
  have hk : kappa = Complex.I / 2 * ((Real.pi : ℂ)⁻¹) := by
    rw [GlobalTheory.HermFrame.kappa]; field_simp
  have h2 : (Complex.I / 2) ^ n ≠ 0 := pow_ne_zero _ (by simp)
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [hk, show ∀ d : ℂ, (n.factorial : ℂ) * ((Complex.I / 2 * ((Real.pi : ℂ))⁻¹) ^ n * d) / (Complex.I / 2) ^ n =
      (((n.factorial / Real.pi ^ n : ℝ)) : ℂ) * d from fun d => by
    rw [mul_pow]; field_simp; push_cast; ring, Complex.re_ofReal_mul]

variable {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {L : LB X.X}

theorem dens_loc_c1W_pow (ψ : Weight X.str σ L) (hψ : ψ.IsCInf) (c : AlgChart X.str σ X.dim)
    (y : CxPts X.str σ) (hy : y ∈ c.e.source) :
    (dens ((atlas X σ).loc (fld (atlas X σ) (c1W ψ ^ X.dim)) c (c.e y))).re = c.chernDens ψ y := by
  have e := (atlas X σ).loc_crd (fld (atlas X σ) (c1W ψ ^ X.dim)) (⟨(c, y), hy⟩ : (atlas X σ).Pt)
  erw [e]
  have hs := hψ.contDiffAt c hy (mem_pick ψ.isLB y)
  erw [fld, Pi.pow_apply, c1W, dens_ofValues_ddc_pow X.dim _ _ hs]
  rfl

theorem part_c1W_pow : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (L : LB X.X) (ψ : Weight X.str σ L),
    ψ.IsCInf → ∀ ε : ℤˣ, (atlas X σ).part (fld (atlas X σ) (c1W ψ ^ X.dim)) ε = ψ.chernPart X.dim ε := by
  intro F _ σ X L ψ hψ ε
  unfold HolAtlas.part Weight.chernPart ChartGlue.glueMeas
  refine iSup_congr fun c => ?_
  unfold ChartGlue.chartMeas
  congr 1
  refine withDensity_congr_ae (ae_restrict_of_forall_mem c.e.open_target.measurableSet fun v hv => ?_)
  have hy := c.e.map_target hv
  simp only [Function.comp_apply]
  erw [dens_loc_c1W_pow ψ hψ c _ hy]

end GlobalTheory.ChernCalc.TopPow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartFirstChernFormOfWeightPowEqChernPartStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.part_firstChernFormOfWeight_pow_eq_chernPart : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (L : LB X.X) (ψ : Weight X.str σ L), ψ.IsCInf → ∀ ε : ℤˣ, (atlas X σ).part (fld (atlas X σ) (c1W ψ ^ X.dim)) ε = ψ.chernPart X.dim ε := by
  first | exact @GlobalTheory.ChernCalc.TopPow.part_c1W_pow | exact GlobalTheory.ChernCalc.TopPow.part_c1W_pow | (intros; apply GlobalTheory.ChernCalc.TopPow.part_c1W_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralChernFormPolynomialEqIntersectionNumber
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem integral_evalF_c1W_eq_interPoly : GlobalTheory.Published.ChernDegree → ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (κ : Type) [Fintype κ] (Δ : κ → X.Dv) (L : κ → LB X.X) (r : ∀ a, (L a).ι → X.Fnˣ) (ψ : ∀ a, Weight X.str σ (L a)), (∀ a, Presents (Δ a) (L a) (r a) ∧ (ψ a).IsCInf) → ∀ P : MvPolynomial κ ℝ, P.IsHomogeneous X.dim → (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) P) = X.interPoly Δ P := by
  intro hCD F _ σ X κ _ Δ L r ψ hψ P hP
  haveI := CxPts.compactSpace σ X.isProjOver
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ X.isProjOver
  haveI := CxPts.secondCountableTopology_of_isProjOver σ X.isProjOver
  have hform : ∀ G : MvPolynomial κ ℝ, (atlas X σ).IsForm (evalF (atlas X σ) (fun a => c1W (ψ a)) G) :=
    fun G => ((GlobalTheory.formCalculus _ _ (atlas X σ)).2.2.2.1 κ _ G
      (fun a => (GlobalTheory.T.firstChernFormOfWeight_isForm_dbar_eq_zero F σ X (L a) (ψ a) (hψ a).2).1)).1
  have Pw := GlobalTheory.LineForm.wInt_props (CxPts X.str σ) X.dim (atlas X σ)
  have hint : ∀ G : MvPolynomial κ ℝ, ∀ ε : ℤˣ,
      Integrable (fun _ => (1 : ℝ)) ((atlas X σ).part (evalF (atlas X σ) (fun a => c1W (ψ a)) G) ε) :=
    fun G ε => by
      haveI := Pw.1 _ (hform G) ε
      exact integrable_const _
  have eval_add (G₁ G₂ : MvPolynomial κ ℝ) :
      evalF (atlas X σ) (fun a => c1W (ψ a)) (G₁ + G₂) =
        evalF (atlas X σ) (fun a => c1W (ψ a)) G₁ + evalF (atlas X σ) (fun a => c1W (ψ a)) G₂ := by
    funext x
    simp [evalF, fld]
  have eval_smul (t : ℝ) (G : MvPolynomial κ ℝ) :
      evalF (atlas X σ) (fun a => c1W (ψ a)) (t • G) =
        (t : ℂ) • evalF (atlas X σ) (fun a => c1W (ψ a)) G := by
    funext x
    simp [evalF, fld, MvPolynomial.smul_eq_C_mul, Algebra.smul_def]
  have hadd : ∀ G₁ G₂ : MvPolynomial κ ℝ,
      (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) (G₁ + G₂)) =
        (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) G₁) +
          (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) G₂) := fun G₁ G₂ => by
    rw [← wInt_one, ← wInt_one, ← wInt_one, eval_add]
    exact (Pw.2.1 _ _ _ (hform G₁) (hform G₂) (hint G₁) (hint G₂)).2
  have hsmul : ∀ (t : ℝ) (G : MvPolynomial κ ℝ),
      (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) (t • G)) =
        t * (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) G) := fun t G => by
    rw [← wInt_one, ← wInt_one, eval_smul]
    exact Pw.2.2.1 _ t _ (hform G)
  have hspan : P ∈ Submodule.span ℝ (Set.range fun n : κ → ℤ => GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ X.dim) := by
    classical
    by_contra hnot
    obtain ⟨φ, hφF, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
    have hkill : ∀ n : κ → ℤ, φ (GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ X.dim) = 0 := by
      intro n
      have hm : GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ X.dim ∈ Submodule.span ℝ
          (Set.range fun n : κ → ℤ => GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ X.dim) := Submodule.subset_span ⟨n, rfl⟩
      have h2 := Submodule.mem_map_of_mem (f := φ) hm
      rw [hφ] at h2
      exact (Submodule.mem_bot ℝ).mp h2
    have hQ : GlobalTheory.PowLinSpan.polOf φ X.dim = 0 := by
      refine eq_zero_of_eval_zero_at_prod_finset _
        (fun _ => (Finset.range (X.dim + 1)).image (fun k : ℕ => (k : ℝ))) ?_ ?_
      · intro x
        rw [Finset.card_image_of_injective _ Nat.cast_injective]
        simpa using Nat.lt_succ_of_le (GlobalTheory.PowLinSpan.degreeOf_polOf_le φ X.dim x)
      · intro v hv
        have hv' : ∀ i, ∃ k : ℕ, (k : ℝ) = v i := by
          intro i
          obtain ⟨k, -, hk⟩ := Finset.mem_image.mp (hv i)
          exact ⟨k, hk⟩
        choose k hk using hv'
        rw [GlobalTheory.PowLinSpan.eval_polOf]
        have he : (∑ x, C (v x) * MvPolynomial.X x : MvPolynomial κ ℝ) = GlobalTheory.ArInt.lin (fun i => (((k i : ℤ)) : ℝ)) := by
          simp only [GlobalTheory.ArInt.lin, Int.cast_natCast, hk]
        rw [he]
        exact hkill (fun i => (k i : ℤ))
    exact hφF (GlobalTheory.PowLinSpan.homog_kill φ X.dim hQ P hP)
  clear hP
  induction hspan using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    obtain ⟨L', r', ψ', hpr, hci, hc1⟩ := GlobalTheory.T.exists_smoothWeight_integral_combination F σ X κ Δ L r ψ hψ n
    have e1 : evalF (atlas X σ) (fun a => c1W (ψ a)) (GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ X.dim) =
        fld (atlas X σ) (c1W ψ' ^ X.dim) := by
      funext x
      rw [hc1]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [evalF, fld, GlobalTheory.ArInt.lin, map_pow, map_sum, map_mul, MvPolynomial.map_C,
        MvPolynomial.map_X, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Finset.sum_apply, Pi.smul_apply, Pi.pow_apply]
      congr 2
    have e2 : X.interPoly Δ (GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ X.dim) = (X.inter fun _ => ∑ a, n a • Δ a : ℝ) := by
      have := Var.interPoly_prod_sum X Δ (fun _ a => n a)
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
      exact this
    rw [e1, e2, HolAtlas.integral, GlobalTheory.T.part_firstChernFormOfWeight_pow_eq_chernPart F σ X L' ψ' hci, GlobalTheory.T.part_firstChernFormOfWeight_pow_eq_chernPart F σ X L' ψ' hci,
      ← (hCD F X σ _ L' r' hpr ψ' hci).2]
    simp only [Weight.chernInt, Measure.restrict_univ, integral_const, smul_eq_mul, mul_one]
  | zero =>
    rw [map_zero]
    have := hsmul 0 0
    rw [zero_smul, zero_mul] at this
    exact this
  | add x y _ _ hx hy =>
    rw [map_add (f := _), hadd, hx, hy]
  | smul t x _ hx =>
    rw [map_smul, hsmul, hx, smul_eq_mul]

end GlobalTheory.ChernCalc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralChernFormPolynomialEqIntersectionNumberStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_chernForm_polynomial_eq_intersectionNumber : GlobalTheory.Published.ChernDegree → ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (κ : Type) [Fintype κ] (Δ : κ → X.Dv) (L : κ → LB X.X) (r : ∀ a, (L a).ι → X.Fnˣ) (ψ : ∀ a, Weight X.str σ (L a)), (∀ a, Presents (Δ a) (L a) (r a) ∧ (ψ a).IsCInf) → ∀ P : MvPolynomial κ ℝ, P.IsHomogeneous X.dim → (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) P) = X.interPoly Δ P := by
  first | exact @GlobalTheory.ChernCalc.integral_evalF_c1W_eq_interPoly | exact GlobalTheory.ChernCalc.integral_evalF_c1W_eq_interPoly | (intros; apply GlobalTheory.ChernCalc.integral_evalF_c1W_eq_interPoly <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDensityHermitianFormsEqZeroOffDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDensityHermitianFormsEqZeroOffDegree
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
namespace GlobalTheory.ChernCalc

noncomputable def linPoly {n : ℕ} (α : V n → V n → ℂ) : MvPolynomial (Fin n × Fin n) ℂ :=
  ∑ a, ∑ b, C (α (coordVec a) (coordVec b)) * X (a, b)

theorem linPoly_isHomogeneous {n : ℕ} (α : V n → V n → ℂ) : (linPoly α).IsHomogeneous 1 := by
  unfold linPoly
  refine IsHomogeneous.sum _ _ _ fun a _ => IsHomogeneous.sum _ _ _ fun b _ => ?_
  simpa using (isHomogeneous_C (Fin n × Fin n) (α (coordVec a) (coordVec b))).mul (isHomogeneous_X ℂ (a, b))

theorem aeval_sym_linPoly {n : ℕ} (α : V n → V n → ℂ) : aeval sym (linPoly α) = ofValues α := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [linPoly, ofValues, map_sum, Algebra.smul_def]

theorem degree_permMono {n : ℕ} (w : Equiv.Perm (Fin n)) :
    Finsupp.degree (∑ a, Finsupp.single (a, w a) 1 : Fin n × Fin n →₀ ℕ) = n := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]; simp [Finsupp.degree_single]

theorem topCoeff_eq_zero_of_isHomogeneous {n d : ℕ} {Q : MvPolynomial (Fin n × Fin n) ℂ} (hQ : Q.IsHomogeneous d)
    (hd : d ≠ n) : topCoeff Q = 0 := by
  unfold topCoeff
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [hQ.coeff_eq_zero (by rw [degree_permMono]; exact fun h => hd h.symm), mul_zero]

theorem dens_aeval_ofValues_offDeg : ∀ (n : ℕ) (κ : Type) (α : κ → V n → V n → ℂ) (d : ℕ) (P : MvPolynomial κ ℝ),
    P.IsHomogeneous d → d ≠ n →
      dens ((aeval (fun i => ofValues (α i)) (P.map (algebraMap ℝ ℂ)) : Ev n) : Alt n) = 0 := by
  intro n κ α d P hP hd
  have h1 : (aeval (fun i => ofValues (α i)) (P.map (algebraMap ℝ ℂ)) : Ev n) =
      aeval sym (bind₁ (fun i => linPoly (α i)) (P.map (algebraMap ℝ ℂ))) := by
    rw [aeval_bind₁]; simp only [aeval_sym_linPoly]
  have hQ : (bind₁ (fun i => linPoly (α i)) (P.map (algebraMap ℝ ℂ))).IsHomogeneous d := by
    simpa using (hP.map (algebraMap ℝ ℂ)).aeval (fun i => linPoly (α i)) fun i => linPoly_isHomogeneous (α i)
  rw [h1, GlobalTheory.T.topDegreeDensityComplexForm_aeval_dzWedgeDzbar, topCoeff_eq_zero_of_isHomogeneous hQ hd, zero_div]

end GlobalTheory.ChernCalc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDensityHermitianFormsEqZeroOffDegreeStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDensity_hermitianForms_eq_zero_offDegree : ∀ (n : ℕ) (κ : Type) (α : κ → V n → V n → ℂ) (d : ℕ) (P : MvPolynomial κ ℝ), P.IsHomogeneous d → d ≠ n → dens ((aeval (fun i => ofValues (α i)) (P.map (algebraMap ℝ ℂ)) : Ev n) : Alt n) = 0 := by
  first | exact @GlobalTheory.ChernCalc.dens_aeval_ofValues_offDeg | exact GlobalTheory.ChernCalc.dens_aeval_ofValues_offDeg | (intros; apply GlobalTheory.ChernCalc.dens_aeval_ofValues_offDeg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralChernFormPolyEqIntersectionNumber
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChernLine

theorem eq_homogeneousComponent {κ R : Type} [AddCommGroup R] (f : MvPolynomial κ ℝ →+ R) (D : ℕ)
    (hf : ∀ d, d ≠ D → ∀ Q : MvPolynomial κ ℝ, Q.IsHomogeneous d → f Q = 0) (P : MvPolynomial κ ℝ) :
    f P = f (homogeneousComponent D P) := by
  conv_lhs => rw [← sum_homogeneousComponent P]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single D]
  · intro b _ hb
    exact hf b hb _ (homogeneousComponent_isHomogeneous b P)
  · intro hD
    rw [Finset.mem_range, not_lt] at hD
    rw [homogeneousComponent_eq_zero _ _ (by omega), map_zero]

theorem interPoly_eq_zero {F : Type} [Field F] (Y : Var F) {κ : Type} (Δ : κ → Y.Dv) (d : ℕ) (hd : d ≠ Y.dim)
    (Q : MvPolynomial κ ℝ) (hQ : Q.IsHomogeneous d) : Y.interPoly Δ Q = 0 := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Q.as_sum, map_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hm' : m.degree = d := by
    have := hQ (mem_support_iff.mp hm)
    first
    | (rw [Finsupp.degree_eq_weight_one]; exact this)
    | exact this
  rw [show monomial m (AddMonoidAlgebra.coeff Q m) = AddMonoidAlgebra.coeff Q m • basisMonomials κ ℝ m by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]]
  rw [map_smul, Var.interPoly, Module.Basis.constr_basis, dite_eq_right, smul_zero]
  rintro ⟨s, hs⟩
  apply hd
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hm', ← hs, map_sum]
  simp

theorem integral_evalF_c1W_eq_interPoly : GlobalTheory.Published.ChernDegree → ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (κ : Type) [Fintype κ] (Δ : κ → X.Dv) (L : κ → LB X.X) (r : ∀ a, (L a).ι → X.Fnˣ) (ψ : ∀ a, Weight X.str σ (L a)), (∀ a, Presents (Δ a) (L a) (r a) ∧ (ψ a).IsCInf) → ∀ P : MvPolynomial κ ℝ, (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) P) = X.interPoly Δ P := by
  intro hC F _ σ X κ _ Δ L r ψ hψ P
  have hR : X.interPoly Δ P = X.interPoly Δ (homogeneousComponent X.dim P) :=
    eq_homogeneousComponent (X.interPoly Δ).toAddMonoidHom X.dim (fun d hd Q hQ => interPoly_eq_zero X Δ d hd Q hQ) P
  have hL : ∀ x, dens (evalF (atlas X σ) (fun a => c1W (ψ a)) P x) =
      dens (evalF (atlas X σ) (fun a => c1W (ψ a)) (homogeneousComponent X.dim P) x) := by
    intro x
    let f : MvPolynomial κ ℝ →+ ℂ :=
      { toFun := fun Q => dens (evalF (atlas X σ) (fun a => c1W (ψ a)) Q x)
        map_zero' := by simp [evalF, LineForm.fld, dens]
        map_add' := fun Q Q' => by
          simp only [evalF, LineForm.fld, map_add (f := _), Subalgebra.coe_add]
          exact LineForm.TopInt.dens_add _ _ }
    refine eq_homogeneousComponent f X.dim (fun d hd Q hQ => ?_) P
    exact GlobalTheory.T.topDensity_hermitianForms_eq_zero_offDegree X.dim κ _ d Q hQ hd
  rw [hR, ← GlobalTheory.T.integral_chernForm_polynomial_eq_intersectionNumber hC F σ X κ Δ L r ψ hψ _ (homogeneousComponent_isHomogeneous _ P)]
  simp only [HolAtlas.integral, LineForm.TopInt.part_congr _ hL]

end GlobalTheory.ChernLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralChernFormPolyEqIntersectionNumberStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_chernFormPoly_eq_intersectionNumber : GlobalTheory.Published.ChernDegree → ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (κ : Type) [Fintype κ] (Δ : κ → X.Dv) (L : κ → LB X.X) (r : ∀ a, (L a).ι → X.Fnˣ) (ψ : ∀ a, Weight X.str σ (L a)), (∀ a, Presents (Δ a) (L a) (r a) ∧ (ψ a).IsCInf) → ∀ P : MvPolynomial κ ℝ, (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) P) = X.interPoly Δ P := by
  first | exact @GlobalTheory.ChernLine.integral_evalF_c1W_eq_interPoly | exact GlobalTheory.ChernLine.integral_evalF_c1W_eq_interPoly | (intros; apply GlobalTheory.ChernLine.integral_evalF_c1W_eq_interPoly <;> assumption)
end
