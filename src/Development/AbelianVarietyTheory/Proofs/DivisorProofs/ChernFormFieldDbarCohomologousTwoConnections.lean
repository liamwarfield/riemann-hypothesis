module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMapOfAddFormalGroupLawEvalPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFamilyLinearIndependentProductDegeneration

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerSumTransgressionSmoothDbarClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerSumTransgressionSmoothDbarClosed
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChernCalc

theorem powAt_coe_eq_sum {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (x : V n) (k : ℕ) :
    ((powAt G x k : Ev n) : Alt n) = ∑ i, (((curvEv G x ^ k * curvEv G' x ^ 0) i i : Ev n) : Alt n) := by
  simp [powAt, Matrix.trace]

theorem transAt_eq_sum {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (x : V n) (k : ℕ) :
    transAt G G' x k = ∑ a, ∑ i ∈ Finset.range k, ∑ p, ∑ q,
      (conn G x (coordVec a) - conn G' x (coordVec a)) p q •
        ((((curvEv G' x ^ (k - 1 - i) * curvEv G x ^ i) q p : Ev n) : Alt n) * dz a) := by
  unfold transAt
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, AddSubmonoidClass.coe_finsetSum,
    Finset.sum_mul, Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Algebra.smul_def, mul_assoc]

theorem powAt_transAt_smooth : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → MContDiffAt ∞ G' v → IsUnit (G' v).det → ∀ k, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((powAt G x k : Alt n)) S) v) ∧ dbarAt (fun x => (powAt G x k : Alt n)) v = 0 ∧ (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (transAt G G' x k) S) v) := by
  intro n r _ _ G G' v hG hGu hG' hG'u k
  obtain ⟨hconst, hsum, hsmul, hmul⟩ := GlobalTheory.T.smooth_coefficient_forms_closed_under_operations n v
  obtain ⟨_, hdsum, _, _, _⟩ := GlobalTheory.T.dbar_operator_local_calculus_complex_forms n v
  have hpe : ∀ i, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr
      (((curvEv G x ^ k * curvEv G' x ^ 0) i i : Ev n) : Alt n) S) v) ∧
      dbarAt (fun x => (((curvEv G x ^ k * curvEv G' x ^ 0) i i : Ev n) : Alt n)) v = 0 :=
    fun i => GlobalTheory.T.curvatureMatrix_powProduct_entry_smooth_dbarClosed n r G G' v hG hGu hG' hG'u k 0 i i
  have hpf : (fun x => ((powAt G x k : Ev n) : Alt n)) =
      fun x => ∑ i ∈ Finset.univ, (((curvEv G x ^ k * curvEv G' x ^ 0) i i : Ev n) : Alt n) :=
    funext fun x => powAt_coe_eq_sum G G' x k
  refine ⟨?_, ?_, ?_⟩
  · simp only [powAt_coe_eq_sum G G']
    exact hsum r Finset.univ _ fun i _ => (hpe i).1
  · rw [hpf, hdsum r Finset.univ _ fun i _ S => ((hpe i).1 S).differentiableAt (by simp)]
    exact Finset.sum_eq_zero fun i _ => (hpe i).2
  · have hη : ∀ a p q, ContDiffAt ℝ ∞
        (fun x => (conn G x (coordVec a) - conn G' x (coordVec a)) p q) v := fun a p q =>
      ((hG.conn hGu (j := ∞) (by simp) (coordVec a)).sub
        (hG'.conn hG'u (j := ∞) (by simp) (coordVec a))) p q
    simp only [transAt_eq_sum]
    refine hsum _ Finset.univ _ fun a _ => hsum _ _ _ fun i _ => hsum _ Finset.univ _ fun p _ =>
      hsum _ Finset.univ _ fun q _ => hsmul _ _ (hη a p q) ?_
    exact hmul _ _ (GlobalTheory.T.curvatureMatrix_powProduct_entry_smooth_dbarClosed n r G' G v hG' hG'u hG hGu (k - 1 - i) i q p).1 (hconst (dz a))

end GlobalTheory.ChernCalc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerSumTransgressionSmoothDbarClosedStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curvature_power_sum_transgression_smooth_dbar_closed : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → MContDiffAt ∞ G' v → IsUnit (G' v).det → ∀ k, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((powAt G x k : Alt n)) S) v) ∧ dbarAt (fun x => (powAt G x k : Alt n)) v = 0 ∧ (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (transAt G G' x k) S) v) := by
  first | exact @GlobalTheory.ChernCalc.powAt_transAt_smooth | exact GlobalTheory.ChernCalc.powAt_transAt_smooth | (intros; apply GlobalTheory.ChernCalc.powAt_transAt_smooth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramConnectionPairChernFieldsLocalFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramConnectionPairChernFieldsLocalFrame
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem loc_fields_near : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (r : Type) [Fintype r] [DecidableEq r] (G G' : M → M → Matrix r r ℂ), IsGramPair A G G' → ∀ (x : A.Pt) (k : ℕ), ∀ᶠ v in 𝓝 x.crd, A.loc (fld A (powFld A G k)) x.1.1 v = powAt (fun u => G x.pt (x.ch.symm u)) v k ∧ A.loc (fld A (chernFld A G k)) x.1.1 v = chernAt (fun u => G x.pt (x.ch.symm u)) v k ∧ A.loc (transFld A G G' k) x.1.1 v = transAt (fun u => G x.pt (x.ch.symm u)) (fun u => G' x.pt (x.ch.symm u)) v k := by
  intro M _ n A r _ _ G G' hG x k
  obtain ⟨⟨i, y⟩, hy⟩ := x
  have hyt : A.e i y ∈ (A.e i).target := (A.e i).map_source hy
  have hsymm : (A.e i).symm (A.e i y) = y := (A.e i).left_inv hy
  have hcont : Tendsto (A.e i).symm (𝓝 (A.e i y)) (𝓝 y) := by
    have := (A.e i).continuousAt_symm hyt
    rwa [ContinuousAt, hsymm] at this
  obtain ⟨⟨hGu, hGs⟩, ⟨hG'u, hG's⟩⟩ := hG.smooth y
  have e1 := hGs i hy
  have e2 := hG's i hy
  have u1 := e1.self_of_nhds.eventually_isUnit (by simpa only [hsymm] using hGu)
  have u2 := e2.self_of_nhds.eventually_isUnit (by simpa only [hsymm] using hG'u)
  filter_upwards [(A.e i).open_target.mem_nhds hyt, hcont.eventually (hG.trans y), e1, e2, u1, u2]
    with v hv htr h1 h2 h3 h4
  obtain ⟨T, K, K', hT, hK, hK', hw⟩ := htr
  have hz : (A.e i).symm v ∈ (A.e i).source := (A.e i).map_target hv
  have hzv : A.e i ((A.e i).symm v) = v := (A.e i).right_inv hv
  have hct : Tendsto (A.e i).symm (𝓝 v) (𝓝 ((A.e i).symm v)) := (A.e i).continuousAt_symm hv
  have dT := hT.2 i hz
  have dK := hK.2 i hz
  have dK' := hK'.2 i hz
  rw [hzv] at dT dK dK'
  have key := GlobalTheory.T.chernTransgression_forms_frame_invariant n r (fun u => G y ((A.e i).symm u)) (fun u => G' y ((A.e i).symm u))
    (fun u => G ((A.e i).symm v) ((A.e i).symm u)) (fun u => G' ((A.e i).symm v) ((A.e i).symm u))
    (fun u => T ((A.e i).symm u)) (fun u => K ((A.e i).symm u)) (fun u => K' ((A.e i).symm u)) v
    h1 h3 h2 h4 dT hT.1 dK hK.1 dK' hK'.1 (hct.eventually hw) k
  refine ⟨?_, ?_, ?_⟩
  · rw [HolAtlas.loc, dite_eq_left hv]
    show ((powAt (fun u => G ((A.e i).symm v) ((A.e i).symm u)) (A.e i ((A.e i).symm v)) k : Ev n) : Alt n) = _
    rw [hzv, key.1]
  · rw [HolAtlas.loc, dite_eq_left hv]
    show ((chernAt (fun u => G ((A.e i).symm v) ((A.e i).symm u)) (A.e i ((A.e i).symm v)) k : Ev n) : Alt n) = _
    rw [hzv, key.2.1]
  · rw [HolAtlas.loc, dite_eq_left hv]
    show transAt (fun u => G ((A.e i).symm v) ((A.e i).symm u)) (fun u => G' ((A.e i).symm v) ((A.e i).symm u))
      (A.e i ((A.e i).symm v)) k = _
    rw [hzv, key.2.2]

end GlobalTheory.ChernCalc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramConnectionPairChernFieldsLocalFrameStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramConnectionPair_chernFields_local_frame : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (r : Type) [Fintype r] [DecidableEq r] (G G' : M → M → Matrix r r ℂ), IsGramPair A G G' → ∀ (x : A.Pt) (k : ℕ), ∀ᶠ v in 𝓝 x.crd, A.loc (fld A (powFld A G k)) x.1.1 v = powAt (fun u => G x.pt (x.ch.symm u)) v k ∧ A.loc (fld A (chernFld A G k)) x.1.1 v = chernAt (fun u => G x.pt (x.ch.symm u)) v k ∧ A.loc (transFld A G G' k) x.1.1 v = transAt (fun u => G x.pt (x.ch.symm u)) (fun u => G' x.pt (x.ch.symm u)) v k := by
  first | exact @GlobalTheory.ChernCalc.loc_fields_near | exact GlobalTheory.ChernCalc.loc_fields_near | (intros; apply GlobalTheory.ChernCalc.loc_fields_near <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerSumsDbarCohomologous
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerSumTransgressionIsForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTransgressionFormHolomorphicPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTransgressionFormHolomorphicPullback
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

noncomputable section
namespace GlobalTheory.ChernCalc

theorem eq_sum_ofLp_smul_complexCoordinateVector {n : ℕ} (w : V n) : w = ∑ a, w a • coordVec a := by
  ext i
  simp [coordVec, Pi.single_apply]

theorem trace_mul_constMatrix_mul_evenForms_sum {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (P Q : Matrix r r (Ev n)) (C : Matrix r r ℂ) :
    (((P * C.map (algebraMap ℂ (Ev n)) * Q).trace : Ev n) : Alt n) = ∑ p, ∑ q, C p q • (((Q * P) q p : Ev n) : Alt n) := by
  rw [Matrix.trace_mul_cycle, Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply (M := Q * P), Matrix.map_apply, AddSubmonoidClass.coe_finsetSum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [mul_comm, ← Algebra.smul_def, Subalgebra.coe_smul]

def connectionMatrixDifferenceLinearMap {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (v : V n) :
    V n →ₗ[ℂ] Matrix r r ℂ where
  toFun ξ := conn G v ξ - conn G' v ξ
  map_add' ξ ξ' := by rw [conn_add_vec, conn_add_vec]; abel
  map_smul' c ξ := by rw [conn_smul_vec, conn_smul_vec, smul_sub]; rfl

theorem transAt_comp_holo : ∀ (n n' : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (φ : V n' → V n) (w : V n'), ContDiffAt ℂ 2 φ w → MContDiffAt ∞ G (φ w) → IsUnit (G (φ w)).det → MContDiffAt ∞ G' (φ w) → IsUnit (G' (φ w)).det → ∀ k, transAt (fun x => G (φ x)) (fun x => G' (φ x)) w k = pull (fderiv ℂ φ w) (transAt G G' (φ w) k) := by
  intro n n' r _ _ G G' φ w hφ hG hGu hG' hG'u k
  have hI := (GlobalTheory.T.curvature_power_pullback_holomorphic n n' r G' φ w hφ hG' hG'u).1
  have hφ1 : DifferentiableAt ℂ φ w := hφ.differentiableAt two_ne_zero
  have h1 : MContDiffAt 1 G (φ w) := hG.of_le (by exact_mod_cast le_top)
  have h1' : MContDiffAt 1 G' (φ w) := hG'.of_le (by exact_mod_cast le_top)
  have hc : ∀ ξ, conn (fun x => G (φ x)) w ξ - conn (fun x => G' (φ x)) w ξ =
      ∑ b, fderiv ℂ φ w ξ b • connectionMatrixDifferenceLinearMap G G' (φ w) (coordVec b) := by
    intro ξ
    rw [conn_comp_holo h1 hφ1, conn_comp_holo h1' hφ1]
    show connectionMatrixDifferenceLinearMap G G' (φ w) (fderiv ℂ φ w ξ) = _
    conv_lhs => rw [eq_sum_ofLp_smul_complexCoordinateVector (fderiv ℂ φ w ξ)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul]
  have hd : ∀ b, conn G (φ w) (coordVec b) - conn G' (φ w) (coordVec b) = connectionMatrixDifferenceLinearMap G G' (φ w) (coordVec b) :=
    fun _ => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [transAt, hc, hd, map_sum, map_mul, (pull_dz _ _).1, trace_mul_constMatrix_mul_evenForms_sum, AlgHom.map_smul_of_tower]
  simp only [hI _ _ _ _ G hG hGu, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_smul, Finset.sum_mul,
    Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul, Finset.smul_sum]
  conv_lhs => enter [2, a, 2, i, 2, p]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a, 2, i]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => enter [2, b]; rw [Finset.sum_comm]

end GlobalTheory.ChernCalc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTransgressionFormHolomorphicPullbackStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernTransgressionForm_holomorphic_pullback : ∀ (n n' : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (φ : V n' → V n) (w : V n'), ContDiffAt ℂ 2 φ w → MContDiffAt ∞ G (φ w) → IsUnit (G (φ w)).det → MContDiffAt ∞ G' (φ w) → IsUnit (G' (φ w)).det → ∀ k, transAt (fun x => G (φ x)) (fun x => G' (φ x)) w k = pull (fderiv ℂ φ w) (transAt G G' (φ w) k) := by
  first | exact @GlobalTheory.ChernCalc.transAt_comp_holo | exact GlobalTheory.ChernCalc.transAt_comp_holo | (intros; apply GlobalTheory.ChernCalc.transAt_comp_holo <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerSumTransgressionIsForm
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc.PairForm

section Point

variable {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]

theorem powAt_congr {G G₁ : V n → Matrix r r ℂ} {v : V n} (h : G =ᶠ[𝓝 v] G₁) (k : ℕ) :
    powAt G v k = powAt G₁ v k := by
  simp only [powAt, curvEv, curvPoly, curv_congr h]

theorem transAt_congr {G G₁ G' G₁' : V n → Matrix r r ℂ} {v : V n} (h : G =ᶠ[𝓝 v] G₁)
    (h' : G' =ᶠ[𝓝 v] G₁') (k : ℕ) : transAt G G' v k = transAt G₁ G₁' v k := by
  simp only [transAt, curvEv, curvPoly, curv_congr h, curv_congr h', conn_congr h, conn_congr h']

end Point

section Manifold

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {r : Type} [Fintype r] [DecidableEq r]

theorem contDiffAt_change (x x' : A.Pt) (h : x.pt = x'.pt) : ContDiffAt ℂ 2 (x'.ch ∘ x.ch.symm) x.crd := by
  have hs : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) :=
    x.ch.isOpen_inter_preimage_symm x'.ch.open_source
  have hm : x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source := by
    refine ⟨x.ch.map_source x.2, ?_⟩
    show x.ch.symm ((x.ch) x.pt) ∈ x'.ch.source
    rw [x.ch.left_inv x.2]
    exact (congrArg (fun y => y ∈ x'.ch.source) h).mpr x'.2
  exact GlobalTheory.SCV.contDiffAt_of_differentiableOn (A.holo x.1.1 x'.1.1) (hs.mem_nhds hm) 2

theorem change_crd (x x' : A.Pt) (h : x.pt = x'.pt) : (x'.ch ∘ x.ch.symm) x.crd = x'.crd := by
  show (x'.ch) (x.ch.symm ((x.ch) x.pt)) = (x'.ch) x'.pt
  rw [x.ch.left_inv x.2]
  exact congrArg x'.ch h

theorem germ_change (G : M → M → Matrix r r ℂ) (x x' : A.Pt) (h : x.pt = x'.pt) :
    (fun u => G x.pt (x.ch.symm u)) =ᶠ[𝓝 x.crd] fun u => G x'.pt (x'.ch.symm ((x'.ch ∘ x.ch.symm) u)) := by
  have hc : ContinuousAt x.ch.symm x.crd := x.ch.continuousAt_symm (x.ch.map_source x.2)
  have hmem : x'.ch.source ∈ 𝓝 (x.ch.symm x.crd) := by
    show x'.ch.source ∈ 𝓝 (x.ch.symm ((x.ch) x.pt))
    rw [x.ch.left_inv x.2]
    exact (congrArg (fun y => x'.ch.source ∈ 𝓝 y) h).mpr (x'.ch.open_source.mem_nhds x'.2)
  filter_upwards [hc hmem] with u hu
  show G x.pt (x.ch.symm u) = G x'.pt (x'.ch.symm ((x'.ch) (x.ch.symm u)))
  rw [x'.ch.left_inv hu]
  exact congrArg (fun y => G y (x.ch.symm u)) h

theorem smooth_crd (G : M → M → Matrix r r ℂ) (hG : ∀ y, SmoothUnitAt A (G y) y) (x : A.Pt) :
    MContDiffAt ∞ (fun u => G x.pt (x.ch.symm u)) x.crd ∧ IsUnit (G x.pt (x.ch.symm x.crd)).det := by
  refine ⟨((hG x.pt).2 x.1.1 x.2).self_of_nhds, ?_⟩
  show IsUnit (G x.pt (x.ch.symm ((x.ch) x.pt))).det
  rw [x.ch.left_inv x.2]
  exact (hG x.pt).1

theorem smooth_change (G : M → M → Matrix r r ℂ) (hG : ∀ y, SmoothUnitAt A (G y) y) (x x' : A.Pt) (h : x.pt = x'.pt) :
    MContDiffAt ∞ (fun u => G x'.pt (x'.ch.symm u)) ((x'.ch ∘ x.ch.symm) x.crd) ∧
      IsUnit (G x'.pt (x'.ch.symm ((x'.ch ∘ x.ch.symm) x.crd))).det := by
  rw [change_crd A x x' h]
  exact smooth_crd A G hG x'

end Manifold

theorem isForm_pow_trans : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (r : Type) [Fintype r]
    [DecidableEq r] (G G' : M → M → Matrix r r ℂ), IsGramPair A G G' →
      ∀ k, A.IsForm (fld A (powFld A G k)) ∧ A.IsForm (transFld A G G' k) := by
  intro M _ n A r _ _ G G' hG k
  have sG : ∀ y, SmoothUnitAt A (G y) y := fun y => (hG.smooth y).1
  have sG' : ∀ y, SmoothUnitAt A (G' y) y := fun y => (hG.smooth y).2
  have near := GlobalTheory.T.gramConnectionPair_chernFields_local_frame M n A r G G' hG
  constructor
  · refine ⟨fun i S => ?_, fun x x' h => ?_⟩
    · intro v hv
      let x : A.Pt := ⟨(i, (A.e i).symm v), (A.e i).map_target hv⟩
      have hx : x.crd = v := (A.e i).right_inv hv
      obtain ⟨h1, h2⟩ := smooth_crd A G sG x
      have hs := (GlobalTheory.T.curvature_power_sum_transgression_smooth_dbar_closed n r _ _ x.crd h1 h2 h1 h2 k).1 S
      have key : ContDiffAt ℝ ∞ (fun v => (bas n).repr (A.loc (fld A (powFld A G k)) i v) S) x.crd :=
        hs.congr_of_eventuallyEq ((near x k).mono fun u hu => congrArg (fun a => (bas n).repr a S) hu.1)
      rw [hx] at key
      exact key.contDiffWithinAt
    · obtain ⟨h1, h2⟩ := smooth_change A G sG x x' h
      have hc := ((GlobalTheory.T.curvature_power_pullback_holomorphic n n r _ (x'.ch ∘ x.ch.symm) x.crd (contDiffAt_change A x x' h) h1 h2).2 k).1
      show (powAt (fun v => G x.pt (x.ch.symm v)) x.crd k : Alt n) =
        pull (fderiv ℂ (x'.ch ∘ x.ch.symm) x.crd) (powAt (fun v => G x'.pt (x'.ch.symm v)) x'.crd k : Alt n)
      rw [powAt_congr (germ_change A G x x' h), hc, change_crd A x x' h]
  · refine ⟨fun i S => ?_, fun x x' h => ?_⟩
    · intro v hv
      let x : A.Pt := ⟨(i, (A.e i).symm v), (A.e i).map_target hv⟩
      have hx : x.crd = v := (A.e i).right_inv hv
      obtain ⟨h1, h2⟩ := smooth_crd A G sG x
      obtain ⟨h1', h2'⟩ := smooth_crd A G' sG' x
      have hs := (GlobalTheory.T.curvature_power_sum_transgression_smooth_dbar_closed n r _ _ x.crd h1 h2 h1' h2' k).2.2 S
      have key : ContDiffAt ℝ ∞ (fun v => (bas n).repr (A.loc (transFld A G G' k) i v) S) x.crd :=
        hs.congr_of_eventuallyEq ((near x k).mono fun u hu => congrArg (fun a => (bas n).repr a S) hu.2.2)
      rw [hx] at key
      exact key.contDiffWithinAt
    · obtain ⟨h1, h2⟩ := smooth_change A G sG x x' h
      obtain ⟨h1', h2'⟩ := smooth_change A G' sG' x x' h
      have hc := GlobalTheory.T.chernTransgressionForm_holomorphic_pullback n n r _ _ (x'.ch ∘ x.ch.symm) x.crd (contDiffAt_change A x x' h) h1 h2 h1' h2' k
      show transAt (fun v => G x.pt (x.ch.symm v)) (fun v => G' x.pt (x.ch.symm v)) x.crd k =
        pull (fderiv ℂ (x'.ch ∘ x.ch.symm) x.crd)
          (transAt (fun v => G x'.pt (x'.ch.symm v)) (fun v => G' x'.pt (x'.ch.symm v)) x'.crd k)
      rw [transAt_congr (germ_change A G x x' h) (germ_change A G' x x' h), hc, change_crd A x x' h]

end GlobalTheory.ChernCalc.PairForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerSumTransgressionIsFormStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curvaturePowerSum_transgression_isForm : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (r : Type) [Fintype r] [DecidableEq r] (G G' : M → M → Matrix r r ℂ), IsGramPair A G G' → ∀ k, A.IsForm (fld A (powFld A G k)) ∧ A.IsForm (transFld A G G' k) := by
  first | exact @GlobalTheory.ChernCalc.PairForm.isForm_pow_trans | exact GlobalTheory.ChernCalc.PairForm.isForm_pow_trans | (intros; apply GlobalTheory.ChernCalc.PairForm.isForm_pow_trans <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarChernTransgressionFormEqPowerSumDiff
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarChernConnectionEntryEqCurvature
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarChernConnectionEntryEqCurvature
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc

theorem coefwise_dbar_sum_smul_bas {n : ℕ} {J : Type} [Fintype J] (u : J → V n → ℂ) (S : J → Finset (Fin (n + n)))
    (v η : V n) (hu : ∀ a, DifferentiableAt ℝ (u a) v) :
    coefwise (fun f => GlobalTheory.dbar f v η) (fun x => ∑ a, u a x • bas n (S a)) =
      ∑ a, GlobalTheory.dbar (u a) v η • bas n (S a) := by
  refine (bas n).ext_elem fun S' => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coefwise, map_sum, map_smul, Module.Basis.repr_self, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hd (a : J) : DifferentiableAt ℝ (fun x => if S a = S' then u a x else 0) v := by
    split_ifs
    exacts [hu a, differentiableAt_const _]
  rw [GlobalTheory.dbar_sum fun a _ => hd a, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> simp

theorem dbarAt_conn : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → ∀ i j, dbarAt (fun x => ∑ a, conn G x (coordVec a) i j • dz a) v = (curvEv G v i j : Alt n) := by
  intro n r _ _ G v hG hu i j
  have hc (a : Fin n) : DifferentiableAt ℝ (fun x => conn G x (coordVec a) i j) v :=
    (hG.conn hu (j := 1) (by norm_cast) (coordVec a)).diff i j
  have h (b : Fin n) := coefwise_dbar_sum_smul_bas (fun a x => conn G x (coordVec a) i j)
    (fun a => {finSumFinEquiv (.inl a)}) v (coordVec b) hc
  simp only [bas_singleton] at h
  have e : (curvEv G v i j : Alt n) = ∑ a, ∑ b, curv G v (coordVec a) (coordVec b) i j • (dz a * dzb b) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [curvEv, curvPoly, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul, aeval_C, aeval_X,
      ← Algebra.smul_def, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul, sym]
  rw [e, Finset.sum_comm]
  simp only [dbarAt, dz, h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [mul_smul_comm, dzb]
  conv_lhs =>
    rw [eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap
      (R := ℂ) (M := Fin n ⊕ Fin n → ℂ) (Pi.single (Sum.inr b) 1) (Pi.single (Sum.inl a) 1)),
      smul_neg, ← neg_smul]
  rfl

end GlobalTheory.ChernCalc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarChernConnectionEntryEqCurvatureStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_chernConnection_entry_eq_curvature : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → ∀ i j, dbarAt (fun x => ∑ a, conn G x (coordVec a) i j • dz a) v = (curvEv G v i j : Alt n) := by
  first | exact @GlobalTheory.ChernCalc.dbarAt_conn | exact GlobalTheory.ChernCalc.dbarAt_conn | (intros; apply GlobalTheory.ChernCalc.dbarAt_conn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTracePowMulSubMulPowTelescopeStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTracePowMulSubMulPowTelescope
namespace GlobalTheory.ChernCalc

theorem sum_trace_pow_mul_sub_mul_pow (R : Type) [CommRing R] (r : Type) [Fintype r]
    [DecidableEq r] (P Q : Matrix r r R) (k : ℕ) :
    ∑ i ∈ Finset.range k, (P ^ i * (P - Q) * Q ^ (k - 1 - i)).trace
      = (P ^ k).trace - (Q ^ k).trace := by
  have h : ∀ i ∈ Finset.range k, (P ^ i * (P - Q) * Q ^ (k - 1 - i)).trace
      = (P ^ (i + 1) * Q ^ (k - (i + 1))).trace - (P ^ i * Q ^ (k - i)).trace := by
    intro i hi
    have hi' : i < k := Finset.mem_range.mp hi
    have e1 : k - 1 - i = k - (i + 1) := by omega
    have e2 : k - i = (k - (i + 1)) + 1 := by omega
    rw [e1, e2, ← Matrix.trace_sub, mul_sub, sub_mul, ← pow_succ, pow_succ' Q, mul_assoc]
  rw [Finset.sum_congr rfl h,
    Finset.sum_range_sub (fun i => (P ^ i * Q ^ (k - i)).trace)]
  simp

end GlobalTheory.ChernCalc
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_trace_pow_mul_sub_mul_pow_telescope : ∀ (R : Type) [CommRing R] (r : Type) [Fintype r] [DecidableEq r] (P Q : Matrix r r R) (k : ℕ), ∑ i ∈ Finset.range k, (P ^ i * (P - Q) * Q ^ (k - 1 - i)).trace = (P ^ k).trace - (Q ^ k).trace := by
  first | exact @GlobalTheory.ChernCalc.sum_trace_pow_mul_sub_mul_pow | exact GlobalTheory.ChernCalc.sum_trace_pow_mul_sub_mul_pow | (intros; apply GlobalTheory.ChernCalc.sum_trace_pow_mul_sub_mul_pow <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarChernTransgressionFormEqPowerSumDiff
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc

theorem trace_mul_mul_eq_sum_entries {R : Type} [CommRing R] {r : Type} [Fintype r] (P M Q : Matrix r r R) :
    (P * M * Q).trace = ∑ p, ∑ q, (Q * P) q p * M p q := by
  rw [Matrix.trace_mul_cycle, Matrix.trace, Finset.sum_comm (f := fun p q => (Q * P) q p * M p q)]
  exact Finset.sum_congr rfl fun q _ => Matrix.mul_apply

theorem dbarAt_transAt (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (v : V n)
    (hG : MContDiffAt ∞ G v) (hGu : IsUnit (G v).det) (hG' : MContDiffAt ∞ G' v)
    (hG'u : IsUnit (G' v).det) (k : ℕ) :
    dbarAt (fun x => transAt G G' x k) v = (powAt G v k : Alt n) - powAt G' v k := by
  obtain ⟨_, hsum, hsmul, _, hleib⟩ := GlobalTheory.T.dbar_operator_local_calculus_complex_forms n v
  obtain ⟨sconst, ssum, ssmul, smul⟩ := GlobalTheory.T.smooth_coefficient_forms_closed_under_operations n v
  have hinf : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := le_of_eq (by simp)
  have hdiff : ∀ α : V n → Alt n, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x) S) v) →
      ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (α x) S) v :=
    fun α h S => (h S).differentiableAt (by simp)
  obtain ⟨W, hW⟩ : ∃ W : ℕ → V n → Matrix r r (Ev n),
      W = fun i x => curvEv G' x ^ (k - 1 - i) * curvEv G x ^ i := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : r → r → V n → Alt n, β = fun p q x =>
      (∑ a, conn G x (coordVec a) p q • dz a) - ∑ a, conn G' x (coordVec a) p q • dz a := ⟨_, rfl⟩

  have hWs : ∀ i p q, ∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((W i x q p : Ev n) : Alt n) S) v := by
    intro i p q; subst hW; exact (GlobalTheory.T.curvatureMatrix_powProduct_entry_smooth_dbarClosed n r G' G v hG' hG'u hG hGu (k - 1 - i) i q p).1
  have hWc : ∀ i p q, dbarAt (fun x => ((W i x q p : Ev n) : Alt n)) v = 0 := by
    intro i p q; subst hW; exact (GlobalTheory.T.curvatureMatrix_powProduct_entry_smooth_dbarClosed n r G' G v hG' hG'u hG hGu (k - 1 - i) i q p).2

  have hcs : ∀ (H : V n → Matrix r r ℂ), MContDiffAt ∞ H v → IsUnit (H v).det → ∀ p q,
      ∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (∑ a, conn H x (coordVec a) p q • dz a) S) v := by
    intro H hH hHu p q
    exact ssum (Fin n) Finset.univ (fun a x => conn H x (coordVec a) p q • dz a) fun a _ =>
      ssmul (fun x => conn H x (coordVec a) p q) (fun _ => dz a)
        (hH.conn hHu hinf (coordVec a) p q) (sconst (dz a))
  have hβs : ∀ p q, ∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (β p q x) S) v := by
    intro p q S; subst hβ
    simpa only [map_sub, Finsupp.sub_apply] using (hcs G hG hGu p q S).sub (hcs G' hG' hG'u p q S)
  have dsub : ∀ α γ : V n → Alt n, (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (α x) S) v) →
      (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (γ x) S) v) →
      dbarAt (fun x => α x - γ x) v = dbarAt α v - dbarAt γ v := by
    intro α γ hα hγ
    have e : (fun x => α x - γ x) =
        fun x => ∑ j ∈ (Finset.univ : Finset (Fin 2)), (![α, fun y => (-1 : ℂ) • γ y] j) x := by
      funext x; simp [Fin.sum_univ_two, sub_eq_add_neg]
    rw [e, hsum (Fin 2) Finset.univ _ ?_]
    · rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hsmul (-1) γ hγ]
      simp [sub_eq_add_neg]
    · intro j _ S
      fin_cases j
      · exact hα S
      · simpa [map_smul] using (hγ S).const_smul (-1 : ℂ)
  have hdβ : ∀ p q, dbarAt (β p q) v = (curvEv G v p q : Alt n) - curvEv G' v p q := by
    intro p q; subst hβ
    refine (dsub _ _ (hdiff _ (hcs G hG hGu p q)) (hdiff _ (hcs G' hG' hG'u p q))).trans ?_
    rw [GlobalTheory.T.dbar_chernConnection_entry_eq_curvature n r G v hG hGu p q, GlobalTheory.T.dbar_chernConnection_entry_eq_curvature n r G' v hG' hG'u p q]
  have step : ∀ i p q, dbarAt (fun x => ((W i x q p : Ev n) : Alt n) * β p q x) v =
      (W i v q p : Alt n) * ((curvEv G v p q : Alt n) - curvEv G' v p q) := by
    intro i p q
    rw [hleib (fun x => W i x q p) (β p q) (hdiff _ (hWs i p q)) (hdiff _ (hβs p q)), hWc, zero_mul,
      zero_add, hdβ]

  have key : (fun x => transAt G G' x k) =
      fun x => ∑ i ∈ Finset.range k, ∑ p, ∑ q, ((W i x q p : Ev n) : Alt n) * β p q x := by
    funext x
    subst hW hβ
    simp only [transAt]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [trace_mul_mul_eq_sum_entries, Matrix.map_apply, Matrix.sub_apply, map_sub,
      AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Finset.sum_mul,
      Finset.mul_sum, ← Finset.sum_sub_distrib, mul_sub, sub_mul, Subalgebra.coe_sub]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun a _ => ?_
    simp only [Algebra.smul_def, mul_assoc, mul_sub, sub_mul]

  have alg : ∑ i ∈ Finset.range k, ∑ p, ∑ q, W i v q p * (curvEv G v p q - curvEv G' v p q) =
      powAt G v k - powAt G' v k := by
    refine Eq.trans ?_ (GlobalTheory.T.sum_trace_pow_mul_sub_mul_pow_telescope (Ev n) r (curvEv G v) (curvEv G' v) k)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.trace_mul_cycle, Matrix.trace, Finset.sum_comm, hW]
    exact Finset.sum_congr rfl fun q _ => by rw [Matrix.diag_apply, Matrix.mul_apply]; rfl
  rw [key]
  refine (hsum _ _ _ ?_).trans ?_
  · intro i _
    exact hdiff _ (ssum r Finset.univ _ fun p _ => ssum r Finset.univ _ fun q _ =>
      smul _ _ (hWs i p q) (hβs p q))
  have inner : ∀ i, dbarAt (fun x => ∑ p, ∑ q, ((W i x q p : Ev n) : Alt n) * β p q x) v =
      ∑ p, ∑ q, (W i v q p : Alt n) * ((curvEv G v p q : Alt n) - curvEv G' v p q) := by
    intro i
    refine (hsum _ _ _ ?_).trans (Finset.sum_congr rfl fun p _ => ?_)
    · intro p _
      exact hdiff _ (ssum r Finset.univ _ fun q _ => smul _ _ (hWs i p q) (hβs p q))
    refine (hsum _ _ _ ?_).trans (Finset.sum_congr rfl fun q _ => step i p q)
    intro q _
    exact hdiff _ (smul _ _ (hWs i p q) (hβs p q))
  rw [Finset.sum_congr rfl fun i _ => inner i]
  have := congrArg (fun w : Ev n => (w : Alt n)) alg
  simpa only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul, Subalgebra.coe_sub] using this

end GlobalTheory.ChernCalc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarChernTransgressionFormEqPowerSumDiffStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_chernTransgressionForm_eq_power_sum_diff : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → MContDiffAt ∞ G' v → IsUnit (G' v).det → ∀ k, dbarAt (fun x => transAt G G' x k) v = (powAt G v k : Alt n) - powAt G' v k := by
  first | exact @GlobalTheory.ChernCalc.dbarAt_transAt | exact GlobalTheory.ChernCalc.dbarAt_transAt | (intros; apply GlobalTheory.ChernCalc.dbarAt_transAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerSumsDbarCohomologous
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc.PowCoh

variable {M : Type} [TopologicalSpace M] {n : ℕ} {A : HolAtlas M n} {r : Type} [Fintype r] [DecidableEq r]
  {G G' : M → M → Matrix r r ℂ}

theorem pair_symm (h : IsGramPair A G G') : IsGramPair A G' G :=
  ⟨fun y => (h.smooth y).symm, fun y => (h.trans y).mono fun _ ⟨T, K, K', hT, hK, hK', e⟩ =>
    ⟨T, K', K, hT, hK', hK, e.mono fun _ hw => hw.symm⟩⟩

theorem smooth_crd (h : IsGramPair A G G') (x : A.Pt) :
    MContDiffAt ∞ (fun u => G x.pt (x.ch.symm u)) x.crd ∧ IsUnit (G x.pt (x.ch.symm x.crd)).det := by
  refine ⟨((h.smooth x.pt).1.2 x.1.1 x.2).self_of_nhds, ?_⟩
  rw [x.ch.left_inv x.2]
  exact (h.smooth x.pt).1.1

theorem dbar_powFld (h : IsGramPair A G G') (k : ℕ) : A.dbar (fld A (powFld A G k)) = 0 := by
  funext x
  have h₁ := smooth_crd h x
  refine ((GlobalTheory.T.dbar_operator_local_calculus_complex_forms n x.crd).1 _ _ ((GlobalTheory.T.gramConnectionPair_chernFields_local_frame M n A r G G' h x k).mono fun _ hv => hv.1)).trans ?_
  exact (GlobalTheory.T.curvature_power_sum_transgression_smooth_dbar_closed n r _ _ x.crd h₁.1 h₁.2 h₁.1 h₁.2 k).2.1

theorem dbar_transFld (h : IsGramPair A G G') (k : ℕ) :
    fld A (powFld A G k) - fld A (powFld A G' k) = A.dbar (transFld A G G' k) := by
  funext x
  have h₁ := smooth_crd h x
  have h₂ := smooth_crd (pair_symm h) x
  symm
  refine ((GlobalTheory.T.dbar_operator_local_calculus_complex_forms n x.crd).1 _ _ ((GlobalTheory.T.gramConnectionPair_chernFields_local_frame M n A r G G' h x k).mono fun _ hv => hv.2.2)).trans ?_
  exact GlobalTheory.T.dbar_chernTransgressionForm_eq_power_sum_diff n r _ _ x.crd h₁.1 h₁.2 h₂.1 h₂.2 k

theorem dbarCoh_powFld : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (r : Type) [Fintype r]
    [DecidableEq r] (G G' : M → M → Matrix r r ℂ), IsGramPair A G G' → ∀ k,
    DbarCoh A (powFld A G k) (powFld A G' k) := fun M _ n A r _ _ G G' h k =>
  ⟨(GlobalTheory.T.curvaturePowerSum_transgression_isForm M n A r G G' h k).1, (GlobalTheory.T.curvaturePowerSum_transgression_isForm M n A r G' G (pair_symm h) k).1, dbar_powFld h k,
    dbar_powFld (pair_symm h) k, _, (GlobalTheory.T.curvaturePowerSum_transgression_isForm M n A r G G' h k).2, dbar_transFld h k⟩

end GlobalTheory.ChernCalc.PowCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerSumsDbarCohomologousStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curvaturePowerSums_dbarCohomologous : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (r : Type) [Fintype r] [DecidableEq r] (G G' : M → M → Matrix r r ℂ), IsGramPair A G G' → ∀ k, DbarCoh A (powFld A G k) (powFld A G' k) := by
  first | exact @GlobalTheory.ChernCalc.PowCoh.dbarCoh_powFld | exact GlobalTheory.ChernCalc.PowCoh.dbarCoh_powFld | (intros; apply GlobalTheory.ChernCalc.PowCoh.dbarCoh_powFld <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormNewtonIdentitiesCurvaturePowerSums
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormNewtonIdentitiesCurvaturePowerSums
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ChernCalc

theorem newton_charpolyRev {R r : Type} [CommRing R] [Fintype r] [DecidableEq r] (M : Matrix r r R) (k : ℕ) :
    (k : R) * M.charpolyRev.coeff k =
      -∑ i ∈ Finset.range k, (M ^ (i + 1)).trace * M.charpolyRev.coeff (k - 1 - i) := by
  rcases k with _ | k
  · simp
  · have h := congrArg (PowerSeries.coeff k) (GroundTheory.Global.coe_derivative_charpolyRev M)
    rw [Polynomial.coeff_coe, Polynomial.coeff_derivative, neg_mul, map_neg, mul_comm (M.charpolyRev : PowerSeries R),
      PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
    simp only [PowerSeries.coeff_mk, Polynomial.coeff_coe] at h
    rw [mul_comm]
    simpa using h

theorem chernAt_newton (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n) :
    chernAt G v 0 = 1 ∧ ∀ j : ℕ, (j : ℂ) • chernAt G v j =
      -∑ i ∈ Finset.range j, (-kappa) ^ (i + 1) • (powAt G v (i + 1) * chernAt G v (j - 1 - i)) := by
  refine ⟨?_, fun j => ?_⟩
  · have h : (Matrix.charpolyRev (-curvPoly G v)).coeff 0 = 1 := by
      rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
    rw [chernAt, chernPoly, h, map_one, pow_zero, one_smul]
  · have h := congrArg (MvPolynomial.aeval (R := ℂ) (sym (n := n))) (newton_charpolyRev (-curvPoly G v) j)
    have hp (k : ℕ) : MvPolynomial.aeval (R := ℂ) (sym (n := n)) ((-curvPoly G v) ^ k).trace =
        (-1 : ℂ) ^ k • powAt G v k := by
      have e : curvEv G v ^ k = (curvPoly G v ^ k).map (MvPolynomial.aeval (R := ℂ) (sym (n := n))) :=
        (map_pow (MvPolynomial.aeval (R := ℂ) (sym (n := n))).mapMatrix (curvPoly G v) k).symm
      rw [← neg_one_smul ℂ (curvPoly G v), smul_pow, Matrix.trace_smul, map_smul, powAt, e]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.trace, Matrix.diag, map_sum, Matrix.map_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, map_natCast, map_neg, map_sum] at h
    simp only [map_mul, hp] at h
    simp only [chernAt, chernPoly]
    rw [smul_comm, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, h, smul_neg, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [mul_smul_comm, smul_mul_assoc, smul_smul, smul_smul]
    congr 1
    obtain ⟨m, rfl⟩ : ∃ m, j = i + 1 + m := ⟨j - (i + 1), by omega⟩
    rw [show i + 1 + m - 1 - i = m by omega, neg_pow kappa]
    ring

end GlobalTheory.ChernCalc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormNewtonIdentitiesCurvaturePowerSumsStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernForm_newton_identities_curvature_power_sums : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n), chernAt G v 0 = 1 ∧ ∀ j : ℕ, (j : ℂ) • chernAt G v j = -∑ i ∈ Finset.range j, (-kappa) ^ (i + 1) • (powAt G v (i + 1) * chernAt G v (j - 1 - i)) := by
  first | exact @GlobalTheory.ChernCalc.chernAt_newton | exact GlobalTheory.ChernCalc.chernAt_newton | (intros; apply GlobalTheory.ChernCalc.chernAt_newton <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormFieldDbarCohomologousTwoConnections
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem dbarCoh_chernFld : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (r : Type) [Fintype r]
    [DecidableEq r] (G G' : M → M → Matrix r r ℂ), IsGramPair A G G' → ∀ j, DbarCoh A (chernFld A G j) (chernFld A G' j) := by
  intro M _ n A r _ _ G G' hG j
  obtain ⟨h1, -, halg⟩ := GlobalTheory.T.dbarCohomologousEvenForms_algebra_closed M n A
  have hpow := GlobalTheory.T.curvaturePowerSums_dbarCohomologous M n A r G G' hG
  have hzero : DbarCoh A 0 0 := by
    have := (halg 0 1 1 1 1 h1 h1).1
    simpa using this
  have hsum : ∀ (s : Finset ℕ) (w w' : ℕ → A.Pt → Ev n), (∀ i ∈ s, DbarCoh A (w i) (w' i)) →
      DbarCoh A (∑ i ∈ s, w i) (∑ i ∈ s, w' i) := by
    intro s w w' h
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (halg 0 _ _ _ _ (h a (Finset.mem_insert_self _ _))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))).2.1
  have key : ∀ (H : M → M → Matrix r r ℂ) (j : ℕ), 0 < j → chernFld A H j = (j : ℂ)⁻¹ • ((-1 : ℂ) •
      ∑ i ∈ Finset.range j, (-kappa) ^ (i + 1) • (powFld A H (i + 1) * chernFld A H (j - 1 - i))) := by
    intro H j hj
    funext x
    have := (GlobalTheory.T.chernForm_newton_identities_curvature_power_sums n r (fun v => H x.pt (x.ch.symm v)) x.crd).2 j
    simp only [Pi.smul_apply, Finset.sum_apply, Pi.mul_apply, chernFld, powFld, HolAtlas.chern]
    rw [neg_one_smul, ← this, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hj.ne'), one_smul]
  have key0 : ∀ H : M → M → Matrix r r ℂ, chernFld A H 0 = 1 := by
    intro H; funext x
    exact (GlobalTheory.T.chernForm_newton_identities_curvature_power_sums n r _ x.crd).1
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [key0, key0]; exact h1
    · rw [key G j hj, key G' j hj]
      refine (halg _ _ _ _ _ ?_ h1).1
      refine (halg _ _ _ _ _ ?_ h1).1
      refine hsum _ _ _ fun i hi => ?_
      refine (halg _ _ _ _ _ ?_ h1).1
      exact (halg 0 _ _ _ _ (hpow (i + 1)) (ih _ (by simp at hi; omega))).2.2

end GlobalTheory.ChernCalc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormFieldDbarCohomologousTwoConnectionsStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernFormField_dbarCohomologous_two_connections : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (r : Type) [Fintype r] [DecidableEq r] (G G' : M → M → Matrix r r ℂ), IsGramPair A G G' → ∀ j, DbarCoh A (chernFld A G j) (chernFld A G' j) := by
  first | exact @GlobalTheory.ChernCalc.dbarCoh_chernFld | exact GlobalTheory.ChernCalc.dbarCoh_chernFld | (intros; apply GlobalTheory.ChernCalc.dbarCoh_chernFld <;> assumption)
end
