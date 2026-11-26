module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UValThruTopOfDisjoint
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TwistedFlatBundleRanks
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.GeometricOfHyp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BinomialFlagDimensionDegreeBound

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.RankGrowthBoundSmallScale
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CovTop.HodgeSteps
open MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH in
set_option maxHeartbeats 2000000 in
private theorem exists_semilinear_L2_independent {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {r : ℕ} {D : D7} (hS : Out.SecBaseChangeSt) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ)
    (hσ : GoodEmb c σ) (hU : IsUnf (U σ)) (V : HSp D)
    (dict : Formalism.L2.Theta.GA D V → Σ k, Frame ((U σ).X k).Ψ r) (mu : Formalism.L2.Theta.GA D V → ℂ)
    (hmu1 : ∀ g, ‖mu g‖ = 1) (hm : Formalism.L2.Pj.AdelMeas U σ V dict mu) (hae : Formalism.L2.Pj.AeDom U σ V dict mu)
    (hd : ∀ g, (dict g).2 ∈ ((U σ).X (dict g).1).dom)
    (hunit : ∀ g τ i, ‖dmin ((U σ).X (dict g).1).Gm (dict g).2 τ i‖ = 1) (G : WTZ E) (x : ℝ) :
    ∃ Φ : GlobalTheory.AllWt.cuspW Xo c U G →+ Lp ℂ 2 (muQ1 V), (∀ (a : c.F) f, Φ (a • f) = σ a • Φ f) ∧
      (∀ f : GlobalTheory.AllWt.cuspW Xo c U G, GlobalTheory.AllWt.petAt (U σ) x V dict (muQ1 V) G (f : Rul Xo c) = ‖Φ f‖) ∧
      ∀ (n : ℕ) (e : Fin n → GlobalTheory.AllWt.cuspW Xo c U G), LinearIndependent c.F e →
        LinearIndependent ℂ (fun i => Φ (e i)) := by
  have hhol : ∀ f : GlobalTheory.AllWt.cuspW Xo c U G,
      rdU (U σ) (f : Rul Xo c) ∈ holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G) := fun f =>
    (GlobalTheory.AllWt.mem_cuspW.1 f.2).2 σ hσ
  have heq : ∀ P : holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G),
      eLpNorm (onQ V (adel V dict mu P)) 2 (muQ1 V) =
        GlobalTheory.AllWt.petE V dict (muQ1 V) (GlobalTheory.AllWt.modelWt (U σ) G) P := by
    intro P
    unfold GlobalTheory.AllWt.petE
    have hp : ∀ q : AutQ V, ‖mu q.out * (P : FDSec (U σ).X) (dict q.out).1 (dict q.out).2‖ =
        GlobalTheory.AllWt.ptN (GlobalTheory.AllWt.modelWt (U σ) G) P (dict q.out) := by
      intro q
      rw [norm_mul, hmu1, one_mul, GlobalTheory.AllWt.ptN,
        pnorm_eq_of_unit _ _ _ _ (hunit q.out)]
    have hf := aesm_of_holSub hm _ P.2
    have hg := hf.norm.congr (Filter.Eventually.of_forall hp)
    have hh := eLpNorm_congr_norm_ae (p := 2) hf hg (Filter.Eventually.of_forall fun q => by
      rw [Real.norm_of_nonneg (GlobalTheory.AllWt.ptN_nonneg _ _ _)]
      exact hp q)
    rw [eLpNorm_eq_eLpNorm' (by norm_num) (by simp) hg] at hh
    simpa using hh
  have hmem : ∀ P : holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G),
      MemLp (onQ V (adel V dict mu (P : FDSec (U σ).X))) 2 (muQ1 V) := fun P =>
    by
      change eLpNorm _ _ _ < ⊤
      rw [heq P]
      exact lt_top_iff_ne_top.2 (GlobalTheory.AllWt.petE_ne_top V dict (muQ1 V) prob_le_one hd P.2)
  let L : holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G) →ₗ[ℂ] Lp ℂ 2 (muQ1 V) :=
    { toFun := fun P => (hmem P).toLp _
      map_add' := fun P Q => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (by rw [Submodule.coe_add, map_add (f := _), map_add (f := _)]))
      map_smul' := fun a P => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (by rw [Submodule.coe_smul, map_smul, map_smul])) }
  have hL : ∀ P, L P = (hmem P).toLp _ := fun _ => rfl
  let R : GlobalTheory.AllWt.cuspW Xo c U G → holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G) := fun f => ⟨_, hhol f⟩
  have hRadd : ∀ f g, R (f + g) = R f + R g := fun f g => Subtype.ext (by
    show rdU (U σ) ((f + g : GlobalTheory.AllWt.cuspW Xo c U G) : Rul Xo c) = rdU (U σ) (f : Rul Xo c) + rdU (U σ) (g : Rul Xo c)
    rw [Submodule.coe_add, map_add (f := _)])
  have hRsm : ∀ (a : c.F) f, R (a • f) = σ a • R f := fun a f => Subtype.ext (by
    show rdU (U σ) ((a • f : GlobalTheory.AllWt.cuspW Xo c U G) : Rul Xo c) = σ a • rdU (U σ) (f : Rul Xo c)
    rw [Submodule.coe_smul, map_smulₛₗ])
  let cf : ℝ := GlobalTheory.AllWt.lieFacZ Dw x G
  have hcf : 0 < cf := GlobalTheory.AllWt.lieFacZ_pos x G
  refine ⟨AddMonoidHom.mk' (fun f => (cf : ℂ) • L (R f)) (fun f g => by rw [hRadd, map_add (f := _), smul_add]),
    fun a f => ?_, fun f => ?_, fun n e he => ?_⟩
  · show (cf : ℂ) • L (R (a • f)) = σ a • ((cf : ℂ) • L (R f))
    rw [hRsm, map_smul, smul_comm]
  · show _ = ‖(cf : ℂ) • L (R f)‖
    rw [norm_smul, hL, Lp.norm_toLp, heq, Complex.norm_real, Real.norm_of_nonneg hcf.le]
    rfl
  · have hb : LinearIndependent c.F (fun i => (e i : Rul Xo c)) :=
      he.map' (GlobalTheory.AllWt.cuspW Xo c U G).subtype (Submodule.ker_subtype _)
    have hc := GlobalTheory.reading_linearIndependent_secZ hS (U σ) hU _ n _
      (fun i => GlobalTheory.AllWt.cuspW_le_secZ G (e i).2) hb
    rw [Fintype.linearIndependent_iff] at hc ⊢
    intro w hw
    refine hc w ?_
    have h1 : (cf : ℂ) • L (∑ i, w i • R (e i)) = 0 := by
      have hw' : ∑ i, w i • ((cf : ℂ) • L (R (e i))) = 0 := hw
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.smul_sum, ← hw']
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [L.map_smul]
      exact smul_comm _ _ _
    have h2 : L (∑ i, w i • R (e i)) = 0 :=
      (smul_eq_zero.1 h1).resolve_left (Complex.ofReal_ne_zero.2 hcf.ne')
    have h3 : onQ V (adel V dict mu ((∑ i, w i • R (e i) : holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G)) :
        FDSec (U σ).X)) =ᵐ[muQ1 V] 0 := by
      refine (MemLp.coeFn_toLp (hmem _)).symm.trans ?_
      rw [← hL, h2]
      exact Lp.coeFn_zero _ _ _
    have h4 := hae _ _ (∑ i, w i • R (e i)).2 h3
    have h5 : ((∑ i, w i • R (e i) : holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G)) : FDSec (U σ).X) =
        ∑ i, w i • rdU (U σ) (e i : Rul Xo c) := by
      rw [Submodule.coe_sum]
      rfl
    rw [h5] at h4
    funext k z
    by_cases hz : z ∈ ((U σ).X k).dom
    · exact h4 k z hz
    · simp [Finset.sum_apply, rdU, hz]
set_option maxHeartbeats 2000000 in
private theorem hasGram_nrm_of_good (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ) (hY : Y.Good e o)
    (G : WTZ D.host.E) : GlobalTheory.AllWt.HasGram (Y.nrm G) := by
  haveI := GlobalTheory.Deep.finiteDimensional_V_of_good D T j Y e o hY G
  refine GlobalTheory.HSApp.hasGram_of_inner Y.d.c₂.F (Y.V G) (Y.nrm G) fun v => ?_
  have hσ' : GoodEmb Y.d.c₂ (Formalism.L2.Pj.goodOf Y.d.c₂ v.embedding) := Formalism.L2.Pj.goodEmb_goodOf _ _
  have hd : ∀ g, (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ v.embedding) g).2 ∈
      ((Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ v.embedding)).X (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ v.embedding) g).1).dom :=
    fun g => ((hY.dictU _ hσ').choose_spec.choose_spec.2).2.2.2.1 g
  have hex := exists_semilinear_L2_independent GlobalTheory.abelianSchemeLaws_all.1.secBaseChange Y.U _ hσ' (hY.unf _ hσ')
    (D.sp.W j) (Y.dict _) (fun _ => (1 : ℂ)) (fun _ => norm_one)
    (adelMeas_of_aut Y.d.Xo₂ Y.d.c₂ (U := Y.U) (σ := _) (GlobalTheory.PetDef.adelAut_good Y hY _ hσ'))
    (GlobalTheory.PetDef.aeDom_good Y hY _ hσ') hd (hY.unit _ hσ') G (xiR D)
  refine ⟨_, inferInstance, inferInstance, Classical.choose hex, ?_, fun x => (Classical.choose_spec hex).2.1 x,
    (Classical.choose_spec hex).2.2⟩
  by_cases h : GoodEmb Y.d.c₂ v.embedding
  · left
    intro a x
    refine ((Classical.choose_spec hex).1 a x).trans ?_
    exact congrArg (· • Classical.choose hex x) (congrArg (fun τ : Y.d.c₂.F →+* ℂ => τ a) (ite_eq_left h))
  · right
    intro a x
    refine ((Classical.choose_spec hex).1 a x).trans ?_
    exact congrArg (· • Classical.choose hex x) (congrArg (fun τ : Y.d.c₂.F →+* ℂ => τ a) (ite_eq_right h))
theorem covering_goodAt_shift (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (T : CoreJ D) (hL : LawsJ T) (j : ℕ) (hj : InR D j) (Y : Deep T.toCore j) (e : ℕ)
    (o : ℝ) (hY : Y.Good e o) (hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q)
    (hC : GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum.IsComplexData Y.U (fun _ => D.sp.W j) Y.dict) (hl : ∀ q : ℕ, q.Prime → Y.d.l₂.GoodAt q)
    (hF : GlobalTheory.FlatLine.FlatExists Y.U (xiR D)) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n kc : ℕ) (s : ℤ) (hn : Even n)
    (h : Y.GoodAt (wtOf _ (uWt (T.Q.Dw j) a n kc + s • hodgeWt (T.Q.Dw j)) 0)) : Y.GoodAt (shiftG (T.Q.Dw j) a n s) := by
  obtain ⟨m, rfl⟩ := hn
  have h1 := (((GlobalTheory.T.flatLine_thetaRoot_twist_twistingSection hP.p5 D T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ D.R.r Y.U _ Y.dict hC hY.geo hpq hl hF
    (_root_.GlobalTheory.T.unramified_points_of_deep_cover hP D T j Y e o hL hj hY) (anchor (T.Q.Dw j) a (m + m) kc) m).2 _ 0).2 h).1
  have e1 : uWt (T.Q.Dw j) a (m + m) kc + s • hodgeWt (T.Q.Dw j) +
      GlobalTheory.FlatLine.parWt (T.Q.Dw j) (anchor (T.Q.Dw j) a (m + m) kc) =
      laOf (T.Q.Dw j) a (m + m) + s • hodgeWt (T.Q.Dw j) := by
    rw [add_right_comm, uWt_add_anchor]
  rw [e1, add_comm (0 : ℤ), AllWt.wtOf_add] at h1
  have e2 : exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (laOf (T.Q.Dw j) a (m + m)) m + wtOf (T.Q.Dw j) (s • hodgeWt (T.Q.Dw j)) 0) =
      exZ (T.Q.Dw j) (shiftG (T.Q.Dw j) a (m + m) s) := by
    rw [shiftG, FlatTw.exZ_add_eq, FlatTw.exZ_add_eq]
    congr 1
    have := AllWt.exOf_weightOf (Dw := T.Q.Dw j) (fun x => (a x : ℤ)) m
    rw [AllWt.exOf] at this
    rw [laOf, show (m + m) / 2 = m by omega, this, wtZ]
    push_cast
    rw [two_mul]
  have e3 : cuspW Y.d.Xo₂ Y.d.c₂ Y.U
      (wtOf (T.Q.Dw j) (laOf (T.Q.Dw j) a (m + m)) m + wtOf (T.Q.Dw j) (s • hodgeWt (T.Q.Dw j)) 0) =
      cuspW Y.d.Xo₂ Y.d.c₂ Y.U (shiftG (T.Q.Dw j) a (m + m) s) := by
    ext f
    rw [AllWt.mem_cuspW, AllWt.mem_cuspW, e2]
    exact and_congr_right fun _ => forall₂_congr fun σ hσ => by
      rw [AllWt.modelWt_congr (Y.U σ) hσ (hY.unf σ hσ) e2]
  have key : ∀ C C' : Submodule Y.d.c₂.F (Rul Y.d.Xo₂ Y.d.c₂), C = C' →
      ((AllWt.supLat C).FG ∧ Submodule.span Y.d.c₂.F (AllWt.supLat C : Set C) = ⊤) →
      (AllWt.supLat C').FG ∧ Submodule.span Y.d.c₂.F (AllWt.supLat C' : Set C') = ⊤ := by
    rintro C _ rfl h
    exact h
  exact ⟨hasGram_nrm_of_good D _ j Y e o hY _, key _ _ e3 h1.2⟩
end GlobalTheory.CovTop.HodgeSteps
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ShareStatementOfKnownTheorems
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.CovTop.ShareRowsNef
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
end Weights
theorem nef_share_lower_bound (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hSI : GlobalTheory.Published.SiegelToroidalIntegral) (hKS : GlobalTheory.Published.ToroidalForFanKS)
    (hG : GlobalTheory.Published.GrothendieckDeformation) (hQ : GlobalTheory.HSCore.Quoted) (hSL : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7} {T : CoreJ D}
    (hT : LawsJ T) {j : ℕ} (hp : 1 ≤ (T.Q.Dw j).p) (hq : 1 ≤ (T.Q.Dw j).q) (hf : 2 < Module.finrank ℚ D.host.E / 2) (hj : InR D j)
    (Y : Deep T.toCore j) {e : ℕ} {o : ℝ} (hY : Y.Good e o) (P : WtPar (T.Q.Dw j)) (hB : WtBig P)
    (Z : Comp Y.d.Xo₂ Y.d.c₂) (hbir : BirOn Y.U Z (wtOf _ P.u₁ 0)) :
    (((P.T - 1).choose (CompHt.dimFlag (T.Q.Dw j)) : ℕ) : ℝ) * Y.dg P.u₁ Z ≤ Y.rkC (P.wt P.T) Z := by
  have hP1 := _root_.GlobalTheory.T.covering_topology_refinement hP
  obtain ⟨g1, g2, g3⟩ := gapGe_of_wtBig hB
  have good : ∀ la, GapGe 1 la → _ := fun la h =>
    _root_.GlobalTheory.T.covering_domain_lattice_regularity hP D T hT j hp hq hf hj Y e o hY la (antitone_of_gapGe hp hq h).1 (antitone_of_gapGe hp hq h).2
  obtain ⟨TF, R, ω, h⟩ := _root_.GlobalTheory.T.exists_weight_hodge_bundle_generated hP1 hG hQ hP.q15 hP.q16 hSI hKS.toroidalChartsForFan hSL D T.toCore j Y e o hY hf Z P hB fun i _ => (good _ (g3 i)).1
  obtain ⟨f₁⟩ := nonempty_cuspFrame ((good _ g1).2 Z)
  obtain ⟨f₂⟩ := nonempty_cuspFrame ((good _ g2).2 Z)
  let k : CompHS.Consts := ⟨1, 1, 1, 1, 1, le_rfl, le_rfl, le_rfl⟩
  let th : R.L.Sec := GlobalTheory.CompHS.toSec (R.Δ₁.lift 0)
  have hA := _root_.GlobalTheory.T.hodge_bundle_isNef_isBig_of_weight hP1 hQ.nef hSI hKS.toroidalChartsForFan hSL _ _ _ _ _ _ TF Z _ Y.U P R ω _ D _ _ h f₁ f₂ th k hY.geo hB
  have a3 := GlobalTheory.T.hilbertSamuel_map_birational_of_cuspForms_generate TF.X Z Y.U P R ω _ _ _ h f₁ f₂ th k (GlobalTheory.T.cuspForm_ratios_generate_at_flagSpace_genericPoint TF.X Z Y.U P.u₁ ⟨R.toModif⟩ hbir)
  obtain ⟨a1, a2⟩ := hA
  have key := GlobalTheory.T.choose_mul_componentDegree_le_dimension hQ _ _ _ _ _ _ _ _ Z _ Y.U P R ω _ D _ _ h f₁ f₂ th k a1 a2 a3
  have hr : rankOn Y.U Z (wtOf _ (P.wt P.T) 0) = Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf _ (P.wt P.T) 0)) := by
    rw [rankOn, Formalism.HN.rkK, ((good _ (g3 P.T)).2 Z).2.2, finrank_top]
  rw [← hr] at key
  exact_mod_cast key
theorem nef_share_upper_bound (hX : GlobalTheory.CovTop.HypothesesX) (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hSI : GlobalTheory.Published.SiegelToroidalIntegral) (hKS : GlobalTheory.Published.ToroidalForFanKS) (hG : GlobalTheory.Published.GrothendieckDeformation) (hQ : GlobalTheory.HSCore.Quoted)
    (hSL : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7} {T : CoreJ D}
    (hT : LawsJ T) {j : ℕ} (hp : 1 ≤ (T.Q.Dw j).p) (hq : 1 ≤ (T.Q.Dw j).q) (hf : 2 < Module.finrank ℚ D.host.E / 2) (hj : InR D j)
    (Y : Deep T.toCore j) {e : ℕ} {o : ℝ} (hY : Y.Good e o) (P : WtPar (T.Q.Dw j)) (hB : WtBig P)
    (hs : ∀ τ, StrictAnti (P.u₁ τ) ∧ StrictAnti (CompHt.uPrime _ P.u₁ τ))
    (hbir : ∀ Z, BirOn Y.U Z (wtOf _ P.u₁ 0))
    (hV : ∀ Z, ValMult Y.U Z (wtOf _ P.u₁ 0) (wtOf _ (CompHt.uPrime _ P.u₁) 0))
    (h0 : 0 ≤ CompHt.rhoB _ P.u₁) (h1 : CompHt.rhoB _ P.u₁ ≤ 1 / 2) (la : AllWt.Weight (T.Q.Dw j)) (hla : ∀ τ, Antitone (la τ))
    (hd : ∀ τ, Antitone (((P.T + CompHt.dimFlag (T.Q.Dw j) + 3 : ℕ) : ℤ) • P.u₁ τ - la τ))
    (Z : Comp Y.d.Xo₂ Y.d.c₂) (hδ : 0 < Y.dg P.u₁ Z) :
    (1 - 7 * ((CompHt.dimFlag (T.Q.Dw j) : ℝ) ^ 2 / P.T + CompHt.dimFlag (T.Q.Dw j) * CompHt.rhoB _ P.u₁)) * Y.rkC la Z ≤
      (((P.T - 1).choose (CompHt.dimFlag (T.Q.Dw j)) : ℕ) : ℝ) * Y.dg P.u₁ Z := by
  have hD := GlobalTheory.CompHS.dimFlag_eq (T.Q.Dw j)
  have hg := hB.gaps
  have hT1 := hB.le_T
  have hD2 := two_le_dimFlag hp hq hf
  rw [← hD] at hg hT1 hD2
  have hle := (GlobalTheory.T.componentImageDegree_between_of_proportionality _ _ _ _ _ _ _ Y.U hY.unf (_root_.GlobalTheory.T.proportionality_principle_compactification hP hSI hKS hSL D T hT j hp hq hf hj Y e o hY).1
    (_root_.GlobalTheory.T.compactification_top_chern_eq_volume hP hSI hKS hSL D T hT j hp hq hf hj Y e o hY) P.u₁ (fun τ => (hs τ).1) (fun τ => (hs τ).2) hbir hV Z Z).1
  rw [CompHt.delPrime_eq _ _ (CompHt.vdm_pos fun τ => (hs τ).1).ne'] at hle
  set ρ := CompHt.rhoB _ P.u₁ with hρ
  set n := P.T + CompHt.dimFlag (T.Q.Dw j) + 3 with hn
  have hρ1 : 0 < 1 - ρ := by linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have ha1 : ((⌊(n : ℝ) / (1 - ρ)⌋₊ : ℕ) : ℝ) ≤ n / (1 - ρ) := Nat.floor_le (by positivity)
  have ha2 : (n : ℝ) / (1 - ρ) < (⌊(n : ℝ) / (1 - ρ)⌋₊ : ℕ) + 1 := Nat.lt_floor_add_one _
  have ha3 : n ≤ ⌊(n : ℝ) / (1 - ρ)⌋₊ := Nat.le_floor (by rw [le_div_iff₀ hρ1]; nlinarith)
  have hjet := _root_.GlobalTheory.T.jet_rank_complex_le hX hP hSI hKS hG hQ hSL D T hT j hp hq hf hj Y e o hY Z P.u₁ la n ⌊(n : ℝ) / (1 - ρ)⌋₊ hg hla hd (by
    have h2 : CompHt.topDeg Y.U Z P.u₁ ≤ Y.dg P.u₁ Z / (1 - ρ) := by
      rw [le_div_iff₀ hρ1, mul_comm]; exact hle
    calc (n : ℝ) * CompHt.topDeg Y.U Z P.u₁ ≤ n * (Y.dg P.u₁ Z / (1 - ρ)) := mul_le_mul_of_nonneg_left h2 hn0
      _ = n / (1 - ρ) * Y.dg P.u₁ Z := by ring
      _ < _ := mul_lt_mul_of_pos_right ha2 hδ)
  refine GlobalTheory.share_bound_of_jet_count _ _ _ ρ _ _ hD2 hT1 h0 h1 ha3 ?_ hδ.le (Nat.cast_nonneg _) hjet
  rw [hn] at ha1 ⊢
  push_cast at ha1 ⊢
  exact ha1
end GlobalTheory.CovTop.ShareRowsNef
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.BinomialFlagDimensionDegreeBound
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CovTop.DgShare
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
end Weights
theorem nef_share_lower_bound (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hG : GlobalTheory.Published.GrothendieckDeformation) (hQ : GlobalTheory.HSCore.Quoted)
    (hSi : GlobalTheory.Published.SiegelToroidalIntegral) (hFa : GlobalTheory.Published.ToroidalChartsForFan) (hSA : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7} {T : CoreJ D}
    (hT : LawsJ T) {j : ℕ} (hp : 1 ≤ (T.Q.Dw j).p) (hq : 1 ≤ (T.Q.Dw j).q) (hf : 2 < Module.finrank ℚ D.host.E / 2)
    (hj : InR D j) (Y : Deep T.toCore j) {e : ℕ} {o : ℝ} (hY : Y.Good e o) (P : WtPar (T.Q.Dw j)) (hB : WtBig P)
    (Z : Comp Y.d.Xo₂ Y.d.c₂) (hbir : BirOn Y.U Z (wtOf _ P.u₁ 0)) :
    (P.T - 1).choose (CompHt.dimFlag (T.Q.Dw j)) * CompHt.compDeg Y.U Z (wtOf _ P.u₁ 0) ≤
      Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf _ (P.wt P.T) 0)) := by
  have hP1 := _root_.GlobalTheory.T.covering_topology_refinement hP
  obtain ⟨g1, g2, g3⟩ := gapGe_of_wtBig hB
  have good : ∀ la, GapGe 1 la → _ := fun la h =>
    _root_.GlobalTheory.T.covering_domain_lattice_regularity hP D T hT j hp hq hf hj Y e o hY la (antitone_of_gapGe hp hq h).1
      (antitone_of_gapGe hp hq h).2
  obtain ⟨TF, R, ω, h⟩ := _root_.GlobalTheory.T.exists_weight_hodge_bundle_generated hP1 hG hQ hP.q15 hP.q16 hSi hFa hSA D T.toCore j Y e o hY hf Z P hB fun i _ => (good _ (g3 i)).1
  obtain ⟨f₁⟩ := nonempty_cuspFrame ((good _ g1).2 Z)
  obtain ⟨f₂⟩ := nonempty_cuspFrame ((good _ g2).2 Z)
  let k : CompHS.Consts := ⟨1, 1, 1, 1, 1, le_rfl, le_rfl, le_rfl⟩
  let th : R.L.Sec := GlobalTheory.CompHS.toSec (R.Δ₁.lift 0)
  obtain ⟨a1, a2⟩ := _root_.GlobalTheory.T.hodge_bundle_isNef_isBig_of_weight hP1 hP.q7 hSi hFa hSA _ _ _ _ _ _ TF Z _ Y.U P R ω _ D _ _ h f₁ f₂ th k hY.geo hB
  have a3 := birational_of_ratGen TF.X Z Y.U P R ω _ _ _ h f₁ f₂ th k
    (ratGen_of_birOn TF.X Z Y.U P.u₁ ⟨R.toModif⟩ hbir)
  exact GlobalTheory.HSCore.CompShare.choose_mul_compDeg_le hQ _ _ _ _ _ _ _ _ Z _ Y.U P R ω _ D _ _ h f₁ f₂ th k a1 a2 a3
end GlobalTheory.CovTop.DgShare
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
end
end
