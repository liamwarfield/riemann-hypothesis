module

public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.NuAlgLeOfCharts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzLeviInverseTranspose
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothGramSchmidtIndefiniteHermitianFrames
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsSubspaceStableSobolevFormDeriv
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthInChartChartIndependent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthInChartChartIndependent
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FactorDepth

section Series
open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

theorem exp_eq_of_log_hom {d : ℕ} (G G' : LogFGL v d) (Φ : Fin d → MvPowerSeries (Fin d) C)
    (h0 : ∀ e, constantCoeff (Φ e) = 0) (M : Matrix (Fin d) (Fin d) C)
    (hl : ∀ e, subst Φ (G.lg e) = ∑ f, M e f • G'.lg f) {τ : Type} (w w' : Fin d → MvPowerSeries τ C)
    (hw' : ∀ e, constantCoeff (w' e) = 0) (hw : ∀ e, w e = ∑ f, M e f • w' f) (e : Fin d) :
    subst w (expOf G e) = subst (fun f => subst w' (expOf G' f)) (Φ e) := by
  have s1 : HasSubst w' := hasSubst_of_constantCoeff_zero hw'
  have c2 : ∀ f, constantCoeff (subst w' (expOf G' f) : MvPowerSeries τ C) = 0 := fun f =>
    constantCoeff_subst_eq_zero s1 hw' ((isExp_expOf G').1 f)
  have s2 := hasSubst_of_constantCoeff_zero c2
  have s3 : HasSubst (fun e => (subst (fun f => (subst w' (expOf G' f) : MvPowerSeries τ C)) (Φ e) :
      MvPowerSeries τ C)) :=
    hasSubst_of_constantCoeff_zero fun e => constantCoeff_subst_eq_zero s2 c2 (h0 e)
  have key : (fun j => subst (fun e => (subst (fun f => (subst w' (expOf G' f) : MvPowerSeries τ C)) (Φ e) :
      MvPowerSeries τ C)) (G.lg j)) = w := by
    funext j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero h0) s2, hl, hw, ← coe_substAlgHom s2, map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [map_smul, coe_substAlgHom,
      ← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (isExp_expOf G').1) s1, (isExp_expOf G').2,
      subst_X s1]
  have := subst_comp_subst_apply (hasSubst_of_constantCoeff_zero G.lg_const) s3 (expOf G e)
  rw [subst_lg_expOf, subst_X s3, key] at this
  exact this.symm

theorem depth_le_of_log_hom {κ : Type} [Finite κ] {d : κ → ℕ} (G G' : ∀ b, LogFGL v (d b)) {ι : κ → Type}
    [∀ b, Fintype (ι b)] (u u' : ∀ b, ι b → Fin (d b) → C) (Φ : ∀ b, Fin (d b) → MvPowerSeries (Fin (d b)) C)
    (h0 : ∀ b e, constantCoeff (Φ b e) = 0) (hI : ∀ b e, MvIsInt v (Φ b e))
    (M : ∀ b, Matrix (Fin (d b)) (Fin (d b)) C)
    (hl : ∀ b e, subst (Φ b) ((G b).lg e) = ∑ f, M b e f • (G' b).lg f)
    (hu : ∀ b a, u b a = (M b).mulVec (u' b a)) (P : MvPolynomial (Σ b, ι b) C) :
    depth G' u' P ≤ depth G u P := by
  classical
  have cX : ∀ b (e : Fin (d b)), constantCoeff (X ⟨b, e⟩ : MvPowerSeries (Σ b, Fin (d b)) C) = 0 := fun b e => by simp
  let Ψ : (Σ b, Fin (d b)) → MvPowerSeries (Σ b, Fin (d b)) C :=
    fun x => subst (fun e : Fin (d x.1) => (X ⟨x.1, e⟩ : MvPowerSeries (Σ b, Fin (d b)) C)) (Φ x.1 x.2)
  have cΨ : ∀ x, constantCoeff (Ψ x) = 0 := fun x =>
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (cX x.1)) (cX x.1) (h0 x.1 x.2)
  have iΨ : ∀ x, MvIsInt v (Ψ x) := fun x =>
    ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v (hI x.1 x.2)
      (fun e α => by rw [coeff_X]; split_ifs <;> simp [IsIntV]) (cX x.1)
  have cw : ∀ b (e : Fin (d b)),
      constantCoeff (∑ a, u' b a e • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C)) = 0 := fun b e => by simp
  have cE : ∀ x, constantCoeff (expAlong G' u' x) = 0 := fun x =>
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (cw x.1)) (cw x.1) ((isExp_expOf _).1 _)
  have sE := hasSubst_of_constantCoeff_zero cE
  have key : expAlong G u = fun x => subst (expAlong G' u') (Ψ x) := by
    funext x
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (cX x.1)) sE]
    simp only [subst_X sE]
    refine exp_eq_of_log_hom (G x.1) (G' x.1) (Φ x.1) (h0 x.1) (M x.1) (hl x.1) _ _ (cw x.1) (fun e => ?_) x.2
    simp only [hu, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
    exact Finset.sum_comm
  refine le_iInf fun f => iInf_le_of_le
    ⟨subst Ψ f.1, ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v f.2 iΨ cΨ⟩ (le_of_eq ?_)
  rw [key, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero cΨ) sE]

end Series

section Law
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.GermDerivativeLinearMaps GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.LawLog

variable {C : Type} [Field C] [CharZero C] {d : ℕ}

theorem logOf_spec (G : FGLaw C d) : GP (GlobalTheory.FormalLog.logOf G) ∧ dLin (GlobalTheory.FormalLog.logOf G) = 1 ∧
    comp1 (GlobalTheory.FormalLog.logOf G) (addOf G.F (pt C (n := 2) d 0) (pt C (n := 2) d 1)) =
      comp1 (GlobalTheory.FormalLog.logOf G) (pt C (n := 2) d 0) + comp1 (GlobalTheory.FormalLog.logOf G) (pt C (n := 2) d 1) := by
  refine ⟨fun i => GlobalTheory.FormalLog.constantCoeff_prim _, ?_, ?_⟩
  · refine Matrix.ext fun i j => ?_
    show coeff (Finsupp.single ((0 : Fin 1), j) 1) (GlobalTheory.FormalLog.logOf G i) = (1 : Matrix (Fin d) (Fin d) C) i j
    have h := congrArg constantCoeff (GlobalTheory.FormalLog.pderiv_logOf G i j)
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add] at h
    have h2 := congrFun (congrFun (GlobalTheory.FormalLog.cc_om G) i) j
    simp only [Matrix.map_apply] at h2
    simpa [h2] using h
  · have e : addOf G.F (pt C (n := 2) d 0) (pt C (n := 2) d 1) = G.F := add_pt G
    rw [e]
    funext i
    exact GlobalTheory.FormalLog.logOf_add G i

theorem logOf_comp_hom (G G' : FGLaw C d) (φ : Pt C 1 d) (hφ : GP φ)
    (hhom : comp1 φ G'.F = addOf G.F (comp1 φ (pt C (n := 2) d 0)) (comp1 φ (pt C (n := 2) d 1))) :
    comp1 (GlobalTheory.FormalLog.logOf G) φ = fun i => ∑ j : Fin d, dLin φ i j • GlobalTheory.FormalLog.logOf G' j := by
  obtain ⟨a0, a1, a2⟩ := logOf_spec G
  obtain ⟨b0, b1, b2⟩ := logOf_spec G'
  obtain ⟨ε, hi⟩ := ChartInv.exists_isInvPair C d _ b0 (by rw [b1, Matrix.det_one]; exact isUnit_one)
  have p0 : GP (pt C (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt C (n := 2) d 1) := gp_pt 1
  have e : addOf G'.F (pt C (n := 2) d 0) (pt C (n := 2) d 1) = G'.F := add_pt G'
  have e1 := additive_eq_lin _ G'.const _ ε (comp1 (GlobalTheory.FormalLog.logOf G) φ) b1 b2 hi
    (gp_comp1 _ _ a0 hφ) (by
    rw [e, gt_comp1_comp1 _ _ hφ _ G'.const, hhom,
      additive_at _ G.const _ a2 _ _ (gp_comp1 _ _ hφ p0) (gp_comp1 _ _ hφ p1),
      gt_comp1_comp1 _ _ hφ _ p0, gt_comp1_comp1 _ _ hφ _ p1])
  rw [dLin_comp _ _ hφ, a1, one_mul] at e1
  rw [e1]
  funext i
  rw [germComp_matrixLinearMap_apply _ _ b0]
  simp only [MvPowerSeries.smul_eq_C_mul]


open ReciprocityTheory.PGsh GlobalTheory.FGDepth in
theorem detDepth_le_of_transF {R : Type} [CommRing R] (v : AddValuation C (WithTop ℝ)) (j : R →+* C)
    (hj : ∀ r, IsIntV v (j r)) (F F' : Fin d → PS R 2 d) (hF : ∀ a, constantCoeff (F a) = 0)
    (φ φi : Pt R 1 d) (hi : IsInvPair φ φi)
    (ht : ∀ a, F' a = transF F φ φi a) (L L' : FGLaw C d) (hL : ∀ a, L.F a = MvPowerSeries.map j (F a))
    (hL' : ∀ a, L'.F a = MvPowerSeries.map j (F' a))
    (hI : ∀ a, MvIsInt v (subst (twoVars C d) (L.F a))) (hI' : ∀ a, MvIsInt v (subst (twoVars C d) (L'.F a)))
    {i : ℕ} (u u' : Fin i → Fin d → R) (hu : ∀ a, u a = (dLin φ).mulVec (u' a)) (k : ℕ) :
    detDepth (logFGLOf v L' hI') (fun a e => j (u' a e)) k ≤ detDepth (logFGLOf v L hI) (fun a e => j (u a e)) k := by
  have hφ : GP φ := hi.1
  have p0 : GP (pt R (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt R (n := 2) d 1) := gp_pt 1
  have q := gp_addOf F hF _ _ (gp_comp1 _ _ hφ p0) (gp_comp1 _ _ hφ p1)
  have e0 : F' = comp1 φi (addOf F (comp1 φ (pt R (n := 2) d 0)) (comp1 φ (pt R (n := 2) d 1))) := funext ht
  have hF' : GP F' := e0 ▸ gp_comp1 _ _ hi.2.1 q
  have e1 : comp1 φ F' = addOf F (comp1 φ (pt R (n := 2) d 0)) (comp1 φ (pt R (n := 2) d 1)) := by
    rw [e0, gt_comp_inv hi _ q]
  have e2 := congrArg (GlobalTheory.FBMap.mapPt j) e1
  rw [GlobalTheory.FBMap.mapPt_comp1 j _ hF', GlobalTheory.FBMap.mapPt_addOf j _ (gp_comp1 _ _ hφ p0) (gp_comp1 _ _ hφ p1),
    GlobalTheory.FBMap.mapPt_comp1 j _ p0, GlobalTheory.FBMap.mapPt_comp1 j _ p1, GlobalTheory.FBMap.mapPt_pt, GlobalTheory.FBMap.mapPt_pt,
    show GlobalTheory.FBMap.mapPt j F = L.F from (funext hL).symm, show GlobalTheory.FBMap.mapPt j F' = L'.F from (funext hL').symm] at e2
  have hψ : GP (GlobalTheory.FBMap.mapPt j φ) := fun a => by simp [GlobalTheory.FBMap.mapPt, hφ a]
  have e3 := logOf_comp_hom L L' _ hψ e2
  refine depth_le_of_log_hom _ _ _ _ (fun _ a => subst (oneVar C d) (GlobalTheory.FBMap.mapPt j φ a))
    (fun _ a => constantCoeff_subst_eq_zero hs_oneVar cc_oneVar (hψ a)) (fun _ a α => ?_)
    (fun _ => dLin (GlobalTheory.FBMap.mapPt j φ)) (fun _ a => ?_) (fun _ a => ?_) _
  · have e : subst (oneVar C d) (GlobalTheory.FBMap.mapPt j φ a) = MvPowerSeries.map j (subst (oneVar R d) (φ a)) := by
      rw [MvPowerSeries.map_subst hs_oneVar]
      congr 1
      funext q
      simp [oneVar]
    rw [e, coeff_map]
    exact hj _
  · show subst _ (subst (oneVar C d) (GlobalTheory.FormalLog.logOf L a)) =
      ∑ f, _ • subst (oneVar C d) (GlobalTheory.FormalLog.logOf L' f)
    rw [subst_oneVar _ cc_oneVar _ hψ]
    refine (congrArg (subst (oneVar C d)) (congrFun e3 a)).trans ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← coe_substAlgHom hs_oneVar, map_sum]
    simp only [map_smul]
  · funext e
    rw [hu, RingHom.map_mulVec]
    rfl

end Law

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp GlobalTheory.CharDepth ReciprocityTheory.PGsh GlobalTheory.FGDepth GlobalTheory.LawLog

theorem detDepth_le_of_charts {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    [StarRing (𝓞 E)] (hs : ∀ a : 𝓞 E, star a = H.bar a)
    (V : Type) [CommRing V] [IsLocalRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V)))
    (hsurj : Function.Surjective (t'.G ⊗ t'.G).hom.appTop.hom) (d d' : ℕ)
    (B : FB V d (𝓞 E)) (B' : FB V d' (𝓞 E))
    (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : Fin d' → (Sp (DualNumber V) ⟶ t'.G.left))
    (uv : Fin d → Fin d → V) (uv' : Fin d' → Fin d' → V)
    (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d' m 1 ⟶ t'.G)
    (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d' x' m)
    (hc : IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x)
    (hc' : IsChartG t' (𝟙 (Sp V)) d' B'.G.F B'.A.act tg' uv' x')
    (hu : GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x) (hu' : GlobalTheory.PowGerm.IsUnivJ t'.G (Fin 1 × Fin d') x')
    (hf : IsFrameG t (𝟙 (Sp V)) d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e)
    (hf' : IsFrameG t' (𝟙 (Sp V)) d' x' B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e')
    {i : ℕ} (u : Fin i → Fin d → V) (u' : Fin i → Fin d' → V)
    (w : Fin i → (Sp (DualNumber V) ⟶ t.G.left))
    (hw : ∀ ℓ, IsCombAtG t (𝟙 (Sp V)) (dirs x) (u ℓ) (w ℓ))
    (hw' : ∀ ℓ, IsCombAtG t' (𝟙 (Sp V)) (dirs x') (u' ℓ) (w ℓ ≫ n.φ))
    {C : Type} [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (j : V →+* C) (hj : ∀ r, IsIntV v (j r))
    (L : FGLaw C d) (L' : FGLaw C d') (hL : ∀ a, L.F a = MvPowerSeries.map j (B.G.F a))
    (hL' : ∀ a, L'.F a = MvPowerSeries.map j (B'.G.F a))
    (hI : ∀ a, MvIsInt v (MvPowerSeries.subst (twoVars C d) (L.F a)))
    (hI' : ∀ a, MvIsInt v (MvPowerSeries.subst (twoVars C d') (L'.F a))) (k : ℕ) :
    detDepth (logFGLOf v L' hI') (fun a e => j (u' a e)) k ≤ detDepth (logFGLOf v L hI) (fun a e => j (u a e)) k := by
  have hd : d = d' := by
    obtain ⟨x'', -, h2, -⟩ := GlobalTheory.T.pushChartAlt E H V t t' n d x
    exact GlobalTheory.T.universalJetCoordinates_dim_unique V t'.G d d' x'' x' (h2 hu) hu'
  subst hd
  obtain ⟨φ, φi, hJ, hdir⟩ := GlobalTheory.T.formal_biextensions_related_of_triple_map_over_id E H hs V t t' n hsurj d B B' (Fin d) (Fin d) tg tg' uv uv' x x' e e'
    hc hc' hu hu' hf hf'
  obtain ⟨ε, hε⟩ := hJ 0
  exact detDepth_le_of_transF v j hj _ _ B.G.const φ φi hε.inv hε.law L L' hL hL' hI hI' u u'
    (fun a => hdir _ _ _ (hw a) (hw' a)) k

theorem nuFacC_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) :
    letI := H.starRing
    ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io)
      (C C' : IntegralChartA3 Xo c T io y) (X : ValExt T p) (f : Lt1 Dw) (k : ℕ), nuFacC C' X f k ≤ nuFacC C X f k := by
  letI := H.starRing
  intro p _ T io y C C' X f k
  letI := io.toAlgebra
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_iso_integralModels_matching_lieBases E H Dw l Xo c T io y.1 C.I C'.I
  obtain ⟨B, b1, b2, b3, b4, b5, b6, -⟩ := GlobalTheory.integralChart_formalBiext E H Dw l Xo c T io y C
  obtain ⟨B', b1', b2', b3', b4', b5', b6', -⟩ := GlobalTheory.integralChart_formalBiext E H Dw l Xo c T io y C'
  refine detDepth_le_of_charts (fun _ => rfl) T.V C.I.G C'.I.G n (GlobalTheory.T.surjective_appTop_integralModel_square E H Dw l Xo c T io y.1 C'.I) _ _ B B'
    C.tgT C'.tgT (fun j => Pi.single j 1) (fun j => Pi.single j 1) C.xT C'.xT C.eT C'.eT ?_ ?_
    (GlobalTheory.PowGerm.univSt_holds E H Dw l Xo c T io y C) (GlobalTheory.PowGerm.univSt_holds E H Dw l Xo c T io y C') ?_ ?_
    (fun a => C.uvecT ⟨f.1, Fin.castLE (rk_le f) a⟩) (fun a => C'.uvecT ⟨f.1, Fin.castLE (rk_le f) a⟩)
    (fun a => (C.I.ub f.1 (Fin.castLE (rk_le f) a)).left) (fun a => C.dirT ⟨f.1, Fin.castLE (rk_le f) a⟩) ?_
    (vX_vp X) (jX X) (isIntV_jX X) (lawX C X) (lawX C' X) ?_ ?_ (fgl C X).F_int (fgl C' X).F_int k
  · rw [b1, b2]; exact C.chartT
  · rw [b1', b2']; exact C'.chartT
  · rw [b1, b2, b3, b4, b5, b6]; exact C.frameT
  · rw [b1', b2', b3', b4', b5', b6']; exact C'.frameT
  · intro a
    rw [hn]
    exact C'.dirT ⟨f.1, Fin.castLE (rk_le f) a⟩
  · intro a; rw [b1]; exact lawX_F C X a
  · intro a; rw [b1']; exact lawX_F C' X a

theorem nuFacC_chart_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR)
    (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch Ch' : IntegralChartA3 Xo c T io y) (X : ValExt T p) (f : Lt1 Dw) (k : ℕ),
    nuFacC Ch X f k = nuFacC Ch' X f k :=
  fun _ _ _ _ _ _ _ Xo c p _ T io y Ch Ch' X f k =>
    le_antisymm (nuFacC_le Xo c p T io y Ch' Ch X f k) (nuFacC_le Xo c p T io y Ch Ch' X f k)

end GlobalTheory.FactorDepth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthInChartChartIndependentStatement
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CharDepth GlobalTheory.FactorDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detFactorDepthInChart_chart_independent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch Ch' : IntegralChartA3 Xo c T io y) (X : ValExt T p) (f : Lt1 Dw) (k : ℕ), nuFacC Ch X f k = nuFacC Ch' X f k := by
  first | exact @GlobalTheory.FactorDepth.nuFacC_chart_indep | exact GlobalTheory.FactorDepth.nuFacC_chart_indep | (intros; apply GlobalTheory.FactorDepth.nuFacC_chart_indep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionTorusEquivariantOrthonormalFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionTorusEquivariantOrthonormalFrames
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.TorusExt

open ReciprocityTheory.ChartRestriction.G.AR.Up

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem value_indep (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (F : Frame X.Ψ r → ℂ)
    (hF : ∀ y, IsUnitFr X y → ∀ c ∈ Bor X.Ψ r, IsUnitFr X (rmul y c) → F (rmul y c) = bchar la c * F y)
    {y y' b b' : Frame X.Ψ r} (hy : IsUnitFr X y) (hy' : IsUnitFr X y') (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r)
    (h : rmul y b = rmul y' b') : bchar la b * F y = bchar la b' * F y' := by
  have hi := ExtFPf.invF_mem X hb'
  have hc := ExtFPf.mul_mem X hb hi
  have e : rmul y (rmul b (ExtFPf.invF X b')) = y' := by
    rw [← ExtFPf.rmul_assoc, h, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb', ExtFPf.rmul_oneF]
  have h1 := hF y hy _ hc (by rw [e]; exact hy')
  rw [e, ExtFPf.bchar_mul X la hb hi] at h1
  have h2 : bchar la b' * bchar la (ExtFPf.invF X b') = 1 := by
    rw [← ExtFPf.bchar_mul X la hb' hi, ExtFPf.rmul_invF X hb', ExtFPf.bchar_oneF]
  rw [h1]
  linear_combination (-(bchar la b * F y)) * h2

theorem exists_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (F : Frame X.Ψ r → ℂ), (∀ y, IsUnitFr X y → ∀ t : X.Ψ → Fin r → ℝ, F (rmul y (fun τ => (Matrix.diagonal fun a => Complex.exp ((t τ a : ℂ) * Complex.I) : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)) = bchar la (fun τ => (Matrix.diagonal fun a => Complex.exp ((t τ a : ℂ) * Complex.I) : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) * F y) → ∃ Q : Frame X.Ψ r → ℂ, (∀ y, IsUnitFr X y → Q y = F y) ∧ ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul x b) = bchar la b * Q x := by
  intro E _ _ _ r X la F hF
  obtain ⟨-, hex, huniq, -⟩ := GlobalTheory.T.gramSchmidt_flagDomain_orthonormalFrames E r X
  have hF' : ∀ y, IsUnitFr X y → ∀ c ∈ Bor X.Ψ r, IsUnitFr X (rmul y c) → F (rmul y c) = bchar la c * F y := by
    intro y hy c hc hyc
    obtain ⟨t, rfl⟩ := huniq y hy c hc hyc
    exact hF y hy t
  let D : Frame X.Ψ r → Prop := fun x => ∃ p : Frame X.Ψ r × Frame X.Ψ r,
    IsUnitFr X p.1 ∧ p.2 ∈ Bor X.Ψ r ∧ x = rmul p.1 p.2
  let Q : Frame X.Ψ r → ℂ := fun x => if h : D x then bchar la h.choose.2 * F h.choose.1 else 0
  have hQ : ∀ y, IsUnitFr X y → ∀ b ∈ Bor X.Ψ r, Q (rmul y b) = bchar la b * F y := by
    intro y hy b hb
    have hD : D (rmul y b) := ⟨(y, b), hy, hb, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hD.choose_spec
    show (if h : D (rmul y b) then bchar la h.choose.2 * F h.choose.1 else 0) = _
    rw [dite_eq_left hD]
    exact (value_indep X la F hF' hy h1 hb h2 h3).symm
  refine ⟨Q, fun y hy => ?_, fun x hx b hb => ?_⟩
  · have := hQ y hy _ (ExtFPf.oneF_mem X)
    rwa [ExtFPf.rmul_oneF, ExtFPf.bchar_oneF, one_mul] at this
  · obtain ⟨y, hy, c, hc, rfl⟩ := hex x hx
    rw [ExtFPf.rmul_assoc, hQ y hy _ (ExtFPf.mul_mem X hc hb), hQ y hy c hc, ExtFPf.bchar_mul X la hc hb]
    ring

end GlobalTheory.HolRead.TorusExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionTorusEquivariantOrthonormalFramesStatement
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extension_torusEquivariant_orthonormalFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (F : Frame X.Ψ r → ℂ), (∀ y, IsUnitFr X y → ∀ t : X.Ψ → Fin r → ℝ, F (rmul y (fun τ => (Matrix.diagonal fun a => Complex.exp ((t τ a : ℂ) * Complex.I) : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)) = bchar la (fun τ => (Matrix.diagonal fun a => Complex.exp ((t τ a : ℂ) * Complex.I) : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) * F y) → ∃ Q : Frame X.Ψ r → ℂ, (∀ y, IsUnitFr X y → Q y = F y) ∧ ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul x b) = bchar la b * Q x := by
  first | exact @GlobalTheory.HolRead.TorusExt.exists_extension | exact GlobalTheory.HolRead.TorusExt.exists_extension | (intros; apply GlobalTheory.HolRead.TorusExt.exists_extension <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIsIntegralOfIntegralCoordsLocalTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIsIntegralOfIntegralCoordsLocalTensor
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.FinClsLoc

open IsDedekindDomain

theorem eventually_rat_mem_adicCompletionIntegers (q : ℚ) :
    ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite,
      algebraMap ℚ (v.adicCompletion ℚ) q ∈ v.adicCompletionIntegers ℚ := by
  have h := (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q).2
  filter_upwards [h] with v hv
  exact hv

theorem intC_isIntegral : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∀ᶠ w : AwayP p in Filter.cofinite,
    ∀ x : w.1.adicCompletion ℚ ⊗[ℚ] G.C, IntC G w x → (∃ f : Polynomial (w.1.adicCompletion ℚ), f.Monic ∧
      (∀ i, f.coeff i ∈ w.1.adicCompletionIntegers ℚ) ∧ Polynomial.aeval x f = 0) := by
  intro p _ G
  set b := Module.finBasis ℚ G.C with hb
  have hev : ∀ᶠ w : AwayP p in Filter.cofinite, ∀ k j l,
      algebraMap ℚ (w.1.adicCompletion ℚ) (b.repr (b k * b j) l) ∈ w.1.adicCompletionIntegers ℚ := by
    rw [Filter.eventually_all]; intro k
    rw [Filter.eventually_all]; intro j
    rw [Filter.eventually_all]; intro l
    exact Subtype.val_injective.tendsto_cofinite.eventually (eventually_rat_mem_adicCompletionIntegers _)
  filter_upwards [hev] with w hw
  intro x hx
  set B := Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) b with hB
  have hent : ∀ i j, Algebra.leftMulMatrix B x i j ∈ w.1.adicCompletionIntegers ℚ := by
    intro i j
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    rw [← B.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_mul, map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun k _ => ?_
    rw [smul_mul_assoc, map_smul, Finsupp.smul_apply, smul_eq_mul]
    have e : B k * B j = (1 : w.1.adicCompletion ℚ) ⊗ₜ[ℚ] (b k * b j) := by
      simp [hB, Algebra.TensorProduct.basis_apply]
    rw [e, Algebra.TensorProduct.basis_repr_tmul]
    simp only [one_smul, Finsupp.mapRange_apply]
    exact mul_mem (hx k) (hw k j i)
  refine ⟨(Algebra.leftMulMatrix B x).charpoly, Matrix.charpoly_monic _, ?_, ?_⟩
  · intro n
    let M : Matrix (Fin (Module.finrank ℚ G.C)) (Fin (Module.finrank ℚ G.C)) (w.1.adicCompletionIntegers ℚ) :=
      fun i j => ⟨_, hent i j⟩
    have hM : Algebra.leftMulMatrix B x = M.map (algebraMap (w.1.adicCompletionIntegers ℚ) (w.1.adicCompletion ℚ)) := by
      ext i j; rfl
    rw [hM, Matrix.charpoly_map, Polynomial.coeff_map]
    exact (M.charpoly.coeff n).2
  · apply Algebra.leftMulMatrix_injective B
    rw [← Polynomial.aeval_algHom_apply, Matrix.aeval_self_charpoly, map_zero]

end GlobalTheory.FinClsLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIsIntegralOfIntegralCoordsLocalTensorStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_isIntegral_of_integralCoordsLocalTensor : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∀ᶠ w : AwayP p in Filter.cofinite,
    ∀ x : w.1.adicCompletion ℚ ⊗[ℚ] G.C, IntC G w x → (∃ f : Polynomial (w.1.adicCompletion ℚ), f.Monic ∧ (∀ i, f.coeff i ∈ w.1.adicCompletionIntegers ℚ) ∧ Polynomial.aeval x f = 0) := by
  first | (exact @GlobalTheory.FinClsLoc.intC_isIntegral) | (exact GlobalTheory.FinClsLoc.intC_isIntegral) | (intros; apply GlobalTheory.FinClsLoc.intC_isIntegral  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualHermitianLatticeExistsNonzeroPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualHermitianLatticeExistsNonzeroPairing
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory

theorem sesquilinearFormOfGram_eq_conj_swap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ e, σ (σ e) = e) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (x w : Fin n → E),
    (∀ i j, σ (J j i) = J i j) → form σ J x w = σ (form σ J w x) := by
  intro F E _ _ _ _ _ σ hσ n J x w hJ
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem not_fg_top_ringOfIntegers (E : Type) [Field E] [NumberField E] :
    ¬ (⊤ : Submodule (𝓞 E) E).FG := by
  intro h
  haveI : Module.Finite (𝓞 E) E := ⟨h⟩
  haveI : Module.Finite ℤ E := Module.Finite.trans (𝓞 E) E
  have hi : IsIntegral ℤ (algebraMap ℚ E (2⁻¹ : ℚ)) := Algebra.IsIntegral.isIntegral _
  rw [isIntegral_algebraMap_iff ] at hi
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
  have h2 : ((2 * y : ℤ) : ℚ) = 1 := by
    push_cast
    rw [show (algebraMap ℤ ℚ y) = (y : ℚ) from rfl] at hy
    rw [hy]; norm_num
  have : 2 * y = 1 := by exact_mod_cast h2
  omega

theorem selfDual_pair_nondeg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ e, σ (σ e) = e) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), L.FG →
    (∀ i j, σ (J j i) = J i j) → (∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (form σ J y x)) →
    ∀ x : Fin n → E, x ≠ 0 → ∃ z ∈ L, form σ J z x ≠ 0 := by
  intro F E _ _ _ _ _ σ hσ n J L hL hJ hdual x hx
  by_contra hcon
  push_neg at hcon
  have hxw : ∀ w ∈ L, form σ J x w = 0 := fun w hw => by
    rw [sesquilinearFormOfGram_eq_conj_swap F E σ hσ n J x w hJ, hcon w hw, map_zero]
  have hmem : ∀ c : E, c • x ∈ L := fun c => by
    rw [hdual]
    intro w hw
    have : form σ J (c • x) w = c * form σ J x w := by
      simp [form, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    rw [this, hxw w hw, mul_zero]
    exact isIntegral_zero
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h; push_neg at h; exact hx (funext h)
  let f : (Fin n → E) →ₗ[𝓞 E] E := (LinearMap.proj i : (Fin n → E) →ₗ[E] E).restrictScalars (𝓞 E)
  have htop : L.map f = ⊤ := by
    rw [eq_top_iff]
    intro e _
    refine ⟨(e / x i) • x, hmem _, ?_⟩
    simp [f, div_mul_cancel₀ _ hi]
  exact not_fg_top_ringOfIntegers E (htop ▸ hL.map f)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualHermitianLatticeExistsNonzeroPairingStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_hermitianLattice_exists_nonzero_pairing : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ e, σ (σ e) = e) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), L.FG →
    (∀ i j, σ (J j i) = J i j) → (∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (form σ J y x)) →
    ∀ x : Fin n → E, x ≠ 0 → ∃ z ∈ L, form σ J z x ≠ 0 := by
  first | exact @GlobalTheory.selfDual_pair_nondeg | exact GlobalTheory.selfDual_pair_nondeg | (intros; apply GlobalTheory.selfDual_pair_nondeg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionHermitianLinearFormFgModule
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionHermitianLinearFormFgModule
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory.FormSection

theorem exists_section : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), L.FG →
    ∀ x : Fin n → E, (∃ z ∈ L, form σ J z x ≠ 0) →
    ∃ y₀ : Fin n → E, form σ J y₀ x = 1 ∧ ∀ z ∈ L, form σ J z x • y₀ ∈ L := by
  intro F E _ _ _ _ _ σ n J L hL x ⟨z₀, hz₀L, hz₀⟩
  classical

  let φ : (Fin n → E) →ₗ[𝓞 E] E :=
    { toFun := fun z => form σ J z x
      map_add' := fun a b => by simp [form, add_dotProduct]
      map_smul' := fun a z => by
        simp only [form, RingHom.id_apply]
        rw [← algebraMap_smul E a z, smul_dotProduct, smul_eq_mul, Algebra.smul_def] }
  have hφ : ∀ z, φ z = form σ J z x := fun _ => rfl
  have hφE : ∀ (c : E) z, form σ J (c • z) x = c * form σ J z x := by
    intro c z; simp [form, smul_dotProduct]
  let I : Submodule (𝓞 E) E := L.map φ
  have hIfg : I.FG := hL.map φ
  let I' : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := ⟨I, FractionalIdeal.isFractional_of_fg hIfg⟩
  have hmemI : ∀ z ∈ L, form σ J z x ∈ I' := fun z hz => ⟨z, hz, rfl⟩
  have hI0 : I' ≠ 0 := by
    intro h
    have := hmemI z₀ hz₀L
    rw [h, FractionalIdeal.mem_zero_iff] at this
    exact hz₀ this
  have hone : I' * I'⁻¹ = 1 := mul_inv_cancel₀ hI0
  let S : Submodule (𝓞 E) E :=
    { carrier := {e | ∃ y₀ : Fin n → E, form σ J y₀ x = e ∧ ∀ c ∈ I, c • y₀ ∈ L}
      add_mem' := by
        rintro _ _ ⟨y₁, rfl, h₁⟩ ⟨y₂, rfl, h₂⟩
        refine ⟨y₁ + y₂, by simp [form, add_dotProduct], fun c hc => ?_⟩
        rw [smul_add]; exact L.add_mem (h₁ c hc) (h₂ c hc)
      zero_mem' := ⟨0, by simp [form], fun c _ => by simp⟩
      smul_mem' := by
        rintro a _ ⟨y, rfl, h⟩
        refine ⟨a • y, ?_, fun c hc => ?_⟩
        · rw [← hφ, ← hφ, map_smul]
        · rw [smul_comm]; exact L.smul_mem a (h c hc) }
  have hle : I * ((I'⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) ≤ S := by
    refine Submodule.mul_le.mpr fun i hi j hj => ?_
    obtain ⟨z, hz, rfl⟩ := hi
    refine ⟨j • z, ?_, fun c hc => ?_⟩
    · rw [hφE, hφ, mul_comm]
    · have hcj : j * c ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :=
        (FractionalIdeal.mem_inv_iff hI0).mp hj c hc
      obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).mp hcj
      rw [smul_smul, mul_comm, ← ha, algebraMap_smul]
      exact L.smul_mem a hz
  have h1 : (1 : E) ∈ S := by
    apply hle
    have : (1 : E) ∈ ((I' * I'⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) := by
      rw [hone]; exact (FractionalIdeal.mem_one_iff _).mpr ⟨1, map_one _⟩
    rwa [FractionalIdeal.coe_mul] at this
  obtain ⟨y₀, hy₀, hL'⟩ := h1
  exact ⟨y₀, hy₀, fun z hz => hL' _ (hmemI z hz)⟩

end GlobalTheory.FormSection
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionHermitianLinearFormFgModuleStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_hermitianLinearForm_fg_module : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), L.FG →
    ∀ x : Fin n → E, (∃ z ∈ L, form σ J z x ≠ 0) →
    ∃ y₀ : Fin n → E, form σ J y₀ x = 1 ∧ ∀ z ∈ L, form σ J z x • y₀ ∈ L := by
  first | exact @GlobalTheory.FormSection.exists_section | exact GlobalTheory.FormSection.exists_section | (intros; apply GlobalTheory.FormSection.exists_section <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionOfHasHermitianSignature
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionOfHasHermitianSignature
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory.CartanEx

open scoped ComplexOrder

private lemma map_star_mul' {l m k : Type} [Fintype m] (X : Matrix l m ℂ) (Y : Matrix m k ℂ) :
    (X * Y).map star = X.map star * Y.map star := by
  ext i j; simp [Matrix.mul_apply, star_sum]

private lemma map_star_star {l m : Type} (X : Matrix l m ℂ) : (X.map star).map star = X := by
  ext i j; simp

private lemma map_star_one {m : Type} [DecidableEq m] : (1 : Matrix m m ℂ).map star = 1 := by
  ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]

private lemma star_mulVec_map {l m : Type} [Fintype m] (X : Matrix l m ℂ) (v : m → ℂ) :
    star (X *ᵥ v) = X.map star *ᵥ star v := by
  ext i; simp [Matrix.mulVec, dotProduct, star_sum]

theorem exists_isCartan : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (r s : ℕ), HasSig M r s → ∃ θ, IsCartan M θ := by
  intro n M r s ⟨hn, A, hA⟩
  set D : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ := Matrix.fromBlocks 1 0 0 (-1) with hD
  have hDD : D * D = 1 := by simp [hD, Matrix.fromBlocks_multiply]
  have hDT : Dᵀ = D := by simp [hD, Matrix.fromBlocks_transpose]
  have hDs : D.map star = D := by
    simp only [hD, Matrix.fromBlocks_map]
    congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> simp
  clear_value D
  set L := D * Aᵀ * M with hLdef
  clear_value L
  have hL : L * A.map star = 1 := by
    rw [hLdef, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Aᵀ, hA, hDD]
  have e : Fin n ≃ Fin r ⊕ Fin s := (finSumFinEquiv.trans (finCongr hn)).symm
  have hR : A.map star * L = 1 := (Matrix.mul_eq_one_comm_of_equiv e.symm).mp hL
  have hR' : A * L.map star = 1 := by
    have := congrArg (fun X => Matrix.map X star) hR
    simpa only [map_star_mul', map_star_star, map_star_one] using this
  have hL' : L.map star * A = 1 := by
    have := congrArg (fun X => Matrix.map X star) hL
    simpa only [map_star_mul', map_star_star, map_star_one] using this
  refine ⟨A * D * L.map star, ?_, ?_, ?_⟩
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (L.map star) A, hL', Matrix.one_mul, ← Matrix.mul_assoc D D, hDD, Matrix.one_mul, hR']
  · have hDL : D * L = Aᵀ * M := by
      rw [hLdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hDD, Matrix.one_mul]
    calc (A * D * L.map star)ᵀ * M * (A * D * L.map star).map star
        = (L.map star)ᵀ * D * (Aᵀ * M * A.map star) * (D * L) := by
          rw [Matrix.transpose_mul, Matrix.transpose_mul, map_star_mul', map_star_mul', map_star_star, hDs, hDT]
          simp only [Matrix.mul_assoc]
      _ = (A * L.map star)ᵀ * M := by
          rw [hA, hDL, Matrix.mul_assoc (L.map star)ᵀ D D, hDD, Matrix.mul_one, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = M := by rw [hR', Matrix.transpose_one, Matrix.one_mul]
  · intro x hx
    set a := L.map star *ᵥ x with ha_def
    have hxa : x = A *ᵥ a := by rw [ha_def, Matrix.mulVec_mulVec, hR', Matrix.one_mulVec]
    have ha : a ≠ 0 := by
      intro h; apply hx; rw [hxa, h, Matrix.mulVec_zero]
    have hθx : (A * D * L.map star) *ᵥ x = A *ᵥ (D *ᵥ a) := by
      rw [ha_def, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    have key : ∀ b c : Fin r ⊕ Fin s → ℂ, (A *ᵥ b) ⬝ᵥ M *ᵥ (A.map star *ᵥ c) = b ⬝ᵥ (Aᵀ * M * A.map star) *ᵥ c := by
      intro b c
      rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul,
        ← Matrix.dotProduct_mulVec, Matrix.mul_assoc]
    have hval : ((A * D * L.map star) *ᵥ x) ⬝ᵥ M *ᵥ star x = a ⬝ᵥ star a := by
      rw [hθx]
      conv_lhs => rw [hxa, star_mulVec_map]
      rw [key, hA, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hDT, hDD, Matrix.vecMul_one]
    rw [hval]
    exact (Complex.pos_iff.mp (Matrix.dotProduct_self_star_pos_iff.mpr ha)).1

end GlobalTheory.CartanEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionOfHasHermitianSignatureStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartanInvolution_of_hasHermitianSignature : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (r s : ℕ), HasSig M r s → ∃ θ, IsCartan M θ := by
  first | exact @GlobalTheory.CartanEx.exists_isCartan | exact GlobalTheory.CartanEx.exists_isCartan | (intros; apply GlobalTheory.CartanEx.exists_isCartan <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightDerivativeMultiplicityMapValueEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtSobolevContinuousOrbit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtSobolevContinuousOrbit
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SobOrbit

theorem hasDerivAt_sobCont_orbit : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (J : Matrix (Fin n) (Fin n) ℂ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Jᴴ = J → IsUnit J.det → IsURepOn (Formalism.QuantumDeterminants.UH J) π → ∀ v, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π v → ∀ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π ℓ → ∀ X ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0}, HasDerivAt (fun t : ℝ => ℓ (π (NormedSpace.exp (t • X)) v)) (ℓ (dRep π X v)) 0 :=
  fun _ _ _ _ _ _ _ hu hπ _ hv _ hℓ _ hX =>
    (GlobalTheory.UnitarySmVec.smFam_orbit hu hπ hv hX).hasDerivAt_form hu hπ hℓ

end GlobalTheory.SobOrbit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtSobolevContinuousOrbitStatement
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_sobolevContinuous_orbit : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (J : Matrix (Fin n) (Fin n) ℂ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Jᴴ = J → IsUnit J.det → IsURepOn (Formalism.QuantumDeterminants.UH J) π → ∀ v, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π v → ∀ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π ℓ → ∀ X ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0}, HasDerivAt (fun t : ℝ => ℓ (π (NormedSpace.exp (t • X)) v)) (ℓ (dRep π X v)) 0 := by
  first | exact @GlobalTheory.SobOrbit.hasDerivAt_sobCont_orbit | exact GlobalTheory.SobOrbit.hasDerivAt_sobCont_orbit | (intros; apply GlobalTheory.SobOrbit.hasDerivAt_sobCont_orbit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightDerivativeMultiplicityMapValueEq
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.MultDer

theorem smoothVec_zero {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (L : Set (Matrix (Fin n) (Fin n) ℂ)) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : SmoothVec L π 0 := by
  intro k Xs _
  simp only [map_zero]
  exact contDiff_const

theorem smoothVec_of_mem {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {w : M.H τ} (hw : w ∈ M.sm τ) : SmoothVec (lieAt V τ) (M.rep τ) w := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact smoothVec_zero _ _
  | add x y _ _ hx hy =>
    intro k Xs h
    simp only [map_add (f := _)]
    exact (hx k Xs h).add (hy k Xs h)
  | smul c x _ hx =>
    intro k Xs h
    simp only [map_smul]
    exact (hx k Xs h).const_smul c

theorem rder_eq : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsInfFam θ → IsMultMap θ M J χ T → ∀ (v : M.Vec) (τ : D.what₂.Tau), SmoothVec (lieAt V τ) (M.rep τ) (v τ : M.H τ) ∧ ∀ X ∈ lieAt V τ, ∃ u : M.sm τ, (u : M.H τ) = dRep (M.rep τ) X (v τ : M.H τ) ∧ Rder θ V τ X (T v) = T (Function.update v τ u) := by
  intro D θ V S M J χ T _ hT v τ
  have hs := smoothVec_of_mem M τ (v τ).2
  refine ⟨hs, fun X hX => ?_⟩
  have hH := GlobalTheory.SmoothAutCheck.gramAt_herm V τ
  have hU := GlobalTheory.SmoothAutCheck.gramAt_unit V τ
  have hπ := (GlobalTheory.HolDict.ModelRep.model_rep D V S M τ).2.1
  obtain ⟨h1, -, h3⟩ := GlobalTheory.T.smoothVectors_unitaryRep_stable_conj_skewAdjoint _ _ _ _ hH hU hπ _ hs
  refine ⟨⟨_, Submodule.subset_span (h3 X hX).1⟩, rfl, ?_⟩
  funext x
  obtain ⟨ℓ, hℓ, hℓT⟩ := hT.cont τ v x
  have hd := GlobalTheory.T.hasDerivAt_sobolevContinuous_orbit _ _ _ _ hH hU hπ _ hs ℓ hℓ X hX
  rw [← hℓT]
  have e : (fun t : ℝ => T v (x * oneP θ V τ X t)) =
      fun t : ℝ => ℓ (M.rep τ (NormedSpace.exp (t • X)) (v τ : M.H τ)) := by
    funext t
    have hg := GlobalTheory.SmoothAutCheck.exp_mem_UH hU hX t
    let w : M.sm τ := ⟨_, Submodule.subset_span (h1 _ hg)⟩
    have h4 := congrFun (hT.equiv τ _ hg v w rfl) x
    exact ((hℓT w).trans h4).symm
  show deriv (fun t : ℝ => T v (x * oneP θ V τ X t)) 0 = _
  rw [e]
  exact hd.deriv

end GlobalTheory.HolRead.MultDer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightDerivativeMultiplicityMapValueEqStatement
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_derivative_multiplicity_map_value_eq : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsInfFam θ → IsMultMap θ M J χ T → ∀ (v : M.Vec) (τ : D.what₂.Tau), SmoothVec (lieAt V τ) (M.rep τ) (v τ : M.H τ) ∧ ∀ X ∈ lieAt V τ, ∃ u : M.sm τ, (u : M.H τ) = dRep (M.rep τ) X (v τ : M.H τ) ∧ Rder θ V τ X (T v) = T (Function.update v τ u) := by
  first | exact @GlobalTheory.HolRead.MultDer.rder_eq | exact GlobalTheory.HolRead.MultDer.rder_eq | (intros; apply GlobalTheory.HolRead.MultDer.rder_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaPForms
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsThetaPOfIntegrable
open MeasureTheory Formalism.IndefR

namespace GlobalTheory.ThetaIntegralLinear

theorem exists_isThetaP_of_integrable {G' H' S' Sinf TK Tau : Type} [MeasurableSpace H'] [AddCommGroup S'] [Module ℂ S']
    [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup TK] [Module ℂ TK] [AddCommGroup Tau] [Module ℂ Tau]
    (ν : Measure H') (𝓕 : Set H') (th : G' → H' → S' →ₗ[ℂ] ℂ) (pt : Sinf →ₗ[ℂ] S')
    (io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf) (A : Submodule ℂ (H' → Tau))
    (hint : ∀ f : A, ∀ e g, IntegrableOn (fun h => th g h (pt (io e ((f : H' → Tau) h)))) 𝓕 ν) :
    ∃ thP, Lift.IsThetaP ν 𝓕 (fun g h s => th g h s) (fun s => pt s) io A thP := by

  refine ⟨LinearMap.mk₂ ℂ (fun f e g => ∫ h in 𝓕, th g h (pt (io e ((f : H' → Tau) h))) ∂ν)
    ?_ ?_ ?_ ?_, hint, ?_⟩
  · intro f₁ f₂ e
    funext g
    simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _)]
    exact integral_add (hint f₁ e g) (hint f₂ e g)
  · intro c f e
    funext g
    simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul]
    exact integral_const_mul c _
  · intro f e₁ e₂
    funext g
    simp only [map_add (f := _), LinearMap.add_apply, Pi.add_apply]
    exact integral_add (hint f e₁ g) (hint f e₂ g)
  · intro c f e
    funext g
    simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    exact integral_const_mul c _
  · intro f e g
    rfl

end GlobalTheory.ThetaIntegralLinear
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace Topology ComplexOrder
open GlobalTheory.GalLift

namespace GlobalTheory.ConjThetaIntegral

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem conjVal_one {D : D7} {σ : D.what₂.LL →+* ℂ} {a b : ℂ} (h : ConjVal σ a b) (ha : a = 1) : b = 1 := by
  obtain ⟨y, h1, h2⟩ := h
  have : y = 1 := D.what₂.embLL.injective (by rw [h1, ha, map_one])
  rw [← h2, this, map_one]

theorem ext_continuous {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : LevDat D.host.E ℂ V.rank) (χ' : (levEnv V β L).J →* ℂˣ) (hχ : ∀ k, (levEnv V β L).χ k = 1 → χ' k = 1)
    {f : Bridge.Gf V → c.W}
    (hf : f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J χ') : Continuous (c.ext f) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  exact GlobalTheory.ThetaIntegrand.form_continuous (finHom V).rangeRestrict (GQ V) c.ρ hc.2.2.1
    ((GlobalTheory.ThetaIntegrand.eventually_level V β L).mono fun _ h => h.elim fun hk h1 => ⟨hk, hχ _ h1⟩) hf

theorem IsThetaP₂ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) (hs : S.SigOK)
    (hp : S.IsPosDef) (c : CoefA S) (hc : c.Is) (β : GL (Fin S.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank)
    (χ' : (levEnv S β L).J →* ℂˣ) (hχ : ∀ k, (levEnv S β L).χ k = 1 → χ' k = 1)
    {X : Type} [AddCommGroup X] [Module ℂ X] (e : X →ₗ[ℂ] (Bridge.Gf S → c.W))
    (he : ∀ x, e x ∈ Bridge.AdForms (Bridge.ratF S) c.coef.ρ (levEnv S β L).J χ')
    (pt : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ)) (hpt : ∀ P, IsThetaFunO ψ S T (pt P))
    {TK : Type} [AddCommGroup TK] [Module ℂ TK]
    (io : TK →ₗ[ℂ] c.W →ₗ[ℂ] PolF D T.rank S.rank) {K : Subgroup (GL (Fin S.rank) (Lev.EAf D))} {μ : Measure (GA D S)}
    {𝓕 : Set (GA D S)} (hμ : IsMeasDef S K μ 𝓕) :
    ∃ thP, Lift.IsThetaP μ 𝓕 (fun g h φ => thetaKO om h g φ) (fun P => pt P) io (LinearMap.range (c.ext ∘ₗ e)) thP := by
  have hpos : ∀ τ, (gramAt D S τ).PosDef := fun τ => by
    have := hs (tauE D τ)
    rw [hp] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  refine GlobalTheory.ThetaIntegralLinear.exists_isThetaP_of_integrable μ 𝓕
    (fun g h => LinearMap.proj (R := ℂ) (φ := fun _ : WO S T => ℂ) 0 ∘ₗ om (h, g)) pt io _ ?_
  rintro ⟨_, x, rfl⟩ v g
  exact GlobalTheory.DefiniteQuotient.integrableOn_theta D ψ hom.std S T χS χT om hom hpos c.W (pt ∘ₗ io v)
    (fun w => hpt _) _ (ext_continuous c hc β L χ' hχ (he x)) (GlobalTheory.ThetaIntegrand.ext_invariant c (he x)) μ 𝓕 hμ.1.1 hμ.2 g

end GlobalTheory.ConjThetaIntegral

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularFunctionsPthPowerTwist
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI


open CategoryTheory AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.DI.pow_mul_locRing_subset_regularAt {X : Scheme.{0}} [IsIntegral X] (p : ℕ)
    (G H : _root_.GlobalTheory.Cartier.CartierDiv X) (y : X) (h : (H - p • G).Eff) :
    {z : X.functionField | ∃ c ∈ {c : X.functionField | G.RegularAt y c},
      ∃ b ∈ _root_.GlobalTheory.LogDR.locRing y, z = c ^ p * b} ⊆
      {c | H.RegularAt y c} := by
  rintro z ⟨c, ⟨g, hg, hcg⟩, b, hb, rfl⟩
  obtain ⟨k, hk, hk1⟩ := h y
  have hH : H.IsEqn y (k * g ^ p) := by
    have := hk.add (hg.nsmul p)
    simpa using this
  refine ⟨k * g ^ p, hH, ?_⟩
  rw [← _root_.GlobalTheory.LogDR.mem_locRing] at hcg hk1 ⊢
  have hz : c ^ p * b * ((k * g ^ p : (X.functionField)ˣ) : X.functionField) =
      (c * g) ^ p * b * (1 * k) := by
    push_cast
    ring
  rw [hz]
  exact mul_mem (mul_mem (pow_mem hcg p) hb) hk1

end GlobalTheory.DI
end
