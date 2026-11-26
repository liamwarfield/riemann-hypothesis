module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToricTorsionPointOfLatticeCharacter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTransgressionFormsFrameInvariant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolyRepInducedBundleAndMetric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSimilitudeFixingPointEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorPosDefProperties
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleIsometryCalculus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffFiniteKer

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedTorsionPointTorusExtensionEqOfLiesOver
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedTorsionPointTorusExtensionEqOfLiesOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.Poinc.Sep.LiesUniq

theorem frame_unique {R : Type} [CommRing R] [IsDomain R] [CharZero R] {I : Ideal R} (hA : AdmBase R I)
    {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (hG : IsSemiAbelian G) (U : Unif I D A G) {w₀ : W0 U.toUnifPre} (hw₀ : w₀.IsGen) {F : Type} [Field F]
    [Algebra (FractionRing R) F] {g : GtPtF D.toPre F} {w w' : Frm D.toPre F 1 g.b} {x : TFK (R := R) F ⟶ A.A}
    {fr : FrAt x} (hw : w.IsGen) (hw' : w'.IsGen) (hfr : fr.IsGen) (h : LiesOver U.toUnifPre w₀ g w x fr)
    (h' : LiesOver U.toUnifPre w₀ g w' x fr) :
    ∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J = val w' (𝟙 _) z J := by
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hbij := (expBijF_and_expandsF_lin hL R _ hA D A G hG U).1 F
  obtain ⟨lam, -, hlam⟩ := CoefBasic.exists_frame_ratio hw hw'
  have hk : ∀ k : ℕ, 4 ≤ k → lam ^ k = 1 := fun k hk => by
    obtain ⟨W, hW, hWv⟩ := TorsionValue.exists_frm_pow w hw k
    obtain ⟨W', hW', hWv'⟩ := TorsionValue.exists_frm_pow w' hw' k
    obtain ⟨s, e, he, hs⟩ := NonVan.exists_sec_ne_zero hL R A F k hk x fr hfr
    obtain ⟨s', hs', -⟩ := (hbij k (by omega) w₀ hw₀).1 s
    have S₁ := h k (by omega) W hWv hW s s' e hs' hs
    have S₂ := h' k (by omega) W' hWv' hW' s s' e hs' hs
    have sc := TorsionValue.coef_scale (w' := W') hW (c := lam ^ k) (fun z J hJ => by
      rw [hWv z J hJ, hWv' z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hlam z J hJ, mul_pow,
        CoefBasic.cst_eq, CoefBasic.cst_eq, map_pow]) s'
    have S₃ := (GlobalTheory.AdicSum.sumF_calculus R I hA F _ _ _ e e).2.1 S₁ S₁ (lam ^ k - 1)
    have e₁ : (fun i => (lam ^ k - 1) * coef s' g W i + coef s' g W i) = coef s' g W' := funext fun i => by
      rw [sc]; ring
    rw [e₁] at S₃
    have e₂ := (GlobalTheory.AdicSum.sumF_calculus R I hA F _ _ (coef s' g W') _ _).1 S₃ S₂
    exact sub_eq_zero.1 ((mul_eq_zero.1 (add_eq_right.1 e₂)).resolve_right he)
  have h1 : lam = 1 := by
    have := hk 5 (by norm_num)
    rwa [pow_succ, hk 4 le_rfl, _root_.one_mul] at this
  intro z J hJ
  have := hlam z J hJ
  rw [h1, CoefBasic.cst_eq, map_one, _root_.one_mul] at this
  exact Units.ext this.symm

theorem eq_of_liesOver : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ N : ℕ, 1 ≤ N → ∀ (g g' : GtPtF D.toPre (FractionRing V)) (w : Frm D.toPre (FractionRing V) 1 g.b) (w' : Frm D.toPre (FractionRing V) 1 g'.b) (x : TFK (R := V) (FractionRing V) ⟶ A.A) (fr : FrAt x), (∃ o, GtPtF.IsNsmul N g o ∧ o.IsZero) → (∃ o, GtPtF.IsNsmul N g' o ∧ o.IsZero) → w.IsGen → w'.IsGen → fr.IsGen → LiesOver U.toUnifPre w₀ g w x fr → LiesOver U.toUnifPre w₀ g' w' x fr → g = g' ∧ ∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J = val w' (𝟙 _) z J := by
  intro V _ _ _ hCN D A G _ _ hG U w₀ hw₀ N hN g g' w w' x fr hg hg' hw hw' hfr h h'
  haveI : CharZero V := hCN.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hA : AdmBase V (maximalIdeal V) := ⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩
  have hB := D.tau_bimult
  obtain ⟨p, hy, rfl, hp⟩ := GlobalTheory.T.exists_torus_pair_of_torsion_point_over V hCN D A G hG U w₀ hw₀ N hN g w x fr hg hw hfr h
  obtain ⟨p', hy', rfl, hp'⟩ := GlobalTheory.T.exists_torus_pair_of_torsion_point_over V hCN D A G hG U w₀ hw₀ N hN g' w' x fr hg' hw' hfr h'
  have hf : (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp
      (algebraMap (FractionRing V) (FractionRing V)) = algebraMap _ _ := RingHom.comp_id _
  have hq := (GlobalTheory.TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow U hN
    ((GlobalTheory.TorusExt.qkExt_iff hB _ hf p _).2 rfl) x).1 hp
  have hq' := (GlobalTheory.TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow U hN
    ((GlobalTheory.TorusExt.qkExt_iff hB _ hf p' _).2 rfl) x).1 hp'
  have he := GlobalTheory.TorsionMapInj.qkToAk_injective hL.1 hL.2.1 V _ hA D A G hG U _ N hN _ _ _ hq hq'
  obtain ⟨z, hz, hz'⟩ := (GlobalTheory.TorusExt.equiv_iff hB _ _).1 he
  have e : p.g = p'.g := by
    letI := GlobalTheory.TorusExt.gtGroup D.toPre (AlgebraicClosure (FractionRing V))
    have hz₁ : p'.y = p.y + N • z := hz
    rw [hy, hy', zero_add, ← natCast_zsmul] at hz₁
    obtain rfl : z = 0 := (smul_eq_zero.1 hz₁.symm).resolve_left (by exact_mod_cast (by omega : N ≠ 0))
    rw [map_zero, add_zero] at hz'
    exact GlobalTheory.Balanced.gtExt_injective _ hf D.toPre hz'.symm
  obtain ⟨y, g, hg₁⟩ := p
  obtain ⟨y', g', hg₁'⟩ := p'
  dsimp only at e
  subst e
  exact ⟨rfl, frame_unique hA hG U hw₀ hw hw' hfr h h'⟩

end GlobalTheory.Poinc.Sep.LiesUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedTorsionPointTorusExtensionEqOfLiesOverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framedTorsionPoint_torusExtension_eq_of_liesOver : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ N : ℕ, 1 ≤ N → ∀ (g g' : GtPtF D.toPre (FractionRing V)) (w : Frm D.toPre (FractionRing V) 1 g.b) (w' : Frm D.toPre (FractionRing V) 1 g'.b) (x : TFK (R := V) (FractionRing V) ⟶ A.A) (fr : FrAt x), (∃ o, GtPtF.IsNsmul N g o ∧ o.IsZero) → (∃ o, GtPtF.IsNsmul N g' o ∧ o.IsZero) → w.IsGen → w'.IsGen → fr.IsGen → LiesOver U.toUnifPre w₀ g w x fr → LiesOver U.toUnifPre w₀ g' w' x fr → g = g' ∧ ∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J = val w' (𝟙 _) z J := by
  first | exact @GlobalTheory.Poinc.Sep.LiesUniq.eq_of_liesOver | exact GlobalTheory.Poinc.Sep.LiesUniq.eq_of_liesOver | (intros; apply GlobalTheory.Poinc.Sep.LiesUniq.eq_of_liesOver <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormDelDbarSmooth
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnCoefficientsDelOperatorDbarOperator
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnCoefficientsDelOperatorDbarOperator
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

set_option autoImplicit false

namespace GlobalTheory.CxForm.SmoothCoef

theorem contDiffOn_del_dir {n : ℕ} {s : Set (V n)} {f : V n → ℂ} (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) (e : V n) :
    ContDiffOn ℝ ∞ (fun v => del f v e) s := by
  have h : ContDiffOn ℝ ∞ (fun v => fderiv ℝ f v) s := hf.fderiv_of_isOpen hs (by simp)
  simp only [del_apply]
  exact ((h.clm_apply contDiffOn_const).sub ((h.clm_apply contDiffOn_const).const_smul _)).const_smul _

theorem contDiffOn_dbar_dir {n : ℕ} {s : Set (V n)} {f : V n → ℂ} (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) (e : V n) :
    ContDiffOn ℝ ∞ (fun v => dbar f v e) s := by
  have h : ContDiffOn ℝ ∞ (fun v => fderiv ℝ f v) s := hf.fderiv_of_isOpen hs (by simp)
  simp only [dbar_apply]
  exact ((h.clm_apply contDiffOn_const).add ((h.clm_apply contDiffOn_const).const_smul _)).const_smul _

theorem contDiffOn_coef : ∀ (n : ℕ) (s : Set (V n)) (F : V n → Alt n), IsOpen s →
    (∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (F v) S) s) →
    ∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (delAt F v) S) s ∧
      ContDiffOn ℝ ∞ (fun v => (bas n).repr (dbarAt F v) S) s := by
  intro n s F hs hF U
  constructor
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [delAt, coefwise, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finset.sum_apply',
      Finsupp.smul_apply, smul_eq_mul]
      exact ContDiffOn.sum fun a _ => ContDiffOn.sum fun S _ => (contDiffOn_del_dir hs (hF S) _).mul contDiffOn_const
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [dbarAt, coefwise, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finset.sum_apply',
      Finsupp.smul_apply, smul_eq_mul]
      exact ContDiffOn.sum fun a _ => ContDiffOn.sum fun S _ => (contDiffOn_dbar_dir hs (hF S) _).mul contDiffOn_const

end GlobalTheory.CxForm.SmoothCoef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnCoefficientsDelOperatorDbarOperatorStatement
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffOn_coefficients_delOperator_dbarOperator : ∀ (n : ℕ) (s : Set (V n)) (F : V n → Alt n), IsOpen s →
    (∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (F v) S) s) →
    ∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (delAt F v) S) s ∧ ContDiffOn ℝ ∞ (fun v => (bas n).repr (dbarAt F v) S) s := by
  first | exact @GlobalTheory.CxForm.SmoothCoef.contDiffOn_coef | exact GlobalTheory.CxForm.SmoothCoef.contDiffOn_coef | (intros; apply GlobalTheory.CxForm.SmoothCoef.contDiffOn_coef <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormDelDbarSmooth
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

set_option autoImplicit false

namespace GlobalTheory.CxForm.HolAtlas

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem loc_eventuallyEq_pull {α : A.Fld} (hα : A.IsForm α) (x x' : A.Pt) (h : x.pt = x'.pt) :
    A.loc α x.1.1 =ᶠ[𝓝 x.crd] fun y => pull (fderiv ℂ (x'.ch ∘ x.ch.symm) y) (A.loc α x'.1.1 ((x'.ch ∘ x.ch.symm) y)) := by
  have hU : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) :=
    x.ch.isOpen_inter_preimage_symm x'.ch.open_source
  have hxU : x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source :=
    ⟨x.ch.map_source x.2, by simp only [Set.mem_preimage, x.ch.left_inv x.2, h]; exact x'.2⟩
  refine Filter.eventually_of_mem (hU.mem_nhds hxU) fun y hy => ?_
  show A.loc α x.1.1 y = pull (fderiv ℂ (x'.ch ∘ x.ch.symm) y) (A.loc α x'.1.1 ((x'.ch ∘ x.ch.symm) y))
  let p : A.Pt := ⟨(x.1.1, x.ch.symm y), x.ch.map_target hy.1⟩
  let p' : A.Pt := ⟨(x'.1.1, x.ch.symm y), hy.2⟩
  have e1 : A.loc α x.1.1 y = α p := by rw [HolAtlas.loc, dite_eq_left hy.1]
  have e2 : A.loc α x'.1.1 ((x'.ch ∘ x.ch.symm) y) = α p' := A.loc_crd α p'
  have e3 : p.crd = y := x.ch.right_inv hy.1
  rw [e1, e2, hα.compat p p' rfl]
  show pull (fderiv ℂ (x'.ch ∘ x.ch.symm) p.crd) (α p') = _
  rw [e3]

theorem chg_facts (x x' : A.Pt) (h : x.pt = x'.pt) :
    IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) ∧ x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source ∧
    DifferentiableOn ℂ (x'.ch ∘ x.ch.symm) (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) ∧
    (x'.ch ∘ x.ch.symm) x.crd = x'.crd :=
  ⟨x.ch.isOpen_inter_preimage_symm x'.ch.open_source,
    ⟨x.ch.map_source x.2, by simp only [Set.mem_preimage, x.ch.left_inv x.2, h]; exact x'.2⟩,
    A.holo x.1.1 x'.1.1, by simp only [Function.comp_apply, x.ch.left_inv x.2, h]⟩

theorem loc_diffAt {α : A.Fld} (hα : A.IsForm α) (x : A.Pt) (S : Finset (Fin (n + n))) :
    DifferentiableAt ℝ (fun y => (bas n).repr (A.loc α x.1.1 y) S) x.crd :=
  ((hα.smooth x.1.1 S).contDiffAt (x.ch.open_target.mem_nhds (x.ch.map_source x.2))).differentiableAt (by simp)

theorem isForm_del_dbar {α : A.Fld} (hα : A.IsForm α) : A.IsForm (A.del α) ∧ A.IsForm (A.dbar α) := by
  have hloc : ∀ (T : (V n → Alt n) → V n → Alt n) (i : A.ι) (v : V n), v ∈ (A.e i).target →
      A.loc (fun x => T (A.loc α x.1.1) x.crd) i v = T (A.loc α i) v := by
    intro T i v hv
    rw [HolAtlas.loc, dite_eq_left hv]
    show T (A.loc α i) ((A.e i) ((A.e i).symm v)) = _
    rw [(A.e i).right_inv hv]
  refine ⟨⟨fun i S => ?_, fun x x' h => ?_⟩, ⟨fun i S => ?_, fun x x' h => ?_⟩⟩
  · exact ((GlobalTheory.T.contDiffOn_coefficients_delOperator_dbarOperator n _ (A.loc α i) (A.e i).open_target (hα.smooth i) S).1).congr fun v hv => by
      rw [show A.del α = fun x => delAt (A.loc α x.1.1) x.crd from rfl, hloc delAt i v hv]
  · obtain ⟨hU, hxU, hτ, hτx⟩ := chg_facts A x x' h
    have hβ : ∀ S, DifferentiableAt ℝ (fun y => (bas n).repr (A.loc α x'.1.1 y) S) ((x'.ch ∘ x.ch.symm) x.crd) := by
      rw [hτx]; exact loc_diffAt A hα x'
    show delAt (A.loc α x.1.1) x.crd = pull _ (delAt (A.loc α x'.1.1) x'.crd)
    rw [((GlobalTheory.T.delOperatorAt_dbarOperatorAt_linear_local n x.crd).2.2.2.1 _ _ (loc_eventuallyEq_pull A hα x x' h)).1,
      (GlobalTheory.T.del_dbar_chainRule_holomorphicPullback n n _ _ _ x.crd hU hxU hτ hβ).1, hτx]
  · exact ((GlobalTheory.T.contDiffOn_coefficients_delOperator_dbarOperator n _ (A.loc α i) (A.e i).open_target (hα.smooth i) S).2).congr fun v hv => by
      rw [show A.dbar α = fun x => dbarAt (A.loc α x.1.1) x.crd from rfl, hloc dbarAt i v hv]
  · obtain ⟨hU, hxU, hτ, hτx⟩ := chg_facts A x x' h
    have hβ : ∀ S, DifferentiableAt ℝ (fun y => (bas n).repr (A.loc α x'.1.1 y) S) ((x'.ch ∘ x.ch.symm) x.crd) := by
      rw [hτx]; exact loc_diffAt A hα x'
    show dbarAt (A.loc α x.1.1) x.crd = pull _ (dbarAt (A.loc α x'.1.1) x'.crd)
    rw [((GlobalTheory.T.delOperatorAt_dbarOperatorAt_linear_local n x.crd).2.2.2.1 _ _ (loc_eventuallyEq_pull A hα x x' h)).2,
      (GlobalTheory.T.del_dbar_chainRule_holomorphicPullback n n _ _ _ x.crd hU hxU hτ hβ).2, hτx]

end GlobalTheory.CxForm.HolAtlas

theorem GlobalTheory.CxForm.isForm_del_dbar : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (α : A.Fld), A.IsForm α →
    A.IsForm (A.del α) ∧ A.IsForm (A.dbar α) :=
  fun _ _ _ A _ hα => A.isForm_del_dbar hα
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormDelDbarSmoothStatement
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holAtlas_isForm_del_dbar_smooth : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (α : A.Fld), A.IsForm α →
    A.IsForm (A.del α) ∧ A.IsForm (A.dbar α) := by
  first | exact @GlobalTheory.CxForm.isForm_del_dbar | exact GlobalTheory.CxForm.isForm_del_dbar | (intros; apply GlobalTheory.CxForm.isForm_del_dbar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlaggedBundleMetricPullGramRefinement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlaggedBundleMetricPullGramRefinement
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
open GlobalTheory.GoodMetric.RepBundle

namespace GlobalTheory.ChernCalc

theorem isMetricFr_pullGram : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → IsMetricFr E' (pullGram E H φ f hf) := by
  intro F _ σ X Y ι _ m E E' φ f hf hR H hH
  have key := GlobalTheory.T.pulled_back_gram_matrices_independent_of_frame F σ X Y ι m E E' φ f hf hR H hH
  refine ⟨fun y B hB τ => ?_, fun y B hB τ i j => ?_, fun y B hB B' hB' τ => ?_⟩
  · obtain ⟨ψ, hψ⟩ := exists_ratVal_hom (X := Y) (σ := σ) y
    obtain ⟨A, hA⟩ := E.nonempty (f (under y))
    have hT := ((hR.sub _ B hB A hA).map_of (ratVal · y) ψ hψ).det_ne τ
    rw [(key y).2 A hA B hB τ]
    exact (hH.posDef _ mem_ptsIn_top A ((key y).1 ▸ hA) τ).mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hT.isUnit))
  · obtain ⟨A, hA⟩ := E.nonempty (f (under y))
    have hA' : A ∈ E.S (under (ptMap σ f hf y)) := (key y).1 ▸ hA
    have hC := hR.sub _ B hB A hA
    have hc : Continuous (ptMap σ f hf) := GlobalTheory.Points.PtsOver.continuous_map f hf _
    have hev : ∀ᶠ z in 𝓝 y, pullGram E H φ f hf B z τ = (B * (A.map φ)⁻¹).map (ratVal · z) τ *
        H A (ptMap σ f hf z) τ * ((B * (A.map φ)⁻¹).map (ratVal · z) τ)ᴴ := by
      filter_upwards [hc.continuousAt.eventually (GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m 0 E _ A hA'),
        GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ Y ι m m E' y B hB] with z hAz hBz
      exact (key z).2 A ((key z).1 ▸ hAz) B hBz τ
    have hT : ∀ k l, CS (fun z => (B * (A.map φ)⁻¹).map (ratVal · z) τ k l) y := fun k l =>
      cs_ratVal (mem_O_ratOf.1 ((hC τ).1 k l))
    have hS : ∀ k l, CS (fun z => H A (ptMap σ f hf z) τ k l) y := fun k l =>
      ⟨CInfAt.pull f hf (hH.smooth _ mem_ptsIn_top A hA' τ k l).1,
        CInfAt.pull f hf (hH.smooth _ mem_ptsIn_top A hA' τ k l).2⟩
    exact CS.congr (v := fun z => pullGram E H φ f hf B z τ i j) (cs_conj_entry hT hS i j)
      (hev.mono fun z hz => by simp only [hz])
  · obtain ⟨ψ, hψ⟩ := exists_ratVal_hom (X := Y) (σ := σ) y
    obtain ⟨A, hA⟩ := E.nonempty (f (under y))
    have e := Par.map_mul_of ((Fr.mem_iff hB).1 hB') (hR.sub _ B hB A hA) (ratVal · y) ψ hψ
    rw [mul_assoc, ← mul_assoc B⁻¹, Mat.inv_mul (Fr.det_ne hB), one_mul] at e
    rw [(key y).2 A hA B hB τ, (key y).2 A hA B' hB' τ, e, Pi.mul_apply, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]

end GlobalTheory.ChernCalc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlaggedBundleMetricPullGramRefinementStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFlaggedBundleMetric_pullGram_refinement : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → IsMetricFr E' (pullGram E H φ f hf) := by
  first | exact @GlobalTheory.ChernCalc.isMetricFr_pullGram | exact GlobalTheory.ChernCalc.isMetricFr_pullGram | (intros; apply GlobalTheory.ChernCalc.isMetricFr_pullGram <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenFlagBundleCellAndCoordsRegular
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenFlagBundleCellAndCoordsRegular
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2

theorem isOpen_setOf_mem_frames {F Ω ι : Type} [Field F] [Field Ω] [Algebra F Ω] [Finite ι] {m k : ι → ℕ}
    {M : GlobalTheory.ZH.RatModel F Ω} (S : Fr M m k) (B : Mat m Ω) : IsOpen {z : M.Z | B ∈ S.S z} := by
  have hP (g : Mat m Ω) : IsOpen {z : M.Z | Par k (M.O z).toSubring g} := by
    have : {z : M.Z | Par k (M.O z).toSubring g} = ⋂ τ, ((⋂ i, ⋂ j, {z : M.Z | g τ i j ∈ M.O z}) ∩
        ({_z : M.Z | (g τ).det ≠ 0} ∩ ({z : M.Z | (g τ).det⁻¹ ∈ M.O z} ∩
          {_z : M.Z | ∀ i j : Fin (m τ), (i : ℕ) < k τ → i < j → g τ i j = 0}))) := by
      ext z
      simp only [Par, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
      rfl
    rw [this]
    exact isOpen_iInter_of_finite fun τ => (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      M.isOpen_setOf_mem_O _).inter (isOpen_const.inter ((M.isOpen_setOf_mem_O _).inter isOpen_const))
  refine isOpen_iff_forall_mem_open.2 fun z hz => ?_
  obtain ⟨U, A, hzU, -, hU⟩ := S.loc z
  exact ⟨(U : Set M.Z) ∩ {z' | Par k (M.O z').toSubring (B * A⁻¹)}, fun w hw => (hU w hw.1 B).2 hw.2,
    U.isOpen.inter (hP _), hzU, (hU z hzU B).1 hz⟩

theorem isOpen_inCell_and_regAt : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ)
    (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f →
    ∀ (A : Mat m X.Fn) (u : Cell m → Y.Fn), IsOpen {y : Y.X | InCell E E' φ f A u y} ∧
      ∀ y, InCell E E' φ f A u y → ∀ j, RegAt y (u j) := by
  intro F _ X Y ι _ m E E' φ f hR A u
  refine ⟨((isOpen_setOf_mem_frames E A).preimage f.continuous).inter (isOpen_setOf_mem_frames E' _), ?_⟩
  rintro y ⟨hA, hu⟩ ⟨τ, ⟨b, a⟩, hab⟩
  have h := hR.sub y _ hu A hA
  have hd : ∀ τ, (A.map φ τ).det ≠ 0 := fun τ => by
    have := Mat.det_map A (φ : X.Fn →+* Y.Fn) τ
    exact this.trans_ne ((map_ne_zero _).2 (Fr.det_ne hA τ))
  rw [mul_assoc, Mat.mul_inv hd, mul_one] at h
  have h2 := (h τ).1 a b
  have hab' : a < b := hab
  have e : upM u τ a b = u ⟨τ, ⟨(b, a), hab⟩⟩ := by
    simp only [upM, upU, Matrix.of_apply, dif_pos hab']
  rw [e] at h2
  exact mem_O_ratOf.1 h2

end GlobalTheory.FlagCell2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenFlagBundleCellAndCoordsRegularStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_flagBundleCell_and_coords_regular : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (A : Mat m X.Fn) (u : Cell m → Y.Fn), IsOpen {y : Y.X | InCell E E' φ f A u y} ∧ ∀ y, InCell E E' φ f A u y → ∀ j, RegAt y (u j) := by
  first | exact @GlobalTheory.FlagCell2.isOpen_inCell_and_regAt | exact GlobalTheory.FlagCell2.isOpen_inCell_and_regAt | (intros; apply GlobalTheory.FlagCell2.isOpen_inCell_and_regAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtFlagCellGradedLinePotential
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtFlagCellGradedLinePotential
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.CellPotSmooth

theorem upM_fb_contDiffAt_two {ι : Type} {m : ι → ℕ} {n d : ℕ} (ε : Fin n ≃ Fin d ⊕ Cell m) (τ : ι) (w : V n) :
    MContDiffAt 2 (fun w => upM (fb ε w) τ) w := by
  intro a b
  simp only [upM, upU, Matrix.of_apply, fb]
  split_ifs with h1 h2
  · exact ((EuclideanSpace.proj (𝕜 := ℂ) (ε.symm (.inr ⟨τ, ⟨(b, a), h1⟩⟩))).contDiff.restrict_scalars ℝ).contDiffAt
  · exact contDiffAt_const
  · exact contDiffAt_const

theorem G_bsL_smooth {ι : Type} {m : ι → ℕ} {n d : ℕ} (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (w : V n) (τ : ι)
    (hG : MContDiffAt 2 (fun v => G v τ) (bsL ε w)) : MContDiffAt 2 (fun w => G (bsL ε w) τ) w := by
  intro a b
  exact (hG a b).comp w (((bsL ε).contDiff.restrict_scalars ℝ).contDiffAt)

theorem upU_isUnit {s : ℕ} (y : Low s → ℂ) : IsUnit (upU y) := by
  rw [Matrix.isUnit_iff_isUnit_det, upU_eq, Matrix.det_transpose, GlobalTheory.FlagFibre.det_uni]
  exact isUnit_one

theorem leadMinor_re_pos {s : ℕ} {A : Matrix (Fin s) (Fin s) ℂ} (hA : A.PosDef) (j : ℕ) : 0 < (leadMinor A j).re := by
  have h := (hA.submatrix (Subtype.val_injective (p := fun a : Fin s => (a : ℕ) < j))).det_pos
  exact (Complex.pos_iff.1 h).1

theorem cellPot_contDiffAt : ∀ (ι : Type) (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (w : V n) (x : Root m), (G (bsL ε w) x.1).PosDef → MContDiffAt 2 (fun v => G v x.1) (bsL ε w) → ContDiffAt ℝ 2 (cellPot ε G x) w ∧ 0 < grD (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2 := by
  intro ι m n d ε G w x hP hG
  set A : V n → Matrix (Fin (m x.1)) (Fin (m x.1)) ℂ :=
    fun w => upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ with hAdef
  have hA : MContDiffAt 2 A w :=
    ((upM_fb_contDiffAt_two ε x.1 w).mul (G_bsL_smooth ε G w x.1 hG)).mul (upM_fb_contDiffAt_two ε x.1 w).conjTranspose
  have hPA : (A w).PosDef := by
    refine hP.mul_mul_conjTranspose_same ?_
    exact Matrix.vecMul_injective_iff_isUnit.2 (upU_isUnit _)
  have hm : ∀ j : ℕ, ContDiffAt ℝ 2 (fun w => (leadMinor (A w) j).re) w := fun j =>
    Complex.reCLM.contDiff.contDiffAt.comp w (hA.submatrix _ _).det
  have h1 := leadMinor_re_pos hPA (x.2 + 1)
  have h0 := leadMinor_re_pos hPA x.2
  have hpos : 0 < grD (A w) x.2 := div_pos h1 h0
  refine ⟨?_, hpos⟩
  have hd : ContDiffAt ℝ 2 (fun w => grD (A w) x.2) w := (hm _).div (hm _) h0.ne'
  exact (hd.log hpos.ne').neg

end GlobalTheory.CellPotSmooth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtFlagCellGradedLinePotentialStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffAt_flagCellGradedLinePotential : ∀ (ι : Type) (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (w : V n) (x : Root m), (G (bsL ε w) x.1).PosDef → MContDiffAt 2 (fun v => G v x.1) (bsL ε w) → ContDiffAt ℝ 2 (cellPot ε G x) w ∧ 0 < grD (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2 := by
  first | exact @GlobalTheory.CellPotSmooth.cellPot_contDiffAt | exact GlobalTheory.CellPotSmooth.cellPot_contDiffAt | (intros; apply GlobalTheory.CellPotSmooth.cellPot_contDiffAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyDimLeOfFiniteAndOfSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyDimLeOfFiniteAndOfSurjective
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AV.DimLe

section

attribute [local instance low] specializationOrder

theorem topologicalKrullDim_le_of_isFinite {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] :
    topologicalKrullDim X ≤ topologicalKrullDim Y := by
  have eX : topologicalKrullDim X = Order.krullDim X :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))
  have eY : topologicalKrullDim Y = Order.krullDim Y :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))
  rw [eX, eY]
  refine Order.krullDim_le_of_strictMono (f : X → Y) fun a b hab => ?_
  have h1 : f b ⤳ f a := Specializes.map hab.le f.continuous
  refine lt_of_le_of_ne h1 fun e => hab.ne ?_
  exact ((GlobalTheory.finite_fibre_and_eq_of_specializes_of_isFinite Y X f inferInstance (f a)).2 b a
    e.symm rfl hab.le).symm

theorem topologicalKrullDim_le_of_surjective_of_isClosedMap {X Y : Scheme.{0}} (f : X ⟶ Y)
    (hs : Function.Surjective f) (hc : IsClosedMap f) :
    topologicalKrullDim Y ≤ topologicalKrullDim X := by
  have eX : topologicalKrullDim X = Order.krullDim X :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))
  have eY : topologicalKrullDim Y = Order.krullDim Y :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))
  rw [eX, eY, Order.krullDim_eq_iSup_height]
  refine iSup_le fun y => ?_
  obtain ⟨x, rfl⟩ := hs y
  have h : Order.height (f x) ≤ Order.height x :=
    ENat.forall_natCast_le_iff_le.mp fun n hn =>
      GlobalTheory.GenFibreDim.le_height_of_specializingMap hc.specializingMap n x hn
  exact (WithBot.coe_le_coe.mpr h).trans (Order.height_le_krullDim x)

end

theorem dim_le : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B),
    (IsFinite f.hom.left → A.dim ≤ B.dim) ∧ (Surjective f.hom.left → B.dim ≤ A.dim) := by
  intro K _ A B f
  have hA := GlobalTheory.T.topologicalKrullDim_abVar_eq_dim K A
  have hB := GlobalTheory.T.topologicalKrullDim_abVar_eq_dim K B
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · have h := topologicalKrullDim_le_of_isFinite f.hom.left
    rw [hA, hB] at h
    exact_mod_cast h
  · have := A.ab.proper
    have := B.ab.proper
    have hw : f.hom.left ≫ B.X.hom = A.X.hom := Over.w f.hom
    have : UniversallyClosed (f.hom.left ≫ B.X.hom) := by rw [hw]; infer_instance
    have : UniversallyClosed f.hom.left := UniversallyClosed.of_comp_of_isSeparated f.hom.left B.X.hom
    have h := topologicalKrullDim_le_of_surjective_of_isClosedMap f.hom.left
      hf.surj f.hom.left.isClosedMap
    rw [hA, hB] at h
    exact_mod_cast h

end GlobalTheory.AV.DimLe
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyDimLeOfFiniteAndOfSurjectiveStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_dim_le_of_finite_and_of_surjective : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), (IsFinite f.hom.left → A.dim ≤ B.dim) ∧ (Surjective f.hom.left → B.dim ≤ A.dim) := by
  first | exact @GlobalTheory.AV.DimLe.dim_le | exact GlobalTheory.AV.DimLe.dim_le | (intros; apply GlobalTheory.AV.DimLe.dim_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelCoverMatrices
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor GlobalTheory.SiegLevCalc
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SiegLevCover


set_option maxHeartbeats 1000000 in
theorem exists_levelCover : ∀ (g n ℓ j : ℕ) (F : SFam g n (zetaAway n)), 1 ≤ g → 3 ≤ n → Odd n → ℓ.Prime → ℓ ∣ n →
    1 ≤ j →
    ∃ (κ : cycAway n →+* cycAway (n * (ℓ ^ j) ^ 2)) (F' : SFam g (n * (ℓ ^ j) ^ 2) (zetaAway (n * (ℓ ^ j) ^ 2)))
      (q : F'.X ⟶ F.X),
      (Function.Injective κ ∧ κ (zetaAway n) = zetaAway (n * (ℓ ^ j) ^ 2) ^ ((ℓ ^ j) ^ 2) ∧ IsFinite (spMap κ) ∧
        Etale (spMap κ) ∧ Surjective (spMap κ)) ∧
      (q ≫ F.s = F'.s ≫ spMap κ ∧ IsFinite q ∧ Etale q ∧ Surjective q ∧ SRel F'.univ F.univ ((ℓ ^ j) ^ 2) 1 q) ∧
      ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (ρ : Γ → (F'.X ⟶ F'.X)) (ν : Γ → (F'.univ.A.left ⟶ F'.univ.A.left)),
        ρ 1 = 𝟙 _ ∧ (∀ a b, ρ (a * b) = ρ a ≫ ρ b) ∧ ν 1 = 𝟙 _ ∧ (∀ a b, ν (a * b) = ν a ≫ ν b) ∧
        (∀ a, SRelBy F'.univ F'.univ ((ℓ ^ j) ^ 2) ((ℓ ^ j) ^ 2) (ρ a) (ν a)) ∧ (∀ a, ρ a ≫ q = q) ∧
        ∀ (K : Type) [Field K] [IsAlgClosed K] (x y : Sp K ⟶ F'.X), x ≫ q = y ≫ q → ∃! a, x ≫ ρ a = y := by
  intro g n ℓ j F hg hn hodd hℓ hℓn hj
  have hn0 : n ≠ 0 := by omega
  have hd0 : (ℓ ^ j) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  have hN0 : n * (ℓ ^ j) ^ 2 ≠ 0 := Nat.mul_ne_zero hn0 hd0
  have hnN : n ∣ n * (ℓ ^ j) ^ 2 := dvd_mul_right n _
  have hNn : n * (ℓ ^ j) ^ 2 / n = (ℓ ^ j) ^ 2 := Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn0)
  have hℓodd : Odd ℓ := Odd.of_dvd_nat hodd hℓn
  have hNodd : Odd (n * (ℓ ^ j) ^ 2) := hodd.mul (hℓodd.pow.pow)
  have hN3 : 3 ≤ n * (ℓ ^ j) ^ 2 := le_trans hn (Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero hd0))
  have hpow : ∃ a, n * (ℓ ^ j) ^ 2 ∣ n ^ a := ⟨2 * j + 1, by
    rw [pow_succ' n (2 * j)]
    refine mul_dvd_mul_left n ?_
    rw [← pow_mul, mul_comm j 2]
    exact pow_dvd_pow_of_dvd hℓn _⟩
  obtain ⟨κ, hinj, hζ, hfes⟩ := GlobalTheory.SiegelTor.exists_inclusion_cycAway n (n * (ℓ ^ j) ^ 2) hN0 hnN
  obtain ⟨hfin, het, hsurj⟩ := hfes hpow
  obtain ⟨F'⟩ := GlobalTheory.SiegelTor.exists_sFam_cycAway g (n * (ℓ ^ j) ^ 2) hg hN3 hNodd
  obtain ⟨Q⟩ := GlobalTheory.SiegLev.nonempty_sQuot g n _ F' κ hn hNodd hnN hζ hfin het
  let Fq : SFam g n (zetaAway n) :=
    { X := Q.X
      s := Q.s
      smooth := Q.smooth
      qproj := Q.qproj
      univ := Q.univ
      princ := Q.princ
      rep := fun S s' c hred hdense hpr =>
        GlobalTheory.quotFam_represents g n _ F' κ Q hn hNodd hnN hinj hζ hfin het hsurj S s' c hred hdense hpr
      inj := fun R _ _ x y s' c hs h₁ h₂ =>
        GlobalTheory.SiegLev.SQuot.eq_of_siegPB g n _ _ _ (zetaAway n) (zetaAway _) F' κ Q R x y s' c hs h₁ h₂ }
  obtain ⟨e, he, hpb⟩ := SFam.exists_iso Fq F
  obtain ⟨Ga, _, _, ρ, ν, h1, hmul, hν1, hνmul, hbase, hrel, hfree, htrans⟩ :=
    GlobalTheory.SiegAct.siegel_group_action g n _ F' κ hn hNodd hnN hζ
  rw [hNn] at hζ hrel htrans
  have hlow : SRel F'.univ Q.univ ((ℓ ^ j) ^ 2) 1 Q.π := by
    have := Q.low
    rwa [hNn] at this
  let q : F'.X ⟶ F.X := Q.π ≫ e.hom
  have hqs : q ≫ F.s = F'.s ≫ spMap κ := by
    show (Q.π ≫ e.hom) ≫ F.s = _
    rw [Category.assoc, he]
    exact Q.base
  have hq : SRel F'.univ F.univ ((ℓ ^ j) ^ 2) 1 q :=
    sRel_comp ((sRel_one_one_iff Q.univ F.univ e.hom).2 hpb) hlow
  haveI := Q.fin
  haveI := Q.etale
  haveI := Q.onto
  have hinv : ∀ a, ρ a ≫ q = q := by
    intro a
    obtain ⟨c, hc⟩ := (GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) F.X F'.X F.s (q ≫ F.s) q F.univ rfl).1
    have m1 : SRel c F'.univ 1 ((ℓ ^ j) ^ 2) (𝟙 F'.X) :=
      SiegLevCalc.sRel_cancel (f' := 𝟙 F'.X) hq (by rw [Category.id_comp]; exact (sRel_one_one_iff _ _ _).2 hc)
    have m2 : SRel F'.univ F.univ ((ℓ ^ j) ^ 2) 1 (ρ a ≫ q) := sRel_comp hq ⟨ν a, hrel a⟩
    have m3 := sRel_comp m2 m1
    rw [Category.id_comp, sRel_one_one_iff] at m3
    refine SFam.hom_ext F c _ _ ?_ m3 hc
    rw [Category.assoc, hqs]
    exact hbase a
  refine ⟨κ, F', q, ⟨hinj, hζ, hfin, het, hsurj⟩, ⟨hqs, inferInstance, inferInstance, inferInstance, hq⟩,
    Ga, inferInstance, inferInstance, ρ, ν, h1, hmul, hν1, hνmul, hrel, hinv, ?_⟩
  intro K _ _ x y hxy
  obtain ⟨c, hc⟩ :=
    (GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) F.X (Sp K) F.s ((x ≫ q) ≫ F.s) (x ≫ q) F.univ rfl).1
  have mx : SRel c F'.univ 1 ((ℓ ^ j) ^ 2) x := SiegLevCalc.sRel_cancel hq ((sRel_one_one_iff _ _ _).2 hc)
  have my : SRel c F'.univ 1 ((ℓ ^ j) ^ 2) y := SiegLevCalc.sRel_cancel hq (by rw [← hxy]; exact (sRel_one_one_iff _ _ _).2 hc)
  have hs : x ≫ F'.s ≫ spMap κ = y ≫ F'.s ≫ spMap κ := by
    rw [← hqs, ← Category.assoc, hxy, Category.assoc]
  obtain ⟨a, ha⟩ := htrans K x y _ c hs mx my
  refine ⟨a, ha, fun b hb => ?_⟩
  have hy : y ≫ ρ (a⁻¹ * b) = y := by
    calc y ≫ ρ (a⁻¹ * b) = x ≫ ρ (a * (a⁻¹ * b)) := by rw [hmul a, ← ha, Category.assoc]
      _ = y := by rw [mul_inv_cancel_left, hb]
  exact (inv_mul_eq_one.1 (hfree K y _ hy)).symm

end GlobalTheory.SiegLevCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntAfIntCast
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LKGeo.MultScale

variable {p : ℕ} [Fact p.Prime]

def EFA (D : Datum p) : LinearMap.BilinForm (AfP p) (AfP p ⊗[ℚ] VQ D) :=
  (D.EF.baseChange ℚ).baseChange (AfP p)

theorem EFA_tmul (D : Datum p) (a a' : AfP p) (x x' : D.La) :
    EFA D (a ⊗ₜ ((1 : ℚ) ⊗ₜ x)) (a' ⊗ₜ ((1 : ℚ) ⊗ₜ x')) = a * a' * ((D.EF x x' : ℤ) : AfP p) := by
  simp only [EFA, LinearMap.BilinForm.baseChange_tmul, _root_.mul_one]
  rw [Algebra.smul_def, zsmul_eq_mul, _root_.mul_one, map_intCast, mul_comm]

theorem EFA_inAf (D : Datum p) (x y : D.La) : EFA D (inAf D x) (inAf D y) = ((D.EF x y : ℤ) : AfP p) := by
  rw [inAf, inAf, EFA_tmul, _root_.one_mul, _root_.one_mul]

theorem isIntAf_intCast (z : ℤ) : IsIntAf ((z : AfP p)) := fun v => by
  rw [map_intCast]; exact intCast_mem _ z

theorem isIntAf_add {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a + b) := fun v => by
  rw [map_add]; exact add_mem (ha v) (hb v)

theorem isIntAf_neg {a : AfP p} (ha : IsIntAf a) : IsIntAf (-a) := fun v => by
  rw [map_neg]; exact neg_mem (ha v)

theorem isIntAf_mul {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a * b) := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hb v)

theorem isIntAf_zero : IsIntAf (0 : AfP p) := by simpa using isIntAf_intCast (p := p) 0

theorem isIntAf_EFA (D : Datum p) {v w : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) (hw : w ∈ LaHat D) :
    IsIntAf (EFA D v w) := by
  induction hv using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨a, x, ha, rfl⟩ := hv
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a', x', ha', rfl⟩ := hw
      rw [EFA_tmul]; exact isIntAf_mul (isIntAf_mul ha ha') (isIntAf_intCast _)
    | zero => simpa using isIntAf_zero
    | add u u' _ _ h h' => rw [map_add (f := _)]; exact isIntAf_add h h'
    | neg u _ h => rw [map_neg]; exact isIntAf_neg h
  | zero => simpa using isIntAf_zero
  | add u u' _ _ h h' => rw [map_add (f := _), LinearMap.add_apply]; exact isIntAf_add h h'
  | neg u _ h => rw [map_neg, LinearMap.neg_apply]; exact isIntAf_neg h

section Sim

variable {D : Datum p} {G : HTGroup p}

theorem bc_adj {V : Type} [AddCommGroup V] [Module ℚ V] (A : Type) [CommRing A] [Algebra ℚ A]
    (B : LinearMap.BilinForm ℚ V) (f g : Module.End ℚ V) (h : ∀ v w, B (f v) w = B v (g w)) (v w : A ⊗[ℚ] V) :
    B.baseChange A (f.baseChange A v) w = B.baseChange A v (g.baseChange A w) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v v' hv hv' => simp only [map_add (f := _), LinearMap.add_apply, hv, hv']
  | tmul a x =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add w w' hw hw' => simp only [map_add (f := _), hw, hw']
    | tmul a' y => simp only [LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, h]

theorem actOn_tmul {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) (R : Type) [CommRing R] [Algebra ℚ R] (r : R) (c : C) :
    actOn rep R (r ⊗ₜ c) = r • (rep c).baseChange R := by
  rw [Algebra.smul_def]
  first
  | exact Algebra.TensorProduct.lift_tmul _ _ _ r c
  | (erw [Algebra.TensorProduct.lift_tmul]; rfl)
  | rfl

theorem EFA_actOn (L : Link D G) (X : AfP p ⊗[ℚ] G.C) (v w : AfP p ⊗[ℚ] VQ D) :
    EFA D (actOn L.rep (AfP p) X v) w = EFA D v (actOn L.rep (AfP p) (starT G.star (AfP p) X).unop w) := by
  induction X using TensorProduct.induction_on with
  | zero => simp
  | add X X' hX hX' => simp only [map_add (f := _), MulOpposite.unop_add, LinearMap.add_apply, hX, hX']
  | tmul r c =>
    rw [starT_tmul, actOn_tmul, actOn_tmul, LinearMap.smul_apply, LinearMap.smul_apply, map_smul,
      LinearMap.smul_apply, map_smul]
    congr 1
    exact bc_adj (AfP p) (D.EF.baseChange ℚ) (L.rep c) (L.rep (sh G c)) (fun v w => L.adj c v w) v w

theorem EFA_actG (L : Link D G) (g : G.GAf) (v w : AfP p ⊗[ℚ] VQ D) :
    EFA D (L.actG g v) (L.actG g w) = ((uSimR (AfP p) g : (AfP p)ˣ) : AfP p) * EFA D v w := by
  obtain ⟨⟨u, c⟩, hmem⟩ := g
  have h1 : (u : AfP p ⊗[ℚ] G.C) * (starT G.star (AfP p) u).unop = algebraMap (AfP p) _ (c : AfP p) := hmem
  have h2 : (starT G.star (AfP p) u).unop * u = algebraMap (AfP p) _ (c : AfP p) := by
    have e : (starT G.star (AfP p) u).unop = ((u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) *
        algebraMap (AfP p) _ (c : AfP p) := by
      rw [← h1, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
    rw [e, _root_.mul_assoc, Algebra.commutes, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
  have hg : ∀ z, L.actG ⟨⟨u, c⟩, hmem⟩ z = actOn L.rep (AfP p) (u : AfP p ⊗[ℚ] G.C) z := fun z => rfl
  rw [hg, hg, EFA_actOn, ← Module.End.mul_apply, ← map_mul, h2, AlgHom.commutes, Module.algebraMap_end_apply,
    map_smul, smul_eq_mul]
  rfl

end Sim

theorem isIntAf_one : IsIntAf (1 : AfP p) := by simpa using isIntAf_intCast (p := p) 1

theorem inAf_mem (D : Datum p) (z : D.La) : inAf D z ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, z, isIntAf_one, rfl⟩

end GlobalTheory.LKGeo.MultScale

namespace GlobalTheory.LKGeo

end GlobalTheory.LKGeo
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CancelOfSurjectiveAbelianVarietyHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CancelOfSurjectiveAbelianVarietyHom
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem cancel_of_surjective : ∀ (K : Type) [Field K] (A B : AbVar K) (p : A ⟶ B), Surjective p.hom.left →
    ∀ (C : AbVar K) (f g : B ⟶ C), p ≫ f = p ≫ g → f = g := by
  intro K _ A B p hp C f g h
  have hB : IsIntegral B.X.left := (GlobalTheory.T.abelianVariety_isIntegral_noetherian_compact K B).1
  have hsep : IsSeparated C.X.hom := C.ab.proper.toIsSeparated
  apply Subtype.ext
  change f.hom = g.hom
  refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated C.X.hom
    ((Over.w f.hom).trans (Over.w g.hom).symm) p.hom.left ?_)
  have := congrArg (fun u => (Hom.hom u).left) h
  simpa only [comp_hom, Over.comp_left] using this

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CancelOfSurjectiveAbelianVarietyHomStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cancel_of_surjective_abelianVarietyHom : ∀ (K : Type) [Field K] (A B : AbVar K) (p : A ⟶ B), Surjective p.hom.left → ∀ (C : AbVar K) (f g : B ⟶ C), p ≫ f = p ≫ g → f = g := by
  first | exact @GlobalTheory.AV.AbVar.cancel_of_surjective | exact GlobalTheory.AV.AbVar.cancel_of_surjective | (intros; apply GlobalTheory.AV.AbVar.cancel_of_surjective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitSectionDivisorEq
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.LKGeo

theorem actOn_tmul_tmul' {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) (R : Type) [CommRing R] [Algebra ℚ R] (r a : R) (c : C) (v : V) :
    actOn rep R (r ⊗ₜ c) (a ⊗ₜ v) = (r * a) ⊗ₜ rep c v := by
  simp only [actOn, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, AlgHom.coe_comp, Function.comp_apply,
    Module.End.mul_apply, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
  change r • (rep c).baseChange R (a ⊗ₜ v) = _
  rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul]

theorem adj_actOn_afP : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (x : AfP p ⊗[ℚ] G.C) (v w : AfP p ⊗[ℚ] VQ D), (D.EF.baseChange ℚ).baseChange (AfP p) (actOn L.rep (AfP p) x v) w = (D.EF.baseChange ℚ).baseChange (AfP p) v (actOn L.rep (AfP p) (starT G.star (AfP p) x).unop w) := by
  intro p _ D G L x v w
  induction x using TensorProduct.induction_on generalizing v w with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), LinearMap.add_apply, MulOpposite.unop_add, hx, hy]
  | tmul r c =>
    rw [starT_tmul]
    induction v using TensorProduct.induction_on generalizing w with
    | zero => simp
    | add v v' hv hv' => simp only [map_add (f := _), LinearMap.add_apply, hv, hv']
    | tmul a v₀ =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add w w' hw hw' => simp only [map_add (f := _), hw, hw']
      | tmul a' w₀ =>
        rw [actOn_tmul_tmul', actOn_tmul_tmul', LinearMap.BilinForm.baseChange_tmul,
          LinearMap.BilinForm.baseChange_tmul, L.adj c v₀ w₀, mul_left_comm, _root_.mul_assoc]
        rfl

end GlobalTheory.LKGeo
end
