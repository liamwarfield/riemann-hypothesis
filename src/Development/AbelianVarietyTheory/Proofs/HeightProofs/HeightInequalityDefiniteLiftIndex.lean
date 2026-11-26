module

public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.KapDivFinStLocDataOf
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsReadingDensKNrmTieU
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IndependentDifferentialsRatiosOfTrdegValues
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TwDatPsiValuesInLL
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.LengthsAtPrimesLeFunctionFieldDataOfCurve
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.GenericSectionInjectiveOfAxH
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FractionToIntegralSectionSmulEq
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsDvdOfAlgebraic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ChosenFormsRestrictBasisFunctionField
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BigRec

namespace GlobalTheory.HeightDefinite.Basis

open GlobalTheory.SectionBasis


open ReciprocityTheory.ChartRestriction.G.T0 in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem basis_descends_record {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
    (la : HeightOneSpectrum (𝓞 B.KO)) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData X ka wL wF) (hB : InBasis G la)
    {ι : Type} [Fintype ι] (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)]
    (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z) {Dd N : ℕ} (hD : Dd = WeightFamilies.dimY D j) (e : Fin G.N ≃ Fin (N + 1))
    (j0 : ι → Fin (N + 1)) (v : ∀ Z, Fin G.N → Ω Z) (hvF : ∀ Z k, gF Z (X.inc wL (G.w k)) = v Z k)
    (x : ∀ Z, Fin N → Ω Z) (hv : ∀ Z, v Z (e.symm (j0 Z)) ≠ 0)
    (hx : ∀ Z k, x Z k = v Z (e.symm ((j0 Z).succAbove k)) / v Z (e.symm (j0 Z)))
    (hind : ∀ Z, AlgebraicIndependent B.KO (sImg (D := Dd) (j0 Z) (x Z)))
    (hfin : ∀ Z, FiniteDimensional (IntermediateField.adjoin B.KO (Set.range (sImg (D := Dd) (j0 Z) (x Z))))
      (OmS (Ω Z) Dd N))
    (g0 : B.Cusp j wF) (θ : Fin G.del → ∀ Z, Ω Z) (hθ : ∀ k Z, gF Z (X.inc wF (G.th' k)) = θ k Z)
    (g : ∀ Z, Ω Z) (hgF : ∀ Z, gF Z (X.inc wF g0) = g Z) (hg : ∀ Z, g Z ≠ 0)
    (E : letI : ∀ Z, Module (Kp X la G.N) (RZs X la G.N (Ω Z) (gF Z) G.w ⧸
          Ideal.map (phiZ X la G.N (Ω Z) (gF Z) G.w) (Jid X la G.w)) := fun Z =>
        ((Ideal.Quotient.mk (Ideal.map (phiZ X la G.N (Ω Z) (gF Z) G.w) (Jid X la G.w))).comp
          (algebraMap (Kp X la G.N) (RZs X la G.N (Ω Z) (gF Z) G.w))).toModule
      SectionSheafQuotient X la G.w wF ≃ₗ[Kp X la G.N] ∀ Z, RZs X la G.N (Ω Z) (gF Z) G.w ⧸
                           Ideal.map (phiZ X la G.N (Ω Z) (gF Z) G.w) (Jid X la G.w))
    (hE : ∀ (F : B.Cusp j wF) Z, E (resF G la F) Z *
        Ideal.Quotient.mk (Ideal.map (phiZ X la G.N (Ω Z) (gF Z) G.w) (Jid X la G.w))
          (lwZ X la G.N (Ω Z) (gF Z) G.w (algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wF g0)))) =
        Ideal.Quotient.mk (Ideal.map (phiZ X la G.N (Ω Z) (gF Z) G.w) (Jid X la G.w))
          (lwZ X la G.N (Ω Z) (gF Z) G.w (algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wF F))))) :
    ∑ Z, Module.finrank (IntermediateField.adjoin B.KO (Set.range (sImg (D := Dd) (j0 Z) (x Z))))
      (OmS (Ω Z) Dd N) = G.del ∧
    (∀ p : Fin G.del → MvPolynomial (TVar Dd N) B.KO,
      (∀ Z, ∑ k, sHom (j0 Z) (x Z) (p k) * algebraMap (Ω Z) (OmS (Ω Z) Dd N) (θ k Z / g Z) = 0) → ∀ k, p k = 0) ∧
    (∀ y : ∀ Z, OmS (Ω Z) Dd N, ∃ q : MvPolynomial (TVar Dd N) B.KO, (∀ Z, sHom (j0 Z) (x Z) q ≠ 0) ∧
      ∃ p : Fin G.del → MvPolynomial (TVar Dd N) B.KO, ∀ Z, sHom (j0 Z) (x Z) q * y Z =
        ∑ k, sHom (j0 Z) (x Z) (p k) * algebraMap (Ω Z) (OmS (Ω Z) Dd N) (θ k Z / g Z)) := by
  let iK : Algebra B.KO (Kp X la G.N) :=
    ((algebraMap (X.Kl la) (Kp X la G.N)).comp (algebraMap B.KO (X.Kl la))).toAlgebra
  have : IsScalarTower B.KO (X.Kl la) (Kp X la G.N) := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨h1, h2⟩ := coords_of_equiv _ (tL G la) hB.1 hB.2 E
  refine basis_descends_loc (Kl := X.Kl la) hD e j0 v x hv hx hind hfin _ (GlobalTheory.CurveRecord.tv_indep X la G.N)
    (fun Z i => rzMap X la G.N (Ω Z) (gF Z) (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la G.w i))
    (fun Z i => by rw [GlobalTheory.CurveRecord.rzMap_sec_eq]; simp only [hvF])
    (fun Z => Ideal.map (phiZ X la G.N (Ω Z) (gF Z) G.w) (Jid X la G.w))
    (fun Z => GlobalTheory.CurveRecord.map_Jid_eq X la G.N (Ω Z) (gF Z) G.w) _ (fun _ _ => rfl) θ g hg
    (fun k Z => E (tL G la k) Z) (fun k Z => ?_) h1 h2
  have := hE (G.th' k) Z
  rw [lwZ_alg, lwZ_alg, rzMap_emb, rzMap_emb, hgF, hθ] at this
  exact this


open ReciprocityTheory.ChartRestriction.G.T0 in
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem chosenForms_basis_of_value_basis {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]
    (d : ReciprocityTheory.ChartRestriction.G.T0.Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z)) {n : ℕ}
    (θ : Fin n → ∀ Z : Comp Xo c, Om Z) (g : ∀ Z : Comp Xo c, Om Z) (hg : ∀ Z, g Z ≠ 0) (eδ : Fin d.del ≃ Fin n)
    (h1 : ∀ p : Fin n → MvPolynomial (TVar d.D d.N) c.F,
      (∀ Z, ∑ k, sHom (d.jc Z) (d.x Z) (p k) * algebraMap (Om Z) (OmS (Om Z) d.D d.N) (θ k Z / g Z) = 0) →
        ∀ k, p k = 0)
    (h2 : ∀ y : ∀ Z, OmS (Om Z) d.D d.N, ∃ q : MvPolynomial (TVar d.D d.N) c.F,
      (∀ Z, sHom (d.jc Z) (d.x Z) q ≠ 0) ∧
      ∃ p : Fin n → MvPolynomial (TVar d.D d.N) c.F, ∀ Z, sHom (d.jc Z) (d.x Z) q * y Z =
        ∑ k, sHom (d.jc Z) (d.x Z) (p k) * algebraMap (Om Z) (OmS (Om Z) d.D d.N) (θ k Z / g Z))
    (sel : Fin d.del → Fin d.np)
    (hsel : ∀ i Z, d.thp (sel i) Z = AddMonoidAlgebra.single d.wF (θ (eδ i) Z)) : A4Selection d sel := by
  refine ⟨fun Z => AddMonoidAlgebra.single d.wF (g Z), fun Z => ⟨mem_AG.2 ⟨_, rfl⟩, by simpa using hg Z⟩,
    fun p hp k => ?_, fun y => ?_⟩
  · have := h1 (fun k => p (eδ.symm k)) (fun Z => by
      rw [← hp Z, ← eδ.sum_comp]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hsel, ratio_single _ _ _ (hg Z), eδ.symm_apply_apply]
      rfl) (eδ k)
    exact (congrArg p (eδ.symm_apply_apply k)).symm.trans this
  · obtain ⟨q, hq, p, hp⟩ := h2 y
    refine ⟨q, hq, fun k => p (eδ k), fun Z => (hp Z).trans ?_⟩
    rw [← eδ.sum_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsel, ratio_single _ _ _ (hg Z)]
    rfl


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem chosenForms_restrict_basis_functionField : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF) (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z)) (e : Fin G.N ≃ Fin (d.N + 1)), d.D = WeightFamilies.dimY D j → (∀ k, d.w (e k) = valC hG (wtA wL) wL.n (G.w k).1) → (∀ Z, d.w (d.jc Z) Z ≠ 0) → CurveHyp h j hj hG ka wL wF G S g0 → InBasis G la → ∃ eδ : Fin d.del ≃ Fin G.del, ∀ sel : Fin d.del → Fin d.np, (∀ i, d.thp (sel i) = valC hG (wtA wF) wF.n (G.th' (eδ i)).1) → d.wF = wtZ (wtA wF) wF.n → A4Selection d sel := by
  intro D T h j hj hG ka wL wF G S g0 la _ d e hD hw hb hH hB
  have hT : GenFromTest (T.Q.Xo j) T.Q.c hG := fun Z => h.allTest j hj (Om Z) (genFr hG Z)
  obtain ⟨hfg, htr⟩ := GlobalTheory.FlagDim.fnFG_fnTrdeg_record D T.Q h.pins.2.2.2 j hj
  have hA1 := independent_differentials_ratios_cusp_forms_trdeg D T h j hj hG ka wL wF G d e hD hw hb hH.2.1.2
  have hS := fun Z => GlobalTheory.genericSection_field (D := d.D) (d.jc Z) (d.x Z) (hfg Z) ((htr Z).trans (by rw [hD])) (hA1 Z)
  have hg := GlobalTheory.CurveRecord.evC_ne_zero h j hj hG hT (GlobalTheory.Reg.genValInj_record D T h j hj hG)
    (GlobalTheory.Reg.compSplit_record D T h j hj hG) G hH.2.1 g0 hH.2.2.2
  obtain ⟨⟨E, hE⟩, -⟩ := GlobalTheory.SectionProduct.tieS D T h j hj hG ka wL wF G hT S g0 la hH hB
  have hw' : ∀ i Z, d.w i Z = AddMonoidAlgebra.single (wtZ (wtA wL) wL.n) (evC hG Z (G.w (e.symm i)).1) := by
    intro i Z
    have := congrFun (hw (e.symm i)) Z
    rwa [e.apply_symm_apply] at this
  have hq : ∀ Z, evC hG Z (G.w (e.symm (d.jc Z))).1 ≠ 0 := by
    intro Z h0
    apply hb Z
    rw [hw', h0]
    simp
  have hx : ∀ Z k, d.x Z k =
      evC hG Z (G.w (e.symm ((d.jc Z).succAbove k))).1 / evC hG Z (G.w (e.symm (d.jc Z))).1 := by
    intro Z k
    unfold ReciprocityTheory.ChartRestriction.G.T0.Data.x
    rw [hw', hw']
    exact Formalism.L2.Pj.ratio_single _ _ _ (hq Z)
  obtain ⟨h0, h1, h2⟩ := basis_descends_record (recPlus h j hj) la G hB (fun Z : Comp (T.Q.Xo j) T.Q.c => Om Z)
    (fun Z => formsEvR j hG hT Z) hD e d.jc (fun Z k => evC hG Z (G.w k).1)
    (fun Z k => formsEvR_inc h j hj hG hT Z wL (G.w k)) d.x hq hx (fun Z => (hS Z).1) (fun Z => (hS Z).2.1) g0
    (fun k Z => evC hG Z (G.th' k).1) (fun k Z => formsEvR_inc h j hj hG hT Z wF (G.th' k))
    (fun Z => evC hG Z g0.1) (fun Z => formsEvR_inc h j hj hG hT Z wF g0) hg E hE
  have hdel : d.del = G.del := h0
  refine ⟨finCongr hdel, fun sel hsel hF => ?_⟩
  exact chosenForms_basis_of_value_basis d (fun k Z => evC hG Z (G.th' k).1) (fun Z => evC hG Z g0.1) hg (finCongr hdel) h1 h2 sel
    (fun i Z => by rw [hsel, hF]; rfl)

end GlobalTheory.HeightDefinite.Basis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeightZZeroEqTwoSmulSubSelf
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

namespace GlobalTheory.HeightDefinite

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem ex_zero : ex Dw (0 : (E →+* ℂ) × ℕ → ℕ) 0 = fun _ => 0 := by
  funext i; cases i <;> rfl

theorem one_mem_sec : (1 : Rul Xo c) ∈ sec Xo c 0 0 := by
  refine ⟨fun p q φ y z _ => ?_, fun p t y y' _ => ?_⟩
  · show (1 : q.R) = φ 1
    rw [map_one]
  · show (1 : p.R) = wchar (ex Dw 0 0) t * 1
    simp [wchar, ex_zero]

theorem wtZ_zero : wtZ (E := E) 0 0 = 0 := by
  ext <;> simp [wtZ]

theorem evC_one {h : GenFrEx Xo c} (hgt : GenFromTest Xo c h) (Z : Comp Xo c) : evC h Z 1 = 1 :=
  evalAt_one _ _ _ (hgt Z)

theorem exists_nat_comb {ι : Type} [Finite ι] {Ω : ι → Type} [∀ Z, Field (Ω Z)] [∀ Z, CharZero (Ω Z)] {n : ℕ}
    (a : ∀ Z, Fin n → Ω Z) (ha : ∀ Z, ∃ k, a Z k ≠ 0) :
    ∃ m : Fin n → ℕ, ∀ Z, ∑ k, (m k : Ω Z) * a Z k ≠ 0 := by
  classical
  let p : ∀ Z, Polynomial (Ω Z) := fun Z => ∑ k : Fin n, Polynomial.monomial (k : ℕ) (a Z k)
  have hp : ∀ Z, p Z ≠ 0 := by
    intro Z h0
    obtain ⟨k, hk⟩ := ha Z
    have h1 := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q (k : ℕ)) h0
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finsupp.single_apply,
      Polynomial.coeff_zero] at h1
    rw [Finset.sum_eq_single k (fun b _ hb => if_neg fun e => hb (Fin.ext e)) (by simp), if_pos rfl] at h1
    exact hk h1
  have hfin : ∀ Z, {t : ℕ | (p Z).IsRoot (t : Ω Z)}.Finite := fun Z =>
    Set.Finite.preimage (f := fun t : ℕ => (t : Ω Z)) Nat.cast_injective.injOn (Polynomial.finite_setOf_isRoot (hp Z))
  obtain ⟨t, ht⟩ := (Set.finite_iUnion hfin).exists_notMem
  refine ⟨fun k => t ^ (k : ℕ), fun Z h0 => ht (Set.mem_iUnion.2 ⟨Z, ?_⟩)⟩
  show (p Z).eval (t : Ω Z) = 0
  rw [← h0]
  simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_monomial, Nat.cast_pow, mul_comm]

variable [Fintype (Comp Xo c)]

theorem supBdd_one (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) : SupBdd Xo c fn 0 0 1 := by
  intro σ
  refine ⟨1, ?_⟩
  rintro _ ⟨y, rfl⟩
  unfold ptNorm
  rw [ex_zero]
  simp only [pow_zero, Finset.prod_const_one, mul_one]
  unfold evalAt
  split_ifs
  · rw [Pi.one_apply, Pi.one_apply, map_one]
    exact le_of_eq (norm_one (α := ℂ))
  · exact le_of_eq_of_le (norm_zero (E := ℂ)) zero_le_one

theorem log_sup_le {h : GenFrEx Xo c} {fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ}
    {yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))}
    (hfn : FnNe Xo c fn) (hfg : FnFG Xo c) (hcx : ValAtCx h yP) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {f : Rul Xo c} (hS : f ∈ sec Xo c a n) (hB : SupBdd Xo c fn a n f) (hN : NZSome h f ∨ f = 0) (σ : c.F →+* ℂ) :
    Real.log (⨆ p : (Σ Z : Comp Xo c, PT (Ω := Om Z) σ), nrmC fn (yP p.1) (wtZ a n) (valC h a n f p.1) p.2) ≤
      Real.log (supR Xo c fn σ a n f) := by
  rcases hN with hN | rfl
  · exact log_supN_le hfn (ptNe_of_fnFG hfg) hcx hS hB hN σ
  · unfold supR supAt
    simp only [valC_zero, nrmC_zero, ptNorm_zero, Real.iSup_const_zero, le_refl]

variable (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N : ℕ) (uL uF uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (etR ta2R : Rul Xo c)
    (nu : HeightOneSpectrum (𝓞 c.F) → ℝ)
    (wsize : WTZ E → ℝ) (DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO : ℝ)

abbrev dat : Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z) :=
  dataOf h δ fn yP Dd N 0 1 1 0 uL uF uL uL uL (0, 0) uta2 wR jc np thpR 0 Fin.elim0 uF 0 Fin.elim0 ∅ etR 1 ta2R nu
    (fun _ _ _ => 0) wsize DF PN 1 1 PP0' 1 Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO 0 0

omit [NumberField E] [IsCMField E] in
theorem wt_et : wtZ uL.1 uL.2 = (1 * 1 : ℕ) • wtZ uL.1 uL.2 := by simp

omit [NumberField E] [IsCMField E] in
theorem weightZ_zero_eq_two_smul_sub_self : wtZ ((0, 0) : WtR E).1 ((0, 0) : WtR E).2 = (2 : ℕ) • (wtZ uL.1 uL.2 - wtZ uL.1 uL.2) := by
  rw [sub_self, smul_zero]
  ext <;> simp [wtZ]

theorem htSup_dat (hgt : GenFromTest Xo c h) (hfn : FnNe Xo c fn) (hfg : FnFG Xo c) (hcx : ValAtCx h yP)
    (huta2 : wtZ uta2.1 uta2.2 = (Dd + 4 : ℕ) • wtZ uL.1 uL.2 - wtZ uF.1 uF.2)
    (hwS : ∀ k, wR k ∈ sec Xo c uL.1 uL.2) (hwB : ∀ k, SupBdd Xo c fn uL.1 uL.2 (wR k))
    (hwN : ∀ k, NZSome h (wR k) ∨ wR k = 0)
    (hpS : ∀ k, thpR k ∈ sec Xo c uF.1 uF.2) (hpB : ∀ k, SupBdd Xo c fn uF.1 uF.2 (thpR k))
    (hpN : ∀ k, NZSome h (thpR k) ∨ thpR k = 0)
    (h2S : ta2R ∈ sec Xo c uta2.1 uta2.2) (h2B : SupBdd Xo c fn uta2.1 uta2.2 ta2R)
    (h2N : NZSome h ta2R ∨ ta2R = 0)
    (mx : (c.F →+* ℂ) → ℝ) (hmx : ∀ σ k, Real.log (supR Xo c fn σ uL.1 uL.2 (wR k)) ≤ mx σ)
    (hmxm : meanK mx ≤ Gc * wsize (wtZ uL.1 uL.2))
    (hth : ∀ k, meanK (fun σ => Real.log (supR Xo c fn σ uF.1 uF.2 (thpR k))) ≤ Gc * wsize (wtZ uF.1 uF.2))
    (hta1 : 0 ≤ 2 * PI4 * Dd * wsize (wtZ uL.1 uL.2))
    (hta2 : ∀ σ, Real.log (supR Xo c fn σ uta2.1 uta2.2 ta2R) ≤ PI4 * Dd * wsize (wtZ uL.1 uL.2)) :
    (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO).HtSup := by
  have hmean : ∀ (F : (c.F →+* ℂ) → ℝ) (b : ℝ), (∀ σ, F σ ≤ b) → meanK F ≤ b := by
    intro F b hF
    have hn : (0 : ℝ) < Fintype.card (c.F →+* ℂ) := by
      rw [NumberField.Embeddings.card]; exact_mod_cast Module.finrank_pos
    unfold meanK
    rw [div_le_iff₀ hn]
    refine (Finset.sum_le_sum fun σ _ => hF σ).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (meanK_mono' fun σ => ?_).trans hmxm
    have : Nonempty (Fin (N + 1)) := ⟨0⟩
    exact ciSup_le fun j => (log_sup_le hfn hfg hcx (hwS j) (hwB j) (hwN j) σ).trans (hmx σ j)
  · intro k
    exact (meanK_mono' fun σ => log_sup_le hfn hfg hcx (hpS k) (hpB k) (hpN k) σ).trans (hth k)
  · refine hmean _ _ fun σ => le_trans ?_ hta1
    refine Real.log_nonpos (supN_dataOf_nonneg ..) (Real.iSup_le (fun p => ?_) zero_le_one)
    show nrmC fn (yP p.1) ((2 : ℕ) • (wtZ uL.1 uL.2 - wtZ uL.1 uL.2)) (valC h 0 0 1 p.1) p.2 ≤ 1
    rw [sub_self, smul_zero]
    simp only [valC, wtZ_zero, evC_one hgt, nrmC_single, map_one, norm_one, one_mul]
    refine le_of_eq (Finset.prod_eq_one fun i _ => ?_)
    cases i <;> simp [exZ]
  · refine hmean _ _ fun σ => le_trans ?_ (hta2 σ)
    have h2 := log_sup_le (h := h) (yP := yP) hfn hfg hcx h2S h2B h2N σ
    rw [huta2] at h2
    exact h2

theorem htI2be_dat {rU : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ rU) (xR : ℝ)
    (htie : NrmTieU h fn yP U xR wR uL etR uL)
    (hI2 : ∀ σ, GoodEmb c σ → ∀ (k : (U σ).Comp) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ rU),
      x ∈ ((U σ).X k).dom → -Real.log (Real.sqrt (∑ j, recNrm (U σ) xR uL.1 uL.2 (wR j) k x ^ 2)) ≤ tableLineDegreeFive * DF) :
    (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO).HeightIntegralBoundEstimate := by
  intro Z P
  obtain ⟨σ, hσ, k, x, hx, hw, -⟩ := htie Z P
  have h1 := hI2 σ hσ k x hx
  show -Real.log (Real.sqrt (∑ j, nrmC fn (yP Z) (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR j) Z) P ^ 2)) ≤
    tableLineDegreeFive * DF + (0 : ℝ) / _ * _ + (0 : ℝ) * tableLineDegreeTwo
  simp only [hw, zero_div, zero_mul, add_zero]
  exact h1

theorem lawBdd_dat (hcx : ValAtCx h yP)
    (huta2 : wtZ uta2.1 uta2.2 = (Dd + 4 : ℕ) • wtZ uL.1 uL.2 - wtZ uF.1 uF.2)
    (hwS : ∀ k, wR k ∈ sec Xo c uL.1 uL.2) (hwB : ∀ k, SupBdd Xo c fn uL.1 uL.2 (wR k))
    (hpS : ∀ k, thpR k ∈ sec Xo c uF.1 uF.2) (hpB : ∀ k, SupBdd Xo c fn uF.1 uF.2 (thpR k))
    (heS : etR ∈ sec Xo c uL.1 uL.2) (heB : SupBdd Xo c fn uL.1 uL.2 etR)
    (h2S : ta2R ∈ sec Xo c uta2.1 uta2.2) (h2B : SupBdd Xo c fn uta2.1 uta2.2 ta2R) :
    LawBdd (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO) :=
  GlobalTheory.Reg.LawBddPf.lawBdd_dataOf E H Dw l Xo c h δ fn yP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcx (fun k => ⟨hwS k, hwB k⟩) (fun k => ⟨hpS k, hpB k⟩) ⟨heS, heB⟩
    ⟨one_mem_sec, supBdd_one fn⟩ ⟨h2S, h2B⟩ (wt_et uL) (weightZ_zero_eq_two_smul_sub_self uL) huta2

theorem exists_htConcl (hgt : GenFromTest Xo c h)
    (hne : CompNe Xo c) (hfg : FnFG Xo c) (htr : FnTrdeg Xo c Dd) (hac : FnAlgClosed (Xo := Xo) (c := c))
    (hwb : ∀ Z, evC h Z (wR (jc Z)) ≠ 0) (het : NZAt h etR) (hta2 : NZAt h ta2R)
    (huta2 : wtZ uta2.1 uta2.2 = (Dd + 4 : ℕ) • wtZ uL.1 uL.2 - wtZ uF.1 uF.2)
    (hfn : FnNe Xo c fn) (hconj : FnConj Xo c fn yP)
    (hbdd : LawBdd (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO))
    (ha1 : A1Bigness (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO))
    (ha2 : A2RegularityOrders (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO))
    (ha3' : LawA3' (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO))
    (sel : Fin (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO).del → Fin np)
    (ha4 : A4Selection (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO) sel)
    (hnum : NumOK (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO))
    (ha13 : A13Measurable (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO))
    (hH1 : (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO).FinitePlaceHyp)
    (hF1d : (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO).TrivialPlaceHyp)
    (hLAM : (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO).HtLAM)
    (hSup : (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO).HtSup)
    (hI2et : (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO).HeightIntegralEstimateTrivialPlace)
    (hI2be : (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO).HeightIntegralBoundEstimate) :
    ∃ (hd : (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO).AxH (fun Z => AG Z))
      (hs : (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO).S1),
      hd.sel = sel ∧ Formalism.MainNotions.Gaps.HeightData.HtConcl ((dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO).htOf hd hs) := by
  have h1 : NZAt h 1 := fun Z => by rw [evC_one hgt]; exact one_ne_zero
  refine ⟨_, _, ?_, htConcl_dataOf h δ fn yP Dd N 0 1 1 0 uL uF uL uL uL (0, 0) uta2 wR jc np thpR 0 Fin.elim0 uF 0
    Fin.elim0 ∅ etR 1 ta2R nu (fun _ _ _ => 0) wsize DF PN 1 1 PP0' 1 Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO 0 0 hne hfg htr hac hwb
    het h1 hta2 (wt_et uL) (weightZ_zero_eq_two_smul_sub_self uL) huta2 hfn hconj hbdd ha1 ha2 ha3' sel ha4 hnum ha13 hH1 hF1d hLAM hSup hI2et
    hI2be⟩
  obtain ⟨hD, hi, hg, hc0, hc1, hcg, hL, hDF, hrw, hnK, hrd, hP⟩ := hnum
  rfl

section Transfer

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.MainNotions.Gaps.HeightData

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
  {ι : Type} [Fintype ι] {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra B.KO (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra B.KO (A c)]
  [∀ c, Algebra (𝓞 B.KO) (A c)] {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

theorem heights_of_first (d : Data B.KO ι Ω WT A) (hd : d.AxH 𝒜) (hs : d.S1)
    (G : GlobalFamilyData X ka wL wF) (Qf : ∀ la, LocalPointData G la) (Gc PH Prw Pet : ℝ) (hj : ¬ j < D.R.m)
    (hD : d.D = WeightFamilies.dimY D j) (hδ : d.del = G.del) (hL : d.wsize d.wL = wL.size) (hG : d.Gc = Gc)
    (hPH : d.PHc = PH) (hPrw : d.Prw = Prw)
    (hS : ∑ k, (d.htOf hd hs).S k ≤ ∑ k, WeightFamilies.meanLogSup B (G.th' k))
    (hI : IlaTie d hd hs G Qf Gc PH Prw Pet) (h : HtConcl (d.htOf hd hs)) : Heights Qf Gc PH Prw Pet := by
  refine heights_of_htConcl G Qf Gc PH Prw Pet ?_
  obtain ⟨hfin, hsum, hineq, -⟩ := h
  have hle : ∀ la : HeightOneSpectrum (𝓞 B.KO),
      (((toHtData G Qf Gc PH Prw Pet).Ila la).toNat : ℝ) * Formalism.MainNotions.Gaps.HeightData.lN B.KO la ≤
        (((d.htOf hd hs).Ila la).toNat : ℝ) * Formalism.MainNotions.Gaps.HeightData.lN B.KO la := fun la =>
    mul_le_mul_of_nonneg_right (by exact_mod_cast ENat.toNat_le_toNat (hI la) (hfin la)) (lN_nonneg' _ la)
  have hsum' : Summable fun la : HeightOneSpectrum (𝓞 B.KO) =>
      (((toHtData G Qf Gc PH Prw Pet).Ila la).toNat : ℝ) * Formalism.MainNotions.Gaps.HeightData.lN B.KO la :=
    Summable.of_nonneg_of_le (fun la => mul_nonneg (Nat.cast_nonneg _) (lN_nonneg' _ la)) hle hsum
  have hDr : ((d.htOf hd hs).D : ℝ) = (WeightFamilies.dimY D j : ℝ) := by exact_mod_cast hD
  have hδr : ((d.htOf hd hs).δ : ℝ) = (G.del : ℝ) := by exact_mod_cast hδ
  have hL' : (d.htOf hd hs).L = wL.size := hL
  have hG' : (d.htOf hd hs).G = Gc := hG
  have hPH' : (d.htOf hd hs).PH = PH := hPH
  have hPrw' : (d.htOf hd hs).Prw = Prw := hPrw
  refine ⟨fun la => ne_top_of_le_ne_top (hfin la) (hI la), hsum', ?_, fun he => absurd he hj⟩
  have ht := Summable.tsum_le_tsum hle hsum' hsum
  have hineq' : 2 * ∑' la : HeightOneSpectrum (𝓞 B.KO),
        (((d.htOf hd hs).Ila la).toNat : ℝ) * Formalism.MainNotions.Gaps.HeightData.lN B.KO la ≤
      (G.del : ℝ) * Real.log G.del + 2 * ∑ k, (d.htOf hd hs).S k +
      8 / 3 * (WeightFamilies.dimY D j : ℝ) * ((WeightFamilies.dimY D j : ℝ) + 4) * G.del * Prw * wL.size +
      2 * ((WeightFamilies.dimY D j : ℝ) + 4) * ((WeightFamilies.dimY D j : ℝ) + 1) * G.del * (2 * Gc + 6 * PH) * wL.size := by
    rw [hDr, hδr, hL', hG', hPH', hPrw'] at hineq
    exact hineq
  show 2 * ∑' la : HeightOneSpectrum (𝓞 B.KO),
        (((toHtData G Qf Gc PH Prw Pet).Ila la).toNat : ℝ) * Formalism.MainNotions.Gaps.HeightData.lN B.KO la ≤
      (G.del : ℝ) * Real.log G.del + 2 * ∑ k, WeightFamilies.meanLogSup B (G.th' k) +
      8 / 3 * (WeightFamilies.dimY D j : ℝ) * ((WeightFamilies.dimY D j : ℝ) + 4) * G.del * Prw * wL.size +
      2 * ((WeightFamilies.dimY D j : ℝ) + 4) * ((WeightFamilies.dimY D j : ℝ) + 1) * G.del * (2 * Gc + 6 * PH) * wL.size
  linarith

end Transfer

end GlobalTheory.HeightDefinite
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.HeightInequalityDefiniteLiftIndex
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HeightDefinite

section Weights

variable {D : D7} {j : ℕ}

theorem wtZ_wsmul (k : ℕ) (w : WeightFamilies.Wt D j) : wtZ (wtA (wsmul k w)) (wsmul k w).n = k • wtZ (wtA w) w.n := by
  rw [GlobalTheory.Reg.wtA_wsmul_eq]
  ext <;> simp [wtZ, wsmul]

theorem weightSumVector_secondGeneratorWeight_definite {wL wF w2 : WeightFamilies.Wt D j} (hG : IsG2 wL wF w2) :
    wtZ (wtA w2) w2.n = (WeightFamilies.dimY D j + 4 : ℕ) • wtZ (wtA wL) wL.n - wtZ (wtA wF) wF.n := by
  have e : wadd w2 wF = wsmul (WeightFamilies.dimY D j + 4) wL := by
    apply deg_inj
    simp only [deg, wadd, wsmul, Prod.mk.injEq]
    exact ⟨funext fun τ => funext fun i => hG.2.1 τ i, funext fun τ => funext fun i => hG.2.2 τ i, hG.1⟩
  rw [eq_sub_iff_add_eq, ← wtZ_add, ← wtA_wadd, ← n_wadd, e, wtZ_wsmul]

theorem tauEmb_inj {t t' : D.what₂.Tau} (h : DV.tauEmb D t = DV.tauEmb D t') : t = t' :=
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem tauEmb_ne_conj {Q : Par D} (hp : Q.PinHost) (t t' : D.what₂.Tau) :
    DV.tauEmb D t ≠ conjEmb (DV.tauEmb D t') := by
  intro h
  have h1 := hp.2.2.2 t
  rw [h] at h1
  have h5 : (starRingEnd ℂ) (DV.tauEmb D t' (Q.H.rt : D.host.E)) = Q.H.rt0 := h1
  rw [hp.2.2.2 t'] at h5
  obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 h5
  have h6 := Q.H.sqrt_neg_disc_sq
  rw [hx] at h6
  have h7 : x ^ 2 = -(Q.H.d : ℝ) := by exact_mod_cast h6
  have h8 : (0 : ℝ) < Q.H.d := by exact_mod_cast Q.H.d_prime.pos
  nlinarith [sq_nonneg x]

theorem wtA_tau {Q : Par D} (hp : Q.PinHost) (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (DV.tauEmb D t, i) = ext0 (w.aP t) i := by
  classical
  unfold wtA
  rw [Finset.sum_eq_single t]
  · simp [tauEmb_ne_conj hp]
  · intro t' _ ht'
    have : DV.tauEmb D t ≠ DV.tauEmb D t' := fun h => ht' (tauEmb_inj h).symm
    simp [tauEmb_ne_conj hp, this]
  · simp

theorem wtA_conj_tau {Q : Par D} (hp : Q.PinHost) (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (conjEmb (DV.tauEmb D t), i) = ext0 (w.aM t) i := by
  classical
  have h0 : ∀ τ : D.host.E →+* ℂ, conjEmb (conjEmb τ) = τ := fun τ => by
    ext x
    simp [conjEmb]
  have h1 : ∀ t', conjEmb (DV.tauEmb D t) ≠ DV.tauEmb D t' := fun t' h => tauEmb_ne_conj hp t' t h.symm
  unfold wtA
  rw [Finset.sum_eq_single t]
  · simp [h1]
  · intro t' _ ht'
    have : conjEmb (DV.tauEmb D t) ≠ conjEmb (DV.tauEmb D t') := fun h =>
      ht' (tauEmb_inj (by rw [← h0 (DV.tauEmb D t'), ← h, h0]))
    simp [h1, this]
  · simp

theorem eq_of_wtZ_eq {Q : Par D} (hp : Q.PinHost) {w w' : WeightFamilies.Wt D j}
    (e : wtZ (wtA w) w.n = wtZ (wtA w') w'.n) : w = w' := by
  have e1 : ∀ x, wtA w x = wtA w' x := fun x => by
    have := congrFun (congrArg Prod.fst e) x
    simpa [wtZ] using this
  have e2 : w.n = w'.n := by
    have := congrArg Prod.snd e
    simpa [wtZ] using this
  apply deg_inj
  simp only [deg, Prod.mk.injEq]
  refine ⟨funext fun t => funext fun i => ?_, funext fun t => funext fun i => ?_, e2⟩
  · have := e1 (DV.tauEmb D t, i)
    rw [wtA_tau hp, wtA_tau hp] at this
    simpa [ext0, i.isLt] using this
  · have := e1 (conjEmb (DV.tauEmb D t), i)
    rw [wtA_conj_tau hp, wtA_conj_tau hp] at this
    simpa [ext0, i.isLt] using this

theorem exists_wsize {Q : Par D} (hp : Q.PinHost) (w w' : WeightFamilies.Wt D j) :
    ∃ s : WTZ D.host.E → ℝ, s (wtZ (wtA w) w.n) = w.size ∧ s (wtZ (wtA w') w'.n) = w'.size := by
  classical
  refine ⟨fun u => if u = wtZ (wtA w) w.n then w.size else w'.size, if_pos rfl, ?_⟩
  by_cases e : wtZ (wtA w') w'.n = wtZ (wtA w) w.n
  · exact (if_pos e).trans (by rw [eq_of_wtZ_eq hp e])
  · exact if_neg e

end Weights

theorem ev_ne_zero_of_nonZeroComp {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) {ι : Type}
    (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)] (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)
    (hinj : ∀ (w : WeightFamilies.Wt D j) (g : B.Cusp j w), (∀ Z, gF Z (X.inc w g) = 0) → g = 0)
    {u : WeightFamilies.Wt D j} {F : B.Cusp j u} (hF : X.NonZeroComp u F) (Z : ι) {w : WeightFamilies.Wt D j} (g : B.Cusp j w)
    (hg : gF Z (X.inc w g) ≠ 0) (hg' : ∀ Z', Z' ≠ Z → gF Z' (X.inc w g) = 0) : gF Z (X.inc u F) ≠ 0 := by
  intro h0
  obtain ⟨H, hH⟩ := X.inc_mul u w F g
  have hH0 : H = 0 := by
    refine hinj _ H fun Z' => ?_
    rw [← hH, map_mul]
    by_cases hZ : Z' = Z
    · subst hZ
      rw [h0, zero_mul]
    · rw [hg' Z' hZ, mul_zero]
  rw [hH0, map_zero] at hH
  have := hF w g hH
  rw [this, map_zero, map_zero] at hg
  exact hg rfl

section Forms

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)

theorem nzAt_of_nonZeroComp (hT : GenFromTest (T.Q.Xo j) T.Q.c hG) (hV : GenValInjSt h j hG)
    (hC : CompSplitSt h j hG) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (hB : BigAt h j hj hG G) {u : WeightFamilies.Wt D j}
    (F : (recB h.toLawsCore).Cusp j u) (hF : (recPlus h j hj).NonZeroComp u F) : NZAt hG (F : T.R j) := by
  intro Z
  obtain ⟨k, hk, -⟩ := hB.2 Z
  obtain ⟨g, e1, e2⟩ := hC Z wL (G.w k)
  have := ev_ne_zero_of_nonZeroComp (recPlus h j hj) (fun Z => Om Z) (fun Z => formsEvR j hG hT Z)
    (fun w g hg => hV w g fun Z => (formsEvR_inc h j hj hG hT Z w g).symm.trans (hg Z)) hF Z g
    (fun h0 => hk (e1.symm.trans ((formsEvR_inc h j hj hG hT Z wL g).symm.trans h0)))
    (fun Z' hZ' => (formsEvR_inc h j hj hG hT Z' wL g).trans (e2 Z' hZ'))
  exact fun h0 => this ((formsEvR_inc h j hj hG hT Z u F).trans h0)

theorem exists_comb [Fintype (Comp (T.Q.Xo j) T.Q.c)] {w : WeightFamilies.Wt D j} {n : ℕ}
    (f : Fin n → (recB h.toLawsCore).Cusp j w) (hf : ∀ k, f k ∈ (recB h.toLawsCore).Mlat j w)
    (hne : ∀ Z, ∃ k, evC hG Z (f k).1 ≠ 0) :
    ∃ F : (recB h.toLawsCore).Cusp j w, F ∈ (recB h.toLawsCore).Mlat j w ∧ NZAt hG F.1 := by
  have : ∀ Z : Comp (T.Q.Xo j) T.Q.c, CharZero (Om Z) := fun Z =>
    charZero_of_injective_algebraMap (algebraMap T.Q.c.F (Om Z)).injective
  obtain ⟨m, hm⟩ := exists_nat_comb (Ω := fun Z : Comp (T.Q.Xo j) T.Q.c => Om Z) (fun Z k => evC hG Z (f k).1) hne
  refine ⟨∑ k, m k • f k, Submodule.sum_mem _ fun k _ => nsmul_mem (hf k) _, fun Z h0 => hm Z ?_⟩
  let φ : (recB h.toLawsCore).Cusp j w →+ Om Z :=
    { toFun := fun F => evC hG Z F.1
      map_zero' := evC_zero hG Z
      map_add' := fun F F' => evC_add hG Z F.1 F'.1 }
  have h1 : φ (∑ k, m k • f k) = 0 := h0
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at h1
  simp only [map_nsmul, nsmul_eq_mul] at h1
  exact h1

end Forms

theorem one_le_del {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)] (hne : CompNe Xo c)
    (d : ReciprocityTheory.ChartRestriction.G.T0.Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z))
    (sel : Fin d.del → Fin d.np) (ha : A4Selection d sel) : 1 ≤ d.del := by
  obtain ⟨e, -, -, h3⟩ := ha
  obtain ⟨q, hq, p, hp⟩ := h3 fun _ => 1
  obtain ⟨Z⟩ := hne
  by_contra h0
  have : IsEmpty (Fin d.del) := ⟨fun k => by have := k.2; omega⟩
  have h1 := hp Z
  rw [Finset.univ_eq_empty, Finset.sum_empty, mul_one] at h1
  exact hq Z h1

section Orders

open ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]
  (h : GenFrEx Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)

theorem ord_nonneg_of_regP {rU : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ rU} (hreg : regular₂ Xo c U)
    (hT : OrdTie h δ (trivialClassCondition Xo c) (fun _ => Unit) (fun _ _ _ _ _ => True)) (hTQ : OrdTieQ h δ)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hdom : Dom a n) {F : Rul Xo c} (hFC : F ∈ cusp Xo c U a n) (hF : IntAlg F)
    {Z : Comp Xo c} {v : AddValuation (Om Z) (WithTop ℤ)} (hd : IsNormDiscrete v)
    (hv : (∃ la, IsOver (K := c.F) v la) ∨ IsTrivOn c.F v) (hne : evC h Z F ≠ 0) :
    0 ≤ ordC (δ Z v) v (wtZ a n) (valC h a n F Z) := by
  have hFs := cusp_le_sec Xo c U a n hFC
  have hR := hreg.1.1 ⟨(a, n), hdom⟩ ⟨F, hFC⟩ fun la y => hF la y.1 y.2
  have key : (0 : EReal) ≤ (((ordC (δ Z v) v (wtZ a n) (valC h a n F Z) : ℤ) : ℝ) : EReal) := by
    rcases hv with ⟨la, ho⟩ | ht
    · obtain ⟨y, hy⟩ := hT Z v la hd ho
      rw [hy a n F hFs hne]
      exact mul_nonneg (by exact_mod_cast ramIdx_nonneg ho) (hR.1 la ⟨vAtV y, y, rfl⟩)
    · obtain ⟨q, hq⟩ := hTQ Z v hd ht
      rw [hq a n F hFs hne]
      have hqT : (fun f => ordQ Xo c q f) ∈ trivSet Xo c := by
        refine ⟨q.T, q.ι, q.y, fun a ha => ?_, rfl⟩
        obtain ⟨u, hu⟩ := q.triv a ha
        rw [← hu]
        exact extVal_unit_zero q.T u
      exact hR.2 ⟨_, hqT⟩
  exact_mod_cast key

variable (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N : ℕ) (uL uF uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (etR ta2R : Rul Xo c)
    (nu : HeightOneSpectrum (𝓞 c.F) → ℝ)
    (wsize : WTZ E → ℝ) (DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO : ℝ)

theorem secondHeightLaw_of_regularUniformisation {rU : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ rU} (hreg : regular₂ Xo c U)
    (hgt : GenFromTest Xo c h)
    (hT : OrdTie h δ (trivialClassCondition Xo c) (fun _ => Unit) (fun _ _ _ _ _ => True)) (hTQ : OrdTieQ h δ)
    (hdL : Dom uL.1 uL.2) (hdF : Dom uF.1 uF.2) (hd2 : Dom uta2.1 uta2.2)
    (hwC : ∀ k, wR k ∈ cusp Xo c U uL.1 uL.2) (hwI : ∀ k, IntAlg (wR k))
    (hpC : ∀ k, thpR k ∈ cusp Xo c U uF.1 uF.2) (hpI : ∀ k, IntAlg (thpR k))
    (heC : etR ∈ cusp Xo c U uL.1 uL.2) (heI : IntAlg etR) (heN : NZAt h etR)
    (h2C : ta2R ∈ cusp Xo c U uta2.1 uta2.2) (h2I : IntAlg ta2R) (h2N : NZAt h ta2R)
    (huta2 : wtZ uta2.1 uta2.2 = (Dd + 4 : ℕ) • wtZ uL.1 uL.2 - wtZ uF.1 uF.2) :
    A2RegularityOrders (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO) := by
  have cases' : ∀ {Z : Comp Xo c} {v : AddValuation (Om Z) (WithTop ℤ)},
      (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO).admitted Z v →
      IsNormDiscrete v ∧ ((∃ la, IsOver (K := c.F) v la) ∨ IsTrivOn c.F v) := by
    intro Z v hA
    obtain ⟨hd, hc⟩ := hA
    exact ⟨hd, hc.imp (fun h' => let ⟨la, ho, _⟩ := h'; ⟨la, ho⟩) (fun h' => h'.1)⟩
  refine ⟨fun Z v hA x hx hx0 => ?_, fun Z v hA x hx hx0 => ?_, fun Z v hA => ?_, fun Z v hA => ?_,
    fun Z v hA => ?_⟩
  · obtain ⟨hd, hc⟩ := cases' hA
    obtain ⟨F, hF, rfl⟩ := exists_of_mem_span_valG h hx
    exact ord_nonneg_of_regP h δ hreg hT hTQ hdL (mem_of_mem_span_int _ (Set.range_subset_iff.2 hwC) hF)
      (intAlg_span (Set.forall_mem_range.2 hwI) hF) hd hc (evC_ne_zero_of_valC hx0)
  · obtain ⟨hd, hc⟩ := cases' hA
    obtain ⟨F, hF, rfl⟩ := exists_of_mem_span_valG h hx
    exact ord_nonneg_of_regP h δ hreg hT hTQ hdF (mem_of_mem_span_int _ (Set.range_subset_iff.2 hpC) hF)
      (intAlg_span (Set.forall_mem_range.2 hpI) hF) hd hc (evC_ne_zero_of_valC hx0)
  · obtain ⟨hd, hc⟩ := cases' hA
    have h0 := ord_nonneg_of_regP h δ hreg hT hTQ hdL heC heI hd hc (heN Z)
    show 0 ≤ ordC (δ Z v) v ((1 * 1 : ℕ) • wtZ uL.1 uL.2) (valC h uL.1 uL.2 etR Z)
    rw [← wt_et]
    exact h0
  · show 0 ≤ ordC (δ Z v) v ((2 : ℕ) • (wtZ uL.1 uL.2 - wtZ uL.1 uL.2)) (valC h 0 0 1 Z)
    have hz : frW (δ Z v) (0 : WTZ E) = 0 := by
      simp only [frW]
      exact Finset.sum_eq_zero fun i _ => by cases i <;> simp [exZ]
    rw [sub_self, smul_zero]
    simp only [valC, wtZ_zero, evC_one hgt, ordC, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same, hz,
      AddValuation.map_one, add_zero]
    exact le_rfl
  · obtain ⟨hd, hc⟩ := cases' hA
    have h0 := ord_nonneg_of_regP h δ hreg hT hTQ hd2 h2C h2I hd hc (h2N Z)
    rw [huta2] at h0
    exact h0

theorem exists_htI2et : ∃ Pet : ℝ, 1 ≤ Pet ∧
    (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO).HeightIntegralEstimateTrivialPlace :=
  ⟨max 1 _, le_max_left _ _, le_max_right 1 (meanK (fun σ => Real.log
      (⨆ p : (Σ Z : Comp Xo c, PT (Ω := Om Z) σ),
        nrmC fn (yP p.1) ((1 * 1 : ℕ) • wtZ uL.1 uL.2) (valC h uL.1 uL.2 etR p.1) p.2)) / ((1 : ℕ) : ℝ))⟩

end Orders

theorem heights_definite :
    ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → ∀ (y : ∀ la, PtsG G la → (extAll h j hj).Pt' la) (hw : ∀ la ζ, FromW (E := extAll h j hj) (hM := intAtExt_extAll h j hj) ζ (y la ζ)), (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InCurve) → (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InTie S) → j = D.R.m → FnAlgClosed (Xo := (T.Q.Xo j)) (c := T.Q.c) → 3 ≤ WeightFamilies.dimY D j → 0 < wL.n → (∀ la, InBasis G la) → ∀ (large₂ : SizeData₂ D) (Gc PH Prw Pet PN' PP0' PI4' tableLineDegreeFive tableLineDegreeTwo POb CL AL : ℝ) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (w2 : WeightFamilies.Wt D j) (t2 : (recB h.toLawsCore).Cusp j w2), G.TiedW S Gc Prw → G.TiedTh S Gc → (∀ i, G.th' i ∈ (recB h.toLawsCore).Mlat j wF) → IsG2 wL wF w2 → t2 ∈ (recB h.toLawsCore).Mlat j w2 → (recPlus h j hj).NonZeroComp w2 t2 → (∀ σ, Real.log ((recB h.toLawsCore).supN j w2 σ t2) ≤ PI4' * (WeightFamilies.dimY D j : ℝ) * wL.size) → WeightedPrimeSumBoundAlt large₂ (recPJ h j hj) wL nus → WeightAlgebra.PN D large₂ ≤ PN' → LAMwAt large₂ (recB h.toLawsCore) j (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) CL AL → LamConst j large₂ CL AL (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) PP0' (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL.size → 1 ≤ wL.size → (WeightAlgebra.DF wL : ℝ) ≤ wL.size → Real.log G.N + 1 / 2 ≤ Prw * (wL.size - 1) → Real.log (Module.finrank ℚ T.Q.c.F) ≤ POb → Real.log (|(NumberField.discr T.Q.c.F : ℝ)| ^ (1 / (Module.finrank ℚ T.Q.c.F : ℝ))) ≤ POb → 1 ≤ PN' → 1 ≤ PP0' → 1 ≤ Gc → 1 ≤ PI4' → 1 ≤ Pet → 1 ≤ tableLineDegreeFive → 1 ≤ tableLineDegreeTwo → 1 ≤ Prw → 1 ≤ POb → PH = 2 * (PP0' + PN' + tableLineDegreeFive + tableLineDegreeTwo + PI4' + Prw) + Gc → (∀ la, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la, (⨅ k, v (G.w k).1) ≤ (nus la : EReal)) → (∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ ((T.U j σ).X k).dom → -Real.log (Real.sqrt (∑ k', recNrm (T.U j σ) (xiR D) (wtA wL) wL.n (G.w k').1 k x ^ 2)) ≤ tableLineDegreeFive * (WeightAlgebra.DF wL : ℝ)) → Heights (fun la => (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0)) Gc PH Prw Pet := by
  intro D T h j hj hG _ ka wL wF G S g0 hH hV hC hB y hw hcur htie hjm hac hD3 _ hbas large₂ Gc PH Prw Pet PN' PP0' PI4'
    tableLineDegreeFive tableLineDegreeTwo POb CL AL nus w2 t2 hTW hTT hthM hG2 ht2M ht2N ht2S hH1w hPN hlam hlc hL1 hDF hrw hnK hrd
    gPN gPP0 gGc gPI4 _ gP14 gP16 gPrw gPO hPH hval harch
  classical
  have hgt : GenFromTest (T.Q.Xo j) T.Q.c hG := fun Z => h.allTest j hj (Om Z) (genFr hG Z)
  obtain ⟨hkfg, -, htr, hne, δ, hTQ, hTQZ, hTO, hT, hFr⟩ := Ties.ordTies_of_pins D T.Q h.pins j hj hG
  have hreg := h.reg j hj
  obtain ⟨-, -, -, hx, -, -, hrk⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  obtain ⟨-, -, hdim⟩ := hrk j hj
  have hfg := fnFG_of (T.Q.Xo j) T.Q.c hkfg
  have hU : ∀ σ, Formalism.L2.PjFree.GoodEmb T.Q.c σ →
      Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) := fun σ hσ =>
    (Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj σ ((Formalism.L2.PjFree.goodEmb_iff σ).1 hσ))
  obtain ⟨fn, hpin, hfn⟩ := GlobalTheory.FrameNorm.Existence.exists_pinned _ _ _ _ _ _ _ _ hU _ hx
  obtain ⟨yP, hyP, hcx, -⟩ := GlobalTheory.Reg.exists_cBase_valAtCx _ _ _ _ (T.Q.Xo j) T.Q.c
    (GlobalTheory.Reg.evLaws_genFr_atlas _ _ _ _ (T.Q.Xo j) T.Q.c).1 hG
  have hconj := (GlobalTheory.FrameNorm.fnConj_valAtCx_nrmC_eq_ptNorm _ _ _ _ _ _ _ _ hU _ fn hx hpin hG yP hyP).1
  obtain ⟨-, hsup, -⟩ := GlobalTheory.FrameNorm.RecSup.supBdd_and_supR_eq_supN D T h j hj fn hpin
  obtain ⟨-, -, -, hnt⟩ := Generic.exists_reading_densK_nrmTieU D T.toCore h.toLawsCore j hj fn hpin
    hG yP hyP
  have hcusp : ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w),
      F.1 ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n := fun w F => cutR_le T.C j w F.2
  have hsec : ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w),
      F.1 ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n := fun w F => cusp_le_sec _ _ _ _ _ (hcusp w F)
  have hint : ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w), F ∈ (recB h.toLawsCore).Mlat j w →
      IntAlg F.1 := fun _ _ hF => hF
  have hNZ : ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w), NZSome hG F.1 ∨ F.1 = 0 := by
    intro w F
    by_cases h0 : NZSome hG F.1
    · exact Or.inl h0
    · right
      rw [hV w F fun Z => by_contra fun hZ => h0 ⟨Z, hZ⟩]
      rfl
  have hBig := hH.2.1
  have hk0 : ∀ Z, ∃ k, evC hG Z (G.w k).1 ≠ 0 := fun Z => (hBig.2 Z).imp fun _ hk => hk.1
  obtain ⟨N, hN⟩ : ∃ N, G.N = N + 1 := by
    obtain ⟨Z⟩ := hne
    obtain ⟨k, -⟩ := hk0 Z
    exact ⟨G.N - 1, by have := k.2; omega⟩
  obtain ⟨e⟩ : Nonempty (Fin (N + 1) ≃ Fin G.N) := ⟨finCongr hN.symm⟩
  obtain ⟨jc, hwb⟩ : ∃ jc : Comp (T.Q.Xo j) T.Q.c → Fin (N + 1), ∀ Z, evC hG Z (G.w (e (jc Z))).1 ≠ 0 := by
    choose k hk using hk0
    exact ⟨fun Z => e.symm (k Z), fun Z => by rw [e.apply_symm_apply]; exact hk Z⟩
  obtain ⟨et, hetM, hetN⟩ := exists_comb h j hG G.w hTW.2.1 hk0
  have ht2Z : NZAt hG t2.1 := nzAt_of_nonZeroComp h j hj hG hgt hV hC G hBig t2 ht2N
  obtain ⟨ws, hwL, hwF⟩ := exists_wsize h.pins.1 wL wF
  obtain ⟨hnu, hnus⟩ := GlobalTheory.numerical_h_one_of_weighted_bound D T h j hj large₂ wL nus hH1w
  have huta2 := weightSumVector_secondGeneratorWeight_definite hG2
  obtain ⟨Pet', gPet, hI2et⟩ := exists_htI2et hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' tableLineDegreeFive tableLineDegreeTwo Prw POb
  have hnz : NoCommonZero (T.Q.Xo j) T.Q.c fun k => (G.w (e k)).1 := by
    intro k _ _ _ y
    obtain ⟨i, hi⟩ := hBig.1 k y
    exact ⟨e.symm i, by simpa only [e.apply_symm_apply] using hi⟩
  have hcomb : CombAlg (T.Q.Xo j) T.Q.c (fun k => (G.w (e k)).1) et.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) (0 / (2 * ((1 : ℕ) : ℝ))) := by
    intro la v hv
    refine ⟨hint _ _ hetM la v hv, fun _ => ?_⟩
    rw [zero_div, EReal.coe_zero, zero_mul, add_zero, hnus, e.iInf_comp (g := fun k => v (G.w k).1)]
    exact hval la v hv
  have hpl : Nonempty (HeightOneSpectrum (𝓞 T.Q.c.F)) := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 T.Q.c.F)
    exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField _)⟩⟩
  have hwd : ∀ k, (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb).w (e.symm k) = valC hG (wtA wL) wL.n (G.w k).1 := fun k => by
    show valC hG (wtA wL) wL.n (G.w (e (e.symm k))).1 = _
    rw [e.apply_symm_apply]
  have hwd0 : ∀ Z, (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb).w ((dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb).jc Z) Z ≠ 0 := fun Z => valC_ne_zero (hwb Z)
  have ha1 : A1Bigness (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb) :=
    GlobalTheory.BigRec.independent_differentials_ratios_cusp_forms_trdeg D T h j hj hG ka wL wF G (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb) e.symm rfl hwd hwd0 hBig.2
  obtain ⟨la0⟩ := id hpl
  obtain ⟨eδ, ha4'⟩ := Basis.chosenForms_restrict_basis_functionField D T h j hj hG ka wL wF G S g0 la0 (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb) e.symm rfl hwd hwd0 hH (hbas la0)
  have ha4 : A4Selection (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb) eδ := ha4' eδ (fun _ => rfl) rfl
  have hdel : (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb).del = G.del := Fin.equiv_iff_eq.1 ⟨eδ⟩
  obtain ⟨-, -, hdiv, hst⟩ := GlobalTheory.Reg.kap_divFin_stLoc_dataOf _ _ _ _ _ _ hG δ fn yP (WeightFamilies.dimY D j) N 0 1 1 0 (wtA wL, wL.n) (wtA wF, wF.n) (wtA wL, wL.n) (wtA wL, wL.n) (wtA wL, wL.n) (0, 0) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) 0 Fin.elim0 (wtA wF, wF.n) 0 Fin.elim0 ∅ et.1 1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) (fun _ _ _ => 0) ws (WeightAlgebra.DF wL : ℝ) PN' 1 1 PP0' 1 Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb 0 0 (by omega) hdim.symm hwb ha1
  have ha3 : LawA3' (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb) := lawA3'_of _ δ (fun _ _ => rfl) hdiv (hFr _ hdiv)
  have ha13 : A13Measurable (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb) := lawA13_of_data hG δ fn yP (WeightFamilies.dimY D j) N 0 1 1 0 (wtA wL, wL.n) (wtA wF, wF.n) (wtA wL, wL.n) (wtA wL, wL.n) (wtA wL, wL.n) (0, 0) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) 0 Fin.elim0 (wtA wF, wF.n) 0 Fin.elim0 ∅ et.1 1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) (fun _ _ _ => 0) ws (WeightAlgebra.DF wL : ℝ) PN' 1 1 PP0' 1 Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb 0 0
    ((GlobalTheory.FrameNorm.nrmAlong_of_fnPin _ _ _ _ _ _ _ _ hU _ fn hx hpin hG yP hyP).2 _ _ _ _ _ hst htr hwb)
  have hbdd := lawBdd_dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb hcx huta2 (fun k => hsec _ _) (fun k => (hsup _ _).1) (fun k => hsec _ _)
    (fun k => (hsup _ _).1) (hsec _ _) (hsup _ _).1 (hsec _ _) (hsup _ _).1
  have ha2 := secondHeightLaw_of_regularUniformisation hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb hreg hgt hT hTQ (dom_wtA wL) (dom_wtA wF) (dom_wtA w2)
    (fun k => hcusp _ _) (fun k => hint _ _ (hTW.2.1 _)) (fun k => hcusp _ _) (fun k => hint _ _ (hthM _))
    (hcusp _ _) (hint _ _ hetM) hetN (hcusp _ _) (hint _ _ ht2M) ht2Z huta2
  have hnum : NumOK (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb) := by
    refine ⟨hD3, le_rfl, le_rfl, le_rfl, zero_le_one, ?_, hL1.trans hwL.ge, hDF.trans hwL.ge, ?_, hnK, hrd,
      gPN, le_rfl, le_rfl, gPP0, le_rfl, gGc, gPI4, gPet, gP14, gP16, gPrw, gPO⟩
    · show (0 : ℝ) * _ ≤ 1 / 2
      norm_num
    · show Real.log (N + 1 : ℕ) + 1 / 2 ≤ Prw * (ws (wtZ (wtA wL) wL.n) - 1)
      rw [hwL, ← hN]
      exact hrw
  have hnu' : NumericalH1Condition T.Q.c (fun la => nus la / (ramOverZ la : ℝ)) PN' (ws (wtZ (wtA wL) wL.n)) := by
    refine ⟨hnu.1, hnu.2.1, hnu.2.2.trans ?_⟩
    rw [hwL]
    exact mul_le_mul_of_nonneg_right hPN (by linarith)
  have hH1 : (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb).FinitePlaceHyp := height_H1_of_data hG δ fn yP (WeightFamilies.dimY D j) N 0 1 1 0 (wtA wL, wL.n) (wtA wF, wF.n) (wtA wL, wL.n) (wtA wL, wL.n) (wtA wL, wL.n) (0, 0) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) 0 Fin.elim0 (wtA wF, wF.n) 0 Fin.elim0 ∅ et.1 1 t2.1 (fun la => nus la / (ramOverZ la : ℝ)) (fun _ _ _ => 0) ws (WeightAlgebra.DF wL : ℝ) PN' 1 1 PP0' 1 Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb 0 0 (T.U j) hreg (dom_wtA wL) (dom_wtA wL)
    (fun k => hcusp _ _) (hcusp _ _) hnz hetN hwb (wt_et _) le_rfl hcomb _ _ _ hTO hnu'
  have hF1d : (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb).TrivialPlaceHyp := height_F1_of_data hG δ fn yP (WeightFamilies.dimY D j) N 0 1 1 0 (wtA wL, wL.n) (wtA wF, wF.n) (wtA wL, wL.n) (wtA wL, wL.n) (wtA wL, wL.n) (0, 0) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) 0 Fin.elim0 (wtA wF, wF.n) 0 Fin.elim0 ∅ et.1 1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) (fun _ _ _ => 0) ws (WeightAlgebra.DF wL : ℝ) PN' 1 1 PP0' 1 Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb 0 0 (T.U j) hreg hTQZ (dom_wtA wL) (dom_wtA wL)
    (fun k => hcusp _ _) (hcusp _ _) hnz hetN (wt_et _) le_rfl _ hcomb
  have hn96 : (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb).n96 = (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) := by
    show 8 * ((WeightFamilies.dimY D j + 2) * (N + 1)) ^ 2 * (WeightFamilies.dimY D j + 1) * (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb).del * (1 + ⌈POb⌉₊) = _
    rw [hdel, ← hN]
  have hn1 : 1 ≤ (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) := by
    have h1 := one_le_del hne _ _ ha4
    rw [hdel] at h1
    have h2 : 0 < G.N := by omega
    have h3 : 0 < G.del := h1
    exact Nat.succ_le_of_lt (by positivity)
  have hLAM : (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb).HtLAM := by
    refine htLAM_of h.toLawsCore j hG δ fn yP (WeightFamilies.dimY D j) N 0 1 1 0 (wtA wL, wL.n) (wtA wF, wF.n) (wtA wL, wL.n) (wtA wL, wL.n) (wtA wL, wL.n) (0, 0) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) 0 Fin.elim0 (wtA wF, wF.n) 0 Fin.elim0 ∅ et.1 1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) (fun _ _ _ => 0) ws (WeightAlgebra.DF wL : ℝ) PN' 1 1 PP0' 1 Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb 0 0 large₂ CL AL (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) hgt ?_ hlam ?_
      (Generic.supPTGe_of_fnPin D T.toCore h.toLawsCore j hj fn hpin hG yP hyP _) ?_
    · exact (wtZ_wsmul _ _).trans (congrArg (fun n : ℕ => n • wtZ (wtA wL) wL.n) hn96.symm)
    · have h1 := prodInLat_of_wtZ h.toLawsCore j hj (fun k => (G.w (e k)).1) wL _ _
        (fun k => ⟨G.w (e k), hTW.2.1 _, rfl⟩) hn1 (wtZ_wsmul _ _)
      exact Eq.mp (congrArg (ProdInLat h.toLawsCore j (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) fun k => (G.w (e k)).1) hn96.symm) h1
    · exact Eq.mp (congrArg₂ (LamConst j large₂ CL AL (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) PP0') hn96.symm hwL.symm) hlc
  have hSup := htSup_dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb hgt hfn hfg hcx huta2
    (fun k => hsec _ _) (fun k => (hsup _ _).1) (fun k => hNZ _ _)
    (fun k => hsec _ _) (fun k => (hsup _ _).1) (fun k => hNZ _ _) (hsec _ _) (hsup _ _).1 (hNZ _ _) G.mx
    (fun σ k => ((congrArg Real.log ((hsup _ _).2 σ)).le).trans (hTW.2.2.2.1 σ _))
    (by rw [hwL]; exact hTW.2.2.2.2)
    (fun k => by
      rw [hwF]
      simp only [(hsup wF (G.th' k)).2]
      exact (hTT k).2)
    (by rw [hwL]; positivity)
    (fun σ => by
      rw [hwL]
      exact ((congrArg Real.log ((hsup _ _).2 σ)).le).trans (ht2S σ))
  have hI2be := htI2be_dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb (T.U j) (xiR D)
    (hnt N (fun k => (G.w (e k)).1) (wtA wL, wL.n) et.1 (wtA wL, wL.n) (dom_wtA wL) (dom_wtA wL)
      (fun k => hsec _ _) (hsec _ _))
    (fun σ hσ k x hx => by
      rw [e.sum_comp fun k' => recNrm (T.U j σ) (xiR D) (wtA wL) wL.n (G.w k').1 k x ^ 2]
      exact harch σ hσ k x hx)
  obtain ⟨hd, hs, hsel, hcon⟩ := exists_htConcl hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb hgt hne hfg htr hac hwb hetN ht2Z huta2 hfn hconj hbdd ha1 ha2
    ha3 eδ ha4 hnum ha13 hH1 hF1d hLAM hSup hI2et hI2be
  have hI := GlobalTheory.T.lengths_at_primes_le_functionField_data_of_curve D T h j hj hG ka wL wF G S g0 hH hV hC hB y hw hcur htie δ hT (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb) hd hs e rfl
    (fun _ _ => rfl) rfl rfl (fun _ => rfl) eδ (fun k => by rw [hsel]; rfl) Gc PH Prw Pet
  refine heights_of_first (B := recB h.toLawsCore) (dat hG δ fn yP (WeightFamilies.dimY D j) N (wtA wL, wL.n) (wtA wF, wF.n) (wtA w2, w2.n) (fun k => (G.w (e k)).1) jc G.del (fun k => (G.th' k).1) et.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) ws (WeightAlgebra.DF wL : ℝ) PN' PP0' Gc PI4' Pet' tableLineDegreeFive tableLineDegreeTwo Prw POb) hd hs G _ Gc PH Prw Pet (by omega) rfl hdel hwL rfl
    hPH.symm rfl ?_ hI hcon
  rw [← eδ.sum_comp]
  refine Finset.sum_le_sum fun k _ => ?_
  show ReciprocityTheory.ChartRestriction.G.T0.meanK (fun σ => Real.log
      (⨆ p : (Σ Z : Comp (T.Q.Xo j) T.Q.c, ReciprocityTheory.ChartRestriction.G.T0.PT (Ω := Om Z) σ),
        nrmC fn (yP p.1) (wtZ (wtA wF) wF.n) (valC hG (wtA wF) wF.n (G.th' (hd.sel k)).1 p.1) p.2)) ≤ _
  rw [hsel]
  refine (meanK_mono' fun σ => log_sup_le hfn hfg hcx (hsec _ _) (hsup _ _).1 (hNZ _ _) σ).trans (le_of_eq ?_)
  simp only [(hsup wF (G.th' (eδ k))).2]
  rfl

end GlobalTheory.HeightDefinite
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.HeightInequalityDefiniteLiftIndexStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heightInequality_definite_liftIndex : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → ∀ (y : ∀ la, PtsG G la → (extAll h j hj).Pt' la) (hw : ∀ la ζ, FromW (E := extAll h j hj) (hM := intAtExt_extAll h j hj) ζ (y la ζ)), (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InCurve) → (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InTie S) → j = D.R.m → FnAlgClosed (Xo := (T.Q.Xo j)) (c := T.Q.c) → 3 ≤ WeightFamilies.dimY D j → 0 < wL.n → (∀ la, InBasis G la) → ∀ (large₂ : SizeData₂ D) (Gc PH Prw Pet PN' PP0' PI4' tableLineDegreeFive tableLineDegreeTwo POb CL AL : ℝ) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (w2 : WeightFamilies.Wt D j) (t2 : (recB h.toLawsCore).Cusp j w2), G.TiedW S Gc Prw → G.TiedTh S Gc → (∀ i, G.th' i ∈ (recB h.toLawsCore).Mlat j wF) → IsG2 wL wF w2 → t2 ∈ (recB h.toLawsCore).Mlat j w2 → (recPlus h j hj).NonZeroComp w2 t2 → (∀ σ, Real.log ((recB h.toLawsCore).supN j w2 σ t2) ≤ PI4' * (WeightFamilies.dimY D j : ℝ) * wL.size) → WeightedPrimeSumBoundAlt large₂ (recPJ h j hj) wL nus → WeightAlgebra.PN D large₂ ≤ PN' → LAMwAt large₂ (recB h.toLawsCore) j (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) CL AL → LamConst j large₂ CL AL (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) PP0' (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL.size → 1 ≤ wL.size → (WeightAlgebra.DF wL : ℝ) ≤ wL.size → Real.log G.N + 1 / 2 ≤ Prw * (wL.size - 1) → Real.log (Module.finrank ℚ T.Q.c.F) ≤ POb → Real.log (|(NumberField.discr T.Q.c.F : ℝ)| ^ (1 / (Module.finrank ℚ T.Q.c.F : ℝ))) ≤ POb → 1 ≤ PN' → 1 ≤ PP0' → 1 ≤ Gc → 1 ≤ PI4' → 1 ≤ Pet → 1 ≤ tableLineDegreeFive → 1 ≤ tableLineDegreeTwo → 1 ≤ Prw → 1 ≤ POb → PH = 2 * (PP0' + PN' + tableLineDegreeFive + tableLineDegreeTwo + PI4' + Prw) + Gc → (∀ la, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la, (⨅ k, v (G.w k).1) ≤ (nus la : EReal)) → (∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ ((T.U j σ).X k).dom → -Real.log (Real.sqrt (∑ k', recNrm (T.U j σ) (xiR D) (wtA wL) wL.n (G.w k').1 k x ^ 2)) ≤ tableLineDegreeFive * (WeightAlgebra.DF wL : ℝ)) → Heights (fun la => (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0)) Gc PH Prw Pet := by
  first | exact @GlobalTheory.HeightDefinite.heights_definite | exact GlobalTheory.HeightDefinite.heights_definite | (intros; apply GlobalTheory.HeightDefinite.heights_definite <;> assumption)
end
