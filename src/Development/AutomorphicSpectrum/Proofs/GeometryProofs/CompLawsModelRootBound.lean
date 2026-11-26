module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentNormConstantModels
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerWeightOfZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPosLowerBoundSections
section -- merged from Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FullTranscendenceDegree
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FullTranscendenceDegree

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Pj
  Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)

abbrev CuspAt (u : WeightFamilies.Wt D j) : Type := (recB h.toLawsCore).Cusp j u

abbrev XP : WeightAlgebra.PJ D (recB h.toLawsCore) T.G.P j :=
  xplus (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj)

def GeneratesIn {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j) {wL : WeightFamilies.Wt D j} {N : ℕ}
    (s : 𝓞 B.KO) (w : Fin N → B.Cusp j wL) : Prop :=
  Submodule.span (𝓞 B.KO) (Set.range w) = X.WWc s wL

def Generates {wL : WeightFamilies.Wt D j} {N : ℕ} (s : 𝓞 T.Q.c.F) (w : Fin N → CuspAt h j wL) : Prop :=
  GeneratesIn (XP h j hj) s w

def ptNorm (σ : T.Q.c.F →+* ℂ) (u : WeightFamilies.Wt D j) (F : CuspAt h j u) (p : FPt (T.U j σ).X) : ℝ :=
  ((T.U j σ).X p.1).pnorm (laU (T.U j σ) (wtA u) u.n p.1) (rdU (T.U j σ) (F.1 : T.R j) p.1) p.2.1

def l2Norm (σ : T.Q.c.F →+* ℂ) {wL : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → CuspAt h j wL)
    (p : FPt (T.U j σ).X) : ℝ :=
  Real.sqrt (∑ i, ptNorm h j σ wL (w i) p ^ 2)

def NoCommonZero {wL : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → CuspAt h j wL) : Prop :=
  ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ p : FPt (T.U j σ).X,
    ∃ i, rdU (T.U j σ) ((w i).1 : T.R j) p.1 p.2.1 ≠ 0

def FullTrdeg (hg : GenFrEx (T.Q.Xo j) T.Q.c) {wL : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → CuspAt h j wL) : Prop :=
  ∀ Z : Comp (T.Q.Xo j) T.Q.c, ∃ i₀, evC hg Z ((w i₀).1 : T.R j) ≠ 0 ∧
    Algebra.trdeg T.Q.c.F (IntermediateField.adjoin T.Q.c.F
      (Set.range fun i => evC hg Z ((w i).1 : T.R j) / evC hg Z ((w i₀).1 : T.R j))) = (WeightFamilies.dimY D j : Cardinal)

def SmallForm {wL : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → CuspAt h j wL) : Prop :=
  ∃ (k m₀ : ℕ) (β : CuspAt h j (WeightAlgebra.wsmul k wL)), (XP h j hj).NonZeroComp (WeightAlgebra.wsmul k wL) β ∧
    ∃ C : ℝ, ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ p : FPt (T.U j σ).X,
      ptNorm h j σ (WeightAlgebra.wsmul k wL) β p ≤ C * l2Norm h j σ w p ^ k ∧
      ptNorm h j σ (WeightAlgebra.wsmul k wL) β p ^ m₀ ≤ C * l2Norm h j σ w p ^ (k * m₀ + 1)

def BigAt (hg : GenFrEx (T.Q.Xo j) T.Q.c) {wL : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → CuspAt h j wL) : Prop :=
  NoCommonZero h j w ∧ FullTrdeg h j hg w ∧ SmallForm h j hj w

def ExistsNonzeroCuspFormOfWeightPair (wL wF : WeightFamilies.Wt D j) : Prop :=
  ∃ w₂ : WeightFamilies.Wt D j, WeightAlgebra.IsG2 wL wF w₂ ∧ ∃ θ : CuspAt h j w₂, (XP h j hj).NonZeroComp w₂ θ

def CurveModelAt (hg : GenFrEx (T.Q.Xo j) T.Q.c) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (XP h j hj) ka wL wF)
    (S : WeightAlgebra.Scal (recB h.toLawsCore)) : Prop :=
  Generates h j hj S.sW G.w → BigAt h j hj hg G.w → ExistsNonzeroCuspFormOfWeightPair h j hj wL wF →
    ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (g₀ : CuspAt h j wF), (XP h j hj).NonZeroComp wF g₀ →
      Nonempty (CurveModel (X := recPJ h j hj) (E := extAll h j hj) (hM := intAtExt_extAll h j hj) G la g₀)

def CurveModelExists : Prop :=
  ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hg : GenFrEx (T.Q.Xo j) T.Q.c)
    (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (XP h j hj) ka wL wF) (S : WeightAlgebra.Scal (recB h.toLawsCore)),
    CurveModelAt h j hj hg G S

theorem ptNorm_nonneg (σ : T.Q.c.F →+* ℂ) (u : WeightFamilies.Wt D j) (F : CuspAt h j u) (p : FPt (T.U j σ).X) :
    0 ≤ ptNorm h j σ u F p :=
  mul_nonneg (norm_nonneg _) (pnorm_fac_nonneg _ _ _)

end GlobalTheory.IndefiniteRowSideFullHecke.FullTranscendenceDegree
end
end

noncomputable section

namespace GlobalTheory.BignessCompare

open _root_.Formalism.L2.Pj NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.IndefiniteRowSideFullHecke.FullTranscendenceDegree (CuspAt XP Generates ptNorm l2Norm FullTrdeg SmallForm ExistsNonzeroCuspFormOfWeightPair CurveModelAt CurveModelExists
  ptNorm_nonneg)

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {κ : Type} [Fintype κ]

theorem bdd_of_mem_holSub (X : κ → Data E r) (la : ∀ c, Wt (X c).Ψ r) {P : FDSec X} (hP : P ∈ holSub X la) :
    ∃ M : ℝ, ∀ p : FPt X, (X p.1).pnorm (la p.1) (P p.1) p.2 ≤ M := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    choose C hC using fun c => (hP c).1.2
    refine ⟨∑ c, |C c|, fun p => (hC p.1 p.2 p.2.2).trans ((le_abs_self _).trans ?_)⟩
    exact Finset.single_le_sum (f := fun c => |C c|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
  | zero => exact ⟨0, fun p => (pnorm_zero _ _ _).le⟩
  | add P Q _ _ hP hQ =>
    obtain ⟨a, ha⟩ := hP
    obtain ⟨b, hb⟩ := hQ
    exact ⟨a + b, fun p => (pnorm_add_le _ _ _ _ _).trans (add_le_add (ha p) (hb p))⟩
  | smul a P _ hP =>
    obtain ⟨b, hb⟩ := hP
    exact ⟨‖a‖ * b, fun p => (pnorm_smul _ _ a _ _).le.trans (mul_le_mul_of_nonneg_left (hb p) (norm_nonneg _))⟩

end Model

section Weights

variable {D : D7} {j : ℕ}

end Weights

section Record

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)

variable {ι : Type} (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)] (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)
  (hinj : ∀ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), (∀ Z, gF Z (X.inc u F) = 0) → F = 0)


end Record

section Inst

variable {D : D7} {T : Formalism.L2.Pj.Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  {ka wL wF : WeightFamilies.Wt D j}






end Inst

end GlobalTheory.BignessCompare
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompLawsModelRootBound
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug.CuspHodge

theorem mem_ptsOver_mcPts {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)}
    {z : (Σ k, ι k) → ℂ} (h : z ∈ mcPts P) : z ∈ Small.ptsOver ℂ P := by
  refine ⟨h.1, fun f hf => ?_⟩
  have := h.2 f hf
  rw [MvPolynomial.eval_map] at this
  rw [MvPolynomial.aeval_def]
  exact this

theorem exists_form_const {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) (hb : Birational y) {F : Type} [Field F] [NumberField F] (cst : F →+* Ω) :
    ∃ v : MRing ι, Small.IsFormOff (mCoordIdeal y) v ∧ ∀ z ∈ mcPts (mCoordIdeal y), MvPolynomial.aeval z v ≠ 0 →
      ∃ σ : F →+* ℂ, ∀ t : F, Small.HasVal y 0 (cst t) z (σ t) := by
  classical
  haveI : CharZero Ω := charZero_of_injective_ringHom cst.injective
  let b := Module.finBasis ℚ F
  obtain ⟨v, hv, H⟩ := GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ValSub.exists_subring_val K ι Ω y hb
    (Finset.univ.image fun i => cst (b i))
  refine ⟨v, hv, fun z hz hzv => ?_⟩
  obtain ⟨A, ev, hB, hinv, hval⟩ := H ℂ z (mem_ptsOver_mcPts hz) hzv
  have hq : ∀ q : ℚ, cst (algebraMap ℚ F q) ∈ A := fun q => by
    have e : cst (algebraMap ℚ F q) = (q.num : Ω) * ((q.den : ℕ) : Ω)⁻¹ := by
      have e1 : cst (algebraMap ℚ F q) = (q : Ω) := eq_ratCast (cst.comp (algebraMap ℚ F)) q
      rw [e1, Rat.cast_def, div_eq_mul_inv]
    rw [e]
    exact A.mul_mem (intCast_mem A _) (hinv _ q.den_nz)
  have hA : ∀ t : F, cst t ∈ A := fun t => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr t, map_sum]
    refine A.sum_mem fun i _ => ?_
    rw [Algebra.smul_def, map_mul]
    exact A.mul_mem (hq _) (hB (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ i))))
  exact ⟨ev.comp (cst.codRestrict A hA), fun t => hval ⟨cst t, hA t⟩⟩

theorem cusp_hodgeLe : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (Z : Comp Xo c) (Rd : Reading Fr h Z) (u : GlobalTheory.AllWt.Weight Dw), ∀ f ∈ GlobalTheory.AllWt.cuspOn U Z (GlobalTheory.AllWt.wtOf Dw u 0), ∃ R : ℝ, HodgeLe Or u (gauge Rd u * Rd.φ (evC h Z f)) R := by
  intro hG E _ _ _ H Dw l Xo c r U h e hL x hx O _ β Y SS RM Sys Fx Or Fr Z Rd u f hf
  classical
  obtain ⟨a, ha⟩ : ∃ a, a = (GlobalTheory.AllWt.wtOf Dw u 0).1 := ⟨_, rfl⟩
  obtain ⟨hw1, hw2, -, hw4, -⟩ := GlobalTheory.CompanionTheory.Ar.Plug.integer_weights_vocab E H Dw l Xo c RM u
  rw [← ha] at hw1 hw2
  obtain ⟨-, -, hco, -, -⟩ := GlobalTheory.T.all_weight_sections_compat E H Dw l Xo c r U h e hL a Z
  rw [hw2, ← hco] at hf
  have hcz : f ∈ GlobalTheory.CompanionTheory.Ar.Rec.cuspZ Xo c U a := hf.1
  have hsec : f ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a := hcz.1
  have hhol : ∀ σ, GoodEmb c σ → rdU (U σ) f ∈ holSub (U σ).X (laZ (U σ) a) := fun σ hσ => by
    have h2 : f ∈ ⨅ (σ : c.F →+* ℂ) (_ : GoodEmb c σ), (holSub (U σ).X (laZ (U σ) a)).comap (rdU (U σ)) := hcz.2
    exact (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 h2 σ) hσ
  have hM : ∀ σ : c.F →+* ℂ, ∃ M : ℝ, 0 ≤ M ∧ (GoodEmb c σ → ∀ k, ∀ y ∈ ((U σ).X k).dom,
      ((U σ).X k).pnorm (laZ (U σ) a k) (rdU (U σ) f k) y ≤ M) := fun σ => by
    by_cases hσ : GoodEmb c σ
    · obtain ⟨M, hM⟩ := GlobalTheory.BignessCompare.bdd_of_mem_holSub (U σ).X (laZ (U σ) a) (hhol σ hσ)
      exact ⟨|M|, abs_nonneg M, fun _ k y hy => (hM ⟨k, ⟨y, hy⟩⟩).trans (le_abs_self M)⟩
    · exact ⟨0, le_rfl, fun h' => absurd h' hσ⟩
  choose M hM0 hMb using hM
  obtain ⟨u₀, hu₀, hread⟩ := GlobalTheory.T.component_norm_constant_models hG E H Dw l Xo c r U h e hL x hx O β Y SS RM Sys Fx Or Fr Z Rd
  obtain ⟨v, hv, hcst⟩ := exists_form_const RM.y RM.birational Or.𝔐.cst
  have hform : Small.IsFormOff (mCoordIdeal RM.y) (u₀ * v) := by
    obtain ⟨d₁, h₁⟩ := hu₀.1
    obtain ⟨d₂, h₂⟩ := hv.1
    refine ⟨⟨_, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul h₁ h₂⟩, fun h' => ?_⟩
    have hp : (mCoordIdeal RM.y).IsPrime := RingHom.ker_isPrime _
    rcases hp.mem_or_mem h' with h' | h'
    · exact hu₀.2 h'
    · exact hv.2 h'
  have hgauge : gauge Rd u * Rd.φ (evC h Z f) = Fr.rd f * ∏ r', Or.e r' ^ (-nOf u (some r')) := by
    rw [Rd.rd_eq a f hsec, gauge, ← ha]
    ring
  have hn' : ∀ j, (nOf u j : ℝ) = RM.coef (towerWt Dw a) 0 j := fun j => by
    rw [hw1]
    exact hw4 j
  refine ⟨lieFacZ Dw x a * ∑ σ, M σ, u₀ * v, hform, fun z hz hne w hw => ?_⟩
  rw [map_mul] at hne
  obtain ⟨σ, hσ⟩ := hcst z hz (right_ne_zero_of_mul hne)
  obtain ⟨k, -, y, hy, hr⟩ := hread σ z hz hσ (left_ne_zero_of_mul hne)
  obtain ⟨θ, hθ, hval⟩ := hr a (nOf u) hn'
  obtain ⟨hg, hb⟩ := hval f hsec
  have hzp := mem_ptsOver_mcPts hz
  have hw' : Small.HasVal RM.y (Top.combLine (RM.line 1) (nOf u)).a
      (Fr.rd f * ∏ r', Or.e r' ^ (-nOf u (some r'))) z w := by
    rw [← hgauge]
    exact hw
  have hnorm : ‖w‖ = ‖θ‖ * ‖rdU (U (goodOf c σ)) f k y‖ := by
    by_cases hgd : GoodEmb c σ
    · rw [GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest.hasVal_unique hzp hw' (hg hgd), norm_mul]
    · rw [GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest.hasVal_unique hzp hw' (hb hgd), norm_mul, RCLike.norm_conj]
  have hP : 0 < ∏ r', (Or.sing r').h z ^ nOf u (some r') :=
    Finset.prod_pos fun r' _ => zpow_pos ((Or.sing r').pos z hz.1) _
  have hL0 : 0 < lieFacZ Dw x a := Real.exp_pos _
  have hmain : ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a k) (fun _ => 1) y * ‖rdU (U (goodOf c σ)) f k y‖ =
      ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a k) (rdU (U (goodOf c σ)) f k) y := by
    simp only [ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm, norm_one, one_mul]
    ring
  have hbd : ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a k) (rdU (U (goodOf c σ)) f k) y ≤ ∑ σ, M σ :=
    (hMb _ (goodEmb_goodOf c σ) k y hy).trans
      (Finset.single_le_sum (f := M) (fun i _ => hM0 i) (Finset.mem_univ _))
  rw [hnorm, hθ, mul_assoc, mul_assoc, hmain]
  calc _ ≤ (∏ r', (Or.sing r').h z ^ nOf u (some r')) * (lieFacZ Dw x a * ∑ σ, M σ) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbd hL0.le) hP.le
    _ = _ := by ring

end GlobalTheory.CompanionTheory.Ar.Plug.CuspHodge
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompLawsModelRootBoundStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comp_laws_model_root_bound : GlobalTheory.CompanionTheory.Ar.Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (Z : Comp Xo c) (Rd : Reading Fr h Z) (u : GlobalTheory.AllWt.Weight Dw), ∀ f ∈ GlobalTheory.AllWt.cuspOn U Z (GlobalTheory.AllWt.wtOf Dw u 0), ∃ R : ℝ, HodgeLe Or u (gauge Rd u * Rd.φ (evC h Z f)) R := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.CuspHodge.cusp_hodgeLe | exact GlobalTheory.CompanionTheory.Ar.Plug.CuspHodge.cusp_hodgeLe | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.CuspHodge.cusp_hodgeLe <;> assumption)
end
