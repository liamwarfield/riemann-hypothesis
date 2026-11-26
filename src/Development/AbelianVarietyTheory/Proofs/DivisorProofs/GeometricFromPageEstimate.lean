module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ParametersOkOfLaws
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsThresholdRunHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMomentMatrixTransform
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GamAtOfLawsCore

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsConstantsIndexBoundHypothesesLiftWeights
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsConstantsIndexBoundHypothesesLiftWeights
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin GlobalTheory.FinalJoin2

namespace GlobalTheory.FinalJoin2

theorem hyp_concl_at_run : ∃ (CK : ℝ) (x₁ : ℝ), ∀ (D : D7) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ), (∀ j, InR D j → ParOK T EX p j) → ∀ (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D), SizesAt L → Pm.CnW = 10 → (∀ i, Real.log (D.host.g i) ≤ 9 * L.sc.L + 1) → 1000 ≤ Tp.CP → Tp.CP ^ 20 ≤ zBase L → x₁ ≤ L.sc.x → FieldSmall D L → (∀ (j : ℕ) (hj : InR D j), HypC L (recPJ h j hj) ⟨CK, 20, Tp.CP, Tp.eP, Tp.CP, Tp.eP, 7⟩ Tp.CP Tp.eP 7 0 L.Ct (scalOfP (recB (h).toLawsCore) hinj EX p (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO) (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO Tp.nP Tp.nWn (LevelStarExponents.h0 L - 4) (nusR h j (lR Tp hK j)) ∧ Concl (recPJ h j hj) (scalOfP (recB (h).toLawsCore) hinj EX p (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO) (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO (nusR h j (lR Tp hK j)) ((recPJ h j hj).rk (kaR Tp hK j) ((recB (h).toLawsCore).Mlat j (kaR Tp hK j)) * D.R.f * D.R.m * L.sc.b * L.de2)) := by
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.FinalJoin.runHolds_of_parOK
  obtain ⟨CK, hCK⟩ := GlobalTheory.FinalJoin.RecordRun.exists_pageRun_record_sub_four
  refine ⟨CK, max ((10 : ℝ) ^ 60) (x₀ 20 CK), ?_⟩
  intro D T h hinj EX p hpar L Pm Tp hK hS hC hg hCP hz hx hF j hj
  have hO : OPO L (recB h.toLawsCore) := (fieldSmall_iff_opo D T h L).1 hF
  have hP := hCK D L Pm Tp hK hS hC hg ((le_max_left _ _).trans hx) hCP hz _ _ j (recPJ h j hj) hj hO
  exact (hx₀ D T h hinj EX p hpar j hj L _ _ _ _ _ _ _ _ _ _ _ hP ((le_max_right _ _).trans hx)).2

end GlobalTheory.FinalJoin2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsConstantsIndexBoundHypothesesLiftWeightsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin GlobalTheory.FinalJoin2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_constants_indexBound_hypotheses_liftWeights : ∃ (CK : ℝ) (x₁ : ℝ), ∀ (D : D7) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ), (∀ j, InR D j → ParOK T EX p j) → ∀ (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D), SizesAt L → Pm.CnW = 10 → (∀ i, Real.log (D.host.g i) ≤ 9 * L.sc.L + 1) → 1000 ≤ Tp.CP → Tp.CP ^ 20 ≤ zBase L → x₁ ≤ L.sc.x → FieldSmall D L → (∀ (j : ℕ) (hj : InR D j), HypC L (recPJ h j hj) ⟨CK, 20, Tp.CP, Tp.eP, Tp.CP, Tp.eP, 7⟩ Tp.CP Tp.eP 7 0 L.Ct (scalOfP (recB (h).toLawsCore) hinj EX p (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO) (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO Tp.nP Tp.nWn (LevelStarExponents.h0 L - 4) (nusR h j (lR Tp hK j)) ∧ Concl (recPJ h j hj) (scalOfP (recB (h).toLawsCore) hinj EX p (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO) (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO (nusR h j (lR Tp hK j)) ((recPJ h j hj).rk (kaR Tp hK j) ((recB (h).toLawsCore).Mlat j (kaR Tp hK j)) * D.R.f * D.R.m * L.sc.b * L.de2)) := by
  first | exact @GlobalTheory.FinalJoin2.hyp_concl_at_run | exact GlobalTheory.FinalJoin2.hyp_concl_at_run | (intros; apply GlobalTheory.FinalJoin2.hyp_concl_at_run <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LatAtAndSpanAtOfHypC
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps GlobalTheory

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.RunLat

theorem thc_le_shortTh {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j)
    (s : 𝓞 B.KO) (w : WeightFamilies.Wt D j) : X.Thc s w ≤ X.shortTh w := by
  intro x hx
  simp only [PJ.Thc, PJ.scaled, Submodule.mem_map, LinearMap.smul_apply, LinearMap.id_apply] at hx
  obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := hx
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hz)

theorem spanAt_of_shortG {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j)
    (s : 𝓞 B.KO) (w : WeightFamilies.Wt D j) (β : ℝ) (h : WeightAlgebra.ShortG X w (X.Thc s w) β) : PullbackSections.SpanAt X w := by

  obtain ⟨Sh, hSh, hspan, -⟩ := h
  show Submodule.span _ _ = ⊤
  rw [eq_top_iff, ← hspan]
  exact Submodule.span_mono fun x hx => thc_le_shortTh X s w (hSh hx)

end GlobalTheory.RunLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NusOfEqRamMulNuStarAt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

noncomputable section

namespace GlobalTheory.RunDepthScale

open Formalism.MainNotions.ModuliIntegralCharts.H1 in
theorem nusOf_eq_nuN {D : D7} (B : WeightFamilies.Prov D) {j : ℕ} (w : WeightFamilies.Wt D j)
    (nu : HeightOneSpectrum (𝓞 B.KO) → ℝ) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : DepPage)
    (h1 : Q.g1 = D.host.g 0) (h2 : Q.g2 = D.host.g 1) (hq1 : Q.q1 = D.host.q) (hdd : Q.dd = D.host.d)
    (hsm : Q.sm = D.host.small) (hvd : Q.vd = vdOf D) :
    nusOf B w nu la = (ramOverZ la : ℝ) * Q.nuN (WeightAlgebra.DF w) (nu la) (resCharOf la) := by
  classical
  have hq : D.host.q.Prime := D.host.hyp.1
  have hd : D.host.d.Prime := D.host.hyp.2.1
  unfold nusOf DepPage.nuN
  rw [H1algLink.eWL_eq la, h1, h2]
  by_cases hc : ∃ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 B.KO) ∈ la.asIdeal
  · rw [dite_eq_left hc]
    have hch := (H1algLink.prime_mem_iff la (D.host.g_prime _)).1 (Classical.choose_spec hc)
    rw [← hch, mul_div_assoc]
    congr 1
    by_cases e0 : resCharOf la = D.host.g 0
    · rw [if_pos e0, e0]
    · rw [if_neg e0]
      have e1 : resCharOf la = D.host.g 1 := by
        generalize Classical.choose hc = i at hch
        fin_cases i
        · exact absurd hch e0
        · exact hch
      rw [if_pos e1, e1]
  · rw [dite_eq_right hc]
    have e0 : ¬ resCharOf la = D.host.g 0 := fun e =>
      hc ⟨0, (H1algLink.prime_mem_iff la (D.host.g_prime 0)).2 e⟩
    have e1 : ¬ resCharOf la = D.host.g 1 := fun e =>
      hc ⟨1, (H1algLink.prime_mem_iff la (D.host.g_prime 1)).2 e⟩
    rw [if_neg e0, if_neg e1]
    congr 2
    unfold DepPage.cP DepPage.IsRam
    rw [hq1, hdd, hvd, hsm, show ringChar (𝓞 B.KO ⧸ la.asIdeal) = resCharOf la from rfl]
    have hS : ((D.host.QS : ℕ) : 𝓞 B.KO) ∈ la.asIdeal ↔ resCharOf la ∈ D.host.small :=
      (UpperTheory.cmDatum_natCast_mem_heightOneSpectrum_iff D.host.toHostRaw B.KO la).1
    simp only [hS, H1algLink.prime_mem_iff la hq, H1algLink.prime_mem_iff la hd]
    by_cases a2 : resCharOf la ∈ D.host.small
    · rw [if_pos a2, if_pos (Or.inl a2)]
      unfold c2 vdOf
      rw [if_pos a2, Int.ceil_toNat, ← Nat.cast_mul, Nat.ceil_natCast]
    · rw [if_neg a2]
      by_cases b : resCharOf la = D.host.q ∨ resCharOf la = D.host.d
      · rw [if_pos b, if_pos (Or.inr b)]
        unfold Formalism.MainNotions.DIV.Cons.cHalf vdOf
        rw [if_neg a2, Int.ceil_toNat]
        congr 2
        ring
      · rw [if_neg b, if_neg (fun h => h.elim a2 b)]
        simp

theorem nusOf_eq_ram_mul_nuStarAt : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Top D) (h : LawsP T) (EX : ErrX D) (j : ℕ), InR D j → letI := T.Q.H.starRing; ∀ la : HeightOneSpectrum (𝓞 T.Q.c.F), nusOf (recB h.toLawsCore) (lR Tp hK j) (fun la' => (nuW (T.Q.Xo j) T.Q.c la' T.Q.l.M (wtA (lR Tp hK j)) Tp.nWn).toReal / (ramOverZ la' : ℝ)) la = (ramOverZ la : ℝ) * nuStarAt (Xo := T.Q.Xo j) (c := T.Q.c) (depOf T.toCore EX Tp hK) la j := by
  intro D L Pm Tp hK T h EX j hj la
  letI := T.Q.H.starRing
  refine (nusOf_eq_nuN (recB h.toLawsCore) (lR Tp hK j) _ la (depOf T.toCore EX Tp hK).Q rfl rfl rfl rfl rfl rfl).trans ?_
  rw [← GlobalTheory.WeightExponents.DF_wtA h.pins hj (lR Tp hK j)]
  rfl

end GlobalTheory.RunDepthScale
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IndexBoundAtLargerField
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

noncomputable def coordMap {F : Type} [Field F] {K : Type} [Field K] [Algebra F K] {C : Type} [AddCommGroup C]
    [Module F C] {n : ℕ} (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) : C →ₗ[F] (Fin n → K) :=
  ((z.symm : K ⊗[F] C →ₗ[K] (Fin n → K)).restrictScalars F).comp (TensorProduct.mk F K C 1)

theorem coordMap_linearIndependent {F : Type} [Field F] {K : Type} [Field K] [Algebra F K] {C : Type} [AddCommGroup C]
    [Module F C] {n : ℕ} (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) (m : ℕ) (b : Fin m → C) (hb : LinearIndependent F b) :
    LinearIndependent K fun a => coordMap z (b a) :=
  (Module.Flat.linearIndependent_one_tmul (S := K) hb).map' (z.symm : K ⊗[F] C →ₗ[K] (Fin n → K)) z.symm.ker

theorem coordMap_span {F : Type} [Field F] {K : Type} [Field K] [Algebra F K] {C : Type} [AddCommGroup C]
    [Module F C] {n : ℕ} (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) : Submodule.span K (Set.range (coordMap z)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := z.symm.surjective x
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a f =>
    have e : a ⊗ₜ[F] f = a • ((1 : K) ⊗ₜ[F] f) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, rfl⟩)
  | add x y hx hy =>
    rw [map_add (f := _)]
    exact Submodule.add_mem _ (hx trivial) (hy trivial)

end GlobalTheory.FormTies
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunsHoldOfTies
set_option autoImplicit false

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn

theorem runsHold_of_ties : ∃ CK x₁ : ℝ, ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G), CoreTies L EX J R → RunsOk fw r → OwnPin r → PageNum Tp x₁ → RunsHold Tp hK EX CK r := by
  obtain ⟨CK, x₁, H⟩ := GlobalTheory.T.exists_constants_indexBound_hypotheses_liftWeights
  refine ⟨CK, x₁, ?_⟩
  intro D G _ _ Pl0 T0 A J _ R F κ v₀ fw L Pm Tp hK EX r hc ok hown hnum v h hinj
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hnum
  have hl := ok.laws v
  have hF : GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) := by
    unfold ownAt
    split_ifs
    · exact hc.field₂
    · exact hc.field₁
  refine H D _ h hinj EX (ownAt D v) ?_ L Pm Tp hK h1 h2 h3 h4 h5 h6 hc.small
  refine GlobalTheory.FinalJoin2.liftIndexParameterConditions_of_coreAndShortLaws D J _ EX _ hl.j h hl.sh rfl hc.canon hF hc.halfEX ?_
  intro j hj n
  exact ⟨hl.lvA j hj n, hown v j n hj⟩

end GlobalTheory.BigOn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeafDepthAllRecord
open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.BigOn.leafDepth_all_record : ∃ C0 : ℝ, ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst) (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c), IsRec Tp hK EX F fw r O → ∀ N : IndefNum A.fam.base, LeafPage O → LeafSizes O → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → Formalism.L2.Indef.Tree.DepthCond.ContentEqualsDatumContent N (GlobalTheory.RunDepth.numOf D L) (fun j : Fin D.R.m => (j : ℕ) + 1) → C0 ≤ c.C → 10 ≤ Pm.CnW → 3 ≤ L.sc.x ^ (L.sc.ez / 5) → LeafDepthGood N O ∧ LeafDepthRam N O ∧ LeafDepth2 N O ∧ LeafDepthLevel N O := by
  obtain ⟨C0, h⟩ := GlobalTheory.RunDepth.leafDepth_all_run GlobalTheory.ChF.colength_bound_split_place_chart
    GlobalTheory.ChF.hodgeTate_inclusion_chart GlobalTheory.ChF.unramified_companion_chart_characters
  refine ⟨C0, ?_⟩
  intro D G _ _ Pl0 T0 A J _ R F κ v₀ fw L Pm Tp hK EX r c O hrec N hPg hSz hx hb tF hC hn he
  obtain ⟨st, hd⟩ := hrec.depth
  obtain ⟨hc, -⟩ := hrec.tied
  letI := st
  letI := hostAlg D
  exact h D L Pm Tp hK J.toCore EX D.what₂.LL _ _ _ _ c O _ N hc.toLawsM hd hPg hSz hx hb tF hC hn he
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasIndexBoundOfRuns
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.BigOn

theorem isLattice_of_spanK {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] {C : Type}
    [AddCommGroup C] [Module F C] [Module (𝓞 F) C] [IsScalarTower (𝓞 F) F C] {n : ℕ}
    (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) (M : Submodule (𝓞 F) C) (h : IsLatIn ⊤ (spanK z (M : Set C))) :
    Submodule.IsFullLattice F M := by
  have hinj : Function.Injective (coordMap z) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : z.symm ((1 : K) ⊗ₜ[F] x) = 0 := hx
    rw [LinearEquiv.map_eq_zero_iff] at h1
    exact (Module.FaithfullyFlat.one_tmul_eq_zero_iff F C x).1 h1
  have hfg : M.FG := by
    have h1 : ((spanK z (M : Set C)).restrictScalars (𝓞 F)).FG := h.1.restrictScalars
    have h2 : M.map ((coordMap z).restrictScalars (𝓞 F)) ≤ (spanK z (M : Set C)).restrictScalars (𝓞 F) := by
      rintro _ ⟨x, hx, rfl⟩
      exact mem_spanK z hx
    exact Submodule.fg_of_fg_map_injective ((coordMap z).restrictScalars (𝓞 F)) hinj (h1.of_le h2)
  letI := Submodule.IsLattice.of_fg F hfg
  refine ⟨?_⟩
  · refine Submodule.baseChange_injective (A := K) ?_
    rw [Submodule.baseChange_top, Submodule.baseChange_span, eq_top_iff]
    intro y _
    have h2 := h.2
    unfold spanK at h2
    rw [Submodule.span_span_of_tower] at h2
    have h3 : z.symm y ∈ Submodule.span K ((fun f : C => z.symm (1 ⊗ₜ[F] f)) '' (M : Set C)) := h2 ▸ Submodule.mem_top
    have h4 := Submodule.mem_map_of_mem (f := z.toLinearMap) h3
    rw [Submodule.map_span, ← Set.image_comp] at h4
    simp only [Function.comp_def, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h4
    exact h4

theorem exists_rem_of_concl {D : D7} {B : WeightFamilies.Prov D} {P6 : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P6 j) (S : WeightAlgebra.Scal B)
    (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (a b c d : ℝ)
    {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra B.KO K] {n : ℕ}
    (z : (Fin n → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j ka) (hM : IsLatIn ⊤ (spanK z (B.Mlat j ka : Set _)))
    (hC : WeightAlgebra.Concl X S ka wL wF T nus (X.rk ka (B.Mlat j ka) * a * b * c * d)) :
    ∃ r : HeightOneSpectrum (𝓞 K) → ℝ, (∀ v, 0 ≤ r v) ∧
      (∀ S' : Finset (HeightOneSpectrum (𝓞 K)), ∑ v ∈ S', Formalism.DivisionValues.lw v * r v ≤ (n : ℝ) * (a * b * c * d)) ∧
      ∀ (v : HeightOneSpectrum (𝓞 K)) (e : ℕ), (T : ℝ) * nus (placeBelow (K := B.KO) v) ≤ e →
        ∀ W : Submodule K (Fin n → K),
          (lix v (Formalism.EigenvalueLevelCeiling.cut W (spanK z (B.Mlat j ka : Set _))) (Formalism.EigenvalueLevelCeiling.cut W (spanK z {F | X.inc ka F ∈ X.Theta S ka wL wF T})) : ℝ) ≤
            ((ramOver (K := B.KO) v * e : ℕ) : ℝ) * (Module.finrank K W : ℝ) + r v := by
  have hM' := isLattice_of_spanK z _ hM
  letI := hM'
  have hn : X.rk ka (B.Mlat j ka) = n := by
    unfold WeightAlgebra.PJ.rk
    rw [Submodule.IsFullLattice.span_eq_top, finrank_top]
    have := z.finrank_eq
    rw [Module.finrank_baseChange, Module.finrank_fin_fun] at this
    exact this.symm
  let Q : Formalism.MainNotions.Gaps.LocalGlobalPassage.Run D B P6 := ⟨j, X, S, ka, wL, wF, T, nus, X.rk ka (B.Mlat j ka) * a * b * c * d⟩
  letI : Submodule.IsFullLattice B.KO Q.M0 := hM'
  obtain ⟨r, h0, h1, h2, h3⟩ := Formalism.MainNotions.Gaps.LocalGlobalPassage.l2 Q (fun la => Formalism.MainNotions.Gaps.LocalGlobalPassage.l1 la)
    (fun la => Formalism.MainNotions.Gaps.LocalGlobalPassage.l1b la) (fun la => Formalism.MainNotions.Gaps.LocalGlobalPassage.l1c la) (by first | exact hM' | exact hM'.toIsLattice) hC
  have hβ : Q.β = (n : ℝ) * (a * b * c * d) := by
    change (X.rk ka (B.Mlat j ka) : ℝ) * a * b * c * d = _
    rw [hn]
    ring
  refine ⟨fun v => (v.asIdeal.ramificationIdx (𝓞 B.KO) : ℝ) * r (v.under (𝓞 B.KO)),
    fun v => mul_nonneg (Nat.cast_nonneg _) (h0 _),
    fun S' => (Formalism.MainNotions.Gaps.LocalGlobalPassage.l4 r h0 h1 S').trans (h2.trans hβ.le), ?_⟩
  intro v e he W
  have hpl : placeBelow (K := B.KO) v = v.under (𝓞 B.KO) := rfl
  have hram : ramOver (K := B.KO) v = v.asIdeal.ramificationIdx (𝓞 B.KO) := Formalism.MainNotions.Gaps.LocalGlobalPassage.ram_eq v
  obtain ⟨h4, h5⟩ := h3 (v.under (𝓞 B.KO))
  have hTh : Formalism.MainNotions.Gaps.LocalGlobalPassage.up (coordMap z) (Q.M0 ⊓ Q.Th0) ≤ spanK z {F | X.inc ka F ∈ X.Theta S ka wL wF T} :=
    Submodule.span_mono (Set.image_mono fun f hf => hf.2)
  exact Formalism.MainNotions.Gaps.LocalGlobalPassage.l5 (coordMap z) (coordMap_linearIndependent z) (coordMap_span z) Q.M0 (Q.M0 ⊓ Q.Th0) (Submodule.IsLattice.fg B.KO (B.Mlat j ka))
    Submodule.IsFullLattice.span_eq_top h4 inf_le_left v e (r (v.under (𝓞 B.KO))) (ramOver (K := B.KO) v * e)
    (by rw [hram]; push_cast; rfl) (h5 e (by rw [Int.cast_natCast, ← hpl]; exact he)) _ hTh W

theorem starRing_eq {R : Type} [CommRing R] (s t : StarRing R) (h : ∀ a : R, s.star a = t.star a) : s = t := by
  obtain @⟨@⟨@⟨⟨f⟩, _⟩, _⟩, _⟩ := s
  obtain @⟨@⟨@⟨⟨g⟩, _⟩, _⟩, _⟩ := t
  obtain rfl : f = g := funext h
  rfl

theorem exists_rem_of_tie {D : D7} {B : WeightFamilies.Prov D} {P6 : ModuliIntegralCharts.Prov D} {j : ℕ} {X : WeightAlgebra.PJ D B P6 j}
    {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ} {ka wL wF : WeightFamilies.Wt D j} {T : ℕ}
    {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ} {a b c d : ℝ}
    {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra B.KO K]
    {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
    {O : OnObj S P oc} {v₁ : HeightOneSpectrum (𝓞 K)} {i : Bs.J}
    {z : (Fin (O.nZ i) → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j ka} {act : P → B.Cusp j ka → B.Cusp j ka}
    (ht : FormTieK X hinj EX p ka wL wF T O v₁ i z act) (hM : IsLatIn ⊤ (O.Ms i))
    (hC : WeightAlgebra.Concl X (scalOfP B hinj EX p ka wL wF T) ka wL wF T nus (X.rk ka (B.Mlat j ka) * a * b * c * d)) :
    ∃ r : HeightOneSpectrum (𝓞 K) → ℝ, (∀ v, 0 ≤ r v) ∧
      (∀ S' : Finset (HeightOneSpectrum (𝓞 K)), ∑ v ∈ S', Formalism.DivisionValues.lw v * r v ≤ (O.nZ i : ℝ) * (a * b * c * d)) ∧
      ∀ (v : HeightOneSpectrum (𝓞 K)), FormTieK X hinj EX p ka wL wF T O v i z act →
        ∀ e : ℕ, (T : ℝ) * nus (placeBelow (K := B.KO) v) ≤ e → ∀ W : Submodule K (Fin (O.nZ i) → K),
          (lix v (Formalism.EigenvalueLevelCeiling.cut W (O.Ms i)) (Formalism.EigenvalueLevelCeiling.cut W (O.Th v i)) : ℝ) ≤
            ((ramOver (K := B.KO) v * e : ℕ) : ℝ) * (Module.finrank K W : ℝ) + r v := by
  obtain ⟨ρ, h0, h1, h2⟩ := exists_rem_of_concl X _ ka wL wF T nus a b c d z (ht.Ms_eq ▸ hM) hC
  refine ⟨ρ, h0, h1, fun v hv e he W => ?_⟩
  rw [hv.Ms_eq, hv.Th_eq]
  exact h2 v e he W

theorem nusR_le_eLam {D : D7} {L : SizeData₂ D} {Pm : ParameterChoice' D L} (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D)
    (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) :
    letI := T.Q.H.starRing
    (Tp.TO : ℝ) * GlobalTheory.RunJoin.nusR h j (lR Tp hK j) la ≤
      ((GlobalTheory.RunDepth.depOf T.toCore EX Tp hK).Q.eLam (ramOverZ la)
        (nuStarAt (Xo := T.Q.Xo j) (c := T.Q.c) (GlobalTheory.RunDepth.depOf T.toCore EX Tp hK) la j) (resCharOf la) : ℝ) := by
  have hn := GlobalTheory.RunDepthScale.nusOf_eq_ram_mul_nuStarAt D L Pm Tp hK T h EX j hj la
  refine le_trans (le_of_eq ?_) (DepPage.le_eLam _ _ _ _)
  refine (congrArg (fun t => (Tp.TO : ℝ) * t) hn).trans ?_
  rw [← mul_assoc, mul_comm (Tp.TO : ℝ)]
  rfl


set_option maxHeartbeats 1000000 in
theorem hasIndexBound_of_runs : ∀ CK : ℝ, ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst) (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c), IsRec Tp hK EX F fw r O → CoreTies L EX J R → OwnPin r → RunsHold Tp hK EX CK r → LeafSup O → LeafSpan O → O.b = L.sc.b → HasIndexBound O := by
  intro CK D G _ _ Pl0 T0 A J inst R F κ v₀ fw L Pm Tp hK EX r c O hO _ _ hR hS hSp hb
  obtain rfl : κ = fun i : Fin D.R.m => kaR Tp hK ((i : ℕ) + 1) := funext hO.kap
  obtain ⟨hc, hinj, z, act, y, ht⟩ := hO.tied
  obtain ⟨st, hd⟩ := hO.depth
  let _ := hostAlg D
  obtain rfl : st = J.toCore.Q.H.starRing := starRing_eq _ _ hd.star_eq
  let _ := J.toCore.Q.H.starRing
  let _ : ∀ s : GlobalTheory.RealIndexBound.RunData J, Algebra s.full.J.Q.c.F D.what₂.LL := fun _ => inst
  let _ : ∀ (s : GlobalTheory.RealIndexBound.RunData J) (h : LawsP s.full.toTop), Algebra (recB h.toLawsCore).KO D.what₂.LL := fun _ _ => inst
  have key : ∀ (q : Prop) (i : Fin D.R.m), ∃ ρ : HeightOneSpectrum (𝓞 D.what₂.LL) → ℝ, (∀ v, 0 ≤ ρ v) ∧
      (∀ S' : Finset (HeightOneSpectrum (𝓞 D.what₂.LL)),
        ∑ v ∈ S', Formalism.DivisionValues.lw v * ρ v ≤ (O.nZ i : ℝ) * (D.R.f * D.R.m * L.sc.b * L.de2)) ∧
      ∀ v, (Formalism.EigenvalueLevelCeiling.plc v = D.host.pde ↔ q) → ∀ W : Submodule D.what₂.LL (Fin (O.nZ i) → D.what₂.LL),
        (lix v (Formalism.EigenvalueLevelCeiling.cut W (O.Ms i)) (Formalism.EigenvalueLevelCeiling.cut W (O.Th v i)) : ℝ) ≤ (O.E v i : ℝ) * (finrank D.what₂.LL W : ℝ) + ρ v := by
    intro q i
    by_cases hq : ∃ v₁ : HeightOneSpectrum (𝓞 D.what₂.LL), (Formalism.EigenvalueLevelCeiling.plc v₁ = D.host.pde ↔ q)
    · obtain ⟨v₁, hv₁⟩ := hq
      obtain ⟨ρ, h0, h1, h2⟩ := @exists_rem_of_tie D (recB hc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ inst _ _ _ _ _ _ _ _ _ _ _ _ (ht v₁ i).1.toFormTieK (hS i).1
        (hR v₁ (hO.ok.laws v₁).p hinj ((i : ℕ) + 1) (inR_succ i)).2
      refine ⟨ρ, h0, h1, fun v hv W => ?_⟩
      have e1 : r.used v = r.used v₁ := by
        unfold TwoRuns.used
        exact if_congr (hv.trans hv₁.symm) rfl rfl
      have e2 : ownAt D v = ownAt D v₁ := by
        unfold ownAt
        exact if_congr (hv.trans hv₁.symm) rfl rfl
      have h3 := (ht v i).1.toFormTieK
      have h4 := (hO.ok.laws v).p
      rw [hd.E_eq v i]
      refine h2 v ?_ _ (nusR_le_eLam Tp hK EX (r.used v₁).full.toTop (hO.ok.laws v₁).p _ (inR_succ i) _) W
      have h5 : ∀ (s : GlobalTheory.RealIndexBound.RunData J) (h' : LawsP s.full.toTop) (p' : ℕ), s = r.used v₁ → p' = ownAt D v₁ →
          letI : Algebra (recB h'.toLawsCore).KO D.what₂.LL := inst
          FormTieK (recPJ h' ((i : ℕ) + 1) (inR_succ i)) hinj EX p' (kaR Tp hK ((i : ℕ) + 1)) (lR Tp hK ((i : ℕ) + 1))
            (fR Tp hK ((i : ℕ) + 1)) Tp.TO O v i (z i) (act i) →
          letI : Algebra (recB (hO.ok.laws v₁).p.toLawsCore).KO D.what₂.LL := inst
          FormTieK (recPJ (hO.ok.laws v₁).p ((i : ℕ) + 1) (inR_succ i)) hinj EX (ownAt D v₁) (kaR Tp hK ((i : ℕ) + 1))
            (lR Tp hK ((i : ℕ) + 1)) (fR Tp hK ((i : ℕ) + 1)) Tp.TO O v i (z i) (act i) := by
        rintro _ _ _ rfl rfl h
        exact h
      exact h5 _ h4 _ e1 e2 h3
    · refine ⟨fun _ => 0, fun _ => le_rfl, fun S' => ?_, fun v hv => absurd ⟨v, hv⟩ hq⟩
      have h1 := L.thickDensity_pos
      have h2 : 0 < L.sc.b := Real.exp_pos _
      simp only [mul_zero, Finset.sum_const_zero]
      positivity
  choose ρ h0 h1 h2 using key
  rw [← hd.f_eq, ← hd.m_eq, ← hb] at h1
  choose a ha using fun (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (i : Fin D.R.m) => Formalism.MainNotions.Gaps.LocalGlobalPassage.exists_vw_eq v (O.E v i)
  refine ⟨O.Th, a, fun v i => ρ False i v, fun v i => ρ True i v, L.de2, ?_, L.thickDensity_pos.le, L.thickDensity_le_one,
    fun v i => ⟨h0 _ i v, h0 _ i v⟩, fun i S' => ⟨h1 _ i S', h1 _ i S'⟩⟩
  have hloc : ∀ v (i : Fin D.R.m) (W : Submodule D.what₂.LL (Fin (O.nZ i) → D.what₂.LL)),
      (lix v (Formalism.EigenvalueLevelCeiling.cut W (O.Ms i)) (Formalism.EigenvalueLevelCeiling.cut W (O.Th v i)) : ℝ) ≤ (O.E v i : ℝ) * (finrank D.what₂.LL W : ℝ) +
        (if Formalism.EigenvalueLevelCeiling.plc v = O.pde then ρ True i v else ρ False i v) := by
    intro v i W
    rw [hO.pde_eq]
    split_ifs with hv
    · exact h2 True i v (iff_true_intro hv) W
    · exact h2 False i v (iff_false_intro hv) W
  intro w hw
  exact ⟨fun i => ⟨((hSp w hw).1 i).1, le_rfl, (ha _ i).1, (ha _ i).2, hloc _ i⟩,
    fun i => ⟨((hSp w hw).2 i).1, le_rfl, (ha _ i).1, (ha _ i).2, hloc _ i⟩⟩

end GlobalTheory.BigOn

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeavesSupSpanData
set_option autoImplicit false

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn

theorem lat_span_of_hypC {D : D7} {T : Top D} (h : LawsP T) {j : ℕ} (hj : InR D j) {large₂ : SizeData₂ D} {H : WeightAlgebra.KHyp}
    {C2 A2 CR Bx CT : ℝ} {S : WeightAlgebra.Scal (recB h.toLawsCore)} {ka wL wF : WeightFamilies.Wt D j} {Tn nP nW : ℕ} {h0 : ℝ}
    {nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ}
    (hyp : Formalism.MainNotions.Gaps.EtaleWeightGaps.HypC large₂ (recPJ h j hj) H C2 A2 CR Bx CT S ka wL wF Tn nP nW h0 nus) :
    Formalism.MainNotions.Gaps.EtaleWeightGaps.LatAt (recB h.toLawsCore) j ka ∧ ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) ka ∧
      WeightAlgebra.H2 (recPJ h j hj) S ka wL wF := by
  obtain ⟨hA, -, hB, -, hH2, -⟩ := hyp
  obtain ⟨-, -, -, hK, -, po, -, -, PLam, -, -, -, -, hka⟩ := hB
  have sK := GlobalTheory.RunLat.spanAt_of_shortG _ _ _ _ hka
  exact ⟨GlobalTheory.latAt_record D _ h.toLawsCore (GlobalTheory.RunIn.gamAt_of_lawsCore' D _ h.toLawsCore) large₂ H.CA hA j ka _
    (recPJ h j hj) S wL wF hK sK hH2, sK, hH2⟩

theorem ownAt_pos (D : D7) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) : 0 < ownAt D v := by
  unfold ownAt
  split_ifs
  · exact D.host.pde'_prime.pos
  · exact D.host.pde_prime.pos


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem leaves_sup_span_data : ∀ CK : ℝ, ∃ x₁ : ℝ, ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst) (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c), IsRec Tp hK EX F fw r O → CoreTies L EX J R → OwnPin r → PageNum Tp x₁ → RunsHold Tp hK EX CK r → R.IsGrp F → R.tup_mu_conj → R.tup_mu_off → R.tup_mu_ne → LeafSup O ∧ LeafSpan O ∧ LeafLemmaS O ∧ LeafData O := by
  intro CK
  refine ⟨0, ?_⟩
  intro D G _ _ Pl0 T0 A J inst R F κ v₀ fw L Pm Tp hK EX r c O hrec _ _ _ hrun hgrp _ _ _
  obtain rfl : κ = fun i : Fin D.R.m => kaR Tp hK ((i : ℕ) + 1) := funext hrec.kap
  obtain ⟨hc, hinj, z, act, y, ht⟩ := hrec.tied
  have hok := hrec.ok
  have h3 : LeafSup O ∧ LeafSpan O ∧ LeafLemmaS O := by
    refine leaves_sup_span_lemmaS_of_formTieK GlobalTheory.chartIndependence_unconditional D L Pm Tp hK hinj EX _ _ _ _ _ c O
      fun v i => ?_
    letI : Algebra (r.used v).full.J.Q.c.F D.what₂.LL := inst
    obtain ⟨a1, a2, a3⟩ := lat_span_of_hypC _ _ (hrun v (hok.laws v).p hinj _ (inR_succ i)).1
    exact ⟨(r.used v).full, (hok.laws v).p, _, inR_succ i, ownAt D v, inst, z i, act i, fun g => r.lev i (mirIncl R g),
      (ht v i).1.toFormTieK, (ht v i).1.act_eq, hok.laws v, hok.xiRat v i, hok.cover v i, ownAt_pos D v, a1, a2, a3⟩
  refine ⟨h3.1, h3.2.1, h3.2.2, ?_⟩
  have hU : ∀ g, g ∈ F.P0 ↔ ∀ PP : R.Pg, R.eG g PP ∈ unip (kP PP.1) D.R.r := fun g => by
    rw [GlobalTheory.OntoChain.mem_base_iff hgrp.levels]
    refine Iff.trans ?_ ((mem_pi_unip_iff R (R.eG g)).symm.trans ⟨fun H PP => H PP (Set.mem_univ _), fun H PP _ => H PP⟩)
    refine exists_congr fun u => and_congr_right fun _ => ?_
    rw [← eG_mirIncl, R.eG.injective.eq_iff]
  have key : ∀ v (i : Fin D.R.m), GlobalTheory.TraceLattice.TiedAt A hinj EX O (mirIncl R) F.P0 F.ψ0⁻¹
      (fun _ _ _ _ _ _ _ _ _ => True) v i := fun v i =>
    ⟨(r.used v).full, inst, R, _, v₀, (hok.laws v).p, fw, ownAt D v, i, _, _, _, z i, act i, r.lev i, 1, y v i,
      (ht v i).1, hok.laws v, hok.xiRat v i, kaWt_n _ _ _ _, GlobalTheory.TraceLattice.kaR_lastPos Tp hK (inR_succ i),
      @GlobalTheory.TraceLattice.detOneOn_of_pins D G _ _ _ _ A (r.used v).full inst R i (hok.laws v) _ (hok.level v i) hok.half _ hU,
      trivial⟩
  exact GlobalTheory.TraceLattice.leafData_of_onTie_of_leafSpan h3.2.1 fun w _ => ⟨key w, key _⟩

end GlobalTheory.BigOn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumOfFjEqOfRecord
open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn

theorem numOf_eq_ofRecord (D : D7) (L : SizeData₂ D) (Del h0 : ℕ) (h1 : D.s.Del = (Del : ℚ))
    (h2 : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ)) : GlobalTheory.RunDepth.numOf D L = ofRecord D L Del h0 := by
  have hm : (D.R.m : ℝ) ≠ 0 := by
    intro h
    have := L.etaSz_pos
    rw [h2, h, zero_mul] at this
    exact lt_irrefl _ this
  have e1 : ⌊((D.s.Del : ℚ) : ℝ)⌋₊ = Del := by
    rw [h1, Rat.cast_natCast, Nat.floor_natCast]
  have e2 : ⌊LevelStarExponents.h0 L⌋₊ = h0 := by
    have : LevelStarExponents.h0 L = (h0 : ℝ) := by
      unfold LevelStarExponents.h0
      rw [h2, mul_div_cancel_left₀ _ hm]
    rw [this, Nat.floor_natCast]
  have e3 : (fun z => D.hc (GlobalTheory.RunDepth.plOf D z)) = fun z => D.hc (Formalism.BasicNotions.tauPl D z) := by
    funext z
    obtain ⟨b, t⟩ := z
    cases b <;> rfl
  unfold GlobalTheory.RunDepth.numOf ofRecord
  simp only [e1, e2, e3]

theorem numOf_Fj_eq_ofRecord :
    ∀ (D : D7) (L : SizeData₂ D) (Del h0 : ℕ), D.s.Del = (Del : ℚ) → L.etaSz = (D.R.m : ℝ) * (h0 : ℝ) → ∀ (j : ℕ) (w : HeightOneSpectrum (𝓞 D.what₂.LL)), (GlobalTheory.RunDepth.numOf D L).Fj j w = (ofRecord D L Del h0).Fj j w := by
  intro D L Del h0 h1 h2 j w
  rw [numOf_eq_ofRecord D L Del h0 h1 h2]

end GlobalTheory.BigOn
end

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn

section Comparison₂

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem indefinitePoint_splitPartContent_eq_forcedContent (p : PtAt ex Csz) (C CH : ℝ) :
    Formalism.L2.Indef.Tree.DepthCond.ContentEqualsDatumContent ((R2 p).num (F2 p) C CH) (GlobalTheory.RunDepth.numOf D L) (fun j : Fin D.R.m => (j : ℕ) + 1) := by
  intro w j
  rw [numOf_Fj_eq_ofRecord D L p.Del p.h0 p.hDel p.hh0]
  rfl

end Comparison₂

end GlobalTheory.BigOn
