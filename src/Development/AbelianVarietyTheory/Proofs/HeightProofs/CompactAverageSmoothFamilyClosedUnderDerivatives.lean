module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.WeightsBelow
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraEigenDecompositionCMSignature
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SemiAbelianHomExtensionDvr

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactAverageSmoothFamilyClosedUnderDerivatives
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactAverageSmoothFamilyClosedUnderDerivatives
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AvgFam

section Compact

variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (μ : Measure K) [IsFiniteMeasure μ]

theorem integrable_of_continuous {f : K → ℂ} (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun k => hC k (Set.mem_univ k))

def intCLM : C(K, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ k, f k ∂μ
      map_add' := fun f g => integral_add (integrable_of_continuous μ f.continuous)
        (integrable_of_continuous μ g.continuous)
      map_smul' := fun c f => integral_smul c _ }
    (μ.real Set.univ) fun f => by
      rw [mul_comm]
      exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun k => f.norm_coe_le_norm k)

theorem continuous_avg {Y : Type} [TopologicalSpace Y] {F : K → Y → ℂ}
    (hF : Continuous fun p : K × Y => F p.1 p.2) : Continuous fun x => ∫ k, F k x ∂μ := by
  let Φ : C(Y × K, ℂ) := ⟨fun p => F p.2 p.1, hF.comp continuous_swap⟩
  exact (intCLM μ).continuous.comp Φ.curry.continuous

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem hasDerivAt_avg (hθ : IsInfFam θ) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) {F : K → GA D V → ℂ} (hF : ∀ k, F k ∈ GlobalTheory.Mem.AutSpace.SmFun θ V)
    (hFc : ∀ x, Continuous fun k => F k x)
    (hGc : Continuous fun p : K × GA D V => Rder θ V τ X (F p.1) p.2) (g : GA D V) :
    HasDerivAt (fun t : ℝ => ∫ k, F k (g * oneP θ V τ X t) ∂μ) (∫ k, Rder θ V τ X (F k) g ∂μ) 0 := by
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hc1 : Continuous fun p : K × ℝ => Rder θ V τ X (F p.1) (g * oneP θ V τ X p.2) :=
    hGc.comp (continuous_fst.prodMk (continuous_const.mul ((GlobalTheory.Mem.Lift.continuous_oneP hθ hX).comp continuous_snd)))
  obtain ⟨C, hC⟩ := (isCompact_univ.prod (isCompact_closedBall (0 : ℝ) 1)).exists_bound_of_continuousOn
    hc1.continuousOn
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun t k => F k (g * oneP θ V τ X t))
    (F' := fun t k => Rder θ V τ X (F k) (g * oneP θ V τ X t)) (x₀ := 0) (bound := fun _ => C)
    (Metric.closedBall_mem_nhds (0 : ℝ) zero_lt_one)
    (Filter.Eventually.of_forall fun t => (hFc _).aestronglyMeasurable)
    (integrable_of_continuous μ (hFc _))
    ((hc1.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun k t ht => hC (k, t) ⟨Set.mem_univ _, ht⟩)
    (integrable_const C)
    (Filter.Eventually.of_forall fun k t _ =>
      GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (GlobalTheory.Mem.Lift.hasDerivAt_Rder (hF k) hX) g t)
  have e := key.2
  simp only [GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] at e
  exact e

end Compact

theorem avg_closed : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam (D := D) θ → ∀ (V : HSp D) (K : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (𝒢 : Submodule ℂ (K → GA D V → ℂ)), (∀ F ∈ 𝒢, Continuous fun p : K × GA D V => F p.1 p.2) → (∀ F ∈ 𝒢, ∀ k, F k ∈ GlobalTheory.Mem.AutSpace.SmFun θ V) → (∀ F ∈ 𝒢, ∀ τ, ∀ X ∈ lieAt V τ, (fun k => Rder θ V τ X (F k)) ∈ 𝒢) → ∀ F ∈ 𝒢, Continuous (fun x => ∫ k, F k x ∂μ) ∧ (fun x => ∫ k, F k x ∂μ) ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ (∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → l.foldr (fun p f => Rder θ V p.1 p.2 f) (fun x => ∫ k, F k x ∂μ) = fun x => ∫ k, (l.foldr (fun p f => Rder θ V p.1 p.2 f) (F k)) x ∂μ) ∧ ∀ τ j, gelf θ V τ j (fun x => ∫ k, F k x ∂μ) = fun x => ∫ k, gelf θ V τ j (F k) x ∂μ := by
  intro D θ hθ V K _ _ _ _ μ _ 𝒢 hc hsm hder
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hk : ∀ F ∈ 𝒢, ∀ x, Continuous fun k => F k x := fun F hF x =>
    (hc F hF).comp (continuous_id.prodMk continuous_const)
  have hint : ∀ F ∈ 𝒢, ∀ x, Integrable (fun k => F k x) μ := fun F hF x =>
    integrable_of_continuous μ (hk F hF x)
  have hd : ∀ F ∈ 𝒢, ∀ τ, ∀ X ∈ lieAt V τ, ∀ g, HasDerivAt (fun t : ℝ => ∫ k, F k (g * oneP θ V τ X t) ∂μ)
      (∫ k, Rder θ V τ X (F k) g ∂μ) 0 := fun F hF τ X hX g =>
    hasDerivAt_avg μ hθ hX (hsm F hF) (hk F hF) (hc _ (hder F hF τ X hX)) g
  have hR : ∀ F ∈ 𝒢, ∀ τ, ∀ X ∈ lieAt V τ,
      Rder θ V τ X (fun x => ∫ k, F k x ∂μ) = fun x => ∫ k, Rder θ V τ X (F k) x ∂μ :=
    fun F hF τ X hX => funext fun g => (hd F hF τ X hX g).deriv
  have hSm : ∀ F ∈ 𝒢, (fun x => ∫ k, F k x ∂μ) ∈ GlobalTheory.Mem.AutSpace.SmFun θ V := by
    intro F hF
    refine GlobalTheory.Mem.DerClosed.mem_smFun_of_closed D θ hθ V {φ | ∃ F ∈ 𝒢, φ = fun x => ∫ k, F k x ∂μ} ?_ ?_ _
      ⟨F, hF, rfl⟩
    · rintro _ ⟨F, hF, rfl⟩
      exact continuous_avg μ (hc F hF)
    · rintro _ ⟨F, hF, rfl⟩ τ X hX
      exact ⟨_, ⟨_, hder F hF τ X hX, rfl⟩, hd F hF τ X hX⟩
  have hW : ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
      ∀ F ∈ 𝒢, (fun k => l.foldr (fun p f => Rder θ V p.1 p.2 f) (F k)) ∈ 𝒢 ∧
        l.foldr (fun p f => Rder θ V p.1 p.2 f) (fun x => ∫ k, F k x ∂μ) =
          fun x => ∫ k, (l.foldr (fun p f => Rder θ V p.1 p.2 f) (F k)) x ∂μ := by
    intro l hl F hF
    induction l with
    | nil => exact ⟨hF, rfl⟩
    | cons p l ih =>
      obtain ⟨h1, h2⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
      have hp := hl p List.mem_cons_self
      refine ⟨hder _ h1 p.1 p.2 hp, ?_⟩
      simp only [List.foldr_cons]
      rw [h2]
      exact hR _ h1 p.1 p.2 hp
  have hC : ∀ F ∈ 𝒢, ∀ τ Z, (fun k => RderC θ V τ Z (F k)) ∈ 𝒢 ∧
      RderC θ V τ Z (fun x => ∫ k, F k x ∂μ) = fun x => ∫ k, RderC θ V τ Z (F k) x ∂μ := by
    intro F hF τ Z
    obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
    have m1 := hder F hF τ _ h1
    have m2 := hder F hF τ _ h2
    have e : (fun k => RderC θ V τ Z (F k)) = (fun k => Rder θ V τ ((1 / 2 : ℂ) • (Z + conjAt V τ Z)) (F k)) +
        Complex.I • (fun k => Rder θ V τ ((1 / (2 * Complex.I)) • (Z - conjAt V τ Z)) (F k)) := rfl
    refine ⟨e ▸ add_mem m1 (Submodule.smul_mem _ _ m2), ?_⟩
    have i1 := hint _ m1
    have i2 := hint _ m2
    simp only [RderC]
    rw [hR F hF τ _ h1, hR F hF τ _ h2]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_add (i1 x) ((i2 x).const_mul _), integral_const_mul]
  have hL : ∀ τ (L : List ((GA D V → ℂ) → GA D V → ℂ)), (∀ f ∈ L, ∃ Z, f = RderC θ V τ Z) → ∀ F ∈ 𝒢,
      (fun k => L.foldr (fun f acc => f acc) (F k)) ∈ 𝒢 ∧
        L.foldr (fun f acc => f acc) (fun x => ∫ k, F k x ∂μ) =
          fun x => ∫ k, (L.foldr (fun f acc => f acc) (F k)) x ∂μ := by
    intro τ L hLZ F hF
    induction L with
    | nil => exact ⟨hF, rfl⟩
    | cons f L ih =>
      obtain ⟨h1, h2⟩ := ih fun q hq => hLZ q (List.mem_cons_of_mem _ hq)
      obtain ⟨Z, rfl⟩ := hLZ f List.mem_cons_self
      refine ⟨(hC _ h1 τ Z).1, ?_⟩
      simp only [List.foldr_cons]
      rw [h2]
      exact (hC _ h1 τ Z).2
  intro F hF
  refine ⟨continuous_avg μ (hc F hF), hSm F hF, fun l hl => (hW l hl F hF).2, fun τ j => ?_⟩
  have hmem : ∀ idx : Fin (j + 1) → Fin V.rank, ∀ f ∈ List.ofFn (fun a : Fin (j + 1) =>
      RderC θ V τ (Matrix.single (idx a) (idx (a + 1)) 1)), ∃ Z, f = RderC θ V τ Z := by
    intro idx f hf
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hf
    exact ⟨_, rfl⟩
  simp only [gelf]
  rw [Finset.sum_congr rfl fun idx _ => (hL τ _ (hmem idx) F hF).2]
  funext x
  simp only [Finset.sum_apply]
  rw [integral_finsetSum _ fun idx _ => hint _ (hL τ _ (hmem idx) F hF).1 x]

end GlobalTheory.AvgFam

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactAverageSmoothFamilyClosedUnderDerivativesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactAverage_smoothFamily_closedUnderDerivatives : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam (D := D) θ → ∀ (V : HSp D) (K : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (𝒢 : Submodule ℂ (K → GA D V → ℂ)), (∀ F ∈ 𝒢, Continuous fun p : K × GA D V => F p.1 p.2) → (∀ F ∈ 𝒢, ∀ k, F k ∈ GlobalTheory.Mem.AutSpace.SmFun θ V) → (∀ F ∈ 𝒢, ∀ τ, ∀ X ∈ lieAt V τ, (fun k => Rder θ V τ X (F k)) ∈ 𝒢) → ∀ F ∈ 𝒢, Continuous (fun x => ∫ k, F k x ∂μ) ∧ (fun x => ∫ k, F k x ∂μ) ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ (∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → l.foldr (fun p f => Rder θ V p.1 p.2 f) (fun x => ∫ k, F k x ∂μ) = fun x => ∫ k, (l.foldr (fun p f => Rder θ V p.1 p.2 f) (F k)) x ∂μ) ∧ ∀ τ j, gelf θ V τ j (fun x => ∫ k, F k x ∂μ) = fun x => ∫ k, gelf θ V τ j (F k) x ∂μ := by
  first | exact @GlobalTheory.AvgFam.avg_closed | exact GlobalTheory.AvgFam.avg_closed | (intros; apply GlobalTheory.AvgFam.avg_closed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.LowerBoundConstAtLargeMultipleNumericalBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.LowerBoundConstAtLargeMultipleNumericalBounds
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunJoin

theorem three_le_dimY_of_rank (D : D7) (j : ℕ) (hj : InR D j) (hr : 8 ≤ D.R.r) : 3 ≤ WeightFamilies.dimY D j := by
  have hf : 1 ≤ D.R.f := by
    unfold Ranks.f Ranks.n
    have := D.R.ord_pos
    omega
  have hs : (D.R.sigW j).1 + (D.R.sigW j).2 = D.R.r := Formalism.L2.Geo.sigW_sum D hj.1 hj.2
  unfold WeightFamilies.dimY
  generalize (D.R.sigW j).1 = a at hs ⊢
  generalize (D.R.sigW j).2 = b at hs ⊢
  have key : ∀ c : ℕ, 3 ≤ c → 3 ≤ c * (c - 1) / 2 := fun c hc => by
    have : 3 * 2 ≤ c * (c - 1) := Nat.mul_le_mul hc (by omega)
    omega
  have h3 : 3 ≤ a * b + a * (a - 1) / 2 + b * (b - 1) / 2 := by
    rcases le_or_gt 3 a with h | h
    · have := key a h; omega
    · have := key b (by omega); omega
  calc 3 = 1 * 3 := rfl
    _ ≤ _ := Nat.mul_le_mul hf h3

theorem DF_add_one_le_size {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) : (DF w : ℝ) + 1 ≤ w.size := by
  unfold WeightFamilies.Wt.size WeightAlgebra.DF degP
  have h2 : 0 ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) := by positivity
  push_cast at h2 ⊢
  linarith

theorem lamConst_lamR_rows : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 CL : ℝ) (N del : ℕ), InR D j → PageOK large₂ X H C2 A2 CT ka wL wF Tn nP nW h0 → 0 < CL → 0 < N → 0 < del → Real.log N ≤ nbR large₂ wL → Real.log del ≤ 1041 * Zb D large₂ ^ 3 → LamConst j large₂ CL 2 (wsmul (8 * ((WeightFamilies.dimY D j + 2) * N) ^ 2 * (WeightFamilies.dimY D j + 1) * del * (1 + ⌈PO D large₂⌉₊)) wL) (lamR large₂ CL wL) (8 * ((WeightFamilies.dimY D j + 2) * N) ^ 2 * (WeightFamilies.dimY D j + 1) * del * (1 + ⌈PO D large₂⌉₊)) wL.size ∧ 3 ≤ WeightFamilies.dimY D j ∧ wL.n = nW ∧ 0 < wL.n ∧ (DF wL : ℝ) ≤ wL.size ∧ 2 ≤ wL.size ∧ 1 ≤ PO D large₂ ∧ 1 ≤ zBase large₂ ∧ cc D large₂ C2 A2 7 wL * (g0 D : ℝ) ≤ 1 / 2 ∧ PI4 D j (1009 * Zb D large₂) (81 * Zb D large₂ ^ 2) ≤ max 1 (PI4 D j (1009 * Zb D large₂) (81 * Zb D large₂ ^ 2)) := by
  intro D B P j X large₂ H C2 A2 CT ka wL wF Tn nP nW h0 CL N del hj hP hCL hN hdel hlN hld
  have hL : 1 ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hf : 1 ≤ D.R.f := by
    unfold Ranks.f Ranks.n
    have := D.R.ord_pos
    omega
  have hf' : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hPO : 1 ≤ PO D large₂ := by
    unfold PO
    have h1 : 0 ≤ 19 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * large₂.sc.L := by positivity
    have h2 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 2 * large₂.sc.L := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hf') hL
    nlinarith
  obtain ⟨-, hS, h3, -⟩ := hP.hyp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hIL, -, -, -, -, h40, -, h22, -⟩ := hS
  obtain ⟨-, -, -, hc, -⟩ := h3
  obtain ⟨-, -, t1, t2, t3, -⟩ := hP.tie
  rw [t1, t2, t3] at hc
  have hdf : (3 : ℝ) ≤ DF wL := by exact_mod_cast hP.df
  have hsz := DF_add_one_le_size wL
  have hn : wL.n = nW := hIL.1
  refine ⟨?_, three_le_dimY_of_rank D j hj hP.r8, hn, by omega, by linarith, by linarith, hPO,
    WeightFamilies.one_le_zBase large₂, ?_, le_max_right _ _⟩
  · set n : ℕ := 8 * ((WeightFamilies.dimY D j + 2) * N) ^ 2 * (WeightFamilies.dimY D j + 1) * del * (1 + ⌈PO D large₂⌉₊) with hndef
    have hn1 : 1 ≤ n := Nat.succ_le_of_lt (by rw [hndef]; positivity)
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hs1 : (wsmul n wL).size ≤ (n : ℝ) * wL.size :=
      GlobalTheory.RunWeights.size_le_mul _ _ n hn1 (fun _ _ => le_rfl) (fun _ _ => le_rfl) le_rfl
    have hs0 : 1 ≤ (wsmul n wL).size := by
      have := DF_add_one_le_size (wsmul n wL)
      have h0 : (0 : ℝ) ≤ DF (wsmul n wL) := Nat.cast_nonneg _
      linarith
    have hP0 : 0 ≤ WeightFamilies.PP0v D large₂ CL 2 := by
      unfold WeightFamilies.PP0v
      rw [Real.rpow_two]
      positivity
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hdel' : (0 : ℝ) < del := by exact_mod_cast hdel
    have hceil : (1 : ℝ) + (⌈PO D large₂⌉₊ : ℝ) ≤ 2 + PO D large₂ := by
      have := Nat.ceil_lt_add_one (a := PO D large₂) (by linarith)
      linarith
    have hd0 : (0 : ℝ) ≤ WeightFamilies.dimY D j := Nat.cast_nonneg _
    have hnle : (n : ℝ) ≤ 8 * ((WeightFamilies.dimY D j : ℝ) + 2) ^ 3 * (2 + PO D large₂) * (N : ℝ) ^ 2 * del := by
      rw [hndef]
      push_cast
      calc 8 * (((WeightFamilies.dimY D j : ℝ) + 2) * N) ^ 2 * ((WeightFamilies.dimY D j : ℝ) + 1) * del * (1 + (⌈PO D large₂⌉₊ : ℝ))
          ≤ 8 * (((WeightFamilies.dimY D j : ℝ) + 2) * N) ^ 2 * ((WeightFamilies.dimY D j : ℝ) + 2) * del * (2 + PO D large₂) := by
            gcongr; norm_num
        _ = _ := by ring
    have hA : (0 : ℝ) < 8 * ((WeightFamilies.dimY D j : ℝ) + 2) ^ 3 * (2 + PO D large₂) := by positivity
    have hlogn := Real.log_le_log (by linarith) hnle
    rw [Real.log_mul (by positivity) hdel'.ne', Real.log_mul hA.ne' (by positivity), Real.log_pow] at hlogn
    push_cast at hlogn
    have hlogs := Real.log_le_log (by linarith) hs1
    rw [Real.log_mul (by linarith) (by linarith)] at hlogs
    have hl0 : 0 ≤ Real.log (wsmul n wL).size := Real.log_nonneg hs0
    have hmain : WeightFamilies.PP0v D large₂ CL 2 * (1 + Real.log (wsmul n wL).size) ≤ lamR large₂ CL wL := by
      refine le_trans ?_ (le_max_right _ _)
      exact mul_le_mul_of_nonneg_left (by linarith) hP0
    have hlam : 0 ≤ lamR large₂ CL wL := le_trans zero_le_one (le_max_left _ _)
    unfold LamConst
    rw [mul_assoc (lamR large₂ CL wL)]
    exact mul_le_mul hmain hs1 (by linarith) hlam
  · have hT : (2 : ℝ) ≤ Tn := by
      have : 2 ≤ Tn := by omega
      exact_mod_cast this
    rw [mul_assoc] at hc
    by_contra hcon
    push Not at hcon
    nlinarith

end GlobalTheory.RunJoin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.LowerBoundConstAtLargeMultipleNumericalBoundsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowerBoundConst_at_large_multiple_numerical_bounds : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 CL : ℝ) (N del : ℕ), InR D j → PageOK large₂ X H C2 A2 CT ka wL wF Tn nP nW h0 → 0 < CL → 0 < N → 0 < del → Real.log N ≤ nbR large₂ wL → Real.log del ≤ 1041 * Zb D large₂ ^ 3 → LamConst j large₂ CL 2 (wsmul (8 * ((WeightFamilies.dimY D j + 2) * N) ^ 2 * (WeightFamilies.dimY D j + 1) * del * (1 + ⌈PO D large₂⌉₊)) wL) (lamR large₂ CL wL) (8 * ((WeightFamilies.dimY D j + 2) * N) ^ 2 * (WeightFamilies.dimY D j + 1) * del * (1 + ⌈PO D large₂⌉₊)) wL.size ∧ 3 ≤ WeightFamilies.dimY D j ∧ wL.n = nW ∧ 0 < wL.n ∧ (DF wL : ℝ) ≤ wL.size ∧ 2 ≤ wL.size ∧ 1 ≤ PO D large₂ ∧ 1 ≤ zBase large₂ ∧ cc D large₂ C2 A2 7 wL * (g0 D : ℝ) ≤ 1 / 2 ∧ PI4 D j (1009 * Zb D large₂) (81 * Zb D large₂ ^ 2) ≤ max 1 (PI4 D j (1009 * Zb D large₂) (81 * Zb D large₂ ^ 2)) := by
  first | exact @GlobalTheory.RunJoin.lamConst_lamR_rows | exact GlobalTheory.RunJoin.lamConst_lamR_rows | (intros; apply GlobalTheory.RunJoin.lamConst_lamR_rows <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.IsAbelianSchemeOfIsPrincipal
section -- merged from Development.AbelianVarietyTheory.BlockTheory.HeightDefect.EigenLatticeFibres
section -- merged from Development.AbelianVarietyTheory.BlockTheory.HeightDefect.CMCurveHermitianForms
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CMCurveHermitianForms

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Pairings

variable {S : Scheme.{0}} {A B G G' : Over S} [GrpObj A] [GrpObj B] [GrpObj G] [GrpObj G']

def WeilEqAt (k : ℕ) (L : LB G.left) (f₁ : A ⟶ G) (f₂ : B ⟶ G) (L' : LB G'.left) (g₁ : A ⟶ G') (g₂ : B ⟶ G') :
    Prop :=
  ∀ (T : Over S) (x : T ⟶ A) (y : T ⟶ B), x ^ k = 1 → y ^ k = 1 → ∀ c : Γ(T.left, ⊤)ˣ,
    Out.WeilIs G L k (x ≫ f₁) (y ≫ f₂) c ↔ Out.WeilIs G' L' k (x ≫ g₁) (y ≫ g₂) c

def WeilEq (L : LB G.left) (f₁ : A ⟶ G) (f₂ : B ⟶ G) (L' : LB G'.left) (g₁ : A ⟶ G') (g₂ : B ⟶ G') : Prop :=
  ∀ k : ℕ, 0 < k → WeilEqAt k L f₁ f₂ L' g₁ g₂

end Pairings

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev Zw (H : Host E) : Subalgebra ℤ (𝓞 E) := Algebra.adjoin ℤ ({H.w0} : Set (𝓞 E))

def wz (H : Host E) : Zw H := ⟨H.w0, Algebra.self_mem_adjoin_singleton ℤ H.w0⟩

variable {H : Host E}

structure IsPrincipal {S : Scheme.{0}} (t : SAB H S) : Prop where
  proper : IsProper t.G.hom
  ample : Out.RelAmple t.G t.PP.L
  ktriv : Out.KTriv t.G t.PP.L

def SigAt (H : Host E) (p q : ℕ) {S : Scheme.{0}} {G : Over S} [GrpObj G] (act : OAct (𝓞 E) G)
    {k : Type} [Field k] (x : Sp k ⟶ S) (ρ : k) : Prop :=
  ∀ τ : 𝓞 E →+* k, (τ H.rt = ρ → LieMult act x τ p) ∧ (τ H.rt ≠ ρ → LieMult act x τ q)

def HasSig (H : Host E) (p q : ℕ) {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] (act : OAct (𝓞 E) G)
    (ρ : R) : Prop :=
  ρ ^ 2 = -(H.d : R) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (β : R →+* k), SigAt H p q act (spMap β) (β ρ)

def herm (D : Datum H) (x y : D.La) : Zw H :=
  ((D.EF (H.w0 • x) y - D.EF x y : ℤ) : Zw H) + ((D.EF x y : ℤ) : Zw H) * wz H


end GlobalTheory.IndefiniteRowSideFullHecke.CMCurveHermitianForms
end
end

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFibres

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.CMCurveHermitianForms

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {K : Type} [Field K] [NumberField K]

structure GenFib (t : SAB H (Sp (𝓞 K))) where

  tK : SAB H (Sp K)

  m : SABMap tK t (spMap (algebraMap (𝓞 K) K))

  g : ℕ

  v : Fin g → (epsR K ⟶ tK.G)
  basis : IsLieBasis v

namespace GenFib

variable {t t' : SAB H (Sp (𝓞 K))} (F : GenFib t) (F' : GenFib t')

structure CxFib (σ : K →+* ℂ) where

  A : Over (Sp ℂ)
  [grp : GrpObj A]

  φ : A.left ⟶ F.tK.G.left
  cart : IsGrpPullback A F.tK.G (spMap σ) φ

  u : HolUnif A (F.tK.PP.L.pull φ) F.g

  Hm : Matrix (Fin F.g) (Fin F.g) ℂ

  χ : u.Λ → ℂ
  ah : u.IsAH Hm χ

  vC : Fin F.g → (epsR ℂ ⟶ A)
  vC_base : ∀ i, (vC i).left ≫ φ = spMap (Chart.dualMapR σ) ≫ (F.v i).left

  W : Fin F.g → (Fin F.g → ℂ)
  diff : ∀ i, u.IsDiff (W i) (vC i)

attribute [instance] CxFib.grp



end GenFib

section Sum

variable {S : Scheme.{0}}

def sumPow {A B : Over S} [GrpObj B] {n : ℕ} (f : Fin n → (A ⟶ B)) : (∏ᶜ fun _ : Fin n => A) ⟶ B :=
  (List.ofFn fun i => Pi.π (fun _ : Fin n => A) i ≫ f i).prod

def sumMap {A A' B : Over S} [GrpObj B] {p q : ℕ} (f : Fin p → (A ⟶ B)) (f' : Fin q → (A' ⟶ B)) :
    (∏ᶜ fun _ : Fin p => A) ⊗ (∏ᶜ fun _ : Fin q => A') ⟶ B :=
  (fst _ _ ≫ sumPow f) * (snd _ _ ≫ sumPow f')

def IsFinFlatSurj {X Y : Over S} (f : X ⟶ Y) : Prop := IsFinite f.left ∧ Flat f.left ∧ Surjective f.left

def IsLinHom {t t' : SAB H S} (f : t.G ⟶ t'.G) : Prop :=
  IsMonHom f ∧ ∀ a : 𝓞 E, t.act.act a ≫ f = f ≫ t'.act.act a

def PolId {t t' : SAB H S} (f : t.G ⟶ t'.G) (h : 𝓞 E) : Prop :=
  WeilEq t'.PP.L f f t.PP.L (t.act.act h) (𝟙 t.G)

end Sum

structure CMObj (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (p q : ℕ) where

  A : SAB H (Sp (𝓞 K))

  A' : SAB H (Sp (𝓞 K))

  B : SAB H (Sp (𝓞 K))
  prinA : IsPrincipal A
  prinA' : IsPrincipal A'
  prinB : IsPrincipal B
  sigA : HasSig H 1 0 A.act ρ
  sigA' : HasSig H 0 1 A'.act ρ
  sigB : HasSig H p q B.act ρ

  ph : Fin p → (A.G ⟶ B.G)

  ph' : Fin q → (A'.G ⟶ B.G)
  lin : ∀ i, IsLinHom (ph i)
  lin' : ∀ j, IsLinHom (ph' j)
  isog : IsFinFlatSurj (sumMap ph ph')

  h : Fin p → 𝓞 E

  h' : Fin q → 𝓞 E
  pol : ∀ i, PolId (ph i) (h i)
  pol' : ∀ j, PolId (ph' j) (h' j)

namespace CMObj

variable {ρ : 𝓞 K} {p q : ℕ} (X : CMObj H K ρ p q)

end CMObj

end GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFibres
end
end

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory.CM GlobalTheory.IndefiniteRowSideFullHecke

noncomputable section
namespace GlobalTheory.CMSharedCompare

section Comb

variable {R : Type} [CommRing R]

end Comb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]

section Vec

variable {t : SAB H (Sp (𝓞 K))} (G : EigenLatticeFibres.GenFib t)

end Vec

structure Partner {T : PAT H (Sp (𝓞 K))} (F : GenFib T.pol) where

  tK : SAB H (Sp K)

  m : SABMap tK T.t (spMap (algebraMap (𝓞 K) K))

  v : Fin F.P₀.g → (epsR K ⟶ tK.G)
  basis : IsLieBasis v
  same : ∀ i, (v i).left ≫ m.φ = (F.v i).left ≫ F.φ

variable {T T' : PAT H (Sp (𝓞 K))}

namespace Partner

variable {F : GenFib T.pol} {F' : GenFib T'.pol} (Q : Partner F) (Q' : Partner F')

end Partner

section Metric

variable {T : PAT H (Sp (𝓞 K))} {F : GenFib T.pol} (Q : Partner F)

end Metric

section Embeddings

end Embeddings

section Isogeny

end Isogeny

section Object

theorem nonempty_genFib (P : Out.PolAV (Sp (𝓞 K))) : Nonempty (GenFib P) := by
  have := P.isAb.comm
  have h := isGrpPullback_pullback P.A (spMap (algebraMap (𝓞 K) K))
  obtain ⟨v, hv⟩ := TenDim.exists_isLieBasis _ (TorsionTauCompare.polOfPullback P _ h).smoothDim
  exact ⟨⟨TorsionTauCompare.polOfPullback P _ h, _, ⟨rfl, h, PolBaseChange.lbIso_refl (pull_isLB P.isLB _)⟩, v, hv⟩⟩

theorem dim_eq {ρ : 𝓞 K} {p q : ℕ} (T : PAT H (Sp (𝓞 K))) (hs : Splits E K) (ht : HasType H T.t.act ρ p q)
    (hρ : ρ ^ 2 = -(H.d : 𝓞 K)) : T.g = Module.finrank ℚ E / 2 * (p + q) := by
  obtain ⟨F⟩ := nonempty_genFib T.pol
  exact (EigDec.eigen_decomposition E H K ρ T F p q hs ht hρ).2.2.2.1

variable {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ}

end Object

end GlobalTheory.CMSharedCompare
end
end
