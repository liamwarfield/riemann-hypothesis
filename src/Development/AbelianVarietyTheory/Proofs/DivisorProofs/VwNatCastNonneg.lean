module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnfoldingConstantTermsAgreeAtGoodEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelDataX
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.LocalGeometry.Imports
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHeckeCharacterPhaseTypeCm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealOneParamProductChartAdelicUnitary

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SumSize.TopInt

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

def primeUnder (w : PlL D) : ℕ := ringChar (𝓞 D.what₂.LL ⧸ w.asIdeal)

theorem primeUnder_mem (w : PlL D) : ((primeUnder w : ℕ) : 𝓞 D.what₂.LL) ∈ w.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem primeUnder_prime (w : PlL D) : (primeUnder w).Prime := by
  haveI : w.asIdeal.IsPrime := w.isPrime
  haveI : Finite (𝓞 D.what₂.LL ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  exact CharP.char_is_prime (𝓞 D.what₂.LL ⧸ w.asIdeal) (ringChar (𝓞 D.what₂.LL ⧸ w.asIdeal))

def kerLoss (G : GridData L sc) (δ : ℕ → ℝ) (C1 b : ℝ) (X Y : Node) (l n : ℕ) : ℝ :=
  (((∑ τ, ∑ a, (wt G Y τ).natW a : ℕ) : ℝ) + (D.R.f : ℝ) * (G.V X).rank * (G.V Y).rank) *
      (δ l + (if l = D.host.d then 1 else 0) + n) +
    (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * (if (l : ℝ) ≤ C1 * b then Real.logb l (C1 * b) else 0)

def topDl (G : GridData L sc) (δ : ℕ → ℝ) (C1 b : ℝ) (w : PlL D) : ℝ :=
  (vw w ((primeUnder w : ℕ) : D.what₂.LL) : ℝ) * C1 *
    ∑ j ∈ Finset.range D.R.m, kerLoss G δ C1 b (.top j) (.top (j + 1)) (primeUnder w) (depL G (primeUnder w))

theorem vw_natCast_nonneg (w : PlL D) (n : ℕ) : 0 ≤ vw w ((n : ℕ) : D.what₂.LL) := by
  have e : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.what₂.LL)) ((n : ℕ) : D.what₂.LL) =
      ((Ideal.span {((n : ℕ) : 𝓞 D.what₂.LL)} : Ideal (𝓞 D.what₂.LL)) : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) := by
    rw [FractionalIdeal.coeIdeal_span_singleton,
      map_natCast (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)]
  unfold vw
  rw [e]
  exact FractionalIdeal.count_coe_nonneg _ _ _

theorem kerLoss_nonneg (G : GridData L sc) {δ : ℕ → ℝ} (hδ : ∀ l, 0 ≤ δ l) (C1 b : ℝ) (X Y : Node) {l : ℕ} (hl : l.Prime)
    (n : ℕ) : 0 ≤ kerLoss G δ C1 b X Y l n := by
  unfold kerLoss
  have h1 : 0 ≤ (if l = D.host.d then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have h2 : 0 ≤ (if (l : ℝ) ≤ C1 * b then Real.logb l (C1 * b) else 0) := by
    split_ifs with h
    · exact Real.logb_nonneg (by exact_mod_cast hl.one_lt) (le_trans (by exact_mod_cast hl.one_lt.le) h)
    · exact le_rfl
  have := hδ l
  positivity

theorem kerLoss_mono (G : GridData L sc) (δ : ℕ → ℝ) (C1 b : ℝ) (X Y : Node) (l : ℕ) {n n' : ℕ} (h : n ≤ n') :
    kerLoss G δ C1 b X Y l n ≤ kerLoss G δ C1 b X Y l n' := by
  unfold kerLoss
  have : (n : ℝ) ≤ n' := by exact_mod_cast h
  gcongr

theorem le_topDl (G : GridData L sc) {δ : ℕ → ℝ} (hδ : ∀ l, 0 ≤ δ l) {C1 : ℝ} (hC1 : 0 ≤ C1) (b : ℝ) (w : PlL D) {j : ℕ}
    (hj : j < D.R.m) {n : ℕ} (hn : n ≤ depL G (primeUnder w)) :
    (vw w ((primeUnder w : ℕ) : D.what₂.LL) : ℝ) * C1 * kerLoss G δ C1 b (.top j) (.top (j + 1)) (primeUnder w) n ≤
      topDl G δ C1 b w := by
  unfold topDl
  have h0 : (0 : ℝ) ≤ (vw w ((primeUnder w : ℕ) : D.what₂.LL) : ℝ) * C1 :=
    mul_nonneg (by exact_mod_cast vw_natCast_nonneg w _) hC1
  refine mul_le_mul_of_nonneg_left ?_ h0
  refine le_trans (kerLoss_mono G δ C1 b _ _ _ hn) ?_
  exact Finset.single_le_sum (f := fun j => kerLoss G δ C1 b (.top j) (.top (j + 1)) (primeUnder w) (depL G (primeUnder w)))
    (fun j _ => kerLoss_nonneg G hδ C1 b _ _ (primeUnder_prime w) _) (Finset.mem_range.2 hj)

theorem inLat_mono {n : ℕ} {lam : D.what₂.Tau → DomWeight n} {w : PlL D} {a a' : ℝ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {v : VV ℂ lam} (h : InLat lam w a Λ v) (ha : a ≤ a') : InLat lam w a' Λ v := by
  obtain ⟨u, s, h1, h2, h3, h4⟩ := h
  exact ⟨u, s, h1, h2, h3.trans ha, h4⟩

end GlobalTheory.SumSize.TopInt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open Filter
open scoped SchwartzMap Topology Uniformity

namespace GlobalTheory
namespace SchwartzComplete

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem iteratedFDeriv_sub' (f g : 𝓢(V, ℂ)) (n : ℕ) (x : V) :
    iteratedFDeriv ℝ n (⇑(f - g)) x = iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n g x := by
  have hf : ContDiff ℝ n f := f.smooth n
  have hg : ContDiff ℝ n g := g.smooth n
  rw [show (⇑(f - g) : V → ℂ) = ⇑f - ⇑g from rfl]
  exact iteratedFDeriv_sub_apply hf.contDiffAt hg.contDiffAt

theorem cauchy_seminorm {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) (k n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ a ≥ N, ∀ b ≥ N, SchwartzMap.seminorm ℝ k n (u a - u b) < ε := by
  rw [cauchySeq_iff_tendsto, uniformity_eq_comap_nhds_zero, tendsto_comap_iff] at hu
  have h := ((schwartz_withSeminorms ℝ V ℂ).tendsto_nhds _ 0).1 hu (k, n) ε hε
  obtain ⟨⟨N₁, N₂⟩, hN⟩ := eventually_atTop.1 h
  refine ⟨max N₁ N₂, fun a ha b hb => ?_⟩
  have := hN (b, a) (Prod.mk_le_mk.2 ⟨le_of_max_le_left hb, le_of_max_le_right ha⟩)
  simpa [schwartzSeminormFamily] using this

noncomputable def limD (u : ℕ → 𝓢(V, ℂ)) (n : ℕ) (x : V) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => V) ℂ :=
  limUnder atTop fun j => iteratedFDeriv ℝ n (u j) x

theorem tendsto_limD {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) (n : ℕ) (x : V) :
    Tendsto (fun j => iteratedFDeriv ℝ n (u j) x) atTop (𝓝 (limD u n x)) := by
  refine tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete ?_)
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := cauchy_seminorm hu 0 n hε
  refine ⟨N, fun a ha b hb => ?_⟩
  rw [dist_eq_norm, ← iteratedFDeriv_sub']
  have := SchwartzMap.le_seminorm ℝ 0 n (u a - u b) x
  simp only [pow_zero, one_mul] at this
  exact this.trans_lt (hN a ha b hb)

theorem key {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) (k n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ j ≥ N, ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (u j) x - limD u n x‖ ≤ ε := by
  obtain ⟨N, hN⟩ := cauchy_seminorm hu k n hε
  refine ⟨N, fun j hj x => ?_⟩
  have ht : Tendsto (fun b => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (u j) x - iteratedFDeriv ℝ n (u b) x‖)
      atTop (𝓝 (‖x‖ ^ k * ‖iteratedFDeriv ℝ n (u j) x - limD u n x‖)) :=
    ((tendsto_const_nhds.sub (tendsto_limD hu n x)).norm).const_mul _
  refine le_of_tendsto ht (eventually_atTop.2 ⟨N, fun b hb => ?_⟩)
  rw [← iteratedFDeriv_sub']
  exact (SchwartzMap.le_seminorm ℝ k n (u j - u b) x).trans (hN j hj b hb).le

theorem tendstoUniformly_limD {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) (n : ℕ) :
    TendstoUniformly (fun j => iteratedFDeriv ℝ n (u j)) (limD u n) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := key hu 0 n (half_pos hε)
  refine eventually_atTop.2 ⟨N, fun j hj x => ?_⟩
  have := hN j hj x
  rw [pow_zero, one_mul] at this
  rw [dist_eq_norm, norm_sub_rev]
  linarith

theorem continuous_limD {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) (n : ℕ) :
    Continuous (limD u n) :=
  (tendstoUniformly_limD hu n).continuous (Eventually.of_forall (f := atTop) fun j =>
    ((u j).smooth ⊤).continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)).frequently

theorem hasFDerivAt_limD {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) (m : ℕ) (x : V) :
    HasFDerivAt (limD u m) ((limD u (m + 1) x).curryLeft) x := by
  refine hasFDerivAt_of_tendstoUniformly (f := fun j => iteratedFDeriv ℝ m (u j))
    (f' := fun j y => fderiv ℝ (iteratedFDeriv ℝ m (u j)) y)
    (g' := fun y => (limD u (m + 1) y).curryLeft) ?_ ?_ (fun y => tendsto_limD hu m y) x
  · exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => V) ℂ).isometry.uniformContinuous.comp_tendstoUniformly
      (tendstoUniformly_limD hu (m + 1))
  · intro j y
    exact ((((u j).smooth ⊤).differentiable_iteratedFDeriv
      (by exact_mod_cast WithTop.coe_lt_top (m : ℕ))) y).hasFDerivAt

theorem hasFTaylorSeries {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) :
    HasFTaylorSeriesUpTo ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (limD u 0 x).curry0)
      (fun x => (fun m => limD u m x : FormalMultilinearSeries ℝ V ℂ)) :=
  ⟨fun _ => rfl, fun m _ x => hasFDerivAt_limD hu m x, fun m _ => continuous_limD hu m⟩

noncomputable def limMap (u : ℕ → 𝓢(V, ℂ)) (hu : CauchySeq u) : 𝓢(V, ℂ) where
  toFun x := (limD u 0 x).curry0
  smooth' := (hasFTaylorSeries hu).contDiff
  decay' k n := by
    obtain ⟨N, hN⟩ := key hu k n one_pos
    refine ⟨SchwartzMap.seminorm ℝ k n (u N) + 1, fun x => ?_⟩
    rw [← (hasFTaylorSeries hu).eq_iteratedFDeriv (m := n) (by exact_mod_cast le_top) x]
    have h1 := hN N le_rfl x
    have h2 := SchwartzMap.le_seminorm ℝ k n (u N) x
    have h3 : ‖limD u n x‖ ≤ ‖iteratedFDeriv ℝ n (u N) x‖ + ‖iteratedFDeriv ℝ n (u N) x - limD u n x‖ := by
      have := norm_sub_le (iteratedFDeriv ℝ n (u N) x) (iteratedFDeriv ℝ n (u N) x - limD u n x)
      simpa using this
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ ‖x‖ ^ k)
    change ‖x‖ ^ k * ‖limD u n x‖ ≤ _
    rw [mul_add] at h4
    linarith

theorem iteratedFDeriv_limMap {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) (n : ℕ) (x : V) :
    iteratedFDeriv ℝ n (limMap u hu) x = limD u n x :=
  ((hasFTaylorSeries hu).eq_iteratedFDeriv (m := n) (by exact_mod_cast le_top) x).symm

theorem tendsto_limMap {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) :
    Tendsto u atTop (𝓝 (limMap u hu)) := by
  rw [(schwartz_withSeminorms ℝ V ℂ).tendsto_nhds]
  rintro ⟨k, n⟩ ε hε
  obtain ⟨N, hN⟩ := key hu k n (half_pos hε)
  refine eventually_atTop.2 ⟨N, fun j hj => ?_⟩
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  refine SchwartzMap.seminorm_le_bound ℝ k n _ (half_pos hε).le fun x => ?_
  rw [iteratedFDeriv_sub', iteratedFDeriv_limMap]
  exact hN j hj x

instance completeSpace : CompleteSpace 𝓢(V, ℂ) := by
  haveI : (𝓤 𝓢(V, ℂ)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact UniformSpace.complete_of_cauchySeq_tendsto fun u hu => ⟨limMap u hu, tendsto_limMap hu⟩

end SchwartzComplete

theorem schwartzMap_barrelledSpace : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V], BarrelledSpace ℂ (SchwartzMap V ℂ) := by
  intro V _ _ _
  haveI : (𝓤 𝓢(V, ℂ)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  infer_instance

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzMap_barrelledSpace' : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V], BarrelledSpace ℂ (SchwartzMap V ℂ) := by
  first | exact @GlobalTheory.schwartzMap_barrelledSpace | exact GlobalTheory.schwartzMap_barrelledSpace | (intros; apply GlobalTheory.schwartzMap_barrelledSpace <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicCuspSectionsLeSpanAlgebraicCuspForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicCuspSectionsLeSpanAlgebraicCuspForms
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OntoCore


set_option maxHeartbeats 1000000 in
theorem holSub0_le_span_cuspA : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → ∀ w : WeightFamilies.Wt D j, w.LastPos → 8 * D.R.f * D.R.r + 4 ≤ w.n → ∀ σ, GoodEmb T.Q.c σ → Formalism.L2.Pj.holSub0 (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) ≤ Submodule.span ℂ (rdU (T.U j σ) '' (T.cuspA j (wtA w) w.n : Set (T.R j))) := by
  intro D T h j hj w hw hn σ hσ
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := Formalism.L2.Pj.hostSize_finrank D
  have hn' : 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ w.n := by
    rw [hfr]
    calc 4 * (2 * D.R.f * D.R.r) + 4 = 8 * D.R.f * D.R.r + 4 := by ring
      _ ≤ w.n := hn
  obtain ⟨hrk, hM⟩ := h.modelW j hj σ hσ
  have key := GlobalTheory.Dict.holSub0_le_span_cusp GlobalTheory.chartIndependence_unconditional D.host.E T.Q.H (T.Q.Dw j) T.Q.l
    (T.Q.Xo j) T.Q.c D.R.r (fun s => Formalism.L2.PjFree.Unf.ofPj (T.U j s)) hr h.pins.2.1.2
    (fun s hs => (Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj s hs)) σ hσ
    (fun k k' => ⟨(hM k).1.trans (hM k').1.symm, (hM k).2.trans (hM k').2.symm⟩)
    (fun k => GlobalTheory.PrincCore.mem_group_of_congruent D T.toCore h.toLawsM j hj σ hσ k)
    (wtA w) w.n (dom_wtA w) (GlobalTheory.lastPos_wtA_of_pins D T.Q h.pins j hj w hw) hn'
    (fun k => h.chiTriv j hj σ hσ (wtA w) w.n (dom_wtA w) k)
  intro P hP
  exact key ⟨hP.1, hP.2⟩

end GlobalTheory.OntoCore
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicCuspSectionsLeSpanAlgebraicCuspFormsStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicCuspSections_le_span_algebraicCuspForms : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → ∀ w : WeightFamilies.Wt D j, w.LastPos → 8 * D.R.f * D.R.r + 4 ≤ w.n → ∀ σ, GoodEmb T.Q.c σ → Formalism.L2.Pj.holSub0 (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) ≤ Submodule.span ℂ (rdU (T.U j σ) '' (T.cuspA j (wtA w) w.n : Set (T.R j))) := by
  first | exact @GlobalTheory.OntoCore.holSub0_le_span_cuspA | exact GlobalTheory.OntoCore.holSub0_le_span_cuspA | (intros; apply GlobalTheory.OntoCore.holSub0_le_span_cuspA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbLLMem
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

namespace GlobalTheory.KerConjMean

variable (D : D7) (δ t0 : ℂ)

abbrev lat : AddSubgroup ℂ := lamOf D D.host.ccK δ

def fld : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (Set.range D.what₂.embLL ∪ {g2 (lat D δ), g3 (lat D δ), wpF (lat D δ) t0})

theorem embLL_mem (x : D.what₂.LL) : D.what₂.embLL x ∈ fld D δ t0 :=
  IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨x, rfl⟩)

def ext (σ : D.what₂.LL →+* ℂ) : Set (fld D δ t0 →ₐ[ℚ] ℂ) :=
  {ρ | ∀ x, ρ ⟨D.what₂.embLL x, embLL_mem D δ t0 x⟩ = σ x}


open Classical in
def tc (ρ : fld D δ t0 →ₐ[ℚ] ℂ) : ℂ :=
  if h : ∃ t, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj (fld D δ t0) ρ (lat D δ)) t then h.choose else 0

def hArea (ρ : fld D δ t0 →ₐ[ℚ] ℂ) : ℝ := Real.posLog (area (lamConj (fld D δ t0) ρ (lat D δ)))⁻¹

def hTh (ρ : fld D δ t0 →ₐ[ℚ] ℂ) : ℝ :=
  Real.posLog (nrm1Sq (lamConj (fld D δ t0) ρ (lat D δ)) (GL3Theta.th0 (lamConj (fld D δ t0) ρ (lat D δ)) (tc D δ t0 ρ)))

def avg (σ : D.what₂.LL →+* ℂ) (h : (fld D δ t0 →ₐ[ℚ] ℂ) → ℝ) : ℝ :=
  (∑ᶠ ρ ∈ ext D δ t0 σ, h ρ) / Nat.card (ext D δ t0 σ)

end GlobalTheory.KerConjMean

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat

namespace GlobalTheory.KerConjMean

open GlobalTheory.SumSize GlobalTheory.RowTest GlobalTheory.FunObj GlobalTheory.ChiGrid Formalism.IndefR.Links Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Claims

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
  (ch : _root_.GlobalTheory.RowTest.Choice R) (C b C1 : ℝ)

def RatTopAt : Prop := ∀ Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (j : Fin D.R.m),
  ∃ f : VV D.what₂.LL (wt ch.G (.top j)) →ₗ[D.what₂.LL] VV D.what₂.LL (wt ch.G (.top (j + 1))), ∀ u,
    ch.S.Z.kkMap 1 (d.1 j) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) (GlobalTheory.CoefModel.mapVV D.what₂.embLL _ u) =
      GlobalTheory.CoefModel.mapVV D.what₂.embLL _ (f u)

def ConjTopAt : Prop := ∃ a0 nD Gd : ℝ, 0 ≤ a0 ∧ 0 ≤ nD ∧ 0 ≤ Gd ∧ 2 * a0 + (nD + Gd) * C1 * Real.log b ≤ aOne ch.G C b ∧
  ∀ Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (j : Fin D.R.m)
    (f : VV D.what₂.LL (wt ch.G (.top j)) →ₗ[D.what₂.LL] VV D.what₂.LL (wt ch.G (.top (j + 1)))),
    (∀ u, ch.S.Z.kkMap 1 (d.1 j) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) (GlobalTheory.CoefModel.mapVV D.what₂.embLL _ u) =
      GlobalTheory.CoefModel.mapVV D.what₂.embLL _ (f u)) →
    ∀ (σ : D.what₂.LL →+* ℂ), ∀ ρ ∈ ext D ch.S.Z.δ ch.S.Z.t0 σ, ∀ u (B : ℝ), nrm _ (fun _ => 1) (GlobalTheory.CoefModel.mapVV σ _ u) ≤ B →
      nrm _ (fun _ => 1) (GlobalTheory.CoefModel.mapVV σ _ (f u)) ≤
        Real.exp (a0 + nD * hArea D ch.S.Z.δ ch.S.Z.t0 ρ + Gd * hTh D ch.S.Z.δ ch.S.Z.t0 ρ) * B

end Claims

end GlobalTheory.KerConjMean

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeltaTApply
open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace GlobalTheory.DblTargetDelta

open Formalism.IndefR.DatumF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {nS nT : ℕ}

def topR (x : WOF F E nS (nT + nT)) : WOF F E nS nT := x.submatrix (finSumFinEquiv ∘ Sum.inl) id

def botR (x : WOF F E nS (nT + nT)) : WOF F E nS nT := x.submatrix (finSumFinEquiv ∘ Sum.inr) id

def deltaT (f₁ f₂ : WOF F E nS nT → ℂ) : WOF F E nS (nT + nT) → ℂ :=
  fun x => f₁ (topR x) * conj (f₂ (-botR x))

theorem deltaT_apply (f₁ f₂ : WOF F E nS nT → ℂ) (x : WOF F E nS (nT + nT)) :
    deltaT f₁ f₂ x = f₁ (topR x) * conj (f₂ (-botR x)) := rfl

end GlobalTheory.DblTargetDelta

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHermitianFormScaledCoordinateEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaLawOF
variable {D : D7}

theorem zCo_iota {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hch : GlobalTheory.FockCompare.Chart θ σ) {S T : HSp D}
    (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E) (z : GlobalTheory.FockCompare.RW T S) :
    GlobalTheory.FockPos.zCo θ frS frT (GlobalTheory.FockCompare.iotaW σ T S z) =
      fun τ => (GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (z τ) * GlobalTheory.FockPos.frAt frS τ := by
  funext τ
  have e : compAt θ τ (GlobalTheory.FockCompare.iotaW σ T S z) = Matrix.of (z τ) := congrFun (hch.pi_iota T S z) τ
  simp only [GlobalTheory.FockPos.zCo, e]
  rfl

theorem frAt_inv {n : ℕ} (fr : GL (Fin n) D.host.E) (τ : D.what₂.Tau) :
    (GlobalTheory.FockPos.frAt fr τ)⁻¹ * GlobalTheory.FockPos.frAt fr τ = 1 ∧ GlobalTheory.FockPos.frAt fr τ * (GlobalTheory.FockPos.frAt fr τ)⁻¹ = 1 :=
  ⟨Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (GlobalTheory.FockPos.frAt_det_ne fr τ)),
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (GlobalTheory.FockPos.frAt_det_ne fr τ))⟩

theorem coord_back {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (Z : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank) (τ : D.what₂.Tau) :
    (GlobalTheory.FockPos.frAt frT τ)⁻¹ * (GlobalTheory.FockPos.frAt frT τ * Matrix.of (Z τ) * (GlobalTheory.FockPos.frAt frS τ)⁻¹) *
      GlobalTheory.FockPos.frAt frS τ = Matrix.of (Z τ) := by
  have h1 := (frAt_inv frS τ).1
  have h2 := (frAt_inv frT τ).1
  calc _ = ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * GlobalTheory.FockPos.frAt frT τ) * Matrix.of (Z τ) *
        ((GlobalTheory.FockPos.frAt frS τ)⁻¹ * GlobalTheory.FockPos.frAt frS τ) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.ThetaLawOF

namespace GlobalTheory.ThetaLawOF
variable {D : D7}

theorem trace_conjTranspose_mul {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℂ) :
    (Aᴴ * B).trace = ∑ a, ∑ b, starRingEnd ℂ (A a b) * B a b := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  rfl

theorem omO_frame {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (hT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1) (x y : GlobalTheory.FockCompare.RW T S) :
    GlobalTheory.VacUnique.omO S T x y = ∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ (((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (y τ) * GlobalTheory.FockPos.frAt frS τ) a b) *
        ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (x τ) * GlobalTheory.FockPos.frAt frS τ) a b)).re := by
  rw [GlobalTheory.VacUnique.omO_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  show 2 * (tauE D τ D.host.xi0 * GlobalTheory.VacUnique.hAt S T τ (Matrix.of (x τ)) (Matrix.of (y τ))).re = _
  rw [GlobalTheory.FockJetOrigin.hAt_coord (BS := fun τ => GlobalTheory.FockPos.frAt frS τ)
    (BT := fun τ => GlobalTheory.FockPos.frAt frT τ) (GlobalTheory.FockPos.frAt_on frS hS τ) (GlobalTheory.FockPos.frAt_on frT hT τ),
    trace_conjTranspose_mul, GlobalTheory.FockJetOrigin.realPlace_cmTrace_zero_element_eq_I_mul_abs, Finset.mul_sum, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Complex.re_sum, Finset.mul_sum]

theorem torusHermitianForm_scaled_coordinate_eq {N N' : ℕ} {δ : ℂ} (hδ : δ ≠ 0) (Z X : Formalism.MainNotions.TaylorLogMetric.VC D N N') :
    Formalism.MainNotions.TaylorLogMetric.Hf D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • Z) (δ • X) =
      2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b) := by
  have e : (∑ τ, ∑ i, ∑ j, (δ • Z) τ i j * starRingEnd ℂ ((δ • X) τ i j)) =
      (δ * starRingEnd ℂ δ) * ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (X τ i j) := by
    simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hL : (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ).abelian₂ = Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ := rfl
  obtain ⟨hxi, hN, hd⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D
  rw [Formalism.MainNotions.TaylorLogMetric.Hf, e, hL, GlobalTheory.MomDict.area_lamOf D D.host.ccK δ D.host.ccK_ne_bot, hxi, Complex.mul_conj]
  have h0 : (Complex.normSq δ : ℂ) ≠ 0 := by exact_mod_cast (Complex.normSq_pos.2 hδ).ne'
  have h1 : ((Ideal.absNorm D.host.ccK : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (Ideal.absNorm D.host.ccK : ℝ) ≠ 0)
  have h2 : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : Real.sqrt D.host.d ≠ 0)
  push_cast
  field_simp

theorem al_mul_self {N N' : ℕ} (T0 : Formalism.MainNotions.TaylorLogMetric.Tor D) (x : Formalism.MainNotions.TaylorLogMetric.VC D N N') :
    Formalism.MainNotions.TaylorLogMetric.al D T0 x * Formalism.MainNotions.TaylorLogMetric.al D T0 x = 1 := by
  rw [Formalism.MainNotions.TaylorLogMetric.al, ← mul_zpow, show (-1 : ℂ) * -1 = 1 by norm_num, _root_.one_zpow]

theorem entry (zz xx : ℂ) (r : ℝ) :
    (Real.pi : ℂ) * Complex.I * ((2 * (Complex.I * (r : ℂ) * (starRingEnd ℂ zz * xx)).re : ℝ) : ℂ) -
      2 * (Real.pi : ℂ) * (r : ℂ) * (zz * starRingEnd ℂ xx) - (Real.pi : ℂ) * (r : ℂ) * (xx * starRingEnd ℂ xx) =
      (Real.pi : ℂ) * (r : ℂ) * ((‖zz‖ ^ 2 : ℝ) - (‖zz + xx‖ ^ 2 : ℝ) : ℝ) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.mul_conj]
  apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring

end GlobalTheory.ThetaLawOF

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedFormEqAdelicThetaDistribution
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedFormEqAdelicThetaDistribution
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

open scoped Classical

namespace GlobalTheory.ThetaAdmitted

theorem summable_one_add_norm_inv_pow {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] {k : ℕ} (hk : Module.finrank ℤ L < k) :
    Summable fun z : L => ((1 + ‖z‖)⁻¹) ^ k := by
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_)
    ((ZLattice.summable_norm_pow_inv L k hk).add (hasSum_ite_eq (0 : L) (1 : ℝ)).summable)
  by_cases hz : z = 0
  · subst hz
    simp only [if_pos rfl, norm_zero, add_zero, inv_one, one_pow]
    exact le_add_of_nonneg_left (by positivity)
  · have h0 : 0 < ‖z‖ := norm_pos_iff.2 hz
    simp only [hz, if_false, add_zero]
    gcongr
    linarith

variable (F : Type) [Field F] [NumberField F]

theorem norm_thetaSum_pureA_le {κ : Type} [Fintype κ] {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.pureA F f g)‖ ≤
        C * (s.sup (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)) f := by
  obtain ⟨B, hB⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  obtain ⟨N, hN, hK⟩ := GlobalTheory.WeilM.exists_nat_mul_integral_of_isCompact F hg.2.isCompact
  haveI := GlobalTheory.WeilM.discreteTopology_denomLattice F κ hN
  set L := GlobalTheory.WeilM.denomLattice F κ N with hLdef
  set k := Module.finrank ℤ L + 1 with hkdef
  have hu : Summable fun z : L => ((1 + ‖z‖)⁻¹) ^ k := summable_one_add_norm_inv_pow L (Nat.lt_succ_self _)
  set M := ∑' z : L, ((1 + ‖z‖)⁻¹) ^ k with hMdef
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hM0 : 0 ≤ M := tsum_nonneg fun z => by positivity
  refine ⟨Finset.Iic (k, 0), B * 2 ^ k * M, by positivity, fun f => ?_⟩
  set S := (Finset.Iic (k, 0)).sup (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ) f with hSdef
  have hS0 : 0 ≤ S := apply_nonneg _ _
  have hf : ∀ x, ‖f x‖ ≤ 2 ^ k * S * ((1 + ‖x‖)⁻¹) ^ k := by
    intro x
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, 0)) le_rfl le_rfl f x
    rw [norm_iteratedFDeriv_zero] at h
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
    exact h
  let Sset : Set (κ → F) := {ξ | (fun i => mixedEmbedding F (ξ i)) ∈ L}
  have hsupp : ∀ ξ, ξ ∉ Sset → g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) = 0 := by
    intro ξ hξ
    by_contra h0
    apply hξ
    refine fun i => ?_
    obtain ⟨y, hy⟩ := (IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun v => by
      rw [map_mul, map_natCast]
      exact hK _ (subset_tsupport _ h0) i v
    refine ⟨y, ?_⟩
    have h2 := congrArg (mixedEmbedding F) hy
    rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
    exact h2.symm
  have hΦ : GlobalTheory.WeilM.pureA F f g ∈ GlobalTheory.WeilM.schA F κ := Submodule.subset_span ⟨f, g, hg, rfl⟩
  have hsn := GlobalTheory.WeilM.summable_norm_of_mem_schA F hΦ
  let a : (κ → F) → ℂ := fun ξ => GlobalTheory.WeilM.pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))
  have ha : ∀ ξ, a ξ = f (fun i => mixedEmbedding F (ξ i)) *
      g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) := fun ξ => GlobalTheory.WeilM.pureA_algebraMap F f g ξ
  have hsupa : Function.support (fun ξ => ‖a ξ‖) ⊆ Sset := by
    intro ξ hξ
    by_contra h
    apply hξ
    simp only [ha, hsupp ξ h, mul_zero, norm_zero]
  let j : Sset → L := fun ξ => ⟨_, ξ.2⟩
  have hj : Function.Injective j := fun a b h => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
  have hle : ∀ ξ : Sset, ‖a ξ‖ ≤ B * 2 ^ k * S * ((1 + ‖j ξ‖)⁻¹) ^ k := by
    intro ξ
    have h1 := hB (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ.1 i))
    have h2 : ‖f (fun i => mixedEmbedding F (ξ.1 i))‖ ≤ 2 ^ k * S * ((1 + ‖j ξ‖)⁻¹) ^ k := hf (j ξ)
    rw [ha, norm_mul]
    calc ‖f (fun i => mixedEmbedding F (ξ.1 i))‖ * ‖g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ.1 i))‖
        ≤ (2 ^ k * S * ((1 + ‖j ξ‖)⁻¹) ^ k) * B := mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
      _ = B * 2 ^ k * S * ((1 + ‖j ξ‖)⁻¹) ^ k := by ring
  have hsumS : Summable fun ξ : Sset => B * 2 ^ k * S * ((1 + ‖j ξ‖)⁻¹) ^ k :=
    (hu.comp_injective hj).mul_left _
  calc ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.pureA F f g)‖ = ‖∑' ξ, a ξ‖ := rfl
    _ ≤ ∑' ξ, ‖a ξ‖ := norm_tsum_le_tsum_norm hsn
    _ = ∑' ξ : Sset, ‖a ξ‖ := (tsum_subtype_eq_of_support_subset hsupa).symm
    _ ≤ ∑' ξ : Sset, B * 2 ^ k * S * ((1 + ‖j ξ‖)⁻¹) ^ k :=
        Summable.tsum_le_tsum hle (hsn.subtype _) hsumS
    _ = B * 2 ^ k * S * ∑' ξ : Sset, ((1 + ‖j ξ‖)⁻¹) ^ k := tsum_mul_left
    _ ≤ B * 2 ^ k * S * M := by
        gcongr
        exact tsum_comp_le_tsum_of_inj hu (fun z => by positivity) hj
    _ = B * 2 ^ k * M * S := by ring

theorem exists_admitted_form_eq_adelicThetaDistribution_alt : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ l ∈ (GlobalTheory.WeilM.adeleClass F).adm κ, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, l Φ = GlobalTheory.WeilM.thetaSum F Φ := by
  intro F _ _ κ _
  obtain ⟨l, hl⟩ := LinearMap.exists_extend (GlobalTheory.WeilM.thetaLin F κ)
  have hl' : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, l Φ = GlobalTheory.WeilM.thetaSum F Φ := fun Φ hΦ => by
    have := LinearMap.congr_fun hl ⟨Φ, hΦ⟩
    simpa using this
  refine ⟨l, ?_, hl'⟩
  intro g hg
  have hmem : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      GlobalTheory.WeilM.pureA F f g ∈ GlobalTheory.WeilM.schA F κ := fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩
  refine ⟨SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ)
    (fun f => GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.pureA F f g)) ?_ ?_ (norm_thetaSum_pureA_le F hg), fun f => ?_⟩
  · intro f₁ f₂
    have : GlobalTheory.WeilM.pureA F (f₁ + f₂) g = GlobalTheory.WeilM.pureA F f₁ g + GlobalTheory.WeilM.pureA F f₂ g := by
      funext x; simp [GlobalTheory.WeilM.pureA, add_mul]
    rw [this, GlobalTheory.WeilM.thetaSum_add F (hmem f₁) (hmem f₂)]
  · intro c f
    have : GlobalTheory.WeilM.pureA F (c • f) g = c • GlobalTheory.WeilM.pureA F f g := by
      funext x; simp [GlobalTheory.WeilM.pureA, mul_assoc]
    rw [this, GlobalTheory.WeilM.thetaSum_smul]
    rfl
  · rw [hl' _ (hmem f)]
    rfl

end GlobalTheory.ThetaAdmitted
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedFormEqAdelicThetaDistributionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_admitted_form_eq_adelicThetaDistribution : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ l ∈ (GlobalTheory.WeilM.adeleClass F).adm κ, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, l Φ = GlobalTheory.WeilM.thetaSum F Φ := by
  first | exact @GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt | exact GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt | (intros; apply GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCColumnLatticeOfOrthonormalFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCColumnLatticeOfOrthonormalFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FunObj.OrthoFrame

theorem isSelfDualC_colLat_of_orthonormal : ∀ {D : D7} (S : HSp D) (B : GL (Fin S.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram * B.1 = 1 → IsSelfDualC S (colLat B) := by
  intro D S B hB
  exact GlobalTheory.FunObj.VecEx.isSelfDualC_colLat S B hB

end GlobalTheory.FunObj.OrthoFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCColumnLatticeOfOrthonormalFrameStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSelfDualC_columnLattice_of_orthonormalFrame : ∀ {D : D7} (S : HSp D) (B : GL (Fin S.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram * B.1 = 1 → IsSelfDualC S (colLat B) := by
  first | exact @GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal | exact GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal | (intros; apply GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairIntAt
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.DivisionValues (vw lw)

namespace GlobalTheory.SumSize

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Claims

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (C b : ℝ)

end Claims

theorem BigC.and {Q Q' : ChQ} (h : BigC Q) (h' : BigC Q') : BigC fun F ch C b => Q F ch C b ∧ Q' F ch C b := by
  obtain ⟨CF0, h⟩ := h
  obtain ⟨CF0', h'⟩ := h'
  refine ⟨max CF0 CF0', fun CF hCF => ?_⟩
  obtain ⟨C0, h⟩ := h CF ((le_max_left _ _).trans hCF)
  obtain ⟨C0', h'⟩ := h' CF ((le_max_right _ _).trans hCF)
  refine ⟨max C0 C0', fun ε C hC => ?_⟩
  obtain ⟨x0, h⟩ := h ε C ((le_max_left _ _).trans hC)
  obtain ⟨x0', h'⟩ := h' ε C ((le_max_right _ _).trans hC)
  refine ⟨max x0 x0', fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch h1 h2 h3 => ⟨?_, ?_⟩⟩
  · exact h D large₂ he ((le_max_left _ _).trans hx) Γ Pl0 T A Ks R F hS ch h1 h2 h3
  · exact h' D large₂ he ((le_max_right _ _).trans hx) Γ Pl0 T A Ks R F hS ch h1 h2 h3

end GlobalTheory.SumSize

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DownRight
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqStepBig

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Geo Chars)

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

def EmbCM (Bs : Base D.host.F D.host.E) : Prop := ∀ w, ∃ τ, ∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)

def OverH (c : D.host.E) (A : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) {n : ℕ}
    (V : Spc D.host.F D.host.E n) : Prop :=
  ∃ h : A.rank = n, V.J = c • Matrix.reindex (finCongr h) (finCongr h) A.gram ∧
    ∀ y, y ∈ V.L ↔ (fun i => star (y (finCongr h i))) ∈ Λ

def OverW (WW : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)) {d : ℕ} (Z : Spc D.host.F D.host.E d) : Prop :=
  ∃ h : WW.rank = d, Z.J = D.host.xi0 • Matrix.reindex (finCongr h) (finCongr h) WW.gram.transpose ∧
    ∀ y, y ∈ Z.L ↔ (fun i => y (finCongr h i)) ∈ GlobalTheory.SkewLat.scLat D.host.AA Λ

def Over {A A' WW : HSp D} (X : Tri T A A' WW) {a a' : ℕ} (Γ : Geo D.sp.cm.sig a a') : Prop :=
  OverH 1 A X.rA.Λ Γ.V ∧ OverH (-1) A' X.rA'.Λ Γ.V' ∧ OverW WW X.rW.Λ Γ.W

def Fit (G : GridData Lc sc) (W : G.Weil) (i j : Fin D.R.m) (t μ₀ : T) (Bs : Base D.host.F D.host.E) (a a' : ℕ) : Prop :=
  GlobalTheory.SqStep.BaseFits G W i j t Bs ∧ Bs.IsGood D.sp.cm.sig ∧ EmbCM Bs ∧ (GlobalTheory.SqStep.chs G i j t).IsGood Bs a a' ∧
    (GlobalTheory.SqStep.chs G i j μ₀).IsGood Bs a a' ∧ ∀ w, ((a + a' : ℕ) : ℤ) < Bs.mα w - Bs.mβ w

theorem OverH.eq {c : D.host.E} {A : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} {n : ℕ}
    {V V₂ : Spc D.host.F D.host.E n} (h : OverH c A Λ V) (h₂ : OverH c A Λ V₂) : V₂.J = V.J ∧ V₂.L = V.L := by
  obtain ⟨e, hJ, hL⟩ := h
  obtain ⟨e₂, hJ₂, hL₂⟩ := h₂
  exact ⟨hJ₂.trans hJ.symm, Submodule.ext fun y => (hL₂ y).trans (hL y).symm⟩

theorem OverW.eq {WW : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)} {d : ℕ}
    {Z Z₂ : Spc D.host.F D.host.E d} (h : OverW WW Λ Z) (h₂ : OverW WW Λ Z₂) : Z₂.J = Z.J ∧ Z₂.L = Z.L := by
  obtain ⟨e, hJ, hL⟩ := h
  obtain ⟨e₂, hJ₂, hL₂⟩ := h₂
  exact ⟨hJ₂.trans hJ.symm, Submodule.ext fun y => (hL₂ y).trans (hL y).symm⟩

theorem Fit.down_left {G : GridData Lc sc} {W : G.Weil} {i j : Fin D.R.m} {t μ₀ : T} {Bs : Base D.host.F D.host.E} {b a' : ℕ}
    (h : Fit G W i j t μ₀ Bs (b + 2) a') : Fit G W i j t μ₀ Bs b a' := by
  obtain ⟨h1, h2, h3, c, c₀, hk⟩ := h
  refine ⟨h1, h2, h3, ⟨c.heckeα, c.heckeβ, c.resα, fun x => ?_, c.expα, c.expβ, c.disj, c.sub, c.ram, c.unrα, c.unrβ, c.good⟩,
    ⟨c₀.heckeα, c₀.heckeβ, c₀.resα, fun x => ?_, c₀.expα, c₀.expβ, c₀.disj, c₀.sub, c₀.ram, c₀.unrα, c₀.unrβ, c₀.good⟩, fun w => ?_⟩
  · rw [c.resβ x]; simp [pow_add]
  · rw [c₀.resβ x]; simp [pow_add]
  · have := hk w
    push_cast at this ⊢
    omega

theorem Fit.down_right {G : GridData Lc sc} {W : G.Weil} {i j : Fin D.R.m} {t μ₀ : T} {Bs : Base D.host.F D.host.E} {a b : ℕ}
    (h : Fit G W i j t μ₀ Bs a (b + 2)) : Fit G W i j t μ₀ Bs a b := by
  obtain ⟨h1, h2, h3, c, c₀, hk⟩ := h
  refine ⟨h1, h2, h3, ⟨c.heckeα, c.heckeβ, fun x => ?_, c.resβ, c.expα, c.expβ, c.disj, c.sub, c.ram, c.unrα, c.unrβ, c.good⟩,
    ⟨c₀.heckeα, c₀.heckeβ, fun x => ?_, c₀.resβ, c₀.expα, c₀.expβ, c₀.disj, c₀.sub, c₀.ram, c₀.unrα, c₀.unrβ, c₀.good⟩, fun w => ?_⟩
  · rw [c.resα x]; simp [pow_add]
  · rw [c₀.resα x]; simp [pow_add]
  · have := hk w
    push_cast at this ⊢
    omega

end GlobalTheory.SqStepBig

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricLemmaFiltrationHolds
namespace GlobalTheory

theorem geometricLemmaFiltration_holds : GlobalTheory.Published.GeometricLemmaFiltration :=
  CompanionTheory.Geo.geometricLemmaFiltration

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicConstantTermParabolic
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open GlobalTheory.AutomorphicL2Unitary (LeftInv)
open GlobalTheory.Cusp (Cocompact constTermOn)
open scoped TensorProduct

namespace GlobalTheory.UAut.ConstAut

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem leftInv_foldr {Γ : Subgroup (GAd σ J)} {φ : GAd σ J → ℂ} (h : LeftInv Γ φ) :
    ∀ l : List (ℝ → GAd σ J), LeftInv Γ (l.foldr lineDer φ) := by
  intro l
  induction l with
  | nil => exact h
  | cons γ l ih =>
    intro x hx g
    simp only [List.foldr_cons, lineDer, mul_assoc, ih x hx]

theorem realLine_zero (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) : γ 0 = 1 := by
  have e := isRealLine_add F E σ h n J γ hγ 0 0
  rw [add_zero] at e
  exact mul_left_cancel (e.symm.trans (mul_one _).symm)

theorem hasDerivAt_foldr (h : IsCMExt F E σ) {φ : GAd σ J → ℂ} (hs : IsSm σ J φ) {l : List (ℝ → GAd σ J)}
    (hl : ∀ γ ∈ l, IsRealLine σ J γ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (g : GAd σ J) (t : ℝ) :
    HasDerivAt (fun s => l.foldr lineDer φ (g * γ s)) ((γ :: l).foldr lineDer φ (g * γ t)) t := by
  have hd := (GlobalTheory.ThK.RealLineGrowthDerivative.differentiableAt_foldr_lineDer hs l hl hγ (g * γ t)).hasDerivAt
  have e : ∀ s, g * γ t * γ (s - t) = g * γ s := fun s => by
    rw [mul_assoc, ← isRealLine_add F E σ h n J γ hγ, add_sub_cancel]
  have h2 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact hd)
  simp only [e] at h2
  exact h2

end GlobalTheory.UAut.ConstAut

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricLemmaFiltrationUnconditional
namespace GlobalTheory

theorem geometricLemmaFiltration_unconditional : GlobalTheory.Published.GeometricLemmaFiltration :=
  CompanionTheory.Geo.geometricLemmaFiltration

end GlobalTheory
end
