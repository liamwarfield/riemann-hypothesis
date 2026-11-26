module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelThetaSeriesModerateGrowth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AnisotropicTermsMeanZeroUnipotentRadical
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicTermMeanInvariantUnipotentRadical

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankFacGen
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal

noncomputable section
namespace GlobalTheory.TowerCT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem vol : ∀ (D : D7) (V : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C →
    ∀ (κ : Measure (NI V C)) (𝓝 : Set (NI V C)), κ.IsHaarMeasure → IsFundamentalDomain (NIQ V C) 𝓝 κ → κ 𝓝 ≠ ⊤ := by
  intro D V r C hC κ 𝓝 hκ h𝓝
  have hint : IntegrableOn (fun _ : NI V C => (1 : ℂ)) 𝓝 κ := by
    have key : ∀ N : Subgroup (GA D V),
        N = GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) (GlobalTheory.AutFunCompare.colSpan V C) →
        ∀ Q : Subgroup (GA D V), Q = GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.ratPts D.sp.cm V →
        ∀ (μ : Measure N) (𝓕 : Set N), μ.IsHaarMeasure → IsFundamentalDomain (Q.subgroupOf N) 𝓕 μ →
          IntegrableOn (fun _ : N => (1 : ℂ)) 𝓕 μ := by
      rintro N rfl Q rfl μ 𝓕 hμ h𝓕
      exact GlobalTheory.AutFunCompare.integrableOn_constTerm D.sp.cm V _ ((GlobalTheory.AutFunCompare.isIsoFrame_iff V C).1 hC).2
        (fun _ => 1) continuous_const (fun _ _ _ => rfl) μ hμ 𝓕 h𝓕 1
    exact key _ (GlobalTheory.AutFunCompare.NI_eq V C) _ (GlobalTheory.AutFunCompare.GQ_eq V) κ 𝓝 hκ h𝓝
  rcases (integrableOn_const_iff (C := (1 : ℂ))).1 hint with h | h
  · exact absurd h (by simp)
  · exact h.ne

theorem cusp : ∀ (D : D7) (W : HSp D) (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W L →
    ∀ (ν : Measure (GA D W)), ν.IsHaarMeasure → ∀ F : GA D W → ℂ, GlobalTheory.Grow.RapidDec W F → IsCuspFun W F →
    ∀ Γ : Subgroup (GA D W), Γ ≤ GQ W → (∀ γ ∈ Γ, ∀ n ∈ NI W L, γ * n * γ⁻¹ ∈ NI W L) →
    (∀ n ∈ NI W L, n ∈ GQ W → n ∈ Γ) → ∀ K : GA D W → ℂ, Measurable K → (∀ n ∈ NI W L, ∀ h, K (n * h) = K h) →
    (∀ γ ∈ Γ, ∀ h, K (γ * h) = K h) → ∀ 𝓖 : Set (GA D W), IsFundamentalDomain Γ 𝓖 ν →
    IntegrableOn (fun h => K h * F h) 𝓖 ν → ∫ h in 𝓖, K h * F h ∂ν = 0 := by
  intro D W s L hL ν hν F hF hcusp Γ hle hnorm hin K hKm hKn hKγ 𝓖 h𝓖 hint
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hcl := GlobalTheory.CuspDecay.Model.isClosed_NI W hL
  have : LocallyCompactSpace (NI W L) := hcl.locallyCompactSpace
  have hQ : Countable (GQ W) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig W.gram
  let i : NIQ W L → GQ W := fun x => ⟨x.1.1, x.2⟩
  have hi : Function.Injective i := fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : GQ W => z.1) h))
  have : DiscreteTopology (NIQ W L) := DiscreteTopology.of_continuous_injective (f := i)
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) hi
  have : Countable (NIQ W L) := hi.countable
  have : SecondCountableTopology (NI W L) := TopologicalSpace.Subtype.secondCountableTopology _
  let κ : Measure (NI W L) := Measure.haar
  obtain ⟨𝓝, h𝓝⟩ := GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain (NIQ W L) κ
  have hκ : κ.IsHaarMeasure := inferInstance
  have hΓ : Countable Γ := (Subgroup.inclusion_injective hle).countable
  have e : Γ.subgroupOf (NI W L) = NIQ W L := by
    ext n
    exact ⟨fun h => hle h, fun h => hin _ n.2 h⟩
  have h𝓝' : IsFundamentalDomain (Γ.subgroupOf (NI W L)) 𝓝 κ := by
    rw [e]
    exact h𝓝
  exact GlobalTheory.T.unfolding_zero_mean_normalized_subgroup (GA D W) ν Γ (NI W L) hΓ hcl hnorm κ 𝓝 hκ h𝓝' (vol D W s L hL κ 𝓝 hκ h𝓝) K F hKm
    hF.2.1.measurable hKn hKγ (fun γ hγ h => hF.1 γ (hle hγ) h) (fun h => hcusp s L hL κ 𝓝 hκ h𝓝 h) 𝓖 h𝓖 hint

theorem rankFacGen {K : Type} [Field K] {a b : ℕ} (y : Matrix (Fin a) (Fin b) K) (hy : y ≠ 0) :
    ∃ (s : ℕ) (L : Matrix (Fin a) (Fin s) K) (m : Matrix (Fin s) (Fin b) K) (m' : Matrix (Fin b) (Fin s) K),
      0 < s ∧ LinearIndependent K L.transpose ∧ m.rank = s ∧ m * m' = 1 ∧ y = L * m := by
  classical
  let U : Submodule K (Fin a → K) := Submodule.span K (Set.range y.transpose)
  let s := Module.finrank K U
  let bs : Module.Basis (Fin s) K U := Module.finBasisOfFinrankEq K U rfl
  have hcol : ∀ j, y.transpose j ∈ U := fun j => Submodule.subset_span ⟨j, rfl⟩
  let L : Matrix (Fin a) (Fin s) K := Matrix.of fun i k => (bs k : Fin a → K) i
  let m : Matrix (Fin s) (Fin b) K := Matrix.of fun k j => bs.repr ⟨y.transpose j, hcol j⟩ k
  have hym : y = L * m := by
    ext i j
    have h := bs.sum_repr ⟨y.transpose j, hcol j⟩
    have h2 := congrArg (fun u : U => (u : Fin a → K) i) h
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
    simp only [Matrix.mul_apply, L, m, Matrix.of_apply]
    rw [show y i j = y.transpose j i from rfl, ← h2]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hLi : LinearIndependent K L.transpose := by
    have : LinearIndependent K fun k => (bs k : Fin a → K) := bs.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
    exact this
  have hrk : y.rank = s := by
    rw [Matrix.rank_eq_finrank_span_cols]
    rfl
  have hs : 0 < s := by
    refine Nat.pos_of_ne_zero fun h => hy ?_
    have hU : U = ⊥ := Submodule.finrank_eq_zero.1 h
    ext i j
    have := hcol j
    rw [hU, Submodule.mem_bot] at this
    exact congrFun this i
  have hle : s ≤ m.rank := by
    calc s = y.rank := hrk.symm
      _ = (L * m).rank := by rw [← hym]
      _ ≤ m.rank := Matrix.rank_mul_le_right _ _
  have hm : m.rank = s := le_antisymm ((Matrix.rank_le_height m)) hle
  have hsurj : Function.Surjective m.mulVecLin := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    have : Module.finrank K (LinearMap.range m.mulVecLin) = s := hm
    simpa using this
  obtain ⟨g, hg⟩ := m.mulVecLin.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hsurj)
  refine ⟨s, L, m, LinearMap.toMatrix' g, hs, hLi, hm, ?_, hym⟩
  have : Matrix.toLin' (m * LinearMap.toMatrix' g) = LinearMap.id := by
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
    exact hg
  apply Matrix.toLin'.injective
  rw [this, Matrix.toLin'_one]

theorem rankFac : ∀ (D : D7) (W : HSp D) (r : ℕ) (y : Matrix (Fin W.rank) (Fin r) D.host.E), y ≠ 0 →
    adj D y * W.gram * y = 0 → ∃ (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E) (m : Matrix (Fin s) (Fin r) D.host.E)
      (m' : Matrix (Fin r) (Fin s) D.host.E), IsIsoFrame W L ∧ m.rank = s ∧ m * m' = 1 ∧ y = L * m := by
  intro D W r y hy hiso
  obtain ⟨s, L, m, m', hs, hL, hm, hmm, e⟩ := rankFacGen y hy
  refine ⟨s, L, m, m', ⟨hs, hL, ?_⟩, hm, hmm, e⟩
  have hLy : L = y * m' := by rw [e, Matrix.mul_assoc, hmm, Matrix.mul_one]
  have hc : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) L = adj D m' * adj D y := by
    rw [hLy]
    simp only [adj, Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  rw [hc]
  calc adj D m' * adj D y * W.gram * L = adj D m' * (adj D y * W.gram * y) * m' := by
        rw [hLy]
        simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hiso, Matrix.mul_zero, Matrix.zero_mul]

theorem fub {N H Y : Type} [MeasurableSpace N] [MeasurableSpace H] [Countable Y]
    (κ : Measure N) (ν : Measure H) [SFinite κ] [SFinite ν] (𝓝 : Set N) (𝓕 : Set H)
    (T : Y → N → H → ℂ) (hT : ∀ y, Measurable (Function.uncurry (T y))) (Θ : N → H → ℂ)
    (F : H → ℂ) (hF : Measurable F) (hs : ∀ n h, HasSum (fun y => T y n h) (Θ n h))
    (hb : ∫⁻ n in 𝓝, ∫⁻ h in 𝓕, (∑' y, ‖T y n h‖ₑ) * ‖F h‖ₑ ∂ν ∂κ ≠ ⊤) :
    IntegrableOn (fun n => ∫ h in 𝓕, Θ n h * F h ∂ν) 𝓝 κ ∧
    (∑' y, ∫⁻ h in 𝓕, ‖(∫ n in 𝓝, T y n h ∂κ) * F h‖ₑ ∂ν) ≠ ⊤ ∧
    HasSum (fun y => ∫ h in 𝓕, (∫ n in 𝓝, T y n h ∂κ) * F h ∂ν)
      (∫ n in 𝓝, ∫ h in 𝓕, Θ n h * F h ∂ν ∂κ) := by
  set P := (κ.restrict 𝓝).prod (ν.restrict 𝓕) with hP
  let G : Y → N × H → ℂ := fun y p => T y p.1 p.2 * F p.2
  have hGm : ∀ y, Measurable (G y) := fun y => (hT y).mul (hF.comp measurable_snd)
  have hGe : ∀ y, Measurable fun p => ‖G y p‖ₑ := fun y => (hGm y).enorm
  have hlin : ∫⁻ p, ∑' y, ‖G y p‖ₑ ∂P ≠ ⊤ := by
    rw [hP, lintegral_prod _ (Measurable.tsum hGe).aemeasurable]
    convert hb using 6 with n _ h
    simp only [G, enorm_mul]
    rw [ENNReal.tsum_mul_right]
  have hsum : ∑' y, ∫⁻ p, ‖G y p‖ₑ ∂P ≠ ⊤ := by
    rwa [← lintegral_tsum fun y => (hGe y).aemeasurable]
  have hfin : ∀ y, ∫⁻ p, ‖G y p‖ₑ ∂P ≠ ⊤ := fun y => ENNReal.ne_top_of_tsum_ne_top hsum y
  have hGi : ∀ y, Integrable (G y) P := fun y =>
    ⟨(hGm y).aestronglyMeasurable, lt_top_iff_ne_top.2 (hfin y)⟩
  have hsp : ∀ p : N × H, HasSum (fun y => G y p) (Θ p.1 p.2 * F p.2) := fun p => (hs p.1 p.2).mul_right _
  have hΘm : Measurable fun p : N × H => Θ p.1 p.2 * F p.2 :=
    measurable_of_tendsto_metrizable' Filter.atTop (f := fun (s : Finset Y) p => ∑ y ∈ s, G y p)
      (fun s => Finset.measurable_sum _ fun y _ => hGm y) (tendsto_pi_nhds.2 hsp)
  have hle : ∀ p : N × H, ‖Θ p.1 p.2 * F p.2‖ₑ ≤ ∑' y, ‖G y p‖ₑ := fun p =>
    le_of_tendsto' ((continuous_enorm.tendsto _).comp (hsp p)) fun s =>
      (enorm_sum_le s _).trans (ENNReal.sum_le_tsum s)
  have hΘi : Integrable (fun p : N × H => Θ p.1 p.2 * F p.2) P :=
    ⟨hΘm.aestronglyMeasurable, ((lintegral_mono hle).trans_lt (lt_top_iff_ne_top.2 hlin))⟩
  have hnorm : Summable fun y => ∫ p, ‖G y p‖ ∂P := by
    have e : ∀ y, ∫ p, ‖G y p‖ ∂P = (∫⁻ p, ‖G y p‖ₑ ∂P).toReal := fun y => by
      rw [integral_norm_eq_lintegral_enorm (hGm y).aestronglyMeasurable]
    simp only [e]
    exact ENNReal.summable_toReal hsum
  have hS := hasSum_integral_of_summable_integral_norm hGi hnorm
  have eT : (fun p => ∑' y, G y p) = fun p : N × H => Θ p.1 p.2 * F p.2 := funext fun p => (hsp p).tsum_eq
  rw [eT, hP, integral_prod _ (by rw [← hP]; exact hΘi)] at hS
  refine ⟨hΘi.integral_prod_left, ?_, ?_⟩
  · refine ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum fun y => ?_)
    rw [hP, lintegral_prod_symm _ (hGe y).aemeasurable]
    refine lintegral_mono fun h => ?_
    simp only [G, enorm_mul]
    rw [lintegral_mul_const _ ((hT y).of_uncurry_right.enorm)]
    exact mul_le_mul' (enorm_integral_le_lintegral_enorm _) le_rfl
  · have e : (fun y => ∫ h in 𝓕, (∫ n in 𝓝, T y n h ∂κ) * F h ∂ν) =
        fun y => ∫ p, G y p ∂(κ.restrict 𝓝).prod (ν.restrict 𝓕) := funext fun y => by
      rw [integral_prod_symm _ (by rw [← hP]; exact hGi y)]
      refine integral_congr_ae (.of_forall fun h => ?_)
      simp only [G]
      rw [integral_mul_const]
    rw [e]
    exact hS

end GlobalTheory.TowerCT

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftConstantTermCompatibleWeil
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermsRationalUnipotentInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermsRationalUnipotentInvariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.UnipMixed

variable {D : D7}

theorem mt_mul_frame (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (g : GA D V) (hg : g ∈ NI V C) :
    mt V g * C.map (incA D) = C.map (incA D) := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨h, -, -⟩ := hg
    have h' : (mt V g - 1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) * (C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) = 0 := h
    rwa [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h'
  | one => rw [GlobalTheory.AdelicLatMove.mt_one, Matrix.one_mul]
  | mul g h _ _ hg hh => rw [GlobalTheory.AdelicLatMove.mt_mul, Matrix.mul_assoc, hh, hg]
  | inv g _ hg =>
    conv_lhs => rw [← hg]
    rw [← Matrix.mul_assoc, ← GlobalTheory.AdelicLatMove.mt_mul, inv_mul_cancel, GlobalTheory.AdelicLatMove.mt_one, Matrix.one_mul]

theorem hO_eq_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace (S.gram⁻¹.map (incA D) * (y.map (cA D))ᵀ * T.gram.map (incA D) * x) := by
  simp only [hO, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans ?_
  exact Finset.sum_comm

theorem symplOH_isoPart_eq_zero (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (t : Mx D W.rank r)
    (δ : WO V W) (hδ : δ * C.map (incA D) = 0) : symplOH V W (isoPart V W C t) δ = 0 := by
  have hh : hO V W (isoPart V W C t) δ = 0 := by
    rw [hO_eq_trace]
    have hP : (adj D C * V.gram).map (incA D) = ((C.map (incA D)).map (cA D))ᵀ * V.gram.map (incA D) := by
      rw [Matrix.map_mul]; rfl
    have hC : ((C.map (incA D)).map (cA D))ᵀ * (δ.map (cA D))ᵀ = 0 := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, hδ, Matrix.map_zero _ (map_zero _), Matrix.transpose_zero]
    simp only [isoPart]
    rw [hP, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Matrix.mul_assoc _ (V.gram.map (incA D)), GlobalTheory.SplitOnto.gram_mul_inv, Matrix.mul_one, hC,
      Matrix.zero_mul, Matrix.zero_mul, Matrix.trace_zero]
  simp only [symplOH, symplO, hh, mul_zero, map_zero]

theorem heisO_add_rat (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsStdChar D ψ (-1)) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (x δ : Matrix (Fin W.rank) (Fin V.rank) D.host.E) (hδ : δ.map (incA D) * C.map (incA D) = 0) (t : Mx D W.rank r) :
    heisO ψ V W (x.map (incA D) + δ.map (incA D)) f (isoPart V W C t) =
      heisO ψ V W (x.map (incA D)) f (isoPart V W C t) := by
  have o := symplOH_isoPart_eq_zero V W C t _ hδ
  have ha := GlobalTheory.OrientedFormLaws.symplOH_rat (S := V) (T := W) δ x
  generalize (1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * GlobalTheory.LatVac.hRat V W δ x)) = a at ha
  have q := hf.quasi δ (isoPart V W C t + x.map (incA D))
  have e : isoPart V W C t + (x.map (incA D) + δ.map (incA D)) = ratW W V δ + (isoPart V W C t + x.map (incA D)) := by
    simp only [ratW]; abel
  have s1 : symplOH V W (ratW W V δ) (isoPart V W C t + x.map (incA D)) = algebraMap D.host.F (AF D.host.F) a := by
    rw [GlobalTheory.FinTranslate.symplOH_add_right, GlobalTheory.FinTranslate.symplOH_skew, ratW, o, neg_zero, zero_add, ha]
  have s2 : ψ (-(algebraMap D.host.F (AF D.host.F) a)) = 1 := by
    rw [← map_neg]; exact hψ.1.2.2.1 (-a)
  simp only [heisO]
  rw [e, q, s1, s2, GlobalTheory.FinTranslate.symplOH_add_right, o, add_zero, one_mul]

theorem res_heisO_unip : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ n ∈ NI V C, n ∈ GQ V → ∀ (y : Matrix (Fin W.rank) (Fin r) D.host.E) f, IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) (ω (n, 1) f)) 0 = res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) f) 0 := by
  intro D V V' W r C C' B hs _ _ _ ψ χS χT ω hω μ 𝓨 hcov n hnN hnQ y f hf
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E, mt V n = n₀.map (incA D) := by
    obtain ⟨γ', -, e⟩ := hnQ
    exact ⟨γ'.1, (congrArg Units.val e).symm⟩
  set X₀ : Matrix (Fin W.rank) (Fin V.rank) D.host.E := y * (adj D C' * V.gram) with hX₀
  have hx : isoPart V W C' (y.map (incA D)) = X₀.map (incA D) := by
    simp only [isoPart, hX₀, Matrix.map_mul]
  set δ : Matrix (Fin W.rank) (Fin V.rank) D.host.E := X₀ * (n₀ - 1) with hδdef
  have hδ : δ.map (incA D) * C.map (incA D) = 0 := by
    rw [hδdef, Matrix.map_mul, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), ← hn₀, Matrix.mul_assoc,
      Matrix.sub_mul, Matrix.one_mul, mt_mul_frame V C n hnN, sub_self, Matrix.mul_zero]
  have hx' : actO V W n⁻¹ 1 (X₀.map (incA D)) = X₀.map (incA D) + δ.map (incA D) := by
    simp only [actO, inv_inv, GlobalTheory.AdelicLatMove.mt_one, Matrix.one_mul, hn₀, hδdef]
    rw [← Matrix.map_mul, Matrix.mul_sub, Matrix.mul_one, ← Matrix.map_add _ (map_add _), add_sub_cancel]
  have hA : heisO ψ V W (X₀.map (incA D)) (ω (n, 1) f) =
      ω (n, 1) (heisO ψ V W (actO V W n⁻¹ 1 (X₀.map (incA D))) f) := by
    rw [hω.om_heis n 1 _ f hf]
    congr 1
    have := GlobalTheory.AdelicLatMove.actO_actO_inv V W n 1 (X₀.map (incA D))
    rw [inv_one] at this
    exact this.symm
  have hK := GlobalTheory.T.wittTower_restriction_unipotentRadical_invariant D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hcov ⟨n, hnN⟩ _
    (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hω.std hf (actO V W n⁻¹ 1 (X₀.map (incA D))))
  rw [hx, hA, show res V V' W C B μ 𝓨 (ω (n, 1) (heisO ψ V W (actO V W n⁻¹ 1 (X₀.map (incA D))) f)) =
    res V V' W C B μ 𝓨 (heisO ψ V W (actO V W n⁻¹ 1 (X₀.map (incA D))) f) from hK, hx']
  have hm : midPart V V' W B 0 = 0 := by simp [midPart]
  simp only [res, hm, add_zero]
  congr 1
  funext t
  exact heisO_add_rat V W C hω.std hf X₀ δ hδ t

end GlobalTheory.UnipMixed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermsRationalUnipotentInvariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModelTerms_rationalUnipotent_invariant : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ n ∈ NI V C, n ∈ GQ V → ∀ (y : Matrix (Fin W.rank) (Fin r) D.host.E) f, IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) (ω (n, 1) f)) 0 = res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) f) 0 := by
  first | exact @GlobalTheory.UnipMixed.res_heisO_unip | exact GlobalTheory.UnipMixed.res_heisO_unip | (intros; apply GlobalTheory.UnipMixed.res_heisO_unip <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralThetaLiftTermSumNeTop
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralThetaLiftTermSumNeTop
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal

noncomputable section

namespace GlobalTheory.ThetaLiftBound

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_rat_height_le {D : D7} (W : HSp D) (h : GA D W) :
    ∃ γ ∈ GQ W, GlobalTheory.Grow.height W (γ * h) ≤ 2 * GlobalTheory.Grow.quotHeight W h := by
  have hq := GlobalTheory.Grow.one_le_quotHeight W h
  by_contra hne
  push_neg at hne
  have : 2 * GlobalTheory.Grow.quotHeight W h ≤ GlobalTheory.Grow.quotHeight W h :=
    (GlobalTheory.Grow.le_quotHeight_iff W).2 fun γ hγ => (hne γ hγ).le
  linarith

theorem bound_pow (c a b M q : ℝ) (A : ℕ) (ha : 1 ≤ a) (haM : a ≤ M) (hb : 1 ≤ b) (hbq : b ≤ 2 * q) :
    c * (a * b) ^ A ≤ max c 0 * (M * (2 * q)) ^ A := by
  have hX : a * b ≤ M * (2 * q) := mul_le_mul haM hbq (by linarith) (by linarith)
  have hXp : (a * b) ^ A ≤ (M * (2 * q)) ^ A := pow_le_pow_left₀ (mul_nonneg (by linarith) (by linarith)) hX A
  exact (mul_le_mul_of_nonneg_right (le_max_left c 0) (pow_nonneg (mul_nonneg (by linarith) (by linarith)) A)).trans
    (mul_le_mul_of_nonneg_left hXp (le_max_right c 0))

theorem bound_mul (c M q f C' : ℝ) (A : ℕ) (hM : 0 ≤ M) (hq : 0 ≤ q) (hf : 0 ≤ f) (hF : f * q ^ A ≤ C') :
    max c 0 * (M * (2 * q)) ^ A * f ≤ max c 0 * (2 * M) ^ A * max C' 0 := by
  have e : max c 0 * (M * (2 * q)) ^ A * f = max c 0 * (2 * M) ^ A * (f * q ^ A) := by
    rw [mul_pow, mul_pow, mul_pow]; ring
  rw [e]
  exact mul_le_mul_of_nonneg_left (hF.trans (le_max_left _ _))
    (mul_nonneg (le_max_right c 0) (pow_nonneg (by linarith) A))

theorem lintegral_ne_top : ∀ (D : D7) (V W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C → ∀ (κ : Measure (NI V C)) (𝓝 : Set (NI V C)), κ.IsHaarMeasure → IsFundamentalDomain (NIQ V C) 𝓝 κ → ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν → ∀ F : GA D W → ℂ, GlobalTheory.Grow.RapidDec W F → ∀ (Sg : GA D V × GA D W → ℝ≥0∞), (∀ n ∈ NI V C, n ∈ GQ V → ∀ a b, Sg (n * a, b) = Sg (a, b)) → (∀ γ ∈ GQ W, ∀ a b, Sg (a, γ * b) = Sg (a, b)) → ∀ (A : ℕ) (c : ℝ), (∀ a b, Sg (a, b) ≤ ENNReal.ofReal (c * (GlobalTheory.Grow.height V a * GlobalTheory.Grow.height W b) ^ A)) → ∀ g : GA D V, ∫⁻ n in 𝓝, ∫⁻ h in 𝓕, Sg ((n : GA D V) * g, h) * ‖F h‖ₑ ∂ν ∂κ ≠ ⊤ := by
  intro D V W r C hC κ 𝓝 hκ h𝓝 ν 𝓕 hν h𝓕 F hF Sg h1 h2 A c hc g
  obtain ⟨K, hK, hcov⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D V r C ⟨hC.2.1, hC.2.2⟩).2
  obtain ⟨M, hM⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact V
    (hK.image (f := fun k : NI V C => (k : GA D V) * g) (by fun_prop))
  obtain ⟨C', hC'⟩ := hF.2.2 A
  have hbound : ∀ n : NI V C, ∀ h, Sg ((n : GA D V) * g, h) * ‖F h‖ₑ ≤
      ENNReal.ofReal (max c 0 * (2 * M) ^ A * max C' 0) := by
    intro n h
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov n
    obtain ⟨γ', hγ', hh⟩ := exists_rat_height_le W h
    have e1 : Sg (((γ * k : NI V C) : GA D V) * g, h) = Sg ((k : GA D V) * g, γ' * h) := by
      rw [Subgroup.coe_mul, mul_assoc, h1 _ γ.2 (Subgroup.mem_subgroupOf.1 hγ), h2 _ hγ']
    rw [e1]
    have hkM : GlobalTheory.Grow.height V ((k : GA D V) * g) ≤ M := hM _ ⟨k, hk, rfl⟩
    have hV1 := GlobalTheory.Grow.one_le_height V ((k : GA D V) * g)
    have hW1 := GlobalTheory.Grow.one_le_height W (γ' * h)
    have hq1 := GlobalTheory.Grow.one_le_quotHeight W h
    have hc1 := bound_pow c _ _ M (GlobalTheory.Grow.quotHeight W h) A hV1 hkM hW1 hh
    have hb := bound_mul c M (GlobalTheory.Grow.quotHeight W h) ‖F h‖ C' A (by linarith) (by linarith) (norm_nonneg _) (hC' h)
    calc Sg ((k : GA D V) * g, γ' * h) * ‖F h‖ₑ
        ≤ ENNReal.ofReal (max c 0 * (M * (2 * GlobalTheory.Grow.quotHeight W h)) ^ A) * ENNReal.ofReal ‖F h‖ := by
          rw [ofReal_norm_eq_enorm]
          exact mul_le_mul' ((hc _ _).trans (ENNReal.ofReal_le_ofReal hc1)) le_rfl
      _ = ENNReal.ofReal (max c 0 * (M * (2 * GlobalTheory.Grow.quotHeight W h)) ^ A * ‖F h‖) :=
          (ENNReal.ofReal_mul (mul_nonneg (le_max_right c 0)
            (pow_nonneg (mul_nonneg (by linarith) (by linarith)) A))).symm
      _ ≤ ENNReal.ofReal (max c 0 * (2 * M) ^ A * max C' 0) := ENNReal.ofReal_le_ofReal hb
  have hν𝓕 := (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol W ν 𝓕 hν h𝓕).ne
  have hκ𝓝 := GlobalTheory.TowerCT.vol D V r C hC κ 𝓝 hκ h𝓝
  refine ne_top_of_le_ne_top ?_ (lintegral_mono fun n => lintegral_mono fun h => hbound n h)
  rw [setLIntegral_const, setLIntegral_const]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hν𝓕) hκ𝓝

end GlobalTheory.ThetaLiftBound

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralThetaLiftTermSumNeTopStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_thetaLift_termSum_ne_top : ∀ (D : D7) (V W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C → ∀ (κ : Measure (NI V C)) (𝓝 : Set (NI V C)), κ.IsHaarMeasure → IsFundamentalDomain (NIQ V C) 𝓝 κ → ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν → ∀ F : GA D W → ℂ, GlobalTheory.Grow.RapidDec W F → ∀ (Sg : GA D V × GA D W → ℝ≥0∞), (∀ n ∈ NI V C, n ∈ GQ V → ∀ a b, Sg (n * a, b) = Sg (a, b)) → (∀ γ ∈ GQ W, ∀ a b, Sg (a, γ * b) = Sg (a, b)) → ∀ (A : ℕ) (c : ℝ), (∀ a b, Sg (a, b) ≤ ENNReal.ofReal (c * (GlobalTheory.Grow.height V a * GlobalTheory.Grow.height W b) ^ A)) → ∀ g : GA D V, ∫⁻ n in 𝓝, ∫⁻ h in 𝓕, Sg ((n : GA D V) * g, h) * ‖F h‖ₑ ∂ν ∂κ ≠ ⊤ := by
  first | exact @GlobalTheory.ThetaLiftBound.lintegral_ne_top | exact GlobalTheory.ThetaLiftBound.lintegral_ne_top | (intros; apply GlobalTheory.ThetaLiftBound.lintegral_ne_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftConstantTermCompatibleWeil
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TowerCT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ratM_ex (D : D7) (W : HSp D) (γ : GA D W) (h : γ ∈ GQ W) :
    ∃ m : Matrix (Fin W.rank) (Fin W.rank) D.host.E, Formalism.L2.Theta.mt W γ = m.map (incA D) := by
  obtain ⟨u, -, hu⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp h)
  refine ⟨(u : Matrix (Fin W.rank) (Fin W.rank) D.host.E), ?_⟩
  have hu' := congrArg (fun x : GL (Fin W.rank) (TensorProduct D.host.F (AF D.host.F) D.host.E) =>
    (x : Matrix (Fin W.rank) (Fin W.rank) (TensorProduct D.host.F (AF D.host.F) D.host.E))) hu
  exact hu'.symm

variable {D : D7}

def ratM (W : HSp D) (γ : GQ W) : Matrix (Fin W.rank) (Fin W.rank) D.host.E := Classical.choose (ratM_ex D W γ.1 γ.2)

theorem ratM_spec (W : HSp D) (γ : GQ W) : Formalism.L2.Theta.mt W γ.1 = (ratM W γ).map (incA D) := by
  unfold ratM
  exact (ratM_ex D W γ.1 γ.2).choose_spec

theorem map_incA_injective (W : HSp D) :
    Function.Injective fun m : Matrix (Fin W.rank) (Fin W.rank) D.host.E => m.map (incA D) := by
  have : Nontrivial (AF D.host.F) := by
    obtain ⟨v⟩ : Nonempty (NumberField.InfinitePlace D.host.F) := inferInstance
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h2 : ((0 : AF D.host.F).1 v) = ((1 : AF D.host.F).1 v) := congrArg (fun x : AF D.host.F => x.1 v) h
    exact zero_ne_one h2
  intro a b hab
  ext i j
  have hij : (a.map (incA D)) i j = (b.map (incA D)) i j := by
    rw [show a.map (incA D) = b.map (incA D) from hab]
  simp only [Matrix.map_apply] at hij
  exact Algebra.TensorProduct.includeRight_injective (algebraMap D.host.F (AF D.host.F)).injective hij

theorem ratM_mul (W : HSp D) (a b : GQ W) : ratM W (a * b) = ratM W a * ratM W b := by
  apply map_incA_injective W
  show (ratM W (a * b)).map (incA D) = (ratM W a * ratM W b).map (incA D)
  rw [Matrix.map_mul, ← ratM_spec, ← ratM_spec, ← ratM_spec]
  exact congrArg Units.val (map_mul (matHom W) a.1 b.1)

theorem ratM_one (W : HSp D) : ratM W (1 : GQ W) = 1 := by
  apply map_incA_injective W
  show (ratM W 1).map (incA D) = (1 : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D)
  rw [← ratM_spec, Matrix.map_one _ (map_zero _) (map_one _)]
  exact congrArg Units.val (map_one (matHom W))

private theorem heisO_zero_twisted_operators {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (u : WO V W → ℂ) :
    heisO ψ V W 0 u = u := by
  funext w
  unfold heisO
  simp only [symplOH]
  unfold symplO hO
  simp

def ratAct (W : HSp D) (r : ℕ) : MulAction (GQ W) {y : Matrix (Fin W.rank) (Fin r) D.host.E // y ≠ 0} where
  smul γ y := ⟨ratM W γ * y.1, fun h => y.2 (by
    have := congrArg (ratM W γ⁻¹ * ·) h
    simpa [← Matrix.mul_assoc, ← ratM_mul, ratM_one] using this)⟩
  one_smul y := Subtype.ext (by
    change ratM W 1 * y.1 = y.1
    rw [ratM_one, Matrix.one_mul])
  mul_smul a b y := Subtype.ext (by
    change ratM W (a * b) * y.1 = ratM W a * (ratM W b * y.1)
    rw [ratM_mul, Matrix.mul_assoc])

end GlobalTheory.TowerCT

open GlobalTheory.TowerCT

theorem GlobalTheory.TowerCT.towerConstTermOfCompatible_holds : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.TowerConstTermOfCompatible D := by
  intro D V V' W r C B hS ψ χS χT χS' χT' ω ω' hω hω' hc μ 𝓨 hY ν 𝓕 hν h𝓕 κ 𝓝 hκ h𝓝 F hFd hFc f hf g
  obtain ⟨hVlc, hVsc, hVt2, hVb, hVtg, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨hWlc, hWsc, hWt2, hWb, hWtg, -, hWcount⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hMc : ∀ a b : ℕ, Countable (Matrix (Fin a) (Fin b) D.host.E) := fun a b =>
    inferInstanceAs (Countable (Fin a → Fin b → D.host.E))
  obtain ⟨C', h1, h2, h3⟩ := GlobalTheory.T.exists_isotropicDualFrame_of_splitEmbedding D V V' r C B hS
  have hstd : IsStdChar D ψ (-1) := hω.std
  obtain ⟨θ, hθ⟩ := (GlobalTheory.Ker.exists_infFam_and_stdChar D).1
  have hG := GlobalTheory.KernelSeminorm.thetaGrowth_onObjects D

  have hωm : ∀ (p q : GA D V × GA D W) (u : WO V W → ℂ), ω (p * q) u = ω p (ω q u) := by
    intro p q u
    rw [map_mul]
    rfl
  have hL : ∀ (k a : GA D V) (b : GA D W) (u : WO V W → ℂ), ω (k * a, b) u = ω (k, 1) (ω (a, b) u) := by
    intro k a b u
    rw [← hωm, Prod.mk_mul_mk, one_mul]
  have hR : ∀ (a : GA D V) (k b : GA D W) (u : WO V W → ℂ), ω (a, k * b) u = ω (1, k) (ω (a, b) u) := by
    intro a k b u
    rw [← hωm, Prod.mk_mul_mk, one_mul]
  have hLR : ∀ (k a : GA D V) (k' b : GA D W) (u : WO V W → ℂ), ω (k * a, k' * b) u = ω (k, k') (ω (a, b) u) := by
    intro k a k' b u
    rw [← hωm]
    rfl
  have hf₁ : IsThetaFunO ψ V W (ω (g, 1) f) := hω.om_pres _ f hf
  have hfp : ∀ p : GA D V × GA D W, IsThetaFunO ψ V W (ω p f) := fun p => hω.om_pres p f hf
  obtain ⟨hI1, hI2, -, -⟩ := (GlobalTheory.T.thetaRestrictIsotropicQuotient_wittTower_properties D V V' W r C B hS ψ hstd μ 𝓨 hY).1 _ hf₁
  have hvol : κ 𝓝 ≠ ⊤ := vol D V r C hS.frame κ 𝓝 hκ h𝓝
  have : IsFiniteMeasure (κ.restrict 𝓝) := isFiniteMeasure_restrict.mpr hvol

  obtain ⟨tm, htm⟩ : ∃ tm : Matrix (Fin W.rank) (Fin r) D.host.E → (WO V W → ℂ) → ℂ, ∀ y u,
      tm y u = res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) u) 0 :=
    ⟨fun y u => res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) u) 0, fun _ _ => rfl⟩
  have hsum : ∀ u, IsThetaFunO ψ V W u → HasSum (fun y => tm y u) (u 0) := by
    intro u hu
    simp only [htm]
    exact (GlobalTheory.T.theta_series_summable_on_covolume_domain D V V' W r C C' B hS h1 h2 h3 ψ hstd μ 𝓨 hY u hu).2
  have hrat : ∀ n ∈ NI V C, n ∈ GQ V → ∀ y u, IsThetaFunO ψ V W u → tm y (ω (n, 1) u) = tm y u := by
    intro n hn hnq y u hu
    rw [htm, htm]
    exact GlobalTheory.T.mixedModelTerms_rationalUnipotent_invariant D V V' W r C C' B hS h1 h2 h3 ψ χS χT ω hω μ 𝓨 hY n hn hnq y u hu
  have heqv : ∀ (γ : GA D W) (γ₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E), γ ∈ GQ W →
      Formalism.L2.Theta.mt W γ = γ₀.map (incA D) → ∀ y u, IsThetaFunO ψ V W u → tm (γ₀ * y) (ω (1, γ) u) = tm y u := by
    intro γ γ₀ hγ hγ₀ y u hu
    rw [htm, htm]
    exact GlobalTheory.T.restrictedHeisenbergTerms_permuted_rationalUnitary D V V' W r C C' B hS h1 h2 h3 ψ χS χT ω hω μ 𝓨 hY γ γ₀ hγ hγ₀ y u hu
  have hnon : ∀ y : Matrix (Fin W.rank) (Fin r) D.host.E, adj D y * W.gram * y ≠ 0 → ∀ u, IsThetaFunO ψ V W u →
      ∫ n in 𝓝, tm y (ω ((n : GA D V), 1) u) ∂κ = 0 := by
    intro y hy u hu
    simp only [htm]
    exact GlobalTheory.T.anisotropicTerms_mean_zero_unipotentRadical D V V' W r C C' B hS h1 h2 h3 ψ χS χT ω hω μ 𝓨 hY κ 𝓝 hκ h𝓝 y hy u hu
  have hcuspN : ∀ (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E) (m : Matrix (Fin s) (Fin r) D.host.E),
      IsIsoFrame W L → m.rank = s → ∀ (n' : NI W L) u, IsThetaFunO ψ V W u →
      ∫ n in 𝓝, tm (L * m) (ω ((n : GA D V), (n' : GA D W)) u) ∂κ = ∫ n in 𝓝, tm (L * m) (ω ((n : GA D V), 1) u) ∂κ := by
    intro s L m hL hm n' u hu
    simp only [htm]
    exact GlobalTheory.T.isotropicTermMean_invariant_unipotentRadical D V V' W r C C' B hS h1 h2 h3 ψ χS χT ω hω μ 𝓨 hY κ 𝓝 hκ h𝓝 s L m hL hm n' u hu
  obtain ⟨A, hA⟩ := GlobalTheory.T.mixedModel_thetaSeries_moderate_growth D V V' W r C C' B hS h1 h2 h3 ψ χS χT ω hω μ 𝓨 hY
  obtain ⟨c, hcb⟩ := hA f hf
  have hcont : ∀ y, Continuous fun p : GA D V × GA D W => tm y (ω p f) := by
    intro y
    simp only [htm]
    exact (hcb 1 1).1 y
  have hTm : ∀ y, Measurable (Function.uncurry fun (n : NI V C) (h : GA D W) => tm y (ω ((n : GA D V) * g, h) f)) := by
    intro y
    exact ((hcont y).comp (by fun_prop : Continuous fun q : NI V C × GA D W => ((q.1 : GA D V) * g, q.2))).measurable
  have hKm : ∀ y, Measurable fun h : GA D W => ∫ n in 𝓝, tm y (ω ((n : GA D V) * g, h) f) ∂κ := by
    intro y
    exact (StronglyMeasurable.integral_prod_left (μ := κ.restrict 𝓝) (hTm y).stronglyMeasurable).measurable

  have hb0 := GlobalTheory.T.lintegral_thetaLift_termSum_ne_top D V W r C hS.frame κ 𝓝 hκ h𝓝 ν 𝓕 hν h𝓕 F hFd
    (fun p => ∑' y, ‖tm y (ω p f)‖ₑ)
    (by
      intro n hn hnq a b
      refine tsum_congr fun y => ?_
      show ‖tm y (ω (n * a, b) f)‖ₑ = ‖tm y (ω (a, b) f)‖ₑ
      rw [hL, hrat n hn hnq y _ (hfp _)])
    (by
      intro γ hγ a b
      show ∑' y, ‖tm y (ω (a, γ * b) f)‖ₑ = ∑' y, ‖tm y (ω (a, b) f)‖ₑ
      let γq : GQ W := ⟨γ, hγ⟩
      have hl : ∀ y : Matrix (Fin W.rank) (Fin r) D.host.E, ratM W γq⁻¹ * (ratM W γq * y) = y := fun y => by
        rw [← Matrix.mul_assoc, ← ratM_mul, inv_mul_cancel, ratM_one, Matrix.one_mul]
      have hr : ∀ y : Matrix (Fin W.rank) (Fin r) D.host.E, ratM W γq * (ratM W γq⁻¹ * y) = y := fun y => by
        rw [← Matrix.mul_assoc, ← ratM_mul, mul_inv_cancel, ratM_one, Matrix.one_mul]
      let e : Matrix (Fin W.rank) (Fin r) D.host.E ≃ Matrix (Fin W.rank) (Fin r) D.host.E :=
        ⟨fun y => ratM W γq * y, fun y => ratM W γq⁻¹ * y, hl, hr⟩
      rw [← e.tsum_eq (fun y => ‖tm y (ω (a, γ * b) f)‖ₑ)]
      refine tsum_congr fun y => ?_
      show ‖tm (ratM W γq * y) (ω (a, γ * b) f)‖ₑ = ‖tm y (ω (a, b) f)‖ₑ
      rw [hR, heqv γ (ratM W γq) hγ (ratM_spec W γq) y _ (hfp _)])
    A c (fun a b => by simp only [htm]; exact (hcb a b).2) g

  obtain ⟨hInt, hSum, hHas⟩ := fub (κ.restrict 𝓝) ν Set.univ 𝓕
    (fun y (n : NI V C) h => tm y (ω ((n : GA D V) * g, h) f)) hTm
    (fun (n : NI V C) h => thetaKO ω ((n : GA D V) * g) h f) F hFd.2.1.measurable
    (fun n h => hsum _ (hfp _)) (by rw [Measure.restrict_univ]; exact hb0)
  simp only [Measure.restrict_univ, integrableOn_univ] at hInt hSum hHas
  set a : Matrix (Fin W.rank) (Fin r) D.host.E → ℂ :=
    fun y => ∫ h in 𝓕, (∫ n in 𝓝, tm y (ω ((n : GA D V) * g, h) f) ∂κ) * F h ∂ν with ha

  have heis0 : ∀ u : WO V W → ℂ, heisO ψ V W 0 u = u := fun u => heisO_zero_twisted_operators ψ V W u
  have hT0 : ∀ (n : NI V C) (h : GA D W),
      tm 0 (ω ((n : GA D V) * g, h) f) = thetaKO ω' 1 h (res V V' W C B μ 𝓨 (ω (g, 1) f)) := by
    intro n h
    rw [htm]
    have hiso0 : isoPart V W C' ((0 : Matrix (Fin W.rank) (Fin r) D.host.E).map (incA D)) = 0 := by
      simp [isoPart]
    rw [hiso0, heis0, hL, GlobalTheory.T.wittTower_restriction_unipotentRadical_invariant D V V' W r C B hS ψ χS χT ω hω μ 𝓨 hY n _ (hfp _)]
    have e2 : ((g, h) : GA D V × GA D W) = (1, h) * (g, 1) := by rw [Prod.mk_mul_mk, one_mul, mul_one]
    rw [e2, hωm, hc μ 𝓨 hY h _ hf₁]
    rfl
  have hc0 : ∀ h : GA D W, ∫ _ in 𝓝, thetaKO ω' 1 h (res V V' W C B μ 𝓨 (ω (g, 1) f)) ∂κ =
      ((κ 𝓝).toReal : ℂ) * thetaKO ω' 1 h (res V V' W C B μ 𝓨 (ω (g, 1) f)) := by
    intro h
    rw [setIntegral_const, Complex.real_smul]
    try rfl
  have ha0 : a 0 = ((κ 𝓝).toReal : ℂ) * Lift.liftInt ν 𝓕 (thetaKO ω') (res V V' W C B μ 𝓨 (ω (g, 1) f)) F 1 := by
    calc a 0 = ∫ h in 𝓕, ((κ 𝓝).toReal : ℂ) * (thetaKO ω' 1 h (res V V' W C B μ 𝓨 (ω (g, 1) f)) * F h) ∂ν := by
          refine integral_congr_ae (ae_of_all _ fun h => ?_)
          simp only [hT0, hc0]
          ring
      _ = _ := by
          rw [integral_const_mul]
          rfl

  have hvanish : ∑' y : {y : Matrix (Fin W.rank) (Fin r) D.host.E // y ≠ 0}, a y.1 = 0 := by
    letI := ratAct W r
    refine GlobalTheory.T.tsum_setIntegral_fundamentalDomain_eq_zero_by_orbits (GA D W) ν (GQ W) {y : Matrix (Fin W.rank) (Fin r) D.host.E // y ≠ 0} 𝓕 h𝓕
      (fun y h => (∫ n in 𝓝, tm y.1 (ω ((n : GA D V) * g, h) f) ∂κ) * F h)
      (fun y => (hKm y.1).mul hFd.2.1.measurable) ?_ ?_ ?_
    · intro γ y h
      show (∫ n in 𝓝, tm (ratM W γ * y.1) (ω ((n : GA D V) * g, (γ : GA D W) * h) f) ∂κ) * F ((γ : GA D W) * h) =
        (∫ n in 𝓝, tm y.1 (ω ((n : GA D V) * g, h) f) ∂κ) * F h
      rw [hFd.1 γ γ.2 h]
      congr 1
      refine integral_congr_ae (ae_of_all _ fun n => ?_)
      show tm (ratM W γ * y.1) (ω ((n : GA D V) * g, (γ : GA D W) * h) f) = tm y.1 (ω ((n : GA D V) * g, h) f)
      rw [hR, heqv γ.1 (ratM W γ) γ.2 (ratM_spec W γ) y.1 _ (hfp _)]
    · refine ne_top_of_le_ne_top hSum ?_
      exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
        (fun y => ∫⁻ h in 𝓕, ‖(∫ n in 𝓝, tm y (ω ((n : GA D V) * g, h) f) ∂κ) * F h‖ₑ ∂ν)
    · intro y 𝓖 h𝓖 hint
      by_cases hiso : adj D y.1 * W.gram * y.1 = 0
      · obtain ⟨s, L, m, m', hLf, hm, hmm', hy⟩ := rankFac D W r y.1 y.2 hiso
        have hLy : ∀ k : GQ W, ratM W k * y.1 = y.1 → ratM W k * L = L := by
          intro k hk
          rw [hy, ← Matrix.mul_assoc] at hk
          have hk' := congrArg (· * m') hk
          simpa only [Matrix.mul_assoc, hmm', Matrix.mul_one] using hk'
        refine cusp D W s L hLf ν hν F hFd hFc ((MulAction.stabilizer (GQ W) y).map (GQ W).subtype)
          (Subgroup.map_subtype_le _) ?_ ?_ (fun h => ∫ n in 𝓝, tm y.1 (ω ((n : GA D V) * g, h) f) ∂κ)
          (hKm y.1) ?_ ?_ 𝓖 h𝓖 hint
        · rintro γ ⟨k, hk, rfl⟩ n hn
          have hk1 : ratM W k * y.1 = y.1 := congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hk)
          exact (GlobalTheory.T.rationalFrameStabiliser_normalises_unipotentRadical D W s L hLf).1 k.1 k.2 (ratM W k) (ratM_spec W k) (hLy k hk1) n hn
        · intro n hn hnq
          refine ⟨⟨n, hnq⟩, MulAction.mem_stabilizer_iff.mpr (Subtype.ext ?_), rfl⟩
          show ratM W ⟨n, hnq⟩ * y.1 = y.1
          rw [hy, ← Matrix.mul_assoc,
            (GlobalTheory.T.rationalFrameStabiliser_normalises_unipotentRadical D W s L hLf).2 n hn (ratM W ⟨n, hnq⟩) (ratM_spec W ⟨n, hnq⟩)]
        · intro n' hn' h
          have e1 : (fun n : NI V C => tm y.1 (ω ((n : GA D V) * g, n' * h) f)) =
              fun n : NI V C => tm (L * m) (ω ((n : GA D V), n') (ω (g, h) f)) := by
            funext n
            rw [hLR, hy]
          have e2 : (fun n : NI V C => tm y.1 (ω ((n : GA D V) * g, h) f)) =
              fun n : NI V C => tm (L * m) (ω ((n : GA D V), 1) (ω (g, h) f)) := by
            funext n
            rw [hL, hy]
          show ∫ n in 𝓝, tm y.1 (ω ((n : GA D V) * g, n' * h) f) ∂κ = ∫ n in 𝓝, tm y.1 (ω ((n : GA D V) * g, h) f) ∂κ
          rw [e1, e2]
          exact hcuspN s L m hLf hm ⟨n', hn'⟩ _ (hfp _)
        · rintro γ ⟨k, hk, rfl⟩ h
          have hk1 : ratM W k * y.1 = y.1 := congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hk)
          refine integral_congr_ae (ae_of_all _ fun n => ?_)
          show tm y.1 (ω ((n : GA D V) * g, (k : GA D W) * h) f) = tm y.1 (ω ((n : GA D V) * g, h) f)
          conv_lhs => rw [← hk1]
          rw [hR, heqv k.1 (ratM W k) k.2 (ratM_spec W k) y.1 _ (hfp _)]
      · have hz : ∀ h, ∫ n in 𝓝, tm y.1 (ω ((n : GA D V) * g, h) f) ∂κ = 0 := by
          intro h
          have e2 : (fun n : NI V C => tm y.1 (ω ((n : GA D V) * g, h) f)) =
              fun n : NI V C => tm y.1 (ω ((n : GA D V), 1) (ω (g, h) f)) := by
            funext n
            rw [hL]
          rw [e2]
          exact hnon y.1 hiso _ (hfp _)
        simp [hz]
  have hbsum : HasSum (Set.indicator {y | y ≠ 0} a) 0 := by
    have hs := hHas.summable.indicator {y | y ≠ 0}
    have ht : ∑' y, Set.indicator {y | y ≠ 0} a y = 0 := by
      rw [← tsum_subtype]
      exact hvanish
    rw [← ht]
    exact hs.hasSum
  have hfull : HasSum a (a 0 + 0) := by
    classical
    have h0 := (hasSum_ite_eq (0 : Matrix (Fin W.rank) (Fin r) D.host.E) (a 0)).add hbsum
    convert h0 using 1
    funext y
    by_cases hy0 : y = 0
    · subst hy0
      simp
    · simp [hy0]
  refine ⟨hvol, hI1, hI2,
    fun g₁ => GlobalTheory.Chain.LiftConv.integrableOn_of_rapidDec hG hθ hω hf hν h𝓕 hFd g₁,
    GlobalTheory.Chain.LiftConv.integrableOn_of_rapidDec hG hθ hω' hI2 hν h𝓕 hFd 1, hInt, ?_⟩
  exact (hHas.unique hfull).trans ((add_zero _).trans ha0)

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftConstantTermCompatibleWeilStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_constantTerm_compatibleWeil : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.TowerConstTermOfCompatible D := by
  first | exact @GlobalTheory.TowerCT.towerConstTermOfCompatible_holds | exact GlobalTheory.TowerCT.towerConstTermOfCompatible_holds | (intros; apply GlobalTheory.TowerCT.towerConstTermOfCompatible_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstantTermLiftIsotropicSubspace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TowerConstTermObj

theorem towerConstTerm : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.TowerConstTerm D := by

  intro D V V' W r C B hsplit ψ χS χT χT' ω ω' hω hω'
  have hcomp : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.Compatible ψ V V' W C B ω ω' :=
    GlobalTheory.T.weilCompatible_of_sameSplittingCharacter D V V' W r C B hsplit ψ χS χT χT' ω ω' hω hω'
  exact GlobalTheory.T.thetaLift_constantTerm_compatibleWeil D V V' W r C B hsplit ψ χS χT χS χT' ω ω' hω hω' hcomp

end GlobalTheory.TowerConstTermObj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstantTermLiftIsotropicSubspaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantTermLift_isotropicSubspace : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.TowerConstTerm D := by
  first | exact @GlobalTheory.TowerConstTermObj.towerConstTerm | exact GlobalTheory.TowerConstTermObj.towerConstTerm | (intros; apply GlobalTheory.TowerConstTermObj.towerConstTerm <;> assumption)
end
