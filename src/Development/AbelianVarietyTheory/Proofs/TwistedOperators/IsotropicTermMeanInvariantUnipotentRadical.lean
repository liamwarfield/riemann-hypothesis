module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilCompatibleOfSameSplittingCharacter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittTowerRestrictionUnipotentRadicalInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalTargetPreservesIsotropicMean
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalTargetPreservesIsotropicMean
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnipMean

theorem heisO_zero {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (f : WO V W → ℂ) : heisO ψ V W 0 f = f := by
  funext x
  unfold heisO symplOH symplO hO
  simp

theorem symplO_zero_left {D : D7} (V W : HSp D) (z : WO V W) : symplO V W 0 z = 0 := by
  unfold symplO hO
  simp

theorem mean_target : ∀ (D : D7) (V W : HSp D) (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W L → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D s V.rank)) (𝓐 : Set (Mx D s V.rank)), IsCovolOne (ratMx D s V.rank) μ 𝓐 → ∀ (n : NI W L) (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∫ a in 𝓐, ω (1, (n : GA D W)) f (HMul.hMul (L.map (incA D)) (a : Matrix (Fin s) (Fin V.rank) (AE D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) ∂μ = ∫ a in 𝓐, f (HMul.hMul (L.map (incA D)) (a : Matrix (Fin s) (Fin V.rank) (AE D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) ∂μ := by
  intro D V W s L hL ψ χS χT ω hω μ 𝓐 hcov n f hf
  have hiso := iso_rat hL
  have e1 : (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hm1 : Formalism.L2.Theta.mt V 1 = 1 := by
    unfold Formalism.L2.Theta.mt
    simp
  have hact : ∀ (g : GA D W) (x : WO V W), actO V W 1 g x = HMul.hMul (Formalism.L2.Theta.mt W g) x := by
    intro g x
    unfold actO
    rw [inv_one, hm1, Matrix.mul_one]
  have hrk : L.rank = s := by
    rw [Matrix.rank_eq_finrank_span_cols]
    exact (finrank_span_eq_card hL.2.1).trans (Fintype.card_fin s)
  have hsym : ∀ y y' : Mx D s V.rank, symplO V W (HMul.hMul (HMul.hMul (L.map (incA D)) y) ((1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D))) (HMul.hMul (HMul.hMul (L.map (incA D)) y') ((1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D))) = 0 := by
    intro y y'
    rw [e1, Matrix.mul_one, Matrix.mul_one]
    exact symplO_frame hiso y y'
  have hsc : ∀ g : GA D W,
      (∀ y : Mx D s V.rank, HMul.hMul (mt W g) (HMul.hMul (GlobalTheory.MixModel.rat L) y) = HMul.hMul (GlobalTheory.MixModel.rat L) y) →
      (∀ x : WO V W, HMul.hMul (GlobalTheory.MixModel.adj (GlobalTheory.MixModel.rat L)) (HMul.hMul (GlobalTheory.MixModel.gA W) x) = 0 →
        ∃ y : Mx D s V.rank, HMul.hMul (mt W g) x = x + HMul.hMul (GlobalTheory.MixModel.rat L) y) →
      ∃ c : ℂ, c ≠ 0 ∧ Sc ψ ω (GlobalTheory.MixModel.rat L) μ 𝓐 g c := by
    intro g hg1 hg2
    have hfix : ∀ y : Mx D s V.rank, actO V W 1 g (HMul.hMul (HMul.hMul (L.map (incA D)) y) ((1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D))) = HMul.hMul (HMul.hMul (L.map (incA D)) y) ((1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D)) := by
      intro y
      rw [e1, Matrix.mul_one, hact]
      exact hg1 y
    have hmov : ∀ x : WO V W, (∀ y : Mx D s V.rank, symplO V W x (HMul.hMul (HMul.hMul (L.map (incA D)) y) ((1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D))) = 0) → ∃ y : Mx D s V.rank, actO V W 1 g x = x + HMul.hMul (HMul.hMul (L.map (incA D)) y) ((1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D)) := by
      intro x hx
      rw [e1] at hx
      simp only [Matrix.mul_one] at hx
      obtain ⟨y, hy⟩ := hg2 x (adj_eq_zero_of_symplO (C := GlobalTheory.MixModel.rat L) hx)
      refine ⟨y, ?_⟩
      rw [e1, Matrix.mul_one, hact]
      exact hy
    obtain ⟨c, hc⟩ := GlobalTheory.T.isotropicMean_changes_by_scalar_of_trivial_action D V W s V.rank L 1 hrk (Matrix.rank_one.trans (Fintype.card_fin _)) hsym ψ χS χT ω hω μ 𝓐 hcov 1 g hfix hmov
    refine ⟨c, Circle.coe_ne_zero c, ?_⟩
    intro f' hf'
    have h0 := hc f' hf' 0 (fun y => symplO_zero_left V W _)
    simp only [heisO_zero, e1, Matrix.mul_one] at h0
    exact h0
  have key := mean_unip hL hω hcov hsc n.2 f hf
  unfold meanL at key
  rw [one_mul] at key
  exact key

end GlobalTheory.UnipMean

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalTargetPreservesIsotropicMeanStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentRadical_target_preserves_isotropic_mean : ∀ (D : D7) (V W : HSp D) (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W L → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D s V.rank)) (𝓐 : Set (Mx D s V.rank)), IsCovolOne (ratMx D s V.rank) μ 𝓐 → ∀ (n : NI W L) (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∫ a in 𝓐, ω (1, (n : GA D W)) f (HMul.hMul (L.map (incA D)) (a : Matrix (Fin s) (Fin V.rank) (AE D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) ∂μ = ∫ a in 𝓐, f (HMul.hMul (L.map (incA D)) (a : Matrix (Fin s) (Fin V.rank) (AE D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) ∂μ := by
  first | exact @GlobalTheory.UnipMean.mean_target | exact GlobalTheory.UnipMean.mean_target | (intros; apply GlobalTheory.UnipMean.mean_target <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalMeanEqVolumeMulRationalMean
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalMeanEqVolumeMulRationalMean
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped GlobalTheory.MixModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnipMean

variable {D : D7}

theorem topology_NI (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (hC : IsIsoFrame V C) :
    LocallyCompactSpace (NI V C) ∧ SecondCountableTopology (NI V C) ∧ BorelSpace (NI V C) ∧
    IsTopologicalGroup (NI V C) ∧ Countable (NIQ V C) ∧
    ∃ K : Set (NI V C), IsCompact K ∧ ∀ n, ∃ γ ∈ NIQ V C, ∃ k ∈ K, n = γ * k := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨K, hK, h⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D V r C ⟨hC.2.1, hC.2.2⟩).2
  have hcl : IsClosed (NI V C : Set (GA D V)) := by
    have : DiscreteTopology (GQ V ⊓ NI V C : Subgroup (GA D V)) :=
      DiscreteTopology.of_subset (s := (GQ V : Set (GA D V))) i6 (fun x hx => hx.1)
    have h1 : IsClosed ((GQ V ⊓ NI V C : Subgroup (GA D V)) : Set (GA D V)) := Subgroup.isClosed_of_discrete
    have h2 := h1.mul_right_of_isCompact (hK.image continuous_subtype_val)
    convert h2 using 1
    ext x
    constructor
    · intro hx
      obtain ⟨γ, hγ, k, hk, e⟩ := h ⟨x, hx⟩
      exact ⟨γ, ⟨hγ, γ.2⟩, k, ⟨k, hk, rfl⟩, (congrArg Subtype.val e).symm⟩
    · rintro ⟨γ, hγ, _, ⟨k, -, rfl⟩, rfl⟩
      exact mul_mem hγ.2 k.2
  have hinj : Function.Injective fun γ : NIQ V C => (⟨γ.1.1, γ.2⟩ : GQ V) :=
    fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : GQ V => (x : GA D V)) h))
  exact ⟨hcl.locallyCompactSpace, TopologicalSpace.Subtype.secondCountableTopology _, Subtype.borelSpace _,
    inferInstance, hinj.countable, K, hK, h⟩

theorem mean_of_hom {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ]
    {s k : ℕ} (f : G → Mx D s k) (hf : ∀ x y, f (x * y) = f x + f y) (hfc : Continuous f)
    (hfs : Function.Surjective f) (hfΓ : ∀ γ ∈ Γ, f γ ∈ ratMx D s k)
    (κ : Measure G) [κ.IsHaarMeasure] (𝓝 : Set G) (h𝓝 : IsFundamentalDomain Γ 𝓝 κ) (hfin : κ 𝓝 ≠ ⊤)
    {μ : Measure (Mx D s k)} {𝓐 : Set (Mx D s k)} (hμ : IsCovolOne (ratMx D s k) μ 𝓐)
    (φ : Mx D s k → ℂ) (hφc : Continuous φ) (hφ : ∀ γ ∈ ratMx D s k, ∀ a, φ (γ + a) = φ a) :
    ∫ n in 𝓝, φ (f n) ∂κ = ((κ 𝓝).toReal : ℂ) * ∫ a in 𝓐, φ a ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D s k
  haveI : BorelSpace (Mx D s k) := ⟨rfl⟩
  haveI := hμ.1
  have h0 : κ 𝓝 ≠ 0 := h𝓝.measure_ne_zero (NeZero.ne κ)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hφc.continuousOn
  have hb : ∀ a, ‖φ a‖ ≤ M := fun a => by
    obtain ⟨γ, hγ, ha⟩ := hKc a
    rw [← hφ γ hγ a]
    exact hM _ ha
  have hinv : ∀ a, ∫ n in 𝓝, φ (f n + a) ∂κ = ∫ n in 𝓝, φ (f n) ∂κ := by
    intro a
    obtain ⟨n0, rfl⟩ := hfs a
    have hmp : MeasurePreserving (· * n0) κ κ :=
      ⟨measurable_mul_const n0, GlobalTheory.AutQuotCheck.rightInvariant_of_covolume Γ κ h𝓝 h0 hfin n0⟩
    have hmp' : MeasurePreserving (· * n0⁻¹) κ κ :=
      ⟨measurable_mul_const n0⁻¹, GlobalTheory.AutQuotCheck.rightInvariant_of_covolume Γ κ h𝓝 h0 hfin n0⁻¹⟩
    have hF' : IsFundamentalDomain Γ ((· * n0⁻¹) ⁻¹' 𝓝) κ :=
      h𝓝.preimage_of_equiv hmp'.quasiMeasurePreserving (e := id) Function.bijective_id
        (fun γ x => by simp [Subgroup.smul_def, mul_assoc])
    have e1 : (· * n0) ⁻¹' ((· * n0⁻¹) ⁻¹' 𝓝) = 𝓝 := by
      ext x; simp
    have := hmp.setIntegral_preimage_emb (measurableEmbedding_mulRight n0) (fun y => φ (f y)) ((· * n0⁻¹) ⁻¹' 𝓝)
    rw [e1] at this
    simp only [hf] at this
    rw [this]
    exact hF'.setIntegral_eq h𝓝 fun γ x => by
      rw [Subgroup.smul_def, smul_eq_mul, hf, hφ _ (hfΓ _ γ.2)]
  haveI : IsFiniteMeasure (κ.restrict 𝓝) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓐) := ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
  have hint : Integrable (Function.uncurry fun n a => φ (f n + a)) ((κ.restrict 𝓝).prod (μ.restrict 𝓐)) :=
    Integrable.of_bound (hφc.comp ((hfc.comp continuous_fst).add continuous_snd)).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun p => hb _)
  have hswap := integral_integral_swap hint
  have l1 : ∀ n, ∫ a in 𝓐, φ (f n + a) ∂μ = ∫ a in 𝓐, φ a ∂μ := fun n => by
    rw [← GlobalTheory.MixModel.covolOne_integral_add hμ φ hφ (f n)]
    simp only [add_comm]
  simp only [l1, hinv, integral_const, smul_eq_mul] at hswap
  rw [Measure.real, Measure.real, Measure.restrict_apply_univ, Measure.restrict_apply_univ, hμ.2.2] at hswap
  simpa [mul_comm] using hswap.symm

theorem mul_sub_one_eq {R : Type*} [Ring R] (a b : R) : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by
  noncomm_ring

def coord (V : HSp D) {s k : ℕ} (M : Matrix (Fin s) (Fin V.rank) D.host.E) (B : Matrix (Fin V.rank) (Fin k) D.host.E)
    (g : GA D V) : Mx D s k :=
  HMul.hMul (HMul.hMul (M.map (incA D) : Matrix (Fin s) (Fin V.rank) (AE D)) (mt V g - 1))
    (B.map (incA D) : Matrix (Fin V.rank) (Fin k) (AE D))


set_option maxHeartbeats 2000000 in
theorem mem_NI_prop (V : HSp D) {r k : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin k) D.host.E) (hB : adj D C * V.gram * B = 0) {g : GA D V} (hg : g ∈ NI V C) :
    (mt V g - 1) ⬝ C.map (incA D) = 0 ∧
      ∃ Y : Matrix (Fin r) (Fin k) (AE D), (mt V g - 1) ⬝ B.map (incA D) = C.map (incA D) ⬝ Y := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨h1, -, h3⟩ := hx
    refine ⟨h1, ?_⟩
    have hcol : ∀ j, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).mulVec (fun i => B i j) = 0 := by
      intro j
      funext i
      have := congrFun (congrFun hB i) j
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, adj] using this
    choose a ha using fun j => h3 (fun i => B i j) (hcol j)
    refine ⟨Matrix.of fun i j => a j i, ?_⟩
    funext i j
    have := congrFun (ha j) i
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply] at this ⊢
    exact this
  | one =>
    refine ⟨by simp [GlobalTheory.MixModel.mt_one], 0, by simp [GlobalTheory.MixModel.mt_one]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨hx1, Yx, hx2⟩ := hx
    obtain ⟨hy1, Yy, hy2⟩ := hy
    have e : mt V (x * y) - 1 = (mt V x - 1) * (mt V y - 1) + (mt V x - 1) + (mt V y - 1) := by
      rw [GlobalTheory.MixModel.mt_mul]; exact mul_sub_one_eq _ _
    refine ⟨?_, Yx + Yy, ?_⟩
    · rw [e, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc, hy1, hx1, Matrix.mul_zero, add_zero, add_zero]
    · rw [e, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc, hy2, hx2, ← Matrix.mul_assoc, hx1, Matrix.zero_mul,
        zero_add, Matrix.mul_add]
  | inv x _ hx =>
    obtain ⟨hx1, Y, hx2⟩ := hx
    have hinv : ∀ {q : ℕ} (Z : Matrix (Fin V.rank) (Fin q) (AE D)), mt V x⁻¹ ⬝ (mt V x ⬝ Z) = Z := fun Z => by
      rw [← Matrix.mul_assoc, GlobalTheory.MixModel.mt_inv_mul, Matrix.one_mul]
    have hc : mt V x ⬝ (C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) = C.map (incA D) := by
      have h := hx1
      rw [Matrix.sub_mul] at h
      rw [Matrix.one_mul] at h
      exact sub_eq_zero.1 h
    have hb : mt V x ⬝ (B.map (incA D) : Matrix (Fin V.rank) (Fin k) (AE D)) = B.map (incA D) + (C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) ⬝ Y := by
      have h := hx2
      rw [Matrix.sub_mul] at h
      rw [Matrix.one_mul] at h
      exact sub_eq_iff_eq_add'.1 h
    have h2 : mt V x⁻¹ ⬝ (C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) = C.map (incA D) := by
      conv_lhs => rw [← hc]
      exact hinv _
    refine ⟨by rw [Matrix.sub_mul, Matrix.one_mul, h2, sub_self], -Y, ?_⟩
    have h3 := hinv (B.map (incA D))
    rw [hb, Matrix.mul_add, ← Matrix.mul_assoc, h2] at h3
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_neg]
    rw [← eq_sub_iff_add_eq] at h3
    rw [h3]
    abel

theorem coord_mul (V : HSp D) {r s k : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (M : Matrix (Fin s) (Fin V.rank) D.host.E) (B : Matrix (Fin V.rank) (Fin k) D.host.E)
    (hB : adj D C * V.gram * B = 0) (x y : NI V C) :
    coord V M B ((x * y : NI V C) : GA D V) = coord V M B x + coord V M B y := by
  obtain ⟨hx1, -⟩ := mem_NI_prop V C B hB x.2
  obtain ⟨-, Yy, hy2⟩ := mem_NI_prop V C B hB y.2
  have e : mt V ((x * y : NI V C) : GA D V) - 1 =
      (mt V x - 1) * (mt V y - 1) + (mt V x - 1) + (mt V y - 1) := by
    rw [Subgroup.coe_mul, GlobalTheory.MixModel.mt_mul]; exact mul_sub_one_eq _ _
  simp only [coord]
  rw [e, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc _ ((mt V x - 1) * _),
    Matrix.mul_assoc (mt V x - 1), hy2, ← Matrix.mul_assoc (mt V x - 1), hx1, Matrix.zero_mul, Matrix.mul_zero,
    zero_add]

theorem coord_rat (V : HSp D) {r s k : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (M : Matrix (Fin s) (Fin V.rank) D.host.E) (B : Matrix (Fin V.rank) (Fin k) D.host.E) (γ : NI V C)
    (hγ : γ ∈ NIQ V C) : coord V M B γ ∈ ratMx D s k := by
  have h := (GlobalTheory.MixModel.mem_GQ_iff V (γ : GA D V)).1 hγ
  have h1 : mt V γ - 1 ∈ GlobalTheory.MixModel.ratMx D V.rank V.rank := sub_mem h GlobalTheory.MixModel.ratMx_one
  exact GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem M) h1) (GlobalTheory.MixModel.rat_mem B)

theorem continuous_coord (V : HSp D) {s k : ℕ} (M : Matrix (Fin s) (Fin V.rank) D.host.E)
    (B : Matrix (Fin V.rank) (Fin k) D.host.E) : Continuous (coord V M B) := by
  obtain ⟨i1, -⟩ := GlobalTheory.MixModel.lattice_Mx D V.rank V.rank
  haveI : ContinuousSub (Mx D V.rank V.rank) := IsTopologicalAddGroup.to_continuousSub
  exact (continuous_const.matrix_mul ((GlobalTheory.MixModel.continuous_mt V).sub continuous_const)).matrix_mul continuous_const

theorem exists_right_inv {K : Type*} [Field K] {s r : ℕ} (m : Matrix (Fin s) (Fin r) K) (hm : m.rank = s) :
    ∃ m' : Matrix (Fin r) (Fin s) K, m * m' = 1 := by
  have htop : LinearMap.range m.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    exact hm
  have hs : ∀ i, ∃ v, m.mulVec v = Pi.single i 1 := fun i => by
    have : (Pi.single i (1 : K) : Fin s → K) ∈ LinearMap.range m.mulVecLin := htop ▸ Submodule.mem_top
    obtain ⟨v, hv⟩ := this
    exact ⟨v, hv⟩
  choose v hv using hs
  refine ⟨Matrix.of fun j i => v i j, ?_⟩
  ext i i'
  have := congrFun (hv i') i
  simp only [Matrix.mulVec, dotProduct] at this
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.of_apply, this, Pi.single_apply]

theorem unit_aux {S R : Type*} [CommRing S] [Ring R] [Algebra S R] (h : S) (hh : h + h = 1) (g u q us qs : R)
    (hu : us * g = -(g * u)) (hq : qs * g = g * q) (huu : u * u = -q) (huq : u * q = 0) (hqu : q * u = 0) :
    (1 + us - h • qs) * g * (1 + u - h • q) = g := by
  have hqq : q * q = 0 := by
    have : q * (u * u) = 0 := by rw [← mul_assoc, hqu, zero_mul]
    rwa [huu, mul_neg, neg_eq_zero] at this
  have e1 : (1 + us - h • qs) * g = g * (1 - u - h • q) := by
    rw [sub_mul, add_mul, one_mul, hu, smul_mul_assoc, hq, mul_sub, mul_sub, mul_one, mul_smul_comm]
    abel
  have e2 : (1 - u - h • q) * (1 + u - h • q) = 1 := by
    simp only [sub_mul, add_mul, mul_sub, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, huu, huq, hqu,
      hqq, smul_zero, smul_smul]
    linear_combination (norm := module) (-1 : S) • hh • q
  rw [e1, mul_assoc, e2, mul_one]

section Surj

open GlobalTheory.MixModel (rat gA giA half ofMat)


set_option maxHeartbeats 4000000 in
theorem coord_surj (V V' : HSp D) {r s : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (hs : IsIsoSplit V V' C B) (h1 : adj D C * V.gram * C' = 1)
    (h3 : adj D C' * V.gram * B = 0) (m : Matrix (Fin s) (Fin r) D.host.E) (hm : m.rank = s)
    (X : Mx D s V'.rank) : ∃ n : NI V C, coord V (m * adj D C' * V.gram) B n = X := by
  obtain ⟨m', hm'⟩ := exists_right_inv m hm
  have hr : ∀ {a b : ℕ} (P : Matrix (Fin V.rank) (Fin a) D.host.E) (Q : Matrix (Fin V.rank) (Fin b) D.host.E),
      rat (adj D P * V.gram * Q) = GlobalTheory.MixModel.adj (rat P) ⬝ (gA V ⬝ rat Q) := by
    intro a b P Q
    rw [GlobalTheory.MixModel.rat_mul, GlobalTheory.MixModel.rat_mul, Matrix.mul_assoc]
    rfl
  set c := rat C with hc
  set b := rat B with hb
  set c' := rat C' with hc'
  set G := gA V with hG
  set G' := gA V' with hG'
  have f1 : GlobalTheory.MixModel.adj c ⬝ (G ⬝ c) = 0 := by
    rw [← hr, show adj D C * V.gram * C = 0 from hs.frame.2.2, GlobalTheory.MixModel.rat_zero]
  have f2 : GlobalTheory.MixModel.adj c ⬝ (G ⬝ b) = 0 := by rw [← hr, hs.orth, GlobalTheory.MixModel.rat_zero]
  have f3 : GlobalTheory.MixModel.adj b ⬝ (G ⬝ b) = G' := by rw [← hr, hs.isom]; rfl
  have f6 : GlobalTheory.MixModel.adj c' ⬝ (G ⬝ b) = 0 := by rw [← hr, h3, GlobalTheory.MixModel.rat_zero]
  have f4 : GlobalTheory.MixModel.adj b ⬝ (G ⬝ c) = 0 := by
    have := congrArg GlobalTheory.MixModel.adj f2
    rwa [GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_adj, GlobalTheory.MixModel.adj_gA,
      GlobalTheory.MixModel.adj_zero, Matrix.mul_assoc] at this
  have f5 : GlobalTheory.MixModel.adj c' ⬝ (G ⬝ c) = 1 := by
    have := congrArg GlobalTheory.MixModel.adj (show GlobalTheory.MixModel.adj c ⬝ (G ⬝ c') = 1 by
      rw [← hr, h1, GlobalTheory.MixModel.rat_one])
    rwa [GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_adj, GlobalTheory.MixModel.adj_gA,
      GlobalTheory.MixModel.adj_one, Matrix.mul_assoc] at this
  have e1 : ∀ {q : ℕ} (Y : Matrix (Fin r) (Fin q) (AE D)), GlobalTheory.MixModel.adj c ⬝ (G ⬝ (c ⬝ Y)) = 0 := fun Y => by
    rw [← Matrix.mul_assoc G, ← Matrix.mul_assoc, f1, Matrix.zero_mul]
  have e2 : ∀ {q : ℕ} (Y : Matrix (Fin V'.rank) (Fin q) (AE D)), GlobalTheory.MixModel.adj c ⬝ (G ⬝ (b ⬝ Y)) = 0 := fun Y => by
    rw [← Matrix.mul_assoc G, ← Matrix.mul_assoc, f2, Matrix.zero_mul]
  have e3 : ∀ {q : ℕ} (Y : Matrix (Fin V'.rank) (Fin q) (AE D)), GlobalTheory.MixModel.adj b ⬝ (G ⬝ (b ⬝ Y)) = G' ⬝ Y :=
    fun Y => by rw [← Matrix.mul_assoc G, ← Matrix.mul_assoc, f3]
  have e4 : ∀ {q : ℕ} (Y : Matrix (Fin r) (Fin q) (AE D)), GlobalTheory.MixModel.adj b ⬝ (G ⬝ (c ⬝ Y)) = 0 := fun Y => by
    rw [← Matrix.mul_assoc G, ← Matrix.mul_assoc, f4, Matrix.zero_mul]
  have e5 : ∀ {q : ℕ} (Y : Matrix (Fin r) (Fin q) (AE D)), GlobalTheory.MixModel.adj c' ⬝ (G ⬝ (c ⬝ Y)) = Y := fun Y => by
    rw [← Matrix.mul_assoc G, ← Matrix.mul_assoc, f5, Matrix.one_mul]
  set Z : Matrix (Fin r) (Fin V'.rank) (AE D) := rat m' ⬝ X ⬝ giA V' with hZ
  set u : Matrix (Fin V.rank) (Fin V.rank) (AE D) :=
    c ⬝ (Z ⬝ (GlobalTheory.MixModel.adj b ⬝ G)) - b ⬝ (GlobalTheory.MixModel.adj Z ⬝ (GlobalTheory.MixModel.adj c ⬝ G)) with hu
  set q : Matrix (Fin V.rank) (Fin V.rank) (AE D) :=
    c ⬝ (Z ⬝ (G' ⬝ (GlobalTheory.MixModel.adj Z ⬝ (GlobalTheory.MixModel.adj c ⬝ G)))) with hq
  have ku : GlobalTheory.MixModel.adj u * G = -(G * u) := by
    simp only [hu, GlobalTheory.MixModel.adj_sub, GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_adj, hG, GlobalTheory.MixModel.adj_gA,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, neg_sub]
  have kq : GlobalTheory.MixModel.adj q * G = G * q := by
    simp only [hq, GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_adj, hG, hG', GlobalTheory.MixModel.adj_gA, Matrix.mul_assoc]
  have kuu : u * u = -q := by
    simp only [hu, hq, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, e1, e2, e3, e4, Matrix.mul_zero, sub_zero,
      zero_sub]
  have kuq : u * q = 0 := by
    simp only [hu, hq, Matrix.sub_mul, Matrix.mul_assoc, e1, e4, Matrix.mul_zero, sub_zero]
  have kqu : q * u = 0 := by
    simp only [hu, hq, Matrix.mul_sub, Matrix.mul_assoc, e1, e2, Matrix.mul_zero, sub_zero]
  set N : Matrix (Fin V.rank) (Fin V.rank) (AE D) := 1 + u - half D • q with hN
  have hadjN : GlobalTheory.MixModel.adj N = 1 + GlobalTheory.MixModel.adj u - half D • GlobalTheory.MixModel.adj q := by
    rw [hN, GlobalTheory.MixModel.adj_sub, GlobalTheory.MixModel.adj_add, GlobalTheory.MixModel.adj_one, GlobalTheory.MixModel.adj_smul,
      GlobalTheory.MixModel.cA_half]
  have hunit : GlobalTheory.MixModel.adj N * (gA V * N) = gA V := by
    rw [hadjN, ← Matrix.mul_assoc]
    exact unit_aux (half D) GlobalTheory.MixModel.half_add_half G u q _ _ ku kq kuu kuq kqu
  set n : GA D V := ofMat V N hunit with hn
  have hN1 : mt V n - 1 = u - half D • q := by
    rw [hn, GlobalTheory.MixModel.mt_ofMat, hN]; abel
  have kuc : u ⬝ c = 0 := by
    simp only [hu, Matrix.sub_mul, Matrix.mul_assoc, f1, f4, Matrix.mul_zero, sub_zero]
  have kqc : q ⬝ c = 0 := by
    simp only [hq, Matrix.mul_assoc, f1, Matrix.mul_zero]
  have kcu : (GlobalTheory.MixModel.adj c ⬝ G) ⬝ u = 0 := by
    simp only [hu, Matrix.mul_sub, Matrix.mul_assoc, e1, e2, sub_zero]
  have kcq : (GlobalTheory.MixModel.adj c ⬝ G) ⬝ q = 0 := by
    simp only [hq, Matrix.mul_assoc, e1]
  have kub : u ⬝ b = c ⬝ (Z ⬝ G') := by
    simp only [hu, Matrix.sub_mul, Matrix.mul_assoc, f2, f3, Matrix.mul_zero, sub_zero]
  have kqb : q ⬝ b = 0 := by
    simp only [hq, Matrix.mul_assoc, f2, Matrix.mul_zero]
  have he : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).map (incA D) =
      GlobalTheory.MixModel.adj c ⬝ G := GlobalTheory.MixModel.rat_mul _ _
  have hmem : n ∈ NI V C := by
    refine Subgroup.subset_closure ⟨?_, ?_, ?_⟩
    · change (mt V n - 1) ⬝ c = 0
      rw [hN1, Matrix.sub_mul, kuc, Matrix.smul_mul, kqc, smul_zero, sub_zero]
    · rw [he]
      change (GlobalTheory.MixModel.adj c ⬝ G) ⬝ (mt V n - 1) = 0
      rw [hN1, Matrix.mul_sub, kcu, Matrix.mul_smul, kcq, smul_zero, sub_zero]
    · intro x hx
      set xA : Fin V.rank → AE D := fun i => incA D (x i) with hxA
      have hz : GlobalTheory.MixModel.adj c *ᵥ (G *ᵥ xA) = 0 := by
        rw [Matrix.mulVec_mulVec, ← he]
        funext i
        have := congrArg (incA D) (congrFun hx i)
        rw [RingHom.map_mulVec, Pi.zero_apply, map_zero] at this
        exact this
      refine ⟨(Z ⬝ (GlobalTheory.MixModel.adj b ⬝ G)) *ᵥ xA, ?_⟩
      change (mt V n - 1) *ᵥ xA = _
      rw [hN1, Matrix.sub_mulVec, Matrix.smul_mulVec]
      have hu' : u *ᵥ xA = c *ᵥ ((Z ⬝ (GlobalTheory.MixModel.adj b ⬝ G)) *ᵥ xA) := by
        rw [hu, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec (M := b), ← Matrix.mulVec_mulVec (M := GlobalTheory.MixModel.adj Z),
          ← Matrix.mulVec_mulVec (M := GlobalTheory.MixModel.adj c), hz, Matrix.mulVec_zero, Matrix.mulVec_zero, sub_zero,
          Matrix.mulVec_mulVec]
      have hq' : q *ᵥ xA = 0 := by
        rw [hq, ← Matrix.mulVec_mulVec (M := c), ← Matrix.mulVec_mulVec (M := Z), ← Matrix.mulVec_mulVec (M := G'),
          ← Matrix.mulVec_mulVec (M := GlobalTheory.MixModel.adj Z), ← Matrix.mulVec_mulVec (M := GlobalTheory.MixModel.adj c), hz,
          Matrix.mulVec_zero, Matrix.mulVec_zero, Matrix.mulVec_zero, Matrix.mulVec_zero]
      rw [hu', hq', smul_zero, sub_zero]
      rfl
  refine ⟨⟨n, hmem⟩, ?_⟩
  have hM : (m * adj D C' * V.gram).map (incA D) = rat m ⬝ (GlobalTheory.MixModel.adj c' ⬝ G) := by
    change rat (m * adj D C' * V.gram) = _
    rw [GlobalTheory.MixModel.rat_mul, GlobalTheory.MixModel.rat_mul, Matrix.mul_assoc]
    rfl
  change (m * adj D C' * V.gram).map (incA D) ⬝ (mt V n - 1) ⬝ b = X
  rw [hM, hN1, Matrix.mul_assoc, Matrix.sub_mul, kub, Matrix.smul_mul, kqb, smul_zero, sub_zero, Matrix.mul_assoc,
    Matrix.mul_assoc, e5, hZ, Matrix.mul_assoc, Matrix.mul_assoc, hG', GlobalTheory.MixModel.giA_mul_gA, Matrix.mul_one,
    ← Matrix.mul_assoc, ← GlobalTheory.MixModel.rat_mul, hm', GlobalTheory.MixModel.rat_one, Matrix.one_mul]

end Surj

theorem mean_eq_volume_mul : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (κ : Measure (NI V C)) (𝓝 : Set (NI V C)), κ.IsHaarMeasure → IsFundamentalDomain (NIQ V C) 𝓝 κ → ∀ (s : ℕ) (m : Matrix (Fin s) (Fin r) D.host.E), m.rank = s → ∃ (μ : Measure (Mx D s V'.rank)) (𝓐 : Set (Mx D s V'.rank)), IsCovolOne (ratMx D s V'.rank) μ 𝓐 ∧ ∀ φ : Mx D s V'.rank → ℂ, Continuous φ → (∀ γ ∈ ratMx D s V'.rank, ∀ a, φ (γ + a) = φ a) → ∫ n in 𝓝, φ (HMul.hMul (HMul.hMul ((m * adj D C' * V.gram).map (incA D) : Matrix (Fin s) (Fin V.rank) (AE D)) (mt V (n : GA D V) - 1)) (B.map (incA D) : Matrix (Fin V.rank) (Fin V'.rank) (AE D))) ∂κ = ((κ 𝓝).toReal : ℂ) * ∫ a in 𝓐, φ a ∂μ := by
  intro D V V' r C C' B hs h1 _ h3 κ 𝓝 hκ h𝓝 s m hm
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := topology_NI V C hs.frame
  obtain ⟨μ, 𝓐, hμ⟩ := GlobalTheory.MixModel.exists_isCovolOne D s V'.rank
  have hfin : κ 𝓝 ≠ ⊤ := by
    have hle : κ 𝓝 ≤ κ K := by
      rw [h𝓝.measure_eq_tsum K]
      refine (measure_mono fun n hn => ?_).trans (measure_iUnion_le _)
      obtain ⟨γ, hγ, k, hk, rfl⟩ := hKc n
      exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨k, hk, rfl⟩, hn⟩
    exact (hle.trans_lt hK.measure_lt_top).ne
  refine ⟨μ, 𝓐, hμ, fun φ hφc hφ => ?_⟩
  exact mean_of_hom (NIQ V C) (fun n : NI V C => coord V (m * adj D C' * V.gram) B n)
    (coord_mul V C _ B hs.orth) ((continuous_coord V _ B).comp continuous_subtype_val)
    (fun X => coord_surj V V' C C' B hs h1 h3 m hm X) (fun γ hγ => coord_rat V C _ B γ hγ) κ 𝓝 h𝓝 hfin hμ φ hφc hφ

end GlobalTheory.UnipMean
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalMeanEqVolumeMulRationalMeanStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentRadicalMean_eq_volume_mul_rationalMean : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (κ : Measure (NI V C)) (𝓝 : Set (NI V C)), κ.IsHaarMeasure → IsFundamentalDomain (NIQ V C) 𝓝 κ → ∀ (s : ℕ) (m : Matrix (Fin s) (Fin r) D.host.E), m.rank = s → ∃ (μ : Measure (Mx D s V'.rank)) (𝓐 : Set (Mx D s V'.rank)), IsCovolOne (ratMx D s V'.rank) μ 𝓐 ∧ ∀ φ : Mx D s V'.rank → ℂ, Continuous φ → (∀ γ ∈ ratMx D s V'.rank, ∀ a, φ (γ + a) = φ a) → ∫ n in 𝓝, φ (HMul.hMul (HMul.hMul ((m * adj D C' * V.gram).map (incA D) : Matrix (Fin s) (Fin V.rank) (AE D)) (mt V (n : GA D V) - 1)) (B.map (incA D) : Matrix (Fin V.rank) (Fin V'.rank) (AE D))) ∂κ = ((κ 𝓝).toReal : ℂ) * ∫ a in 𝓐, φ a ∂μ := by
  first | exact @GlobalTheory.UnipMean.mean_eq_volume_mul | exact GlobalTheory.UnipMean.mean_eq_volume_mul | (intros; apply GlobalTheory.UnipMean.mean_eq_volume_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicTermMeanInvariantUnipotentRadical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.IsoTermMean
variable {D : D7}

theorem adj_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) : adj D A = (A.map star)ᵀ := rfl

theorem adj_ct {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) : adj D A = Aᴴ := by
  ext i j; rfl

theorem adj_mul {m n p : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) (B : Matrix (Fin n) (Fin p) D.host.E) :
    adj D (A * B) = adj D B * adj D A := by
  simp only [adj_ct, Matrix.conjTranspose_mul]

theorem adj_adjS {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) : adj D (adj D A) = A := by
  simp only [adj_ct, Matrix.conjTranspose_conjTranspose]

theorem adj_gram (V : HSp D) : adj D V.gram = V.gram := by
  ext i j; simp [adj_eq, GlobalTheory.DualPairCheck.gram_star]

theorem adj_one {m : ℕ} : adj D (1 : Matrix (Fin m) (Fin m) D.host.E) = 1 := by
  simp only [adj_ct, Matrix.conjTranspose_one]

theorem adj_zero {m n : ℕ} : adj D (0 : Matrix (Fin m) (Fin n) D.host.E) = 0 := by
  simp only [adj_ct, Matrix.conjTranspose_zero]

theorem frame_decomp (V V' : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E)
    (hCC : adj D C * V.gram * C = 0) (hBB : adj D B * V.gram * B = V'.gram) (hCB : adj D C * V.gram * B = 0)
    (hrk : V.rank = V'.rank + 2 * r)
    (h1 : adj D C * V.gram * C' = 1) (h2 : adj D C' * V.gram * C' = 0) (h3 : adj D C' * V.gram * B = 0) :
    C * (adj D C' * V.gram) + B * (V'.gram⁻¹ * adj D B * V.gram) + C' * (adj D C * V.gram) = 1 := by
  have hdet : IsUnit V'.gram.det := isUnit_iff_ne_zero.2 (GlobalTheory.AutFunCounterexample.gram_det_ne V')

  have h1' : adj D C' * V.gram * C = 1 := by
    have := congrArg (adj D) h1
    rwa [adj_mul, adj_mul, adj_adjS, adj_gram, adj_one, ← Matrix.mul_assoc] at this
  have hBC : adj D B * V.gram * C = 0 := by
    have := congrArg (adj D) hCB
    rwa [adj_mul, adj_mul, adj_adjS, adj_gram, adj_zero, ← Matrix.mul_assoc] at this
  have hBC' : adj D B * V.gram * C' = 0 := by
    have := congrArg (adj D) h3
    rwa [adj_mul, adj_mul, adj_adjS, adj_gram, adj_zero, ← Matrix.mul_assoc] at this
  let P : Matrix (Fin V.rank) (Fin r ⊕ (Fin V'.rank ⊕ Fin r)) D.host.E := Matrix.fromCols C (Matrix.fromCols B C')
  let Q : Matrix (Fin r ⊕ (Fin V'.rank ⊕ Fin r)) (Fin V.rank) D.host.E :=
    Matrix.fromRows (adj D C' * V.gram) (Matrix.fromRows (V'.gram⁻¹ * adj D B * V.gram) (adj D C * V.gram))
  have hPQ : P * Q = C * (adj D C' * V.gram) + B * (V'.gram⁻¹ * adj D B * V.gram) + C' * (adj D C * V.gram) := by
    simp only [P, Q, Matrix.fromCols_mul_fromRows, add_assoc]
  have hQP : Q * P = 1 := by
    simp only [P, Q, Matrix.fromRows_mul_fromCols, Matrix.fromRows_mul, Matrix.mul_fromCols]
    have e1 : V'.gram⁻¹ * adj D B * V.gram * B = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (adj D B), hBB, Matrix.nonsing_inv_mul _ hdet]
    have e2 : V'.gram⁻¹ * adj D B * V.gram * C = 0 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (adj D B), hBC, Matrix.mul_zero]
    have e3 : V'.gram⁻¹ * adj D B * V.gram * C' = 0 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (adj D B), hBC', Matrix.mul_zero]
    rw [h1', h3, h2, e1, e2, e3, hCC, hCB, h1]
    ext (i | i | i) (j | j | j) <;> simp [Matrix.one_apply]
  have hcard : Fintype.card (Fin r ⊕ (Fin V'.rank ⊕ Fin r)) = Fintype.card (Fin V.rank) := by
    simp [hrk]; ring
  rw [← hPQ]
  exact (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hcard.symm)).2 hQP

end GlobalTheory.IsoTermMean

namespace GlobalTheory.IsoTermMean
variable {D : D7}

theorem mt_mul_frame (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) {g : GA D V}
    (hg : g ∈ NI V C) : mt V g * (C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) = C.map (incA D) := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨h1, -, -⟩ := hx
    have h : (mt V x - 1) * (C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) = 0 := h1
    rwa [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
  | one => simp [Formalism.L2.Theta.mt]
  | mul x y _ _ hx hy =>
    have e : mt V (x * y) = mt V x * mt V y := by simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]
    rw [e, Matrix.mul_assoc, hy, hx]
  | inv x _ hx =>
    have e : mt V x⁻¹ * mt V x = 1 := by
      simp only [Formalism.L2.Theta.mt, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    calc mt V x⁻¹ * (C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D))
          = mt V x⁻¹ * (mt V x * (C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D))) := by rw [hx]
      _ = C.map (incA D) := by rw [← Matrix.mul_assoc, e, Matrix.one_mul]

theorem hO_iso (S T : HSp D) {s : ℕ} (L : Matrix (Fin T.rank) (Fin s) D.host.E) (hL : adj D L * T.gram * L = 0)
    (α β : Matrix (Fin s) (Fin S.rank) (AE D)) :
    hO S T ((L.map (incA D) : Matrix (Fin T.rank) (Fin s) (AE D)) * α) ((L.map (incA D) : Matrix (Fin T.rank) (Fin s) (AE D)) * β) = 0 := by
  have hM : (((L.map (incA D) : Matrix (Fin T.rank) (Fin s) (AE D)) * β).map (cA D))ᵀ *
      (T.gram.map (incA D) : Matrix (Fin T.rank) (Fin T.rank) (AE D)) * ((L.map (incA D) : Matrix (Fin T.rank) (Fin s) (AE D)) * α) = 0 := by
    have e1 : ((L.map (incA D) : Matrix (Fin T.rank) (Fin s) (AE D)) * β).map (cA D) =
        ((L.map star).map (incA D) : Matrix (Fin T.rank) (Fin s) (AE D)) * β.map (cA D) := by
      rw [Matrix.map_mul]; congr 1
    have e2 : (((L.map star).map (incA D) : Matrix (Fin T.rank) (Fin s) (AE D)))ᵀ *
        (T.gram.map (incA D) : Matrix (Fin T.rank) (Fin T.rank) (AE D)) * (L.map (incA D) : Matrix (Fin T.rank) (Fin s) (AE D)) =
        ((adj D L * T.gram * L).map (incA D) : Matrix (Fin s) (Fin s) (AE D)) := by
      rw [Matrix.map_mul, Matrix.map_mul, adj_eq, Matrix.transpose_map]
    rw [e1, Matrix.transpose_mul]
    calc _ = (β.map (cA D))ᵀ * ((((L.map star).map (incA D) : Matrix (Fin T.rank) (Fin s) (AE D)))ᵀ *
          (T.gram.map (incA D) : Matrix (Fin T.rank) (Fin T.rank) (AE D)) * (L.map (incA D) : Matrix (Fin T.rank) (Fin s) (AE D))) * α := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [e2, hL, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul]
  have hent : ∀ b a, ∑ c, ∑ d, cA D (((L.map (incA D) : Matrix (Fin T.rank) (Fin s) (AE D)) * β) c b) * incA D (T.gram c d) * ((L.map (incA D) : Matrix (Fin T.rank) (Fin s) (AE D)) * α) d a = 0 := by
    intro b a
    have h := congrFun (congrFun hM b) a
    simp only [Matrix.mul_apply (M := _ * _), Matrix.mul_apply (M := Matrix.transpose _), Matrix.transpose_apply,
      Matrix.map_apply, Matrix.zero_apply, Finset.sum_mul] at h
    rw [Finset.sum_comm]
    exact h
  unfold hO
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  calc _ = incA D (S.gram⁻¹ a b) * ∑ c, ∑ d, cA D (((L.map (incA D) : Matrix (Fin T.rank) (Fin s) (AE D)) * β) c b) * incA D (T.gram c d) *
        ((L.map (incA D) : Matrix (Fin T.rank) (Fin s) (AE D)) * α) d a := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun d _ => ?_
        ring
    _ = 0 := by rw [hent b a, mul_zero]

theorem symplO_iso (S T : HSp D) {s : ℕ} (L : Matrix (Fin T.rank) (Fin s) D.host.E) (hL : adj D L * T.gram * L = 0)
    (α β : Matrix (Fin s) (Fin S.rank) (AE D)) :
    symplO S T ((L.map (incA D) : Matrix (Fin T.rank) (Fin s) (AE D)) * α) ((L.map (incA D) : Matrix (Fin T.rank) (Fin s) (AE D)) * β) = 0 := by
  rw [symplO, hO_iso S T L hL, mul_zero, map_zero]

end GlobalTheory.IsoTermMean

namespace GlobalTheory.IsoTermMean
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
variable {D : D7}

theorem mt_one (V : HSp D) : mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]

theorem mt_mul_inv (V : HSp D) (g : GA D V) : mt V g * mt V g⁻¹ = 1 := by
  simp only [Formalism.L2.Theta.mt, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

end GlobalTheory.IsoTermMean

namespace GlobalTheory.IsoTermMean
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
variable {D : D7}

theorem map_frame_decomp (V V' : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (hs : IsIsoSplit V V' C B) (h1 : adj D C * V.gram * C' = 1)
    (h2 : adj D C' * V.gram * C' = 0) (h3 : adj D C' * V.gram * B = 0) :
    (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) =
      (C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) *
        ((adj D C' * V.gram).map (incA D) : Matrix (Fin r) (Fin V.rank) (AE D)) +
      (B.map (incA D) : Matrix (Fin V.rank) (Fin V'.rank) (AE D)) *
        ((V'.gram⁻¹ * adj D B * V.gram).map (incA D) : Matrix (Fin V'.rank) (Fin V.rank) (AE D)) +
      (C'.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) *
        ((adj D C * V.gram).map (incA D) : Matrix (Fin r) (Fin V.rank) (AE D)) := by
  have e : C * (adj D C' * V.gram) + B * (V'.gram⁻¹ * adj D B * V.gram) + C' * (adj D C * V.gram) = 1 :=
    frame_decomp V V' C C' B hs.frame.2.2 hs.isom hs.orth hs.rank h1 h2 h3
  rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add (incA D)),
    ← Matrix.map_add _ (map_add (incA D)), e, Matrix.map_one _ (map_zero _) (map_one _)]

theorem decomp (V V' W : HSp D) {r s : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E)
    (hI : (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) =
      (C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) *
        ((adj D C' * V.gram).map (incA D) : Matrix (Fin r) (Fin V.rank) (AE D)) +
      (B.map (incA D) : Matrix (Fin V.rank) (Fin V'.rank) (AE D)) *
        ((V'.gram⁻¹ * adj D B * V.gram).map (incA D) : Matrix (Fin V'.rank) (Fin V.rank) (AE D)) +
      (C'.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) *
        ((adj D C * V.gram).map (incA D) : Matrix (Fin r) (Fin V.rank) (AE D)))
    (Lm : Matrix (Fin W.rank) (Fin s) (AE D)) (K : Matrix (Fin s) (Fin V.rank) (AE D))
    (M : Matrix (Fin V.rank) (Fin V.rank) (AE D))
    (hM : (M - 1) * (C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) = 0) :
    (Lm * K * M : WO V W) =
      isoPart V W C (Lm * (K * (M - 1) * (C'.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)))) +
        (midPart V V' W B (Lm * (K * (M - 1) * (B.map (incA D) : Matrix (Fin V.rank) (Fin V'.rank) (AE D)))) +
          Lm * K) := by
  have e : (Lm * K * M : WO V W) = Lm * K + Lm * K * (M - 1) *
      ((C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) *
        ((adj D C' * V.gram).map (incA D) : Matrix (Fin r) (Fin V.rank) (AE D)) +
      (B.map (incA D) : Matrix (Fin V.rank) (Fin V'.rank) (AE D)) *
        ((V'.gram⁻¹ * adj D B * V.gram).map (incA D) : Matrix (Fin V'.rank) (Fin V.rank) (AE D)) +
      (C'.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) *
        ((adj D C * V.gram).map (incA D) : Matrix (Fin r) (Fin V.rank) (AE D))) := by
    rw [← hI, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one]; abel
  rw [e]
  simp only [isoPart, midPart, Matrix.mul_add, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (M - 1) (C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)), hM]
  simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add]
  abel

end GlobalTheory.IsoTermMean

namespace GlobalTheory.IsoTermMean
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
variable {D : D7}

theorem term_eq_aux (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (hs : IsIsoSplit V V' C B) (h1 : adj D C * V.gram * C' = 1)
    (h2 : adj D C' * V.gram * C' = 0) (h3 : adj D C' * V.gram * B = 0)
    (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))
    (hω : IsWeilDatumO ψ V W χS χT ω) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    (hY : IsCovolOne (ratMx D W.rank r) μ 𝓨) (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E)
    (m : Matrix (Fin s) (Fin r) D.host.E) (hL : IsIsoFrame W L) (n : NI V C) (F : WO V W → ℂ)
    (hF : IsThetaFunO ψ V W F) (Lm : Matrix (Fin W.rank) (Fin s) (AE D)) (hLm : Lm = L.map (incA D))
    (K : Matrix (Fin s) (Fin V.rank) (AE D)) (hK : K = (m * adj D C' * V.gram).map (incA D)) :
    res V V' W C B μ 𝓨 (heisO ψ V W (Lm * K) (ω ((n : GA D V), 1) F)) 0 =
      res V V' W C B μ 𝓨 (heisO ψ V W (Lm * K) F)
        (Lm * (K * (mt V (n : GA D V) - 1) * (B.map (incA D) : Matrix (Fin V.rank) (Fin V'.rank) (AE D)))) := by
  have hstd := hω.std
  have hLiso : adj D L * W.gram * L = 0 := hL.2.2
  have hres := (GlobalTheory.T.thetaRestrictIsotropicQuotient_wittTower_properties D V V' W r C B hs ψ hstd μ 𝓨 hY).1
  have hact : actO V W (n : GA D V) 1 (Lm * K * mt V (n : GA D V)) = Lm * K := by
    simp only [actO, mt_one, Matrix.one_mul, Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one]
  have hFu := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hstd hF (Lm * K * mt V (n : GA D V))
  have step1 : heisO ψ V W (Lm * K) (ω ((n : GA D V), 1) F) =
      ω ((n : GA D V), 1) (heisO ψ V W (Lm * K * mt V (n : GA D V)) F) := by
    rw [hω.om_heis (n : GA D V) 1 _ F hF, hact]
  have step2 := GlobalTheory.T.wittTower_restriction_unipotentRadical_invariant D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hY n _ hFu
  have hM : (mt V (n : GA D V) - 1) * (C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) = 0 := by
    rw [Matrix.sub_mul, mt_mul_frame V C n.2, Matrix.one_mul, sub_self]
  have hdec := decomp V V' W C C' B (map_frame_decomp V V' C C' B hs h1 h2 h3) Lm K (mt V (n : GA D V)) hM
  have o1 : symplO V W (isoPart V W C (Lm * (K * (mt V (n : GA D V) - 1) *
      (C'.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)))))
      (midPart V V' W B (Lm * (K * (mt V (n : GA D V) - 1) *
        (B.map (incA D) : Matrix (Fin V.rank) (Fin V'.rank) (AE D)))) + Lm * K) = 0 := by
    simp only [isoPart, midPart, Matrix.mul_assoc, ← Matrix.mul_add]
    rw [hLm]; exact symplO_iso V W L hLiso _ _
  have o2 : symplO V W (midPart V V' W B (Lm * (K * (mt V (n : GA D V) - 1) *
        (B.map (incA D) : Matrix (Fin V.rank) (Fin V'.rank) (AE D))))) (Lm * K) = 0 := by
    simp only [midPart, Matrix.mul_assoc]
    rw [hLm]; exact symplO_iso V W L hLiso _ _
  have hF0 := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hstd hF (Lm * K)
  have hF1 := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hstd hF0 (midPart V V' W B (Lm * (K * (mt V (n : GA D V) - 1) *
        (B.map (incA D) : Matrix (Fin V.rank) (Fin V'.rank) (AE D)))))
  rw [step1, step2, hdec, GlobalTheory.SplitScalar.heisO_add_of_orth ψ V W o1, GlobalTheory.SplitScalar.heisO_add_of_orth ψ V W o2,
    (hres _ hF1).2.2.2, (hres _ hF0).2.2.1]
  simp only [heisO, symplOH, GlobalTheory.SplitScalar.symplO_zero_left, mul_zero, AddChar.map_zero_eq_one, one_mul, zero_add]

end GlobalTheory.IsoTermMean

namespace GlobalTheory.IsoTermMean
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
variable {D : D7}

theorem iso_read_periodic (V' W : HSp D) (ψ : AddChar (AF D.host.F) ℂ) {s : ℕ} (L : Matrix (Fin W.rank) (Fin s) D.host.E)
    (hL : IsIsoFrame W L) (G : WO V' W → ℂ) (hG : IsThetaFunO ψ V' W G) :
    Continuous (fun a : Mx D s V'.rank => G ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) * a)) ∧
    ∀ γ ∈ ratMx D s V'.rank, ∀ a : Mx D s V'.rank,
      G ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) * (γ + a)) =
        G ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) * a) := by
  refine ⟨hG.cont.comp (continuous_const.matrix_mul continuous_id), ?_⟩
  intro γ hγ a
  obtain ⟨γ₀, rfl⟩ := hγ
  have hLiso : adj D L * W.gram * L = 0 := hL.2.2
  have e : ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) *
      ((incA D).toAddMonoidHom.mapMatrix γ₀ : Mx D s V'.rank)) = ratW W V' (L * γ₀) := by
    simp only [ratW, Matrix.map_mul]; rfl
  rw [Matrix.mul_add, e, hG.quasi, symplOH]
  have h0 : symplO V' W (ratW W V' (L * γ₀)) ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) * a) = 0 := by
    rw [← e]; exact symplO_iso V' W L hLiso _ _
  rw [h0, mul_zero, neg_zero, AddChar.map_zero_eq_one, one_mul]

theorem heis_comm_radical (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (hω : IsWeilDatumO ψ V W χS χT ω) {s : ℕ}
    (L : Matrix (Fin W.rank) (Fin s) D.host.E) (K : Matrix (Fin s) (Fin V.rank) (AE D)) (n' : NI W L)
    (f : WO V W → ℂ) (hf : IsThetaFunO ψ V W f) :
    heisO ψ V W ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) * K) (ω (1, (n' : GA D W)) f) =
      ω (1, (n' : GA D W)) (heisO ψ V W ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) * K) f) := by
  rw [hω.om_heis 1 (n' : GA D W) _ f hf]
  congr 1
  simp only [actO, inv_one, mt_one, Matrix.mul_one, ← Matrix.mul_assoc, mt_mul_frame W L n'.2]

theorem mean_isoTerm_invariant : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (κ : Measure (NI V C)) (𝓝 : Set (NI V C)), κ.IsHaarMeasure → IsFundamentalDomain (NIQ V C) 𝓝 κ → ∀ (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E) (m : Matrix (Fin s) (Fin r) D.host.E), IsIsoFrame W L → m.rank = s → ∀ (n' : NI W L) f, IsThetaFunO ψ V W f → ∫ n in 𝓝, res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map (L * m) (incA D))) (ω ((n : GA D V), (n' : GA D W)) f)) 0 ∂κ = ∫ n in 𝓝, res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map (L * m) (incA D))) (ω ((n : GA D V), 1) f)) 0 ∂κ := by
  intro D V V' W r C C' B hs h1 h2 h3 ψ χS χT ω hω μ 𝓨 hY κ 𝓝 hκ h𝓝 s L m hL hm n' f hf
  have hstd := hω.std
  obtain ⟨ω', hω'⟩ := GlobalTheory.T.exists_weilDatum_of_splittingCharacters D ψ hstd V' W χS χT (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hω.hecS
    hω.hecT (Formalism.L2.Theta.resEta_parity hω.resS (by rw [hs.rank]; omega)) hω.resT
  have hcomp := GlobalTheory.T.weilCompatible_of_sameSplittingCharacter D V V' W r C B hs ψ χS χT χT ω ω' hω hω' μ 𝓨 hY
  obtain ⟨μ', 𝓐, hA, hmean⟩ := GlobalTheory.T.unipotentRadicalMean_eq_volume_mul_rationalMean D V V' r C C' B hs h1 h2 h3 κ 𝓝 hκ h𝓝 s m hm
  have hres := (GlobalTheory.T.thetaRestrictIsotropicQuotient_wittTower_properties D V V' W r C B hs ψ hstd μ 𝓨 hY).1
  have hw₀ : isoPart V W C' (Matrix.map (L * m) (incA D)) =
      (L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) *
        ((m * adj D C' * V.gram).map (incA D) : Matrix (Fin s) (Fin V.rank) (AE D)) := by
    simp only [isoPart, Matrix.map_mul, Matrix.mul_assoc]
  rw [hw₀]
  have hsplit : ∀ n : NI V C, ω ((n : GA D V), (n' : GA D W)) f = ω ((n : GA D V), 1) (ω (1, (n' : GA D W)) f) := by
    intro n
    rw [show (((n : GA D V), (n' : GA D W)) : GA D V × GA D W) = ((n : GA D V), 1) * (1, (n' : GA D W)) by simp,
      map_mul, Module.End.mul_apply]
  have hf1 : IsThetaFunO ψ V W (ω (1, (n' : GA D W)) f) := hω.om_pres _ f hf
  have hf0 := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hstd hf ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) *
        ((m * adj D C' * V.gram).map (incA D) : Matrix (Fin s) (Fin V.rank) (AE D)))
  have hG0 := (hres _ hf0).2.1
  have hG1 : res V V' W C B μ 𝓨 (heisO ψ V W ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) *
        ((m * adj D C' * V.gram).map (incA D) : Matrix (Fin s) (Fin V.rank) (AE D))) (ω (1, (n' : GA D W)) f)) =
      ω' (1, (n' : GA D W)) (res V V' W C B μ 𝓨 (heisO ψ V W ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) *
        ((m * adj D C' * V.gram).map (incA D) : Matrix (Fin s) (Fin V.rank) (AE D))) f)) := by
    rw [heis_comm_radical V W ψ χS χT ω hω L _ n' f hf, hcomp _ _ hf0]
  have hG1' := hω'.om_pres (1, (n' : GA D W)) _ hG0
  have p0 := iso_read_periodic V' W ψ L hL _ hG0
  have p1 := iso_read_periodic V' W ψ L hL _ hG1'
  calc _ = ∫ n in 𝓝, ω' (1, (n' : GA D W)) (res V V' W C B μ 𝓨 (heisO ψ V W ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) *
          ((m * adj D C' * V.gram).map (incA D) : Matrix (Fin s) (Fin V.rank) (AE D))) f))
          ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) *
            (((m * adj D C' * V.gram).map (incA D) : Matrix (Fin s) (Fin V.rank) (AE D)) * (mt V (n : GA D V) - 1) *
              (B.map (incA D) : Matrix (Fin V.rank) (Fin V'.rank) (AE D)))) ∂κ := by
        congr 1; funext n
        rw [hsplit n, term_eq_aux V V' W r C C' B hs h1 h2 h3 ψ χS χT ω hω μ 𝓨 hY s L m hL n _ hf1 _ rfl _ rfl, hG1]
    _ = ((κ 𝓝).toReal : ℂ) * ∫ a in 𝓐, ω' (1, (n' : GA D W)) (res V V' W C B μ 𝓨 (heisO ψ V W
          ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) *
          ((m * adj D C' * V.gram).map (incA D) : Matrix (Fin s) (Fin V.rank) (AE D))) f))
          ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) * a) ∂μ' := hmean _ p1.1 p1.2
    _ = ((κ 𝓝).toReal : ℂ) * ∫ a in 𝓐, (res V V' W C B μ 𝓨 (heisO ψ V W
          ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) *
          ((m * adj D C' * V.gram).map (incA D) : Matrix (Fin s) (Fin V.rank) (AE D))) f))
          ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) * a) ∂μ' := by
        rw [GlobalTheory.T.unipotentRadical_target_preserves_isotropic_mean D V' W s L hL ψ χS χT ω' hω' μ' 𝓐 hA n' _ hG0]
    _ = ∫ n in 𝓝, (res V V' W C B μ 𝓨 (heisO ψ V W
          ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) *
          ((m * adj D C' * V.gram).map (incA D) : Matrix (Fin s) (Fin V.rank) (AE D))) f))
          ((L.map (incA D) : Matrix (Fin W.rank) (Fin s) (AE D)) *
            (((m * adj D C' * V.gram).map (incA D) : Matrix (Fin s) (Fin V.rank) (AE D)) * (mt V (n : GA D V) - 1) *
              (B.map (incA D) : Matrix (Fin V.rank) (Fin V'.rank) (AE D)))) ∂κ := (hmean _ p0.1 p0.2).symm
    _ = _ := by
        refine (congrArg (fun φ : NI V C → ℂ => ∫ n in 𝓝, φ n ∂κ) (funext fun n => ?_)).symm
        exact term_eq_aux V V' W r C C' B hs h1 h2 h3 ψ χS χT ω hω μ 𝓨 hY s L m hL n f hf
          (L.map (incA D)) rfl ((m * adj D C' * V.gram).map (incA D)) rfl

end GlobalTheory.IsoTermMean
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicTermMeanInvariantUnipotentRadicalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicTermMean_invariant_unipotentRadical : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (κ : Measure (NI V C)) (𝓝 : Set (NI V C)), κ.IsHaarMeasure → IsFundamentalDomain (NIQ V C) 𝓝 κ → ∀ (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E) (m : Matrix (Fin s) (Fin r) D.host.E), IsIsoFrame W L → m.rank = s → ∀ (n' : NI W L) f, IsThetaFunO ψ V W f → ∫ n in 𝓝, res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map (L * m) (incA D))) (ω ((n : GA D V), (n' : GA D W)) f)) 0 ∂κ = ∫ n in 𝓝, res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map (L * m) (incA D))) (ω ((n : GA D V), 1) f)) 0 ∂κ := by
  first | exact @GlobalTheory.IsoTermMean.mean_isoTerm_invariant | exact GlobalTheory.IsoTermMean.mean_isoTerm_invariant | (intros; apply GlobalTheory.IsoTermMean.mean_isoTerm_invariant <;> assumption)
end
