module

public import Development.WeilBound.ThetaLifts.FrameEstimates.TowerRallisLemma
public import Development.WeilBound.ThetaLifts.FrameEstimates.ThickFrames
public import Development.WeilBound.ThetaLifts.FrameEstimates.IsCompactIntV
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.OrthogonalDecomposition.SigThConst
public import Development.WeilBound.ThetaLifts.FrameEstimates.ContinuousMixedSymm
public import Development.WeilBound.ThetaLifts.FrameEstimates.RankIffRight
public import Development.AutomorphicSpectrum.Proofs.TwistedProofs.EqZeroOfPiInf

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.DomContinuous
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section

variable {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

theorem dom_continuous (hB : ThetaBasic) (hT : GrpTop) (hE : EpsOf) (hp : IsPair B M χX χW om r s r' s') {𝓕}
    (hD : Dom M om 𝓕) {φ} (hφ : φ ∈ 𝓕) (hsb : φ ∈ SB _) (f : SInf F (Fin n × Fin d)) :
    Continuous (M.I om (pureA F f φ)) := by
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  obtain ⟨hJ', -, -⟩ := hE F E σ B hp.base d W r' s' (Or.inr hp.skew)
  obtain ⟨i1, i2, -, -, -, -, -, hb⟩ := hT F E σ hp.base.cm d W.J hJ'
  obtain ⟨p, k, G, -, hG, hfin, hbd⟩ := hD φ hφ
  have hc := ((hB F E σ B n d X W M χX χW om r s r' s' hp).1 _ (pureA_mem f hsb)).1
  haveI : FirstCountableTopology (UA σ W.J) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i2
  refine continuous_iff_continuousAt.2 fun h₀ => ?_
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds h₀
  obtain ⟨C, hC⟩ := hb K hK
  have hpf : 0 ≤ p f := apply_nonneg p f
  refine continuousAt_of_dominated (bound := fun g => p f * (C : ℝ) ^ k * (G g).toReal)
    (Eventually.of_forall fun h => (hc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable) ?_
    ((integrable_toReal_of_lintegral_ne_top hG.aemeasurable hfin.ne).const_mul _)
    (Eventually.of_forall fun g => (hc.comp (continuous_const.prodMk continuous_id)).continuousAt)
  filter_upwards [hK0] with h hh
  filter_upwards [ae_lt_top hG hfin.ne] with g hg
  have e := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg.ne) (hbd f g h)
  rw [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at e
  refine e.trans ?_
  have : (ht h : ℝ) ≤ C := hC h hh
  gcongr

theorem dom_bound (hp : IsPair B M χX χW om r s r' s') {𝓕} (hD : Dom M om 𝓕) {φ} (hφ : φ ∈ 𝓕) :
    ∃ k : ℕ, ∀ f : SInf F (Fin n × Fin d), ∃ C : ℝ, ∀ h, ‖M.I om (pureA F f φ) h‖ ≤ C * (ht h : ℝ) ^ k := by
  obtain ⟨p, k, G, -, hG, hfin, hb⟩ := hD φ hφ
  refine ⟨k, fun f => ⟨p f * (∫⁻ g in M.dom, G g ∂M.μ).toReal, fun h => ?_⟩⟩
  have h1 : ‖M.I om (pureA F f φ) h‖ₑ ≤ ENNReal.ofReal (p f * (ht h : ℝ) ^ k) * ∫⁻ g in M.dom, G g ∂M.μ := by
    rw [← lintegral_const_mul _ hG]
    exact (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun g => hb f g h)
  have e := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne) h1
  rw [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg (apply_nonneg p f) (by positivity))] at e
  exact e.trans (le_of_eq (by ring))

end

theorem iUMG_of (hB : ThetaBasic) (hT : GrpTop) (hE : EpsOf) (hD : IDer) (hL : Level) (hI : IInv) : IUMG := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp 𝓕 hdom φ hφ hsb f hf
  obtain ⟨k, hk⟩ := dom_bound hp hdom hφ
  refine ⟨⟨k, {u | ∃ f₁ ∈ M.Pol B.ψ B.emb, u = M.I om (pureA F f₁ φ)}, ⟨f, hf, rfl⟩, ?_⟩, ?_⟩
  · rintro _ ⟨f₁, hf₁, rfl⟩
    refine ⟨dom_continuous hB hT hE hp hdom hφ hsb f₁, hk f₁, fun γ hγ => ?_⟩
    obtain ⟨f₂, hf₂, -, hd⟩ := (hD F E σ B n d X W M χX χW om r s r' s' hp 𝓕 hdom φ hφ hsb f₁ hf₁).1 γ hγ
    exact ⟨_, ⟨f₂, hf₂, rfl⟩, hd⟩
  · obtain ⟨U, hU, hu⟩ := hL F E σ B n d X W M χX χW om r s r' s' hp φ hsb
    refine ⟨U, hU, fun u huU h1 h => ?_⟩
    rw [← (hI F E σ B n d X W M χX χW om r s r' s' hp _ (pureA_mem f hsb)).2.2 h u, hu u huU h1]

end PositivityTheory.ThKEst

end
end

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.DomWeil
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem domWeilU_of (hT : GrpTop) (hE : EpsOf) (hS : SiegelAll) (hQ : SqAll) (hI : LatInv) (hM : LatMeas) (hK : LatCpt)
    (hA : LatArch) (hL : LatTor) (hP : PosWt) (h2 : ConeIntegralsFinite) : DomWeilU := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp hw
  have hc := hp.base.cm
  obtain ⟨hJ, -, hr⟩ := hE F E σ B hp.base n X r s (Or.inl hp.herm)
  obtain ⟨hJ', -, -⟩ := hE F E σ B hp.base d W r' s' (Or.inr hp.skew)
  obtain ⟨fr, hg, -, -, hint, -⟩ := hS F E σ hc n X.J hJ
  obtain ⟨fr', hg', -, -, -, -⟩ := hS F E σ hc d W.J hJ'
  obtain ⟨N, hN⟩ := hL F E σ hc B.emb n d X.J W.J hJ hJ' fr fr' hg hg'
  obtain ⟨k, hk⟩ := latSum_redH hT hS hI hK hA hc B.emb hJ hJ' N
  refine ⟨k, fun φ hφ => ?_⟩
  obtain ⟨p, C, hpc, hC, hb⟩ := hQ F E σ B n d X W M χX χW om r s r' s' hp φ hφ N
  obtain ⟨C', K, hC', hK0, hb'⟩ := hk C hC
  obtain ⟨K₀, Ω, hK₀, hΩ, hi⟩ := hint M.μ M.dom hp.good.haar hp.good.dom
  obtain ⟨C₁, K₁, hC₁, h₁⟩ := hK F E σ hc B.emb n d X.J W.J hJ hJ' Ω {1} hΩ isCompact_singleton C' N hC'
  obtain ⟨K₂, h₂'⟩ := hN C₁ hC₁
  have ha0 : fr'.a 0 = 1 := by
    have := hg'.add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have h0 : (0 : Fin fr'.r → ℝ) ∈ Cone fr'.r := ⟨fun _ _ _ => le_rfl, fun _ => le_rfl⟩
  have hmeas : Measurable fun g : UA σ X.J => latSum B.emb C' N Set.univ g (1 : UA σ W.J) ^ (1 / 2 : ℝ) :=
    (hM F E σ hc B.emb n d X.J W.J hJ hJ' C' N Set.univ hC' 1).pow_const _
  set D : ℝ := (Module.finrank ℚ E : ℝ) with hD
  have hD0 : 0 < D := by
    rw [hD]; exact_mod_cast Module.finrank_pos
  refine ⟨NNReal.mk K hK0 • p, fun g => latSum B.emb C' N Set.univ g (1 : UA σ W.J) ^ (1 / 2 : ℝ), ?_, hmeas, ?_, ?_⟩
  · exact (continuous_const.mul hpc : Continuous fun f => K * p f)
  · have hq : fr.r = 0 ∨ d + 2 * fr.r < 2 * n := by
      have := hr fr hg
      omega
    have hfin := (h2 n d fr.r 0 D hD0 hq (Or.inl rfl)).1
    set c : ℝ≥0∞ := ((K₁ : ℝ≥0∞) * K₂) ^ (1 / 2 : ℝ) with hcdef
    have hcfin : c < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top)
    have key := hi (fun t => c * ENNReal.ofReal (Real.exp (D * (d / 2 * ∑ i, t i)))) (by fun_prop) _ hmeas
      (fun γ hγ g => by
        have := hI F E σ hc B.emb n d X.J W.J hJ hJ' C' N Set.univ (by simp) γ hγ 1 (one_mem _) g 1
        rw [mul_one] at this
        rw [this])
      (fun t ht' κ hκ => by
        have e1 := h₁ Set.univ (fr.a t) 1 κ hκ 1 rfl
        rw [mul_one] at e1
        have e2 := h₂' t ht' 0 h0
        rw [ha0] at e2
        have e3 : posWt n d t (0 : Fin fr'.r → ℝ) ≤ d * ∑ i, t i := by
          simpa using (hP n d fr.r fr'.r t 0 ht' h0).1
        have e4 : latSum B.emb C' N Set.univ (fr.a t * κ) (1 : UA σ W.J) ≤
            ((K₁ : ℝ≥0∞) * K₂) * ENNReal.ofReal (Real.exp (D * (d / 2 * ∑ i, t i))) ^ (2 : ℝ) := by
          refine e1.trans ?_
          rw [mul_assoc]
          refine mul_le_mul_right (e2.trans (mul_le_mul_right ?_ _)) _
          rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
          nlinarith
        refine (ENNReal.rpow_le_rpow e4 (by norm_num)).trans (le_of_eq ?_)
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
        norm_num [hcdef])
    refine key.trans_lt (ENNReal.mul_lt_top hK₀ ?_)
    simp only [mul_assoc c]
    rw [lintegral_const_mul' _ _ hcfin.ne]
    exact ENNReal.mul_lt_top hcfin hfin
  · intro f g h
    have e := (hb f g h).trans (mul_le_mul_right (hb' g h) _)
    have hpf : 0 ≤ p f := apply_nonneg p f
    have e2 : ‖theta om (pureA F f φ) g h‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal (K * p f * (ht h : ℝ) ^ k) ^ (2 : ℝ) * latSum B.emb C' N Set.univ g (1 : UA σ W.J) := by
      rw [ENNReal.rpow_two, ENNReal.rpow_two]
      refine e.trans (le_of_eq ?_)
      rw [← mul_assoc, ← ENNReal.ofReal_pow hpf, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow (by positivity)]
      congr 2
      ring
    have e3 := ENNReal.rpow_le_rpow e2 (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at e3
    norm_num at e3
    simpa [NNReal.smul_def] using e3

end PositivityTheory.ThKEst

end
end

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.SigRapid
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section

variable {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

theorem exists_soFin (hF : SoFin) (hp : IsPair B M χX χW om r s r' s') {m : ℕ} (φ : Fin m → (Fin n × Fin d → Af F) → ℂ)
    (hφ : ∀ j, φ j ∈ SB _) : ∃ ψ : Fin m → (Fin n × Fin d → Af F) → ℂ, (∀ j, ψ j ∈ soFin B M) ∧
      ∀ w : Fin m → SInf F (Fin n × Fin d), ∑ j, pureA F (w j) (φ j) ∈ M.So B.ψ B.τ₁ →
        ∑ j, pureA F (w j) (φ j) = ∑ j, pureA F (w j) (ψ j) := by
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (soCoeff (B := B) M φ)
  let P := Submodule.linearProjOfIsCompl _ _ hQ
  let ψ : Fin m → (Fin n × Fin d → Af F) → ℂ := fun j => ∑ i, (P (Pi.single j 1) : Fin m → ℂ) i • φ i
  have hψ : ∀ j, ψ j ∈ soFin B M := fun j =>
    ⟨Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hφ i), (P (Pi.single j 1)).2⟩
  have key : ∀ w : Fin m → SInf F (Fin n × Fin d), ∑ j, pureA F (w j) (φ j) ∈ M.So B.ψ B.τ₁ →
      ∑ j, pureA F (w j) (φ j) = ∑ j, pureA F (w j) (ψ j) := fun w hw => by
    obtain ⟨m', f', χ, hχ, e⟩ := (hF F E σ B n d X W M χX χW om r s r' s' hp).1 _ hw
    have hmem : ∀ x, (fun j => w j x) ∈ soCoeff (B := B) M φ := fun x f₀ => by
      have e2 : ∑ j, w j x • φ j = ∑ i, f' i x • χ i := by
        funext y
        obtain ⟨z, hz1, hz2⟩ : ∃ z : Fin n × Fin d → AdeleRing (𝓞 F) F,
            (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1) = x ∧ (fun i => (z i).2) = y :=
          ⟨fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i),
            funext fun i => RingEquiv.apply_symm_apply _ _, rfl⟩
        have := congrFun e z
        simp only [Finset.sum_apply, pureA, hz1, hz2] at this
        simpa [Finset.sum_apply] using this
      have e3 : pureA F f₀ (∑ i, f' i x • χ i) = ∑ i, f' i x • pureA F f₀ (χ i) := by
        funext z; simp [pureA, Finset.mul_sum, Finset.sum_apply]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [e2, e3]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ((hχ i).2 f₀)
    funext z
    set x : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1
    have e4 : (fun j => w j x) = ∑ j, w j x • (P (Pi.single j 1) : Fin m → ℂ) := by
      have a1 : (P (fun j => w j x) : Fin m → ℂ) = fun j => w j x :=
        congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hQ ⟨_, hmem x⟩)
      have a2 : (fun j => w j x) = ∑ j, w j x • (Pi.single j 1 : Fin m → ℂ) := by
        funext i; simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [← a1, a2]
      simp
    have e5 : ∀ i, w i x = ∑ j, w j x * (P (Pi.single j 1) : Fin m → ℂ) i := fun i => by
      simpa [Finset.sum_apply] using congrFun e4 i
    simp only [Finset.sum_apply, pureA, ψ, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show w i (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1) = _ from e5 i, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _
  exact ⟨ψ, hψ, key⟩

theorem polData_sum (hp : IsPair B M χX χW om r s r' s') {Φ : Fn F n d} (hΦ : Φ ∈ PolData B M) :
    ∃ (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → (Fin n × Fin d → Af F) → ℂ),
      (∀ i, f i ∈ M.Pol B.ψ B.emb) ∧ (∀ i, φ i ∈ SB _) ∧ Φ = ∑ i, pureA F (f i) (φ i) := by
  obtain ⟨m, c, x, rfl⟩ := Submodule.mem_span_set'.1 hΦ
  choose f hf χ h1 h2 h3 using fun i => (x i).2
  refine ⟨m, fun i => c i • f i, fun i => FiniteAdelicSupportCompactness.pf (χ i), fun i => Submodule.smul_mem _ _ (hf i),
    fun i => FiniteAdelicSupportCompactness.pf_mem ⟨h1 i, ((h2 i).and hp.good.std).mono fun v hv => hv.1.trans hv.2⟩,
    Finset.sum_congr rfl fun i _ => ?_⟩
  rw [h3 i, FiniteAdelicSupportCompactness.pure_eq]
  funext z
  simp [pureA, mul_assoc]


variable (B W) in
def Nice (f : UA σ W.J → ℂ) : Prop := LeftInv f ∧ UMG W f ∧ SmoothFin W B.emb f

theorem nice_zero : Nice B W (0 : UA σ W.J → ℂ) :=
  ⟨fun _ _ _ => rfl, ⟨0, {0}, rfl, by
    rintro _ rfl
    exact ⟨continuous_const, ⟨0, fun h => by simp⟩, fun γ _ => ⟨0, rfl, fun h => hasDerivAt_const _ _⟩⟩⟩,
    Set.univ, univ_mem, fun _ _ _ _ => rfl⟩

theorem Nice.lin (hU : UMGLin) (hc : IsCMExt F E σ) (hJ : EpsHerm σ W.J) {f f' : UA σ W.J → ℂ} (h : Nice B W f)
    (h' : Nice B W f') (a b : ℂ) : Nice B W (a • f + b • f') := by
  refine ⟨fun γ hγ x => ?_, hU F E σ hc B.emb d W hJ f f' h.2.1 h'.2.1 a b, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, h.1 γ hγ x, h'.1 γ hγ x]
  · obtain ⟨U, hU1, hu⟩ := h.2.2
    obtain ⟨U', hU1', hu'⟩ := h'.2.2
    refine ⟨U ∩ U', inter_mem hU1 hU1', fun u hm h1 x => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, hu u hm.1 h1 x, hu' u hm.2 h1 x]

theorem nice_sum (hB : ThetaBasic) (hU : UMGLin) (hE : EpsOf) (hG : IUMG) (hI : IInv) (hp : IsPair B M χX χW om r s r' s')
    {𝓕} (hD : Dom M om 𝓕) {m : ℕ} (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → (Fin n × Fin d → Af F) → ℂ)
    (hf : ∀ i, f i ∈ M.Pol B.ψ B.emb) (hφ : ∀ i, φ i ∈ 𝓕) (hsb : ∀ i, φ i ∈ SB _) :
    Nice B W (M.I om (∑ i, pureA F (f i) (φ i))) := by
  obtain ⟨hJ, -, -⟩ := hE F E σ B hp.base d W r' s' (Or.inr hp.skew)
  have e : M.I om (∑ i, pureA F (f i) (φ i)) = ∑ i, M.I om (pureA F (f i) (φ i)) :=
    funext fun h => ((dom_sum hB hp hD f φ hφ hsb).2.2 h).trans (Finset.sum_apply _ _ _).symm
  rw [e]
  refine Finset.sum_induction _ _ (fun a b ha hb => by simpa using ha.lin hU hp.base.cm hJ hb 1 1) nice_zero fun i _ => ?_
  exact ⟨(hI F E σ B n d X W M χX χW om r s r' s' hp _ (pureA_mem _ (hsb i))).1,
    hG F E σ B n d X W M χX χW om r s r' s' hp 𝓕 hD _ (hφ i) (hsb i) _ (hf i)⟩

end

theorem sig_nice (hB : ThetaBasic) (hU : UMGLin) (hE : EpsOf) (hG : IUMG) (hI : IInv) (hT : TriplePair) (hW : DomWeil)
    (hS : DomSoU) (hF : SoFin) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (ht' : IsTriple B G X om om') {f : UA σ G.W.J → ℂ} (hf : f ∈ PositivityTheory.ThKEnd.Sig B G om om') :
    Nice B G.W f := by
  obtain ⟨h1, h2, h3⟩ := hT F E σ B a a' G X om om' ht'
  obtain ⟨Φ, hΦ, Φ', hΦ', rfl⟩ := hf
  obtain ⟨hJ, -, -⟩ := hE F E σ B h1.base _ G.W _ _ (Or.inr h1.skew)
  obtain ⟨m, f, φ, c1, c2, rfl⟩ := polData_sum h1 hΦ
  obtain ⟨m', f', φ', c1', c2', rfl⟩ := polData_sum h2 hΦ'.1
  obtain ⟨ψ, hψ, hk⟩ := exists_soFin hF h2 φ' c2'
  rw [hk f' hΦ'.2]
  have n1 := nice_sum hB hU hE hG hI h1 (hW F E σ B _ _ _ _ _ _ _ om _ _ _ _ h1 (Or.inl h3)) f φ c1 c2 c2
  have n2 := nice_sum hB hU hE hG hI h2 (dom_of_domSoU hS h2) f' ψ c1' hψ fun i => (hψ i).1
  simpa [sub_eq_add_neg] using n1.lin hU h1.base.cm hJ n2 1 (-1)

theorem sigRapid_of (hB : ThetaBasic) (hU : UMGLin) (hE : EpsOf) (hG : IUMG) (hI : IInv) (hT : TriplePair) (hW : DomWeil)
    (hS : DomSoU) (hF : SoFin) (hC : CuspRapid) : PositivityTheory.ThKEnd.Orth.SigRapid := by
  intro F E _ _ _ _ _ σ B a a' G X om om' ht' f hf hc
  obtain ⟨n1, n2, n3⟩ := sig_nice hB hU hE hG hI hT hW hS hF ht' hf
  obtain ⟨h1, -, -⟩ := hT F E σ B a a' G X om om' ht'
  obtain ⟨hJ, -, -⟩ := hE F E σ B h1.base _ G.W _ _ (Or.inr h1.skew)
  refine ⟨?_, n1, hC F E σ h1.base.cm B.emb _ G.W hJ f n1 n2 n3 hc⟩
  obtain ⟨k, S, hS1, hS2⟩ := n2
  exact (hS2 f hS1).1

end PositivityTheory.ThKEst

end
end

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.ThetaSumNeg
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section

variable {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

theorem sq_iff {a P L : ℝ≥0∞} : a ^ 2 ≤ P ^ 2 * L ↔ a ≤ P * L ^ (1 / 2 : ℝ) := by
  have e : L = (L ^ (1 / 2 : ℝ)) ^ 2 := by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]; norm_num
  conv_lhs => rw [e, ← mul_pow]
  exact ⟨fun h => (ENNReal.pow_le_pow_left_iff two_ne_zero).1 h, fun h => by gcongr⟩

theorem latSum_mono {τ : ∀ w : InfinitePlace F, EmbOver E w} {C C' : Set (Ten F E n d)} (hC : C ⊆ C') (N : ℕ) (S)
    (g : UA σ X.J) (h : UA σ W.J) : latSum τ C N S g h ≤ latSum τ C' N S g h := by
  refine ENNReal.tsum_le_tsum fun x => ENNReal.ofReal_le_ofReal ?_
  by_cases hx : ∃ c ∈ C, At (evI F) (mat g⁻¹ * incM F x.1 * (mat h⁻¹)ᵀ - c)
  · obtain ⟨c, h1, h2⟩ := hx
    unfold maj
    rw [if_pos ⟨c, h1, h2⟩, if_pos ⟨c, hC h1, h2⟩]
  · conv_lhs => unfold maj
    rw [if_neg hx]
    exact sq_maj_nonneg _ _ _ _


variable (B om) in
def Qb (N : ℕ) (Φ : SInf F (Fin n × Fin d) → Fn F n d) : Prop :=
  (∀ f, Φ f ∈ schA F (Fin n × Fin d)) ∧ ∃ (p : Seminorm ℂ (SInf F (Fin n × Fin d))) (C : Set (Ten F E n d)), Continuous p ∧
    IsCompact C ∧ ∀ f g h, ‖theta om (Φ f) g h‖ₑ ^ 2 ≤ ENNReal.ofReal (p f) ^ 2 * latSum B.emb C N (fullRank E n d) g h

theorem qb_zero (N : ℕ) : Qb B om N fun _ => 0 :=
  ⟨fun _ => zero_mem _, 0, ∅, continuous_const, isCompact_empty, fun f g h => by simp [theta, thetaSum]⟩

theorem Qb.add (hp : IsPair B M χX χW om r s r' s') {N : ℕ} {Φ Ψ : SInf F (Fin n × Fin d) → Fn F n d} (h1 : Qb B om N Φ)
    (h2 : Qb B om N Ψ) : Qb B om N fun f => Φ f + Ψ f := by
  obtain ⟨a1, p, C, b1, c1, d1⟩ := h1
  obtain ⟨a2, q, C', b2, c2, d2⟩ := h2
  refine ⟨fun f => add_mem (a1 f) (a2 f), p + q, C ∪ C', (b1.add b2 : Continuous fun f => p f + q f), c1.union c2,
    fun f g h => sq_iff.2 ?_⟩
  have e1 := sq_iff.1 ((d1 f g h).trans (mul_le_mul_right (latSum_mono (C' := C ∪ C') Set.subset_union_left N _ g h) _))
  have e2 := sq_iff.1 ((d2 f g h).trans (mul_le_mul_right (latSum_mono (C' := C ∪ C') Set.subset_union_right N _ g h) _))
  rw [theta_add hp (a1 f) (a2 f), Seminorm.add_apply, ENNReal.ofReal_add (apply_nonneg p f) (apply_nonneg q f), add_mul]
  exact (enorm_add_le _ _).trans (add_le_add e1 e2)

theorem Qb.smul (hp : IsPair B M χX χW om r s r' s') {N : ℕ} {Φ : SInf F (Fin n × Fin d) → Fn F n d} (h1 : Qb B om N Φ)
    (c : ℂ) : Qb B om N fun f => c • Φ f := by
  obtain ⟨a1, p, C, b1, c1, d1⟩ := h1
  refine ⟨fun f => Submodule.smul_mem _ _ (a1 f), ‖c‖₊ • p, C, (continuous_const.mul b1 : Continuous fun f => ‖c‖ * p f), c1,
    fun f g h => sq_iff.2 ?_⟩
  have e1 := sq_iff.1 (d1 f g h)
  rw [theta_smul hp c (a1 f), enorm_mul, show (‖c‖₊ • p) f = ‖c‖ * p f from rfl, ENNReal.ofReal_mul (norm_nonneg c),
    ofReal_norm, mul_assoc]
  exact mul_le_mul_right e1 _

theorem qb_sum (hp : IsPair B M χX χW om r s r' s') {N : ℕ} {ι : Type} (S : Finset ι)
    {Φ : ι → SInf F (Fin n × Fin d) → Fn F n d} (h : ∀ i, Qb B om N (Φ i)) : Qb B om N fun f => ∑ i ∈ S, Φ i f := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using qb_zero N
  | insert a S ha ih => simpa [Finset.sum_insert ha] using (h a).add hp ih

theorem thetaSum_neg {κ : Type} (Φ : (κ → AF F) → ℂ) : thetaSum F (fun x => Φ (-x)) = thetaSum F Φ := by
  unfold thetaSum
  rw [← (Equiv.neg (κ → F)).tsum_eq]
  refine tsum_congr fun ξ => congrArg Φ (funext fun i => ?_)
  simp

theorem theta_neg (hP : Parity) (hp : IsPair B M χX χW om r s r' s') {Φ : Fn F n d} (hΦ : Φ ∈ schA F _) (g h) :
    theta om (fun x => Φ (-x)) g h = theta om Φ g h := by
  obtain ⟨e, c, he, hc, h1⟩ := hP F E σ B n d X W M χX χW om r s r' s' hp
  have hc0 : c ≠ 0 := fun h0 => by simp [h0] at hc
  have hs := (IsUWeilPair.isUSplitting hp.weil).pres (g, h) Φ hΦ
  have hcomm : g * e = e * g := Subtype.ext (Units.ext (by
    change mat g * mat e = mat e * mat g
    rw [he]; simp))
  have e1 : om (g, h) (om (e, 1) Φ) = om (e, 1) (om (g, h) Φ) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, hcomm, mul_one,
      one_mul]
  rw [h1 Φ hΦ, h1 _ hs, map_smul] at e1
  unfold theta
  rw [smul_right_injective _ hc0 e1, thetaSum_neg]


set_option maxHeartbeats 800000 in
open scoped Classical in
theorem qb_piece (hP : Parity) (hS : CoefSum) (hE : CoefEq) (hB : CoefBd) (hp : IsPair B M χX χW om r s r' s') (N : ℕ)
    {φ : (Fin n × Fin d → Af F) → ℂ} (hφ : φ ∈ SB _)
    (h0 : ∀ (f : SInf F (Fin n × Fin d)) (μ : Measure (Fin n × Fin d → AF F)), μ.IsAddHaarMeasure → ∀ z : Ten F E n d,
      (z.map (piW (B.τ₁.comp σ))).rank ≠ n → coef F B.ψ μ (pureA F f φ) (fun x => pureA F f φ (-x)) (M.co.e z) = 0) :
    Qb B om N fun f => pureA F f φ := by
  obtain ⟨μ, hμ, -⟩ := ParityOfCoefficients.exists_haar (F := F) (κ := Fin n × Fin d)
  obtain ⟨c, hc, h1⟩ := theta_mul_le hS hE hp μ hμ
  have hφ' : (fun y => φ (-y)) ∈ SB (Fin n × Fin d → Af F) :=
    ⟨hφ.1.comp_continuous continuous_neg, hφ.2.comp_homeomorph (Homeomorph.neg _)⟩
  obtain ⟨p, C, hpc, hC, h2⟩ := hB F E σ B n d X W M χX χW om r s r' s' hp μ hμ φ hφ _ hφ' N
  let P : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ)
  have hPf : ∀ f : SInf F (Fin n × Fin d), (fun x => pureA F f φ (-x)) = pureA F (P f) fun y => φ (-y) := fun f => by
    funext x
    unfold pureA
    congr 1
    exact congrArg f (funext fun i => map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x i).1)
  let q : Seminorm ℂ (SInf F (Fin n × Fin d)) := p + p.comp P.toLinearMap
  have hq : Continuous q := (hpc.add (hpc.comp P.continuous) : Continuous fun f => p f + p (P f))
  refine ⟨fun f => pureA_mem f hφ, NNReal.mk √c (Real.sqrt_nonneg c) • q, C,
    (continuous_const.mul hq : Continuous fun f => √c * q f), hC, fun f g h => ?_⟩
  have hm := pureA_mem f hφ
  have e := h1 _ hm _ (ParityOfCoefficients.neg_mem_schA hm) g h
  rw [theta_neg hP hp hm] at e
  refine sq_le_of_coef hc (apply_nonneg q f) e (fun x hx => h0 f μ hμ _ fun hr => hx ?_) fun x => ?_
  · rw [Matrix.map_mul, Matrix.map_mul, ThKEst.W.incM_piW] at hr
    have hr2 := ThKEst.W.rank_of_mul _ _ _ hr
    exact ThKEst.W.rank_of_map (B.τ₁.comp σ).toRingHom x hr2
  · rw [hPf]
    refine (h2 f (P f) _).trans (mul_le_mul_of_nonneg_right ?_ (sq_maj_nonneg _ _ _ _))
    have a1 := apply_nonneg p f
    have a2 := apply_nonneg p (P f)
    change p f * p (P f) ≤ (p f + p (P f)) * (p f + p (P f))
    nlinarith

end

theorem sqSo_of' (hF : SoFin) (hC : SoCut) (hP : Parity) (hS : CoefSum) (hE : CoefEq) (hB : CoefBd) : SqSo := by
  classical
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp φ hφ N
  obtain ⟨m, c, χ, hχ, e⟩ := (hF F E σ B n d X W M χX χW om r s r' s' hp).2.2.2 φ hφ
  have key : Qb B om N fun f => ∑ i, c i • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (χ i) := qb_sum hp _ fun i => Qb.smul hp (c := c i) <| by
    obtain ⟨k, ξ, e1, hξ⟩ := hC F E σ B n d X W M χX χW om r s r' s' hp _ (hχ i).2.2
    have hstd : ∀ᶠ u in cofinite, χ i u = ThKEst.W.stdF _ u := ((hχ i).2.1.and hp.good.std).mono fun v hv => hv.1.trans hv.2
    have hg : ThKEst.W.Good (χ i) := ⟨(hχ i).1, hstd⟩
    have e2 : (fun f : SInf F (Fin n × Fin d) => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (χ i)) =
        fun f : SInf F (Fin n × Fin d) => ∑ j, pureA F f (ThKEst.W.pf (Function.update (χ i) B.v₁ (ξ j))) := funext fun f => by
      conv_lhs => rw [← Function.update_eq_self B.v₁ (χ i), ThKEst.W.pure_update (v := B.v₁) f hstd, e1]
      have e3 : ∀ j, pureA F f (ThKEst.W.pf (Function.update (χ i) B.v₁ (ξ j))) =
          tens (evFin F B.v₁) (ξ j) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update (χ i) B.v₁ 1)) := fun j =>
        ThKEst.W.pure_update (v := B.v₁) f hstd (ξ j)
      rw [Finset.sum_congr rfl fun j _ => e3 j]
      funext x
      rw [Finset.sum_apply]
      unfold tens
      rw [Finset.sum_apply, Finset.sum_mul]
    rw [e2]
    refine qb_sum hp _ fun j => qb_piece hP hS hE hB hp N (ThKEst.W.pf_mem (hg.update (hξ j).1.1)) fun f μ hμ z hz => ?_
    rw [← ThKEst.W.pure_eq, ThKEst.W.pure_update (v := B.v₁) f hstd]
    refine (hξ j).2 _ ⟨fun x z hz => ?_, ?_⟩ μ hμ z hz
    · have h1 := (ThKEst.W.at_iff (v := B.v₁) z).1 hz
      have h2 : z = fun i => GlobalTheory.EmbChart.atPlace B.v₁ (evFin F B.v₁ (z i)) := funext fun i =>
        (congrFun h1 i).symm.trans (ThKEst.W.ep_mul (v := B.v₁) (z i))
      rw [h2]
      exact ThKEst.W.indep_pure (v := B.v₁) f (χ i) x _
    · rw [← ThKEst.W.pure_update (v := B.v₁) f hstd]
      exact ThKEst.W.pure_mem f (hg.update (hξ j).1.1)
  obtain ⟨-, p, C, h1, h2, h3⟩ := key
  exact ⟨p, C, h1, h2, fun f g h => by rw [e f]; exact h3 f g h⟩

end PositivityTheory.ThKEst

end
end

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.LineGen
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace ExponentialLineGeneration

set_option linter.unusedSectionVars false

section Banach

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem exists_deriv {g : ℝ → A} (hc : Continuous g) (h0 : g 0 = 1) (ha : ∀ s t, g (s + t) = g s * g t) :
    ∃ Y : A, ∀ t, HasDerivAt g (g t * Y) t := by
  let G : ℝ → A := fun t => ∫ s in (0 : ℝ)..t, g s
  have hG : ∀ t, HasDerivAt G (g t) t := fun t => (hc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hG0 : G 0 = 0 := intervalIntegral.integral_same
  have h1 : Tendsto (slope G 0) (𝓝[≠] 0) (𝓝 1) := by
    have := hasDerivAt_iff_tendsto_slope.1 (hG 0)
    rwa [h0] at this
  have h2 : ∀ᶠ h in 𝓝[≠] (0 : ℝ), IsUnit (slope G 0 h) := h1 (Units.isOpen.mem_nhds isUnit_one)
  obtain ⟨h, hu, hne⟩ := (h2.and self_mem_nhdsWithin).exists
  have hne' : h ≠ 0 := hne
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  rw [slope_def_module, hG0, sub_zero, sub_zero] at hv
  have hv' : G h * (h⁻¹ • v) = 1 := by rw [mul_smul_comm, ← smul_mul_assoc, hv]
  set u := h⁻¹ • v
  have key : ∀ t, g t * G h = G (t + h) - G t := by
    intro t
    have e1 : g t * G h = ∫ s in (0 : ℝ)..h, g (t + s) := by
      simp only [ha]
      exact ((ContinuousLinearMap.mul ℝ A (g t)).intervalIntegral_comp_comm (hc.intervalIntegrable 0 h)).symm
    rw [e1, intervalIntegral.integral_comp_add_left, add_zero]
    exact (intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)).symm
  have e : g = fun t => (G (t + h) - G t) * u := by
    funext t
    rw [← key, mul_assoc, hv', mul_one]
  refine ⟨(g h - 1) * u, fun t => ?_⟩
  have d := (((hG (t + h)).comp_add_const t h).sub (hG t)).mul_const u
  have e2 : g t * ((g h - 1) * u) = (g (t + h) - g t) * u := by
    rw [← mul_assoc, mul_sub, mul_one, ha]
  rw [e2]
  exact d.congr_of_eventuallyEq (Eventually.of_forall fun s => congrFun e s)

theorem exists_exp {g : ℝ → A} (hc : Continuous g) (h0 : g 0 = 1) (ha : ∀ s t, g (s + t) = g s * g t) :
    ∃ Y : A, HasDerivAt g Y 0 ∧ ∀ t, g t = NormedSpace.exp (t • Y) := by
  obtain ⟨Y, hY⟩ := exists_deriv hc h0 ha
  refine ⟨Y, by simpa [h0] using hY 0, fun t => ?_⟩
  have d : ∀ s : ℝ, HasDerivAt (fun s : ℝ => g s * NormedSpace.exp ((t - s) • Y)) 0 s := by
    intro s
    have d1 := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) Y (t - s)).scomp s ((hasDerivAt_id s).const_sub t)
    have d2 := (hY s).mul d1
    refine d2.congr_deriv ?_
    simp [mul_assoc]
  have c := is_const_of_deriv_eq_zero (fun s => (d s).differentiableAt) (fun s => (d s).deriv) t 0
  simpa [h0] using c

end Banach

set_option backward.isDefEq.respectTransparency false in
theorem mat_exp {d : ℕ} {g : ℝ → Matrix (Fin d) (Fin d) ℂ} (hc : Continuous g) (h0 : g 0 = 1)
    (ha : ∀ s t, g (s + t) = g s * g t) :
    ∃ Y : Matrix (Fin d) (Fin d) ℂ, (∀ i j, HasDerivAt (fun t => g t i j) (Y i j) 0) ∧
      ∀ t : ℝ, g t = NormedSpace.exp ((t : ℂ) • Y) := by
  open scoped Matrix.Norms.Operator in
  obtain ⟨Y, h1, h2⟩ := exists_exp (A := Matrix (Fin d) (Fin d) ℂ) hc h0 ha
  refine ⟨Y, fun i j => ?_, fun t => ?_⟩
  · exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j :
      Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ] ℂ)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  · rw [h2 t, Complex.coe_smul]

theorem lie_of_unitary {d : ℕ} {g : ℝ → Matrix (Fin d) (Fin d) ℂ} {J Y : Matrix (Fin d) (Fin d) ℂ} (h0 : g 0 = 1)
    (hd : ∀ i j, HasDerivAt (fun t => g t i j) (Y i j) 0) (hu : ∀ t, (g t)ᵀ * J * (g t).map star = J) :
    Yᵀ * J + J * Y.map star = 0 := by
  ext i j
  have d1 : HasDerivAt (fun t => ∑ l, (∑ k, g t k i * J k l) * star (g t l j))
      (∑ l, ((∑ k, Y k i * J k l) * star (g 0 l j) + (∑ k, g 0 k i * J k l) * star (Y l j))) 0 :=
    HasDerivAt.fun_sum fun l _ => (HasDerivAt.fun_sum fun k _ => (hd k i).mul_const (J k l)).fun_mul (hd l j).star
  have e : (fun t => ∑ l, (∑ k, g t k i * J k l) * star (g t l j)) = fun _ => J i j := by
    funext t
    rw [← congrFun (congrFun (hu t) i) j]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [e] at d1
  have z := d1.unique (hasDerivAt_const (0 : ℝ) (J i j))
  have e1 : (Yᵀ * J * (g 0).map star + (g 0)ᵀ * J * Y.map star) i j = 0 := by
    rw [← z, Finset.sum_add_distrib]
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rwa [h0, Matrix.map_one _ (star_zero _) (star_one _), Matrix.mul_one, Matrix.transpose_one, Matrix.one_mul] at e1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem piInf_tmul' {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) (x : E) :
    piInf τ (a ⊗ₜ[F] x) = InfinitePlace.Completion.extensionEmbedding w (a.1 w) * τ.1 x := by
  change infEmb τ (evInf F w a ⊗ₜ[F] x) = _
  rw [infEmb_tmul]
  rfl

theorem continuous_piInf {w : InfinitePlace F} (τ : EmbOver E w) : Continuous (piInf τ) := by
  refine IsModuleTopology.continuous_of_ringHom (R := AF F) (piInf τ) ?_
  have h : ⇑((piInf τ).comp (algebraMap (AF F) (AE F E))) =
      fun a : AF F => InfinitePlace.Completion.extensionEmbedding w (a.1 w) := by
    funext a
    change piInf τ (a ⊗ₜ[F] (1 : E)) = _
    rw [piInf_tmul', map_one, mul_one]
  rw [h]
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
    ((continuous_apply w).comp continuous_fst)

theorem piInf_cA (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E) :
    piInf τ (cA σ z) = star (piInf τ z) := by
  have hw : w.IsReal := h.1.isReal w
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, star_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, star_add]
  | tmul a x =>
    change piInf τ (a ⊗ₜ[F] σ x) = _
    rw [piInf_tmul', piInf_tmul', h.2.2.2, star_mul',
      ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw]
    rw [Complex.star_def, Complex.conj_ofReal]

theorem map_incM {w : InfinitePlace F} (τ : EmbOver E w) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  exact (piInf_tmul' τ 1 (J i j)).trans (by rw [show (1 : AF F).1 w = 1 from rfl, map_one, one_mul]; rfl)

end ExponentialLineGeneration

open ExponentialLineGeneration in
theorem lineGen_of : LineGen := by
  intro F E _ _ _ _ _ σ h τ d W _ γ hγ
  have main : ∀ w, ∃ Y : Matrix (Fin d) (Fin d) ℂ,
      Yᵀ * W.J.map (τ w).1 + W.J.map (τ w).1 * Y.map star = 0 ∧
      ∀ t : ℝ, (mat (γ (Multiplicative.ofAdd t))).map (piInf (τ w)) = NormedSpace.exp ((t : ℂ) • Y) := by
    intro w
    let g : ℝ → Matrix (Fin d) (Fin d) ℂ := fun t => (mat (γ (Multiplicative.ofAdd t))).map (piInf (τ w))
    have hm : Continuous (mat : UA σ W.J → Matrix (Fin d) (Fin d) (AE F E)) :=
      Units.continuous_val.comp continuous_subtype_val
    have hc : Continuous g :=
      ((hm.comp (hγ.1.comp continuous_ofAdd))).matrix_map (continuous_piInf (τ w))
    have h0 : g 0 = 1 := by
      change (mat (γ 1)).map (piInf (τ w)) = 1
      rw [map_one]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have ha : ∀ s t, g (s + t) = g s * g t := by
      intro s t
      change (mat (γ (Multiplicative.ofAdd s * Multiplicative.ofAdd t))).map (piInf (τ w)) = _
      rw [map_mul]
      exact Matrix.map_mul
    obtain ⟨Y, h1, h2⟩ := mat_exp hc h0 ha
    refine ⟨Y, lie_of_unitary h0 h1 fun t => ?_, h2⟩
    have hu : (mat (γ (Multiplicative.ofAdd t)))ᵀ * incM F W.J * (mat (γ (Multiplicative.ofAdd t))).map (cA σ) =
        incM F W.J := (γ (Multiplicative.ofAdd t)).2
    have e : ((mat (γ (Multiplicative.ofAdd t))).map (cA σ)).map (piInf (τ w)) = (g t).map star := by
      ext i j
      exact piInf_cA h _ _
    have hv := congrArg (fun M : Matrix (Fin d) (Fin d) (AE F E) => M.map (piInf (τ w))) hu
    simp only [Matrix.map_mul] at hv
    rwa [Matrix.transpose_map, map_incM, e] at hv
  choose Y hY using main
  exact ⟨Y, fun w => (hY w).1, fun w => (hY w).2⟩

end PositivityTheory.ThKEst

end
end

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.LineEx
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace ExponentialLineExistence

open GlobalTheory.CompanionTheory.CMAdele

section Cx

variable {d : ℕ}

theorem exp_line_add (Y : Matrix (Fin d) (Fin d) ℂ) (s t : ℝ) :
    NormedSpace.exp (((s + t : ℝ) : ℂ) • Y) = NormedSpace.exp ((s : ℂ) • Y) * NormedSpace.exp ((t : ℂ) • Y) := by
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left _).smul_right _), Complex.ofReal_add, add_smul]

theorem exp_map_star (A : Matrix (Fin d) (Fin d) ℂ) :
    (NormedSpace.exp A).map star = NormedSpace.exp (A.map star) := by
  have e : ∀ B : Matrix (Fin d) (Fin d) ℂ, B.map star = Bᴴᵀ := fun B => rfl
  rw [e, e, Matrix.exp_transpose, Matrix.exp_conjTranspose]

set_option backward.isDefEq.respectTransparency false in
theorem exp_semiconj {J A B : Matrix (Fin d) (Fin d) ℂ} (h : SemiconjBy J A B) :
    NormedSpace.exp (-B) * J * NormedSpace.exp A = J :=
  open scoped Matrix.Norms.Operator in h.exp_neg_mul_mul_exp_eq_self

set_option backward.isDefEq.respectTransparency false in
theorem continuous_exp_mat : Continuous (NormedSpace.exp : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ) :=
  open scoped Matrix.Norms.Operator in NormedSpace.exp_continuous

theorem exp_unitary {J Y : Matrix (Fin d) (Fin d) ℂ} (h : Yᵀ * J + J * Y.map star = 0) (t : ℝ) :
    (NormedSpace.exp ((t : ℂ) • Y))ᵀ * J * (NormedSpace.exp ((t : ℂ) • Y)).map star = J := by
  have h1 : SemiconjBy J (((t : ℂ) • Y).map star) (-((t : ℂ) • Y)ᵀ) := by
    have e : ((t : ℂ) • Y).map star = (t : ℂ) • Y.map star := by
      ext i j
      simp
    rw [SemiconjBy, e, Matrix.transpose_smul, Matrix.mul_smul, neg_mul, Matrix.smul_mul, ← smul_neg,
      eq_neg_of_add_eq_zero_right h]
  have h2 := exp_semiconj h1
  rwa [neg_neg, Matrix.exp_transpose, ← exp_map_star] at h2

end Cx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem piInf_cA (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E) :
    piInf τ (cA σ z) = star (piInf τ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, star_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, star_add]
  | tmul a x =>
    change piInf τ (a ⊗ₜ[F] σ x) = _
    rw [piInf_tmul, piInf_tmul, h.2.2.2, star_mul', show star (InfinitePlace.Completion.extensionEmbedding w (a.1 w)) = _ from
      Complex.conj_eq_iff_im.2 (im_extension h.1 w _)]

theorem map_incM {w : InfinitePlace F} (τ : EmbOver E w) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  exact (piInf_tmul τ 1 (J i j)).trans (by rw [show (1 : AF F).1 w = 1 from rfl, map_one, one_mul]; rfl)

theorem continuous_realAd : Continuous (realAd F) := by
  refine Continuous.prodMk (f := fun t => (realAd F t).1) (g := fun _ => (0 : Af F)) ?_ continuous_const
  refine continuous_pi fun w => ?_
  refine (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.isInducing.continuous_iff.2 ?_
  have e : (InfinitePlace.Completion.extensionEmbedding w) ∘ (fun t => (realAd F t).1 w) = fun t : ℝ => (t : ℂ) :=
    funext fun t => GlobalTheory.CompanionTheory.RealAdeleComponent.extensionEmbedding_evInf_realAd w t
  exact e ▸ Complex.continuous_ofReal

theorem exists_section (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    ∃ s : (InfinitePlace F → ℂ) → AE F E, Continuous s ∧ (∀ z, At (evI F) (s z)) ∧ ∀ z w, piInf (τ w) (s z) = z w := by
  classical
  choose x hx hx' using fun w : InfinitePlace F =>
    GlobalTheory.CompanionTheory.RealPlaceAdele.exists_adele_piInf σ h τ (Pi.single w 1)
  choose y hy hy' using fun w : InfinitePlace F =>
    GlobalTheory.CompanionTheory.RealPlaceAdele.exists_adele_piInf σ h τ (Pi.single w Complex.I)
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  refine ⟨fun z => ∑ w, (realAd F (z w).re • x w + realAd F (z w).im • y w), ?_, fun z c hc => ?_, fun z w => ?_⟩
  · have hr : ∀ (a : AE F E) (f : (InfinitePlace F → ℂ) → ℝ), Continuous f → Continuous fun z => realAd F (f z) • a :=
      fun a f hf => ((continuous_realAd (F := F)).comp hf).smul (continuous_const (y := a))
    refine continuous_finsetSum _ fun w _ => Continuous.add (hr _ _ ?_) (hr _ _ ?_)
    · exact Complex.continuous_re.comp (continuous_apply (A := fun _ => ℂ) w)
    · exact Complex.continuous_im.comp (continuous_apply (A := fun _ => ℂ) w)
  · rw [Finset.smul_sum]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [smul_add, smul_comm c, smul_comm c, hx w c hc, hy w c hc, smul_zero, smul_zero, add_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum, Finset.sum_eq_single w]
      · rw [map_add (f := _), GlobalTheory.CompanionTheory.RealAdeleComponent.piInf_realAd_smul, GlobalTheory.CompanionTheory.RealAdeleComponent.piInf_realAd_smul, hx', hy',
        Pi.single_eq_same, Pi.single_eq_same, mul_one, Complex.re_add_im]
      · intro v _ hv
        rw [map_add (f := _), GlobalTheory.CompanionTheory.RealAdeleComponent.piInf_realAd_smul, GlobalTheory.CompanionTheory.RealAdeleComponent.piInf_realAd_smul, hx', hy',
        Pi.single_eq_of_ne hv.symm, Pi.single_eq_of_ne hv.symm, mul_zero, mul_zero, add_zero]
      · simp

variable {d : ℕ}

theorem mat_ext (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {u v : Matrix (Fin d) (Fin d) (AE F E)}
    (hf : ∀ c : AF F, evI F c = 0 → c • u = c • v) (e : ∀ w, u.map (piInf (τ w)) = v.map (piInf (τ w))) : u = v := by
  ext i j
  refine sub_eq_zero.1 (eq_zero_of_piInf σ h τ _ (fun c hc => ?_) fun w => ?_)
  · rw [smul_sub]
    exact sub_eq_zero.2 (congrFun (congrFun (hf c hc) i) j)
  · rw [map_sub]
    exact sub_eq_zero.2 (congrFun (congrFun (e w) i) j)

omit [NumberField E] in
theorem at_iff {u : Matrix (Fin d) (Fin d) (AE F E)} :
    At (evI F) (u - 1) ↔ ∀ c : AF F, evI F c = 0 → c • u = c • (1 : Matrix (Fin d) (Fin d) (AE F E)) :=
  forall_congr' fun c => forall_congr' fun _ => by rw [smul_sub, sub_eq_zero]

theorem exists_matSection (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (d : ℕ) :
    ∃ S : (InfinitePlace F → Matrix (Fin d) (Fin d) ℂ) → Matrix (Fin d) (Fin d) (AE F E), Continuous S ∧
      (∀ z (c : AF F), evI F c = 0 → c • S z = c • (1 : Matrix (Fin d) (Fin d) (AE F E))) ∧
      ∀ z w, (S z).map (piInf (τ w)) = z w := by
  obtain ⟨s, hs, hA, hp⟩ := exists_section h τ
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  refine ⟨fun z => Matrix.of fun i j => (1 : Matrix (Fin d) (Fin d) (AE F E)) i j +
    s fun w => z w i j - (1 : Matrix (Fin d) (Fin d) ℂ) i j, ?_, fun z c hc => ?_, fun z w => ?_⟩
  · refine continuous_matrix fun i j => continuous_const.add (hs.comp (continuous_pi fun w => ?_))
    exact ((continuous_apply w).matrix_elem i j).sub continuous_const
  · ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply]
    rw [smul_add, hA _ c hc, add_zero]
  · ext i j
    have e := congrFun (congrFun (Matrix.map_one (n := Fin d) (piInf (τ w)) (map_zero _) (map_one _)) i) j
    rw [Matrix.map_apply] at e
    simp only [Matrix.map_apply, Matrix.of_apply]
    rw [map_add (f := _), hp, e, add_sub_cancel]

end ExponentialLineExistence

open ExponentialLineExistence in
theorem lineEx_of : LineEx := by
  intro F E _ _ _ _ _ σ h τ d W _ Y hY
  obtain ⟨S, hS, hf, hp⟩ := exists_matSection h τ d
  let g : ℝ → Matrix (Fin d) (Fin d) (AE F E) := fun t => S fun w => NormedSpace.exp ((t : ℂ) • Y w)
  have gp : ∀ t w, (g t).map (piInf (τ w)) = NormedSpace.exp ((t : ℂ) • Y w) := fun t w => hp _ w
  have gf : ∀ t (c : AF F), evI F c = 0 → c • g t = c • (1 : Matrix (Fin d) (Fin d) (AE F E)) := fun t => hf _
  have gc : Continuous g := hS.comp (continuous_pi fun w =>
    continuous_exp_mat.comp (Complex.continuous_ofReal.smul continuous_const))
  have g0 : g 0 = 1 := mat_ext h τ (gf 0) fun w => by
    rw [gp, Matrix.map_one _ (map_zero _) (map_one _), Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]
  have ga : ∀ s t, g (s + t) = g s * g t := fun s t => mat_ext h τ
    (fun c hc => by rw [gf _ c hc, ← Matrix.smul_mul, gf _ c hc, Matrix.smul_mul, Matrix.one_mul, gf _ c hc])
    fun w => by rw [Matrix.map_mul, gp, gp, gp, exp_line_add]
  have gu : ∀ t, (g t)ᵀ * incM F W.J * (g t).map (cA σ) = incM F W.J := fun t => mat_ext h τ
    (fun c hc => by
      have e : ∀ u : Matrix (Fin d) (Fin d) (AE F E), c • u.map (cA σ) = (c • u).map (cA σ) := fun u => by
        ext i j
        simp only [Matrix.smul_apply, Matrix.map_apply, map_smul]
      rw [← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.transpose_smul, gf _ c hc, Matrix.transpose_smul,
        Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, ← Matrix.mul_smul, e, gf _ c hc, ← e,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_smul, Matrix.mul_one])
    fun w => by
      have e : ((g t).map (cA σ)).map (piInf (τ w)) = ((g t).map (piInf (τ w))).map star := by
        ext i j
        exact piInf_cA h _ _
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, map_incM, e, gp]
      exact exp_unitary (hY w) t
  let G : ℝ → GL (Fin d) (AE F E) := fun t =>
    ⟨g t, g (-t), by rw [← ga, add_neg_cancel, g0], by rw [← ga, neg_add_cancel, g0]⟩
  let γ : Multiplicative ℝ →* UA σ W.J :=
    { toFun := fun t => ⟨G t.toAdd, gu _⟩
      map_one' := Subtype.ext (Units.ext g0)
      map_mul' := fun s t => Subtype.ext (Units.ext (ga _ _)) }
  refine ⟨γ, ⟨?_, fun t => at_iff.2 (gf _)⟩, fun w t => gp t w, fun γ' hγ' hG => ?_⟩
  · refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
    · exact gc.comp continuous_toAdd
    · exact (gc.comp continuous_neg).comp continuous_toAdd
  · refine MonoidHom.ext fun t => Subtype.ext (Units.ext ?_)
    refine mat_ext h τ (u := mat (γ' t)) (v := g t.toAdd) (fun c hc => ?_) fun w => ?_
    · rw [at_iff.1 (hγ'.2 t) c hc, gf _ c hc]
    · rw [gp]
      exact hG w t.toAdd

end PositivityTheory.ThKEst

end
end
