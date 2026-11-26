module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLaws
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFormsFiniteStabilisers

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMeasLevW
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelMeasure

theorem isMinf_unique {p q : ℕ} {m m' : Measure (UpqT p q)} (h : Lev.IsMinf m) (h' : Lev.IsMinf m') : m' = m := by
  haveI := (GlobalTheory.UpqTopology.upq_lcsc p q).1
  haveI := (GlobalTheory.UpqTopology.upq_lcsc p q).2.2.1
  haveI := (GlobalTheory.UpqTopology.upq_lcsc p q).2.2.2.1
  haveI := (GlobalTheory.UpqTopology.upq_lcsc p q).2.2.2.2.1
  haveI := h.1
  haveI := h'.1
  have e : m' = ((Measure.haarScalarFactor m' m : NNReal) : ENNReal) • m := Measure.isMulLeftInvariant_eq_smul m' m
  have h1 := GlobalTheory.OmegaDensityScale.omegaDensity_smul h.2 (Measure.haarScalarFactor m' m)
  rw [← e] at h1
  have h2 := GlobalTheory.OmegaDensityScale.omegaDensity_unique h'.2 h1
  have h0 : minfDensity (p + q) ≠ 0 := ENNReal.inv_ne_zero.2 (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have ht : minfDensity (p + q) ≠ ⊤ := ENNReal.inv_ne_top.2 (pow_ne_zero _ two_ne_zero)
  have hc : ((Measure.haarScalarFactor m' m : NNReal) : ENNReal) = 1 :=
    (ENNReal.mul_left_inj h0 ht).1 (h2.trans (one_mul _).symm)
  rw [e, hc, one_smul]

theorem exists_isMeasLevW (D : D7) (V : HSp D) (hV : V.SigOK) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (hKo : IsOpen ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)))
    (hKc : IsCompact ((Lev.levA V K : Subgroup (GA D V)) : Set (GA D V)))
    (good : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → Prop)
    (m : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2))
    (hm : ∀ ρ, (m ρ).IsHaarMeasure) (hg : ∀ ρ, good ρ (m ρ)) (hu : ∀ ρ m', good ρ m' → m' = m ρ) :
    ∃ μ, Lev.IsMeasLevW V K good μ := by
  have hτ : GlobalTheory.Mem.Vol.IsCMFam (tauE D) := GlobalTheory.Mem.Vol.isCMFam_host _ D.host _ D.eTau
  obtain ⟨hcm, -⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hθ := GlobalTheory.Mem.VolEmb.existsUnique_infEmb D.host.F D.host.E D.sp.cm.sig hcm
  choose θ hθ1 hθ2 using fun i => hθ (tauE D i)
  have hA := fun i => GlobalTheory.Mem.SignatureFactor.exists_factor _ _ _ _ (hV (tauE D i))
  choose A hA1 using fun i => (hA i).2.1
  obtain ⟨e1, he1⟩ := GlobalTheory.Mem.InfGroup.real_points D.host.F D.host.E D.sp.cm.sig V.rank V.gram D.what₂.Tau (tauE D) θ
    (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) A hcm hτ hθ1 (fun i => hV (tauE D i)) hA1
  obtain ⟨e0, he0⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  obtain ⟨-, hsc, ht2⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  have hinj := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.2.injective
  let j : HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram →* GA D V :=
    (e0.symm.toMulEquiv.toMonoidHom).comp (MonoidHom.inr _ _)
  have hj : Continuous j := e0.symm.continuous.comp (Continuous.prodMk_right 1)
  have hj0 : ∀ k, e0 (j k) = (1, k) := fun k => e0.apply_symm_apply _
  have hfin : ∀ h : GA D V, Lev.finE V (j (e0 h).2) = Lev.finE V h := by
    intro h
    have h1 : finHom V (j (e0 h).2) = finHom V h := by
      refine Units.ext ?_
      have a1 := (he0 (j (e0 h).2)).1
      have a2 := (he0 h).1
      rw [hj0] at a1
      exact a1.symm.trans a2
    rw [Lev.finE_eq, Lev.finE_eq, h1]
  have hinf : ∀ k, j k ∈ GfC V := by
    intro k
    have a1 := (he0 (j k)).2
    rw [hj0] at a1
    exact Units.ext a1.symm
  let K' := (K.comap (Lev.finE V)).comap j
  have hK : ∀ h : GA D V, (e0 h).2 ∈ K' ↔ Lev.finE V h ∈ K := fun h => by
    rw [← hfin h]; rfl
  have hK'o : IsOpen (K' : Set (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)) := hKo.preimage hj
  have hK'c : IsCompact (K' : Set (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)) := by
    have h1 := hKc.image (continuous_snd.comp e0.continuous)
    convert h1 using 1
    ext k
    constructor
    · intro hk
      exact ⟨j k, ⟨hinf k, hk⟩, congrArg Prod.snd (hj0 k)⟩
    · rintro ⟨h, hh, rfl⟩
      exact (hK h).2 hh.2
  let e : GA D V ≃ₜ* (∀ i, UpqT (V.sig (tauE D i)).1 (V.sig (tauE D i)).2) ×
      HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram :=
    e0.trans
      { e1.toMulEquiv.prodCongr (MulEquiv.refl _) with
        continuous_toFun := e1.continuous_toFun.prodMap continuous_id
        continuous_invFun := e1.continuous_invFun.prodMap continuous_id }
  have hee : ∀ h, e h = (e1 (e0 h).1, (e0 h).2) := fun h => rfl
  obtain ⟨μ, hμ, hμB⟩ := GlobalTheory.Mem.VolExists.exists_haar_prod m e K' hK'o hK'c
  refine ⟨μ, hμ, ⟨θ, hθ1⟩, fun θ' hθ' => ?_⟩
  obtain rfl : θ' = θ := funext fun i => hθ2 i _ (hθ' i)
  refine ⟨⟨A, hA1⟩, fun A' hA' => ⟨⟨m, hg⟩, fun m' hm' B hB => ?_⟩⟩
  obtain rfl : m' = m := funext fun i => hu i _ (hm' i)
  have hv : ∀ i, ∃ u : UpqT (V.sig (tauE D i)).1 (V.sig (tauE D i)).2, UpqT.mat u * A i = A' i := by
    intro i
    obtain ⟨C, h1, h2⟩ := (hA i).2.2 _ (hA1 i)
    obtain ⟨C', h3, h4⟩ := (hA i).2.2 _ (hA' i)
    exact GlobalTheory.Mem.VolExists.exists_upq_mul _ _ C C' h1 h2 h3 h4 ((hA1 i).trans (hA' i).symm)
  choose u hv using hv
  have key := hμB (fun i => (fun g => u i * g) ⁻¹' ((fun g => g * (u i)⁻¹) ⁻¹' B i))
    (fun i => measurable_const_mul _ (measurable_mul_const _ (hB i)))
  have hcj : ∀ i, m' i ((fun g => u i * g) ⁻¹' ((fun g => g * (u i)⁻¹) ⁻¹' B i)) = m' i (B i) := by
    intro i
    haveI := GlobalTheory.UpqHaarRight.isMulRightInvariant _ _ _ (hm i)
    rw [measure_preimage_mul, measure_preimage_mul_right]
  rw [Finset.prod_congr rfl (fun i _ => hcj i)] at key
  rw [← key]
  congr 1
  ext h
  simp only [Set.mem_setOf_eq, hee, Set.mem_preimage]
  rw [hK]
  refine and_congr_right fun _ => forall_congr' fun i => ?_
  have h1 : UpqT.mat (e1 (e0 h).1 i) * A i = A i * infMat D.sp.cm.sig V.gram (θ' i) h := by
    rw [he1, (he0 h).2]; rfl
  have h2 : UpqT.mat (u i * e1 (e0 h).1 i * (u i)⁻¹) * A' i = A' i * infMat D.sp.cm.sig V.gram (θ' i) h := by
    have h3 : UpqT.mat (u i)⁻¹ * A' i = A i := by
      rw [← hv i, ← Matrix.mul_assoc, ← GlobalTheory.Mem.VolExists.mat_mul, inv_mul_cancel, GlobalTheory.Mem.VolExists.mat_one,
        Matrix.one_mul]
    rw [GlobalTheory.Mem.VolExists.mat_mul, GlobalTheory.Mem.VolExists.mat_mul, Matrix.mul_assoc, h3, Matrix.mul_assoc, h1,
      ← Matrix.mul_assoc, hv i]
  constructor
  · rintro ⟨b, hb, hbe⟩
    obtain ⟨C', h3, -⟩ := (hA i).2.2 _ (hA' i)
    have : b = u i * e1 (e0 h).1 i * (u i)⁻¹ := by
      apply hinj
      have h5 := congrArg (· * C') (hbe.trans h2.symm)
      simpa only [Matrix.mul_assoc, h3, Matrix.mul_one] using h5
    exact this ▸ hb
  · intro hb
    exact ⟨_, hb, h2⟩

end GlobalTheory.LevelMeasure
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerKAvgNeZero
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum.KCoef

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem toMK_mem_UJ (k : KG ε) : toMK k ∈ UJset ε := K_le_UJ (toMK_mem_K k)

theorem continuous_orbit (hσ : IsURepOn (UJset ε) σ) (w : H) : Continuous fun k : KG ε => σ (toMK k) w :=
  (hσ.2.2 w).comp_continuous (continuous_toMK ε) toMK_mem_UJ

theorem integrable_avg (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) (w : H) :
    Integrable (fun k : KG ε => e k • σ (toMK k) w) (muK ε) :=
  (he.smul (continuous_orbit hσ w)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem sigma_K_mul (hσ : IsURepOn (UJset ε) σ) (a b : KG ε) (w : H) :
    σ (toMK (a * b)) w = σ (toMK a) (σ (toMK b) w) :=
  sigma_mul hσ (toMK_mem_UJ a) (toMK_mem_UJ b) w

theorem inner_K (hσ : IsURepOn (UJset ε) σ) (a : KG ε) (x w : H) :
    ⟪σ (toMK a) w, x⟫_ℂ = ⟪w, σ (toMK a⁻¹) x⟫_ℂ := by
  have h := LinearIsometry.inner_map_map ⟨(σ (toMK a) : H →ₗ[ℂ] H), hσ.2.1 _ (toMK_mem_UJ a)⟩ w (σ (toMK a⁻¹) x)
  have e : σ (toMK a) (σ (toMK a⁻¹) x) = x := by
    rw [← sigma_K_mul hσ, mul_inv_cancel]; exact sigma_one hσ x
  rw [← h]
  exact congrArg (fun z => ⟪σ (toMK a) w, z⟫_ℂ) e.symm

theorem kFinFun_coef (hσ : IsURepOn (UJset ε) σ) {y : H} (hy : IsKFin ε σ y) :
    KFinFun ε (fun k => star ⟪y, σ (toMK k) y⟫_ℂ) := by
  obtain ⟨S, hS, hyS, hK⟩ := hy
  let φ : H → H → KG ε → ℂ := fun s s' k => ⟪σ (toMK k) s', s⟫_ℂ
  obtain ⟨t, ht⟩ : S.FG := Module.Finite.iff_fg.1 hS
  have hfin : (Set.image2 φ (t : Set H) (t : Set H)).Finite := t.finite_toSet.image2 _ t.finite_toSet
  have key : ∀ s ∈ S, ∀ s' ∈ S, φ s s' ∈ Submodule.span ℂ (Set.image2 φ (t : Set H) (t : Set H)) := by
    intro s hs s' hs'
    rw [← ht] at hs hs'
    induction hs using Submodule.span_induction with
    | mem x hx =>
      induction hs' using Submodule.span_induction with
      | mem z hz => exact Submodule.subset_span (Set.mem_image2_of_mem hx hz)
      | zero =>
        have : φ x 0 = 0 := by ext k; simp [φ]
        rw [this]; exact Submodule.zero_mem _
      | add a b _ _ ha hb =>
        have : φ x (a + b) = φ x a + φ x b := by ext k; simp [φ, inner_add_left]
        rw [this]; exact Submodule.add_mem _ ha hb
      | smul c a _ ha =>
        have : φ x (c • a) = (starRingEnd ℂ c) • φ x a := by ext k; simp [φ, inner_smul_left, mul_comm]
        rw [this]; exact Submodule.smul_mem _ _ ha
    | zero =>
      have : φ 0 s' = 0 := by ext k; simp [φ]
      rw [this]; exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      have : φ (a + b) s' = φ a s' + φ b s' := by ext k; simp [φ, inner_add_right]
      rw [this]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      have : φ (c • a) s' = c • φ a s' := by ext k; simp [φ, inner_smul_right]
      rw [this]; exact Submodule.smul_mem _ _ ha
  have htS : ∀ x ∈ (t : Set H), x ∈ S := fun x hx => ht ▸ Submodule.subset_span hx
  refine ⟨Submodule.span ℂ (Set.image2 φ (t : Set H) (t : Set H)), FiniteDimensional.span_of_finite ℂ hfin, ?_, ?_, ?_⟩
  · have : (fun k : KG ε => star ⟪y, σ (toMK k) y⟫_ℂ) = φ y y := by
      ext k; exact inner_conj_symm _ _
    rw [this]; exact key y hyS y hyS
  · intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, -, b, -, rfl⟩ := hx
      exact (continuous_orbit hσ b).inner continuous_const
    | zero => exact continuous_zero
    | add a b _ _ ha hb => exact ha.add hb
    | smul c a _ ha => exact ha.const_smul c
  · intro ψ hψ k₀
    induction hψ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      constructor
      · have : (fun k => φ a b (k₀ * k)) = φ (σ (toMK k₀⁻¹) a) b := by
          ext k; simp only [φ]; rw [sigma_K_mul hσ, inner_K hσ]
        rw [this]; exact key _ (hK _ (toMK_mem_K _) _ (htS a ha)) _ (htS b hb)
      · have : (fun k => φ a b (k * k₀)) = φ a (σ (toMK k₀) b) := by
          ext k; simp only [φ]; rw [sigma_K_mul hσ]
        rw [this]; exact key _ (htS a ha) _ (hK _ (toMK_mem_K _) _ (htS b hb))
    | zero => exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
    | add a b _ _ ha hb => exact ⟨Submodule.add_mem _ ha.1 hb.1, Submodule.add_mem _ ha.2 hb.2⟩
    | smul c a _ ha => exact ⟨Submodule.smul_mem _ c ha.1, Submodule.smul_mem _ c ha.2⟩

variable [CompleteSpace H]

theorem inner_kAvg (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) (x w : H) :
    ⟪x, kAvg ε σ e w⟫_ℂ = ∫ k, e k * ⟪x, σ (toMK k) w⟫_ℂ ∂(muK ε) := by
  rw [kAvg, ← integral_inner (integrable_avg hσ he w)]
  simp only [inner_smul_right]

theorem inner_kAvg_ne_zero (hσ : IsURepOn (UJset ε) σ) {y : H} (hy : y ≠ 0) :
    ⟪y, kAvg ε σ (fun k => star ⟪y, σ (toMK k) y⟫_ℂ) y⟫_ℂ ≠ 0 := by
  have hc : Continuous fun k : KG ε => ⟪y, σ (toMK k) y⟫_ℂ := continuous_const.inner (continuous_orbit hσ y)
  rw [inner_kAvg hσ (e := fun k => star ⟪y, σ (toMK k) y⟫_ℂ) (continuous_star.comp hc)]
  have e : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
  simp only [e]
  rw [integral_complex_ofReal]
  have hpos : 0 < ∫ k : KG ε, ‖⟪y, σ (toMK k) y⟫_ℂ‖ ^ 2 ∂(muK ε) := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) (hc.norm.pow 2)
      (HasCompactSupport.of_compactSpace _) (fun k => by positivity) ?_
    have : σ (toMK (1 : KG ε)) y = y := sigma_one hσ y
    rw [this]
    exact pow_ne_zero _ (norm_ne_zero_iff.2 (inner_self_ne_zero.2 hy))
  exact_mod_cast hpos.ne'


omit [CompleteSpace H] in
theorem exists_clm_kAvg (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) :
    ∃ Q : H →L[ℂ] H, ∀ w, Q w = kAvg ε σ e w := by
  let L : H →ₗ[ℂ] H :=
    { toFun := kAvg ε σ e
      map_add' := fun x y => by
        simp only [kAvg, map_add (f := _), smul_add]
        exact integral_add (integrable_avg hσ he x) (integrable_avg hσ he y)
      map_smul' := fun c x => by
        simp only [kAvg, map_smul, RingHom.id_apply, smul_comm _ c]
        exact integral_smul _ _ }
  refine ⟨L.mkContinuous (∫ k, ‖e k‖ ∂(muK ε)) fun w => ?_, fun w => rfl⟩
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp only [norm_smul, fun k : KG ε => hσ.2.1 _ (toMK_mem_UJ k) w]
  exact integral_mul_const _ _

theorem kAvg_mem (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) {S : Submodule ℂ H}
    [FiniteDimensional ℂ S] (hK : IsKStableOn ε σ S) {z : H} (hz : z ∈ S) : kAvg ε σ e z ∈ S := by
  rw [← S.orthogonal_orthogonal, Submodule.mem_orthogonal]
  intro u hu
  rw [inner_kAvg hσ he]
  have : ∀ k : KG ε, ⟪u, σ (toMK k) z⟫_ℂ = 0 := fun k =>
    Submodule.inner_left_of_mem_orthogonal (hK _ (toMK_mem_K k) z hz) hu
  simp [this]

end GlobalTheory.TypeSum.KCoef

namespace GlobalTheory.TypeSum

theorem kCoef_kAvg : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → (∀ y, IsKFin ε σ y → KFinFun ε (fun k => star ⟪y, σ (toMK k) y⟫_ℂ)) ∧ (∀ y : H, y ≠ 0 → ⟪y, kAvg ε σ (fun k => star ⟪y, σ (toMK k) y⟫_ℂ) y⟫_ℂ ≠ 0) ∧ (∀ e : KG ε → ℂ, Continuous e → ∃ Q : H →L[ℂ] H, ∀ w, Q w = kAvg ε σ e w) ∧ ∀ e : KG ε → ℂ, Continuous e → ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → IsKStableOn ε σ S → ∀ z ∈ S, kAvg ε σ e z ∈ S :=
  fun _ _ _ _ _ _ _ hσ => ⟨fun _ hy => KCoef.kFinFun_coef hσ hy, fun _ hy => KCoef.inner_kAvg_ne_zero hσ hy,
    fun _ he => KCoef.exists_clm_kAvg hσ he, fun _ he _ _ hK _ hz => KCoef.kAvg_mem hσ he hK hz⟩

end GlobalTheory.TypeSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionStar
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionStar
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.Mem.AutConj

open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.SmoothForms

def ConjAlg (A : Type) : Type := A

instance (A : Type) [Ring A] : Ring (ConjAlg A) := inferInstanceAs (Ring A)

instance (A : Type) [Ring A] [Algebra ℂ A] : Algebra ℂ (ConjAlg A) :=
  RingHom.toAlgebra' (S := ConjAlg A) ((algebraMap ℂ A).comp (starRingEnd ℂ))
    fun c x => Algebra.commutes (A := A) (star c) x

theorem exists_conj (L : Type) [LieRing L] [LieAlgebra ℝ L] :
    ∃ π : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L) →+* UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L),
      (∀ (c : ℂ) u, π (c • u) = star c • π u) ∧
      ∀ X, π (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X) := by
  have hs : ∀ (c : ℂ) (u : ConjAlg (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L))),
      c • u = (star c • (show UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L) from u) :
        UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L)) := fun c u =>
    (Algebra.smul_def (A := UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L)) (star c) u).symm
  obtain ⟨π, hπ⟩ := GlobalTheory.EnvelopingExtension.exists_algHom_of_real L
    (ConjAlg (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L)))
    (fun X => (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X) : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L)))
    (fun X Y => by rw [TensorProduct.tmul_add, map_add (f := _)]; rfl)
    (fun c X => by
      refine Eq.trans ?_ (hs _ _).symm
      change UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] (c • X)) =
        star (c : ℂ) • UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)
      rw [← map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
      simp)
    (fun X Y => by
      have : UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] ⁅X, Y⁆) =
          UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X) * UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] Y) -
          UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] Y) * UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X) := by
        rw [← Ring.lie_def, ← LieHom.map_lie, LieAlgebra.ExtendScalars.bracket_tmul, one_mul]
      exact this)
  exact ⟨π.toRingHom, fun c u => (map_smul π c u).trans (hs c _), hπ⟩

variable {D : D7} {θ : InfF D} {V : HSp D}

def conjWord {α : Type} (w : α →₀ ℂ) : α →₀ ℂ := w.mapRange star (star_zero ℂ)

theorem conjWord_conjWord {α : Type} (w : α →₀ ℂ) : conjWord (conjWord w) = w := by
  ext a; simp [conjWord]

theorem conjWord_center (τ : D.what₂.Tau) {w : List (LieAt V τ) →₀ ℂ}
    (hw : envOf V τ w ∈ Subalgebra.center ℂ (EnvAt V τ)) :
    envOf V τ (conjWord w) ∈ Subalgebra.center ℂ (EnvAt V τ) := by
  obtain ⟨π, h1, h2⟩ := exists_conj (LieAt V τ)
  have key : ∀ w : List (LieAt V τ) →₀ ℂ, envOf V τ (conjWord w) = π (envOf V τ w) := fun w => by
    rw [envOf, envOf, conjWord, Finsupp.sum_mapRange_index (fun _ => by rw [zero_smul]), map_finsuppSum]
    refine Finsupp.sum_congr fun l _ => ?_
    rw [h1, map_list_prod, List.map_map]
    congr 2
    exact List.map_congr_left fun X _ => (h2 X).symm
  rw [Subalgebra.mem_center_iff] at hw ⊢
  intro u
  obtain ⟨w', rfl⟩ := GlobalTheory.T.enveloping_map_surjective D V τ u
  rw [← conjWord_conjWord w', key (conjWord w'), key w, ← map_mul, ← map_mul, hw]

theorem wordDer_star (e : LieInf V → GA D V) (l : List (LieInf V)) (φ : GA D V → ℂ) :
    wordDer V e l (star φ) = star (wordDer V e l φ) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    change lieDer V e X (wordDer V e l (star φ)) = star (lieDer V e X (wordDer V e l φ))
    rw [ih]
    funext g
    exact deriv.star

theorem envDer_star (e : LieInf V → GA D V) (τ : D.what₂.Tau) (w : List (LieAt V τ) →₀ ℂ) (φ : GA D V → ℂ) :
    envDer V e τ w (star φ) = star (envDer V e τ (conjWord w) φ) := by
  rw [envDer, envDer, conjWord, Finsupp.sum_mapRange_index (fun _ => by rw [zero_smul]), Finsupp.sum, Finsupp.sum, star_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [wordDer_star, star_smul, star_star]

theorem finiteDimensional_span_star {G : Type} {S S' : Set (G → ℂ)} (h : FiniteDimensional ℂ (Submodule.span ℂ S))
    (hs : ∀ f ∈ S', star f ∈ S) : FiniteDimensional ℂ (Submodule.span ℂ S') := by
  obtain ⟨t, ht, e⟩ := Submodule.fg_def.1 (Module.Finite.iff_fg.1 h)
  have := FiniteDimensional.span_of_finite ℂ (ht.image star)
  have key : ∀ f ∈ Submodule.span ℂ t, star f ∈ Submodule.span ℂ (star '' t) := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [star_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [star_add]; exact add_mem hx hy
    | smul c x _ hx => rw [star_smul]; exact Submodule.smul_mem _ _ hx
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (star '' t)) (Submodule.span_le.2 fun f hf => ?_)
  have := key (star f) (e ▸ Submodule.subset_span (hs f hf))
  rwa [star_star] at this

theorem isZFiniteAt_star {e : LieInf V → GA D V} {τ : D.what₂.Tau} {φ : GA D V → ℂ} (h : IsZFiniteAt V e τ φ) :
    IsZFiniteAt V e τ (star φ) := by
  refine finiteDimensional_span_star h ?_
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨conjWord w, conjWord_center τ hw, by rw [envDer_star, star_star]⟩

theorem foldr_Rder_star (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (φ : GA D V → ℂ) :
    l.foldr (fun p f => Rder θ V p.1 p.2 f) (star φ) = star (l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    rw [List.foldr_cons, List.foldr_cons, ih]
    funext g
    exact deriv.star

theorem isAutFunSm_star : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (φ : GA D V → ℂ),
    IsAutFunSm θ V φ → IsAutFunSm θ V (fun g => star (φ g)) := by
  intro D θ hθ V φ h
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  have hsm : ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ =>
        (star φ) (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod) :=
    fun k τs Xs hX g => Complex.conjCLE.contDiff.comp (h.smooth k τs Xs hX g)
  change IsAutFunSm θ V (star φ)
  refine ⟨⟨fun γ hγ g => ?_, ?_, h.cont.star⟩, hsm, ?_, ?_⟩
  · simp only [Pi.star_apply, h.left γ hγ g]
  · obtain ⟨U, hU, hk⟩ := h.level
    exact ⟨U, hU, fun k h1 h2 g => by simp only [Pi.star_apply, hk k h1 h2 g]⟩
  · exact (zfin_iff R ((smooth_iff R _).1 hsm)).2 fun τ =>
      isZFiniteAt_star ((zfin_iff R ((smooth_iff R φ).1 h.smooth)).1 h.zfin τ)
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl x
    refine ⟨C, fun g hg => ?_⟩
    rw [foldr_Rder_star, Pi.star_apply, norm_star]
    exact hC g hg

end GlobalTheory.Mem.AutConj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionStarStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSmoothAutomorphicFunction_star : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (φ : GA D V → ℂ), IsAutFunSm θ V φ → IsAutFunSm θ V (fun g => star (φ g)) := by
  first | exact @GlobalTheory.Mem.AutConj.isAutFunSm_star | exact GlobalTheory.Mem.AutConj.isAutFunSm_star | (intros; apply GlobalTheory.Mem.AutConj.isAutFunSm_star <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.APlusComm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockSubst

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis Complex
open scoped Real Classical

private theorem _theta_add_aux {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} :
    ∀ {f g : WO S T → ℂ}, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IsThetaFunO ψ S T (f + g) := by
  intro f g hf hg
  refine ⟨?_, ?_, hf.cont.add hg.cont, ?_⟩
  · intro γ w
    simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
  · obtain ⟨U, hU, h1⟩ := hf.level
    obtain ⟨V, hV, h2⟩ := hg.level
    refine ⟨U ⊓ V, hU.inter hV, fun u hu h0 => ?_⟩
    funext w
    have e1 := congrFun (h1 u hu.1 h0) w
    have e2 := congrFun (h2 u hu.2 h0) w
    unfold heisO at e1 e2 ⊢
    rw [Pi.add_apply, Pi.add_apply, mul_add, e1, e2]
  · intro k L h1 h2 w
    exact (hf.smooth k L h1 h2 w).add (hg.smooth k L h1 h2 w)

private theorem _theta_smul_aux {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} :
    ∀ (c : ℂ) {f : WO S T → ℂ}, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (c • f) := by
  intro c f hf
  refine ⟨?_, ?_, hf.cont.const_smul c, ?_⟩
  · intro γ w
    rw [Pi.smul_apply, Pi.smul_apply, hf.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
  · obtain ⟨U, hU, h1⟩ := hf.level
    refine ⟨U, hU, fun u hu h0 => ?_⟩
    funext w
    have e1 := congrFun (h1 u hu h0) w
    unfold heisO at e1 ⊢
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, e1]
  · intro k L h1 h2 w
    exact contDiff_const.mul (hf.smooth k L h1 h2 w)


variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

noncomputable def dirPt (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) : RW T S :=
  (Pi.single τ z : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ)

theorem dRho_laws (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    (∀ f', IsThetaFunO ψ S T f' → Datum.dRho (heisO ψ S T) θ τ z (f + f') =
      Datum.dRho (heisO ψ S T) θ τ z f + Datum.dRho (heisO ψ S T) θ τ z f') ∧
    (∀ a : ℂ, Datum.dRho (heisO ψ S T) θ τ z (a • f) = a • Datum.dRho (heisO ψ S T) θ τ z f) ∧
    (∀ z', Datum.dRho (heisO ψ S T) θ τ (z + z') f =
      Datum.dRho (heisO ψ S T) θ τ z f + Datum.dRho (heisO ψ S T) θ τ z' f) ∧
    (∀ t : ℝ, Datum.dRho (heisO ψ S T) θ τ ((t : ℂ) • z) f = (t : ℂ) • Datum.dRho (heisO ψ S T) θ τ z f) ∧
    ∀ (τ' : D.what₂.Tau) (z' : Matrix (Fin T.rank) (Fin S.rank) ℂ),
      Datum.dRho (heisO ψ S T) θ τ z (Datum.dRho (heisO ψ S T) θ τ' z' f) -
        Datum.dRho (heisO ψ S T) θ τ' z' (Datum.dRho (heisO ψ S T) θ τ z f) =
      (-(2 * π * I) * (omO S T (dirPt τ z) (dirPt τ' z') : ℝ)) • f := by
  have theta_add : ∀ {f g : WO S T → ℂ}, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IsThetaFunO ψ S T (f + g) := fun hf hg => _root_.GlobalTheory.FockSubst._theta_add_aux hf hg
  have theta_smul : ∀ (c : ℂ) {f : WO S T → ℂ}, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (c • f) := fun c {_} hf => _root_.GlobalTheory.FockSubst._theta_smul_aux c hf
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hE : ∀ τ z g, Datum.dRho (heisO ψ S T) θ τ z g =
      FockCompare.hD (iotaW σ T S) (piW θ T S) (omO S T) (dirPt τ z) g := fun τ z g => by
    have := dLine_eq_hD h hψ (isRealDir_lineAt hθ τ z) g
    rw [GlobalTheory.Ker.HeisDeriv.pi_lineAt hθ] at this
    exact this
  have hs := theta_sm h hf
  have hd : ∀ {g}, IsThetaFunO ψ S T g → ∀ w, DifferentiableAt ℝ (fun x : RW T S => g (w + iotaW σ T S x)) 0 :=
    fun hg w => ((theta_sm h hg w).differentiable (by simp)).differentiableAt
  refine ⟨fun f' hf' => ?_, fun a => ?_, fun z' => ?_, fun t => ?_, fun τ' z' => ?_⟩
  · funext w
    rw [Pi.add_apply, hE, hE, hE, hD_eq_fderiv _ _ _ _ (theta_sm h (theta_add hf hf')), hD_eq_fderiv _ _ _ _ hs,
      hD_eq_fderiv _ _ _ _ (theta_sm h hf')]
    have e : (fun x : RW T S => (f + f') (w + iotaW σ T S x)) =
        fun x : RW T S => f (w + iotaW σ T S x) + f' (w + iotaW σ T S x) := rfl
    rw [e, fderiv_fun_add (hd hf w) (hd hf' w), ContinuousLinearMap.add_apply, Pi.add_apply]
    ring
  · funext w
    rw [Pi.smul_apply, hE, hE, hD_eq_fderiv _ _ _ _ (theta_sm h (theta_smul a hf)), hD_eq_fderiv _ _ _ _ hs]
    have e : (fun x : RW T S => (a • f) (w + iotaW σ T S x)) =
        fun x : RW T S => a • f (w + iotaW σ T S x) := rfl
    rw [e, fderiv_fun_const_smul (hd hf w), ContinuousLinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      smul_eq_mul]
    ring
  · have e : dirPt τ (z + z') = dirPt τ z + dirPt τ z' := by
      unfold dirPt
      rw [Pi.single_add]
      rfl
    funext w
    rw [Pi.add_apply, hE, hE, hE, e, hD_eq_fderiv _ _ _ _ hs, hD_eq_fderiv _ _ _ _ hs, hD_eq_fderiv _ _ _ _ hs,
      LinearMap.map_add, ContinuousLinearMap.map_add]
    push_cast
    ring
  · have e : dirPt τ ((t : ℂ) • z) = t • dirPt τ z := by
      unfold dirPt
      rw [Pi.single_smul]
      rfl
    funext w
    rw [Pi.smul_apply, hE, hE, e, hD_eq_fderiv _ _ _ _ hs, hD_eq_fderiv _ _ _ _ hs,
      LinearMap.map_smul, ContinuousLinearMap.map_smul, smul_eq_mul, smul_eq_mul, Complex.real_smul]
    push_cast
    ring
  · have sk : ∀ u v, omO S T v u = -omO S T u v := fun u v => by
      have h1 := omO_self h (S := S) (T := T) (u + v)
      simp only [LinearMap.map_add (f := _), LinearMap.add_apply, omO_self h] at h1
      linarith
    rw [hE, hE, hE, hE, heisenberg_derivative_commutator _ _ _ _ _ (h.pi_iota T S)
      (fun g hg u w => hD_eq_fderiv _ _ _ g hg u w) sk f hs]

theorem om_cplx (hθ : IsInfFam θ) {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ))
    (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) (τ τ' : D.what₂.Tau) (z z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    omO S T (dirPt τ (cplxO (sS τ) (sT τ) z)) (dirPt τ' (cplxO (sS τ') (sT τ') z')) =
      omO S T (dirPt τ z) (dirPt τ' z') ∧
    omO S T (dirPt τ (cplxO (sS τ) (sT τ) z)) (dirPt τ' z') =
      -omO S T (dirPt τ z) (dirPt τ' (cplxO (sS τ') (sT τ') z')) := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have sk : ∀ u v, omO S T v u = -omO S T u v := fun u v => by
    have h1 := omO_self h (S := S) (T := T) (u + v)
    simp only [LinearMap.map_add (f := _), LinearMap.add_apply, omO_self h] at h1
    linarith
  have key := fun τ => GlobalTheory.CartanTrace.cplxO_pos T.rank S.rank (gramAt D S τ) (sS τ) (gramAt D T τ) (sT τ)
    (tauE D τ D.host.xi0) (GlobalTheory.OrientedRealForm.realPlace_imaginaryGenerator_re_eq_zero τ) (xi_zero_im_pos D τ) (hS τ) (hT τ)
  have hom : ∀ x y : RW T S, omO S T x y = ∑ τ, formAt S T τ (x τ) (y τ) := fun _ _ => rfl
  have hJ : ∀ τ z, dirPt τ (cplxO (sS τ) (sT τ) z) = GlobalTheory.OrientedRealForm.jO S T sS sT (dirPt τ z) := by
    intro τ z
    funext ρ
    show _ = cplxO (sS ρ) (sT ρ) (dirPt τ z ρ)
    unfold dirPt
    by_cases e : ρ = τ
    · subst e
      rw [Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne e, Pi.single_eq_of_ne e]
      simp [cplxO]
  have hJJ : ∀ v, GlobalTheory.OrientedRealForm.jO S T sS sT (GlobalTheory.OrientedRealForm.jO S T sS sT v) = -v := fun v => by
    funext τ
    exact (key τ).2.1 (v τ)
  have hsym : ∀ x y, omO S T x (GlobalTheory.OrientedRealForm.jO S T sS sT y) =
      omO S T y (GlobalTheory.OrientedRealForm.jO S T sS sT x) := fun x y => by
    rw [hom, hom]
    refine Finset.sum_congr rfl fun τ _ => ?_
    refine (GlobalTheory.OrientedRealForm.formAt_eq S T τ _ _).trans
      (Eq.trans ?_ (GlobalTheory.OrientedRealForm.formAt_eq S T τ _ _).symm)
    exact congrArg (2 * ·) ((key τ).2.2.1 (x τ) (y τ))
  rw [hJ, hJ]
  constructor
  · rw [hsym, hJJ, map_neg, ← sk]
  · rw [sk, hsym]

variable (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (τ : D.what₂.Tau)
  (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
  (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)

theorem aPlus_eq (f : WO S T → ℂ) : aPlus (heisO ψ S T) θ τ J z f =
    ((fockScale D τ : ℂ)⁻¹) • (Datum.dRho (heisO ψ S T) θ τ z f + (-I) • Datum.dRho (heisO ψ S T) θ τ (J z) f) := by
  rw [aPlus, crea, neg_smul, sub_eq_add_neg]

include hψ hθ

theorem aPlus_th {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (aPlus (heisO ψ S T) θ τ J z f) := by
  have theta_add : ∀ {f g : WO S T → ℂ}, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IsThetaFunO ψ S T (f + g) := fun hf hg => _root_.GlobalTheory.FockSubst._theta_add_aux hf hg
  have theta_smul : ∀ (c : ℂ) {f : WO S T → ℂ}, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (c • f) := fun c {_} hf => _root_.GlobalTheory.FockSubst._theta_smul_aux c hf
  rw [aPlus_eq]
  exact theta_smul _ (theta_add (theta_dRho hθ hψ τ z hf) (theta_smul _ (theta_dRho hθ hψ τ _ hf)))

theorem aPlus_add {f f' : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hf' : IsThetaFunO ψ S T f') :
    aPlus (heisO ψ S T) θ τ J z (f + f') = aPlus (heisO ψ S T) θ τ J z f + aPlus (heisO ψ S T) θ τ J z f' := by
  simp only [aPlus_eq, fun z => (dRho_laws hψ hθ hf τ z).1 f' hf']
  module

theorem aPlus_smul (a : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    aPlus (heisO ψ S T) θ τ J z (a • f) = a • aPlus (heisO ψ S T) θ τ J z f := by
  simp only [aPlus_eq, fun z => (dRho_laws hψ hθ hf τ z).2.1 a]
  module

theorem aPlus_comm {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ))
    (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) (τ' : D.what₂.Tau) (z' : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    aPlus (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z (aPlus (heisO ψ S T) θ τ' (cplxO (sS τ') (sT τ')) z' f) =
    aPlus (heisO ψ S T) θ τ' (cplxO (sS τ') (sT τ')) z' (aPlus (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z f) := by
  have theta_add : ∀ {f g : WO S T → ℂ}, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IsThetaFunO ψ S T (f + g) := fun hf hg => _root_.GlobalTheory.FockSubst._theta_add_aux hf hg
  have theta_smul : ∀ (c : ℂ) {f : WO S T → ℂ}, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (c • f) := fun c {_} hf => _root_.GlobalTheory.FockSubst._theta_smul_aux c hf
  have ht := fun τ z => theta_dRho hθ hψ τ z hf
  have hc := fun τ z τ' z' => eq_add_of_sub_eq ((dRho_laws hψ hθ hf τ z).2.2.2.2 τ' z')
  obtain ⟨h1, h2⟩ := om_cplx hθ hS hT τ τ' z z'
  rw [aPlus_eq τ' _ z' f, aPlus_eq τ _ z f, aPlus_smul hψ hθ _ _ _ _ (theta_add (ht _ _) (theta_smul _ (ht _ _))),
    aPlus_smul hψ hθ _ _ _ _ (theta_add (ht _ _) (theta_smul _ (ht _ _))),
    aPlus_add hψ hθ _ _ _ (ht _ _) (theta_smul _ (ht _ _)), aPlus_add hψ hθ _ _ _ (ht _ _) (theta_smul _ (ht _ _)),
    aPlus_smul hψ hθ _ _ _ _ (ht _ _), aPlus_smul hψ hθ _ _ _ _ (ht _ _)]
  simp only [aPlus_eq]
  rw [hc τ z τ' z', hc τ z τ' (cplxO (sS τ') (sT τ') z'), hc τ (cplxO (sS τ) (sT τ) z) τ' z',
    hc τ (cplxO (sS τ) (sT τ) z) τ' (cplxO (sS τ') (sT τ') z'), h1, h2]
  match_scalars
  all_goals first | ring1 | (ring_nf; simp only [I_pow_three]; ring1)

end GlobalTheory.FockSubst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAvgClosure
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem isAvg_sigma {g : Mx n} (hg : g ∈ UJset ε) : IsAvg ε σ (σ g) :=
  ⟨{g}, 1, isCompact_singleton, Set.singleton_subset_iff.2 hg, zero_le_one, fun ι _ x w M _ h => by
    rw [one_mul]; exact h g rfl⟩

theorem IsAvg.add {T T' : H → H} (h : IsAvg ε σ T) (h' : IsAvg ε σ T') : IsAvg ε σ (fun w => T w + T' w) := by
  obtain ⟨Z, C, h1, h2, h3, h4⟩ := h
  obtain ⟨Z', C', k1, k2, k3, k4⟩ := h'
  refine ⟨Z ∪ Z', C + C', h1.union k1, Set.union_subset h2 k2, add_nonneg h3 k3, fun ι _ x w M hM hb => ?_⟩
  simp only [inner_add_right, Finset.sum_add_distrib, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (h4 ι x w M hM fun y hy => hb y (Or.inl hy))
    (k4 ι x w M hM fun y hy => hb y (Or.inr hy)))

theorem IsAvg.comp (hσ : IsURepOn (UJset ε) σ) {T T' : H → H} (h : IsAvg ε σ T) (h' : IsAvg ε σ T') :
    IsAvg ε σ (fun w => T (T' w)) := by
  obtain ⟨Z, C, h1, h2, h3, h4⟩ := h
  obtain ⟨Z', C', k1, k2, k3, k4⟩ := h'
  refine ⟨(fun p : Mx n × Mx n => p.1 * p.2) '' (Z ×ˢ Z'), C * C',
    (h1.prod k1).image (continuous_fst.matrix_mul continuous_snd), ?_, mul_nonneg h3 k3, fun ι _ x w M hM hb => ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact mul_mem_UJ (h2 hp.1) (k2 hp.2)
  rw [mul_assoc]
  refine h4 ι x (fun j => T' (w j)) (C' * M) (mul_nonneg k3 hM) fun y hy => ?_
  simp only [inner_sigma hσ (h2 hy)]
  refine k4 ι (fun j => σ y⁻¹ (x j)) w M hM fun y' hy' => ?_
  have := hb (y * y') ⟨(y, y'), ⟨hy, hy'⟩, rfl⟩
  simpa only [sigma_mul hσ (h2 hy) (k2 hy'), inner_sigma hσ (h2 hy)] using this

theorem IsAvg.smul (c : ℂ) {T : H → H} (h : IsAvg ε σ T) : IsAvg ε σ (fun w => c • T w) := by
  obtain ⟨Z, C, h1, h2, h3, h4⟩ := h
  refine ⟨Z, ‖c‖ * C, h1, h2, mul_nonneg (norm_nonneg _) h3, fun ι _ x w M hM hb => ?_⟩
  simp only [inner_smul_right, ← Finset.mul_sum, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h4 ι x w M hM hb) (norm_nonneg _)

theorem isAvg_zero : IsAvg ε σ (fun _ => 0) :=
  ⟨∅, 0, isCompact_empty, Set.empty_subset _, le_rfl, fun ι _ x w M _ _ => by simp⟩

theorem isAvg_kAvg [CompleteSpace H] (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) :
    IsAvg ε σ (kAvg ε σ e) := by
  refine ⟨Kset ε, ∫ k, ‖e k‖ ∂(muK ε), (maximal_compact_facts n ε).2.1, fun k hk => K_le_UJ hk,
    integral_nonneg fun _ => norm_nonneg _, fun ι _ x w M hM hb => ?_⟩
  have hi : ∀ v : H, Integrable (fun k : KG ε => e k • σ (toMK k) v) (muK ε) := fun v =>
    (he.smul ((hσ.2.2 v).comp_continuous (continuous_toMK ε)
      fun k => K_le_UJ (toMK_mem_K k))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [kAvg]
  simp only [fun j => (integral_inner (𝕜 := ℂ) (hi (w j)) (x j)).symm]
  rw [← integral_finsetSum _ fun j _ => (hi (w j)).const_inner (x j), ← integral_mul_const]
  refine norm_integral_le_of_norm_le ((he.norm.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)).mul_const M) (Eventually.of_forall fun k => ?_)
  simp only [inner_smul_right, ← Finset.mul_sum, norm_mul]
  exact mul_le_mul_of_nonneg_left (hb _ (toMK_mem_K k)) (norm_nonneg _)

theorem isAvg_closure : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → (∀ g ∈ UJset ε, IsAvg ε σ (σ g)) ∧ (∀ T T' : H → H, IsAvg ε σ T → IsAvg ε σ T' → IsAvg ε σ (fun w => T w + T' w) ∧ IsAvg ε σ (fun w => T (T' w))) ∧ (∀ (c : ℂ) (T : H → H), IsAvg ε σ T → IsAvg ε σ (fun w => c • T w)) ∧ (∀ e : KG ε → ℂ, Continuous e → IsAvg ε σ (kAvg ε σ e)) ∧ IsAvg ε σ (fun _ => 0) :=
  fun _ _ _ _ _ _ _ hσ => ⟨fun _ hg => isAvg_sigma hg, fun _ _ h h' => ⟨h.add h', h.comp hσ h'⟩,
    fun c _ h => h.smul c, fun _ he => isAvg_kAvg hσ he, isAvg_zero⟩

end GlobalTheory.TypeSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormSubLeOfDerivIcc
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

variable {n : ℕ} {ε : Fin n → Bool}

theorem IsDerFam.hasDerivAt_exp {F : List (Mx n) → Mx n → ℂ} (hF : IsDerFam ε F) {l : List (Mx n)}
    (hl : ∀ Y ∈ l, Y ∈ lieSet ε) {X : Mx n} (hX : X ∈ lieSet ε) {z : Mx n} (hz : z ∈ UJset ε) (s : ℝ) :
    HasDerivAt (fun t : ℝ => F l (z * NormedSpace.exp (t • X))) (F (X :: l) (z * NormedSpace.exp (s • X))) s := by
  have h1 := hF l hl X hX _ (mul_mem_UJ hz (exp_mem_UJ hX s))
  have h2 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h1)
  refine HasDerivAt.congr_of_eventuallyEq h2 (Filter.Eventually.of_forall fun t => ?_)
  show _ = F l (z * _ * _)
  rw [Matrix.mul_assoc, ← exp_add_smul, add_sub_cancel]

theorem norm_sub_le_of_deriv_Icc {f f' : ℝ → ℂ} (hf : ∀ s, HasDerivAt f (f' s) s) {δ B : ℝ} (hδ : 0 ≤ δ)
    (hB : ∀ s ∈ Set.Icc (-δ) δ, ‖f' s‖ ≤ B) {t : ℝ} (ht : t ∈ Set.Icc (-δ) δ) : ‖f t - f 0‖ ≤ B * |t| := by
  have := (convex_Icc (-δ) δ).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hf s).hasDerivWithinAt) hB (x := 0) (y := t) ⟨by linarith, hδ⟩ ht
  simpa using this

end GlobalTheory.TypeSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOKAll
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelOpenCompactSmooth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LevelSmooth

theorem level_open_compact_smooth (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    IsOpen (((lev D.sp.cm V.gram β L).comap (finE V) : Subgroup (GA D V)) : Set (GA D V)) ∧
    IsCompact ((levA V (lev D.sp.cm V.gram β L) : Subgroup (GA D V)) : Set (GA D V)) ∧
    levS V β L ⊆ (GfC V : Set (GA D V)) ∧
    ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧
      ∀ k ∈ U, k ∈ GfC V → k ∈ levS V β L ∧ levChi V β L k = 1 :=
  ⟨GlobalTheory.ParahoricCompact.isOpen_comap_lev V β L, GlobalTheory.ParahoricCompact.isCompact_levG V β L, fun _ hk => hk.1,
    GlobalTheory.GoodFiniteDim.exists_open_subgroup V β L⟩

end GlobalTheory.Mem.LevelSmooth
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LevelOK

theorem levOK_all : ∀ D : D7, LevOK D := by
  intro D V β L
  obtain ⟨hO, hC, hS, U, hU, hk⟩ := GlobalTheory.Mem.LevelSmooth.level_open_compact_smooth D V β L
  refine ⟨⟨hC, ?_⟩, U, hU, fun k hkU hkG => ?_⟩
  · have : (((Lev.levA V (lev D.sp.cm (HSpace.gram V) β L)).subgroupOf (GfC V)) : Set (GfC V)) =
        Subtype.val ⁻¹' ((Subgroup.comap (Lev.finE V) (lev D.sp.cm (HSpace.gram V) β L)) : Set (GA D V)) := by
      ext x; simp [Subgroup.mem_subgroupOf, Lev.levA, x.2]
    rw [this]; exact hO.preimage continuous_subtype_val
  · obtain ⟨h1, h2⟩ := hk k hkU hkG
    exact ⟨h1, h2⟩
end GlobalTheory.Mem.LevelOK
end
