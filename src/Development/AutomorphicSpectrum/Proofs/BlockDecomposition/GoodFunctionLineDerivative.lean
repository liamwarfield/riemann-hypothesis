module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAdelicThetaSumSqParsevalSecondVariable
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.QuadAtOf
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodFunctionLineDerivative
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodFunctionLineDerivative
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem continuous_lineDer_of_growth (h : IsCMExt F E σ) {φ : GAd σ J → ℂ} (hs : GlobalTheory.UAut.IsSm σ J φ) (hc : Continuous φ)
    {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) {A : ℕ} {B : ℝ}
    (hB : ∀ g, ‖lineDer γ (lineDer γ φ) g‖ ≤ B * (height σ J g : ℝ) ^ A) : Continuous (lineDer γ φ) := by
  have hpos : ∀ g, 0 < (height σ J g : ℝ) := fun g =>
    zero_lt_one.trans_le (by exact_mod_cast GlobalTheory.AdelicU.one_le_height σ J g)
  have hB0 : 0 ≤ B := (mul_nonneg_iff_of_pos_right (pow_pos (hpos 1) A)).1 ((norm_nonneg _).trans (hB 1))
  have hγc : Continuous γ := by
    obtain ⟨w, τ, Z, _, hy⟩ := hγ
    choose y hγ' hy using hy
    have hc : Continuous y := by
      rw [(GlobalTheory.Orb.isEmbedding_archMat J h τ).continuous_iff]
      have e : (GlobalTheory.Orb.matCoord (GlobalTheory.Orb.archMat σ J τ) ∘ y) = fun t i j => NormedSpace.exp (t • Z) i j := by
        funext t i j; simp only [Function.comp_apply, GlobalTheory.Orb.matCoord, hy t]
      rw [e]
      have hexp : Continuous fun t : ℝ => NormedSpace.exp (t • Z) := by
        letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
        letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
        letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
        exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
      exact continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp ((continuous_apply i).comp hexp)
    have : γ = fun t => embArch σ J w (y t) := funext hγ'
    rw [this]
    exact (continuous_embArch σ J w).comp hc
  have hht : Continuous fun g : GAd σ J => (height σ J g : ℝ) :=
    NNReal.continuous_coe.comp (GlobalTheory.AdelicU.continuous_height_GAd σ J)
  obtain ⟨c, hc'⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).image (hht.comp hγc)).bddAbove
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ g, ‖lineDer γ φ g - t⁻¹ • (φ (g * γ t) - φ g)‖ ≤
      B * ((height σ J g : ℝ) * c) ^ A * t := fun t t0 t1 g => by
    set q := t⁻¹ • (φ (g * γ t) - φ g) with hq
    have d1 := GlobalTheory.UAut.ConstAut.hasDerivAt_foldr h hs (l := []) (by simp) hγ g
    have d2 := GlobalTheory.UAut.ConstAut.hasDerivAt_foldr h hs (l := [γ]) (by simpa using hγ) hγ g
    simp only [List.foldr_cons, List.foldr_nil] at d1 d2
    have := GlobalTheory.CuspDecay.mul_norm_deriv_le (f := fun s => φ (g * γ s) - φ g - s • q)
      (f₁ := fun s => lineDer γ φ (g * γ s) - q) (f₂ := fun s => lineDer γ (lineDer γ φ) (g * γ s))
      (fun s => by simpa using ((d1 s).sub_const (φ g)).fun_sub ((hasDerivAt_id s).smul_const q))
      (fun s => (d2 s).sub_const q) t0.le (B := B * ((height σ J g : ℝ) * c) ^ A) fun s hs' => (hB _).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hpos _).le
          ((NNReal.coe_le_coe.2 (GlobalTheory.AdelicU.height_mul_le σ J _ _)).trans (by
            rw [NNReal.coe_mul]
            exact mul_le_mul_of_nonneg_left (hc' ⟨s, ⟨hs'.1, hs'.2.trans t1⟩, rfl⟩) (hpos g).le)) A) hB0)
    rw [GlobalTheory.UAut.ConstAut.realLine_zero h hγ, mul_one, hq, smul_inv_smul₀ t0.ne', sub_self, sub_self, zero_smul, sub_self,
      norm_zero, zero_add, zero_add, mul_comm _ t] at this
    exact le_of_mul_le_mul_left this t0
  refine continuous_of_locally_uniform_approx_of_continuousAt fun x u hu => ?_
  obtain ⟨ε, hε, hu⟩ := Metric.mem_uniformity_dist.1 hu
  have hb : Continuous fun g : GAd σ J => B * ((height σ J g : ℝ) * c) ^ A :=
    continuous_const.mul ((hht.mul continuous_const).pow A)
  obtain ⟨t, t0, t1, t2⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ B * ((height σ J x : ℝ) * c) ^ A * t < ε := by
    have : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t ≤ 1 ∧ B * ((height σ J x : ℝ) * c) ^ A * t < ε :=
      eventually_mem_nhdsWithin.and (Filter.Eventually.filter_mono nhdsWithin_le_nhds
        ((eventually_le_nhds zero_lt_one).and
          ((continuous_const.mul continuous_id).continuousAt.eventually_lt continuousAt_const (by simpa using hε))))
    exact this.exists
  refine ⟨_, (isOpen_lt (hb.mul (continuous_const (y := t))) (continuous_const (y := ε))).mem_nhds t2,
    fun g => t⁻¹ • (φ (g * γ t) - φ g),
    (((hc.comp (continuous_mul_const _)).sub hc).const_smul t⁻¹).continuousAt, fun y hy => hu ?_⟩
  rw [dist_eq_norm]
  exact (key t t0 t1 y).trans_lt hy

theorem lineDer_mul_fin {φ : GAd σ J → ℂ} {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) {k : GAd σ J} (hk : k ∈ finPts σ J)
    (e : ∀ g, φ (g * k) = φ g) (g : GAd σ J) : lineDer γ φ (g * k) = lineDer γ φ g := by
  have : (fun t => φ (g * k * γ t)) = fun t => φ (g * γ t) := funext fun t => by
    have hmem : γ t ∈ infPts σ J := by
      obtain ⟨w, τ, Z, -, ht⟩ := hγ
      obtain ⟨y, hy, -⟩ := ht t
      rw [hy]
      exact mem_infPts.2 (projFin_embArch σ J w y)
    have hc := GlobalTheory.CompanionTheory.SiegelAssemble.commute_of_mem hmem hk
    calc
      φ (g * k * γ t) = φ ((g * γ t) * k) := by rw [mul_assoc, ← hc.eq, ← mul_assoc]
      _ = φ (g * γ t) := e _
  simp only [lineDer, this]

theorem isCuspidal_lineDer (h : IsCMExt F E σ) (hJ : IsHermND σ J) {φ : GAd σ J → ℂ} (hl : GlobalTheory.AutomorphicL2Unitary.LeftInv (ratPts σ J) φ)
    (hc : Continuous φ) (hs : GlobalTheory.UAut.IsSm σ J φ) (hcu : IsCuspidal σ J φ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ)
    (hc' : Continuous (lineDer γ φ)) : IsCuspidal σ J (lineDer γ φ) := by
  intro r C hC μ 𝓕 hμ h𝓕 x
  have hI : GlobalTheory.UAut.IsIsoCols σ J C := hC.2
  haveI := GlobalTheory.UAut.locallyCompact_unipRad h hJ hI
  have hco := GlobalTheory.UAut.cocompact_unipRad h hJ hI
  have hl' : GlobalTheory.AutomorphicL2Unitary.LeftInv (ratPts σ J) (lineDer γ φ) := GlobalTheory.UAut.ConstAut.leftInv_foldr hl [γ]
  have h0 : ∀ y, GlobalTheory.Cusp.constTermOn (ratPts σ J) (unipRad σ J C) φ y = 0 := fun y =>
    (hco.constTermOn_eq_zero_iff h𝓕 hl y).2 (hcu r C hC μ 𝓕 hμ h𝓕 y)
  have hd := GlobalTheory.CuspLie.hasDerivAt_constTermOn hco hl hc hl' hc'
    (by
      obtain ⟨w, τ, Z, _, hy⟩ := hγ
      choose y hγ' hy using hy
      have hc : Continuous y := by
        rw [(GlobalTheory.Orb.isEmbedding_archMat J h τ).continuous_iff]
        have e : (GlobalTheory.Orb.matCoord (GlobalTheory.Orb.archMat σ J τ) ∘ y) = fun t i j => NormedSpace.exp (t • Z) i j := by
          funext t i j; simp only [Function.comp_apply, GlobalTheory.Orb.matCoord, hy t]
        rw [e]
        have hexp : Continuous fun t : ℝ => NormedSpace.exp (t • Z) := by
          letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
          letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
          letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
          exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
        exact continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp ((continuous_apply i).comp hexp)
      have : γ = fun t => embArch σ J w (y t) := funext hγ'
      rw [this]
      exact (continuous_embArch σ J w).comp hc)
    (GlobalTheory.UAut.ConstAut.hasDerivAt_foldr h hs (l := []) (by simp) hγ) x
  simp only [h0] at hd
  rw [GlobalTheory.UAut.ConstAut.realLine_zero h hγ, mul_one] at hd
  exact (hco.constTermOn_eq_zero_iff h𝓕 hl' x).1 (hd.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ)))

theorem good_lineDer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (U : Subgroup (GAd σ J)) (A : ℕ) (φ : GAd σ J → ℂ) (γ : ℝ → GAd σ J), Good σ J U A φ → IsRealLine σ J γ → Good σ J U A (lineDer γ φ) := by
  intro F E _ _ _ _ _ σ h n J hJ U A φ γ hφ hγ
  obtain ⟨B, hB⟩ := hφ.growth [γ, γ] (by simpa using hγ)
  have hcont : Continuous (lineDer γ φ) :=
    continuous_lineDer_of_growth h hφ.smooth hφ.cont hγ (A := A) (B := B) (by simpa using hB)
  refine ⟨GlobalTheory.UAut.ConstAut.leftInv_foldr hφ.left [γ], fun k hk hf => lineDer_mul_fin hγ hf (hφ.level k hk hf), hcont,
    GlobalTheory.UAut.isSm_lineDer hφ.smooth hγ, fun l hl => ?_,
    isCuspidal_lineDer h hJ hφ.left hφ.cont hφ.smooth hφ.cusp hγ hcont⟩
  have := hφ.growth (l ++ [γ]) (by
    intro δ hδ
    rcases List.mem_append.1 hδ with e | e
    · exact hl δ e
    · rw [List.mem_singleton.1 e]; exact hγ)
  simpa only [List.foldr_append, List.foldr_cons, List.foldr_nil] using this

end GlobalTheory.CompanionTheory.RapidDecay

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodFunctionLineDerivativeStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_function_line_derivative : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (U : Subgroup (GAd σ J)) (A : ℕ) (φ : GAd σ J → ℂ) (γ : ℝ → GAd σ J), Good σ J U A φ → IsRealLine σ J γ → Good σ J U A (lineDer γ φ) := by
  first | exact @GlobalTheory.CompanionTheory.RapidDecay.good_lineDer | exact GlobalTheory.CompanionTheory.RapidDecay.good_lineDer | (intros; apply GlobalTheory.CompanionTheory.RapidDecay.good_lineDer <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelSetUniformSmoothBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelSetUniformSmoothBound
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay.Mean

open GlobalTheory.LeviHC GlobalTheory.LeviHC.LineLie GlobalTheory.SmoothForms

section OnePlace

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {w : InfinitePlace F}

theorem norm_le_of_entries {X : Matrix (Fin n) (Fin n) ℂ} {r : ℝ} (hr : 0 ≤ r) (h : ∀ i j, ‖X i j‖ ≤ r) :
    ‖X‖ ≤ n * r := by
  have key : ‖X‖₊ ≤ (n : ℝ≥0) * r.toNNReal := by
    rw [Matrix.linfty_opNNNorm_def]
    refine Finset.sup_le fun i _ => ?_
    calc ∑ j, ‖X i j‖₊ ≤ ∑ _j : Fin n, r.toNNReal :=
          Finset.sum_le_sum fun j _ => by
            rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hr]
            exact h i j
      _ = (n : ℝ≥0) * r.toNNReal := by simp
  have key' := NNReal.coe_le_coe.mpr key
  simpa [Real.coe_toNNReal _ hr] using key'

theorem expMap_zero (h : IsCMExt F E σ) (τ : EmbOver E w) :
    expMap (jA (J.map τ.1)) (secA σ J τ) 0 = 1 := by
  show secA σ J τ (NormedSpace.exp ((jA (J.map τ.1)) 0)) = 1
  rw [map_zero, NormedSpace.exp_zero, ← map_one (archMat σ J τ), secA_archMat h, map_one]

theorem expMap_add (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) (Z : LieL (J.map τ.1)) (s t : ℝ) :
    expMap (jA (J.map τ.1)) (secA σ J τ) ((s + t) • Z) =
      expMap (jA (J.map τ.1)) (secA σ J τ) (s • Z) * expMap (jA (J.map τ.1)) (secA σ J τ) (t • Z) := by
  obtain ⟨y1, e1, a1⟩ := isLineOf_expMap h hJ τ Z s
  obtain ⟨y2, e2, a2⟩ := isLineOf_expMap h hJ τ Z t
  obtain ⟨y3, e3, a3⟩ := isLineOf_expMap h hJ τ Z (s + t)
  beta_reduce at e1 e2 e3
  rw [e1, e2, e3, ← map_mul]
  congr 1
  apply archMat_injective h τ
  rw [map_mul, a1, a2, a3, add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl _).smul_left s).smul_right t)

theorem one_place (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) :
    ∃ (ι : Type) (_ : Fintype ι) (b : ι → ℝ → GAd σ J) (K : Set (GArch σ J w)) (C δ₁ : ℝ),
      (∀ i, IsRealLine σ J (b i)) ∧ IsCompact K ∧ 1 ∈ K ∧ 0 < δ₁ ∧ 0 ≤ C ∧
      ∀ (y : GArch σ J w) (δ : ℝ), 0 ≤ δ → δ ≤ δ₁ → (∀ i j, ‖(archMat σ J τ y - 1) i j‖ ≤ δ) →
        y ∈ K ∧ ∀ ψ : GAd σ J → ℂ, GlobalTheory.UAut.IsSm σ J ψ → ∀ (g : GAd σ J) (c : ι → ℝ),
          (∀ i, ∀ x ∈ K, ‖lineDer (b i) ψ (g * embArch σ J w x)‖ ≤ c i) →
          ‖ψ (g * embArch σ J w y) - ψ g‖ ≤ C * δ * ∑ i, c i := by
  have hA := isUnit_det_map hJ τ.1
  obtain ⟨δ₁, C₀, h1, hlog⟩ := GlobalTheory.UnitaryLog.exists_log_unitary n (J.map τ.1) hA
  haveI : FiniteDimensional ℝ (LieL (J.map τ.1)) := inferInstance
  haveI : ProperSpace (LieL (J.map τ.1)) := FiniteDimensional.proper_real _
  let b := Module.finBasis ℝ (LieL (J.map τ.1))
  obtain ⟨K₀, hK₀, hco⟩ := GlobalTheory.CuspGeo.MeanValue.exists_coord_bound b
  choose yOf hy1 hy2 using fun Y : LieL (J.map τ.1) => isLineOf_expMap h hJ τ Y 1
  simp only [one_smul] at hy1 hy2
  have hyc : Continuous yOf := (GlobalTheory.Orb.isEmbedding_archMat J h τ).continuous_iff.2 (by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    change Continuous fun Y => archMat σ J τ (yOf Y) i j
    simp only [hy2]
    have : Continuous fun Y : LieL (J.map τ.1) => NormedSpace.exp Y.1 :=
      (NormedSpace.exp_continuous).comp continuous_subtype_val
    exact (continuous_apply j).comp ((continuous_apply i).comp this))
  have hy0 : yOf 0 = 1 := archMat_injective h τ (by
    rw [hy2, map_one]; simp)
  set C₁ : ℝ := n * |C₀| with hC₁
  have hC₁0 : 0 ≤ C₁ := mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  refine ⟨_, inferInstance, fun i t => expMap (jA (J.map τ.1)) (secA σ J τ) (t • b i),
    yOf '' Metric.closedBall 0 (C₁ * δ₁), K₀ * C₁, δ₁, fun i => (isLineOf_expMap h hJ τ (b i)).isRealLine h,
    (isCompact_closedBall _ _).image hyc, ⟨0, ?_, hy0⟩, h1, mul_nonneg hK₀ hC₁0, fun y δ h0 hδ hy => ?_⟩
  · simpa using mul_nonneg hC₁0 h1.le
  have hU : (archMat σ J τ y)ᴴ * J.map τ.1 * archMat σ J τ y = J.map τ.1 := by
    rw [GlobalTheory.Orb.archMat_eq_archEquiv J h]
    exact (archEquiv J h τ y).2
  obtain ⟨X, hX, hE, hB⟩ := hlog (archMat σ J τ y) δ hU hδ hy
  let Z : LieL (J.map τ.1) := ⟨X, hX⟩
  have hZ : ‖Z‖ ≤ C₁ * δ := by
    have := norm_le_of_entries (mul_nonneg (abs_nonneg C₀) h0) fun i j =>
      (hB i j).trans (mul_le_mul_of_nonneg_right (le_abs_self C₀) h0)
    rw [hC₁, mul_assoc]
    exact this
  have hyZ : yOf Z = y := archMat_injective h τ (by rw [hy2, ← hE])
  have hball : ∀ t ∈ Set.Icc (0 : ℝ) 1, t • Z ∈ Metric.closedBall (0 : LieL (J.map τ.1)) (C₁ * δ₁) := fun t ht => by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans (hZ.trans (mul_le_mul_of_nonneg_left hδ hC₁0))
  refine ⟨⟨Z, by simpa using hball 1 (by simp), hyZ⟩, fun ψ hψ g c hc => ?_⟩
  rw [← hyZ, ← hy1 Z]
  refine GlobalTheory.CuspGeo.MeanValue.norm_sub_le _ (expMap_zero h τ) (expMap_add h hJ τ) b (sm_of_isSm h hJ τ hψ) g Z _
    (fun i => (hco Z i).trans ?_) c fun i t ht => ?_
  · rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hZ hK₀
  · have := hc i (yOf (t • Z)) ⟨_, hball t ht, rfl⟩
    rw [← hy1] at this
    exact this

end OnePlace

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

def pt (a : ∀ w, GArch σ J w) : GAd σ J := ofInf σ J (embArchPi σ J a)

theorem pt_mul_single [DecidableEq (InfinitePlace F)] (a : ∀ w, GArch σ J w) (w : InfinitePlace F) (x : GArch σ J w) :
    pt (a * Pi.mulSingle w x) = pt a * embArch σ J w x := by
  show ofInf σ J (embArchPi σ J (a * Pi.mulSingle w x)) = ofInf σ J (embArchPi σ J a) * embArch σ J w x
  rw [map_mul, map_mul, embArchPi_mulSingle]
  rfl

theorem pt_one : pt (1 : ∀ w, GArch σ J w) = 1 := by
  simp only [pt, map_one]

theorem pt_proj {u : GAd σ J} (hu : u ∈ infPts σ J) : pt (fun w => projArch σ J w u) = u := by
  refine GAd_ext σ J (fun w' => ?_) (fun v => ?_)
  · rw [pt, projArch_ofInf, projInfArch_embArchPi]
  · rw [pt, proj_ofInf, mem_infPts_iff_forall.mp hu v]

theorem continuous_pt : Continuous (pt : (∀ w, GArch σ J w) → GAd σ J) := by
  show Continuous fun a => ofInf σ J (embArchPi σ J a)
  exact (continuous_ofInf σ J).comp (continuous_embArchPi σ J)


open Classical in
theorem telescope {ι : InfinitePlace F → Type} [∀ w, Fintype (ι w)] {b : ∀ w, ι w → ℝ → GAd σ J}
    {K : ∀ w, Set (GArch σ J w)} {C : InfinitePlace F → ℝ} (h1 : ∀ w, 1 ∈ K w) {ψ : GAd σ J → ℂ} (g : GAd σ J)
    {y : ∀ w, GArch σ J w} (hyK : ∀ w, y w ∈ K w) {δ : ℝ} {c : ∀ w, ι w → ℝ}
    (hstep : ∀ w (g : GAd σ J), (∀ i, ∀ x ∈ K w, ‖lineDer (b w i) ψ (g * embArch σ J w x)‖ ≤ c w i) →
      ‖ψ (g * embArch σ J w (y w)) - ψ g‖ ≤ C w * δ * ∑ i, c w i)
    (hc : ∀ w i, ∀ x ∈ pt '' Set.pi Set.univ K, ‖lineDer (b w i) ψ (g * x)‖ ≤ c w i)
    (S : Finset (InfinitePlace F)) :
    ‖ψ (g * pt fun w => if w ∈ S then y w else 1) - ψ g‖ ≤ ∑ w ∈ S, C w * δ * ∑ i, c w i := by
  induction S using Finset.induction_on with
  | empty =>
    have h0 : (fun w => if w ∈ (∅ : Finset (InfinitePlace F)) then y w else 1) = (1 : ∀ w, GArch σ J w) := by
      funext w
      simp
    rw [h0, pt_one, mul_one, sub_self, norm_zero, Finset.sum_empty]
  | @insert v S hv ih =>
    set a : ∀ w, GArch σ J w := fun w => if w ∈ S then y w else 1 with ha
    have hsplit : (fun w => if w ∈ insert v S then y w else 1) = a * Pi.mulSingle v (y v) := by
      funext w
      by_cases hw : w = v
      · subst hw
        simp [ha, hv]
      · simp only [Pi.mul_apply, Pi.mulSingle_eq_of_ne hw, mul_one, ha, Finset.mem_insert, hw, false_or]
    have hK : ∀ x ∈ K v, a * Pi.mulSingle v x ∈ Set.pi Set.univ K := by
      intro x hx
      rw [Set.mem_univ_pi]
      intro w
      by_cases hw : w = v
      · subst hw
        simp [ha, hv, hx]
      · simp only [Pi.mul_apply, Pi.mulSingle_eq_of_ne hw, mul_one, ha]
        split_ifs
        · exact hyK w
        · exact h1 w
    have step := hstep v (g * pt a) (fun i x hx => by
      rw [mul_assoc, ← pt_mul_single]
      exact hc v i _ ⟨_, hK x hx, rfl⟩)
    rw [hsplit, pt_mul_single, Finset.sum_insert hv, ← mul_assoc]
    calc _ = ‖(ψ (g * pt a * embArch σ J v (y v)) - ψ (g * pt a)) + (ψ (g * pt a) - ψ g)‖ := by
          rw [sub_add_sub_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add step ih)

end Places

theorem mean_value : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∃ (m : ℕ) (b : Fin m → ℝ → GAd σ J) (Ω₀ : Set (GAd σ J)) (C δ₁ : ℝ), (∀ i, IsRealLine σ J (b i)) ∧ IsCompact Ω₀ ∧ 0 < δ₁ ∧ 0 ≤ C ∧ ∀ ψ : GAd σ J → ℂ, GlobalTheory.UAut.IsSm σ J ψ → ∀ (g u : GAd σ J) (δ : ℝ), 0 ≤ δ → δ ≤ δ₁ → CloseInf σ J u δ → ∀ c : Fin m → ℝ, (∀ i, ∀ x ∈ Ω₀, ‖lineDer (b i) ψ (g * x)‖ ≤ c i) → ‖ψ (g * u) - ψ g‖ ≤ C * δ * ∑ i, c i := by
  intro F E _ _ _ _ _ σ h n J hJ
  classical
  have τ : ∀ w : InfinitePlace F, EmbOver E w := fun w => Classical.arbitrary _
  choose ι hι b K C d hb hK h1K hd hC key using fun w => one_place (J := J) h hJ (τ w)
  letI : ∀ w, Fintype (ι w) := hι
  obtain ⟨δ₁, hδ₁, hle⟩ : ∃ δ₁ > 0, ∀ w, δ₁ ≤ d w := by
    obtain ⟨w₀, h0⟩ := Finite.exists_min d
    exact ⟨d w₀, hd w₀, h0⟩
  let e := Fintype.equivFin (Σ w, ι w)
  have hCs : 0 ≤ ∑ w, C w := Finset.sum_nonneg fun w _ => hC w
  refine ⟨_, fun i => b (e.symm i).1 (e.symm i).2, pt '' Set.pi Set.univ K, ∑ w, C w, δ₁, fun i => hb _ _,
    (isCompact_univ_pi hK).image continuous_pt, hδ₁, hCs, fun ψ hψ g u δ h0 hδ hu c hc => ?_⟩
  let c' : ∀ w, ι w → ℝ := fun w i => c (e ⟨w, i⟩)
  have hc' : ∀ w i, ∀ x ∈ pt '' Set.pi Set.univ K, ‖lineDer (b w i) ψ (g * x)‖ ≤ c' w i := fun w i x hx => by
    have aux : ∀ p q : Σ w, ι w, p = q → lineDer (b p.1 p.2) ψ = lineDer (b q.1 q.2) ψ := by
      rintro _ _ rfl; rfl
    have := hc (e ⟨w, i⟩) x hx
    rwa [aux _ ⟨w, i⟩ (e.symm_apply_apply _)] at this
  have hnn : ∀ w i, 0 ≤ c' w i := fun w i =>
    (norm_nonneg _).trans (hc' w i 1 ⟨1, fun w _ => h1K w, pt_one⟩)
  have hclose := fun w => key w (projArch σ J w u) δ h0 (hδ.trans (hle w)) (hu.2 w (τ w))
  have T := telescope (b := b) (K := K) (C := C) h1K (ψ := ψ) g (y := fun w => projArch σ J w u)
    (fun w => (hclose w).1) (δ := δ) (c := c') (fun w g' hg' => (hclose w).2 ψ hψ g' (c' w) hg') hc' Finset.univ
  have hfull : (fun w => if w ∈ (Finset.univ : Finset (InfinitePlace F)) then projArch σ J w u else 1) =
      fun w => projArch σ J w u := by
    funext w; simp
  rw [hfull, pt_proj hu.1] at T
  refine T.trans ?_
  have hsum : ∑ i, c i = ∑ w, ∑ i, c' w i := by
    rw [← Equiv.sum_comp e c, Fintype.sum_sigma]
  have hT : ∀ w, ∑ i, c' w i ≤ ∑ i, c i := fun w => by
    rw [hsum]
    exact Finset.single_le_sum (f := fun w => ∑ i, c' w i)
      (fun w _ => Finset.sum_nonneg fun i _ => hnn w i) (Finset.mem_univ w)
  rw [Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hT w) (mul_nonneg (hC w) h0)

end GlobalTheory.CompanionTheory.RapidDecay.Mean

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelSetUniformSmoothBoundStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_set_uniform_smooth_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∃ (m : ℕ) (b : Fin m → ℝ → GAd σ J) (Ω₀ : Set (GAd σ J)) (C δ₁ : ℝ), (∀ i, IsRealLine σ J (b i)) ∧ IsCompact Ω₀ ∧ 0 < δ₁ ∧ 0 ≤ C ∧ ∀ ψ : GAd σ J → ℂ, GlobalTheory.UAut.IsSm σ J ψ → ∀ (g u : GAd σ J) (δ : ℝ), 0 ≤ δ → δ ≤ δ₁ → CloseInf σ J u δ → ∀ c : Fin m → ℝ, (∀ i, ∀ x ∈ Ω₀, ‖lineDer (b i) ψ (g * x)‖ ≤ c i) → ‖ψ (g * u) - ψ g‖ ≤ C * δ * ∑ i, c i := by
  exact GlobalTheory.CompanionTheory.RapidDecay.Mean.mean_value
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionFour
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionFour
noncomputable section

namespace GlobalTheory.CompanionTheory.DiscriminantUnit

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

theorem decomp {S : Type*} [CommRing S] (σS : S →+* S) (hinv : ∀ a, σS (σS a) = a) {u t w : S}
    (hu : σS u = -u) (ht : σS t = t) (h2 : t * 2 = 1) (hw : w * u = 1) :
    IsUnit (u - σS u) ∧ ∀ a, ∃ x y, σS x = x ∧ σS y = y ∧ a = x + y * u := by
  have hσw : σS w = -w := by
    have h1 : σS w * σS u = 1 := by rw [← map_mul, hw, map_one]
    rw [hu] at h1
    linear_combination (-w) * h1 - (σS w) * hw
  refine ⟨isUnit_iff_exists_inv.2 ⟨t * w, ?_⟩, fun a => ⟨(a + σS a) * t, (a - σS a) * t * w, ?_, ?_, ?_⟩⟩
  · rw [hu]
    linear_combination (w * u) * h2 + hw
  · rw [map_mul, map_add (f := _), hinv, ht]
    ring
  · rw [map_mul, map_mul, map_sub, hinv, ht, hσw]
    ring
  · linear_combination (-a) * h2 - (a - σS a) * t * hw

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem conj_conj (h : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem exists_of_conj_eq (h : IsCMExt F E σ) (e : E) (he : σ e = e) :
    ∃ f, algebraMap F E f = e := by
  haveI := Subalgebra.isSimpleOrder_of_finrank h.2.2.1
  rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h0 | h0
  · have : e ∈ AlgHom.equalizer σ (AlgHom.id F E) := he
    rw [h0, Algebra.mem_bot] at this
    exact this
  · exfalso
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    haveI := h.2.1
    refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have hx : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := h0 ▸ Algebra.mem_top
    have hx' : σ x = x := hx
    have := h.2.2.2 τ x
    rw [hx'] at this
    exact this.symm

theorem trace_field (h : IsCMExt F E σ) (e : E) :
    algebraMap F E (Algebra.trace F E e) = e + σ e := by
  have hσ := conj_conj h
  obtain ⟨a, ha⟩ := exists_of_conj_eq h (e + σ e) (by rw [map_add (f := _), hσ, add_comm])
  have h1 : Algebra.trace F E (σ e) = Algebra.trace F E e :=
    Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)) e
  have h3 := congrArg (Algebra.trace F E) ha
  rw [Algebra.trace_algebraMap, h.2.2.1, map_add (f := _), h1, two_smul, ← two_mul, ← two_mul] at h3
  rw [← ha, mul_left_cancel₀ two_ne_zero h3]

theorem trace_tensor (R : Type) [CommRing R] [Algebra F R] (h : IsCMExt F E σ) (z : R ⊗[F] E) :
    algebraMap R (R ⊗[F] E) (Algebra.trace R (R ⊗[F] E) z) = z + sigR R σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]; ring
  | tmul a e =>
    have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h3 : Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) =
        a * algebraMap F R (Algebra.trace F E e) := by
      rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
        LinearMap.trace_baseChange, smul_eq_mul]
    have h4 : sigR R σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := rfl
    rw [h3, h4, ← TensorProduct.tmul_add, ← trace_field h, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, mul_comm, ← Algebra.smul_def,
      TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]

theorem sigR_sigR (R : Type) [CommRing R] [Algebra F R] (h : IsCMExt F E σ) (z : R ⊗[F] E) :
    sigR R σ (sigR R σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul a e =>
    show a ⊗ₜ[F] σ (σ e) = _
    rw [conj_conj h]

theorem sigR_scalar (R : Type) [CommRing R] [Algebra F R] (c : R) :
    sigR R σ (algebraMap R (R ⊗[F] E) c) = algebraMap R (R ⊗[F] E) c := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

theorem discr_eq (h : IsCMExt F E σ) (bs : Module.Basis (Fin 2) F E) :
    algebraMap F E (Algebra.discr F ⇑bs) = (bs 0 * σ (bs 1) - bs 1 * σ (bs 0)) ^ 2 := by
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, map_sub, map_mul, trace_field h]
  ring

section Ring

variable {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {S : Subring (Fv F v ⊗[F] E)}

theorem smul_mem (hcar : (S : Set (Fv F v ⊗[F] E)) = Rv bs v) {β : Fv F v}
    (hβ : β ∈ v.adicCompletionIntegers F) {x : Fv F v ⊗[F] E} (hx : x ∈ S) : β • x ∈ S := by
  have h1 : x ∈ Rv bs v := by
    rw [← hcar]
    exact hx
  have h2 : β • x ∈ Rv bs v := fun k => by
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact mul_mem hβ (h1 k)
  rw [← hcar] at h2
  exact h2

theorem scalar_mem (hcar : (S : Set (Fv F v ⊗[F] E)) = Rv bs v) {β : Fv F v}
    (hβ : β ∈ v.adicCompletionIntegers F) : algebraMap (Fv F v) (Fv F v ⊗[F] E) β ∈ S := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact smul_mem hcar hβ (one_mem S)

theorem basis_mem (hcar : (S : Set (Fv F v ⊗[F] E)) = Rv bs v) (i : Fin d) :
    Algebra.TensorProduct.basis (Fv F v) bs i ∈ S := by
  have h : Algebra.TensorProduct.basis (Fv F v) bs i ∈ Rv bs v := fun k => by
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  rw [← hcar] at h
  exact h

theorem trace_mem (hcar : (S : Set (Fv F v ⊗[F] E)) = Rv bs v) {a : Fv F v ⊗[F] E} (ha : a ∈ S) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) a ∈ v.adicCompletionIntegers F := by
  rw [Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis (Fv F v) bs), Matrix.trace]
  refine sum_mem fun k _ => ?_
  rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  have h1 : a * Algebra.TensorProduct.basis (Fv F v) bs k ∈ Rv bs v := by
    rw [← hcar]
    exact mul_mem ha (basis_mem hcar k)
  exact h1 k

theorem half_mem (hI : IntAt v (basisSet σ bs)) : (2 : Fv F v)⁻¹ ∈ v.adicCompletionIntegers F := by
  have h := hI (2 : F)⁻¹ (by classical exact Finset.mem_union_right _ (by simp))
  rwa [map_inv₀, map_ofNat] at h

theorem discr_mem (hI : IntAt v (basisSet σ bs)) :
    algebraMap F (Fv F v) (Algebra.discr F (⇑bs))⁻¹ ∈ v.adicCompletionIntegers F :=
  hI _ (by classical exact Finset.mem_union_right _ (by simp))

end Ring

theorem fixed_isUnit {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    {S : Subring (Fv F v ⊗[F] E)} {σS : S →+* S} {ϖ : v.adicCompletionIntegers F}
    (hH : QuadHyp σ bs v S σS ϖ) (hϖ : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ ∈ S) (a : S) (ha : σS a = a)
    (hn : a ∉ lev (⟨_, hϖ⟩ : S) 1) : IsUnit a := by
  obtain ⟨hcm, hI, hcar, hsig, hϖ0, hϖ1, hϖd, hϖc⟩ := hH
  have h20 : (2 : Fv F v) ≠ 0 := by
    have h := (algebraMap F (Fv F v)).injective.ne (two_ne_zero (α := F))
    rwa [map_ofNat, map_zero] at h
  have e2 : algebraMap (Fv F v) (Fv F v ⊗[F] E) (2 : Fv F v)⁻¹ * 2 = 1 := by
    rw [← map_ofNat (algebraMap (Fv F v) (Fv F v ⊗[F] E)) 2, ← map_mul, inv_mul_cancel₀ h20, map_one]
  have hfix : sigR (Fv F v) σ (a : Fv F v ⊗[F] E) = a := by rw [← hsig, ha]
  have hc1 := trace_tensor (Fv F v) hcm (a : Fv F v ⊗[F] E)
  rw [hfix] at hc1
  set c : Fv F v := (2 : Fv F v)⁻¹ * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (a : Fv F v ⊗[F] E) with hc
  have hcO : c ∈ v.adicCompletionIntegers F := mul_mem (half_mem hI) (trace_mem hcar a.2)
  have hac : (a : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) c := by
    rw [hc, map_mul, hc1, ← two_mul, ← mul_assoc, e2, one_mul]
  by_cases hlt : ‖c‖ < 1
  · exfalso
    apply hn
    obtain ⟨c', hc'⟩ := hϖd ⟨c, hcO⟩ hlt
    have hc'' : c = (ϖ : Fv F v) * (c' : Fv F v) := congrArg Subtype.val hc'
    refine Ideal.mem_span_singleton'.2 ⟨⟨_, scalar_mem hcar c'.2⟩, Subtype.ext ?_⟩
    rw [pow_one, Subring.coe_mul, hac, hc'', map_mul, mul_comm]
  · have hle : ‖c‖ ≤ 1 := by
      have h := hcO
      rwa [HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff] at h
    have h1 : ‖c‖ = 1 := le_antisymm hle (not_lt.1 hlt)
    have hc0 : c ≠ 0 := by
      intro h
      rw [h, norm_zero] at h1
      exact zero_ne_one h1
    have hinvO : c⁻¹ ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff, norm_inv, h1,
        inv_one]
    refine isUnit_iff_exists_inv.2 ⟨⟨_, scalar_mem hcar hinvO⟩, Subtype.ext ?_⟩
    rw [Subring.coe_mul, hac]
    show algebraMap (Fv F v) (Fv F v ⊗[F] E) c * algebraMap (Fv F v) (Fv F v ⊗[F] E) c⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hc0, map_one]

theorem exists_split {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    {S : Subring (Fv F v ⊗[F] E)} {σS : S →+* S} {ϖ : v.adicCompletionIntegers F}
    (hH : QuadHyp σ bs v S σS ϖ) :
    ∃ u : S, IsUnit (u - σS u) ∧ ∀ a, ∃ x y, σS x = x ∧ σS y = y ∧ a = x + y * u := by
  obtain ⟨hcm, hI, hcar, hsig, -⟩ := hH
  have hd : d = 2 := by
    have h := Module.finrank_eq_card_basis bs
    rw [hcm.2.2.1] at h
    simpa using h.symm
  subst hd
  have h20 : (2 : Fv F v) ≠ 0 := by
    have h := (algebraMap F (Fv F v)).injective.ne (two_ne_zero (α := F))
    rwa [map_ofNat, map_zero] at h
  have hinv : ∀ a, σS (σS a) = a := fun a => Subtype.ext (by rw [hsig, hsig, sigR_sigR _ hcm])
  let ι : E →ₐ[F] Fv F v ⊗[F] E := Algebra.TensorProduct.includeRight
  let B : Fin 2 → S := fun i => ⟨_, basis_mem hcar i⟩
  have hB : ∀ i, ((B i : S) : Fv F v ⊗[F] E) = ι (bs i) := fun i =>
    Algebra.TensorProduct.basis_apply _ _
  have hσB : ∀ i, ((σS (B i) : S) : Fv F v ⊗[F] E) = ι (σ (bs i)) := fun i => by
    rw [hsig, hB]
    rfl
  obtain ⟨u, hudef⟩ : ∃ u : S, u = B 0 * σS (B 1) - B 1 * σS (B 0) := ⟨_, rfl⟩
  have hu : σS u = -u := by
    rw [hudef, map_sub, map_mul, map_mul, hinv, hinv]
    ring
  have huc : (u : Fv F v ⊗[F] E) = ι (bs 0 * σ (bs 1) - bs 1 * σ (bs 0)) := by
    rw [hudef, AddSubgroupClass.coe_sub, Subring.coe_mul, Subring.coe_mul, hB, hB, hσB, hσB, map_sub, map_mul, map_mul]
  have hsq : (u : Fv F v ⊗[F] E) * u =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) (Algebra.discr F ⇑bs)) := by
    rw [huc, ← map_mul, ← pow_two, ← discr_eq hcm, ι.commutes, IsScalarTower.algebraMap_apply F (Fv F v)]
  have hD : Algebra.discr F ⇑bs ≠ 0 := Algebra.discr_not_zero_of_basis F bs
  have hw : (⟨_, scalar_mem hcar (discr_mem hI)⟩ * u : S) * u = 1 := by
    refine Subtype.ext ?_
    rw [Subring.coe_mul, Subring.coe_mul, mul_assoc, hsq]
    show algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) (Algebra.discr F ⇑bs)⁻¹) * _ = 1
    rw [← map_mul, ← map_mul, inv_mul_cancel₀ hD, map_one, map_one]
  have ht : σS ⟨_, scalar_mem hcar (half_mem hI)⟩ = ⟨_, scalar_mem hcar (half_mem hI)⟩ :=
    Subtype.ext (by rw [hsig]; exact sigR_scalar _ _)
  have h2 : (⟨_, scalar_mem hcar (half_mem hI)⟩ : S) * 2 = 1 := by
    refine Subtype.ext ?_
    rw [Subring.coe_mul]
    show algebraMap (Fv F v) (Fv F v ⊗[F] E) (2 : Fv F v)⁻¹ * 2 = 1
    rw [← map_ofNat (algebraMap (Fv F v) (Fv F v ⊗[F] E)) 2, ← map_mul, inv_mul_cancel₀ h20, map_one]
  exact ⟨u, decomp σS hinv hu ht h2 hw⟩

theorem q4 : PositivityTheory.SiegelWeilFormula.Gunr.Q4 := by
  intro F E _ _ _ _ _ σ d bs v S σS ϖ hH hϖ
  exact ⟨fun a ha hn => fixed_isUnit hH hϖ a ha hn, exists_split hH⟩

end GlobalTheory.CompanionTheory.DiscriminantUnit

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionFourStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_quadratic_condition_four : PositivityTheory.SiegelWeilFormula.Gunr.Q4 := by
  first | exact @GlobalTheory.CompanionTheory.DiscriminantUnit.q4 | exact GlobalTheory.CompanionTheory.DiscriminantUnit.q4 | (intros; apply GlobalTheory.CompanionTheory.DiscriminantUnit.q4 <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdeleMapMemIntAdIff
open NumberField IsDedekindDomain
open scoped NumberField.AdeleRing TensorProduct
open PositivityTheory.RgEis PositivityTheory.RgEis.So GroundTheory.Global GroundTheory.Global.AdeleBaseChange GroundTheory.Automorphic.Reduction

namespace GlobalTheory.CompanionTheory.RgEisBInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_below_eq (v : HeightOneSpectrum (𝓞 F)) :
    ∃ w : HeightOneSpectrum (𝓞 E), below F w = v := by
  have hker : RingHom.ker (algebraMap (𝓞 F) (𝓞 E)) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))
  obtain ⟨Q, -, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (⊥ : Ideal (𝓞 E))
    (hker.le.trans bot_le)
  have hne : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQv]
    exact hker
  exact ⟨⟨Q, hQ, hne⟩, HeightOneSpectrum.ext hQv⟩

theorem adeleMap_mem_intAd_iff (x : 𝔸[F]) : adeleMap F E x ∈ intAd E ↔ x ∈ intAd F := by
  have key : ∀ w : HeightOneSpectrum (𝓞 E),
      finEval w (adeleMap F E x) ∈ w.adicCompletionIntegers E ↔
        finEval (below F w) x ∈ (below F w).adicCompletionIntegers F := by
    intro w
    haveI := liesOver_below (K := F) w
    haveI := w.isPrime
    have h1 : finEval w (adeleMap F E x) =
        SemiLocal.completionMap (below F w) w (finEval (below F w) x) :=
      finiteAdeleMap_apply x.2 w
    rw [h1, HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
      SemiLocal.valued_completionMap]
    exact pow_le_one_iff (Ideal.ramificationIdx_pos (R := 𝓞 F) w.asIdeal).ne'
  simp only [intAd, Subring.mem_iInf, Subring.mem_comap]
  constructor
  · intro h v
    obtain ⟨w, rfl⟩ := exists_below_eq (E := E) v
    exact (key w).1 (h w)
  · intro h w
    exact (key w).2 (h _)

theorem nuCM_eqv (x : 𝔸[F]) : eqv F E (nuCM F E x) = adeleMap F E x := by
  have h := (GroundTheory.BlockD.ThmBHecke.adeleEquiv F E).commutes x
  exact h

theorem bInt : BInt := by
  unfold BInt ForCM
  intro F E _ _ _ _ _ σ χ c _ _ _ _ x
  simp only [adCM, Subring.mem_comap]
  change eqv F E (nuCM F E x) ∈ intAd E ↔ _
  rw [nuCM_eqv, adeleMap_mem_intAd_iff]

end GlobalTheory.CompanionTheory.RgEisBInt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Jtop
open PositivityTheory.RgEis PositivityTheory.RgEis.So
open NumberField Matrix
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.EisSo

theorem jtop : JTop := by
  intro F E R _ _ _ _ _ _ _ _ _ _ A ε ν _ δ _ _ ι _ _ _ j hA hB _ hJ
  have hcv : Continuous ν := hB.cont

  have hval : Continuous fun x : cover A ν ι => (((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) := by
    have e : (fun x : cover A ν ι => (((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) = fun x =>
        (x.1.1 : R) • ((((dg ι (Units.map A.i.toMonoidHom δ))⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) *
          ((x.1.2 : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]).map ν) *
          ((dg ι (Units.map A.i.toMonoidHom δ) : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) := by
      funext x; rw [hJ x]; rfl
    rw [e]
    have h1 : Continuous fun x : cover A ν ι => (x.1.1 : R) :=
      Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)
    have h2 : Continuous fun x : cover A ν ι => (x.1.2 : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) :=
      Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)
    exact h1.smul ((continuous_const.matrix_mul (h2.matrix_map hcv)).matrix_mul continuous_const)
  have hjGL : Continuous fun x : cover A ν ι => ((j x).1 : GL (ι ⊕ ι) R) := by
    refine Units.continuous_iff.2 ⟨hval, ?_⟩
    have e : (fun x : cover A ν ι => (((((j x).1 : GL (ι ⊕ ι) R))⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) =
        (fun x : cover A ν ι => (((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) ∘ fun x => x⁻¹ := by
      funext x; simp [map_inv]
    rw [e]; exact hval.comp continuous_inv
  have hum : ∀ {S T : Type} [CommRing S] [CommRing T] [TopologicalSpace S] [TopologicalSpace T]
      [IsTopologicalRing S] (φ : S →+* T), Continuous φ → Continuous (Units.map φ.toMonoidHom) := by
    intro S T _ _ _ _ _ φ hφ
    exact Units.continuous_iff.2 ⟨hφ.comp Units.continuous_val, hφ.comp (Units.continuous_val.comp continuous_inv)⟩
  have hdet : Continuous (Matrix.GeneralLinearGroup.det : GL (ι ⊕ ι) 𝔸[F] → 𝔸[F]ˣ) :=
    Units.continuous_iff.2 ⟨Units.continuous_val.matrix_det, (Units.continuous_val.comp continuous_inv).matrix_det⟩
  haveI : SecondCountableTopology Rᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) := inferInstanceAs (SecondCountableTopology (ι ⊕ ι → ι ⊕ ι → 𝔸[F]))
  haveI : SecondCountableTopology (Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F])ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology Rˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SecondCountableTopology (GL (ι ⊕ ι) 𝔸[F]) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : LocallyCompactSpace Rˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (ι ⊕ ι) 𝔸[F]) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  have hf : Continuous fun x : Rˣ × GL (ι ⊕ ι) 𝔸[F] =>
      x.1 * Units.map A.σ.toMonoidHom x.1 * Units.map ν.toMonoidHom (Matrix.GeneralLinearGroup.det x.2) :=
    (continuous_fst.mul ((hum A.σ hA.σcont).comp continuous_fst)).mul ((hum ν hcv).comp (hdet.comp continuous_snd))
  have hcl : IsClosed (cover A ν ι : Set (Rˣ × GL (ι ⊕ ι) 𝔸[F])) := by
    have e : (cover A ν ι : Set (Rˣ × GL (ι ⊕ ι) 𝔸[F])) = (fun x : Rˣ × GL (ι ⊕ ι) 𝔸[F] =>
        x.1 * Units.map A.σ.toMonoidHom x.1 * Units.map ν.toMonoidHom (Matrix.GeneralLinearGroup.det x.2)) ⁻¹' {1} :=
      Set.ext fun x => Iff.rfl
    rw [e]; exact isClosed_singleton.preimage hf
  haveI : T2Space Rˣ := Units.isEmbedding_embedProduct.t2Space
  haveI : T2Space (GL (ι ⊕ ι) 𝔸[F]) := Units.isEmbedding_embedProduct.t2Space
  haveI : T2Space (Rˣ × GL (ι ⊕ ι) 𝔸[F]) := inferInstance
  haveI : SecondCountableTopology (Rˣ × GL (ι ⊕ ι) 𝔸[F]) := inferInstance
  exact ⟨hjGL.subtype_mk _, inferInstance, hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    Topology.IsEmbedding.subtypeVal.secondCountableTopology⟩

end GlobalTheory.CompanionTheory.EisSo
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtensionEmbeddingAlgebraMapOfTotallyReal
noncomputable section

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.AdeleRing NumberField.LiesOver TensorProduct
open PositivityTheory.RgEis PositivityTheory.RgEis.So
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace GlobalTheory.CompanionTheory.RgEisSo

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem embedding_algebraMap_of_totallyReal (hF : IsTotallyReal F) (w : InfinitePlace E) (x : F) :
    w.embedding (algebraMap F E x) = (w.comap (algebraMap F E)).embedding x := by
  have hreal : ComplexEmbedding.IsReal (w.comap (algebraMap F E)).embedding :=
    InfinitePlace.isReal_iff.1 (IsTotallyReal.isReal _)
  have h : InfinitePlace.mk (w.embedding.comp (algebraMap F E)) =
      InfinitePlace.mk (w.comap (algebraMap F E)).embedding := by
    rw [InfinitePlace.mk_embedding, ← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
  rcases InfinitePlace.mk_eq_iff.1 h with h | h
  · exact congrArg (fun f : F →+* ℂ => f x) h
  · have h' : w.embedding.comp (algebraMap F E) = (w.comap (algebraMap F E)).embedding := by
      have h2 : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate (w.embedding.comp (algebraMap F E))) =
          w.embedding.comp (algebraMap F E) := star_star _
      rw [← h2, h]
      exact ComplexEmbedding.isReal_iff.1 hreal
    exact congrArg (fun f : F →+* ℂ => f x) h'

theorem extensionEmbedding_algebraMap_of_totallyReal (hF : IsTotallyReal F) (w : InfinitePlace E)
    (z : (w.comap (algebraMap F E)).Completion) :
    extensionEmbedding w (algebraMap (w.comap (algebraMap F E)).Completion w.Completion z) =
      extensionEmbedding (w.comap (algebraMap F E)) z := by
  rw [AbsoluteValue.Completion.algebraMap_eq_of_liesOver (w.comap (algebraMap F E)).1 w.1]
  have h := (denseRange_coe (v := w.comap (algebraMap F E))).equalizer
    (g := fun z => extensionEmbedding w (AbsoluteValue.Completion.map (w.comap (algebraMap F E)).1 w.1 z))
    (h := fun z => extensionEmbedding (w.comap (algebraMap F E)) z)
    ((isometry_extensionEmbedding w).continuous.comp (AbsoluteValue.Completion.continuous_map _ _))
    (isometry_extensionEmbedding _).continuous (funext fun k => ?_)
  · exact congrFun h z
  · have e := LiesOver.completionMap_coe (v := w.comap (algebraMap F E)) (w := w) k
    show extensionEmbedding w (AbsoluteValue.Completion.map (w.comap (algebraMap F E)).1 w.1 (k : (w.comap (algebraMap F E)).Completion)) =
      extensionEmbedding (w.comap (algebraMap F E)) (k : (w.comap (algebraMap F E)).Completion)
    rw [e, extensionEmbedding_coe, extensionEmbedding_coe]
    exact embedding_algebraMap_of_totallyReal hF w _

theorem phi_nuCM (σ : E →ₐ[F] E) (χ : Chr F E) (hF : IsTotallyReal F) (w : InfinitePlace E) (x : 𝔸[F]) :
    (adCM σ χ).φ w (nuCM F E x) = (adStd F).φ (w.comap (algebraMap F E)) x := by
  have h : eqv F E (nuCM F E x) = GroundTheory.Global.AdeleBaseChange.adeleMap F E x :=
    GroundTheory.BlockD.ThmBHecke.adeleEquiv_algebraMap x
  show extensionEmbedding w (GroundTheory.Automorphic.Reduction.infEval w (eqv F E (nuCM F E x))) =
    extensionEmbedding _ (GroundTheory.Automorphic.Reduction.infEval _ x)
  rw [h]
  exact extensionEmbedding_algebraMap_of_totallyReal hF w _

end GlobalTheory.CompanionTheory.RgEisSo

namespace GlobalTheory.CompanionTheory.RgEisSo

theorem bInf : BInf := by
  intro F E _ _ _ _ _ σ χ c hcm _ _ _
  haveI : IsTotallyReal F := hcm.1
  refine ⟨fun w => ⟨w.comap (algebraMap F E), fun x => phi_nuCM σ χ hcm.1 w x⟩, fun v => ?_⟩
  obtain ⟨w, rfl⟩ := InfinitePlace.comap_surjective (k := F) (K := E) v
  exact ⟨w, fun x => phi_nuCM σ χ hcm.1 w x⟩

end GlobalTheory.CompanionTheory.RgEisSo
end
end
