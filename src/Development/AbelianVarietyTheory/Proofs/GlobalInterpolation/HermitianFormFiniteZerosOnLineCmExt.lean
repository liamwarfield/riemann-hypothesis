module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassNumberLeAbsDiscrOfFinrankEqTwo
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivLFunctionStrip

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormFiniteZerosOnLineCmExt
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormFiniteZerosOnLineCmExt
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.HermLineZeros

section Ring

variable {A : Type} [CommRing A] {M : ℕ}

theorem _root_.GlobalTheory.HermLineZeros.hform_expand (s : A →+* A) (J : Matrix (Fin M) (Fin M) A)
    (x y : Fin M → A) (c : A) :
    _root_.Formalism.UG.hform s J (x + c • y) (x + c • y) =
      _root_.Formalism.UG.hform s J x x + c * _root_.Formalism.UG.hform s J x y + s c * _root_.Formalism.UG.hform s J y x
        + s c * c * _root_.Formalism.UG.hform s J y y := by
  unfold _root_.Formalism.UG.hform
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul]
  ring

theorem _root_.GlobalTheory.HermLineZeros.hform_single (s : A →+* A) (J : Matrix (Fin M) (Fin M) A)
    (i j : Fin M) :
    _root_.Formalism.UG.hform s J (Pi.single i 1) (Pi.single j 1) = J i j := by
  simp [_root_.Formalism.UG.hform, Pi.single_apply, apply_ite s]

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem _root_.GlobalTheory.HermLineZeros.conj_invol (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem _root_.GlobalTheory.HermLineZeros.exists_conj_ne (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) : ∃ d, σ d ≠ d := by
  by_contra! hσ
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hreal : ComplexEmbedding.IsReal τ := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have hx := h.2.2.2 τ x
    rw [hσ x] at hx
    simpa [ComplexEmbedding.conjugate_coe_eq] using hx.symm
  have hcx := (h.2.1).isComplex (InfinitePlace.mk τ)
  rw [InfinitePlace.isComplex_mk_iff] at hcx
  exact hcx hreal

theorem _root_.GlobalTheory.HermLineZeros.exists_of_fixed (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (e : E) (he : σ e = e) :
    ∃ f, algebraMap F E f = e := by
  obtain ⟨d, hd⟩ := _root_.GlobalTheory.HermLineZeros.exists_conj_ne h
  let S : Subalgebra F E := AlgHom.equalizer σ (AlgHom.id F E)
  have hS : S ≠ ⊤ := by
    intro hS
    have hdS : d ∈ S := hS ▸ Algebra.mem_top
    exact hd hdS
  have hle : Module.finrank F S ≤ 2 :=
    h.2.2.1 ▸ Submodule.finrank_le (Subalgebra.toSubmodule S)
  have hne : Module.finrank F S ≠ 2 := by
    intro h2
    apply hS
    apply Subalgebra.toSubmodule.injective
    rw [Algebra.top_toSubmodule]
    exact Submodule.eq_top_of_finrank_eq (h2.trans h.2.2.1.symm)
  have hpos : 0 < Module.finrank F S := Module.finrank_pos
  have hbot : S = ⊥ := Subalgebra.finrank_eq_one_iff.mp (by omega)
  have heS : e ∈ S := he
  rw [hbot] at heS
  exact Algebra.mem_bot.mp heS

private theorem hE_self_conj_fixed (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J) (v : Fin M → E) :
    σ (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J v v) = _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J v v := by
  unfold _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE _root_.Formalism.UG.hform
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [AlgHom.coe_toRingHom, map_mul, _root_.GlobalTheory.HermLineZeros.conj_invol h, hJ.1]
  ring

theorem _root_.GlobalTheory.HermLineZeros.exists_anisotropic (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) {M : ℕ} (hM : 1 ≤ M)
    {J : Matrix (Fin M) (Fin M) E} (hJ : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J) :
    ∃ (y : Fin M → E) (a : F), a ≠ 0 ∧ _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J y y = algebraMap F E a := by
  suffices hv : ∃ v, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J v v ≠ 0 by
    obtain ⟨v, hv⟩ := hv
    obtain ⟨a, ha⟩ := _root_.GlobalTheory.HermLineZeros.exists_of_fixed h _ (hE_self_conj_fixed h hJ v)
    refine ⟨v, a, ?_, ha.symm⟩
    rintro rfl
    exact hv (by rw [← ha, map_zero])
  by_cases hd : ∃ i, J i i ≠ 0
  · obtain ⟨i, hi⟩ := hd
    exact ⟨Pi.single i 1, by rwa [_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE, _root_.GlobalTheory.HermLineZeros.hform_single]⟩
  push_neg at hd
  let i₀ : Fin M := ⟨0, hM⟩
  obtain ⟨j, hj⟩ : ∃ j, J i₀ j ≠ 0 := by
    by_contra! hrow
    exact hJ.2 (Matrix.det_eq_zero_of_row_eq_zero i₀ hrow)
  refine ⟨Pi.single i₀ 1 + (J i₀ j)⁻¹ • Pi.single j 1, ?_⟩
  have hji : J j i₀ = σ (J i₀ j) := (hJ.1 j i₀).symm
  rw [_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE, _root_.GlobalTheory.HermLineZeros.hform_expand, _root_.GlobalTheory.HermLineZeros.hform_single,
    _root_.GlobalTheory.HermLineZeros.hform_single, _root_.GlobalTheory.HermLineZeros.hform_single,
    _root_.GlobalTheory.HermLineZeros.hform_single, hd, hd, hji]
  simp only [AlgHom.coe_toRingHom, RingHom.coe_coe]
  rw [inv_mul_cancel₀ hj, ← map_mul, inv_mul_cancel₀ hj, map_one]
  norm_num

theorem _root_.GlobalTheory.HermLineZeros.finite_zeros_on_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (M : ℕ), 1 ≤ M → ∀ (J : Matrix (Fin M) (Fin M) E), _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J → ∀ (K : Type) [Field K] [Algebra F K], ∃ y : Fin M → K ⊗[F] E, ∀ x : Fin M → K ⊗[F] E, {t : K | _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR K σ J (x + t • y) = 0}.Finite := by
  intro F E _ _ _ _ _ σ h M hM J hJ K _ _
  obtain ⟨y₀, a, ha, hy⟩ := _root_.GlobalTheory.HermLineZeros.exists_anisotropic h hM hJ
  let φ : E →ₐ[F] K ⊗[F] E := Algebra.TensorProduct.includeRight
  let S := _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR K σ
  let JR := _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (F := F) K J
  set y : Fin M → K ⊗[F] E := fun i => φ (y₀ i)
  refine ⟨y, fun x => ?_⟩
  have hSc : ∀ t : K, S (algebraMap K (K ⊗[F] E) t) = algebraMap K (K ⊗[F] E) t := fun t => by
    simp [S, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.algebraMap_apply]
  have hSφ : ∀ e : E, S (φ e) = φ (σ e) := fun e => by simp [S, φ, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  have hyy : _root_.Formalism.UG.hform S JR y y = algebraMap K (K ⊗[F] E) (algebraMap F K a) := by
    rw [← IsScalarTower.algebraMap_apply, ← φ.commutes, ← hy]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [_root_.Formalism.UG.hform, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE, map_sum, map_mul, y, hSφ, JR, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Matrix.map_apply, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]
    rfl
  have htr : Algebra.trace K (K ⊗[F] E) (_root_.Formalism.UG.hform S JR y y)
      = Module.finrank K (K ⊗[F] E) • algebraMap F K a := by
    rw [hyy, Algebra.trace_algebraMap]
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  have hfr : Module.finrank K (K ⊗[F] E) ≠ 0 := by
    rw [Module.finrank_baseChange, h.2.2.1]; norm_num
  set α := algebraMap F K (1 / 2) * Algebra.trace K (K ⊗[F] E) (_root_.Formalism.UG.hform S JR y y) with hα
  set β := algebraMap F K (1 / 2) * Algebra.trace K (K ⊗[F] E) (_root_.Formalism.UG.hform S JR x y + _root_.Formalism.UG.hform S JR y x)
  set γ := algebraMap F K (1 / 2) * Algebra.trace K (K ⊗[F] E) (_root_.Formalism.UG.hform S JR x x)
  have hα0 : α ≠ 0 := by
    rw [hα, htr]
    refine mul_ne_zero ?_ (smul_ne_zero hfr ?_)
    · rw [Ne, map_eq_zero_iff _ (algebraMap F K).injective]; norm_num
    · rw [Ne, map_eq_zero_iff _ (algebraMap F K).injective]; exact ha
  let p : Polynomial K := Polynomial.C α * Polynomial.X ^ 2 + Polynomial.C β * Polynomial.X + Polynomial.C γ
  have hp : p ≠ 0 := by
    intro hp
    have := congrArg (fun q : Polynomial K => q.coeff 2) hp
    simp [p, Polynomial.coeff_X, Polynomial.coeff_C] at this
    exact hα0 this
  refine (Polynomial.finite_setOf_isRoot hp).subset fun t ht => ?_
  simp only [Set.mem_setOf_eq] at ht ⊢
  rw [Polynomial.IsRoot.def, ← ht]
  have hsmul : t • y = algebraMap K (K ⊗[F] E) t • y := by
    funext i; simp [Algebra.smul_def]
  have hexp := _root_.GlobalTheory.HermLineZeros.hform_expand S JR x y (algebraMap K (K ⊗[F] E) t)
  rw [hSc] at hexp
  have hq : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR K σ J (x + t • y) = algebraMap F K (1 / 2) *
      Algebra.trace K (K ⊗[F] E) (_root_.Formalism.UG.hform S JR (x + algebraMap K (K ⊗[F] E) t • y)
        (x + algebraMap K (K ⊗[F] E) t • y)) := by
    rw [← hsmul]; rfl
  have htc : ∀ z, Algebra.trace K (K ⊗[F] E) (algebraMap K (K ⊗[F] E) t * z)
      = t * Algebra.trace K (K ⊗[F] E) z := fun z => by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  rw [hq, hexp, mul_assoc (algebraMap K (K ⊗[F] E) t), map_add (f := _), map_add (f := _), map_add (f := _), htc, htc, htc, htc]
  simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, α, β, γ, map_add]
  ring

end GlobalTheory.HermLineZeros
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormFiniteZerosOnLineCmExtStatement
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_finite_zeros_on_line_cmExt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ), 1 ≤ M → ∀ (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (K : Type) [Field K] [Algebra F K], ∃ y : Fin M → K ⊗[F] E, ∀ x : Fin M → K ⊗[F] E, {t : K | qR K σ J (x + t • y) = 0}.Finite := by
  first | exact @GlobalTheory.HermLineZeros.finite_zeros_on_line | exact GlobalTheory.HermLineZeros.finite_zeros_on_line | (intros; apply GlobalTheory.HermLineZeros.finite_zeros_on_line <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableOddTheta
open Complex
open UpperHalfPlane hiding I
open scoped Real

noncomputable section

namespace GlobalTheory.ThetaWeberRoad

def tpFactor (τ : ℍ) (z : ℂ) (n : ℕ) : ℂ :=
  (1 - cexp (2 * π * I * ((n : ℂ) + 1) * (τ : ℂ))) *
    (1 + cexp (π * I * (2 * (n : ℂ) + 1) * (τ : ℂ) + 2 * π * I * z)) *
    (1 + cexp (π * I * (2 * (n : ℂ) + 1) * (τ : ℂ) - 2 * π * I * z))

def TripleProduct : Prop := ∀ (τ : ℍ) (z : ℂ), HasProd (tpFactor τ z) (jacobiTheta₂ z τ)

def oddTheta (τ : ℍ) (z : ℂ) : ℂ :=
  cexp (π * I * (τ : ℂ) / 4 + π * I * (z + 1 / 2)) * jacobiTheta₂ (z + ((τ : ℂ) + 1) / 2) τ

theorem differentiable_oddTheta (τ : ℍ) : Differentiable ℂ (oddTheta τ) := by
  intro z
  have hexp : DifferentiableAt ℂ
      (fun w : ℂ => cexp (π * I * (τ : ℂ) / 4 + π * I * (w + 1 / 2))) z := by
    fun_prop
  have hshift : DifferentiableAt ℂ (fun w : ℂ => w + ((τ : ℂ) + 1) / 2) z :=
    differentiableAt_id.add_const _
  have htheta : DifferentiableAt ℂ
      (fun w : ℂ => jacobiTheta₂ (w + ((τ : ℂ) + 1) / 2) τ) z := by
    have h0 : DifferentiableAt ℂ (fun w : ℂ => jacobiTheta₂ w τ) (z + ((τ : ℂ) + 1) / 2) :=
      differentiableAt_jacobiTheta₂_fst _ τ.2
    exact h0.comp z hshift
  exact hexp.mul htheta

end GlobalTheory.ThetaWeberRoad
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFibreFamilyEqAtContinuityPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFibreFamilyEqAtContinuityPoint
open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Set Topology
open scoped ENNReal

namespace GlobalTheory

private lemma exists_compact_exhaustion_with_bumps {V : Type} [MetricSpace V] [ProperSpace V]
    {G : Set V} (hG : IsOpen G) :
    ∃ (K : ℕ → Set V) (f : ℕ → C(V, ℝ)), Monotone K ∧ ⋃ n, K n = G ∧
      ∀ n, IsCompact (K n) ∧ EqOn (f n) 1 (K n) ∧ IsCompact (tsupport (f n)) ∧
        tsupport (f n) ⊆ G ∧ ∀ v, f n v ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨F, hFc, hFG, hFU, hFm⟩ := hG.exists_iUnion_isClosed
  let E := CompactExhaustion.choice V
  let K : ℕ → Set V := fun n => F n ∩ E n
  have hKm : Monotone K := fun a b hab => inter_subset_inter (hFm hab) (E.subset hab)
  have hKU : ⋃ n, K n = G := by
    apply Subset.antisymm
    · exact iUnion_subset fun n => inter_subset_left.trans (hFG n)
    · intro x hx
      rw [← hFU] at hx
      obtain ⟨a, ha⟩ := mem_iUnion.1 hx
      obtain ⟨b, hb⟩ := E.exists_mem x
      exact mem_iUnion.2 ⟨max a b, hFm (le_max_left a b) ha, E.subset (le_max_right a b) hb⟩
  have hKc : ∀ n, IsCompact (K n) := fun n => (E.isCompact n).inter_left (hFc n)
  choose f hf1 hfc hfG hf01 using fun n =>
    exists_continuousMap_one_of_isCompact_subset_isOpen (hKc n) hG
      (inter_subset_left.trans (hFG n))
  exact ⟨K, f, hKm, hKU, fun n => ⟨hKc n, hf1 n, hfc n, hfG n, hf01 n⟩⟩

private lemma measure_le_lintegral_of_eqOn_one {V : Type} [MeasurableSpace V] (μ : Measure V)
    {K : Set V} (hK : MeasurableSet K) {g : V → ℝ} (hg : EqOn g 1 K) :
    μ K ≤ ∫⁻ v, ENNReal.ofReal (g v) ∂μ := by
  rw [← lintegral_indicator_one hK]
  refine lintegral_mono fun v => ?_
  by_cases hv : v ∈ K
  · simp [indicator_of_mem hv, hg hv]
  · simp [indicator_of_notMem hv]

private lemma measure_isOpen_le_of_lintegral_le {V : Type} [MetricSpace V] [ProperSpace V]
    [MeasurableSpace V] [BorelSpace V] (m m' : Measure V) {G : Set V} (hG : IsOpen G)
    (h : ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ G → (∀ v, 0 ≤ φ v) →
      ∫⁻ v, ENNReal.ofReal (φ v) ∂m ≤ ∫⁻ v, ENNReal.ofReal (φ v) ∂m') :
    m G ≤ m' G := by
  obtain ⟨K, f, hKm, hKU, hKf⟩ := exists_compact_exhaustion_with_bumps hG
  have hGK : m G = ⨆ n, m (K n) := by rw [← hKm.measure_iUnion, hKU]
  rw [hGK]
  refine iSup_le fun n => ?_
  obtain ⟨hKc, hf1, hfc, hfG, hf01⟩ := hKf n
  calc m (K n) ≤ ∫⁻ v, ENNReal.ofReal (f n v) ∂m :=
        measure_le_lintegral_of_eqOn_one m hKc.isClosed.measurableSet hf1
    _ ≤ ∫⁻ v, ENNReal.ofReal (f n v) ∂m' :=
        h (f n) (f n).continuous hfc hfG fun v => (hf01 v).1
    _ ≤ ∫⁻ v, G.indicator 1 v ∂m' := by
        refine lintegral_mono fun v => ?_
        by_cases hv : v ∈ G
        · simp [indicator_of_mem hv, (hf01 v).2]
        · have : f n v = 0 := image_eq_zero_of_notMem_tsupport fun h' => hv (hfG h')
          simp [this]
    _ = m' G := lintegral_indicator_one hG.measurableSet

theorem _root_.GlobalTheory.measure_eq_of_lintegral_eq_on_compactSupport {V : Type} [MetricSpace V] [ProperSpace V]
    [MeasurableSpace V] [BorelSpace V] (m m' : Measure V) (O : Set V) (hO : IsOpen O)
    (hm : m Oᶜ = 0) (hm' : m' Oᶜ = 0)
    (h : ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ O → (∀ v, 0 ≤ φ v) →
      Integrable φ m ∧ ∫⁻ v, ENNReal.ofReal (φ v) ∂m = ∫⁻ v, ENNReal.ofReal (φ v) ∂m') :
    m = m' := by
  have hopen : ∀ G : Set V, IsOpen G → G ⊆ O → m G = m' G := fun G hG hGO =>
    le_antisymm
      (measure_isOpen_le_of_lintegral_le m m' hG fun φ hc hs ht hn =>
        (h φ hc hs (ht.trans hGO) hn).2.le)
      (measure_isOpen_le_of_lintegral_le m' m hG fun φ hc hs ht hn =>
        (h φ hc hs (ht.trans hGO) hn).2.ge)
  obtain ⟨K, f, -, hKU, hKf⟩ := exists_compact_exhaustion_with_bumps hO
  let W : Option ℕ → Set V := fun i => i.elim Oᶜ fun n => {v | 0 < f n v}
  have hWU : ⋃ i, W i = univ := by
    refine eq_univ_of_forall fun v => ?_
    by_cases hv : v ∈ O
    · rw [← hKU] at hv
      obtain ⟨n, hn⟩ := mem_iUnion.1 hv
      exact mem_iUnion.2 ⟨some n, show 0 < f n v by simp [(hKf n).2.1 hn]⟩
    · exact mem_iUnion.2 ⟨none, hv⟩
  rw [Measure.ext_iff_of_iUnion_eq_univ hWU]
  rintro (_ | n)
  · simp [W, Measure.restrict_eq_zero.2 hm, Measure.restrict_eq_zero.2 hm']
  · obtain ⟨-, -, hfc, hfO, -⟩ := hKf n
    have hWo : IsOpen {v | 0 < f n v} := isOpen_lt continuous_const (f n).continuous
    have hsub : {v | 0 < f n v} ⊆ tsupport (f n) := fun v hv =>
      subset_tsupport _ (ne_of_gt (show 0 < f n v from hv))
    have hWO : {v | 0 < f n v} ⊆ O := hsub.trans hfO
    obtain ⟨g, hg1, hgc, hgO, hg01⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hfc hO hfO
    have hfin : m {v | 0 < f n v} < ∞ :=
      (measure_mono hsub).trans_lt <|
        (measure_le_lintegral_of_eqOn_one m hfc.isClosed.measurableSet hg1).trans_lt
          (h g g.continuous hgc hgO fun v => (hg01 v).1).1.lintegral_lt_top
    haveI : IsFiniteMeasure (m.restrict {v | 0 < f n v}) := isFiniteMeasure_restrict.2 hfin.ne
    show m.restrict {v | 0 < f n v} = m'.restrict {v | 0 < f n v}
    refine ext_of_generate_finite {s | IsOpen s} BorelSpace.measurable_eq isPiSystem_isOpen
      (fun s hs => ?_) ?_
    · rw [Measure.restrict_apply hs.measurableSet, Measure.restrict_apply hs.measurableSet]
      exact hopen _ (hs.inter hWo) (inter_subset_right.trans hWO)
    · simpa using hopen _ hWo hWO

theorem _root_.GlobalTheory.IsFibreFamily_lintegral_preimage {V : Type} [TopologicalSpace V]
    [MeasurableSpace V] [BorelSpace V] {μ : Measure V} {f : V → ℝ} {O U : Set V} {B : Set ℝ}
    {fib : ℝ → Measure V}
    (hf : Measurable f) (hO : IsOpen O) (hU : O ⊆ U)
    (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f id U (volume : Measure ℝ) B fib)
    (φ : V → ℝ≥0∞) (hφ : Measurable φ) (hs : ∀ v, v ∉ O → φ v = 0)
    (S : Set ℝ) (hS : MeasurableSet S) :
    ∫⁻ v in O, (f ⁻¹' S).indicator φ v ∂μ = ∫⁻ b in S, ∫⁻ v, φ v ∂(fib b) := by
  unfold _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily at h
  obtain ⟨hfib, hint, -⟩ := h
  have hψ : Measurable ((f ⁻¹' S).indicator φ) := hφ.indicator (hf hS)
  have hsupp : Function.support ((f ⁻¹' S).indicator φ) ⊆ O := by
    intro v hv
    by_contra hvO
    exact hv (by simp [indicator, hs v hvO])
  rw [setLIntegral_eq_of_support_subset hsupp,
    ← setLIntegral_eq_of_support_subset (hsupp.trans hU), hint _ hψ, ← lintegral_indicator hS]
  refine lintegral_congr fun b => ?_
  have hae : ∀ᵐ v ∂(fib b), f v = b := by
    refine ae_iff.2 (measure_mono_null ?_ (hfib b))
    intro v hv hv'
    exact hv hv'.1
  by_cases hb : b ∈ S
  · rw [indicator_of_mem hb]
    exact lintegral_congr_ae (hae.mono fun v hv => by simp [indicator, hv, hb])
  · rw [indicator_of_notMem hb]
    exact (lintegral_congr_ae (hae.mono fun v hv => by simp [indicator, hv, hb])).trans
      lintegral_zero

private lemma le_of_setLIntegral_eq_near {g g' : ℝ → ℝ} {β : ℝ} {W : Set ℝ} (hW : W ∈ 𝓝 β)
    (hg : ContinuousAt g β) (hg' : ContinuousAt g' β) (hg0 : 0 ≤ g' β)
    (h : ∀ S ⊆ W, MeasurableSet S →
      ∫⁻ b in S, ENNReal.ofReal (g b) = ∫⁻ b in S, ENNReal.ofReal (g' b)) :
    g β ≤ g' β := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨c₁, h₁, h₂⟩ := exists_between hlt
  obtain ⟨c₂, h₃, h₄⟩ := exists_between h₂
  have e₁ : ∀ᶠ b in 𝓝 β, g' b < c₁ := hg'.eventually (gt_mem_nhds h₁)
  have e₂ : ∀ᶠ b in 𝓝 β, c₂ < g b := hg.eventually (lt_mem_nhds h₄)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hW (e₁.and e₂))
  have hS : MeasurableSet (Metric.ball β ε) := measurableSet_ball
  have hpos : volume (Metric.ball β ε) ≠ 0 := (Metric.measure_ball_pos volume β hε).ne'
  have hfin : volume (Metric.ball β ε) ≠ ∞ := measure_ball_lt_top.ne
  have low : ENNReal.ofReal c₂ * volume (Metric.ball β ε) ≤
      ∫⁻ b in Metric.ball β ε, ENNReal.ofReal (g b) := by
    rw [← setLIntegral_const]
    exact lintegral_mono_ae ((ae_restrict_iff' hS).2 (Filter.Eventually.of_forall
      fun b hb => ENNReal.ofReal_le_ofReal (hball hb).2.2.le))
  have up : ∫⁻ b in Metric.ball β ε, ENNReal.ofReal (g' b) ≤
      ENNReal.ofReal c₁ * volume (Metric.ball β ε) := by
    rw [← setLIntegral_const]
    exact lintegral_mono_ae ((ae_restrict_iff' hS).2 (Filter.Eventually.of_forall
      fun b hb => ENNReal.ofReal_le_ofReal (hball hb).2.1.le))
  have key := low.trans ((h _ (fun b hb => (hball hb).1) hS).le.trans up)
  have key' : ENNReal.ofReal c₂ ≤ ENNReal.ofReal c₁ := (ENNReal.mul_le_mul_iff_left hpos hfin).1 key
  rw [ENNReal.ofReal_le_ofReal_iff (hg0.trans h₁.le)] at key'
  exact absurd key' (not_le.2 h₃)

theorem _root_.GlobalTheory.IsFibreFamily_eq_at {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) (f : V → ℝ)
    (O U U' : Set V) (B B' : Set ℝ) (fib fib' : ℝ → Measure V) (β : ℝ)
    (hf : Measurable f) (hO : IsOpen O) (hU : O ⊆ U) (hU' : O ⊆ U') (hβ : f ⁻¹' {β} ⊆ O)
    (hB : IsOpen B) (hB' : IsOpen B') (hβB : β ∈ B) (hβB' : β ∈ B')
    (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f id U (volume : Measure ℝ) B fib)
    (h' : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f id U' (volume : Measure ℝ) B' fib') : fib β = fib' β := by
  have hdens := fun (S : Set ℝ) (hS : MeasurableSet S) (φ : V → ℝ≥0∞) (hφ : Measurable φ)
      (hs : ∀ v, v ∉ O → φ v = 0) =>
    (_root_.GlobalTheory.IsFibreFamily_lintegral_preimage hf hO hU h φ hφ hs S hS).symm.trans
      (_root_.GlobalTheory.IsFibreFamily_lintegral_preimage hf hO hU' h' φ hφ hs S hS)
  unfold _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily at h h'
  obtain ⟨hfib, -, hcts⟩ := h
  obtain ⟨hfib', -, hcts'⟩ := h'
  have hnull : Oᶜ ⊆ (f ⁻¹' {id β} ∩ U)ᶜ := compl_subset_compl.2 (inter_subset_left.trans hβ)
  have hnull' : Oᶜ ⊆ (f ⁻¹' {id β} ∩ U')ᶜ := compl_subset_compl.2 (inter_subset_left.trans hβ)
  refine _root_.GlobalTheory.measure_eq_of_lintegral_eq_on_compactSupport _ _ O hO (measure_mono_null hnull (hfib β))
    (measure_mono_null hnull' (hfib' β)) fun φ hφc hφs hφO hφ0 => ?_
  obtain ⟨hi, hc⟩ := hcts φ hφc hφs (hφO.trans hU)
  obtain ⟨hi', hc'⟩ := hcts' φ hφc hφs (hφO.trans hU')
  refine ⟨hi β hβB, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal (hi β hβB) (Filter.Eventually.of_forall hφ0),
    ← ofReal_integral_eq_lintegral_ofReal (hi' β hβB') (Filter.Eventually.of_forall hφ0)]
  have hW : B ∩ B' ∈ 𝓝 β := Filter.inter_mem (hB.mem_nhds hβB) (hB'.mem_nhds hβB')
  have hφm : Measurable fun v => ENNReal.ofReal (φ v) := hφc.measurable.ennreal_ofReal
  have hφz : ∀ v, v ∉ O → ENNReal.ofReal (φ v) = 0 := fun v hv => by
    rw [image_eq_zero_of_notMem_tsupport fun h'' => hv (hφO h'')]
    simp
  have hset : ∀ S ⊆ B ∩ B', MeasurableSet S →
      ∫⁻ b in S, ENNReal.ofReal (∫ v, φ v ∂fib b) =
        ∫⁻ b in S, ENNReal.ofReal (∫ v, φ v ∂fib' b) := by
    intro S hSW hS
    rw [setLIntegral_congr_fun hS fun b hb =>
        ofReal_integral_eq_lintegral_ofReal (hi b (hSW hb).1) (Filter.Eventually.of_forall hφ0),
      setLIntegral_congr_fun hS fun b hb =>
        ofReal_integral_eq_lintegral_ofReal (hi' b (hSW hb).2) (Filter.Eventually.of_forall hφ0)]
    exact hdens S hS _ hφm hφz
  have hca := hc.continuousAt (hB.mem_nhds hβB)
  have hca' := hc'.continuousAt (hB'.mem_nhds hβB')
  congr 1
  exact le_antisymm
    (le_of_setLIntegral_eq_near hW hca hca' (integral_nonneg hφ0) hset)
    (le_of_setLIntegral_eq_near hW hca' hca (integral_nonneg hφ0) fun S hSW hS =>
      (hset S hSW hS).symm)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFibreFamilyEqAtContinuityPointStatement
open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFibreFamily_eq_at_continuity_point : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (f : V → ℝ) (O U U' : Set V) (B B' : Set ℝ) (fib fib' : ℝ → Measure V) (β : ℝ), Measurable f → IsOpen O → O ⊆ U → O ⊆ U' → f ⁻¹' {β} ⊆ O → IsOpen B → IsOpen B' → β ∈ B → β ∈ B' → IsFibreFamily μ f id U (volume : Measure ℝ) B fib → IsFibreFamily μ f id U' (volume : Measure ℝ) B' fib' → fib β = fib' β := by
  first | exact @GlobalTheory.IsFibreFamily_eq_at | exact GlobalTheory.IsFibreFamily_eq_at | (intros; apply GlobalTheory.IsFibreFamily_eq_at <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FibOfZero
noncomputable section

namespace GlobalTheory.QuadFibre

open MeasureTheory
open scoped Pointwise

def IsSqrtOn {K : Type} [NormedField K] (U : Set K) (s : K → K) : Prop :=
  IsOpen U ∧ IsCompact U ∧ (1 : K) ∈ U ∧ (∀ a ∈ U, ∀ b ∈ U, a * b ∈ U) ∧ (∀ a ∈ U, a⁻¹ ∈ U) ∧
    (∀ a ∈ U, ‖a‖ = 1) ∧ Continuous s ∧ ∀ a ∈ U, s a ^ 2 = a

open Classical in
def fibOf {K V : Type} [NormedField K] [MeasurableSpace K] [AddCommGroup V] [Module K V]
    [MeasurableSpace V] (μ : Measure V) (ν : Measure K) (q : V → K) (U : Set K) (s : K → K)
    (t : K) : Measure V := by
  classical
  exact if t = 0 then 0 else
    (ν (t • U))⁻¹ • Measure.map (fun x => s (t / q x) • x) (μ.restrict (q ⁻¹' (t • U)))

theorem fibOf_zero {K V : Type} [NormedField K] [MeasurableSpace K] [AddCommGroup V] [Module K V]
    [MeasurableSpace V] (μ : Measure V) (ν : Measure K) (q : V → K) (U : Set K) (s : K → K) :
    fibOf μ ν q U s 0 = 0 := by simp [fibOf]

theorem fibOf_ne {K V : Type} [NormedField K] [MeasurableSpace K] [AddCommGroup V] [Module K V]
    [MeasurableSpace V] (μ : Measure V) (ν : Measure K) (q : V → K) (U : Set K) (s : K → K)
    {t : K} (ht : t ≠ 0) : fibOf μ ν q U s t =
      (ν (t • U))⁻¹ • Measure.map (fun x => s (t / q x) • x) (μ.restrict (q ⁻¹' (t • U))) := by
  simp [fibOf, ht]

end GlobalTheory.QuadFibre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBruhatFunctionOfClosedEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBruhatFunctionOfClosedEmbedding
open MeasureTheory Topology
open scoped ENNReal

namespace GlobalTheory

theorem exists_bruhat_function_closedEmbedding
    (T T' : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [T2Space T] [MeasurableSpace T] [BorelSpace T]
    [Group T'] [TopologicalSpace T'] [IsTopologicalGroup T'] [MeasurableSpace T'] [BorelSpace T']
    (j : T' →* T) (hj : IsClosedEmbedding j) (m' : Measure T') [m'.IsHaarMeasure]
    [m'.IsInvInvariant] :
    ∃ b : T → ℝ≥0∞, Measurable b ∧ ∀ t, ∫⁻ s, b (j s * t) ∂m' = 1 := by
  classical
  let H : Subgroup T := j.range
  have hH : IsClosed (H : Set T) := by
    simpa [H, MonoidHom.coe_range] using hj.isClosed_range
  let e : T' ≃* H := MonoidHom.ofInjective hj.injective
  have he : Continuous e := hj.continuous.subtype_mk _
  have hes : Continuous e.symm := by
    rw [hj.isEmbedding.isInducing.continuous_iff]
    have : (fun x : H => j (e.symm x)) = fun x : H => (x : T) := by
      funext x
      exact MonoidHom.apply_ofInjective_symm hj.injective x
    rw [Function.comp_def, this]
    exact continuous_subtype_val
  have : (Measure.map e m').IsHaarMeasure := e.isHaarMeasure_map m' he hes
  obtain ⟨φ, hφ, hint, -⟩ := exists_bruhat_function_closed_subgroup T H hH (Measure.map e m')
  refine ⟨fun x => φ x⁻¹, hφ.comp measurable_inv, fun t => ?_⟩
  show ∫⁻ s, φ (j s * t)⁻¹ ∂m' = 1
  have h1 := hint t⁻¹
  have hm : Measurable (fun h : H => φ (t⁻¹ * (h : T))) :=
    hφ.comp (continuous_const.mul continuous_subtype_val).measurable
  rw [lintegral_map hm he.measurable] at h1
  have h2 : ∀ s : T', ((e s : H) : T) = j s := fun s => rfl
  simp only [h2] at h1
  have h3 : ∀ s : T', (j s * t)⁻¹ = t⁻¹ * j s⁻¹ := fun s => by
    rw [mul_inv_rev, map_inv]
  simp only [h3]
  rw [lintegral_inv_eq_self (fun s => φ (t⁻¹ * j s))]
  exact h1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBruhatFunctionOfClosedEmbeddingStatement
open MeasureTheory Topology
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bruhatFunction_of_closedEmbedding : ∀ (T T' : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [SecondCountableTopology T] [T2Space T] [MeasurableSpace T] [BorelSpace T] [Group T'] [TopologicalSpace T'] [IsTopologicalGroup T'] [MeasurableSpace T'] [BorelSpace T'] (j : T' →* T), IsClosedEmbedding j → ∀ (m' : Measure T') [m'.IsHaarMeasure] [m'.IsInvInvariant], ∃ b : T → ℝ≥0∞, Measurable b ∧ ∀ t, ∫⁻ s, b (j s * t) ∂m' = 1 := by
  first | exact @GlobalTheory.exists_bruhat_function_closedEmbedding | exact GlobalTheory.exists_bruhat_function_closedEmbedding | (intros; apply GlobalTheory.exists_bruhat_function_closedEmbedding <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinsumMemLeOfSubset
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.ZeroWindow

private lemma norm_sub_two_add_le_of_mem_strip {ρ : ℂ} {t : ℝ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (ht : |ρ.im - t| ≤ 1) : ‖ρ - (2 + (t : ℂ) * I)‖ ≤ 7 / 2 := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hre : (ρ - (2 + (t : ℂ) * I)).re = ρ.re - 2 := by simp
  have him : (ρ - (2 + (t : ℂ) * I)).im = ρ.im - t := by simp
  rw [hre, him, abs_of_neg (by linarith)]
  linarith

private lemma finsum_mem_le_of_subset_of_nonneg {S D : Set ℂ} (f : ℂ → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hD : D.Finite) (hSD : S ⊆ D) :
    ∑ᶠ x ∈ S, f x ≤ ∑ᶠ x ∈ D, f x := by
  rw [finsum_mem_eq_finite_toFinset_sum f (hD.subset hSD), finsum_mem_eq_finite_toFinset_sum f hD]
  exact Finset.sum_le_sum_of_subset_of_nonneg (by simpa using hSD) (fun x _ _ => hf x)

theorem _root_.GlobalTheory.ZeroWindow.count_zeros_window : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ t : ℝ,
    {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ LFunction χ ρ = 0}.Finite ∧
    ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ LFunction χ ρ = 0},
      ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) ≤ C * Real.log (N * (|t| + 2)) := by
  obtain ⟨C1, hC1, hL⟩ := _root_.GlobalTheory.LWide.logDeriv_LFunction_strip
  obtain ⟨C2, hC2, hZ⟩ := _root_.GlobalTheory.ZetaWide.main
  refine ⟨max C1 C2, lt_max_of_lt_left hC1, fun N _ χ hχ t => ?_⟩
  set s : ℂ := 2 + (t : ℂ) * I with hs
  have hsre : s.re = 2 := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have ht2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  by_cases h1χ : χ = 1
  · have hN : N = 1 := by
      have h := hχ
      rw [DirichletCharacter.isPrimitive_def, h1χ, DirichletCharacter.conductor_one] at h
      exact h.symm
    subst hN
    have hLz : LFunction χ = riemannZeta := LFunction_modOne_eq
    have hs1 : s ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      rw [hsre] at this
      norm_num at this
    obtain ⟨hfin, hsum, -⟩ := hZ s (by rw [hsre]; norm_num) (by rw [hsre]) hs1
      (riemannZeta_ne_zero_of_one_le_re (by rw [hsre]; norm_num))
    rw [hsim] at hfin hsum
    have hsub : {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ LFunction χ ρ = 0} ⊆
        {w : ℂ | ‖w - (2 + (t : ℂ) * I)‖ ≤ 7 / 2 ∧ w ≠ 1 ∧ riemannZeta w = 0} := by
      rintro ρ ⟨h0, h1, h2, h3⟩
      refine ⟨norm_sub_two_add_le_of_mem_strip h0 h1 h2, ?_, by rwa [hLz] at h3⟩
      rintro rfl
      simp at h1
    refine ⟨hfin.subset hsub, ?_⟩
    calc ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ LFunction χ ρ = 0},
          ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ)
        ≤ ∑ᶠ ρ ∈ {w : ℂ | ‖w - (2 + (t : ℂ) * I)‖ ≤ 7 / 2 ∧ w ≠ 1 ∧ riemannZeta w = 0},
          ((analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) := by
          rw [hLz]
          exact finsum_mem_le_of_subset_of_nonneg _ (fun _ => Nat.cast_nonneg _) hfin
            (by rw [hLz] at hsub; exact hsub)
      _ ≤ C2 * Real.log (|t| + 2) := hsum
      _ ≤ max C1 C2 * Real.log (((1 : ℕ) : ℝ) * (|t| + 2)) := by
          rw [Nat.cast_one, one_mul]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.log_nonneg (by linarith))
  · have hLs : LFunction χ s ≠ 0 :=
      LFunction_ne_zero_of_one_le_re χ (Or.inl h1χ) (by rw [hsre]; norm_num)
    obtain ⟨hfin, hsum, -⟩ := hL N χ h1χ s (by rw [hsre]; norm_num) (by rw [hsre]) hLs
    rw [hsim] at hfin hsum
    have hsub : {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ LFunction χ ρ = 0} ⊆
        {w : ℂ | ‖w - (2 + (t : ℂ) * I)‖ ≤ 7 / 2 ∧ LFunction χ w = 0} := by
      rintro ρ ⟨h0, h1, h2, h3⟩
      exact ⟨norm_sub_two_add_le_of_mem_strip h0 h1 h2, h3⟩
    refine ⟨hfin.subset hsub, ?_⟩
    calc ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ LFunction χ ρ = 0},
          ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ)
        ≤ ∑ᶠ ρ ∈ {w : ℂ | ‖w - (2 + (t : ℂ) * I)‖ ≤ 7 / 2 ∧ LFunction χ w = 0},
          ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) :=
          finsum_mem_le_of_subset_of_nonneg _ (fun _ => Nat.cast_nonneg _) hfin hsub
      _ ≤ C1 * Real.log (N * (|t| + 2)) := hsum
      _ ≤ max C1 C2 * Real.log (N * (|t| + 2)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _)
            (Real.log_nonneg (by nlinarith))

end GlobalTheory.ZeroWindow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NegReLogDerivPrincipalLFunctionLe
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NegReLogDerivPrincipalLFunctionLe
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.PrincipalLogDeriv

lemma norm_cpow_neg_le {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖(p : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
  calc (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    _ = 1 / p := by rw [Real.rpow_neg_one, one_div]
    _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2

lemma half_le_norm_one_sub {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 ≤ s.re) :
    1 / 2 ≤ ‖1 - (p : ℂ) ^ (-s)‖ := by
  have h := norm_cpow_neg_le hp hs
  have h' := norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-s))
  rw [norm_one] at h'
  linarith

lemma one_sub_ne_zero {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 ≤ s.re) :
    1 - (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h' := half_le_norm_one_sub hp hs
  rw [h, norm_zero] at h'
  norm_num at h'

lemma hasDerivAt_factor {p : ℕ} (hp : p.Prime) (s : ℂ) :
    HasDerivAt (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) ((p : ℂ) ^ (-s) * Complex.log p) s := by
  have hc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h : HasDerivAt (fun z : ℂ => (p : ℂ) ^ (-z)) ((p : ℂ) ^ (-s) * Complex.log p * (-1)) s :=
    ((hasDerivAt_id' s).neg).const_cpow (Or.inl hc)
  have h2 : HasDerivAt (fun z : ℂ => 1 - (p : ℂ) ^ (-z))
      (-((p : ℂ) ^ (-s) * Complex.log p * (-1))) s := h.const_sub 1
  convert h2 using 1
  ring

lemma norm_logDeriv_factor_le {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ ≤ Real.log p := by
  have h1 := norm_cpow_neg_le hp hs
  have h2 := half_le_norm_one_sub hp hs
  have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hlog : ‖Complex.log (p : ℂ)‖ = Real.log p := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg p), Complex.norm_real,
      Real.norm_of_nonneg hl]
  rw [logDeriv_apply, (hasDerivAt_factor hp s).deriv, norm_div, norm_mul, hlog,
    div_le_iff₀ (by linarith)]
  nlinarith

lemma sum_log_primeFactors_le (q : ℕ) [NeZero q] :
    ∑ p ∈ q.primeFactors, Real.log p ≤ Real.log q := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [← Real.log_prod (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)]
  apply Real.log_le_log
  · exact Finset.prod_pos fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  · have h := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
    rw [← Nat.cast_prod]
    exact_mod_cast h

lemma norm_logDeriv_sub_le (q : ℕ) [NeZero q] {s : ℂ} (hs : 1 < s.re) :
    ‖deriv (LFunction (1 : DirichletCharacter ℂ q)) s / LFunction (1 : DirichletCharacter ℂ q) s
      - deriv riemannZeta s / riemannZeta s‖ ≤ Real.log q := by
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    exact lt_irrefl _ hs
  have hre : 1 ≤ s.re := hs.le
  have hev : LFunction (1 : DirichletCharacter ℂ q) =ᶠ[nhds s]
      fun z => (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) * riemannZeta z := by
    filter_upwards [isOpen_ne.mem_nhds hs1] with z hz
    exact LFunctionTrivChar_eq_mul_riemannZeta hz
  have hfac : ∀ p ∈ q.primeFactors, (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s ≠ 0 :=
    fun p hp => one_sub_ne_zero (Nat.prime_of_mem_primeFactors hp) hre
  have hdfac : ∀ p ∈ q.primeFactors, DifferentiableAt ℂ (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s :=
    fun p hp => (hasDerivAt_factor (Nat.prime_of_mem_primeFactors hp) s).differentiableAt
  have hF0 : (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hfac
  have hFd : DifferentiableAt ℂ (fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s :=
    DifferentiableAt.fun_finsetProd hdfac
  have hζ0 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hζd : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hL : deriv (LFunction (1 : DirichletCharacter ℂ q)) s /
      LFunction (1 : DirichletCharacter ℂ q) s =
      logDeriv (fun z => (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) * riemannZeta z) s := by
    rw [logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [hL, logDeriv_fun_mul (f := fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s hF0 hζ0
    hFd hζd, ← logDeriv_apply riemannZeta, add_sub_cancel_right,
    logDeriv_fun_prod (f := fun (p : ℕ) (z : ℂ) => 1 - (p : ℂ) ^ (-z)) hfac hdfac]
  calc ‖∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖
      ≤ ∑ p ∈ q.primeFactors, ‖logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ q.primeFactors, Real.log p :=
        Finset.sum_le_sum fun p hp => norm_logDeriv_factor_le (Nat.prime_of_mem_primeFactors hp) hre
    _ ≤ Real.log q := sum_log_primeFactors_le q

theorem neg_re_logDeriv_le : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (σ t : ℝ), 1 < σ → σ ≤ 2 → -(deriv (LFunction (1 : DirichletCharacter ℂ q)) (σ + t * I) / LFunction (1 : DirichletCharacter ℂ q) (σ + t * I)).re ≤ (1 / ((σ : ℂ) + t * I - 1)).re + C * Real.log (q * (|t| + 2)) := by
  obtain ⟨C, hC, hZ⟩ := GlobalTheory.T.logDeriv_riemannZeta_local_zero_sum
  refine ⟨C + 1, by linarith, ?_⟩
  intro q _ σ t hσ1 hσ2
  set s : ℂ := (σ : ℂ) + t * I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hs1 : 1 < s.re := by rw [hsre]; exact hσ1
  have hsne : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs1
    exact lt_irrefl _ hs1
  have hζ0 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs1
  have hdist : ‖s - (3 / 2 + t * I)‖ ≤ 2 / 3 := by
    have h1 : s - (3 / 2 + t * I) = ((σ - 3 / 2 : ℝ) : ℂ) := by
      rw [hsdef]; push_cast; ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  obtain ⟨hfin, hbound⟩ := hZ t s hdist hsne hζ0
  set Z := {w : ℂ | ‖w - (3 / 2 + t * I)‖ ≤ 5 / 6 ∧ w ≠ 1 ∧ riemannZeta w = 0} with hZdef
  set S := ∑ᶠ w ∈ Z, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w) with hSdef
  have hterm : ∀ w ∈ Z, 0 ≤ ((analyticOrderNatAt riemannZeta w : ℂ) / (s - w)).re := by
    intro w hw
    have hw1 : w.re ≤ 1 := by
      by_contra h
      push Not at h
      exact riemannZeta_ne_zero_of_one_lt_re h hw.2.2
    have hpos : 0 ≤ (s - w).re := by rw [Complex.sub_re, hsre]; linarith
    rw [Complex.div_re]
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, add_zero]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hpos) (Complex.normSq_nonneg _)
  have hS : 0 ≤ S.re := by
    rw [hSdef, finsum_mem_eq_finite_toFinset_sum _ hfin, Complex.re_sum]
    exact Finset.sum_nonneg fun w hw => hterm w (hfin.mem_toFinset.mp hw)
  set E := deriv riemannZeta s / riemannZeta s + 1 / (s - 1) - S with hEdef
  have hζ : deriv riemannZeta s / riemannZeta s = E - 1 / (s - 1) + S := by
    rw [hEdef]; ring
  have hE : -E.re ≤ C * Real.log (|t| + 2) :=
    le_trans (neg_le_abs _) (le_trans (Complex.abs_re_le_norm E) hbound)
  set D := deriv (LFunction (1 : DirichletCharacter ℂ q)) s / LFunction (1 : DirichletCharacter ℂ q) s
    - deriv riemannZeta s / riemannZeta s with hDdef
  have hD : ‖D‖ ≤ Real.log q := norm_logDeriv_sub_le q hs1
  have hDre : -D.re ≤ Real.log q := le_trans (neg_le_abs _) (le_trans (Complex.abs_re_le_norm D) hD)
  have hLsplit : deriv (LFunction (1 : DirichletCharacter ℂ q)) s /
      LFunction (1 : DirichletCharacter ℂ q) s = D + (E - 1 / (s - 1) + S) := by
    rw [hDdef, ← hζ]; ring
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have ht2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hlt : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith)
  have hlog : Real.log (q * (|t| + 2)) = Real.log q + Real.log (|t| + 2) :=
    Real.log_mul (by linarith) (by linarith)
  rw [hLsplit, hlog]
  simp only [Complex.add_re, Complex.sub_re]
  nlinarith

end GlobalTheory.PrincipalLogDeriv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NegReLogDerivPrincipalLFunctionLeStatement
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.neg_re_logDeriv_principalLFunction_le : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (σ t : ℝ), 1 < σ → σ ≤ 2 → -(deriv (LFunction (1 : DirichletCharacter ℂ q)) (σ + t * I) / LFunction (1 : DirichletCharacter ℂ q) (σ + t * I)).re ≤ (1 / ((σ : ℂ) + t * I - 1)).re + C * Real.log (q * (|t| + 2)) := by
  first | exact @GlobalTheory.PrincipalLogDeriv.neg_re_logDeriv_le | exact GlobalTheory.PrincipalLogDeriv.neg_re_logDeriv_le | (intros; apply GlobalTheory.PrincipalLogDeriv.neg_re_logDeriv_le <;> assumption)
end
end
