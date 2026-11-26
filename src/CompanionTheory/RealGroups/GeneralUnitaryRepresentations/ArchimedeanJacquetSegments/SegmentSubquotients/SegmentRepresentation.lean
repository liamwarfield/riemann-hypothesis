module

public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SegRepOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeCuspidalPairLength
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.CuspPairIrr
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.PiTensorTwist
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.Compact
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.BoundB
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.ThetaContra

@[expose] public section

section -- merged from CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.PosMkIff
noncomputable section

open Filter Topology Module

namespace CompanionTheory.RgGu.NR.Sig

def qf {n : ℕ} (M : Fin n → Fin n → ℂ) (x y : Fin n → ℂ) : ℂ := ∑ i, ∑ j, x i * (star (y j) * M i j)

theorem cont_qf {n : ℕ} :
    Continuous fun p : (Fin n → Fin n → ℂ) × (Fin n → ℂ) × (Fin n → ℂ) => qf p.1 p.2.1 p.2.2 := by
  unfold qf
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact ((continuous_apply i).comp (continuous_fst.comp continuous_snd)).mul
    ((continuous_star.comp ((continuous_apply j).comp (continuous_snd.comp continuous_snd))).mul
      ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst)))

theorem qf_smul {n : ℕ} (M : Fin n → Fin n → ℂ) (a : ℂ) (x y : Fin n → ℂ) :
    qf M (a • x) (a • y) = a * star a * qf M x y := by
  simp only [qf, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem qf_single {n : ℕ} (M : Fin n → Fin n → ℂ) (i j : Fin n) :
    qf M (Pi.single i 1) (Pi.single j 1) = M i j := by
  classical
  simp [qf, Pi.single_apply]

variable {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

abbrev Sq (W : Type) [AddCommGroup W] [Module ℂ W] := W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ

abbrev ef (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] :
    W ≃ₗ[ℂ] (Fin (finrank ℂ W) → ℂ) := (Module.finBasis ℂ W).equivFun

def gram (B : Sq W) : Fin (finrank ℂ W) → Fin (finrank ℂ W) → ℂ :=
  fun i j => B (Module.finBasis ℂ W i) (Module.finBasis ℂ W j)

def mk (M : Fin (finrank ℂ W) → Fin (finrank ℂ W) → ℂ) : Sq W :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => qf M (ef W v) (ef W w))
    (fun v v' w => by simp only [qf, map_add (f := _), Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun c v w => by
      simp only [qf, map_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
    (fun v w w' => by
      simp only [qf, map_add (f := _), Pi.add_apply, star_add, add_mul, mul_add, Finset.sum_add_distrib])
    (fun c v w => by
      simp only [qf, map_smul, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum, starRingEnd_apply]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)

theorem mk_apply (M : Fin (finrank ℂ W) → Fin (finrank ℂ W) → ℂ) (v w : W) :
    mk M v w = qf M (ef W v) (ef W w) := rfl

theorem expand (B : Sq W) (v w : W) : B v w = qf (gram B) (ef W v) (ef W w) := by
  conv_lhs => rw [← (Module.finBasis ℂ W).sum_equivFun v, ← (Module.finBasis ℂ W).sum_equivFun w]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul,
    qf, gram, starRingEnd_apply, Finset.mul_sum, ef]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem mk_gram (B : Sq W) : mk (gram B) = B := by
  ext v w
  rw [mk_apply, expand]

theorem gram_mk (M : Fin (finrank ℂ W) → Fin (finrank ℂ W) → ℂ) : gram (mk M : Sq W) = M := by
  funext i j
  have h : ∀ a, (Module.finBasis ℂ W).equivFun (Module.finBasis ℂ W a) = Pi.single a 1 := fun a => by
    funext b
    rw [Module.Basis.equivFun_self]
    simp [Pi.single_apply, eq_comm]
  simp only [gram, mk_apply, ef, h]
  exact qf_single M i j

theorem gram_smul (c : ℂ) (B : Sq W) : gram (c • B) = c • gram B := by
  funext i j
  simp [gram]

section Fam

variable {I : Type} (ι : I → I) (T : I → Module.End ℂ W)

def Inv (B : Sq W) : Prop := ∀ i v w, B (T i v) w = B v (T (ι i) w)

def Herm (B : Sq W) : Prop := ∀ v w, B w v = starRingEnd ℂ (B v w)

def Pos (B : Sq W) : Prop := ∀ v, v ≠ 0 → 0 < (B v v).re

variable {ι T}

theorem ker_bot (hsim : ∀ U : Submodule ℂ W, (∀ i, ∀ w ∈ U, T i w ∈ U) → U = ⊥ ∨ U = ⊤) (B : Sq W) (hB : B ≠ 0)
    (hinv : Inv ι T B) : LinearMap.ker B = ⊥ := by
  have hst : ∀ i, ∀ w ∈ LinearMap.ker B, T i w ∈ LinearMap.ker B := by
    intro i w hw
    rw [LinearMap.mem_ker] at hw ⊢
    ext u
    rw [hinv, hw]
    rfl
  rcases hsim (LinearMap.ker B) hst with h | h
  · exact h
  · exact absurd (LinearMap.ker_eq_top.1 h) hB

theorem inv_sub {B B' : Sq W} (h : Inv ι T B) (h' : Inv ι T B') (c : ℂ) : Inv ι T (B - c • B') := by
  intro i v w
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, h i v w, h' i v w]

theorem uniq (hsim : ∀ U : Submodule ℂ W, (∀ i, ∀ w ∈ U, T i w ∈ U) → U = ⊥ ∨ U = ⊤) (B₀ B : Sq W) (h0 : B₀ ≠ 0)
    (hinv0 : Inv ι T B₀) (hinv : Inv ι T B) : ∃ c : ℂ, B = c • B₀ := by
  classical
  have hk := ker_bot hsim B₀ h0 hinv0
  let b := Module.finBasis ℂ W
  let E : (W →ₛₗ[starRingEnd ℂ] ℂ) →ₗ[ℂ] (Fin (finrank ℂ W) → ℂ) :=
    { toFun := fun f j => f (b j)
      map_add' := fun f g => by funext j; simp
      map_smul' := fun c f => by funext j; simp }
  have hE : Function.Injective E := fun f g h => b.ext fun j => congrFun h j
  have hinj : Function.Injective (E ∘ₗ B₀) := hE.comp (LinearMap.ker_eq_bot.1 hk)
  have hdim : finrank ℂ W = finrank ℂ (Fin (finrank ℂ W) → ℂ) := by simp
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj
  let e := LinearEquiv.ofBijective (E ∘ₗ B₀) ⟨hinj, hsurj⟩
  let A : Module.End ℂ W := e.symm.toLinearMap ∘ₗ (E ∘ₗ B)
  have : Nontrivial W := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact h0 (by ext v w; simp [Subsingleton.elim v 0])
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue A
  obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
  have hAx : A x = c • x := Module.End.mem_eigenspace_iff.1 hx.1
  have key : B x = B₀ (c • x) := by
    apply hE
    have h1 := congrArg e hAx
    have h2 : e (A x) = E (B x) := by simp [A]
    rw [h2] at h1
    rw [h1]
    exact LinearEquiv.ofBijective_apply _ _
  refine ⟨c, ?_⟩
  by_contra hne
  have hne' : B - c • B₀ ≠ 0 := sub_ne_zero.2 hne
  have hk' := ker_bot hsim (B - c • B₀) hne' (inv_sub hinv hinv0 c)
  have hmem : x ∈ LinearMap.ker (B - c • B₀) := by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, key, map_smul, sub_self]
  rw [hk'] at hmem
  exact hx.2 ((Submodule.mem_bot ℂ).1 hmem)

theorem real_of {B₀ B : Sq W} (h0 : B₀ ≠ 0) (hh0 : Herm B₀) (hh : Herm B) (c : ℂ) (hc : B = c • B₀) :
    starRingEnd ℂ c = c := by
  obtain ⟨v, w, hvw⟩ : ∃ v w, B₀ v w ≠ 0 := by
    by_contra hn
    push Not at hn
    exact h0 (by ext v w; simp [hn])
  have e1 := hh v w
  rw [hc] at e1
  simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, hh0 v w] at e1
  have hz : starRingEnd ℂ (B₀ v w) ≠ 0 := (map_ne_zero _).2 hvw
  exact (mul_right_cancel₀ hz e1).symm

theorem pos_of (B : Sq W) (hh : Herm B) (hk : LinearMap.ker B = ⊥) (hsd : ∀ v, 0 ≤ (B v v).re) : Pos B := by
  intro v hv
  rcases (hsd v).lt_or_eq with h | h
  · exact h
  exfalso
  have hvv : B v v = 0 := by
    have e := hh v v
    apply Complex.ext
    · exact h.symm
    · have := congrArg Complex.im e
      simp only [Complex.conj_im] at this
      simp only [Complex.zero_im]
      linarith
  have hB : B v = 0 := by
    ext w
    have hwv : B w v = starRingEnd ℂ (B v w) := hh v w
    have hww : (B w w).im = 0 := by
      have := congrArg Complex.im (hh w w)
      simp only [Complex.conj_im] at this
      linarith
    have key : ∀ t : ℝ, 0 ≤ -2 * t * Complex.normSq (B v w) + t ^ 2 * Complex.normSq (B v w) * (B w w).re := by
      intro t
      set a : ℂ := -(t : ℂ) * B v w with ha
      have := hsd (v + a • w)
      have e0 : B (v + a • w) (v + a • w) =
          starRingEnd ℂ a * B v w + a * starRingEnd ℂ (B v w) + a * starRingEnd ℂ a * B w w := by
        simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul,
          hvv, hwv]
        ring
      have e : (B (v + a • w) (v + a • w)).re =
          -2 * t * Complex.normSq (B v w) + t ^ 2 * Complex.normSq (B v w) * (B w w).re := by
        rw [e0, ha]
        simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.conj_re, Complex.conj_im, map_mul, map_neg, Complex.conj_ofReal, hww,
          Complex.normSq_apply]
        ring
      linarith
    have hR : 0 < |(B w w).re| + 1 := by positivity
    have h1 := key (1 / (|(B w w).re| + 1))
    have hn := Complex.normSq_nonneg (B v w)
    have h2 : (1 / (|(B w w).re| + 1)) * (B w w).re ≤ 1 / (|(B w w).re| + 1) * |(B w w).re| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    have h3 : 1 / (|(B w w).re| + 1) * |(B w w).re| < 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_lt_one hR]
      linarith
    have h4 : Complex.normSq (B v w) = 0 := by
      by_contra hne
      have hpos : 0 < Complex.normSq (B v w) := lt_of_le_of_ne hn (Ne.symm hne)
      have ht : 0 < 1 / (|(B w w).re| + 1) := by positivity
      nlinarith [mul_pos ht hpos]
    simpa using Complex.normSq_eq_zero.1 h4
  have hm : v ∈ LinearMap.ker B := LinearMap.mem_ker.2 hB
  rw [hk] at hm
  exact hv ((Submodule.mem_bot ℂ).1 hm)

end Fam

theorem pos_mk_iff (M : Fin (finrank ℂ W) → Fin (finrank ℂ W) → ℂ) :
    (∀ v : W, v ≠ 0 → 0 < ((mk M : Sq W) v v).re) ↔ ∀ c, c ≠ 0 → 0 < (qf M c c).re := by
  constructor
  · intro h c hc
    have := h ((ef W).symm c) (((ef W).symm.map_ne_zero_iff).2 hc)
    rwa [mk_apply, LinearEquiv.apply_symm_apply] at this
  · intro h v hv
    rw [mk_apply]
    exact h _ ((LinearEquiv.map_ne_zero_iff _).2 hv)

theorem pos_open {n : ℕ} (M : Fin n → Fin n → ℂ) (hM : ∀ c : Fin n → ℂ, c ≠ 0 → 0 < (qf M c c).re) :
    ∀ᶠ M' in 𝓝 M, ∀ c : Fin n → ℂ, c ≠ 0 → 0 < (qf M' c c).re := by
  have hK : IsCompact (Metric.sphere (0 : Fin n → ℂ) 1) := isCompact_sphere 0 1
  have hcont : Continuous fun p : (Fin n → Fin n → ℂ) × (Fin n → ℂ) => (qf p.1 p.2 p.2).re :=
    Complex.continuous_re.comp (cont_qf.comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_snd)))
  have h1 : ∀ᶠ M' in 𝓝 M, ∀ u ∈ Metric.sphere (0 : Fin n → ℂ) 1, 0 < (qf M' u u).re := by
    refine hK.eventually_forall_of_forall_eventually fun u hu => ?_
    have hu0 : u ≠ 0 := by
      intro h
      rw [h, mem_sphere_zero_iff_norm, norm_zero] at hu
      exact zero_ne_one hu
    exact (hcont.tendsto (M, u)).eventually (lt_mem_nhds (hM u hu0))
  filter_upwards [h1] with M' hM' c hc
  set a : ℂ := (‖c‖ : ℂ)
  have ha : a ≠ 0 := by simpa [a] using hc
  have hu : a⁻¹ • c ∈ Metric.sphere (0 : Fin n → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv]
    simp [a, norm_ne_zero_iff.2 hc]
  have e : c = a • (a⁻¹ • c) := by rw [smul_smul, mul_inv_cancel₀ ha, one_smul]
  rw [e, qf_smul]
  have hs : a * star a = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    simp only [a, Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  rw [hs, Complex.re_ofReal_mul]
  exact mul_pos (by positivity) (hM' _ hu)

theorem mk_smul (a : ℂ) (M : Fin (finrank ℂ W) → Fin (finrank ℂ W) → ℂ) : (mk (a • M) : Sq W) = a • mk M := by
  ext v w
  simp only [mk_apply, qf, Pi.smul_apply, smul_eq_mul, LinearMap.smul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

section Real

variable {I : Type} {ι : I → I} {T : I → Module.End ℂ W}

omit [FiniteDimensional ℂ W] in
theorem herm_smul {B : Sq W} (h : Herm B) (r : ℝ) : Herm ((r : ℂ) • B) := by
  intro v w
  simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal, h v w]

omit [FiniteDimensional ℂ W] in
theorem inv_smul {B : Sq W} (h : Inv ι T B) (c : ℂ) : Inv ι T (c • B) := by
  intro i v w
  simp only [LinearMap.smul_apply, h i v w]

theorem normalize (B : Sq W) (hB : B ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ‖gram ((r : ℂ) • B)‖ = 1 := by
  have hg : gram B ≠ 0 := by
    intro h
    apply hB
    rw [← mk_gram B, h]
    ext v w
    simp [mk_apply, qf]
  refine ⟨‖gram B‖⁻¹, inv_pos.2 (norm_pos_iff.2 hg), ?_⟩
  rw [gram_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (norm_pos_iff.2 hg)),
    inv_mul_cancel₀ (norm_ne_zero_iff.2 hg)]

end Real

set_option maxHeartbeats 400000 in
theorem lim_form {I : Type} (ι : I → I) (T : ℝ → I → Module.End ℂ W)
    (hc : ∀ (i : I) (w : W) (l : Module.Dual ℂ W), Continuous fun s => l (T s i w))
    (s : ℕ → ℝ) (p : ℝ) (hs : Tendsto s atTop (𝓝 p)) (B : ℕ → Sq W) (hinv : ∀ k, Inv ι (T (s k)) (B k))
    (hh : ∀ k, Herm (B k)) (hn : ∀ k, ‖gram (B k)‖ = 1) :
    ∃ (φ : ℕ → ℕ) (M : Fin (finrank ℂ W) → Fin (finrank ℂ W) → ℂ), StrictMono φ ∧ ‖M‖ = 1 ∧
      Tendsto (fun k => gram (B (φ k))) atTop (𝓝 M) ∧ Inv ι (T p) (mk M) ∧ Herm (mk M) ∧
      ∀ v w, Tendsto (fun k => B (φ k) v w) atTop (𝓝 (mk M v w)) := by
  have hmem : ∀ k, gram (B k) ∈ Metric.sphere (0 : Fin (finrank ℂ W) → Fin (finrank ℂ W) → ℂ) 1 := fun k => by
    rw [mem_sphere_zero_iff_norm]
    exact hn k
  obtain ⟨M, hM, φ, hφ, hlim0⟩ := (isCompact_sphere (0 : Fin (finrank ℂ W) → Fin (finrank ℂ W) → ℂ) 1).tendsto_subseq
    hmem
  have hMn : ‖M‖ = 1 := mem_sphere_zero_iff_norm.1 hM
  have hcoord : ∀ i j, Tendsto (fun k => gram (B (φ k)) i j) atTop (𝓝 (M i j)) := by
    intro i j
    have h0 : Tendsto (fun k => ‖gram (B (φ k)) - M‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 hlim0
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) h0
    have h1 := norm_le_pi_norm ((gram (B (φ k)) - M) i) j
    have h2 := norm_le_pi_norm (gram (B (φ k)) - M) i
    simp only [Pi.sub_apply] at h1 h2
    exact h1.trans h2
  have hlim : Tendsto (fun k => gram (B (φ k))) atTop (𝓝 M) :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => hcoord i j
  have hcT : ∀ i v, Continuous fun t => ef W (T t i v) := fun i v => by
    refine continuous_pi fun j => ?_
    have h := hc i v ((Module.finBasis ℂ W).coord j)
    have e : (fun t => ef W (T t i v) j) = fun t => (Module.finBasis ℂ W).coord j (T t i v) := by
      funext t
      rw [Module.Basis.coord_apply, ef, Module.Basis.equivFun_apply]
    rw [e]
    exact h
  have key : ∀ (x y : ℕ → W) (x0 y0 : W), Tendsto (fun k => ef W (x k)) atTop (𝓝 (ef W x0)) →
      Tendsto (fun k => ef W (y k)) atTop (𝓝 (ef W y0)) →
      Tendsto (fun k => B (φ k) (x k) (y k)) atTop (𝓝 (mk M x0 y0)) := by
    intro x y x0 y0 hx hy
    have e : (fun k => B (φ k) (x k) (y k)) = fun k => qf (gram (B (φ k))) (ef W (x k)) (ef W (y k)) := by
      funext k
      exact expand _ _ _
    rw [e, mk_apply]
    unfold qf
    refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
    exact (tendsto_pi_nhds.1 hx i).mul (((continuous_star.tendsto _).comp (tendsto_pi_nhds.1 hy j)).mul
      (hcoord i j))
  have hsφ : Tendsto (fun k => s (φ k)) atTop (𝓝 p) := hs.comp hφ.tendsto_atTop
  have cst : ∀ v : W, Tendsto (fun _ : ℕ => ef W v) atTop (𝓝 (ef W v)) := fun v => tendsto_const_nhds
  refine ⟨φ, M, hφ, hMn, hlim, fun i v w => ?_, fun v w => ?_, fun v w => key _ _ v w (cst v) (cst w)⟩
  · have h1 := key (fun k => T (s (φ k)) i v) (fun _ => w) (T p i v) w (((hcT i v).tendsto p).comp hsφ) (cst w)
    have h2 := key (fun _ => v) (fun k => T (s (φ k)) (ι i) w) v (T p (ι i) w) (cst v)
      (((hcT (ι i) w).tendsto p).comp hsφ)
    have e : (fun k => B (φ k) (T (s (φ k)) i v) w) = fun k => B (φ k) v (T (s (φ k)) (ι i) w) :=
      funext fun k => hinv (φ k) i v w
    rw [e] at h1
    exact tendsto_nhds_unique h1 h2
  · have h1 := key (fun _ => w) (fun _ => v) w v (cst w) (cst v)
    have h2 := key (fun _ => v) (fun _ => w) v w (cst v) (cst w)
    have h3 : Tendsto (fun k => B (φ k) w v) atTop (𝓝 (starRingEnd ℂ (mk M v w))) := by
      have e : (fun k => B (φ k) w v) = fun k => starRingEnd ℂ (B (φ k) v w) := funext fun k => hh (φ k) v w
      rw [e]
      exact (Complex.continuous_conj.tendsto _).comp h2
    exact tendsto_nhds_unique h1 h3

end CompanionTheory.RgGu.NR.Sig

namespace CompanionTheory.RgGu.NR

open Sig

set_option maxHeartbeats 800000 in
theorem signature : Signature := by
  intro I W _ _ _ ι T hc hsim hex hpos _ s hs B hB hh hinv
  classical
  have hnt : Nontrivial W := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact hB (by ext v w; simp [Subsingleton.elim v 0])
  have hpos_ne : ∀ B₀ : Sq W, Sig.Pos B₀ → B₀ ≠ 0 := by
    intro B₀ h e
    obtain ⟨v, hv⟩ := exists_ne (0 : W)
    have := h v hv
    rw [e] at this
    simp at this
  have re_smul : ∀ (c : ℂ) (z : ℂ), c.im = 0 → (c * z).re = c.re * z.re := by
    intro c z h
    simp [Complex.mul_re, h]
  let D : Set ℝ := {t | ∃ B₀ : Sq W, Sig.Herm B₀ ∧ Sig.Inv ι (T t) B₀ ∧ Sig.Pos B₀}
  let P : Set (Set.Ici (0 : ℝ)) := {x | x.1 ∈ D}
  have : PreconnectedSpace (Set.Ici (0 : ℝ)) := Subtype.preconnectedSpace isPreconnected_Ici
  have hcl : IsClosed P := by
    refine IsSeqClosed.isClosed fun x p hx hp => ?_
    have hsq : Tendsto (fun n => (x n).1) atTop (𝓝 p.1) := (continuous_subtype_val.tendsto p).comp hp
    choose B₁ hB1 hB2 hB3 using hx
    choose r hr hrn using fun k => normalize (B₁ k) (hpos_ne _ (hB3 k))
    obtain ⟨φ, M, hφ, hM, hlim, hinvM, hhM, hpt⟩ := lim_form ι T hc (fun n => (x n).1) p.1 hsq
      (fun k => (r k : ℂ) • B₁ k) (fun k => inv_smul (hB2 k) _) (fun k => herm_smul (hB1 k) _) hrn
    have hsd : ∀ v, 0 ≤ ((mk M : Sq W) v v).re := by
      intro v
      refine ge_of_tendsto ((Complex.continuous_re.tendsto _).comp (hpt v v)) (Eventually.of_forall fun k => ?_)
      show 0 ≤ (((r (φ k) : ℂ) • B₁ (φ k)) v v).re
      rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, Complex.re_ofReal_mul]
      by_cases hv : v = 0
      · simp [hv]
      · exact (mul_pos (hr _) (hB3 _ v hv)).le
    have hne : (mk M : Sq W) ≠ 0 := by
      intro e
      have := gram_mk (W := W) M
      rw [e] at this
      have h0 : gram (0 : Sq W) = 0 := by funext i j; simp [gram]
      rw [h0] at this
      rw [← this] at hM
      simp at hM
    exact ⟨mk M, hhM, hinvM, pos_of _ hhM (ker_bot (hsim p.1 p.2) _ hne hinvM) hsd⟩
  have hop : IsClosed Pᶜ := by
    refine IsSeqClosed.isClosed fun x p hx hp => ?_
    intro hpD
    obtain ⟨B₀, h0h, h0i, h0p⟩ := hpD
    have hsq : Tendsto (fun n => (x n).1) atTop (𝓝 p.1) := (continuous_subtype_val.tendsto p).comp hp
    choose B₁ hB1 hB2 hB3 using fun k => hex (x k).1 (x k).2
    choose r hr hrn using fun k => normalize (B₁ k) (hB1 k)
    obtain ⟨φ, M, hφ, hM, hlim, hinvM, hhM, hpt⟩ := lim_form ι T hc (fun n => (x n).1) p.1 hsq
      (fun k => (r k : ℂ) • B₁ k) (fun k => inv_smul (hB3 k) _) (fun k => herm_smul (hB2 k) _) hrn
    have hne : (mk M : Sq W) ≠ 0 := by
      intro e
      have := gram_mk (W := W) M
      rw [e] at this
      have h0 : gram (0 : Sq W) = 0 := by funext i j; simp [gram]
      rw [h0] at this
      rw [← this] at hM
      simp at hM
    obtain ⟨c, hc⟩ := uniq (hsim p.1 p.2) B₀ (mk M) (hpos_ne _ h0p) h0i hinvM
    have hcr := real_of (hpos_ne _ h0p) h0h hhM c hc
    have hcim : c.im = 0 := by
      have := congrArg Complex.im hcr
      simp only [Complex.conj_im] at this
      linarith
    have hc0 : c.re ≠ 0 := by
      intro h
      apply hne
      have : c = 0 := Complex.ext h hcim
      rw [hc, this, zero_smul]
    obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, 0 < σ * c.re := by
      rcases lt_or_gt_of_ne hc0 with h | h
      · exact ⟨-1, by linarith⟩
      · exact ⟨1, by linarith⟩
    have hposM : ∀ y, y ≠ 0 → 0 < (qf ((σ : ℂ) • M) y y).re := by
      rw [← pos_mk_iff]
      intro v hv
      rw [mk_smul, hc, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply,
        smul_eq_mul, smul_eq_mul, ← mul_assoc, re_smul _ _ (by simp [hcim])]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hcim, mul_zero, sub_zero]
      exact mul_pos hσ (h0p v hv)
    have hev := (hlim.const_smul (σ : ℂ)).eventually (pos_open _ hposM)
    obtain ⟨k, hk⟩ := hev.exists
    apply hx (φ k)
    refine ⟨(σ : ℂ) • ((r (φ k) : ℂ) • B₁ (φ k)), herm_smul (herm_smul (hB2 _) _) σ, inv_smul (inv_smul (hB3 _) _) _, ?_⟩
    have hk' := (pos_mk_iff (W := W) _).2 hk
    rwa [← gram_smul, mk_gram] at hk'
  have hne : P.Nonempty := by
    obtain ⟨B₀, h1, h2, h3⟩ := hpos
    exact ⟨⟨0, Set.mem_Ici.2 le_rfl⟩, B₀, h1, h3, h2⟩
  have huniv := IsClopen.eq_univ ⟨hcl, isClosed_compl_iff.1 hop⟩ hne
  have hsD : s ∈ D := by
    have : (⟨s, hs⟩ : Set.Ici (0 : ℝ)) ∈ P := by rw [huniv]; trivial
    exact this
  obtain ⟨B₀, h0h, h0i, h0p⟩ := hsD
  obtain ⟨c, hc⟩ := uniq (hsim s hs) B₀ B (hpos_ne _ h0p) h0i hinv
  have hcr := real_of (hpos_ne _ h0p) h0h hh c hc
  have hcim : c.im = 0 := by
    have := congrArg Complex.im hcr
    simp only [Complex.conj_im] at this
    linarith
  have hval : ∀ v, (B v v).re = c.re * (B₀ v v).re := by
    intro v
    rw [hc, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, re_smul _ _ hcim]
  have hc0 : c.re ≠ 0 := by
    intro h
    apply hB
    have : c = 0 := Complex.ext h hcim
    rw [hc, this, zero_smul]
  rcases lt_or_gt_of_ne hc0 with h | h
  · right
    intro v hv
    rw [hval]
    exact mul_neg_of_neg_of_pos h (h0p v hv)
  · left
    intro v hv
    rw [hval]
    exact mul_pos h (h0p v hv)

end CompanionTheory.RgGu.NR
end
end

section -- merged from CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.StageC
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel CompanionTheory.Pf1.SegRepC

namespace CompanionTheory.RgGu.SRC

namespace StageC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

abbrev cls {d : ℕ} (σ : IrrRep (GL (Fin d) k)) : IrrGL (k := k) := IrrGL.of σ.ρ σ.smooth σ.irr

theorem segTerm_smooth {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) (a : Fin l) : IsSmooth (segTerm σ.ρ l a) :=
  isSmooth_twist σ.smooth (isSmoothChar_absPow _).detChar

theorem segTerm_irr {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) (a : Fin l) : (segTerm σ.ρ l a).IsIrreducible :=
  isIrreducible_twist σ.irr _

abbrev tcl {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) (a : Fin l) : IrrGL (k := k) :=
  IrrGL.of (segTerm σ.ρ l a) (segTerm_smooth σ l a) (segTerm_irr σ l a)

theorem tcl_eq {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) (a : Fin l) : tcl σ l a = (cls σ).nu ((a : ℕ) : ℂ) :=
  (IrrGL.tw_of σ.ρ σ.smooth σ.irr _ _).symm

theorem blocks_eq (l d : ℕ) (h : ∑ _a : Fin l, d = l * d) : stdBlocks (fun _ : Fin l => d) h = consecBlocks l d := by
  ext ⟨a, j⟩
  rw [stdBlocks_val, consecBlocks_val]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

theorem consec_equiv {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) (h : ∑ a, (tcl σ l a).1 = l * d) :
    Nonempty ((multiProd (consecBlocks l d) (segTerm σ.ρ l)).Equiv (prodIrr (tcl σ l) h)) := by
  have he : stdBlocks (fun a => (tcl σ l a).1) h = consecBlocks l d := blocks_eq l d h
  unfold prodIrr
  rw [he]
  exact ⟨multiProdEquiv (consecBlocks l d) fun a => IrrGL.equivOf _ _ _⟩

theorem prod₂_map_injective_right (r t : ℕ) {U W W' : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (σ : Representation ℂ (GL (Fin r) k) U)
    (ρ : Representation ℂ (GL (Fin t) k) W) (ρ' : Representation ℂ (GL (Fin t) k) W')
    (f : ρ.IntertwiningMap ρ') (hf : Function.Injective f) :
    ∃ F : (prod₂ σ ρ).IntertwiningMap (prod₂ σ ρ'), Function.Injective F := by
  have hι : Function.Injective (GlobalTheory.ParIndExact.extTensorMapRight σ f) :=
    Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap hf
  have hι' : Function.Injective (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ f)
      (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) := hι
  exact ⟨parIndMap (two (stdSum rfl)) (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ f)
    (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom), GlobalTheory.ParIndExact.parIndMap_injective _ _ hι'⟩

theorem inj_comp {G V₁ V₂ V₃ : Type} [Group G] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    [AddCommGroup V₃] [Module ℂ V₃] {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂}
    {ρ₃ : Representation ℂ G V₃} (f : ρ₂.IntertwiningMap ρ₃) (g : ρ₁.IntertwiningMap ρ₂)
    (hf : Function.Injective f) (hg : Function.Injective g) : Function.Injective (f.comp g) :=
  fun _ _ h => hg (hf h)

theorem inj_equiv {G V₁ V₂ : Type} [Group G] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂} (φ : ρ₁.Equiv ρ₂) :
    Function.Injective φ.toIntertwiningMap :=
  φ.toLinearEquiv.injective

theorem sum_const_fin (n d : ℕ) : ∑ _a : Fin n, d = n * d := by simp

section Emb

variable {G V₁ V₂ V₃ : Type} [Group G] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
  [AddCommGroup V₃] [Module ℂ V₃] {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂} {ρ₃ : Representation ℂ G V₃}

def Emb (ρ₁ : Representation ℂ G V₁) (ρ₂ : Representation ℂ G V₂) : Prop :=
  ∃ F : ρ₁.IntertwiningMap ρ₂, Function.Injective F

theorem Emb.trans (h : Emb ρ₁ ρ₂) (h' : Emb ρ₂ ρ₃) : Emb ρ₁ ρ₃ := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨g, hg⟩ := h'
  exact ⟨g.comp f, inj_comp _ _ hg hf⟩

theorem Emb.of (e : Nonempty (ρ₁.Equiv ρ₂)) : Emb ρ₁ ρ₂ := ⟨e.some.toIntertwiningMap, inj_equiv _⟩

theorem Emb.of' (e : Nonempty (ρ₂.Equiv ρ₁)) : Emb ρ₁ ρ₂ := ⟨e.some.symm.toIntertwiningMap, inj_equiv _⟩

theorem Emb.sub (S : Subrepresentation ρ₁) : Emb S.toRepresentation ρ₁ :=
  ⟨⟨S.toSubmodule.subtype, fun _ => rfl⟩, Subtype.val_injective⟩

theorem Emb.range (h : Emb ρ₁ ρ₂) [Nontrivial V₁] :
    ∃ T : Subrepresentation ρ₂, T.toSubmodule ≠ ⊥ ∧ IsSubquotient T.toRepresentation ρ₁ := by
  obtain ⟨F, hF⟩ := h
  let T : Subrepresentation ρ₂ :=
    ⟨LinearMap.range F.toLinearMap, by
      rintro g _ ⟨v, rfl⟩
      exact ⟨_, F.isIntertwining _ _ g v⟩⟩
  let toT : ρ₁.IntertwiningMap T.toRepresentation :=
    ⟨LinearMap.codRestrict T.toSubmodule F.toLinearMap (fun v => ⟨v, rfl⟩), fun g => by
      ext v
      exact F.isIntertwining _ _ g v⟩
  refine ⟨T, fun hT => ?_, IsSubquotient.of_surjective toT ?_⟩
  · obtain ⟨v, hv⟩ := exists_ne (0 : V₁)
    have hmem : F v ∈ T.toSubmodule := ⟨v, rfl⟩
    rw [hT, Submodule.mem_bot] at hmem
    exact hv (hF (hmem.trans (map_zero F).symm))
  · rintro ⟨_, v, rfl⟩
    exact ⟨v, rfl⟩

end Emb

theorem sum_app {p q : ℕ} (x : Fin p → IrrGL (k := k)) (y : Fin q → IrrGL (k := k)) :
    ∑ a, (Fin.append x y a).1 = ∑ a, (x a).1 + ∑ a, (y a).1 := by
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

section Two

variable {r t : ℕ} {U U' W W' Y Y' : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup U'] [Module ℂ U']
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Y']
  [Module ℂ Y']

set_option synthInstance.maxHeartbeats 400000 in
theorem embR (σ : Representation ℂ (GL (Fin r) k) U) (ρ : Representation ℂ (GL (Fin t) k) W)
    (ρ' : Representation ℂ (GL (Fin t) k) W') (P : Representation ℂ (GL (Fin (r + t)) k) Y)
    (P' : Representation ℂ (GL (Fin (r + t)) k) Y') (h : Emb ρ ρ') (e : Nonempty ((prod₂ σ ρ).Equiv P))
    (e' : Nonempty ((prod₂ σ ρ').Equiv P')) : Emb P P' := by
  obtain ⟨f, hf⟩ := h
  have h3 : Emb (prod₂ σ ρ) (prod₂ σ ρ') := prod₂_map_injective_right r t σ ρ ρ' f hf
  exact ((Emb.of' e).trans h3).trans (Emb.of e')

set_option synthInstance.maxHeartbeats 400000 in
theorem embL (σ : Representation ℂ (GL (Fin r) k) U) (σ' : Representation ℂ (GL (Fin r) k) U')
    (ρ : Representation ℂ (GL (Fin t) k) W) (P : Representation ℂ (GL (Fin (r + t)) k) Y)
    (P' : Representation ℂ (GL (Fin (r + t)) k) Y') (h : Emb σ σ') (e : Nonempty ((prod₂ σ ρ).Equiv P))
    (e' : Nonempty ((prod₂ σ' ρ).Equiv P')) : Emb P P' := by
  obtain ⟨f, hf⟩ := h
  have h3 : Emb (prod₂ σ ρ) (prod₂ σ' ρ) := GlobalTheory.CompanionTheory.ProdInj.prod₂_map_injective k r t _ _ _ σ σ' ρ f hf
  exact ((Emb.of' e).trans h3).trans (Emb.of e')

end Two

set_option synthInstance.maxHeartbeats 400000 in
theorem emb_right {p q q' r t : ℕ} (A : Fin p → IrrGL (k := k)) (y : Fin q → IrrGL (k := k)) (y' : Fin q' → IrrGL (k := k))
    (hA : ∑ a, (A a).1 = r) (hy : ∑ a, (y a).1 = t) (hy' : ∑ a, (y' a).1 = t) (h : Emb (prodIrr y hy) (prodIrr y' hy'))
    (h1 : ∑ a, (Fin.append A y a).1 = r + t) (h2 : ∑ a, (Fin.append A y' a).1 = r + t) :
    Emb (prodIrr (Fin.append A y) h1) (prodIrr (Fin.append A y') h2) :=
  embR (prodIrr A hA) (prodIrr y hy) (prodIrr y' hy') _ _ h (GlobalTheory.T.product_irreducible_append_equiv k p q r t A y hA hy h1)
    (GlobalTheory.T.product_irreducible_append_equiv k p q' r t A y' hA hy' h2)

set_option synthInstance.maxHeartbeats 400000 in
theorem emb_left {p p' q r t : ℕ} (y : Fin p → IrrGL (k := k)) (y' : Fin p' → IrrGL (k := k)) (B : Fin q → IrrGL (k := k))
    (hy : ∑ a, (y a).1 = r) (hy' : ∑ a, (y' a).1 = r) (hB : ∑ a, (B a).1 = t) (h : Emb (prodIrr y hy) (prodIrr y' hy'))
    (h1 : ∑ a, (Fin.append y B a).1 = r + t) (h2 : ∑ a, (Fin.append y' B a).1 = r + t) :
    Emb (prodIrr (Fin.append y B) h1) (prodIrr (Fin.append y' B) h2) :=
  embL (prodIrr y hy) (prodIrr y' hy') (prodIrr B hB) _ _ h (GlobalTheory.T.product_irreducible_append_equiv k p q r t y B hy hB h1)
    (GlobalTheory.T.product_irreducible_append_equiv k p' q r t y' B hy' hB h2)

set_option synthInstance.maxHeartbeats 400000 in
theorem comb {n c N : ℕ} (xx : Fin n → IrrGL (k := k)) (hdx : ∑ a, (xx a).1 = N) (iz : Fin n) (z : IrrGL (k := k)) (hz : xx iz = z)
    (pr : Fin 2 → IrrGL (k := k)) (hs : ∑ j, (pr j).1 = z.1) (d : ℕ) (hsd : ∀ j, (pr j).1 = d) (hsc : ∀ j, (pr j).IsCusp)
    (hu : Nonempty ((jac (stdBlocks (fun j => (pr j).1) hs) z.rep).Equiv (piTensor fun j => (pr j).rep)))
    (y : Fin c → IrrGL (k := k)) (hy : ∑ a, (y a).1 = N) (hyc : ∀ a, (y a).IsCusp) (hjm : 1 ≤ Zc.jm y hy (prodIrr xx hdx)) :
    ∃ f : Fin 2 ↪o Fin c, ∀ j, y (f j) = pr j := by
  subst hz
  have hA : GlobalTheory.Published.IrreducibleAdmissibleGL := GlobalTheory.CompanionTheory.BZCuspPair.irrAdm
  obtain ⟨b, hb, s', hrow, hcol⟩ := GlobalTheory.CompanionTheory.Shuffle2.exists_cell_data hA xx hdx y hy hyc hjm
  choose a ha haw using hcol
  have key : ∀ r j, b r j ≠ 0 → IrrGL.of (s' r j).ρ (s' r j).smooth (s' r j).irr = y j := by
    intro r j hj
    obtain rfl : a j = r := by_contra fun hne => hj (ha j r (Ne.symm hne))
    exact haw j
  obtain ⟨f, -, hf⟩ := GlobalTheory.CompanionTheory.Shuffle2.exists_row hA (xx iz) pr hs d hsd hsc hu (b iz) (hb iz)
    (s' iz) (hrow iz) y hyc (key iz)
  exact ⟨f, hf⟩

set_option synthInstance.maxHeartbeats 400000 in
theorem classMain {i q N : ℕ} (t : Fin (i + 2 + q) → IrrGL (k := k)) (ht : ∑ a, (t a).1 = N) (pr : Fin 2 → IrrGL (k := k))
    (hpr : ∀ j, pr j = t (Fin.castAdd q (Fin.natAdd i j))) (z : IrrGL (k := k)) (hs : ∑ j, (pr j).1 = z.1)
    (he : Emb z.rep (prodIrr pr hs)) :
    ∃ (n : ℕ) (xx : Fin n → IrrGL (k := k)) (hdx : ∑ a, (xx a).1 = N) (iz : Fin n), xx iz = z ∧
      Emb (prodIrr xx hdx) (prodIrr t ht) := by
  obtain ⟨A, hA⟩ : ∃ A : Fin i → IrrGL (k := k), ∀ a, A a = t (Fin.castAdd q (Fin.castAdd 2 a)) := ⟨_, fun _ => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Fin q → IrrGL (k := k), ∀ b, B b = t (Fin.natAdd (i + 2) b) := ⟨_, fun _ => rfl⟩
  have hfun : Fin.append (Fin.append A pr) B = t := by
    funext a
    refine Fin.addCases (fun u => ?_) (fun b => ?_) a
    · rw [Fin.append_left]
      refine Fin.addCases (fun v => ?_) (fun j => ?_) u
      · rw [Fin.append_left, hA]
      · rw [Fin.append_right, hpr]
    · rw [Fin.append_right, hB]
  clear hA hB hpr
  subst hfun
  have hzs : ∑ _a : Fin 1, z.1 = z.1 := by simp
  have h1 : ∑ a, (Fin.append A (fun _ : Fin 1 => z) a).1 = ∑ a, (A a).1 + z.1 := by rw [sum_app, hzs]
  have h2 : ∑ a, (Fin.append A pr a).1 = ∑ a, (A a).1 + z.1 := by rw [sum_app, hs]
  have hN : ∑ a, (A a).1 + z.1 + ∑ a, (B a).1 = N := by rw [← ht, sum_app, h2]
  subst hN
  have h3 : ∑ a, (Fin.append (Fin.append A (fun _ : Fin 1 => z)) B a).1 = ∑ a, (A a).1 + z.1 + ∑ a, (B a).1 := by
    rw [sum_app, h1]
  have e0 : Emb (prodIrr (fun _ : Fin 1 => z) hzs) (prodIrr pr hs) :=
    (Emb.of' (nonempty_equiv_prodIrr_one z hzs)).trans he
  refine ⟨_, _, h3, Fin.castAdd q (Fin.natAdd i (0 : Fin 1)), by rw [Fin.append_left, Fin.append_right], ?_⟩
  exact emb_left _ _ B h1 h2 rfl (emb_right A _ pr rfl hzs hs e0 h1 h2) h3 ht

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem exists_alt_ter {d : ℕ} (σ : IrrRep (GL (Fin d) k)) {U : Type} [AddCommGroup U] [Module ℂ U]
    (τ : Representation ℂ (GL (Fin (2 * d)) k) U) (hsS : IsSmooth τ) (hiS : τ.IsIrreducible)
    (hs : ∑ j, (tcl σ 2 j).1 = 2 * d) (a2 : Emb τ (prodIrr (tcl σ 2) hs))
    (eS : (jac (consecBlocks 2 d) τ).Equiv (piTensor (segTerm σ.ρ 2))) :
    ∃ (z : IrrGL (k := k)) (hs : ∑ j, (tcl σ 2 j).1 = z.1), Emb z.rep (prodIrr (tcl σ 2) hs) ∧
      Nonempty ((jac (stdBlocks (fun j => (tcl σ 2 j).1) hs) z.rep).Equiv (piTensor fun j => (tcl σ 2 j).rep)) := by
  have a1 : Emb (IrrGL.of τ hsS hiS).rep τ := Emb.of' ⟨IrrGL.equivOf τ hsS hiS⟩
  have he2 : stdBlocks (fun j => (tcl σ 2 j).1) hs = consecBlocks 2 d := blocks_eq 2 d hs
  have e1 : (piTensor (segTerm σ.ρ 2)).Equiv (piTensor fun a => (tcl σ 2 a).rep) :=
    piTensorEquiv fun a => IrrGL.equivOf _ _ _
  have a3 : Nonempty ((jac (stdBlocks (fun j => (tcl σ 2 j).1) hs) τ).Equiv (piTensor fun j => (tcl σ 2 j).rep)) := by
    rw [he2]
    exact ⟨eS.trans e1⟩
  exact ⟨IrrGL.of τ hsS hiS, hs, a1.trans a2,
    ⟨(SrMult.jacEquivOf (stdBlocks (fun j => (tcl σ 2 j).1) hs) (IrrGL.equivOf τ hsS hiS).symm).trans a3.some⟩⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem exists_unit_one_add_generator (h2 : CompanionTheory.Pf1.SegRepC.SegTwo) {d : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ) :
    ∃ (z : IrrGL (k := k)) (hs : ∑ j, (tcl σ 2 j).1 = z.1), Emb z.rep (prodIrr (tcl σ 2) hs) ∧
      Nonempty ((jac (stdBlocks (fun j => (tcl σ 2 j).1) hs) z.rep).Equiv (piTensor fun j => (tcl σ 2 j).rep)) := by
  obtain ⟨S, hiS, -, ⟨eS⟩⟩ := h2 k d hd σ hσ
  have hs : ∑ j, (tcl σ 2 j).1 = 2 * d := sum_const_fin 2 d
  exact exists_alt_ter σ S.toRepresentation (GlobalTheory.CompanionTheory.JacExp.isSmooth_sub (isSmooth_parInd _ _) S) hiS hs
    ((Emb.sub S).trans (Emb.of (consec_equiv σ 2 hs))) eS

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem one_le_jm {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) {U X : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup X]
    [Module ℂ X] (τ : Representation ℂ (GL (Fin (l * d)) k) U) (π : Representation ℂ (Levi k fun _ : Fin l => Fin d) X)
    (hsub : IsSubquotient π (jac (consecBlocks l d) τ)) (w : Equiv.Perm (Fin l))
    (φ : π.Equiv (piTensor fun a => segTerm σ.ρ l (w a))) (hy : ∑ a, (tcl σ l (w a)).1 = l * d) :
    1 ≤ Zc.jm (fun a => tcl σ l (w a)) hy τ := by
  have hey : stdBlocks (fun a => (tcl σ l (w a)).1) hy = consecBlocks l d := blocks_eq _ d hy
  refine ENat.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2 ?_)
  show IsSubquotient (piTensor fun a => (tcl σ l (w a)).rep) (jac (stdBlocks (fun a => (tcl σ l (w a)).1) hy) τ)
  rw [hey]
  have e1 : (piTensor fun a => segTerm σ.ρ l (w a)).Equiv (piTensor fun a => (tcl σ l (w a)).rep) :=
    piTensorEquiv fun a => IrrGL.equivOf _ _ _
  exact (GlobalTheory.JacStages.isSubquotient_of_equiv (e1.symm.trans φ.symm)).trans hsub

end StageC

open StageC in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem stageP : StageP := by
  intro k _ _ _ _ _ h2 d l hd _ σ hσ i hi
  obtain ⟨q, rfl⟩ : ∃ q, l = i + 2 + q := ⟨l - (i + 2), by omega⟩
  have hx : (cls σ).IsCusp := ⟨hd, isCuspidal_of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irr) hσ⟩
  obtain ⟨σ', hσ'c, hcls'⟩ : ∃ σ' : IrrRep (GL (Fin d) k), IsCuspidal σ'.ρ ∧ cls σ' = (cls σ).nu ((i : ℕ) : ℂ) :=
    ⟨((cls σ).nu ((i : ℕ) : ℂ)).2.rep, (hx.nu _).2, IrrGL.of_rep _⟩
  have hpr : ∀ j : Fin 2, tcl σ' 2 j = tcl σ (i + 2 + q) (Fin.castAdd q (Fin.natAdd i j)) := by
    intro j
    rw [tcl_eq, tcl_eq, hcls', IrrGL.nu_nu]
    congr 1
    simp only [Fin.val_castAdd, Fin.val_natAdd]
    push_cast
    ring
  obtain ⟨z, hs, hz, hu⟩ := exists_unit_one_add_generator h2 hd σ' hσ'c
  have ht : ∑ a, (tcl σ (i + 2 + q) a).1 = (i + 2 + q) * d := sum_const_fin (i + 2 + q) d
  obtain ⟨n, xx, hdx, iz, hxz, he⟩ := classMain (tcl σ (i + 2 + q)) ht (tcl σ' 2) hpr z hs hz
  haveI := GlobalTheory.CompanionTheory.AdjQuot.nontrivial_prodIrr xx hdx
  obtain ⟨T, hT, hTs⟩ := (he.trans (Emb.of' (consec_equiv σ (i + 2 + q) ht))).range
  refine ⟨T, hT, ?_⟩
  intro X _ _ π _ hsub w φ
  have hy : ∑ a, (tcl σ (i + 2 + q) (w a)).1 = (i + 2 + q) * d := sum_const_fin (i + 2 + q) d
  have hjm := (one_le_jm σ T.toRepresentation π hsub w φ hy).trans
    (GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient _ hy _ _ (isSmooth_prodIrr xx hdx) hTs)
  have hsc : ∀ j, (tcl σ' 2 j).IsCusp := fun j => by
    rw [tcl_eq, hcls']
    exact (hx.nu _).nu _
  obtain ⟨f, hf⟩ := comb xx hdx iz z hxz (tcl σ' 2) hs d (fun _ => rfl) hsc hu _ hy
    (fun a => by rw [tcl_eq]; exact hx.nu _) hjm
  have hval : ∀ j : Fin 2, ((w (f j) : Fin (i + 2 + q)) : ℕ) = i + j := by
    intro j
    have h3 : tcl σ (i + 2 + q) (w (f j)) = tcl σ (i + 2 + q) (Fin.castAdd q (Fin.natAdd i j)) := (hf j).trans (hpr j)
    rw [tcl_eq, tcl_eq] at h3
    exact (IrrGL.nu_natCast_inj hx.1).1 h3
  have e0 : w.symm ⟨i, by omega⟩ = f 0 := by
    rw [Equiv.symm_apply_eq]
    exact Fin.ext (by simpa using (hval 0).symm)
  have e1 : w.symm ⟨i + 1, hi⟩ = f 1 := by
    rw [Equiv.symm_apply_eq]
    exact Fin.ext (by simpa using (hval 1).symm)
  rw [e0, e1]
  exact f.strictMono (by decide)

end CompanionTheory.RgGu.SRC

end
end

section -- merged from CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.RhoNuRhoReducibleC
section -- merged from CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.RhoNuRhoOfC
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.Published

namespace CompanionTheory.RgGu.NR

namespace RedC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem irr_congr {h N : ℕ} {x x' : Fin h → IrrGL (k := k)} (e : x = x') (hd : ∑ a, (x a).1 = N) :
    ∃ hd' : ∑ a, (x' a).1 = N, ((prodIrr x hd).IsIrreducible ↔ (prodIrr x' hd').IsIrreducible) := by
  subst e
  exact ⟨hd, Iff.rfl⟩

theorem irr_tw {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (s : ℂ)
    (hi : (prodIrr x hd).IsIrreducible) : (prodIrr (fun a => (x a).nu s) hd).IsIrreducible :=
  GlobalTheory.Parabolic.isIrreducible_of_equiv (prodIrrTwistEquiv x hd (absPow k s) (isSmoothChar_absPow s))
    (isIrreducible_twist hi _)

end RedC

open RedC in
set_option maxHeartbeats 800000 in
theorem redCl_ofC (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (h1 : SomeRed k) (h2 : CuspUnit k) (h3 : GlobalTheory.BZSeg.CuspPairIrr k) : RedCl k := by
  intro y hy N hd hirr
  obtain ⟨ρ, z, hρ, hu, rfl⟩ := h2 y hy
  obtain ⟨s, hs0, hs⟩ := h1 ρ hρ hu
  have hpos : 0 < ρ.1 := hρ.1
  have hs2 : s = 1 / 2 := by
    by_contra hne
    have hd0 : ∑ a, (![ρ.nu (-(s : ℂ)), ρ.nu (s : ℂ)] a).1 = ∑ a, (![ρ.nu (-(s : ℂ)), ρ.nu (s : ℂ)] a).1 := rfl
    refine hs _ hd0 (h3 _ _ _ hd0 (hρ.nu _) (hρ.nu _) ?_ ?_)
    · intro e
      rw [IrrGL.nu_nu, show -(s : ℂ) + 1 = ((-s + 1 : ℝ) : ℂ) by push_cast; ring] at e
      have := (IrrGL.nu_ofReal_inj hpos).1 e
      exact hne (by linarith)
    · intro e
      rw [IrrGL.nu_nu, show -(s : ℂ) = ((-s : ℝ) : ℂ) by push_cast; ring,
        show (s : ℂ) + 1 = ((s + 1 : ℝ) : ℂ) by push_cast; ring] at e
      have := (IrrGL.nu_ofReal_inj hpos).1 e
      linarith
  set t : ℂ := -((z : ℂ) + 1 / 2) with ht
  have key : (fun a => (![ρ.nu (z : ℂ), (ρ.nu (z : ℂ)).nu 1] a).nu t) = ![ρ.nu (-(s : ℂ)), ρ.nu (s : ℂ)] := by
    funext a
    fin_cases a
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      rw [IrrGL.nu_nu, hs2, ht]
      congr 1
      push_cast
      ring
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons]
      rw [IrrGL.nu_nu, IrrGL.nu_nu, hs2, ht]
      congr 1
      push_cast
      ring
  obtain ⟨hd', hiff⟩ := irr_congr key hd
  exact hs N hd' (hiff.1 (irr_tw _ hd t hirr))

theorem rhoNuRho_ofC (h : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    RedCl k) : CompanionTheory.Pf1.SegRepC.SegTwo.RhoNuRhoReducible := by
  intro k _ _ _ _ d hd σ hσ hirr
  set y : IrrGL (k := k) := IrrGL.of σ.ρ σ.smooth σ.irr with hy
  have hyc : y.IsCusp := IrrGL.isCusp_of.2 ⟨hd, hσ⟩
  let x : Fin 2 → IrrGL (k := k) := fun a => y.nu ((a : ℕ) : ℂ)
  have hx1 : ∀ a, (x a).1 = d := fun _ => rfl
  have hdx : ∑ a, (x a).1 = 2 * d := by
    simp only [hx1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  let φ : ∀ a : Fin 2, (segTerm σ.ρ 2 a).Equiv (x a).rep := fun a =>
    (twistEquiv (IrrGL.equivOf σ.ρ σ.smooth σ.irr) _).trans (y.twEquiv _ _)
  have E1 := multiProdEquiv (consecBlocks 2 d) φ
  have hdd : ∑ _a : Fin 2, d = 2 * d := by simp
  have hE : consecBlocks 2 d = stdBlocks (fun _ : Fin 2 => d) hdd := by
    ext ⟨a, i⟩
    rw [consecBlocks_val, stdBlocks_val]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have h3 : (prodIrr x hdx).IsIrreducible := by
    have h4 := GlobalTheory.Parabolic.isIrreducible_of_equiv E1 hirr
    rw [hE] at h4
    exact h4
  have e : x = ![y, y.nu 1] := by
    funext a
    fin_cases a
    · simp [x]
    · simp [x]
  obtain ⟨hd', hiff⟩ := RedC.irr_congr e hdx
  exact h k y hyc (2 * d) hd' (hiff.1 h3)

end CompanionTheory.RgGu.NR
end
end

namespace CompanionTheory.RgGu.NR

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem redClC : RedCl k :=
  redCl_ofC k (someRed_of k (complementary_of signature) (compact k) (boundB k) (herm_ofB k (conjProd k) (conjDual k))
    (prodModel k)) (cuspUnit k) (cuspPairIrr k)

theorem rhoNuRhoReducibleC : CompanionTheory.Pf1.SegRepC.SegTwo.RhoNuRhoReducible := rhoNuRho_ofC fun k _ _ _ _ => redClC k

end CompanionTheory.RgGu.NR
end

namespace CompanionTheory.RgGu

theorem segmentRepresentation : GlobalTheory.Published.SegmentRepresentation :=
  have hG : GlobalTheory.Published.GeometricLemma :=
    GlobalTheory.geometricLemma_of_filtration GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness CompanionTheory.Geo.geometricLemmaFiltration
  SRC.segRep_of SRC.stageP hG (SRC.segTwo_of hG NR.rhoNuRhoReducibleC)

end CompanionTheory.RgGu
