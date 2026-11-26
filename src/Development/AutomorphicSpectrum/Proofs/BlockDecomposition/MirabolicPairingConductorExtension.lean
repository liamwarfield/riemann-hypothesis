module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColJoinColLColR

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearOrbitFinite
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearOrbitFinite
noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair.ShearOrbit

variable {k : Type} [Field k]

theorem shear_mul_inv (n : ℕ) (b : Fin (n + 1) → k) (hb : 1 + b (Fin.last n) ≠ 0) :
    (1 + vecMulVec (eLast k n) b) * (1 - (1 + b (Fin.last n))⁻¹ • vecMulVec (eLast k n) b) = 1 := by
  have hd : b ⬝ᵥ GlobalTheory.BZMir.eLast k n = b (Fin.last n) := by
    simp [GlobalTheory.BZMir.eLast, dotProduct_single]
  have hM : vecMulVec (GlobalTheory.BZMir.eLast k n) b * vecMulVec (GlobalTheory.BZMir.eLast k n) b =
      b (Fin.last n) • vecMulVec (GlobalTheory.BZMir.eLast k n) b := by
    rw [vecMulVec_mul_vecMulVec, hd]
    ext i j
    simp only [vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hc : (1 + b (Fin.last n))⁻¹ + (1 + b (Fin.last n))⁻¹ * b (Fin.last n) = 1 := by
    rw [← mul_one_add]
    exact inv_mul_cancel₀ hb
  rw [mul_sub, mul_one, mul_smul_comm, add_mul, one_mul, hM, smul_add, smul_smul, ← add_smul, hc,
    one_smul, add_sub_cancel_right]

theorem shearGL_val (n : ℕ) (b : Fin (n + 1) → k) (hb : 1 + b (Fin.last n) ≠ 0) :
    ((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      1 + vecMulVec (eLast k n) b := by
  have h := GlobalTheory.CompanionTheory.MirPair.ShearOrbit.shear_mul_inv n b hb
  have hu : IsUnit (1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b) :=
    ⟨⟨_, _, h, mul_eq_one_comm.mp h⟩, rfl⟩
  rw [GlobalTheory.CompanionTheory.MirPair.shearGL, dite_eq_left hu]
  exact hu.unit_spec

theorem shearGL_inv_val (n : ℕ) (b : Fin (n + 1) → k) (hb : 1 + b (Fin.last n) ≠ 0) :
    (((shearGL n b)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      1 - (1 + b (Fin.last n))⁻¹ • vecMulVec (eLast k n) b :=
  Units.inv_eq_of_mul_eq_one_right (by rw [shearGL_val n b hb]; exact shear_mul_inv n b hb)

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem one_add_ne_zero_of_mem_box (n : ℕ) {r : kˣ} (hr : valuation k (r : k) < 1) {b : Fin (n + 1) → k}
    (hb : b ∈ box (n + 1) r) : 1 + b (Fin.last n) ≠ 0 := by
  intro h
  have h1 : valuation k (b (Fin.last n)) ≤ valuation k (r : k) := hb (Fin.last n)
  have h2 : b (Fin.last n) = -1 := by linear_combination h
  rw [h2, Valuation.map_neg, map_one] at h1
  exact absurd hr (not_lt.mpr h1)

theorem continuous_shearGL (n : ℕ) {r : kˣ} (hr : valuation k (r : k) < 1) :
    Continuous fun b : (box (n + 1) r : Set (Fin (n + 1) → k)) => shearGL n b.1 := by
  have hne : ∀ b : (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) r : Set (Fin (n + 1) → k)), 1 + b.1 (Fin.last n) ≠ 0 :=
    fun b => GlobalTheory.CompanionTheory.MirPair.ShearOrbit.one_add_ne_zero_of_mem_box n hr b.2
  have hv : Continuous fun b : (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) r : Set (Fin (n + 1) → k)) =>
      vecMulVec (GlobalTheory.BZMir.eLast k n) b.1 :=
    continuous_matrix fun i j => by
      simp only [vecMulVec_apply]
      exact continuous_const.mul ((continuous_apply j).comp continuous_subtype_val)
  rw [Units.continuous_iff]
  constructor
  · exact (continuous_const.add hv).congr fun b => (GlobalTheory.CompanionTheory.MirPair.ShearOrbit.shearGL_val n b.1 (hne b)).symm
  · have hinv : Continuous fun b : (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) r : Set (Fin (n + 1) → k)) =>
        (1 + b.1 (Fin.last n))⁻¹ :=
      (continuous_const.add ((continuous_apply _).comp continuous_subtype_val)).inv₀ hne
    exact (continuous_const.sub (hinv.smul hv)).congr fun b => (GlobalTheory.CompanionTheory.MirPair.ShearOrbit.shearGL_inv_val n b.1 (hne b)).symm


omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem continuous_levi (m : ℕ) : Continuous (levi k m) := by
  have hmat : Continuous (GlobalTheory.BZMir.glEmbHom k m) := by
    apply continuous_matrix
    intro i j
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp [GlobalTheory.BZMir.glEmbHom, GlobalTheory.BZMir.glEmbMat] <;>
      first
        | exact continuous_const
        | exact continuous_id.matrix_elem _ _
        | fun_prop
  have hGL : Continuous (GlobalTheory.BZMir.glEmb k m) := Continuous.units_map _ hmat
  exact continuous_induced_rng.2 hGL

theorem isOpen_orbit_fiber {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : Representation ℂ (Mir k (n + 1)) V) (hT : IsSmooth T) (v w : V) :
    IsOpen {p : Mir k (n + 1) | T p v = w} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  have hS : IsOpen {g : GlobalTheory.BZMir.Mir k (n + 1) | T g v = v} := hT v
  have hcont : Continuous fun g : GlobalTheory.BZMir.Mir k (n + 1) => p⁻¹ * g := continuous_const.mul continuous_id
  have hmem : (fun g : GlobalTheory.BZMir.Mir k (n + 1) => p⁻¹ * g) ⁻¹' {g | T g v = v} ∈ 𝓝 p := by
    apply hcont.continuousAt.preimage_mem_nhds
    apply hS.mem_nhds
    simp
  filter_upwards [hmem] with g hg
  have hg' : T (p⁻¹ * g) v = v := hg
  have hsplit : T g = T p * T (p⁻¹ * g) := by
    rw [← map_mul, mul_inv_cancel_left]
  show T g v = w
  rw [hsplit, Module.End.mul_apply, hg']
  exact hp

theorem shear_orbit_finite {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : Representation ℂ (Mir k (n + 1)) V) (hT : IsSmooth T) (v : V) (r : kˣ)
    (hr : valuation k (r : k) < 1) :
    ((fun b => T (levi k (n + 1) (shearGL n b)) v) '' (box (n + 1) r : Set (Fin (n + 1) → k))).Finite := by
  haveI : CompactSpace (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) r : Set (Fin (n + 1) → k)) :=
    isCompact_iff_compactSpace.mp (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.isCompact_box (n + 1) r)
  have hc : Continuous fun b : (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) r : Set (Fin (n + 1) → k)) =>
      GlobalTheory.BZMir.levi k (n + 1) (GlobalTheory.CompanionTheory.MirPair.shearGL n b.1) :=
    (GlobalTheory.CompanionTheory.MirPair.ShearOrbit.continuous_levi (n + 1)).comp (GlobalTheory.CompanionTheory.MirPair.ShearOrbit.continuous_shearGL n hr)
  have hlc : IsLocallyConstant fun b : (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) r : Set (Fin (n + 1) → k)) =>
      T (GlobalTheory.BZMir.levi k (n + 1) (GlobalTheory.CompanionTheory.MirPair.shearGL n b.1)) v := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro w
    exact (GlobalTheory.CompanionTheory.MirPair.ShearOrbit.isOpen_orbit_fiber T hT v w).preimage hc
  rw [Set.image_eq_range]
  exact hlc.range_finite

end GlobalTheory.CompanionTheory.MirPair.ShearOrbit

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearOrbitFiniteStatement
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shear_orbit_box_finite_of_isSmooth : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (T : Representation ℂ (Mir k (n + 1)) V), IsSmooth T → ∀ (v : V) (r : kˣ), valuation k (r : k) < 1 → ((fun b => T (levi k (n + 1) (shearGL n b)) v) '' (box (n + 1) r : Set (Fin (n + 1) → k))).Finite := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.ShearOrbit.shear_orbit_finite | exact GlobalTheory.CompanionTheory.MirPair.ShearOrbit.shear_orbit_finite | (intros; apply GlobalTheory.CompanionTheory.MirPair.ShearOrbit.shear_orbit_finite <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicTwistedKernelNonvanishing
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicTwistedKernelNonvanishing
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

noncomputable section

namespace GlobalTheory.CompanionTheory.MirPair.AvgBox

theorem setIntegral_eq_sum_reps {E : Type} [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd E]
    (μ : Measure E) [μ.IsAddLeftInvariant] (D M : AddSubgroup E) (hD : MeasurableSet (D : Set E))
    (hfin : μ (D : Set E) ≠ ⊤) (hDM : D ≤ M) (S : Finset E) (hSM : ∀ s ∈ S, s ∈ M)
    (hS : ∀ x ∈ M, ∃! s, s ∈ S ∧ x - s ∈ D) (f : E → ℂ) (hf : ∀ x, ∀ d ∈ D, f (x + d) = f x) :
    ∫ x in (M : Set E), f x ∂μ = ((μ.real (D : Set E) : ℝ) : ℂ) * ∑ s ∈ S, f s := by
  classical
  set A : E → Set E := fun s => (fun x => -s + x) ⁻¹' (D : Set E) with hA
  have hAm : ∀ s, MeasurableSet (A s) := fun s => (measurable_const_add (-s)) hD
  have hmem : ∀ s x, x ∈ A s ↔ x - s ∈ D := by
    intro s x
    simp only [hA, Set.mem_preimage, SetLike.mem_coe, neg_add_eq_sub]
  have hAM : ∀ s ∈ S, ∀ x ∈ A s, x ∈ M := by
    intro s hs x hx
    have := M.add_mem (hDM ((hmem s x).1 hx)) (hSM s hs)
    simpa using this
  have hU : (M : Set E) = ⋃ s ∈ S, A s := by
    ext x
    simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop]
    constructor
    · intro hx
      obtain ⟨s, ⟨hs, hxs⟩, -⟩ := hS x hx
      exact ⟨s, hs, (hmem s x).2 hxs⟩
    · rintro ⟨s, hs, hx⟩
      exact hAM s hs x hx
  have hdisj : Set.Pairwise (S : Set E) (Function.onFun Disjoint A) := by
    intro s hs s' hs' hne
    refine Set.disjoint_left.2 fun x hx hx' => hne ?_
    exact (hS x (hAM s hs x hx)).unique ⟨hs, (hmem s x).1 hx⟩ ⟨hs', (hmem s' x).1 hx'⟩
  have hconst : ∀ s, Set.EqOn (fun _ => f s) f (A s) := by
    intro s x hx
    have := hf s (x - s) ((hmem s x).1 hx)
    simpa using this.symm
  have hvol : ∀ s, μ (A s) = μ (D : Set E) := fun s => measure_preimage_add μ (-s) _
  rw [hU, integral_biUnion_finset S (fun s _ => hAm s) hdisj ?_]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← setIntegral_congr_fun (hAm s) (hconst s), setIntegral_const]
    simp [Measure.real, hvol]
  · intro s _
    refine IntegrableOn.congr_fun ?_ (hconst s) (hAm s)
    exact integrableOn_const (by rw [hvol]; exact hfin)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem uM_add (n : ℕ) (x y : Fin n → k) : uM n (x + y) = uM n x * uM n y := by
  simp only [uM, ofAdd_add, map_mul]

theorem continuous_uM (n : ℕ) : Continuous (uM (k := k) n) :=
  (continuous_unipIn n).comp continuous_ofAdd

section Rep

variable {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem sub_smul_mem_twKer (ψ : AddChar k Circle) (T : Representation ℂ (Mir k (n + 1)) V)
    (y : Fin (n + 1) → k) (v : V) :
    T (uM (n + 1) y) v - ((ψ (y (Fin.last n)) : Circle) : ℂ) • v ∈
      twKer T (MirUin k (n + 1)) (mirChar k ψ n) := by
  let x : MirUin k (n + 1) := ⟨uM (n + 1) y, Subgroup.mem_subgroupOf.2 ⟨Multiplicative.ofAdd y, rfl⟩⟩
  have hx := mirChar_eq k ψ n x (Multiplicative.ofAdd y) rfl
  refine Submodule.subset_span ⟨x, v, ?_⟩
  rw [hx]
  rfl

theorem wt_mul_psi (ψ : AddChar k Circle) (y : Fin (n + 1) → k) :
    wt ψ n y * ((ψ (y (Fin.last n)) : Circle) : ℂ) = 1 := by
  rw [wt, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  simp

theorem avg_sub_mem_twKer (ψ : AddChar k Circle) (T : Representation ℂ (Mir k (n + 1)) V)
    (S : Finset (Fin (n + 1) → k)) (v : V) :
    (∑ s ∈ S, wt ψ n s • T (uM (n + 1) s) v) - (S.card : ℂ) • v ∈
      twKer T (MirUin k (n + 1)) (mirChar k ψ n) := by
  have h : (∑ s ∈ S, wt ψ n s • T (uM (n + 1) s) v) - (S.card : ℂ) • v =
      ∑ s ∈ S, wt ψ n s • (T (uM (n + 1) s) v - ((ψ (s (Fin.last n)) : Circle) : ℂ) • v) := by
    simp only [smul_sub, smul_smul, wt_mul_psi, one_smul, Finset.sum_sub_distrib, Finset.sum_const,
      Nat.cast_smul_eq_nsmul]
  rw [h]
  exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (sub_smul_mem_twKer ψ T s v)

theorem integrand_add (ψ : AddChar k Circle) (T : Representation ℂ (Mir k (n + 1)) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ)
    (v : V) (v' : V') (x d : Fin (n + 1) → k) (hd : T (uM (n + 1) d) v = v)
    (hψ : ψ (d (Fin.last n)) = 1) :
    wt ψ n (x + d) * coef T B v v' (x + d) = wt ψ n x * coef T B v v' x := by
  have h1 : wt ψ n (x + d) = wt ψ n x := by
    simp only [wt, Pi.add_apply, neg_add, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, hψ, inv_one, mul_one]
  have h2 : coef T B v v' (x + d) = coef T B v v' x := by
    simp only [coef, uM_add, map_mul, Module.End.mul_apply, hd]
  rw [h1, h2]

end Rep

theorem exists_JJ_ne_zero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ), Continuous ψ → IsSmooth T → (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) → ∀ v : V, v ∉ twKer T (MirUin k (n + 1)) (mirChar k ψ n) → ∃ t₀ : kˣ, ∀ t : kˣ, valuation k (t₀ : k) ≤ valuation k (t : k) → ∃ v', JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) v v' ≠ 0 := by
  intro k _ _ _ _ _ _ ν _ ψ n V V' _ _ _ _ T B hψ hT hB v hv
  haveI : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k
  haveI : SigmaFinite ν := sigmaFinite_of_locallyFinite
  haveI : (piHaar ν (n + 1)).IsAddHaarMeasure := by
    unfold piHaar
    infer_instance
  obtain ⟨r, hr⟩ := exists_cball_addChar_eq_one ψ hψ
  have hΩ₁ : {y : Fin (n + 1) → k | T (uM (n + 1) y) v = v} ∈ 𝓝 (0 : Fin (n + 1) → k) := by
    refine ((hT v).preimage (continuous_uM (n + 1))).mem_nhds ?_
    simp [uM]
  have hΩ₂ : {y : Fin (n + 1) → k | y (Fin.last n) ∈ cball r} ∈ 𝓝 (0 : Fin (n + 1) → k) := by
    have h0 : cball r ∈ 𝓝 ((0 : Fin (n + 1) → k) (Fin.last n)) := by simpa using cball_mem_nhds r
    exact (continuous_apply (Fin.last n)).continuousAt h0
  obtain ⟨t₀, ht₀⟩ := exists_box_subset (Filter.inter_mem hΩ₁ hΩ₂)
  refine ⟨t₀, fun t ht => ?_⟩
  have hDM : box (n + 1) t₀ ≤ box (n + 1) t := fun x hx j =>
    show valuation k (x j) ≤ valuation k (t : k) from
      le_trans (show valuation k (x j) ≤ valuation k (t₀ : k) from hx j) ht
  have hDo : IsOpen (box (n + 1) t₀ : Set (Fin (n + 1) → k)) :=
    AddSubgroup.isOpen_of_mem_nhds _ (g := 0) (box_mem_nhds (n + 1) t₀)
  obtain ⟨S, hSM, hS⟩ := GlobalTheory.CompanionTheory.OpenSubgroupCosets.exists_finset_unique_coset_reps
    (box (n + 1) t₀) hDo (box (n + 1) t : Set (Fin (n + 1) → k)) (isCompact_box (n + 1) t)
  have hfin : piHaar ν (n + 1) (box (n + 1) t₀ : Set (Fin (n + 1) → k)) ≠ ⊤ :=
    (isCompact_box (n + 1) t₀).measure_lt_top.ne
  have hpos : piHaar ν (n + 1) (box (n + 1) t₀ : Set (Fin (n + 1) → k)) ≠ 0 :=
    hDo.measure_ne_zero _ ⟨0, (box (n + 1) t₀).zero_mem⟩
  have hvol : ((piHaar ν (n + 1)).real (box (n + 1) t₀ : Set (Fin (n + 1) → k)) : ℝ) ≠ 0 :=
    (ENNReal.toReal_pos hpos hfin).ne'
  have hcard : (S.card : ℂ) ≠ 0 := by
    obtain ⟨s, ⟨hs, -⟩, -⟩ := hS 0 (box (n + 1) t).zero_mem
    exact Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem hs)
  set v₁ : V := ∑ s ∈ S, wt ψ n s • T (uM (n + 1) s) v with hv₁
  have hv₁0 : v₁ ≠ 0 := by
    intro h0
    have h := avg_sub_mem_twKer ψ T S v
    rw [← hv₁, h0, zero_sub, neg_mem_iff] at h
    exact hv ((Submodule.smul_mem_iff _ hcard).1 h)
  obtain ⟨v', hv'⟩ := hB v₁ hv₁0
  refine ⟨v', ?_⟩
  have hJ : JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) v v' =
      (((piHaar ν (n + 1)).real (box (n + 1) t₀ : Set (Fin (n + 1) → k)) : ℝ) : ℂ) * B v₁ v' := by
    rw [JJ, setIntegral_eq_sum_reps (piHaar ν (n + 1)) (box (n + 1) t₀) (box (n + 1) t) hDo.measurableSet hfin hDM S
      hSM hS _ fun x d hd => integrand_add ψ T B v v' x d (ht₀ hd).1 (hr _ (ht₀ hd).2)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hv₁, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, coef]
  rw [hJ]
  exact mul_ne_zero (Complex.ofReal_ne_zero.2 hvol) hv'

end GlobalTheory.CompanionTheory.MirPair.AvgBox

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicTwistedKernelNonvanishingStatement
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_twisted_kernel_nonvanishing : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ), Continuous ψ → IsSmooth T → (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) → ∀ v : V, v ∉ twKer T (MirUin k (n + 1)) (mirChar k ψ n) → ∃ t₀ : kˣ, ∀ t : kˣ, valuation k (t₀ : k) ≤ valuation k (t : k) → ∃ v', JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) v v' ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.AvgBox.exists_JJ_ne_zero | exact GlobalTheory.CompanionTheory.MirPair.AvgBox.exists_JJ_ne_zero | (intros; apply GlobalTheory.CompanionTheory.MirPair.AvgBox.exists_JJ_ne_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorExtension
noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair.Nondeg

theorem box_subset_of_valuation_le {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {m : ℕ} {s t : kˣ} (h : valuation k (s : k) ≤ valuation k (t : k)) :
    (box m s : Set (Fin m → k)) ⊆ box m t := fun x hx j =>
  le_trans (show valuation k (x j) ≤ valuation k (s : k) from hx j) h

theorem exists_unit_bound {k : Type} [Field k] [ValuativeRel k] {W : Type} {S : Set W} (hS : S.Finite)
    (τ : W → kˣ) (t : kˣ) :
    ∃ u : kˣ, valuation k (t : k) ≤ valuation k (u : k) ∧
      ∀ w ∈ S, valuation k (τ w : k) ≤ valuation k (u : k) := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨t, le_rfl, by simp⟩
  | @insert a s _ _ ih =>
    obtain ⟨u, h1, h2⟩ := ih
    rcases le_total (valuation k (u : k)) (valuation k (τ a : k)) with h | h
    · refine ⟨τ a, h1.trans h, fun w hw => ?_⟩
      rcases Set.mem_insert_iff.1 hw with rfl | hw
      · exact le_rfl
      · exact (h2 w hw).trans h
    · refine ⟨u, h1, fun w hw => ?_⟩
      rcases Set.mem_insert_iff.1 hw with rfl | hw
      · exact h
      · exact h2 w hw

theorem exists_large_unit {k : Type} [Field k] [ValuativeRel k] (c r t₀ : kˣ) :
    ∃ t : kˣ, valuation k (t₀ : k) ≤ valuation k (t : k) ∧
      valuation k ((c * t⁻¹ : kˣ) : k) ≤ valuation k (r : k) := by
  rcases le_total (valuation k (t₀ : k)) (valuation k ((c * r⁻¹ : kˣ) : k)) with h | h
  · refine ⟨c * r⁻¹, h, ?_⟩
    have e : c * (c * r⁻¹)⁻¹ = r := by simp
    rw [e]
  · refine ⟨t₀, le_rfl, ?_⟩
    have e : ((c * t₀⁻¹ : kˣ) : k) = ((c * r⁻¹ : kˣ) : k) * ((t₀⁻¹ : kˣ) : k) * (r : k) := by
      push_cast
      field_simp
    have e1 : valuation k (t₀ : k) * valuation k ((t₀⁻¹ : kˣ) : k) = 1 := by
      rw [← map_mul]
      simp
    rw [e, map_mul, map_mul]
    calc valuation k ((c * r⁻¹ : kˣ) : k) * valuation k ((t₀⁻¹ : kˣ) : k) * valuation k (r : k)
        ≤ valuation k (t₀ : k) * valuation k ((t₀⁻¹ : kˣ) : k) * valuation k (r : k) := by gcongr
      _ = valuation k (r : k) := by rw [e1, one_mul]

theorem continuous_wt_mul_coef {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψ : Continuous ψ) {n : ℕ} {V V' : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V)
    (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (hT : IsSmooth T) (v : V) (v' : V') :
    Continuous fun x => wt ψ n x * coef T B v v' x := by
  refine Continuous.mul ?_ (continuous_coef T B hT v v')
  have h : Continuous fun x : Fin (n + 1) → k => ψ (-x (Fin.last n)) :=
    hψ.comp (continuous_apply _).neg
  exact continuous_subtype_val.comp h

end GlobalTheory.CompanionTheory.MirPair.Nondeg

namespace GlobalTheory.CompanionTheory.MirPair


open GlobalTheory.CompanionTheory.MirPair.Nondeg in
theorem exists_evVal_ne_zero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) → ∀ v : V, v ∉ twKer T (MirUin k (n + 1)) (mirChar k ψ n) → ∃ (v' : V') (A : ℂ), EvVal ν ψ T B v v' A ∧ A ≠ 0 := by
  intro k _ _ _ _ _ _ ν _ ψ c n V V' _ _ _ _ T T' B s hψ hc hT hT' hinv hnd v hv
  obtain ⟨r₁, hr₁, hfix⟩ := GlobalTheory.T.smooth_vector_fixed_small_shear T hT v
  obtain ⟨r₂, hr₂, hlat⟩ := GlobalTheory.T.shear_preserves_box_membership (k := k) (n := n) 1
  obtain ⟨r, hr, hrr₁, hrr₂⟩ : ∃ r : kˣ, valuation k (r : k) < 1 ∧
      valuation k (r : k) ≤ valuation k (r₁ : k) ∧ valuation k (r : k) ≤ valuation k (r₂ : k) := by
    rcases le_total (valuation k (r₁ : k)) (valuation k (r₂ : k)) with h | h
    · exact ⟨r₁, hr₁, le_rfl, h⟩
    · exact ⟨r₂, hr₂, h, le_rfl⟩
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.mirabolic_twisted_kernel_nonvanishing ν ψ T B hψ hT hnd v hv
  obtain ⟨t, htt₀, htc⟩ := exists_large_unit c r t₀
  obtain ⟨v', hv'⟩ := ht₀ t htt₀
  by_contra hno
  push_neg at hno
  have hev : ∀ w : V', ∃ τ : kˣ, ∀ u : kˣ, valuation k (τ : k) ≤ valuation k (u : k) →
      JJ ν ψ T B (box (n + 1) u : Set (Fin (n + 1) → k)) v w = 0 := by
    intro w
    obtain ⟨A, hA⟩ := GlobalTheory.T.mirabolic_pairing_exists_eventual_value ν ψ c T T' B s hψ hc hT hT' hinv v w
    have h0 : A = 0 := hno w A hA
    obtain ⟨τ, hτ⟩ := hA
    exact ⟨τ, fun u hu => (hτ u hu).trans h0⟩
  choose τ hτ using hev
  obtain ⟨u, htu, hu⟩ := exists_unit_bound (GlobalTheory.T.shear_orbit_box_finite_of_isSmooth T' hT' v' r hr) τ t
  have hz : ∀ b ∈ box (n + 1) (c * t⁻¹), ∫ x in (box (n + 1) u : Set (Fin (n + 1) → k)),
      ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * (wt ψ n x * coef T B v v' x) ∂(piHaar ν (n + 1)) = 0 := by
    intro b hb
    have hbr : b ∈ (box (n + 1) r : Set (Fin (n + 1) → k)) := box_subset_of_valuation_le htc hb
    have hlast : valuation k (b (Fin.last n)) < 1 :=
      lt_of_le_of_lt (show valuation k (b (Fin.last n)) ≤ valuation k (r : k) from hbr _) hr
    rw [GlobalTheory.T.mirabolic_pairing_depth_vanishing ν ψ T T' B s hψ hT hinv b _ v v' hlast
      (hfix b (box_subset_of_valuation_le hrr₁ hbr)) ?_]
    · exact hτ _ u (hu _ ⟨b, hbr, rfl⟩)
    · intro x
      have h := hlat b (box_subset_of_valuation_le hrr₂ hbr) u x
      simpa using h
  have hm : MeasurableSet (box (n + 1) u : Set (Fin (n + 1) → k)) := by
    rw [coe_box]
    exact MeasurableSet.univ_pi fun _ => (isOpen_cball u).measurableSet
  have hfin := setIntegral_inter_box_of_twists ν ψ c hψ hc (n + 1) t
    (box (n + 1) u : Set (Fin (n + 1) → k)) (fun x => wt ψ n x * coef T B v v' x) 0
    (isCompact_box _ _) hm (continuous_wt_mul_coef ψ hψ T B hT v v') hz
  rw [Set.inter_eq_right.2 (box_subset_of_valuation_le htu)] at hfin
  exact hv' hfin

end GlobalTheory.CompanionTheory.MirPair

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorExtensionStatement
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_pairing_conductor_extension : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) → ∀ v : V, v ∉ twKer T (MirUin k (n + 1)) (mirChar k ψ n) → ∃ (v' : V') (A : ℂ), EvVal ν ψ T B v v' A ∧ A ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.exists_evVal_ne_zero | exact GlobalTheory.CompanionTheory.MirPair.exists_evVal_ne_zero | (intros; apply GlobalTheory.CompanionTheory.MirPair.exists_evVal_ne_zero <;> assumption)
end
