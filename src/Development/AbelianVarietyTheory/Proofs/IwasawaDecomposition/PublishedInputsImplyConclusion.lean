module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberOfConstructionStepsSecondPass
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelThreeToFour
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAllTiedEqTiedOnOfRealised
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunctionLevelDataOfEqualTuplesZeroIntertwiners
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupPinsOfMuIsW

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrmOfPosDef
open NumberField
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.AmbCrd

open _root_.Formalism.L2.DIV

section Frames

variable {K : Type} [Field K] [NumberField K]


open Classical in
def frm {n : ℕ} (H : Matrix (Fin n) (Fin n) K) : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ :=
  fun v => if (H.map v.embedding).PosDef then frameOf (H.map v.embedding) else 1

theorem frm_det {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) : IsUnit (frm H v).det := by
  unfold frm
  split_ifs with h
  · exact (frameOfSpec _ _ h).1
  · simp

theorem frm_of_posDef {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (h : (H.map v.embedding).PosDef) :
    frm H v = frameOf (H.map v.embedding) := by
  unfold frm
  rw [if_pos h]

end Frames

section Coord

variable {K : Type} [Field K]

def rdx {a b : ℕ} (h : a = b) : (Fin b → K) ≃ₗ[K] (Fin a → K) := LinearEquiv.funCongrLeft K K (finCongr h)

theorem rdx_apply {a b : ℕ} (h : a = b) (x : Fin b → K) (i : Fin a) : rdx h x i = x (Fin.cast h i) := rfl

theorem rdx_refl {a : ℕ} (h : a = a) (x : Fin a → K) : rdx h x = x := by
  funext i
  rw [rdx_apply]
  rfl

end Coord

end GlobalTheory.AmbCrd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefMapEmbeddingOfPositiveAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefMapEmbeddingOfPositiveAtPlace
open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder

namespace GlobalTheory.AmbTiePosDef

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem hAt_eq_dotProduct {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (x y : Fin n → K) :
    hAt H v x y = star (fun i => v.embedding (x i)) ⬝ᵥ (H.map v.embedding) *ᵥ (fun i => v.embedding (y i)) := by
  simp only [hAt, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Pi.star_apply, mul_assoc]

theorem hAt_single_single {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (i j : Fin n) :
    hAt H v (Pi.single i 1) (Pi.single j 1) = v.embedding (H i j) := by
  simp [hAt, Pi.single_apply]

theorem posDef_map_of_posAt [_root_.NumberField.IsTotallyComplex K] {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K)
    (h : PosAt H v) : (H.map v.embedding).PosDef := by
  have herm : (H.map v.embedding).IsHermitian := by
    ext i j
    have := h.1 (Pi.single j 1) (Pi.single i 1)
    rw [hAt_single_single, hAt_single_single] at this
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
    rw [this]
  have hd : DenseRange (Pi.map (fun _ : Fin n => (v.embedding : K → ℂ))) :=
    DenseRange.piMap (fun _ => Formalism.BasicNotions.denseRange_embedding_of_isComplex v (IsTotallyComplex.isComplex v))
  have psd : (H.map v.embedding).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg herm fun z => ?_
    induction z using hd.induction_on with
    | hp =>
      refine isClosed_le continuous_const ?_
      exact Continuous.dotProduct (continuous_star) (Continuous.matrix_mulVec continuous_const continuous_id)
    | ih y =>
      have hy : Pi.map (fun _ : Fin n => (v.embedding : K → ℂ)) y = fun i => v.embedding (y i) := rfl
      rw [hy, ← hAt_eq_dotProduct]
      have hs := h.1 y y
      have him : (hAt H v y y).im = 0 := by
        have := congrArg Complex.im hs
        simp at this
        linarith
      rw [Complex.nonneg_iff]
      refine ⟨?_, him.symm⟩
      by_cases hy0 : y = 0
      · subst hy0
        simp [hAt]
      · exact (h.2 y hy0).le
  rw [psd.posDef_iff_det_ne_zero]
  show (v.embedding.mapMatrix H).det ≠ 0
  rw [← RingHom.map_det]
  intro h0
  rw [map_eq_zero] at h0
  obtain ⟨y, hy0, hHy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hz : hAt H v y y = 0 := by
    rw [hAt_eq_dotProduct]
    have : (H.map v.embedding) *ᵥ (fun i => v.embedding (y i)) = 0 := by
      funext i
      have := RingHom.map_mulVec v.embedding H y i
      rw [hHy] at this
      simpa [Function.comp_def] using this.symm
    rw [this, dotProduct_zero]
  have := h.2 y hy0
  rw [hz] at this
  simp at this

end GlobalTheory.AmbTiePosDef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefMapEmbeddingOfPositiveAtPlaceStatement
open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.posDef_map_embedding_of_positiveAtPlace : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K), Formalism.L2.Rows.PosAt H v → (H.map v.embedding).PosDef := by
  first | exact @GlobalTheory.AmbTiePosDef.posDef_map_of_posAt | exact GlobalTheory.AmbTiePosDef.posDef_map_of_posAt | (intros; apply GlobalTheory.AmbTiePosDef.posDef_map_of_posAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmbExOfRx
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormAtStandardFrameEqNormComplexForm
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormAtStandardFrameEqNormComplexForm
open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder

namespace GlobalTheory.AmbNormTie

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem hform_eq_sum {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    Formalism.DivisionValues.hform H x y = ∑ i, ∑ j, star (x i) * H i j * y j := by
  simp only [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, starRingEnd_apply, RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem j_eq_sum {σ : K →+* ℂ} {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (j : (Fin n → K) →ₛₗ[σ] W) (x : Fin n → K) :
    j x = ∑ i, σ (x i) • j (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (Pi.single i (x i) : Fin n → K) = x i • Pi.single i 1 := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this, LinearMap.map_smulₛₗ]

theorem j_ne_zero {σ : K →+* ℂ} {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (j : (Fin n → K) →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => j (Pi.single i 1))
    {x : Fin n → K} (hx : x ≠ 0) : j x ≠ 0 := by
  intro h0
  apply hx
  funext i
  rw [j_eq_sum] at h0
  have := Fintype.linearIndependent_iff.mp hli (fun i => σ (x i)) h0 i
  simpa using this

theorem normAt_sq {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι K V) (Xf : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x : V) :
    Formalism.HermitianLatticesTheory.normAt b Xf v x ^ 2 = (Formalism.HermitianLatticesTheory.majAt b Xf v x x).re := by
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm Formalism.HermitianLatticesTheory.majAt
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem hAt_mk {σ : K →+* ℂ} (hσ : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (H : Matrix (Fin n) (Fin n) K)
    (hin : ∀ x y, inner ℂ (j x) (j y) = σ (Formalism.DivisionValues.hform H x y)) :
    (∀ x y, hAt H (InfinitePlace.mk σ) x y = inner ℂ (j x) (j y)) ∨
      (∀ x y, hAt H (InfinitePlace.mk σ) x y = star (inner ℂ (j x) (j y))) := by
  rcases InfinitePlace.embedding_mk_eq σ with he | he
  · left
    intro x y
    rw [hin, hform_eq_sum, hAt, he]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, hσ]
    rfl
  · right
    intro x y
    rw [hin, hform_eq_sum, hAt, he]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, hσ, star_sum, star_mul', ComplexEmbedding.conjugate_coe_eq, Complex.star_def]

theorem posAt_mk {σ : K →+* ℂ} (hσ : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (H E : Matrix (Fin n) (Fin n) K)
    (op : W →ₗ[ℂ] W) (hT : FormsTie σ j H E op) :
    PosAt H (InfinitePlace.mk σ) ∧ ∀ x, hAt H (InfinitePlace.mk σ) x x = ((‖j x‖ ^ 2 : ℝ) : ℂ) := by
  have hd : ∀ x, hAt H (InfinitePlace.mk σ) x x = ((‖j x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rcases hAt_mk hσ j H hT.inner with h | h
    · rw [h, inner_self_eq_norm_sq_to_K]; push_cast; rfl
    · rw [h, inner_self_eq_norm_sq_to_K]; push_cast; simp [Complex.star_def]
  refine ⟨⟨fun x y => ?_, fun x hx => ?_⟩, hd⟩
  · rcases hAt_mk hσ j H hT.inner with h | h
    · rw [h, h]; exact (inner_conj_symm (j y) (j x)).symm
    · rw [h, h, star_star]; exact inner_conj_symm (j x) (j y)
  · rw [hd, Complex.ofReal_re]
    exact pow_pos (norm_pos_iff.mpr (j_ne_zero j hT.li hx)) 2

end GlobalTheory.AmbNormTie


open GlobalTheory.AmbNormTie in
theorem GlobalTheory.AmbNormTie.normAt_frm_mk : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (σ : K →+* ℂ), (∀ a, σ (star a) = starRingEnd ℂ (σ a)) → ∀ {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (H E : Matrix (Fin n) (Fin n) K) (op : W →ₗ[ℂ] W), Formalism.L2.DIV.FormsTie σ j H E op → ∀ x : Fin n → K, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x = ‖j x‖ := by
  intro K _ _ _ _ σ hσ W _ _ n j H E op hT x
  obtain ⟨hP, hd⟩ := posAt_mk hσ j H E op hT
  have hPD := GlobalTheory.T.posDef_map_embedding_of_positiveAtPlace H (InfinitePlace.mk σ) hP
  have hmaj : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x x =
      hAt H (InfinitePlace.mk σ) x x := by
    rw [Formalism.L2.DIV.majAt_eq, GlobalTheory.AmbCrd.frm_of_posDef H _ hPD, (Formalism.L2.DIV.frameOfSpec _ _ hPD).2,
      GlobalTheory.Core.AmbTieStep.hAt_eq_dot]
  have h2 := normAt_sq (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x
  rw [hmaj, hd, Complex.ofReal_re] at h2
  have h0 : 0 ≤ Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x :=
    Real.sqrt_nonneg _
  exact (pow_left_inj₀ h0 (norm_nonneg _) two_ne_zero).mp h2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormAtStandardFrameEqNormComplexFormStatement
open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normAt_standardFrame_eq_norm_complexForm : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (σ : K →+* ℂ), (∀ a, σ (star a) = starRingEnd ℂ (σ a)) → ∀ {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (H E : Matrix (Fin n) (Fin n) K) (op : W →ₗ[ℂ] W), Formalism.L2.DIV.FormsTie σ j H E op → ∀ x : Fin n → K, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x = ‖j x‖ := by
  first | exact @GlobalTheory.AmbNormTie.normAt_frm_mk | exact GlobalTheory.AmbNormTie.normAt_frm_mk | (intros; apply GlobalTheory.AmbNormTie.normAt_frm_mk <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FgSpanTopOfLatticeCompatibleSemilinear
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FgSpanTopOfLatticeCompatibleSemilinear
open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem oLatTie_fg_span_top : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} (σ : K →+* ℂ) {O : Type} [CommRing O] {φO : O →+* ℂ} {W : Type} [AddCommGroup W] [Module ℂ W] (M : Formalism.BasicNotions.Rows.OLat O φO W) (j : (Fin n → K) →ₛₗ[σ] W) (N : Submodule (𝓞 K) (Fin n → K)), (LinearIndependent ℂ fun i => j (Pi.single i 1)) → Formalism.L2.DIV.OLatTie σ M j N → N.FG ∧ Submodule.span K (N : Set (Fin n → K)) = ⊤ := by
  intro K _ _ _ n σ O _ φO W _ _ M j N hli hT
  classical
  obtain ⟨hgen, hmem⟩ := hT
  have hj : ∀ x, j x = ∑ i, σ (x i) • j (Pi.single i 1) := by
    intro x
    conv_lhs => rw [← (Pi.basisFun K (Fin n)).sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smulₛₗ]
    simp
  have hinj : Function.Injective j := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hj] at hx
    have h0 := Fintype.linearIndependent_iff.1 hli _ hx
    funext i
    exact σ.injective (by simpa using h0 i)
  have hgen' : ∀ v, ∃ x, v ∈ M.gen → j x = v := by
    intro v
    by_cases hv : v ∈ M.gen
    · obtain ⟨x, hx⟩ := hgen v hv
      exact ⟨x, fun _ => hx⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose pre hpre using hgen'
  have hN : N = Submodule.span (𝓞 K) (pre '' (M.gen : Set W)) := by
    ext x
    rw [hmem, Submodule.mem_span_image_finset_iff_exists_fun']
    refine exists_congr fun a => ?_
    have : ∑ v ∈ M.gen, σ ((a v : 𝓞 K) : K) • v = j (∑ v ∈ M.gen, a v • pre v) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [← algebraMap_smul K (a v) (pre v), map_smulₛₗ, hpre v hv]
    rw [this]
    exact ⟨fun h => (hinj h).symm, fun h => congrArg j h.symm⟩
  refine ⟨hN ▸ Submodule.fg_span ((M.gen.finite_toSet).image pre), ?_⟩
  rw [hN]
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
  let B := Module.Basis.span hli
  let F0 := B.constr ℂ (fun i => σ (f (Pi.single i 1)))
  obtain ⟨F, hFF⟩ := LinearMap.exists_extend F0
  have hFe : ∀ i, F (j (Pi.single i 1)) = σ (f (Pi.single i 1)) := by
    intro i
    have h1 : (B i : W) = j (Pi.single i 1) := by simp [B, Module.Basis.span_apply hli i]
    rw [← h1]
    have h2 := LinearMap.congr_fun hFF (B i)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h2
    rw [h2]
    simp [F0]
  have hF : ∀ x, F (j x) = σ (f x) := by
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hj, map_sum]
    conv_rhs => rw [← (Pi.basisFun K (Fin n)).sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hFe]
    simp
  have hF0 : F = 0 := by
    apply LinearMap.ext_on M.span_top
    intro v hv
    rw [← hpre v hv, hF]
    have : f (pre v) ∈ (⊥ : Submodule K K) := by
      rw [← hf]
      exact Submodule.mem_map_of_mem
        (Submodule.subset_span (Submodule.subset_span ⟨v, hv, rfl⟩))
    rw [(Submodule.mem_bot K).1 this]
    simp
  apply hf0
  refine LinearMap.ext fun x => σ.injective ?_
  rw [← hF, hF0]
  simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FgSpanTopOfLatticeCompatibleSemilinearStatement
open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fg_span_top_of_lattice_compatible_semilinear : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} (σ : K →+* ℂ) {O : Type} [CommRing O] {φO : O →+* ℂ} {W : Type} [AddCommGroup W] [Module ℂ W] (M : Formalism.BasicNotions.Rows.OLat O φO W) (j : (Fin n → K) →ₛₗ[σ] W) (N : Submodule (𝓞 K) (Fin n → K)), (LinearIndependent ℂ fun i => j (Pi.single i 1)) → Formalism.L2.DIV.OLatTie σ M j N → N.FG ∧ Submodule.span K (N : Set (Fin n → K)) = ⊤ := by
  first | exact @GlobalTheory.oLatTie_fg_span_top | exact GlobalTheory.oLatTie_fg_span_top | (intros; apply GlobalTheory.oLatTie_fg_span_top <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
  NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AmbCrd

open _root_.Formalism.L2.DIV _root_.Formalism.L2.Rows

theorem majAt_frm {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] {n : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (h : PosAt H v) (x y : Fin n → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) (frm H) v x y = hAt H v x y := by
  have hp := GlobalTheory.T.posDef_map_embedding_of_positiveAtPlace H v h
  rw [majAt_eq, frm_of_posDef H v hp, (frameOfSpec _ _ hp).2]
  simp only [hAt, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Pi.star_apply, mul_assoc]

section Level

variable (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ} (A : FamIn D.what₂.LL G Pl0 T m)
  (P : Subgroup G) (ψ : P →* D.what₂.LLˣ)

theorem rNab_rdx {t1 t2 : T} (e : t1 = t2) (h : rDim D A P ψ t2 = rDim D A P ψ t1) :
    rNab D A P ψ t2 = (rNab D A P ψ t1).map ((rdx h).toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := by
  subst e
  ext x
  simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, rdx_refl]
  exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, e⟩ => e ▸ hy⟩

theorem majAt_rdx {t1 t2 : T} (e : t1 = t2) (h : rDim D A P ψ t2 = rDim D A P ψ t1) (v : InfinitePlace D.what₂.LL)
    (hp : PosAt (rH D A P ψ t1) v) (x y : Fin (rDim D A P ψ t1) → D.what₂.LL) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) (frm (rH D A P ψ t2)) v (rdx h x) (rdx h y) =
      hAt (rH D A P ψ t1) v x y := by
  subst e
  have := D.tcLL
  rw [rdx_refl, rdx_refl]
  exact majAt_frm _ v hp x y

end Level

theorem tie_level (D : D7) {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (S : RowSide D EE) {G : Type} [Group G] [Fintype G] {Pl0 T T' : Type} {m : ℕ} (A : FamIn D.what₂.LL G Pl0 T m)
    (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (tp : D.what₂.Tup → T)
    (j : ∀ μ, (Fin (rDim D A P ψ (tp μ)) → D.what₂.LL) →ₛₗ[D.what₂.embLL] S.Amb μ)
    (E : ∀ μ, Matrix (Fin (rDim D A P ψ (tp μ))) (Fin (rDim D A P ψ (tp μ))) D.what₂.LL)
    (op : ∀ μ, S.Amb μ →ₗ[ℂ] S.Amb μ)
    (hF : ∀ μ, FormsTie D.what₂.embLL (j μ) (rH D A P ψ (tp μ)) (E μ) (op μ))
    (hL : ∀ μ, OLatTie D.what₂.embLL (S.Mtilde μ) (j μ) (rNab D A P ψ (tp μ)))
    (f : T' → T) (μ0' : T') (tup : T' → D.what₂.Tup) (hf : ∀ s, f s = tp (tup s))
    (j' : ∀ s, (Fin (rDim D (A.comap f μ0') P ψ s) → D.what₂.LL) →ₛₗ[D.what₂.embLL] S.Amb (tup s))
    (hs : ∀ s, SameOn (j (tup s)) (j' s)) :
    ∃ (Fm : AmbForm D S) (J : AmbIds D (A.comap f μ0') S Fm P ψ tup), AmbTie D (A.comap f μ0') S Fm P ψ tup j' J := by
  have := D.tcLL
  let Fm : AmbForm D S :=
    { MtH := fun μ => toHLat (frm (rH D A P ψ (tp μ))) (rNab D A P ψ (tp μ))
      jAmb := j
      MtH_good := fun μ _ => ⟨frm_det _, GlobalTheory.T.fg_span_top_of_lattice_compatible_semilinear D.what₂.embLL (S.Mtilde μ) (j μ) _ (hF μ).li (hL μ)⟩
      jAmb_basis := fun μ _ => by
        show LinearIndependent ℂ (fun i => j μ (Pi.basisFun D.what₂.LL _ i)) ∧
          Submodule.span ℂ (Set.range (fun i => j μ (Pi.basisFun D.what₂.LL _ i))) = ⊤
        simp only [Pi.basisFun_apply]
        exact ⟨(hF μ).li, (hF μ).span⟩
      jAmb_lat := fun μ _ x => (hL μ).2 x
      jAmb_gen := fun μ _ => (hL μ).1
      jAmb_norm := fun μ _ x => GlobalTheory.T.normAt_standardFrame_eq_norm_complexForm D.what₂.embLL D.starLL_cx (j μ) _ _ _ (hF μ) x }
  let J : AmbIds D (A.comap f μ0') S Fm P ψ tup := ⟨fun s _ => rdx (hs s).1⟩
  refine ⟨Fm, J, ⟨fun s _ x => ?_, fun s _ => ?_, fun s _ v hv x y => ?_⟩⟩
  · refine (hs s).2 _ x fun a a' e => ?_
    show x (Fin.cast (hs s).1 a) = x a'
    congr 1
    exact Fin.ext e
  · exact rNab_rdx D A P ψ (hf s) _
  · exact majAt_rdx D A P ψ (hf s) _ v hv x y


set_option maxHeartbeats 3000000 in
theorem ambEx_of_rx : ∀ 𝒮 : Slots, 𝒮.Rx = RX → AmbEx 𝒮 := by
  rintro ⟨Rx, Nx, Sx, Ox⟩ h
  dsimp only at h
  subst h
  refine StepW.of_all fun K B f T w _ _ _ => ?_
  intro Z l
  have x : RXs l.what₂ := l.rx
  have hsub : R3.tuOf w.I (R3.usedOf w.I T l.Wt) ⊆ R3.tuOf w.I Set.univ := fun τ hτ => by
    obtain ⟨a, -, e⟩ := (R3.mem_tuOf w.I).1 hτ
    exact (R3.mem_tuOf w.I).2 ⟨a, Set.mem_univ _, e⟩
  have hf : ∀ s, TupF.incl hsub s = tAll w.I (l.what₂.r.Y.tup s) := fun s => by
    apply Subtype.ext
    show s.1 = w.I.tup (l.what₂.r.Y.tup s)
    have e : l.what₂.r.Y.tup s = R3.ixOf w.I _ s := l.what₂.r.tup_ix s
    rw [e, R3.tup_ixOf]
  obtain ⟨a, J, hJ⟩ := tie_level (w.st Z).toD7 (RowSide.sharp _) (famAll l.what₂) (R3.lev1 w.I) (R3.chr1 w.I) (tAll w.I)
    x.all.jA _ _ x.all.formsA x.all.latA (TupF.incl hsub) (mu0F _) l.what₂.r.Y.tup hf l.what₂.r.Y.jA x.jA_use
  obtain ⟨a0, J0, hJ0⟩ := tie_level (w.st Z).toD7 l.p0.s (famAll l.what₂) (R3.lev0 w.I) (R3.chr0 w.I) (tAll w.I)
    x.all.jA0 _ _ x.all.formsAtBottomLevel x.all.latA0 (TupF.incl hsub) (mu0F _) l.what₂.r.Y.tup hf l.what₂.r.Y.jA0 x.movedReadingSameMaps_baseReading_agrees
  exact ⟨a, a0, ⟨J, hJ⟩, ⟨J0, hJ0⟩⟩

end GlobalTheory.AmbCrd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaDataTrueRowsColumnsAllCompatible
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SameChrOfChrEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SameChrFin

theorem sameChr_of_chrEq : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (nch : NChoice D) (Tp : Formalism.L2.Host.TupTied D C nch) (X : ThetaX D)
    (T : ThetaTied D X) (H : Formalism.L2.Host.ThetaChrTied D C nch Tp X),
    (∀ c, Formalism.IndefR.Links.ChrEq (T.eChr c) (H.eChr c)) → Formalism.L2.JoinChr.SameChr T H := by
  intro D C nch Tp X T H h
  refine ⟨fun P => ?_, fun c P e he k x hx => (h c).2 P e he k x hx,
    fun θ hθ c τ k x hx => GlobalTheory.CharInfPlace.chrEq_infLoc D (T.eChr c) (H.eChr c) (h c) θ hθ τ k x hx⟩
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  exact ⟨e, he⟩

end GlobalTheory.SameChrFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeakCompatibilityOfRealRowSideAdelicChain
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeakCompatibilityOfRealRowSideAdelicChain
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.RecTie
open scoped InnerProductSpace

namespace GlobalTheory.RowTieRead

open GlobalTheory.HilbertLevels

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R)

theorem mem_cc (b : Bool) (μ : D.what₂.Tup) {k : ℕ} (hk : k < D.R.m) (x : SmT (R.MY k) →ₗ[ℂ] GA D (Yc D k) → ℂ) :
    x ∈ (toChainReal R F tupT hm hTop).CC b μ k ↔ x ∈ R.CC (tupT μ) k := by
  show x ∈ MultT R.θ (R.MY k) (if k < D.R.m then _ else Set.univ) (if k < D.R.m then _ else 0) ↔ _
  rw [if_pos hk, if_pos hk]

theorem ioC_coe (b : Bool) (μ : D.what₂.Tup) (k : ℕ) (hk : k + 1 < D.R.m)
    (z : (toChainReal R F tupT hm hTop).CC b μ (k + 1)) :
    (((toChainReal R F tupT hm hTop).ioC b μ k z).1 :
        SmT (R.MY k) →ₗ[ℂ] GA D (Yc D k) → ℂ) =
      (((R.ioY (tupT μ) k ⟨(z.1 : SmT (R.MY (k + 1)) →ₗ[ℂ] GA D (Yc D (k + 1)) → ℂ),
        (mem_cc R F tupT hm hTop b μ hk _).1 z.2⟩).1 : _)) := by
  simp only [toChainReal, dif_pos hk]
  rfl

theorem ioOK (hC : R.IsChain) (b : Bool) (μ : D.what₂.Tup) : (toChainReal R F tupT hm hTop).IoOK b μ := by
  refine ⟨fun k hk => ⟨fun Fz φ v g => ?_, fun Fz φ v g => ?_⟩, fun _ => ⟨fun Fz φ v g => ?_, fun Fz φ v g => ?_⟩⟩
  · exact (hC.ioY (tupT μ) k hk).integ ⟨Fz.1, (mem_cc R F tupT hm hTop b μ (by omega) _).1 Fz.2⟩ φ v g
  · rw [ioC_coe R F tupT hm hTop b μ k (by omega)]
    exact (hC.ioY (tupT μ) k hk).eq ⟨Fz.1, (mem_cc R F tupT hm hTop b μ (by omega) _).1 Fz.2⟩ φ v g
  · exact (hC.ioX (tupT μ)).integ ⟨Fz.1, (hTop (tupT μ)).symm ▸ Fz.2⟩ φ v g
  · exact (hC.ioX (tupT μ)).eq ⟨Fz.1, (hTop (tupT μ)).symm ▸ Fz.2⟩ φ v g

def nuW (t : T) : ∀ j, Measure (GA D (Yc D j))
  | 0 => ENNReal.ofReal (RealDat.nP F true)⁻¹ • R.ν0
  | j + 1 => R.νY t (j + 1)

def fdW (t : T) : ∀ j, Set (GA D (Yc D j))
  | 0 => R.fd0
  | j + 1 => R.fdY t (j + 1)

def cW : ℕ → ℝ
  | 0 => 1
  | _ + 1 => (RealDat.nP F true)⁻¹

def cXW : ℝ := (RealDat.nP F true)⁻¹ * ∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)

variable (I : RowIds (RowSide.sharp D) (toChainReal R F tupT hm hTop) true)

def eW (μ : D.what₂.Tup) (hμ : Used0 D μ) : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] R.CC (tupT μ) j
  | 0 => LinearMap.codRestrict (R.CC (tupT μ) 0)
      (((toChainReal R F tupT hm hTop).EEc true).subtype ∘ₗ I.jE.toLinearMap ∘ₗ
        (D.what₂.multZero μ).toLinearEquiv.toLinearMap)
      (fun x => (mem_cc R F tupT hm hTop true μ hm _).1 (eec_le_cc R F tupT hm hTop true μ (I.jE _).2))
  | j + 1 => if h : j + 1 ≤ D.R.m - 1 then
      LinearMap.codRestrict (R.CC (tupT μ) (j + 1))
        (((toChainReal R F tupT hm hTop).CCP true μ (j + 1)).subtype ∘ₗ
          (I.jM μ hμ (j + 1) (by omega) h).toLinearMap)
        (fun x => (mem_cc R F tupT hm hTop true μ (by omega) _).1
          (ccp_le R F tupT hm hTop true μ (by omega) (I.jM μ hμ (j + 1) (by omega) h x).2))
    else 0

def eXW (μ : D.what₂.Tup) (hμ : Used0 D μ) :
    D.what₂.Mult μ D.R.m →ₗ[ℂ] LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e) :=
  LinearMap.codRestrict (LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e))
    (((toChainReal R F tupT hm hTop).CCXP true μ).subtype ∘ₗ (I.jX μ hμ).toLinearMap)
    (fun x => (hTop (tupT μ)).symm ▸ ccxp_le R F tupT hm hTop true μ (I.jX μ hμ x).2)

theorem eW_pos (μ : D.what₂.Tup) (hμ : Used0 D μ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m - 1) (x : D.what₂.Mult μ j) :
    ((eW R F tupT hm hTop I μ hμ j x).1 : SmT (R.MY j) →ₗ[ℂ] GA D (Yc D j) → ℂ) = (I.jM μ hμ j h1 h2 x).1 := by
  obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  simp only [eW, dif_pos h2]
  rfl

theorem nuW_pos (t : T) (j : ℕ) (h1 : 1 ≤ j) : nuW R F t j = R.νY t j := by
  obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rfl

theorem fdW_pos (t : T) (j : ℕ) (h1 : 1 ≤ j) : fdW R t j = R.fdY t j := by
  obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rfl

theorem cW_pos (j : ℕ) (h1 : 1 ≤ j) : cW F j = (RealDat.nP F true)⁻¹ := by
  obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rfl

theorem eW_succ_eq (μ : D.what₂.Tup) (hμ : Used0 D μ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m - 1) (x : D.what₂.Mult μ j) :
    eW R F tupT hm hTop I μ hμ j x = ⟨(I.jM μ hμ j h1 h2 x).1, (mem_cc R F tupT hm hTop true μ (by omega) _).1
      (ccp_le R F tupT hm hTop true μ (by omega) (I.jM μ hμ j h1 h2 x).2)⟩ :=
  Subtype.ext (eW_pos R F tupT hm hTop I μ hμ j h1 h2 x)

theorem inner_io_cast (μ : D.what₂.Tup) {k k' : ℕ} (h : k = k') (x : D.what₂.Mult μ k) (y : D.what₂.Mult μ (k + 1)) :
    ⟪x, D.what₂.io μ k y⟫_ℂ = ⟪cast (congrArg (D.what₂.Mult μ) h) x,
      D.what₂.io μ k' (cast (congrArg (fun i => D.what₂.Mult μ (i + 1)) h) y)⟫_ℂ := by
  subst h; rfl

theorem rhs_cast (μ : D.what₂.Tup) (hμ : Used0 D μ) {k k' : ℕ} (h : k = k')
    (a : SmT (R.MY k) →ₗ[ℂ] GA D (Yc D k) → ℂ) (x : D.what₂.Mult μ k) :
    (cW F k : ℂ) * ipT (R.MY k) (nuW R F (tupT μ) k) (fdW R (tupT μ) k) a (eW R F tupT hm hTop I μ hμ k x).1 =
      (cW F k' : ℂ) * ipT (R.MY k') (nuW R F (tupT μ) k') (fdW R (tupT μ) k')
        (cast (congrArg (fun i => SmT (R.MY i) →ₗ[ℂ] GA D (Yc D i) → ℂ) h) a)
        (eW R F tupT hm hTop I μ hμ k' (cast (congrArg (D.what₂.Mult μ) h) x)).1 := by
  subst h; rfl

variable {n : ℕ} {bs : OrthonormalBasis (Fin n) ℂ D.what₂.EE} {ty : Fin n → D.what₂.FT}

theorem levels (hM : R.IsModels) (hRS : RowSideReal (RowSide.sharp D) (toChainReal R F tupT hm hTop) true I bs ty)
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (j : ℕ) (hj : j < D.R.m) :
    IsQuot (Yc D j) (nuW R F (tupT μ) j) (fdW R (tupT μ) j) ∧ 0 < cW F j ∧ ∀ x y : D.what₂.Mult μ j,
      ⟪x, y⟫_ℂ = (cW F j : ℂ) * ipT (R.MY j) (nuW R F (tupT μ) j) (fdW R (tupT μ) j)
        (eW R F tupT hm hTop I μ hμ j y).1 (eW R F tupT hm hTop I μ hμ j x).1 := by
  cases j with
  | zero =>
    refine ⟨scaled (inv_pos.2 (nP_pos F true)) hM.ν0.1.1 hM.ν0.2, one_pos, fun x y => ?_⟩
    rw [← LinearIsometryEquiv.inner_map_map (D.what₂.multZero μ)]
    refine (hRS.ee _ _).trans ?_
    show _ = ((1 : ℝ) : ℂ) * _
    rw [Complex.ofReal_one, one_mul]
    rfl
  | succ j =>
    have h2 : j + 1 ≤ D.R.m - 1 := by omega
    refine ⟨measY R hM (tupT μ) h2 hm, inv_pos.2 (nP_pos F true), fun x y => ?_⟩
    refine (hRS.mult μ hμ (j + 1) (by omega) h2 x y).trans ?_
    rw [eW_pos R F tupT hm hTop I μ hμ (j + 1) (by omega) h2 x, eW_pos R F tupT hm hTop I μ hμ (j + 1) (by omega) h2 y]
    rfl

theorem ipT_eq {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (ν : Measure (GA D V)) (𝓕 : Set (GA D V))
    (a b : SmT M →ₗ[ℂ] GA D V → ℂ) : ipT M ν 𝓕 a b = ipMT M ν 𝓕 b a := rfl

theorem eW_zero_coe (μ : D.what₂.Tup) (hμ : Used0 D μ) (x : D.what₂.Mult μ 0) :
    ((eW R F tupT hm hTop I μ hμ 0 x).1 : SmT (R.MY 0) →ₗ[ℂ] GA D (Yc D 0) → ℂ) = (I.jE (D.what₂.multZero μ x)).1 := rfl

theorem ipE_eq (t : T) (a a' : SmT (R.MY 0) →ₗ[ℂ] GA D (Yc D 0) → ℂ) :
    (toChainReal R F tupT hm hTop).ipE true a a' = ipMT (R.MY 0) (nuW R F t 0) (fdW R t 0) a a' := rfl

theorem weightedInner_eq (μ : D.what₂.Tup) (j : ℕ) (a a' : SmT (R.MY j) →ₗ[ℂ] GA D (Yc D j) → ℂ) :
    (toChainReal R F tupT hm hTop).ipP true μ j a a' =
      (((RealDat.nP F true)⁻¹ : ℝ) : ℂ) * ipMT (R.MY j) (R.νY (tupT μ) j) (R.fdY (tupT μ) j) a a' := rfl

theorem ipXP_eq (μ : D.what₂.Tup) (a a' : SmT R.MX →ₗ[ℂ] GA D D.sp.X' → ℂ) :
    (toChainReal R F tupT hm hTop).ipXP true μ a a' =
      (((RealDat.nP F true)⁻¹ : ℝ) : ℂ) * ((((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) / 1 : ℝ) : ℂ) *
        ipMT R.MX (R.νX (tupT μ)) (R.fdX (tupT μ)) a a') := rfl

theorem top_pos : 0 < cXW R F := by
  have hdef : D.sp.X'.IsDefinite := (factXmDef D.R D.host.F D.sp).1
  exact mul_pos (inv_pos.2 (nP_pos F true))
    (Finset.prod_pos fun τ _ => by exact_mod_cast finrank_model_pos D.sp.X'_sig hdef R.MX τ)

theorem top_inner (hRS : RowSideReal (RowSide.sharp D) (toChainReal R F tupT hm hTop) true I bs ty)
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (x y : D.what₂.Mult μ D.R.m) :
    ⟪x, y⟫_ℂ = (cXW R F : ℂ) * ipT R.MX (R.νX (tupT μ)) (R.fdX (tupT μ))
      (eXW R F tupT hm hTop I μ hμ y).1 (eXW R F tupT hm hTop I μ hμ x).1 := by
  rw [ipT_eq]
  refine (hRS.multX (by omega) μ hμ x y).trans ?_
  have key : ∀ (a b : ℝ) (c : ℂ), (a : ℂ) * (((b / 1 : ℝ)) * c) = ((a * b : ℝ) : ℂ) * c := by
    intro a b c; push_cast; ring
  exact (ipXP_eq R F tupT hm hTop μ _ _).trans ((key _ _ _).trans rfl)

theorem eW_incl (μ : D.what₂.Tup) (hμ : Used0 D μ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m - 1) (y : D.what₂.Mult μ j) :
    eW R F tupT hm hTop I μ hμ j y =
      ⟨((Submodule.inclusion (ccp_le R F tupT hm hTop true μ (by omega)) (I.jM μ hμ j h1 h2 y)).1 :
        SmT (R.MY j) →ₗ[ℂ] GA D (Yc D j) → ℂ), (mem_cc R F tupT hm hTop true μ (by omega) _).1
          (Submodule.inclusion (ccp_le R F tupT hm hTop true μ (by omega)) (I.jM μ hμ j h1 h2 y)).2⟩ := by
  have e1 : (((Submodule.inclusion (ccp_le R F tupT hm hTop true μ (by omega)) (I.jM μ hμ j h1 h2 y) :
      (toChainReal R F tupT hm hTop).CC true μ j)) : (toChainReal R F tupT hm hTop).Amb j) =
      ((I.jM μ hμ j h1 h2 y : (toChainReal R F tupT hm hTop).CCP true μ j) : (toChainReal R F tupT hm hTop).Amb j) :=
    Submodule.coe_inclusion _ _
  exact Subtype.ext ((eW_pos R F tupT hm hTop I μ hμ j h1 h2 y).trans e1.symm)

theorem eXW_val (μ : D.what₂.Tup) (hμ : Used0 D μ) (y : D.what₂.Mult μ D.R.m) :
    ((eXW R F tupT hm hTop I μ hμ y).1 : SmT R.MX →ₗ[ℂ] GA D D.sp.X' → ℂ) = (I.jX μ hμ y).1 := by
  simp only [eXW, LinearMap.codRestrict_apply]
  rfl

theorem eXW_incl (μ : D.what₂.Tup) (hμ : Used0 D μ) (y : D.what₂.Mult μ D.R.m) :
    eXW R F tupT hm hTop I μ hμ y =
      ⟨((Submodule.inclusion (ccxp_le R F tupT hm hTop true μ) (I.jX μ hμ y)).1 : SmT R.MX →ₗ[ℂ] GA D D.sp.X' → ℂ),
        (hTop (tupT μ)).symm ▸ (Submodule.inclusion (ccxp_le R F tupT hm hTop true μ) (I.jX μ hμ y)).2⟩ := by
  have e1 : (((Submodule.inclusion (ccxp_le R F tupT hm hTop true μ) (I.jX μ hμ y) :
      (toChainReal R F tupT hm hTop).CCX true μ)) : (toChainReal R F tupT hm hTop).AmbX) =
      ((I.jX μ hμ y : (toChainReal R F tupT hm hTop).CCXP true μ) : (toChainReal R F tupT hm hTop).AmbX) :=
    Submodule.coe_inclusion _ _
  exact Subtype.ext ((eXW_val R F tupT hm hTop I μ hμ y).trans e1.symm)

theorem ioX_coe (b : Bool) (μ : D.what₂.Tup) (z : (toChainReal R F tupT hm hTop).CCX b μ) :
    (((toChainReal R F tupT hm hTop).ioX b μ z).1 : SmT (R.MY (D.R.m - 1)) →ₗ[ℂ] GA D (Yc D (D.R.m - 1)) → ℂ) =
      ((R.ioX (tupT μ) ⟨(z.1 : SmT R.MX →ₗ[ℂ] GA D D.sp.X' → ℂ), (hTop (tupT μ)).symm ▸ z.2⟩).1 : _) := by
  simp only [toChainReal]
  rfl

theorem L0 (μ : D.what₂.Tup) (hj : 0 + 1 < D.R.m) (a : SmT (R.MY 0) →ₗ[ℂ] GA D (Yc D 0) → ℂ)
    (z : (toChainReal R F tupT hm hTop).CC true μ 1) :
    (toChainReal R F tupT hm hTop).ipE true a ((toChainReal R F tupT hm hTop).ioC true μ 0 z).1 =
      ipMT (R.MY 0) (nuW R F (tupT μ) 0) (fdW R (tupT μ) 0) a
        (R.ioY (tupT μ) 0 ⟨(z.1 : SmT (R.MY 1) →ₗ[ℂ] GA D (Yc D 1) → ℂ), (mem_cc R F tupT hm hTop true μ hj _).1 z.2⟩).1 :=
  (congrArg ((toChainReal R F tupT hm hTop).ipE true a) (ioC_coe R F tupT hm hTop true μ 0 hj z)).trans
    (ipE_eq R F tupT hm hTop (tupT μ) _ _)

theorem inner_io_zero (hC : R.IsChain)
    (hRS : RowSideReal (RowSide.sharp D) (toChainReal R F tupT hm hTop) true I bs ty)
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (hj : 0 + 1 < D.R.m) (x : D.what₂.Mult μ 0) (y : D.what₂.Mult μ 1) :
    ⟪x, D.what₂.io μ 0 y⟫_ℂ = (cW F 0 : ℂ) * ipT (R.MY 0) (nuW R F (tupT μ) 0) (fdW R (tupT μ) 0)
      (R.ioY (tupT μ) 0 (eW R F tupT hm hTop I μ hμ 1 y)).1 (eW R F tupT hm hTop I μ hμ 0 x).1 := by
  have h1 : ((cW F 0 : ℝ) : ℂ) = 1 := by simp [cW]
  rw [eW_incl R F tupT hm hTop I μ hμ 1 le_rfl (by omega) y, ipT_eq, h1, one_mul,
    ← LinearIsometryEquiv.inner_map_map (D.what₂.multZero μ)]
  exact (hRS.io0 (by omega) μ hμ (ioOK R F tupT hm hTop hC true μ) (D.what₂.multZero μ x) y).trans
    ((L0 R F tupT hm hTop μ hj _ _).trans (congrArg (fun a => ipMT (R.MY 0) (nuW R F (tupT μ) 0) (fdW R (tupT μ) 0) a _)
      (eW_zero_coe R F tupT hm hTop I μ hμ x).symm))

theorem inner_io_succ (hC : R.IsChain)
    (hRS : RowSideReal (RowSide.sharp D) (toChainReal R F tupT hm hTop) true I bs ty)
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (j : ℕ) (hj : j + 1 + 1 < D.R.m) (x : D.what₂.Mult μ (j + 1))
    (y : D.what₂.Mult μ (j + 1 + 1)) :
    ⟪x, D.what₂.io μ (j + 1) y⟫_ℂ = (cW F (j + 1) : ℂ) * ipT (R.MY (j + 1)) (nuW R F (tupT μ) (j + 1)) (fdW R (tupT μ) (j + 1))
      (R.ioY (tupT μ) (j + 1) (eW R F tupT hm hTop I μ hμ (j + 1 + 1) y)).1 (eW R F tupT hm hTop I μ hμ (j + 1) x).1 := by
  rw [nuW_pos R F (tupT μ) (j + 1) (by omega), fdW_pos R (tupT μ) (j + 1) (by omega), cW_pos F (j + 1) (by omega),
    ipT_eq, eW_incl R F tupT hm hTop I μ hμ (j + 1 + 1) (by omega) (by omega) y,
    eW_succ_eq R F tupT hm hTop I μ hμ (j + 1) (by omega) (by omega) x]
  exact (hRS.io μ hμ (ioOK R F tupT hm hTop hC true μ) (j + 1) (by omega) (by omega) x y).trans
    ((congrArg ((toChainReal R F tupT hm hTop).ipP true μ (j + 1) (I.jM μ hμ (j + 1) (by omega) (by omega) x).1)
      (ioC_coe R F tupT hm hTop true μ (j + 1) hj _)).trans (weightedInner_eq R F tupT hm hTop μ (j + 1) _ _))

theorem io_step (hC : R.IsChain)
    (hRS : RowSideReal (RowSide.sharp D) (toChainReal R F tupT hm hTop) true I bs ty)
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (j : ℕ) (hj : j + 1 < D.R.m) (x : D.what₂.Mult μ j) (y : D.what₂.Mult μ (j + 1)) :
    ⟪x, D.what₂.io μ j y⟫_ℂ = (cW F j : ℂ) * ipT (R.MY j) (nuW R F (tupT μ) j) (fdW R (tupT μ) j)
      (R.ioY (tupT μ) j (eW R F tupT hm hTop I μ hμ (j + 1) y)).1 (eW R F tupT hm hTop I μ hμ j x).1 := by
  cases j with
  | zero => exact inner_io_zero R F tupT hm hTop I hC hRS μ hμ hj x y
  | succ j => exact inner_io_succ R F tupT hm hTop I hC hRS μ hμ j hj x y

theorem rhs_gen (t : T) (k : ℕ) (hk : 1 ≤ k) (a b : SmT (R.MY k) →ₗ[ℂ] GA D (Yc D k) → ℂ) :
    (cW F k : ℂ) * ipT (R.MY k) (nuW R F t k) (fdW R t k) a b =
      (((RealDat.nP F true)⁻¹ : ℝ) : ℂ) * ipMT (R.MY k) (R.νY t k) (R.fdY t k) b a := by
  obtain ⟨j, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  rfl

theorem rhs_zero (t : T) (a b : SmT (R.MY 0) →ₗ[ℂ] GA D (Yc D 0) → ℂ) :
    (cW F 0 : ℂ) * ipT (R.MY 0) (nuW R F t 0) (fdW R t 0) a b = ipMT (R.MY 0) (nuW R F t 0) (fdW R t 0) b a := by
  have h : ((cW F 0 : ℝ) : ℂ) = 1 := by simp [cW]
  rw [h, one_mul]
  rfl

theorem rowChain_intertwiner_top_second (hC : R.IsChain)
    (hRS : RowSideReal (RowSide.sharp D) (toChainReal R F tupT hm hTop) true I bs ty)
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (h2 : 1 < D.R.m) (x : D.what₂.Mult μ (D.R.m - 1))
    (y' : D.what₂.Mult μ D.R.m) :
    ⟪x, D.what₂.io μ (D.R.m - 1) (cast (congrArg (D.what₂.Mult μ) (by omega : D.R.m = D.R.m - 1 + 1)) y')⟫_ℂ =
      (cW F (D.R.m - 1) : ℂ) * ipT (R.MY (D.R.m - 1))
      (nuW R F (tupT μ) (D.R.m - 1)) (fdW R (tupT μ) (D.R.m - 1))
      (R.ioX (tupT μ) (eXW R F tupT hm hTop I μ hμ y')).1 (eW R F tupT hm hTop I μ hμ (D.R.m - 1) x).1 := by
  have h1m : 1 ≤ D.R.m - 1 := by omega
  refine (hRS.ioTop (by omega) μ hμ (ioOK R F tupT hm hTop hC true μ) x y').trans
    ((congrArg ((toChainReal R F tupT hm hTop).ipP true μ (D.R.m - 1) (I.jM μ hμ (D.R.m - 1) h1m le_rfl x).1)
      (ioX_coe R F tupT hm hTop true μ _)).trans ((weightedInner_eq R F tupT hm hTop μ (D.R.m - 1) _ _).trans
        (Eq.trans ?_ (rhs_gen R F (tupT μ) (D.R.m - 1) h1m _ _).symm)))
  exact congrArg₂ (fun a b => (((RealDat.nP F true)⁻¹ : ℝ) : ℂ) *
      ipMT (R.MY (D.R.m - 1)) (R.νY (tupT μ) (D.R.m - 1)) (R.fdY (tupT μ) (D.R.m - 1)) a b)
    (congrArg Subtype.val (eW_succ_eq R F tupT hm hTop I μ hμ (D.R.m - 1) h1m le_rfl x)).symm
    (congrArg (fun z => (R.ioX (tupT μ) z).1) (eXW_incl R F tupT hm hTop I μ hμ y')).symm

theorem rowChain_intertwiner_top_first (hC : R.IsChain)
    (hRS : RowSideReal (RowSide.sharp D) (toChainReal R F tupT hm hTop) true I bs ty)
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (h1' : D.R.m = 1) (x : D.what₂.Mult μ (D.R.m - 1))
    (y : D.what₂.Mult μ (D.R.m - 1 + 1)) (y' : D.what₂.Mult μ D.R.m) (hy : HEq y y') :
    ⟪x, D.what₂.io μ (D.R.m - 1) y⟫_ℂ = (cW F (D.R.m - 1) : ℂ) * ipT (R.MY (D.R.m - 1))
      (nuW R F (tupT μ) (D.R.m - 1)) (fdW R (tupT μ) (D.R.m - 1))
      (R.ioX (tupT μ) (eXW R F tupT hm hTop I μ hμ y')).1 (eW R F tupT hm hTop I μ hμ (D.R.m - 1) x).1 := by
  have hk : D.R.m - 1 = 0 := by omega
  have hIo := ioOK R F tupT hm hTop hC true μ
  have key : ∀ (a : D.what₂.Mult μ 1) (z : D.what₂.Mult μ D.R.m), HEq a z → ∀ w : D.what₂.Mult μ 0,
      ⟪D.what₂.multZero μ w, D.what₂.multZero μ (D.what₂.io μ 0 a)⟫_ℂ =
        (toChainReal R F tupT hm hTop).ipE true (I.jE (D.what₂.multZero μ w)).1
          (cast (congrArg (toChainReal R F tupT hm hTop).Amb (show D.R.m - 1 = 0 by omega))
            ((toChainReal R F tupT hm hTop).ioX true μ
              (Submodule.inclusion (hRS.lvlX μ hμ) (I.jX μ hμ z))).1) := by
    intro a z haz w
    obtain rfl : z = cast (congrArg ((RowSide.sharp D).Mult μ) h1'.symm) a := (cast_eq_iff_heq.2 haz).symm
    exact hRS.io0X h1' μ hμ hIo _ a
  refine (inner_io_cast μ hk x y).trans ((LinearIsometryEquiv.inner_map_map (D.what₂.multZero μ) _ _).symm.trans
    ((key _ y' ((cast_heq _ _).trans hy) _).trans ((ipE_eq R F tupT hm hTop (tupT μ) _ _).trans
      ((Eq.trans ?_ (rhs_zero R F (tupT μ) _ _).symm).trans (rhs_cast R F tupT hm hTop I μ hμ hk _ x).symm))))
  exact congrArg₂ (ipMT (R.MY 0) (nuW R F (tupT μ) 0) (fdW R (tupT μ) 0))
    (eW_zero_coe R F tupT hm hTop I μ hμ _).symm
    (congrArg (fun w => cast (congrArg (fun i => SmT (R.MY i) →ₗ[ℂ] GA D (Yc D i) → ℂ) hk) w)
      ((ioX_coe R F tupT hm hTop true μ _).trans
        (congrArg (fun z => (R.ioX (tupT μ) z).1) (eXW_incl R F tupT hm hTop I μ hμ y')).symm))

theorem io_top (hC : R.IsChain)
    (hRS : RowSideReal (RowSide.sharp D) (toChainReal R F tupT hm hTop) true I bs ty)
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (x : D.what₂.Mult μ (D.R.m - 1)) (y : D.what₂.Mult μ (D.R.m - 1 + 1))
    (y' : D.what₂.Mult μ D.R.m) (hy : HEq y y') :
    ⟪x, D.what₂.io μ (D.R.m - 1) y⟫_ℂ = (cW F (D.R.m - 1) : ℂ) * ipT (R.MY (D.R.m - 1))
      (nuW R F (tupT μ) (D.R.m - 1)) (fdW R (tupT μ) (D.R.m - 1))
      (R.ioX (tupT μ) (eXW R F tupT hm hTop I μ hμ y')).1 (eW R F tupT hm hTop I μ hμ (D.R.m - 1) x).1 := by
  by_cases h2 : 1 < D.R.m
  · have hyy : cast (congrArg (D.what₂.Mult μ) (by omega : D.R.m = D.R.m - 1 + 1)) y' = y :=
      cast_eq_iff_heq.2 hy.symm
    exact (congrArg (fun z => ⟪x, D.what₂.io μ (D.R.m - 1) z⟫_ℂ) hyy.symm).trans
      (rowChain_intertwiner_top_second R F tupT hm hTop I hC hRS μ hμ h2 x y')
  · exact rowChain_intertwiner_top_first R F tupT hm hTop I hC hRS μ hμ (by omega) x y y' hy

theorem weak_tie : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R) (I : RowIds (RowSide.sharp D) (toChainReal R F tupT hm hTop) true) (n : ℕ) (bs : OrthonormalBasis (Fin n) ℂ D.what₂.EE) (ty : Fin n → D.what₂.FT), R.IsModels → R.IsChain → RowSideReal (RowSide.sharp D) (toChainReal R F tupT hm hTop) true I bs ty → ∀ μ, Used0 D μ → (∃ (e : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] R.CC (tupT μ) j) (eX : D.what₂.Mult μ D.R.m →ₗ[ℂ] LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e)) (ν : ∀ j, Measure (GA D (Yc D j))) (𝓕 : ∀ j, Set (GA D (Yc D j))) (c : ℕ → ℝ) (cX : ℝ), (∀ j, j < D.R.m → IsQuot (Yc D j) (ν j) (𝓕 j) ∧ 0 < c j ∧ ∀ x y, ⟪x, y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (e j y).1 (e j x).1) ∧ (∃ J χ, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e) ≤ MultT R.θ R.MX J χ) ∧ 0 < cX ∧ (∀ x y, ⟪x, y⟫_ℂ = (cX : ℂ) * ipT R.MX (R.νX (tupT μ)) (R.fdX (tupT μ)) (eX y).1 (eX x).1) ∧ (∀ j, j + 1 < D.R.m → ∀ x y, ⟪x, D.what₂.io μ j y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (R.ioY (tupT μ) j (e (j + 1) y)).1 (e j x).1) ∧ ∀ x (y : D.what₂.Mult μ (D.R.m - 1 + 1)) (y' : D.what₂.Mult μ D.R.m), HEq y y' → ⟪x, D.what₂.io μ (D.R.m - 1) y⟫_ℂ = (c (D.R.m - 1) : ℂ) * ipT (R.MY (D.R.m - 1)) (ν (D.R.m - 1)) (𝓕 (D.R.m - 1)) (R.ioX (tupT μ) (eX y')).1 (e (D.R.m - 1) x).1) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F tupT hm hTop I n bs ty hM hC hRS μ hμ
  exact ⟨eW R F tupT hm hTop I μ hμ, eXW R F tupT hm hTop I μ hμ, nuW R F (tupT μ), fdW R (tupT μ), cW F, cXW R F,
    fun j hj => levels R F tupT hm hTop I hM hRS μ hμ j hj, ⟨_, _, (hTop (tupT μ)).le⟩, top_pos R F,
    top_inner R F tupT hm hTop I hRS μ hμ, fun j hj x y => io_step R F tupT hm hTop I hC hRS μ hμ j hj x y,
    fun x y y' hy => io_top R F tupT hm hTop I hC hRS μ hμ x y y' hy⟩

end GlobalTheory.RowTieRead

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeakCompatibilityOfRealRowSideAdelicChainStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.RecTie
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weakCompatibility_of_realRowSide_adelicChain : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R) (I : RowIds (RowSide.sharp D) (toChainReal R F tupT hm hTop) true) (n : ℕ) (bs : OrthonormalBasis (Fin n) ℂ D.what₂.EE) (ty : Fin n → D.what₂.FT), R.IsModels → R.IsChain → RowSideReal (RowSide.sharp D) (toChainReal R F tupT hm hTop) true I bs ty → ∀ μ, Used0 D μ → (∃ (e : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] R.CC (tupT μ) j) (eX : D.what₂.Mult μ D.R.m →ₗ[ℂ] LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e)) (ν : ∀ j, Measure (GA D (Yc D j))) (𝓕 : ∀ j, Set (GA D (Yc D j))) (c : ℕ → ℝ) (cX : ℝ), (∀ j, j < D.R.m → IsQuot (Yc D j) (ν j) (𝓕 j) ∧ 0 < c j ∧ ∀ x y, ⟪x, y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (e j y).1 (e j x).1) ∧ (∃ J χ, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e) ≤ MultT R.θ R.MX J χ) ∧ 0 < cX ∧ (∀ x y, ⟪x, y⟫_ℂ = (cX : ℂ) * ipT R.MX (R.νX (tupT μ)) (R.fdX (tupT μ)) (eX y).1 (eX x).1) ∧ (∀ j, j + 1 < D.R.m → ∀ x y, ⟪x, D.what₂.io μ j y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (R.ioY (tupT μ) j (e (j + 1) y)).1 (e j x).1) ∧ ∀ x (y : D.what₂.Mult μ (D.R.m - 1 + 1)) (y' : D.what₂.Mult μ D.R.m), HEq y y' → ⟪x, D.what₂.io μ (D.R.m - 1) y⟫_ℂ = (c (D.R.m - 1) : ℂ) * ipT (R.MY (D.R.m - 1)) (ν (D.R.m - 1)) (𝓕 (D.R.m - 1)) (R.ioX (tupT μ) (eX y')).1 (e (D.R.m - 1) x).1) := by
  first | exact @GlobalTheory.RowTieRead.weak_tie | exact GlobalTheory.RowTieRead.weak_tie | (intros; apply GlobalTheory.RowTieRead.weak_tie <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilTiedEqOfEqTied
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Th

theorem weilTiedEq_of_eqTied : ∀ (D : D7) (X : ThetaX D) (T : ThetaTied D X) (W : WeilTied D X T), WeilThetaCompatibility W → WeilCompatibleEquivariance W :=
  fun _ _ _ _ h => ⟨h.range, h.Heisenberg₂, h.aut, h.cont, h.unit, h.split, ⟨h.twW, h.twV⟩, h.th⟩

end GlobalTheory.Mem.Th
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaDataTrueRowsColumnsAllCompatible
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ThetaRecordTrue

theorem recFun_of_rows (hR : GlobalTheory.Published.CuspRapidDecay) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (what₂ : RowsT K w Z Wt p0) {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch)
    (hio : ∀ μ, ¬ Formalism.IndefR.RecTie.Used0 (w.D Z) μ → ∀ j, j < (w.D Z).R.m → (w.D Z).what₂.io μ j = 0) :
    ∀ θ : InfF (w.D Z), IsInfFam θ → ∀ ψ, IsStdChar (w.D Z) ψ (-1) → ∀ Wf : WeilFun (w.D Z) ψ,
      ∃ Rc : RecFun (w.D Z) θ ψ, Rc.ChrIs (TC.cf w.I w.l Z) n.tp.xi ∧ Rc.IoTie Wf ∧ ∀ μ ∈ {μ | Formalism.IndefR.RecTie.Used0 (w.D Z) μ}, ∀ j, j ≤ (w.D Z).R.m → ∀ x y : (w.D Z).what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt ((w.D Z).sp.Y j) (Rc.mY μ j * Rc.petC ((w.D Z).sp.Y j)) (fun h => star ((Rc.row μ j x).1 h) * (Rc.row μ j y).1 h) (inner ℂ x y) := by
  intro θ hθ ψ hψ Wf
  letI : Algebra what₂.r.z.core.Q.c.F (w.D Z).what₂.LL := what₂.r.z.alg
  have h3 := Formalism.IndefR.Links.RealDat3.characterisation_of_weak what₂.r.z.pins.char what₂.exAt
  have hC : what₂.r.z.R.toRealDat.C = TC.cf w.I w.l Z := what₂.r.z.lev.C
  obtain ⟨Rc, h1, h2, h4⟩ := GlobalTheory.T.functionLevelData_of_equal_tuples_zero_intertwiners hR (w.D Z) _ _ _ _ _ what₂.r.z.R.toRealDat h3.lev h3.models h3.chain n.tp.xi
    {μ | Formalism.IndefR.RecTie.Used0 (w.D Z) μ} what₂.r.Y.tupT n.tp.xi_fin n.tp.xi_triv
    (fun μ hμ => ⟨by
        rw [what₂.r.z.lev.xiH, ← what₂.r.tup_ix, what₂.r.Y.tupTie μ hμ, ← n.xi]; rfl,
      GlobalTheory.T.weakCompatibility_of_realRowSide_adelicChain (w.D Z) _ _ _ _ _ what₂.r.z.R.toRealDat what₂.r.z.F.lv2 what₂.r.Y.tupT what₂.r.Y.hm what₂.r.Y.hTop what₂.r.Y.Ish _
        (w.D Z).what₂.onb (w.D Z).what₂.ft h3.models h3.chain what₂.r.Y.tied.sharp μ hμ⟩)
    (fun μ hμ => hio μ hμ) θ hθ ψ hψ Wf
  rw [hC] at h1
  exact ⟨Rc, h1, h2, h4⟩


set_option maxHeartbeats 1000000 in
theorem thEx_main : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ) → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v, U (σ g v) = σ' g (U v)) → (∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∃ R : DSRep T, HasParam R lam) → ∀ 𝒮 : Slots, (∀ K B f T (w : ColW B f T) (Z : w.Lt) Wt p0 (t : RowsT K w Z Wt p0), 𝒮.Rx K B f T w Z Wt p0 t → ∀ μ, ¬ Formalism.IndefR.RecTie.Used0 (w.D Z) μ → ∀ j, j < (w.D Z).R.m → (w.D Z).what₂.io μ j = 0) → ThEx 𝒮 := by
  intro hW hR _ _ hDS hDSu hDSR 𝒮 hio
  refine StepW.of_all fun K B f T w _ _ _ Z l => ?_
  obtain ⟨X, hio', -, A, a, heq, hchr⟩ := GlobalTheory.Mem.Th.exists_allTied_eqTied_on hW hR hDS hDSu hDSR (w.D Z) (TC.cf w.I w.l Z) l.n.tp.xi
    {μ | Formalism.IndefR.RecTie.Used0 (w.D Z) μ} l.real (recFun_of_rows hR l.what₂ l.n (hio K B f T w Z l.Wt l.p0 l.what₂ l.rx))
  obtain ⟨H, hH⟩ := hchr l.nch l.n.tp rfl
  exact ⟨X, ⟨⟨A, a, GlobalTheory.Mem.Th.weilTiedEq_of_eqTied _ _ _ _ heq, H,
    GlobalTheory.SameChrFin.sameChr_of_chrEq _ _ _ _ _ _ _ hH, a.W.ψ_std, hio'⟩⟩⟩

end GlobalTheory.ThetaRecordTrue

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaDataTrueRowsColumnsAllCompatibleStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaData_trueRowsColumns_allCompatible : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ) → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v, U (σ g v) = σ' g (U v)) → (∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∃ R : DSRep T, HasParam R lam) → ∀ 𝒮 : Slots, (∀ K B f T (w : ColW B f T) (Z : w.Lt) Wt p0 (t : RowsT K w Z Wt p0), 𝒮.Rx K B f T w Z Wt p0 t → ∀ μ, ¬ Formalism.IndefR.RecTie.Used0 (w.D Z) μ → ∀ j, j < (w.D Z).R.m → (w.D Z).what₂.io μ j = 0) → ThEx 𝒮 := by
  first | exact @GlobalTheory.ThetaRecordTrue.thEx_main | exact GlobalTheory.ThetaRecordTrue.thEx_main | (intros; apply GlobalTheory.ThetaRecordTrue.thEx_main <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw GlobalTheory.ShFam
open Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.Mem.Th

namespace GlobalTheory.Mem.Top.Closing

theorem divEx_geoCl (h1 : GlobalTheory.NT.RayField) (h2 : GlobalTheory.Published.PrincipalIdealSt) (h3 : GlobalTheory.Published.CMCurveGoodOutsidePrimeSt)
    (R : RPosition) (N : NCondition) (S : SPosition) : DivEx ⟨R, N, S, OX (geoCl anyGeometry)⟩ := by
  have h := GlobalTheory.Mem.Top.DivRec.divEx_of_ox h1 h2 h3 ⟨R, N, S, OX anyGeometry⟩ rfl
  refine GlobalTheory.Mem.Top.Bl.StepW.trans h (GlobalTheory.Mem.Top.Bl.StepW.of_all ?_)
  intro K B f T w _ _ hw Z l
  obtain ⟨Y, hY1, hY2, hY3, hY4⟩ := hw Z
    { g := l.g, coh := l.coh, Wt := l.Wt, p0 := l.p0, what₂ := l.what₂, rx := l.rx, nch := l.nch, n := l.n, xd := l.xd,
      chiT := l.chiT, nx := l.nx, col := l.col, real := l.real, dsig_eq := l.dsig_eq, del := l.del, sx := l.sx }
  refine ⟨Y, hY1, hY2, hY3, fun O t e1 e2 e3 => ?_⟩
  obtain ⟨o⟩ := hY4 O t e1 e2 e3
  exact ⟨⟨geoCl_of o.geo, o.lam⟩⟩

theorem io_zero (𝒮 : Slots) (h : 𝒮.Rx = RX) : ∀ K B f T (w : ColW B f T) (Z : w.Lt) Wt p0 (t : RowsT K w Z Wt p0),
    𝒮.Rx K B f T w Z Wt p0 t → ∀ μ, ¬ Formalism.IndefR.RecTie.Used0 (w.D Z) μ → ∀ j, j < (w.D Z).R.m → (w.D Z).what₂.io μ j = 0 := by
  intro K B f T w Z Wt p0 t r μ hμ j _
  rw [h] at r
  exact (RXs.io r μ j hμ).1

end GlobalTheory.Mem.Top.Closing
