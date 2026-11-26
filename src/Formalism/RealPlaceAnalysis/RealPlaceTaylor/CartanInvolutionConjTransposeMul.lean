module

public import Formalism.RealPlaceAnalysis.StatementKT
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MonicNormLtOne

@[expose] public section

section -- merged from Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.REAL

section F3ALinfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
  Matrix.linftyOpNormedSpace

lemma hasDerivAt_matrix_exp_smul_at_zero {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) X 0 := by
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℂ) X ((0 : ℝ) : ℂ))
  have h2 := h.scomp (x := (0:ℝ)) Complex.ofRealCLM.hasDerivAt
  exact h2.congr_deriv (by simp)

end F3ALinfty

lemma tendsto_slope_exp_smul {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (slope (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) 0) (𝓝[≠] 0) (𝓝 X) := by
  let _ := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℂ) (n := Fin n) (α := ℂ)
  let _ := Matrix.linftyOpNormedSpace (R := ℝ) (m := Fin n) (n := Fin n) (α := ℂ)
  exact (hasDerivAt_matrix_exp_smul_at_zero X).tendsto_slope

lemma tendsto_slope_mul_exp_smul {n : ℕ} (g X : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (slope (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) 0) (𝓝[≠] 0) (𝓝 (g * X)) := by
  have h := (tendsto_slope_exp_smul X).const_mul g
  refine h.congr (fun t => ?_)
  simp only [slope_def_module, Matrix.mul_sub, Matrix.mul_smul]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma hasDerivAt_mul_exp_smul_zero {n : ℕ} (g X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * X) 0 :=
  hasDerivAt_iff_tendsto_slope.mpr (tendsto_slope_mul_exp_smul g X)

lemma indefinite_unitary_mul_mem {n : ℕ} (ε : Fin n → Bool) {a b : Matrix (Fin n) (Fin n) ℂ}
    (ha : inUJ ε a) (hb : inUJ ε b) : inUJ ε (a * b) := by
  unfold inUJ at *
  calc (a * b)ᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Jm ε := by rw [ha, hb]

lemma lie_algebra_add_mem {n : ℕ} (ε : Fin n → Bool) {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) (hY : inG ε Y) : inG ε (X + Y) := by
  unfold inG at *
  rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]

lemma lie_algebra_real_smul_mem {n : ℕ} (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) (r : ℝ) : inG ε ((r : ℂ) • X) := by
  unfold inG at *
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
    Matrix.mul_smul, ← smul_add, hX, smul_zero]

theorem right_derivative_extends : RdExt := by
  intro n ε f F U g X hU hg hgJ hF hfF hX
  unfold Rd
  have hγ := hasDerivAt_mul_exp_smul_zero g X
  have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by
    simp [NormedSpace.exp_zero]
  have hFd : DifferentiableAt ℝ F g :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
  have hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X)))
      (fderiv ℝ F g (g * X)) 0 :=
    hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  have hev : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) := by
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hg)
    filter_upwards [hmem] with t ht
    exact hfF _ ht (indefinite_unitary_mul_mem ε hgJ (exp_indefinite_unitary_holds n ε X hX t))
  rw [hev.deriv_eq]
  exact hcomp.deriv

theorem right_derivative_left_invariant : RdLeft := by
  intro n f X h g
  simp only [Rd, Matrix.mul_assoc]

theorem rdLin_of (h : RdExt) : RdLin := by
  intro n ε f f' X Y r c g hf hf' hX hY hg
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := hf' g hg
  have hFd : DifferentiableAt ℝ F g :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
  have hFd' : DifferentiableAt ℝ F' g :=
    (hF'.differentiableOn (by simp)).differentiableAt (hU'.mem_nhds hgU')
  have eX := h n ε f F U g X hU hgU hg hF hfF hX
  refine ⟨?_, ?_, ?_⟩
  · rw [h n ε f F U g (X + Y) hU hgU hg hF hfF (lie_algebra_add_mem ε hX hY), eX,
      h n ε f F U g Y hU hgU hg hF hfF hY, Matrix.mul_add, map_add]
  · rw [h n ε f F U g ((r : ℂ) • X) hU hgU hg hF hfF (lie_algebra_real_smul_mem ε hX r), eX,
      Matrix.mul_smul, Complex.coe_smul, map_smul, Complex.real_smul]
  · have hsm : ContDiffOn ℝ ∞ (fun x => F x + c * F' x) (U ∩ U') :=
      (hF.mono Set.inter_subset_left).add (contDiffOn_const.mul (hF'.mono Set.inter_subset_right))
    rw [h n ε (fun x => f x + c * f' x) (fun x => F x + c * F' x) (U ∩ U') g X (hU.inter hU')
      ⟨hgU, hgU'⟩ hg hsm (fun x hx hxJ => by rw [hfF x hx.1 hxJ, hfF' x hx.2 hxJ]) hX,
      eX, h n ε f' F' U' g X hU' hgU' hg hF' hfF' hX]
    have hD : HasFDerivAt (fun x => F x + c * F' x) (fderiv ℝ F g + c • fderiv ℝ F' g) g :=
      hFd.hasFDerivAt.add (hFd'.hasFDerivAt.const_mul c)
    rw [hD.fderiv]
    simp

theorem right_derivative_linear : RdLin := rdLin_of right_derivative_extends

lemma signature_mul_signature_mul {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) :
    Jm ε * (Jm ε * A) = A := by
  rw [← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]

lemma cartan_involution_conjTranspose_mul {n : ℕ} (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    (Jm ε * Zᴴ * Jm ε)ᴴ * Jm ε = Jm ε * Z := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Jm_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, Matrix.mul_assoc, Jm_mul_self,
    Matrix.mul_one]

lemma signature_mul_cartan_involution {n : ℕ} (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    Jm ε * (Jm ε * Zᴴ * Jm ε) = Zᴴ * Jm ε := by
  rw [Matrix.mul_assoc, signature_mul_signature_mul]

lemma star_one_half : star (1 / 2 : ℂ) = 1 / 2 := by simp

lemma star_one_div_two_I : star (1 / (2 * Complex.I) : ℂ) = - (1 / (2 * Complex.I)) := by
  simp [Complex.conj_I]

theorem complex_parts_mem_lie_algebra_holds : CpartMem := by
  intro n ε Z
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold inG cpart1
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.smul_mul, Matrix.sub_mul,
      cartan_involution_conjTranspose_mul, Matrix.mul_smul, Matrix.mul_sub, signature_mul_cartan_involution, star_one_half, ← smul_add]
    simp
  · unfold inG cpart2
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.smul_mul, Matrix.add_mul,
      cartan_involution_conjTranspose_mul, Matrix.mul_smul, Matrix.mul_add, signature_mul_cartan_involution, star_one_div_two_I, neg_smul,
      add_comm (Jm ε * Z), neg_add_cancel]
  · unfold cpart1 cpart2
    rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp, ← smul_add]
    rw [sub_add_add_cancel, ← two_smul ℂ Z, smul_smul]
    norm_num
  · intro hX
    unfold inG at hX
    have hA : Jm ε * Zᴴ * Jm ε = -Z := by
      rw [Matrix.mul_assoc, eq_neg_of_add_eq_zero_left hX, Matrix.mul_neg, signature_mul_signature_mul]
    unfold cpart1 cpart2
    rw [hA, sub_neg_eq_add, add_neg_cancel, smul_zero, ← two_smul ℂ Z, smul_smul]
    norm_num

end Formalism.REAL
end
end

section -- merged from Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
open scoped InnerProductSpace
open Finset

noncomputable section

namespace Formalism.REAL

theorem mem_compactSpan_self {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (x : V) : x ∈ kSpan ε F x := by
  unfold kSpan
  rw [Submodule.mem_sInf]
  intro S hS
  exact hS.1

theorem compactSpan_le_of_mem {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) {x : V} {S : Submodule ℂ V} (hx : x ∈ S)
    (hS : KStable ε F S) : kSpan ε F x ≤ S :=
  sInf_le ⟨hx, hS⟩

theorem compactSpan_isCompactInvariant {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (x : V) : KStable ε F (kSpan ε F x) := by
  intro a b hab y hy
  unfold kSpan at *
  rw [Submodule.mem_sInf] at *
  intro S hS
  exact hS.2 a b hab y (hy S hS)

theorem inner_compactCasimir_self {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V) (hu : KUnit ε F) (y : V) :
    ⟪y, CasK ε F y⟫_ℂ = ((∑ a, ∑ b, if ε a = ε b then ‖F b a y‖ ^ 2 else 0 : ℝ) : ℂ) := by
  unfold CasK
  simp only [LinearMap.sum_apply, inner_sum]
  push_cast
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · rw [Module.End.mul_apply, ← hu b a h.symm y (F b a y), inner_self_eq_norm_sq_to_K]
    push_cast; rfl
  · simp

theorem kWtBound_of (hc : KCasSpan) : KWtBound := by
  intro V _ _ n ε F μ ν x y hr hu hx hy hy0 hν
  have h1 := hc V n ε F μ x hr hx y hy
  have h2 := inner_compactCasimir_self ε F hu y
  rw [h1, inner_smul_right, inner_self_eq_norm_sq_to_K] at h2
  have h3 : ckv ε μ * ‖y‖ ^ 2 = ∑ a, ∑ b, (if ε a = ε b then ‖F b a y‖ ^ 2 else 0 : ℝ) := by
    apply Complex.ofReal_injective
    push_cast at h2 ⊢
    exact h2
  have h4 : nsq ν * ‖y‖ ^ 2 ≤ ∑ a, ∑ b, (if ε a = ε b then ‖F b a y‖ ^ 2 else 0 : ℝ) := by
    unfold nsq dot
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro a _
    calc ν a * ν a * ‖y‖ ^ 2 = (if ε a = ε a then ‖F a a y‖ ^ 2 else 0 : ℝ) := by
          rw [if_pos rfl, hν a, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
          ring
      _ ≤ ∑ b, (if ε a = ε b then ‖F b a y‖ ^ 2 else 0 : ℝ) :=
          Finset.single_le_sum (f := fun b => (if ε a = ε b then ‖F b a y‖ ^ 2 else 0 : ℝ))
            (fun b _ => by split_ifs <;> positivity) (Finset.mem_univ a)
  have hpos : 0 < ‖y‖ ^ 2 := by positivity
  exact le_of_mul_le_mul_right (h4.trans h3.ge) hpos

theorem isCompactInvariant_orthogonal_inf {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V) (hu : KUnit ε F)
    {K S : Submodule ℂ V} (hK : KStable ε F K) (hS : KStable ε F S) : KStable ε F (Kᗮ ⊓ S) := by
  intro a b hab y hy
  rw [Submodule.mem_inf] at hy ⊢
  refine ⟨?_, hS a b hab y hy.2⟩
  rw [Submodule.mem_orthogonal]
  intro z hz
  rw [← hu b a hab.symm z y]
  exact (Submodule.mem_orthogonal K y).1 hy.1 _ (hK b a hab.symm z hz)

theorem compactDecomposition_of_finrank (he : KHiExist) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (n : ℕ) (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V) (hr : KRel ε F)
    (hu : KUnit ε F) :
    ∀ (d : ℕ) (S : Submodule ℂ V), Module.finrank ℂ S = d → FiniteDimensional ℂ S →
    KStable ε F S →
    ∃ (m : ℕ) (x : Fin m → V) (μ : Fin m → Fin n → ℝ),
      (∀ i, x i ∈ S ∧ x i ≠ 0 ∧ KHighest ε F (μ i) (x i)) ∧
      (∀ i i', i ≠ i' → ∀ y ∈ kSpan ε F (x i), ∀ z ∈ kSpan ε F (x i'), ⟪y, z⟫_ℂ = 0) ∧
      (⨆ i, kSpan ε F (x i)) = S := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro S hd hfin hS
  by_cases h0 : S = ⊥
  · refine ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
    rw [h0]
    exact iSup_of_empty _
  obtain ⟨x, hxS, hx0, μ, hxμ⟩ := he V n ε F S hfin hr hu hS h0
  have hKS : kSpan ε F x ≤ S := compactSpan_le_of_mem ε F hxS hS
  have : FiniteDimensional ℂ (kSpan ε F x) := Submodule.finiteDimensional_of_le hKS
  have hS'S : (kSpan ε F x)ᗮ ⊓ S < S := by
    refine lt_of_le_of_ne inf_le_right ?_
    intro heq
    have hx' : x ∈ (kSpan ε F x)ᗮ ⊓ S := by rw [heq]; exact hxS
    rw [Submodule.mem_inf] at hx'
    have h1 := (Submodule.mem_orthogonal (kSpan ε F x) x).1 hx'.1 x (mem_compactSpan_self ε F x)
    exact hx0 (inner_self_eq_zero.1 h1)
  have : FiniteDimensional ℂ ↥((kSpan ε F x)ᗮ ⊓ S) := Submodule.finiteDimensional_of_le hS'S.le
  have hlt : Module.finrank ℂ ↥((kSpan ε F x)ᗮ ⊓ S) < d := hd ▸ Submodule.finrank_lt_finrank_of_lt hS'S
  obtain ⟨m, xs, μs, h1, h2, h3⟩ := ih _ hlt ((kSpan ε F x)ᗮ ⊓ S) rfl inferInstance
    (isCompactInvariant_orthogonal_inf ε F hu (compactSpan_isCompactInvariant ε F x) hS)
  have hle : ∀ j, kSpan ε F (xs j) ≤ (kSpan ε F x)ᗮ ⊓ S := fun j =>
    h3 ▸ le_iSup (fun i => kSpan ε F (xs i)) j
  refine ⟨m + 1, Fin.cons x xs, Fin.cons μ μs, ?_, ?_, ?_⟩
  · intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · simp only [Fin.cons_zero]
      exact ⟨hxS, hx0, hxμ⟩
    · simp only [Fin.cons_succ]
      exact ⟨(h1 j).1.2, (h1 j).2⟩
  · intro i i' hii'
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ i' with rfl | ⟨j', rfl⟩
    · exact absurd rfl hii'
    · simp only [Fin.cons_zero, Fin.cons_succ]
      intro y hy z hz
      exact Submodule.inner_right_of_mem_orthogonal hy (hle j' hz).1
    · simp only [Fin.cons_zero, Fin.cons_succ]
      intro y hy z hz
      exact Submodule.inner_left_of_mem_orthogonal hz (hle j hy).1
    · simp only [Fin.cons_succ]
      exact h2 j j' (fun h => hii' (congrArg Fin.succ h))
  · apply le_antisymm
    · refine iSup_le fun i => ?_
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · simpa using hKS
      · simp only [Fin.cons_succ]
        exact (hle j).trans inf_le_right
    · calc S = kSpan ε F x ⊔ (kSpan ε F x)ᗮ ⊓ S :=
            (Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hKS).symm
        _ ≤ _ := by
          refine sup_le ?_ ?_
          · exact le_iSup_of_le (0 : Fin (m + 1)) (by simp)
          · conv_lhs => rw [← h3]
            exact iSup_le fun j => le_iSup_of_le j.succ (by simp)

theorem kDecomp_of (he : KHiExist) (ho : KOrth) : KDecomp := by
  intro V _ _ n ε F S hfin hr hu hS
  exact compactDecomposition_of_finrank he V n ε F hr hu _ S rfl hfin hS

theorem compactSpan_le_isotypicPart {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (T : Set (Fin n → ℝ)) (S : Submodule ℂ V) {y : V}
    {μ : Fin n → ℝ} (hy : y ∈ S) (hμ : μ ∈ T) (hk : KHighest ε F μ y) :
    kSpan ε F y ≤ isoPart ε F T S := by
  unfold isoPart
  exact le_iSup₂_of_le (f := fun y (_ : y ∈ S ∧ ∃ μ ∈ T, KHighest ε F μ y) => kSpan ε F y)
    y ⟨hy, μ, hμ, hk⟩ le_rfl

theorem isotypicPart_le {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (T : Set (Fin n → ℝ)) (S : Submodule ℂ V)
    (hS : KStable ε F S) : isoPart ε F T S ≤ S := by
  unfold isoPart
  exact iSup₂_le fun y hy => compactSpan_le_of_mem ε F hy.1 hS

theorem kIsoSplit_of (hd : KDecomp) (ho : KOrth) : KIsoSplit := by
  intro V _ _ n ε F S T hfin hr hu hS
  constructor
  · have h : isoPart ε F T S ⟂ isoPart ε F Tᶜ S := by
      unfold isoPart
      rw [Submodule.isOrtho_iSup_left]; intro y
      rw [Submodule.isOrtho_iSup_left]; rintro ⟨_, μ, hμT, hyμ⟩
      rw [Submodule.isOrtho_iSup_right]; intro z
      rw [Submodule.isOrtho_iSup_right]; rintro ⟨_, ν, hνT, hzν⟩
      rw [Submodule.isOrtho_iff_inner_eq]
      exact ho V n ε F μ ν y z hr hu hyμ hzν (fun h => hνT (h ▸ hμT))
    exact Submodule.isOrtho_iff_inner_eq.1 h
  · obtain ⟨m, x, μ, h1, h2, h3⟩ := hd V n ε F S hfin hr hu hS
    apply le_antisymm
    · exact sup_le (isotypicPart_le ε F T S hS) (isotypicPart_le ε F Tᶜ S hS)
    · conv_lhs => rw [← h3]
      refine iSup_le fun i => ?_
      by_cases hi : μ i ∈ T
      · exact le_sup_of_le_left (compactSpan_le_isotypicPart ε F T S (h1 i).1 hi (h1 i).2.2)
      · exact le_sup_of_le_right (compactSpan_le_isotypicPart ε F Tᶜ S (h1 i).1 hi (h1 i).2.2)

theorem abs_compactHalfSum_le {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : |rhoC ε a| ≤ n := by
  unfold rhoC
  have c1 := Finset.card_filter_le (univ : Finset (Fin n)) (fun b => a < b ∧ ε b = ε a)
  have c2 := Finset.card_filter_le (univ : Finset (Fin n)) (fun b => b < a ∧ ε b = ε a)
  simp only [Finset.card_univ, Fintype.card_fin] at c1 c2
  have d1 : ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) ≤ n := by exact_mod_cast c1
  have d2 : ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) ≤ n := by exact_mod_cast c2
  have e1 : (0 : ℝ) ≤ ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) := Nat.cast_nonneg _
  have e2 : (0 : ℝ) ≤ ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) := Nat.cast_nonneg _
  rw [abs_le]
  constructor <;> linarith

theorem compactCasimirValue_le {n : ℕ} (ε : Fin n → Bool) (μ : Fin n → ℝ) (R : ℝ)
    (hμ : ∀ a, |μ a| ≤ R) : ckv ε μ ≤ n * (R + n) ^ 2 := by
  unfold ckv nsq dot
  have h0 : 0 ≤ ∑ a, rhoC ε a * rhoC ε a := Finset.sum_nonneg fun a _ => mul_self_nonneg _
  have h1 : ∑ a, (μ + rhoC ε) a * (μ + rhoC ε) a ≤ ∑ _a : Fin n, (R + n) ^ 2 := by
    apply Finset.sum_le_sum
    intro a _
    simp only [Pi.add_apply]
    have h3 : |μ a + rhoC ε a| ≤ R + n :=
      (abs_add_le (μ a) (rhoC ε a)).trans (add_le_add (hμ a) (abs_compactHalfSum_le ε a))
    rw [← sq, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h3 2
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  linarith

theorem kCasBound_of (hd : KDecomp) (hc : KCasSpan) (ho : KOrth) : KCasBound := by
  intro V _ _ n ε F S R hfin hr hu hS hR hw y hy
  obtain ⟨m, x, μ, h1, h2, h3⟩ := hd V n ε F S hfin hr hu hS
  have hy' : y ∈ ⨆ i ∈ (univ : Finset (Fin m)), kSpan ε F (x i) := by simpa [h3] using hy
  obtain ⟨v, hv⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ y).1 hy'
  have hC : CasK ε F y = ∑ i, ((ckv ε (μ i) : ℝ) : ℂ) • (v i : V) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hv, map_sum]
    exact Finset.sum_congr rfl fun i _ => hc V n ε F (μ i) (x i) hr (h1 i).2.2 _ (v i).2
  have key : ∀ c : Fin m → ℂ,
      ⟪y, ∑ i, c i • (v i : V)⟫_ℂ = ∑ i, c i * ⟪(v i : V), (v i : V)⟫_ℂ := by
    intro c
    rw [← hv, sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_sum, Finset.sum_eq_single j]
    · rw [inner_smul_right]
    · intro i _ hij
      rw [inner_smul_right, h2 j i (Ne.symm hij) _ (v j).2 _ (v i).2, mul_zero]
    · simp
  have hvv : ∀ i, ⟪(v i : V), (v i : V)⟫_ℂ = ((‖(v i : V)‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  have hn : ‖y‖ ^ 2 = ∑ i, ‖(v i : V)‖ ^ 2 := by
    have h := key (fun _ => 1)
    simp only [one_smul, one_mul, hv, inner_self_eq_norm_sq_to_K] at h
    apply Complex.ofReal_injective
    push_cast
    exact h
  have key2 := key (fun i => ((ckv ε (μ i) : ℝ) : ℂ))
  rw [hC, key2]
  simp only [hvv]
  have hre : (∑ i, ((ckv ε (μ i) : ℝ) : ℂ) * ((‖(v i : V)‖ ^ 2 : ℝ) : ℂ)).re =
      ∑ i, ckv ε (μ i) * ‖(v i : V)‖ ^ 2 := by
    simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re]
  rw [hre, hn, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact compactCasimirValue_le ε (μ i) R (hw (μ i) (x i) (h1 i).1 (h1 i).2.1 (h1 i).2.2.1)

end Formalism.REAL
end
end

section -- merged from Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator
open Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.REAL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def mulRightRealCLM {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)

lemma mulRightCLM_apply {n : ℕ} (X h : Matrix (Fin n) (Fin n) ℂ) : mulRightRealCLM X h = h * X := rfl

lemma withTop_enat_infty_add_one_le_infty : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by simp

theorem rdSmooth_of (h : RdExt) : RdSmooth := by
  intro n ε f X hf hX g₀ hg₀
  obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U, fun k => fderiv ℝ F k (k * X), hU, hg₀U, ?_, ?_⟩
  · have h1 := hF.fderiv_of_isOpen (m := ∞) hU withTop_enat_infty_add_one_le_infty
    have h2 : ContDiffOn ℝ ∞ (fun k : Matrix (Fin n) (Fin n) ℂ => k * X) U :=
      (mulRightRealCLM X).contDiff.contDiffOn
    exact h1.clm_apply h2
  · intro k hk hkJ
    exact h n ε f F U k X hU hk hkJ hF hfF hX

lemma lie_algebra_bracket_mem {n : ℕ} {ε : Fin n → Bool} {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) (hY : inG ε Y) : inG ε (X * Y - Y * X) := by
  unfold inG at *
  have hX' : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left hX
  have hY' : Yᴴ * Jm ε = -(Jm ε * Y) := eq_neg_of_add_eq_zero_left hY
  have e1 : Yᴴ * Xᴴ * Jm ε = Jm ε * Y * X := by
    rw [Matrix.mul_assoc, hX', Matrix.mul_neg, ← Matrix.mul_assoc, hY', Matrix.neg_mul, neg_neg]
  have e2 : Xᴴ * Yᴴ * Jm ε = Jm ε * X * Y := by
    rw [Matrix.mul_assoc, hY', Matrix.mul_neg, ← Matrix.mul_assoc, hX', Matrix.neg_mul, neg_neg]
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Matrix.sub_mul, e1, e2,
    Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  abel

theorem rdBracket_of (h : RdExt) (hs : RdSmooth) : RdBracket := by
  intro n ε f X Y g hf hX hY hg
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have hFa : ContDiffAt ℝ ∞ F g := hF.contDiffAt (hU.mem_nhds hgU)
  have ext : ∀ Z, inG ε Z → ∀ k ∈ U, inUJ ε k → Rd Z f k = fderiv ℝ F k (k * Z) :=
    fun Z hZ k hk hkJ => h n ε f F U k Z hU hk hkJ hF hfF hZ
  have hsm : ∀ Z : Matrix (Fin n) (Fin n) ℂ,
      ContDiffOn ℝ ∞ (fun k => fderiv ℝ F k (k * Z)) U := fun Z =>
    (hF.fderiv_of_isOpen hU withTop_enat_infty_add_one_le_infty).clm_apply (mulRightRealCLM Z).contDiff.contDiffOn
  have hc : DifferentiableAt ℝ (fderiv ℝ F) g :=
    (hFa.fderiv_right (m := ∞) withTop_enat_infty_add_one_le_infty).differentiableAt (by simp)
  have hd : ∀ Z W : Matrix (Fin n) (Fin n) ℂ, fderiv ℝ (fun k => fderiv ℝ F k (k * Z)) g W
      = fderiv ℝ (fderiv ℝ F) g W (g * Z) + fderiv ℝ F g (W * Z) := by
    intro Z W
    have H := (hc.hasFDerivAt.clm_apply (mulRightRealCLM Z).hasFDerivAt).fderiv
    erw [H]
    exact add_comm _ _
  have e1 : Rd X (Rd Y f) g = fderiv ℝ (fun k => fderiv ℝ F k (k * Y)) g (g * X) :=
    h n ε (Rd Y f) _ U g X hU hgU hg (hsm Y) (ext Y hY) hX
  have e2 : Rd Y (Rd X f) g = fderiv ℝ (fun k => fderiv ℝ F k (k * X)) g (g * Y) :=
    h n ε (Rd X f) _ U g Y hU hgU hg (hsm X) (ext X hX) hY
  have e3 := ext _ (lie_algebra_bracket_mem hX hY) g hgU hg
  have hsym : IsSymmSndFDerivAt ℝ F g := hFa.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; norm_cast)
  have hs2 := hsym (g * X) (g * Y)
  rw [e1, e2, e3, hd, hd]
  simp only [Matrix.mul_sub, Matrix.mul_assoc, map_sub]
  erw [hs2]
  exact add_sub_add_left_eq_sub _ _ _

lemma lie_algebra_add_mem_matrix {n : ℕ} {ε : Fin n → Bool} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : inG ε A) (hB : inG ε B) : inG ε (A + B) := by
  unfold inG at *
  rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
  calc Aᴴ * Jm ε + Bᴴ * Jm ε + (Jm ε * A + Jm ε * B)
      = (Aᴴ * Jm ε + Jm ε * A) + (Bᴴ * Jm ε + Jm ε * B) := by abel
    _ = 0 := by rw [hA, hB, add_zero]

lemma lie_algebra_neg_mem {n : ℕ} {ε : Fin n → Bool} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : inG ε A) : inG ε (-A) := by
  unfold inG at *
  rw [conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, hA, neg_zero]

lemma lie_algebra_sub_mem {n : ℕ} {ε : Fin n → Bool} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : inG ε A) (hB : inG ε B) : inG ε (A - B) := by
  rw [sub_eq_add_neg]; exact lie_algebra_add_mem_matrix hA (lie_algebra_neg_mem hB)

lemma lie_algebra_signature_conj {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    Jm ε * Xᴴ * Jm ε = -X := by
  have hX' : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left hX
  rw [Matrix.mul_assoc, hX', Matrix.mul_neg, ← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]

lemma complex_parts_unique {n : ℕ} {ε : Fin n → Bool} {P Q : Matrix (Fin n) (Fin n) ℂ}
    (hP : inG ε P) (hQ : inG ε Q) :
    cpart1 ε (P + Complex.I • Q) = P ∧ cpart2 ε (P + Complex.I • Q) = Q := by
  have hZ : Jm ε * (P + Complex.I • Q)ᴴ * Jm ε = -P + Complex.I • Q := by
    rw [conjTranspose_add, conjTranspose_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, lie_algebra_signature_conj hP, lie_algebra_signature_conj hQ, Complex.star_def, Complex.conj_I]
    module
  unfold cpart1 cpart2
  rw [hZ]
  constructor
  · module
  · have : P + Complex.I • Q + (-P + Complex.I • Q) = (2 * Complex.I) • Q := by module
    rw [this, smul_smul, one_div, inv_mul_cancel₀ (by simp), one_smul]

lemma real_part_sub {n : ℕ} (ε : Fin n → Bool) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    cpart1 ε (Z - W) = cpart1 ε Z - cpart1 ε W := by
  unfold cpart1
  rw [conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]
  module

lemma imaginary_part_sub {n : ℕ} (ε : Fin n → Bool) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    cpart2 ε (Z - W) = cpart2 ε Z - cpart2 ε W := by
  unfold cpart2
  rw [conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]
  module

lemma commutator_complex_expand {n : ℕ} (X1 X2 Y1 Y2 : Matrix (Fin n) (Fin n) ℂ) :
    (X1 + Complex.I • X2) * (Y1 + Complex.I • Y2) - (Y1 + Complex.I • Y2) * (X1 + Complex.I • X2) =
      ((X1 * Y1 - Y1 * X1) - (X2 * Y2 - Y2 * X2)) +
        Complex.I • ((X1 * Y2 - Y2 * X1) + (X2 * Y1 - Y1 * X2)) := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
  match_scalars <;> first | ring1 | linear_combination Complex.I_sq | linear_combination -Complex.I_sq

lemma right_derivative_neg (hl : RdLin) {n : ℕ} {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    {B g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnG ε f) (hB : inG ε B) (hg : inUJ ε g) :
    Rd (-B) f g = -Rd B f g := by
  have := (hl n ε f f B B (-1) 0 g hf hf hB hB hg).2.1
  have e : (((-1 : ℝ) : ℂ) • B) = -B := by simp
  rw [e] at this
  rw [this]; simp

lemma right_derivative_add (hl : RdLin) {n : ℕ} {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    {A B g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnG ε f) (hA : inG ε A) (hB : inG ε B)
    (hg : inUJ ε g) : Rd (A + B) f g = Rd A f g + Rd B f g :=
  (hl n ε f f A B 0 0 g hf hf hA hB hg).1

lemma right_derivative_sub (hl : RdLin) {n : ℕ} {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    {A B g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnG ε f) (hA : inG ε A) (hB : inG ε B)
    (hg : inUJ ε g) : Rd (A - B) f g = Rd A f g - Rd B f g := by
  rw [sub_eq_add_neg, right_derivative_add hl hf hA (lie_algebra_neg_mem hB) hg, right_derivative_neg hl hf hB hg, sub_eq_add_neg]

lemma complexified_derivative_sub (hc : CpartMem) (hl : RdLin) {n : ℕ} {ε : Fin n → Bool}
    {f : Matrix (Fin n) (Fin n) ℂ → ℂ} {g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnG ε f)
    (hg : inUJ ε g) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    Ec ε (Z - W) f g = Ec ε Z f g - Ec ε W f g := by
  obtain ⟨hZ1, hZ2, -, -⟩ := hc n ε Z
  obtain ⟨hW1, hW2, -, -⟩ := hc n ε W
  unfold Ec
  rw [real_part_sub, imaginary_part_sub, right_derivative_sub hl hf hZ1 hW1 hg, right_derivative_sub hl hf hZ2 hW2 hg]
  ring

lemma complexified_derivative_zero {n : ℕ} (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) : Ec ε 0 f g = 0 := by
  simp [Ec, cpart1, cpart2, Rd]

lemma complexified_derivative_commutator (hc : CpartMem) (hl : RdLin) (hb : RdBracket) (hs : RdSmooth) {n : ℕ}
    (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (Z W g : Matrix (Fin n) (Fin n) ℂ)
    (hf : SmoothOnG ε f) (hg : inUJ ε g) :
    Ec ε Z (Ec ε W f) g - Ec ε W (Ec ε Z f) g = Ec ε (Z * W - W * Z) f g := by
  obtain ⟨hX1, hX2, hZ, -⟩ := hc n ε Z
  obtain ⟨hY1, hY2, hW, -⟩ := hc n ε W
  have hEc : ∀ (Z' : Matrix (Fin n) (Fin n) ℂ) (f' : Matrix (Fin n) (Fin n) ℂ → ℂ),
      Ec ε Z' f' g = Rd (cpart1 ε Z') f' g + Complex.I * Rd (cpart2 ε Z') f' g := fun _ _ => rfl
  have hE : ∀ V, inG ε V → ∀ W' : Matrix (Fin n) (Fin n) ℂ,
      Rd V (Ec ε W' f) g = Rd V (Rd (cpart1 ε W') f) g + Complex.I * Rd V (Rd (cpart2 ε W') f) g :=
    fun V hV W' => (hl n ε _ _ V V 0 Complex.I g (hs n ε f _ hf (hc n ε W').1)
      (hs n ε f _ hf (hc n ε W').2.1) hV hV hg).2.2
  have hZW := commutator_complex_expand (cpart1 ε Z) (cpart2 ε Z) (cpart1 ε W) (cpart2 ε W)
  rw [← hZ, ← hW] at hZW
  have hP := lie_algebra_sub_mem (lie_algebra_bracket_mem hX1 hY1) (lie_algebra_bracket_mem hX2 hY2)
  have hQ := lie_algebra_add_mem_matrix (lie_algebra_bracket_mem hX1 hY2) (lie_algebra_bracket_mem hX2 hY1)
  obtain ⟨h1, h2⟩ := complex_parts_unique hP hQ
  rw [hEc Z, hEc W, hE _ hX1, hE _ hX2, hE _ hY1, hE _ hY2, hZW, hEc, h1, h2,
    right_derivative_sub hl hf (lie_algebra_bracket_mem hX1 hY1) (lie_algebra_bracket_mem hX2 hY2) hg,
    right_derivative_add hl hf (lie_algebra_bracket_mem hX1 hY2) (lie_algebra_bracket_mem hX2 hY1) hg,
    ← hb n ε f _ _ g hf hX1 hY1 hg, ← hb n ε f _ _ g hf hX2 hY2 hg,
    ← hb n ε f _ _ g hf hX1 hY2 hg, ← hb n ε f _ _ g hf hX2 hY1 hg]
  linear_combination (Rd (cpart2 ε Z) (Rd (cpart2 ε W) f) g -
    Rd (cpart2 ε W) (Rd (cpart2 ε Z) f) g) * Complex.I_mul_I

theorem eabGl_of (hc : CpartMem) (hl : RdLin) (hb : RdBracket) (hs : RdSmooth) : EabGl := by
  intro n ε f a b c d g hf hg
  unfold Eab
  rw [complexified_derivative_commutator hc hl hb hs ε f _ _ g hf hg]
  have hm : Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
      (if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) := by
    by_cases h1 : b = c <;> by_cases h2 : d = a
    · subst h1; subst h2; simp
    · subst h1; simp [h2]
    · subst h2; simp [h1]
    · simp [h1, h2]
  rw [hm, complexified_derivative_sub hc hl hf hg]
  split_ifs <;> simp [complexified_derivative_zero]

end Formalism.REAL
end
end

section -- merged from Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorPowUpperVanishHolds
open Finset

noncomputable section

namespace Formalism.REAL

theorem generatorPowCovariance_holds : EpowCov := by
  intro A _ n E hE k
  induction k with
  | zero =>
    intro a b c d
    simp only [epow, @eq_comm _ b c, @eq_comm _ a d]
    have hl : E c d * (if a = b then (1 : A) else 0) - (if a = b then (1 : A) else 0) * E c d = 0 := by
      split_ifs <;> simp
    rw [hl]
    by_cases h2 : d = a <;> by_cases h3 : c = b <;> simp [h2, h3]
  | succ k ih =>
    intro a b c d
    simp only [epow]
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    have step : ∀ e, E c d * (epow E k a e * E e b) - epow E k a e * E e b * E c d =
        ((if d = a then epow E k c e else 0) - (if e = c then epow E k a d else 0)) * E e b +
        epow E k a e * ((if d = e then E c b else 0) - (if b = c then E e d else 0)) := by
      intro e
      rw [← ih a e c d, ← hE c d e b]
      noncomm_ring
    simp only [step]
    by_cases hda : d = a <;> by_cases hbc : b = c <;>
      simp [hda, hbc, Finset.sum_add_distrib, Finset.sum_sub_distrib, sub_mul, mul_sub, ite_mul, mul_ite] <;> abel

theorem generatorTraceCentral_holds : EtrCentral := by
  intro A _ n E hE k c d
  have hc := generatorPowCovariance_holds A n E hE k
  unfold etr
  rw [Finset.sum_mul, Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  have h1 : ∀ a, epow E k a a * E c d - E c d * epow E k a a =
      -((if d = a then epow E k c a else 0) - (if a = c then epow E k a d else 0)) := by
    intro a
    rw [← hc a a c d]
    abel
  simp only [h1, Finset.sum_neg_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, sub_self, neg_zero]

end Formalism.REAL
end
end

section -- merged from Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantCompactSpan
open scoped InnerProductSpace
open Finset

noncomputable section

namespace Formalism.REAL

section KT2Gen
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ V}

theorem mem_compactSpan (x : V) : x ∈ kSpan ε F x := by
  exact Submodule.mem_sInf.2 fun S hS => hS.1

theorem compactSpan_le {x : V} {S : Submodule ℂ V} (hx : x ∈ S) (hS : KStable ε F S) :
    kSpan ε F x ≤ S := sInf_le ⟨hx, hS⟩

theorem isCompactInvariant_compactSpan (x : V) : KStable ε F (kSpan ε F x) := by
  intro a b hab y hy
  rw [kSpan, Submodule.mem_sInf] at hy ⊢
  intro S hS
  exact hS.2 a b hab y (hy S hS)

theorem isWeightVector_apply (hrel : KRel ε F) {ν : Fin n → ℝ} {v : V}
    (hv : IsWeight F ν v) (a b : Fin n) (hab : ε a = ε b) :
    IsWeight F (ν + root a b) (F a b v) := by
  intro c
  have h := congrArg (fun T : Module.End ℂ V => T v) (hrel c c a b rfl hab)
  have e1 : (if c = a then F c b else 0) v = (if c = a then (1 : ℂ) else 0) • F a b v := by
    split_ifs with h1
    · subst h1
      simp
    · simp
  have e2 : (if b = c then F a c else 0) v = (if c = b then (1 : ℂ) else 0) • F a b v := by
    by_cases h2 : c = b
    · subst h2
      simp
    · simp [h2, Ne.symm h2]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hv c, map_smul, e1, e2] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h, ← sub_smul, ← add_smul]
  congr 1
  simp only [root, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  split_ifs <;> push_cast <;> ring

end KT2Gen

theorem eigenvalue_real {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    {ε : Fin n → Bool} {F : Fin n → Fin n → Module.End ℂ V} (hunit : KUnit ε F)
    {v : V} (hv : v ≠ 0) (a : Fin n) {c : ℂ} (hc : F a a v = c • v) : ((c.re : ℝ) : ℂ) = c := by
  have h := hunit a a rfl v v
  rw [hc, inner_smul_left, inner_smul_right] at h
  have hvv : ⟪v, v⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hv
  exact Complex.conj_eq_iff_re.1 (mul_right_cancel₀ hvv h)

theorem kHiUniq_of (hl : KLow) (_hw : KWtOrth) (ho : KOrth) : KHiUniq := by
  intro V _ _ n ε F μ ν x y hrel hunit hx hyx hy
  by_cases hμν : ν = μ
  · right
    refine ⟨hμν, ?_⟩
    obtain ⟨hspan, huniq⟩ := hl V n ε F μ x hrel hx
    exact huniq y (hspan ▸ hyx) (hμν ▸ hy.1)
  · left
    have h0 := ho V n ε F μ ν x y hrel hunit hx hy (Ne.symm hμν) y hyx y (mem_compactSpan y)
    exact inner_self_eq_zero.1 h0

theorem kIrr_of (he : KHiExist) (hu : KHiUniq) : KIrr := by
  intro V _ _ n ε F μ x hfd hrel hunit hx S hS hSst
  by_cases h0 : S = ⊥
  · exact Or.inl h0
  right
  haveI := hfd
  have hfdS : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hS
  obtain ⟨y, hyS, hy0, ν, hy⟩ := he V n ε F S hfdS hrel hunit hSst h0
  rcases hu V n ε F μ ν x y hrel hunit hx (hS hyS) hy with h | ⟨-, c, hc⟩
  · exact absurd h hy0
  · have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hy0 hc
    have hxS : x ∈ S := by
      have h1 : c⁻¹ • y ∈ S := S.smul_mem _ hyS
      rwa [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at h1
    exact le_antisymm hS (compactSpan_le hxS hSst)

theorem weighted_sum_rootVector_shift {n : ℕ} (ν : Fin n → ℝ) (a b : Fin n) :
    (∑ i : Fin n, -((i : ℕ) : ℝ) * (ν + root a b) i) =
      (∑ i : Fin n, -((i : ℕ) : ℝ) * ν i) + (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
  simp only [root, Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  ring

theorem highestWeightExists_holds : KHiExist := by
  intro V _ _ n ε F S hfd hrel hunit hst hne
  haveI := hfd
  have hcomm : ∀ a b : Fin n, F a a * F b b = F b b * F a a := by
    intro a b
    have h := hrel a a b b rfl rfl
    by_cases hab : a = b
    · subst hab
      rfl
    · simpa [hab, Ne.symm hab, sub_eq_zero] using h
  have main : ∀ s : Finset (Fin n), ∃ W : Submodule ℂ V, W ≤ S ∧ W ≠ ⊥ ∧
      (∀ a, ∀ w ∈ W, F a a w ∈ W) ∧ ∃ lam : Fin n → ℂ, ∀ a ∈ s, ∀ w ∈ W, F a a w = lam a • w := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨S, le_rfl, hne, fun a w hw => hst a a rfl w hw, 0, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨W, hWS, hW0, hWst, lam, hlam⟩ := ih
      haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWS
      haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hW0
      obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((F a a).restrict (hWst a))
      obtain ⟨⟨v, hvW⟩, hv⟩ := hc.exists_hasEigenvector
      have hker : ∀ y, y ∈ LinearMap.ker (F a a - c • 1) ↔ F a a y = c • y := by
        intro y
        simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
          sub_eq_zero]
      have hvker : F a a v = c • v := by
        have h1 := congrArg Subtype.val hv.apply_eq_smul
        simpa using h1
      refine ⟨W ⊓ LinearMap.ker (F a a - c • 1), inf_le_left.trans hWS, ?_, ?_, Function.update lam a c, ?_⟩
      · intro h
        have hvmem : v ∈ W ⊓ LinearMap.ker (F a a - c • 1) := ⟨hvW, (hker v).2 hvker⟩
        rw [h] at hvmem
        exact hv.2 (Subtype.ext (by simpa using (Submodule.mem_bot ℂ).1 hvmem))
      · intro b w hw
        refine ⟨hWst b w hw.1, (hker _).2 ?_⟩
        have h1 : F a a w = c • w := (hker w).1 hw.2
        have h2 := congrArg (fun T : Module.End ℂ V => T w) (hcomm a b)
        simp only [Module.End.mul_apply] at h2
        rw [h2, h1, map_smul]
      · intro b hb w hw
        rcases Finset.mem_insert.1 hb with rfl | hb'
        · rw [Function.update_self]
          exact (hker w).1 hw.2
        · rw [Function.update_of_ne (by rintro rfl; exact ha hb')]
          exact hlam b hb' w hw.1
  obtain ⟨W, hWS, hW0, -, lam, hlam⟩ := main Finset.univ
  obtain ⟨v0, hv0W, hv00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hw0 : IsWeight F (fun a => (lam a).re) v0 := fun a => by
    rw [eigenvalue_real hunit hv00 a (hlam a (Finset.mem_univ a) v0 hv0W)]
    exact hlam a (Finset.mem_univ a) v0 hv0W
  have hstab : ∀ a, ∀ y ∈ S, F a a y ∈ S := fun a => hst a a rfl
  have hfinW : {ν : Fin n → ℝ | ∃ v ∈ S, v ≠ 0 ∧ IsWeight F ν v}.Finite := by
    refine (Set.Finite.pi (t := fun a => {r : ℝ | Module.End.HasEigenvalue ((F a a).restrict (hstab a)) (r : ℂ)})
      (fun a => ?_)).subset ?_
    · exact (Module.End.finite_hasEigenvalue _).preimage (fun _ _ _ _ h => Complex.ofReal_injective h)
    · rintro ν ⟨v, hvS, hv0, hvw⟩
      simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq]
      intro a
      apply Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨v, hvS⟩)
      refine ⟨?_, ?_⟩
      · rw [Module.End.mem_eigenspace_iff]
        apply Subtype.ext
        simp [hvw a]
      · intro h
        apply hv0
        simpa using congrArg Subtype.val h
  obtain ⟨ν, ⟨v, hvS, hv0, hvw⟩, hmax⟩ := Set.exists_max_image _
    (fun ν : Fin n → ℝ => ∑ i : Fin n, -((i : ℕ) : ℝ) * ν i) hfinW ⟨_, v0, hWS hv0W, hv00, hw0⟩
  refine ⟨v, hvS, hv0, ν, hvw, fun a b hab hεab => ?_⟩
  by_contra hne'
  have hmem : ν + root a b ∈ {ν : Fin n → ℝ | ∃ v ∈ S, v ≠ 0 ∧ IsWeight F ν v} :=
    ⟨F a b v, hst a b hεab v hvS, hne', isWeightVector_apply hrel hvw a b hεab⟩
  have h1 := hmax _ hmem
  rw [weighted_sum_rootVector_shift] at h1
  have h2 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  linarith

end Formalism.REAL
end
end

section -- merged from Formalism.RealPlaceAnalysis.RealPlaceTaylor.CasComm
open scoped TensorProduct
open Finset

noncomputable section

namespace Formalism.REAL

theorem casComm_casK_comm {A : Type} [Ring A] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → A) (hE : GlRel E) (c d : Fin n) (hcd : ε c = ε d) :
    CasK ε E * E c d = E c d * CasK ε E :=
  _root_.UpperTheory.Reformulated.B.CasimirCommutation.casComm_casK_comm ε E hE c d hcd

theorem casimir_central_holds : CasCentral := by
  intro A _ n ε E hE
  refine ⟨fun c d => ?_, fun c d h => casComm_casK_comm ε E hE c d h⟩
  have h := casComm_casK_comm (fun _ => true) E hE c d rfl
  have hC : CasK (fun _ : Fin n => true) E = Cas E := by simp [CasK, Cas]
  rwa [hC] at h

end Formalism.REAL
end
end
