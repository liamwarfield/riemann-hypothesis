module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CliffordHighestWeightVector
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParthasarathyRaoVaradarajan
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteWeightsInvariantHom
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualWeightsDominated
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarmonicOfNormBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualWeightTraceFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarmonicWeightsCoefficient

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDualLieFamily
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDualLieFamily
noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG

theorem dualFam_exists : ∀ {n : ℕ} (E : KMod n), ∃ G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ), IsDualFam E G := by
  intro n E
  obtain ⟨e, ρ', hc, hiso, hint⟩ := GlobalTheory.T.unitary_euclidean_model E
  obtain ⟨F, hgl, -, hder⟩ := GlobalTheory.T.exists_compact_lie_action _ ρ' hc hiso
  refine ⟨fun a b => e.symm.toLinearMap ∘ₗ F a b ∘ₗ e.toLinearMap, ?_, ?_⟩
  · intro a b c d
    ext1 ξ
    have h := LinearMap.congr_fun (hgl a b c d) (e ξ)
    apply e.injective
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, map_sub] at h ⊢
    rw [h]
    split_ifs <;> simp
  · intro X γ hX hγ ξ
    let eL : EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)) →L[ℂ] (E.V →L[ℂ] ℂ) :=
      LinearMap.toContinuousLinearMap e.symm.toLinearMap
    have heL : ∀ w, eL w = e.symm w := fun _ => rfl
    have h := (eL.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hder X γ hX hγ (e ξ))
    have hf : (fun t : ℝ => ξ ∘L E.ρ (γ t)⁻¹) = (eL.restrictScalars ℝ) ∘ fun t : ℝ => ρ' (γ t) (e ξ) := by
      funext t
      simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars', heL, ← hint,
        LinearEquiv.symm_apply_apply]
    rw [hf]
    refine h.congr_deriv ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ContinuousLinearMap.coe_restrictScalars', map_sum, map_smul, heL, LinearMap.comp_apply,
      LinearEquiv.coe_coe]

end GlobalTheory.CompanionTheory.RealCountG
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDualLieFamilyStatement
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dual_lie_family : ∀ {n : ℕ} (E : KMod n), ∃ G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ), IsDualFam E G := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.dualFam_exists | exact GlobalTheory.CompanionTheory.RealCountG.dualFam_exists | (intros; apply GlobalTheory.CompanionTheory.RealCountG.dualFam_exists <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvariantExtending
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvariantExtending
noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG.ExtMulti

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def lowS (D : Fin n → Fin n → Module.End ℂ H) (S : Submodule ℂ H) (k : ℕ) : Submodule ℂ H :=
  Nat.rec S (fun _ N => N ⊔ ⨆ (a : Fin n) (b : Fin n) (_ : b < a), N.map (D a b)) k

theorem lowS_le_succ (D : Fin n → Fin n → Module.End ℂ H) (S : Submodule ℂ H) (k : ℕ) :
    lowS D S k ≤ lowS D S (k + 1) := le_sup_left

theorem lowS_low (D : Fin n → Fin n → Module.End ℂ H) (S : Submodule ℂ H) (k : ℕ) {a b : Fin n} (h : b < a)
    {u : H} (hu : u ∈ lowS D S k) : D a b u ∈ lowS D S (k + 1) :=
  Submodule.mem_sup_right (Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem b
    (Submodule.mem_iSup_of_mem h (Submodule.mem_map_of_mem hu))))

theorem lowS_stable {D : Fin n → Fin n → Module.End ℂ H} (hD : Formalism.REAL.GlRel D) {S : Submodule ℂ H} {μ : Fin n → ℝ}
    (hS : ∀ x ∈ S, Formalism.REAL.KHighest (fun _ => true) D μ x) (k : ℕ) :
    ∀ c d : Fin n, c ≤ d → ∀ u ∈ lowS D S k, D c d u ∈ lowS D S k := by
  induction k with
  | zero =>
    intro c d hcd x hx
    change x ∈ S at hx
    change D c d x ∈ S
    rcases hcd.lt_or_eq with h | rfl
    · rw [(hS x hx).2 c d h rfl]
      exact S.zero_mem
    · rw [(hS x hx).1 c]
      exact S.smul_mem _ hx
  | succ k ih =>
    have step : ∀ (x y : Fin n), ∀ w ∈ lowS D S k, D x y w ∈ lowS D S (k + 1) := by
      intro x y w hw
      rcases lt_or_ge y x with h | h
      · exact lowS_low D S k h hw
      · exact lowS_le_succ D S k (ih x y h w hw)
    intro c d hcd
    suffices h : lowS D S (k + 1) ≤ (lowS D S (k + 1)).comap (D c d) from fun u hu => h hu
    refine sup_le (fun u hu => step c d u hu) ?_
    refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
    rintro _ ⟨w, hw, rfl⟩
    have hc := congrArg (fun A : Module.End ℂ H => A w) (hD c d a b)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at hc
    have e : D c d (D a b w) = D a b (D c d w) +
        ((if d = a then D c b else 0) - (if b = c then D a d else 0) : Module.End ℂ H) w := by
      rw [LinearMap.sub_apply, ← hc]
      abel
    change D c d (D a b w) ∈ lowS D S (k + 1)
    rw [e]
    refine Submodule.add_mem _ (lowS_low D S k hab (ih c d hcd w hw)) ?_
    rw [LinearMap.sub_apply]
    refine Submodule.sub_mem _ ?_ ?_
    · split_ifs
      · exact step _ _ w hw
      · simp
    · split_ifs
      · exact step _ _ w hw
      · simp

theorem lowS_orth {D : Fin n → Fin n → Module.End ℂ H} (hU : ∀ a b (x y : H), ⟪D a b x, y⟫_ℂ = ⟪x, D b a y⟫_ℂ)
    {S : Submodule ℂ H} {μ ν : Fin n → ℝ} (hS : ∀ x ∈ S, Formalism.REAL.KHighest (fun _ => true) D μ x) (hne : ν ≠ μ) {y : H}
    (hy : Formalism.REAL.KHighest (fun _ => true) D ν y) (k : ℕ) : ∀ u ∈ lowS D S k, ⟪u, y⟫_ℂ = 0 := by
  induction k with
  | zero =>
    intro x hx
    change x ∈ S at hx
    obtain ⟨a, ha⟩ := Function.ne_iff.1 hne
    have h := hU a a x y
    rw [(hS x hx).1 a, hy.1 a, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h
    have h' : ((μ a : ℂ) - (ν a : ℂ)) * ⟪x, y⟫_ℂ = 0 := by
      rw [sub_mul, h, sub_self]
    have hd : (μ a : ℂ) - (ν a : ℂ) ≠ 0 := by
      rw [sub_ne_zero]
      exact fun e => ha (Complex.ofReal_injective e).symm
    exact (mul_eq_zero.1 h').resolve_left hd
  | succ k ih =>
    suffices h : lowS D S (k + 1) ≤ (ℂ ∙ y)ᗮ by
      intro u hu
      have := Submodule.mem_orthogonal_singleton_iff_inner_left.1 (h hu)
      exact this
    refine sup_le (fun u hu => Submodule.mem_orthogonal_singleton_iff_inner_left.2 (ih u hu)) ?_
    refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
    rintro _ ⟨w, hw, rfl⟩
    refine Submodule.mem_orthogonal_singleton_iff_inner_left.2 ?_
    rw [hU, hy.2 b a hab rfl, inner_zero_right]

theorem exists_proj [FiniteDimensional ℂ H] {D : Fin n → Fin n → Module.End ℂ H} (hD : Formalism.REAL.GlRel D)
    (hU : ∀ a b (x y : H), ⟪D a b x, y⟫_ℂ = ⟪x, D b a y⟫_ℂ) {S : Submodule ℂ H} {μ : Fin n → ℝ}
    (hS : ∀ x ∈ S, Formalism.REAL.KHighest (fun _ => true) D μ x) :
    ∃ P : H →ₗ[ℂ] H, (∀ a b w, P (D a b w) = D a b (P w)) ∧ (∀ x ∈ S, P x = x) ∧
      ∀ ν, ν ≠ μ → ∀ y, Formalism.REAL.KHighest (fun _ => true) D ν y → P y = 0 := by
  set N : Submodule ℂ H := ⨆ k, lowS D S k with hN
  have hmem : ∀ k, lowS D S k ≤ N := fun k => le_iSup (lowS D S) k
  have hstab : ∀ a b, ∀ u ∈ N, D a b u ∈ N := by
    intro a b
    suffices h : N ≤ N.comap (D a b) from fun u hu => h hu
    refine iSup_le fun k u hu => ?_
    rcases lt_or_ge b a with h | h
    · exact hmem _ (lowS_low D S k h hu)
    · exact hmem _ (lowS_stable hD hS k a b h u hu)
  refine ⟨(N.starProjection : H →ₗ[ℂ] H), ?_, ?_, ?_⟩
  · intro a b w
    change N.starProjection (D a b w) = D a b (N.starProjection w)
    refine (Submodule.eq_starProjection_of_mem_orthogonal (hstab a b _ (Submodule.starProjection_apply_mem N w)) ?_)
    rw [← map_sub]
    have hw := Submodule.sub_starProjection_mem_orthogonal (K := N) w
    rw [Submodule.mem_orthogonal] at hw ⊢
    intro u hu
    rw [← hU, hw _ (hstab b a u hu)]
  · intro x hx
    exact Submodule.starProjection_eq_self_iff.2 (hmem 0 hx)
  · intro ν hne y hy
    refine Submodule.eq_starProjection_of_mem_orthogonal N.zero_mem ?_
    rw [sub_zero, Submodule.mem_orthogonal]
    intro u hu
    suffices h : N ≤ (ℂ ∙ y)ᗮ from Submodule.mem_orthogonal_singleton_iff_inner_left.1 (h hu)
    exact iSup_le fun k u hu => Submodule.mem_orthogonal_singleton_iff_inner_left.2 (lowS_orth hU hS hne hy k u hu)

theorem exists_multi {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (D : Fin n → Fin n → Module.End ℂ H)
    (D' : Fin n → Fin n → Module.End ℂ V) (hD : Formalism.REAL.GlRel D) (hD' : Formalism.REAL.GlRel D')
    (hU : ∀ a b (x y : H), ⟪D a b x, y⟫_ℂ = ⟪x, D b a y⟫_ℂ) (hU' : ∀ a b (x y : V), ⟪D' a b x, y⟫_ℂ = ⟪x, D' b a y⟫_ℂ)
    {ι : Type} (M : Finset ι) (wt : ι → Fin n → ℝ) (hwt : Function.Injective wt) (Hs : ι → Submodule ℂ H)
    (hHs : ∀ i, ∀ x ∈ Hs i, Formalism.REAL.KHighest (fun _ => true) D (wt i) x) (f : ∀ i, Hs i →ₗ[ℂ] V)
    (hf : ∀ i x, Formalism.REAL.KHighest (fun _ => true) D' (wt i) (f i x)) :
    ∃ T : H →ₗ[ℂ] V, (∀ i ∈ M, ∀ x : Hs i, T x = f i x) ∧ ∀ a b w, T (D a b w) = D' a b (T w) := by
  classical
  choose P hP1 hP2 hP3 using fun i => exists_proj hD hU (hHs i)
  choose T hT1 hT2 using fun i => GlobalTheory.T.highest_weight_tensor_decomposition H V D D' (wt i) hD hD' hU hU' (Hs i) (hHs i) (f i) (hf i)
  refine ⟨∑ i ∈ M, (T i).comp (P i), ?_, ?_⟩
  · intro i hi x
    rw [LinearMap.sum_apply, Finset.sum_eq_single i]
    · rw [LinearMap.comp_apply, hP2 i _ x.2, hT1]
    · intro j _ hji
      rw [LinearMap.comp_apply, hP3 j _ (fun e => hji (hwt e).symm) _ (hHs i _ x.2), map_zero]
    · exact fun h => absurd hi h
  · intro a b w
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum, hP1, hT2]

theorem exp_mem_unitary (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s : ℝ) :
    NormedSpace.exp ((s : ℂ) • X) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose]
  have h : ((s : ℂ) • X)ᴴ = -((s : ℂ) • X) := by
    rw [conjTranspose_smul, hX]
    simp
  have hc : Commute ((s : ℂ) • X) (-((s : ℂ) • X)) := (Commute.refl _).neg_right
  rw [h, ← Matrix.exp_add_of_commute _ _ hc]
  simp

theorem single_conjT (a b : Fin n) (c : ℂ) :
    (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ)ᴴ = Matrix.single b a (star c) := by
  ext i j
  simp only [conjTranspose_apply, Matrix.single_apply]
  by_cases h : a = j ∧ b = i
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
  · rw [if_neg h, if_neg (fun hh => h ⟨hh.2, hh.1⟩)]
    simp

theorem single_neg' (a b : Fin n) (c : ℂ) :
    (Matrix.single a b (-c) : Matrix (Fin n) (Fin n) ℂ) = -Matrix.single a b c := by
  ext i j
  simp only [Matrix.neg_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem sum_single {W : Type} [AddCommGroup W] [Module ℂ W] (L : Fin n → Fin n → W) (a b : Fin n) (c : ℂ) :
    ∑ i, ∑ j, (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ) i j • L i j = c • L a b := by
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro j _ hj
    simp [hj.symm]
  · simp
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [hi.symm]
  · simp

theorem coef_zero {W : Type} [AddCommGroup W] [Module ℂ W] (L : Fin n → Fin n → W)
    (h : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X → ∑ i, ∑ j, X i j • L i j = 0) (a b : Fin n) : L a b = 0 := by
  have h1 := h (Matrix.single a b 1 - Matrix.single b a 1) (by
    rw [conjTranspose_sub, single_conjT, single_conjT, star_one, neg_sub])
  have h2 := h (Matrix.single a b Complex.I + Matrix.single b a Complex.I) (by
    rw [conjTranspose_add, single_conjT, single_conjT, Complex.star_def, Complex.conj_I, single_neg', single_neg',
      neg_add, add_comm])
  simp only [Matrix.sub_apply, Matrix.add_apply, sub_smul, add_smul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_single] at h1 h2
  rw [one_smul, one_smul, sub_eq_zero] at h1
  rw [← h1, ← two_smul ℂ, smul_smul] at h2
  exact (smul_eq_zero.1 h2).resolve_left (by simp)

theorem dual_rel (E : KMod n) (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)) (hG : IsDualFam E G)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (e : (E.V →L[ℂ] ℂ) ≃ₗ[ℂ] H) (ρ' : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H))
    (he : ∀ k ξ, e (ξ ∘L E.ρ k⁻¹) = ρ' k (e ξ)) (G' : Fin n → Fin n → Module.End ℂ H)
    (hGd : ∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X →
      (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) → ∀ w : H,
        HasDerivAt (fun t : ℝ => ρ' (γ t) w) (∑ a, ∑ b, X a b • G' a b w) 0)
    (a b : Fin n) (ξ : E.V →L[ℂ] ℂ) : G' a b (e ξ) = e (G a b ξ) := by
  have key := coef_zero (fun i j => G' i j (e ξ) - e (G i j ξ)) (fun X hX => by
    let γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ := fun t => ⟨_, exp_mem_unitary X hX t⟩
    have h1 := hGd X γ hX (fun _ => rfl) (e ξ)
    have h2 := hG.2 X γ hX (fun _ => rfl) ξ
    have h3 : HasDerivAt (fun t : ℝ => e (ξ ∘L E.ρ (γ t)⁻¹)) (e (∑ a, ∑ b, X a b • G a b ξ)) 0 :=
      ((LinearMap.toContinuousLinearMap e.toLinearMap).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
    have h4 : (fun t : ℝ => ρ' (γ t) (e ξ)) = fun t : ℝ => e (ξ ∘L E.ρ (γ t)⁻¹) := by
      funext t
      exact (he (γ t) ξ).symm
    rw [h4] at h1
    have h5 := h1.unique h3
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul] at h5
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [h5, sub_self]) a b
  exact sub_eq_zero.1 key

theorem exists_inv_multi : ∀ {n : ℕ} (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)), IsPair E1 E2 →
    IsDerivK σ (kF E1 E2) → ∀ (E : KMod n) (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)), IsDualFam E G →
    ∀ (M : Finset (Fin n → ℤ)) (f : ∀ μ : Fin n → ℤ, hwOf G (wtR μ) →ₗ[ℂ] hwSp E1 E2 (wtR μ)),
      ∃ t ∈ invA σ E, ∀ μ ∈ M, ∀ ξ : hwOf G (wtR μ), t ξ = f μ ξ := by
  intro n V _ _ E1 E2 σ hp hσ E G hG M f
  obtain ⟨e, ρ', hc, hi, he⟩ := GlobalTheory.T.unitary_euclidean_model E
  obtain ⟨G', hG', hGa, hGd⟩ := GlobalTheory.T.exists_compact_lie_action _ ρ' hc hi
  have hK : Formalism.REAL.GlRel (kF E1 E2) := by
    intro a b c d
    have h1 := hp.gl1 a b c d
    have h2 := hp.gl2 a b c d
    have e' : kF E1 E2 a b * kF E1 E2 c d - kF E1 E2 c d * kF E1 E2 a b =
        (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b) := by
      simp only [kF, add_mul, mul_add]
      rw [hp.comm a b c d, hp.comm c d a b]
      abel
    rw [e', h1, h2]
    split_ifs <;> simp [kF] <;> abel
  have hrel := dual_rel E G hG e ρ' he G' hGd
  have hHigh : ∀ (μ : Fin n → ℤ), ∀ x ∈ (hwOf G (wtR μ)).map e.toLinearMap,
      Formalism.REAL.KHighest (fun _ => true) G' (wtR μ) x := by
    rintro μ _ ⟨ξ, hξ, rfl⟩
    refine ⟨fun a => ?_, fun a b hab h => ?_⟩
    · change G' a a (e ξ) = _ • e ξ
      rw [hrel, hξ.1 a, map_smul]
    · change G' a b (e ξ) = 0
      rw [hrel, hξ.2 a b hab h, map_zero]
  let eS : ∀ μ : Fin n → ℤ, hwOf G (wtR μ) ≃ₗ[ℂ] (hwOf G (wtR μ)).map e.toLinearMap := fun μ => e.submoduleMap _
  obtain ⟨T, hT1, hT2⟩ := exists_multi G' (kF E1 E2) hG' hK hGa hp.unitK M wtR wtR_injective
    (fun μ => (hwOf G (wtR μ)).map e.toLinearMap) hHigh
    (fun μ => ((hwSp E1 E2 (wtR μ)).subtype.comp (f μ)).comp (eS μ).symm.toLinearMap)
    (fun μ x => (f μ ((eS μ).symm x)).2)
  have hint := GlobalTheory.T.derivative_unitary_action _ V ρ' G' hGd σ (kF E1 E2) hσ hp.unitK T hT2
  refine ⟨T.comp e.toLinearMap, ?_, ?_⟩
  · intro k ξ
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [he, hint]
  · intro μ hμ ξ
    have := hT1 μ hμ (eS μ ξ)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Submodule.subtype_apply] at this
    exact this

end GlobalTheory.CompanionTheory.RealCountG.ExtMulti
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvariantExtendingStatement
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_extending : ∀ {n : ℕ} (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)), IsPair E1 E2 → IsDerivK σ (kF E1 E2) → ∀ (E : KMod n) (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)), IsDualFam E G → ∀ (M : Finset (Fin n → ℤ)) (f : ∀ μ : Fin n → ℤ, hwOf G (wtR μ) →ₗ[ℂ] hwSp E1 E2 (wtR μ)), ∃ t ∈ invA σ E, ∀ μ ∈ M, ∀ ξ : hwOf G (wtR μ), t ξ = f μ ξ := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.ExtMulti.exists_inv_multi | exact GlobalTheory.CompanionTheory.RealCountG.ExtMulti.exists_inv_multi | (intros; apply GlobalTheory.CompanionTheory.RealCountG.ExtMulti.exists_inv_multi <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceFactorTensorDecomp
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalOfHom
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.HomTrace

theorem finiteDimensional_of_hom (W H : Type) [AddCommGroup W] [Module ℂ W]
    [AddCommGroup H] [Module ℂ H] [Nontrivial W] [FiniteDimensional ℂ (W →ₗ[ℂ] H)] :
    FiniteDimensional ℂ H := by
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  have hex : ∃ φ : Module.Dual ℂ W, φ w ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hw ((Module.forall_dual_apply_eq_zero_iff ℂ w).1 hcon)
  obtain ⟨φ, hφ⟩ := hex
  let j : H →ₗ[ℂ] (W →ₗ[ℂ] H) :=
    { toFun := fun h => φ.smulRight h
      map_add' := fun x y => by ext v; simp
      map_smul' := fun c x => by
        ext v
        simp only [LinearMap.smulRight_apply, LinearMap.smul_apply, RingHom.id_apply]
        exact smul_comm _ _ _ }
  have hj : Function.Injective j := by
    intro x y hxy
    have h1 : φ w • x = φ w • y := by
      simpa [j] using LinearMap.congr_fun hxy w
    exact smul_right_injective H hφ h1
  exact FiniteDimensional.of_injective j hj

noncomputable def sandwich {W H : Type} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup H] [Module ℂ H] (a : H →ₗ[ℂ] H) (b : W →ₗ[ℂ] W) :
    (W →ₗ[ℂ] H) →ₗ[ℂ] (W →ₗ[ℂ] H) where
  toFun f := a ∘ₗ f ∘ₗ b
  map_add' f g := by ext v; simp
  map_smul' c f := by ext v; simp

theorem trace_sandwich {W H : Type} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup H] [Module ℂ H] [FiniteDimensional ℂ W] [FiniteDimensional ℂ H]
    (a : H →ₗ[ℂ] H) (b : W →ₗ[ℂ] W) :
    LinearMap.trace ℂ (W →ₗ[ℂ] H) (sandwich a b) =
      LinearMap.trace ℂ W b * LinearMap.trace ℂ H a := by
  let e := dualTensorHomEquiv ℂ W H
  let M : (TensorProduct ℂ (Module.Dual ℂ W) H) →ₗ[ℂ] (TensorProduct ℂ (Module.Dual ℂ W) H) :=
    TensorProduct.map (Module.Dual.transpose (R := ℂ) b) a
  have hcomp : (e : _ →ₗ[ℂ] _) ∘ₗ M = sandwich a b ∘ₗ (e : _ →ₗ[ℂ] _) := by
    apply TensorProduct.ext'
    intro φ h
    ext v
    simp [e, M, sandwich, dualTensorHomEquiv, dualTensorHomEquivOfBasis_apply, dualTensorHom_apply,
      Module.Dual.transpose_apply]
  have hconj : e.conj M = sandwich a b := by
    rw [LinearEquiv.conj_apply]
    ext1 f
    have := LinearMap.congr_fun hcomp (e.symm f)
    simpa using this
  rw [← hconj, LinearMap.trace_conj', LinearMap.trace_tensorProduct', LinearMap.trace_transpose']

end GlobalTheory.CompanionTheory.HomTrace
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceFactorTensorDecomp
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.HomTrace

theorem trace_pi_blocks {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Type)
    [∀ i, AddCommGroup (P i)] [∀ i, Module ℂ (P i)] [∀ i, FiniteDimensional ℂ (P i)]
    (S : ∀ i, P i →ₗ[ℂ] P i) :
    LinearMap.trace ℂ (∀ i, P i) (LinearMap.pi fun i => S i ∘ₗ LinearMap.proj i) =
      ∑ i, LinearMap.trace ℂ (P i) (S i) := by
  have h : (LinearMap.pi fun i => S i ∘ₗ LinearMap.proj i) =
      ∑ i, (LinearMap.single ℂ P i) ∘ₗ (S i ∘ₗ LinearMap.proj i) := by
    refine LinearMap.ext fun x => funext fun j => ?_
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.sum_apply, Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [Pi.single_eq_of_ne hij.symm]
    · simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.trace_comp_comm']
  have h2 : (S i ∘ₗ LinearMap.proj i) ∘ₗ LinearMap.single ℂ P i = S i := by
    refine LinearMap.ext fun x => ?_
    simp
  rw [h2]

theorem trace_of_block_sandwich : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (I : Type) (W H : ι → Type) [AddCommGroup I] [Module ℂ I] [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] [∀ i, AddCommGroup (H i)] [∀ i, Module ℂ (H i)] [FiniteDimensional ℂ I] [∀ i, FiniteDimensional ℂ (W i)] [∀ i, Nontrivial (W i)] (R : I ≃ₗ[ℂ] ∀ i, W i →ₗ[ℂ] H i) (F : I →ₗ[ℂ] I) (a : ∀ i, H i →ₗ[ℂ] H i) (b : ∀ i, W i →ₗ[ℂ] W i), (∀ x i, R (F x) i = a i ∘ₗ R x i ∘ₗ b i) → (∀ i, FiniteDimensional ℂ (H i)) ∧ LinearMap.trace ℂ I F = ∑ i, LinearMap.trace ℂ (W i) (b i) * LinearMap.trace ℂ (H i) (a i) := by
  intro ι _ _ I W H _ _ _ _ _ _ _ _ _ R F a b hF
  haveI hP : FiniteDimensional ℂ (∀ i, W i →ₗ[ℂ] H i) := LinearEquiv.finiteDimensional R
  haveI hHom : ∀ i, FiniteDimensional ℂ (W i →ₗ[ℂ] H i) := fun i =>
    Module.Finite.of_surjective (LinearMap.proj (R := ℂ) (φ := fun i => W i →ₗ[ℂ] H i) i)
      (fun y => ⟨Pi.single i y, by simp⟩)
  haveI hH : ∀ i, FiniteDimensional ℂ (H i) := fun i => finiteDimensional_of_hom (W i) (H i)
  refine ⟨hH, ?_⟩
  have hconj : R.conj F =
      LinearMap.pi fun i => sandwich (a i) (b i) ∘ₗ LinearMap.proj i := by
    rw [LinearEquiv.conj_apply]
    refine LinearMap.ext fun f => funext fun i => ?_
    have := hF (R.symm f) i
    simpa [sandwich] using this
  rw [← LinearMap.trace_conj' F R, hconj, trace_pi_blocks]
  exact Finset.sum_congr rfl fun i _ => trace_sandwich (a i) (b i)

end GlobalTheory.CompanionTheory.HomTrace
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceFactorTensorDecompStatement
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_factor_tensor_decomp : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (I : Type) (W H : ι → Type) [AddCommGroup I] [Module ℂ I] [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] [∀ i, AddCommGroup (H i)] [∀ i, Module ℂ (H i)] [FiniteDimensional ℂ I] [∀ i, FiniteDimensional ℂ (W i)] [∀ i, Nontrivial (W i)] (R : I ≃ₗ[ℂ] ∀ i, W i →ₗ[ℂ] H i) (F : I →ₗ[ℂ] I) (a : ∀ i, H i →ₗ[ℂ] H i) (b : ∀ i, W i →ₗ[ℂ] W i), (∀ x i, R (F x) i = a i ∘ₗ R x i ∘ₗ b i) → (∀ i, FiniteDimensional ℂ (H i)) ∧ LinearMap.trace ℂ I F = ∑ i, LinearMap.trace ℂ (W i) (b i) * LinearMap.trace ℂ (H i) (a i) := by
  first | exact @GlobalTheory.CompanionTheory.HomTrace.trace_of_block_sandwich | exact GlobalTheory.CompanionTheory.HomTrace.trace_of_block_sandwich | (intros; apply GlobalTheory.CompanionTheory.HomTrace.trace_of_block_sandwich <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedTraceWeylCharacter
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedTraceWeylCharacter
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.RealCountG.LefDual

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

variable {n : ℕ}

theorem trace_dualT (E : KMod n) (S : E.V →L[ℂ] E.V) :
    LinearMap.trace ℂ (E.V →L[ℂ] ℂ) (dualT E S : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) =
      LinearMap.trace ℂ E.V (S : E.V →ₗ[ℂ] E.V) := by
  let e : Module.Dual ℂ E.V ≃ₗ[ℂ] (E.V →L[ℂ] ℂ) := LinearMap.toContinuousLinearMap
  have h : (dualT E S : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) =
      e.conj (Module.Dual.transpose (R := ℂ) (S : E.V →ₗ[ℂ] E.V)) := by
    ext φ x
    simp [e, dualT, LinearEquiv.conj_apply, Module.Dual.transpose_apply]
  rw [h, LinearMap.trace_conj', LinearMap.trace_transpose']

theorem weylChar_conj_arg (lam : Fin n → ℤ) (u : Fin n → ℂ) :
    weylChar lam (fun a => conj (u a)) = conj (weylChar lam u) := by
  unfold weylChar
  rw [map_div₀, RingHom.map_det, RingHom.map_det]
  congr 2 <;> ext i j <;> simp [map_zpow₀]

theorem conj_eq_inv (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ) (hk : k.1 = diagonal z) (a : Fin n) :
    z a ≠ 0 ∧ conj (z a) = (z a)⁻¹ := by
  have h := Matrix.mem_unitaryGroup_iff'.1 k.2
  rw [hk, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal] at h
  have ha := congrFun (congrFun h a) a
  rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.star_apply] at ha
  have h1 : conj (z a) * z a = 1 := ha
  have h0 : z a ≠ 0 := fun h0 => by rw [h0, mul_zero] at h1; exact zero_ne_one h1
  exact ⟨h0, eq_inv_of_mul_eq_one_left h1⟩

theorem trace_dualT_inv (lam : Fin n → ℤ) (E : KMod n) (T : E.V →L[ℂ] E.V) (hT : IsLefK lam E T)
    (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ) (hk : k.1 = diagonal z)
    (hinj : Function.Injective (fun a => z a ^ 2)) :
    LinearMap.trace ℂ (E.V →L[ℂ] ℂ) (dualT E (E.ρ k⁻¹ * T) : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) =
      (∏ a, ∏ b, (1 + z a / z b)) * weylChar lam (fun a => z a ^ 2) := by
  have hz := conj_eq_inv k z hk
  have hk' : (k⁻¹ : Matrix.unitaryGroup (Fin n) ℂ).1 = diagonal (fun a => (z a)⁻¹) := by
    rw [← Unitary.star_eq_inv, Unitary.coe_star, hk, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    exact (hz a).2
  have hinj' : Function.Injective (fun a => (z a)⁻¹ ^ 2) := fun a b h => by
    apply hinj
    simpa [inv_pow] using h
  obtain ⟨-, -, h3⟩ := hT
  obtain ⟨-, h2⟩ := h3 k⁻¹ (fun a => (z a)⁻¹) hk' hinj'
  beta_reduce at h2
  rw [trace_dualT, h2]
  have hw : (fun a => (z a)⁻¹ ^ 2) = fun a => conj (z a ^ 2) := by
    funext a
    rw [map_pow, (hz a).2]
  congr 1
  · simp_rw [inv_div_inv]
    exact Finset.prod_comm
  · rw [hw, weylChar_conj_arg, Complex.conj_conj]

end GlobalTheory.CompanionTheory.RealCountG.LefDual
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedTraceWeylCharacterStatement
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_trace_weyl_character : ∀ {n : ℕ} (lam : Fin n → ℤ) (E : KMod n) (T : E.V →L[ℂ] E.V), IsLefK lam E T → ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective (fun a => z a ^ 2) → LinearMap.trace ℂ (E.V →L[ℂ] ℂ) (dualT E (E.ρ k⁻¹ * T) : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) = (∏ a, ∏ b, (1 + z a / z b)) * weylChar lam (fun a => z a ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.LefDual.trace_dualT_inv | exact GlobalTheory.CompanionTheory.RealCountG.LefDual.trace_dualT_inv | (intros; apply GlobalTheory.CompanionTheory.RealCountG.LefDual.trace_dualT_inv <;> assumption)
end
end

noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG

theorem hw_harm {n : ℕ} (lam : Fin n → ℤ) (hl : Antitone lam)
    (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V)
    (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (A : V →ₗ[ℂ] V) (hc : IsCoreMod (infOf lam) E1 E2 σ A)
    (ν : Fin n → ℤ) (v : V) (hv : v ≠ 0) (hh : v ∈ hwSp E1 E2 (wtR ν)) (hdom : DomLE (wtR ν) (m0 lam)) :
    ν ∈ harmZ lam := by
  obtain ⟨S, hfd, hvS, -, hKS, -⟩ := hc.der.2 v
  have hGl : Formalism.REAL.GlRel (kF E1 E2) := GlobalTheory.CompanionTheory.RealCount.KHw.glRel_kF hc.pair
  have hK : Formalism.REAL.KHighest (fun _ => true) (kF E1 E2) (wtR ν) v := hh
  have hanti : Antitone (wtR ν) := GlobalTheory.CompanionTheory.RealCount.highestWeight_antitone_of_finiteDimensional_stable V (kF E1 E2) S (wtR ν) v hGl hfd hKS hvS hv hK
  have hanti' : Antitone ν := fun a b hab => by
    have := hanti hab
    simpa [wtR] using this
  obtain ⟨ι, i1, i2, c, hcl, hconds⟩ := GlobalTheory.T.parthasarathy_rao_varadarajan n
  obtain ⟨w, hw, x, hx, hxh⟩ := hconds V (kF E1 E2) S ν v hGl hc.pair.unitK hfd hKS hvS hv hK
  have hn := GlobalTheory.T.clifford_highest_weight_vector lam V E1 E2 σ A hc ι c hcl _ x hx hxh
  exact GlobalTheory.T.harmonic_of_norm_bound lam hl ν hanti' hdom w hw hn

theorem hw_stable' {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {E1 E2 : Fin n → Fin n → Module.End ℂ V} {A : V →ₗ[ℂ] V} (hA2 : A * A = 1) (hAE : ∀ a b, A * E1 a b = E2 a b * A)
    (μ : Fin n → ℝ) : ∀ x ∈ hwSp E1 E2 μ, A x ∈ hwSp E1 E2 μ := by
  have hk : ∀ a b (y : V), A (kF E1 E2 a b y) = kF E1 E2 a b (A y) := by
    intro a b y
    have h1 : A (E1 a b y) = E2 a b (A y) := LinearMap.congr_fun (hAE a b) y
    have h2 : A (E2 a b y) = E1 a b (A y) := by
      have h3 : A (E1 a b (A y)) = E2 a b (A (A y)) := LinearMap.congr_fun (hAE a b) (A y)
      have h4 : ∀ u : V, A (A u) = u := fun u => LinearMap.congr_fun hA2 u
      rw [h4] at h3
      rw [← h3, h4]
    simp only [kF, LinearMap.add_apply, map_add (f := _), h1, h2]
    abel
  intro x hx
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · rw [← hk, hx.1 a, map_smul]
  · rw [← hk, hx.2 a b hab he, map_zero]

theorem flip_stable' {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)} {A : V →ₗ[ℂ] V} (hAσ : ∀ k, A * σ k = σ k * A)
    (E : KMod n) (T : E.V →L[ℂ] E.V) (hT : ∀ k, T * E.ρ k = E.ρ k * T) :
    ∀ t ∈ invA σ E, flipA E A T t ∈ invA σ E := by
  intro t ht k ξ
  have h1 : dualT E T (ξ ∘L E.ρ k⁻¹) = (dualT E T ξ) ∘L E.ρ k⁻¹ := by
    ext y
    have h2 := congrArg (fun S : E.V →L[ℂ] E.V => ξ (S y)) (hT k⁻¹)
    simp only [dualT, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply]
    exact (h2.symm)
  have h3 : flipA E A T t (ξ ∘L E.ρ k⁻¹) = A (t (dualT E T (ξ ∘L E.ρ k⁻¹))) := rfl
  have h4 : flipA E A T t ξ = A (t (dualT E T ξ)) := rfl
  rw [h3, h4, h1, ht k (dualT E T ξ)]
  exact LinearMap.congr_fun (hAσ k) _

theorem dual_stable' {n : ℕ} (E : KMod n) (T : E.V →L[ℂ] E.V) (hT : ∀ k, T * E.ρ k = E.ρ k * T)
    (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)) (hG : IsDualFam E G) (μ : Fin n → ℝ) :
    ∀ ξ ∈ hwOf G μ, (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) ξ ∈ hwOf G μ := by
  intro ξ hξ
  have hc := GlobalTheory.T.dual_operator_commutes_lie E T hT G hG
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · show G a a (dualT E T ξ) = _
    rw [← hc, hξ.1 a, map_smul]
    rfl
  · show G a b (dualT E T ξ) = 0
    rw [← hc, hξ.2 a b hab he, map_zero]

theorem diagonal_mem_unitary {n : ℕ} (z : Fin n → ℂ) (hz : ∀ a, ‖z a‖ = 1) :
    (diagonal z : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  refine congrArg Matrix.diagonal (funext fun a => ?_)
  change z a * (starRingEnd ℂ) (z a) = 1
  rw [Complex.mul_conj', hz a]
  simp

theorem dualtr {n : ℕ} (lam : Fin n → ℤ) (hl : Antitone lam) (E : KMod n) (T : E.V →L[ℂ] E.V) (hT : IsLefK lam E T)
    (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)) (hG : IsDualFam E G) :
    ∀ μ ∈ harmZ lam, trOn (hwOf G (wtR μ)) (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) = 2 ^ n := by
  obtain ⟨F, hF, -, hch⟩ := GlobalTheory.T.dual_weight_trace_formula E T hT.1 G hG
  intro μ hμ
  refine (GlobalTheory.T.harmonic_weights_coefficient lam hl F hF (fun ν => trOn (hwOf G (wtR ν)) (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)))
    (fun z hz hinj => ?_) μ hμ).2
  have hzi : Function.Injective z := fun a b h => hinj (by simp only [h])
  have h1 := hch ⟨diagonal z, diagonal_mem_unitary z hz⟩ z rfl hzi
  have h2 := GlobalTheory.T.twisted_trace_weyl_character lam E T hT ⟨diagonal z, diagonal_mem_unitary z hz⟩ z rfl hinj
  rw [← h1, h2]

theorem countG : CountG := by
  intro n lam hlam E T hT V _ _ E1 E2 σ A hc hfin
  obtain ⟨hsp, htop⟩ := GlobalTheory.T.dual_weights_dominated lam hlam E T hT
  obtain ⟨G, hG⟩ := GlobalTheory.T.exists_dual_lie_family E
  have hint := GlobalTheory.T.invariant_intertwines_dual V σ (kF E1 E2) hc.der E G hG
  have hmaps : ∀ t ∈ invA σ E, ∀ (μ : Fin n → ℝ), ∀ ξ ∈ hwOf G μ, t ξ ∈ hwSp E1 E2 μ := by
    intro t ht μ ξ hξ
    refine ⟨fun a => ?_, fun a b hab he => ?_⟩
    · rw [← hint t ht, hξ.1 a, map_smul]
    · rw [← hint t ht, hξ.2 a b hab he, map_zero]
  have hinj := GlobalTheory.T.finite_weights_invariant_hom V E1 E2 σ hc.pair hc.der E G hG hsp (harmZ lam)
    (fun ν v hv hh hw => hw_harm lam hlam V E1 E2 σ A hc ν v hv hh (htop ν hw))
  have hext := GlobalTheory.T.exists_invariant_extending V E1 E2 σ hc.pair hc.der E G hG (harmZ lam)
  have hA : ∀ μ, ∀ x ∈ hwSp E1 E2 μ, A x ∈ hwSp E1 E2 μ := hw_stable' hc.Asq hc.AE
  have hF : ∀ t ∈ invA σ E, flipA E A T t ∈ invA σ E := flip_stable' hc.Aσ E T hT.1
  have hB := dual_stable' E T hT.1 G hG
  have htr := dualtr lam hlam E T hT G hG
  let ι := {μ // μ ∈ harmZ lam}
  let W : ι → Type := fun i => hwOf G (wtR i.1)
  let H : ι → Type := fun i => hwSp E1 E2 (wtR i.1)
  let b : ∀ i, W i →ₗ[ℂ] W i := fun i =>
    (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)).restrict (p := hwOf G (wtR i.1)) (q := hwOf G (wtR i.1)) (hB _)
  let a : ∀ i, H i →ₗ[ℂ] H i := fun i => A.restrict (p := hwSp E1 E2 (wtR i.1)) (q := hwSp E1 E2 (wtR i.1)) (hA _)
  have e3 : ∀ i : ι, LinearMap.trace ℂ (W i) (b i) = 2 ^ n := by
    intro i
    have := htr i.1 i.2
    unfold trOn at this
    rwa [dite_eq_left (hB _)] at this
  haveI hWnt : ∀ i, Nontrivial (W i) := by
    intro i
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have h0 : b i = 0 := LinearMap.ext fun x => Subsingleton.elim _ _
    have := e3 i
    rw [h0, map_zero] at this
    exact (pow_ne_zero n (two_ne_zero : (2 : ℂ) ≠ 0)) this.symm
  let R0 : invA σ E →ₗ[ℂ] (∀ i, W i →ₗ[ℂ] H i) :=
    { toFun := fun t i => LinearMap.codRestrict (hwSp E1 E2 (wtR i.1)) (t.1 ∘ₗ (hwOf G (wtR i.1)).subtype)
        (fun ξ => hmaps t.1 t.2 _ ξ.1 ξ.2)
      map_add' := fun x y => by funext i; ext ξ; rfl
      map_smul' := fun c x => by funext i; ext ξ; rfl }
  have hR0 : ∀ (t : invA σ E) (i : ι) (ξ : W i), ((R0 t i ξ : hwSp E1 E2 (wtR i.1)) : V) = t.1 ξ.1 := fun _ _ _ => rfl
  have hbij : Function.Bijective R0 := by
    constructor
    · refine (injective_iff_map_eq_zero R0).2 fun t ht => ?_
      refine Subtype.ext (hinj t.1 t.2 fun μ hμ ξ hξ => ?_)
      have := hR0 t ⟨μ, hμ⟩ ⟨ξ, hξ⟩
      rw [ht] at this
      simpa using this.symm
    · intro f
      obtain ⟨t, ht, hf⟩ := hext (fun μ => if h : μ ∈ harmZ lam then f ⟨μ, h⟩ else 0)
      refine ⟨⟨t, ht⟩, ?_⟩
      funext i
      ext ξ
      rw [hR0]
      have := hf i.1 i.2 ξ
      rw [dite_eq_left i.2] at this
      exact this
  let R := LinearEquiv.ofBijective R0 hbij
  let Fl := (flipA E A T).restrict (p := invA σ E) (q := invA σ E) hF
  have hcomp : ∀ x i, R (Fl x) i = a i ∘ₗ R x i ∘ₗ b i := by
    intro x i
    ext ξ
    rfl
  haveI : FiniteDimensional ℂ (invA σ E) := hfin
  obtain ⟨hfd, htrace⟩ := GlobalTheory.T.trace_factor_tensor_decomp ι (invA σ E) W H R Fl a b hcomp
  have hse : harmSet lam = (harmZ lam).image wtR := harmSet_eq lam
  refine ⟨fun μ hμ => ?_, fun hne => ?_, ?_⟩
  · rw [hse, Finset.mem_image] at hμ
    obtain ⟨ν, hν, rfl⟩ := hμ
    exact ⟨hA _, hfd ⟨ν, hν⟩⟩
  · by_contra hno
    push_neg at hno
    apply hne
    refine (Submodule.eq_bot_iff _).2 fun t ht => hinj t ht fun μ hμ ξ hξ => ?_
    have h1 := hmaps t ht _ ξ hξ
    have hμ' : wtR μ ∈ harmSet lam := by
      rw [hse]
      exact Finset.mem_image_of_mem _ hμ
    rw [hno _ hμ'] at h1
    simpa using h1
  · have e1 : trOn (invA σ E) (flipA E A T) = LinearMap.trace ℂ (invA σ E) Fl := by
      unfold trOn; rw [dite_eq_left hF]
    have e2 : ∀ i : ι, trOn (hwSp E1 E2 (wtR i.1)) A = LinearMap.trace ℂ (H i) (a i) := by
      intro i
      unfold trOn; rw [dite_eq_left (hA _)]
    rw [e1, htrace, hse, Finset.sum_image (fun x _ y _ h => wtR_injective h), Finset.mul_sum,
      ← Finset.sum_coe_sort (harmZ lam)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [e3 i, e2 i]

end GlobalTheory.CompanionTheory.RealCountG
