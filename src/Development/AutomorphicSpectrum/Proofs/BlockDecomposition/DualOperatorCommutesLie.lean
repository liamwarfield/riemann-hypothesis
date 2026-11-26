module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotent
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalEmbeddingRangeEqField
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalConjugationInvolutiveValuationPreserving
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MvecLeviMulUv

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualOperatorCommutesLie
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualOperatorCommutesLie
noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG.DualComm

variable {n : ℕ}

theorem sum_single_smul {W : Type*} [AddCommGroup W] [Module ℂ W] (Δ : Fin n → Fin n → W) (a b : Fin n) (c : ℂ) :
    ∑ x, ∑ y, (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ) x y • Δ x y = c • Δ a b := by
  have hx : ∀ x y, (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ) x y • Δ x y =
      if y = b then (if x = a then c • Δ a b else 0) else 0 := by
    intro x y
    by_cases h1 : x = a
    · by_cases h2 : y = b
      · subst h1
        subst h2
        simp [Matrix.single_apply]
      · simp [Matrix.single_apply, h1, h2, Ne.symm h2]
    · simp [Matrix.single_apply, h1, Ne.symm h1]
  simp only [hx, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem eq_zero_of_skew {W : Type*} [AddCommGroup W] [Module ℂ W] (Δ : Fin n → Fin n → W)
    (h : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X → ∑ x, ∑ y, X x y • Δ x y = 0) (a b : Fin n) : Δ a b = 0 := by
  have h1 := h (Matrix.single a b 1 - Matrix.single b a 1) (by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_single, Matrix.conjTranspose_single, star_one,
      neg_sub])
  have h2 := h (Matrix.single a b Complex.I + Matrix.single b a Complex.I) (by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_single, Matrix.conjTranspose_single]
    ext i j
    simp [Matrix.single_apply]
    split_ifs <;> ring)
  simp only [Matrix.sub_apply, Matrix.add_apply, sub_smul, add_smul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, sum_single_smul, one_smul] at h1 h2
  rw [sub_eq_zero] at h1
  rw [← h1, ← two_smul ℂ, smul_smul, smul_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact absurd h2 (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  · exact h2

theorem dualT_comp_rho (E : KMod n) (T : E.V →L[ℂ] E.V) (hT : ∀ k, T * E.ρ k = E.ρ k * T)
    (k : Matrix.unitaryGroup (Fin n) ℂ) (ξ : E.V →L[ℂ] ℂ) :
    dualT E T (ξ ∘L E.ρ k) = dualT E T ξ ∘L E.ρ k := by
  ext v
  have h := congrArg (fun f : E.V →L[ℂ] E.V => f v) (hT k)
  change T (E.ρ k v) = E.ρ k (T v) at h
  simp [dualT, h]

theorem dualT_sum (E : KMod n) (T : E.V →L[ℂ] E.V) (hT : ∀ k, T * E.ρ k = E.ρ k * T)
    (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)) (hG : IsDualFam E G)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (ξ : E.V →L[ℂ] ℂ) :
    dualT E T (∑ a, ∑ b, X a b • G a b ξ) = ∑ a, ∑ b, X a b • G a b (dualT E T ξ) := by
  have hmem : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    intro t
    have hc : Commute ((t : ℂ) • X) (-((t : ℂ) • X)) := (Commute.refl _).neg_right
    have hs : ((t : ℂ) • X)ᴴ = -((t : ℂ) • X) := by
      rw [Matrix.conjTranspose_smul, hX, smul_neg]
      simp
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hs,
      ← Matrix.exp_add_of_commute _ _ hc, add_neg_cancel, NormedSpace.exp_zero]
  let γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ := fun t => ⟨NormedSpace.exp ((t : ℂ) • X), hmem t⟩
  have hγ : ∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X) := fun t => rfl
  have h1 := hG.2 X γ hX hγ ξ
  have h2 := hG.2 X γ hX hγ (dualT E T ξ)
  have h3 : HasDerivAt (fun t : ℝ => dualT E T (ξ ∘L E.ρ (γ t)⁻¹))
      (dualT E T (∑ a, ∑ b, X a b • G a b ξ)) 0 :=
    ((dualT E T).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have hfun : (fun t : ℝ => dualT E T (ξ ∘L E.ρ (γ t)⁻¹)) =
      fun t : ℝ => dualT E T ξ ∘L E.ρ (γ t)⁻¹ := by
    funext t
    exact dualT_comp_rho E T hT (γ t)⁻¹ ξ
  rw [hfun] at h3
  exact h3.unique h2

theorem dualT_G : ∀ {n : ℕ} (E : KMod n) (T : E.V →L[ℂ] E.V), (∀ k, T * E.ρ k = E.ρ k * T) →
    ∀ G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ), IsDualFam E G →
      ∀ a b ξ, dualT E T (G a b ξ) = G a b (dualT E T ξ) := by
  intro n E T hT G hG a b ξ
  have h := eq_zero_of_skew (fun a b => dualT E T (G a b ξ) - G a b (dualT E T ξ)) ?_ a b
  · exact sub_eq_zero.mp h
  · intro X hX
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [sub_eq_zero, ← dualT_sum E T hT G hG X hX ξ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]

end GlobalTheory.CompanionTheory.RealCountG.DualComm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualOperatorCommutesLieStatement
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_operator_commutes_lie : ∀ {n : ℕ} (E : KMod n) (T : E.V →L[ℂ] E.V), (∀ k, T * E.ρ k = E.ρ k * T) → ∀ G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ), IsDualFam E G → ∀ a b ξ, dualT E T (G a b ξ) = G a b (dualT E T ξ) := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.DualComm.dualT_G | exact GlobalTheory.CompanionTheory.RealCountG.DualComm.dualT_G | (intros; apply GlobalTheory.CompanionTheory.RealCountG.DualComm.dualT_G <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantIntertwinesDual
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantIntertwinesDual
noncomputable section

open Matrix Finset
open scoped InnerProductSpace

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG.Intertw

variable {n : ℕ}

theorem exp_mem (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s : ℝ) :
    NormedSpace.exp ((s : ℂ) • X) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose]
  have h : ((s : ℂ) • X)ᴴ = -((s : ℂ) • X) := by
    rw [conjTranspose_smul, hX]
    simp
  have hc : Commute ((s : ℂ) • X) (-((s : ℂ) • X)) := (Commute.refl _).neg_right
  rw [h, ← Matrix.exp_add_of_commute _ _ hc]
  simp

theorem sum_single {V : Type} [AddCommGroup V] [Module ℂ V] (F : Fin n → Fin n → V) (a b : Fin n) (c : ℂ) :
    ∑ x, ∑ y, (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ) x y • F x y = c • F a b := by
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro y _ hy
    rw [Matrix.single_apply, if_neg (fun hh => hy hh.2.symm), zero_smul]
  · simp
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [Matrix.single_apply, if_neg (fun hh => hx hh.1.symm), zero_smul]
  · simp

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

theorem family_eq_zero {V : Type} [AddCommGroup V] [Module ℂ V] (F : Fin n → Fin n → V)
    (h : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X → ∑ a, ∑ b, X a b • F a b = 0) (a b : Fin n) : F a b = 0 := by
  have h1 : (Matrix.single a b (1 : ℂ) - Matrix.single b a 1)ᴴ = -(Matrix.single a b (1 : ℂ) - Matrix.single b a 1) := by
    rw [conjTranspose_sub, single_conjT, single_conjT, star_one, neg_sub]
  have h2 : (Matrix.single a b Complex.I + Matrix.single b a Complex.I)ᴴ =
      -(Matrix.single a b Complex.I + Matrix.single b a Complex.I) := by
    rw [conjTranspose_add, single_conjT, single_conjT, Complex.star_def, Complex.conj_I, single_neg', single_neg', neg_add,
      add_comm]
  have m1 := h _ h1
  have m2 := h _ h2
  simp only [Matrix.sub_apply, Matrix.add_apply, sub_smul, add_smul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, sum_single, one_smul] at m1 m2
  have m3 : F a b + F b a = 0 := by
    have := congrArg (fun v => (-Complex.I) • v) m2
    simpa [smul_add, smul_smul] using this
  have m4 : (2 : ℂ) • F a b = 0 := by
    rw [two_smul]
    calc F a b + F a b = (F a b - F b a) + (F a b + F b a) := by abel
      _ = 0 := by rw [m1, m3, add_zero]
  exact (smul_eq_zero.1 m4).resolve_left two_ne_zero

theorem intertwines : ∀ {n : ℕ} (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (Kf : Fin n → Fin n → Module.End ℂ V), IsDerivK σ Kf →
    ∀ (E : KMod n) (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)), IsDualFam E G →
    ∀ t ∈ invA σ E, ∀ a b ξ, t (G a b ξ) = Kf a b (t ξ) := by
  intro n V _ _ σ Kf hK E G hG t ht a b ξ
  refine sub_eq_zero.1 (family_eq_zero (fun a b => t (G a b ξ) - Kf a b (t ξ)) (fun X hX => ?_) a b)
  let γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ := fun s => ⟨NormedSpace.exp ((s : ℂ) • X), exp_mem X hX s⟩
  have h1 := hG.2 X γ hX (fun _ => rfl) ξ
  obtain ⟨S, _, hS, _, _, hd⟩ := hK.2 (t ξ)
  have h2 := hd X γ (fun _ => rfl) (t ξ) hS
  let tL : (E.V →L[ℂ] ℂ) →L[ℂ] V := LinearMap.toContinuousLinearMap t
  have h3 : HasDerivAt (fun s : ℝ => tL (ξ ∘L E.ρ (γ s)⁻¹)) (tL (∑ a, ∑ b, X a b • G a b ξ)) 0 :=
    (tL.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h1
  have h4 : (fun s : ℝ => tL (ξ ∘L E.ρ (γ s)⁻¹)) = fun s : ℝ => σ (γ s) (t ξ) := by
    funext s
    exact ht (γ s) ξ
  rw [h4] at h3
  have h5 := h3.unique h2
  have h6 : tL (∑ a, ∑ b, X a b • G a b ξ) = ∑ a, ∑ b, X a b • t (G a b ξ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
    rfl
  rw [h6] at h5
  simp only [smul_sub, Finset.sum_sub_distrib, h5, sub_self]

end GlobalTheory.CompanionTheory.RealCountG.Intertw
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantIntertwinesDualStatement
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_intertwines_dual : ∀ {n : ℕ} (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (Kf : Fin n → Fin n → Module.End ℂ V), IsDerivK σ Kf → ∀ (E : KMod n) (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)), IsDualFam E G → ∀ t ∈ invA σ E, ∀ a b ξ, t (G a b ξ) = Kf a b (t ξ) := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.Intertw.intertwines | exact GlobalTheory.CompanionTheory.RealCountG.Intertw.intertwines | (intros; apply GlobalTheory.CompanionTheory.RealCountG.Intertw.intertwines <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemUnipBOfMemUnipotent
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GroundTheory.Automorphic Matrix
open scoped ValuativeRel
open PositivityTheory.JacquetShalikaLocal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.JSBound

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem psiOK_of_hasConductor {ψ₁ : AddChar F Circle} (h : GlobalTheory.SplitWeil.HasConductor ψ₁ 1) :
    PsiOK (Circle.coeHom.compAddChar ψ₁) := by
  have h1 : ∀ y : F, ValuativeRel.valuation F y ≤ 1 → ψ₁ y = 1 := fun y hy =>
    (h 1).mpr (by simp) y (by simpa using hy)
  refine ⟨fun x hx => ?_, ?_, fun x => Circle.norm_coe (ψ₁ x)⟩
  · simp [h1 x ((Valuation.mem_integer_iff _ _).mp hx)]
  · have hlt := GroundTheory.Automorphic.GLnLocal.valuation_uniformizer_lt_one F
    have hne := GroundTheory.Automorphic.GLnLocal.valuation_uniformizer_ne_zero F
    set ϖ : F := (GroundTheory.Automorphic.GLnLocal.uniformizer F : F) with hϖdef
    have hϖ : ϖ ≠ 0 := fun h0 => hne (by rw [h0, map_zero])
    have hinv : ValuativeRel.valuation F ϖ * ValuativeRel.valuation F ϖ⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hϖ, map_one]
    have hnot : ¬ ValuativeRel.valuation F ϖ⁻¹ ≤ ValuativeRel.valuation F ((1 : Fˣ) : F) := by
      rw [Units.val_one, map_one]
      intro hle
      have h3 : ValuativeRel.valuation F ϖ * ValuativeRel.valuation F ϖ⁻¹ ≤
          ValuativeRel.valuation F ϖ * 1 := by gcongr
      rw [hinv, mul_one] at h3
      exact absurd hlt (not_lt.mpr h3)
    have hex : ¬ ∀ y : F, ValuativeRel.valuation F y ≤ ValuativeRel.valuation F ϖ⁻¹ → ψ₁ y = 1 :=
      fun hall => hnot ((h _).mp hall)
    push Not at hex
    obtain ⟨y, hy, hy1⟩ := hex
    refine ⟨y, ?_, ?_⟩
    · rw [Valuation.mem_integer_iff, map_mul]
      calc ValuativeRel.valuation F ϖ * ValuativeRel.valuation F y
          ≤ ValuativeRel.valuation F ϖ * ValuativeRel.valuation F ϖ⁻¹ := by gcongr
        _ = 1 := hinv
    · intro hc
      apply hy1
      apply Circle.ext
      rw [Circle.coe_one]
      exact hc

theorem mem_unipB_of_mem_unipotent {n : ℕ} {g : GL (Fin n) F} (hg : g ∈ Iwasawa.unipotent F n) :
    g ∈ GlobalTheory.SmGL.unipB F (Fin n) := by
  obtain ⟨hut, hdiag⟩ := hg
  have hp : g ∈ GlobalTheory.SmGL.parab F (GlobalTheory.SmGL.points (Fin n)) := by
    intro i j hij
    exact hut (by simpa [GlobalTheory.SmGL.blk, GlobalTheory.SmGL.points] using hij)
  refine ⟨⟨g, hp⟩, ?_, rfl⟩
  show GlobalTheory.SmGL.leviProj F (GlobalTheory.SmGL.points (Fin n)) ⟨g, hp⟩ = 1
  refine funext fun a => ?_
  show (GlobalTheory.SmGL.diagBlock F (GlobalTheory.SmGL.points (Fin n)) a).toHomUnits ⟨g, hp⟩ = 1
  apply Units.ext
  ext i j
  show (GlobalTheory.SmGL.diagBlock F (GlobalTheory.SmGL.points (Fin n)) a ⟨g, hp⟩) i j = (1 : Matrix Unit Unit F) i j
  obtain rfl : i = j := Subsingleton.elim _ _
  rw [Matrix.one_apply_eq]
  exact hdiag a

theorem superDiag_eq_superdiagSum {n : ℕ} (g : GL (Fin n) F) :
    GlobalTheory.Whittaker.superDiag g = Whittaker.superdiagSum (g : Matrix (Fin n) (Fin n) F) := by
  simp only [GlobalTheory.Whittaker.superDiag, GroundTheory.Automorphic.Whittaker.superdiagSum, Finset.sum_filter]

theorem whit_of_isFunctional {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin n) F) V} {ψ₁ : AddChar F Circle} {l : Module.Dual ℂ V}
    (h : GlobalTheory.Whittaker.IsFunctional ψ₁ ρ l) : Whit ρ (Circle.coeHom.compAddChar ψ₁) l := by
  intro g hg u
  rw [h g (mem_unipB_of_mem_unipotent hg) u, GroundTheory.Automorphic.Whittaker.psiN,
    ← superDiag_eq_superdiagSum]
  all_goals rfl

end Local

private theorem continuous_of_hasConductor_one {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ψ₁ : AddChar k Circle}
    (h : GlobalTheory.SplitWeil.HasConductor ψ₁ 1) : Continuous ψ₁ := by
  have h1 : ∀ y : k, ValuativeRel.valuation k y ≤ 1 → ψ₁ y = 1 := fun y hy =>
    (h 1).mpr (by simp) y (by simpa using hy)
  have hopen : IsOpen ((ValuativeRel.valuation k).integer : Set k) := Valuation.isOpen_integer
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => y - x) ⁻¹' ((ValuativeRel.valuation k).integer : Set k),
    hopen.preimage (continuous_sub_right x), ?_, ?_⟩
  · show x - x ∈ (ValuativeRel.valuation k).integer
    rw [sub_self]
    exact zero_mem _
  · intro y hy
    have hy' : ψ₁ (y - x) = 1 := h1 _ ((Valuation.mem_integer_iff _ _).mp hy)
    calc ψ₁ y = ψ₁ ((y - x) + x) := by rw [sub_add_cancel]
      _ = ψ₁ (y - x) * ψ₁ x := AddChar.map_add_eq_mul _ _ _
      _ = ψ₁ x := by rw [hy', one_mul]

theorem global_character_holds : G4 := by
  intro E _ _ _ a ha π w
  obtain ⟨ψ₁, hψ⟩ := GlobalTheory.SplitWeil.Model.exists_hasConductor (k := w.adicCompletion E)
  have hne : ψ₁ ≠ 1 := by
    rintro rfl
    exact GlobalTheory.SplitWeil.Model.not_hasConductor_one 1 hψ
  obtain ⟨l, hl0, hl⟩ := GlobalTheory.Published.cuspidalGeneric_holds E a ha π w ψ₁
    (continuous_of_hasConductor_one hψ) hne
  exact ⟨_, psiOK_of_hasConductor hψ, l, hl0, whit_of_isFunctional hl⟩

end GlobalTheory.CompanionTheory.JSBound
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenRightInvarianceLocalCoefficient
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenRightInvarianceLocalCoefficient
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.EcSmooth

theorem continuous_glEmb (k : Type) [Field k] [TopologicalSpace k] [IsTopologicalRing k] (n : ℕ) :
    Continuous (glEmb k n) := by
  have hm : Continuous (glEmbMat k n) := by
    refine continuous_matrix fun a b => ?_
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => simpa [glEmbMat] using continuous_const
      | cast b => simpa [glEmbMat] using continuous_const
    | cast a =>
      induction b using Fin.lastCases with
      | last => simpa [glEmbMat] using continuous_const
      | cast b =>
        simpa [glEmbMat] using (continuous_id.matrix_elem a b)
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact hm.comp Units.continuous_val
  · exact hm.comp (Units.continuous_coe_inv)

theorem continuous_sEmb (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) : Continuous (sEmb k n) :=
  Continuous.subtype_mk ((continuous_glEmb k (n + 1)).comp continuous_subtype_val) _

theorem isOpen_rightInv {M X : Type} [Group M] [TopologicalSpace M] [IsTopologicalGroup M] (e : M → X) (A : Set M)
    (hA : IsOpen A) (h1 : (1 : M) ∈ A) (h : ∀ g ∈ A, ∀ m, e (m * g) = e m) :
    IsOpen {g : M | ∀ m, e (m * g) = e m} := by
  let T : Subgroup M :=
    { carrier := {g | ∀ m, e (m * g) = e m}
      mul_mem' := by
        intro a b ha hb m
        rw [← mul_assoc, hb, ha]
      one_mem' := by
        intro m
        rw [mul_one]
      inv_mem' := by
        intro a ha m
        have := ha (m * a⁻¹)
        rw [inv_mul_cancel_right] at this
        exact this.symm }
  exact T.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (hA.mem_nhds h1) h)

section Fix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {i t : ℕ}
  {τ : MRep k (i + 1)} {σ : GRep k (t + 1)}

def fixX (f : XS τ σ) : Set (Mir k ((i + 1) + (t + 1))) :=
  {x | ind (HPG k (i + 1) (t + 1)) (sigX τ σ) x (f : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ))).1 =
    (f : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ))).1}

theorem isOpen_fixX (f : XS τ σ) : IsOpen (fixX f) :=
  (f : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ))).2

theorem one_mem_fixX (f : XS τ σ) : (1 : Mir k ((i + 1) + (t + 1))) ∈ fixX f := by
  show ind (HPG k (i + 1) (t + 1)) (sigX τ σ) 1 _ = _
  rw [map_one]
  rfl

theorem evX_mul_of_mem (f : XS τ σ) {x : Mir k ((i + 1) + (t + 1))} (hx : x ∈ fixX f)
    (p : Mir k ((i + 1) + (t + 1))) : evX f (p * x) = evX f p :=
  congrArg (fun w : indSpace (HPG k (i + 1) (t + 1)) (sigX τ σ) => w.1 p) hx

theorem intC_mul (ψ : AddChar k Circle) (f : XS τ σ) (m g : Mir k ((i + 1) + t))
    (h : sEmb k ((i + 1) + t) g ∈ fixX f) :
    intC ψ f (sEmb k ((i + 1) + t) (m * g)) = intC ψ f (sEmb k ((i + 1) + t) m) := by
  unfold intC
  congr 1
  funext d
  have h2 : dEmb k i t d * sEmb k ((i + 1) + t) (m * g) =
      (dEmb k i t d * sEmb k ((i + 1) + t) m) * sEmb k ((i + 1) + t) g := by
    rw [MonoidHom.map_mul, mul_assoc]
  rw [h2]
  exact congrArg (fun v => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • v)
    (evX_mul_of_mem f h (dEmb k i t d * sEmb k ((i + 1) + t) m))

theorem eC_mul (ψ : AddChar k Circle) (f : XS τ σ) (m g : Mir k ((i + 1) + t))
    (h : sEmb k ((i + 1) + t) g ∈ fixX f) (h2 : dpowM (k := k) ((i + 1) + t) (-1 / 2) g = 1) :
    eC ψ f (m * g) = eC ψ f m := by
  have h5 : dpowM (k := k) ((i + 1) + t) (-1 / 2) (m * g) = dpowM ((i + 1) + t) (-1 / 2) m :=
    ((dpowM (k := k) ((i + 1) + t) (-1 / 2)).map_mul m g).trans (by rw [h2, mul_one])
  unfold eC
  exact congrArg₂ (fun (c : ℂˣ) v => (c : ℂ) • qC τ σ v) h5 (intC_mul ψ f m g h)

end Fix

theorem isOpen_eC_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1))
    (σ : GRep k (t + 1)) (f : XS τ σ),
    IsOpen {g : Mir k ((i + 1) + t) | ∀ m, eC ψ f (m * g) = eC ψ f m} := by
  intro k _ _ _ _ i t ψ τ σ f
  have hA : IsOpen ((sEmb k ((i + 1) + t)) ⁻¹' fixX f) := (isOpen_fixX f).preimage (continuous_sEmb k _)
  have hB : IsOpen {g : Mir k ((i + 1) + t) | dpowM (k := k) ((i + 1) + t) (-1 / 2) g = 1} :=
    (GlobalTheory.CompanionTheory.LeibPhi.isOpen_ker_dpow k ((i + 1) + t + 1) (-1 / 2)).preimage continuous_subtype_val
  refine isOpen_rightInv (eC ψ f) _ (hA.inter hB) ⟨?_, ?_⟩ fun g hg m => eC_mul ψ f m g hg.1 hg.2
  · show sEmb k ((i + 1) + t) 1 ∈ fixX f
    rw [MonoidHom.map_one]
    exact one_mem_fixX f
  · exact (dpowM (k := k) ((i + 1) + t) (-1 / 2)).map_one

end GlobalTheory.CompanionTheory.BZPhiPG.EcSmooth
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenRightInvarianceLocalCoefficientStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_right_invariance_local_coefficient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ), IsOpen {g : Mir k ((i + 1) + t) | ∀ m, eC ψ f (m * g) = eC ψ f m} := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.EcSmooth.isOpen_eC_invariant | exact GlobalTheory.CompanionTheory.BZPhiPG.EcSmooth.isOpen_eC_invariant | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.EcSmooth.isOpen_eC_invariant <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitDictionaryHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitDictionaryHolds
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SplitPlace

section Generic

variable {G : Type} [Group G]

def toFull (H : Subgroup G) (hH : ∀ g, g ∈ H) : G →* H where
  toFun g := ⟨g, hH g⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def quotEquiv (H : Subgroup G) (hH : ∀ g, g ∈ H) (K : Subgroup H) : H ⧸ K ≃ G ⧸ K.map H.subtype :=
  Quotient.congr (Equiv.ofBijective H.subtype ⟨Subtype.val_injective, fun g => ⟨⟨g, hH g⟩, rfl⟩⟩) fun a b => by
    change QuotientGroup.leftRel K a b ↔ QuotientGroup.leftRel (K.map H.subtype) a.1 b.1
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨x, hx, hxe⟩
      have : x = a⁻¹ * b := Subtype.ext hxe
      exact this ▸ hx

theorem finite_cosets [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G) (hK : IsOpen (K : Set G)) (f : G → ℂ)
    (hc : HasCompactSupport f) : {q : G ⧸ K | f q.out ≠ 0}.Finite := by
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hK
  have h1 : IsCompact ((QuotientGroup.mk : G → G ⧸ K) '' tsupport f) := hc.image continuous_quotient_mk'
  refine h1.finite_of_discrete.subset fun q hq => ?_
  exact ⟨q.out, subset_tsupport _ hq, QuotientGroup.out_eq' q⟩

theorem hasCompactSupport_val [TopologicalSpace G] (H : Subgroup G) (hH : ∀ g, g ∈ H) (e : G → ℂ)
    (hc : HasCompactSupport e) : HasCompactSupport fun x : H => e x.1 := by
  have hcl : IsClosed {a : G | a ∈ H} := by
    have : {a : G | a ∈ H} = Set.univ := Set.eq_univ_of_forall hH
    rw [this]
    exact isClosed_univ
  exact hc.comp_isClosedEmbedding (Topology.IsClosedEmbedding.subtypeVal hcl)

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem levOp_full [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G) (hH : ∀ g, g ∈ H)
    (ρ : Representation ℂ H V) (K K' : Subgroup H) (hK' : IsOpen (K' : Set H)) (hr : K'.relIndex K ≠ 0) (e : G → ℂ)
    (hc : HasCompactSupport e) (hinv : ∀ k ∈ K'.map H.subtype, ∀ g, e (g * k) = e g) (y : V) (hy : y ∈ fixed ρ K') :
    levOp ρ K K' (fun x => ((K'.relIndex K : ℕ) : ℂ) * e x.1) LinearMap.id y =
      ∑ᶠ q : G ⧸ K'.map H.subtype, e q.out • (ρ.comp (toFull H hH)) q.out y := by
  have hr' : ((K'.relIndex K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hr
  have hfin := finite_cosets K' hK' _ (hasCompactSupport_val H hH e hc)
  have hs : (Function.support fun q : H ⧸ K' =>
      ((fun x : H => ((K'.relIndex K : ℕ) : ℂ) * e x.1) q.out • (ρ q.out ∘ₗ LinearMap.id) : V →ₗ[ℂ] V)).Finite := by
    refine hfin.subset fun q hq h0 => hq ?_
    have h0' : e q.out.1 = 0 := h0
    simp [h0']
  have h1 : levOp ρ K K' (fun x => ((K'.relIndex K : ℕ) : ℂ) * e x.1) LinearMap.id y =
      ((K'.relIndex K : ℕ) : ℂ)⁻¹ • (LinearMap.applyₗ y : (V →ₗ[ℂ] V) →ₗ[ℂ] V).toAddMonoidHom
        (∑ᶠ q : H ⧸ K', (fun x : H => ((K'.relIndex K : ℕ) : ℂ) * e x.1) q.out • (ρ q.out ∘ₗ LinearMap.id)) := rfl
  rw [h1, AddMonoidHom.map_finsum _ hs, smul_finsum, ← finsum_comp_equiv (quotEquiv H hH K')]
  refine finsum_congr fun q => ?_
  have hq : quotEquiv H hH K' q = ((q.out.1 : G) : G ⧸ K'.map H.subtype) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (K'.map H.subtype) q.out.1
  rw [hq, hk, hinv k.1 k.2]
  have hk' : (toFull H hH k.1) ∈ K' := by
    obtain ⟨x, hx, hxe⟩ := k.2
    have : toFull H hH k.1 = x := Subtype.ext hxe.symm
    exact this ▸ hx
  have hfix := (GlobalTheory.TwTrLin.mem_fixed_iff ρ K' y).1 hy _ hk'
  have h2 : (ρ.comp (toFull H hH)) (q.out.1 * k.1) y = ρ q.out y := by
    have : toFull H hH (q.out.1 * k.1) = q.out * toFull H hH k.1 := Subtype.ext rfl
    rw [MonoidHom.comp_apply, this, map_mul, Module.End.mul_apply, hfix]
  rw [h2]
  simp [smul_smul, hr']

def fullIrr [TopologicalSpace G] (H : Subgroup G) (hH : ∀ g, g ∈ H) (σ : SmIrr H) : SmIrr G where
  V := σ.V
  ρ := σ.ρ.comp (toFull H hH)
  smooth v := (σ.smooth v).preimage (Continuous.subtype_mk continuous_id hH)
  irred := by
    obtain ⟨h0, h⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 σ.irred
    refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h W fun g v hv => ?_⟩
    exact hW g.1 v hv

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_UL {w : Pl E} (hw : IsSplitAt w) (g : GLw n w) : g ∈ UL n w := by
  unfold UL
  rw [if_pos hw]
  exact Subgroup.mem_top g

theorem splitDict : PositivityTheory.Rg.BcB.F.Eig.SplitDict := by
  intro E _ _ _ n w hw σ
  have hH := mem_UL (n := n) hw
  refine ⟨fullIrr (UL n w) hH σ, LinearEquiv.refl ℂ σ.V, fun _ _ => rfl, ?_, ?_⟩
  · rintro π ⟨p, hp, -, f, hf0, hfm, hfe⟩
    refine ⟨(fullIrr (UL n w) hH σ).irred, f, hf0, hfm, fun x v => ?_⟩
    have hpx : toFull (UL n w) hH (((cLoc w).comp (locU n w).subtype) x) = p x := Subtype.ext (hp x).symm
    change f (σ.ρ (toFull (UL n w) hH (((cLoc w).comp (locU n w).subtype) x)) v) = _
    rw [hpx]
    exact hfe x v
  · intro K' hlev e hk
    obtain ⟨-, -, hcs, hinv⟩ := hk
    have hKK : ∀ k ∈ K', ∀ x : UL n w, (k.1 * x.1 * 1 : GLw n w) = (k * x).1 := fun k _ x => by simp
    refine ⟨⟨hasCompactSupport_val _ hH e hcs, fun k hk x => ⟨?_, ?_⟩⟩, fun y hy => ⟨?_, ?_⟩⟩
    · have := hinv k.1 ⟨k, hk, rfl⟩ 1 (by simp) x.1
      simpa using this
    · have := hinv 1 (by simp) k.1 ⟨k, hk, rfl⟩ x.1
      simpa using this
    · refine (GlobalTheory.TwTrLin.mem_fixed_iff _ _ _).2 ?_
      rintro _ ⟨k, hk, rfl⟩
      exact (GlobalTheory.TwTrLin.mem_fixed_iff σ.ρ K' y).1 hy k hk
    · have hr := (GlobalTheory.TwTrUnit.twTr_unit E n w K' hlev σ).2.1
      exact levOp_full (UL n w) hH σ.ρ (KL n w) K' hlev.1 hr e hcs
        (fun k hk g => by simpa using hinv 1 (by simp) k hk g) y hy

end GlobalTheory.CompanionTheory.SplitPlace

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitDictionaryHoldsStatement
open PositivityTheory.Rg.BcB.F.Eig
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_dictionary_holds : SplitDict := by
  first | exact @GlobalTheory.CompanionTheory.SplitPlace.splitDict | exact GlobalTheory.CompanionTheory.SplitPlace.splitDict | (intros; apply GlobalTheory.CompanionTheory.SplitPlace.splitDict <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicProjShiftedEmbedding
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicProjShiftedEmbedding
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb

theorem ePG_false_castSucc (i t : ℕ) (a : Fin (i + 1)) :
    ePG (i + 1) (t + 1) ⟨false, Fin.castSucc a⟩ =
      (Fin.castSucc (eGP (i + 1) t ⟨false, a⟩) : Fin ((i + 1) + t + 1 + 1)) := by
  apply Fin.ext
  rw [Fin.val_castSucc, GlobalTheory.CompanionTheory.LeibPhi.blockIndex_false_val]
  first
  | (simp [GlobalTheory.BZMir.Leib.ePG, finSumFinEquiv_symm_apply_castSucc]; done)
  | (have h1 : (finSumFinEquiv.symm (Fin.castSucc a) : Fin (i + 1) ⊕ Fin 1) = Sum.inl a :=
        finSumFinEquiv_symm_apply_castSucc a
     have h2 : GlobalTheory.BZMir.Leib.ePG (i + 1) (t + 1) ⟨false, Fin.castSucc a⟩ =
        finSumFinEquiv (Sum.map finSumFinEquiv (Equiv.refl (Fin 1))
          ((Equiv.sumAssoc (Fin (i + 1)) (Fin (t + 1)) (Fin 1)).symm
            (Sum.map (Equiv.refl (Fin (i + 1))) (Equiv.sumComm (Fin 1) (Fin (t + 1)))
              (Equiv.sumAssoc (Fin (i + 1)) (Fin 1) (Fin (t + 1))
                (Sum.inl (finSumFinEquiv.symm (Fin.castSucc a) : Fin (i + 1) ⊕ Fin 1)))))) := rfl
     rw [h2, h1]
     simp)

theorem ePG_true_eq (i t : ℕ) (b : Fin (t + 1)) :
    ePG (i + 1) (t + 1) ⟨true, b⟩ =
      (Fin.castSucc (eGP (i + 1) t ⟨true, b⟩) : Fin ((i + 1) + t + 1 + 1)) := by
  apply Fin.ext
  rw [Fin.val_castSucc, GlobalTheory.CompanionTheory.LeibPhi.blockIndex_true_val]
  all_goals first | rfl | simp [GlobalTheory.BZMir.Leib.ePG]

section Ent

variable (k : Type) [Field k]

theorem glEmbMat_cc (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (a b : Fin n) :
    glEmbMat k n A (Fin.castSucc a) (Fin.castSucc b) = A a b := by
  first
  | (simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_castSucc]; done)
  | simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_lc (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (b : Fin n) :
    glEmbMat k n A (Fin.last n) (Fin.castSucc b) = 0 := by
  first
  | (simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_last, Fin.lastCases_castSucc]; done)
  | simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_cl (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (a : Fin n) :
    glEmbMat k n A (Fin.castSucc a) (Fin.last n) = 0 := by
  first
  | (simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_last, Fin.lastCases_castSucc]; done)
  | simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_ll (n : ℕ) (A : Matrix (Fin n) (Fin n) k) :
    glEmbMat k n A (Fin.last n) (Fin.last n) = 1 := by
  first
  | (simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_last]; done)
  | simp [GlobalTheory.BZMir.glEmbMat]

end Ent

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sEmb_mem_HPG (i t : ℕ) (h : MirabolicParabolic k (i + 1) t) :
    sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) ∈ HPG k (i + 1) (t + 1) := by
  have hh : ∀ (b : Fin (t + 1)) (a : Fin (i + 1)),
      (((h : Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k) :
        Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k)
        (eGP (i + 1) t ⟨true, b⟩) (eGP (i + 1) t ⟨false, a⟩) = 0 := by
    have hp : ((h : Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k) ∈
        parab k (eGP (i + 1) t) := h.2
    rw [mem_parab_iff] at hp
    intro b a
    exact hp true false b a (by decide)
  have hentry : ∀ p q : Fin ((i + 1) + t + 1 + 1),
      (((GlobalTheory.CompanionTheory.BZPhiPG.sEmb k ((i + 1) + t) (h : GlobalTheory.BZMir.Mir k ((i + 1) + t)) :
          GlobalTheory.BZMir.Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 1 + 1)) k) :
          Matrix (Fin ((i + 1) + t + 1 + 1)) (Fin ((i + 1) + t + 1 + 1)) k) p q =
        GlobalTheory.BZMir.glEmbMat k ((i + 1) + t + 1)
          (((h : GlobalTheory.BZMir.Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k) :
            Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) p q := fun _ _ => rfl
  have hlast : GlobalTheory.BZMir.Leib.ePG (i + 1) (t + 1) ⟨false, Fin.last (i + 1)⟩ =
      Fin.last ((i + 1) + t + 1) := GlobalTheory.BZMir.Leib.ePG_false_last (i + 1) (t + 1)
  show ((GlobalTheory.CompanionTheory.BZPhiPG.sEmb k ((i + 1) + t) (h : GlobalTheory.BZMir.Mir k ((i + 1) + t)) :
      GlobalTheory.BZMir.Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + (t + 1) + 1)) k) ∈
    GlobalTheory.SmGL.parab k (GlobalTheory.BZMir.Leib.ePG (i + 1) (t + 1))
  rw [GlobalTheory.SmGL.mem_parab_iff]
  intro a b x y hba
  cases a <;> cases b
  all_goals first | exact absurd hba (by decide) | skip
  refine (hentry _ _).trans ?_
  obtain ⟨c, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last (y : Fin (i + 1 + 1))
  · rw [GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_true_eq,
      GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_false_castSucc,
      GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_cc]
    exact hh x c
  · rw [GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_true_eq, hlast, GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_cl]

theorem sEmb_HGP_mem_HPG : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (h : MirabolicParabolic k (i + 1) t), ∃ η : HPG k (i + 1) (t + 1), (η : Mir k ((i + 1) + t + 1)) = sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) ∧ pgProj k (i + 1) (t + 1) η = (levi k (i + 1) (gpProj k (i + 1) t h).1, (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)) := by
  intro k _ _ _ _ i t h
  let η : GlobalTheory.BZMir.Leib.HPG k (i + 1) (t + 1) :=
    ⟨GlobalTheory.CompanionTheory.BZPhiPG.sEmb k ((i + 1) + t) (h : GlobalTheory.BZMir.Mir k ((i + 1) + t)),
      GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.sEmb_mem_HPG k i t h⟩
  have hη : ∀ p q : Fin ((i + 1) + (t + 1) + 1),
      ((GlobalTheory.BZMir.Leib.hpgIncl k (i + 1) (t + 1) η : GL (Fin ((i + 1) + (t + 1) + 1)) k) :
          Matrix (Fin ((i + 1) + (t + 1) + 1)) (Fin ((i + 1) + (t + 1) + 1)) k) p q =
        GlobalTheory.BZMir.glEmbMat k ((i + 1) + t + 1)
          (((h : GlobalTheory.BZMir.Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k) :
            Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) p q := fun _ _ => rfl
  have hlast : GlobalTheory.BZMir.Leib.ePG (i + 1) (t + 1) ⟨false, Fin.last (i + 1)⟩ =
      Fin.last ((i + 1) + t + 1) := GlobalTheory.BZMir.Leib.ePG_false_last (i + 1) (t + 1)
  refine ⟨η, rfl, ?_⟩
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    apply Units.ext
    ext p q
    refine (GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.ePG (i + 1) (t + 1))
      (GlobalTheory.BZMir.Leib.hpgIncl k (i + 1) (t + 1) η) false p q).trans ?_
    refine (hη _ _).trans ?_
    have hX : ∀ a b : Fin (i + 1),
        (((GlobalTheory.BZMir.Leib.gpProj k (i + 1) t h).1 : GL (Fin (i + 1)) k) :
            Matrix (Fin (i + 1)) (Fin (i + 1)) k) a b =
          ((h : GlobalTheory.BZMir.Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k)
            (GlobalTheory.BZMir.Leib.eGP (i + 1) t ⟨false, a⟩) (GlobalTheory.BZMir.Leib.eGP (i + 1) t ⟨false, b⟩) :=
      fun a b => GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP (i + 1) t)
        (GlobalTheory.BZMir.Leib.hgpIncl k (i + 1) t h) false a b
    have hL : ∀ a b : Fin (i + 1 + 1),
        (((GlobalTheory.BZMir.levi k (i + 1) (GlobalTheory.BZMir.Leib.gpProj k (i + 1) t h).1 :
            GlobalTheory.BZMir.Mir k (i + 1)) : GL (Fin (i + 1 + 1)) k) : Matrix (Fin (i + 1 + 1)) (Fin (i + 1 + 1)) k) a b =
          GlobalTheory.BZMir.glEmbMat k (i + 1)
            (((GlobalTheory.BZMir.Leib.gpProj k (i + 1) t h).1 : GL (Fin (i + 1)) k) :
              Matrix (Fin (i + 1)) (Fin (i + 1)) k) a b := fun _ _ => rfl
    refine Eq.trans ?_ (hL _ _).symm
    obtain ⟨a, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last (p : Fin (i + 1 + 1)) <;>
    obtain ⟨b, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last (q : Fin (i + 1 + 1))
    · rw [GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_false_castSucc,
        GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_false_castSucc,
        GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_cc, GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_cc]
      exact (hX a b).symm
    · rw [GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_false_castSucc, hlast,
        GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_cl, GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_cl]
    · rw [GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_false_castSucc, hlast,
        GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_lc, GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_lc]
    · rw [hlast, GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_ll, GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_ll]
  · apply Units.ext
    ext p q
    refine (GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.ePG (i + 1) (t + 1))
      (GlobalTheory.BZMir.Leib.hpgIncl k (i + 1) (t + 1) η) true p q).trans ?_
    refine (hη _ _).trans ?_
    refine Eq.trans ?_ (GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP (i + 1) t)
      (GlobalTheory.BZMir.Leib.hgpIncl k (i + 1) t h) true p q).symm
    rw [GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_true_eq, GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.ePG_true_eq,
      GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.glEmbMat_cc]
    rfl

end GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicProjShiftedEmbeddingStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_proj_shifted_embedding : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (h : MirabolicParabolic k (i + 1) t), ∃ η : HPG k (i + 1) (t + 1), (η : Mir k ((i + 1) + t + 1)) = sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) ∧ pgProj k (i + 1) (t + 1) η = (levi k (i + 1) (gpProj k (i + 1) t h).1, (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)) := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.sEmb_HGP_mem_HPG | exact GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.sEmb_HGP_mem_HPG | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb.sEmb_HGP_mem_HPG <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalWittFrame
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalWittFrame
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.KFin.FrameLoc

theorem hR_colV {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin r) E)
    (v : HeightOneSpectrum (𝓞 F)) (i j : Fin r) :
    hR (Fv F v) σ J (colV v X i) (colV v Y j) = inclR (F := F) (Fv F v) ((cT (σ : E →+* E) X * J * Y) i j) := by
  have hs : ∀ t : E, sigR (Fv F v) σ (inclR (F := F) (Fv F v) t) = inclR (F := F) (Fv F v) (σ t) := by
    intro t; simp [sigR, inclR]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, Formalism.UG.hform, colV, JR, Matrix.map_apply, hs, Matrix.mul_apply, cT, Matrix.transpose_apply,
    map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem isFrame_colV : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (v : HeightOneSpectrum (𝓞 F)), IsFrame (hR (Fv F v) σ J) (colV v X) (colV v Y) := by
  intro F E _ _ _ _ _ σ n J r X Y _ _ hW v
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
  · rw [hR_colV, hW.xx]; simp
  · rw [hR_colV, hW.yy]; simp
  · rw [hR_colV, hW.xy, Matrix.one_apply]; split_ifs <;> simp

end GlobalTheory.CompanionTheory.KFin.FrameLoc
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalWittFrameStatement
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_witt_frame : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (v : HeightOneSpectrum (𝓞 F)), IsFrame (hR (Fv F v) σ J) (colV v X) (colV v Y) := by
  first | exact @GlobalTheory.CompanionTheory.KFin.FrameLoc.isFrame_colV | exact GlobalTheory.CompanionTheory.KFin.FrameLoc.isFrame_colV | (intros; apply GlobalTheory.CompanionTheory.KFin.FrameLoc.isFrame_colV <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorCosetSum
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorCosetSum
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.HeckeAvg

theorem hecke_eq_average : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (J : Subgroup (GL (Fin N) k)), IsCompact (J : Set (GL (Fin N) k)) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ (g : GL (Fin N) k) (T : Module.End ℂ (fixed π J)), IsHeckeOp π J g T → ∀ (r : ℕ) (x : Fin r → GL (Fin N) k), 0 < r → (∀ i, x i ∈ J) → (∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ J ⊓ J.map (MulAut.conj g).toMonoidHom) → ∀ v : fixed π J, ((T v : fixed π J) : V) = ((r : ℂ)⁻¹) • ∑ i, π (x i * g) (v : V) := by
  intro k _ _ _ _ N J hJ V _ _ π hπ g T hT r x hr hx hy v
  obtain ⟨E, hE1, -, hE3, -, hE5⟩ := GlobalTheory.T.compact_fixed_vector_projection (GL (Fin N) k) J hJ V π hπ
  have hv : ∀ j ∈ J, π j (v : V) = v := fun j hj => by
    have := v.2 ⟨j, hj⟩
    simpa using this
  have hu : ∀ h ∈ J ⊓ J.map (MulAut.conj g).toMonoidHom, π h (π g (v : V)) = π g (v : V) := by
    intro h hh
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hh.2
    have e : (MulAut.conj g).toMonoidHom j * g = g * j := by simp
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hv j hj]
  have hEu := hE5 (π g (v : V)) (J ⊓ J.map (MulAut.conj g).toMonoidHom) inf_le_left hu r x hr hx hy
  have hsum : ∑ i, π (x i) (π g (v : V)) = ∑ i, π (x i * g) (v : V) :=
    Finset.sum_congr rfl fun i _ => by rw [map_mul, Module.End.mul_apply]
  rw [← hsum, ← hEu]
  have hw : ((T v : fixed π J) : V) - E (π g (v : V)) ∈ fixed π J :=
    Submodule.sub_mem _ (T v).2 (hE1 _)
  have h0 := GlobalTheory.T.fixed_vector_zero_of_dual (GL (Fin N) k) J hJ V π hπ _ hw (by
    intro l hl
    have h1 : l (E (π g (v : V))) = l (π g (v : V)) := by
      have := hE3 l hl
      exact LinearMap.congr_fun this _
    rw [map_sub, h1, hT v l hl, sub_self])
  exact sub_eq_zero.mp h0

end GlobalTheory.CompanionTheory.HeckeAvg
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorCosetSumStatement
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_operator_coset_sum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (J : Subgroup (GL (Fin N) k)), IsCompact (J : Set (GL (Fin N) k)) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ (g : GL (Fin N) k) (T : Module.End ℂ (fixed π J)), IsHeckeOp π J g T → ∀ (r : ℕ) (x : Fin r → GL (Fin N) k), 0 < r → (∀ i, x i ∈ J) → (∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ J ⊓ J.map (MulAut.conj g).toMonoidHom) → ∀ v : fixed π J, ((T v : fixed π J) : V) = ((r : ℂ)⁻¹) • ∑ i, π (x i * g) (v : V) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeAvg.hecke_eq_average | exact GlobalTheory.CompanionTheory.HeckeAvg.hecke_eq_average | (intros; apply GlobalTheory.CompanionTheory.HeckeAvg.hecke_eq_average <;> assumption)
end
end
