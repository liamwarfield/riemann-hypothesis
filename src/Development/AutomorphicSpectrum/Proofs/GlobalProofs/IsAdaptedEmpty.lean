module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfSlices
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CapelliLowestGelfandConj

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsAdaptedEmpty
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore

def IsAdapted {D : D7} (V : HSp D) {m : ℕ} (X Y : Matrix (Fin V.rank) (Fin m) D.host.E) (T : Finset (Fin m))
    (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) : Prop :=
  ∀ τ, ∃ (k : Formalism.REAL.KG (ε τ)) (S : Set (Fin V.rank)),
    Submodule.span ℂ (Set.range (fun i : upTo T => (fr τ *ᵥ fun j => tauE D τ (X j i))) ∪
        Set.range (fun i : upTo T => (fr τ *ᵥ fun j => tauE D τ (Y j i)))) =
      (Submodule.span ℂ (Set.range fun j : S => (Pi.single (j : Fin V.rank) (1 : ℂ) : Fin V.rank → ℂ))).map
        (Formalism.REAL.toMK k).mulVecLin

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.GelfandEigenvalueCasimirScalar
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.GelfandEigenvalueCasimirScalar
noncomputable section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.CompanionTheory.DerGlRel

private theorem commutator_eq_of_glRel {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M)
    (hL : Formalism.REAL.GlRel fun a b : Fin n => L (Matrix.single a b 1))
    (Z W : Matrix (Fin n) (Fin n) ℂ) :
    L Z * L W - L W * L Z = L (Z * W - W * Z) := by
  classical
  have hs : ∀ (i j : Fin n) (x : ℂ),
      (Matrix.single i j x : Matrix (Fin n) (Fin n) ℂ) = x • Matrix.single i j 1 := by
    intro i j x
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  have base : ∀ a b c d : Fin n,
      L (Matrix.single a b 1) * L (Matrix.single c d 1) -
          L (Matrix.single c d 1) * L (Matrix.single a b 1) =
        L (Matrix.single a b 1 * Matrix.single c d 1 -
          Matrix.single c d 1 * Matrix.single a b 1) := by
    intro a b c d
    have h := hL a b c d
    simp only at h
    rw [h, map_sub]
    congr 1
    · by_cases h' : b = c
      · subst h'
        rw [if_pos rfl, Matrix.single_mul_single_same, mul_one]
      · rw [if_neg h']
        simp [Matrix.single_mul_single_of_ne, h']
    · by_cases h' : d = a
      · subst h'
        rw [if_pos rfl, Matrix.single_mul_single_same, mul_one]
      · rw [if_neg h']
        simp [Matrix.single_mul_single_of_ne, h']
  have key1 : ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n),
      L Z * L (Matrix.single c d 1) - L (Matrix.single c d 1) * L Z =
        L (Z * Matrix.single c d 1 - Matrix.single c d 1 * Z) := by
    intro Z c d
    refine Matrix.induction_on' Z ?_ ?_ ?_
    · simp
    · intro p q hp hq
      rw [show (p + q) * Matrix.single c d 1 - Matrix.single c d 1 * (p + q) =
          (p * Matrix.single c d 1 - Matrix.single c d 1 * p) +
            (q * Matrix.single c d 1 - Matrix.single c d 1 * q) by noncomm_ring]
      simp only [map_add (f := _)]
      rw [← hp, ← hq]
      noncomm_ring
    · intro i j x
      rw [hs i j x]
      simp only [smul_mul_assoc, mul_smul_comm, ← smul_sub, map_smul, base]
  refine Matrix.induction_on' W ?_ ?_ ?_
  · simp
  · intro p q hp hq
    rw [show Z * (p + q) - (p + q) * Z = (Z * p - p * Z) + (Z * q - q * Z) by noncomm_ring]
    simp only [map_add (f := _)]
    rw [← hp, ← hq]
    noncomm_ring
  · intro i j x
    rw [hs i j x]
    simp only [smul_mul_assoc, mul_smul_comm, ← smul_sub, map_smul, key1]

theorem glRel_derEnd_family : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    (M : Fin V.rank → Fin V.rank → Matrix (Fin V.rank) (Fin V.rank) ℂ), Formalism.REAL.GlRel M →
    Formalism.REAL.GlRel (fun i j => GlobalTheory.Mem.RealTranslate.derEnd hθ τ (M i j)) := by
  intro D θ hθ V τ M hM
  unfold Formalism.REAL.GlRel at hM ⊢
  dsimp only at hM ⊢
  intro a b c d
  have h1 := commutator_eq_of_glRel (GlobalTheory.Mem.RealTranslate.derEnd (V := V) hθ τ)
    (GlobalTheory.Mem.Lift.glRel_derEnd hθ V τ) (M a b) (M c d)
  rw [h1, hM a b c d, map_sub]
  split_ifs <;> simp

end GlobalTheory.CompanionTheory.DerGlRel

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.GelfandEigenvalueCasimirScalarStatement
open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gl_relations_derivative_preserved : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    (M : Fin V.rank → Fin V.rank → Matrix (Fin V.rank) (Fin V.rank) ℂ), Formalism.REAL.GlRel M →
    Formalism.REAL.GlRel (fun i j => GlobalTheory.Mem.RealTranslate.derEnd hθ τ (M i j)) := by
  first | exact @GlobalTheory.CompanionTheory.DerGlRel.glRel_derEnd_family | exact GlobalTheory.CompanionTheory.DerGlRel.glRel_derEnd_family | (intros; apply GlobalTheory.CompanionTheory.DerGlRel.glRel_derEnd_family <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.OrthogonalSubspaceWittFrameExtension
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.OrthogonalSubspaceWittFrameExtension
open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.CompanionTheory.Hypotheses₂.AdaptedBasis

theorem exists_basis_of_duality {E : Type} [Field E] {n m : ℕ} (X Y : Matrix (Fin n) (Fin m) E)
    (A B : Matrix (Fin m) (Fin n) E) (hAX : A * X = 1) (hAY : A * Y = 0) (hBX : B * X = 0) (hBY : B * Y = 1) :
    2 * m ≤ n ∧ ∃ C : GL (Fin n) E,
      (∀ (i : Fin n) (j : Fin m), i.val = j.val → ∀ k, C.1 k i = X k j) ∧
      (∀ (i : Fin n) (j : Fin m), i.val + j.val + 1 = n → ∀ k, C.1 k i = Y k j) ∧
      (∀ i : Fin n, m ≤ i.val → i.val + m < n →
        A *ᵥ (fun k => C.1 k i) = 0 ∧ B *ᵥ (fun k => C.1 k i) = 0) := by
  classical
  set P : Matrix (Fin m ⊕ Fin m) (Fin n) E := Matrix.fromRows A B with hP
  have hPQ : P * Matrix.fromCols X Y = 1 := by
    rw [hP, Matrix.fromRows_mul_fromCols, hAX, hAY, hBX, hBY, Matrix.fromBlocks_one]
  have hsurj : Function.Surjective P.mulVecLin := fun u => ⟨Matrix.fromCols X Y *ᵥ u, by
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]⟩
  have hrk := LinearMap.finrank_range_add_finrank_ker P.mulVecLin
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at hrk
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at hrk
  have hmem : ∀ k, k ∈ LinearMap.ker P.mulVecLin ↔ A *ᵥ k = 0 ∧ B *ᵥ k = 0 := by
    intro k
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hP, Matrix.fromRows_mulVec]
    constructor
    · intro h
      exact ⟨funext fun i => congrFun h (Sum.inl i), funext fun i => congrFun h (Sum.inr i)⟩
    · rintro ⟨h1, h2⟩
      funext i
      cases i <;> simp [h1, h2]
  set K := LinearMap.ker P.mulVecLin with hK
  let b := Module.finBasis E K
  have hle : 2 * m ≤ n := by omega
  refine ⟨hle, ?_⟩
  let col : Fin n → Fin n → E := fun i =>
    if h1 : i.val < m then fun k => X k ⟨i.val, h1⟩
    else if h2 : i.val + m < n then (b ⟨i.val - m, by have := i.2; omega⟩ : K).1
    else fun k => Y k ⟨n - 1 - i.val, by have := i.2; omega⟩
  let C0 : Matrix (Fin n) (Fin n) E := Matrix.of fun k i => col i k
  have hcol : ∀ i, col i ∈ LinearMap.range C0.mulVecLin := fun i =>
    ⟨Pi.single i 1, by
      funext k
      simp [Matrix.mulVecLin_apply, C0]⟩
  have hX : ∀ (j : Fin m), (fun k => X k j) ∈ LinearMap.range C0.mulVecLin := by
    intro j
    have hi : j.val < n := by have := j.2; omega
    have := hcol ⟨j.val, hi⟩
    simpa [col] using this
  have hY : ∀ (j : Fin m), (fun k => Y k j) ∈ LinearMap.range C0.mulVecLin := by
    intro j
    have hj := j.2
    have hi : n - 1 - j.val < n := by omega
    have := hcol ⟨n - 1 - j.val, hi⟩
    have e1 : ¬ (n - 1 - j.val < m) := by omega
    have e2 : ¬ (n - 1 - j.val + m < n) := by omega
    have e3 : n - 1 - (n - 1 - j.val) = j.val := by omega
    simpa [col, e1, e2, e3] using this
  have hb : ∀ (t : Fin (Module.finrank E K)), (b t : K).1 ∈ LinearMap.range C0.mulVecLin := by
    intro t
    have ht := t.2
    have hi : t.val + m < n := by omega
    have := hcol ⟨t.val + m, hi⟩
    have e1 : ¬ (t.val + m < m) := by omega
    have e2 : t.val + m + m < n := by omega
    simpa [col, e1, e2] using this
  have hKr : ∀ k : K, k.1 ∈ LinearMap.range C0.mulVecLin := by
    intro k
    rw [← b.sum_repr k]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (hb t)
  have hmv : ∀ (Z : Matrix (Fin n) (Fin m) E), (∀ j : Fin m, (fun k => Z k j) ∈ LinearMap.range C0.mulVecLin) →
      ∀ u, Z *ᵥ u ∈ LinearMap.range C0.mulVecLin := by
    intro Z hZ u
    have : Z *ᵥ u = ∑ j, u j • (fun k => Z k j) := by
      funext k
      simp [Matrix.mulVec, dotProduct, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (hZ t)
  have hs : Function.Surjective C0.mulVec := by
    intro v
    have hk : v - X *ᵥ (A *ᵥ v) - Y *ᵥ (B *ᵥ v) ∈ K := by
      have eAX : ∀ w, A *ᵥ (X *ᵥ w) = w := fun w => by rw [Matrix.mulVec_mulVec, hAX, Matrix.one_mulVec]
      have eAY : ∀ w, A *ᵥ (Y *ᵥ w) = 0 := fun w => by rw [Matrix.mulVec_mulVec, hAY, Matrix.zero_mulVec]
      have eBX : ∀ w, B *ᵥ (X *ᵥ w) = 0 := fun w => by rw [Matrix.mulVec_mulVec, hBX, Matrix.zero_mulVec]
      have eBY : ∀ w, B *ᵥ (Y *ᵥ w) = w := fun w => by rw [Matrix.mulVec_mulVec, hBY, Matrix.one_mulVec]
      rw [hK, hmem]
      constructor
      · simp only [Matrix.mulVec_sub, eAX, eAY, sub_self, sub_zero]
      · simp only [Matrix.mulVec_sub, eBX, eBY, sub_self, sub_zero]
    have h3 := hKr ⟨_, hk⟩
    have h1 := hmv X hX (A *ᵥ v)
    have h2 := hmv Y hY (B *ᵥ v)
    have : v = (v - X *ᵥ (A *ᵥ v) - Y *ᵥ (B *ᵥ v)) + X *ᵥ (A *ᵥ v) + Y *ᵥ (B *ᵥ v) := by abel
    have h4 := Submodule.add_mem _ (Submodule.add_mem _ h3 h1) h2
    simp only at h4
    rw [← this] at h4
    exact h4
  have hu : IsUnit C0 := Matrix.mulVec_surjective_iff_isUnit.1 hs
  obtain ⟨C, hC⟩ := hu
  have hCk : ∀ k i, C.1 k i = col i k := fun k i => by rw [hC]; rfl
  refine ⟨C, ?_, ?_, ?_⟩
  · intro i j h k
    have h1 : i.val < m := h ▸ j.2
    rw [hCk]
    simp only [col, dif_pos h1]
    congr 1
    exact Fin.ext h
  · intro i j h k
    have hj := j.2
    have e1 : ¬ (i.val < m) := by omega
    have e2 : ¬ (i.val + m < n) := by omega
    rw [hCk]
    simp only [col, dif_neg e1, dif_neg e2]
    congr 1
    exact Fin.ext (by simp; omega)
  · intro i h1 h2
    have e1 : ¬ (i.val < m) := by omega
    have : (fun k => C.1 k i) = (b ⟨i.val - m, by have := i.2; omega⟩ : K).1 := by
      funext k
      rw [hCk]
      simp only [col, dif_neg e1, dif_pos h2]
    rw [this]
    exact (hmem _).1 (b _).2

theorem exists_isAdapted : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    IsWittFrame D.sp.cm.sig V.gram X Y → ∃ C : GL (Fin V.rank) D.host.E, GlobalTheory.BlockForms.IsAdapted D.sp.cm.sig V.gram X Y C := by
  intro D V m X Y hW
  have hyx := GlobalTheory.WittFrame.yx_eq_one D V m X Y hW
  have hxx := hW.xx
  have hyy := hW.yy
  have hxy := hW.xy
  obtain ⟨hle, C, h1, h2, h3⟩ := exists_basis_of_duality X Y
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram)
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram) hyx hyy hxx hxy
  exact ⟨C, ⟨hle, h1, h2, fun i a b => (h3 i a b).2, fun i a b => (h3 i a b).1⟩⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.AdaptedBasis
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.OrthogonalSubspaceWittFrameExtensionStatement
open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adapted_witt_basis : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    IsWittFrame D.sp.cm.sig V.gram X Y → ∃ C : GL (Fin V.rank) D.host.E, GlobalTheory.BlockForms.IsAdapted D.sp.cm.sig V.gram X Y C := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.AdaptedBasis.exists_isAdapted | exact GlobalTheory.CompanionTheory.Hypotheses₂.AdaptedBasis.exists_isAdapted | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.AdaptedBasis.exists_isAdapted <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AutomorphicFunctionRestrictBlock
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AutomorphicFunctionRestrictBlock
noncomputable section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.CompanionTheory.CoreGL.CapScalar

def linOf {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A where
  toFun Z := ∑ a, ∑ b, Z a b • E a b
  map_add' Z W := by simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c Z := by
    simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

theorem linOf_single {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (a b : Fin n) :
    linOf E (Matrix.single a b 1) = E a b := by
  classical
  change ∑ i, ∑ j, (Matrix.single a b (1 : ℂ)) i j • E i j = E a b
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro j _ hj; simp [Matrix.single_apply, Ne.symm hj]
  · simp
  · intro i _ hi; exact Finset.sum_eq_zero fun j _ => by simp [Matrix.single_apply, Ne.symm hi]
  · simp

theorem glRel_linOf {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A} (hE : Formalism.REAL.GlRel E)
    {M : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ} (hM : Formalism.REAL.GlRel M) :
    Formalism.REAL.GlRel fun i j => linOf E (M i j) := by
  have h : Formalism.REAL.GlRel (fun i j => linOf E (Matrix.single i j 1)) := by
    simpa only [linOf_single] using hE
  intro a b c d
  simp only
  rw [GlobalTheory.CapelliLowest.lie_of_glRel (linOf E) h, hM a b c d, map_sub, apply_ite (linOf E), apply_ite (linOf E), map_zero]

theorem qdet_commute {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A} (hE : Formalism.REAL.GlRel E)
    {M : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ} (hM : Formalism.REAL.GlRel M)
    (hs : Submodule.span ℂ (Set.range fun p : Fin n × Fin n => M p.1 p.2) = ⊤) (v : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    linOf E Z * Formalism.REAL.qdet (fun i j => linOf E (M i j)) v = Formalism.REAL.qdet (fun i j => linOf E (M i j)) v * linOf E Z := by
  have hZ : Z ∈ Submodule.span ℂ (Set.range fun p : Fin n × Fin n => M p.1 p.2) := hs ▸ Submodule.mem_top
  induction hZ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact (Formalism.REAL.qDetCentral A n _ (glRel_linOf hE hM) v p.1 p.2).symm
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), add_mul, mul_add, hx, hy]
  | smul c x _ hx => rw [map_smul, smul_mul_assoc, mul_smul_comm, hx]

end GlobalTheory.CompanionTheory.CoreGL.CapScalar

namespace GlobalTheory.CompanionTheory.CoreGL

open GlobalTheory.CompanionTheory.CoreGL.CapScalar GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies

attribute [local instance 100] LieRing.ofAssociativeRing

theorem qdet_scalar_of_gelf : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    (M : Fin V.rank → Fin V.rank → Matrix (Fin V.rank) (Fin V.rank) ℂ), Formalism.REAL.GlRel M →
    Submodule.span ℂ (Set.range fun p : Fin V.rank × Fin V.rank => M p.1 p.2) = ⊤ → ∀ (c : ℕ → ℂ) (v : ℂ), ∃ s : ℂ,
      ∀ f : GlobalTheory.Mem.AutSpace.SmFun θ V, (∀ k, gelf θ V τ k f.1 = c k • f.1) →
        Formalism.REAL.qdet (fun i j => GlobalTheory.Mem.RealTranslate.derEnd hθ τ (M i j)) v f = s • f := by
  intro D θ hθ V τ M hM hsp c v
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  obtain ⟨P, Q, hPQ, h⟩ := GlobalTheory.T.unitary_lie_generators_rep _ _ (R.1 τ).1 (R.1 τ).2
  obtain ⟨h1, h2⟩ := h (EnvAt V τ) (fun X => UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X))
    (fun X Y => by rw [TensorProduct.tmul_add, map_add (f := _)])
    (fun c X => by
      rw [← map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
      simp)
    (fun X Y Z hZ => by
      have : Z = ⁅X, Y⁆ := Subtype.ext hZ
      rw [this, ← Ring.lie_def, ← LieHom.map_lie, LieAlgebra.ExtendScalars.bracket_tmul, one_mul])
  set E : Fin V.rank → Fin V.rank → EnvAt V τ := fun a b =>
    UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] P a b) + Complex.I • UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] Q a b) with hEdef

  have hcomm := qdet_commute h1 hM hsp v
  set z : EnvAt V τ := Formalism.REAL.qdet (fun i j => linOf E (M i j)) v with hz
  have hι : ∀ X : LieAt V τ, UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X) * z = z * UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X) := by
    intro X
    have hX := h2 X
    generalize UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X) = y at hX
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      have := hcomm (Matrix.single p.1 p.2 1)
      rwa [linOf_single] at this
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]
    | smul c x _ hx => rw [smul_mul_assoc, mul_smul_comm, hx]
  obtain ⟨cg, hc, hg⟩ := exists_gelf R τ
  have hcen : z ∈ Subalgebra.center ℂ (EnvAt V τ) := by
    rw [Subalgebra.mem_center_iff]
    intro u
    have : u ∈ Subalgebra.centralizer ℂ ({z} : Set (EnvAt V τ)) := by
      obtain ⟨w, rfl⟩ := GlobalTheory.T.enveloping_map_surjective D V τ u
      refine Subalgebra.sum_mem _ fun l _ => Subalgebra.smul_mem _ (Subalgebra.list_prod_mem _ fun x hx => ?_) _
      obtain ⟨X, -, rfl⟩ := List.mem_map.1 hx
      rw [Subalgebra.mem_centralizer_iff]
      rintro _ rfl
      exact (hι X).symm
    rw [Subalgebra.mem_centralizer_iff] at this
    exact (this z rfl).symm

  have key : ∀ y ∈ Algebra.adjoin ℂ (Set.range cg), ∃ s : ℂ, ∀ ψ : SmF θ V,
      (∀ k, gelf θ V τ k ψ.1 = c k • ψ.1) → envRep R τ y ψ = s • ψ := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact ⟨c k, fun ψ e => Subtype.ext ((hg k ψ).symm.trans (e k))⟩
    | algebraMap r => exact ⟨r, fun ψ _ => by rw [AlgHom.commutes]; rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs⟩ := hx
      obtain ⟨t, ht⟩ := hy
      exact ⟨s + t, fun ψ e => by rw [map_add (f := _), LinearMap.add_apply, hs ψ e, ht ψ e, add_smul]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨s, hs⟩ := hx
      obtain ⟨t, ht⟩ := hy
      exact ⟨s * t, fun ψ e => by
        rw [map_mul, Module.End.mul_apply, ht ψ e, map_smul, hs ψ e, smul_smul, mul_comm]⟩
  rw [hc] at hcen
  obtain ⟨s, hs⟩ := key z hcen

  have e : GlobalTheory.Mem.AutSpace.SmFun θ V = SmF θ V := Submodule.ext fun φ => smooth_iff R φ
  let T := (LinearEquiv.ofEq _ _ e).conjAlgEquiv ℂ
  have k0 : ∀ a b, T (GlobalTheory.Mem.RealTranslate.derEnd (V := V) hθ τ (Matrix.single a b 1)) = envRep R τ (E a b) := by
    intro a b
    rw [hEdef]
    simp only [map_add (f := _), map_smul, envRep_ι]
    refine LinearMap.ext fun φ => Subtype.ext ?_
    change RderC θ V τ (Matrix.single a b 1) φ.1 = _
    rw [RderC, conjAt, ← (hPQ _ _).1, ← (hPQ _ _).2, Rder_eq R, Rder_eq R]
    rfl
  have k1 : ∀ Z, T (GlobalTheory.Mem.RealTranslate.derEnd (V := V) hθ τ Z) = envRep R τ (linOf E Z) := by
    intro Z
    conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
    change _ = envRep R τ (∑ a, ∑ b, Z a b • E a b)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have : Matrix.single a b (Z a b) = Z a b • Matrix.single a b (1 : ℂ) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [this, map_smul, map_smul, map_smul, k0]
  have k2 : T (Formalism.REAL.qdet (fun i j => GlobalTheory.Mem.RealTranslate.derEnd hθ τ (M i j)) v) = envRep R τ z := by
    have a1 := GlobalTheory.CompanionTheory.CapelliMap.map_qdet T.toAlgHom (fun i j => GlobalTheory.Mem.RealTranslate.derEnd (V := V) hθ τ (M i j)) v
    have a2 := GlobalTheory.CompanionTheory.CapelliMap.map_qdet (envRep R τ) (fun i j => linOf E (M i j)) v
    change T _ = _ at a1
    rw [a1, hz, a2]
    congr 1
    funext i j
    exact k1 (M i j)
  refine ⟨s, fun f hf => ?_⟩
  have k3 := congrArg (fun S : Module.End ℂ (SmF θ V) => (S (LinearEquiv.ofEq _ _ e f)).1) k2
  have k4 := hs (LinearEquiv.ofEq _ _ e f) hf
  exact Subtype.ext (k3.trans (congrArg Subtype.val k4))

end GlobalTheory.CompanionTheory.CoreGL

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AutomorphicFunctionRestrictBlockStatement
open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_eigenvalue_casimir_scalar : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    (M : Fin V.rank → Fin V.rank → Matrix (Fin V.rank) (Fin V.rank) ℂ), Formalism.REAL.GlRel M →
    Submodule.span ℂ (Set.range fun p : Fin V.rank × Fin V.rank => M p.1 p.2) = ⊤ → ∀ (c : ℕ → ℂ) (v : ℂ), ∃ s : ℂ,
      ∀ f : GlobalTheory.Mem.AutSpace.SmFun θ V, (∀ k, gelf θ V τ k f.1 = c k • f.1) →
        Formalism.REAL.qdet (fun i j => GlobalTheory.Mem.RealTranslate.derEnd hθ τ (M i j)) v f = s • f := by
  first | exact @GlobalTheory.CompanionTheory.CoreGL.qdet_scalar_of_gelf | exact GlobalTheory.CompanionTheory.CoreGL.qdet_scalar_of_gelf | (intros; apply GlobalTheory.CompanionTheory.CoreGL.qdet_scalar_of_gelf <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermParabolicKFinite
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermParabolicKFinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin.TypeKeep

open MeasureTheory GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin

theorem finiteDimensional_coeffs {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  let T : Module.Dual ℂ W →ₗ[ℂ] W →ₗ[ℂ] (K → ℂ) :=
    LinearMap.mk₂ ℂ (fun ℓ w => fun k => ℓ (ρ k w))
      (fun ℓ₁ ℓ₂ w => by funext k; simp)
      (fun a ℓ w => by funext k; simp)
      (fun ℓ w₁ w₂ => by funext k; simp)
      (fun a ℓ w => by funext k; simp)
  have hle : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ LinearMap.range (TensorProduct.lift T) := by
    unfold GlobalTheory.Published.AutFin.coeffSpan
    rw [Submodule.span_le]
    rintro f ⟨ℓ, w, rfl⟩
    exact ⟨ℓ ⊗ₜ w, by simp [T]⟩
  exact Submodule.finiteDimensional_of_le hle

theorem exists_interp {K : Type} (A : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ A] :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → K) (a : ι → K → ℂ), (∀ i, a i ∈ A) ∧
      ∀ f ∈ A, ∀ k, f k = ∑ i, f (p i) * a i k := by
  classical
  let E : K → Module.Dual ℂ A := fun k => (LinearMap.proj k).comp A.subtype
  have htop : Submodule.span ℂ (Set.range E) = ⊤ := by
    have h0 : (Submodule.span ℂ (Set.range E)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro f hf
      rw [Submodule.mem_dualCoannihilator] at hf
      rw [Submodule.mem_bot]
      apply Subtype.ext
      funext k
      have h := hf (E k) (Submodule.subset_span ⟨k, rfl⟩)
      simpa [E] using h
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range E)), h0,
      Submodule.dualAnnihilator_bot]
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent ℂ (Set.range E)
  have hbtop : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : b → Module.Dual ℂ A)) := by
    rw [Subtype.range_coe, hbspan, htop]
  let B : Module.Basis b ℂ (Module.Dual ℂ A) := Module.Basis.mk hbli hbtop
  haveI : Finite b := hbli.finite
  letI : Fintype b := Fintype.ofFinite b
  have hp : ∀ i : b, ∃ k, E k = (i : Module.Dual ℂ A) := fun i => hbsub i.2
  choose p hpE using hp
  let a : b → A := fun i => (Module.evalEquiv ℂ A).symm (B.coord i)
  refine ⟨b, inferInstance, p, fun i k => (a i : K → ℂ) k, fun i => (a i).2, ?_⟩
  intro f hf k
  have key := B.sum_dual_apply_smul_coord (Module.evalEquiv ℂ A ⟨f, hf⟩)
  have key2 : (⟨f, hf⟩ : A) = ∑ i, (B i ⟨f, hf⟩) • a i := by
    apply (Module.evalEquiv ℂ A).injective
    conv_lhs => rw [← key]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul, a, LinearEquiv.apply_symm_apply, Module.evalEquiv_apply, Module.Dual.eval_apply]
  have hk := congrArg (fun g : A => (g : K → ℂ) k) key2
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hk
  rw [hk]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hBi : B i = (i : Module.Dual ℂ A) := by simp [B]
  rw [hBi, ← hpE i]
  rfl

theorem hasTypeAt_of_isConstAlong : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ S T : Finset (Fin m), S ⊆ T → ∀ (τ : D.what₂.Tau) (e : Fin V.rank → Bool) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Formalism.REAL.KG e) W) (φ c : GA D V → ℂ), IsSmModOn D.sp.cm.sig V.gram (leftSub V X Y S : Set (GA D V)) φ → HasTypeAt θ V τ e P ρ φ → IsConstAlong D.sp.cm.sig V.gram X T φ c → HasTypeAt θ V τ e P ρ c := by
  intro D θ V m X Y hW S T hST τ e P W _ _ _ ρ φ c hφ hty hc
  classical
  have hst := GlobalTheory.StdPar.constAlong_cocompact_unique_stages (GlobalTheory.DefiniteQuotient.cmExt D)
    (GlobalTheory.DefiniteQuotient.gram_hermND V) hW
  obtain ⟨hcoc, μ, 𝓕, hμ, h𝓕, h1⟩ := hst.1 T
  haveI := hμ
  have hcI := hc μ 𝓕 hμ h𝓕 h1
  haveI := finiteDimensional_coeffs ρ
  obtain ⟨ι, _, p, a, ha, hrep⟩ := exists_interp (GlobalTheory.Published.AutFin.coeffSpan ρ)
  have hcoc' : GlobalTheory.Cusp.Cocompact (GQ V ⊓ unip D.sp.cm.sig V.gram X T) (unip D.sp.cm.sig V.gram X T) := by
    obtain ⟨K, hK, hKc⟩ := hcoc
    refine ⟨K, hK, fun n => ?_⟩
    obtain ⟨γ, hγ, hγK⟩ := hKc n
    refine ⟨γ, ?_, hγK⟩
    rw [Subgroup.inf_subgroupOf_right]
    exact hγ
  have h𝓕' : IsFundamentalDomain ((GQ V ⊓ unip D.sp.cm.sig V.gram X T).subgroupOf
      (unip D.sp.cm.sig V.gram X T)) 𝓕 μ := by
    rw [Subgroup.inf_subgroupOf_right]
    exact h𝓕
  haveI hdQ : DiscreteTopology ↥(GlobalTheory.AdelicU.ratPts D.sp.cm.sig V.gram) := inferInstance
  haveI hdisc : DiscreteTopology ↥(GQ V ⊓ unip D.sp.cm.sig V.gram X T) :=
    DiscreteTopology.of_subset hdQ (fun y hy => hy.1)
  have hint : ∀ g : GA D V, IntegrableOn (fun u : unip D.sp.cm.sig V.gram X T => φ ((u : GA D V) * g)) 𝓕 μ := by
    intro g
    exact GlobalTheory.Cusp.Cocompact.integrableOn hcoc' h𝓕'
      (fun γ hγ g' => hφ.left γ (ratPts_unip_le_leftSub D V m X Y hW S T hST hγ) g') hφ.cont g
  intro x
  have hfun : (fun k => c (x * kAt θ V τ e P k)) = ∑ i, c (x * kAt θ V τ e P (p i)) • a i := by
    funext k
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hcI (x * kAt θ V τ e P k)]
    have hpt : ∀ u : unip D.sp.cm.sig V.gram X T, φ ((u : GA D V) * (x * kAt θ V τ e P k)) =
        ∑ i, φ ((u : GA D V) * (x * kAt θ V τ e P (p i))) * a i k := by
      intro u
      have h := hrep _ (hty ((u : GA D V) * x)) k
      simpa [mul_assoc] using h
    simp_rw [hpt]
    rw [integral_finsetSum _ (fun i _ => Integrable.mul_const (hint _) _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_mul_const, hcI]
  rw [hfun]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (ha i)

end GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin.TypeKeep
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermParabolicKFiniteStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_parabolic_K_finite : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ S T : Finset (Fin m), S ⊆ T → ∀ (τ : D.what₂.Tau) (e : Fin V.rank → Bool) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Formalism.REAL.KG e) W) (φ c : GA D V → ℂ), IsSmModOn D.sp.cm.sig V.gram (leftSub V X Y S : Set (GA D V)) φ → HasTypeAt θ V τ e P ρ φ → IsConstAlong D.sp.cm.sig V.gram X T φ c → HasTypeAt θ V τ e P ρ c := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin.TypeKeep.hasTypeAt_of_isConstAlong | exact GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin.TypeKeep.hasTypeAt_of_isConstAlong | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin.TypeKeep.hasTypeAt_of_isConstAlong <;> assumption)
end
end
