module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockHarmonicRepresentative
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmMulRightOfIsCMExt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsProductDataCopiesTrivialisationValuation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrFractionFieldRingEquivEqUnitMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousSplitTorusSection

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarmonicHighestWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicMemFiniteDimensionalCompactStable
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicMemFiniteDimensionalCompactStable
noncomputable section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.FockAlg.HarmStable MvPolynomial

namespace GlobalTheory.FockAlg.FinHarm

variable {σ : Type}

def lowDeg (σ : Type) (N : ℕ) : Submodule ℂ (MvPolynomial σ ℂ) :=
  ⨆ d : Fin (N + 1), homog σ d

instance [Finite σ] (N : ℕ) : FiniteDimensional ℂ (lowDeg σ N) := by
  haveI : ∀ d : ℕ, FiniteDimensional ℂ (homog σ d) := fun d =>
    Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg _ _ _)
  unfold lowDeg
  infer_instance

theorem mem_lowDeg_self (P : MvPolynomial σ ℂ) : P ∈ lowDeg σ P.totalDegree := by
  obtain ⟨N, hN⟩ : ∃ N, N = P.totalDegree := ⟨_, rfl⟩
  rw [← hN]
  have hs := sum_homogeneousComponent P
  rw [← hN] at hs
  rw [← hs]
  refine Submodule.sum_mem _ fun e he => ?_
  have he' : e < N + 1 := Finset.mem_range.1 he
  exact Submodule.mem_iSup_of_mem (⟨e, he'⟩ : Fin (N + 1))
    (homogeneousComponent_mem e P)

theorem DegZero.map_lowDeg {K : Module.End ℂ (MvPolynomial σ ℂ)} (hK : DegZero K) (N : ℕ)
    {P : MvPolynomial σ ℂ} (hP : P ∈ lowDeg σ N) : K P ∈ lowDeg σ N := by
  have hle : lowDeg σ N ≤ (lowDeg σ N).comap K :=
    iSup_le fun d x hx => Submodule.mem_comap.2 (Submodule.mem_iSup_of_mem d (hK d x hx))
  exact hle hP

end GlobalTheory.FockAlg.FinHarm

namespace GlobalTheory.FockAlg

open FinHarm

theorem fin_harm : ∀ (P Q R S : ℕ) (h : Pol P Q R S), h ∈ harm2 P Q R S →
    ∃ H0 : Submodule ℂ (Pol P Q R S), FiniteDimensional ℂ H0 ∧ h ∈ H0 ∧
      (∀ v ∈ H0, v ∈ harm2 P Q R S) ∧ KStable (fockAct1 P Q R S) H0 ∧
      KStable (fockAct2 P Q R S) H0 := by
  intro P Q R S h hh
  have hh' : h ∈ sub2 P Q R S := by
    rw [← SetLike.mem_coe, coe_fockHarmonicsSecondMemberSubmodule]; exact hh
  refine ⟨sub2 P Q R S ⊓ lowDeg _ h.totalDegree, ?_, ⟨hh', mem_lowDeg_self h⟩, ?_, ?_, ?_⟩
  · exact Submodule.finiteDimensional_of_le inf_le_right
  · intro v hv
    rw [← coe_fockHarmonicsSecondMemberSubmodule]; exact hv.1
  · intro Y hY w hw
    exact ⟨fockHarmonicsSecondMember_kStable.1 Y hY w hw.1, DegZero.map_lowDeg (degZero_fockAct1 hY) _ hw.2⟩
  · intro Y hY w hw
    exact ⟨fockHarmonicsSecondMember_kStable.2 Y hY w hw.1, DegZero.map_lowDeg (degZero_fockAct2 hY) _ hw.2⟩

end GlobalTheory.FockAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicMemFiniteDimensionalCompactStableStatement
open Formalism.BasicNotions.TH GlobalTheory.FockAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockHarmonic_mem_finiteDimensional_compactStable : ∀ (P Q R S : ℕ) (h : Pol P Q R S), h ∈ harm2 P Q R S → ∃ H0 : Submodule ℂ (Pol P Q R S), FiniteDimensional ℂ H0 ∧ h ∈ H0 ∧ (∀ v ∈ H0, v ∈ harm2 P Q R S) ∧ KStable (fockAct1 P Q R S) H0 ∧ KStable (fockAct2 P Q R S) H0 := by
  first | exact @GlobalTheory.FockAlg.fin_harm | exact GlobalTheory.FockAlg.fin_harm | (intros; apply GlobalTheory.FockAlg.fin_harm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableComplementOfKernelExists
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableComplementOfKernelExists
namespace GlobalTheory

theorem stable_complement_of_kernel_exists
    (V W H : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H)
    (hι : Function.Injective ι) (pr : V →ₗ[ℂ] W) (H0 : Submodule ℂ V)
    (hfin : FiniteDimensional ℂ H0) (A : Set (Module.End ℂ V))
    (h1 : ∀ a ∈ A, ∀ v ∈ H0, a v ∈ H0)
    (h2 : ∀ a ∈ A, ∀ v ∈ H0, pr v = 0 → pr (a v) = 0)
    (h3 : ∀ a ∈ A, ∃ b ∈ A, ∀ u v, inner ℂ (ι (a u)) (ι v) = inner ℂ (ι u) (ι (b v))) :
    ∀ h ∈ H0, ∃ c ∈ H0, pr c = pr h ∧
      ∀ a ∈ A, ∀ z : ℂ, pr (a c) = z • pr c → a c = z • c := by
  intro h hh
  set K : Submodule ℂ V := H0 ⊓ LinearMap.ker pr with hK
  haveI : FiniteDimensional ℂ K := Submodule.finiteDimensional_of_le inf_le_left
  set K' : Submodule ℂ H := K.map ι with hK'
  haveI : FiniteDimensional ℂ K' := inferInstance
  haveI : CompleteSpace K' := FiniteDimensional.complete ℂ K'
  obtain ⟨y, hy, e, he, hsum⟩ := K'.exists_add_mem_mem_orthogonal (ι h)
  obtain ⟨k, hk, rfl⟩ := Submodule.mem_map.mp hy
  have hkH0 : k ∈ H0 := hk.1
  have hkker : pr k = 0 := hk.2
  refine ⟨h - k, H0.sub_mem hh hkH0, by simp [hkker], ?_⟩
  have horth : ∀ k' ∈ K, inner ℂ (ι k') (ι (h - k)) = 0 := by
    intro k' hk'
    have : ι (h - k) = e := by rw [map_sub, hsum]; abel
    rw [this]
    exact (Submodule.mem_orthogonal K' e).mp he _ (Submodule.mem_map_of_mem hk')
  intro a ha z hz
  set c := h - k with hc
  have hcH0 : c ∈ H0 := H0.sub_mem hh hkH0
  set d := a c - z • c with hd
  have hdK : d ∈ K := by
    refine ⟨H0.sub_mem (h1 a ha c hcH0) (H0.smul_mem z hcH0), ?_⟩
    show pr d = 0
    simp [hd, hz]
  obtain ⟨b, hb, hab⟩ := h3 a ha
  have hdorth : ∀ k' ∈ K, inner ℂ (ι k') (ι d) = 0 := by
    intro k' hk'
    have hbk : b k' ∈ K := ⟨h1 b hb k' hk'.1, h2 b hb k' hk'.1 hk'.2⟩
    have e1 : inner ℂ (ι k') (ι (a c)) = 0 := by
      rw [← inner_conj_symm, hab, inner_conj_symm]
      exact horth _ hbk
    rw [hd, map_sub, inner_sub_right, e1, map_smul, inner_smul_right, horth k' hk']
    simp
  have : ι d = 0 := inner_self_eq_zero.mp (hdorth d hdK)
  have hd0 : d = 0 := hι (by rw [this, map_zero])
  exact sub_eq_zero.mp hd0

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableComplementOfKernelExistsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigen_complement_of_adjoint_stable_kernel : ∀ (V W H : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H), Function.Injective ι → ∀ (pr : V →ₗ[ℂ] W) (H0 : Submodule ℂ V), FiniteDimensional ℂ H0 → ∀ (A : Set (Module.End ℂ V)), (∀ a ∈ A, ∀ v ∈ H0, a v ∈ H0) → (∀ a ∈ A, ∀ v ∈ H0, pr v = 0 → pr (a v) = 0) → (∀ a ∈ A, ∃ b ∈ A, ∀ u v, inner ℂ (ι (a u)) (ι v) = inner ℂ (ι u) (ι (b v))) → ∀ h ∈ H0, ∃ c ∈ H0, pr c = pr h ∧ ∀ a ∈ A, ∀ z : ℂ, pr (a c) = z • pr c → a c = z • c := by
  first | exact @GlobalTheory.stable_complement_of_kernel_exists | exact GlobalTheory.stable_complement_of_kernel_exists | (intros; apply GlobalTheory.stable_complement_of_kernel_exists <;> assumption)
end
end

noncomputable section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.BasicNotions.TH GlobalTheory.FockAlg

namespace GlobalTheory.HarmLift

theorem lemA : ∀ (P Q R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (pr : Pol P Q R S →ₗ[ℂ] W),
    (∀ Z : Mat P Q, IsPC Z → ∀ f, pr (fockAct1 P Q R S Z f) = 0) →
    ∀ f, ∃ h ∈ harm2 P Q R S, pr h = pr f := GlobalTheory.T.exists_fockHarmonic_representative

theorem lemB : ∀ (P Q R S : ℕ) (h : Pol P Q R S), h ∈ harm2 P Q R S →
    ∃ H0 : Submodule ℂ (Pol P Q R S), FiniteDimensional ℂ H0 ∧ h ∈ H0 ∧ (∀ v ∈ H0, v ∈ harm2 P Q R S) ∧
      KStable (fockAct1 P Q R S) H0 ∧ KStable (fockAct2 P Q R S) H0 := GlobalTheory.T.fockHarmonic_mem_finiteDimensional_compactStable

theorem lemC : ∀ (V W H : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H), Function.Injective ι →
    ∀ (pr : V →ₗ[ℂ] W) (H0 : Submodule ℂ V), FiniteDimensional ℂ H0 →
    ∀ (A : Set (Module.End ℂ V)), (∀ a ∈ A, ∀ v ∈ H0, a v ∈ H0) →
      (∀ a ∈ A, ∀ v ∈ H0, pr v = 0 → pr (a v) = 0) →
      (∀ a ∈ A, ∃ b ∈ A, ∀ u v, inner ℂ (ι (a u)) (ι v) = inner ℂ (ι u) (ι (b v))) →
      ∀ h ∈ H0, ∃ c ∈ H0, pr c = pr h ∧ ∀ a ∈ A, ∀ z : ℂ, pr (a c) = z • pr c → a c = z • c := GlobalTheory.T.exists_eigen_complement_of_adjoint_stable_kernel

theorem isKC_adjZ {p q : ℕ} {Z : Mat p q} (hZ : IsKC Z) : IsKC (adjZ Z) := by
  intro a b hab
  rw [GlobalTheory.FockAdj.adjZ_apply, hZ b a (fun h => hab (by revert h; rcases a with a | a <;> rcases b with b | b <;> simp [sameBlock])),
    star_zero, mul_zero]

theorem trace_PC {p q : ℕ} {Z : Mat p q} (hZ : IsPC Z) : Z.trace = 0 := by
  simp only [Matrix.trace, Matrix.diag]
  refine Finset.sum_eq_zero fun a _ => hZ a a ?_
  rcases a with a | a <;> simp [sameBlock]

theorem isKC_Eab {p q : ℕ} {a b : Ix p q} (h : sameBlock a b) : IsKC (Eab a b) := by
  intro c d hcd
  simp only [Eab, Matrix.single_apply]
  split_ifs with e
  · obtain ⟨rfl, rfl⟩ := e; exact absurd h hcd
  · rfl

end GlobalTheory.HarmLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedFullRankIrreducible
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedFullRankIrreducible
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitFlip
open scoped Matrix

namespace GlobalTheory.FullRankCoinv.IndTwist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem Y0_mul_apply {a n : ℕ} (M : Matrix (Fin (a + n)) (Fin (a + n)) k) (i : Fin n) (j : Fin (a + n)) :
    (Y0 k n (a + n) * M) i j = M (Fin.natAdd a i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.natAdd a i)]
  · simp [Y0]
  · intro l _ hl
    have : ¬ ((l : ℕ) = a + i) := fun h => hl (Fin.ext (by simp; omega))
    simp [Y0, this]
  · simp

theorem mul_Y0_apply {a n : ℕ} (D : Matrix (Fin n) (Fin n) k) (i : Fin n) (j : Fin (a + n)) :
    (D * Y0 k n (a + n)) i j = if h : a ≤ (j : ℕ) then D i ⟨j - a, by omega⟩ else 0 := by
  split_ifs with h
  · rw [Matrix.mul_apply, Finset.sum_eq_single (⟨j - a, by omega⟩ : Fin n)]
    · simp [Y0]; omega
    · intro l _ hl
      have : ¬ ((j : ℕ) = a + l) := fun h' => hl (Fin.ext (by simp; omega))
      simp [Y0, this]
    · simp
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    have : ¬ ((j : ℕ) = a + l) := by omega
    simp [Y0, this]

theorem Y0_mul_parab {a n : ℕ} (p : parab k (GlobalTheory.RankFibre.blocks a n)) :
    Y0 k n (a + n) * (p : GL (Fin (a + n)) k).1 =
      (leviProj k (GlobalTheory.RankFibre.blocks a n) p true : GL (Fin n) k).1 * Y0 k n (a + n) := by
  ext i j
  rw [Y0_mul_apply, mul_Y0_apply]
  have hp := (mem_parab_two k).1 p.2
  split_ifs with h
  · rw [leviProj_apply]
    have e1 : GlobalTheory.RankFibre.blocks a n ⟨true, i⟩ = Fin.natAdd a i := Fin.ext (by simp [stdSum])
    have e2 : GlobalTheory.RankFibre.blocks a n ⟨true, (⟨j - a, by omega⟩ : Fin n)⟩ = j := Fin.ext (by simp [stdSum]; omega)
    rw [e1, e2]
  · have := hp i ⟨j, by omega⟩
    simpa [stdSum] using this

end GlobalTheory.FullRankCoinv.IndTwist

namespace GlobalTheory.FullRankCoinv.IndTwist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem parChar_eq {a n : ℕ} (ν : kˣ →* ℂˣ) (p : parab k (GlobalTheory.RankFibre.blocks a n)) :
    ((GlobalTheory.RankFibre.parChar ν ν⁻¹ a n p : ℂˣ) : ℂ) =
      apow (gdet (p : GL (Fin (a + n)) k)) ((n : ℂ) / 2) *
        ((((ν (gdet (leviProj k (GlobalTheory.RankFibre.blocks a n) p true)))⁻¹ : ℂˣ) : ℂ) *
          apow (gdet (leviProj k (GlobalTheory.RankFibre.blocks a n) p true)) (-((a + n : ℕ) : ℂ) / 2)) := by
  set A := leviProj k (GlobalTheory.RankFibre.blocks a n) p false
  set D := leviProj k (GlobalTheory.RankFibre.blocks a n) p true
  have hδ : deltaHalf k (Two (Fin a) (Fin n)) (leviProj k (GlobalTheory.RankFibre.blocks a n) p) =
      absPow k ((n : ℂ) / 2) (gdet A) * absPow k (-(a : ℂ) / 2) (gdet D) := by
    rw [← (leviTwo k (Fin a) (Fin n)).apply_symm_apply (leviProj k (GlobalTheory.RankFibre.blocks a n) p), deltaHalf_two]
    simp [A, D]
    rfl
  have hdet : gdet (p : GL (Fin (a + n)) k) = gdet A * gdet D := by
    rw [gdet, det_parab, Fintype.prod_bool, mul_comm]
  simp only [GlobalTheory.RankFibre.parChar, MonoidHom.comp_apply, MonoidHom.mul_apply, Units.val_mul, hδ]
  rw [hdet, apow_mul]
  have e : apow (gdet D) (-(a : ℂ) / 2) =
      apow (gdet D) ((n : ℂ) / 2) * apow (gdet D) (-((a + n : ℕ) : ℂ) / 2) := by
    rw [← apow_add]; congr 1; push_cast; ring
  show apow (gdet A) ((n : ℂ) / 2) * apow (gdet D) (-(a : ℂ) / 2) * (((ν * ν⁻¹) (gdet A) : ℂˣ) : ℂ) *
    ((ν⁻¹ (gdet D) : ℂˣ) : ℂ) = _
  rw [e, mul_inv_cancel]
  simp only [MonoidHom.one_apply, Units.val_one, mul_one, MonoidHom.inv_apply]
  ring

end GlobalTheory.FullRankCoinv.IndTwist

namespace GlobalTheory.FullRankCoinv.IndTwist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def detTw (d : ℕ) (s : ℂ) : (GL (Fin d) k → ℂ) →ₗ[ℂ] (GL (Fin d) k → ℂ) where
  toFun f x := apow (gdet x) s * f x
  map_add' f g := by funext x; simp [mul_add]
  map_smul' c f := by funext x; simp; ring

theorem detTw_apply (d : ℕ) (s : ℂ) (f : GL (Fin d) k → ℂ) (x : GL (Fin d) k) :
    detTw d s f x = apow (gdet x) s * f x := rfl

theorem detTw_neg_detTw (d : ℕ) (s : ℂ) (f : GL (Fin d) k → ℂ) : detTw d (-s) (detTw d s f) = f := by
  funext x; rw [detTw_apply, detTw_apply, ← mul_assoc, ← apow_add]; simp

theorem detTw_detTw_neg (d : ℕ) (s : ℂ) (f : GL (Fin d) k → ℂ) : detTw d s (detTw d (-s) f) = f := by
  simpa using detTw_neg_detTw d (-s) f

theorem detTw_translate (d : ℕ) (s : ℂ) (f : GL (Fin d) k → ℂ) (h : GL (Fin d) k) :
    (fun x => detTw d s f (x * h)) = apow (gdet h) s • detTw d s (fun x => f (x * h)) := by
  funext x
  simp only [detTw_apply, Pi.smul_apply, smul_eq_mul, gdet_mul, apow_mul]
  ring

theorem detTw_mem_indScal {a n : ℕ} (ν : kˣ →* ℂˣ) {f : GL (Fin (a + n)) k → ℂ} (hf : f ∈ indSp k n (a + n) ν) :
    detTw (a + n) ((n : ℂ) / 2) f ∈ GlobalTheory.RankFibre.indScal ν ν⁻¹ a n := by
  obtain ⟨⟨U, hU, hfU⟩, hfl⟩ := hf
  have hK : IsSmoothChar (detChar (Fin (a + n)) (absPow k ((n : ℂ) / 2))) :=
    (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar
  have hK1 : ((detChar (Fin (a + n)) (absPow k ((n : ℂ) / 2))).ker : Set (GL (Fin (a + n)) k)) ∈ nhds 1 :=
    hK.mem_nhds (by simp)
  refine ⟨mem_smoothPart_of_nhds (Filter.mem_of_superset (Filter.inter_mem hU hK1) fun g hg => ?_), ?_⟩
  · have hg2 : apow (gdet g) ((n : ℂ) / 2) = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.1 hg.2)
      exact this
    show (fun x => detTw (a + n) ((n : ℂ) / 2) f (x * g)) = detTw (a + n) ((n : ℂ) / 2) f
    funext x
    simp only [detTw_apply, gdet_mul, apow_mul, hg2, mul_one, hfU x g hg.1]
  · intro p x
    have h := hfl p x (leviProj k (GlobalTheory.RankFibre.blocks a n) p true) (Y0_mul_parab p)
    simp only [ofChar_apply, detTw_apply, gdet_mul, apow_mul, h, parChar_eq]
    ring

end GlobalTheory.FullRankCoinv.IndTwist

namespace GlobalTheory.FullRankCoinv

open IndTwist

theorem indSp_irreducible : GlobalTheory.FunPr.Hypotheses₂ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν →
    ∀ N : Submodule ℂ (GL (Fin d) k → ℂ), N ≤ GlobalTheory.FullRankCoinv.indSp k n d ν →
      (∀ f ∈ N, ∀ h₀ : GL (Fin d) k, (fun h => f (h * h₀)) ∈ N) → N = ⊥ ∨ N = GlobalTheory.FullRankCoinv.indSp k n d ν := by
  intro P k _ _ _ _ n d ν hn hνs hνu N hN hinv
  obtain ⟨a, rfl⟩ : ∃ a, d = a + n := ⟨d - n, by omega⟩
  have hu : IsUnitaryChar ν⁻¹ := fun g => by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hνu g, inv_one]
  set s : ℂ := (n : ℂ) / 2
  let M : Submodule ℂ (GL (Fin (a + n)) k → ℂ) := N.comap (detTw (a + n) (-s))
  have hMle : M ≤ GlobalTheory.RankFibre.indScal ν ν⁻¹ a n := fun g hg => by
    have := detTw_mem_indScal ν (hN hg)
    rwa [detTw_detTw_neg] at this
  have hMinv : ∀ g ∈ M, ∀ h : GL (Fin (a + n)) k, (fun x => g (x * h)) ∈ M := fun g hg h => by
    show detTw (a + n) (-s) (fun x => g (x * h)) ∈ N
    have e : detTw (a + n) (-s) (fun x => g (x * h)) =
        apow (gdet h) s • (fun x => detTw (a + n) (-s) g (x * h)) := by
      rw [detTw_translate, smul_smul, ← apow_add]; simp
    rw [e]
    exact N.smul_mem _ (hinv _ hg h)
  have hmemM : ∀ f ∈ N, detTw (a + n) s f ∈ M := fun f hf => by
    show detTw (a + n) (-s) (detTw (a + n) s f) ∈ N
    rwa [detTw_neg_detTw]
  rcases GlobalTheory.RankFibre.indScal_irreducible P.bernsteinUnitaryProductIrreducible k a n ν ν⁻¹ hνs hνu hνs.inv hu
    M hMle hMinv with h | h
  · left
    refine (Submodule.eq_bot_iff N).2 fun f hf => ?_
    have h0 : detTw (a + n) s f = 0 := by
      have := hmemM f hf
      rw [h] at this
      exact (Submodule.mem_bot ℂ).1 this
    rw [← detTw_neg_detTw (a + n) s f, h0, map_zero]
  · right
    refine le_antisymm hN fun f hf => ?_
    have := h (detTw_mem_indScal ν hf)
    have h' : detTw (a + n) (-s) (detTw (a + n) s f) ∈ N := this
    rwa [detTw_neg_detTw] at h'

end GlobalTheory.FullRankCoinv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedFullRankIrreducibleStatement
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_full_rank_irreducible : GlobalTheory.FunPr.Hypotheses₂ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν →
    ∀ N : Submodule ℂ (GL (Fin d) k → ℂ), N ≤ GlobalTheory.FullRankCoinv.indSp k n d ν →
      (∀ f ∈ N, ∀ h₀ : GL (Fin d) k, (fun h => f (h * h₀)) ∈ N) → N = ⊥ ∨ N = GlobalTheory.FullRankCoinv.indSp k n d ν := by
  first | exact @GlobalTheory.FullRankCoinv.indSp_irreducible | exact GlobalTheory.FullRankCoinv.indSp_irreducible | (intros; apply GlobalTheory.FullRankCoinv.indSp_irreducible <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorIrreducibleModules
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.TensIrr

open Formalism.BasicNotions.TH GlobalTheory.RealLift

section Lin

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

theorem atPl_add (w : ι) (a b : Module.End ℂ (V w)) : atPl w (a + b) = atPl w a + atPl w b :=
  PiTensorProduct.map_update_add _ w a b

theorem atPl_smul (w : ι) (c : ℂ) (a : Module.End ℂ (V w)) : atPl w (c • a) = c • atPl w a :=
  PiTensorProduct.map_update_smul _ w c a

theorem atPl_mul (w : ι) (a b : Module.End ℂ (V w)) : atPl w (a * b) = atPl w a * atPl w b := by
  unfold atPl
  rw [← PiTensorProduct.map_mul]
  congr 1
  funext j
  by_cases h : j = w
  · subst h; simp
  · simp [Function.update_of_ne h]; rfl

theorem atPl_one (w : ι) : atPl (V := V) w 1 = 1 := by
  unfold atPl
  show PiTensorProduct.map (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w LinearMap.id) = 1
  rw [Function.update_eq_self]
  exact PiTensorProduct.map_id

theorem atPl_tprod (w : ι) (L : Module.End ℂ (V w)) (v : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v w (L (v w))) := by
  unfold atPl
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext j
  by_cases h : j = w
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem atPl_local (w : ι) (y : ⨂[ℂ] i, V i) : ∃ s : Finset (V w), ∀ f g : Module.End ℂ (V w),
    (∀ m ∈ s, f m = g m) → atPl w f y = atPl w g y := by
  classical
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    refine ⟨{v w}, fun f g h => ?_⟩
    rw [map_smul, map_smul, atPl_tprod, atPl_tprod, h (v w) (Finset.mem_singleton_self _)]
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    refine ⟨s ∪ t, fun f g h => ?_⟩
    rw [map_add (f := _), map_add (f := _), hs f g (fun m hm => h m (Finset.mem_union_left _ hm)),
      ht f g (fun m hm => h m (Finset.mem_union_right _ hm))]

theorem stable_all (w : ι) {Z : Type} (A : Z → Module.End ℂ (V w)) [Nontrivial (V w)]
    (hirr : ∀ N : Submodule ℂ (V w), (∀ z, ∀ y ∈ N, A z y ∈ N) → N = ⊥ ∨ N = ⊤)
    (hsch : ∀ T : V w →ₗ[ℂ] V w, (∀ z, T ∘ₗ A z = A z ∘ₗ T) → ∃ c : ℂ, T = c • LinearMap.id)
    (N : Submodule ℂ (⨂[ℂ] i, V i)) (hN : ∀ z, ∀ y ∈ N, atPl w (A z) y ∈ N) :
    ∀ f : Module.End ℂ (V w), ∀ y ∈ N, atPl w f y ∈ N := by
  have hadj : ∀ r ∈ Algebra.adjoin ℂ (Set.range A), ∀ y ∈ N, atPl w r y ∈ N := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨z, rfl⟩ := hx; exact hN z
    | algebraMap c =>
      intro y hy
      rw [Algebra.algebraMap_eq_smul_one, atPl_smul, atPl_one]
      exact N.smul_mem c hy
    | add x y _ _ hx hy =>
      intro z hz
      rw [atPl_add]
      exact N.add_mem (hx z hz) (hy z hz)
    | mul x y _ _ hx hy =>
      intro z hz
      rw [atPl_mul]
      exact hx _ (hy z hz)
  intro f y hy
  obtain ⟨s, hs⟩ := atPl_local w y
  obtain ⟨r, hr, hf⟩ := GlobalTheory.IrrTensor.density A hirr hsch f s
  rw [hs f r hf]
  exact hadj r hr y hy

theorem stable_map (N : Submodule ℂ (⨂[ℂ] i, V i))
    (hN : ∀ w (f : Module.End ℂ (V w)), ∀ y ∈ N, atPl w f y ∈ N) (g : ∀ i, Module.End ℂ (V i)) :
    ∀ y ∈ N, PiTensorProduct.map g y ∈ N := by
  classical
  have key : ∀ s : Finset ι, ∀ y ∈ N,
      PiTensorProduct.map (fun i => if i ∈ s then g i else LinearMap.id) y ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro y hy; simpa using hy
    | insert a s ha ih =>
      intro y hy
      have e : PiTensorProduct.map (fun i => if i ∈ insert a s then g i else LinearMap.id) =
          atPl a (g a) ∘ₗ PiTensorProduct.map (fun i => if i ∈ s then g i else LinearMap.id) := by
        unfold atPl
        rw [← PiTensorProduct.map_comp]
        congr 1
        funext j
        by_cases h : j = a
        · subst h; simp [ha]
        · simp [Function.update_of_ne h, Finset.mem_insert, h]
      rw [e]
      exact hN a _ _ (ih y hy)
  intro y hy
  simpa using key Finset.univ y hy

def prodForm (ℓ : ∀ i, Module.Dual ℂ (V i)) : (⨂[ℂ] i, V i) →ₗ[ℂ] ℂ :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap ℓ)

theorem prodForm_tprod (ℓ : ∀ i, Module.Dual ℂ (V i)) (v : ∀ i, V i) :
    prodForm ℓ (PiTensorProduct.tprod ℂ v) = ∏ i, ℓ i (v i) := by
  simp [prodForm]

theorem map_rankOne (ℓ : ∀ i, Module.Dual ℂ (V i)) (u : ∀ i, V i) (y : ⨂[ℂ] i, V i) :
    PiTensorProduct.map (fun i => (ℓ i).smulRight (u i)) y = prodForm ℓ y • PiTensorProduct.tprod ℂ u := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    rw [map_smul, map_smul, PiTensorProduct.map_tprod, prodForm_tprod, smul_assoc]
    congr 1
    simp only [LinearMap.smulRight_apply]
    exact MultilinearMap.map_smul_univ _ _ _
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_smul]

end Lin

end GlobalTheory.TensIrr

namespace GlobalTheory.TensIrr

open Formalism.BasicNotions.TH GlobalTheory.RealLift
open scoped Matrix

section Lin2

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

theorem exists_prodForm_ne (y : ⨂[ℂ] i, V i) (hy : y ≠ 0) : ∃ ℓ : ∀ i, Module.Dual ℂ (V i), prodForm ℓ y ≠ 0 := by
  classical
  let b := fun i => Module.Basis.ofVectorSpace ℂ (V i)
  let B := Basis.piTensorProduct b
  obtain ⟨α, hα⟩ : ∃ α, B.repr y α ≠ 0 := by
    by_contra h
    push_neg at h
    apply hy
    apply B.repr.injective
    ext α
    simp [h α]
  refine ⟨fun i => (b i).coord (α i), ?_⟩
  have e : (Finsupp.lapply α ∘ₗ B.repr.toLinearMap) = prodForm (fun i => (b i).coord (α i)) := by
    refine B.ext fun β => ?_
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply,
      show B β = _ from Basis.piTensorProduct_apply b β, prodForm_tprod]
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self]
    by_cases h : β = α
    · subst h; simp
    · obtain ⟨i, hi⟩ := Function.ne_iff.1 h
      rw [Finsupp.single_apply, if_neg h]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [Finsupp.single_apply, if_neg hi])
  rw [← e]
  simpa using hα

theorem tensor_nontrivial [∀ i, Nontrivial (V i)] : Nontrivial (⨂[ℂ] i, V i) := by
  choose v hv using fun i => exists_ne (0 : V i)
  choose ℓ hℓ using fun i => Module.Projective.exists_dual_eq_one ℂ (hv i)
  refine nontrivial_of_ne (PiTensorProduct.tprod ℂ v) 0 fun h => ?_
  have := congrArg (prodForm ℓ) h
  rw [prodForm_tprod, map_zero] at this
  simp [hℓ] at this

theorem irr_of_stable (N : Submodule ℂ (⨂[ℂ] i, V i))
    (hN : ∀ w (f : Module.End ℂ (V w)), ∀ y ∈ N, atPl w f y ∈ N) : N = ⊥ ∨ N = ⊤ := by
  by_cases h : N = ⊥
  · exact Or.inl h
  right
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨ℓ, hℓ⟩ := exists_prodForm_ne y hy0
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨u, rfl⟩
  have h1 := stable_map N hN (fun i => (ℓ i).smulRight (u i)) y hy
  rw [map_rankOne] at h1
  have h2 := N.smul_mem (prodForm ℓ y)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hℓ, one_smul] at h2

end Lin2

theorem Jm_conjTranspose (R S : ℕ) : (Jm R S)ᴴ = Jm R S := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]

theorem Jm_mul_self (R S : ℕ) : Jm R S * Jm R S = 1 := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem mem_upq_comb {R S : ℕ} (Z : Mat R S) (a b : ℂ) (h : star a + b = 0) :
    a • Z + b • (Jm R S * Zᴴ * Jm R S) ∈ upq R S := by
  have hJh := Jm_conjTranspose R S
  have hJJ := Jm_mul_self R S
  set J := Jm R S
  have e1 : J * (Z * J) * J = J * Z := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hJJ, Matrix.mul_one]
  have e2 : J * (J * Zᴴ * J) = Zᴴ * J := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hb : b = -star a := by linear_combination h
  show (a • Z + b • (J * Zᴴ * J))ᴴ * J + J * (a • Z + b • (J * Zᴴ * J)) = 0
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, hJh, Matrix.conjTranspose_conjTranspose, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, e1, e2, hb]
  simp only [star_neg, star_star, neg_smul]
  abel

theorem upq_decomp {R S : ℕ} (Z : Mat R S) : ∃ X₁ ∈ upq R S, ∃ X₂ ∈ upq R S, Z = X₁ + Complex.I • X₂ := by
  refine ⟨(1 / 2 : ℂ) • Z + (-(1 / 2) : ℂ) • (Jm R S * Zᴴ * Jm R S), mem_upq_comb Z _ _ (by simp),
    (-(Complex.I / 2)) • Z + (-(Complex.I / 2)) • (Jm R S * Zᴴ * Jm R S), mem_upq_comb Z _ _ ?_, ?_⟩
  · simp [Complex.conj_I]; ring
  · rw [smul_add, smul_smul, smul_smul]
    have : Complex.I * -(Complex.I / 2) = 1 / 2 := by ring_nf; simp; ring
    rw [this]
    module

theorem tensor_irr : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (R S : ℕ) (M : ι → Formalism.BasicNotions.TH.GKMod R S),
    (∀ i, Formalism.MainNotions.SchurIrreducible.IrrGK (M i) ∧ GlobalTheory.RealLift.ScalarEnd (M i)) →
    Nontrivial (PiTensorProduct ℂ fun i => (M i).V) ∧
    ∀ N : Submodule ℂ (PiTensorProduct ℂ fun i => (M i).V),
      (∀ i, ∀ Z ∈ Formalism.BasicNotions.TH.upq R S, ∀ y ∈ N, GlobalTheory.RealLift.atPl i ((M i).act Z) y ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro ι _ _ R S M hM
  haveI : ∀ i, Nontrivial (M i).V := fun i => (hM i).1.1
  refine ⟨tensor_nontrivial, fun N hN => irr_of_stable N ?_⟩
  have hgl : ∀ i (Z : Mat R S), ∀ y ∈ N, atPl i ((M i).act Z) y ∈ N := by
    intro i Z y hy
    obtain ⟨X₁, h₁, X₂, h₂, rfl⟩ := upq_decomp Z
    rw [map_add (f := _), map_smul, atPl_add, atPl_smul, LinearMap.add_apply, LinearMap.smul_apply]
    exact N.add_mem (hN i X₁ h₁ y hy) (N.smul_mem _ (hN i X₂ h₂ y hy))
  intro w f y hy
  exact stable_all (V := fun i => (M i).V) w (fun Z => (M w).act Z) (hM w).1.2 (hM w).2 N (hgl w) f y hy

end GlobalTheory.TensIrr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivSplitCentre
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

noncomputable section

namespace GlobalTheory.CuspRep.SplitDeriv

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem hasDerivAt_scalar_exp :
    HasDerivAt (fun t : ℝ =>
      toL (Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (t : ℂ))).val)
      (fun i j => if i = j then (1 : Cinf E) else 0) 0 := by
  rw [hasDerivAt_pi]; intro i
  rw [hasDerivAt_pi]; intro j
  rw [hasDerivAt_pi]; intro w
  by_cases h : i = j
  · subst h
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
    have h2 := h1.cexp
    simpa [toL, Matrix.scalar_apply, Matrix.diagonal_apply, expU] using h2
  · simpa [toL, Matrix.scalar_apply, Matrix.diagonal_apply, h] using hasDerivAt_const (0 : ℝ) (0 : ℂ)


open GlobalTheory.UnitaryBC in
theorem hasDerivAt_splitCentre (ψ : Sm E a) (g : GA E a) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ψ.1 (g * splitCentre E a t))
      ((lie E a (fun i j => if i = j then (1 : Cinf E) else 0) ψ).1 (g * splitCentre E a s)) s := by
  have h0 : Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => ((0 : ℝ) : ℂ)) = 1 := by
    ext i j w
    by_cases h : i = j <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply, expU, Matrix.one_apply, h]
  have h := hasDerivAt_curve ψ (g * splitCentre E a s)
    (fun t => Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (t : ℂ)))
    _ h0 hasDerivAt_scalar_exp
  have h' := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h)
  rw [lie_apply]
  refine h'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  change ψ.1 (g * splitCentre E a t) = ψ.1 (g * splitCentre E a s * splitCentre E a (t - s))
  rw [mul_assoc, ← splitCentre_add, add_sub_cancel]

end GlobalTheory.CuspRep.SplitDeriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostHalfRootAddConjEqOne
open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000

namespace GlobalTheory.FrameEquiv.GenMove

section Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

variable {H : Geo.Tor.Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ]
  {r g : ℕ}


end Classical

section Adelic

open GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws

variable {D : D7}

theorem isUnitFr_of_archM (W : HSp D) (X : Data D.host.E W.rank) (hX : ModelW W rfl X)
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin W.rank) (Fin W.rank) ℂ} (h0 : IsOrthogonalFrame X x₀)
    {th : X.Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hth : ∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th τ))
    (g : GA D W) (x : Frame X.Ψ W.rank)
    (hx : ∀ τ : X.Ψ, mat x τ = Matrix.reindex (finCongr rfl) (finCongr rfl) (archM W (th τ) g) * x₀ τ.1) :
    IsUnitFr X x := by
  refine ((GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular _ _ X.p0 X.Ψ X.Gm X.Gm_herm).2.1 x
    fun τ => ?_).2
  rw [← h0 τ.1 τ.2, hx τ, GlobalTheory.RecDictModel.gram_eq, GlobalTheory.RecDictModel.gram_eq, hX.1]
  have hu := GlobalTheory.RecDictModel.archM_unitary W (hth τ) g
  have e1 : ∀ A : Matrix (Fin W.rank) (Fin W.rank) ℂ, Matrix.reindex (finCongr rfl) (finCongr rfl) A = A :=
    fun A => rfl
  have e2 : ((-(Matrix.reindex (finCongr rfl) (finCongr rfl) W.gram).transpose).map τ.1).transpose =
      -(W.gram.map τ.1) := by
    ext a b; simp
  rw [e1, e2, Matrix.conjTranspose_mul]
  congr 1
  conv_rhs => rw [← hu]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

end Adelic

end GlobalTheory.FrameEquiv.GenMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonIrreducibleQuotient
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
open GlobalTheory.FockAlg (genSub)

noncomputable section

namespace GlobalTheory.CommonQuot

variable {p q : ℕ}

section General

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem mem_hwSub' (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (v : V) :
    v ∈ hwSub act μ ↔ (∀ a, act (Eab a a) v - ((μ a : ℚ) : ℂ) • v = 0) ∧
      ∀ a b, posC a b → act (Eab a b) v = 0 := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]

theorem isKC_diag' (a : Ix p q) : IsKC (Eab a a) := by
  intro c d h
  rw [Eab, Matrix.single_apply, ite_eq_right]
  rintro ⟨rfl, rfl⟩
  cases a <;> simp [sameBlock] at h

theorem isKC_pos' {a b : Ix p q} (hab : posC a b) : IsKC (Eab a b) := by
  intro c d h
  rw [Eab, Matrix.single_apply, ite_eq_right]
  rintro ⟨rfl, rfl⟩
  cases a <;> cases b <;> simp_all [sameBlock, posC]

theorem map_hw {a : Mat p q →ₗ[ℂ] Module.End ℂ V} {b : Mat p q →ₗ[ℂ] Module.End ℂ V'}
    (g : V →ₗ[ℂ] V') (hg : ∀ Z v, g (a Z v) = b Z (g v)) {μ : Ix p q → ℚ} {v : V}
    (hv : v ∈ hwSub a μ) : g v ∈ hwSub b μ := by
  rw [mem_hwSub'] at hv ⊢
  refine ⟨fun c => ?_, fun c d h => ?_⟩
  · rw [← hg, ← map_smul, ← map_sub, hv.1 c, map_zero]
  · rw [← hg, hv.2 c d h, map_zero]

theorem map_wts {a : Mat p q →ₗ[ℂ] Module.End ℂ V} {b : Mat p q →ₗ[ℂ] Module.End ℂ V'}
    (g : V →ₗ[ℂ] V') (hg : ∀ Z v, g (a Z v) = b Z (g v)) {x : V}
    (hx : x ∈ ⨆ μ : Ix p q → ℚ, wtSub a μ) : g x ∈ ⨆ μ : Ix p q → ℚ, wtSub b μ := by
  refine Submodule.iSup_induction _ (motive := fun v => g v ∈ _) hx ?_ (by simp) ?_
  · intro μ y hy
    refine Submodule.mem_iSup_of_mem μ ?_
    simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply] at hy ⊢
    intro c
    rw [← hg, ← map_smul, ← map_sub, hy c, map_zero]
  · intro x y hx hy
    rw [map_add]; exact add_mem hx hy

end General

section Constructions

end Constructions

section Max

end Max

section Main

end Main

end GlobalTheory.CommonQuot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalSectionsPolynomialGrowth
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalSectionsPolynomialGrowth
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem hdim_twist_zero_le_of_cls_eq_add_nsmul (k : Type) [Field k] [Infinite k] (X : Scheme.{0})
    [Algebra k Γ(X, ⊤)] (hX : IsProjOver (strHom k (X := X))) (F : X.Modules) [IsFiniteQC F]
    (B : LB X) (hB : B.IsLB) (s : B.Sec) (hs : Mono (cutHom F hB s)) (j : ℕ) :
    ∀ (M M' : LB X) (hM : M.IsLB) (hM' : M'.IsLB), cls M hM = cls M' hM' + j • cls B hB →
      hdim k (twist F M') 0 ≤ hdim k (twist F M) 0 := by
  induction j with
  | zero =>
    intro M M' hM hM' e
    obtain ⟨e⟩ := nonempty_twist_iso_of_cls_eq F hM hM' (by simpa using e)
    exact (hdim_congr k 0 e).ge
  | succ j ih =>
    intro M M' hM hM' e
    obtain ⟨N, hN, eN⟩ := cls_surj (cls M' hM' + j • cls B hB)
    exact (ih N M' hN hM' eN).trans
      (GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities k X hX F B M N hB hM hN s hs (by rw [e, eN, succ_nsmul, add_assoc])).2.2

theorem exists_hdim_twist_lbPow_zero_le :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X), L.IsLB → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) → ∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) 0 ≤ C * (m + 1) ^ d := by
  intro k _ _ X _ hX d L hL F _ hF
  have := isNoetherian_of_isProjOver hX
  obtain ⟨-, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hX
  obtain ⟨D, hD, eD⟩ := cls_surj (-cls L hL)
  obtain ⟨n, hn, hn1⟩ := ((tendsto_natCast_atTop_atTop (R := ℤ).eventually
    (hA.eventually_exists_mono_cutHom hD F)).and (eventually_ge_atTop 1)).exists
  obtain ⟨B, hB, eB⟩ := cls_surj (cls D hD + (n : ℤ) • cls A hA.isLB)
  obtain ⟨s, hs⟩ := hn B hB eB
  have hH : IsAmpleLB (lbPow A n) := (isAmpleLB_pow_iff hA.isLB hn1).2 hA
  have h₁ : ∀ m : ℕ, hdim k (twist F (lbPow L m)) 0 ≤ hdim k (twist F (lbPow (lbPow A n) m)) 0 :=
    fun m => hdim_twist_zero_le_of_cls_eq_add_nsmul k X hX F B hB s hs m _ _
      (isLB_lbPow hH.isLB m) (isLB_lbPow hL m) (by
        rw [cls_lbPow hH.isLB, cls_lbPow hA.isLB, cls_lbPow hL, eB, eD, natCast_zsmul, ← nsmul_add,
          add_neg_cancel_left])
  obtain ⟨C, m₀, hC⟩ := GlobalTheory.T.asymptotic_riemannRoch_ample_coherent k X hX d F hF _ hH
  set a := interNum k F (fun _ : Fin d => lbPow A n)
  set h : ℕ → ℕ := fun m => hdim k (twist F (lbPow (lbPow A n) m)) 0 with hh
  refine ⟨a.natAbs + C * d + ∑ i ∈ Finset.range m₀, h i, fun m => (h₁ m).trans ?_⟩
  change h m ≤ _
  have hp : 1 ≤ (m + 1) ^ d := Nat.one_le_pow _ _ (Nat.succ_pos m)
  rcases lt_or_ge m m₀ with hm | hm
  · have : h m ≤ ∑ i ∈ Finset.range m₀, h i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hm)
    exact (this.trans (Nat.le_add_left _ _)).trans (Nat.le_mul_of_pos_right _ hp)
  · have h₂ : (d.factorial : ℤ) * (h m : ℤ) - a * (m : ℤ) ^ d ≤
        C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) := (abs_le.1 (hC m hm)).2
    have h₃ : (h m : ℤ) ≤ (d.factorial : ℤ) * (h m : ℤ) :=
      le_mul_of_one_le_left (by positivity) (by exact_mod_cast d.factorial_pos)
    have h₄ : a * (m : ℤ) ^ d ≤ |a| * ((m : ℤ) + 1) ^ d :=
      (mul_le_mul_of_nonneg_right (le_abs_self a) (by positivity)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) d) (abs_nonneg a))
    have h₅ : (C : ℤ) * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) ≤ C * ((d : ℤ) * ((m : ℤ) + 1) ^ d) := by
      gcongr
      · have : (0 : ℤ) ≤ m := by positivity
        linarith
      · exact Nat.sub_le _ _
    have h₆ : (h m : ℤ) ≤ ((a.natAbs + C * d) * (m + 1) ^ d : ℕ) := by
      push_cast
      linarith
    exact (by exact_mod_cast h₆ : h m ≤ _).trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalSectionsPolynomialGrowthStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_sections_polynomial_growth : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X), L.IsLB → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) → ∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) 0 ≤ C * (m + 1) ^ d := by
  first | exact @GlobalTheory.exists_hdim_twist_lbPow_zero_le | exact GlobalTheory.exists_hdim_twist_lbPow_zero_le | (intros; apply GlobalTheory.exists_hdim_twist_lbPow_zero_le <;> assumption)
end
end
