module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LinkSPos
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnsRealDataSpec

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HdNumbers
open Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.Core.Rk

noncomputable section

namespace GlobalTheory.Core.Rk

theorem hd_numbers : ∀ (D : D7) (u : D.what₂.Word) (L C' Cl Cg cb Cu cT CT : ℝ), HD D L C' Cl Cg cb Cu cT CT →
    5 ≤ mfL D L ∧ 4 * D.R.f + 1 ≤ (D.mem u).A.T ∧ 0 < d0 D u ∧ 5 ≤ (D.R.f : ℝ) * D.R.k * L := by
  intro D u L C' Cl Cg cb Cu cT CT h
  obtain ⟨-, -, hH, hN, -⟩ := h
  obtain ⟨hL1, -, hmf, hfk, -, -, -, -, -, -, -, hg0, -, hg1, -⟩ := hH
  obtain ⟨-, -, -, -, -, -, -, -, hT, hdu, -⟩ := hN
  have hm : 2 ≤ D.R.m := D.R.two_le_m
  have hm4 : 16 ≤ D.R.m ^ 4 := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm 4
  have hf16 : 16 ≤ D.R.f := le_trans hm4 hmf
  have hk16 : 16 ≤ D.R.k := le_trans hf16 hfk
  have hmR : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have hfR : (16 : ℝ) ≤ D.R.f := by exact_mod_cast hf16
  have hkR : (16 : ℝ) ≤ D.R.k := by exact_mod_cast hk16
  have hL : (1 : ℝ) ≤ L := hL1.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hm5 : (32 : ℝ) ≤ (D.R.m : ℝ) ^ 5 := by
      calc (32 : ℝ) = 2 ^ 5 := by norm_num
        _ ≤ (D.R.m : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) hmR 5
    unfold mfL
    calc (5 : ℝ) ≤ 32 * 16 * 1 := by norm_num
      _ ≤ (D.R.m : ℝ) ^ 5 * D.R.f * L := by
        apply mul_le_mul (mul_le_mul hm5 hfR (by norm_num) (by positivity)) hL (by norm_num) (by positivity)
  · have hb : (1 : ℝ) ≤ Real.exp L := Real.one_le_exp (by linarith)
    have hkg : ∀ g : ℝ, ((D.R.k : ℝ) * Real.exp L) ^ 8 ≤ g → (D.R.k : ℝ) ^ 8 ≤ g := fun g hg =>
      le_trans (pow_le_pow_left₀ (by positivity) (le_mul_of_one_le_right (by positivity) hb) 8) hg
    have h0 : D.R.k ^ 8 ≤ D.host.g 0 := by exact_mod_cast hkg _ hg0
    have h1 : D.R.k ^ 8 ≤ D.host.g 1 := by exact_mod_cast hkg _ hg1
    set N := (D.host.g 0 * D.host.g 1) ^ 2 with hNdef
    have hk8 : 4 * D.R.f ≤ D.R.k ^ 8 := by
      calc 4 * D.R.f ≤ D.R.k * D.R.k := Nat.mul_le_mul (by omega) hfk
        _ = D.R.k ^ 2 := (sq _).symm
        _ ≤ D.R.k ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have hkpos : 1 ≤ D.R.k ^ 8 := Nat.one_le_pow _ _ (by omega)
    have hgg : D.R.k ^ 8 ≤ D.host.g 0 * D.host.g 1 :=
      le_trans h0 (Nat.le_mul_of_pos_right _ (by omega))
    have hNge : D.host.g 0 * D.host.g 1 ≤ N := by
      rw [hNdef, sq]; exact Nat.le_mul_of_pos_right _ (by omega)
    have hN4 : 4 * D.R.f ≤ N := le_trans hk8 (le_trans hgg hNge)
    have hN2 : 2 ≤ N := by omega
    obtain ⟨-, hmod⟩ := hT u
    rw [Nat.one_mod_eq_one.mpr (by omega)] at hmod
    have hTp := (D.mem u).A.T_prime
    have h2 := hTp.two_le
    have hdiv := Nat.div_add_mod ((D.mem u).A.T) N
    rw [hmod] at hdiv
    have hq : (D.mem u).A.T / N ≠ 0 := by
      intro hq0; rw [hq0] at hdiv; omega
    have : N ≤ N * ((D.mem u).A.T / N) := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hq)
    omega
  · rw [d0_eq]; exact hdu u
  · calc (5 : ℝ) ≤ 16 * 16 * 1 := by norm_num
      _ ≤ (D.R.f : ℝ) * D.R.k * L :=
        mul_le_mul (mul_le_mul hfR hkR (by norm_num) (by positivity)) hL (by norm_num) (by positivity)

end GlobalTheory.Core.Rk

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamShareOfFreeT
open Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.Core.Rk

noncomputable section

namespace GlobalTheory.Core.Rk

theorem ramShare_of_freeT {D : D7} {u : D.what₂.Word} (W : Formalism.MainNotions.product_first_zeroth_parts.FreeT D u) : RamShare D u := by
  have h := Formalism.MainNotions.product_first_zeroth_parts.rank_nat W
  have hT2 : 2 ≤ (D.mem u).A.T := ((D.mem u).A.T_prime).two_le
  unfold RamShare dU
  rw [d0_eq]
  have h' : ((D.mem u).A.du : ℝ) * (((D.mem u).A.T : ℝ) - 1) ^ D.R.f =
      (D.duS u : ℝ) * (((D.mem u).A.T : ℝ) - 2) ^ D.R.f := by
    have e2 : (D.mem u).A.T - 1 - 1 = (D.mem u).A.T - 2 := by omega
    rw [e2] at h
    have := congrArg (fun n : ℕ => (n : ℝ)) h
    simp only [Nat.cast_mul, Nat.cast_pow] at this
    rw [Nat.cast_sub (by omega : 1 ≤ (D.mem u).A.T), Nat.cast_sub hT2] at this
    push_cast at this
    exact this
  have hpos : (0 : ℝ) < ((D.mem u).A.T : ℝ) - 1 := by
    have : (2 : ℝ) ≤ ((D.mem u).A.T : ℝ) := by exact_mod_cast hT2
    linarith
  have e : (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) = (((D.mem u).A.T : ℝ) - 2) / (((D.mem u).A.T : ℝ) - 1) := by
    field_simp; ring
  rw [e, div_pow]
  have hne : (((D.mem u).A.T : ℝ) - 1) ^ D.R.f ≠ 0 := pow_ne_zero _ hpos.ne'
  field_simp
  linarith [h']

theorem ramShare_of_trueD (D : D7) (u : D.what₂.Word) (hD : TrueD D) : RamShare D u :=
  TrueD.elim (Q := fun D => ∀ u : D.what₂.Word, RamShare D u)
    (fun _ _ _ _ _ w u => ramShare_of_freeT (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.freeT_0 (w.C.forms u).to0).some) hD u

end GlobalTheory.Core.Rk
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagCorollary
open Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.Core.Rk
open scoped InnerProductSpace

namespace GlobalTheory.Core.Rk

theorem dstar_pos_of (D : D7) (u : D.what₂.Word) : 0 < D.what₂.Dstar := by
  rw [← D.Dstar_eq u]; exact (D.mem u).A.Dstar_pos

theorem diagS_mono {D : D7} {u : D.what₂.Word} {e e' : ℝ} (h : DiagS D u e) (he : e ≤ e') : DiagS D u e' := by
  unfold DiagS at *
  exact h.trans (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _))

theorem kfk_nonneg (D : D7) : 0 ≤ kfk D := by
  unfold kfk
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Real.log_natCast_nonneg _)

theorem diag_corollary :
    (∀ (D : D7) (u : D.what₂.Word) (A x κ : ℝ), 0 ≤ A → TwoTerm D u A x → (d0 D u : ℝ) ≤ κ * D.what₂.Dstar →
      DiagS D u (A * κ + x)) ∧
    (∀ (D : D7) (u : D.what₂.Word) (L C : ℝ), 0 ≤ C * mfL D L → SDiag D u L C → Small D u L C →
      DiagS D u (eDiag D L C)) ∧
    (∀ (D : D7) (u : D.what₂.Word) (Γ₀ : ℝ), SAbs D u Γ₀ ↔ TwoTerm D u Γ₀ (1 / 4)) := by
  have first : ∀ (D : D7) (u : D.what₂.Word) (A x κ : ℝ), 0 ≤ A → TwoTerm D u A x → (d0 D u : ℝ) ≤ κ * D.what₂.Dstar →
      DiagS D u (A * κ + x) := by
    intro D u A x κ hA h hd
    have hD := dstar_pos_of D u
    have hd0 : (0 : ℝ) ≤ (d0 D u : ℝ) := Nat.cast_nonneg _
    have hq : (d0 D u : ℝ) ^ 2 / D.what₂.Dstar ≤ κ * (d0 D u : ℝ) := by
      rw [div_le_iff₀ hD]
      have := mul_le_mul_of_nonneg_left hd hd0
      nlinarith
    unfold DiagS
    unfold TwoTerm at h
    calc hsDev D u ≤ A * (d0 D u : ℝ) ^ 2 / D.what₂.Dstar + x * (d0 D u : ℝ) := h
      _ = A * ((d0 D u : ℝ) ^ 2 / D.what₂.Dstar) + x * (d0 D u : ℝ) := by rw [mul_div_assoc]
      _ ≤ A * (κ * (d0 D u : ℝ)) + x * (d0 D u : ℝ) := by gcongr
      _ = (A * κ + x) * (d0 D u : ℝ) := by ring
  refine ⟨first, ?_, ?_⟩
  · intro D u L C hc hS hSm
    set c := C * mfL D L with hcdef
    have h2 : Real.exp (-(2 * C * mfL D L)) = Real.exp (-c) * Real.exp (-c) := by
      rw [← Real.exp_add]; congr 1; rw [hcdef]; ring
    have h1 : Real.exp c * Real.exp (-c) = 1 := by rw [← Real.exp_add]; simp
    have hle : Real.exp (-c) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hpos : 0 < Real.exp (-c) := Real.exp_pos _
    have hk := kfk_nonneg D
    have hkk : Real.exp (-kfk D) ≤ Real.exp (-(kfk D / 2)) := Real.exp_le_exp.2 (by linarith)
    have hd := first D u (4 * (Real.exp c + 1)) (4 * Real.exp (-(kfk D / 2)) + 2 * Real.exp (-kfk D))
      (Real.exp (-(2 * C * mfL D L))) (by positivity) hS (by unfold Small at hSm; linarith [hSm])
    refine diagS_mono hd ?_
    unfold eDiag
    rw [h2, ← hcdef]
    have : 4 * (Real.exp c + 1) * (Real.exp (-c) * Real.exp (-c)) = 4 * Real.exp (-c) + 4 * (Real.exp (-c) * Real.exp (-c)) := by
      have e : 4 * (Real.exp c + 1) * (Real.exp (-c) * Real.exp (-c))
          = 4 * (Real.exp c * Real.exp (-c)) * Real.exp (-c) + 4 * (Real.exp (-c) * Real.exp (-c)) := by ring
      rw [e, h1]; ring
    rw [this]
    nlinarith
  · intro D u Γ₀
    unfold SAbs TwoTerm
    rw [show (1 / 4 : ℝ) * (d0 D u : ℝ) = (d0 D u : ℝ) / 4 by ring]

end GlobalTheory.Core.Rk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamBigOfRamShare
open Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.Core.Rk
open scoped InnerProductSpace

namespace GlobalTheory.Core.Rk

theorem ramBig_of_ramShare : ∀ (D : D7) (u : D.what₂.Word), RamShare D u → 0 < d0 D u → 2 < (D.mem u).A.T →
    RamBig D u ((D.R.f : ℝ) / (((D.mem u).A.T : ℝ) - 1)) := by
  intro D u hS hd hT
  have hT' : (2 : ℝ) < ((D.mem u).A.T : ℝ) := by exact_mod_cast hT
  have hpos : (0 : ℝ) < ((D.mem u).A.T : ℝ) - 1 := by linarith
  set a : ℝ := -(1 / (((D.mem u).A.T : ℝ) - 1)) with ha
  have ha1 : 1 / (((D.mem u).A.T : ℝ) - 1) < 1 := by
    rw [div_lt_one hpos]; linarith
  have ha0 : 0 < 1 / (((D.mem u).A.T : ℝ) - 1) := by positivity
  have hb : -2 ≤ a := by rw [ha]; linarith
  have hB := one_add_mul_le_pow hb D.R.f
  have hd' : (0 : ℝ) < (d0 D u : ℝ) := by exact_mod_cast hd
  unfold RamShare at hS
  unfold RamBig
  have hbase : 0 < 1 - 1 / (((D.mem u).A.T : ℝ) - 1) := by linarith
  have hp : 0 < (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) ^ D.R.f := pow_pos hbase _
  refine ⟨?_, ?_⟩
  · have : (0 : ℝ) < (dU D u : ℝ) := by rw [hS]; exact mul_pos hd' hp
    exact_mod_cast this
  · rw [hS]
    have e1 : 1 + a = 1 - 1 / (((D.mem u).A.T : ℝ) - 1) := by rw [ha]; ring
    rw [e1] at hB
    have e2 : 1 + (D.R.f : ℝ) * a = 1 - (D.R.f : ℝ) / (((D.mem u).A.T : ℝ) - 1) := by rw [ha]; ring
    rw [e2] at hB
    rw [mul_comm ((d0 D u : ℝ))]
    exact mul_le_mul_of_nonneg_right hB hd'.le

end GlobalTheory.Core.Rk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiveLeHalfKfk
open Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.Core.Rk
open scoped InnerProductSpace

namespace GlobalTheory.Core.Rk

theorem exp_neg_five_lt : Real.exp (-5) < 1 / 128 := by
  have h1 : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h5 : Real.exp 5 = Real.exp 1 ^ 5 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h2 : (2.7 : ℝ) ^ 5 < Real.exp 1 ^ 5 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  have h3 : (128 : ℝ) < Real.exp 5 := by
    rw [h5]; exact lt_trans (by norm_num) h2
  rw [Real.exp_neg, one_div]
  exact inv_strictAnti₀ (by norm_num) h3

theorem five_le_half_kfk (D : D7) : 5 ≤ kfk D / 2 := by
  have hk : 5 ≤ D.R.k := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    omega
  have hf : 2 ≤ D.R.f := by
    have h1 : 0 < D.R.n := D.R.toFrame.ord_pos
    have h2 : D.R.f = 2 * D.R.n := rfl
    omega
  have hkR : (5 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast hk
  have hfR : (2 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast hf
  have hlog : 1 ≤ Real.log (D.R.k : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hkf : (10 : ℝ) ≤ (D.R.k : ℝ) * D.R.f := by nlinarith
  have : (10 : ℝ) ≤ (D.R.k : ℝ) * D.R.f * Real.log (D.R.k : ℝ) := by nlinarith
  unfold kfk
  linarith

theorem two_eDiag_lt : ∀ (D : D7) (u : D.what₂.Word) (L C : ℝ), 5 ≤ C * mfL D L → 4 * D.R.f + 1 ≤ (D.mem u).A.T → 2 * eDiag D L C < 1 - (D.R.f : ℝ) / (((D.mem u).A.T : ℝ) - 1) := by
  intro D u L C hC hT
  have hf : 2 ≤ D.R.f := by
    have h1 : 0 < D.R.n := D.R.toFrame.ord_pos
    have h2 : D.R.f = 2 * D.R.n := rfl
    omega
  have hfR : (2 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast hf
  have hTR : 4 * (D.R.f : ℝ) + 1 ≤ ((D.mem u).A.T : ℝ) := by exact_mod_cast hT
  have hden : 0 < ((D.mem u).A.T : ℝ) - 1 := by linarith
  have hq : (D.R.f : ℝ) / (((D.mem u).A.T : ℝ) - 1) ≤ 1 / 4 := by
    rw [div_le_iff₀ hden]
    linarith
  have h5 := exp_neg_five_lt
  have hA : Real.exp (-(C * mfL D L)) ≤ Real.exp (-5) :=
    Real.exp_le_exp.mpr (by linarith)
  have hB : Real.exp (-(kfk D / 2)) ≤ Real.exp (-5) :=
    Real.exp_le_exp.mpr (by linarith [five_le_half_kfk D])
  unfold eDiag
  linarith

end GlobalTheory.Core.Rk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinrankKerPuLeHsDev
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinrankKerLeHilbertSchmidtNormSqSubId
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinrankKerLeHilbertSchmidtNormSqSubId
open Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory

theorem finrank_ker_le_hsNormSq_sub_id {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (K : V →L[ℂ] V) (N : Submodule ℂ V) (hN : ∀ x ∈ N, K x = 0) :
    (Module.finrank ℂ N : ℝ) ≤ hsNormSq (K - ContinuousLinearMap.id ℂ V) := by
  let b := stdOrthonormalBasis ℂ N
  let v : Fin (Module.finrank ℂ N) → V := fun i => (b i : V)
  have hv : Orthonormal ℂ v := b.orthonormal.comp_linearIsometry N.subtypeₗᵢ
  have h := GlobalTheory.T.sum_norm_sq_orthonormal_le_hilbertSchmidt (K - ContinuousLinearMap.id ℂ V) v hv
  have hterm : ∀ i, ‖(K - ContinuousLinearMap.id ℂ V) (v i)‖ ^ 2 = 1 := by
    intro i
    have hK : K (v i) = 0 := hN _ (b i).2
    have hn : ‖v i‖ = 1 := hv.1 i
    simp [hK, hn]
  have hsum : ∑ i, ‖(K - ContinuousLinearMap.id ℂ V) (v i)‖ ^ 2 = (Module.finrank ℂ N : ℝ) := by
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    simp
  rw [hsum] at h
  exact h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinrankKerLeHilbertSchmidtNormSqSubIdStatement
open Formalism.MainNotions.S
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_ker_le_hilbertSchmidtNormSq_sub_id : ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (K : V →L[ℂ] V) (N : Submodule ℂ V), (∀ x ∈ N, K x = 0) → (Module.finrank ℂ N : ℝ) ≤ hsNormSq (K - ContinuousLinearMap.id ℂ V) := by
  first | exact @GlobalTheory.finrank_ker_le_hsNormSq_sub_id | exact GlobalTheory.finrank_ker_le_hsNormSq_sub_id | (intros; apply GlobalTheory.finrank_ker_le_hsNormSq_sub_id <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.Core.Rk
open scoped InnerProductSpace

namespace GlobalTheory.Core.Rk

theorem finrank_ker_Pu_le_hsDev (D : D7) (u : D.what₂.Word) :
    (Module.finrank ℂ (LinearMap.ker (D.s.Pu u : D.s.Cu u →ₗ[ℂ] D.s.HH)) : ℝ) ≤ hsDev D u := by
  unfold hsDev
  refine GlobalTheory.T.finrank_ker_le_hilbertSchmidtNormSq_sub_id (Kmat D.s u u) _ ?_
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have hx' : D.s.Pu u x = 0 := hx
  simp [Kmat, hx']

end GlobalTheory.Core.Rk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeWindow
noncomputable section

namespace GlobalTheory.Core.Rk

open Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace

theorem levelPrime_window : ∀ (D : D7) (u : D.what₂.Word),
    (RankMu D u → (d0 D u : ℝ) ≤ Real.exp 1 / (D.mem u).A.GamP ^ 2 * D.what₂.Dstar) ∧
    (Real.log (D.mem u).A.Xu - 2 * Real.log (D.mem u).A.GamP / ((D.R.f : ℝ) * D.R.k) ≤ Real.log ((D.mem u).A.T : ℝ)) ∧
    (∀ L C : ℝ, RankMu D u → 1 + 2 * C * mfL D L ≤ 2 * Real.log (D.mem u).A.GamP → Small D u L C) := by
  intro D u
  have hfN : 1 ≤ D.R.f := by
    unfold Ranks.f Ranks.n
    have := Nat.one_le_two_pow (n := D.R.e)
    have := D.R.ord_pos
    omega
  have hkN : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hfN
  have hk : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hkN
  have hfk : (0 : ℝ) < (D.R.f : ℝ) * D.R.k := by positivity
  have hdu : (0 : ℝ) < (D.mem u).A.duStar := by exact_mod_cast (D.mem u).A.duStar_pos
  have hDs : 0 < (D.mem u).A.Dstar := (D.mem u).A.Dstar_pos
  have hDpos : 0 < D.what₂.Dstar := D.Dstar_eq u ▸ hDs
  have hq : 0 < (D.mem u).A.Dstar / (D.mem u).A.duStar := div_pos hDs hdu
  have hGp : 0 < (D.mem u).A.GamP := lt_trans one_pos (D.mem u).A.one_lt_gammaP
  have hXu : 0 < (D.mem u).A.Xu := Real.rpow_pos_of_pos hq _
  have hTs : 0 < (D.mem u).A.Tstar := mul_pos hXu (Real.rpow_pos_of_pos hGp _)
  have hlogTs : Real.log (D.mem u).A.Tstar =
      Real.log (D.mem u).A.Xu - 2 * Real.log (D.mem u).A.GamP / ((D.R.f : ℝ) * D.R.k) := by
    unfold ColumnsAtT.Tstar
    rw [Real.log_mul hXu.ne' (Real.rpow_pos_of_pos hGp _).ne', Real.log_rpow hGp]
    ring
  obtain ⟨hT1, hT2⟩ := D.T_win u
  have hT0 : (0 : ℝ) < ((D.mem u).A.T : ℝ) := hTs.trans_le hT1
  have part2 : Real.log (D.mem u).A.Xu - 2 * Real.log (D.mem u).A.GamP / ((D.R.f : ℝ) * D.R.k) ≤
      Real.log ((D.mem u).A.T : ℝ) := by
    rw [← hlogTs]; exact Real.log_le_log hTs hT1
  have hTs_pow : (D.mem u).A.Tstar ^ (D.R.f * D.R.k) =
      (D.mem u).A.Dstar / (D.mem u).A.duStar / (D.mem u).A.GamP ^ 2 := by
    have hn : ((D.R.f * D.R.k : ℕ) : ℝ) = (D.R.f : ℝ) * D.R.k := by push_cast; ring
    rw [← Real.rpow_natCast, hn]
    unfold ColumnsAtT.Tstar ColumnsAtT.Xu
    rw [Real.mul_rpow (Real.rpow_pos_of_pos hq _).le (Real.rpow_pos_of_pos hGp _).le, ← Real.rpow_mul hq.le,
      ← Real.rpow_mul hGp.le, one_div_mul_cancel hfk.ne', div_mul_cancel₀ _ hfk.ne', Real.rpow_one,
      Real.rpow_neg hGp.le, Real.rpow_two, div_eq_mul_inv _ ((D.mem u).A.GamP ^ 2)]
  have hexp : (1 + 1 / ((D.R.f : ℝ) * D.R.k)) ^ (D.R.f * D.R.k) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 / ((D.R.f : ℝ) * D.R.k))
    calc (1 + 1 / ((D.R.f : ℝ) * D.R.k)) ^ (D.R.f * D.R.k)
        ≤ Real.exp (1 / ((D.R.f : ℝ) * D.R.k)) ^ (D.R.f * D.R.k) :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = Real.exp 1 := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp
  have hTpow : ((D.mem u).A.T : ℝ) ^ (D.R.f * D.R.k) ≤
      Real.exp 1 * ((D.mem u).A.Dstar / (D.mem u).A.duStar / (D.mem u).A.GamP ^ 2) := by
    calc ((D.mem u).A.T : ℝ) ^ (D.R.f * D.R.k)
        ≤ ((1 + 1 / ((D.R.f : ℝ) * D.R.k)) * (D.mem u).A.Tstar) ^ (D.R.f * D.R.k) :=
          pow_le_pow_left₀ hT0.le hT2 _
      _ = (1 + 1 / ((D.R.f : ℝ) * D.R.k)) ^ (D.R.f * D.R.k) *
          ((D.mem u).A.Dstar / (D.mem u).A.duStar / (D.mem u).A.GamP ^ 2) := by
          rw [mul_pow, hTs_pow]
      _ ≤ _ := mul_le_mul_of_nonneg_right hexp (by positivity)
  have part1 : RankMu D u → (d0 D u : ℝ) ≤ Real.exp 1 / (D.mem u).A.GamP ^ 2 * D.what₂.Dstar := by
    intro h
    unfold RankMu at h
    rw [h]
    have hT1' : (1 : ℝ) ≤ ((D.mem u).A.T : ℝ) := by
      have : 0 < (D.mem u).A.T := by exact_mod_cast hT0
      exact_mod_cast this
    have hTk : 1 ≤ ((D.mem u).A.T : ℝ) ^ D.R.k := one_le_pow₀ hT1'
    have h1 : (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f ≤ ((D.mem u).A.T : ℝ) ^ (D.R.f * D.R.k) := by
      rw [mul_comm, pow_mul]
      exact pow_le_pow_left₀ (by linarith) (by linarith) _
    calc ((D.mem u).A.duStar : ℝ) * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f
        ≤ ((D.mem u).A.duStar : ℝ) *
          (Real.exp 1 * ((D.mem u).A.Dstar / (D.mem u).A.duStar / (D.mem u).A.GamP ^ 2)) :=
          mul_le_mul_of_nonneg_left (h1.trans hTpow) hdu.le
      _ = Real.exp 1 / (D.mem u).A.GamP ^ 2 * D.what₂.Dstar := by
          rw [← D.Dstar_eq u]
          first | (field_simp; ring) | field_simp
  refine ⟨part1, part2, fun L C hR hLC => ?_⟩
  unfold Small
  have hG2 : Real.exp (2 * Real.log (D.mem u).A.GamP) = (D.mem u).A.GamP ^ 2 := by
    rw [show 2 * Real.log (D.mem u).A.GamP = Real.log ((D.mem u).A.GamP ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity)]
  calc (d0 D u : ℝ) ≤ Real.exp 1 / (D.mem u).A.GamP ^ 2 * D.what₂.Dstar := part1 hR
    _ = D.what₂.Dstar * Real.exp (1 - 2 * Real.log (D.mem u).A.GamP) := by
        rw [Real.exp_sub, hG2]; ring
    _ ≤ D.what₂.Dstar * Real.exp (-(2 * C * mfL D L)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hDpos.le

end GlobalTheory.Core.Rk

end
end

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MiTop

open GlobalTheory.Core.Rk

theorem trueE_of_trueD {D : D7} (h : TrueD D) : TrueE D :=
  let ⟨B, X, I, l, Z, e, ⟨w⟩⟩ := h; ⟨B, X, I, l, Z, e, w, w.S.pin⟩

theorem puNZ_at (D : D7) (u : D.what₂.Word) (e δ : ℝ) (hS : DiagS D u e) (hR : RamBig D u δ) (hlt : e < 1 - δ)
    (hd : 0 < d0 D u) : ∃ φ : (D.mem u).A.Mram, D.s.Pu u ((D.s_Cu u).symm ⟨φ.1, φ.2.1⟩) ≠ 0 := by
  by_contra hne
  push_neg at hne
  let FF : (D.mem u).A.Mram →ₗ[ℂ] D.s.Cu u :=
    (D.s_Cu u).symm.toLinearMap ∘ₗ Submodule.inclusion (inf_le_left : (D.mem u).A.Mram ≤ (D.mem u).A.Mu0)
  have hFF : Function.Injective FF := (D.s_Cu u).symm.injective.comp (Submodule.inclusion_injective _)
  have hle : Module.finrank ℂ (D.mem u).A.Mram ≤
      Module.finrank ℂ (LinearMap.ker (D.s.Pu u : D.s.Cu u →ₗ[ℂ] D.s.HH)) := by
    let g : (D.mem u).A.Mram →ₗ[ℂ] LinearMap.ker (D.s.Pu u : D.s.Cu u →ₗ[ℂ] D.s.HH) :=
      FF.codRestrict _ (fun φ => by rw [LinearMap.mem_ker]; exact hne φ)
    exact LinearMap.finrank_le_finrank_of_injective (f := g) (fun x y h => hFF (congrArg Subtype.val h))
  have hk := finrank_ker_Pu_le_hsDev D u
  obtain ⟨-, hbig⟩ := hR
  have hU : (GlobalTheory.Core.Rk.dU D u : ℝ) ≤ (Module.finrank ℂ (LinearMap.ker (D.s.Pu u : D.s.Cu u →ₗ[ℂ] D.s.HH)) : ℝ) := by
    unfold GlobalTheory.Core.Rk.dU; exact_mod_cast hle
  have hd' : (0 : ℝ) < (d0 D u : ℝ) := by exact_mod_cast hd
  unfold DiagS at hS
  have : (1 - δ) * (d0 D u : ℝ) ≤ e * (d0 D u : ℝ) := by linarith
  have := le_of_mul_le_mul_right this hd'
  linarith

theorem puNZ_of_sDiag {D : D7} (large₂ : SizeData₂ D) {C C' Cl Cg cb Cu cT CT : ℝ} (hC : 1 ≤ C) (hCG : C + 1 ≤ large₂.CGam) (hD : TrueD D)
    (hH : GlobalTheory.Core.Rk.HD D large₂.sc.L C' Cl Cg cb Cu cT CT) (hmu : ∀ u, RankMu D u) (hS : ∀ u, SDiag D u large₂.sc.L C) : PuNZ D := by
  intro u
  obtain ⟨hm, hT, hd, -⟩ := hd_numbers D u _ C' Cl Cg cb Cu cT CT hH
  have hG : Real.log (D.mem u).A.GamP = large₂.CGam * mfL D large₂.sc.L := by rw [large₂.Gam_eq u]; unfold mfL; ring
  have hw : 1 + 2 * C * mfL D large₂.sc.L ≤ 2 * Real.log (D.mem u).A.GamP := by rw [hG]; nlinarith
  have hCm : 5 ≤ C * mfL D large₂.sc.L := by nlinarith
  have hdiag := diag_corollary.2.1 D u _ C (by linarith) (hS u) ((levelPrime_window D u).2.2 _ C (hmu u) hw)
  have hf : D.R.f ≠ 0 := by
    intro h0
    unfold mfL at hm
    rw [h0] at hm
    norm_num at hm
  have hR := ramBig_of_ramShare D u (ramShare_of_trueD D u hD) hd (by omega)
  have h2 := two_eDiag_lt D u _ C hCm hT
  have h0 : 0 ≤ eDiag D large₂.sc.L C := by unfold eDiag; positivity
  exact puNZ_at D u _ _ hdiag hR (by linarith) hd

theorem evP_cGam (J : ℝ → ℝ → ℝ) : EvP fun κ _ => J (κ.C.P.CYL + 1) κ.C.CTu ≤ κ.C.CGam :=
  ⟨1, one_pos, fun _ _ _ _ _ _ _ _ _ =>
    ⟨⟨0, fun _ => 0, fun l => J (l.getD 6 0 + 1) (l.getD 13 0), fun _ => 0⟩, fun C _ _ hL =>
      ⟨0, fun _ _ => ⟨0, fun _ _ _ => ⟨0, fun _ _ _ => hL.2.2.1 C.CGam (by simp [Formalism.MainNotions.Inhab.FC.cMid])⟩⟩⟩⟩⟩

end GlobalTheory.MiTop
