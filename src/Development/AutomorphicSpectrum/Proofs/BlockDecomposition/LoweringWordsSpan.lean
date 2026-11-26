module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMapIntertwinesRestriction

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CasimirElement
noncomputable def UpperTheory.Reformulated.B.CasimirElement.casC :
    {n : ℕ} → (Fin n → ℂ) → ℂ :=
    fun {n : ℕ} (τ : Fin n → ℂ) ↦
      ∑ a : Fin n, τ a ^ (2 : ℕ) + ∑ a : Fin n, ∑ b : Fin n, if a < b then τ a - τ b else (0 : ℂ)

namespace YgaHelp

private lemma inner_left {n : ℕ} (σ : Fin n → ℂ) (a : Fin n) :
    (∑ b : Fin n, if a < b then σ a else (0 : ℂ)) = σ a * (((n : ℂ) - 1) - ((a : ℕ) : ℂ)) := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    Finset.filter_lt_eq_Ioi, Fin.card_Ioi, nsmul_eq_mul]
  have h : (a : ℕ) ≤ n - 1 := by omega
  have h1 : 1 ≤ n := by omega
  rw [Nat.cast_sub h, Nat.cast_sub h1]
  push_cast; ring

private lemma inner_right {n : ℕ} (σ : Fin n → ℂ) (b : Fin n) :
    (∑ a : Fin n, if a < b then σ b else (0 : ℂ)) = σ b * ((b : ℕ) : ℂ) := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    Finset.filter_gt_eq_Iio, Fin.card_Iio, nsmul_eq_mul]
  ring

end YgaHelp

theorem UpperTheory.Reformulated.B.CasimirElement.main :
    ∀ {n : ℕ} (σ : Fin n → ℂ),
      UpperTheory.Reformulated.B.CasimirElement.casC σ =
        ∑ a : Fin n, σ a ^ (2 : ℕ) + ∑ a : Fin n, σ a * ((↑n : ℂ) - (1 : ℂ) - (2 : ℂ) * (↑(↑a : ℕ) : ℂ)) := by
  intro n σ
  unfold UpperTheory.Reformulated.B.CasimirElement.casC
  congr 1
  have hsplit : ∀ a b : Fin n, (if a < b then σ a - σ b else (0 : ℂ)) =
      (if a < b then σ a else 0) - (if a < b then σ b else 0) := by
    intro a b; split_ifs <;> simp
  simp_rw [hsplit, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun a b => if a < b then σ b else (0 : ℂ))]
  simp_rw [YgaHelp.inner_left, YgaHelp.inner_right]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro a _
  ring
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleLoweringPowMemIdeal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleLoweringPowMemIdeal
set_option maxSynthPendingDepth 1

noncomputable section

open GroundTheory.Automorphic.HarishChandra

namespace GlobalTheory.CompanionTheory.PresRho

variable {n : ℕ}

def adL (F u : U n) : U n := F * u - u * F

theorem adL_zero (F : U n) : adL F 0 = 0 := by simp [adL]

theorem adL_sub (F u v : U n) : adL F (u - v) = adL F u - adL F v := by
  simp only [adL, mul_sub, sub_mul]; abel

theorem adL_neg (F u : U n) : adL F (-u) = - adL F u := by
  simp only [adL, mul_neg, neg_mul]; abel

theorem adL_e (i j c d : Fin n) :
    adL (e (j, i)) (e (c, d)) =
      (if i = c then e (j, d) else 0) - (if d = j then e (c, i) else 0) :=
  e_mul_sub_mul (j, i) (c, d)

theorem adL_iter_e {i j : Fin n} (hij : i ≠ j) (a : Fin n × Fin n) :
    (adL (e (j, i)))^[3] (e a) = 0 := by
  obtain ⟨c, d⟩ := a
  show adL (e (j, i)) (adL (e (j, i)) (adL (e (j, i)) (e (c, d)))) = 0
  have hji : j ≠ i := hij.symm
  by_cases h1 : i = c <;> by_cases h2 : d = j
  · subst h1; subst h2
    simp [adL_e, adL_sub, adL_neg, adL_zero, hij, hji]
  · subst h1
    simp [adL_e, adL_sub, adL_neg, adL_zero, hij, hji, h2]
  · subst h2
    simp [adL_e, adL_sub, adL_neg, adL_zero, hij, hji, h1]
  · simp [adL_e, adL_sub, adL_neg, adL_zero, h1, h2]

theorem pow_mul_mem_Jp_of_le {F w : U n} {N N' : ℕ} (h : N ≤ N') (hw : F ^ N * w ∈ Jp n) :
    F ^ N' * w ∈ Jp n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' h
  rw [pow_add, mul_assoc]
  exact mul_mem_Jp _ hw

theorem exists_pow_mul_mul_mem (F : U n) (s : ℕ) :
    ∀ (r M : ℕ) (u y : U n), r + M = s → (adL F)^[r] u = 0 → F ^ M * y ∈ Jp n →
      ∃ N : ℕ, F ^ N * (u * y) ∈ Jp n := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro r M u y hs hu hy
    rcases M with _ | M
    · refine ⟨0, ?_⟩
      rw [pow_zero, one_mul] at hy ⊢
      exact mul_mem_Jp u hy
    rcases r with _ | r
    · refine ⟨0, ?_⟩
      have : u = 0 := hu
      simp [this]
    obtain ⟨N₁, h₁⟩ := ih (r + 1 + M) (by omega) (r + 1) M u (F * y) rfl hu
      (by rw [← mul_assoc, ← pow_succ]; exact hy)
    obtain ⟨N₂, h₂⟩ := ih (r + (M + 1)) (by omega) r (M + 1) (adL F u) y rfl
      (by rw [← Function.iterate_succ_apply]; exact hu) hy
    refine ⟨max N₁ N₂ + 1, ?_⟩
    have key : F ^ (max N₁ N₂ + 1) * (u * y) =
        F ^ max N₁ N₂ * (u * (F * y)) + F ^ max N₁ N₂ * (adL F u * y) := by
      rw [pow_succ, ← mul_add, mul_assoc]
      congr 1
      simp only [adL, sub_mul, mul_assoc]
      abel
    rw [key]
    exact Submodule.add_mem _ (pow_mul_mem_Jp_of_le (le_max_left _ _) h₁)
      (pow_mul_mem_Jp_of_le (le_max_right _ _) h₂)

theorem lower_locally_nilpotent {n : ℕ} (i j : Fin n) (x : U n) (hij : (j : ℕ) = i + 1) :
    ∃ N : ℕ, e (j, i) ^ N * x ∈ Jp n := by
  have hne : i ≠ j := by
    intro h
    rw [h] at hij
    omega
  have step : ∀ v : U n, ∀ y : U n, (∃ N : ℕ, e (j, i) ^ N * y ∈ Jp n) →
      ∃ N : ℕ, e (j, i) ^ N * (v * y) ∈ Jp n := by
    intro v
    induction v using U.induction with
    | halg r =>
      rintro y ⟨N, hN⟩
      refine ⟨N, ?_⟩
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_comm]
      exact Submodule.smul_mem _ r hN
    | hι X =>
      intro y hy
      obtain ⟨M, hM⟩ := hy
      have hsum : ∀ t : Finset (Fin n × Fin n), ∃ N : ℕ, e (j, i) ^ N *
          ((∑ a ∈ t, X a.1 a.2 • e (n := n) a) * y) ∈ Jp n := by
        intro t
        induction t using Finset.induction_on with
        | empty => exact ⟨0, by simp⟩
        | insert a t ha ih =>
          obtain ⟨N₁, h₁⟩ := ih
          obtain ⟨N₂, h₂⟩ := exists_pow_mul_mul_mem (e (j, i)) (3 + M) 3 M (e a) y rfl
            (adL_iter_e hne a) hM
          refine ⟨max N₁ N₂, ?_⟩
          rw [Finset.sum_insert ha, add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
          exact Submodule.add_mem _
            (Submodule.smul_mem _ _ (pow_mul_mem_Jp_of_le (le_max_right _ _) h₂))
            (pow_mul_mem_Jp_of_le (le_max_left _ _) h₁)
      rw [ι_eq_sum_e]
      exact hsum Finset.univ
    | hmul a b ha hb =>
      intro y hy
      rw [mul_assoc]
      exact ha _ (hb _ hy)
    | hadd a b ha hb =>
      intro y hy
      obtain ⟨N₁, h₁⟩ := ha y hy
      obtain ⟨N₂, h₂⟩ := hb y hy
      refine ⟨max N₁ N₂, ?_⟩
      rw [add_mul, mul_add]
      exact Submodule.add_mem _ (pow_mul_mem_Jp_of_le (le_max_left _ _) h₁)
        (pow_mul_mem_Jp_of_le (le_max_right _ _) h₂)
  have h1 : ∃ N : ℕ, e (j, i) ^ N * (1 : U n) ∈ Jp n :=
    ⟨2, by simpa using mul_sq_mem_Jp (1 : U n) hij⟩
  simpa using step x 1 h1

end GlobalTheory.CompanionTheory.PresRho
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleLoweringPowMemIdealStatement
open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simple_lowering_pow_mem_ideal : ∀ {n : ℕ} (i j : Fin n) (x : U n), (j : ℕ) = i + 1 → ∃ N : ℕ, e (j, i) ^ N * x ∈ Jp n := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.lower_locally_nilpotent | exact GlobalTheory.CompanionTheory.PresRho.lower_locally_nilpotent | (intros; apply GlobalTheory.CompanionTheory.PresRho.lower_locally_nilpotent <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorSpannedByWeightVectors
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorSpannedByWeightVectors
noncomputable section

open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho

namespace GlobalTheory.CompanionTheory.PresRho

theorem eq_zero_of_sum_weightVec {ι κ A : Type} [DecidableEq ι] [AddCommGroup A] [Module ℂ A]
    (T : κ → Module.End ℂ A) (f : ι → κ → ℂ) (hf : Function.Injective f) (s : Finset ι) :
    ∀ v : ι → A, (∀ i ∈ s, ∀ k, T k (v i) = f i k • v i) → ∑ i ∈ s, v i = 0 →
      ∀ i ∈ s, v i = 0 :=
  _root_.UpperTheory.Reformulated.B.P6.r14a.GlobalTheory.CompanionTheory.PresRho.eq_zero_of_sum_weightVec T f hf s

def wtPart {n : ℕ} (x : U n) (w : Fin n → ℤ) : U n :=
  ∑ m ∈ (pbw.repr x).support.filter (fun m => wt m = w), pbw.repr x m • canon m

theorem isAdW_wtPart {n : ℕ} (x : U n) (w : Fin n → ℤ) : IsAdW w (wtPart x w) := by
  intro k
  simp only [wtPart, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, e_diag_mul_canon_sub,
    (Finset.mem_filter.1 hm).2, smul_comm]

theorem sum_wtPart {n : ℕ} (x : U n) :
    ∑ w ∈ (pbw.repr x).support.image wt, wtPart x w = x := by
  simp only [wtPart]
  rw [Finset.sum_fiberwise_of_maps_to (fun m hm => Finset.mem_image_of_mem _ hm)]
  exact sum_repr_canon x

theorem mem_span_isAdW_of_kills {n : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A]
    (φ : U n →ₐ[ℂ] Module.End ℂ A) (t : A) (hd : ∀ k, φ (e (k, k)) t = rhoVec n k • t)
    (x : U n) (hx : φ x t = 0) :
    x ∈ Submodule.span ℂ {y : U n | ∃ μ : Fin n → ℤ, IsAdW μ y ∧ φ y t = 0} := by
  classical
  have hinj : Function.Injective (fun (w : Fin n → ℤ) (k : Fin n) => rhoVec n k + (w k : ℂ)) := by
    intro w w' h
    funext k
    have := congrFun h k
    simpa using this
  have hz := eq_zero_of_sum_weightVec (fun k : Fin n => φ (e (k, k)))
    (fun (w : Fin n → ℤ) k => rhoVec n k + (w k : ℂ)) hinj ((pbw.repr x).support.image wt)
    (fun w => φ (wtPart x w) t)
    (fun w _ k => by
      have h1 : e (k, k) * wtPart x w = wtPart x w * e (k, k) + (w k : ℂ) • wtPart x w := by
        rw [← isAdW_wtPart x w k]; abel
      have h2 := congrArg (fun u => φ u t) h1
      simp only [map_mul, map_add (f := _), map_smul, Module.End.mul_apply, LinearMap.add_apply,
        LinearMap.smul_apply, hd k, add_smul] at h2 ⊢
      rw [h2])
    (by
      have h3 := congrArg (fun u => φ u t) (sum_wtPart x)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, LinearMap.sum_apply] at h3
      rw [h3, hx])
  rw [← sum_wtPart x]
  exact Submodule.sum_mem _ fun w hw => Submodule.subset_span ⟨w, isAdW_wtPart x w, hz w hw⟩

end GlobalTheory.CompanionTheory.PresRho
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorSpannedByWeightVectorsStatement
open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.annihilator_spanned_by_weight_vectors : ∀ {n : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A] (φ : U n →ₐ[ℂ] Module.End ℂ A) (t : A), (∀ k, φ (e (k, k)) t = rhoVec n k • t) → ∀ x : U n, φ x t = 0 → x ∈ Submodule.span ℂ {y : U n | ∃ μ : Fin n → ℤ, IsAdW μ y ∧ φ y t = 0} := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.mem_span_isAdW_of_kills | exact GlobalTheory.CompanionTheory.PresRho.mem_span_isAdW_of_kills | (intros; apply GlobalTheory.CompanionTheory.PresRho.mem_span_isAdW_of_kills <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightVectorMemLowSpanSupVerma
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightVectorMemLowSpanSupVerma
set_option maxSynthPendingDepth 1

noncomputable section

open GroundTheory.Automorphic.HarishChandra

namespace GlobalTheory.CompanionTheory.PresRho

variable {n : ℕ}

namespace Verma

def lowPart (m : Fin n × Fin n →₀ ℕ) : Fin n × Fin n →₀ ℕ := m.filter fun a => IsLower a

theorem lowExp_lowPart (m : Fin n × Fin n →₀ ℕ) : LowExp (lowPart m) := by
  intro a ha
  rw [lowPart, Finsupp.support_filter, Finset.mem_filter] at ha
  exact ha.2

theorem canon_lowPart (m : Fin n × Fin n →₀ ℕ) :
    canon (lowPart m) = word (blockW (lowL n) m) := by
  have hd : ∀ a ∈ diagL n, lowPart m a = 0 := fun a ha => by
    rw [lowPart, Finsupp.filter_apply_neg]
    exact not_lower_of_diag (mem_diagL.1 ha)
  have hu : ∀ a ∈ upL n, lowPart m a = 0 := fun a ha => by
    rw [lowPart, Finsupp.filter_apply_neg]
    exact not_lower_of_upper (mem_upL.1 ha)
  rw [canon_eq_blocks, blockW_eq_nil hd, blockW_eq_nil hu]
  simp only [word_nil, mul_one]
  refine congrArg word (blockW_congr fun a ha => ?_)
  rw [lowPart, Finsupp.filter_apply_pos _ _ (mem_lowL.1 ha)]

theorem wt_lowPart {m : Fin n × Fin n →₀ ℕ} (hu : ¬ HasUpper m) : wt (lowPart m) = wt m := by
  funext k
  rw [wt, wt, lowPart, Finsupp.sum_filter_index, Finsupp.support_filter, Finsupp.sum]
  refine Finset.sum_filter_of_ne fun a ha hne => ?_
  rcases lt_trichotomy a.1 a.2 with h | h | h
  · exact absurd ⟨a, h, Finsupp.mem_support_iff.1 ha⟩ hu
  · exfalso
    apply hne
    have : rootAt a k = 0 := by simp [rootAt, h]
    rw [this, mul_zero]
  · exact h

theorem wt_eq_of_mem_support {μ : Fin n → ℤ} {x : U n} (hx : IsAdW μ x)
    {m : Fin n × Fin n →₀ ℕ} (hm : m ∈ (pbw.repr x).support) : wt m = μ := by
  funext k
  set s := (pbw.repr x).support
  set c := fun m => pbw.repr x m
  have hxs : x = ∑ m ∈ s, c m • canon m := (sum_repr_canon x).symm
  have h0 : ∑ m ∈ s, (c m * ((wt m k : ℂ) - (μ k : ℂ))) • canon m = 0 := by
    have h1 := sub_eq_zero.2 (hx k)
    rw [← h1]
    conv_rhs => rw [hxs]
    rw [Finset.mul_sum, Finset.sum_mul, Finset.smul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, e_diag_mul_canon_sub, smul_smul, smul_smul,
      ← sub_smul, mul_sub, mul_comm (μ k : ℂ)]
  have h2 := linearIndependent_iff'.1 linearIndependent_canon s _ h0 m hm
  have hc : c m ≠ 0 := Finsupp.mem_support_iff.1 hm
  have h3 := sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left hc)
  exact_mod_cast h3

theorem canon_mem {μ : Fin n → ℤ} {m : Fin n × Fin n →₀ ℕ} (hw : wt m = μ) :
    canon m ∈ lowSpanW μ ⊔ vermaIdeal (rhoVec n) := by
  by_cases hu : HasUpper m
  · exact Submodule.mem_sup_right (nPlusU_le_vermaIdeal _ (canon_mem_nPlusU hu))
  · have hnil : blockW (upL n) m = [] := blockW_eq_nil fun a ha => by
      by_contra h
      exact hu ⟨a, mem_upL.1 ha, h⟩
    set p : MvPolynomial (Fin n) ℂ := MvPolynomial.monomial (diagExp m) 1
    set ev : ℂ := MvPolynomial.eval (rhoVec n) p
    have hdec : canon m = ev • canon (lowPart m) +
        word (blockW (lowL n) m) * (hcEmb p - algebraMap ℂ (U n) ev) := by
      rw [canon_eq_triangular, hnil, canon_lowPart, mul_sub, word_nil, mul_one,
        Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
      abel
    rw [hdec]
    refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨lowPart m, lowExp_lowPart m, (wt_lowPart hu).trans hw, rfl⟩)) ?_
    exact mul_mem_vermaIdeal _ _ (hcEmb_sub_eval_mem_vermaIdeal _ p)

end Verma

theorem mem_lowSpanW_sup_vermaIdeal_of_isAdW {n : ℕ} (μ : Fin n → ℤ) (x : U n) (hx : IsAdW μ x) :
    x ∈ lowSpanW μ ⊔ vermaIdeal (rhoVec n) := by
  rw [← sum_repr_canon x]
  exact Submodule.sum_mem _ fun m hm =>
    Submodule.smul_mem _ _ (Verma.canon_mem (Verma.wt_eq_of_mem_support hx hm))

end GlobalTheory.CompanionTheory.PresRho
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightVectorMemLowSpanSupVermaStatement
open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_vector_mem_low_span_sup_verma : ∀ {n : ℕ} (μ : Fin n → ℤ) (x : U n), IsAdW μ x → x ∈ lowSpanW μ ⊔ vermaIdeal (rhoVec n) := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.mem_lowSpanW_sup_vermaIdeal_of_isAdW | exact GlobalTheory.CompanionTheory.PresRho.mem_lowSpanW_sup_vermaIdeal_of_isAdW | (intros; apply GlobalTheory.CompanionTheory.PresRho.mem_lowSpanW_sup_vermaIdeal_of_isAdW <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowSpanInfIdealLeSquareSpan
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowSpanInfIdealLeSquareSpan
set_option maxSynthPendingDepth 1

open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho

namespace GlobalTheory.CompanionTheory.PresRho.LowMeet

variable {n : ℕ}

theorem not_hasUpper {m : Fin n × Fin n →₀ ℕ} (hm : LowExp m) : ¬ HasUpper m := by
  rintro ⟨a, ha, hne⟩
  exact not_lower_of_upper ha (hm a (Finsupp.mem_support_iff.2 hne))

theorem lowPart_eq {m : Fin n × Fin n →₀ ℕ} (hm : LowExp m) : lowPart m = m := by
  ext a
  simp only [lowPart, Finsupp.filter_apply]
  split_ifs with h
  · rfl
  · by_contra hne
    exact h (hm a (Finsupp.mem_support_iff.2 (Ne.symm hne)))

theorem diagExp_eq {m : Fin n × Fin n →₀ ℕ} (hm : LowExp m) : diagExp m = 0 := by
  ext i
  rw [diagExp_apply]
  by_contra hne
  exact not_lower_of_diag (a := (i, i)) rfl (hm (i, i) (Finsupp.mem_support_iff.2 hne))

theorem recover (lam : Fin n → ℂ) {x : U n} (hx : x ∈ lowSpan n) :
    Finsupp.linearCombination ℂ (canon (n := n)) (vermaCoord lam x) = x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    rw [vermaCoord_canon_of_not lam (not_hasUpper hm), lowPart_eq hm, diagExp_eq hm]
    simp
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | smul r x _ hx => rw [map_smul, map_smul, hx]

theorem eq_zero_of_mem (lam : Fin n → ℂ) {x : U n} (hx : x ∈ lowSpan n)
    (hJ : x ∈ vermaIdeal lam) : x = 0 := by
  rw [← recover lam hx, vermaCoord_vermaIdeal lam hJ, map_zero]

theorem canonSpan_lower_le (lo hi : ℕ) : canonSpan (IsLower (n := n)) lo hi ≤ lowSpan n := by
  refine Submodule.span_mono ?_
  rintro _ ⟨m, hm, -, -, rfl⟩
  exact ⟨m, hm, rfl⟩

theorem word_mem_lowSpan {w : List (Fin n × Fin n)} (hw : ∀ a ∈ w, IsLower a) :
    word w ∈ lowSpan n :=
  canonSpan_lower_le _ _ (word_mem_canonSpan closed_lower w hw)

theorem isLower_simple {i j : Fin n} (hij : (j : ℕ) = i + 1) : IsLower (j, i) := by
  simp only [IsLower]; rw [Fin.lt_def, hij]; omega

theorem mul_sq_mem_lowSpan {a : Fin n × Fin n} (ha : IsLower a) {x : U n} (hx : x ∈ lowSpan n) :
    x * e a ^ 2 ∈ lowSpan n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    have h : canon m * e a ^ 2 = word (expand m ++ [a, a]) := by
      rw [word_append, word_cons, word_singleton, pow_two]; rfl
    rw [h]
    refine word_mem_lowSpan fun b hb => ?_
    rcases List.mem_append.1 hb with hb | hb
    · exact hm b (mem_support_of_mem_expand hb)
    · simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hb
      rw [hb]; exact ha
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

def lowSq (n : ℕ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {x | ∃ (v : U n) (i j : Fin n), v ∈ lowSpan n ∧ (j : ℕ) = i + 1 ∧
    v * e (j, i) ^ 2 = x}

theorem lowSq_le_lowSpan : lowSq n ≤ lowSpan n := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨v, i, j, hv, hij, rfl⟩
  exact mul_sq_mem_lowSpan (isLower_simple hij) hv

theorem lowSq_le_sqSpan : lowSq n ≤ sqSpan n := by
  refine Submodule.span_mono ?_
  rintro _ ⟨v, i, j, -, hij, rfl⟩
  exact ⟨v, i, j, hij, rfl⟩

theorem canon_mul_sq_mem (m : Fin n × Fin n →₀ ℕ) {i j : Fin n} (hij : (j : ℕ) = i + 1) :
    canon m * e (j, i) ^ 2 ∈ lowSq n ⊔ vermaIdeal (rhoVec n) := by
  by_cases h : HasUpper m
  · refine Submodule.mem_sup_right ?_
    exact mul_pow_mem_vermaIdeal hij (rhoVec n) 1 (by rw [rhoVec_sub hij]; simp)
      (canon_mem_nPlusU h)
  · have hup : ∀ a ∈ upL n, m a = 0 := fun a ha => by
      by_contra hne; exact h ⟨a, mem_upL.1 ha, hne⟩
    set low := word (blockW (lowL n) m) with hlow
    have hlowS : low ∈ lowSpan n :=
      word_mem_lowSpan fun a ha => mem_lowL.1 (mem_of_mem_blockW ha).1
    set p := MvPolynomial.monomial (diagExp m) (1 : ℂ)
    set q := translate (fun k => ((2 : ℕ) : ℂ) * rootAt (j, i) k) p
    have hc : canon m * e (j, i) ^ 2 = low * e (j, i) ^ 2 * hcEmb q := by
      rw [canon_eq_triangular, blockW_eq_nil hup, word_nil, mul_one, mul_assoc,
        hcEmb_mul_e_pow, mul_assoc]
    have hs : canon m * e (j, i) ^ 2 =
        MvPolynomial.eval (rhoVec n) q • (low * e (j, i) ^ 2) +
          low * e (j, i) ^ 2 * (hcEmb q - algebraMap ℂ (U n) (MvPolynomial.eval (rhoVec n) q)) := by
      rw [hc, mul_sub, ← Algebra.commutes, ← Algebra.smul_def]
      abel
    rw [hs]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _ ?_))
      (Submodule.mem_sup_right
        (mul_mem_vermaIdeal _ _ (hcEmb_sub_eval_mem_vermaIdeal (rhoVec n) q)))
    exact Submodule.subset_span ⟨low, i, j, hlowS, hij, rfl⟩

theorem mul_sq_mem (u : U n) {i j : Fin n} (hij : (j : ℕ) = i + 1) :
    u * e (j, i) ^ 2 ∈ lowSq n ⊔ vermaIdeal (rhoVec n) := by
  have hu : u ∈ Submodule.span ℂ (Set.range (canon (n := n))) := by
    rw [span_canon_eq_top]; trivial
  induction hu using Submodule.span_induction with
  | mem x hx => obtain ⟨m, rfl⟩ := hx; exact canon_mul_sq_mem m hij
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

theorem Jp_le : Jp n ≤ lowSq n ⊔ vermaIdeal (rhoVec n) := by
  refine sup_le le_sup_right (Submodule.span_le.2 ?_)
  rintro _ ⟨u, i, j, hij, rfl⟩
  exact mul_sq_mem u hij

theorem mem_sqSpan_of_mem_lowSpan_of_mem_Jp : ∀ {n : ℕ} (x : U n), x ∈ lowSpan n → x ∈ Jp n →
    x ∈ sqSpan n := by
  intro n x hx hJ
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 (Jp_le hJ)
  have ht0 : t = 0 := by
    refine eq_zero_of_mem (rhoVec n) ?_ ht
    have := Submodule.sub_mem _ hx (lowSq_le_lowSpan hs)
    rwa [add_sub_cancel_left] at this
  rw [ht0, add_zero]
  exact lowSq_le_sqSpan hs

end GlobalTheory.CompanionTheory.PresRho.LowMeet
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowSpanInfIdealLeSquareSpanStatement
open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.low_span_inf_ideal_le_square_span : ∀ {n : ℕ} (x : U n), x ∈ lowSpan n → x ∈ Jp n → x ∈ sqSpan n := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.LowMeet.mem_sqSpan_of_mem_lowSpan_of_mem_Jp | exact GlobalTheory.CompanionTheory.PresRho.LowMeet.mem_sqSpan_of_mem_lowSpan_of_mem_Jp | (intros; apply GlobalTheory.CompanionTheory.PresRho.LowMeet.mem_sqSpan_of_mem_lowSpan_of_mem_Jp <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NatOfSimpleLoweringNilpotent
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NatOfSimpleLoweringNilpotent
set_option maxSynthPendingDepth 1

noncomputable section

open GroundTheory.Automorphic.HarishChandra

namespace GlobalTheory.CompanionTheory.PresRho

variable {n : ℕ}

theorem e_upper_mul_pow_succ_eq {i j : Fin n} (hij : (j : ℕ) = i + 1) (m : ℕ) :
    e (i, j) * e (j, i) ^ (m + 1) =
      e (j, i) ^ (m + 1) * e (i, j) + ((m : ℂ) + 1) • (e (j, i) ^ m * (e (i, i) - e (j, j))) -
        (((m : ℂ) + 1) * m) • e (j, i) ^ m := by
  have hne : i ≠ j := fun h => by rw [h] at hij; omega
  have hxy : e (i, j) * e (j, i) = e (j, i) * e (i, j) + (e (i, i) - e (j, j)) := by
    have := e_mul_sub_mul (i, j) (j, i)
    simp only [if_true] at this
    rw [← this]; abel
  have hh : ∀ p : ℕ, (e (i, i) - e (j, j)) * e (j, i) ^ p =
      e (j, i) ^ p * (e (i, i) - e (j, j)) - (2 * (p : ℂ)) • e (j, i) ^ p := by
    intro p
    rw [sub_mul, e_diag_mul_e_pow, e_diag_mul_e_pow, rootAt_lower_self hne, rootAt_lower_other hne,
      mul_sub]
    module
  induction m with
  | zero =>
    simp only [pow_zero, pow_one, one_mul, Nat.cast_zero, zero_add, one_smul, mul_zero, zero_smul,
      sub_zero]
    exact hxy
  | succ m ih =>
    have e1 : e (i, j) * e (j, i) ^ (m + 1 + 1) =
        e (j, i) * (e (i, j) * e (j, i) ^ (m + 1)) + (e (i, i) - e (j, j)) * e (j, i) ^ (m + 1) := by
      rw [pow_succ' _ (m + 1), ← mul_assoc, hxy, add_mul, mul_assoc]
    rw [e1, hh, ih]
    simp only [mul_sub, mul_add, mul_smul_comm, ← mul_assoc, ← pow_succ']
    push_cast
    module

theorem h_mul_sub_mem_Jp {μ : Fin n → ℤ} {x : U n} (hx : IsAdW μ x) {i j : Fin n}
    (hij : (j : ℕ) = i + 1) :
    (e (i, i) - e (j, j)) * x - ((1 : ℂ) + (μ i : ℂ) - (μ j : ℂ)) • x ∈ Jp n := by
  have hi := hx i
  have hj := hx j
  have hd := rhoVec_sub (n := n) hij
  have key : (e (i, i) - e (j, j)) * x - ((1 : ℂ) + (μ i : ℂ) - (μ j : ℂ)) • x =
      x * (e (i, i) - algebraMap ℂ (U n) (rhoVec n i)) -
        x * (e (j, j) - algebraMap ℂ (U n) (rhoVec n j)) := by
    have h1 : e (i, i) * x = x * e (i, i) + (μ i : ℂ) • x := by rw [← hi]; abel
    have h2 : e (j, j) * x = x * e (j, j) + (μ j : ℂ) • x := by rw [← hj]; abel
    have h3 : rhoVec n i = rhoVec n j + 1 := by rw [← hd]; ring
    rw [sub_mul, h1, h2]
    simp only [mul_sub, ← Algebra.commutes, ← Algebra.smul_def, h3]
    module
  rw [key]
  exact vermaIdeal_le_Jp (Submodule.sub_mem _ (mul_e_sub_mem_vermaIdeal _ _ i)
    (mul_e_sub_mem_vermaIdeal _ _ j))

theorem natural_of_primitive {n : ℕ} (μ : Fin n → ℤ) (x : U n) (i j : Fin n) (hx : IsAdW μ x)
    (hup : ∀ a : Fin n × Fin n, IsUpper a → e a * x ∈ Jp n) (hxJ : x ∉ Jp n)
    (hij : (j : ℕ) = i + 1) (hN : ∃ N : ℕ, e (j, i) ^ N * x ∈ Jp n) :
    ∃ p : ℕ, 1 + μ i - μ j = (p : ℤ) := by
  classical
  have hp := Nat.find_spec hN
  have hmin := fun m => Nat.find_min hN (m := m)
  obtain ⟨q, hq⟩ : ∃ q, Nat.find hN = q + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun h0 => hxJ ?_
    rw [h0] at hp
    simpa using hp
  rw [hq] at hp
  have hqn : e (j, i) ^ q * x ∉ Jp n := hmin q (by omega)
  have hEx : e (i, j) * x ∈ Jp n := hup (i, j) (by
    simp only [IsUpper]; rw [Fin.lt_def, hij]; omega)
  set c : ℂ := (1 : ℂ) + (μ i : ℂ) - (μ j : ℂ) with hc
  have h1 := mul_mem_Jp (e (i, j)) hp
  have h2 := mul_mem_Jp (e (j, i) ^ (q + 1)) hEx
  have h3 := mul_mem_Jp (e (j, i) ^ q) (h_mul_sub_mem_Jp hx hij)
  have key : (((q : ℂ) + 1) * (c - q)) • (e (j, i) ^ q * x) =
      e (i, j) * (e (j, i) ^ (q + 1) * x) - e (j, i) ^ (q + 1) * (e (i, j) * x) -
        ((q : ℂ) + 1) • (e (j, i) ^ q * ((e (i, i) - e (j, j)) * x - c • x)) := by
    rw [← mul_assoc (e (i, j)), e_upper_mul_pow_succ_eq hij q]
    simp only [mul_sub, sub_mul, add_mul, smul_mul_assoc, mul_smul_comm, mul_assoc]
    module
  have hmem : (((q : ℂ) + 1) * (c - q)) • (e (j, i) ^ q * x) ∈ Jp n := by
    rw [key]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ h1 h2) (Submodule.smul_mem _ _ h3)
  have hzero : ((q : ℂ) + 1) * (c - q) = 0 := by
    by_contra hne
    exact hqn ((Submodule.smul_mem_iff _ hne).1 hmem)
  have hq1 : (q : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero q
  have hcq : c = q := sub_eq_zero.1 ((mul_eq_zero.1 hzero).resolve_left hq1)
  refine ⟨q, ?_⟩
  have : ((1 + μ i - μ j : ℤ) : ℂ) = ((q : ℤ) : ℂ) := by
    push_cast
    exact hcq
  exact_mod_cast this

end GlobalTheory.CompanionTheory.PresRho
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NatOfSimpleLoweringNilpotentStatement
open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nat_of_simple_lowering_nilpotent : ∀ {n : ℕ} (μ : Fin n → ℤ) (x : U n) (i j : Fin n), IsAdW μ x → (∀ a : Fin n × Fin n, IsUpper a → e a * x ∈ Jp n) → x ∉ Jp n → (j : ℕ) = i + 1 → (∃ N : ℕ, e (j, i) ^ N * x ∈ Jp n) → ∃ p : ℕ, 1 + μ i - μ j = (p : ℤ) := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.natural_of_primitive | exact GlobalTheory.CompanionTheory.PresRho.natural_of_primitive | (intros; apply GlobalTheory.CompanionTheory.PresRho.natural_of_primitive <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfLowExponentCasimir
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfLowExponentCasimir
open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho

namespace GlobalTheory.CompanionTheory.PresRho.NormIneq

variable {n : ℕ}

theorem casC_eq_sum (σ : Fin n → ℂ) :
    casC σ = ∑ a, σ a ^ 2 + ∑ a, σ a * ((n : ℂ) - 1 - 2 * ((a : ℕ) : ℂ)) :=
  _root_.UpperTheory.Reformulated.B.CasimirElement.main σ

theorem sum_wt_mul (m : Fin n × Fin n →₀ ℕ) (f : Fin n → ℤ) :
    ∑ k, wt m k * f k = m.sum fun a c => (c : ℤ) * (f a.1 - f a.2) := by
  simp only [wt, Finsupp.sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [rootAt, mul_sub, sub_mul, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem lt_of_step {f : Fin n → ℤ} (h : ∀ i j : Fin n, (j : ℕ) = i + 1 → f j < f i) :
    ∀ (d : ℕ) (i j : Fin n), (j : ℕ) = i + d + 1 → f j < f i := by
  intro d
  induction d with
  | zero => intro i j hij; exact h i j (by simpa using hij)
  | succ d ih =>
    intro i j hij
    have hk : (i : ℕ) + d + 1 < n := by have := j.2; omega
    have h1 := ih i ⟨(i : ℕ) + d + 1, hk⟩ rfl
    have h2 := h ⟨(i : ℕ) + d + 1, hk⟩ j (by simp only; omega)
    exact h2.trans h1

theorem eq_zero_of_casC_eq {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (hm : LowExp m)
    (hp : ∀ i j : Fin n, (j : ℕ) = i + 1 → ∃ p : ℕ, 1 + wt m i - wt m j = (p : ℤ))
    (hc : casC (fun k => rhoVec n k + (wt m k : ℂ)) = casC (rhoVec n)) : m = 0 := by
  by_contra hne
  obtain ⟨f, hf⟩ : ∃ f : Fin n → ℤ, ∀ k, f k = 2 * ((n : ℤ) - 1 - 2 * ((k : ℕ) : ℤ)) + wt m k :=
    ⟨_, fun _ => rfl⟩
  have hstep : ∀ i j : Fin n, (j : ℕ) = i + 1 → f j < f i := by
    intro i j hij
    obtain ⟨p, hp⟩ := hp i j hij
    have hp0 : (0 : ℤ) ≤ (p : ℤ) := by positivity
    have hij' : ((j : ℕ) : ℤ) = ((i : ℕ) : ℤ) + 1 := by exact_mod_cast hij
    rw [hf, hf, hij']
    linarith
  have hneg : ∑ k, wt m k * f k < 0 := by
    rw [sum_wt_mul]
    refine Finset.sum_neg (fun a ha => ?_) (Finsupp.support_nonempty_iff.2 hne)
    have hlow : (a.2 : ℕ) < a.1 := hm a ha
    obtain ⟨d, hd⟩ : ∃ d : ℕ, (a.1 : ℕ) = a.2 + d + 1 := ⟨(a.1 : ℕ) - a.2 - 1, by omega⟩
    have hlt := lt_of_step hstep d a.2 a.1 hd
    have hpos : (0 : ℤ) < (m a : ℤ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 ha)
    exact mul_neg_of_pos_of_neg hpos (by linarith)
  have key : ((∑ k, wt m k * f k : ℤ) : ℂ) =
      casC (fun k => rhoVec n k + (wt m k : ℂ)) - casC (rhoVec n) := by
    rw [casC_eq_sum, casC_eq_sum, add_sub_add_comm, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hf]
    push_cast
    simp only [rhoVec]
    ring
  rw [hc, sub_self] at key
  have : ∑ k, wt m k * f k = 0 := by exact_mod_cast key
  omega

end GlobalTheory.CompanionTheory.PresRho.NormIneq
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfLowExponentCasimirStatement
open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_low_exponent_casimir : ∀ {n : ℕ} (m : Fin n × Fin n →₀ ℕ), LowExp m → (∀ i j : Fin n, (j : ℕ) = i + 1 → ∃ p : ℕ, 1 + wt m i - wt m j = (p : ℤ)) → casC (fun k => rhoVec n k + (wt m k : ℂ)) = casC (rhoVec n) → m = 0 := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.NormIneq.eq_zero_of_casC_eq | exact GlobalTheory.CompanionTheory.PresRho.NormIneq.eq_zero_of_casC_eq | (intros; apply GlobalTheory.CompanionTheory.PresRho.NormIneq.eq_zero_of_casC_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LoweringWordsSpan
set_option maxSynthPendingDepth 1

noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount
open GroundTheory.Automorphic.HarishChandra

namespace GlobalTheory.CompanionTheory.PresRho

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

theorem exists_exp {μ : Fin n → ℤ} {x : U n} (h : x ∈ lowSpanW μ ⊔ vermaIdeal (rhoVec n))
    (hx : x ∉ vermaIdeal (rhoVec n)) : ∃ m : Fin n × Fin n →₀ ℕ, LowExp m ∧ wt m = μ := by
  by_contra hne
  have hbot : lowSpanW μ = ⊥ := by
    refine Submodule.span_eq_bot.2 ?_
    rintro _ ⟨m, hm, hw, rfl⟩
    exact absurd ⟨m, hm, hw⟩ hne
  rw [hbot, bot_sup_eq] at h
  exact hx h

theorem lowExp_wt_zero {m : Fin n × Fin n →₀ ℕ} (hm : LowExp m) (h : wt m = 0) : m = 0 := by
  refine GlobalTheory.T.eq_zero_of_low_exponent_casimir m hm (fun i j hij => ⟨1, by simp [h]⟩) ?_
  simp [h]

theorem mem_of_adW_zero {x : U n} (h : x ∈ lowSpanW (0 : Fin n → ℤ) ⊔ vermaIdeal (rhoVec n)) :
    ∃ c : ℂ, x - c • 1 ∈ vermaIdeal (rhoVec n) := by
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 h
  clear h
  have : ∃ c : ℂ, y = c • 1 := by
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, hm, hw0, rfl⟩ := hx
      exact ⟨1, by rw [lowExp_wt_zero hm hw0]; simp⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨d, rfl⟩ := hy
      exact ⟨c + d, by rw [add_smul]⟩
    | smul r x _ hx =>
      obtain ⟨c, rfl⟩ := hx
      exact ⟨r * c, by rw [mul_smul]⟩
  obtain ⟨c, rfl⟩ := this
  exact ⟨c, by simpa using hw⟩

theorem mem_Jp_of_adW {A : Type} [AddCommGroup A] [Module ℂ A]
    (φ : U n →ₐ[ℂ] Module.End ℂ A) (t : A) (ht0 : t ≠ 0)
    (hd : ∀ k, φ (e (k, k)) t = rhoVec n k • t)
    (hu : ∀ a : Fin n × Fin n, IsUpper a → φ (e a) t = 0) :
    ∀ (N : ℕ) (μ : Fin n → ℤ) (x : U n), -ht μ < N → IsAdW μ x → φ x t = 0 → x ∈ Jp n := by
  intro N
  induction N with
  | zero =>
    intro μ x hN hx h0
    by_contra hJ
    obtain ⟨m, hm, rfl⟩ := exists_exp (GlobalTheory.T.weight_vector_mem_low_span_sup_verma μ x hx) fun h => hJ (vermaIdeal_le_Jp h)
    have := ht_wt_nonpos hm
    push_cast at hN
    omega
  | succ N ih =>
    intro μ x hN hx h0
    by_contra hJ
    obtain ⟨m, hm, rfl⟩ := exists_exp (GlobalTheory.T.weight_vector_mem_low_span_sup_verma μ x hx) fun h => hJ (vermaIdeal_le_Jp h)
    have hup : ∀ a : Fin n × Fin n, IsUpper a → e a * x ∈ Jp n := by
      intro a ha
      refine ih _ _ ?_ (hx.e_mul a) (by simp [h0])
      rw [ht_add_rootAt, ht_rootAt]
      have h1 : (a.1 : ℕ) < a.2 := ha
      push_cast at hN
      omega
    have hm0 : m = 0 := GlobalTheory.T.eq_zero_of_low_exponent_casimir m hm
      (fun i j hij => GlobalTheory.T.nat_of_simple_lowering_nilpotent (wt m) x i j hx hup hJ hij (GlobalTheory.T.simple_lowering_pow_mem_ideal i j x hij))
      (GlobalTheory.T.casimir_eq_of_singular_weight_vector (wt m) x hx hup hJ)
    subst hm0
    have hw0 : wt (0 : Fin n × Fin n →₀ ℕ) = 0 := by ext k; simp [wt]
    rw [hw0] at hx
    obtain ⟨c, hc⟩ := mem_of_adW_zero (GlobalTheory.T.weight_vector_mem_low_span_sup_verma 0 x hx)
    have h1 := act_eq_zero_of_mem φ t hd hu hc
    rw [map_sub, LinearMap.sub_apply, h0, zero_sub, map_smul, map_one] at h1
    have hc0 : c = 0 := by
      by_contra hne
      simp [hne, ht0] at h1
    rw [hc0, zero_smul, sub_zero] at hc
    exact hJ (vermaIdeal_le_Jp hc)

theorem word_mem_lowSpan {l : List (Fin n × Fin n)} (hl : ∀ p ∈ l, p.2 < p.1) :
    word l ∈ lowSpan n := by
  refine (Submodule.span_le.2 ?_) (word_mem_canonSpan closed_lower l hl)
  rintro _ ⟨m, hm, -, -, rfl⟩
  exact Submodule.subset_span ⟨m, hm, rfl⟩

theorem rho_cast (a : Fin n) : ((rhoV n a : ℝ) : ℂ) = rhoVec n a := by
  simp [rhoV, rhoVec]

theorem act_eq_zero_of_sqSpan {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    {F : Fin n → Fin n → Module.End ℂ Z} (φ : U n →ₐ[ℂ] Module.End ℂ Z)
    (hφ : ∀ i j, φ (e (i, j)) = F i j) (z : Z)
    (hz : ∀ i j : Fin n, (j : ℕ) = i + 1 → ((F j i) ^ 2) z = 0) {x : U n}
    (hx : x ∈ sqSpan n) : φ x z = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, i, j, hij, rfl⟩ := hx
    simp only [map_mul, map_pow, hφ, Module.End.mul_apply]
    rw [hz i j hij, map_zero]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul r x _ hx => simp [hx]

theorem pres_rho : ∀ {n : ℕ} {A Z : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup Z] [Module ℂ Z]
    (G : Fin n → Fin n → Module.End ℂ A) (F : Fin n → Fin n → Module.End ℂ Z),
    Formalism.REAL.GlRel G → Formalism.REAL.GlRel F → ∀ t : A, t ≠ 0 →
    (∀ a, G a a t = ((rhoV n a : ℝ) : ℂ) • t) → (∀ a b, a < b → G a b t = 0) →
    ∀ z : Z, (∀ i j : Fin n, (j : ℕ) = i + 1 → ((F j i) ^ 2) z = 0) →
    ∀ (s : Finset (List (Fin n × Fin n))) (coef : List (Fin n × Fin n) → ℂ), (∀ l ∈ s, ∀ p ∈ l, p.2 < p.1) →
    ∑ l ∈ s, coef l • (l.map fun p => G p.1 p.2).prod t = 0 →
    ∑ l ∈ s, coef l • (l.map fun p => F p.1 p.2).prod z = 0 := by
  intro n A Z _ _ _ _ G F hG hF t ht0 hd hu z hz s coef hs hsum
  obtain ⟨φ, hφ⟩ := exists_act G hG
  obtain ⟨ψ, hψ⟩ := exists_act F hF
  have hd' : ∀ k, φ (e (k, k)) t = rhoVec n k • t := fun k => by
    rw [hφ, hd, rho_cast]
  have hu' : ∀ a : Fin n × Fin n, IsUpper a → φ (e a) t = 0 := fun a ha => by
    rw [show e a = e (a.1, a.2) from rfl, hφ]; exact hu _ _ ha
  set Y : U n := ∑ l ∈ s, coef l • word l with hY
  have hYlow : Y ∈ lowSpan n :=
    Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ (word_mem_lowSpan (hs l hl))
  have hYt : φ Y t = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hY, map_sum, LinearMap.sum_apply, ← hsum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, LinearMap.smul_apply, act_word φ hφ]
  have hYJ : Y ∈ Jp n := by
    refine (Submodule.span_le.2 ?_) (GlobalTheory.T.annihilator_spanned_by_weight_vectors φ t hd' Y hYt)
    rintro y ⟨μ, hy, h0⟩
    exact mem_Jp_of_adW φ t ht0 hd' hu' (-ht μ + 1).toNat μ y (by omega) hy h0
  have hYs := GlobalTheory.T.low_span_inf_ideal_le_square_span Y hYlow hYJ
  have h := act_eq_zero_of_sqSpan ψ hψ z hz hYs
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hY, map_sum, LinearMap.sum_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, LinearMap.smul_apply, act_word ψ hψ]

end GlobalTheory.CompanionTheory.PresRho
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LoweringWordsSpanStatement
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowering_words_span : ∀ {n : ℕ} {A Z : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup Z] [Module ℂ Z]
    (G : Fin n → Fin n → Module.End ℂ A) (F : Fin n → Fin n → Module.End ℂ Z),
    Formalism.REAL.GlRel G → Formalism.REAL.GlRel F → ∀ t : A, t ≠ 0 →
    (∀ a, G a a t = ((rhoV n a : ℝ) : ℂ) • t) → (∀ a b, a < b → G a b t = 0) →
    ∀ z : Z, (∀ i j : Fin n, (j : ℕ) = i + 1 → ((F j i) ^ 2) z = 0) →
    ∀ (s : Finset (List (Fin n × Fin n))) (coef : List (Fin n × Fin n) → ℂ), (∀ l ∈ s, ∀ p ∈ l, p.2 < p.1) →
    ∑ l ∈ s, coef l • (l.map fun p => G p.1 p.2).prod t = 0 →
    ∑ l ∈ s, coef l • (l.map fun p => F p.1 p.2).prod z = 0 := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.pres_rho | exact GlobalTheory.CompanionTheory.PresRho.pres_rho | (intros; apply GlobalTheory.CompanionTheory.PresRho.pres_rho <;> assumption)
end
