module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDifferenceSummable
set_option autoImplicit false

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem summable_fd {r : ℕ} (i : Fin r) (g : (Fin r → ℕ) → ℂ) (hg : Summable g) :
    Summable (fd i g) := by
  have hinj : Function.Injective (fun m : Fin r → ℕ => m + Pi.single i 1) :=
    fun a b h => add_right_cancel h
  exact (hg.comp_injective hinj).sub hg

theorem summable_DL : ∀ (r : ℕ) (cs : List (Fin r)) (g : (Fin r → ℕ) → ℂ), Summable g →
    Summable (DL cs g) := by
  intro r cs g hg
  induction cs with
  | nil => simpa [DL] using hg
  | cons c cs ih =>
    have : DL (c :: cs) g = fd c (DL cs g) := rfl
    rw [this]
    exact summable_fd c _ ih

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.PeriodicWeightBounded
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.PeriodicWeightBounded
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd

theorem periodic_mul {r l : ℕ} {v : (Fin r → ℕ) → ℚ}
    (hv : ∀ i, ∀ m, v (m + (Pi.single i l : Fin r → ℕ)) = v m) (i : Fin r) (k : ℕ)
    (m : Fin r → ℕ) : v (m + (Pi.single i (k * l) : Fin r → ℕ)) = v m := by
  induction k with
  | zero => simp
  | succ k ih => rw [add_mul, one_mul, Pi.single_add, ← add_assoc, hv, ih]

theorem reduce_on {r l : ℕ} {v : (Fin r → ℕ) → ℚ}
    (hv : ∀ i, ∀ m, v (m + (Pi.single i l : Fin r → ℕ)) = v m) (s : Finset (Fin r))
    (m : Fin r → ℕ) : v m = v (fun i => if i ∈ s then m i % l else m i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [ih]
    have hfun : (fun i => if i ∈ s then m i % l else m i) =
        (fun i => if i ∈ insert a s then m i % l else m i) +
          (Pi.single a (m a / l * l) : Fin r → ℕ) := by
      funext j
      by_cases hj : j = a
      · subst hj
        simp [ha, Nat.mod_add_div']
      · simp [hj, Pi.single_eq_of_ne hj]
    rw [hfun, GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd.periodic_mul hv]

theorem bddW_of_periodic : ∀ (r l : ℕ) (v : (Fin r → ℕ) → ℚ), 0 < l →
    (∀ i, ∀ m, v (m + (Pi.single i l : Fin r → ℕ)) = v m) → BddW v := by
  intro r l v hl hv
  refine ⟨∑ f : Fin r → Fin l, |((v fun i => (f i : ℕ) : ℚ) : ℝ)|, fun m => ?_⟩
  have hm : v m = v fun i => ((⟨m i % l, Nat.mod_lt _ hl⟩ : Fin l) : ℕ) := by
    simpa using GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd.reduce_on hv Finset.univ m
  rw [hm]
  exact Finset.single_le_sum (f := fun f : Fin r → Fin l => |((v fun i => (f i : ℕ) : ℚ) : ℝ)|)
    (fun f _ => abs_nonneg _) (Finset.mem_univ fun i => (⟨m i % l, Nat.mod_lt _ hl⟩ : Fin l))

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.PeriodicWeightBoundedStatement
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodic_weight_bounded : ∀ (r l : ℕ) (v : (Fin r → ℕ) → ℚ), 0 < l → (∀ i, ∀ m, v (m + (Pi.single i l : Fin r → ℕ)) = v m) → BddW v := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd.bddW_of_periodic | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd.bddW_of_periodic | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd.bddW_of_periodic <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConeSeriesSummableRightHalfPlane
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConeSeriesSummableRightHalfPlane
set_option autoImplicit false

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem summable_prod_fin {f : ℕ → ℝ} (hf : Summable f) (h0 : ∀ n, 0 ≤ f n) (r : ℕ) :
    Summable (fun m : Fin r → ℕ => ∏ i, f (m i)) := by
  induction r with
  | zero => exact Summable.of_finite
  | succ r ih =>
    have h2 := Summable.mul_of_nonneg hf ih (fun n => h0 n)
      (fun m => Finset.prod_nonneg fun i _ => h0 (m i))
    rw [← (Fin.consEquiv (fun _ : Fin (r + 1) => ℕ)).summable_iff]
    convert h2 using 1
    funext x
    simp [Fin.consEquiv, Fin.prod_univ_succ]

private theorem exists_pos_lower_bound_of_forall_pos {ι : Type} [Fintype ι] {r : ℕ} (a : ι → Fin r → ℝ) (b : ι → ℝ)
    (ha : ∀ j i, 0 < a j i) (hb : ∀ j, 0 < b j) :
    ∃ c : ℝ, 0 < c ∧ (∀ j, c ≤ b j) ∧ ∀ j i, c ≤ a j i := by
  classical
  let T : Finset ℝ := Finset.univ.image b ∪ Finset.univ.image (fun p : ι × Fin r => a p.1 p.2)
  by_cases hT : T.Nonempty
  · refine ⟨T.min' hT, ?_, fun j => T.min'_le _ ?_, fun j i => T.min'_le _ ?_⟩
    · have h := T.min'_mem hT
      simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at h
      rcases h with ⟨j, hj⟩ | ⟨⟨j, i⟩, hj⟩
      · rw [← hj]; exact hb j
      · rw [← hj]; exact ha j i
    · simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      exact Or.inl ⟨j, rfl⟩
    · simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      exact Or.inr ⟨(j, i), rfl⟩
  · refine ⟨1, one_pos, fun j => ?_, fun j i => ?_⟩
    · exact absurd ⟨b j, by simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]; exact Or.inl ⟨j, rfl⟩⟩ hT
    · exact absurd ⟨b j, by simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]; exact Or.inl ⟨j, rfl⟩⟩ hT

theorem coneTerm_summable : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ),
    r ≤ Fintype.card ι → (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ s : ℂ, 1 < s.re →
    Summable (coneTerm a b s) := by
  intro ι _ r a b hr ha hb s hs
  obtain ⟨c, hc0, hcb, hca⟩ := exists_pos_lower_bound_of_forall_pos a b ha hb
  have hσ0 : 0 < s.re := by linarith
  have hf : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ (-s.re)) := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith : -s.re < -1))
    simpa [Nat.cast_add, Nat.cast_one] using h
  have hC : 0 ≤ (c ^ (-s.re)) ^ Fintype.card ι := pow_nonneg (Real.rpow_nonneg hc0.le _) _
  have hg := (summable_prod_fin hf (fun k => Real.rpow_nonneg (by positivity) _) r).mul_left
    ((c ^ (-s.re)) ^ Fintype.card ι)
  have key : ∀ {x y : ℝ}, 0 < x → x ≤ y → y ^ (-s.re) ≤ x ^ (-s.re) := fun hx hxy => by
    rw [Real.rpow_neg hx.le, Real.rpow_neg (hx.le.trans hxy)]
    exact inv_anti₀ (Real.rpow_pos_of_pos hx _) (Real.rpow_le_rpow hx.le hxy hσ0.le)
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hg)
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = 1 + ∑ i, (m i : ℝ) := ⟨_, rfl⟩
  have hsum0 : 0 ≤ ∑ i, (m i : ℝ) := Finset.sum_nonneg (fun i _ => Nat.cast_nonneg (m i))
  have hS1 : 1 ≤ S := by rw [hSdef]; linarith
  have hS0 : 0 < S := by linarith
  have hL : ∀ j, c * S ≤ b j + ∑ i, a j i * (m i : ℝ) := by
    intro j
    rw [hSdef, mul_add, mul_one, Finset.mul_sum]
    apply add_le_add (hcb j)
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (hca j i) (Nat.cast_nonneg _)
  have hLpos : ∀ j, 0 < b j + ∑ i, a j i * (m i : ℝ) := fun j => lt_of_lt_of_le (mul_pos hc0 hS0) (hL j)
  have hv1 : S ^ (-s.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hS1 (by linarith)
  have hv0 : 0 ≤ S ^ (-s.re) := Real.rpow_nonneg hS0.le _
  calc ‖coneTerm a b s m‖ = ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ (-s.re) := by
        rw [coneTerm, norm_prod]
        refine Finset.prod_congr rfl (fun j _ => ?_)
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (hLpos j), Complex.neg_re]
    _ ≤ ∏ _j : ι, (c * S) ^ (-s.re) :=
        Finset.prod_le_prod₀ (fun j _ => Real.rpow_nonneg (hLpos j).le _)
          (fun j _ => key (mul_pos hc0 hS0) (hL j))
    _ = (c ^ (-s.re)) ^ Fintype.card ι * (S ^ (-s.re)) ^ Fintype.card ι := by
        rw [Finset.prod_const, Finset.card_univ, Real.mul_rpow hc0.le hS0.le, mul_pow]
    _ ≤ (c ^ (-s.re)) ^ Fintype.card ι * (S ^ (-s.re)) ^ r :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hv0 hv1 hr) hC
    _ = (c ^ (-s.re)) ^ Fintype.card ι * ∏ _i : Fin r, S ^ (-s.re) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ (c ^ (-s.re)) ^ Fintype.card ι * ∏ i, ((m i : ℝ) + 1) ^ (-s.re) := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply Finset.prod_le_prod₀ (fun i _ => hv0)
        intro i _
        apply key (by positivity)
        have hi : (m i : ℝ) ≤ ∑ k, (m k : ℝ) :=
          Finset.single_le_sum (fun k _ => Nat.cast_nonneg (m k)) (Finset.mem_univ i)
        rw [hSdef]
        linarith

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConeSeriesSummableRightHalfPlaneStatement
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_series_summable_right_half_plane : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ), r ≤ Fintype.card ι → (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ s : ℂ, 1 < s.re → Summable (coneTerm a b s) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.coneTerm_summable | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.coneTerm_summable | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.coneTerm_summable <;> assumption)
end
end
