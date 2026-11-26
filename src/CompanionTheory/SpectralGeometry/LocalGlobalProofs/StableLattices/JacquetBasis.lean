module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.TensDecomp
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HaarExistence

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.JacquetBasis
noncomputable section

open Matrix CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL GlobalTheory.SmGL

namespace GlobalTheory.CompanionTheory.GradEig

variable {n : ℕ}

theorem Jm_mul_self (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem trace_eq_zero {ε : Fin n → Bool} {A : Matrix (Fin n) (Fin n) ℂ} (h : IsGrad ε A) : A.trace = 0 := by
  obtain ⟨hG, hH, -, -⟩ := h
  have hG' : A.conjTranspose * Jm ε + Jm ε * A = 0 := hG
  rw [hH] at hG'
  have h1 : A * Jm ε = -(Jm ε * A) := eq_neg_of_add_eq_zero_left hG'
  have h2 : (A * Jm ε * Jm ε).trace = -(Jm ε * A * Jm ε).trace := by
    rw [h1, Matrix.neg_mul, Matrix.trace_neg]
  rw [Matrix.mul_assoc A, Jm_mul_self, Matrix.mul_one, Matrix.trace_mul_cycle, Jm_mul_self,
    Matrix.one_mul] at h2
  linear_combination h2 / 2

theorem eigenvalue_cases {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (h3 : A * A * A = A) (i : Fin n) :
    hA.eigenvalues i = -1 ∨ hA.eigenvalues i = 0 ∨ hA.eigenvalues i = 1 := by
  have hev := hA.mulVec_eigenvectorBasis i
  obtain ⟨v, hv⟩ : ∃ v, v = (hA.eigenvectorBasis i).ofLp := ⟨_, rfl⟩
  rw [← hv] at hev
  obtain ⟨r, hr⟩ : ∃ r, r = hA.eigenvalues i := ⟨_, rfl⟩
  rw [← hr] at hev ⊢
  have h3v : (A * A * A) *ᵥ v = (r ^ 3) • v := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    simp only [hev, Matrix.mulVec_smul, smul_smul]
    congr 1
    ring
  rw [h3, hev] at h3v
  have hne : v ≠ 0 := by
    intro h0
    have h1 : ‖hA.eigenvectorBasis i‖ = 1 := (hA.eigenvectorBasis).orthonormal.1 i
    have h2 : hA.eigenvectorBasis i = 0 := by
      rw [hv] at h0
      simpa using h0
    rw [h2, norm_zero] at h1
    exact zero_ne_one h1
  have hr3 : r ^ 3 = r := by
    have h4 : (r ^ 3 - r) • v = 0 := by rw [sub_smul, ← h3v, sub_self]
    rcases smul_eq_zero.1 h4 with h5 | h5
    · exact sub_eq_zero.1 h5
    · exact absurd h5 hne
  have hf : r * (r - 1) * (r + 1) = 0 := by linear_combination hr3
  rcases mul_eq_zero.1 hf with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by linarith))
  · exact Or.inl (by linarith)

theorem exists_perm_blocks {c : Fin n → Fin 3} {d : Fin 3 → ℕ} (hd : ∑ i, d i = n)
    (hc : ∀ i, Fintype.card {x // c x = i} = d i) :
    ∃ σ : Fin n ≃ Fin n, ∀ p, c (σ p) = ((stdBlocks d hd).symm p).1 := by
  classical
  let e : ∀ i, {x // c x = i} ≃ Fin (d i) := fun i => Fintype.equivFinOfCardEq (hc i)
  let τ : Fin n ≃ Fin n :=
    ((Equiv.sigmaFiberEquiv c).symm.trans (Equiv.sigmaCongrRight e)).trans (stdBlocks d hd)
  refine ⟨τ.symm, fun p => ?_⟩
  have hτ : τ.symm p = (((e ((stdBlocks d hd).symm p).1).symm ((stdBlocks d hd).symm p).2) : Fin n) := rfl
  rw [hτ]
  exact ((e _).symm _).2

theorem exists_gradBasis {ε : Fin n → Bool} {A : Matrix (Fin n) (Fin n) ℂ} (h : IsGrad ε A) :
    Nonempty (GradBasis A) := by
  classical
  have htr := trace_eq_zero h
  obtain ⟨_, hH, h3, _⟩ := h
  have hA : A.IsHermitian := hH
  have hcase := eigenvalue_cases hA h3
  let c : Fin n → Fin 3 := fun x =>
    if hA.eigenvalues x = -1 then 0 else if hA.eigenvalues x = 0 then 1 else 2
  have hc0 : ∀ x, c x = 0 ↔ hA.eigenvalues x = -1 := by
    intro x; rcases hcase x with hx | hx | hx <;> norm_num [c, hx] <;> decide
  have hc1 : ∀ x, c x = 1 ↔ hA.eigenvalues x = 0 := by
    intro x; rcases hcase x with hx | hx | hx <;> norm_num [c, hx] <;> decide
  have hc2 : ∀ x, c x = 2 ↔ hA.eigenvalues x = 1 := by
    intro x; rcases hcase x with hx | hx | hx <;> norm_num [c, hx] <;> decide
  have hval : ∀ x, (![-1, 0, 1] : Fin 3 → ℂ) (c x) = ((hA.eigenvalues x : ℝ) : ℂ) := by
    intro x; rcases hcase x with hx | hx | hx <;> norm_num [c, hx] <;> rfl
  obtain ⟨j, hj⟩ : ∃ j, (Finset.univ.filter fun x => hA.eigenvalues x = -1).card = j := ⟨_, rfl⟩
  have hsumR : ∑ x, hA.eigenvalues x = 0 := by
    have h1 := hA.trace_eq_sum_eigenvalues
    rw [htr] at h1
    have h2 := congrArg Complex.re h1
    simpa [Complex.re_sum] using h2.symm
  have hk1 : (Finset.univ.filter fun x => hA.eigenvalues x = 1).card = j := by
    have hs : ∑ x, hA.eigenvalues x = ∑ x, ((if hA.eigenvalues x = 1 then (1 : ℝ) else 0) -
        (if hA.eigenvalues x = -1 then (1 : ℝ) else 0)) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rcases hcase x with hx | hx | hx <;> norm_num [hx]
    rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole, hsumR, hj] at hs
    have hs' : ((Finset.univ.filter fun x => hA.eigenvalues x = 1).card : ℝ) = j := by linarith
    exact_mod_cast hs'
  have htot : j + (Finset.univ.filter fun x => hA.eigenvalues x = 0).card + j = n := by
    have hs : ∑ x : Fin n, ((if hA.eigenvalues x = -1 then 1 else 0) +
        (if hA.eigenvalues x = 0 then 1 else 0) + (if hA.eigenvalues x = 1 then 1 else 0) : ℕ) =
        ∑ x : Fin n, 1 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rcases hcase x with hx | hx | hx <;> norm_num [hx]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_boole,
      Finset.sum_boole, hj, hk1] at hs
    simpa using hs
  have hcard : ∀ i, Fintype.card {x // c x = i} = dims n j i := by
    intro i
    fin_cases i
    · show Fintype.card {x // c x = 0} = j
      rw [Fintype.card_subtype, Finset.filter_congr fun x _ => hc0 x, hj]
    · show Fintype.card {x // c x = 1} = n - 2 * j
      rw [Fintype.card_subtype, Finset.filter_congr fun x _ => hc1 x]
      omega
    · show Fintype.card {x // c x = 2} = j
      rw [Fintype.card_subtype, Finset.filter_congr fun x _ => hc2 x, hk1]
  have hd : ∑ i, dims n j i = n := by
    rw [Fin.sum_univ_three]
    show j + (n - 2 * j) + j = n
    omega
  obtain ⟨σ, hσ⟩ := exists_perm_blocks hd hcard
  have hs := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  have hUU : (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.1 hA.eigenvectorUnitary.2
  have hUU' : star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 hA.eigenvectorUnitary.2
  have hdiag : (diagonal fun p => (![-1, 0, 1] : Fin 3 → ℂ) ((stdBlocks (dims n j) hd).symm p).fst) =
      (diagonal (RCLike.ofReal ∘ hA.eigenvalues)).submatrix σ σ := by
    rw [Matrix.submatrix_diagonal_equiv]
    congr 1
    funext p
    rw [← hσ p, hval]
    rfl
  have e1 : (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).submatrix id σ *
      (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)).submatrix σ id = 1 := by
    rw [← Matrix.submatrix_mul _ _ _ _ _ σ.bijective, hUU, Matrix.submatrix_id_id]
  have e2 : (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)).submatrix σ id *
      (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).submatrix id σ = 1 := by
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, hUU', Matrix.submatrix_one_equiv]
  have e3 : A = ((hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).submatrix id σ *
      diagonal fun p => (![-1, 0, 1] : Fin 3 → ℂ) ((stdBlocks (dims n j) hd).symm p).fst) *
      (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)).submatrix σ id := by
    rw [hdiag, ← Matrix.submatrix_mul _ _ _ _ _ σ.bijective,
      ← Matrix.submatrix_mul _ _ _ _ _ σ.bijective, Matrix.submatrix_id_id]
    exact hs
  exact ⟨⟨_, _, e1, e2, j, hd, e3⟩⟩

end GlobalTheory.CompanionTheory.GradEig

theorem GlobalTheory.CompanionTheory.GradEig.basis : CompanionTheory.RgExh.Dec.J.Basis := by
  intro n ε A h
  exact GlobalTheory.CompanionTheory.GradEig.exists_gradBasis h
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionIsGlRepresentation
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionIsGlRepresentation
noncomputable section

namespace GlobalTheory.CompanionTheory.RgCOBlock.LetterGl

open Finset
open Formalism.REAL (GlRel)
open CompanionTheory.D.LK (Pos Cn ann cre lift)
open CompanionTheory.RgExh.U
open GlobalTheory.CompanionTheory.FarReg.BdProd (adL_cre)

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem lift_mul_cre (φ : Module.End ℂ V) (g : Pos n) :
    (lift n φ * cre g : Module.End ℂ (Cn n V)) = cre g * lift n φ :=
  LinearMap.ext fun x => CompanionTheory.D.LK.lift_cre φ g x

theorem lift_mul_ann (φ : Module.End ℂ V) (g : Pos n) :
    (lift n φ * ann g : Module.End ℂ (Cn n V)) = ann g * lift n φ :=
  LinearMap.ext fun x => CompanionTheory.D.LK.lift_ann φ g x

theorem lift_mul_adL (φ : Module.End ℂ V) (p q : Fin n) :
    (lift n φ * adL p q : Module.End ℂ (Cn n V)) = adL p q * lift n φ := by
  simp only [adL, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, lift_mul_cre, mul_assoc, lift_mul_ann, mul_assoc]

theorem term_ann (k i g : Pos n) :
    (ann g * (cre k * ann i) - cre k * ann i * ann g : Module.End ℂ (Cn n V)) = if k = g then ann i else 0 := by
  have h1 := CompanionTheory.D.LK.Car.ann_cre (V := V) g k
  have h2 := CompanionTheory.D.LK.Car.ann_ann (V := V) g i
  rw [← mul_assoc, eq_sub_of_add_eq h1, sub_mul, mul_assoc (cre k) (ann g), eq_neg_of_add_eq_zero_left h2]
  by_cases e : k = g
  · subst e
    simp [mul_assoc]
  · have e' : ¬g = k := fun h => e h.symm
    simp [e, e', mul_assoc]

theorem adL_ann (p q : Fin n) (g : Pos n) :
    (∑ i : Pos n, adC p q i g • ann i : Module.End ℂ (Cn n V)) = ann g * adL p q - adL p q * ann g := by
  have h : (ann g * adL p q - adL p q * ann g : Module.End ℂ (Cn n V)) =
      ∑ i : Pos n, ∑ k : Pos n, adC p q i k • (ann g * (cre k * ann i) - cre k * ann i * ann g) := by
    simp only [adL, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_sub,
      ← Finset.sum_sub_distrib]
  rw [h]
  simp only [term_ann]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single g]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

theorem adL_comm (p q r v : Fin n) :
    (adL p q * adL r v - adL r v * adL p q : Module.End ℂ (Cn n V)) =
      ∑ i : Pos n, ∑ l : Pos n,
        (∑ k : Pos n, (adC r v i k * adC p q k l - adC p q i k * adC r v k l)) • (cre l * ann i) := by
  have gen : ∀ A : Module.End ℂ (Cn n V), A * adL r v - adL r v * A =
      ∑ i : Pos n, ∑ k : Pos n, adC r v i k • (A * (cre k * ann i) - cre k * ann i * A) := by
    intro A
    simp only [adL, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_sub,
      ← Finset.sum_sub_distrib]
  have h1 : ∀ k i : Pos n, (adL p q * (cre k * ann i) - cre k * ann i * adL p q : Module.End ℂ (Cn n V)) =
      (∑ l : Pos n, adC p q k l • cre l) * ann i - cre k * ∑ m : Pos n, adC p q m i • ann m := by
    intro k i
    rw [← adL_cre, adL_ann]
    noncomm_ring
  rw [gen]
  simp only [h1, smul_sub, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, Finset.smul_sum, smul_smul, sub_smul, Finset.sum_smul]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_comm
  · refine (Finset.sum_congr rfl fun k _ => Finset.sum_comm).trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_comm.trans ?_
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]

def dl (a b : Fin n) : ℂ := if a = b then 1 else 0

def cc (p q : Fin n) (s t : Fin n × Fin n) : ℂ :=
  dl q s.1 * dl t.1 p * dl t.2 s.2 - dl s.2 p * dl t.1 s.1 * dl t.2 q

theorem ite3 (A B C : Prop) [Decidable A] [Decidable B] [Decidable C] :
    (if A ∧ B ∧ C then 1 else 0 : ℂ) = (if A then 1 else 0) * (if B then 1 else 0) * (if C then 1 else 0) := by
  by_cases a : A <;> by_cases b : B <;> by_cases c : C <;> simp [a, b, c]

theorem adC_eq (p q : Fin n) (i k : Pos n) : adC p q i k = cc p q i.1 k.1 := by
  have e1 : ∀ a b : Fin n × Fin n, a = b ↔ a.1 = b.1 ∧ a.2 = b.2 := fun a b => Prod.ext_iff
  simp only [adC, cc, dl, e1 k.1, ite3]

theorem ite_dl (a b : Fin n) (x : ℂ) : (if a = b then x else 0) = dl a b * x := by
  by_cases h : a = b <;> simp [dl, h]

theorem sum_at (f : Fin n × Fin n → ℂ) (s : Fin n × Fin n) (hs : (s.1 : ℕ) < s.2) :
    ∑ k : Pos n, (if k.1 = s then f k.1 else 0) = f s := by
  have e : ∀ k : Pos n, k.1 = s ↔ k = ⟨s, hs⟩ := fun k => (Subtype.ext_iff (a1 := k) (a2 := ⟨s, hs⟩)).symm
  simp only [e, Finset.sum_ite_eq', mem_univ, if_true]

theorem sum_adC {lev : Fin n → ℕ} (hm : Monotone lev) {p q : Fin n} (hpq : lev p = lev q) {i : Pos n}
    (hi : inU lev i) (f : Fin n × Fin n → ℂ) :
    ∑ k : Pos n, adC p q i k * f k.1 =
      dl q i.1.1 * f (p, i.1.2) - dl i.1.2 p * f (i.1.1, q) := by
  have a1 : ∑ k : Pos n, (if q = i.1.1 ∧ k.1 = (p, i.1.2) then 1 else 0) * f k.1 = dl q i.1.1 * f (p, i.1.2) := by
    by_cases h : q = i.1.1
    · have hs : (p : ℕ) < i.1.2 := by
        have : lev p < lev i.1.2 := by rw [hpq, h]; exact hi
        exact hm.reflect_lt this
      have := sum_at f (p, i.1.2) hs
      simp only [h, true_and, dl, if_true, one_mul, ite_mul, zero_mul] at this ⊢
      exact this
    · simp [h, dl]
  have a2 : ∑ k : Pos n, (if i.1.2 = p ∧ k.1 = (i.1.1, q) then 1 else 0) * f k.1 = dl i.1.2 p * f (i.1.1, q) := by
    by_cases h : i.1.2 = p
    · have hs : (i.1.1 : ℕ) < q := by
        have : lev i.1.1 < lev q := by rw [← hpq, ← h]; exact hi
        exact hm.reflect_lt this
      have := sum_at f (i.1.1, q) hs
      simp only [h, true_and, dl, if_true, one_mul, ite_mul, zero_mul] at this ⊢
      exact this
    · simp [h, dl]
  simp only [adC, sub_mul, Finset.sum_sub_distrib, a1, a2]

theorem mat_id {lev : Fin n → ℕ} (hm : Monotone lev) {p q r v : Fin n} (hpq : lev p = lev q) (hrv : lev r = lev v)
    {i : Pos n} (hi : inU lev i) (l : Pos n) :
    ∑ k : Pos n, (adC r v i k * adC p q k l - adC p q i k * adC r v k l) =
      (if q = r then adC p v i l else 0) - (if v = p then adC r q i l else 0) := by
  have h1 := sum_adC hm hrv hi (fun s => cc p q s l.1)
  have h2 := sum_adC hm hpq hi (fun s => cc r v s l.1)
  simp only [← adC_eq] at h1 h2
  rw [Finset.sum_sub_distrib, h1, h2, ite_dl, ite_dl]
  simp only [adC_eq, cc]
  ring

theorem ann_eq_zero {lev : Fin n → ℕ} {x : Cn n V} (hx : SuppIn (inU lev) x) {i : Pos n} (hi : ¬inU lev i) :
    ann i x = 0 := by
  funext A
  by_contra h
  exact hi (hx _ (CompanionTheory.D.LK.ann_ne h).2 i (mem_insert_self _ _))

theorem adL_comm_apply {lev : Fin n → ℕ} (hm : Monotone lev) {x : Cn n V} (hx : SuppIn (inU lev) x)
    {p q r v : Fin n} (hpq : lev p = lev q) (hrv : lev r = lev v) :
    adL p q (adL r v x) - adL r v (adL p q x) =
      (if q = r then adL p v x else 0) - (if v = p then adL r q x else 0) := by
  have h := LinearMap.congr_fun (adL_comm (V := V) p q r v) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [h]
  have e : ∀ a b : Fin n, (adL a b x : Cn n V) = ∑ i : Pos n, ∑ l : Pos n, adC a b i l • cre l (ann i x) := by
    intro a b
    simp [adL, LinearMap.sum_apply, Module.End.mul_apply]
  have t : ∀ i l : Pos n,
      (∑ k : Pos n, (adC r v i k * adC p q k l - adC p q i k * adC r v k l)) • cre l (ann i x) =
      ((if q = r then adC p v i l else 0) - (if v = p then adC r q i l else 0)) • cre l (ann i x) := by
    intro i l
    by_cases hi : inU lev i
    · rw [mat_id hm hpq hrv hi]
    · rw [ann_eq_zero hx hi, map_zero, smul_zero, smul_zero]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
  simp only [t]
  simp only [sub_smul, Finset.sum_sub_distrib]
  congr 1
  · split_ifs
    · rw [e]
    · simp
  · split_ifs
    · rw [e]
    · simp

end GlobalTheory.CompanionTheory.RgCOBlock.LetterGl

open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

namespace GlobalTheory.CompanionTheory.RgCOBlock

theorem lF_glRel : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), Monotone lev → GlRel E → ∀ (x : Cn n V), SuppIn (inU lev) x → ∀ p q r v, lev p = lev q → lev r = lev v → lF E p q (lF E r v x) - lF E r v (lF E p q x) = (if q = r then lF E p v x else 0) - (if v = p then lF E r q x else 0) := by
  intro n lev V _ _ E hm hE x hx p q r v hpq hrv
  have hA := LetterGl.adL_comm_apply hm hx hpq hrv
  have h1 : ∀ y : Cn n V, lift n (E p q) (adL r v y) = adL r v (lift n (E p q) y) := fun y =>
    LinearMap.congr_fun (LetterGl.lift_mul_adL (E p q) r v) y
  have h2 : ∀ y : Cn n V, lift n (E r v) (adL p q y) = adL p q (lift n (E r v) y) := fun y =>
    LinearMap.congr_fun (LetterGl.lift_mul_adL (E r v) p q) y
  have hL : lift n (E p q) (lift n (E r v) x) - lift n (E r v) (lift n (E p q) x) =
      (if q = r then lift n (E p v) x else 0) - (if v = p then lift n (E r q) x else 0) := by
    funext A
    have := LinearMap.congr_fun (hE p q r v) (x A)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
    simp only [Pi.sub_apply, CompanionTheory.D.LK.lift_apply]
    rw [this]
    split_ifs <;> simp
  simp only [lF, LinearMap.add_apply, map_add (f := _), h1, h2]
  calc _ = (lift n (E p q) (lift n (E r v) x) - lift n (E r v) (lift n (E p q) x)) +
        (adL p q (adL r v x) - adL r v (adL p q x)) := by abel
    _ = _ := by
      rw [hL, hA]
      split_ifs <;> abel

end GlobalTheory.CompanionTheory.RgCOBlock
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionIsGlRepresentationStatement
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_action_is_gl_representation : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), Monotone lev → GlRel E → ∀ (x : Cn n V), SuppIn (inU lev) x → ∀ p q r v, lev p = lev q → lev r = lev v → lF E p q (lF E r v x) - lF E r v (lF E p q x) = (if q = r then lF E p v x else 0) - (if v = p then lF E r q x else 0) := by
  first | exact @GlobalTheory.CompanionTheory.RgCOBlock.lF_glRel | exact GlobalTheory.CompanionTheory.RgCOBlock.lF_glRel | (intros; apply GlobalTheory.CompanionTheory.RgCOBlock.lF_glRel <;> assumption)
end
end
