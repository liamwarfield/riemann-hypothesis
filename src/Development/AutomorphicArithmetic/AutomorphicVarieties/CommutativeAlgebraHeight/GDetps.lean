module

public import Mathlib

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GHomprime
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GHommem
open IsLocalRing

private theorem UpperTheory.V.CA.exists_part {R σ : Type} [CommRing R] [Finite σ]
    (F : MvPowerSeries σ R) (d : ℕ) :
    ∃ g : MvPolynomial σ R, ∀ m : σ →₀ ℕ,
      g.coeff m = if m.degree ≤ d then MvPowerSeries.coeff m F else 0 := by
  classical
  haveI : Fintype σ := Fintype.ofFinite σ
  set D : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => d) with hD
  refine ⟨∑ m ∈ Finset.Iic D, MvPolynomial.monomial m
    (if m.degree ≤ d then MvPowerSeries.coeff m F else 0), fun m => ?_⟩
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases h : m.degree ≤ d
  · have hm : m ∈ Finset.Iic D := by
      refine Finset.mem_Iic.mpr (Finsupp.le_def.mpr fun i => (Finsupp.le_degree i m).trans (h.trans ?_))
      simp [hD]
    rw [if_pos hm]
  · simp [h]

theorem UpperTheory.V.CA.g_hommem :
    ∀ (R σ : Type) [CommRing R] [IsNoetherianRing R] [Finite σ] (P : Ideal (MvPolynomial σ R)),
      (∀ f ∈ P, ∀ d : ℕ, MvPolynomial.homogeneousComponent d f ∈ P) → ∀ F : MvPowerSeries σ R,
        F ∈ P.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := R)) ↔
          ∀ (d : ℕ) (g : MvPolynomial σ R),
            (∀ m : σ →₀ ℕ, g.coeff m = if m.degree = d then MvPowerSeries.coeff m F else 0) → g ∈ P := by
  intro R σ _ _ _ P hP F
  classical
  have hsumco : ∀ (f : MvPolynomial σ R) (d : ℕ) (m : σ →₀ ℕ),
      AddMonoidAlgebra.coeff (∑ k ∈ Finset.range (d + 1), MvPolynomial.homogeneousComponent k f) m =
        if m.degree ≤ d then AddMonoidAlgebra.coeff f m else 0 := by
    intro f d m
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_homogeneousComponent]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_range, Nat.lt_succ_iff]
  have htr := UpperTheory.V.CA.exists_part (R := R) (σ := σ)
  have hpolyQ : ∀ f ∈ P, ∀ (d : ℕ) (g : MvPolynomial σ R),
      (∀ m : σ →₀ ℕ, g.coeff m = if m.degree ≤ d then AddMonoidAlgebra.coeff f m else 0) → g ∈ P := by
    intro f hf d g hg
    have hgeq : g = ∑ k ∈ Finset.range (d + 1), MvPolynomial.homogeneousComponent k f := by
      ext m
      rw [hg, hsumco]
    rw [hgeq]
    exact Ideal.sum_mem _ fun k _ => hP f hf k
  have hRQ : ∀ G : MvPowerSeries σ R,
      ((∀ (d : ℕ) (g : MvPolynomial σ R),
        (∀ m : σ →₀ ℕ, g.coeff m = if m.degree = d then MvPowerSeries.coeff m G else 0) → g ∈ P) ↔
      (∀ (d : ℕ) (g : MvPolynomial σ R),
        (∀ m : σ →₀ ℕ, g.coeff m = if m.degree ≤ d then MvPowerSeries.coeff m G else 0) → g ∈ P)) := by
    intro G
    constructor
    · intro h d g hg
      have hgeq : g = ∑ k ∈ Finset.range (d + 1), MvPolynomial.homogeneousComponent k g := by
        ext m
        rw [hsumco]
        by_cases hm : m.degree ≤ d
        · rw [if_pos hm]
        · rw [if_neg hm, hg, if_neg hm]
      rw [hgeq]
      refine Ideal.sum_mem _ fun k hk => h k _ fun m => ?_
      have hk' : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [MvPolynomial.coeff_homogeneousComponent, hg]
      split_ifs <;> first | rfl | (exfalso; omega)
    · intro h d g hg
      obtain ⟨T, hT⟩ := htr G d
      have hTP : T ∈ P := h d T hT
      have hgeq : g = MvPolynomial.homogeneousComponent d T := by
        ext m
        rw [hg, MvPolynomial.coeff_homogeneousComponent, hT]
        split_ifs <;> first | rfl | (exfalso; omega)
      rw [hgeq]
      exact hP T hTP d
  refine Iff.trans ?_ (hRQ F).symm
  constructor
  · intro hF
    have hF' : F ∈ Submodule.span (MvPowerSeries σ R)
        (MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := R) '' (P : Set (MvPolynomial σ R))) := hF
    refine Submodule.span_induction (p := fun x _ => ∀ (d : ℕ) (g : MvPolynomial σ R),
        (∀ m : σ →₀ ℕ, g.coeff m = if m.degree ≤ d then MvPowerSeries.coeff m x else 0) → g ∈ P)
      ?_ ?_ ?_ ?_ hF'
    · rintro x ⟨f, hf, rfl⟩ d g hg
      refine hpolyQ f hf d g fun m => ?_
      rw [hg, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coeff_coe]
    · intro d g hg
      have hg0 : g = 0 := by
        ext m
        simp [hg]
      rw [hg0]
      exact P.zero_mem
    · intro x y _ _ hx hy d g hg
      obtain ⟨gx, hgx⟩ := htr x d
      obtain ⟨gy, hgy⟩ := htr y d
      have hgeq : g = gx + gy := by
        ext m
        rw [hg, MvPolynomial.coeff_add, hgx, hgy, map_add (f := _)]
        split_ifs <;> simp
      rw [hgeq]
      exact P.add_mem (hx d gx hgx) (hy d gy hgy)
    · intro a x _ hx d g hg
      obtain ⟨Ta, hTa⟩ := htr a d
      obtain ⟨Tx, hTx⟩ := htr x d
      have hTxP := hx d Tx hTx
      have hgeq : g = ∑ k ∈ Finset.range (d + 1), MvPolynomial.homogeneousComponent k (Ta * Tx) := by
        ext m
        rw [hsumco, hg, smul_eq_mul]
        by_cases hm : m.degree ≤ d
        · rw [if_pos hm, if_pos hm, MvPowerSeries.coeff_mul, MvPolynomial.coeff_mul]
          refine Finset.sum_congr rfl fun p hp => ?_
          have hpm : p.1 + p.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
          have hdeg : p.1.degree + p.2.degree = m.degree := by rw [← map_add (f := _), hpm]
          rw [hTa, hTx, if_pos (by omega), if_pos (by omega)]
        · rw [if_neg hm, if_neg hm]
      rw [hgeq]
      exact Ideal.sum_mem _ fun k _ => hP _ (P.mul_mem_left Ta hTxP) k
  · intro hQ
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian P : P.FG)
    set D := s.sup MvPolynomial.totalDegree with hD
    let h : ↥s × Fin (D + 1) → MvPolynomial σ R := fun i =>
      MvPolynomial.homogeneousComponent i.2.val i.1.val
    have hhP : ∀ i, h i ∈ P := by
      intro i
      have hi : (i.1 : MvPolynomial σ R) ∈ P := by
        rw [← hs]
        exact Submodule.subset_span i.1.2
      exact hP _ hi _
    have hPspan : P ≤ Ideal.span (Set.range h) := by
      rw [← hs, Submodule.span_le]
      intro f hf
      have hf' : f ∈ s := Finset.mem_coe.mp hf
      have hfsum : f = ∑ k ∈ Finset.range (D + 1), MvPolynomial.homogeneousComponent k f := by
        rw [← Finset.sum_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ (Finset.le_sup (f := MvPolynomial.totalDegree) hf'))) ?_,
          MvPolynomial.sum_homogeneousComponent]
        intro k _ hk
        simp only [Finset.mem_range] at hk
        exact MvPolynomial.homogeneousComponent_eq_zero k f (by omega)
      rw [SetLike.mem_coe, hfsum]
      exact Ideal.sum_mem _ fun k hk =>
        Ideal.subset_span ⟨(⟨f, hf'⟩, ⟨k, Finset.mem_range.mp hk⟩), rfl⟩
    have hcomp : ∀ d : ℕ, ∃ c : ↥s × Fin (D + 1) → MvPolynomial σ R,
        ∑ i, c i • h i = MvPolynomial.homogeneousComponent d (Classical.choose (htr F d)) := by
      intro d
      have hmem : MvPolynomial.homogeneousComponent d (Classical.choose (htr F d)) ∈ P :=
        hP _ (hQ d _ (Classical.choose_spec (htr F d))) d
      exact (Submodule.mem_span_range_iff_exists_fun _).mp (hPspan hmem)
    choose c hc using hcomp
    have hcoefF : ∀ m : σ →₀ ℕ,
        AddMonoidAlgebra.coeff (∑ i, c m.degree i • h i) m = MvPowerSeries.coeff m F := by
      intro m
      rw [hc, MvPolynomial.coeff_homogeneousComponent, if_pos rfl,
        Classical.choose_spec (htr F m.degree) m, if_pos le_rfl]
    let C : ↥s × Fin (D + 1) → MvPowerSeries σ R := fun i p =>
      AddMonoidAlgebra.coeff (c (p.degree + i.2.val) i) p
    have hFeq : F = ∑ i, C i * MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := R) (h i) := by
      ext m
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hcoefF m, map_sum, MvPolynomial.coeff_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [MvPowerSeries.coeff_mul, smul_eq_mul, MvPolynomial.coeff_mul]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coeff_coe]
      have hpm : p.1 + p.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      have hdeg : p.1.degree + p.2.degree = m.degree := by rw [← map_add (f := _), hpm]
      show AddMonoidAlgebra.coeff (c m.degree i) p.1 * AddMonoidAlgebra.coeff (h i) p.2 =
        AddMonoidAlgebra.coeff (c (p.1.degree + i.2.val) i) p.1 * AddMonoidAlgebra.coeff (h i) p.2
      by_cases h2 : p.2.degree = i.2.val
      · rw [← h2, hdeg]
      · have h0 : AddMonoidAlgebra.coeff (h i) p.2 = 0 := by
          show AddMonoidAlgebra.coeff (MvPolynomial.homogeneousComponent i.2.val i.1.val) p.2 = 0
          rw [MvPolynomial.coeff_homogeneousComponent, if_neg h2]
        rw [h0, mul_zero, mul_zero]
    rw [hFeq]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hhP i))
end

open IsLocalRing

private theorem UpperTheory.V.CA.homprime_part (R σ : Type) [CommRing R] [Finite σ] :
    ∃ p : MvPowerSeries σ R → ℕ → MvPolynomial σ R, ∀ F d (m : σ →₀ ℕ),
      (p F d).coeff m = if m.degree = d then MvPowerSeries.coeff m F else 0 := by
  classical
  have hfin : ∀ d : ℕ, {m : σ →₀ ℕ | m.degree = d}.Finite := fun d =>
    (Finsupp.finite_of_degree_le (σ := σ) d).subset (fun m hm => le_of_eq hm)
  refine ⟨fun F d => ∑ m ∈ (hfin d).toFinset, MvPolynomial.monomial m (MvPowerSeries.coeff m F), ?_⟩
  intro F d m
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp

private theorem UpperTheory.V.CA.homprime_mul (R σ : Type) [CommRing R]
    (p : MvPowerSeries σ R → ℕ → MvPolynomial σ R) (hp : ∀ F d (m : σ →₀ ℕ),
      (p F d).coeff m = if m.degree = d then MvPowerSeries.coeff m F else 0)
    (F G : MvPowerSeries σ R) (n : ℕ) :
    p (F * G) n = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, p F q.1 * p G q.2 := by
  classical
  ext m
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_mul, hp, MvPowerSeries.coeff_mul]
  rw [Finset.sum_comm]
  split_ifs with h
  · refine Finset.sum_congr rfl ?_
    intro x hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [Finset.sum_eq_single (x.1.degree, x.2.degree)]
    · simp
    · intro q _ hq
      by_cases h1 : x.1.degree = q.1
      · have h2 : x.2.degree ≠ q.2 := by
          intro h2
          exact hq (Prod.ext h1.symm h2.symm)
        simp [h2]
      · simp [h1]
    · intro hq
      exfalso
      apply hq
      rw [Finset.HasAntidiagonal.mem_antidiagonal, ← h, ← hx, map_add (f := _)]
  · symm
    refine Finset.sum_eq_zero ?_
    intro x hx
    refine Finset.sum_eq_zero ?_
    intro q hq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx hq
    by_cases h1 : x.1.degree = q.1
    · by_cases h2 : x.2.degree = q.2
      · exfalso
        apply h
        rw [← hx, map_add (f := _), h1, h2, hq]
      · simp [h2]
    · simp [h1]

theorem UpperTheory.V.CA.g_homprime :
    ∀ (R σ : Type) [CommRing R] [IsNoetherianRing R] [Finite σ] (P : Ideal (MvPolynomial σ R)), P.IsPrime →
      (∀ f ∈ P, ∀ d : ℕ, MvPolynomial.homogeneousComponent d f ∈ P) →
        (P.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := R))).IsPrime ∧
          (P.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := R))).comap
            (MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := R)) = P := by
  intro R σ _ _ _ P hP hhom
  classical
  obtain ⟨p, hp⟩ := UpperTheory.V.CA.homprime_part R σ
  have key : ∀ F : MvPowerSeries σ R,
      F ∈ P.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := R)) ↔ ∀ d, p F d ∈ P := by
    intro F
    rw [UpperTheory.V.CA.g_hommem R σ P hhom F]
    constructor
    · intro h d
      exact h d (p F d) (hp F d)
    · intro h d g hg
      have hg' : g = p F d := by
        ext m
        rw [hg, hp]
      rw [hg']
      exact h d
  have hcomap : (P.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := R))).comap
      (MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := R)) = P := by
    apply le_antisymm
    · intro f hf
      rw [Ideal.mem_comap, key] at hf
      have hd : ∀ d, MvPolynomial.homogeneousComponent d f ∈ P := by
        intro d
        have he : MvPolynomial.homogeneousComponent d f =
            p (MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := R) f) d := by
          ext m
          rw [MvPolynomial.coeff_homogeneousComponent, hp,
            MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coeff_coe]
        rw [he]
        exact hf d
      rw [← MvPolynomial.sum_homogeneousComponent f]
      exact Ideal.sum_mem _ (fun i _ => hd i)
    · exact Ideal.le_comap_map
  refine ⟨⟨?_, ?_⟩, hcomap⟩
  · intro htop
    apply hP.ne_top
    rw [← hcomap, htop, Ideal.comap_top]
  · intro F G hFG
    by_contra hne
    push_neg at hne
    obtain ⟨hF, hG⟩ := hne
    rw [key] at hF hG hFG
    push_neg at hF hG
    have ha : p F (Nat.find hF) ∉ P := Nat.find_spec hF
    have hb : p G (Nat.find hG) ∉ P := Nat.find_spec hG
    have ha' : ∀ i < Nat.find hF, p F i ∈ P := fun i hi => by
      simpa using Nat.find_min hF hi
    have hb' : ∀ i < Nat.find hG, p G i ∈ P := fun i hi => by
      simpa using Nat.find_min hG hi
    have hsum := hFG (Nat.find hF + Nat.find hG)
    rw [UpperTheory.V.CA.homprime_mul R σ p hp] at hsum
    have hmem : (Nat.find hF, Nat.find hG) ∈
        Finset.HasAntidiagonal.antidiagonal (Nat.find hF + Nat.find hG) := by
      rw [Finset.HasAntidiagonal.mem_antidiagonal]
    rw [← Finset.add_sum_erase _ _ hmem] at hsum
    have hrest : ∑ q ∈ (Finset.HasAntidiagonal.antidiagonal (Nat.find hF + Nat.find hG)).erase
        (Nat.find hF, Nat.find hG), p F q.1 * p G q.2 ∈ P := by
      refine Ideal.sum_mem _ (fun q hq => ?_)
      rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hq
      obtain ⟨hq2, hq1⟩ := hq
      rcases lt_or_ge q.1 (Nat.find hF) with h | h
      · exact P.mul_mem_right _ (ha' _ h)
      · have h2 : q.2 < Nat.find hG := by
          rcases eq_or_lt_of_le h with h' | h'
          · exfalso
            apply hq2
            ext
            · exact h'.symm
            · simp only
              omega
          · omega
        exact P.mul_mem_left _ (hb' _ h2)
    have hmain : p F (Nat.find hF) * p G (Nat.find hG) ∈ P := by
      have := P.sub_mem hsum hrest
      simpa using this
    rcases hP.mem_or_mem hmain with h | h
    · exact ha h
    · exact hb h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GDetrad
open IsLocalRing

private theorem exists_col {K : Type} [Field K] {n : ℕ} (a : Fin (n+1) → K) (ha : a ≠ 0) :
    ∃ U : Matrix (Fin (n+1)) (Fin (n+1)) K, U.det ≠ 0 ∧ ∀ i, U i 0 = a i := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  refine ⟨((1 : Matrix (Fin (n+1)) (Fin (n+1)) K).updateCol i a).submatrix id (Equiv.swap 0 i), ?_, ?_⟩
  · rw [Matrix.det_permute', ← Matrix.cramer_apply, Matrix.cramer_one]
    refine mul_ne_zero ?_ (by simpa using hi)
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap (0 : Fin (n+1)) i)) with h | h <;> simp [h]
  · intro j
    simp

private def Emat (K : Type) [CommRing K] (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) K :=
  Matrix.diagonal (fun i => if i = 0 then 0 else 1)

private theorem exists_param {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) K)
    (m : Fin (n+1) → K) (h1 : M.mulVec m = 0) (h2 : M.det = 0) :
    ∃ (N U : Matrix (Fin (n+1)) (Fin (n+1)) K) (t : K),
      N * Emat K n * U.adjugate = M ∧ ∀ i, t * U i 0 = m i := by
  have : ∃ (a : Fin (n+1) → K) (t : K), a ≠ 0 ∧ M.mulVec a = 0 ∧ ∀ i, t * a i = m i := by
    by_cases hm : m = 0
    · obtain ⟨a, ha, hMa⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h2
      exact ⟨a, 0, ha, hMa, by simp [hm]⟩
    · exact ⟨m, 1, hm, h1, by simp⟩
  obtain ⟨a, t, ha, hMa, hta⟩ := this
  obtain ⟨U, hU, hUa⟩ := exists_col a ha
  refine ⟨(U.det)⁻¹ • (M * U), U, t, ?_, fun i => by rw [hUa, hta]⟩
  have hE : M * U * Emat K n = M * U := by
    ext i j
    rw [Emat, Matrix.mul_diagonal]
    by_cases hj : j = 0
    · subst hj
      have := congrFun hMa i
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
      simp [Matrix.mul_apply, hUa, this]
    · simp [hj]
  rw [Matrix.smul_mul, hE, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul,
    Matrix.mul_one, smul_smul, inv_mul_cancel₀ hU, one_smul]

private theorem param_mulVec {B : Type} [CommRing B] {n : ℕ} (N U : Matrix (Fin (n+1)) (Fin (n+1)) B)
    (t : B) (a : Fin (n+1)) :
    ∑ b, (N * Emat B n * U.adjugate) a b * (t * U b 0) = 0 := by
  have h : (N * Emat B n * U.adjugate * U) a 0 = 0 := by
    rw [Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_apply,
      Emat, Matrix.mul_diagonal]
    simp
  rw [Matrix.mul_apply] at h
  calc _ = t * ∑ b, (N * Emat B n * U.adjugate) a b * U b 0 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun b _ => by ring)
    _ = 0 := by rw [h, mul_zero]

private theorem param_det {B : Type} [CommRing B] {n : ℕ} (N U : Matrix (Fin (n+1)) (Fin (n+1)) B) :
    (N * Emat B n * U.adjugate).det = 0 := by
  have : (Emat B n).det = 0 := by
    rw [Emat, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ 0) (by simp)
  simp [Matrix.det_mul, this]

private abbrev Bv (n : ℕ) := Option ((Fin (n+1) × Fin (n+1)) ⊕ (Fin (n+1) × Fin (n+1)))

private noncomputable def phi (R : Type) [CommRing R] (n : ℕ) :
    MvPolynomial ((Fin (n + 1) × Fin (n + 1)) ⊕ Fin (n + 1)) R →ₐ[R] MvPolynomial (Bv n) R :=
  MvPolynomial.aeval (Sum.elim
    (fun p => (((Matrix.of fun a b => (MvPolynomial.X (some (Sum.inl (a, b))) : MvPolynomial (Bv n) R))
      * Emat (MvPolynomial (Bv n) R) n * (Matrix.of fun a b => (MvPolynomial.X (some (Sum.inr (a, b))) : MvPolynomial (Bv n) R)).adjugate : Matrix (Fin (n+1)) (Fin (n+1)) (MvPolynomial (Bv n) R))) p.1 p.2)
    (fun i => MvPolynomial.X none * MvPolynomial.X (some (Sum.inr (i, 0)))))

private theorem factor (R : Type) [CommRing R] (n : ℕ) {K : Type} [Field K] [Algebra R K]
    (ψ : MvPolynomial ((Fin (n + 1) × Fin (n + 1)) ⊕ Fin (n + 1)) R →ₐ[R] K)
    (h1 : ∀ a, ψ (∑ b : Fin (n + 1), MvPolynomial.X (Sum.inl (a, b)) * MvPolynomial.X (Sum.inr b)) = 0)
    (h2 : ψ (Matrix.det (Matrix.of fun a b : Fin (n + 1) => MvPolynomial.X (Sum.inl (a, b)))) = 0)
    (f) (hf : phi R n f = 0) : ψ f = 0 := by
  obtain ⟨N, U, t, hM, hm⟩ := exists_param (Matrix.of fun a b => ψ (MvPolynomial.X (Sum.inl (a, b))))
    (fun b => ψ (MvPolynomial.X (Sum.inr b)))
    (by ext a; simpa [Matrix.mulVec, dotProduct] using h1 a)
    (by rw [AlgHom.map_det] at h2; exact h2)
  let χ : MvPolynomial (Bv n) R →ₐ[R] K := MvPolynomial.aeval
    (fun o => Option.elim o t (Sum.elim (fun p => N p.1 p.2) (fun p => U p.1 p.2)))
  have hc : χ.comp (phi R n) = ψ := by
    apply MvPolynomial.algHom_ext
    rintro (⟨a, b⟩ | i)
    · have e1 : χ.mapMatrix (Matrix.of fun a b => (MvPolynomial.X (some (Sum.inl (a, b))) : MvPolynomial (Bv n) R)) = N := by
        ext a b; simp [χ]
      have e2 : χ.mapMatrix (Matrix.of fun a b => (MvPolynomial.X (some (Sum.inr (a, b))) : MvPolynomial (Bv n) R)) = U := by
        ext a b; simp [χ]
      have e3 : χ.mapMatrix (Emat _ n) = Emat K n := by
        ext a b; simp [Emat, Matrix.diagonal_apply]; split_ifs <;> simp
      have e4 := congrFun (congrFun hM a) b
      rw [← e1, ← e2, ← e3, ← AlgHom.map_adjugate, ← map_mul, ← map_mul] at e4
      simpa [phi] using e4
    · simpa [phi, χ] using hm i
  rw [← hc, AlgHom.comp_apply, hf, map_zero]

private theorem phi_row (R : Type) [CommRing R] (n : ℕ) (a : Fin (n+1)) :
    phi R n (∑ b : Fin (n + 1), MvPolynomial.X (Sum.inl (a, b)) * MvPolynomial.X (Sum.inr b)) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← param_mulVec (Matrix.of fun a b => (MvPolynomial.X (some (Sum.inl (a, b))) : MvPolynomial (Bv n) R)) (Matrix.of fun a b => (MvPolynomial.X (some (Sum.inr (a, b))) : MvPolynomial (Bv n) R)) (MvPolynomial.X none) a]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [map_mul, phi, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  rfl

private theorem phi_det (R : Type) [CommRing R] (n : ℕ) :
    phi R n (Matrix.det (Matrix.of fun a b : Fin (n + 1) => MvPolynomial.X (Sum.inl (a, b)))) = 0 := by
  rw [AlgHom.map_det, ← param_det (Matrix.of fun a b => (MvPolynomial.X (some (Sum.inl (a, b))) : MvPolynomial (Bv n) R)) (Matrix.of fun a b => (MvPolynomial.X (some (Sum.inr (a, b))) : MvPolynomial (Bv n) R))]
  congr 1
  ext1 a b
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, phi, MvPolynomial.aeval_X]
  rfl

theorem UpperTheory.V.CA.g_detrad :
    (∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ),
      let A := MvPolynomial ((Fin (n + 1) × Fin (n + 1)) ⊕ Fin (n + 1)) R
      let I : Ideal A := Ideal.span (Set.range (fun a : Fin (n + 1) => ∑ b : Fin (n + 1), (MvPolynomial.X (Sum.inl (a, b)) * MvPolynomial.X (Sum.inr b) : A)) ∪ {Matrix.det (Matrix.of fun a b : Fin (n + 1) => (MvPolynomial.X (Sum.inl (a, b)) : A))})
      I.radical.IsPrime ∧ (MvPolynomial.X (Sum.inr 0) : A) ∉ I.radical ∧ (∀ r : R, MvPolynomial.C r ∈ I.radical → r = 0) ∧
        ∀ f ∈ I.radical, ∀ d : ℕ, MvPolynomial.homogeneousComponent d f ∈ I.radical) := by
  intro R _ _ n A I
  have hP : (RingHom.ker (phi R n)).IsPrime := RingHom.ker_isPrime _
  have hle : I ≤ RingHom.ker (phi R n) := by
    rw [Ideal.span_le]
    rintro x (⟨a, rfl⟩ | rfl)
    · exact phi_row R n a
    · exact phi_det R n
  have heq : I.radical = RingHom.ker (phi R n) := by
    apply le_antisymm (hP.radical_le_iff.mpr hle)
    rw [Ideal.radical_eq_sInf]
    apply le_sInf
    rintro q ⟨hIq, hq⟩ f hf
    let ψ : A →ₐ[R] FractionRing (A ⧸ q) :=
      (IsScalarTower.toAlgHom R (A ⧸ q) (FractionRing (A ⧸ q))).comp (Ideal.Quotient.mkₐ R q)
    have hψ : ∀ g, ψ g = 0 ↔ g ∈ q := by
      intro g
      simp [ψ, Ideal.Quotient.eq_zero_iff_mem]
    rw [← hψ]
    refine factor R n ψ (fun a => ?_) ?_ f hf
    · rw [hψ]; exact hIq (Ideal.subset_span (Or.inl ⟨a, rfl⟩))
    · rw [hψ]; exact hIq (Ideal.subset_span (Or.inr rfl))
  refine ⟨heq ▸ hP, ?_, ?_, ?_⟩
  · rw [heq, RingHom.mem_ker]
    simp [phi, MvPolynomial.X_ne_zero]
  · intro r hr
    rw [heq, RingHom.mem_ker] at hr
    simpa [phi] using hr
  · letI := MvPolynomial.gradedAlgebra (σ := (Fin (n + 1) × Fin (n + 1)) ⊕ Fin (n + 1)) (R := R)
    have hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ R) := by
      apply Ideal.homogeneous_span
      rintro x (⟨a, rfl⟩ | rfl)
      · refine ⟨1 + 1, ?_⟩
        rw [MvPolynomial.mem_homogeneousSubmodule]
        exact MvPolynomial.IsHomogeneous.sum _ _ _ (fun b _ =>
          (MvPolynomial.isHomogeneous_X _ _).mul (MvPolynomial.isHomogeneous_X _ _))
      · refine ⟨∑ _i : Fin (n+1), 1, ?_⟩
        rw [Matrix.det_apply]
        refine Submodule.sum_mem _ (fun σ _ => ?_)
        rw [Units.smul_def]
        refine zsmul_mem ?_ _
        rw [MvPolynomial.mem_homogeneousSubmodule]
        exact MvPolynomial.IsHomogeneous.prod _ _ (fun _ => 1) (fun b _ => MvPolynomial.isHomogeneous_X _ _)
    intro f hf d
    have := hI.radical d hf
    rw [← MvPolynomial.decomposition.decompose'_apply]
    exact this
end

open IsLocalRing

private theorem UpperTheory.V.CA.detps_height {A : Type} [CommRing A] [IsNoetherianRing A] (n : ℕ)
    (M : Fin (n + 1) → Fin (n + 1) → A) (v : Fin (n + 1) → A) (I : Ideal A)
    (hI : I = Ideal.span (Set.range (fun a => ∑ b, M a b * v b) ∪ {Matrix.det (Matrix.of M)}))
    (hp : I.radical.IsPrime) (hv : v 0 ∉ I.radical) : I.radical.height ≤ (n + 1 : ℕ) := by
  classical
  have hJI : Ideal.span (Set.range (fun a => ∑ b, M a b * v b)) ≤ I := by
    rw [hI]
    exact Ideal.span_mono Set.subset_union_left
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le (hJI.trans I.le_radical)
  have hQprime : Q.IsPrime := hQ.1.1
  have key : Matrix.mulVec (Matrix.adjugate (Matrix.of M)) (Matrix.mulVec (Matrix.of M) v) 0
      = Matrix.det (Matrix.of M) * v 0 := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp
  have hdv : Matrix.det (Matrix.of M) * v 0 ∈ Q := by
    rw [← key]
    apply hQ.1.2
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    refine Ideal.sum_mem _ fun b _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨b, rfl⟩)
  have hdet : Matrix.det (Matrix.of M) ∈ Q := by
    rcases hQprime.mem_or_mem hdv with h | h
    · exact h
    · exact absurd (hQP h) hv
  have hIQ : I ≤ Q := by
    rw [hI, Ideal.span_le]
    rintro x (⟨a, rfl⟩ | hx)
    · exact hQ.1.2 (Ideal.subset_span ⟨a, rfl⟩)
    · rw [Set.mem_singleton_iff.mp hx]
      exact hdet
  have hPQ : I.radical = Q :=
    le_antisymm (by rw [← hQprime.radical]; exact Ideal.radical_mono hIQ) hQP
  rw [hPQ]
  have hQ' : Q ∈ (Ideal.span ((Finset.univ.image fun a => ∑ b, M a b * v b : Finset A) :
      Set A)).minimalPrimes := by
    simpa using hQ
  refine (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hQ').trans ?_
  exact_mod_cast Finset.card_image_le.trans (by simp)

theorem UpperTheory.V.CA.g_detps :
    (∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (n : ℕ),
      let A := MvPowerSeries ((Fin (n + 1) × Fin (n + 1)) ⊕ Fin (n + 1)) R
      let I : Ideal A := Ideal.span (Set.range (fun a : Fin (n + 1) => ∑ b : Fin (n + 1), (MvPowerSeries.X (Sum.inl (a, b)) * MvPowerSeries.X (Sum.inr b) : A)) ∪ {Matrix.det (Matrix.of fun a b : Fin (n + 1) => (MvPowerSeries.X (Sum.inl (a, b)) : A))})
      I.radical.IsPrime ∧ I.radical.height ≤ (n + 1 : ℕ)) := by
  intro R _ _ _ n A I
  classical
  have hd := UpperTheory.V.CA.g_detrad R n
  simp only at hd
  obtain ⟨hP, hX0, -, hhom⟩ := hd
  set Ip : Ideal (MvPolynomial ((Fin (n + 1) × Fin (n + 1)) ⊕ Fin (n + 1)) R) :=
    Ideal.span (Set.range (fun a : Fin (n + 1) => ∑ b : Fin (n + 1),
      MvPolynomial.X (Sum.inl (a, b)) * MvPolynomial.X (Sum.inr b)) ∪
      {Matrix.det (Matrix.of fun a b : Fin (n + 1) => MvPolynomial.X (Sum.inl (a, b)))}) with hIp
  set φ := (MvPolynomial.coeToMvPowerSeries.ringHom :
    MvPolynomial ((Fin (n + 1) × Fin (n + 1)) ⊕ Fin (n + 1)) R →+* A) with hφ
  have hmap : Ideal.map φ Ip = I := by
    rw [hIp, Ideal.map_span, Set.image_union, Set.image_singleton, ← Set.range_comp]
    congr 3
    · funext a
      set_option synthInstance.maxHeartbeats 100000 in
        simp [φ, map_sum]
    · rw [RingHom.map_det]
      congr 1
      ext a b
      simp [φ]
  obtain ⟨hmp, hcomap⟩ := UpperTheory.V.CA.g_homprime R _ Ip.radical hP hhom
  have hrad : I.radical = Ideal.map φ Ip.radical := by
    apply le_antisymm
    · rw [← hmp.radical]
      apply Ideal.radical_mono
      rw [← hmap]
      exact Ideal.map_mono Ip.le_radical
    · rw [← hmap]
      exact Ideal.map_radical_le φ
  have hIprime : I.radical.IsPrime := by
    rw [hrad]
    exact hmp
  refine ⟨hIprime, ?_⟩
  refine UpperTheory.V.CA.detps_height n (fun a b => (MvPowerSeries.X (Sum.inl (a, b)) : A))
    (fun b => (MvPowerSeries.X (Sum.inr b) : A)) I rfl hIprime ?_
  rw [hrad]
  intro h
  apply hX0
  rw [← hcomap, Ideal.mem_comap]
  simpa [φ] using h
