module

public import Formalism.IncomingBounds.WeightIdentities
public import Formalism.GaussJetBounds.GaussJetProofs.CapacityLeReachCapacity
public import Formalism.GaussJetBounds.GaussJetProofs.LemmaRA

@[expose] public section

section -- merged from Formalism.GaussJetBounds.GaussJetProofs.ThmAJet
section -- merged from Formalism.GaussJetBounds.GaussJetProofs.FrameCoeffMulLin
noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

section Rank

end Rank

section Pure

private theorem frame_frob_norm {K : Type*} [NormedField K] [IsUltrametricDist K] {l : ℕ}
    (hl : l.Prime) {ι : Type*} (U : ι → K) (hU : ∀ a, ‖U a‖ ≤ 1) (e : ℕ) (S : Finset ι) :
    ‖(∑ a ∈ S, U a) ^ (l ^ e) - ∑ a ∈ S, U a ^ (l ^ e)‖ ≤ ‖(l : K)‖ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, zero_pow (pow_ne_zero _ hl.ne_zero), sub_zero,
      norm_zero]
    exact norm_nonneg _
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hV : ‖∑ b ∈ S, U b‖ ≤ 1 :=
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun b _ => hU b)
    obtain ⟨R, hReq, hRle⟩ : ∃ R : K, (U a + ∑ b ∈ S, U b) ^ (l ^ e) =
        U a ^ (l ^ e) + (∑ b ∈ S, U b) ^ (l ^ e) + (l : K) * R ∧ ‖R‖ ≤ 1 := by
      refine ⟨_, add_pow_prime_pow_eq' hl (U a) (∑ b ∈ S, U b) e, ?_⟩
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun k _ => ?_)
      rw [norm_mul, norm_mul, norm_pow, norm_pow]
      have h1 : ‖U a‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) (hU a)
      have h2 : ‖∑ b ∈ S, U b‖ ^ (l ^ e - k) ≤ 1 := pow_le_one₀ (norm_nonneg _) hV
      have h3 := IsUltrametricDist.norm_natCast_le_one K ((l ^ e).choose k / l)
      calc ‖U a‖ ^ k * ‖∑ b ∈ S, U b‖ ^ (l ^ e - k) * ‖(((l ^ e).choose k / l : ℕ) : K)‖
          ≤ 1 * 1 * 1 := by gcongr
        _ = 1 := by ring
    have heq : (U a + ∑ b ∈ S, U b) ^ (l ^ e) - (U a ^ (l ^ e) + ∑ b ∈ S, U b ^ (l ^ e)) =
        ((∑ b ∈ S, U b) ^ (l ^ e) - ∑ b ∈ S, U b ^ (l ^ e)) + (l : K) * R := by
      rw [hReq]; ring
    rw [heq]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih ?_)
    rw [norm_mul]
    calc ‖(l : K)‖ * ‖R‖ ≤ ‖(l : K)‖ * 1 := by gcongr
      _ = ‖(l : K)‖ := mul_one _

private theorem frame_coeff_mul_lin {R ι : Type*} [CommSemiring R] [Fintype ι] [DecidableEq ι]
    (Q : MvPolynomial ι R) (c : ι → R) (m : ι →₀ ℕ) :
    AddMonoidAlgebra.coeff (Q * ∑ y, MvPolynomial.C (c y) * MvPolynomial.X y) m =
      ∑ y, c y * (if y ∈ m.support then AddMonoidAlgebra.coeff Q (m - Finsupp.single y 1) else 0) := by
  rw [Finset.mul_sum, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [mul_left_comm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_mul_X']

private theorem frame_coeff_pow_lin {R ι : Type*} [CommSemiring R] [Fintype ι] [DecidableEq ι]
    (c : ι → R) (j : ι) (B : ℕ) :
    AddMonoidAlgebra.coeff ((∑ y, MvPolynomial.C (c y) * MvPolynomial.X y) ^ B)
      (Finsupp.single j B) = c j ^ B := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [pow_succ, frame_coeff_mul_lin, Finset.sum_eq_single j]
    · rw [if_pos (by simp), ← Finsupp.single_tsub, Nat.add_sub_cancel, ih, pow_succ, mul_comm]
    · intro y _ hy
      rw [if_neg (by simp [Ne.symm hy]), mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h

private theorem frame_coeff_two {R ι : Type*} [CommSemiring R] [Fintype ι] [DecidableEq ι]
    (c c' : ι → R) (i j : ι) (hij : i ≠ j) (hc : ∀ y, c y ≠ 0 → y ≠ j) (A B : ℕ) :
    AddMonoidAlgebra.coeff ((∑ y, MvPolynomial.C (c' y) * MvPolynomial.X y) ^ B *
        (∑ y, MvPolynomial.C (c y) * MvPolynomial.X y) ^ A)
      (Finsupp.single i A + Finsupp.single j B) = c i ^ A * c' j ^ B := by
  induction A with
  | zero => simp [frame_coeff_pow_lin]
  | succ A ih =>
    rw [pow_succ, ← mul_assoc, frame_coeff_mul_lin, Finset.sum_eq_single i]
    · have hmem : i ∈ (Finsupp.single i (A + 1) + Finsupp.single j B).support := by
        rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same]; omega
      have hsub : Finsupp.single i (A + 1) + Finsupp.single j B - Finsupp.single i 1 =
          Finsupp.single i A + Finsupp.single j B := by
        ext y
        simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.add_apply, Finsupp.single_apply]
        by_cases h1 : i = y
        · subst h1; simp [Ne.symm hij]
        · simp [h1]
      rw [if_pos hmem, hsub, ih, pow_succ]; ring
    · intro y _ hy
      by_cases hcy : c y = 0
      · rw [hcy, zero_mul]
      · rw [if_neg, mul_zero]
        rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply,
          if_neg (Ne.symm hy), if_neg (Ne.symm (hc y hcy))]
        simp
    · intro h; exact absurd (Finset.mem_univ i) h

private theorem frame_lin_hom {R ι τ : Type*} [CommSemiring R] [Fintype ι] (lt : ι → τ)
    (c : ι → R) (t : τ) (hc : ∀ y, c y ≠ 0 → lt y = t) :
    MvPolynomial.IsWeightedHomogeneous (fun y => Finsupp.single (lt y) 1)
      (∑ y, MvPolynomial.C (c y) * MvPolynomial.X y) (Finsupp.single t 1) := by
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun y _ => ?_
  by_cases hcy : c y = 0
  · rw [hcy, map_zero, zero_mul]; exact MvPolynomial.isWeightedHomogeneous_zero R _ _
  · have h1 := (MvPolynomial.isWeightedHomogeneous_X R
      (fun y => Finsupp.single (lt y) 1) y).C_mul (c y)
    have h2 : Finsupp.single t 1 = (fun y => Finsupp.single (lt y) 1) y := by simp [hc y hcy]
    rw [h2]; exact h1

private theorem frame_prod_hom {R ι τ : Type*} [CommSemiring R] (lt : ι → τ)
    (P : τ → MvPolynomial ι R)
    (hP : ∀ t, MvPolynomial.IsWeightedHomogeneous (fun y => Finsupp.single (lt y) 1) (P t)
      (Finsupp.single t 1)) (e : τ →₀ ℕ) :
    MvPolynomial.IsWeightedHomogeneous (fun y => Finsupp.single (lt y) 1)
      (e.prod fun t k => P t ^ k) e := by
  have h1 := MvPolynomial.IsWeightedHomogeneous.prod e.support (fun t => P t ^ e t)
    (fun t => e t • Finsupp.single t 1) (fun t _ => (hP t).pow (e t))
  have h2 : (∑ t ∈ e.support, e t • Finsupp.single t 1) = e := by
    simp_rw [Finsupp.smul_single_one]
    exact Finsupp.sum_single e
  rw [h2] at h1
  exact h1

private theorem frame_pure_formula {K : Type u} [Field K] {d N0 N1 : ℕ} [NeZero d]
    {ι : Type} [Fintype ι] [DecidableEq ι] (lt : ι → ZMod d) (M : ZV d N0 N1 → ι → K)
    (hM : ∀ x i, M x i ≠ 0 → lt i = x.1) (be : MvPowerSeries (ZMod d) K) (i j : ι) (A B : ℕ)
    (hij : lt i ≠ lt j) :
    MvPowerSeries.coeff (Finsupp.single i A + Finsupp.single j B) (bSum M be) =
      MvPowerSeries.coeff (Finsupp.single (lt i) A + Finsupp.single (lt j) B) be *
        ∑ ab : Fin N0 × Fin N1, M (lt i, ab.1, ab.2) i ^ A * M (lt j, ab.1, ab.2) j ^ B := by
  classical
  unfold bSum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ab _ => ?_
  set φ : MvPolynomial ι K →+* MvPowerSeries ι K := MvPolynomial.coeToMvPowerSeries.ringHom
    with hφ
  set P : ZMod d → MvPolynomial ι K :=
    fun t => ∑ y, MvPolynomial.C (M (t, ab.1, ab.2) y) * MvPolynomial.X y with hPdef
  have hL : ∀ t, linSub M (t, ab.1, ab.2) = φ (P t) := by
    intro t
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [linSub, hPdef, hφ, map_sum, map_mul, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
      MvPolynomial.coe_C, MvPolynomial.coe_X]
  have hsub : MvPowerSeries.HasSubst (fun t => linSub (K := K) M (t, ab.1, ab.2)) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro t; simp [linSub]
  have hPh : ∀ t, MvPolynomial.IsWeightedHomogeneous (fun y => Finsupp.single (lt y) 1) (P t)
      (Finsupp.single t 1) := fun t =>
    frame_lin_hom lt (fun y => M (t, ab.1, ab.2) y) t (fun y hy => hM _ y hy)
  have hwt : Finsupp.weight (fun y => Finsupp.single (lt y) 1)
      (Finsupp.single i A + Finsupp.single j B) =
      Finsupp.single (lt i) A + Finsupp.single (lt j) B := by
    simp only [map_add (f := _), Finsupp.weight_single, Finsupp.smul_single_one]
  have hij' : i ≠ j := fun h => hij (congrArg lt h)
  have hterm : ∀ e : ZMod d →₀ ℕ, MvPowerSeries.coeff (Finsupp.single i A + Finsupp.single j B)
      (e.prod fun t k => linSub M (t, ab.1, ab.2) ^ k) =
      if e = Finsupp.single (lt i) A + Finsupp.single (lt j) B then
        M (lt i, ab.1, ab.2) i ^ A * M (lt j, ab.1, ab.2) j ^ B else 0 := by
    intro e
    have hprod : (e.prod fun t k => linSub M (t, ab.1, ab.2) ^ k) =
        φ (e.prod fun t k => P t ^ k) := by
      simp only [hL, ← map_pow]
      exact (map_finsuppProd φ e _).symm
    rw [hprod, hφ, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coeff_coe]
    split_ifs with he
    · rw [he, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
        Finsupp.prod_single_index (h := fun t k => P t ^ k) (by simp),
        Finsupp.prod_single_index (h := fun t k => P t ^ k) (by simp), mul_comm]
      exact frame_coeff_two (fun y => M (lt i, ab.1, ab.2) y) (fun y => M (lt j, ab.1, ab.2) y)
        i j hij' (fun y hy hyj => hij ((hM _ y hy).symm.trans (by rw [hyj]))) A B
    · by_contra hne
      exact he ((frame_prod_hom lt P hPh e hne).symm.trans hwt)
  rw [MvPowerSeries.coeff_subst hsub, finsum_eq_single _
    (Finsupp.single (lt i) A + Finsupp.single (lt j) B)
    (fun e he => by rw [hterm, if_neg he, smul_zero]), hterm, if_pos rfl, smul_eq_mul]

theorem frame_pure_weight : FramePure.{u} := by
  intro K _ _ _ l d N0 N1 _ hl hpi h0 x hx be hbe s s' hss' k b b' α β
  classical
  have hM : ∀ (z y : ZV d N0 N1), frameM (N1 := N1) x z y ≠ 0 → y.1 = z.1 := by
    intro z y h
    unfold frameM at h
    split_ifs at h with h1
    · exact h1.1
    · exact absurd rfl h
  have hform : ∀ b1 b2 : Fin N1,
      MvPowerSeries.coeff (pureMon l ((s, ⟨0, h0⟩, b1) : ZV d N0 N1) (s', k, b2) α β)
        (bSum (frameM (N1 := N1) x) be) =
      MvPowerSeries.coeff (pureMon l s s' α β) be *
        ∑ ab : Fin N0 × Fin N1, frameM (N1 := N1) x (s, ab.1, ab.2) (s, ⟨0, h0⟩, b1) ^ (l ^ α) *
          frameM (N1 := N1) x (s', ab.1, ab.2) (s', k, b2) ^ (l ^ β) := by
    intro b1 b2
    unfold pureMon
    exact frame_pure_formula Prod.fst (frameM (N1 := N1) x) hM be _ _ _ _ hss'
  have hz : ∀ m : ℕ, (0 : K) ^ (l ^ m) = 0 := fun m => zero_pow (pow_ne_zero _ hl.ne_zero)
  refine ⟨fun hbb' => ?_, fun hyp => ?_⟩
  · rw [hform]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun ab _ => ?_)
    simp only [frameM, true_and]
    by_cases h1 : b = ab.2
    · rw [if_pos h1, if_neg (fun h2 => hbb' (h1.trans h2.symm)), hz, mul_zero]
    · rw [if_neg h1, hz, zero_mul]
  · unfold MonoWtGe
    rw [hform b b]
    have hS : (∑ ab : Fin N0 × Fin N1, frameM (N1 := N1) x (s, ab.1, ab.2) (s, ⟨0, h0⟩, b) ^ (l ^ α) *
          frameM (N1 := N1) x (s', ab.1, ab.2) (s', k, b) ^ (l ^ β)) =
        ∑ a : Fin N0, x (s, ⟨0, h0⟩, a) ^ (l ^ α) * x (s', k, a) ^ (l ^ β) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [frameM, true_and]
      rw [Finset.sum_eq_single b (fun b'' _ hb'' => by rw [if_neg (Ne.symm hb''), hz, zero_mul])
        (fun h => absurd (Finset.mem_univ b) h), if_pos rfl, if_pos rfl]
    rw [hS]
    have hsum1 : ∀ (U : Fin N0 → K), (∀ a, ‖U a‖ ≤ 1) → ‖∑ a, U a‖ ≤ ‖(l : K)‖ → ∀ e : ℕ,
        ‖∑ a, U a ^ (l ^ e)‖ ≤ ‖(l : K)‖ := by
      intro U hU hsU e
      have hfr := frame_frob_norm hl U hU e Finset.univ
      have h1 : ‖(∑ a, U a) ^ (l ^ e)‖ ≤ ‖(l : K)‖ := by
        rw [norm_pow]
        have hle1 : ‖∑ a, U a‖ ≤ 1 :=
          IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun a _ => hU a)
        exact (pow_le_of_le_one (norm_nonneg _) hle1 (pow_ne_zero _ hl.ne_zero)).trans hsU
      have heq : ∑ a, U a ^ (l ^ e) =
          (∑ a, U a) ^ (l ^ e) + -((∑ a, U a) ^ (l ^ e) - ∑ a, U a ^ (l ^ e)) := by ring
      rw [heq]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ?_)
      rw [norm_neg]; exact hfr
    have hSn : ‖∑ a : Fin N0, x (s, ⟨0, h0⟩, a) ^ (l ^ α) * x (s', k, a) ^ (l ^ β)‖ ≤
        ‖(l : K)‖ := by
      split_ifs at hyp with hba
      · have hU : ∀ a, ‖x (s, ⟨0, h0⟩, a) ^ (l ^ (α - β)) * x (s', k, a)‖ ≤ 1 := fun a => by
          rw [norm_mul, norm_pow]
          exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (hx _)) (norm_nonneg _) (hx _)
        have h := hsum1 _ hU hyp β
        have hpow : ∀ a, (x (s, ⟨0, h0⟩, a) ^ (l ^ (α - β)) * x (s', k, a)) ^ (l ^ β) =
            x (s, ⟨0, h0⟩, a) ^ (l ^ α) * x (s', k, a) ^ (l ^ β) := fun a => by
          rw [mul_pow, ← pow_mul, ← pow_add, Nat.sub_add_cancel hba]
        simpa only [hpow] using h
      · have hU : ∀ a, ‖x (s, ⟨0, h0⟩, a) * x (s', k, a) ^ (l ^ (β - α))‖ ≤ 1 := fun a => by
          rw [norm_mul, norm_pow]
          exact mul_le_one₀ (hx _) (pow_nonneg (norm_nonneg _) _) (pow_le_one₀ (norm_nonneg _) (hx _))
        have h := hsum1 _ hU hyp α
        have hpow : ∀ a, (x (s, ⟨0, h0⟩, a) * x (s', k, a) ^ (l ^ (β - α))) ^ (l ^ α) =
            x (s, ⟨0, h0⟩, a) ^ (l ^ α) * x (s', k, a) ^ (l ^ β) := fun a => by
          rw [mul_pow, ← pow_mul, ← pow_add, Nat.sub_add_cancel (le_of_lt (not_le.mp hba))]
        simpa only [hpow] using h
    have hc := hbe (pureMon l s s' α β)
    unfold MonoWtGe at hc
    rw [asmR_dot_pureMon] at hc ⊢
    have hπ : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)
    rw [norm_mul]
    calc ‖MvPowerSeries.coeff (pureMon l s s' α β) be‖ *
          ‖∑ a : Fin N0, x (s, ⟨0, h0⟩, a) ^ (l ^ α) * x (s', k, a) ^ (l ^ β)‖
        ≤ ‖(l : K)‖ ^ (1 / ((l : ℝ) - 1) - 1 - ((l : ℝ) ^ α * rho l + (l : ℝ) ^ β * rho l)) *
            ‖(l : K)‖ :=
          mul_le_mul hc hSn (norm_nonneg _) (Real.rpow_nonneg hπ.le _)
      _ = ‖(l : K)‖ ^ (1 / ((l : ℝ) - 1) - ((l : ℝ) ^ α * rho l + (l : ℝ) ^ β * rho l)) := by
        have he : 1 / ((l : ℝ) - 1) - ((l : ℝ) ^ α * rho l + (l : ℝ) ^ β * rho l) =
            (1 / ((l : ℝ) - 1) - 1 - ((l : ℝ) ^ α * rho l + (l : ℝ) ^ β * rho l)) + 1 := by ring
        rw [he, Real.rpow_add hπ, Real.rpow_one]

end Pure

end Formalism.DworkPowerSeriesWeights
end
end

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

section Collapse

variable {K : Type u} [NormedField K] {ι σ : Type*} (lt : ι → σ)

def jetHom (n : σ →₀ ℕ) (f : MvPowerSeries ι K) : Prop :=
  ∀ m, MvPowerSeries.coeff m f ≠ 0 → m.mapDomain lt = n

theorem jetHom_one : jetHom lt 0 (1 : MvPowerSeries ι K) := by
  classical
  intro m hm
  rw [MvPowerSeries.coeff_one] at hm
  split_ifs at hm with h
  · subst h; simp
  · exact absurd rfl hm

theorem jetHom_mul {n1 n2 : σ →₀ ℕ} {f g : MvPowerSeries ι K} (hf : jetHom lt n1 f)
    (hg : jetHom lt n2 g) : jetHom lt (n1 + n2) (f * g) := by
  classical
  intro m hm
  rw [MvPowerSeries.coeff_mul] at hm
  obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have h1 : MvPowerSeries.coeff p.1 f ≠ 0 := left_ne_zero_of_mul hne
  have h2 : MvPowerSeries.coeff p.2 g ≠ 0 := right_ne_zero_of_mul hne
  rw [← hp, Finsupp.mapDomain_add, hf _ h1, hg _ h2]

theorem jetHom_pow {n : σ →₀ ℕ} {f : MvPowerSeries ι K} (hf : jetHom lt n f) (k : ℕ) :
    jetHom lt (k • n) (f ^ k) := by
  induction k with
  | zero => simpa using jetHom_one (K := K) lt
  | succ k ih => rw [pow_succ, succ_nsmul]; exact jetHom_mul lt ih hf

theorem jetHom_prod {α : Type*} (s : Finset α) (n : α → σ →₀ ℕ) (F : α → MvPowerSeries ι K)
    (h : ∀ a ∈ s, jetHom lt (n a) (F a)) : jetHom lt (∑ a ∈ s, n a) (∏ a ∈ s, F a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using jetHom_one (K := K) lt
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact jetHom_mul lt (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem jetHom_lin [Fintype ι] (c : ι → K) (t : σ) (hc : ∀ i, c i ≠ 0 → lt i = t) :
    jetHom lt (Finsupp.single t 1) (∑ i, MvPowerSeries.C (c i) * MvPowerSeries.X i) := by
  classical
  intro m hm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X] at hm
  obtain ⟨i, -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  split_ifs at hne with h
  · subst h; rw [Finsupp.mapDomain_single, hc i (left_ne_zero_of_mul hne)]
  · simp at hne

theorem jetHom_substProd (a : σ → MvPowerSeries ι K)
    (ha : ∀ t, jetHom lt (Finsupp.single t 1) (a t)) (n : σ →₀ ℕ) :
    jetHom lt n (n.prod fun s e => a s ^ e) := by
  classical
  have h := jetHom_prod lt n.support (fun s => n s • Finsupp.single s 1) (fun s => a s ^ n s)
    fun s _ => jetHom_pow lt (ha s) (n s)
  have hd : ∑ s ∈ n.support, n s • Finsupp.single s 1 = n := by
    simp_rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    exact Finsupp.sum_single n
  rw [hd] at h
  simpa [Finsupp.prod] using h

end Collapse

theorem jet_collapse {K : Type u} [NormedField K] [IsUltrametricDist K] {d N0 N1 : ℕ} [NeZero d]
    {ι : Type*}
    [Fintype ι] [DecidableEq ι] (lt : ι → ZMod d) (M : ZV d N0 N1 → ι → K)
    (hM1 : ∀ x i, ‖M x i‖ ≤ 1) (hMlt : ∀ x i, M x i ≠ 0 → lt i = x.1)
    (be : MvPowerSeries (ZMod d) K) (m : ι →₀ ℕ) :
    ‖MvPowerSeries.coeff m (bSum M be)‖ ≤ ‖MvPowerSeries.coeff (m.mapDomain lt) be‖ := by
  classical
  unfold bSum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun ab _ => ?_
  have hlin0 : ∀ s, MvPowerSeries.constantCoeff (linSub M (s, ab.1, ab.2)) = 0 := fun s => by
    simp [linSub]
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero hlin0
  have hhom : ∀ t, jetHom lt (Finsupp.single t 1) (linSub M (t, ab.1, ab.2)) := fun t =>
    jetHom_lin lt _ t fun i hi => hMlt _ i hi
  have hlinI : ∀ t, WtGe (1 : ℝ) (fun _ : ι => (0 : ℝ)) 0 (linSub M (t, ab.1, ab.2)) := by
    intro t
    unfold linSub
    refine wtGe_sum one_pos _ _ fun i _ => ?_
    simpa using wtGe_CX (K := K) one_pos (fun _ : ι => (0 : ℝ)) i (hM1 (t, ab.1, ab.2) i)
  rw [MvPowerSeries.coeff_subst hs, finsum_eq_single _ (m.mapDomain lt)]
  · rw [smul_eq_mul, norm_mul]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    have hp := wtGe_prod (K := K) one_pos (r := fun _ : ι => (0 : ℝ)) (m.mapDomain lt).support
      (fun s => ((m.mapDomain lt) s : ℝ) * 0)
      (fun s => linSub M (s, ab.1, ab.2) ^ (m.mapDomain lt) s)
      (fun s _ => wtGe_pow one_pos (hlinI s) _) m
    rw [monoWtGe_iff, Real.one_rpow] at hp
    simpa [Finsupp.prod] using hp
  · intro n hn
    have h0 : MvPowerSeries.coeff m (n.prod fun s e => linSub M (s, ab.1, ab.2) ^ e) = 0 := by
      by_contra h
      exact hn (jetHom_substProd lt (fun s => linSub M (s, ab.1, ab.2)) hhom n m h).symm
    rw [h0, smul_zero]

theorem jet_parity {d : ℕ} [NeZero d] (hde : Even d) {s s' : ZMod d} {α β : ℕ}
    (hs : s.val % 2 = 0) (hs' : s'.val % 2 = 1) (h : s + (α : ZMod d) = s' + (β : ZMod d)) :
    Odd (α + β) := by
  have h' : ((s.val + α : ℕ) : ZMod d) = ((s'.val + β : ℕ) : ZMod d) := by
    push_cast; rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rw [ZMod.natCast_eq_natCast_iff] at h'
  have h2 := Nat.ModEq.of_dvd (even_iff_two_dvd.mp hde) h'
  unfold Nat.ModEq at h2
  rw [Nat.odd_iff]
  omega

theorem jet_bipower {d : ℕ} [NeZero d] (hde : Even d) {l : ℕ} (hl : 2 ≤ l) {t1 t2 : ZMod d}
    {α β : ℕ} (h : IsBiPower l (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β))) :
    t1 ≠ t2 ∧ t1 + (α : ZMod d) = t2 + (β : ZMod d) ∧ Odd (α + β) := by
  classical
  obtain ⟨s, s', α', β', hs, hs', -, heq, hn⟩ := h
  have hss : s ≠ s' := by rintro rfl; omega
  have hpar := jet_parity hde hs hs' heq
  have hpos : ∀ k : ℕ, l ^ k ≠ 0 := fun k => pow_ne_zero _ (by omega)
  have hinj : ∀ a b : ℕ, l ^ a = l ^ b → a = b := fun a b hab =>
    Nat.pow_right_injective hl hab
  have F1 : (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β)) s = l ^ α' := by
    rw [hn]; simp [hss]
  have F2 : (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β)) s' = l ^ β' := by
    rw [hn]; simp [Ne.symm hss]
  have F3 : ∀ t, (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β)) t ≠ 0 →
      t = s ∨ t = s' := by
    intro t ht
    rw [hn] at ht
    by_contra hc
    simp only [not_or] at hc
    apply ht
    simp [Ne.symm hc.1, Ne.symm hc.2]
  have G3 : ∀ t, (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β)) t ≠ 0 →
      t = t1 ∨ t = t2 := by
    intro t ht
    by_contra hc
    simp only [not_or] at hc
    apply ht
    simp [Ne.symm hc.1, Ne.symm hc.2]
  have ht12 : t1 ≠ t2 := by
    rintro rfl
    have a := G3 s (by rw [F1]; exact hpos _)
    have b := G3 s' (by rw [F2]; exact hpos _)
    simp only [or_self] at a b
    exact hss (a.trans b.symm)
  have H1 : (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β)) t1 = l ^ α := by
    simp [ht12]
  have H2 : (Finsupp.single t1 (l ^ α) + Finsupp.single t2 (l ^ β)) t2 = l ^ β := by
    simp [Ne.symm ht12]
  refine ⟨ht12, ?_⟩
  rcases F3 t1 (by rw [H1]; exact hpos _) with h1 | h1 <;>
    rcases F3 t2 (by rw [H2]; exact hpos _) with h2 | h2
  · exact absurd (h1.trans h2.symm) ht12
  · subst h1 h2
    have e1 := hinj _ _ (H1.symm.trans F1)
    have e2 := hinj _ _ (H2.symm.trans F2)
    subst e1 e2
    exact ⟨heq, hpar⟩
  · subst h1 h2
    have e1 := hinj _ _ (H1.symm.trans F2)
    have e2 := hinj _ _ (H2.symm.trans F1)
    subst e1 e2
    exact ⟨heq.symm, by rwa [add_comm]⟩
  · exact absurd (h1.trans h2.symm) ht12

theorem jet_rowRad_ge {d : ℕ} {ι : Type} (l : ℕ) (sig eps : ZMod d → ℝ) (lt : ι → ZMod d)
    (isTop : ι → Bool) (spec : ι → Option (ZMod d × ℤ)) (i : ι) (hi : isTop i = false) :
    sig (lt i) ≤ rowRad l sig eps lt isTop spec i := by
  unfold rowRad
  rw [if_neg (by simp [hi])]
  rcases spec i with _ | ⟨s, j⟩
  · exact le_rfl
  · dsimp only
    split_ifs
    · exact le_max_left _ _
    · exact le_max_left _ _

theorem jet_rowRad_nonneg {d : ℕ} {ι : Type} (l : ℕ) (sig eps : ZMod d → ℝ) (lt : ι → ZMod d)
    (isTop : ι → Bool) (spec : ι → Option (ZMod d × ℤ)) (hs : ∀ s, 0 ≤ sig s)
    (he : ∀ s, 0 ≤ eps s) (i : ι) : 0 ≤ rowRad l sig eps lt isTop spec i := by
  cases hi : isTop i
  · exact (hs _).trans (jet_rowRad_ge l sig eps lt isTop spec i hi)
  · unfold rowRad; rw [if_pos hi]; exact he _

theorem jet_rowRad_top {d : ℕ} {ι : Type} (l : ℕ) (sig eps : ZMod d → ℝ) (lt : ι → ZMod d)
    (isTop : ι → Bool) (spec : ι → Option (ZMod d × ℤ)) (i : ι) (hi : isTop i = true) :
    rowRad l sig eps lt isTop spec i = eps (lt i) := by
  unfold rowRad; rw [if_pos hi]

theorem jet_rowRad_spec {d : ℕ} {ι : Type} (l : ℕ) (sig eps : ZMod d → ℝ) (lt : ι → ZMod d)
    (isTop : ι → Bool) (spec : ι → Option (ZMod d × ℤ)) (i : ι) (hi : isTop i = false)
    {s0 : ZMod d} {j : ℤ} (hs : spec i = some (s0, j)) :
    rowRad l sig eps lt isTop spec i = if 0 < j then max (sig (lt i)) (1 - (l : ℝ) ^ j.toNat * eps s0)
      else max (sig (lt i)) ((l : ℝ) ^ (-j).toNat)⁻¹ := by
  unfold rowRad
  rw [if_neg (by simp [hi]), hs]

end Formalism.DworkPowerSeriesWeights
end
end

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

theorem ThmAJetA_of (hS : LemmaS.{u}) (hR : LemmaRA.{u, 0}) (hA : ThmAAssembly)
    (hFP : FramePure.{u}) : ThmAJetA.{u} := by
  intro K _ _ _ l d N0 N1 _ hl hl3 hd hde hpi h0 K0 hK0 ζ hζ be hbe x hx g hg0 hg U hU ε hε
    TT nu1 nu2 size hnu21 hnu1s a ha hsa spec κ hκtop hκD hspec hcap hkill
  classical
  have hodd : Odd l := hl.odd_of_ne_two (by omega)
  have hl2 : 2 ≤ l := hl.two_le
  have hlpos : 0 < l := by omega
  have hpi0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)
  obtain ⟨⟨sig, hsigD, hsigA, hFn⟩, -⟩ := lemmaFa l d hl3 hd hde
    (fun s => (Dl d TT nu1 size s : ℝ)) (fun s => Nat.cast_nonneg _)
  have hsig0 : ∀ s, 0 ≤ sig s := fun s => (hsigD.1 s).1
  have hnotop : ∀ (s : ZMod d) (k : Fin N0), (s ∈ TT ∧ k.val = 0) → spec (s, k) = none := by
    intro s k hsk
    rcases h : spec (s, k) with _ | ⟨s0, j⟩
    · rfl
    · exact absurd hsk (hspec s k s0 j h).2.2.2.1
  obtain ⟨eps, heps0, hepsT, hmain⟩ := hA l d hl3 hd hde TT nu1 nu2 size hnu21 hnu1s sig
    ⟨hsigD, hFn⟩ (ZV d N0 N1) (fun y => y.1) (frameTop TT) (fun y => spec (y.1, y.2.1))
    (fun y => κ y)
    (by
      intro i hi
      have hi' := of_decide_eq_true hi
      exact ⟨hi'.1, hnotop _ _ hi'⟩)
    (by
      intro s hs
      have hset : Finset.univ.filter (fun i : ZV d N0 N1 => i.1 = s ∧ frameTop TT i = true) =
          Finset.univ.image (fun b : Fin N1 => ((s, ⟨0, h0⟩, b) : ZV d N0 N1)) := by
        ext ⟨s', k, b⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, frameTop,
          decide_eq_true_eq, Prod.mk.injEq]
        constructor
        · rintro ⟨rfl, -, hk⟩
          exact ⟨b, rfl, Fin.ext hk.symm, rfl⟩
        · rintro ⟨b', rfl, rfl, rfl⟩
          exact ⟨rfl, hs, rfl⟩
      rw [hset, Finset.sum_image (fun b _ b' _ h => by simpa using h)]
      exact_mod_cast hκtop s hs)
    (by intro s; exact_mod_cast hκD s)
    (by
      intro i s0 j h
      obtain ⟨h1, h2, h3, -, h5, h6⟩ := hspec i.1 i.2.1 s0 j h
      exact ⟨h1, h2, h3, h5, h6⟩)
    (by intro s0 j; exact_mod_cast hcap s0 j)
  have R := dualRadiiInequalities l d hl3 hd hde TT sig eps hsigA hsig0 heps0 hepsT
  obtain ⟨hS1, hS2⟩ := hS K l d hl hodd hd hde hpi K0 hK0 ζ hζ be hbe
  have hM1 : ∀ (z i : ZV d N0 N1), ‖frameM (N1 := N1) x z i‖ ≤ 1 := by
    intro z i
    unfold frameM
    split_ifs
    · exact hx _
    · simp
  have hMlt : ∀ (z i : ZV d N0 N1), frameM (N1 := N1) x z i ≠ 0 → i.1 = z.1 := by
    intro z i h
    unfold frameM at h
    split_ifs at h with h'
    · exact h'.1
    · exact absurd rfl h

  have hsmall : ∀ (i j : ZV d N0 N1) (α β : ℕ),
      ¬ MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) (pureMon l i j α β)
        (MvPowerSeries.coeff (pureMon l i j α β) (bSum (frameM (N1 := N1) x) be)) →
      i.1 ≠ j.1 ∧ i.1 + (α : ZMod d) = j.1 + (β : ZMod d) ∧ Odd (α + β) := by
    intro i j α β hnot
    apply jet_bipower hde hl2
    by_contra hnb
    apply hnot
    have hc := jet_collapse (fun y : ZV d N0 N1 => y.1) (frameM (N1 := N1) x) hM1 hMlt be
      (pureMon l i j α β)
    have hmd : (pureMon l i j α β).mapDomain (fun y : ZV d N0 N1 => y.1) =
        Finsupp.single i.1 (l ^ α) + Finsupp.single j.1 (l ^ β) := by
      simp [pureMon, Finsupp.mapDomain_add, Finsupp.mapDomain_single]
    rw [hmd] at hc
    have h2 := hS2 _ hnb
    rw [monoWtGe_iff] at h2 ⊢
    refine hc.trans (h2.trans_eq ?_)
    congr 2
    rw [asmR_dot_pureMon, dot_add, asmR_dot_single, asmR_dot_single]
    push_cast
    ring

  have key : ∀ (i j : ZV d N0 N1) (α β : ℕ), pureMon l i j α β ≤ κ →
      ¬ MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) (pureMon l i j α β)
        (MvPowerSeries.coeff (pureMon l i j α β) (bSum (frameM (N1 := N1) x) be)) →
      frameTop TT i = true → frameTop TT j = false →
      1 ≤ (l : ℝ) ^ α * rowRad l sig eps (fun y : ZV d N0 N1 => y.1) (frameTop TT)
          (fun y => spec (y.1, y.2.1)) i +
        (l : ℝ) ^ β * rowRad l sig eps (fun y : ZV d N0 N1 => y.1) (frameTop TT)
          (fun y => spec (y.1, y.2.1)) j := by
    rintro ⟨s0, k0, b⟩ ⟨s, k, b'⟩ α β hle hnot hti htj
    obtain ⟨hne, heq, hab⟩ := hsmall _ _ α β hnot
    simp only at hne heq
    have hti' : s0 ∈ TT ∧ k0.val = 0 := of_decide_eq_true hti
    have htj' : ¬ (s ∈ TT ∧ k.val = 0) := of_decide_eq_false htj
    obtain rfl : k0 = ⟨0, h0⟩ := Fin.ext hti'.2
    rw [jet_rowRad_top l sig eps _ _ _ _ hti]
    obtain ⟨hz, hw⟩ := hFP K l d N0 N1 hl hpi h0 x hx be hS1 s0 s hne k b b' α β
    have hbb : b = b' := by
      by_contra hbb
      apply hnot
      rw [hz hbb, monoWtGe_iff, norm_zero]
      exact Real.rpow_nonneg hpi0.le _
    subst hbb
    have hij : ((s0, ⟨0, h0⟩, b) : ZV d N0 N1) ≠ (s, k, b) := fun h => hne (congrArg Prod.fst h)
    have hκi : l ^ α ≤ κ (s0, ⟨0, h0⟩, b) := by
      have := hle (s0, ⟨0, h0⟩, b)
      simpa [pureMon, Finsupp.single_apply, hij, Ne.symm hij] using this
    have hκj : l ^ β ≤ κ (s, k, b) := by
      have := hle (s, k, b)
      simpa [pureMon, Finsupp.single_apply, hij, Ne.symm hij] using this
    have hnu : κ (s0, ⟨0, h0⟩, b) ≤ nu1 s0 := by
      rw [← hκtop s0 hti'.1]
      exact Finset.single_le_sum (f := fun b => κ (s0, ⟨0, h0⟩, b)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ b)
    have hsz : κ (s, k, b) ≤ size s := by
      have h1 : κ (s, k, b) ≤ Dl d TT nu1 size s := by
        rw [← hκD s]
        exact Finset.single_le_sum (f := fun y => κ y) (fun _ _ => Nat.zero_le _)
          (by simp [htj])
      refine h1.trans ?_
      unfold Dl
      split_ifs <;> omega
    obtain ⟨j0, hj0⟩ : ∃ j0 : ℤ, j0 = (α : ℤ) - β := ⟨_, rfl⟩
    have hsj : s = s0 + (j0 : ZMod d) := by
      rw [hj0]
      push_cast
      linear_combination (-1 : ZMod d) * heq
    have hjodd : Odd j0 := by
      obtain ⟨c, hc⟩ := hab
      exact ⟨(c : ℤ) - β, by omega⟩
    have hlev1 : 0 < j0 → l ^ j0.toNat ≤ nu1 s0 := by
      intro hj
      have : j0.toNat = α - β := by omega
      rw [this]
      exact (Nat.pow_le_pow_right hlpos (Nat.sub_le α β)).trans (hκi.trans hnu)
    have hlev2 : j0 < 0 → l ^ (-j0).toNat ≤ size s := by
      intro hj
      have : (-j0).toNat = β - α := by omega
      rw [this]
      exact (Nat.pow_le_pow_right hlpos (Nat.sub_le β α)).trans (hκj.trans hsz)
    by_cases hsp : spec (s, k) = some (s0, j0)
    · rw [jet_rowRad_spec l sig eps (fun y : ZV d N0 N1 => y.1) (frameTop TT)
        (fun y => spec (y.1, y.2.1)) (s, k, b) htj hsp]
      rcases lt_trichotomy α β with hαβ | hαβ | hαβ
      · rw [if_neg (by omega)]
        have ht : (-j0).toNat = β - α := by omega
        rw [ht]
        have := R.2.2.1 s0 α (β - α) (max (sig s) ((l : ℝ) ^ (β - α))⁻¹) (by omega)
          (le_max_right _ _)
        rwa [Nat.add_sub_cancel' hαβ.le] at this
      · subst hαβ
        exfalso
        obtain ⟨c, hc⟩ := hab
        omega
      · rw [if_pos (by omega)]
        have ht : j0.toNat = α - β := by omega
        rw [ht]
        have := R.2.1 s0 β (α - β) (max (sig s) (1 - (l : ℝ) ^ (α - β) * eps s0)) (by omega)
          (le_max_right _ _)
        rwa [Nat.add_sub_cancel' hαβ.le] at this
    · exfalso
      apply hnot
      apply hw
      have hk := hkill s0 hti'.1 s k j0 htj' hjodd hsj hlev1 hlev2 hsp
      by_cases hβα : β ≤ α
      · rw [if_pos hβα]
        rw [if_pos (by omega : (0 : ℤ) ≤ j0)] at hk
        have ht : j0.toNat = α - β := by omega
        rwa [ht] at hk
      · rw [if_neg hβα]
        rw [if_neg (by omega : ¬ (0 : ℤ) ≤ j0)] at hk
        have ht : (-j0).toNat = β - α := by omega
        rwa [ht] at hk
  have hpure : ∀ (i j : ZV d N0 N1) (α β : ℕ), pureMon l i j α β ≤ κ →
      ¬ MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) (pureMon l i j α β)
        (MvPowerSeries.coeff (pureMon l i j α β) (bSum (frameM (N1 := N1) x) be)) →
      1 ≤ (l : ℝ) ^ α * rowRad l sig eps (fun y : ZV d N0 N1 => y.1) (frameTop TT)
          (fun y => spec (y.1, y.2.1)) i +
        (l : ℝ) ^ β * rowRad l sig eps (fun y : ZV d N0 N1 => y.1) (frameTop TT)
          (fun y => spec (y.1, y.2.1)) j := by
    intro i j α β hle hnot
    obtain ⟨hne, heq, hab⟩ := hsmall i j α β hnot
    have hsw : pureMon l j i β α = pureMon l i j α β := by
      unfold pureMon; exact add_comm _ _
    cases hti : frameTop TT i <;> cases htj : frameTop TT j
    · exact R.1 i.1 j.1 α β _ _ (jet_rowRad_ge l sig eps _ _ _ i hti)
        (jet_rowRad_ge l sig eps _ _ _ j htj) hab heq
    · have h := key j i β α (by rw [hsw]; exact hle) (by rw [hsw]; exact hnot) htj hti
      linarith
    · exact key i j α β hle hnot hti htj
    · rw [jet_rowRad_top l sig eps _ _ _ _ hti, jet_rowRad_top l sig eps _ _ _ _ htj]
      exact R.2.2.2 i.1 (of_decide_eq_true hti).1 j.1 (of_decide_eq_true htj).1 α β hab heq

  have hκa : ∀ y : ZV d N0 N1, κ y ≤ a := by
    rintro ⟨s, k, b⟩
    cases hty : frameTop TT ((s, k, b) : ZV d N0 N1)
    · have h1 : κ (s, k, b) ≤ Dl d TT nu1 size s := by
        rw [← hκD s]
        exact Finset.single_le_sum (f := fun y => κ y) (fun _ _ => Nat.zero_le _)
          (by simp [hty])
      have h2 : Dl d TT nu1 size s ≤ size s := by
        unfold Dl
        split_ifs <;> omega
      exact h1.trans (h2.trans (hsa s))
    · have hty' : s ∈ TT ∧ k.val = 0 := of_decide_eq_true hty
      obtain rfl : k = ⟨0, h0⟩ := Fin.ext hty'.2
      have h1 : κ (s, ⟨0, h0⟩, b) ≤ nu1 s := by
        rw [← hκtop s hty'.1]
        exact Finset.single_le_sum (f := fun b => κ (s, ⟨0, h0⟩, b)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ b)
      exact h1.trans ((hnu1s s).trans (hsa s))
  have hLR := hR K l d N0 N1 hl hodd hd hde hpi K0 hK0 ζ hζ be hbe (ZV d N0 N1)
    (fun y => y.1) (frameM (N1 := N1) x) hM1 hMlt g hg0 hg U hU ε hε
    (rowRad l sig eps (fun y : ZV d N0 N1 => y.1) (frameTop TT) (fun y => spec (y.1, y.2.1)))
    (jet_rowRad_nonneg l sig eps _ _ _ hsig0 heps0) κ a ha hκa hpure
  have hcard : (Fintype.card (ZV d N0 N1) : ℝ) = (d : ℝ) * N0 * N1 := by
    simp only [ZV, Fintype.card_prod, ZMod.card, Fintype.card_fin]
    push_cast
    ring
  rw [hcard] at hLR
  refine hLR.trans (Real.rpow_le_rpow_of_exponent_ge hpi0 hpi.le ?_)
  linarith [hmain]

theorem theorem_A_one_monomial_log_loss : ThmAJetA.{u} :=
  ThmAJetA_of lemmaS.{u} lemma_R_log_loss.{u, 0} rowRadiusAssembly frame_pure_weight.{u}

end Formalism.DworkPowerSeriesWeights
