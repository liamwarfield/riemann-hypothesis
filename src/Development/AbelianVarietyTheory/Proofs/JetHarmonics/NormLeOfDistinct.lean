module

public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormLeOfDistinct
noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.Triang

variable {q : ℕ} [Fact q.Prime]

theorem bd_one_mul {f g : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (hg : Bd 1 g) : Bd 1 (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hf _) (norm_nonneg _) (hg _)

theorem bd_one_pow {f : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (n : ℕ) : Bd 1 (f ^ n) := by
  induction n with
  | zero =>
    intro m
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs <;> simp
  | succ n ih =>
    rw [pow_succ]
    exact bd_one_mul ih hf

theorem norm_le_of_distinct {ι : Type*} (s : Finset ι) (e : ι → ℕ) (u : ι → ℂ_[q]⟦X⟧) (c : ι → ℂ_[q]) (B : ℝ)
    (he : Set.InjOn e s) (hu : ∀ j ∈ s, Bd 1 (u j)) (h0 : ∀ j ∈ s, ‖constantCoeff (u j)‖ = 1)
    (hB : Bd B (∑ j ∈ s, C (c j) * (X ^ e j * u j))) : ∀ j ∈ s, ‖c j‖ ≤ B := by
  classical
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hcoeff : ∀ N, coeff N (∑ j ∈ s, C (c j) * (X ^ e j * u j)) =
      ∑ j ∈ s, c j * (if e j ≤ N then coeff (N - e j) (u j) else 0) := by
    intro N
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  have key : ∀ N, ∀ j ∈ s, e j = N → ‖c j‖ ≤ B := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    intro j hj hjN
    have hsplit := (hcoeff N).trans (Finset.add_sum_erase s _ hj).symm
    beta_reduce at hsplit
    have hjterm : c j * (if e j ≤ N then coeff (N - e j) (u j) else 0) = c j * constantCoeff (u j) := by
      rw [if_pos hjN.le, hjN, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    have hrest : ‖∑ i ∈ s.erase j, c i * (if e i ≤ N then coeff (N - e i) (u i) else 0)‖ ≤ B := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB0 fun i hi => ?_
      obtain ⟨hij, his⟩ := Finset.mem_erase.mp hi
      split_ifs with hle
      · have hlt : e i < N := lt_of_le_of_ne hle fun h => hij (he his hj (h.trans hjN.symm))
        rw [norm_mul]
        calc ‖c i‖ * ‖coeff (N - e i) (u i)‖ ≤ B * 1 :=
              mul_le_mul (ih _ hlt i his rfl) (hu i his _) (norm_nonneg _) hB0
          _ = B := mul_one B
      · simpa using hB0
    have hmain : c j * constantCoeff (u j) = coeff N (∑ j ∈ s, C (c j) * (X ^ e j * u j)) -
        ∑ i ∈ s.erase j, c i * (if e i ≤ N then coeff (N - e i) (u i) else 0) := by
      linear_combination -hsplit - hjterm
    have hnorm : ‖c j‖ = ‖c j * constantCoeff (u j)‖ := by rw [norm_mul, h0 j hj, mul_one]
    rw [hnorm, hmain, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hB N) ?_)
    rwa [norm_neg]
  exact fun j hj => key (e j) j hj rfl

theorem coeff_norm_le : ∀ (q : ℕ) [Fact q.Prime] (xs ys : ℂ_[q]⟦X⟧) (k : ℕ) (a b : ℕ → ℂ_[q]) (B : ℝ), Bd 1 xs → Bd 1 ys → ‖constantCoeff xs‖ = 1 → ‖constantCoeff ys‖ = 1 → Bd B (∑ i ∈ Finset.range (k + 1), (C (a i) * X ^ (2 * (k - i) + 3) * xs ^ i + C (b i) * X ^ (2 * (k - i)) * xs ^ i * ys)) → ∀ i ≤ k, ‖a i‖ ≤ B ∧ ‖b i‖ ≤ B := by
  intro q _ xs ys k a b B hxs hys hx0 hy0 hB
  classical
  let s : Finset (Bool × ℕ) := Finset.univ ×ˢ Finset.range (k + 1)
  let e : Bool × ℕ → ℕ := fun j => bif j.1 then 2 * (k - j.2) + 3 else 2 * (k - j.2)
  let u : Bool × ℕ → ℂ_[q]⟦X⟧ := fun j => bif j.1 then xs ^ j.2 else xs ^ j.2 * ys
  let c : Bool × ℕ → ℂ_[q] := fun j => bif j.1 then a j.2 else b j.2
  have hmem : ∀ {j : Bool × ℕ}, j ∈ s → j.2 < k + 1 := fun hj =>
    Finset.mem_range.mp (Finset.mem_product.mp hj).2
  have he : Set.InjOn e s := by
    rintro ⟨b₁, i₁⟩ h₁ ⟨b₂, i₂⟩ h₂ heq
    have hi₁ := hmem (Finset.mem_coe.mp h₁)
    have hi₂ := hmem (Finset.mem_coe.mp h₂)
    cases b₁ <;> cases b₂ <;> simp only [e, cond_true, cond_false] at heq hi₁ hi₂ <;>
      first | (exfalso; omega) | (congr 1; omega)
  have hu : ∀ j ∈ s, Bd 1 (u j) := by
    rintro ⟨_ | _, i⟩ _
    · exact bd_one_mul (bd_one_pow hxs i) hys
    · exact bd_one_pow hxs i
  have h0 : ∀ j ∈ s, ‖constantCoeff (u j)‖ = 1 := by
    rintro ⟨_ | _, i⟩ _
    · show ‖constantCoeff (xs ^ i * ys)‖ = 1
      rw [map_mul, map_pow, norm_mul, norm_pow, hx0, hy0, one_pow, one_mul]
    · show ‖constantCoeff (xs ^ i)‖ = 1
      rw [map_pow, norm_pow, hx0, one_pow]
  have hsum : (∑ j ∈ s, C (c j) * (X ^ e j * u j)) = ∑ i ∈ Finset.range (k + 1),
      (C (a i) * X ^ (2 * (k - i) + 3) * xs ^ i + C (b i) * X ^ (2 * (k - i)) * xs ^ i * ys) := by
    simp only [s]
    rw [Finset.sum_product, Fintype.sum_bool, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [e, u, c, cond_true, cond_false]
    ring
  have hB' : Bd B (∑ j ∈ s, C (c j) * (X ^ e j * u j)) := by
    rw [hsum]
    exact hB
  have key := norm_le_of_distinct s e u c B he hu h0 hB'
  intro i hi
  have hi' : i ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
  exact ⟨key (true, i) (Finset.mem_product.mpr ⟨Finset.mem_univ _, hi'⟩),
    key (false, i) (Finset.mem_product.mpr ⟨Finset.mem_univ _, hi'⟩)⟩

end GlobalTheory.MomOne.Triang
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HeisenbergOperatorsOrthogonalFrameCoords
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HeisenbergOperatorsOrthogonalFrameCoords
open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators

namespace GlobalTheory.MomOne.Frame

variable {g : ℕ}

theorem hf_sum_left {ι : Type} [Fintype ι] (Hm : Matrix (Fin g) (Fin g) ℂ) (z : ι → ℂ) (x : ι → Fin g → ℂ)
    (w : Fin g → ℂ) : hf Hm (∑ i, z i • x i) w = ∑ i, z i * hf Hm (x i) w := by
  simp only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem hf_sum_right {ι : Type} [Fintype ι] (Hm : Matrix (Fin g) (Fin g) ℂ) (z : ι → ℂ) (x : ι → Fin g → ℂ)
    (w : Fin g → ℂ) : hf Hm w (∑ i, z i • x i) = ∑ i, conj (z i) * hf Hm w (x i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem beta_sum_left {ι : Type} [Fintype ι] (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (z : ι → ℂ) (x : ι → Fin g → ℂ)
    (w : Fin g → ℂ) : beta d Hm (∑ i, z i • x i) w = ∑ i, z i * beta d Hm (x i) w := by
  simp only [beta, hf_sum_left, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem beta_sum_right {ι : Type} [Fintype ι] (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (z : ι → ℂ) (x : ι → Fin g → ℂ)
    (w : Fin g → ℂ) : beta d Hm w (∑ i, z i • x i) = ∑ i, conj (z i) * beta d Hm w (x i) := by
  simp only [beta, hf_sum_right, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

section
variable {d : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} {x : Fin g → Fin g → ℂ} {a : Fin g → ℕ}

theorem beta_coord (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) (z : Fin g → ℂ) (j : Fin g) :
    beta d Hm (∑ i, z i • x i) (x j) = z j * a j := by
  simp [beta_sum_left, hx]

theorem beta_frame (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) (z w : Fin g → ℂ) :
    beta d Hm (∑ i, z i • x i) (∑ i, w i • x i) = ∑ i, (a i : ℂ) * (z i * conj (w i)) := by
  rw [beta_sum_right]
  exact Finset.sum_congr rfl fun i _ => by rw [beta_coord hx]; ring

theorem hf_frame (hd : 0 < d) (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) (z w : Fin g → ℂ) :
    hf Hm (∑ i, z i • x i) (∑ i, w i • x i) = ∑ i, (a i : ℂ) * h1 d (z i) (w i) := by
  have hs : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by
    have : Real.sqrt d ≠ 0 := by positivity
    exact_mod_cast this
  have h := beta_frame hx z w
  have e : hf Hm (∑ i, z i • x i) (∑ i, w i • x i) =
      ((2 / Real.sqrt d : ℝ) : ℂ) * beta d Hm (∑ i, z i • x i) (∑ i, w i • x i) := by
    rw [beta]; push_cast; field_simp
  rw [e, h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [h1]; ring

theorem expand (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) (ha : ∀ i, 0 < a i)
    (v : Fin g → ℂ) : v = ∑ i, (beta d Hm v (x i) / (a i : ℂ)) • x i := by
  have ha' : ∀ i, (a i : ℂ) ≠ 0 := fun i => by exact_mod_cast (ha i).ne'
  let L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := Fintype.linearCombination ℂ x
  have hL : ∀ z, L z = ∑ i, z i • x i := fun z => Fintype.linearCombination_apply _ _ _
  have hinj : Function.Injective L := by
    intro z w h
    funext j
    have h1 := beta_coord hx z j
    have h2 := beta_coord hx w j
    rw [← hL] at h1 h2
    rw [h, h2] at h1
    exact (mul_right_cancel₀ (ha' j) h1).symm
  obtain ⟨z, rfl⟩ := (LinearMap.injective_iff_surjective.1 hinj) v
  rw [hL]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [beta_coord hx, mul_div_cancel_right₀ _ (ha' i)]

theorem opU_frame (hd : 0 < d) (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0)
    {m : ℕ} (c : Fin m → ℂ) (f : Fin m → Fin g → ℂ → ℂ) (G : (Fin g → ℂ) → ℂ)
    (hG : ∀ z : Fin g → ℂ, G (∑ i, z i • x i) = ∑ j, c j * ∏ i, f j i (z i) ^ a i) (t z : Fin g → ℂ) :
    opU Hm (∑ i, t i • x i) G (∑ i, z i • x i) = ∑ j, c j * ∏ i, U1 d (t i) (f j i) (z i) ^ a i := by
  have e : (∑ i, z i • x i) + ∑ i, t i • x i = ∑ i, (z + t) i • x i := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  rw [opU, e, hG, hf_frame hd hx, hf_frame hd hx, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [U1, mul_pow, Finset.prod_mul_distrib, ← Complex.exp_nat_mul, ← Complex.exp_sum, Pi.add_apply,
    Finset.mul_sum, ← Finset.sum_sub_distrib, mul_assoc]
  congr 3
  exact Finset.sum_congr rfl fun i _ => by ring

theorem opW_frame (hd : 0 < d) (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0)
    {m : ℕ} (c : Fin m → ℂ) (f : Fin m → Fin g → ℂ → ℂ) (G : (Fin g → ℂ) → ℂ)
    (hG : ∀ z : Fin g → ℂ, G (∑ i, z i • x i) = ∑ j, c j * ∏ i, f j i (z i) ^ a i) (t z : Fin g → ℂ) :
    opW d Hm (∑ i, t i • x i) G (∑ i, z i • x i) = ∑ j, c j * ∏ i, W1 d (t i) (f j i) (z i) ^ a i := by
  have e : (((beta d Hm (∑ i, t i • x i) (∑ i, t i • x i)).re : ℝ) : ℂ) =
      ∑ i, (a i : ℂ) * ((Complex.normSq (t i) : ℝ) : ℂ) := by
    rw [beta_frame hx]
    simp only [Complex.mul_conj]
    have : (∑ i, (a i : ℂ) * ((Complex.normSq (t i) : ℝ) : ℂ)) = ((∑ i, (a i : ℝ) * Complex.normSq (t i) : ℝ) : ℂ) := by
      push_cast; rfl
    rw [this, Complex.ofReal_re]
  rw [opW, opU_frame hd hx c f G hG, e, Finset.mul_sum _ (fun j => c j * _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [W1, mul_pow, Finset.prod_mul_distrib, ← Complex.exp_nat_mul, ← Complex.exp_sum, Finset.mul_sum]
  rw [mul_left_comm]
  congr 3
  exact Finset.sum_congr rfl fun i _ => by ring

end

theorem jetV_frame (x : Fin g → Fin g → ℂ) (G : (Fin g → ℂ) → ℂ) (hG : ContDiff ℂ ⊤ G) (k : ℕ)
    (ys : Fin k → Fin g → ℂ) :
    jetV G (fun l => ∑ i, ys l i • x i) = iteratedFDeriv ℂ k (fun z : Fin g → ℂ => G (∑ i, z i • x i)) 0 ys := by
  let L : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) := LinearMap.toContinuousLinearMap (Fintype.linearCombination ℂ x)
  have hL : ∀ z, L z = ∑ i, z i • x i := fun z => Fintype.linearCombination_apply _ _ _
  have e : (fun z : Fin g → ℂ => G (∑ i, z i • x i)) = G ∘ L := by
    funext z; simp [hL]
  rw [e, L.iteratedFDeriv_comp_right hG 0 le_top, ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero, jetV]
  simp only [hL]

theorem coord : ∀ (g : ℕ) (S : Setup g) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ), 0 < S.d → (∀ i j, beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) → (∀ i, 0 < a i) → (∀ v : Fin g → ℂ, v = ∑ i, (beta S.d S.Hm v (x i) / (a i : ℂ)) • x i) ∧ (∀ z w : Fin g → ℂ, hf S.Hm (∑ i, z i • x i) (∑ i, w i • x i) = ∑ i, (a i : ℂ) * h1 S.d (z i) (w i)) ∧ (∀ (m : ℕ) (c : Fin m → ℂ) (f : Fin m → Fin g → ℂ → ℂ) (G : (Fin g → ℂ) → ℂ), (∀ z : Fin g → ℂ, G (∑ i, z i • x i) = ∑ j, c j * ∏ i, f j i (z i) ^ a i) → ∀ t z : Fin g → ℂ, opU S.Hm (∑ i, t i • x i) G (∑ i, z i • x i) = ∑ j, c j * ∏ i, U1 S.d (t i) (f j i) (z i) ^ a i ∧ opW S.d S.Hm (∑ i, t i • x i) G (∑ i, z i • x i) = ∑ j, c j * ∏ i, W1 S.d (t i) (f j i) (z i) ^ a i) ∧ ∀ (G : (Fin g → ℂ) → ℂ), ContDiff ℂ ⊤ G → ∀ (k : ℕ) (ys : Fin k → Fin g → ℂ), jetV G (fun l => ∑ i, ys l i • x i) = iteratedFDeriv ℂ k (fun z : Fin g → ℂ => G (∑ i, z i • x i)) 0 ys :=
  fun _ _ x _ hd hx ha =>
    ⟨expand hx ha, hf_frame hd hx,
      fun _ c f G hG t z => ⟨opU_frame hd hx c f G hG t z, opW_frame hd hx c f G hG t z⟩,
      jetV_frame x⟩

end GlobalTheory.MomOne.Frame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HeisenbergOperatorsOrthogonalFrameCoordsStatement
open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOperators_orthogonalFrame_coords : ∀ (g : ℕ) (S : Setup g) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ), 0 < S.d → (∀ i j, beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) → (∀ i, 0 < a i) → (∀ v : Fin g → ℂ, v = ∑ i, (beta S.d S.Hm v (x i) / (a i : ℂ)) • x i) ∧ (∀ z w : Fin g → ℂ, hf S.Hm (∑ i, z i • x i) (∑ i, w i • x i) = ∑ i, (a i : ℂ) * h1 S.d (z i) (w i)) ∧ (∀ (m : ℕ) (c : Fin m → ℂ) (f : Fin m → Fin g → ℂ → ℂ) (G : (Fin g → ℂ) → ℂ), (∀ z : Fin g → ℂ, G (∑ i, z i • x i) = ∑ j, c j * ∏ i, f j i (z i) ^ a i) → ∀ t z : Fin g → ℂ, opU S.Hm (∑ i, t i • x i) G (∑ i, z i • x i) = ∑ j, c j * ∏ i, U1 S.d (t i) (f j i) (z i) ^ a i ∧ opW S.d S.Hm (∑ i, t i • x i) G (∑ i, z i • x i) = ∑ j, c j * ∏ i, W1 S.d (t i) (f j i) (z i) ^ a i) ∧ ∀ (G : (Fin g → ℂ) → ℂ), ContDiff ℂ ⊤ G → ∀ (k : ℕ) (ys : Fin k → Fin g → ℂ), jetV G (fun l => ∑ i, ys l i • x i) = iteratedFDeriv ℂ k (fun z : Fin g → ℂ => G (∑ i, z i • x i)) 0 ys := by
  first | exact @GlobalTheory.MomOne.Frame.coord | exact GlobalTheory.MomOne.Frame.coord | (intros; apply GlobalTheory.MomOne.Frame.coord <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffSubstEq
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.FeUniq

variable {q : ℕ} [Fact q.Prime]

theorem intSer_mul {f g : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (hg : Bd 1 g) : Bd 1 (f * g) := by
  intro n
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hf _) (norm_nonneg _) (hg _)

theorem intSer_C {c : ℂ_[q]} (hc : ‖c‖ ≤ 1) : Bd 1 (C c : ℂ_[q]⟦X⟧) := by
  intro n
  rw [coeff_C]
  split_ifs
  · exact hc
  · simp

theorem intSer_pow {f : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (n : ℕ) : Bd 1 (f ^ n) := by
  induction n with
  | zero => simpa using intSer_C (q := q) (c := 1) (by simp)
  | succ n ih => rw [pow_succ]; exact intSer_mul ih hf

theorem intSer_aeval {h : ℂ_[q]⟦X⟧} (hh : Bd 1 h) (P : Polynomial ℂ_[q]) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) :
    Bd 1 (Polynomial.aeval h P) := by
  intro n
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Polynomial.aeval_eq_sum_range, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  rw [coeff_smul, smul_eq_mul, norm_mul]
  exact mul_le_one₀ (hP _) (norm_nonneg _) (intSer_pow hh i n)

theorem intSer_of_funEq (f h A B : ℂ_[q]⟦X⟧) (N : ℕ) (hf : constantCoeff f = 1) (hh : Bd 1 h)
    (hh0 : constantCoeff h = 0) (hh1 : ‖coeff 1 h‖ = 1) (hN : ‖(N : ℂ_[q])‖ < 1) (hA : Bd 1 A)
    (hA0 : constantCoeff A = 1) (hB : Bd 1 B) (hB0 : constantCoeff B = 1)
    (e : (PowerSeries.subst h f : ℂ_[q]⟦X⟧) * A = f ^ N * B) : Bd 1 f := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hf]
  have hs : HasSubst h := HasSubst.of_constantCoeff_zero' hh0
  set P : Polynomial ℂ_[q] := trunc n f with hP
  have hPi : ∀ i, ‖P.coeff i‖ ≤ 1 := by
    intro i
    rw [hP, coeff_trunc]
    split_ifs with hi
    · exact ih i hi
    · simp
  have hPs : Bd 1 (P : ℂ_[q]⟦X⟧) := fun i => by rw [Polynomial.coeff_coe]; exact hPi i
  have hP0 : constantCoeff (P : ℂ_[q]⟦X⟧) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hP, coeff_trunc, if_pos hn,
      coeff_zero_eq_constantCoeff_apply, hf]
  obtain ⟨Q, hQ⟩ : (X : ℂ_[q]⟦X⟧) ^ n ∣ f - P := by
    rw [X_pow_dvd_iff]
    intro m hm
    rw [map_sub, Polynomial.coeff_coe, hP, coeff_trunc, if_pos hm, sub_self]
  have hX : ∀ g : ℂ_[q]⟦X⟧, coeff n (X ^ n * g) = constantCoeff g := fun g => by
    simpa using coeff_X_pow_mul g n 0
  have hQ0 : constantCoeff Q = coeff n f := by
    rw [← hX, ← hQ, map_sub, Polynomial.coeff_coe, hP, coeff_trunc, if_neg (lt_irrefl n), sub_zero]
  obtain ⟨h', hh'⟩ : (X : ℂ_[q]⟦X⟧) ∣ h := X_dvd_iff.2 hh0
  have h'0 : constantCoeff h' = coeff 1 h := by
    rw [hh', coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  have hfe : f = (P : ℂ_[q]⟦X⟧) + X ^ n * Q := by rw [← hQ]; ring
  have hsQ : constantCoeff (PowerSeries.subst h Q : ℂ_[q]⟦X⟧) = constantCoeff Q := by
    obtain ⟨Q', hQ'⟩ : (X : ℂ_[q]⟦X⟧) ∣ Q - C (constantCoeff Q) := X_dvd_iff.2 (by simp)
    have : Q = C (constantCoeff Q) + X * Q' := by rw [← hQ']; ring
    conv_lhs => rw [this, subst_add hs, subst_mul hs, subst_X hs]
    have hC : (PowerSeries.subst h (C (constantCoeff Q) : ℂ_[q]⟦X⟧) : ℂ_[q]⟦X⟧) = C (constantCoeff Q) := by
      rw [← Polynomial.coe_C, subst_coe hs, Polynomial.aeval_C]; simp
    rw [hC]
    simp [hh0]
  have hL : (PowerSeries.subst h f : ℂ_[q]⟦X⟧) * A =
      Polynomial.aeval h P * A + X ^ n * (h' ^ n * PowerSeries.subst h Q * A) := by
    conv_lhs => rw [hfe, subst_add hs, subst_mul hs, subst_pow hs, subst_X hs, subst_coe hs]
    have : h ^ n = X ^ n * h' ^ n := by rw [hh', mul_pow]
    rw [this]; ring
  have hR : f ^ N * B = (P : ℂ_[q]⟦X⟧) ^ N * B +
      X ^ n * (Q * (∑ i ∈ Finset.range N, f ^ i * (P : ℂ_[q]⟦X⟧) ^ (N - 1 - i)) * B) := by
    have := geom_sum₂_mul f (P : ℂ_[q]⟦X⟧) N
    rw [hQ] at this
    linear_combination (-B) * this
  have key := congrArg (coeff n) e
  rw [hL, hR, map_add (f := _), map_add (f := _), hX, hX] at key
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, map_pow, map_sum, hA0, hB0, hf, hP0, hsQ, hQ0, h'0, one_pow, mul_one,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul] at key
  have h1 := intSer_mul (intSer_aeval hh P hPi) hA n
  have h2 := intSer_mul (intSer_pow hPs N) hB n
  have k2 : (coeff 1 h ^ n - N) * coeff n f =
      coeff n ((P : ℂ_[q]⟦X⟧) ^ N * B) - coeff n (Polynomial.aeval h P * A) := by
    linear_combination key
  have hu : ‖coeff 1 h ^ n - (N : ℂ_[q])‖ = 1 := by
    have hp : ‖coeff 1 h ^ n‖ = 1 := by rw [norm_pow, hh1, one_pow]
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [hp, norm_neg]; exact hN.ne'), hp, norm_neg, max_eq_left hN.le]
  have := congrArg norm k2
  rw [norm_mul, hu, one_mul] at this
  rw [this, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 (by rwa [norm_neg]))

theorem subst_C_eq {h : ℂ_[q]⟦X⟧} (hs : HasSubst h) (c : ℂ_[q]) :
    (PowerSeries.subst h (C c : ℂ_[q]⟦X⟧) : ℂ_[q]⟦X⟧) = C c := by
  rw [← Polynomial.coe_C, subst_coe hs, Polynomial.aeval_C]; simp

theorem constantCoeff_subst_eq {h : ℂ_[q]⟦X⟧} (hh0 : constantCoeff h = 0) (Q : ℂ_[q]⟦X⟧) :
    constantCoeff (PowerSeries.subst h Q : ℂ_[q]⟦X⟧) = constantCoeff Q := by
  have hs : HasSubst h := HasSubst.of_constantCoeff_zero' hh0
  obtain ⟨Q', hQ'⟩ : (X : ℂ_[q]⟦X⟧) ∣ Q - C (constantCoeff Q) := X_dvd_iff.2 (by simp)
  have : Q = C (constantCoeff Q) + X * Q' := by rw [← hQ']; ring
  conv_lhs => rw [this, subst_add hs, subst_mul hs, subst_X hs]
  rw [subst_C_eq hs]
  simp [hh0]

theorem exists_fac {f : ℂ_[q]⟦X⟧} (hf : f ≠ 0) :
    ∃ (n : ℕ) (Q : ℂ_[q]⟦X⟧), f = X ^ n * Q ∧ constantCoeff Q ≠ 0 :=
  ⟨f.order.toNat, divXPowOrder f, X_pow_order_mul_divXPowOrder.symm, by
    rw [Ne, constantCoeff_divXPowOrder_eq_zero_iff]; exact hf⟩

theorem const_of_funEq (e : ℂ_[q]⟦X⟧) (m : ℕ) (he0 : constantCoeff e = 0) (he1 : ‖coeff 1 e‖ = 1)
    (hm : ‖(m : ℂ_[q])‖ < 1) (h2 : 2 ≤ m) (ρ : ℂ_[q]⟦X⟧) (hρ : ρ ≠ 0) (h : ρ.subst e = ρ ^ m) :
    ∃ c : ℂ_[q], ρ = C c ∧ c ^ (m - 1) = 1 := by
  have hs : HasSubst e := HasSubst.of_constantCoeff_zero' he0
  obtain ⟨e', he'⟩ : (X : ℂ_[q]⟦X⟧) ∣ e := X_dvd_iff.2 he0
  have h'0 : constantCoeff e' = coeff 1 e := by
    rw [he', coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  have ha : coeff 1 e ≠ 0 := by
    intro h0; rw [h0, norm_zero] at he1; exact zero_ne_one he1
  have hsub : ∀ (n : ℕ) (Q : ℂ_[q]⟦X⟧), (PowerSeries.subst e (X ^ n * Q : ℂ_[q]⟦X⟧) : ℂ_[q]⟦X⟧)
      = X ^ n * (e' ^ n * PowerSeries.subst e Q) := by
    intro n Q
    rw [subst_mul hs, subst_pow hs, subst_X hs]
    have : e ^ n = X ^ n * e' ^ n := by rw [he', mul_pow]
    rw [this]; ring
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hc : constantCoeff ρ ≠ 0 := by
    obtain ⟨n, Q, rfl, hQ⟩ := exists_fac hρ
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using hQ
    exfalso
    rw [hsub] at h
    have h3 : e' ^ n * PowerSeries.subst e Q = X ^ n * (Q * Q * (X ^ n * Q) ^ k) := by
      apply mul_left_cancel₀ (pow_ne_zero n (X_ne_zero (R := ℂ_[q])))
      rw [h]; ring
    have h4 := congrArg constantCoeff h3
    rw [map_mul, map_mul, map_pow, map_pow, constantCoeff_X, zero_pow hn.ne', zero_mul, h'0,
      constantCoeff_subst_eq he0] at h4
    exact mul_ne_zero (pow_ne_zero _ ha) hQ h4
  set c := constantCoeff ρ with hcd
  have hc1 : c ^ (k + 1) = 1 := by
    have h4 := congrArg constantCoeff h
    rw [constantCoeff_subst_eq he0, map_pow, ← hcd] at h4
    apply mul_left_cancel₀ hc
    rw [mul_one]
    linear_combination -h4
  refine ⟨c, ?_, hc1⟩
  by_contra hne
  obtain ⟨n, Q, hf, hQ⟩ := exists_fac (sub_ne_zero.2 hne)
  have hn : n ≠ 0 := by
    rintro rfl
    apply hQ
    rw [pow_zero, one_mul] at hf
    rw [← hf, map_sub, constantCoeff_C, ← hcd, sub_self]
  have hL : (PowerSeries.subst e ρ : ℂ_[q]⟦X⟧) = C c + X ^ n * (e' ^ n * PowerSeries.subst e Q) := by
    have : ρ = C c + X ^ n * Q := by rw [← hf]; ring
    conv_lhs => rw [this, subst_add hs, hsub, subst_C_eq hs]
  have hR : ρ ^ (k + 2) = C c +
      X ^ n * (Q * (∑ i ∈ Finset.range (k + 2), ρ ^ i * (C c : ℂ_[q]⟦X⟧) ^ (k + 2 - 1 - i))) := by
    have := geom_sum₂_mul ρ (C c : ℂ_[q]⟦X⟧) (k + 2)
    rw [hf] at this
    have h5 : (C c : ℂ_[q]⟦X⟧) ^ (k + 2) = C c := by
      rw [← map_pow, pow_succ, hc1, one_mul]
    rw [h5] at this
    linear_combination -this
  rw [hL, hR] at h
  have h3 := mul_left_cancel₀ (pow_ne_zero n (X_ne_zero (R := ℂ_[q]))) (add_left_cancel h)
  have h4 := congrArg constantCoeff h3
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, map_mul, map_pow, h'0, constantCoeff_subst_eq he0, map_sum,
    Finset.sum_congr rfl (g := fun _ => (1 : ℂ_[q])), Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one, mul_comm] at h4
  · have h5 := congrArg norm (mul_left_cancel₀ hQ h4)
    rw [norm_pow, he1, one_pow] at h5
    exact hm.ne' h5
  · intro i hi
    rw [Finset.mem_range] at hi
    rw [map_mul, map_pow, map_pow, constantCoeff_C, ← hcd, ← pow_add, ← hc1]
    congr 1; omega

theorem funEq_unique : ∀ (q : ℕ) [Fact q.Prime] (e : ℂ_[q]⟦X⟧) (m : ℕ), constantCoeff e = 0 → ‖coeff 1 e‖ = 1 → ‖(m : ℂ_[q])‖ < 1 → 2 ≤ m → (∀ ρ : ℂ_[q]⟦X⟧, ρ ≠ 0 → ρ.subst e = ρ ^ m → ∃ c : ℂ_[q], ρ = C c ∧ c ^ (m - 1) = 1) ∧ ∀ g ε : ℂ_[q]⟦X⟧, Bd 1 e → Bd 1 ε → constantCoeff g = 1 → g.subst e = g ^ m * ε → Bd 1 g := by
  intro q _ e m he0 he1 hm h2
  refine ⟨const_of_funEq e m he0 he1 hm h2, fun g ε he hε hg h => ?_⟩
  have hε0 : constantCoeff ε = 1 := by
    have h4 := congrArg constantCoeff h
    rw [constantCoeff_subst_eq he0, map_mul, map_pow, hg, one_pow, one_mul] at h4
    exact h4.symm
  have h1 : Bd 1 (1 : ℂ_[q]⟦X⟧) := by simpa using intSer_C (q := q) (c := 1) (by simp)
  exact intSer_of_funEq g e 1 ε m hg he he0 he1 hm h1 (by simp) hε hε0 (by rw [mul_one, h])

end GlobalTheory.MomOne.FeUniq
end
