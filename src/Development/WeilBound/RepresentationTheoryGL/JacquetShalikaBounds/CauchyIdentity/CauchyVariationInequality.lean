module

public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.ProductCoefficients.ElementaryRelationOfGenerating
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.StaircaseDeterminants.AlternatingJacobiTrudiOfRelation
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.PaddingMonotonicity.CauchyLocalOfCauchy

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.BetaGenerators.BetaGeneratingOfSumBound
noncomputable section

open Finset Matrix Filter Topology GroundTheory.Automorphic GroundTheory.Automorphic.Spherical

namespace PositivityTheory.RgJS

namespace BetaGeneratingBounds

variable {m k : ℕ}

theorem hZ_neg' (α : Fin m → ℂ) {z : ℤ} (hz : z < 0) : hZ z α = 0 := by
  simp [hZ, hz]

theorem hZ_nat (α : Fin m → ℂ) (p : ℕ) : hZ (p : ℤ) α = hN p α := by
  simp [hZ]

def cE (α : Fin m → ℂ) (X : ℂ) (k : ℕ) (n : ℕ) (c : Fin k) : ℂ :=
  hZ ((n : ℤ) - (stair k c : ℕ)) α * X ^ (n - stair k c)

def ML (α : Fin m → ℂ) (b : Fin k → ℂ) (X : ℂ) (L : ℕ) : Matrix (Fin k) (Fin k) ℂ :=
  Matrix.of fun i c => ∑ n ∈ range L, b i ^ n * cE α X k n c

def KL (k L : ℕ) : Finset (Fin k → ℕ) := (Fintype.piFinset fun _ => range L).filter fun l => ∀ t, l t + stair k t < L

def gF (α : Fin m → ℂ) (b : Fin k → ℂ) (X : ℂ) (l : Fin k → ℕ) : ℂ :=
  if Antitone l then jt α l * jt b l * X ^ (∑ j, l j) else 0

theorem stair_lt (t : Fin k) : stair k t < k := by
  unfold stair; omega

theorem stair_int (t : Fin k) : ((stair k t : ℕ) : ℤ) = (k : ℤ) - 1 - t := by
  unfold stair; have := t.2; omega

theorem detC (α : Fin m → ℂ) (X : ℂ) (l : Fin k → ℕ) :
    (Matrix.of fun t c : Fin k => cE α X k (l t + stair k t) c).det = X ^ (∑ j, l j) * jt α l := by
  rw [← det_transpose, jt, det_apply, det_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_comm (X ^ _), smul_mul_assoc]
  congr 1
  simp only [transpose_apply, of_apply, cE]
  by_cases h : ∀ i, 0 ≤ (l i : ℤ) - i + σ i
  · have he : ∀ i : Fin k, (l i + stair k i - stair k (σ i)) = ((l i : ℤ) - i + σ i).toNat := by
      intro i
      have h1 := stair_int i
      have h2 := stair_int (σ i)
      have hi := h i
      omega
    have hz : ∀ i : Fin k, ((l i + stair k i : ℕ) : ℤ) - (stair k (σ i) : ℕ) = (l i : ℤ) - i + σ i := by
      intro i
      have h1 := stair_int i
      have h2 := stair_int (σ i)
      push_cast
      omega
    simp only [hz, he, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    have hs : ∑ i : Fin k, ((l i : ℤ) - i + σ i).toNat = ∑ i, l i := by
      have h3 : ∀ i : Fin k, (((l i : ℤ) - i + σ i).toNat : ℤ) = (l i : ℤ) - i + σ i := fun i => Int.toNat_of_nonneg (h i)
      have h4 : ((∑ i : Fin k, ((l i : ℤ) - i + σ i).toNat : ℕ) : ℤ) = ∑ i : Fin k, (l i : ℤ) := by
        push_cast
        simp only [h3, Finset.sum_add_distrib, Finset.sum_sub_distrib]
        have h5 : ∑ i : Fin k, ((σ i : ℕ) : ℤ) = ∑ i : Fin k, ((i : ℕ) : ℤ) :=
          Equiv.sum_comp σ (fun i : Fin k => ((i : ℕ) : ℤ))
        rw [h5]; ring
      exact_mod_cast h4
    rw [hs]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have hz : ((l i + stair k i : ℕ) : ℤ) - (stair k (σ i) : ℕ) = (l i : ℤ) - i + σ i := by
      have h1 := stair_int i
      have h2 := stair_int (σ i)
      push_cast
      omega
    have h0 : ∏ x : Fin k, hZ ((l x : ℤ) - x + σ x) α = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (hZ_neg' α hi)
    have h0' : ∏ x : Fin k, hZ (((l x + stair k x : ℕ) : ℤ) - (stair k (σ x) : ℕ)) α * X ^ (l x + stair k x - stair k (σ x)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hz, hZ_neg' α hi, zero_mul])
    rw [h0', h0, zero_mul]

theorem ML_eq (α : Fin m → ℂ) (b : Fin k → ℂ) (X : ℂ) (L : ℕ) :
    ML α b X L = (Matrix.of fun i (n : Fin L) => b i ^ (n : ℕ)) * (Matrix.of fun (n : Fin L) c => cE α X k n c) := by
  ext i c
  simp only [ML, of_apply, Matrix.mul_apply]
  exact (Fin.sum_univ_eq_sum_range (fun n => b i ^ n * cE α X k n c) L).symm

theorem gap {f : Fin k → ℕ} (hf : StrictMono f) : ∀ (d : ℕ) (s t : Fin k), (t : ℕ) = s + d → f s + d ≤ f t := by
  intro d
  induction d with
  | zero =>
    intro s t h
    have : s = t := Fin.ext (by omega)
    subst this; simp
  | succ d ih =>
    intro s t h
    have h1 := ih s ⟨s + d, by omega⟩ rfl
    have h2 : f ⟨s + d, by omega⟩ < f t := hf (Fin.lt_def.2 (by simp only; omega))
    omega

theorem cb_facts {L : ℕ} (C : Fin k → Fin L) (hC : StrictMono fun t => L - 1 - (C t : ℕ)) :
    (∀ t, stair k t ≤ C t) ∧ Antitone fun t => (C t : ℕ) - stair k t := by
  have hlast : ∀ t : Fin k, stair k t ≤ C t := by
    intro t
    have hk : k - 1 < k := by have := t.2; omega
    have h := gap hC (k - 1 - t) t ⟨k - 1, hk⟩ (by simp only; omega)
    have h1 := (C t).2
    have h2 := (C ⟨k - 1, hk⟩).2
    unfold stair
    omega
  refine ⟨hlast, fun s t hst => ?_⟩
  have h := gap hC ((t : ℕ) - s) s t (by have := Fin.le_def.1 hst; omega)
  have h1 := (C t).2
  have h2 := (C s).2
  have h3 := hlast s
  have h4 := hlast t
  have h5 := Fin.le_def.1 hst
  unfold stair at *
  simp only at h ⊢
  omega

theorem finite_id (hA : AltJT) (α : Fin m → ℂ) (b : Fin k → ℂ) (X : ℂ) (L : ℕ) :
    (ML α b X L).det = altN b (stair k) * ∑ l ∈ KL k L, gF α b X l := by
  classical
  rw [ML_eq, AAInvW.cauchyBinet (fun n : Fin L => L - 1 - (n : ℕ)) (by
    intro x y h
    have := x.2; have := y.2
    exact Fin.ext (by simp only at h; omega))]
  rw [← Finset.sum_filter]
  unfold gF
  rw [← Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_bij' (fun C _ => fun t => (C t : ℕ) - stair k t)
    (fun l hl => fun t => (⟨l t + stair k t, ((Finset.mem_filter.1 (Finset.mem_filter.1 hl).1).2 t)⟩ : Fin L))
    ?_ ?_ ?_ ?_ ?_
  · intro C hC
    have hC' := (Finset.mem_filter.1 hC).2
    obtain ⟨h1, h2⟩ := cb_facts C hC'
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun t => ?_, fun t => ?_⟩, h2⟩
    · have := (C t).2; exact Finset.mem_range.2 (by omega)
    · show (C t : ℕ) - stair k t + stair k t < L
      have := (C t).2; have := h1 t; omega
  · intro l hl
    obtain ⟨hl1, hl2⟩ := Finset.mem_filter.1 hl
    obtain ⟨-, hl3⟩ := Finset.mem_filter.1 hl1
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun s t hst => ?_⟩
    have h1 := hl2 (le_of_lt hst)
    have h2 := hl3 s
    have h3 := hl3 t
    have h4 := Fin.lt_def.1 hst
    simp only
    unfold stair at *
    omega
  · intro C hC
    obtain ⟨h1, -⟩ := cb_facts C (Finset.mem_filter.1 hC).2
    funext t
    exact Fin.ext (by simp only; have := h1 t; omega)
  · intro l hl
    funext t
    simp
  · intro C hC
    obtain ⟨h1, -⟩ := cb_facts C (Finset.mem_filter.1 hC).2
    set l : Fin k → ℕ := fun t => (C t : ℕ) - stair k t with hl
    have hCl : ∀ t, (C t : ℕ) = l t + stair k t := fun t => by simp only [hl]; have := h1 t; omega
    have eA : (Matrix.of fun a t => (Matrix.of fun i (n : Fin L) => b i ^ (n : ℕ)) a (C t)) =
        Matrix.of fun i j => b i ^ (l + stair k) j := by
      ext i j; simp only [of_apply, Pi.add_apply, hCl]
    have eB : (Matrix.of fun i t => (Matrix.of fun (n : Fin L) c => cE α X k n c) (C i) t) =
        Matrix.of fun t c : Fin k => cE α X k (l t + stair k t) c := by
      ext i j; simp only [of_apply, hCl]
    rw [eA, eB, detC]
    have hAl := hA k b l
    simp only [altN] at hAl ⊢
    rw [hAl]
    ring

theorem KL_mono : Monotone (KL k) := by
  intro L L' h l hl
  obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hl
  refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun t => ?_, fun t => by have := h2 t; omega⟩
  have := Finset.mem_range.1 (Fintype.mem_piFinset.1 h1 t)
  exact Finset.mem_range.2 (by omega)

theorem KL_exh (l : Fin k → ℕ) : ∃ L, l ∈ KL k L := by
  refine ⟨∑ t, l t + k + 1, Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun t => ?_, fun t => ?_⟩⟩
  · have := Finset.single_le_sum (f := l) (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
    exact Finset.mem_range.2 (by omega)
  · have := Finset.single_le_sum (f := l) (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
    have := stair_lt t
    omega

theorem entry_lim (α : Fin m → ℂ) (b : Fin k → ℂ) (X : ℂ) (i c : Fin k) {H : ℂ}
    (hH : HasSum (fun p => hN p α * (b i * X) ^ p) H) :
    Tendsto (fun L => ML α b X L i c) atTop (𝓝 (H * b i ^ stair k c)) := by
  set s := stair k c with hs
  have e : ∀ L, s ≤ L → ML α b X L i c = (∑ p ∈ range (L - s), hN p α * (b i * X) ^ p) * b i ^ s := by
    intro L hL
    simp only [ML, of_apply]
    rw [show L = s + (L - s) by omega, Finset.sum_range_add, Nat.add_sub_cancel_left]
    have h0 : ∑ n ∈ range s, b i ^ n * cE α X k n c = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      have := Finset.mem_range.1 hn
      rw [cE, hZ_neg' α (by rw [← hs]; omega), zero_mul, mul_zero]
    rw [h0, zero_add, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [cE, ← hs, show ((s + p : ℕ) : ℤ) - (s : ℕ) = (p : ℤ) by push_cast; ring, hZ_nat,
      show s + p - s = p by omega, pow_add, mul_pow]
    ring
  have h1 : Tendsto (fun L => (∑ p ∈ range (L - s), hN p α * (b i * X) ^ p) * b i ^ s) atTop (𝓝 (H * b i ^ s)) :=
    ((hH.tendsto_sum_nat).comp (tendsto_sub_atTop_nat s)).mul_const _
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop s] with L hL
  exact (e L hL).symm

theorem altN_ne {b : Fin k → ℂ} (hb : Function.Injective b) : altN b (stair k) ≠ 0 := by
  have e : (Matrix.of fun i j => b i ^ stair k j) = (Matrix.vandermonde b).submatrix id Fin.revPerm := by
    ext i j
    simp only [of_apply, submatrix_apply, id_eq, Matrix.vandermonde_apply, Fin.revPerm_apply, Fin.val_rev, stair]
    congr 1
    omega
  simp only [altN]
  rw [e, det_permute']
  exact mul_ne_zero (by simp) (Matrix.det_vandermonde_ne_zero_iff.2 hb)

end BetaGeneratingBounds

open BetaGeneratingBounds in
theorem beta_generating_of_sum_bound : HGen → SumBd → SchurJT → BetaGen := by
  intro hG hS hJ m k α β X A B hA hB hα hβ hX hd
  have hAlt : AltJT := alternating_jacobi_trudi_of_relation (elementary_relation_of_generating hG)
  set b : Fin k → ℂ := fun j => (β j : ℂ) with hb
  have hbinj : Function.Injective b := fun j j' h => by
    by_contra hne
    exact hd hne h
  have hterm : ∀ l : {l : Fin k → ℕ // Antitone l},
      jt α l.1 * evalAt β (schur fun j => (l.1 j : ℤ)) * X ^ (∑ j, l.1 j) = gF α b X l.1 := by
    intro l
    rw [gF, if_pos l.2, hJ k β l.1]
  obtain ⟨hsum, hbdα⟩ := hS m k A B ‖X‖ hA hB (norm_nonneg _) hX
  have hbdβ := (hS k k B B 0 hB hB le_rfl (by simp)).2 b hβ
  have hsumF : Summable (fun l : {l : Fin k → ℕ // Antitone l} => gF α b X l.1) := by
    refine Summable.of_norm_bounded hsum fun l => ?_
    rw [gF, if_pos l.2, norm_mul, norm_mul, norm_pow]
    have h1 := hbdα α hα l.1
    have h2 := hbdβ l.1
    have h0 : 0 ≤ cjt m A l.1 := (norm_nonneg _).trans h1
    have h0' : 0 ≤ cjt k B l.1 := (norm_nonneg _).trans h2
    gcongr
  have hind : {l : Fin k → ℕ | Antitone l}.indicator (gF α b X) = gF α b X := by
    funext l
    by_cases h : Antitone l
    · simp [Set.indicator, h]
    · simp [Set.indicator, h, gF]
  have hsumAll : Summable (gF α b X) := by
    rw [← hind, ← summable_subtype_iff_indicator]
    exact hsumF
  set Hs : Fin k → ℂ := fun i => ∏ a, (1 - α a * (b i * X))⁻¹ with hHs
  have hH : ∀ i, HasSum (fun p => hN p α * (b i * X) ^ p) (Hs i) := by
    intro i
    refine (hG m α (b i * X) A hA.le hα ?_).1
    rw [norm_mul]
    have h1 : ‖b i‖ ≤ B := hβ i
    calc A * (‖b i‖ * ‖X‖) ≤ A * (B * ‖X‖) := by gcongr
      _ = ‖X‖ * A * B := by ring
      _ < 1 := hX
  have hlimM : Tendsto (fun L => ML α b X L) atTop (𝓝 (Matrix.of fun i c => Hs i * b i ^ stair k c)) :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun c => entry_lim α b X i c (hH i)
  have hlim1 : Tendsto (fun L => (ML α b X L).det) atTop (𝓝 (Matrix.of fun i c => Hs i * b i ^ stair k c).det) :=
    ((continuous_id.matrix_det).tendsto _).comp hlimM
  have hdet : (Matrix.of fun i c => Hs i * b i ^ stair k c).det = (∏ i, Hs i) * altN b (stair k) := by
    have := det_mul_column Hs (Matrix.of fun i c => b i ^ stair k c)
    simp only [of_apply] at this
    rw [this]
    rfl
  rw [hdet] at hlim1
  have hlim2 : Tendsto (fun L => altN b (stair k) * ∑ l ∈ KL k L, gF α b X l) atTop
      (𝓝 (altN b (stair k) * ∑' l, gF α b X l)) :=
    (hsumAll.hasSum.comp (tendsto_atTop_finset_of_monotone KL_mono KL_exh)).const_mul _
  have hlim1' : Tendsto (fun L => altN b (stair k) * ∑ l ∈ KL k L, gF α b X l) atTop
      (𝓝 ((∏ i, Hs i) * altN b (stair k))) := by
    refine hlim1.congr fun L => ?_
    exact finite_id hAlt α b X L
  have heq := tendsto_nhds_unique hlim2 hlim1'
  have htsum : ∑' l, gF α b X l = ∏ i, Hs i := by
    have hne := altN_ne hbinj
    apply mul_left_cancel₀ hne
    rw [heq, mul_comm]
  have hall : HasSum (gF α b X) (∏ i, Hs i) := htsum ▸ hsumAll.hasSum
  rw [← hind] at hall
  have hsub : HasSum (fun l : {l : Fin k → ℕ // Antitone l} => gF α b X l.1) (∏ i, Hs i) :=
    (hasSum_subtype_iff_indicator).2 hall
  have e2 : (∏ i, Hs i) = ∏ i, ∏ j, (1 - α i * β j * X)⁻¹ := by
    simp only [hHs, hb]
    rw [Finset.prod_comm]
    simp only [mul_assoc]
  rw [← e2]
  convert hsub using 1
  funext l
  exact hterm l

end PositivityTheory.RgJS
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.JacobiTrudiPadding.JacobiTrudiPadding
open Finset Matrix

namespace PositivityTheory.RgJS

namespace JacobiTrudiPadding

theorem hZ_zero {m : ℕ} (α : Fin m → ℂ) : hZ 0 α = 1 := by
  simp [hZ, hN, Finset.Nat.antidiagonalTuple_zero_right]

theorem hZ_neg {m : ℕ} (α : Fin m → ℂ) {z : ℤ} (hz : z < 0) : hZ z α = 0 := by
  simp [hZ, hz]

theorem det_unitri {m d : ℕ} (α : Fin m → ℂ) : (Matrix.of fun i j : Fin d => hZ ((i : ℤ) - j) α).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [hZ_zero]
  · intro i j hij
    simp only [Matrix.of_apply]
    apply hZ_neg
    have : (i : ℕ) < j := hij
    omega

theorem jt_pad_add (m' d : ℕ) (α : Fin (m' + d) → ℂ) (l : Fin m' → ℕ) :
    jt α (padN (m' + d) l) = jt α l := by
  unfold jt
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv]
  rw [← Matrix.fromBlocks_toBlocks (Matrix.submatrix _ finSumFinEquiv finSumFinEquiv)]
  rw [show Matrix.toBlocks₁₂ (Matrix.submatrix _ finSumFinEquiv finSumFinEquiv) = 0 from ?_]
  · rw [Matrix.det_fromBlocks_zero₁₂]
    have h11 : Matrix.toBlocks₁₁ ((of fun (i j : Fin (m' + d)) => hZ (↑(padN (m' + d) l j) - ↑↑j + ↑↑i) α).submatrix
        finSumFinEquiv finSumFinEquiv) = of fun (i j : Fin m') => hZ (↑(l j) - ↑↑j + ↑↑i) α := by
      ext i j
      simp [Matrix.toBlocks₁₁, padN]
    have h22 : Matrix.toBlocks₂₂ ((of fun (i j : Fin (m' + d)) => hZ (↑(padN (m' + d) l j) - ↑↑j + ↑↑i) α).submatrix
        finSumFinEquiv finSumFinEquiv) = of fun (i j : Fin d) => hZ ((i : ℤ) - j) α := by
      ext i j
      simp [Matrix.toBlocks₂₂, padN]
      congr 1
      ring
    rw [h11, h22, det_unitri, mul_one]
  · ext i j
    simp [Matrix.toBlocks₁₂, padN]
    apply hZ_neg
    have := i.isLt
    omega

end JacobiTrudiPadding

theorem jacobi_trudi_padding : JTPad := by
  intro m m' hm α l
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  exact JacobiTrudiPadding.jt_pad_add m' d α l

end PositivityTheory.RgJS
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.HGenerators.CompleteHomogeneousGenerating
noncomputable section

open Finset

namespace PositivityTheory.RgJS

namespace completeHomogeneousGenerating

private theorem summable_norm_mul_and_hasSum_mul_tsum {ι : Type} (a : ℕ → ℂ) (b : ι → ℂ) (ha : Summable fun k => ‖a k‖)
    (hb : Summable fun k => ‖b k‖) :
    Summable (fun x : ℕ × ι => ‖a x.1 * b x.2‖) ∧
      HasSum (fun x : ℕ × ι => a x.1 * b x.2) ((∑' k, a k) * ∑' k, b k) := by
  refine ⟨?_, ?_⟩
  · refine (Summable.mul_of_nonneg ha hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).congr
      fun x => ?_
    exact (norm_mul _ _).symm
  · rw [tsum_mul_tsum_of_summable_norm ha hb]
    exact (summable_mul_of_summable_norm ha hb).hasSum

theorem pi_hasSum (m : ℕ) : ∀ (f : Fin m → ℕ → ℂ), (∀ i, Summable (fun n => ‖f i n‖)) →
    Summable (fun k : Fin m → ℕ => ‖∏ i, f i (k i)‖) ∧ HasSum (fun k : Fin m → ℕ => ∏ i, f i (k i)) (∏ i, ∑' n, f i n) := by
  induction m with
  | zero =>
    intro f _
    refine ⟨Summable.of_finite, ?_⟩
    simpa using (hasSum_fintype (fun k : Fin 0 → ℕ => ∏ i, f i (k i)))
  | succ n ih =>
    intro f hf
    obtain ⟨hs1, hh1⟩ := ih (fun i => f i.succ) (fun i => hf i.succ)
    obtain ⟨hN2, hH2⟩ := summable_norm_mul_and_hasSum_mul_tsum (f 0) (fun k : Fin n → ℕ => ∏ i, f i.succ (k i)) (hf 0)
      (hs1.congr fun _ => rfl)
    rw [hh1.tsum_eq] at hH2
    let e : ℕ × (Fin n → ℕ) ≃ (Fin (n + 1) → ℕ) := Fin.consEquiv (fun _ => ℕ)
    have hcomp : ∀ x : ℕ × (Fin n → ℕ),
        ∏ i, f i (e x i) = f 0 x.1 * ∏ i : Fin n, f i.succ (x.2 i) := by
      intro x
      rw [Fin.prod_univ_succ]
      simp [e, Fin.consEquiv]
    constructor
    · rw [← e.summable_iff]
      refine hN2.congr fun x => ?_
      simp only [Function.comp_apply]
      rw [hcomp]
    · rw [← e.hasSum_iff]
      have hfun : ((fun k : Fin (n + 1) → ℕ => ∏ i, f i (k i)) ∘ e) =
          fun x => f 0 x.1 * ∏ i : Fin n, f i.succ (x.2 i) := funext hcomp
      rw [hfun, Fin.prod_univ_succ]
      exact hH2

theorem card_le (m p : ℕ) : ((Finset.Nat.antidiagonalTuple m p).card : ℝ) ≤ ((p + 1 : ℕ) : ℝ) ^ m := by
  have hsub : Finset.Nat.antidiagonalTuple m p ⊆ Fintype.piFinset (fun _ : Fin m => Finset.range (p + 1)) := by
    intro k hk
    rw [Finset.Nat.mem_antidiagonalTuple] at hk
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range, Nat.lt_succ_iff, ← hk]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i)
  have h := Finset.card_le_card hsub
  rw [Fintype.card_piFinset] at h
  simp only [Finset.card_range, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  exact_mod_cast h

theorem term_eq (m : ℕ) (α : Fin m → ℂ) (u : ℂ) (p : ℕ) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple m p, ∏ i, (α i * u) ^ k i = hN p α * u ^ p := by
  unfold hN
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.Nat.mem_antidiagonalTuple] at hk
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hk]

end completeHomogeneousGenerating

open completeHomogeneousGenerating in
theorem complete_homogeneous_generating : HGen := by
  intro m α u A hA hα hAu
  have hr : ∀ i, ‖α i * u‖ < 1 := fun i => by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (hα i) (norm_nonneg u)) hAu
  refine ⟨?_, fun p => ?_⟩
  · obtain ⟨-, hH⟩ := pi_hasSum m (fun i n => (α i * u) ^ n) (fun i => by
      simpa only [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) (hr i))
    have hprod : (∏ i, ∑' n, (α i * u) ^ n) = ∏ i, (1 - α i * u)⁻¹ :=
      Finset.prod_congr rfl fun i _ => tsum_geometric_of_norm_lt_one (hr i)
    rw [hprod] at hH
    have hF := hH.tsum_fiberwise (fun k : Fin m → ℕ => ∑ i, k i)
    have hset : ∀ c : ℕ, ((fun k : Fin m → ℕ => ∑ i, k i) ⁻¹' {c}) =
        ↑(Finset.Nat.antidiagonalTuple m c) := by
      intro c
      ext k
      simp [Finset.Nat.mem_antidiagonalTuple]
    have hfun : (fun c : ℕ => hN c α * u ^ c) = fun c =>
        ∑' b : ↑((fun k : Fin m → ℕ => ∑ i, k i) ⁻¹' {c}), ∏ i, (α i * u) ^ (b : Fin m → ℕ) i := by
      funext c
      rw [hset c]
      exact ((Finset.tsum_subtype' _ (fun k : Fin m → ℕ => ∏ i, (α i * u) ^ k i)).trans
        (term_eq m α u c)).symm
    rw [hfun]
    exact hF
  · have hterm : ∀ k ∈ Finset.Nat.antidiagonalTuple m p, ‖∏ i, α i ^ k i‖ ≤ A ^ p := by
      intro k hk
      rw [Finset.Nat.mem_antidiagonalTuple] at hk
      rw [norm_prod, ← hk, ← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hα i) _
    calc ‖hN p α‖ ≤ ∑ k ∈ Finset.Nat.antidiagonalTuple m p, ‖∏ i, α i ^ k i‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.Nat.antidiagonalTuple m p, A ^ p := Finset.sum_le_sum hterm
      _ = ((Finset.Nat.antidiagonalTuple m p).card : ℝ) * A ^ p := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((p + 1 : ℕ) : ℝ) ^ m * A ^ p :=
        mul_le_mul_of_nonneg_right (card_le m p) (pow_nonneg hA _)

end PositivityTheory.RgJS
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.PolynomialGeometricSums.HomogeneousSumBound
noncomputable section

open Finset

namespace PositivityTheory.RgJS

namespace HomogeneousSumBound

theorem pow_le (A : ℝ) (hA : 0 < A) (p l k : ℕ) (h1 : p ≤ l + k) (h2 : l ≤ p + k) :
    A ^ p ≤ A ^ l * max A A⁻¹ ^ k := by
  set M := max A A⁻¹ with hM
  have hM1 : 1 ≤ M := by
    rcases le_total 1 A with h | h
    · exact h.trans (le_max_left _ _)
    · exact ((one_le_inv₀ hA).2 h).trans (le_max_right _ _)
  have hAM : A ≤ M := le_max_left _ _
  have hAiM : A⁻¹ ≤ M := le_max_right _ _
  have hl : 0 ≤ A ^ l := by positivity
  rcases le_total l p with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [pow_add]
    refine mul_le_mul_of_nonneg_left ?_ hl
    calc A ^ d ≤ M ^ d := pow_le_pow_left₀ hA.le hAM d
      _ ≤ M ^ k := pow_le_pow_right₀ hM1 (by omega)
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have e : A ^ p = A ^ (p + d) * A⁻¹ ^ d := by
      rw [pow_add, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hA.ne'), mul_one]
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc A⁻¹ ^ d ≤ M ^ d := pow_le_pow_left₀ (by positivity) hAiM d
      _ ≤ M ^ k := pow_le_pow_right₀ hM1 (by omega)

theorem entry_le (hG : HGen) {m m' : ℕ} (α : Fin m → ℂ) (A : ℝ) (hA : 0 < A) (hα : ∀ i, ‖α i‖ ≤ A)
    (l : Fin m' → ℕ) (i j : Fin m') :
    ‖hZ ((l j : ℤ) - j + i) α‖ ≤ ((l j + m' + 1 : ℕ) : ℝ) ^ m * A ^ l j * max A A⁻¹ ^ m' := by
  have hb := (hG m α 0 A hA.le hα (by simp)).2
  have hM : 0 ≤ max A A⁻¹ := le_trans hA.le (le_max_left _ _)
  unfold hZ
  split_ifs with hz
  · rw [norm_zero]; positivity
  · push Not at hz
    set p := ((l j : ℤ) - j + i).toNat with hp
    have hpz : (p : ℤ) = (l j : ℤ) - j + i := Int.toNat_of_nonneg hz
    have hi := i.2
    have hj := j.2
    have e1 : p ≤ l j + m' := by omega
    have e2 : l j ≤ p + m' := by omega
    refine (hb p).trans ?_
    rw [mul_assoc]
    refine mul_le_mul ?_ (pow_le A hA p (l j) m' e1 e2) (by positivity) (by positivity)
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast (by omega : p + 1 ≤ l j + m' + 1)) m

theorem jt_le (hG : HGen) {m m' : ℕ} (α : Fin m → ℂ) (A : ℝ) (hA : 0 < A) (hα : ∀ i, ‖α i‖ ≤ A)
    (l : Fin m' → ℕ) : ‖jt α l‖ ≤ cjt m A l := by
  unfold jt cjt
  rw [Matrix.det_apply]
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ σ : Equiv.Perm (Fin m'), ‖(Equiv.Perm.sign σ) • ∏ i, (Matrix.of fun i j : Fin m' =>
      hZ ((l j : ℤ) - j + i) α) (σ i) i‖ ≤
      ∏ j, (((l j + m' + 1 : ℕ) : ℝ) ^ m * A ^ l j * max A A⁻¹ ^ m') := by
    intro σ
    rw [Units.smul_def, zsmul_eq_mul, norm_mul, norm_prod]
    have hs : ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    rw [hs, one_mul]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => by
      simpa [Matrix.of_apply] using entry_le hG α A hA hα l (σ i) i
  refine (Finset.sum_le_sum fun σ _ => h1 σ).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

theorem summable_pi (g : ℕ → ℝ) (hg0 : ∀ k, 0 ≤ g k) (hg : Summable g) :
    ∀ k : ℕ, Summable fun l : Fin k → ℕ => ∏ j, g (l j)
  | 0 => Summable.of_finite
  | k + 1 => by
      have ih := summable_pi g hg0 hg k
      have hprod : Summable fun p : ℕ × (Fin k → ℕ) => g p.1 * ∏ j, g (p.2 j) := by
        refine summable_mul_of_summable_norm (f := g) (g := fun l : Fin k → ℕ => ∏ j, g (l j)) ?_ ?_
        · exact hg.congr fun k => (Real.norm_of_nonneg (hg0 k)).symm
        · exact ih.congr fun l => (Real.norm_of_nonneg (Finset.prod_nonneg fun j _ => hg0 _)).symm
      refine (Fin.consEquiv (fun _ : Fin (k + 1) => ℕ)).summable_iff.1 (hprod.congr fun p => ?_)
      simp [Fin.consEquiv, Fin.prod_univ_succ]

theorem summable_poly_geom (c N : ℕ) (r : ℝ) (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable fun k : ℕ => ((k + c + 1 : ℕ) : ℝ) ^ N * r ^ k := by
  have h1 : Summable fun k : ℕ => ((k : ℝ) ^ N * r ^ k) :=
    summable_pow_mul_geometric_of_norm_lt_one N (by rw [Real.norm_of_nonneg hr0]; exact hr)
  have h2 : Summable fun k : ℕ => r ^ k := summable_geometric_of_lt_one hr0 hr
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((h1.add h2).mul_left ((2 * ((c : ℝ) + 1)) ^ N))
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have e1 : ((k + c + 1 : ℕ) : ℝ) ≤ 2 * ((c : ℝ) + 1) * max (k : ℝ) 1 := by
    push_cast
    rcases le_total (k : ℝ) 1 with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith
  have e2 : max (k : ℝ) 1 ^ N ≤ (k : ℝ) ^ N + 1 := by
    rcases le_total (k : ℝ) 1 with h | h
    · rw [max_eq_right h, one_pow]; linarith [pow_nonneg hk N]
    · rw [max_eq_left h]; linarith
  calc ((k + c + 1 : ℕ) : ℝ) ^ N * r ^ k ≤ (2 * ((c : ℝ) + 1) * max (k : ℝ) 1) ^ N * r ^ k :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) e1 N) (by positivity)
    _ = (2 * ((c : ℝ) + 1)) ^ N * (max (k : ℝ) 1 ^ N * r ^ k) := by rw [mul_pow]; ring
    _ ≤ (2 * ((c : ℝ) + 1)) ^ N * ((k : ℝ) ^ N * r ^ k + r ^ k) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        nlinarith [pow_nonneg hr0 k]

end HomogeneousSumBound

open HomogeneousSumBound in
theorem homogeneous_sum_bound : HGen → SumBd := by
  intro hG m m' A B ρ hA hB hρ hρAB
  refine ⟨?_, fun α hα l => jt_le hG α A hA hα l⟩
  have hr0 : 0 ≤ ρ * A * B := by positivity
  have hMA0 : 0 ≤ max A A⁻¹ := le_trans hA.le (le_max_left _ _)
  have hMB0 : 0 ≤ max B B⁻¹ := le_trans hB.le (le_max_left _ _)
  have hg0 : ∀ k : ℕ, 0 ≤ ((k + m' + 1 : ℕ) : ℝ) ^ (m + m') * (ρ * A * B) ^ k *
      (max A A⁻¹ ^ m' * max B B⁻¹ ^ m') := fun k => by positivity
  have hgs : Summable fun k : ℕ => ((k + m' + 1 : ℕ) : ℝ) ^ (m + m') * (ρ * A * B) ^ k *
      (max A A⁻¹ ^ m' * max B B⁻¹ ^ m') := (summable_poly_geom m' (m + m') _ hr0 hρAB).mul_right _
  have hall := (summable_pi _ hg0 hgs m').mul_left (((m'.factorial : ℝ)) * (m'.factorial : ℝ))
  refine (hall.comp_injective Subtype.val_injective).congr fun l => ?_
  have key : ∀ j, ((l.1 j + m' + 1 : ℕ) : ℝ) ^ (m + m') * (ρ * A * B) ^ l.1 j *
      (max A A⁻¹ ^ m' * max B B⁻¹ ^ m') =
      (((l.1 j + m' + 1 : ℕ) : ℝ) ^ m * A ^ l.1 j * max A A⁻¹ ^ m') *
        (((l.1 j + m' + 1 : ℕ) : ℝ) ^ m' * B ^ l.1 j * max B B⁻¹ ^ m') * ρ ^ l.1 j := fun j => by
    rw [pow_add, mul_pow, mul_pow]; ring
  simp only [Function.comp_apply, cjt]
  rw [Finset.prod_congr rfl fun j _ => key j, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  ring

end PositivityTheory.RgJS
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.AlternantEvaluation.SchurJacobiTrudiOfAlternating
noncomputable section

open Finset GroundTheory.Automorphic GroundTheory.Automorphic.Spherical AddMonoidAlgebra

namespace PositivityTheory.RgJS

namespace SchurJacobiTrudiEvaluation

variable {m : ℕ}

def hL (m p : ℕ) : LaurentRing m := ∑ k ∈ Finset.Nat.antidiagonalTuple m p, monomial (fun i => (k i : ℤ))

def hLZ (m : ℕ) (z : ℤ) : LaurentRing m := if z < 0 then 0 else hL m z.toNat

def jL (m : ℕ) (l : Fin m → ℕ) : LaurentRing m := (Matrix.of fun i j : Fin m => hLZ m ((l j : ℤ) - j + i)).det

private theorem evalAt_monomial_eq_prod_zpow (z : Fin m → ℂˣ) (v : Fin m → ℤ) :
    evalAt z (monomial v) = ∏ i, ((z i : ℂ) ^ v i) := by
  rw [evalAt_apply]
  simp [monomialChar]

theorem evalAt_monomial_nat (z : Fin m → ℂˣ) (k : Fin m → ℕ) :
    evalAt z (monomial (fun i => (k i : ℤ))) = ∏ i, (z i : ℂ) ^ k i := by
  rw [evalAt_monomial_eq_prod_zpow]
  simp

theorem evalAt_hL (z : Fin m → ℂˣ) (p : ℕ) : evalAt z (hL m p) = hN p (fun i => (z i : ℂ)) := by
  unfold hL hN
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact evalAt_monomial_nat z k

theorem evalAt_hLZ (z : Fin m → ℂˣ) (w : ℤ) : evalAt z (hLZ m w) = hZ w (fun i => (z i : ℂ)) := by
  unfold hLZ hZ
  split_ifs
  · simp
  · exact evalAt_hL z _

theorem evalAt_jL (z : Fin m → ℂˣ) (l : Fin m → ℕ) : evalAt z (jL m l) = jt (fun i => (z i : ℂ)) l := by
  unfold jL jt
  rw [AlgHom.map_det]
  congr 1
  ext i j
  simp [evalAt_hLZ]

theorem evalAt_alternant_nat (z : Fin m → ℂˣ) (μ : Fin m → ℕ) :
    evalAt z (alternant fun i => (μ i : ℤ)) = altN (fun i => (z i : ℂ)) μ := by
  rw [alternant_eq_det, AlgHom.map_det]
  unfold altN
  congr 1
  ext a b
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  rw [evalAt_monomial_eq_prod_zpow, Fintype.prod_eq_single a]
  · simp
  · intro i hi
    simp [Pi.single_apply, hi]

theorem staircase_eq : staircase m = fun i => ((stair m i : ℕ) : ℤ) := by
  funext i
  simp only [staircase, stair]
  have := i.isLt
  omega

end SchurJacobiTrudiEvaluation

open SchurJacobiTrudiEvaluation in
theorem schur_jacobi_trudi_of_alternating : AltJT → SchurJT := by
  intro h m z l
  have key : alternant (staircase m) * schur (fun i => (l i : ℤ)) = alternant (staircase m) * jL m l := by
    rw [alternant_mul_schur]
    apply eq_of_forall_evalAt
    intro w
    rw [map_mul, evalAt_jL, staircase_eq]
    have e : (fun i => (l i : ℤ)) + (fun i => ((stair m i : ℕ) : ℤ)) = fun i => (((l + stair m) i : ℕ) : ℤ) := by
      funext i
      simp
    rw [e, evalAt_alternant_nat, evalAt_alternant_nat]
    exact h m _ l
  rw [mul_left_cancel₀ alternant_staircase_ne_zero key]
  exact evalAt_jL z l

end PositivityTheory.RgJS
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.ContinuityOfH.BetaAllOfGenerating
noncomputable section

open Finset Filter Topology GroundTheory.Automorphic GroundTheory.Automorphic.Spherical

namespace PositivityTheory.RgJS

namespace BetaAllContinuity

variable {m : ℕ}

theorem continuous_hN (p : ℕ) : Continuous fun α : Fin m → ℂ => hN p α := by
  unfold hN
  fun_prop

theorem continuous_hZ (z : ℤ) : Continuous fun α : Fin m → ℂ => hZ z α := by
  by_cases h : z < 0
  · simp only [hZ, if_pos h]
    exact continuous_const
  · simp only [hZ, if_neg h]
    exact continuous_hN _

theorem continuous_jt {m' : ℕ} (l : Fin m' → ℕ) : Continuous fun γ : Fin m → ℂ => jt γ l := by
  unfold jt
  refine Continuous.matrix_det ?_
  exact continuous_pi fun i => continuous_pi fun j => continuous_hZ _

end BetaAllContinuity

open BetaAllContinuity in
theorem beta_all_of_generating : BetaGen → SumBd → SchurJT → BetaAll := by
  intro hG hS hJ m m' α β X A B hA hB hα hβ hX
  unfold BetaGen at hG
  unfold SumBd at hS
  unfold SchurJT at hJ
  simp only [hJ] at hG ⊢
  obtain ⟨B', hBB', hX'⟩ : ∃ B', B < B' ∧ ‖X‖ * A * B' < 1 := by
    have hc : Filter.Tendsto (fun t : ℝ => ‖X‖ * A * t) (𝓝 B) (𝓝 (‖X‖ * A * B)) :=
      tendsto_const_nhds.mul tendsto_id
    have hev : ∀ᶠ t in 𝓝[>] B, ‖X‖ * A * t < 1 :=
      (hc.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hX)
    obtain ⟨t, ht1, ht2⟩ := (hev.and self_mem_nhdsWithin).exists
    exact ⟨t, ht2, ht1⟩
  have hB' : 0 < B' := hB.trans hBB'
  let γ : ℝ → Fin m' → ℂˣ := fun t j =>
    β j * Units.mk0 ((Real.exp (t * ((j : ℕ) : ℝ)) : ℝ) : ℂ) (by exact_mod_cast (Real.exp_pos _).ne')
  let c : ℝ → Fin m' → ℂ := fun t j => ((γ t j : ℂˣ) : ℂ)
  have hγt : ∀ j, Filter.Tendsto (fun t => c t j) (𝓝[>] (0 : ℝ)) (𝓝 (β j : ℂ)) := by
    intro j
    have hcont : Continuous fun t : ℝ => c t j := by
      simp only [c, γ, Units.val_mul, Units.val_mk0]
      fun_prop
    have h0 : c 0 j = β j := by simp [c, γ]
    have := hcont.tendsto 0
    rw [h0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hγB : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, ‖c t j‖ ≤ B' := by
    rw [Filter.eventually_all]
    intro j
    have h2 : ‖(β j : ℂ)‖ < B' := (hβ j).trans_lt hBB'
    exact ((hγt j).norm.eventually (gt_mem_nhds h2)).mono fun t ht => ht.le
  have hdist : ∀ᶠ t in 𝓝[>] (0 : ℝ), Pairwise fun j j' => c t j ≠ c t j' := by
    have key : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j j', j ≠ j' → c t j ≠ c t j' := by
      rw [Filter.eventually_all]
      intro j
      rw [Filter.eventually_all]
      intro j'
      by_cases hjj : j = j'
      · exact Filter.Eventually.of_forall fun t h => absurd hjj h
      by_cases hb : (β j : ℂ) = β j'
      · filter_upwards [self_mem_nhdsWithin] with t ht _
        simp only [c, γ, Units.val_mul, Units.val_mk0]
        intro heq
        rw [hb] at heq
        have h3 := mul_left_cancel₀ (β j').ne_zero heq
        have h4 : Real.exp (t * ((j : ℕ) : ℝ)) = Real.exp (t * ((j' : ℕ) : ℝ)) := by exact_mod_cast h3
        have h5 := Real.exp_injective h4
        have ht' : (0 : ℝ) < t := ht
        have h6 : ((j : ℕ) : ℝ) = ((j' : ℕ) : ℝ) := mul_left_cancel₀ ht'.ne' h5
        exact hjj (Fin.ext (by exact_mod_cast h6))
      · have h1 : Filter.Tendsto (fun t => c t j - c t j') (𝓝[>] (0 : ℝ)) (𝓝 ((β j : ℂ) - β j')) :=
          (hγt j).sub (hγt j')
        have h2 : (β j : ℂ) - β j' ≠ 0 := sub_ne_zero.mpr hb
        exact (h1.eventually (eventually_ne_nhds h2)).mono fun t ht _ => sub_ne_zero.mp ht
    exact key.mono fun t ht j j' h => ht j j' h
  let G : (Fin m' → ℂ) → {l : Fin m' → ℕ // Antitone l} → ℂ := fun b l =>
    jt α (l : Fin m' → ℕ) * jt b (l : Fin m' → ℕ) * X ^ ∑ j : Fin m', (l : Fin m' → ℕ) j
  have hSa := hS m m' A B' ‖X‖ hA hB' (norm_nonneg _) hX'
  have hSb := hS m' m' B' B' 0 hB' hB' le_rfl (by simp)
  have hbound : ∀ b : Fin m' → ℂ, (∀ j, ‖b j‖ ≤ B') → ∀ l : {l : Fin m' → ℕ // Antitone l},
      ‖G b l‖ ≤ cjt m A (l : Fin m' → ℕ) * cjt m' B' (l : Fin m' → ℕ) * ‖X‖ ^ ∑ j : Fin m', (l : Fin m' → ℕ) j := by
    intro b hb l
    simp only [G, norm_mul, norm_pow]
    have h1 := hSa.2 α hα (l : Fin m' → ℕ)
    have h2 := hSb.2 b hb (l : Fin m' → ℕ)
    have h0 : 0 ≤ cjt m A (l : Fin m' → ℕ) := (norm_nonneg _).trans h1
    exact mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (norm_nonneg _) h0) (pow_nonneg (norm_nonneg _) _)
  have hsumG : Summable (G fun j => (β j : ℂ)) :=
    Summable.of_norm_bounded hSa.1 (hbound _ fun j => (hβ j).trans hBB'.le)
  have hc : Filter.Tendsto c (𝓝[>] (0 : ℝ)) (𝓝 fun j => (β j : ℂ)) := tendsto_pi_nhds.mpr hγt
  have hpt : ∀ l, Filter.Tendsto (fun t => G (c t) l) (𝓝[>] (0 : ℝ)) (𝓝 (G (fun j => (β j : ℂ)) l)) := by
    intro l
    have h := ((continuous_jt (m := m') (l : Fin m' → ℕ)).tendsto _).comp hc
    exact (tendsto_const_nhds.mul h).mul tendsto_const_nhds
  have htsum : Filter.Tendsto (fun t => ∑' l, G (c t) l) (𝓝[>] (0 : ℝ)) (𝓝 (∑' l, G (fun j => (β j : ℂ)) l)) :=
    tendsto_tsum_of_dominated_convergence hSa.1 hpt (hγB.mono fun t ht l => hbound _ ht l)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∏ i : Fin m, ∏ j : Fin m', (1 - α i * c t j * X)⁻¹ = ∑' l, G (c t) l := by
    filter_upwards [hγB, hdist] with t hb hd
    exact (hG m m' α (γ t) X A B' hA hB' hα hb hX' hd).tsum_eq.symm
  have hP : Filter.Tendsto (fun t => ∏ i : Fin m, ∏ j : Fin m', (1 - α i * c t j * X)⁻¹) (𝓝[>] (0 : ℝ))
      (𝓝 (∏ i : Fin m, ∏ j : Fin m', (1 - α i * (β j : ℂ) * X)⁻¹)) := by
    refine tendsto_finsetProd _ fun i _ => tendsto_finsetProd _ fun j _ => ?_
    refine (tendsto_const_nhds.sub ((tendsto_const_nhds.mul (hγt j)).mul tendsto_const_nhds)).inv₀ ?_
    intro h0
    have h1 : α i * (β j : ℂ) * X = 1 := by linear_combination -h0
    have h2 : ‖α i * (β j : ℂ) * X‖ < 1 := by
      rw [norm_mul, norm_mul]
      calc ‖α i‖ * ‖(β j : ℂ)‖ * ‖X‖ ≤ A * B * ‖X‖ := by
            gcongr
            · exact hα i
            · exact hβ j
        _ = ‖X‖ * A * B := by ring
        _ < 1 := hX
    rw [h1, norm_one] at h2
    exact lt_irrefl _ h2
  have heq : ∑' l, G (fun j => (β j : ℂ)) l = ∏ i : Fin m, ∏ j : Fin m', (1 - α i * (β j : ℂ) * X)⁻¹ :=
    tendsto_nhds_unique htsum (hP.congr' hev)
  show HasSum (G fun j => (β j : ℂ)) _
  rw [← heq]
  exact hsumG.hasSum

end PositivityTheory.RgJS
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.CauchyFormula.CauchyOfBetaBounds
noncomputable section

open Finset GroundTheory.Automorphic GroundTheory.Automorphic.Spherical

namespace PositivityTheory.RgJS

namespace CauchyPositivity

theorem exists_pos (A B x : ℝ) (hx : 0 ≤ x) (h : x * A * B < 1) :
    ∃ δ : ℝ, 0 < δ ∧ x * max A δ * max B δ < 1 := by
  have hg : Continuous (fun δ : ℝ => x * max A δ * max B δ) := by fun_prop
  have h0 : x * max A 0 * max B 0 < 1 := by
    rcases le_total A 0 with hA | hA
    · rw [max_eq_right hA]; simp
    rcases le_total B 0 with hB | hB
    · rw [max_eq_right hB]; simp
    rw [max_eq_left hA, max_eq_left hB]; exact h
  have hn : ∀ᶠ δ in nhds (0:ℝ), x * max A δ * max B δ < 1 :=
    (hg.tendsto 0).eventually (gt_mem_nhds h0)
  have hev : ∀ᶠ δ in nhdsWithin (0:ℝ) (Set.Ioi 0), x * max A δ * max B δ < 1 ∧ δ ∈ Set.Ioi (0:ℝ) :=
    (Filter.Eventually.filter_mono nhdsWithin_le_nhds hn).and self_mem_nhdsWithin
  obtain ⟨δ, h1, h2⟩ := hev.exists
  exact ⟨δ, h2, h1⟩

end CauchyPositivity

open CauchyPositivity in
theorem cauchy_of_beta_bounds : BetaAll → SumBd → SchurJT → JTPad → Cauchy := by
  intro hBeta hSum hSchur hPad m m' hmm α β X A B hA hB hX
  obtain ⟨δ, hδ, hlt⟩ := exists_pos A B ‖X‖ (norm_nonneg X) hX
  have hA'pos : 0 < max A δ := lt_of_lt_of_le hδ (le_max_right _ _)
  have hB'pos : 0 < max B δ := lt_of_lt_of_le hδ (le_max_right _ _)
  have hαb : ∀ i, ‖((α i : ℂ))‖ ≤ max A δ := fun i => (hA i).trans (le_max_left _ _)
  have hβb : ∀ j, ‖((β j : ℂ))‖ ≤ max B δ := fun j => (hB j).trans (le_max_left _ _)
  have hH := hBeta m m' (fun i => (α i : ℂ)) β X (max A δ) (max B δ) hA'pos hB'pos hαb hβb hlt
  have e := fun l : Fin m' → ℕ => (hSchur m α (padN m l)).trans (hPad m m' hmm _ l)
  simp only [e]
  obtain ⟨hsum, hbdα⟩ := hSum m m' (max A δ) (max B δ) ‖X‖ hA'pos hB'pos (norm_nonneg _) hlt
  have hbdβ := (hSum m' m' (max B δ) (max B δ) 0 hB'pos hB'pos le_rfl (by simp)).2
  refine ⟨hsum.of_nonneg_of_le (fun _ => norm_nonneg _) (fun l => ?_), hH⟩
  rw [norm_mul, norm_mul, norm_pow, hSchur m' β]
  have h1 := hbdα (fun i => (α i : ℂ)) hαb l
  have h2 := hbdβ (fun j => (β j : ℂ)) hβb l
  exact mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1))
    (pow_nonneg (norm_nonneg _) _)

end PositivityTheory.RgJS
end
end

namespace PositivityTheory.RgJS

theorem cauchy_variation_inequality : Cauchy := by
  have hg := complete_homogeneous_generating
  have hs := homogeneous_sum_bound hg
  have hj := schur_jacobi_trudi_of_alternating (alternating_jacobi_trudi_of_relation (elementary_relation_of_generating hg))
  exact cauchy_of_beta_bounds (beta_all_of_generating (beta_generating_of_sum_bound hg hs hj) hs hj) hs hj jacobi_trudi_padding

theorem cauchy_local_inequality : CauchyLoc :=
  cauchy_local_of_cauchy cauchy_variation_inequality (schur_jacobi_trudi_of_alternating (alternating_jacobi_trudi_of_relation (elementary_relation_of_generating complete_homogeneous_generating))) jacobi_trudi_padding

end PositivityTheory.RgJS
