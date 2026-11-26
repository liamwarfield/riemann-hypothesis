module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.UniqueU
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.IsCompactUnitaryMat

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RootSumApply
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.EqSmulHighestWeightOfIsWeight
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.KEConjTranspose
noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas

open Formalism.QuantumDeterminants

variable {k r : ℕ}

def kE (k r : ℕ) (h : Matrix (Fin k) (Fin k) ℂ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  fun i j => if hi : i.val < k then (if hj : j.val < k then h ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0)
    else (if i = j then 1 else 0)

def fI (k r : ℕ) (q : Fin k) : Fin (2 * r + k + 1) := ⟨q.val, by omega⟩

theorem fI_inj : Function.Injective (fI k r) := by
  intro a b h; simp [fI, Fin.ext_iff] at h; exact Fin.ext h

theorem sumF (f : Fin (2 * r + k + 1) → ℂ) (hf : ∀ p : Fin (2 * r + k + 1), ¬ p.val < k → f p = 0) :
    ∑ p, f p = ∑ q : Fin k, f (fI k r q) := by
  symm
  refine Fintype.sum_of_injective (fI k r) fI_inj _ _ ?_ (fun _ => rfl)
  intro p hp
  apply hf
  intro hlt
  exact hp ⟨⟨p.val, hlt⟩, rfl⟩

theorem kE_ff (h : Matrix (Fin k) (Fin k) ℂ) (q q' : Fin k) : kE k r h (fI k r q) (fI k r q') = h q q' := by
  simp [kE, fI]

theorem kE_row (h : Matrix (Fin k) (Fin k) ℂ) {i : Fin (2 * r + k + 1)} (j : Fin (2 * r + k + 1))
    (hi : ¬ i.val < k) : kE k r h i j = if i = j then 1 else 0 := by
  simp [kE, hi]

theorem kE_col (h : Matrix (Fin k) (Fin k) ℂ) (i : Fin (2 * r + k + 1)) {j : Fin (2 * r + k + 1)}
    (hj : ¬ j.val < k) : kE k r h i j = if i = j then 1 else 0 := by
  by_cases hi : i.val < k
  · have hne : i ≠ j := by rintro rfl; exact hj hi
    simp [kE, hi, hj, hne]
  · simp [kE, hi]

theorem ex_fI {i : Fin (2 * r + k + 1)} (hi : i.val < k) : ∃ q, i = fI k r q :=
  ⟨⟨i.val, hi⟩, by ext; simp [fI]⟩

theorem kE_mul (a b : Matrix (Fin k) (Fin k) ℂ) : kE k r (a * b) = kE k r a * kE k r b := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : i.val < k
  · obtain ⟨qi, rfl⟩ := ex_fI hi
    rw [sumF _ (fun p hp => by rw [kE_col a _ hp, if_neg (by rintro rfl; exact hp hi), zero_mul])]
    by_cases hj : j.val < k
    · obtain ⟨qj, rfl⟩ := ex_fI hj
      simp only [kE_ff, Matrix.mul_apply]
    · rw [kE_col _ _ hj, if_neg (by rintro rfl; exact hj hi)]
      refine (Finset.sum_eq_zero fun q _ => ?_).symm
      rw [kE_col b _ hj, if_neg (by intro h; apply hj; rw [← h]; exact q.2), mul_zero]
  · rw [kE_row _ j hi]
    rw [Finset.sum_eq_single i (fun p _ hp => by rw [kE_row a p hi, if_neg (Ne.symm hp), zero_mul])
      (fun h => absurd (Finset.mem_univ _) h)]
    rw [kE_row a i hi, if_pos rfl, one_mul, kE_row b j hi]

theorem kE_one : kE k r (1 : Matrix (Fin k) (Fin k) ℂ) = 1 := by
  ext i j
  by_cases hi : i.val < k
  · by_cases hj : j.val < k
    · simp only [kE, dif_pos hi, dif_pos hj, Matrix.one_apply, Fin.ext_iff]
    · rw [kE_col _ _ hj, Matrix.one_apply]
  · rw [kE_row _ _ hi, Matrix.one_apply]

theorem kE_conjTranspose (h : Matrix (Fin k) (Fin k) ℂ) : (kE k r h)ᴴ = kE k r hᴴ := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  by_cases hi : i.val < k
  · by_cases hj : j.val < k
    · simp only [kE, dif_pos hi, dif_pos hj, Matrix.conjTranspose_apply]
    · rw [kE_row _ _ hj, kE_col _ _ hj]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg (Ne.symm hij), if_neg hij, star_zero]
  · rw [kE_col _ _ hi, kE_row _ _ hi]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg (Ne.symm hij), if_neg hij, star_zero]

variable {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}

theorem cay_col (hW : WCols k r P) (q : Fin k) (l : Fin (2 * r + k + 1)) :
    P l (StandardBasisEmbedding.eB k r q) = if l = fI k r q then 1 else 0 := by
  have h := congrFun (hW q) l
  have e : Formalism.QuantumDeterminants.wI k r q.castSucc = StandardBasisEmbedding.eB k r q := rfl
  rw [e] at h
  simp only [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h
  rw [h]
  rfl

theorem cay_entry (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hW : WCols k r P) (q : Fin k) (j : Fin (2 * r + k + 1)) :
    Hpk k r (StandardBasisEmbedding.eB k r q) j = (if ε (fI k r q) then 1 else -1) * P (fI k r q) j := by
  rw [← hP.2, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, cay_col hW, Formalism.REAL.Jm, Matrix.diagonal_apply]
  simp
  rw [Finset.sum_eq_single (fI k r q) (fun b _ hb => by simp [hb]) (by simp)]
  simp

theorem cay_eps (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hW : WCols k r P) (a : Fin (2 * r + k + 1))
    (ha : a.val < k) : ε a = true := by
  have h := cay_entry hP hW ⟨a.val, ha⟩ (StandardBasisEmbedding.eB k r ⟨a.val, ha⟩)
  rw [StandardBasisEmbedding.H_blrow (StandardBasisEmbedding.bl_eB _), if_pos rfl, cay_col hW, if_pos rfl, mul_one] at h
  have e : fI k r ⟨a.val, ha⟩ = a := Fin.ext rfl
  rw [e] at h
  by_contra hne
  rw [if_neg hne] at h
  norm_num at h

theorem cay_zero (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hW : WCols k r P) (q : Fin k) {j : Fin (2 * r + k + 1)}
    (hj : ¬ StandardBasisEmbedding.bl k r j) : P (fI k r q) j = 0 := by
  have h := cay_entry hP hW q j
  rw [StandardBasisEmbedding.H_blrow (StandardBasisEmbedding.bl_eB _), if_neg (by rintro rfl; exact hj (StandardBasisEmbedding.bl_eB q))] at h
  have hne : (if ε (fI k r q) then (1 : ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num
  exact (mul_eq_zero.1 h.symm).resolve_left hne

theorem cay_mul (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hW : WCols k r P) (h : Matrix (Fin k) (Fin k) ℂ) :
    P * Formalism.MainNotions.S.blockW k r h = kE k r h * P := by
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  by_cases hj : StandardBasisEmbedding.bl k r j
  · obtain ⟨q', rfl⟩ := StandardBasisEmbedding.ex_eB hj
    rw [StandardBasisEmbedding.sumB _ (fun p hp => by rw [StandardBasisEmbedding.bw_off h hp hj, mul_zero])]
    simp only [StandardBasisEmbedding.bw_ee, cay_col hW, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    by_cases hi : i.val < k
    · obtain ⟨qi, rfl⟩ := ex_fI hi
      simp only [ite_mul, one_mul, zero_mul, kE_ff]
      rw [Finset.sum_eq_single qi (fun b _ hb => by rw [if_neg (fun e => hb (fI_inj e).symm)])
        (fun h => absurd (Finset.mem_univ _) h), if_pos rfl]
    · rw [kE_row _ _ hi, if_neg (by intro e; apply hi; rw [e]; exact q'.2)]
      refine Finset.sum_eq_zero fun q _ => ?_
      rw [if_neg (by intro e; apply hi; rw [e]; exact q.2), zero_mul]
  · rw [Finset.sum_eq_single j (fun b _ hb => by rw [StandardBasisEmbedding.bw_col h b hj, if_neg hb, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h), StandardBasisEmbedding.bw_col h j hj, if_pos rfl, mul_one]
    by_cases hi : i.val < k
    · obtain ⟨qi, rfl⟩ := ex_fI hi
      rw [cay_zero hP hW qi hj]
      refine (Finset.sum_eq_zero fun l _ => ?_).symm
      by_cases hl : l.val < k
      · obtain ⟨ql, rfl⟩ := ex_fI hl
        rw [cay_zero hP hW ql hj, mul_zero]
      · rw [kE_col _ _ hl, if_neg (by rintro rfl; exact hl (by simp [fI])), zero_mul]
    · rw [Finset.sum_eq_single i (fun b _ hb => by rw [kE_row h b hi, if_neg (Ne.symm hb), zero_mul])
        (fun h => absurd (Finset.mem_univ _) h), kE_row h i hi, if_pos rfl, one_mul]

theorem cay_kE (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hW : WCols k r P) (h : Matrix (Fin k) (Fin k) ℂ) :
    P * Formalism.MainNotions.S.blockW k r h * P⁻¹ = kE k r h := by
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1
  rw [cay_mul hP hW, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas
end
end

noncomputable section

open Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem eq_smul_highestWeight_of_isWeight {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ) {v : T.V}
    (hv : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) (HW.torepSig T) Λ v) : ∃ c : ℂ, v = c • T.w := by
  by_cases h0 : v = 0
  · exact ⟨0, by simp [h0]⟩
  have hd := HW.torep_dτ_of_wt T hv
  have hraise : ∀ a b, a < b → ε a = ε b → T.dτ (Matrix.single a b 1) v = 0 := by
    intro a b hab he
    by_contra hx
    have hwx : ∀ c, T.dτ (Matrix.single c c 1) (T.dτ (Matrix.single a b 1) v) =
        (((Λ + Pi.single a 1 - Pi.single b 1 : Fin n → ℝ) c : ℝ) : ℂ) • T.dτ (Matrix.single a b 1) v := by
      intro c
      have hR := HW.KType.kRel T c c a b rfl he
      have h1 := congrArg (fun f : Module.End ℂ T.V => f v) hR
      simp only [HW.kunits, LinearMap.sub_apply, Module.End.mul_apply, ContinuousLinearMap.coe_coe] at h1
      have hab' : a ≠ b := ne_of_lt hab
      rw [hd c, map_smul] at h1
      by_cases hca : c = a
      · subst hca
        have hcb : ¬ b = c := fun h => hab' h.symm
        rw [if_pos rfl, if_neg hcb] at h1
        simp only [LinearMap.zero_apply, sub_zero, ContinuousLinearMap.coe_coe] at h1
        rw [sub_eq_iff_eq_add] at h1
        rw [h1]
        simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply, if_pos rfl, if_neg (Ne.symm hcb)]
        push_cast
        module
      · by_cases hcb : b = c
        · subst hcb
          rw [if_neg hca, if_pos rfl] at h1
          simp only [LinearMap.zero_apply, zero_sub, ContinuousLinearMap.coe_coe] at h1
          rw [sub_eq_iff_eq_add] at h1
          rw [h1]
          simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply, if_pos rfl, if_neg hca]
          push_cast
          module
        · rw [if_neg hca, if_neg hcb] at h1
          simp only [LinearMap.zero_apply, sub_zero] at h1
          rw [sub_eq_zero] at h1
          rw [h1]
          simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply, if_neg hca, if_neg (Ne.symm hcb)]
          simp
    obtain ⟨cc, hc, he'⟩ := HW.KType.weight_le T hx hwx
    let ψ : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun f => ∑ j : Fin n, ((j : ℕ) : ℝ) * f j
        map_add' := by
          intro f g
          simp [mul_add, Finset.sum_add_distrib]
        map_smul' := by
          intro r f
          simp [Finset.mul_sum, mul_left_comm] }
    have hψ : ∀ x : Fin n, ψ (Pi.single x 1) = ((x : ℕ) : ℝ) := by
      intro x
      simp [ψ, Pi.single_apply]
    have hl : Λ - (Λ + Pi.single a 1 - Pi.single b 1) = Pi.single b 1 - Pi.single a 1 := by
      abel
    rw [hl] at he'
    have h := congrArg ψ he'
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, root, map_sub, hψ, smul_eq_mul] at h
    have hr : ∑ x, ∑ y, (cc x y : ℝ) * (((x : ℕ) : ℝ) - ((y : ℕ) : ℝ)) ≤ 0 := by
      refine Finset.sum_nonpos fun x _ => Finset.sum_nonpos fun y _ => ?_
      by_cases h0 : cc x y = 0
      · simp [h0]
      · have hxy := (hc x y h0).1
        have : ((x : ℕ) : ℝ) < ((y : ℕ) : ℝ) := by exact_mod_cast hxy
        exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
    have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
    linarith
  obtain ⟨-, c, hc⟩ := HW.KType.hw_unique T h0 ⟨hd, hraise⟩
  exact ⟨c, hc⟩

section Span

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ}

theorem sumF' {M : Type*} [AddCommMonoid M] (f : Fin (2 * r + k + 1) → M)
    (hf : ∀ p : Fin (2 * r + k + 1), ¬ p.val < k → f p = 0) :
    ∑ p, f p = ∑ q : Fin k, f (fI k r q) := by
  symm
  refine Fintype.sum_of_injective (fI k r) fI_inj _ _ ?_ (fun _ => rfl)
  intro p hp
  apply hf
  intro hlt
  exact hp ⟨⟨p.val, hlt⟩, rfl⟩

theorem kE_mem_Kset (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) {h : Matrix (Fin k) (Fin k) ℂ}
    (hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ) : kE k r h ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, kE_conjTranspose, ← kE_mul]
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hh
    rw [hh, kE_one]
  · ext i j
    simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hi : i.val < k
    · by_cases hj : j.val < k
      · rw [hε i hi, hε j hj]; simp
      · rw [kE_col _ _ hj, if_neg (by rintro rfl; exact hj hi)]; simp
    · rw [kE_row _ _ hi]
      by_cases hij : i = j
      · subst hij; ring
      · rw [if_neg hij]; simp

def dg (θ : Fin (2 * r + k + 1) → ℝ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))

def th2 (θ : Fin (2 * r + k + 1) → ℝ) : Fin (2 * r + k + 1) → ℝ := fun a => if a.val < k then 0 else θ a

def th1 (θ : Fin (2 * r + k + 1) → ℝ) : Fin k → ℝ := fun q => θ (fI k r q)

def dgk (t : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℂ := Matrix.diagonal (fun a => Complex.exp ((t a : ℂ) * Complex.I))

theorem dg_mem (θ : Fin (2 * r + k + 1) → ℝ) : dg θ ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, dg, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rw [Pi.star_apply, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    simp
  · simp only [dg, Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, mul_comm]

theorem dgk_mem (t : Fin k → ℝ) : dgk t ∈ Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k) := by
  have := dg_mem (k := k) (r := 0) (ε := fun _ => true)
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, dgk, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rw [Pi.star_apply, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    simp
  · simp only [dgk, Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, mul_comm]

theorem dg_split (θ : Fin (2 * r + k + 1) → ℝ) : dg θ = kE k r (dgk (th1 θ)) * dg (th2 θ) := by
  ext i j
  unfold dg
  rw [Matrix.mul_diagonal]
  by_cases hi : i.val < k
  · by_cases hj : j.val < k
    · simp only [dg, dgk, kE, th1, th2, dif_pos hi, dif_pos hj, if_pos hj, Matrix.diagonal_apply, fI]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij, if_neg (by intro e; apply hij; exact Fin.ext (by simpa using e))]; simp
    · simp only [dg, th2, if_neg hj, Matrix.diagonal_apply]
      rw [kE_col _ _ hj]
      by_cases hij : i = j
      · subst hij; exact absurd hi hj
      · simp [hij]
  · simp only [dg, th2, Matrix.diagonal_apply]
    rw [kE_row _ _ hi]
    by_cases hij : i = j
    · subst hij; simp [hi]
    · simp [hij]

theorem central_diagonal_commute (θ : Fin (2 * r + k + 1) → ℝ) (h : Matrix (Fin k) (Fin k) ℂ) :
    kE k r h * dg (th2 θ) = dg (th2 θ) * kE k r h := by
  ext i j
  rw [dg, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hi : i.val < k
  · by_cases hj : j.val < k
    · simp [th2, hi, hj]
    · rw [kE_col _ _ hj, if_neg (by rintro rfl; exact hj hi)]; simp
  · rw [kE_row _ _ hi]
    by_cases hij : i = j
    · subst hij; ring
    · rw [if_neg hij]; simp

variable (T : S7.KType ε Λ)

def rhoK (h : Matrix (Fin k) (Fin k) ℂ) : T.V →L[ℂ] T.V := HW.torepSig T (kE k r h)

def spanW : Submodule ℂ T.V :=
  sInf {S | T.w ∈ S ∧ ∀ h ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ v ∈ S, rhoK (k := k) (r := r) T h v ∈ S}

theorem w_mem_spanW : T.w ∈ spanW (k := k) (r := r) T :=
  Submodule.mem_sInf.2 fun _ hS => hS.1

theorem spanW_stable {h : Matrix (Fin k) (Fin k) ℂ} (hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ) {v : T.V}
    (hv : v ∈ spanW (k := k) (r := r) T) : rhoK (k := k) (r := r) T h v ∈ spanW (k := k) (r := r) T :=
  Submodule.mem_sInf.2 fun S hS => hS.2 h hh v (Submodule.mem_sInf.1 hv S hS)

theorem spanW_le {S : Submodule ℂ T.V} (hw : T.w ∈ S)
    (hS : ∀ h ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ v ∈ S, rhoK (k := k) (r := r) T h v ∈ S) :
    spanW (k := k) (r := r) T ≤ S :=
  sInf_le ⟨hw, hS⟩

theorem torep_mul {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ Formalism.REAL.Kset ε)
    (hb : b ∈ Formalism.REAL.Kset ε) (v : T.V) : HW.torepSig T (a * b) v = HW.torepSig T a (HW.torepSig T b v) := by
  rw [(HW.torep_isURepOn T).1.2 a ha b hb]; rfl

theorem spanW_scalar (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) (θ : Fin (2 * r + k + 1) → ℝ)
    {x : T.V} (hx : x ∈ spanW (k := k) (r := r) T) :
    HW.torepSig T (dg (th2 θ)) x = Complex.exp (((∑ a, Λ a * th2 θ a : ℝ) : ℂ) * Complex.I) • x := by
  set c := Complex.exp (((∑ a, Λ a * th2 θ a : ℝ) : ℂ) * Complex.I)
  let S : Submodule ℂ T.V := LinearMap.ker ((HW.torepSig T (dg (th2 θ)) : T.V →ₗ[ℂ] T.V) - c • LinearMap.id)
  have hmem : ∀ y, y ∈ S ↔ HW.torepSig T (dg (th2 θ)) y = c • y := by
    intro y
    simp [S, sub_eq_zero]
  have hle : spanW (k := k) (r := r) T ≤ S := by
    refine spanW_le T ((hmem _).2 (HW.torep_wt_w T (th2 θ) (dg_mem _))) ?_
    intro h hh v hv
    rw [hmem] at hv ⊢
    unfold rhoK
    rw [← torep_mul T (dg_mem _) (kE_mem_Kset hε hh), ← central_diagonal_commute, torep_mul T (kE_mem_Kset hε hh) (dg_mem _), hv,
      map_smul]
  exact (hmem x).1 (hle hx)

end Span

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas
end
end

noncomputable section

open Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas

open ReciprocityTheory.ChartRestriction.DS

section Wt

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ} (T : S7.KType ε Λ)

theorem dgk_unit (t : Fin k → ℝ) : dgk t ∈ Matrix.unitaryGroup (Fin k) ℂ := (dgk_mem t).1

theorem wt_full (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) {x : T.V}
    (hx : x ∈ spanW (k := k) (r := r) T) {μ : Fin k → ℝ}
    (hμ : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) (rhoK (k := k) (r := r) T) μ x) :
    Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) (HW.torepSig T)
      (fun a => if h : a.val < k then μ ⟨a.val, h⟩ else Λ a) x := by
  intro θ _
  change HW.torepSig T (dg θ) x = _
  rw [dg_split, torep_mul T (kE_mem_Kset hε (dgk_unit _)) (dg_mem _), spanW_scalar T hε θ hx, map_smul]
  have h1 : HW.torepSig T (kE k r (dgk (th1 θ))) x =
      Complex.exp (((∑ q, μ q * th1 θ q : ℝ) : ℂ) * Complex.I) • x := hμ (th1 θ) (dgk_mem _)
  rw [h1, smul_smul, ← Complex.exp_add]
  congr 1
  have hs : (∑ a, (if h : a.val < k then μ ⟨a.val, h⟩ else Λ a) * θ a) =
      (∑ a, Λ a * th2 θ a) + ∑ q, μ q * th1 θ q := by
    have e : ∑ q, μ q * th1 θ q = ∑ a : Fin (2 * r + k + 1), (if h : a.val < k then μ ⟨a.val, h⟩ * θ a else 0) := by
      rw [sumF' (k := k) (r := r) (fun a : Fin (2 * r + k + 1) => if h : a.val < k then μ ⟨a.val, h⟩ * θ a else 0)
        (fun p hp => by rw [dite_eq_right hp])]
      refine Finset.sum_congr rfl fun q _ => ?_
      have hq : (fI k r q).val < k := q.2
      rw [dif_pos hq]
      rfl
    rw [e, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : a.val < k
    · simp [th2, ha]
    · simp [th2, ha]
  rw [hs, Complex.ofReal_add, add_mul]

theorem root_sum_apply {m : ℕ} (c : Fin m → Fin m → ℕ) (x : Fin m) :
    (∑ a, ∑ b, (c a b : ℝ) • (Pi.single a (1 : ℝ) - Pi.single b 1 : Fin m → ℝ)) x =
      ∑ b, (c x b : ℝ) - ∑ a, (c a x : ℝ) := by
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_apply, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
  congr 1
  · rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq]
  · simp [Finset.sum_ite_eq]

theorem wt_cdom (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) {x : T.V}
    (hx : x ∈ spanW (k := k) (r := r) T) (hx0 : x ≠ 0) {μ : Fin k → ℝ}
    (hμ : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) (rhoK (k := k) (r := r) T) μ x) :
    Formalism.MainNotions.S.CDom (Formalism.MainNotions.S.allPos k) μ (fun q => Λ (fI k r q)) := by
  have hfull := wt_full T hε hx hμ
  obtain ⟨c, hc, he⟩ := HW.KType.weight_le T hx0 (HW.torep_dτ_of_wt T hfull)
  have he' : ∀ y, (Λ - fun a => if h : a.val < k then μ ⟨a.val, h⟩ else Λ a) y =
      ∑ b, (c y b : ℝ) - ∑ a, (c a y : ℝ) := by
    intro y
    rw [he]
    exact root_sum_apply c y

  have hzero : ∀ a b : Fin (2 * r + k + 1), a.val < k → ¬ b.val < k → c a b = 0 := by
    let g : Fin (2 * r + k + 1) → ℝ := fun y => if y.val < k then 0 else 1
    have hsum : ∑ y, g y * (∑ b, (c y b : ℝ) - ∑ a, (c a y : ℝ)) = 0 := by
      refine Finset.sum_eq_zero fun y _ => ?_
      by_cases hy : y.val < k
      · simp [g, hy]
      · rw [← he' y]; simp [g, hy]
    have hsum2 : ∑ y, g y * (∑ b, (c y b : ℝ) - ∑ a, (c a y : ℝ)) =
        ∑ a, ∑ b, (c a b : ℝ) * (g a - g b) := by
      simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
      congr 1
      · exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    rw [hsum2] at hsum
    have hnp : ∀ a b : Fin (2 * r + k + 1), (c a b : ℝ) * (g a - g b) ≤ 0 := by
      intro a b
      by_cases h0 : c a b = 0
      · simp [h0]
      · have hab := (hc a b h0).1
        have hab' : a.val < b.val := hab
        refine mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) ?_
        simp only [g]
        split_ifs with h1 h2 h2 <;> norm_num
        omega
    have hall := (Finset.sum_eq_zero_iff_of_nonpos (fun a _ => Finset.sum_nonpos fun b _ => hnp a b)).1 hsum
    intro a b ha hb
    have h1 := (Finset.sum_eq_zero_iff_of_nonpos (fun b _ => hnp a b)).1 (hall a (Finset.mem_univ _)) b
      (Finset.mem_univ _)
    simp only [g, if_pos ha, if_neg hb] at h1
    norm_num at h1
    exact_mod_cast h1
  refine ⟨fun q q' => c (fI k r q) (fI k r q'), fun q q' h => ⟨?_, rfl⟩, ?_⟩
  · have := (hc _ _ h).1
    exact this
  · funext q
    have hq : (fI k r q).val < k := q.2
    have h1 := he' (fI k r q)
    simp only [Pi.sub_apply, dif_pos hq] at h1
    have e1 : ∑ b, (c (fI k r q) b : ℝ) = ∑ q', (c (fI k r q) (fI k r q') : ℝ) :=
      sumF' _ (fun p hp => by rw [hzero _ _ hq hp]; simp)
    have e2 : ∑ a, (c a (fI k r q) : ℝ) = ∑ q', (c (fI k r q') (fI k r q) : ℝ) := by
      refine sumF' _ (fun p hp => ?_)
      by_cases h0 : c p (fI k r q) = 0
      · simp [h0]
      · have := (hc _ _ h0).1
        have : p.val < (fI k r q).val := this
        exact absurd (lt_trans this hq) hp
    rw [e1, e2] at h1
    have e3 : (⟨(fI k r q).val, hq⟩ : Fin k) = q := Fin.ext rfl
    rw [e3] at h1
    rw [show ((fun q => Λ (fI k r q)) - μ) q = Λ (fI k r q) - μ q from rfl, h1]
    have := root_sum_apply (fun q q' => c (fI k r q) (fI k r q')) q
    rw [← this]
    rfl

end Wt

section Irr

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ} (T : S7.KType ε Λ)

theorem kE_dgk (t : Fin k → ℝ) :
    kE k r (dgk t) = dg (fun a : Fin (2 * r + k + 1) => if h : a.val < k then t ⟨a.val, h⟩ else 0) := by
  ext i j
  simp only [dg, Matrix.diagonal_apply]
  by_cases hi : i.val < k
  · by_cases hj : j.val < k
    · simp only [kE, dgk, dif_pos hi, dif_pos hj, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij, if_neg (by intro e; apply hij; exact Fin.ext (by simpa using e))]
    · rw [kE_col _ _ hj, if_neg (by rintro rfl; exact hj hi)]; simp [show i ≠ j by rintro rfl; exact hj hi]
  · rw [kE_row _ _ hi]
    by_cases hij : i = j
    · subst hij; simp [hi]
    · simp [hij]

theorem kE_cont : Continuous (kE k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [kE]
  split_ifs
  · exact (continuous_apply _).comp (continuous_apply _)
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const

theorem w_wtK : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) (rhoK (k := k) (r := r) T)
    (fun q => Λ (fI k r q)) T.w := by
  intro t _
  change HW.torepSig T (kE k r (dgk t)) T.w = _
  rw [kE_dgk]
  unfold dg
  rw [HW.torep_wt_w T _ (dg_mem _)]
  congr 3
  congr 1
  refine (sumF' (M := ℝ) (k := k) (r := r) _ (fun p hp => ?_)).trans (Finset.sum_congr rfl fun q _ => ?_)
  · simp [hp]
  · have hq : (fI k r q).val < k := q.2
    simp only [dif_pos hq]
    rfl

theorem rhoK_one (v : T.V) : rhoK (k := k) (r := r) T 1 v = v := by
  unfold rhoK
  rw [kE_one, (HW.torep_isURepOn T).1.1]
  rfl

theorem rhoK_mul (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) {a b : Matrix (Fin k) (Fin k) ℂ}
    (ha : a ∈ Matrix.unitaryGroup (Fin k) ℂ) (hb : b ∈ Matrix.unitaryGroup (Fin k) ℂ) (v : T.V) :
    rhoK (k := k) (r := r) T (a * b) v = rhoK (k := k) (r := r) T a (rhoK (k := k) (r := r) T b v) := by
  unfold rhoK
  rw [kE_mul, torep_mul T (kE_mem_Kset hε ha) (kE_mem_Kset hε hb)]

theorem rhoK_norm (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) {a : Matrix (Fin k) (Fin k) ℂ}
    (ha : a ∈ Matrix.unitaryGroup (Fin k) ℂ) (v : T.V) : ‖rhoK (k := k) (r := r) T a v‖ = ‖v‖ :=
  (HW.torep_isURepOn T).2.1 _ (kE_mem_Kset hε ha) v

theorem rhoK_adj (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) {h : Matrix (Fin k) (Fin k) ℂ}
    (hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ) (u v : T.V) :
    ⟪u, rhoK (k := k) (r := r) T h v⟫_ℂ = ⟪rhoK (k := k) (r := r) T (star h) u, v⟫_ℂ := by
  have hs : star h ∈ Matrix.unitaryGroup (Fin k) ℂ := Unitary.star_mem hh
  have hinv : rhoK (k := k) (r := r) T (star h) (rhoK (k := k) (r := r) T h v) = v := by
    rw [← rhoK_mul T hε hs hh, Unitary.star_mul_self_of_mem hh, rhoK_one]
  let Lm : T.V →ₗᵢ[ℂ] T.V :=
    { toLinearMap := (rhoK (k := k) (r := r) T (star h) : T.V →ₗ[ℂ] T.V), norm_map' := rhoK_norm T hε hs }
  have := Lm.inner_map_map u (rhoK (k := k) (r := r) T h v)
  change ⟪rhoK (k := k) (r := r) T (star h) u, rhoK (k := k) (r := r) T (star h) (rhoK (k := k) (r := r) T h v)⟫_ℂ = _
    at this
  rw [hinv] at this
  exact this.symm

theorem spanW_irred (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) (S' : Submodule ℂ T.V)
    (hle : S' ≤ spanW (k := k) (r := r) T)
    (hS' : ∀ h ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ v ∈ S', rhoK (k := k) (r := r) T h v ∈ S') :
    S' = ⊥ ∨ spanW (k := k) (r := r) T ≤ S' := by
  have hperp : ∀ h ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ v ∈ S'ᗮ, rhoK (k := k) (r := r) T h v ∈ S'ᗮ := by
    intro h hh v hv
    rw [Submodule.mem_orthogonal] at hv ⊢
    intro u hu
    rw [rhoK_adj T hε hh]
    exact hv _ (hS' _ (Unitary.star_mem hh) u hu)
  have hbot : ∀ x, x ∈ S' → x ∈ S'ᗮ → x = 0 := by
    intro x h1 h2
    have hm : x ∈ S' ⊓ S'ᗮ := ⟨h1, h2⟩
    rw [Submodule.inf_orthogonal_eq_bot] at hm
    exact (Submodule.mem_bot ℂ).1 hm
  obtain ⟨p, hp, q, hq, hpq⟩ := S'.exists_add_mem_mem_orthogonal T.w
  have hpw : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) (rhoK (k := k) (r := r) T)
      (fun q => Λ (fI k r q)) p := by
    intro t ht
    have hu : dgk t ∈ Matrix.unitaryGroup (Fin k) ℂ := ht.1
    have h1 := w_wtK T t ht
    set c := Complex.exp (((∑ a, Λ (fI k r a) * t a : ℝ) : ℂ) * Complex.I)
    change rhoK (k := k) (r := r) T (dgk t) T.w = c • T.w at h1
    change rhoK (k := k) (r := r) T (dgk t) p = c • p
    rw [hpq, map_add (f := _), smul_add] at h1
    have hA : rhoK (k := k) (r := r) T (dgk t) p - c • p ∈ S' := S'.sub_mem (hS' _ hu _ hp) (S'.smul_mem _ hp)
    have hB : rhoK (k := k) (r := r) T (dgk t) p - c • p ∈ S'ᗮ := by
      have e : rhoK (k := k) (r := r) T (dgk t) p - c • p = c • q - rhoK (k := k) (r := r) T (dgk t) q := by
        rw [sub_eq_sub_iff_add_eq_add, h1]
        exact add_comm _ _
      rw [e]
      exact S'ᗮ.sub_mem (S'ᗮ.smul_mem _ hq) (hperp _ hu _ hq)
    exact sub_eq_zero.1 (hbot _ hA hB)
  have hqw : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) (rhoK (k := k) (r := r) T)
      (fun q => Λ (fI k r q)) q := by
    intro t ht
    have h1 := w_wtK T t ht
    have h2 := hpw t ht
    have e : q = T.w - p := by rw [hpq]; abel
    rw [e, map_sub, h1, h2, smul_sub]
  have hpS : p ∈ spanW (k := k) (r := r) T := hle hp
  have hqS : q ∈ spanW (k := k) (r := r) T := by
    have e : q = T.w - p := by rw [hpq]; abel
    rw [e]; exact sub_mem (w_mem_spanW T) hpS
  have hfix : (fun a : Fin (2 * r + k + 1) => if h : a.val < k then (fun q => Λ (fI k r q)) ⟨a.val, h⟩ else Λ a) = Λ := by
    funext a; split_ifs <;> rfl
  have hp2 := wt_full T hε hpS hpw
  have hq2 := wt_full T hε hqS hqw
  rw [hfix] at hp2 hq2
  obtain ⟨a, ha⟩ := eq_smul_highestWeight_of_isWeight T hp2
  obtain ⟨b, hb⟩ := eq_smul_highestWeight_of_isWeight T hq2
  have hinner : ⟪p, q⟫_ℂ = 0 := Submodule.inner_right_of_mem_orthogonal hp hq
  rw [ha, hb, inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K, T.w_norm] at hinner
  simp only [RCLike.ofReal_one, one_pow, mul_one] at hinner
  rcases mul_eq_zero.1 hinner with h | h
  · left
    have ha0 : a = 0 := by simpa using h
    have hq' : T.w = q := by rw [hpq, ha, ha0, zero_smul, zero_add]
    have hle' : spanW (k := k) (r := r) T ≤ S'ᗮ := spanW_le T (hq' ▸ hq) hperp
    rw [Submodule.eq_bot_iff]
    intro x hx
    exact hbot x hx (hle' (hle hx))
  · right
    have hp' : T.w = p := by rw [hpq, hb, h, zero_smul, add_zero]
    exact spanW_le T (hp' ▸ hp) hS'

end Irr

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas
end
end

noncomputable section

open Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas

open ReciprocityTheory.ChartRestriction.DS

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ} (T : S7.KType ε Λ)


open Classical in
def rhoS (h : Matrix (Fin k) (Fin k) ℂ) : spanW (k := k) (r := r) T →L[ℂ] spanW (k := k) (r := r) T :=
  if hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ then
    LinearMap.toContinuousLinearMap ((rhoK (k := k) (r := r) T h : T.V →ₗ[ℂ] T.V).restrict
      (fun _ hv => spanW_stable T hh hv))
  else 0

theorem rhoS_apply {h : Matrix (Fin k) (Fin k) ℂ} (hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ)
    (v : spanW (k := k) (r := r) T) : (rhoS T h v : T.V) = rhoK (k := k) (r := r) T h v := by
  simp only [rhoS, dif_pos hh]
  rfl

theorem uj_unit {h : Matrix (Fin k) (Fin k) ℂ} (hh : h ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k)) :
    h ∈ Matrix.unitaryGroup (Fin k) ℂ := by
  exact (HW.uqU_mem_Kset hh).1

theorem unit_ks {h : Matrix (Fin k) (Fin k) ℂ} (hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ) :
    h ∈ Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k) := by
  refine ⟨hh, ?_⟩
  simp [Formalism.REAL.Jm, Formalism.MainNotions.S.allPos]

theorem unit_uj {h : Matrix (Fin k) (Fin k) ℂ} (hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ) :
    h ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k) := by
  have hJ : Formalism.REAL.Jm (Formalism.MainNotions.S.allPos k) = 1 := by simp [Formalism.REAL.Jm, Formalism.MainNotions.S.allPos]
  show hᴴ * Formalism.REAL.Jm (Formalism.MainNotions.S.allPos k) * h = Formalism.REAL.Jm (Formalism.MainNotions.S.allPos k)
  rw [hJ, Matrix.mul_one, ← Matrix.star_eq_conjTranspose]
  exact Unitary.star_mul_self_of_mem hh

theorem wtS_iff {μ : Fin k → ℝ} {v : spanW (k := k) (r := r) T} :
    Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) (rhoS T) μ v ↔
      Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) (rhoK (k := k) (r := r) T) μ (v : T.V) := by
  constructor
  · intro h t ht
    have := congrArg Subtype.val (h t ht)
    rw [rhoS_apply T ht.1] at this
    exact this
  · intro h t ht
    apply Subtype.ext
    rw [rhoS_apply T ht.1]
    exact h t ht

theorem rhoS_hc (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) {u : Fin k → ℝ}
    (hΛ : ∀ q : Fin k, Λ (fI k r q) = Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u q) :
    Formalism.MainNotions.S.IsHCTypeU k u (rhoS T) := by
  have hΛ' : (fun q => Λ (fI k r q)) = Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u := funext hΛ
  refine ⟨⟨⟨⟨T.w, w_mem_spanW T⟩, 0, fun h => HW.KType.w_ne_zero T (congrArg Subtype.val h)⟩⟩,
    inferInstance, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨inferInstance, fun _ _ _ _ => Submodule.mem_top, ?_, ?_, ?_⟩⟩
  · ext v
    rw [rhoS_apply T (one_mem _), rhoK_one]
    rfl
  · intro a ha b hb
    ext v
    rw [rhoS_apply T (mul_mem (uj_unit ha) (uj_unit hb)), rhoK_mul T hε (uj_unit ha) (uj_unit hb)]
    change _ = ((rhoS T a (rhoS T b v)) : T.V)
    rw [rhoS_apply T (uj_unit ha), rhoS_apply T (uj_unit hb)]
  · intro g hg v
    change ‖(rhoS T g v : T.V)‖ = ‖(v : T.V)‖
    rw [rhoS_apply T (uj_unit hg), rhoK_norm T hε (uj_unit hg)]
  · intro v
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    have hc : ContinuousOn (fun g => rhoK (k := k) (r := r) T g v) (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k)) :=
      ((HW.torep_isURepOn T).2.2 v).comp kE_cont.continuousOn
        (fun g hg => kE_mem_Kset hε (uj_unit hg))
    refine hc.congr fun g hg => ?_
    exact rhoS_apply T (uj_unit hg) v
  · intro S' _ hS'
    let S'' : Submodule ℂ T.V := S'.map (spanW (k := k) (r := r) T).subtype
    have hle : S'' ≤ spanW (k := k) (r := r) T := by
      rintro _ ⟨v, _, rfl⟩
      exact v.2
    have hst : ∀ h ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ v ∈ S'', rhoK (k := k) (r := r) T h v ∈ S'' := by
      rintro h hh _ ⟨v, hv, rfl⟩
      refine ⟨rhoS T h v, hS' h (unit_ks hh) v hv, ?_⟩
      exact rhoS_apply T hh v
    rcases spanW_irred T hε S'' hle hst with h | h
    · left
      rw [Submodule.eq_bot_iff]
      intro v hv
      have : (v : T.V) ∈ S'' := ⟨v, hv, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact Subtype.ext this
    · right
      rw [eq_top_iff]
      intro v _
      obtain ⟨v', hv', he⟩ := h v.2
      have : v' = v := Subtype.ext he
      rw [← this]; exact hv'
  · refine ⟨⟨T.w, w_mem_spanW T⟩, Submodule.mem_top,
      fun h => HW.KType.w_ne_zero T (congrArg Subtype.val h), ?_⟩
    rw [wtS_iff, ← hΛ']
    exact w_wtK T
  · intro μ v _ hv hwt
    rw [wtS_iff] at hwt
    rw [← hΛ']
    exact wt_cdom T hε v.2 (fun h => hv (Subtype.ext h)) hwt

theorem lowestKType_intertwiner_exists (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) {u : Fin k → ℝ}
    (hΛ : ∀ q : Fin k, Λ (fI k r q) = Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u q)
    {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
    (π' : Matrix (Fin k) (Fin k) ℂ → (Vp →L[ℂ] Vp)) (hπ : Formalism.MainNotions.S.IsHCTypeU k u π') {ξ : Vp}
    (hξ : Formalism.MainNotions.S.IsWtOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k)) π' (Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u) ξ) :
    ∃ (U : Vp ≃ₗᵢ[ℂ] spanW (k := k) (r := r) T) (α : ℂ),
      (∀ g ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ v, rhoK (k := k) (r := r) T g (U v) = (U (π' g v) : T.V)) ∧
        (U ξ : T.V) = α • T.w := by
  obtain ⟨U, hU⟩ := HW.hcTypeU_unique π' (rhoS T) hπ (rhoS_hc T hε hΛ)
  have hint : ∀ g ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ v,
      rhoK (k := k) (r := r) T g (U v) = (U (π' g v) : T.V) := fun g hg v => by
    rw [← rhoS_apply T hg, hU g (unit_uj hg) v]
  have hΛ' : (fun q => Λ (fI k r q)) = Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u := funext hΛ
  have hwt : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) (rhoK (k := k) (r := r) T)
      (Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u) (U ξ : T.V) := by
    intro t ht
    rw [hint _ ht.1, hξ t (unit_uj ht.1), map_smul]
    rfl
  rw [← hΛ'] at hwt
  have hfull := wt_full T hε (U ξ).2 hwt
  have hfix : (fun a : Fin (2 * r + k + 1) => if h : a.val < k then (fun q => Λ (fI k r q)) ⟨a.val, h⟩ else Λ a) = Λ := by
    funext a; split_ifs <;> rfl
  rw [hfix] at hfull
  obtain ⟨α, hα⟩ := eq_smul_highestWeight_of_isWeight T hfull
  exact ⟨U, α, hint, hα⟩

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas
