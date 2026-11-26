module

public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ThresholdStandardLarge

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SymInt
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

abbrev IntAlg (O : Type) [CommRing O] [IsDomain O] (σ : Type*) : Subalgebra O (MvPolynomial σ (KK O)) :=
  (MvPolynomial.mapAlgHom (Algebra.ofId O (KK O)) : MvPolynomial σ O →ₐ[O] MvPolynomial σ (KK O)).range

theorem X_mem_intAlg (O : Type) [CommRing O] [IsDomain O] {σ : Type*} (v : σ) : (X v : MvPolynomial σ (KK O)) ∈ IntAlg O σ := by
  exact (AlgHom.mem_range _).mpr ⟨MvPolynomial.X v, by simp⟩

theorem intPol_le (O : Type) [CommRing O] [IsDomain O] {σ : Type*} {P : MvPolynomial σ (KK O)} (h : P ∈ IntPol O σ) :
    P ∈ IntAlg O σ := by
  obtain ⟨Q, hQ⟩ := LinearMap.mem_range.mp h
  exact (AlgHom.mem_range _).mpr ⟨Q, hQ⟩

theorem inA_of_mem (O : Type) [CommRing O] [IsDomain O] {σ : Type*} {P : MvPolynomial σ (KK O)} (h : P ∈ IntAlg O σ) :
    InA (O := O) P := by
  obtain ⟨Q, rfl⟩ := (AlgHom.mem_range _).mp h
  unfold InA
  intro m
  exact ⟨Q.coeff m, by simp [MvPolynomial.mapAlgHom_apply, MvPolynomial.coeff_map]⟩

theorem rename_mem_intAlg (O : Type) [CommRing O] [IsDomain O] {σ τ : Type*} (f : σ → τ) {P : MvPolynomial σ (KK O)}
    (h : P ∈ IntAlg O σ) : rename f P ∈ IntAlg O τ := by
  obtain ⟨Q, rfl⟩ := (AlgHom.mem_range _).mp h
  exact (AlgHom.mem_range _).mpr ⟨rename f Q, by simp [MvPolynomial.mapAlgHom_apply, MvPolynomial.map_rename]⟩

theorem aeval_mem_intAlg (O : Type) [CommRing O] [IsDomain O] {σ τ : Type*} (f : σ → MvPolynomial τ (KK O))
    (hf : ∀ v, f v ∈ IntAlg O τ) {P : MvPolynomial σ (KK O)} (h : P ∈ IntAlg O σ) : aeval f P ∈ IntAlg O τ := by
  obtain ⟨Q, rfl⟩ := (AlgHom.mem_range _).mp h
  have e : (MvPolynomial.mapAlgHom (Algebra.ofId O (KK O)) : MvPolynomial σ O →ₐ[O] MvPolynomial σ (KK O)) Q =
      MvPolynomial.map (algebraMap O (KK O)) Q := rfl
  rw [e, MvPolynomial.aeval_map_algebraMap]
  clear h e
  induction Q using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.aeval_C]; exact Subalgebra.algebraMap_mem _ a
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p v hp => rw [map_mul, MvPolynomial.aeval_X]; exact mul_mem hp (hf v)

theorem ssz_le_intAlg (O : Type) [CommRing O] [IsDomain O] {N r : ℕ} [NeZero r] (D : BlockData N) :
    ∀ x ∈ D.SSZ O (r := r), x ∈ IntAlg O (BVar N r D.T.t) := by
  intro x hx
  unfold BlockData.SSZ at hx
  refine Submodule.span_induction (p := fun x _ => x ∈ IntAlg O (BVar N r D.T.t)) ?_ ?_ ?_ ?_ hx
  · intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨j, jp, _, y, hy, g0, hg0, rfl⟩ := hx
    have hX := fun v => X_mem_intAlg O (σ := BVar N r D.T.t) v
    have hE : ∀ i, D.Ehat O (r := r) i ∈ IntAlg O (BVar N r D.T.t) := fun i => by
      unfold BlockData.Ehat
      exact (IntAlg O _).add_mem ((IntAlg O _).mul_mem (hX _) (hX _))
        ((IntAlg O _).sum_mem fun c _ => (IntAlg O _).mul_mem (hX _) (hX _))
    have hP : D.Eplus O (r := r) ∈ IntAlg O (BVar N r D.T.t) := by
      unfold BlockData.Eplus
      exact (IntAlg O _).add_mem ((IntAlg O _).mul_mem (hX _) (hX _))
        ((IntAlg O _).sum_mem fun c _ => (IntAlg O _).mul_mem (hX _) (hX _))
    refine (IntAlg O _).mul_mem ((IntAlg O _).mul_mem ((IntAlg O _).mul_mem ((IntAlg O _).mul_mem
      ((IntAlg O _).mul_mem ((IntAlg O _).prod_mem fun i _ => (IntAlg O _).pow_mem (hE i) _)
        ((IntAlg O _).pow_mem hP _)) ((IntAlg O _).prod_mem fun i _ => (IntAlg O _).pow_mem (hX _) _))
      ((IntAlg O _).pow_mem (hX _) _)) (rename_mem_intAlg O _ (intPol_le O hy.2))) (intPol_le O hg0.2)
  · exact (IntAlg O _).zero_mem
  · intro x y _ _ hx hy; exact (IntAlg O _).add_mem hx hy
  · intro a x _ hx; exact (IntAlg O _).smul_mem hx a

theorem symIntAt (C0 CE1 CE2 : ℝ) : SymIntAt C0 CE1 CE2 := by
  intro X _ O _ _ mm β s hs
  apply inA_of_mem
  unfold symFam
  refine (IntAlg O _).prod_mem fun j _ => ?_
  unfold ioBlock
  have hX := fun v => X_mem_intAlg O (σ := (X.TT × Bool) × Fin (X.m + 1)) v
  refine (IntAlg O _).mul_mem ((IntAlg O _).mul_mem ?_ ?_) ?_
  · unfold digitMon
    exact (IntAlg O _).prod_mem fun i _ => (IntAlg O _).prod_mem fun c _ =>
      (IntAlg O _).mul_mem ((IntAlg O _).pow_mem (hX _) _) ((IntAlg O _).pow_mem (hX _) _)
  · unfold sTopMon
    refine (IntAlg O _).prod_mem fun i _ => ?_
    split_ifs
    · exact (IntAlg O _).mul_mem ((IntAlg O _).pow_mem (hX _) _) ((IntAlg O _).pow_mem (hX _) _)
    · exact (IntAlg O _).one_mem
  · have hsj : s j ∈ IntAlg O (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) :=
      ssz_le_intAlg O (r := X.m)
        (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) mm (β j)) (s j) (hs j)
    exact aeval_mem_intAlg O _ (fun v => (IntAlg O _).pow_mem (hX _) _) hsj

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.NotKept
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem nk_b_up (r y : ℕ) : (sdXi r y : ℝ) ≤ ((y : ℝ) + r) ^ (r - 1) * ((r - 1).factorial : ℝ)⁻¹ := by
  unfold sdXi
  have h := Nat.choose_le_pow_div (α := ℝ) (r - 1) (y + r - 1)
  rw [div_eq_mul_inv] at h
  refine h.trans ?_
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  have h1 : ((y + r - 1 : ℕ) : ℝ) ≤ ((y + r : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le _ _
  exact h1.trans_eq (by push_cast; ring)

theorem nk_b_low (r y : ℕ) (hr : 1 ≤ r) : (y : ℝ) ^ (r - 1) * ((r - 1).factorial : ℝ)⁻¹ ≤ (sdXi r y : ℝ) := by
  unfold sdXi
  have h := Nat.pow_le_choose (α := ℝ) (r - 1) (y + r - 1)
  have e : y + r - 1 + 1 - (r - 1) = y + 1 := by omega
  rw [e, div_eq_mul_inv] at h
  refine le_trans ?_ h
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  push_cast
  linarith

theorem nk_sdXi_le_sd (m y : ℕ) (hm : 1 ≤ m) : sdXi m y ≤ sd m y := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  unfold sdXi sd
  have e1 : y + (n + 1) - 1 = y + n := by omega
  have e2 : n + 1 - 1 = n := by omega
  have e3 : y + (n + 1) = y + n + 1 := by omega
  rw [e1, e2, e3, Nat.choose_succ_succ]
  exact Nat.le_add_right _ _

theorem nk_core {s : ℕ} (r : ℕ) (hr : 1 ≤ r) (L A : ℕ) (R n Ai Ci : Fin s → ℕ) (θ : ℝ) (hθ : 0 ≤ θ)
    (H : ((L : ℝ) + r) * (∏ i, ((R i : ℝ) + r)) * (∏ i, ((n i : ℝ) + r)) ≤
      θ * ((A : ℝ) * (∏ i, (Ai i : ℝ)) * ∏ i, (Ci i : ℝ))) :
    (sdXi r L : ℝ) * (∏ i, (sdXi r (R i) : ℝ)) * (∏ i, (sdXi r (n i) : ℝ)) ≤
      θ ^ (r - 1) * ((sdXi r A : ℝ) * (∏ i, (sdXi r (Ai i) : ℝ)) * ∏ i, (sdXi r (Ci i) : ℝ)) := by
  set f : ℝ := ((r - 1).factorial : ℝ)⁻¹ with hf
  have hf0 : 0 ≤ f := by positivity
  have up : (sdXi r L : ℝ) * (∏ i, (sdXi r (R i) : ℝ)) * (∏ i, (sdXi r (n i) : ℝ)) ≤
      (((L : ℝ) + r) ^ (r - 1) * f) * (∏ i, (((R i : ℝ) + r) ^ (r - 1) * f)) *
        (∏ i, (((n i : ℝ) + r) ^ (r - 1) * f)) := by
    apply mul_le_mul (mul_le_mul (nk_b_up r L)
      (Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => nk_b_up r (R i))) (by positivity) (by positivity))
      (Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => nk_b_up r (n i))) (by positivity) (by positivity)
  have low : (((A : ℝ)) ^ (r - 1) * f) * (∏ i, ((Ai i : ℝ) ^ (r - 1) * f)) * (∏ i, ((Ci i : ℝ) ^ (r - 1) * f)) ≤
      (sdXi r A : ℝ) * (∏ i, (sdXi r (Ai i) : ℝ)) * ∏ i, (sdXi r (Ci i) : ℝ) := by
    apply mul_le_mul (mul_le_mul (nk_b_low r A hr)
      (Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => nk_b_low r (Ai i) hr)) (by positivity) (by positivity))
      (Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => nk_b_low r (Ci i) hr)) (by positivity) (by positivity)
  have e1 : (((L : ℝ) + r) ^ (r - 1) * f) * (∏ i, (((R i : ℝ) + r) ^ (r - 1) * f)) *
        (∏ i, (((n i : ℝ) + r) ^ (r - 1) * f)) =
      (((L : ℝ) + r) * (∏ i, ((R i : ℝ) + r)) * (∏ i, ((n i : ℝ) + r))) ^ (r - 1) *
        (f * (∏ _i : Fin s, f) * ∏ _i : Fin s, f) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow, mul_pow, mul_pow]
    ring
  have e2 : (((A : ℝ)) ^ (r - 1) * f) * (∏ i, ((Ai i : ℝ) ^ (r - 1) * f)) * (∏ i, ((Ci i : ℝ) ^ (r - 1) * f)) =
      ((A : ℝ) * (∏ i, (Ai i : ℝ)) * ∏ i, (Ci i : ℝ)) ^ (r - 1) * (f * (∏ _i : Fin s, f) * ∏ _i : Fin s, f) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow, mul_pow, mul_pow]
    ring
  have hc : 0 ≤ f * (∏ _i : Fin s, f) * ∏ _i : Fin s, f := by positivity
  have hP : 0 ≤ ((L : ℝ) + r) * (∏ i, ((R i : ℝ) + r)) * (∏ i, ((n i : ℝ) + r)) := by positivity
  have hpow := pow_le_pow_left₀ hP H (r - 1)
  rw [mul_pow θ] at hpow
  calc _ ≤ _ := up
    _ = _ := e1
    _ ≤ (θ ^ (r - 1) * ((A : ℝ) * (∏ i, (Ai i : ℝ)) * ∏ i, (Ci i : ℝ)) ^ (r - 1)) *
        (f * (∏ _i : Fin s, f) * ∏ _i : Fin s, f) := mul_le_mul_of_nonneg_right hpow hc
    _ = θ ^ (r - 1) * (((A : ℝ)) ^ (r - 1) * f * (∏ i, ((Ai i : ℝ) ^ (r - 1) * f)) *
        (∏ i, ((Ci i : ℝ) ^ (r - 1) * f))) := by rw [e2]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left low (by positivity)

def WtBoundAt : Prop :=
  ∀ (s r : ℕ) [NeZero r] (A : ℕ) (Ai Ci : Fin s → ℕ) (mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ) (lam : Fin r → ℤ),
    2 * s + 1 ≤ r → IsPair A Ai Ci mu lam →
    wdim lam ≤ (sdXi r (lam 0).toNat : ℚ) * (∏ i : Fin s, (sdXi r (pairRho mu i).toNat : ℚ)) *
      ∏ i : Fin s, (sdXi r (pairN (s := s) lam i).toNat : ℚ)

def BracketAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ),
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      ∀ A : ℕ, ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * (1 - X.N1 * X.La C0 / X.k) ≤ (A : ℝ) →
        (A : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) →
        ∀ mu lam, IsPair A (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) mu lam →
          ¬ KeptPair X.p (X.La C0) (r := X.m) (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) mu lam →
          ∃ θ : ℝ, 0 ≤ θ ∧ θ ^ (X.m - 1) ≤ Real.exp (2 - X.La C0 / 5) ∧
            (((lam 0).toNat : ℝ) + X.m) * (∏ i : Fin (segS X.TT j), (((pairRho mu i).toNat : ℝ) + X.m)) *
                (∏ i : Fin (segS X.TT j), (((pairN (s := segS X.TT j) lam i).toNat : ℝ) + X.m)) ≤
              θ * ((A : ℝ) * (∏ i, (clA C0 CE1 CE2 X j rz ry i : ℝ)) * ∏ i, (clC C0 CE1 CE2 X j rz ry i : ℝ))

def RestBracket : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => BracketAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

theorem nk_prod_le_dimMM {s : ℕ} (m : ℕ) (hm : 1 ≤ m) (A : ℕ) (Ai Ci : Fin s → ℕ) :
    (sdXi m A : ℝ) * (∏ i, (sdXi m (Ai i) : ℝ)) * (∏ i, (sdXi m (Ci i) : ℝ)) ≤ (dimMM (m + 1) (A : ℤ) Ai Ci : ℝ) := by
  unfold dimMM
  simp only [tl_symDim_nat]
  push_cast
  rw [Finset.prod_mul_distrib, ← mul_assoc]
  have h : ∀ y : ℕ, (sdXi m y : ℝ) ≤ (sd m y : ℝ) := fun y => by exact_mod_cast nk_sdXi_le_sd m y hm
  apply mul_le_mul (mul_le_mul (h A) (Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => h (Ai i)))
    (by positivity) (by positivity)) (Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => h (Ci i)))
    (by positivity) (by positivity)

theorem notKeptWt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hW : WtBoundAt)
    (hB : BracketAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) : NotKeptWtAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ hD hI hc j rz ry hd A hA1 hA2 mu lam hp hk
  obtain ⟨θ, hθ, hθp, hbr⟩ := hB X hD hI hc j rz ry hd A hA1 hA2 mu lam hp hk
  have hm1 : 1 ≤ X.m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne X.m)
  have hroom : 2 * segS X.TT j + 1 ≤ X.m := by
    obtain ⟨⟨-, -, -, -, h5, -, h7, -⟩, -⟩ := hI
    have := (h5 j).2
    omega
  have h1 := hW (segS X.TT j) X.m A _ _ mu lam hroom hp
  have h1' : ((wdim lam : ℚ) : ℝ) ≤ (sdXi X.m (lam 0).toNat : ℝ) *
      (∏ i : Fin (segS X.TT j), (sdXi X.m (pairRho mu i).toNat : ℝ)) *
      ∏ i : Fin (segS X.TT j), (sdXi X.m (pairN (s := segS X.TT j) lam i).toNat : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr h1
    push_cast at this
    exact this
  have h2 := nk_core X.m hm1 (lam 0).toNat A (fun i => (pairRho mu i).toNat)
    (fun i => (pairN (s := segS X.TT j) lam i).toNat) (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) θ hθ hbr
  have h3 := nk_prod_le_dimMM X.m hm1 A (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry)
  have hT0 : (0 : ℝ) ≤ (sdXi X.m A : ℝ) * (∏ i, (sdXi X.m (clA C0 CE1 CE2 X j rz ry i) : ℝ)) *
      (∏ i, (sdXi X.m (clC C0 CE1 CE2 X j rz ry i) : ℝ)) := by positivity
  have hbig : (1 : ℝ) ≤ (8 * (X.a : ℝ) + X.k) ^ ((2 * X.N1 + 2) ^ 2) := by
    apply one_le_pow₀
    have : (0 : ℝ) ≤ (X.a : ℝ) := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ (X.m : ℝ) := Nat.cast_nonneg _
    unfold Loc.k
    linarith
  have hexp : 0 < Real.exp (2 - X.La C0 / 5) := Real.exp_pos _
  have hdim : (0 : ℝ) ≤ (dimMM (X.m + 1) (A : ℤ) (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) : ℝ) :=
    Nat.cast_nonneg _
  calc ((wdim lam : ℚ) : ℝ) ≤ _ := h1'
    _ ≤ _ := h2
    _ ≤ Real.exp (2 - X.La C0 / 5) * ((sdXi X.m A : ℝ) * (∏ i, (sdXi X.m (clA C0 CE1 CE2 X j rz ry i) : ℝ)) *
        (∏ i, (sdXi X.m (clC C0 CE1 CE2 X j rz ry i) : ℝ))) := mul_le_mul_of_nonneg_right hθp hT0
    _ ≤ Real.exp (2 - X.La C0 / 5) *
        (dimMM (X.m + 1) (A : ℤ) (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) : ℝ) :=
        mul_le_mul_of_nonneg_left h3 hexp.le
    _ ≤ Real.exp (2 - X.La C0 / 5) * (8 * (X.a : ℝ) + X.k) ^ ((2 * X.N1 + 2) ^ 2) *
        (dimMM (X.m + 1) (A : ℤ) (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hdim
        nlinarith [hexp, hbig]

theorem restNotKeptWt_of (hW : WtBoundAt) (hB : RestBracket) : RestNotKeptWt :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h => notKeptWt_of hW h) hB

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SettingCharZeroAt
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.L2.G.Model Formalism.L2.G.Model.TS

def SettingCharZeroAt : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ jO w → CharZero Kf ∧ ¬ IsUnit ((p : ℕ) : O)

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.AiAddMulLeA0
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem coarse_ratio_small {Al Ai Pl Pi bl bi b' be k p : ℝ} (hAl : 0 ≤ Al) (hb : 0 < b') (_hbe0 : 0 ≤ be) (hbe : be ≤ 1 / 12)
    (hPi : 0 < Pi) (hp : 0 < p) (hP : p * Pi ≤ Pl) (h1 : Al * Pl ≤ bl) (h2 : bl ≤ b' * (1 + be))
    (h3 : bi - k * Pi < Ai * Pi) (h4 : b' * (1 - be) ≤ bi) : Al ≤ 2 * (Ai + k) / p := by
  rw [le_div_iff₀ hp]
  have e1 : Al * (p * Pi) ≤ Al * Pl := mul_le_mul_of_nonneg_left hP hAl
  have e2 : b' * be ≤ b' * (1 / 12) := mul_le_mul_of_nonneg_left hbe hb.le
  have e3 : Al * p * Pi ≤ 2 * (Ai + k) * Pi := by nlinarith
  exact le_of_mul_le_mul_right e3 hPi

theorem Ai_add_mul_le_A0 {Ai A0 de ε k p N1 La s : ℝ} (hAi : 0 ≤ Ai) (hA : Ai * (1 + de) < A0) (hde : 40 * ε ≤ de)
    (hde6 : de < 1 / 6) (hε : ε = N1 * La / k) (hk : 5 ≤ k) (hkA : k ≤ A0) (hp : k ^ 2 ≤ p) (hLa : 1 ≤ La)
    (hN1 : 1 ≤ N1) (_hs0 : 0 ≤ s) (hs : s ≤ N1) :
    Ai + s * (2 * (Ai + k) / p + 2 * La * A0 / k) ≤ A0 := by
  have hk0 : 0 < k := by linarith
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  have hA0 : 0 < A0 := by linarith
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hde0 : 0 ≤ de := by linarith
  have hAiA : Ai ≤ A0 := by nlinarith

  have h1 : A0 * de < (A0 - Ai) * (1 + de) := by nlinarith
  have h2 : (A0 - Ai) * (1 + de) ≤ (A0 - Ai) * (7 / 6) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h3 : A0 * (40 * ε) ≤ A0 * de := mul_le_mul_of_nonneg_left hde hA0.le
  have h4 : 34 * (ε * A0) ≤ A0 - Ai := by nlinarith

  have c1 : 2 * (Ai + k) / p ≤ 4 * A0 / k ^ 2 := by
    rw [div_le_div_iff₀ hp0 (by positivity)]
    have : 2 * (Ai + k) ≤ 4 * A0 := by linarith
    calc 2 * (Ai + k) * k ^ 2 ≤ 4 * A0 * k ^ 2 := mul_le_mul_of_nonneg_right this (by positivity)
      _ ≤ 4 * A0 * p := mul_le_mul_of_nonneg_left hp (by positivity)
  have c2 : 4 * A0 / k ^ 2 ≤ La * A0 / k := by
    rw [div_le_div_iff₀ (by positivity) hk0]
    have : 4 * A0 * k ≤ La * A0 * k * k := by
      have : 4 * A0 ≤ La * A0 * k := by nlinarith [mul_le_mul hLa hk (by norm_num) (by linarith)]
      nlinarith
    nlinarith
  have c3 : 2 * (Ai + k) / p + 2 * La * A0 / k ≤ 3 * (La * A0 / k) := by
    have : 2 * La * A0 / k = 2 * (La * A0 / k) := by ring
    linarith
  have c30 : 0 ≤ La * A0 / k := by positivity
  have c4 : s * (2 * (Ai + k) / p + 2 * La * A0 / k) ≤ N1 * (3 * (La * A0 / k)) :=
    mul_le_mul hs c3 (by positivity) (by linarith)
  have c5 : N1 * (3 * (La * A0 / k)) = 3 * (ε * A0) := by rw [hε]; ring
  have c6 : 0 ≤ ε * A0 := by positivity
  linarith

variable {C0 Cde CE1 CE2 H : ℝ} {X : Loc}

theorem partial_width_le_cap [NeZero X.m] (hH : 1 ≤ H) (h : Std C0 Cde CE1 CE2 H X) (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) (hK : Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b)
    (i : Fin (segS X.TT j)) (hi : i.val < (X.seg C0 CE1 CE2 j).sigma) (n : ℕ) (hn : n ≤ i.val + 1) :
    (∑ l : Fin (segS X.TT j), if l.val < i.val + 1 then (b.w l : ℤ) else 0) ≤ cap X.p (X.seg C0 CE1 CE2 j) b n := by
  obtain ⟨hd, -, hSt, -⟩ := hK
  set S := X.seg C0 CE1 CE2 j with hS

  have hk5 := h.k5
  have hk0 : 0 < X.k := by linarith
  have hp0 : (0 : ℝ) < X.p := by linarith [h.p1]
  have hde : 40 * eps X C0 ≤ X.de C0 Cde := by
    have := h.LaK
    unfold eps
    calc 40 * (X.N1 * X.La C0 / X.k) = 40 * X.N1 * X.La C0 / X.k := by ring
      _ ≤ _ := this
  have hbe12 : be X C0 ≤ 1 / 12 := by
    have h1 := h.beLe
    have h2 := h.de6
    have h3 : 0 ≤ 18 * X.N1 * X.La C0 / X.k := by
      have := h.La1
      positivity
    linarith
  have hA0k : X.k ≤ (S.A0 X.p : ℝ) := by
    refine le_trans ?_ (h.half_ratio_le_segment_base_of_std j)
    have hQ0 : 0 < X.Q := by linarith [h.Q1]
    rw [le_div_iff₀ (by positivity)]
    have h1 := h.kQ hH
    have h2 := h.ba
    have h3 : X.k * (2 * X.Q) ≤ X.k ^ 3 * X.Q := by
      have hk2 : (2 : ℝ) ≤ X.k ^ 2 := by nlinarith
      calc X.k * (2 * X.Q) = (X.k * X.Q) * 2 := by ring
        _ ≤ (X.k * X.Q) * X.k ^ 2 := mul_le_mul_of_nonneg_left hk2 (mul_pos hk0 hQ0).le
        _ = X.k ^ 3 * X.Q := by ring
    linarith
  have hcb : ∀ l : Fin (segS X.TT j),
      (coarseA X.p S b l : ℝ) * ((X.p ^ (segG X.TT j - (segDists X.TT j).get l) : ℕ) : ℝ) ≤ X.bT (segPos X.TT j l) ∧
      (X.bT (segPos X.TT j l) : ℝ) - ((X.m : ℝ) + 1) * ((X.p ^ (segG X.TT j - (segDists X.TT j).get l) : ℕ) : ℝ) <
        (coarseA X.p S b l : ℝ) * ((X.p ^ (segG X.TT j - (segDists X.TT j).get l) : ℕ) : ℝ) := fun l =>
    coarse_bounds (X.bT (segPos X.TT j l)) (X.p ^ (segG X.TT j - (segDists X.TT j).get l)) (b.rz l)
      (fun c => (hd.1 l c).1) (hd.2.1 l).1 (hd.2.1 l).2
  have hAi := (coarse_degree_alternative hH h j b hd i).1 hi
  set c1 : ℝ := 2 * ((coarseA X.p S b i : ℝ) + X.k) / X.p with hc1
  set c2 : ℝ := 2 * X.La C0 * (S.A0 X.p : ℝ) / X.k with hc2
  have hc10 : 0 ≤ c1 := by rw [hc1]; positivity
  have hc20 : 0 ≤ c2 := by
    have := h.La1
    have : (0 : ℝ) ≤ (S.A0 X.p : ℝ) := by linarith
    rw [hc2]; positivity
  have hterm : ∀ l : Fin (segS X.TT j),
      ((if l.val < i.val + 1 then ((coarseA X.p S b l : ℤ) + (b.sg l : ℤ)) else 0 : ℤ) : ℝ) ≤
        (if l = i then (coarseA X.p S b i : ℝ) else 0) + (c1 + c2) := by
    intro l
    by_cases hl : l.val < i.val + 1
    · rw [if_pos hl]
      have hlσ : l.val < S.sigma := by omega
      have hsg : (b.sg l : ℝ) ≤ c2 := (hSt l hlσ).2.2.2.2
      push_cast
      by_cases hli : l = i
      · rw [if_pos hli, hli]
        rw [hli] at hsg
        linarith
      · rw [if_neg hli]
        have hlt : l < i := by
          rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hl) with h' | h'
          · exact h'
          · exact absurd (Fin.ext h') hli
        have hdl := dist_strictMono X.TT j hlt
        have hdi := (dist_pos_lt X.TT j i).2
        have hPP : X.p * X.p ^ (segG X.TT j - (segDists X.TT j).get i) ≤
            X.p ^ (segG X.TT j - (segDists X.TT j).get l) := by
          rw [← pow_succ']
          exact Nat.pow_le_pow_right (by have := h.p5; omega) (by omega)
        have hPP' : (X.p : ℝ) * ((X.p ^ (segG X.TT j - (segDists X.TT j).get i) : ℕ) : ℝ) ≤
            ((X.p ^ (segG X.TT j - (segDists X.TT j).get l) : ℕ) : ℝ) := by exact_mod_cast hPP
        have := coarse_ratio_small (k := X.k) (Nat.cast_nonneg _) h.bpos h.be0 hbe12 (h.levels j i).1 hp0 hPP' (hcb l).1
          (h.winB _ (pos_mem X.TT j l).1).2 (hcb i).2 (h.winB _ (pos_mem X.TT j i).1).1
        linarith
    · rw [if_neg hl]
      push_cast
      split_ifs
      · have : (0 : ℝ) ≤ (coarseA X.p S b i : ℝ) := Nat.cast_nonneg _
        linarith
      · linarith
  have hsumR : ((∑ l : Fin (segS X.TT j),
      (if l.val < i.val + 1 then ((coarseA X.p S b l : ℤ) + (b.sg l : ℤ)) else 0) : ℤ) : ℝ) ≤ (S.A0 X.p : ℝ) := by
    rw [Int.cast_sum]
    refine le_trans (Finset.sum_le_sum fun l _ => hterm l) ?_
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ i), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hsN : ((segS X.TT j : ℕ) : ℝ) ≤ X.N1 := by exact_mod_cast (h.segB j).2
    have hpk : X.k ^ 2 ≤ (X.p : ℝ) := by
      have h1 := h.pk
      have h2 := h.Y1
      have : X.k ^ 2 * 1 ≤ X.k ^ 2 * X.Y ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      linarith
    exact Ai_add_mul_le_A0 (ε := eps X C0) (Nat.cast_nonneg _) hAi hde h.de6 rfl hk5 hA0k hpk h.La1 h.one_le_level_alt (Nat.cast_nonneg _) hsN
  have hsumZ : (∑ l : Fin (segS X.TT j),
      (if l.val < i.val + 1 then ((coarseA X.p S b l : ℤ) + (b.sg l : ℤ)) else 0)) ≤ S.A0 X.p := by
    exact_mod_cast hsumR

  unfold cap
  have hcmp : ∀ l : Fin (segS X.TT j),
      (if l.val < i.val + 1 then (b.w l : ℤ) else 0) ≤
        (if l.val < i.val + 1 then ((coarseA X.p S b l : ℤ) + (b.sg l : ℤ)) else 0) * 0 +
        ((if (l : ℕ) < n then ((coarseA X.p S b l : ℤ) - (oEff S b l : ℤ)) else 0) +
          (if l.val < i.val + 1 then ((coarseA X.p S b l : ℤ) + (b.sg l : ℤ)) else 0)) := by
    intro l
    by_cases hl : l.val < i.val + 1
    · have hlσ : l.val < S.sigma := by omega
      have hw : (b.w l : ℤ) ≤ (coarseA X.p S b l : ℤ) := by exact_mod_cast (hSt l hlσ).2.1
      have hsg0 : (0 : ℤ) ≤ (b.sg l : ℤ) := Int.natCast_nonneg _
      have ho : (oEff S b l : ℤ) = (b.w l : ℤ) + (b.sg l : ℤ) := by
        unfold oEff
        rw [if_pos hlσ]
        push_cast
        ring
      rw [if_pos hl, if_pos hl]
      split_ifs
      · rw [ho]; linarith
      · linarith
    · have hln : ¬ (l : ℕ) < n := by omega
      rw [if_neg hl, if_neg hl, if_neg hln]
      simp
  have hs := Finset.sum_le_sum (s := Finset.univ) fun l _ => hcmp l
  simp only [mul_zero, zero_add] at hs
  rw [Finset.sum_add_distrib] at hs
  linarith

theorem top_rows_bound_holds : LeadingRowsBeyondThreshold :=
  TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1)
    fun _ _ _ _ _ _ _ _ _ _ hCc hC0 _ h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 => by
      intro X _ hD hI hc j b hK i hi
      have hs := std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc
      exact ⟨partial_width_le_cap le_rfl hs j b hK i hi i.val (by omega), partial_width_le_cap le_rfl hs j b hK i hi (i.val + 1) le_rfl⟩

end Formalism.MainNotions.ColumnSystems.Pf
end
end
