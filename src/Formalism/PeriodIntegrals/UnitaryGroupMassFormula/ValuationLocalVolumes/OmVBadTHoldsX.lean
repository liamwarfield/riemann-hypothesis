module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVMemEFHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SiegelWeilVolume.AddEquivAddHaarCharEqOne
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOfFfX
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.CountGen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.ProdInertClosed

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FFInertBHolds
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FFSplitBHolds
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.DcountSplit
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FfHSelfOfSnd
noncomputable section

namespace PI.OmVe

open PI.VolStabSW Matrix

section split

variable {k : Type} [Field k] {M : ℕ} (J : Matrix (Fin M) (Fin M) (k × k))

theorem ffH_fst' (y x : Fin M → k × k) :
    (ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J y x).1 = ∑ i, ∑ l, ((RingEquiv.prodComm (R := k) (S := k)).toRingHom (y i) * J i l).1 * (x l).1 := by
  simp only [ffH, Prod.fst_sum, Prod.fst_mul]

theorem ffH_snd' (y x : Fin M → k × k) :
    (ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J y x).2 = ∑ i, ∑ l, ((RingEquiv.prodComm (R := k) (S := k)).toRingHom (y i) * J i l).2 * (x l).2 := by
  simp only [ffH, Prod.snd_sum, Prod.snd_mul]

theorem ffH_self_of_snd (x : Fin M → k × k) (h : ∀ l, (x l).2 = 0) : ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J x x = 0 := by
  refine Prod.ext ?_ ?_
  · rw [ffH_fst']
    simp [h]
  · rw [ffH_snd']
    simp [h]

theorem ffH_self_of_fst (x : Fin M → k × k) (h : ∀ l, (x l).1 = 0) : ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J x x = 0 := by
  refine Prod.ext ?_ ?_
  · rw [ffH_fst']
    simp [h]
  · rw [ffH_snd']
    simp [h]

theorem notFree_iff (x : Fin M → k × k) :
    (¬ ∀ c : k × k, c • x = 0 → c = 0) ↔ (∀ l, (x l).1 = 0) ∨ (∀ l, (x l).2 = 0) := by
  constructor
  · intro h
    push_neg at h
    obtain ⟨c, hc, hne⟩ := h
    by_cases h1 : c.1 = 0
    · right
      have h2 : c.2 ≠ 0 := fun h2 => hne (Prod.ext h1 h2)
      intro l
      have hl := congrArg Prod.snd (congrFun hc l)
      simp only [Pi.smul_apply, smul_eq_mul, Prod.snd_mul, Pi.zero_apply, Prod.snd_zero] at hl
      exact (mul_eq_zero.1 hl).resolve_left h2
    · left
      intro l
      have hl := congrArg Prod.fst (congrFun hc l)
      simp only [Pi.smul_apply, smul_eq_mul, Prod.fst_mul, Pi.zero_apply, Prod.fst_zero] at hl
      exact (mul_eq_zero.1 hl).resolve_left h1
  · rintro (h | h) hfree
    · have h1 := hfree (1, 0) (by
        funext l
        refine Prod.ext ?_ ?_ <;> simp [h l])
      simp at h1
    · have h1 := hfree (0, 1) (by
        funext l
        refine Prod.ext ?_ ?_ <;> simp [h l])
      simp at h1

theorem perp_surj {a' : ℕ} (T0 : Matrix (Fin a') (Fin a') (k × k)) (hu : IsUnit T0.det)
    (Y : Fin a' → Fin M → k × k) (hY : ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J Y = T0) (w : Fin a' → k × k) :
    ∃ x : Fin M → k × k, ∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = w j := by
  classical
  set c := T0⁻¹.mulVec w with hc
  refine ⟨fun l => ∑ m, Y m l * c m, fun j => ?_⟩

  have h1 : ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j)
      (fun l => ∑ m, Y m l * c m) = ∑ m, T0 j m * c m := by
    rw [← hY]
    simp only [ffGram, ffH, Finset.mul_sum, Finset.sum_mul]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [h1]
  have h2 : T0.mulVec c = w := by
    rw [hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have h3 := congrFun h2 j
  simpa [Matrix.mulVec, dotProduct] using h3

private theorem natCard_ker_mul_card_pow_eq_of_surjective [Finite k] {a' : ℕ} (B : Matrix (Fin a') (Fin M) k)
    (hB : Function.Surjective B.mulVec) :
    Nat.card {u : Fin M → k // B.mulVec u = 0} * Nat.card k ^ a' = Nat.card k ^ M := by
  classical
  have _ := Fintype.ofFinite k
  have hs : LinearMap.range (Matrix.mulVecLin B) = ⊤ := by
    refine LinearMap.range_eq_top.2 fun v => ?_
    obtain ⟨u, hu⟩ := hB v
    exact ⟨u, by rw [Matrix.mulVecLin_apply, hu]⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin B)
  rw [hs, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at hrn
  have e : {u : Fin M → k // B.mulVec u = 0} ≃ LinearMap.ker (Matrix.mulVecLin B) :=
    Equiv.subtypeEquivRight fun u => by simp [Matrix.mulVecLin_apply]
  rw [Nat.card_congr e]
  simp only [Nat.card_eq_fintype_card]
  rw [Module.card_eq_pow_finrank (K := k) (V := LinearMap.ker (Matrix.mulVecLin B)), ← pow_add]
  congr 1
  omega

theorem card_half_snd [Finite k] {a' : ℕ} (T0 : Matrix (Fin a') (Fin a') (k × k)) (hu : IsUnit T0.det)
    (Y : Fin a' → Fin M → k × k) (hY : ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J Y = T0) :
    Nat.card {x : Fin M → k × k // (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = 0) ∧ ∀ l, (x l).2 = 0} * Nat.card k ^ a' =
      Nat.card k ^ M := by
  classical
  let B : Matrix (Fin a') (Fin M) k := fun j l =>
    ∑ i, ((RingEquiv.prodComm (R := k) (S := k)).toRingHom (Y j i) * J i l).1
  have hB : ∀ (x : Fin M → k × k) j,
      (ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x).1 =
        B.mulVec (fun l => (x l).1) j := by
    intro x j
    rw [ffH_fst']
    simp only [Matrix.mulVec, dotProduct, B, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hsurj : Function.Surjective B.mulVec := by
    intro w'
    obtain ⟨x, hx⟩ := perp_surj J T0 hu Y hY (fun j => (w' j, 0))
    exact ⟨fun l => (x l).1, funext fun j => by rw [← hB x j, hx j]⟩
  have e : {x : Fin M → k × k // (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J
      (Y j) x = 0) ∧ ∀ l, (x l).2 = 0} ≃ {u : Fin M → k // B.mulVec u = 0} :=
    { toFun := fun x => ⟨fun l => (x.1 l).1, funext fun j => by
        rw [← hB, x.2.1 j]
        rfl⟩
      invFun := fun u => ⟨fun l => (u.1 l, 0), fun j => by
        refine Prod.ext ?_ ?_
        · rw [hB]
          exact congrFun u.2 j
        · rw [ffH_snd']
          simp, fun l => rfl⟩
      left_inv := fun x => Subtype.ext (funext fun l => Prod.ext rfl (x.2.2 l).symm)
      right_inv := fun u => rfl }
  rw [Nat.card_congr e]
  exact natCard_ker_mul_card_pow_eq_of_surjective B hsurj

theorem card_half_fst [Finite k] {a' : ℕ} (T0 : Matrix (Fin a') (Fin a') (k × k)) (hu : IsUnit T0.det)
    (Y : Fin a' → Fin M → k × k) (hY : ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J Y = T0) :
    Nat.card {x : Fin M → k × k // (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = 0) ∧ ∀ l, (x l).1 = 0} * Nat.card k ^ a' =
      Nat.card k ^ M := by
  classical
  let B : Matrix (Fin a') (Fin M) k := fun j l =>
    ∑ i, ((RingEquiv.prodComm (R := k) (S := k)).toRingHom (Y j i) * J i l).2
  have hB : ∀ (x : Fin M → k × k) j,
      (ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x).2 =
        B.mulVec (fun l => (x l).2) j := by
    intro x j
    rw [ffH_snd']
    simp only [Matrix.mulVec, dotProduct, B, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hsurj : Function.Surjective B.mulVec := by
    intro w'
    obtain ⟨x, hx⟩ := perp_surj J T0 hu Y hY (fun j => (0, w' j))
    exact ⟨fun l => (x l).2, funext fun j => by rw [← hB x j, hx j]⟩
  have e : {x : Fin M → k × k // (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J
      (Y j) x = 0) ∧ ∀ l, (x l).1 = 0} ≃ {u : Fin M → k // B.mulVec u = 0} :=
    { toFun := fun x => ⟨fun l => (x.1 l).2, funext fun j => by
        rw [← hB, x.2.1 j]
        rfl⟩
      invFun := fun u => ⟨fun l => (0, u.1 l), fun j => by
        refine Prod.ext ?_ ?_
        · rw [ffH_fst']
          simp
        · rw [hB]
          exact congrFun u.2 j, fun l => rfl⟩
      left_inv := fun x => Subtype.ext (funext fun l => Prod.ext (x.2.2 l).symm rfl)
      right_inv := fun u => rfl }
  rw [Nat.card_congr e]
  exact natCard_ker_mul_card_pow_eq_of_surjective B hsurj

end split

end PI.OmVe
end
end

noncomputable section

namespace PI.OmVe

open PI.VolStabSW Matrix

theorem keySplit (x : ℝ) (hx : x ≠ 0) (n : ℕ) :
    (x ^ 2) ^ (n + 1) - (2 * x ^ (n + 1) - 1) - (x - 1) * (x ^ (2 * n + 1) * (1 - x ^ (-((n + 1 : ℕ) : ℤ)))) =
      x ^ (2 * n + 1) * ((1 - x ^ (-(n : ℤ))) * (1 - x ^ (-((n + 1 : ℕ) : ℤ)))) := by
  rw [_root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast]
  have hxn : x ^ n ≠ 0 := pow_ne_zero _ hx
  have hxn1 : x ^ (n + 1) ≠ 0 := pow_ne_zero _ hx
  field_simp
  ring

theorem dcount_split {k : Type} [Field k] [Finite k] {M : ℕ} (J : Matrix (Fin M) (Fin M) (k × k)) {a' : ℕ}
    (haM : a' ≤ M) (T0 : Matrix (Fin a') (Fin a') (k × k)) (hu : IsUnit T0.det)
    (Y : Fin a' → Fin M → k × k) (hY : ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J Y = T0) :
    Nat.card {x : Fin M → k × k // (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = 0) ∧
      ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J x x = 0 ∧ ¬ ∀ c : k × k, c • x = 0 → c = 0} + 1 =
      2 * Nat.card k ^ (M - a') := by
  classical
  have := Fintype.ofFinite k
  have hk0 : 0 < Nat.card k := Nat.card_pos
  have e2 : Nat.card k ^ M = Nat.card k ^ (M - a') * Nat.card k ^ a' := by
    rw [← pow_add, Nat.sub_add_cancel haM]
  have h1 := card_half_snd J T0 hu Y hY
  have h2 := card_half_fst J T0 hu Y hY
  rw [e2] at h1 h2
  have c1 := Nat.eq_of_mul_eq_mul_right (pow_pos hk0 _) h1
  have c2 := Nat.eq_of_mul_eq_mul_right (pow_pos hk0 _) h2
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at c1 c2 ⊢
  set s1 := Finset.univ.filter (fun x : Fin M → k × k =>
    (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = 0) ∧ ∀ l, (x l).2 = 0)
  set s2 := Finset.univ.filter (fun x : Fin M → k × k =>
    (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = 0) ∧ ∀ l, (x l).1 = 0)
  have hs : Finset.univ.filter (fun x : Fin M → k × k =>
      (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = 0) ∧
      ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J x x = 0 ∧ ¬ ∀ c : k × k, c • x = 0 → c = 0) =
      s1 ∪ s2 := by
    ext x
    simp only [s1, s2, Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
    rw [notFree_iff]
    constructor
    · rintro ⟨hP, _, h | h⟩
      · exact Or.inr ⟨hP, h⟩
      · exact Or.inl ⟨hP, h⟩
    · rintro (⟨hP, h⟩ | ⟨hP, h⟩)
      · exact ⟨hP, ffH_self_of_snd J x h, Or.inr h⟩
      · exact ⟨hP, ffH_self_of_fst J x h, Or.inl h⟩
  have hi : s1 ∩ s2 = {0} := by
    ext x
    simp only [s1, s2, Finset.mem_filter, Finset.mem_inter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨_, h2⟩, ⟨_, h1⟩⟩
      funext l; exact Prod.ext (h1 l) (h2 l)
    · rintro rfl
      exact ⟨⟨fun j => ffH_zero_right _ _ _, fun l => rfl⟩, ⟨fun j => ffH_zero_right _ _ _, fun l => rfl⟩⟩
  have hu2 := Finset.card_union_add_card_inter s1 s2
  rw [hi, Finset.card_singleton, c1, c2] at hu2
  rw [hs, hu2]
  ring

end PI.OmVe
end
end

noncomputable section

namespace PI.OmVe

open PI.VolStabSW Matrix

theorem fFSplitB_holds : PI.OmVd.FFSplitB := by
  intro k _ _ M a haM J hJ hJdet T hT hcor
  obtain ⟨i₀, hrow, hcol, hunit⟩ := hcor
  cases a with
  | zero => exact i₀.elim0
  | succ a' =>
    have hσ : ∀ x : k × k, RingEquiv.prodComm.toRingHom x = x.swap := fun x => rfl
    have hsub : IsUnit (T.submatrix i₀.succAbove i₀.succAbove).det := by
      have := PI.OmVe.det_corOne T i₀ hrow 1
      rw [this, one_mul] at hunit
      exact hunit
    have hinv : ∀ x : k × k, RingEquiv.prodComm.toRingHom (RingEquiv.prodComm.toRingHom x) = x := fun x => by simp [hσ]
    have hJ' : ∀ i j, RingEquiv.prodComm.toRingHom (J j i) = J i j := fun i j => by rw [hσ]; exact hJ i j
    have hdiag : ∀ x : Fin M → k × k, ∃ c : k, PI.VolStabSW.ffH RingEquiv.prodComm.toRingHom J x x = (c, c) := by
      intro x
      have h := PI.OmVe.ffH_herm RingEquiv.prodComm.toRingHom J hinv hJ' x x
      refine ⟨(PI.VolStabSW.ffH RingEquiv.prodComm.toRingHom J x x).1, ?_⟩
      rw [hσ] at h
      ext
      · rfl
      · exact (congrArg Prod.fst h).symm.trans rfl
    have hTs : ∀ i j, ((T.submatrix i₀.succAbove i₀.succAbove) j i).swap = (T.submatrix i₀.succAbove i₀.succAbove) i j := fun i j => hT _ _
    have hY := PI.VolStabSW.fFSplit_holds k M a' (by omega) J hJ hJdet _ hTs hsub
    have hNr : ∀ c : k, c ≠ 0 → (Nat.card { X : Fin (a' + 1) → Fin M → k × k // PI.VolStabSW.ffGram RingEquiv.prodComm.toRingHom J X = T + Matrix.single i₀ i₀ (c, c) } : ℝ) = (∏ i : Fin (a' + 1), ((Nat.card k : ℝ) ^ M - (Nat.card k : ℝ) ^ (i : ℕ))) * (Nat.card k : ℝ) ^ ((a' + 1) * (M - (a' + 1))) := by
      intro c hc
      have hdet : IsUnit (T + Matrix.single i₀ i₀ (c, c)).det := by
        rw [PI.OmVe.det_corOne T i₀ hrow]
        refine IsUnit.mul ?_ hsub
        exact (Prod.isUnit_iff).2 ⟨isUnit_iff_ne_zero.2 hc, isUnit_iff_ne_zero.2 hc⟩
      have hh : ∀ i j, ((T + Matrix.single i₀ i₀ (c, c)) j i).swap = (T + Matrix.single i₀ i₀ (c, c)) i j := by
        intro i j
        rw [Matrix.add_apply, Matrix.add_apply, ← hT i j, Matrix.single_apply, Matrix.single_apply]
        by_cases h1 : i₀ = i <;> by_cases h2 : i₀ = j <;> ext <;> simp [h1, h2] <;> split_ifs <;> rfl
      exact PI.VolStabSW.fFSplit_holds k M (a' + 1) haM J hJ hJdet _ hh hdet
    have key := PI.OmVe.count_gen RingEquiv.prodComm.toRingHom J hinv hJ' T i₀ hrow hcol hunit (by omega) (k := k) (fun c => (c, c)) (fun c d h => by simpa using congrArg Prod.fst h) rfl
    specialize key hdiag
    clear hinv hJ' hdiag hσ
    have hk1 : 1 ≤ Nat.card k := Nat.card_pos
    have hk := key (Nat.card { X : Fin (a' + 1) → Fin M → k × k // PI.VolStabSW.ffGram RingEquiv.prodComm.toRingHom J X = T + Matrix.single i₀ i₀ ((1 : k), (1 : k)) }) (2 * Nat.card k ^ (M - a') - 1)
      (fun c hc => Nat.cast_injective (R := ℝ) ((hNr c hc).trans (hNr 1 one_ne_zero).symm))
      (fun Y hY' => by
        have := PI.OmVe.dcount_split J (by omega) _ hsub Y hY'
        have : 1 ≤ Nat.card k ^ (M - a') := Nat.one_le_pow _ _ hk1
        omega)
    have hN1 := hNr 1 one_ne_zero
    clear key hNr
    rw [Nat.card_prod] at hk
    have hkR := congrArg (fun n : ℕ => (n : ℝ)) hk
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hk1, Nat.cast_one] at hkR
    rw [Nat.cast_sub (by have : 1 ≤ Nat.card k ^ (M - a') := Nat.one_le_pow _ _ hk1; omega)] at hkR
    rw [hY, hN1] at hkR
    push_cast at hkR
    have hq : (1 : ℝ) ≤ Nat.card k := by exact_mod_cast hk1
    generalize ((Nat.card { X : Fin (a' + 1) → Fin M → k × k // PI.VolStabSW.ffGram RingEquiv.prodComm.toRingHom J X = T ∧ LinearIndependent (k × k) X } : ℕ) : ℝ) = C at hkR ⊢
    generalize (Nat.card k : ℝ) = q at hkR hq ⊢
    clear hk hY hN1 hTs hsub hunit hrow hcol hT hJdet hJ
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le haM
    clear haM T J i₀
    have hq0 : q ≠ 0 := by positivity
    have e1 : a' + 1 + r - a' = r + 1 := by omega
    have e2 : a' + 1 + r - (a' + 1) = r := by omega
    have e3 : 2 * (a' + 1 + r) * (a' + 1) - (a' + 1) ^ 2 = (a' + 1) ^ 2 + 2 * r * (a' + 1) := Nat.sub_eq_of_eq_add (by ring)
    have hP := PI.OmVe.prodSplit_closed q hq0 (a' + 1 + r) a' (by omega)
    rw [e1] at hP hkR
    rw [e2] at hkR
    rw [e2, e3]
    simp only [one_pow, one_mul]
    rw [← Finset.insert_Icc_add_one_left_eq_Icc (by omega : r ≤ a' + 1 + r), Finset.prod_insert (by simp), ← Finset.insert_Icc_add_one_left_eq_Icc (by omega : r + 1 ≤ a' + 1 + r), Finset.prod_insert (by simp)]
    rw [Fin.prod_univ_castSucc] at hkR
    simp only [Fin.coe_castSucc, Fin.val_last] at hkR
    rw [hP] at hkR
    have hK := PI.OmVe.keySplit q hq0 r
    have e : q ^ (2 * r + 1) * (1 - q ^ (-((r + 1 : ℕ) : ℤ))) = (q ^ (r + 1) - 1) * q ^ r := by
      rw [_root_.zpow_neg, zpow_natCast]
      field_simp
      ring
    generalize (∏ j ∈ Finset.Icc (r + 1 + 1) (a' + 1 + r), (1 - q ^ (-(j : ℤ)))) = Pi' at hkR ⊢
    generalize (1 - q ^ (-((r + 1 : ℕ) : ℤ))) = B at hK e ⊢
    generalize (1 - q ^ (-(r : ℤ))) = A at hK ⊢
    linear_combination hkR + (Pi' * q ^ ((a' + 1 + r) * a') * q ^ (a' * (r + 1))) * hK + (Pi' * q ^ ((a' + 1 + r) * a') * q ^ (a' * (r + 1)) * (q - 1)) * e

end PI.OmVe
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FFInertBHoldsAlt
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FixedMemRange
noncomputable section

namespace PI.OmVe

open PI.VolStabSW PI.VolStabSW.FFHS PI.OmLocU.CntFF Matrix Polynomial

theorem keyInert (x : ℝ) (hx : x ≠ 0) (n : ℕ) :
    (x ^ 2) ^ (n + 1) - 1 - (x - 1) * (x ^ (2 * n + 1) * (1 - (-1) ^ (n + 1) * x ^ (-((n + 1 : ℕ) : ℤ)))) =
      x ^ (2 * n + 1) * ((1 - (-1) ^ n * x ^ (-(n : ℤ))) * (1 - (-1) ^ (n + 1) * x ^ (-((n + 1 : ℕ) : ℤ)))) := by
  rw [_root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast]
  have hxn : x ^ n ≠ 0 := pow_ne_zero _ hx
  have hxn1 : x ^ (n + 1) ≠ 0 := pow_ne_zero _ hx
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_one_pow, he.add_one.neg_one_pow]
    field_simp
    ring
  · rw [ho.neg_one_pow, ho.add_one.neg_one_pow]
    field_simp
    ring

theorem fixed_mem_range {k K : Type} [Field k] [Fintype k] [Field K] [Fintype K] [DecidableEq K] [Algebra k K]
    (σ : K ≃ₐ[k] K) (h2 : Module.finrank k K = 2) (hne : σ ≠ AlgEquiv.refl) (t : K) (ht : σ t = t) :
    ∃ c : k, t = algebraMap k K c := by
  classical
  haveI : FiniteDimensional k K := inferInstance
  haveI : IsGalois k K := inferInstance
  have hcard : Fintype.card (K ≃ₐ[k] K) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, h2]
  have hall : ∀ τ : K ≃ₐ[k] K, τ = AlgEquiv.refl ∨ τ = σ := by
    intro τ
    by_contra h
    push_neg at h
    have h3 : ({AlgEquiv.refl, σ, τ} : Finset (K ≃ₐ[k] K)).card ≤ 2 := hcard ▸ Finset.card_le_univ _
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm hne, Ne.symm h.1]), Finset.card_pair (Ne.symm h.2)] at h3
    omega
  obtain ⟨c, hc⟩ := (IsGalois.mem_range_algebraMap_iff_fixed t).mpr (fun τ => by
    rcases hall τ with rfl | rfl
    · rfl
    · exact ht)
  exact ⟨c, hc.symm⟩

end PI.OmVe
end
end

noncomputable section

namespace PI.OmVe

open PI.VolStabSW PI.VolStabSW.FFHS PI.OmLocU.CntFF Matrix

theorem fFInertB_holds : PI.OmVd.FFInertB := by
  intro k K _ _ _ _ σ hσ h2 hne M a haM J hJ hdJ T hT hTu
  classical
  obtain ⟨i₀, hr, hc, hu⟩ := hTu
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by have := i₀.pos; omega⟩
  have := Fintype.ofFinite k
  have : Module.Finite k K := Module.finite_of_finrank_pos (by omega)
  have : Finite K := Module.finite_of_finite k
  have := Fintype.ofFinite K
  have hK : Fintype.card K = Fintype.card k ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := k), h2]
  have hσ' : ∀ x, (σ : K →+* K) ((σ : K →+* K) x) = x := fun x => hσ x
  have hJ' : ∀ i j, (σ : K →+* K) (J j i) = J i j := hJ
  have hu0 : IsUnit (T.submatrix i₀.succAbove i₀.succAbove).det := by
    have e := det_corOne T i₀ hr 1
    rw [one_mul] at e
    rw [← e]; exact hu
  have hTt : ∀ c : k, c ≠ 0 →
      (∀ i j, σ ((T + Matrix.single i₀ i₀ (algebraMap k K c)) j i) =
        (T + Matrix.single i₀ i₀ (algebraMap k K c)) i j) ∧
      IsUnit (T + Matrix.single i₀ i₀ (algebraMap k K c)).det := by
    intro c hc0
    refine ⟨fun i j => ?_, ?_⟩
    · rw [Matrix.add_apply, Matrix.add_apply, map_add (f := _), hT, Matrix.single_apply, Matrix.single_apply]
      congr 1
      split_ifs with h1 h2 h2 <;> first | exact AlgEquiv.commutes σ c | exact map_zero σ | (exfalso; tauto)
    · rw [det_corOne T i₀ hr]
      exact (isUnit_iff_ne_zero.2 ((map_ne_zero _).2 hc0)).mul hu0
  have hN : ∀ c : k, c ≠ 0 → Nat.card {X : Fin (a' + 1) → Fin M → K //
      ffGram (σ : K →+* K) J X = T + Matrix.single i₀ i₀ (algebraMap k K c)} =
      Nat.card {X : Fin (a' + 1) → Fin M → K //
        ffGram (σ : K →+* K) J X = T + Matrix.single i₀ i₀ (algebraMap k K 1)} := by
    intro c hc0
    have e1 := fFInert2_holds k K σ hσ h2 hne M (a' + 1) haM J hJ hdJ _ (hTt c hc0).1 (hTt c hc0).2
    have e2 := fFInert2_holds k K σ hσ h2 hne M (a' + 1) haM J hJ hdJ _ (hTt 1 one_ne_zero).1
      (hTt 1 one_ne_zero).2
    exact_mod_cast e1.trans e2.symm
  have hD : ∀ Y : Fin a' → Fin M → K, ffGram (σ : K →+* K) J Y = T.submatrix i₀.succAbove i₀.succAbove →
      Nat.card {x : Fin M → K // (∀ j, ffH (σ : K →+* K) J (Y j) x = 0) ∧ ffH (σ : K →+* K) J x x = 0 ∧
        ¬ ∀ c : K, c • x = 0 → c = 0} = 1 := by
    intro Y _
    rw [Nat.card_eq_one_iff_unique]
    have h0 : ∀ z : Fin M → K, ¬ (∀ c : K, c • z = 0 → c = 0) → z = 0 := fun z hz => by
      by_contra h0
      exact hz (fun c hc => (smul_eq_zero.1 hc).resolve_right h0)
    refine ⟨⟨fun x y => Subtype.ext ((h0 x.1 x.2.2.2).trans (h0 y.1 y.2.2.2).symm)⟩, ⟨⟨0, ?_⟩⟩⟩
    exact ⟨fun j => ffH_zero_right _ _ _, ffH_zero_left _ _ _, fun h => one_ne_zero (h 1 (smul_zero 1))⟩
  have hcnt := count_gen (σ : K →+* K) J hσ' hJ' T i₀ hr hc hu (by omega) (ι := algebraMap k K)
    (algebraMap k K).injective (map_zero _)
    (fun x => fixed_mem_range σ h2 hne _ (ffH_herm (σ : K →+* K) J hσ' hJ' x x).symm) _ 1 hN hD
  have hF0 := fFInert2_holds k K σ hσ h2 hne M a' (by omega) J hJ hdJ
    (T.submatrix i₀.succAbove i₀.succAbove) (fun i j => hT _ _) hu0
  have hN1 := fFInert2_holds k K σ hσ h2 hne M (a' + 1) haM J hJ hdJ _ (hTt 1 one_ne_zero).1
    (hTt 1 one_ne_zero).2
  have h1k : 1 ≤ Nat.card k := Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
  have hKk : Nat.card K = Nat.card k ^ 2 := by simp only [Nat.card_eq_fintype_card]; exact hK
  rw [hKk] at hcnt
  have hR := congrArg (fun n : ℕ => (n : ℝ)) hcnt
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub h1k, Nat.cast_one] at hR
  rw [hF0, hN1] at hR
  have hx : (Nat.card k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [prodInert_closed _ hx M a' (by omega), prodInert_closed _ hx M (a' + 1) haM] at hR
  obtain ⟨n, hn⟩ : ∃ n, M = a' + 1 + n := ⟨M - (a' + 1), by omega⟩
  have eE : 2 * M * (a' + 1) - (a' + 1) ^ 2 = (2 * M * a' - a' ^ 2) + (2 * n + 1) := by
    subst hn
    have h3 : a' ^ 2 ≤ 2 * (a' + 1 + n) * a' := by nlinarith
    have h4 : (a' + 1) ^ 2 ≤ 2 * (a' + 1 + n) * (a' + 1) := by nlinarith
    zify [h3, h4]
    ring
  have i1 : Finset.Icc (M - (a' + 1) + 1) M = insert (n + 1) (Finset.Icc (n + 2) M) := by
    rw [show M - (a' + 1) + 1 = n + 1 by omega]
    exact (Finset.insert_Icc_add_one_left_eq_Icc (by omega)).symm
  have i0 : Finset.Icc (M - (a' + 1)) M = insert n (insert (n + 1) (Finset.Icc (n + 2) M)) := by
    rw [show M - (a' + 1) = n by omega, ← Finset.insert_Icc_add_one_left_eq_Icc (show n ≤ M by omega),
      ← Finset.insert_Icc_add_one_left_eq_Icc (show n + 1 ≤ M by omega)]
    rfl
  rw [show M - a' + 1 = n + 2 by omega, show M - a' = n + 1 by omega, eE, pow_add, i1,
    Finset.prod_insert (by simp)] at hR
  rw [eE, pow_add, i0, Finset.prod_insert (by simp), Finset.prod_insert (by simp)]
  set P0 := ∏ j ∈ Finset.Icc (n + 2) M, (1 - (-1 : ℝ) ^ j * (Nat.card k : ℝ) ^ (-(j : ℤ)))
  set x := (Nat.card k : ℝ)
  set E0 := 2 * M * a' - a' ^ 2
  linear_combination hR + (x ^ E0 * P0) * keyInert x hx n

end PI.OmVe
end
end

namespace PI.OmVe.Top

theorem fFInertB_holds : PI.OmVd.FFInertB := PI.OmVe.fFInertB_holds

theorem fFSplitB_holds : PI.OmVd.FFSplitB := PI.OmVe.fFSplitB_holds

end PI.OmVe.Top
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVScaleHoldsX
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVScaleHolds
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.GramMulTupHolds
noncomputable section

namespace PI.NcVal.OmVc1

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.DegenerateSiegelWeil.Scale
open scoped TensorProduct

theorem gram_entry {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) (n M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (X : Fin n → Fin M → R ⊗[F] E) (a b : Fin n) :
    gramR R σ J (mulTup D X) a b = (conjT R σ D * gramR R σ J X * D) a b := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramR, hR, Formalism.UG.hform, mulTup, conjT, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  have h1 : ∀ f : Fin M → Fin M → Fin n → Fin n → R ⊗[F] E,
      (∑ i, ∑ j, ∑ l, ∑ k, f i j l k) = ∑ l, ∑ k, ∑ i, ∑ j, f i j l k := by
    intro f
    calc _ = ∑ i, ∑ l, ∑ j, ∑ k, f i j l k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ l, ∑ i, ∑ j, ∑ k, f i j l k := Finset.sum_comm
      _ = ∑ l, ∑ i, ∑ k, ∑ j, f i j l k :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ l, ∑ k, ∑ i, ∑ j, f i j l k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  refine (h1 _).trans ?_
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gramMulTup_holds : GramMulTup := by
  intro F E _ _ _ R _ _ σ n M J D X
  ext a b
  exact gram_entry R σ n M J D X a b

end PI.NcVal.OmVc1
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.MulTupDiagonal
noncomputable section

namespace PI.NcVal.OmVc2

open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.DegenerateSiegelWeil.Scale PI.VolStabSW PI.VolStabSW.TensAllW
open scoped NNReal TensorProduct

theorem char_eq_one {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]
    (e p : G ≃ₜ+ G) (hp : ∀ x, p (p x) = x) (he : ∀ x, p (e (p x)) = e.symm x) :
    addEquivAddHaarChar e = 1 := by
  have h1 : e.symm = p.trans (e.trans p) := by
    ext x
    exact (he x).symm
  have h2 : p.trans p = ContinuousAddEquiv.refl G := by
    ext x
    exact hp x
  have hpp : addEquivAddHaarChar p * addEquivAddHaarChar p = 1 := by
    rw [← addEquivAddHaarChar_trans, h2, addEquivAddHaarChar_refl]
  have h3 : (addEquivAddHaarChar e)⁻¹ = addEquivAddHaarChar e := by
    rw [← addEquivAddHaarChar_symm, h1, addEquivAddHaarChar_trans, addEquivAddHaarChar_trans]
    calc addEquivAddHaarChar p * (addEquivAddHaarChar e * addEquivAddHaarChar p)
        = (addEquivAddHaarChar p * addEquivAddHaarChar p) * addEquivAddHaarChar e := by ring
      _ = addEquivAddHaarChar e := by rw [hpp, one_mul]
  have hpos := addEquivAddHaarChar_pos e
  have h4 : addEquivAddHaarChar e * addEquivAddHaarChar e = 1 := by
    calc addEquivAddHaarChar e * addEquivAddHaarChar e
        = addEquivAddHaarChar e * (addEquivAddHaarChar e)⁻¹ := by rw [h3]
      _ = 1 := mul_inv_cancel₀ hpos.ne'
  have h5 : ((addEquivAddHaarChar e : ℝ≥0) : ℝ) * (addEquivAddHaarChar e : ℝ) = 1 := by exact_mod_cast h4
  have h6 : (0 : ℝ) ≤ (addEquivAddHaarChar e : ℝ) := (addEquivAddHaarChar e).2
  have hx : ((addEquivAddHaarChar e : ℝ≥0) : ℝ) = 1 := by
    rcases mul_self_eq_one_iff.1 h5 with h | h
    · exact h
    · linarith
  exact_mod_cast hx

section Alg

variable {K : Type} [CommRing K] {a M : ℕ}

def diagUnit (d : Fin a → Kˣ) : (Matrix (Fin a) (Fin a) K)ˣ where
  val := Matrix.diagonal fun i => (d i : K)
  inv := Matrix.diagonal fun i => ((d i)⁻¹ : Kˣ)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    exact funext fun i => (d i).mul_inv
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    exact funext fun i => (d i).inv_mul

theorem mulTup_diagonal (f : Fin a → K) (X : Fin a → Fin M → K) :
    mulTup (Matrix.diagonal f) X = fun j i => f j * X j i := by
  funext j i
  simp [mulTup, Matrix.diagonal_apply, ite_mul, Finset.sum_ite_eq']

end Alg

section Cov

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M n : ℕ} (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R]
  [SecondCountableTopology R]

def permTup (π : Equiv.Perm (Fin n)) : (Fin n → Fin M → R ⊗[F] E) ≃ₜ+ (Fin n → Fin M → R ⊗[F] E) where
  toFun X := fun j => X (π j)
  invFun X := fun j => X (π.symm j)
  left_inv X := by funext j; simp
  right_inv X := by funext j; simp
  map_add' _ _ := rfl
  continuous_toFun := continuous_pi fun j => continuous_apply _
  continuous_invFun := continuous_pi fun j => continuous_apply _

theorem cTup_eq_one (d : Fin n → (R ⊗[F] E)ˣ) (π : Equiv.Perm (Fin n)) (hπ : ∀ i, π (π i) = i)
    (hd : ∀ i, d (π i) = (d i)⁻¹) : cTup (M := M) R (diagUnit d) = 1 := by
  rw [cTup, char_eq_one (tupEquiv (M := M) (diagUnit d)) (permTup R π) ?_ ?_, inv_one]
  · intro X
    funext j
    show X (π (π j)) = X j
    rw [hπ]
  · intro X
    show (fun j => mulTup (Matrix.diagonal fun i => (d i : R ⊗[F] E)) (fun j => X (π j)) (π j)) =
      mulTup (Matrix.diagonal fun i => (((d i)⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E)) X
    rw [mulTup_diagonal, mulTup_diagonal]
    funext j i
    simp [hπ, hd]

def permHerm (π : Equiv.Perm (Fin n)) : HermR R σ n ≃ₜ+ HermR R σ n where
  toFun S := ⟨(S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).submatrix π π, fun a b => S.2 (π a) (π b)⟩
  invFun S := ⟨(S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).submatrix π.symm π.symm,
    fun a b => S.2 (π.symm a) (π.symm b)⟩
  left_inv S := by apply Subtype.ext; ext i j; simp
  right_inv S := by apply Subtype.ext; ext i j; simp
  map_add' _ _ := rfl
  continuous_toFun := (continuous_subtype_val.matrix_submatrix π π).subtype_mk _
  continuous_invFun := (continuous_subtype_val.matrix_submatrix π.symm π.symm).subtype_mk _

theorem conjT_diagonal (f : Fin n → R ⊗[F] E) :
    conjT R σ (Matrix.diagonal f) = Matrix.diagonal fun i => sigR R σ (f i) := by
  unfold conjT
  rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]

theorem cHerm_eq_one [SecondCountableTopology (HermR R σ n)] (d : Fin n → (R ⊗[F] E)ˣ)
    (π : Equiv.Perm (Fin n)) (hπ : ∀ i, π (π i) = i) (hd : ∀ i, d (π i) = (d i)⁻¹) :
    cHerm σ hσ R (diagUnit d) = 1 := by
  rw [cHerm, char_eq_one (hermEquiv R σ hσ (diagUnit d)) (permHerm σ R π) ?_ ?_]
  · intro S
    apply Subtype.ext
    ext i j
    show (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (π (π i)) (π (π j)) = _
    rw [hπ, hπ]
  · intro S
    apply Subtype.ext
    ext i j
    show (conjT R σ (Matrix.diagonal fun i => (d i : R ⊗[F] E)) *
        (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).submatrix π π *
          Matrix.diagonal fun i => (d i : R ⊗[F] E)) (π i) (π j) =
      (conjT R σ (Matrix.diagonal fun i => (((d i)⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E)) *
        (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) *
          Matrix.diagonal fun i => (((d i)⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E)) i j
    rw [conjT_diagonal, conjT_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp [hπ, hd]

end Cov

end PI.NcVal.OmVc2
end
end

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmVc

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory NumberField IsDedekindDomain PI.DegenerateSiegelWeil.Scale PI.NcVal.OmVc2 PI.VolStabSW PI.VolStabSW.TensAllW
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem scl_ne_zero (v : PlX X) (i : Fin (D.R.rS + 1 + D.R.rS)) : scl X v i ≠ 0 := by
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · rw [scl, Fin.append_left]; exact OmW.alp_ne_zero v _ _
  · rw [scl, Fin.append_right]; exact inv_ne_zero (OmW.alp_ne_zero v _ _)

theorem scl_piv (v : PlX X) (i : Fin (D.R.rS + 1 + D.R.rS)) :
    scl X v (OmW.piv D.R.rS i) = (scl X v i)⁻¹ := by
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) a
    · rw [OmW.pivot_castAdd_last, scl, Fin.append_left, OmW.alp_last, inv_one]
    · rw [OmW.piv_e, scl, Fin.append_left, Fin.append_right]
  · rw [OmW.piv_f, scl, Fin.append_left, Fin.append_right, inv_inv]

def dU (v : PlX X) (i : Fin (D.R.rS + 1 + D.R.rS)) : (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)ˣ where
  val := sc (E := X.B.I.E) v (scl X v i)
  inv := sc (E := X.B.I.E) v (scl X v i)⁻¹
  val_inv := by
    rw [sc, sc, Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ (scl_ne_zero X v i), one_mul,
      Algebra.TensorProduct.one_def]
  inv_val := by
    rw [sc, sc, Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ (scl_ne_zero X v i), one_mul,
      Algebra.TensorProduct.one_def]

theorem dU_piv (v : PlX X) (i : Fin (D.R.rS + 1 + D.R.rS)) : dU X v (OmW.piv D.R.rS i) = (dU X v i)⁻¹ := by
  apply Units.ext
  show sc (E := X.B.I.E) v (scl X v (OmW.piv D.R.rS i)) = sc (E := X.B.I.E) v (scl X v i)⁻¹
  rw [scl_piv]

theorem yTup_eq (v : PlX X) :
    yTup X u' v = mulTup ((diagUnit (dU X v) : (Matrix _ _ _)ˣ) : Matrix _ _ _)
      (ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))) := by
  show _ = mulTup (Matrix.diagonal fun i => (dU X v i : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) _
  rw [mulTup_diagonal]
  funext j i
  rfl

theorem gram_ratTup (v : PlX X) :
    gramR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))) = localGramMatrixFrame X u' v := by
  funext a b
  exact OmW.hR_ratTup (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J _ a b

theorem act_mulTup {K : Type} [CommRing K] {a M : ℕ} (g : Matrix (Fin M) (Fin M) K) (f : Fin a → K)
    (Y : Fin a → Fin M → K) :
    (fun j => g.mulVec (mulTup (Matrix.diagonal f) Y j)) = mulTup (Matrix.diagonal f) (fun j => g.mulVec (Y j)) := by
  rw [mulTup_diagonal, mulTup_diagonal]
  funext j i
  show g.mulVec (f j • Y j) i = f j * g.mulVec (Y j) i
  rw [Matrix.mulVec_smul]
  rfl

theorem orbit_eq (v : PlX X) :
    {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • yTup X u' v} =
      mulTup ((diagUnit (dU X v) : (Matrix _ _ _)ˣ) : Matrix _ _ _) ''
        {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))} := by
  have hc : ∀ k : HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J,
      k • yTup X u' v = mulTup ((diagUnit (dU X v) : (Matrix _ _ _)ˣ) : Matrix _ _ _)
        (k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))) := by
    intro k
    rw [yTup_eq]
    exact act_mulTup _ _ _
  ext Y
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, ⟨k, hk, rfl⟩, (hc k).symm⟩
  · rintro ⟨Z, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, (hc k).symm⟩

theorem omVScale_holds : OmVScale X u' ψ := by
  intro h1 h2 v
  have hS := OmW.omVStd_holds X ψ h1 h2
  have hσ : ∀ x, X.B.I.cm.sig (X.B.I.cm.sig x) = x := PI.VolStabSW.sigma_invol _ hS.1.2.2.2
  have hJ : ∀ i j, X.B.I.cm.sig (X.B.I.J j i) = X.B.I.J i j := hS.2.1.1
  have : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [hS.1.2.2.1]; norm_num)
  rw [orbit_eq]
  unfold omAt
  split_ifs with hT
  swap
  · rfl
  unfold omFam
  split_ifs with hfib
  swap
  · rfl
  have := PI.VolStabSW.secondCountable_Fv X.B.I.F v
  have := PI.VolStabSW.locallyCompact_Fv X.B.I.F v
  have : SecondCountableTopology (Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS))
      (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) :=
    inferInstanceAs (SecondCountableTopology (Fin (D.R.rS + 1 + D.R.rS) → Fin (D.R.rS + 1 + D.R.rS) →
      Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E))
  have : SecondCountableTopology (HermR (Fv X.B.I.F v) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hEx := PI.SelfDualBridge.W.sdExists_holds X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS) (Fin 1) hS
  have hμ : SdW X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J (Fv X.B.I.F v) (psiV X.B.I.F ψ v)
      (D.R.rS + 1 + D.R.rS) (dX X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS)) := by
    unfold dX; rw [dite_eq_left hEx.1]; exact hEx.1.choose_spec
  have hν : SdHerm X.B.I.F X.B.I.E X.B.I.cm.sig (Fv X.B.I.F v) (psiV X.B.I.F ψ v) (D.R.rS + 1 + D.R.rS)
      (dT X.B.I.cm.sig ψ v (D.R.rS + 1 + D.R.rS)) := by
    unfold dT; rw [dite_eq_left hEx.2.1]; exact hEx.2.1.choose_spec
  have := hμ.1
  have := hν.1
  have hπ : ∀ i, (Function.Involutive.toPerm _ (OmW.piv_invol D.R.rS)) ((Function.Involutive.toPerm _
      (OmW.piv_invol D.R.rS)) i) = i := fun i => OmW.piv_invol D.R.rS i
  have hd : ∀ i, dU X v ((Function.Involutive.toPerm _ (OmW.piv_invol D.R.rS)) i) = (dU X v i)⁻¹ :=
    fun i => dU_piv X v i
  have hfix : hermMap (Fv X.B.I.F v) X.B.I.cm.sig hσ
      ((diagUnit (dU X v) : (Matrix _ _ _)ˣ) : Matrix _ _ _) ⟨localGramMatrixFrame X u' v, hT⟩ = ⟨localGramMatrixFrame X u' v, hT⟩ := by
    apply Subtype.ext
    rw [hermMap_coe]
    show _ * localGramMatrixFrame X u' v * _ = localGramMatrixFrame X u' v
    have hg := OmW.omVGram_holds X u' v
    rw [yTup_eq, PI.NcVal.OmVc1.gramMulTup_holds _ _ _ _ _ _ _ _ _, gram_ratTup] at hg
    exact hg
  have key := fib_image_mulTup X.B.I.cm.sig hσ X.B.I.J hJ (Fv X.B.I.F v) PI.NcVal.OmVc1.gramMulTup_holds
    (PI.VolStabSW.isOpen_units_Fv X.B.I.F v) (lip_field _) _ _ hfib.choose hfib.choose_spec
    (diagUnit (dU X v)) ⟨localGramMatrixFrame X u' v, hT⟩ hfix
    {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))}
  rw [cTup_eq_one (Fv X.B.I.F v) (dU X v) _ hπ hd, cHerm_eq_one X.B.I.cm.sig hσ (Fv X.B.I.F v) (dU X v) _ hπ hd]
    at key
  simp only [ENNReal.coe_one, one_mul] at key
  exact key.symm

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmVc
end
end

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmVc

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem omVScale_holdsX {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) :
    Formalism.L2.SG.Pf.NcX.OmVSt.OmVScale X u' ψ :=
  omVScale_holds X u' ψ

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmVc
end

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVLocU_holds : OmVLocU X ψ := fun v a Y =>
  PI.OmLocU.Done.omLocU_closed X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) a Y

theorem omVBadT_holdsX : Formalism.L2.SG.Pf.NcX.OmVSt.OmVBadT X u' ψ :=
  PI.OmVg.omVBadT_of_ffX X u' ψ (Formalism.L2.SG.Pf.NcX.OmVSt.omega_standard_holds X ψ) (Formalism.L2.SG.Pf.NcX.OmVSt.omega_lattice_holds X)
    (OmW.omVGram_holds X u') PI.OmVe.Top.fFInertB_holds PI.OmVe.Top.fFSplitB_holds

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ

namespace Formalism.L2.SG.Pf.NcX.OmVSt

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVZGram : OmVGram X u' := Formalism.L2.SG.Pf.NcVal.OmVSt.OmW.omVGram_holds X u'

theorem omVZDet : OmVDet X u' := Formalism.L2.SG.Pf.NcVal.OmVSt.OmW.omVDet_holds X u'

theorem omVZLocU : OmVLocU X ψ := Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ.omVLocU_holds X ψ

theorem omVZ_holdsX : Formalism.L2.SG.Pf.NcVal.OmV X u' ψ :=
  omV_of X u' ψ (omega_standard_holds X ψ) (omega_lattice_holds X) (Formalism.L2.SG.Pf.NcVal.OmVSt.OmX.omVSD_holdsX X)
    (omega_unramified_holds X) (Formalism.L2.SG.Pf.NcVal.OmVSt.OmX.omVPrim_holdsX X u') (omVZGram X u') (omVZDet X u')
    (Formalism.L2.SG.Pf.NcVal.OmVSt.OmVc.omVScale_holdsX X u' ψ) (Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ.omVBadT_holdsX X u' ψ)
    (omVZLocU X ψ)

end Formalism.L2.SG.Pf.NcX.OmVSt

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem omV_holdsX {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) : Formalism.L2.SG.Pf.NcVal.OmV X u' ψ :=
  Formalism.L2.SG.Pf.NcX.OmVSt.omVZ_holdsX X u' ψ

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ
