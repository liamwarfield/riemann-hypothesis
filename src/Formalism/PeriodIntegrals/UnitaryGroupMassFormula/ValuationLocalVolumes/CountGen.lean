module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFF

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.CardAndAdd
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.SingleMulVec
noncomputable section

namespace PI.OmVe

open PI.VolStabSW Matrix

section gen

variable {K : Type} [CommRing K] (σ : K →+* K) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)

theorem ffH_add_right (x y z : Fin M → K) : ffH σ J x (y + z) = ffH σ J x y + ffH σ J x z := by
  simp [ffH, mul_add, Finset.sum_add_distrib]

theorem ffH_smul_right (c : K) (x y : Fin M → K) : ffH σ J x (c • y) = c * ffH σ J x y := by
  unfold ffH
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem ffH_zero_right (x : Fin M → K) : ffH σ J x 0 = 0 := by
  simp [ffH]

theorem ffH_zero_left (x : Fin M → K) : ffH σ J 0 x = 0 := by
  simp [ffH]

theorem ffH_sum_right {ι : Type} (s : Finset ι) (c : ι → K) (x : Fin M → K) (y : ι → Fin M → K) :
    ffH σ J x (∑ l ∈ s, c l • y l) = ∑ l ∈ s, c l * ffH σ J x (y l) := by
  classical
  refine Finset.induction_on s (by simp [ffH_zero_right]) ?_
  intro l s hl ih
  rw [Finset.sum_insert hl, Finset.sum_insert hl, ffH_add_right, ffH_smul_right, ih]

theorem ffH_herm (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → K) :
    ffH σ J y x = σ (ffH σ J x y) := by
  unfold ffH
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]
  ring

theorem single_mulVec' {a : ℕ} (i₀ : Fin a) (v : Fin a → K) :
    (Matrix.single i₀ i₀ (1 : K)) *ᵥ v = Pi.single i₀ (v i₀) := by
  ext i
  by_cases h : i = i₀
  · subst h
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
  · simp [Matrix.mulVec, dotProduct, Matrix.single_apply, h, Ne.symm h]

theorem indep_iff {a : ℕ} {T : Matrix (Fin a) (Fin a) K} (i₀ : Fin a) (hc : ∀ j, T j i₀ = 0)
    (hu : IsUnit (T + Matrix.single i₀ i₀ 1).det) (X : Fin a → Fin M → K) (hX : ffGram σ J X = T) :
    LinearIndependent K X ↔ ∀ c : K, c • X i₀ = 0 → c = 0 := by
  classical
  constructor
  · intro hli c hc0
    have := Fintype.linearIndependent_iff.1 hli (Pi.single i₀ c) (by simp [Pi.single_apply, hc0])
    simpa using this i₀
  · intro h
    rw [Fintype.linearIndependent_iff]
    intro g hg

    have hT : T *ᵥ g = 0 := by
      funext j
      have := congrArg (ffH σ J (X j)) hg
      rw [ffH_sum_right σ J Finset.univ g (X j) X, ffH_zero_right] at this
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← hX]
      simpa [ffGram, mul_comm] using this
    have hTe : T *ᵥ Pi.single i₀ (g i₀) = 0 := by
      funext j
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, hc]
    have heq : (T + Matrix.single i₀ i₀ (1 : K)) *ᵥ g =
        (T + Matrix.single i₀ i₀ (1 : K)) *ᵥ Pi.single i₀ (g i₀) := by
      rw [Matrix.add_mulVec, Matrix.add_mulVec, hT, hTe, single_mulVec', single_mulVec', Pi.single_eq_same]

    have hinv : (T + Matrix.single i₀ i₀ (1 : K))⁻¹ * (T + Matrix.single i₀ i₀ (1 : K)) = 1 :=
      Matrix.nonsing_inv_mul _ hu
    have hg' : g = Pi.single i₀ (g i₀) := by
      calc g = ((T + Matrix.single i₀ i₀ (1 : K))⁻¹ * (T + Matrix.single i₀ i₀ (1 : K))) *ᵥ g := by
            rw [hinv, Matrix.one_mulVec]
        _ = (T + Matrix.single i₀ i₀ (1 : K))⁻¹ *ᵥ ((T + Matrix.single i₀ i₀ (1 : K)) *ᵥ g) := by
            rw [Matrix.mulVec_mulVec]
        _ = (T + Matrix.single i₀ i₀ (1 : K))⁻¹ *ᵥ ((T + Matrix.single i₀ i₀ (1 : K)) *ᵥ
              Pi.single i₀ (g i₀)) := by rw [heq]
        _ = Pi.single i₀ (g i₀) := by rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    have hsum : ∑ i, g i • X i = g i₀ • X i₀ := by
      rw [hg']
      simp [Pi.single_apply]
    have h0 : g i₀ = 0 := h _ (hsum ▸ hg)
    intro i
    rw [hg', h0]
    simp

theorem det_corOne {a : ℕ} (T : Matrix (Fin (a + 1)) (Fin (a + 1)) K) (i₀ : Fin (a + 1))
    (hr : ∀ j, T i₀ j = 0) (t : K) :
    (T + Matrix.single i₀ i₀ t).det = t * (T.submatrix i₀.succAbove i₀.succAbove).det := by

  rw [Matrix.det_succ_row _ i₀, Finset.sum_eq_single i₀
    (fun j _ hj => by simp [hr, Matrix.single_apply, Ne.symm hj]) (by simp)]
  have hsub : (T + Matrix.single i₀ i₀ t).submatrix i₀.succAbove i₀.succAbove =
      T.submatrix i₀.succAbove i₀.succAbove := by
    ext a b
    simp [Matrix.single_apply, (Fin.succAbove_ne i₀ a).symm]
  rw [hsub]
  simp [hr, Matrix.single_apply, ← two_mul, pow_mul]

end gen

end PI.OmVe
end
end

noncomputable section

namespace PI.OmVe

open PI.VolStabSW Matrix

section gen

variable {K : Type} [CommRing K] (σ : K →+* K) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)

private theorem eq_or_exists_succAbove {n : ℕ} (p i : Fin (n + 1)) :
    i = p ∨ ∃ j, i = p.succAbove j := by
  by_cases h : i = p
  · exact Or.inl h
  · right
    exact (Fin.eq_self_or_eq_succAbove p i).resolve_left h

theorem gram_split (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) {a' : ℕ}
    (T : Matrix (Fin (a' + 1)) (Fin (a' + 1)) K) (i₀ : Fin (a' + 1)) (hr : ∀ j, T i₀ j = 0)
    (hc : ∀ j, T j i₀ = 0) (t : K) (X : Fin (a' + 1) → Fin M → K) :
    ffGram σ J X = T + Matrix.single i₀ i₀ t ↔
      ffGram σ J (fun j => X (i₀.succAbove j)) = T.submatrix i₀.succAbove i₀.succAbove ∧
        (∀ j, ffH σ J (X (i₀.succAbove j)) (X i₀) = 0) ∧ ffH σ J (X i₀) (X i₀) = t := by
  constructor
  · intro h
    have hh : ∀ i j, PI.VolStabSW.ffH σ J (X i) (X j) = T i j + Matrix.single i₀ i₀ t i j :=
      fun i j => congrFun (congrFun h i) j
    refine ⟨?_, fun j => ?_, ?_⟩
    · ext j k
      show PI.VolStabSW.ffH σ J (X (i₀.succAbove j)) (X (i₀.succAbove k)) =
        T (i₀.succAbove j) (i₀.succAbove k)
      have hne : i₀.succAbove j ≠ i₀ := Fin.succAbove_ne i₀ j
      rw [hh]
      simp [hne.symm]
    · have hne : i₀.succAbove j ≠ i₀ := Fin.succAbove_ne i₀ j
      rw [hh, hc]
      simp [hne.symm]
    · rw [hh, hr]
      simp
  · rintro ⟨h1, h2, h3⟩
    ext i j
    show PI.VolStabSW.ffH σ J (X i) (X j) = T i j + Matrix.single i₀ i₀ t i j
    rcases eq_or_exists_succAbove i₀ i with hi | ⟨i', hi⟩ <;>
      rcases eq_or_exists_succAbove i₀ j with hj | ⟨j', hj⟩ <;> rw [hi, hj]
    · rw [h3, hr]
      simp
    · have hne : i₀.succAbove j' ≠ i₀ := Fin.succAbove_ne i₀ j'
      rw [ffH_herm σ J hσ hJ (X (i₀.succAbove j')) (X i₀), h2 j', map_zero, hr]
      simp [hne.symm]
    · have hne : i₀.succAbove i' ≠ i₀ := Fin.succAbove_ne i₀ i'
      rw [h2 i', hc]
      simp [hne.symm]
    · have hne : i₀.succAbove i' ≠ i₀ := Fin.succAbove_ne i₀ i'
      rw [show PI.VolStabSW.ffH σ J (X (i₀.succAbove i')) (X (i₀.succAbove j')) =
          T (i₀.succAbove i') (i₀.succAbove j') from congrFun (congrFun h1 i') j']
      simp [hne.symm]

theorem card_split [Finite K] (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) {a' : ℕ}
    (T : Matrix (Fin (a' + 1)) (Fin (a' + 1)) K) (i₀ : Fin (a' + 1)) (hr : ∀ j, T i₀ j = 0)
    (hc : ∀ j, T j i₀ = 0) (t : K) (R : (Fin M → K) → Prop) :
    Nat.card {X : Fin (a' + 1) → Fin M → K // ffGram σ J X = T + Matrix.single i₀ i₀ t ∧ R (X i₀)} =
      Nat.card (Σ Y : {Y : Fin a' → Fin M → K // ffGram σ J Y = T.submatrix i₀.succAbove i₀.succAbove},
        {x : Fin M → K // (∀ j, ffH σ J (Y.1 j) x = 0) ∧ ffH σ J x x = t ∧ R x}) := by
  have key := fun X => gram_split σ J hσ hJ T i₀ hr hc t X
  apply Nat.card_congr
  refine
    { toFun := fun X => ⟨⟨fun j => X.1 (i₀.succAbove j), ((key X.1).1 X.2.1).1⟩,
        ⟨X.1 i₀, ((key X.1).1 X.2.1).2.1, ((key X.1).1 X.2.1).2.2, X.2.2⟩⟩
      invFun := fun p => ⟨Fin.insertNth (α := fun _ => Fin M → K) i₀ p.2.1 p.1.1,
        (key _).2 ⟨by simpa [Fin.insertNth_apply_succAbove] using p.1.2,
          fun j => by simpa [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same]
            using p.2.2.1 j,
          by simpa [Fin.insertNth_apply_same] using p.2.2.2.1⟩,
        by simpa [Fin.insertNth_apply_same] using p.2.2.2.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro X
    apply Subtype.ext
    funext i
    rcases eq_or_exists_succAbove i₀ i with hi | ⟨j, hi⟩ <;> rw [hi]
    · simp [Fin.insertNth_apply_same]
    · simp [Fin.insertNth_apply_succAbove]
  · rintro ⟨⟨Y, hY⟩, ⟨x, hx⟩⟩
    apply Sigma.subtype_ext
    · apply Subtype.ext
      funext j
      simp [Fin.insertNth_apply_succAbove]
    · simp [Fin.insertNth_apply_same]

theorem card_perp [Finite K] {a' : ℕ} (T0 : Matrix (Fin a') (Fin a') K) (hu : IsUnit T0.det)
    (Y : Fin a' → Fin M → K) (hY : ffGram σ J Y = T0) :
    Nat.card {x : Fin M → K // ∀ j, ffH σ J (Y j) x = 0} * Nat.card K ^ a' = Nat.card K ^ M := by
  classical
  let f : (Fin M → K) →+ (Fin a' → K) :=
    AddMonoidHom.mk' (fun x j => PI.VolStabSW.ffH σ J (Y j) x) (fun x y => by
      funext j
      exact ffH_add_right σ J (Y j) x y)
  have hsurj : Function.Surjective f := by
    intro v
    refine ⟨∑ l, (T0⁻¹ *ᵥ v) l • Y l, ?_⟩
    funext j
    show PI.VolStabSW.ffH σ J (Y j) (∑ l, (T0⁻¹ *ᵥ v) l • Y l) = v j
    rw [ffH_sum_right σ J Finset.univ]
    have hT : ∀ l, PI.VolStabSW.ffH σ J (Y j) (Y l) = T0 j l := fun l => congrFun (congrFun hY j) l
    simp_rw [hT]
    have hinv : T0 *ᵥ (T0⁻¹ *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv T0 hu, Matrix.one_mulVec]
    calc ∑ l, (T0⁻¹ *ᵥ v) l * T0 j l = (T0 *ᵥ (T0⁻¹ *ᵥ v)) j := by
          simp only [Matrix.mulVec, dotProduct]
          exact Finset.sum_congr rfl (fun l _ => mul_comm _ _)
      _ = v j := by rw [hinv]
  have hker : Nat.card {x : Fin M → K // ∀ j, PI.VolStabSW.ffH σ J (Y j) x = 0} = Nat.card f.ker := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun x => by
      rw [AddMonoidHom.mem_ker]
      exact ⟨fun h => by ext j; exact h j, fun h j => congrFun h j⟩)
  have hidx : f.ker.index = Nat.card (Fin a' → K) := by
    exact Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hsurj).toEquiv
  have hpow : ∀ n : ℕ, Nat.card (Fin n → K) = Nat.card K ^ n := by
    intro n
    rw [Nat.card_fun, Nat.card_fin]
  rw [hker, ← hpow a', ← hidx, AddSubgroup.card_mul_index, hpow M]

theorem card_and_add {α : Type} [Finite α] (G Q : α → Prop) :
    Nat.card {x // G x ∧ Q x} + Nat.card {x // G x ∧ ¬ Q x} = Nat.card {x // G x} := by
  classical
  rw [← Nat.card_sum]
  exact Nat.card_congr
    (((Equiv.subtypeSubtypeEquivSubtypeInter G Q).symm.sumCongr
      (Equiv.subtypeSubtypeEquivSubtypeInter G (fun x => ¬ Q x)).symm).trans
      (Equiv.sumCompl (fun y : {x // G x} => Q y.1)))

end gen

end PI.OmVe
end
end

noncomputable section

namespace PI.OmVe

open PI.VolStabSW Matrix

section gen

variable {K : Type} [CommRing K] (σ : K →+* K) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)

theorem count_gen [Finite K] (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) {a' : ℕ}
    (T : Matrix (Fin (a' + 1)) (Fin (a' + 1)) K) (i₀ : Fin (a' + 1)) (hr : ∀ j, T i₀ j = 0)
    (hc : ∀ j, T j i₀ = 0) (hu : IsUnit (T + Matrix.single i₀ i₀ 1).det) (haM : a' ≤ M)
    {k : Type} [Finite k] [Zero k] (ι : k → K) (hι : Function.Injective ι) (hι0 : ι 0 = 0)
    (hrange : ∀ x : Fin M → K, ∃ c, ffH σ J x x = ι c) (N D : ℕ)
    (hN : ∀ c, c ≠ 0 → Nat.card {X : Fin (a' + 1) → Fin M → K //
      ffGram σ J X = T + Matrix.single i₀ i₀ (ι c)} = N)
    (hD : ∀ Y : Fin a' → Fin M → K, ffGram σ J Y = T.submatrix i₀.succAbove i₀.succAbove →
      Nat.card {x : Fin M → K // (∀ j, ffH σ J (Y j) x = 0) ∧ ffH σ J x x = 0 ∧
        ¬ ∀ c : K, c • x = 0 → c = 0} = D) :
    Nat.card {X : Fin (a' + 1) → Fin M → K // ffGram σ J X = T ∧ LinearIndependent K X} +
      Nat.card {Y : Fin a' → Fin M → K // ffGram σ J Y = T.submatrix i₀.succAbove i₀.succAbove} * D +
      (Nat.card k - 1) * N =
    Nat.card {Y : Fin a' → Fin M → K // ffGram σ J Y = T.submatrix i₀.succAbove i₀.succAbove} *
      Nat.card K ^ (M - a') := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fintype k := Fintype.ofFinite k
  set T0 := T.submatrix i₀.succAbove i₀.succAbove with hT0
  have hu0 : IsUnit T0.det := by
    have h1 := det_corOne T i₀ hr (1 : K)
    rw [one_mul] at h1
    rw [← h1]
    exact hu
  let A : {Y : Fin a' → Fin M → K // ffGram σ J Y = T0} → k → ℕ := fun Y c =>
    Nat.card {x : Fin M → K // (∀ j, ffH σ J (Y.1 j) x = 0) ∧ ffH σ J x x = ι c}
  have hperp : ∀ Y : {Y : Fin a' → Fin M → K // ffGram σ J Y = T0},
      Nat.card {x : Fin M → K // ∀ j, ffH σ J (Y.1 j) x = 0} = Nat.card K ^ (M - a') := by
    intro Y
    have h1 := card_perp σ J T0 hu0 Y.1 Y.2
    have hK : 0 < Nat.card K := Nat.card_pos
    have h2 : Nat.card K ^ M = Nat.card K ^ (M - a') * Nat.card K ^ a' := by
      rw [← pow_add, Nat.sub_add_cancel haM]
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hK _) h1
  have hfib : ∀ Y : {Y : Fin a' → Fin M → K // ffGram σ J Y = T0},
      Nat.card {x : Fin M → K // ∀ j, ffH σ J (Y.1 j) x = 0} = ∑ c, A Y c := by
    intro Y
    simp only [A, Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [Finset.card_eq_sum_card_fiberwise (f := fun x => ffH σ J x x) (t := Finset.univ.image ι)
      (fun x _ => by
        obtain ⟨c, hc'⟩ := hrange x
        exact Finset.mem_image.2 ⟨c, Finset.mem_univ _, hc'.symm⟩)]
    rw [Finset.sum_image (fun a _ b _ h => hι h)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.filter_filter]
  have htot : Nat.card {Y : Fin a' → Fin M → K // ffGram σ J Y = T0} * Nat.card K ^ (M - a') =
      ∑ c, ∑ Y, A Y c := by
    rw [Finset.sum_comm, Nat.card_eq_fintype_card, ← smul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [← hperp Y, hfib Y]
  have hcN : ∀ c, c ≠ 0 → ∑ Y, A Y c = N := by
    intro c hc0
    rw [← hN c hc0]
    have h1 := card_split σ J hσ hJ T i₀ hr hc (ι c) (fun _ => True)
    simp only [and_true] at h1
    rw [h1, Nat.card_sigma]
  have h0 : ∑ Y, A Y 0 = Nat.card {X : Fin (a' + 1) → Fin M → K // ffGram σ J X = T ∧ LinearIndependent K X} +
      Nat.card {Y : Fin a' → Fin M → K // ffGram σ J Y = T0} * D := by
    have hR := card_split σ J hσ hJ T i₀ hr hc 0 (fun x => ∀ c : K, c • x = 0 → c = 0)
    simp only [Matrix.single_zero, add_zero] at hR
    have hLI : Nat.card {X : Fin (a' + 1) → Fin M → K // ffGram σ J X = T ∧ LinearIndependent K X} =
        Nat.card {X : Fin (a' + 1) → Fin M → K // ffGram σ J X = T ∧ ∀ c : K, c • X i₀ = 0 → c = 0} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun X =>
        ⟨fun h => ⟨h.1, (indep_iff σ J i₀ hc hu X h.1).1 h.2⟩,
          fun h => ⟨h.1, (indep_iff σ J i₀ hc hu X h.1).2 h.2⟩⟩)
    have hD' : ∑ Y : {Y : Fin a' → Fin M → K // ffGram σ J Y = T0},
        Nat.card {x : Fin M → K // (∀ j, ffH σ J (Y.1 j) x = 0) ∧ ffH σ J x x = 0 ∧
          ¬ ∀ c : K, c • x = 0 → c = 0} =
        Nat.card {Y : Fin a' → Fin M → K // ffGram σ J Y = T0} * D := by
      rw [Finset.sum_congr rfl (fun Y _ => hD Y.1 Y.2), Finset.sum_const, Finset.card_univ,
        smul_eq_mul, Nat.card_eq_fintype_card]
    rw [hLI, hR, Nat.card_sigma, ← hD', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun Y _ => ?_
    simp only [A, hι0]
    have h2 := card_and_add (fun x : Fin M → K => (∀ j, ffH σ J (Y.1 j) x = 0) ∧ ffH σ J x x = 0)
      (fun x => ∀ c : K, c • x = 0 → c = 0)
    simp only [and_assoc] at h2
    exact h2.symm
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : k)),
    Finset.sum_congr rfl (fun c hc0 => hcN c (Finset.ne_of_mem_erase hc0)), Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, smul_eq_mul, h0] at htot
  rw [htot, Nat.card_eq_fintype_card (α := k)]

end gen

end PI.OmVe
