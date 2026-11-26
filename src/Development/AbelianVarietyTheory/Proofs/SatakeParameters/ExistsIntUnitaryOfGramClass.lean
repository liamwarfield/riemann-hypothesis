module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmithNormalFormIntegralMatrix
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTorusEigenformOfCompactTorusEigenvector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralWittTheoremModUniformizerPow

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeKernelLeOfMatrixLatticeIndexEq
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeKernelLeOfMatrixLatticeIndexEq
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.HoweDuality

theorem ker_le_of_latIdx_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (x y : Matrix (Fin n') (Fin n) L),
    (∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) → ∀ i, (y *ᵥ u) i ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.HoweDuality.latIdx y = GlobalTheory.Hk3.HoweDuality.latIdx x →
    ∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (y *ᵥ u) i ∈ Formalism.UG.intL L) → ∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L := by
  intro L _ _ ϖ σ q hU n n' x y hN hidx u hu hyu
  classical
  have hfin := finite_range_latIdx hU x
  set Sx := Set.range fun u : intVec L n =>
      (QuotientAddGroup.mk (x *ᵥ (u : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') with hSx
  set Sy := Set.range fun u : intVec L n =>
      (QuotientAddGroup.mk (y *ᵥ (u : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') with hSy
  let h : (Fin n' → L) ⧸ intVec L n' → (Fin n' → L) ⧸ intVec L n' := fun c =>
    if hc : ∃ u : intVec L n, (QuotientAddGroup.mk (x *ᵥ (u : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') = c
    then QuotientAddGroup.mk (y *ᵥ (hc.choose : Fin n → L)) else 0
  have key : ∀ w : intVec L n, h (QuotientAddGroup.mk (x *ᵥ (w : Fin n → L))) =
      (QuotientAddGroup.mk (y *ᵥ (w : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') := by
    intro w
    have hc : ∃ u' : intVec L n, (QuotientAddGroup.mk (x *ᵥ (u' : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') =
        QuotientAddGroup.mk (x *ᵥ (w : Fin n → L)) := ⟨w, rfl⟩
    simp only [h, dif_pos hc]
    have he := hc.choose_spec
    set u' := hc.choose
    rw [QuotientAddGroup.eq] at he
    rw [QuotientAddGroup.eq]
    have hd := hN ((w : Fin n → L) - (u' : Fin n → L)) (fun i => Subring.sub_mem _ (w.2 i) (u'.2 i))
      (fun i => by
        have := he i
        rw [Matrix.mulVec_sub]
        simpa [neg_add_eq_sub] using this)
    intro i
    have := hd i
    rw [Matrix.mulVec_sub] at this
    simpa [neg_add_eq_sub] using this
  have himg : h '' Sx = Sy := by
    apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, (key w).symm⟩
    · rintro _ ⟨w, rfl⟩
      exact ⟨_, ⟨w, rfl⟩, key w⟩
  have hcard : (h '' Sx).ncard = Sx.ncard := by
    rw [himg]
    unfold latIdx at hidx
    rw [← hSx, ← hSy, Nat.card_coe_set_eq, Nat.card_coe_set_eq] at hidx
    exact hidx
  have hinj : Set.InjOn h Sx := (Set.ncard_image_iff hfin).1 hcard
  let u0 : intVec L n := ⟨u, hu⟩
  have h0 : h (QuotientAddGroup.mk (x *ᵥ ((u0 : intVec L n) : Fin n → L))) = h (QuotientAddGroup.mk (x *ᵥ ((0 : intVec L n) : Fin n → L))) := by
    rw [key, key]
    simp only [AddSubgroup.coe_zero, Matrix.mulVec_zero, QuotientAddGroup.mk_zero]
    exact (QuotientAddGroup.eq_zero_iff _).2 hyu
  have h1 := hinj ⟨u0, rfl⟩ ⟨0, rfl⟩ h0
  simp only [AddSubgroup.coe_zero, Matrix.mulVec_zero, QuotientAddGroup.mk_zero] at h1
  exact (QuotientAddGroup.eq_zero_iff _).1 h1

end GlobalTheory.Hk3.HoweDuality

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeKernelLeOfMatrixLatticeIndexEqStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeKernel_le_of_matrixLatticeIndex_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (x y : Matrix (Fin n') (Fin n) L),
    (∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) → ∀ i, (y *ᵥ u) i ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.HoweDuality.latIdx y = GlobalTheory.Hk3.HoweDuality.latIdx x →
    ∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (y *ᵥ u) i ∈ Formalism.UG.intL L) → ∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L := by
  first | exact @GlobalTheory.Hk3.HoweDuality.ker_le_of_latIdx_eq | exact GlobalTheory.Hk3.HoweDuality.ker_le_of_latIdx_eq | (intros; apply GlobalTheory.Hk3.HoweDuality.ker_le_of_latIdx_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementaryDivisorColumnsIndependentModUniformize
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementaryDivisorColumnsIndependentModUniformize
open Matrix

namespace GlobalTheory

theorem columns_indepMod :
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L),
    Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
    ∀ (n n' : ℕ) (x : Matrix (Fin n') (Fin n) L) (V : Matrix (Fin n) (Fin n) L) (a : Fin n → ℕ),
    (∀ c : Fin n → L, (∀ j, c j ∈ Formalism.UG.intL L) →
      ((∀ i, (x *ᵥ (V *ᵥ c)) i ∈ Formalism.UG.intL L) ↔ ∀ j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a j) (c j))) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ (fun j : {j : Fin n // 0 < a j} => x *ᵥ (V *ᵥ Pi.single (j : Fin n) (ϖ ^ a (j : Fin n)))) := by
  intro L _ _ ϖ hϖ n n' x V a H d hd hdiv j
  classical
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  have hϖi : ϖ ∈ Formalism.UG.intL L := by
    show Valued.v ϖ ≤ 1
    rw [hϖ, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]
    norm_num
  set c : Fin n → L := fun k => if h : 0 < a k then d ⟨k, h⟩ * ϖ ^ (a k - 1) else 0 with hc
  have hcint : ∀ k, c k ∈ Formalism.UG.intL L := by
    intro k; simp only [hc]; split_ifs
    · exact mul_mem (hd _) (pow_mem hϖi _)
    · exact zero_mem _
  have hsum : ϖ • c = ∑ i : {j : Fin n // 0 < a j}, d i • Pi.single (i : Fin n) (ϖ ^ a (i : Fin n)) := by
    funext k
    rw [Finset.sum_apply]
    by_cases hk : 0 < a k
    · rw [Finset.sum_eq_single ⟨k, hk⟩]
      · obtain ⟨m, hm⟩ : ∃ m, a k = m + 1 := Nat.exists_eq_succ_of_ne_zero hk.ne'
        simp [hc, hk, hm]; ring
      · intro b _ hb
        have : k ≠ (b : Fin n) := fun h => hb (Subtype.ext h.symm)
        simp [Pi.single_apply, this]
      · simp
    · rw [Finset.sum_eq_zero]
      · simp [hc, hk]
      · intro i _
        have : k ≠ (i : Fin n) := fun h => hk (h ▸ i.2)
        simp [Pi.single_apply, this]
  have hlin : ϖ • (x *ᵥ (V *ᵥ c)) = ∑ i : {j : Fin n // 0 < a j}, d i • (x *ᵥ (V *ᵥ Pi.single (i : Fin n) (ϖ ^ a (i : Fin n)))) := by
    rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul, hsum, Matrix.mulVec_sum, Matrix.mulVec_sum]
    simp [Matrix.mulVec_smul]
  have hw : ∀ r, (x *ᵥ (V *ᵥ c)) r ∈ Formalism.UG.intL L := by
    intro r
    obtain ⟨b, hb, hbe⟩ := hdiv r
    have h1 := congrFun hlin r
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at h1
    rw [← h1, pow_one] at hbe
    rw [mul_left_cancel₀ hϖ0 hbe]; exact hb
  obtain ⟨b, hb, hbe⟩ := (H c hcint).1 hw j
  refine ⟨b, hb, ?_⟩
  obtain ⟨m, hm⟩ : ∃ m, a j = m + 1 := Nat.exists_eq_succ_of_ne_zero j.2.ne'
  simp only [hc, dif_pos j.2, hm, Nat.add_sub_cancel] at hbe
  apply mul_right_cancel₀ (pow_ne_zero m hϖ0)
  rw [hbe]; ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementaryDivisorColumnsIndependentModUniformizeStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elementaryDivisor_columns_independentModUniformizer : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L),
    Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
    ∀ (n n' : ℕ) (x : Matrix (Fin n') (Fin n) L) (V : Matrix (Fin n) (Fin n) L) (a : Fin n → ℕ),
    (∀ c : Fin n → L, (∀ j, c j ∈ Formalism.UG.intL L) →
      ((∀ i, (x *ᵥ (V *ᵥ c)) i ∈ Formalism.UG.intL L) ↔ ∀ j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a j) (c j))) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ (fun j : {j : Fin n // 0 < a j} => x *ᵥ (V *ᵥ Pi.single (j : Fin n) (ϖ ^ a (j : Fin n)))) := by
  first | exact @GlobalTheory.columns_indepMod | exact GlobalTheory.columns_indepMod | (intros; apply GlobalTheory.columns_indepMod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GramClassElementaryDivisorColumnsCongr
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GramClassElementaryDivisorColumnsCongr
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem hform_smul_smul (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (s t : L) (u v : Fin n → L) :
    Formalism.UG.hform σ J (s • u) (t • v) = σ s * t * Formalism.UG.hform σ J u v := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mulVec_single_int {n : ℕ} (V : Matrix (Fin n) (Fin n) L) (hV : ∀ i j, V i j ∈ Formalism.UG.intL L) (i : Fin n) :
    ∀ r, (V *ᵥ Pi.single i (1 : L)) r ∈ Formalism.UG.intL L := by
  intro r
  have : (V *ᵥ Pi.single i (1 : L)) r = V r i := by
    simp [mulVec, dotProduct, Pi.single_apply]
  rw [this]; exact hV r i

theorem single_eq_smul {n : ℕ} (i : Fin n) (c : L) : (Pi.single i c : Fin n → L) = c • Pi.single i (1 : L) := by
  ext r; by_cases h : r = i
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem gram_class_columns : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (JT : GL (Fin n') L) (x y : Matrix (Fin n') (Fin n) L)
    (V : Matrix (Fin n) (Fin n) L) (a : Fin n → ℕ), (∀ i j, V i j ∈ Formalism.UG.intL L) →
    (∀ c : Fin n → L, (∀ j, c j ∈ Formalism.UG.intL L) →
      ((∀ i, (x *ᵥ (V *ᵥ c)) i ∈ Formalism.UG.intL L) ↔ ∀ j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a j) (c j))) →
    GlobalTheory.Hk3.HoweG.GramEq σ JT x y →
    ∀ i j : Fin n, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (min (a i) (a j))
      (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (y *ᵥ (V *ᵥ Pi.single i (ϖ ^ a i))) (y *ᵥ (V *ᵥ Pi.single j (ϖ ^ a j))) -
        Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (x *ᵥ (V *ᵥ Pi.single i (ϖ ^ a i))) (x *ᵥ (V *ᵥ Pi.single j (ϖ ^ a j)))) := by
  intro L _ _ ϖ σ q hU n n' JT x y V a hV hiff hG i j
  have hϖv : Valued.v ϖ ≤ 1 := by
    rw [hU.2.2.2.1]; exact le_of_lt (by decide)
  have hϖ : ϖ ∈ Formalism.UG.intL L := hϖv
  set k := max (a i) (a j) with hk
  set c : L := ϖ ^ k with hc
  have hcI : c ∈ Formalism.UG.intL L := (Formalism.UG.intL L).pow_mem hϖ _

  have hcond : ∀ l, a l ≤ k → ∀ r, (x *ᵥ (c • (V *ᵥ Pi.single l (1 : L)))) r ∈ Formalism.UG.intL L := by
    intro l hl
    have hI : ∀ t, (Pi.single l c : Fin n → L) t ∈ Formalism.UG.intL L := by
      intro t; by_cases h : t = l
      · subst h; simpa using hcI
      · simp [Pi.single_apply, h, (Formalism.UG.intL L).zero_mem]
    have := (hiff (Pi.single l c) hI).mpr (by
      intro t; by_cases h : t = l
      · subst h
        refine ⟨ϖ ^ (k - a t), (Formalism.UG.intL L).pow_mem hϖ _, ?_⟩
        simp [hc, ← pow_add, Nat.add_sub_cancel' hl]
      · simpa [Pi.single_apply, h] using dvdPow_zero ϖ (a t))
    rwa [single_eq_smul, mulVec_smul] at this
  have hD := hG _ _ (mulVec_single_int V hV i) (mulVec_single_int V hV j) c hcI
    (hcond i (le_max_left _ _)) (hcond j (le_max_right _ _))
  refine ⟨_, hD, ?_⟩
  rw [single_eq_smul i, single_eq_smul j, mulVec_smul, mulVec_smul, mulVec_smul, mulVec_smul, mulVec_smul, mulVec_smul,
    hform_smul_smul, hform_smul_smul, map_pow, hU.2.2.1, hc, ← mul_sub, ← mul_assoc, ← pow_add, ← pow_add,
    min_add_max]

end GlobalTheory.Hk3.IntWitt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GramClassElementaryDivisorColumnsCongrStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramClass_elementaryDivisor_columns_congr : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (JT : GL (Fin n') L) (x y : Matrix (Fin n') (Fin n) L)
    (V : Matrix (Fin n) (Fin n) L) (a : Fin n → ℕ), (∀ i j, V i j ∈ Formalism.UG.intL L) →
    (∀ c : Fin n → L, (∀ j, c j ∈ Formalism.UG.intL L) →
      ((∀ i, (x *ᵥ (V *ᵥ c)) i ∈ Formalism.UG.intL L) ↔ ∀ j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a j) (c j))) →
    GlobalTheory.Hk3.HoweG.GramEq σ JT x y →
    ∀ i j : Fin n, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (min (a i) (a j))
      (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (y *ᵥ (V *ᵥ Pi.single i (ϖ ^ a i))) (y *ᵥ (V *ᵥ Pi.single j (ϖ ^ a j))) -
        Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (x *ᵥ (V *ᵥ Pi.single i (ϖ ^ a i))) (x *ᵥ (V *ᵥ Pi.single j (ϖ ^ a j)))) := by
  first | exact @GlobalTheory.Hk3.IntWitt.gram_class_columns | exact GlobalTheory.Hk3.IntWitt.gram_class_columns | (intros; apply GlobalTheory.Hk3.IntWitt.gram_class_columns <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsElementaryDivisorsIntegralPreimageLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsElementaryDivisorsIntegralPreimageLattice
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.IntWitt.ElemDiv

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mulVec_int {m k : ℕ} {A : Matrix (Fin m) (Fin k) L} (hA : ∀ i j, A i j ∈ Formalism.UG.intL L)
    {c : Fin k → L} (hc : ∀ j, c j ∈ Formalism.UG.intL L) : ∀ i, (A *ᵥ c) i ∈ Formalism.UG.intL L := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (hc j)

theorem diag_mulVec_of_lt {n n' : ℕ} (ϖ : L) (a : Fin n' → ℕ) (c : Fin n → L) (j : Fin n) (hj : (j : ℕ) < n') :
    ((Matrix.of fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0) *ᵥ c) ⟨j, hj⟩ =
      (if 0 < a ⟨j, hj⟩ then ϖ⁻¹ ^ a ⟨j, hj⟩ else 0) * c j := by
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    have : ¬ ((j : ℕ) = (b : ℕ)) := fun h => hb (Fin.ext h.symm)
    simp [this]
  · simp

theorem diag_mulVec_of_ge {n n' : ℕ} (ϖ : L) (a : Fin n' → ℕ) (c : Fin n → L) (i : Fin n') (hi : ¬ (i : ℕ) < n) :
    ((Matrix.of fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0) *ᵥ c) i = 0 := by
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  apply Finset.sum_eq_zero
  intro b _
  have : ¬ ((i : ℕ) = (b : ℕ)) := fun h => hi (h ▸ b.isLt)
  simp [this]

end GlobalTheory.Hk3.IntWitt.ElemDiv

end


open GlobalTheory.Hk3.IntWitt.ElemDiv in
theorem GlobalTheory.Hk3.IntWitt.exists_glInt_mulVec_mem_iff_forall_dvdPow : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L),
    Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
    ∀ (n n' : ℕ) (x : Matrix (Fin n') (Fin n) L),
    ∃ V : GL (Fin n) L, V ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) ∧ ∃ a : Fin n → ℕ,
      ∀ c : Fin n → L, (∀ j, c j ∈ Formalism.UG.intL L) →
        ((∀ i, (x *ᵥ ((V : Matrix (Fin n) (Fin n) L) *ᵥ c)) i ∈ Formalism.UG.intL L) ↔
          ∀ j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a j) (c j)) := by
  intro L _ _ ϖ hϖ n n' x
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  obtain ⟨P, P', Q, Q', a, hP, hP', hPP', hQ, hQ', hQQ', hE⟩ := GlobalTheory.Hk3.smith_int_approx L ϖ hϖ n n' x
  have hQ'Q : Q' * Q = 1 := mul_eq_one_comm.mp hQQ'
  have hP'P : P' * P = 1 := mul_eq_one_comm.mp hPP'
  set O := Formalism.UG.intL L with hOdef
  let QO : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨Q i j, hQ i j⟩
  let QO' : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨Q' i j, hQ' i j⟩
  have hinj : Function.Injective (O.subtype.mapMatrix : Matrix (Fin n) (Fin n) O →+* Matrix (Fin n) (Fin n) L) := by
    intro A B h; ext i j; exact congrFun (congrFun h i) j
  have hm1 : O.subtype.mapMatrix QO = Q := by ext i j; rfl
  have hm2 : O.subtype.mapMatrix QO' = Q' := by ext i j; rfl
  have e1 : QO * QO' = 1 := hinj (by rw [map_mul, map_one, hm1, hm2, hQQ'])
  have e2 : QO' * QO = 1 := hinj (by rw [map_mul, map_one, hm1, hm2, hQ'Q])
  let U : GL (Fin n) O := ⟨QO, QO', e1, e2⟩
  let V : GL (Fin n) L := ⟨Q, Q', hQQ', hQ'Q⟩
  refine ⟨V, ⟨U, Units.ext hm1⟩, fun j => if h : (j : ℕ) < n' then a ⟨j, h⟩ else 0, ?_⟩
  intro c hc
  set Dm : Matrix (Fin n') (Fin n) L :=
    Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0) with hDm
  have hPw : P *ᵥ (x *ᵥ (Q *ᵥ c)) = Dm *ᵥ c + (P * x * Q - Dm) *ᵥ c := by
    rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hEc : ∀ i, ((P * x * Q - Dm) *ᵥ c) i ∈ O := mulVec_int hE hc
  show (∀ i, (x *ᵥ (Q *ᵥ c)) i ∈ O) ↔ _
  constructor
  · intro hw j
    have hDc : ∀ i, (Dm *ᵥ c) i ∈ O := by
      intro i
      have h1 := mulVec_int hP hw i
      rw [hPw, Pi.add_apply] at h1
      have := Subring.sub_mem _ h1 (hEc i)
      rwa [add_sub_cancel_right] at this
    by_cases hj : (j : ℕ) < n'
    · simp only [dif_pos hj]
      have h2 := hDc ⟨j, hj⟩
      rw [hDm, diag_mulVec_of_lt ϖ a c j hj] at h2
      split_ifs at h2 with ha
      · refine ⟨ϖ⁻¹ ^ a ⟨j, hj⟩ * c j, h2, ?_⟩
        rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hϖ0, one_pow, one_mul]
      · have : a ⟨j, hj⟩ = 0 := by omega
        rw [this]; exact dvdPow_zero_iff.mpr (hc j)
    · simp only [dif_neg hj]; exact dvdPow_zero_iff.mpr (hc j)
  · intro hd
    have hDc : ∀ i, (Dm *ᵥ c) i ∈ O := by
      intro i
      by_cases hi : (i : ℕ) < n
      · have hij : i = ⟨((⟨i, hi⟩ : Fin n) : ℕ), i.isLt⟩ := Fin.ext rfl
        rw [hij, hDm, diag_mulVec_of_lt ϖ a c ⟨i, hi⟩ i.isLt]
        split_ifs with ha
        · have h3 := hd ⟨i, hi⟩
          simp only [dif_pos i.isLt] at h3
          obtain ⟨b, hb, hcb⟩ := h3
          rw [hcb, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hϖ0, one_pow, one_mul]; exact hb
        · rw [zero_mul]; exact Subring.zero_mem _
      · rw [hDm, diag_mulVec_of_ge ϖ a c i hi]; exact Subring.zero_mem _
    have hPwi : ∀ i, (P *ᵥ (x *ᵥ (Q *ᵥ c))) i ∈ O := by
      intro i; rw [hPw, Pi.add_apply]; exact Subring.add_mem _ (hDc i) (hEc i)
    intro i
    have key : ∀ w : Fin n' → L, w = P' *ᵥ (P *ᵥ w) := fun w => by
      rw [Matrix.mulVec_mulVec, hP'P, Matrix.one_mulVec]
    rw [key (x *ᵥ (Q *ᵥ c))]; exact mulVec_int hP' hPwi i
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsElementaryDivisorsIntegralPreimageLatticeStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_elementaryDivisors_integral_preimage_lattice : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L),
    Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
    ∀ (n n' : ℕ) (x : Matrix (Fin n') (Fin n) L),
    ∃ V : GL (Fin n) L, V ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) ∧ ∃ a : Fin n → ℕ,
      ∀ c : Fin n → L, (∀ j, c j ∈ Formalism.UG.intL L) →
        ((∀ i, (x *ᵥ ((V : Matrix (Fin n) (Fin n) L) *ᵥ c)) i ∈ Formalism.UG.intL L) ↔
          ∀ j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a j) (c j)) := by
  first | exact @GlobalTheory.Hk3.IntWitt.exists_glInt_mulVec_mem_iff_forall_dvdPow | exact GlobalTheory.Hk3.IntWitt.exists_glInt_mulVec_mem_iff_forall_dvdPow | (intros; apply GlobalTheory.Hk3.IntWitt.exists_glInt_mulVec_mem_iff_forall_dvdPow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntUnitaryOfGramClass
noncomputable section

open Matrix

namespace GlobalTheory.Hk3.HoweG

theorem exists_intUnitary_of_gramClass : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n n' : ℕ)
    (JS : GL (Fin n) L) (JT : GL (Fin n') L), Formalism.UG.IsUnramInv ϖ σ q → Odd q →
    JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ x y : Matrix (Fin n') (Fin n) L,
    (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.HoweG.HomA σ JS JT x y → GlobalTheory.Hk3.HoweG.GramEq σ JT x y → GlobalTheory.Hk3.HoweDuality.latIdx y = GlobalTheory.Hk3.HoweDuality.latIdx x →
    ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      ∀ i j, (y - ((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) i j ∈ Formalism.UG.intL L := by
  intro L _ _ _ ϖ σ q n n' JS JT hU hq hJS hJT hS hT x y _hG hA hGr hidx
  classical
  have hvϖ := hU.2.2.2.1
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hvϖ; exact WithZero.zero_ne_coe hvϖ
  have hϖint : ϖ ∈ Formalism.UG.intL L := by
    unfold Formalism.UG.intL
    rw [Valuation.mem_integer_iff, hvϖ]
    exact_mod_cast (show Multiplicative.ofAdd (-1 : ℤ) ≤ 1 by decide)
  have mulVec_int : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) L) (v : Fin b → L), (∀ i j, M i j ∈ Formalism.UG.intL L) →
      (∀ j, v j ∈ Formalism.UG.intL L) → ∀ i, (M *ᵥ v) i ∈ Formalism.UG.intL L := by
    intro a b M v hM hv i
    simp only [Matrix.mulVec, dotProduct]
    exact (Formalism.UG.intL L).sum_mem fun j _ => (Formalism.UG.intL L).mul_mem (hM i j) (hv j)
  obtain ⟨V, hV, a, hxV⟩ := GlobalTheory.T.exists_elementaryDivisors_integral_preimage_lattice L ϖ hvϖ n n' x
  obtain ⟨g0, hg0⟩ := hV
  have hVint : ∀ i j, (V : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
    intro i j; rw [← hg0]; exact ((g0 : Matrix (Fin n) (Fin n) (Formalism.UG.intL L)) i j).2
  have hVinv : ∀ i j, ((V⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
    intro i j; rw [← hg0, ← map_inv]
    exact (((g0⁻¹ : GL (Fin n) (Formalism.UG.intL L)) : Matrix (Fin n) (Fin n) (Formalism.UG.intL L)) i j).2
  set Vm : Matrix (Fin n) (Fin n) L := (V : Matrix (Fin n) (Fin n) L) with hVm
  have hyV : ∀ c : Fin n → L, (∀ j, c j ∈ Formalism.UG.intL L) →
      ((∀ i, (y *ᵥ (Vm *ᵥ c)) i ∈ Formalism.UG.intL L) ↔ ∀ j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a j) (c j)) := by
    intro c hc
    have hu : ∀ i, (Vm *ᵥ c) i ∈ Formalism.UG.intL L := mulVec_int Vm c hVint hc
    rw [← hxV c hc]
    exact ⟨fun h => GlobalTheory.T.latticeKernel_le_of_matrixLatticeIndex_eq L ϖ σ q hU n n' x y hA.1 hidx _ hu h, fun h => hA.1 _ hu h⟩
  let ej : Fin n → Fin n → L := fun j => Pi.single j (ϖ ^ a j)
  have hej_int : ∀ j k, ej j k ∈ Formalism.UG.intL L := by
    intro j k
    by_cases h : k = j
    · subst h; simpa [ej] using (Formalism.UG.intL L).pow_mem hϖint (a k)
    · simp [ej, Pi.single_apply, h]
  have hej_dvd : ∀ j k, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a k) (ej j k) := by
    intro j k
    by_cases h : k = j
    · subst h; exact ⟨1, (Formalism.UG.intL L).one_mem, by simp [ej]⟩
    · simpa [ej, Pi.single_apply, h] using GlobalTheory.Hk3.IntWitt.dvdPow_zero ϖ (a k)
  let zx : {j : Fin n // 0 < a j} → Fin n' → L := fun j => x *ᵥ (Vm *ᵥ ej j)
  let zy : {j : Fin n // 0 < a j} → Fin n' → L := fun j => y *ᵥ (Vm *ᵥ ej j)
  have hzx : ∀ j r, zx j r ∈ Formalism.UG.intL L := fun j => (hxV _ (hej_int j)).mpr (hej_dvd j)
  have hzy : ∀ j r, zy j r ∈ Formalism.UG.intL L := fun j => (hyV _ (hej_int j)).mpr (hej_dvd j)
  have hix : GlobalTheory.Hk3.IntWitt.IndepMod ϖ zx := GlobalTheory.T.elementaryDivisor_columns_independentModUniformizer L ϖ hvϖ n n' x Vm a hxV
  have hiy : GlobalTheory.Hk3.IntWitt.IndepMod ϖ zy := GlobalTheory.T.elementaryDivisor_columns_independentModUniformizer L ϖ hvϖ n n' y Vm a hyV
  have hgr := GlobalTheory.T.gramClass_elementaryDivisor_columns_congr L ϖ σ q hU n n' JT x y Vm a hVint hxV hGr
  obtain ⟨h, hh, hcong⟩ := GlobalTheory.T.integralWittTheorem_mod_uniformizerPow L ϖ σ q hU hq n' JT hJT hT {j : Fin n // 0 < a j} (fun j => a j) zx zy
    (fun j => j.2) hzx hzy hix hiy (fun i j => hgr i j)
  refine ⟨h, hh, ?_⟩
  set H : Matrix (Fin n') (Fin n') L := ((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) with hH
  have hHint : ∀ i j, H i j ∈ Formalism.UG.intL L := by
    obtain ⟨h0, hh0⟩ := hh
    intro i j; rw [hH, ← hh0]; exact ((h0 : Matrix (Fin n') (Fin n') (Formalism.UG.intL L)) i j).2
  set M := y - H * x with hM
  have hMv : ∀ w : Fin n → L, M *ᵥ w = y *ᵥ w - H *ᵥ (x *ᵥ w) := by
    intro w; rw [hM, Matrix.sub_mulVec, Matrix.mulVec_mulVec]
  have hcol : ∀ j i, (M *ᵥ (Vm *ᵥ Pi.single j 1)) i ∈ Formalism.UG.intL L := by
    intro j i
    by_cases ha : a j = 0
    · have he : Pi.single j (1 : L) = ej j := by simp [ej, ha]
      rw [he, hMv]
      exact (Formalism.UG.intL L).sub_mem ((hyV _ (hej_int j)).mpr (hej_dvd j) i)
        (mulVec_int H _ hHint ((hxV _ (hej_int j)).mpr (hej_dvd j)) i)
    · have hpos : 0 < a j := Nat.pos_of_ne_zero ha
      obtain ⟨b, hb, hbe⟩ := hcong ⟨j, hpos⟩ i
      have he : ej j = ϖ ^ a j • Pi.single j (1 : L) := by
        funext k; simp [ej, Pi.single_apply]
      have key : ϖ ^ a j * (M *ᵥ (Vm *ᵥ Pi.single j 1)) i = ϖ ^ a j * (-b) := by
        have : (M *ᵥ (Vm *ᵥ ej j)) i = -((H *ᵥ zx ⟨j, hpos⟩) i - zy ⟨j, hpos⟩ i) := by
          rw [hMv]; simp only [zx, zy, Pi.sub_apply]; ring
        rw [he, Matrix.mulVec_smul, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at this
        rw [this, hbe]; ring
      have := mul_left_cancel₀ (pow_ne_zero _ hϖ0) key
      rw [this]; exact (Formalism.UG.intL L).neg_mem hb
  intro i r
  have hMe : M = (M * Vm) * ((V⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    rw [Matrix.mul_assoc, hVm, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  rw [hMe, Matrix.mul_apply]
  refine (Formalism.UG.intL L).sum_mem fun k _ => (Formalism.UG.intL L).mul_mem ?_ (hVinv k r)
  have hc := hcol k i
  rwa [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.col_apply] at hc

end GlobalTheory.Hk3.HoweG

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntUnitaryOfGramClassStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_intUnitary_of_gramClass_alt : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n n' : ℕ)
    (JS : GL (Fin n) L) (JT : GL (Fin n') L), Formalism.UG.IsUnramInv ϖ σ q → Odd q →
    JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ x y : Matrix (Fin n') (Fin n) L,
    (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.HoweG.HomA σ JS JT x y → GlobalTheory.Hk3.HoweG.GramEq σ JT x y → GlobalTheory.Hk3.HoweDuality.latIdx y = GlobalTheory.Hk3.HoweDuality.latIdx x →
    ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      ∀ i j, (y - ((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) i j ∈ Formalism.UG.intL L := by
  first | exact @GlobalTheory.Hk3.HoweG.exists_intUnitary_of_gramClass | exact GlobalTheory.Hk3.HoweG.exists_intUnitary_of_gramClass | (intros; apply GlobalTheory.Hk3.HoweG.exists_intUnitary_of_gramClass <;> assumption)
end
