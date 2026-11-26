module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.DTw
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.PhiSub

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.CornerCoc
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem cut_conj {F : Type} [Field F] {n : ℕ} (p q : Fin n → Prop) [DecidablePred p] [DecidablePred q]
    [∀ i j, Decidable (p i ∧ q j)] (A Z B : Matrix (Fin n) (Fin n) F)
    (hA : ∀ i k, ¬ (p i ↔ p k) → A i k = 0) (hB : ∀ i k, ¬ (q i ↔ q k) → B i k = 0) :
    (Matrix.of fun i j => if p i ∧ q j then (A * Z * B) i j else 0) =
      A * (Matrix.of fun i j => if p i ∧ q j then Z i j else 0) * B := by
  ext i j
  have key : (if p i ∧ q j then (A * Z * B) i j else 0) =
      ∑ m, ∑ k, if p i ∧ q j then A i k * Z k m * B m j else 0 := by
    split_ifs
    · simp only [Matrix.mul_apply, Finset.sum_mul]
    · simp
  rw [Matrix.of_apply, key]
  simp only [Matrix.mul_apply, Finset.sum_mul, Matrix.of_apply]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases h1 : p i ↔ p k
  · by_cases h2 : q m ↔ q j
    · by_cases h : p i ∧ q j
      · rw [if_pos h, if_pos ⟨h1.1 h.1, h2.2 h.2⟩]
      · rw [if_neg h, if_neg (fun h' => h ⟨h1.2 h'.1, h2.1 h'.2⟩)]; simp
    · simp [hB m j h2]
  · simp [hA i k h1]

private theorem cV_conj {F : Type} [Field F] {n a : ℕ} {A B : Matrix (Fin n) (Fin n) F}
    (hA : A ∈ Ev F F n a) (hB : B ∈ Ev F F n a) (Z : Matrix (Fin n) (Fin n) F) :
    cV a (A * Z * B) = A * cV a Z * B ∧ cV' a (A * Z * B) = A * cV' a Z * B := by
  have hA' : ∀ i k : Fin n, ¬ ((i : ℕ) < a ↔ (k : ℕ) < a) → A i k = 0 := fun i k h => by
    simpa using (hA i k).2 h
  have hB' : ∀ i k : Fin n, ¬ ((i : ℕ) < a ↔ (k : ℕ) < a) → B i k = 0 := fun i k h => by
    simpa using (hB i k).2 h
  exact ⟨cut_conj (fun i => (i : ℕ) < a) (fun i => ¬ (i : ℕ) < a) A Z B hA'
      (fun i k h => hB' i k (fun e => h (not_congr e))),
    cut_conj (fun i => ¬ (i : ℕ) < a) (fun i => (i : ℕ) < a) A Z B
      (fun i k h => hA' i k (fun e => h (not_congr e))) hB'⟩

private theorem cV_lin {F : Type} [Field F] {n : ℕ} (a : ℕ) (c : F) (Y Z : Matrix (Fin n) (Fin n) F) :
    (cV a (Y + c • Z) = cV a Y + c • cV a Z ∧ cV' a (Y + c • Z) = cV' a Y + c • cV' a Z) ∧
    (cV a (c • Z - Y) = c • cV a Z - cV a Y ∧ cV' a (c • Z - Y) = c • cV' a Z - cV' a Y) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> ext i j <;>
    simp only [cV, cV', Matrix.of_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply] <;>
    split_ifs <;> simp

theorem UpperTheory.V.Pa.Det.cornerCoc :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (χ : G → F) (S : Set G) (z : G → Matrix (Fin n) (Fin n) F), TwCoc χ D.r S z → (TwCoc χ D.r S fun g => cV D.a (z g)) ∧ (TwCoc χ D.r S fun g => cV' D.a (z g)) ∧ (∀ Y g, cV D.a (dTw χ D.r Y g) = dTw χ D.r (cV D.a Y) g ∧ cV' D.a (dTw χ D.r Y g) = dTw χ D.r (cV' D.a Y) g) ∧ ∀ Z : Matrix (Fin n) (Fin n) F, cV D.a Z ∈ Od F F n D.a ∧ cV' D.a Z ∈ Od F F n D.a ∧ (cV D.a Z)ᵀ = cV' D.a Zᵀ ∧ (Z ∈ Od F F n D.a → cV D.a Z + cV' D.a Z = Z) := by
  intro F G _ _ n D χ S z hz
  refine ⟨fun g hg h hh => ?_, fun g hg h hh => ?_, fun Y g => ⟨?_, ?_⟩, fun Z => ⟨?_, ?_, ?_, fun hZ => ?_⟩⟩
  · beta_reduce
    rw [hz g hg h hh, (cV_lin _ _ _ _).1.1, (cV_conj (D.ev _) (D.ev _) _).1]
  · beta_reduce
    rw [hz g hg h hh, (cV_lin _ _ _ _).1.2, (cV_conj (D.ev _) (D.ev _) _).2]
  · unfold dTw
    rw [(cV_lin _ _ _ _).2.1, (cV_conj (D.ev _) (D.ev _) _).1]
  · unfold dTw
    rw [(cV_lin _ _ _ _).2.2, (cV_conj (D.ev _) (D.ev _) _).2]
  · intro i j
    refine ⟨fun e => ?_, fun _ => Submodule.mem_top⟩
    rw [Submodule.mem_bot, cV, Matrix.of_apply, if_neg (fun h => h.2 (e.1 h.1))]
  · intro i j
    refine ⟨fun e => ?_, fun _ => Submodule.mem_top⟩
    rw [Submodule.mem_bot, cV', Matrix.of_apply, if_neg (fun h => h.1 (e.2 h.2))]
  · ext i j
    simp only [cV, cV', Matrix.of_apply, Matrix.transpose_apply, and_comm]
  · ext i j
    have h0 : ((i : ℕ) < D.a ↔ (j : ℕ) < D.a) → Z i j = 0 := fun e => by simpa using (hZ i j).1 e
    simp only [cV, cV', Matrix.of_apply, Matrix.add_apply]
    by_cases hi : (i : ℕ) < D.a <;> by_cases hj : (j : ℕ) < D.a
    · simp [hi, hj, h0 (iff_of_true hi hj)]
    · rw [if_pos ⟨hi, hj⟩, if_neg (fun h => h.1 hi), add_zero]
    · rw [if_neg (fun h => hi h.1), if_pos ⟨hi, hj⟩, zero_add]
    · rw [if_neg (fun h => hi h.1), if_neg (fun h => hj h.2), add_zero, h0 (iff_of_false hi hj)]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.BlockPrinc
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Shapiro
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem shapiro_projection_twisted_cocycle {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (χ : G → F) (s : F)
    (z : G → Matrix (Fin n) (Fin n) F) (Y : Matrix (Fin n) (Fin n) F) (hχ : ∀ g, χ (D.σ g) = χ g)
    (hs : s * s = 1) (hp : ∀ g, z (D.σ g) = s • (z g)ᵀ)
    (P : Matrix (Fin n) (Fin n) F → Matrix (Fin n) (Fin n) F)
    (hPP : ∀ Z, P (P Z) = P Z) (hPs : ∀ Z, P (s • Z) = s • P Z)
    (hPd : ∀ g, P (dTw χ D.r Y g) = dTw χ D.r (P Y) g)
    (hsum : ∀ g, P (z g) + (P (z g)ᵀ)ᵀ = z g)
    (h1 : P Y ∈ Od F F n D.a) (h2 : (P Y)ᵀ ∈ Od F F n D.a)
    (h : ∀ g, P (z g) = dTw χ D.r Y g) :
    ∃ Y' ∈ Od F F n D.a, s • Y'ᵀ = Y' ∧ ∀ g, z g = dTw χ D.r Y' g := by
  refine ⟨P Y + s • (P Y)ᵀ, Submodule.add_mem _ h1 (Submodule.smul_mem _ s h2), ?_, ?_⟩
  · rw [transpose_add, transpose_smul, transpose_transpose, smul_add, smul_smul, hs, one_smul,
      add_comm]
  · intro g
    have hA : ∀ k, dTw χ D.r (P Y) k = P (z k) := fun k => by
      rw [← hPd, ← h, hPP]
    have hzT : (z g)ᵀ = s • z (D.σ g) := by
      rw [hp, smul_smul, hs, one_smul]
    have hB : s • dTw χ D.r (P Y)ᵀ g = (P (z g)ᵀ)ᵀ := by
      rw [hzT, hPs, ← hA, Det.dSigma D χ (P Y) g hχ, transpose_smul, transpose_transpose]
    have hlin : dTw χ D.r (P Y + s • (P Y)ᵀ) g = dTw χ D.r (P Y) g + s • dTw χ D.r (P Y)ᵀ g := by
      simp only [dTw, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
      module
    rw [hlin, hA, hB, hsum]

theorem UpperTheory.V.Pa.Det.shapiro :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (χ : G → F) (s : F) (z : G → Matrix (Fin n) (Fin n) F) (Y : Matrix (Fin n) (Fin n) F), (∀ g, χ (D.σ g) = χ g) → s * s = 1 → TwCoc χ D.r Set.univ z → (∀ g, z g ∈ Od F F n D.a) → (∀ g, z (D.σ g) = s • (z g)ᵀ) → ((∀ g, cV D.a (z g) = dTw χ D.r Y g) ∨ ∀ g, cV' D.a (z g) = dTw χ D.r Y g) → ∃ Y' ∈ Od F F n D.a, s • Y'ᵀ = Y' ∧ ∀ g, z g = dTw χ D.r Y' g := by
  intro F G _ _ n D χ s z Y hχ hs hz hod hp h
  obtain ⟨-, -, hd, hc⟩ := UpperTheory.V.Pa.Det.cornerCoc D χ Set.univ z hz
  have ht : ∀ Z : Matrix (Fin n) (Fin n) F, (cV' D.a Z)ᵀ = cV D.a Zᵀ := fun Z => by
    have := (hc Zᵀ).2.2.1
    rw [transpose_transpose] at this
    rw [← this, transpose_transpose]
  rcases h with h | h
  · refine shapiro_projection_twisted_cocycle D χ s z Y hχ hs hp (cV D.a) (fun Z => ?_) (fun Z => ?_) (fun g => (hd Y g).1)
      (fun g => ?_) (hc Y).1 ?_ h
    · ext i j
      simp only [cV, Matrix.of_apply]
      split_ifs <;> rfl
    · ext i j
      simp only [cV, Matrix.of_apply, Matrix.smul_apply]
      split_ifs <;> simp
    · rw [(hc _).2.2.1, transpose_transpose]
      exact (hc _).2.2.2 (hod g)
    · rw [(hc _).2.2.1]
      exact (hc _).2.1
  · refine shapiro_projection_twisted_cocycle D χ s z Y hχ hs hp (cV' D.a) (fun Z => ?_) (fun Z => ?_) (fun g => (hd Y g).2)
      (fun g => ?_) (hc Y).2.1 ?_ h
    · ext i j
      simp only [cV', Matrix.of_apply]
      split_ifs <;> rfl
    · ext i j
      simp only [cV', Matrix.of_apply, Matrix.smul_apply]
      split_ifs <;> simp
    · rw [ht, transpose_transpose, add_comm]
      exact (hc _).2.2.2 (hod g)
    · rw [ht]
      exact (hc _).1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Infres
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section SlopeTestRemainingChoices

variable {F : Type} [Field F] {n : ℕ}

private def sgnM (F : Type) [Field F] (n a : ℕ) : Matrix (Fin n) (Fin n) F :=
  Matrix.diagonal fun i => if (i : ℕ) < a then 1 else -1

private theorem sgnM_sq (a : ℕ) : sgnM F n a * sgnM F n a = 1 := by
  rw [sgnM, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  split_ifs <;> simp

private theorem sgnM_conj_apply (a : ℕ) (X : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    (sgnM F n a * X * sgnM F n a) i j = if ((i : ℕ) < a ↔ (j : ℕ) < a) then X i j else -X i j := by
  simp only [sgnM, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a <;> simp [hi, hj]

private theorem sgnM_ev (a : ℕ) {X : Matrix (Fin n) (Fin n) F} (hX : X ∈ Ev F F n a) :
    sgnM F n a * X * sgnM F n a = X := by
  have hX' : ∀ i j : Fin n, (((i : ℕ) < a ↔ (j : ℕ) < a) → X i j ∈ (⊤ : Submodule F F)) ∧
      (¬((i : ℕ) < a ↔ (j : ℕ) < a) → X i j ∈ (⊥ : Submodule F F)) := hX
  ext i j
  rw [sgnM_conj_apply]
  split_ifs with h
  · rfl
  · have h0 : X i j = 0 := by simpa using (hX' i j).2 h
    rw [h0, neg_zero]

private theorem sgnM_od (a : ℕ) {X : Matrix (Fin n) (Fin n) F} (hX : X ∈ Od F F n a) :
    sgnM F n a * X * sgnM F n a = -X := by
  have hX' : ∀ i j : Fin n, (((i : ℕ) < a ↔ (j : ℕ) < a) → X i j ∈ (⊥ : Submodule F F)) ∧
      (¬((i : ℕ) < a ↔ (j : ℕ) < a) → X i j ∈ (⊤ : Submodule F F)) := hX
  ext i j
  rw [sgnM_conj_apply, Matrix.neg_apply]
  split_ifs with h
  · have h0 : X i j = 0 := by simpa using (hX' i j).1 h
    rw [h0, neg_zero]
  · rfl

private theorem od_of_sgnM (two : (2 : F) ≠ 0) (a : ℕ) {X : Matrix (Fin n) (Fin n) F}
    (hX : sgnM F n a * X * sgnM F n a = -X) : X ∈ Od F F n a := by
  show ∀ i j : Fin n, (((i : ℕ) < a ↔ (j : ℕ) < a) → X i j ∈ (⊥ : Submodule F F)) ∧
      (¬((i : ℕ) < a ↔ (j : ℕ) < a) → X i j ∈ (⊤ : Submodule F F))
  intro i j
  refine ⟨fun h => ?_, fun _ => Submodule.mem_top⟩
  have e := congrFun (congrFun hX i) j
  rw [sgnM_conj_apply, if_pos h, Matrix.neg_apply] at e
  have h2 : (2 : F) * X i j = 0 := by rw [two_mul]; nth_rewrite 1 [e]; ring
  rw [Submodule.mem_bot]
  exact (mul_eq_zero.mp h2).resolve_left two

private theorem sgnM_mul (a : ℕ) (X Y : Matrix (Fin n) (Fin n) F) :
    sgnM F n a * (X * Y) * sgnM F n a = (sgnM F n a * X * sgnM F n a) * (sgnM F n a * Y * sgnM F n a) := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (sgnM F n a) (sgnM F n a), sgnM_sq, Matrix.one_mul]

private theorem sgnM_dTw {G : Type} [Group G] (D : DetFr F G n) (χ : G → F) (Y : Matrix (Fin n) (Fin n) F) (g : G) :
    sgnM F n D.a * dTw χ D.r Y g * sgnM F n D.a = dTw χ D.r (sgnM F n D.a * Y * sgnM F n D.a) g := by
  simp only [dTw, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, sgnM_mul,
    sgnM_ev D.a (D.ev g), sgnM_ev D.a (D.ev g⁻¹)]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Pa.Det.infres :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (χ : G → F) (z : G → Matrix (Fin n) (Fin n) F) (Y : Matrix (Fin n) (Fin n) F), (∀ g h, χ (g * h) = χ g * χ h) → (∀ g ∈ D.G', χ g = 1) → TwCoc χ D.r Set.univ z → (∀ g, z g ∈ Od F F n D.a) → (∀ g ∈ D.G', z g = dTw χ D.r Y g) → ∃ Y' ∈ Od F F n D.a, ∀ g, z g = dTw χ D.r Y' g := by
  intro F G _ _ n D χ z Y hχ hχ' hz hzod hzG
  have two : (2 : F) ≠ 0 := D.two
  have hdTw_sub : ∀ A B g, dTw χ D.r (A - B) g = dTw χ D.r A g - dTw χ D.r B g := by
    intro A B g
    simp only [dTw, Matrix.mul_sub, Matrix.sub_mul, smul_sub]
    abel
  have hdTw_smul : ∀ (c : F) A g, dTw χ D.r (c • A) g = c • dTw χ D.r A g := by
    intro c A g
    simp only [dTw, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    rw [smul_comm]
  have hdTw_neg : ∀ A g, dTw χ D.r (-A) g = -dTw χ D.r A g := by
    intro A g
    simp only [dTw, Matrix.mul_neg, Matrix.neg_mul, smul_neg]
    abel
  have hdc : ∀ A g h, dTw χ D.r A (g * h) = dTw χ D.r A g + χ g • (D.r g * dTw χ D.r A h * D.r g⁻¹) := by
    intro A g h
    simp only [dTw, hχ, _root_.mul_inv_rev, map_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, smul_sub, smul_smul, Matrix.mul_assoc]
    abel
  have hss := sgnM_sq (F := F) (n := n) D.a
  have hcc : ∀ A : Matrix (Fin n) (Fin n) F,
      sgnM F n D.a * (sgnM F n D.a * A * sgnM F n D.a) * sgnM F n D.a = A := by
    intro A
    rw [show sgnM F n D.a * (sgnM F n D.a * A * sgnM F n D.a) * sgnM F n D.a
        = (sgnM F n D.a * sgnM F n D.a) * A * (sgnM F n D.a * sgnM F n D.a) by
      simp only [Matrix.mul_assoc], hss, Matrix.one_mul, Matrix.mul_one]
  set Y' : Matrix (Fin n) (Fin n) F := (2 : F)⁻¹ • (Y - sgnM F n D.a * Y * sgnM F n D.a) with hY'
  have hY'od : Y' ∈ Od F F n D.a := by
    apply od_of_sgnM two
    rw [hY', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, hcc, ← smul_neg, neg_sub]
  have hG' : ∀ h ∈ D.G', z h = dTw χ D.r Y' h := by
    intro h hh
    have h1 := hzG h hh
    have h2 : -z h = dTw χ D.r (sgnM F n D.a * Y * sgnM F n D.a) h := by
      rw [← sgnM_od D.a (hzod h), h1, sgnM_dTw]
    rw [hY', hdTw_smul, hdTw_sub, ← h1, ← h2, sub_neg_eq_add, ← two_smul F (z h), smul_smul,
      inv_mul_cancel₀ two, one_smul]
  have key : ∀ g, z g - dTw χ D.r Y' g = 0 := by
    intro g
    set w : G → Matrix (Fin n) (Fin n) F := fun x => z x - dTw χ D.r Y' x with hw
    have hwc : ∀ x y, w (x * y) = w x + χ x • (D.r x * w y * D.r x⁻¹) := by
      intro x y
      simp only [hw]
      rw [hz x trivial y trivial, hdc]
      simp only [Matrix.mul_sub, Matrix.sub_mul, smul_sub]
      abel
    have hw0 : ∀ h ∈ D.G', w h = 0 := fun h hh => by
      simp only [hw]
      rw [hG' h hh, sub_self]
    have hcomm : ∀ h ∈ D.G', D.r h * w g = w g * D.r h := by
      intro h hh
      have hh' : g⁻¹ * h * g ∈ D.G' := by
        have hm := D.G'.mul_mem (D.comm g⁻¹ h) hh
        simpa [mul_assoc] using hm
      have e1 := hwc g (g⁻¹ * h * g)
      have e2 := hwc h g
      rw [hw0 _ hh', Matrix.mul_zero, Matrix.zero_mul, smul_zero, add_zero] at e1
      rw [hw0 _ hh, hχ' h hh, one_smul, zero_add] at e2
      have heq : g * (g⁻¹ * h * g) = h * g := by group
      rw [heq, e2] at e1
      calc D.r h * w g = D.r h * w g * (D.r h⁻¹ * D.r h) := by
            rw [← map_mul D.r h⁻¹ h, inv_mul_cancel, map_one, Matrix.mul_one]
        _ = (D.r h * w g * D.r h⁻¹) * D.r h := by simp only [Matrix.mul_assoc]
        _ = w g * D.r h := by rw [e1]
    have hwod : w g ∈ Od F F n D.a := by
      simp only [hw]
      refine Submodule.sub_mem _ (hzod g) ?_
      apply od_of_sgnM two
      rw [sgnM_dTw, sgnM_od D.a hY'od, hdTw_neg]
    exact (Det.central D (w g) hcomm).1 hwod
  exact ⟨Y', hY'od, fun g => sub_eq_zero.mp (key g)⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.RelMove
noncomputable section

open Matrix

namespace UpperTheory.V.Pa.Det

private theorem der_mul {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n)
    (z : G → Matrix (Fin n) (Fin n) F) (hz : TwCoc (fun _ => 1) D.r D.G' z) {g h : G} (hg : g ∈ D.G') (hh : h ∈ D.G') :
    z (g * h) * D.r (g * h) = z g * D.r g * D.r h + D.r g * (z h * D.r h) := by
  have h1 := hz g hg h hh
  simp only [one_smul] at h1
  have hinv : D.r g⁻¹ * D.r g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  rw [h1, map_mul, add_mul]
  congr 1
  · simp only [Matrix.mul_assoc]
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (D.r g⁻¹), hinv, Matrix.one_mul]

private theorem move_one {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n)
    (z : G → Matrix (Fin n) (Fin n) F) (i j : Fin n) (hz : TwCoc (fun _ => 1) D.r D.G' z) (hk : D.KillsRel z i j)
    (c : G →₀ F) (hc : ∀ g ∈ c.support, g ∈ D.G') (h0 : c.sum (fun g x => x • D.r g) = 0)
    {u v : G} (hu : u ∈ D.G') (hv : v ∈ D.G') :
    (D.r u * (c.sum fun g x => x • (z g * D.r g)) * D.r v) i j = 0 := by
  classical
  have hsum : ∀ M : G → Matrix (Fin n) (Fin n) F,
      (Finsupp.mapDomain (fun g => u * g * v) c).sum (fun g x => x • M g) = c.sum (fun g x => x • M (u * g * v)) := by
    intro M
    exact Finsupp.sum_mapDomain_index (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)
  have hsupp : ∀ g ∈ (Finsupp.mapDomain (fun g => u * g * v) c).support, g ∈ D.G' := by
    intro g hg
    obtain ⟨k, hk', rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hg)
    exact D.G'.mul_mem (D.G'.mul_mem hu (hc k hk')) hv
  have hr : ∀ M : G → Matrix (Fin n) (Fin n) F, ∀ P Q : Matrix (Fin n) (Fin n) F,
      P * (c.sum fun g x => x • M g) * Q = c.sum fun g x => x • (P * M g * Q) := by
    intro M P Q
    simp only [Finsupp.sum, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  have h0' : (Finsupp.mapDomain (fun g => u * g * v) c).sum (fun g x => x • D.r g) = 0 := by
    rw [hsum]
    simp only [map_mul]
    rw [← hr, h0, Matrix.mul_zero, Matrix.zero_mul]
  have key := hk _ hsupp h0'
  rw [hsum] at key
  have expand : ∀ g ∈ c.support, c g • (z (u * g * v) * D.r (u * g * v)) =
      c g • (z u * D.r u * D.r g * D.r v) + c g • (D.r u * (z g * D.r g) * D.r v) + c g • (D.r u * D.r g * (z v * D.r v)) := by
    intro g hg
    rw [mul_assoc, der_mul D z hz hu (D.G'.mul_mem (hc g hg) hv), der_mul D z hz (hc g hg) hv, ← smul_add, ← smul_add]
    congr 1
    simp only [map_mul, Matrix.mul_add, Matrix.mul_assoc, add_assoc]
  have eq : (c.sum fun g x => x • (z (u * g * v) * D.r (u * g * v))) =
      z u * D.r u * (c.sum fun g x => x • D.r g) * D.r v + D.r u * (c.sum fun g x => x • (z g * D.r g)) * D.r v
        + D.r u * (c.sum fun g x => x • D.r g) * (z v * D.r v) := by
    rw [hr, hr, hr]
    simp only [Finsupp.sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl expand
  rw [eq, h0] at key
  simpa using key

private theorem single_mem {F : Type} [Field F] {n a : ℕ} (i i' : Fin n) (h : (i : ℕ) < a ↔ (i' : ℕ) < a) :
    Matrix.single i i' (1 : F) ∈ Ev F F n a := by
  intro p q
  refine ⟨fun _ => Submodule.mem_top, fun hpq => ?_⟩
  rw [Submodule.mem_bot, Matrix.single_apply]
  split_ifs with hh
  · obtain ⟨rfl, rfl⟩ := hh
    exact absurd h hpq
  · rfl

theorem relMove {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n)
    (z : G → Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    TwCoc (fun _ => 1) D.r D.G' z → D.KillsRel z i j →
      ∀ i' j' : Fin n, ((i : ℕ) < D.a ↔ (i' : ℕ) < D.a) → ((j : ℕ) < D.a ↔ (j' : ℕ) < D.a) → D.KillsRel z i' j' := by
  intro hz hk i' j' hi hj c hc h0
  have hA : Matrix.single i i' (1 : F) ∈ Submodule.span F (D.r '' D.G') := by
    rw [D.span]
    exact single_mem i i' hi
  have hB : Matrix.single j' j (1 : F) ∈ Submodule.span F (D.r '' D.G') := by
    rw [D.span]
    exact single_mem j' j hj.symm
  have hgen : ∀ A ∈ Submodule.span F (D.r '' D.G'), ∀ B ∈ Submodule.span F (D.r '' D.G'),
      (A * (c.sum fun g x => x • (z g * D.r g)) * B) i j = 0 := by
    intro A hA' B hB'
    induction hA' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      induction hB' using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨v, hv, rfl⟩ := hy
        exact move_one D z i j hz hk c hc h0 hu hv
      | zero => simp
      | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_apply, hx, hy, add_zero]
      | smul a x _ hx => rw [Matrix.mul_smul, Matrix.smul_apply, hx, smul_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.add_mul, Matrix.add_mul, Matrix.add_apply, hx, hy, add_zero]
    | smul a x _ hx => rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_apply, hx, smul_zero]
  have := hgen _ hA _ hB
  simpa [Matrix.mul_apply, Matrix.single_apply] using this

end UpperTheory.V.Pa.Det
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.DTwAlt
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.eigen :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (κ la : G → Matrix (Fin n) (Fin n) F) (Y : Matrix (Fin n) (Fin n) F), TwCoc (fun _ => 1) D.r Set.univ κ → TwCoc D.χF D.r Set.univ la → (∀ g ∈ D.G', κ g + la g = dTw (fun _ => 1) D.r Y g) → (∃ Y₁, ∀ g ∈ D.G', κ g = dTw (fun _ => 1) D.r Y₁ g) ∧ ∃ Y₂, ∀ g ∈ D.G', la g = dTw (fun _ => 1) D.r Y₂ g := by
  intro F G _ _ n D κ la Y hκ hla hY
  set c : F := D.χF D.g₀ with hc
  have hc1 : c - 1 ≠ 0 := by
    intro h
    apply D.χ_ne
    ext
    exact sub_eq_zero.mp h
  set Z : Matrix (Fin n) (Fin n) F := D.r D.g₀ * Y * D.r D.g₀⁻¹ with hZ
  set Y₁ : Matrix (Fin n) (Fin n) F := (c - 1)⁻¹ • (c • Z - c • κ D.g₀ - la D.g₀ - Y) with hY₁
  have key : ∀ g ∈ D.G', κ g = dTw (fun _ => 1) D.r Y₁ g := by
    intro g hg
    have hg' : D.g₀⁻¹ * g * D.g₀ ∈ D.G' := by
      have := D.G'.mul_mem (D.comm D.g₀⁻¹ g) hg
      simpa using this
    set g' := D.g₀⁻¹ * g * D.g₀ with hgg
    have e : g * D.g₀ = D.g₀ * g' := by rw [hgg]; group
    have e' : g'⁻¹ * D.g₀⁻¹ = D.g₀⁻¹ * g⁻¹ := by rw [hgg]; group
    have h1 := hκ g trivial D.g₀ trivial
    have h2 := hla g trivial D.g₀ trivial
    rw [e, hκ D.g₀ trivial g' trivial] at h1
    rw [e, hla D.g₀ trivial g' trivial] at h2
    have hχ : D.χF g = 1 := by simp [DetFr.χF, D.χ_triv g hg]
    rw [hχ, ← hc] at h2
    have h3 := hY g hg
    have h4 : D.r D.g₀ * κ g' * D.r D.g₀⁻¹ + D.r D.g₀ * la g' * D.r D.g₀⁻¹
        = D.r g * Z * D.r g⁻¹ - Z := by
      rw [← add_mul, ← mul_add, hY g' hg', dTw, one_smul, mul_sub, sub_mul, hZ]
      congr 1
      calc D.r D.g₀ * (D.r g' * Y * D.r g'⁻¹) * D.r D.g₀⁻¹
          = (D.r D.g₀ * D.r g') * Y * (D.r g'⁻¹ * D.r D.g₀⁻¹) := by simp only [mul_assoc]
        _ = (D.r g * D.r D.g₀) * Y * (D.r D.g₀⁻¹ * D.r g⁻¹) := by
          rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, e, e']
        _ = _ := by simp only [mul_assoc]
    have h5 : (c - 1) • κ g = (c - 1) • dTw (fun _ => 1) D.r Y₁ g := by
      simp only [dTw, one_smul] at h1 h2 h3 ⊢
      rw [hY₁, smul_sub, mul_smul_comm, smul_mul_assoc, smul_inv_smul₀ hc1, smul_inv_smul₀ hc1]
      simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
      linear_combination (norm := module) c • h4 - c • h1 - h2 - h3
    exact smul_right_injective _ hc1 h5
  refine ⟨⟨Y₁, key⟩, Y - Y₁, fun g hg => ?_⟩
  have h3 := hY g hg
  rw [key g hg] at h3
  simp only [dTw, one_smul, mul_sub, sub_mul] at h3 ⊢
  rw [← sub_eq_zero] at h3 ⊢
  rw [← h3]; abel
end

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem coc_comb {F G : Type} [Field F] [Group G] {n m : ℕ} (χ : G → F)
    (r : G → Matrix (Fin n) (Fin n) F) (z : Fin m → G → Matrix (Fin n) (Fin n) F) (α : Fin m → F)
    (hz : ∀ k, TwCoc χ r Set.univ (z k)) : TwCoc χ r Set.univ fun g => ∑ k, α k • z k g := by
  intro g _ h _
  show ∑ k, α k • z k (g * h) = ∑ k, α k • z k g + χ g • (r g * (∑ k, α k • z k h) * r g⁻¹)
  rw [Finset.sum_congr rfl fun k _ => by rw [hz k g (Set.mem_univ _) h (Set.mem_univ _)]]
  simp [smul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_comm]

private theorem cut_mul {F : Type} [Field F] {n : ℕ} (p q : Fin n → Prop) [∀ i j, Decidable (p i ∧ q j)]
    (Z B : Matrix (Fin n) (Fin n) F) (hB : ∀ k j, ¬ (q k ↔ q j) → B k j = 0) (i j : Fin n) :
    ((Matrix.of fun i j => if p i ∧ q j then Z i j else 0) * B) i j = if p i ∧ q j then (Z * B) i j else 0 := by
  simp only [Matrix.mul_apply, Matrix.of_apply]
  split_ifs with h
  · refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : q k ↔ q j
    · rw [if_pos ⟨h.1, hk.2 h.2⟩]
    · rw [hB k j hk, mul_zero, mul_zero]
  · refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : q k ↔ q j
    · rw [if_neg (fun h' => h ⟨h'.1, hk.1 h'.2⟩), zero_mul]
    · rw [hB k j hk, mul_zero]

private theorem kills_cut {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n)
    (p q : Fin n → Prop) [∀ i j, Decidable (p i ∧ q j)] (z : G → Matrix (Fin n) (Fin n) F)
    (hq : ∀ k j, ¬ (q k ↔ q j) → ¬ ((k : ℕ) < D.a ↔ (j : ℕ) < D.a))
    (hk : ∀ i j, p i → q j → D.KillsRel z i j) (i j : Fin n) :
    D.KillsRel (fun g => Matrix.of fun i j => if p i ∧ q j then z g i j else 0) i j := by
  intro c hc hs
  have hev : ∀ g k l, ¬ (q k ↔ q l) → D.r g k l = 0 := by
    intro g k l h
    exact (Submodule.mem_bot F).1 (((D.ev g) k l).2 (hq k l h))
  have e : ∀ g, ((Matrix.of fun i j => if p i ∧ q j then z g i j else 0) * D.r g) i j
      = if p i ∧ q j then (z g * D.r g) i j else 0 := fun g => cut_mul p q (z g) (D.r g) (hev g) i j
  simp only [Finsupp.sum, Matrix.sum_apply, Matrix.smul_apply, e]
  split_ifs with h
  · have := hk i j h.1 h.2 c hc hs
    simpa [Finsupp.sum, Matrix.sum_apply] using this
  · simp

private theorem block_princ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n)
    (K L : G → Matrix (Fin n) (Fin n) F) (hK : TwCoc (fun _ => 1) D.r Set.univ K)
    (hL : TwCoc D.χF D.r Set.univ L) (hKo : ∀ g, K g ∈ Od F F n D.a) (hLo : ∀ g, L g ∈ Od F F n D.a)
    (hk : ∀ i j, D.KillsRel (fun g => K g + L g) i j) :
    (∃ Y, ∀ g, K g = dTw (fun _ => 1) D.r Y g) ∧ ∃ Y, ∀ g, L g = dTw D.χF D.r Y g := by
  have hKL : TwCoc (fun _ => (1 : F)) D.r D.G' (fun g => K g + L g) := by
    intro g hg h _
    have e1 : K (g * h) = K g + D.r g * K h * D.r g⁻¹ := by simpa using hK g trivial h trivial
    have e2 : L (g * h) = L g + D.r g * L h * D.r g⁻¹ := by
      simpa [DetFr.χF, D.χ_triv g hg] using hL g trivial h trivial
    show K (g * h) + L (g * h) = K g + L g + (1 : F) • (D.r g * (K h + L h) * D.r g⁻¹)
    rw [e1, e2, one_smul, Matrix.mul_add, Matrix.add_mul]
    abel
  obtain ⟨Y, hY⟩ := Det.der D _ hKL hk
  obtain ⟨⟨Y1, hY1⟩, ⟨Y2, hY2⟩⟩ := Det.eigen D K L Y hK hL hY
  have hχ1 : ∀ g ∈ D.G', D.χF g = 1 := by intro g hg; simp [DetFr.χF, D.χ_triv g hg]
  have hY2' : ∀ g ∈ D.G', L g = dTw D.χF D.r Y2 g := by
    intro g hg
    rw [hY2 g hg]
    simp [dTw, hχ1 g hg]
  obtain ⟨Z1, -, hZ1⟩ := Det.infres D (fun _ => 1) K Y1 (by intros; simp) (by intros; rfl) hK hKo hY1
  obtain ⟨Z2, -, hZ2⟩ := Det.infres D D.χF L Y2 (by intro g h; simp [DetFr.χF]) hχ1 hL hLo hY2'
  exact ⟨⟨Z1, hZ1⟩, ⟨Z2, hZ2⟩⟩

theorem UpperTheory.V.Pa.Det.ann :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) {m : ℕ} (κ la : Fin m → G → Matrix (Fin n) (Fin n) F) (s : F) (ph : G → Matrix (Fin n) (Fin n) F), D.IsKap κ → D.IsTw κ s ph la → ∀ (α β : Fin m → F) (i j : Fin n), ¬ (((i : ℕ) < D.a) ↔ ((j : ℕ) < D.a)) → D.KillsRel (fun g => ∑ k, α k • κ k g + ∑ k, β k • la k g) i j → α = 0 ∧ ∃ Y ∈ Od F F n D.a, s • Yᵀ = Y ∧ ∀ g, ∑ k, β k • la k g = dTw D.χF D.r Y g := by
  classical
  intro F G _ _ n D m κ la s ph hκ hla α β i j hij hkill
  obtain ⟨K, hKe⟩ : ∃ K : G → Matrix (Fin n) (Fin n) F, K = fun g => ∑ k, α k • κ k g := ⟨_, rfl⟩
  obtain ⟨L, hLe⟩ : ∃ L : G → Matrix (Fin n) (Fin n) F, L = fun g => ∑ k, β k • la k g := ⟨_, rfl⟩
  rw [show (fun g => ∑ k, α k • κ k g + ∑ k, β k • la k g) = fun g => K g + L g by rw [hKe, hLe]] at hkill
  have hKc : TwCoc (fun _ => (1 : F)) D.r Set.univ K := by rw [hKe]; exact coc_comb _ _ κ α hκ.coc
  have hLc : TwCoc D.χF D.r Set.univ L := by rw [hLe]; exact coc_comb _ _ la β hla.coc
  have hKo : ∀ g, K g ∈ Od F F n D.a := fun g => by
    rw [hKe]; exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hκ.od k g)
  have hLo : ∀ g, L g ∈ Od F F n D.a := fun g => by
    rw [hLe]; exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hla.od k g)
  have hKp : ∀ g, K (D.σ g) = (-1 : F) • (K g)ᵀ := by
    intro g; rw [hKe]; simp [hκ.pol, Matrix.transpose_sum]
  have hLp : ∀ g, L (D.σ g) = s • (L g)ᵀ := by
    intro g; rw [hLe]; simp [hla.pol, Matrix.transpose_sum, Finset.smul_sum, smul_smul, mul_comm]
  have hTot : TwCoc (fun _ => (1 : F)) D.r D.G' (fun g => K g + L g) := by
    intro g hg h _
    have e1 : K (g * h) = K g + D.r g * K h * D.r g⁻¹ := by simpa using hKc g trivial h trivial
    have e2 : L (g * h) = L g + D.r g * L h * D.r g⁻¹ := by
      simpa [DetFr.χF, D.χ_triv g hg] using hLc g trivial h trivial
    show K (g * h) + L (g * h) = K g + L g + (1 : F) • (D.r g * (K h + L h) * D.r g⁻¹)
    rw [e1, e2, one_smul, Matrix.mul_add, Matrix.add_mul]
    abel
  obtain ⟨p, hpd⟩ : ∃ p : Fin n → Prop, ∀ x, p x ↔ ((x : ℕ) < D.a ↔ (i : ℕ) < D.a) := ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨q, hqd⟩ : ∃ q : Fin n → Prop, ∀ x, q x ↔ ((x : ℕ) < D.a ↔ (j : ℕ) < D.a) := ⟨_, fun _ => Iff.rfl⟩
  have hq : ∀ k l, ¬ (q k ↔ q l) → ¬ ((k : ℕ) < D.a ↔ (l : ℕ) < D.a) := by
    intro k l h h'
    apply h
    rw [hqd k, hqd l]
    tauto
  have hk' : ∀ i' j', p i' → q j' → D.KillsRel (fun g => K g + L g) i' j' := fun i' j' hi' hj' =>
    Det.relMove D _ i j hTot hkill i' j' ((hpd i').1 hi').symm ((hqd j').1 hj').symm
  have cK := Det.cornerCoc D _ _ _ hKc
  have cL := Det.cornerCoc D _ _ _ hLc
  have hcase : ((i : ℕ) < D.a ∧ ¬ (j : ℕ) < D.a) ∨ (¬ (i : ℕ) < D.a ∧ (j : ℕ) < D.a) := by tauto
  have key : ∃ Y1 Y2, ((∀ g, cV D.a (K g) = dTw (fun _ => (1 : F)) D.r Y1 g) ∨
      (∀ g, cV' D.a (K g) = dTw (fun _ => (1 : F)) D.r Y1 g)) ∧
      ((∀ g, cV D.a (L g) = dTw D.χF D.r Y2 g) ∨ (∀ g, cV' D.a (L g) = dTw D.χF D.r Y2 g)) := by
    rcases hcase with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · have hc2 : ∀ i' j', D.KillsRel (fun g => cV D.a (K g) + cV D.a (L g)) i' j' := by
        intro i' j'
        rw [show (fun g => cV D.a (K g) + cV D.a (L g)) =
            fun g => Matrix.of fun a b => if p a ∧ q b then (K g + L g) a b else 0 by
          funext g
          ext a b
          have hpa : p a ↔ (a : ℕ) < D.a := by rw [hpd]; tauto
          have hqb : q b ↔ ¬ (b : ℕ) < D.a := by rw [hqd]; tauto
          simp only [cV, Matrix.of_apply, Matrix.add_apply]
          split_ifs <;> first | rfl | (exfalso; tauto) | simp]
        exact kills_cut D p q (fun g => K g + L g) hq hk' i' j'
      obtain ⟨⟨Y1, hY1⟩, ⟨Y2, hY2⟩⟩ := block_princ D (fun g => cV D.a (K g)) (fun g => cV D.a (L g))
        cK.1 cL.1 (fun g => (cK.2.2.2 (K g)).1) (fun g => (cL.2.2.2 (L g)).1) hc2
      exact ⟨Y1, Y2, Or.inl hY1, Or.inl hY2⟩
    · have hc2 : ∀ i' j', D.KillsRel (fun g => cV' D.a (K g) + cV' D.a (L g)) i' j' := by
        intro i' j'
        rw [show (fun g => cV' D.a (K g) + cV' D.a (L g)) =
            fun g => Matrix.of fun a b => if p a ∧ q b then (K g + L g) a b else 0 by
          funext g
          ext a b
          have hpa : p a ↔ ¬ (a : ℕ) < D.a := by rw [hpd]; tauto
          have hqb : q b ↔ (b : ℕ) < D.a := by rw [hqd]; tauto
          simp only [cV', Matrix.of_apply, Matrix.add_apply]
          split_ifs <;> first | rfl | (exfalso; tauto) | simp]
        exact kills_cut D p q (fun g => K g + L g) hq hk' i' j'
      obtain ⟨⟨Y1, hY1⟩, ⟨Y2, hY2⟩⟩ := block_princ D (fun g => cV' D.a (K g)) (fun g => cV' D.a (L g))
        cK.2.1 cL.2.1 (fun g => (cK.2.2.2 (K g)).2.1) (fun g => (cL.2.2.2 (L g)).2.1) hc2
      exact ⟨Y1, Y2, Or.inr hY1, Or.inr hY2⟩
  obtain ⟨Y1, Y2, hK1, hL2⟩ := key
  obtain ⟨YK, hYKo, hYKs, hYK⟩ :=
    Det.shapiro D (fun _ => (1 : F)) (-1) K Y1 (fun _ => rfl) (by norm_num) hKc hKo hKp hK1
  obtain ⟨YL, hYLo, hYLs, hYL⟩ :=
    Det.shapiro D D.χF s L Y2 (fun g => by simp [DetFr.χF, D.χσ]) hla.sq hLc hLo hLp hL2
  have hT : YKᵀ = -YK := by
    have h := congrArg Matrix.transpose hYKs
    simp only [Matrix.transpose_smul, Matrix.transpose_transpose, neg_smul, one_smul] at h
    exact h.symm
  have hα : α = 0 := hκ.indep α YK hYKo hT fun g => by
    have := hYK g
    rw [hKe] at this
    exact this
  exact ⟨hα, YL, hYLo, hYLs, fun g => by
    have := hYL g
    rw [hLe] at this
    exact this⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.RelPair
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

namespace UpperTheory.V.Pa.Det

section Quad

variable {F : Type} [Field F] {n m : ℕ}

private abbrev Quad (F : Type) (n m : ℕ) :=
  Matrix (Fin n) (Fin n) F × (Fin m → Matrix (Fin n) (Fin n) F) × (Fin m → Matrix (Fin n) (Fin n) F) ×
    Matrix (Fin n) (Fin n) F

end Quad

end UpperTheory.V.Pa.Det

theorem UpperTheory.V.Pa.Det.relPair :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) {m : ℕ} (κ la : Fin m → G → Matrix (Fin n) (Fin n) F) (s : F) (ph : G → Matrix (Fin n) (Fin n) F), D.IsKap κ → D.IsTw κ s ph la → ∀ (c c' : G →₀ F), (∀ g ∈ c.support, g ∈ D.G') → (∀ g ∈ c'.support, g ∈ D.G') → c.sum (fun g x => x • D.r g) = 0 → c'.sum (fun g x => x • D.r g) = 0 → ∀ i j : Fin n, ¬ (((i : ℕ) < D.a) ↔ ((j : ℕ) < D.a)) → ∑ k, ((c.sum fun g x => x • (κ k g * D.r g)) i j * (c'.sum fun g x => x • (la k g * D.r g)) j i + (c.sum fun g x => x • (la k g * D.r g)) i j * (c'.sum fun g x => x • (κ k g * D.r g)) j i) = 0 := by
  intro F G _ _ n D m κ la s ph hK hT c c' hc hc' hRc hRc' i j _
  classical
  have hP : ∀ (g : G) (X : Matrix (Fin n) (Fin n) F), D.r g⁻¹ * (D.r g * X) = X := fun g X => by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  have hχ : ∀ g ∈ D.G', D.χF g = 1 := fun g hg => by simp [DetFr.χF, D.χ_triv g hg]
  have eK : ∀ k g h, κ k (g * h) = κ k g + D.r g * κ k h * D.r g⁻¹ := fun k g h => by
    have e := (hK.coc k) g (Set.mem_univ g) h (Set.mem_univ h)
    simpa using e
  have eL : ∀ g ∈ D.G', ∀ k h, la k (g * h) = la k g + D.r g * la k h * D.r g⁻¹ := fun g hg k h => by
    have e := (hT.coc k) g (Set.mem_univ g) h (Set.mem_univ h)
    rw [hχ g hg, one_smul] at e
    exact e
  have pK : ∀ k g h, κ k (g * h) * D.r (g * h) = κ k g * D.r g * D.r h + D.r g * (κ k h * D.r h) := by
    intro k g h
    rw [eK, map_mul]
    simp only [add_mul, mul_assoc, hP]
  have pL : ∀ g ∈ D.G', ∀ k h, la k (g * h) * D.r (g * h) = la k g * D.r g * D.r h + D.r g * (la k h * D.r h) := by
    intro g hg k h
    rw [eL g hg, map_mul]
    simp only [add_mul, mul_assoc, hP]
  have pQ : ∀ g ∈ D.G', ∀ h, ph (g * h) * D.r (g * h) + ∑ k, la k (g * h) * κ k (g * h) * D.r (g * h) =
      (ph g * D.r g + ∑ k, la k g * κ k g * D.r g) * D.r h + D.r g * (ph h * D.r h + ∑ k, la k h * κ k h * D.r h) +
      ∑ k, (κ k g * D.r g * (la k h * D.r h) + la k g * D.r g * (κ k h * D.r h)) := by
    intro g hg h
    have e := hT.ph_mul g h
    rw [hχ g hg, one_smul] at e
    rw [e, map_mul]
    simp only [eK, eL g hg]
    simp only [add_mul, mul_add, sub_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_mul,
      Finset.mul_sum, mul_assoc, hP]
    abel
  let pr : (G →₀ F) → (G →₀ F) → (G →₀ F) := fun c d =>
    c.sum fun g a => d.sum fun h b => Finsupp.single (g * h) (a * b)
  have gen : ∀ (v : G → Matrix (Fin n) (Fin n) F) (c d : G →₀ F), Finsupp.linearCombination F v (pr c d) =
      c.sum fun g a => d.sum fun h b => (a * b) • v (g * h) := by
    intro v c d
    simp only [pr, map_finsuppSum, Finsupp.linearCombination_single]
  have lcMul : ∀ (v w : G → Matrix (Fin n) (Fin n) F) (c d : G →₀ F),
      Finsupp.linearCombination F v c * Finsupp.linearCombination F w d =
      c.sum fun g a => d.sum fun h b => (a * b) • (v g * w h) := by
    intro v w c d
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum_mul]
    refine Finsupp.sum_congr fun g _ => ?_
    rw [Finsupp.mul_sum]
    refine Finsupp.sum_congr fun h _ => ?_
    rw [smul_mul_smul_comm]
  have dK : ∀ (W : Fin m → G → G → Matrix (Fin n) (Fin n) F) (c d : G →₀ F),
      (∑ k, c.sum fun g a => d.sum fun h b => (a * b) • W k g h) =
      c.sum fun g a => d.sum fun h b => (a * b) • ∑ k, W k g h := by
    intro W c d
    simp only [Finsupp.sum, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.sum_comm]
  have memS : ∀ (p : G →₀ F), p ∈ Finsupp.supported F F (D.G' : Set G) → ∀ g ∈ p.support, g ∈ D.G' :=
    fun p hp g hg => (Finsupp.mem_supported F p).1 hp (Finset.mem_coe.2 hg)
  have prS : ∀ c ∈ Finsupp.supported F F (D.G' : Set G), ∀ d ∈ Finsupp.supported F F (D.G' : Set G),
      pr c d ∈ Finsupp.supported F F (D.G' : Set G) := by
    intro c hc d hd
    refine Submodule.finsuppSum_mem F _ c _ fun g hg => Submodule.finsuppSum_mem F _ d _ fun h hh => ?_
    exact Finsupp.single_mem_supported F _ (D.G'.mul_mem (memS c hc g (Finsupp.mem_support_iff.2 hg))
      (memS d hd h (Finsupp.mem_support_iff.2 hh)))
  have mR : ∀ c d, Finsupp.linearCombination F D.r (pr c d) =
      Finsupp.linearCombination F D.r c * Finsupp.linearCombination F D.r d := by
    intro c d
    rw [gen, lcMul]
    simp only [map_mul]
  have mK : ∀ k, ∀ c d, Finsupp.linearCombination F (fun g => κ k g * D.r g) (pr c d) =
      Finsupp.linearCombination F (fun g => κ k g * D.r g) c * Finsupp.linearCombination F D.r d +
      Finsupp.linearCombination F D.r c * Finsupp.linearCombination F (fun g => κ k g * D.r g) d := by
    intro k c d
    rw [gen, lcMul, lcMul, ← Finsupp.sum_add]
    refine Finsupp.sum_congr fun g _ => ?_
    rw [← Finsupp.sum_add]
    refine Finsupp.sum_congr fun h _ => ?_
    rw [pK, smul_add]
  have mL : ∀ c ∈ Finsupp.supported F F (D.G' : Set G), ∀ k d,
      Finsupp.linearCombination F (fun g => la k g * D.r g) (pr c d) =
      Finsupp.linearCombination F (fun g => la k g * D.r g) c * Finsupp.linearCombination F D.r d +
      Finsupp.linearCombination F D.r c * Finsupp.linearCombination F (fun g => la k g * D.r g) d := by
    intro c hc k d
    rw [gen, lcMul, lcMul, ← Finsupp.sum_add]
    refine Finsupp.sum_congr fun g hg => ?_
    rw [← Finsupp.sum_add]
    refine Finsupp.sum_congr fun h _ => ?_
    rw [pL g (memS c hc g hg), smul_add]
  have mQ : ∀ c ∈ Finsupp.supported F F (D.G' : Set G), ∀ d,
      Finsupp.linearCombination F (fun g => ph g * D.r g + ∑ k, la k g * κ k g * D.r g) (pr c d) =
      Finsupp.linearCombination F (fun g => ph g * D.r g + ∑ k, la k g * κ k g * D.r g) c *
        Finsupp.linearCombination F D.r d +
      Finsupp.linearCombination F D.r c *
        Finsupp.linearCombination F (fun g => ph g * D.r g + ∑ k, la k g * κ k g * D.r g) d +
      ∑ k, (Finsupp.linearCombination F (fun g => κ k g * D.r g) c *
          Finsupp.linearCombination F (fun g => la k g * D.r g) d +
        Finsupp.linearCombination F (fun g => la k g * D.r g) c *
          Finsupp.linearCombination F (fun g => κ k g * D.r g) d) := by
    intro c hc d
    have hs : (∑ k, (Finsupp.linearCombination F (fun g => κ k g * D.r g) c *
          Finsupp.linearCombination F (fun g => la k g * D.r g) d +
        Finsupp.linearCombination F (fun g => la k g * D.r g) c *
          Finsupp.linearCombination F (fun g => κ k g * D.r g) d)) =
        c.sum fun g a => d.sum fun h b => (a * b) •
          ∑ k, (κ k g * D.r g * (la k h * D.r h) + la k g * D.r g * (κ k h * D.r h)) := by
      refine Eq.trans ?_ (dK _ c d)
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [lcMul, lcMul, ← Finsupp.sum_add]
      refine Finsupp.sum_congr fun g _ => ?_
      rw [← Finsupp.sum_add]
      refine Finsupp.sum_congr fun h _ => ?_
      rw [smul_add]
    rw [gen, hs, lcMul, lcMul, ← Finsupp.sum_add, ← Finsupp.sum_add]
    refine Finsupp.sum_congr fun g hg => ?_
    rw [← Finsupp.sum_add, ← Finsupp.sum_add]
    refine Finsupp.sum_congr fun h _ => ?_
    rw [← smul_add, ← smul_add, pQ g (memS c hc g hg) h]
  have trQ : ∀ p ∈ Finsupp.supported F F (D.G' : Set G),
      (Finsupp.linearCombination F (fun g => ph g * D.r g + ∑ k, la k g * κ k g * D.r g) p).trace = 0 := by
    intro p hp
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Matrix.trace_sum]
    refine Finset.sum_eq_zero fun g hg => ?_
    rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_sum, hT.ell g (memS p hp g hg), smul_zero]
  have hEv : ∀ t : Fin n, Matrix.single t t (1 : F) ∈ Submodule.span F (D.r '' (D.G' : Set G)) := by
    intro t
    rw [D.span]
    intro i' j'
    refine ⟨fun _ => trivial, fun h => ?_⟩
    rw [Submodule.mem_bot, Matrix.single_apply]
    split_ifs with e
    · obtain ⟨rfl, rfl⟩ := e
      exact absurd Iff.rfl h
    · rfl
  have hS : c ∈ Finsupp.supported F F (D.G' : Set G) :=
    (Finsupp.mem_supported F c).2 fun g hg => hc g (Finset.mem_coe.1 hg)
  have hS' : c' ∈ Finsupp.supported F F (D.G' : Set G) :=
    (Finsupp.mem_supported F c').2 fun g hg => hc' g (Finset.mem_coe.1 hg)
  obtain ⟨dj, hdj, hj⟩ := (Finsupp.mem_span_image_iff_linearCombination F).1 (hEv j)
  obtain ⟨di, hdi, hi⟩ := (Finsupp.mem_span_image_iff_linearCombination F).1 (hEv i)
  have hR0 : Finsupp.linearCombination F D.r c = 0 := by
    rw [Finsupp.linearCombination_apply]; exact hRc
  have hR0' : Finsupp.linearCombination F D.r c' = 0 := by
    rw [Finsupp.linearCombination_apply]; exact hRc'
  have tr : ∀ A B : Matrix (Fin n) (Fin n) F,
      (A * Matrix.single j j 1 * (B * Matrix.single i i 1)).trace = A i j * B j i := by
    intro A B
    rw [← mul_assoc, Matrix.trace_mul_single]
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul]
  have key := trQ _ (prS _ (prS c hS dj hdj) _ (prS c' hS' di hdi))
  rw [mQ _ (prS c hS dj hdj)] at key
  simp only [mR, mK, mL c hS, mL c' hS', hR0, hR0', hi, hj, zero_mul, mul_zero, add_zero, zero_add] at key
  rw [Matrix.trace_sum] at key
  simp only [Matrix.trace_add, tr] at key
  simpa only [Finsupp.linearCombination_apply] using key
end

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem comb_entry {F G : Type} [Field F] {n m : ℕ} (r : G → Matrix (Fin n) (Fin n) F)
    (κ la : Fin m → G → Matrix (Fin n) (Fin n) F) (α β : Fin m → F) (c : G →₀ F) (i j : Fin n) :
    (c.sum fun g x => x • ((∑ k, α k • κ k g + ∑ k, β k • la k g) * r g)) i j =
      ∑ k, ((c.sum fun g x => x • (κ k g * r g)) i j * α k + (c.sum fun g x => x • (la k g * r g)) i j * β k) := by
  simp only [Finsupp.sum, Matrix.sum_apply, Matrix.smul_apply, Matrix.add_mul, Matrix.sum_mul,
    Matrix.smul_mul, Matrix.add_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_add_distrib, mul_add]
  rw [Finset.sum_comm (s := c.support) (f := fun x k => c x * (α k * (κ k x * r x) i j)),
    Finset.sum_comm (s := c.support) (f := fun x k => c x * (β k * (la k x * r x) i j))]
  congr 1 <;> refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem UpperTheory.V.Pa.Det.oddPart :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) {m : ℕ} (κ la : Fin m → G → Matrix (Fin n) (Fin n) F) (s : F) (ph : G → Matrix (Fin n) (Fin n) F), D.IsKap κ → D.IsTw κ s ph la → ∀ k, ∃ Y ∈ Od F F n D.a, s • Yᵀ = Y ∧ ∀ g, la k g = dTw D.χF D.r Y g := by
  intro F G _ _ n D m κ la s ph hK hT k
  classical
  by_cases ha : D.a < n
  · have hpos := D.a_pos
    let i : Fin n := ⟨0, by omega⟩
    let j : Fin n := ⟨D.a, ha⟩
    have hij : ¬((i : ℕ) < D.a ↔ (j : ℕ) < D.a) := by
      intro h
      exact lt_irrefl D.a (h.mp (show (0 : ℕ) < D.a by omega))
    have hji : ¬((j : ℕ) < D.a ↔ (i : ℕ) < D.a) := fun h => hij h.symm
    have step1 : ∀ c' : G →₀ F, (∀ g ∈ c'.support, g ∈ D.G') → (c'.sum fun g x => x • D.r g) = 0 →
        ∀ k', (c'.sum fun g x => x • (la k' g * D.r g)) j i = 0 := by
      intro c' hc' hr'
      have hkill : D.KillsRel (fun g => ∑ q, (fun q => (c'.sum fun g x => x • (la q g * D.r g)) j i) q • κ q g
          + ∑ q, (fun q => (c'.sum fun g x => x • (κ q g * D.r g)) j i) q • la q g) i j := by
        intro c hc hr
        show (c.sum fun g x => x • ((∑ q, (fun q => (c'.sum fun g x => x • (la q g * D.r g)) j i) q • κ q g
          + ∑ q, (fun q => (c'.sum fun g x => x • (κ q g * D.r g)) j i) q • la q g) * D.r g)) i j = 0
        rw [comb_entry]
        exact Det.relPair D κ la s ph hK hT c c' hc hc' hr hr' i j hij
      have h := (Det.ann D κ la s ph hK hT _ _ i j hij hkill).1
      intro k'
      exact congrFun h k'
    have hkill2 : D.KillsRel (fun g => ∑ q, (0 : Fin m → F) q • κ q g
        + ∑ q, (Pi.single k (1 : F) : Fin m → F) q • la q g) j i := by
      intro c hc hr
      show (c.sum fun g x => x • ((∑ q, (0 : Fin m → F) q • κ q g
        + ∑ q, (Pi.single k (1 : F) : Fin m → F) q • la q g) * D.r g)) j i = 0
      rw [comb_entry]
      simp [step1 c hc hr]
    obtain ⟨_, Y, hY, hs, hg⟩ := Det.ann D κ la s ph hK hT 0 (Pi.single k 1) j i hji hkill2
    refine ⟨Y, hY, hs, fun g => ?_⟩
    rw [← hg g]
    simp [Pi.single_apply]
  · have han : D.a = n := le_antisymm D.a_le (not_lt.mp ha)
    refine ⟨0, Submodule.zero_mem _, by simp, fun g => ?_⟩
    have h0 : la k g = 0 := by
      ext i j
      have hm := (hT.od k g i j).1 (by rw [han]; exact iff_of_true i.2 j.2)
      exact (Submodule.mem_bot F).mp hm
    rw [h0]
    simp [dTw]
