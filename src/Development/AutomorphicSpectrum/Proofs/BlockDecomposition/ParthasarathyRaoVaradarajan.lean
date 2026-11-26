module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalEmbeddingRangeEqField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCliffordLowestVector
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpinTensorHighestWeight
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHighestWeightModule
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHighestWeightModule
noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount.Extremal

variable {n : ℕ}

def permM (w : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => if i = w j then 1 else 0

theorem permM_conjTranspose (w : Equiv.Perm (Fin n)) : (permM w)ᴴ = permM w⁻¹ := by
  ext i j
  simp only [permM, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases h : j = w i
  · have h2 : i = w⁻¹ j := by subst h; simp
    rw [if_pos h, if_pos h2]; simp
  · have h2 : ¬ i = w⁻¹ j := fun e => h (by rw [e]; simp)
    rw [if_neg h, if_neg h2]; simp

theorem permM_mul_single (w : Equiv.Perm (Fin n)) (c d : Fin n) :
    permM w * Matrix.single c d (1 : ℂ) = Matrix.single (w c) d 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.single_apply, permM, Matrix.of_apply]
  rw [Finset.sum_eq_single c]
  · by_cases h1 : i = w c <;> by_cases h2 : d = j
    · simp [h1, h2]
    · simp [h1, h2]
    · simp [h2, h1, Ne.symm h1]
    · simp [h1, h2, Ne.symm h1]
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem single_mul_permM (v : Equiv.Perm (Fin n)) (c d : Fin n) :
    Matrix.single c d (1 : ℂ) * permM v = Matrix.single c (v⁻¹ d) 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.single_apply, permM, Matrix.of_apply]
  rw [Finset.sum_eq_single d]
  · by_cases h1 : c = i
    · by_cases h2 : d = v j
      · subst h1 h2; simp
      · subst h1
        have h3 : ¬ v.symm d = j := fun e => h2 (by rw [← e]; simp)
        simp [h2, h3]
    · simp [h1]
  · intro b _ hb
    rw [if_neg (fun q => hb q.2.symm)]; simp
  · simp

theorem permM_single (w : Equiv.Perm (Fin n)) (c d : Fin n) :
    permM w * Matrix.single c d (1 : ℂ) * (permM w)ᴴ = Matrix.single (w c) (w d) 1 := by
  rw [permM_conjTranspose, permM_mul_single, single_mul_permM, inv_inv]

theorem permM_mul (w v : Equiv.Perm (Fin n)) : permM w * permM v = permM (w * v) := by
  ext i j
  simp only [Matrix.mul_apply, permM, Matrix.of_apply]
  rw [Finset.sum_eq_single (v j)]
  · have e : (w * v) j = w (v j) := rfl
    by_cases h : i = w (v j)
    · rw [if_pos h, if_pos rfl, if_pos (h.trans e.symm)]; simp
    · rw [if_neg h, zero_mul, if_neg (fun q => h (q.trans e))]
  · intro b _ hb
    rw [if_neg hb]; simp
  · simp

theorem permM_one : permM (1 : Equiv.Perm (Fin n)) = 1 := by
  ext i j
  simp only [permM, Matrix.of_apply, Matrix.one_apply]
  have e : (1 : Equiv.Perm (Fin n)) j = j := rfl
  by_cases h : i = j
  · rw [if_pos (h.trans e.symm), if_pos h]
  · rw [if_neg (fun q => h (q.trans e)), if_neg h]

theorem Jm_true : ReciprocityTheory.ChartRestriction.DS.Jm (fun _ : Fin n => true) = 1 := by
  simp [ReciprocityTheory.ChartRestriction.DS.Jm]

def permU (w : Equiv.Perm (Fin n)) : (Matrix (Fin n) (Fin n) ℂ)ˣ where
  val := permM w
  inv := permM w⁻¹
  val_inv := by rw [permM_mul, mul_inv_cancel, permM_one]
  inv_val := by rw [permM_mul, inv_mul_cancel, permM_one]

theorem permM_unitary (w : Equiv.Perm (Fin n)) : permM w ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, permM_conjTranspose, permM_mul,
    mul_inv_cancel, permM_one]

def permK (w : Equiv.Perm (Fin n)) : ReciprocityTheory.ChartRestriction.DS.S7.KG (fun _ : Fin n => true) :=
  ⟨⟨permU w, by
      show (permM w)ᴴ * ReciprocityTheory.ChartRestriction.DS.Jm (fun _ : Fin n => true) * permM w = _
      rw [Jm_true, Matrix.mul_one, permM_conjTranspose, permM_mul, inv_mul_cancel, permM_one]⟩,
    by
      show permM w ∈ ReciprocityTheory.ChartRestriction.DS.Kset (fun _ : Fin n => true)
      refine ⟨permM_unitary w, ?_⟩
      rw [Jm_true, Matrix.mul_one, Matrix.one_mul]⟩

theorem toMK_permK (w : Equiv.Perm (Fin n)) : ReciprocityTheory.ChartRestriction.DS.S7.toMK (permK w) = permM w := rfl

theorem conj_single {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : ReciprocityTheory.ChartRestriction.DS.S7.KType ε Λ)
    (k : ReciprocityTheory.ChartRestriction.DS.S7.KG ε) {c d : Fin n} (h : ε c = ε d) :
    T.op k * T.dτ (Matrix.single c d 1) * star (T.op k) =
      T.dτ (ReciprocityTheory.ChartRestriction.DS.S7.toMK k * Matrix.single c d 1 * star (ReciprocityTheory.ChartRestriction.DS.S7.toMK k)) := by
  have h1 := ReciprocityTheory.ChartRestriction.DS.HW.KType.conj_dτ T k (ReciprocityTheory.ChartRestriction.DS.HW.inK_hermitian_unit h)
  have h2 := ReciprocityTheory.ChartRestriction.DS.HW.KType.conj_dτ T k (ReciprocityTheory.ChartRestriction.DS.HW.inK_skew_hermitian_unit h)
  rw [ReciprocityTheory.ChartRestriction.DS.HW.single_eq_kp c d, map_add (f := _), map_smul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    h1, h2, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, map_add, map_smul]

theorem unit_translate {Λ : Fin n → ℝ} (T : ReciprocityTheory.ChartRestriction.DS.S7.KType (fun _ : Fin n => true) Λ)
    (w : Equiv.Perm (Fin n)) (c d : Fin n) (v : T.V) :
    T.dτ (Matrix.single (w c) (w d) 1) (T.op (permK w) v) = T.op (permK w) (T.dτ (Matrix.single c d 1) v) := by
  have h := conj_single T (permK w) (c := c) (d := d) rfl
  rw [toMK_permK, Matrix.star_eq_conjTranspose, permM_single] at h
  rw [← h]
  have hu : star (T.op (permK w)) * T.op (permK w) = 1 := Unitary.coe_star_mul_self _
  have e : T.op (permK w) * T.dτ (Matrix.single c d 1) * star (T.op (permK w)) * T.op (permK w) =
      T.op (permK w) * T.dτ (Matrix.single c d 1) := by
    rw [mul_assoc _ (star _), hu, mul_one]
  exact congrArg (fun F : T.V →L[ℂ] T.V => F v) e

theorem extremal_module : ∀ {n : ℕ} (κ : Fin n → ℝ), Antitone κ → ∀ s : ℝ, (∀ a, ∃ m : ℤ, κ a - s = m) →
    ∀ w : Equiv.Perm (Fin n),
    ∃ (Z : Type) (_ : NormedAddCommGroup Z) (_ : InnerProductSpace ℂ Z) (_ : FiniteDimensional ℂ Z)
      (E : Fin n → Fin n → Module.End ℂ Z) (u a : Z),
      Formalism.REAL.GlRel E ∧ (∀ x y (f g : Z), ⟪E x y f, g⟫_ℂ = ⟪f, E y x g⟫_ℂ) ∧ u ≠ 0 ∧
      Formalism.REAL.KHighest (fun _ => true) E κ u ∧
      (∀ W : Submodule ℂ Z, (∀ x y, ∀ f ∈ W, E x y f ∈ W) → u ∈ W → W = ⊤) ∧ a ≠ 0 ∧
      (∀ x, E (w x) (w x) a = ((κ x : ℝ) : ℂ) • a) ∧ ∀ x y, x < y → E (w x) (w y) a = 0 := by
  intro n κ hκ s hs w
  obtain ⟨T⟩ := ReciprocityTheory.ChartRestriction.DS.HW.kType_exists_of_dom (fun _ : Fin n => true) (fun a => κ a - s) hs
    (fun a b hab _ => sub_le_sub_right (hκ hab.le) s)
  set F := ReciprocityTheory.ChartRestriction.DS.HW.kunits T with hF
  set E := ReciprocityTheory.ChartRestriction.DS.HW.endomorphismFamilyShift F (fun _ => s) with hE
  have hEval : ∀ x y (f : T.V), E x y f = T.dτ (Matrix.single x y 1) f + (if x = y then ((s : ℝ) : ℂ) else 0) • f := by
    intro x y f
    simp only [hE, hF, ReciprocityTheory.ChartRestriction.DS.HW.endomorphismFamilyShift, ReciprocityTheory.ChartRestriction.DS.HW.kunits, LinearMap.add_apply,
      LinearMap.smul_apply, Module.End.one_apply, ContinuousLinearMap.coe_coe]
  have hrel : Formalism.REAL.KRel (fun _ : Fin n => true) E :=
    ReciprocityTheory.ChartRestriction.DS.HW.ext1Shift_kRel (ReciprocityTheory.ChartRestriction.DS.HW.KType.kRel T) (fun _ _ _ => rfl)
  have huni : Formalism.REAL.KUnit (fun _ : Fin n => true) E :=
    ReciprocityTheory.ChartRestriction.DS.HW.ext1Shift_kUnit (ReciprocityTheory.ChartRestriction.DS.HW.KType.kUnit T) _
  have hhigh : Formalism.REAL.KHighest (fun _ => true) E κ T.w := by
    have h := ReciprocityTheory.ChartRestriction.DS.HW.ext1Shift_kHighest (t := fun _ => s) (ReciprocityTheory.ChartRestriction.DS.HW.KType.kHighest_w T)
    have e : (fun a => κ a - s) + (fun _ => s) = κ := by
      funext a
      simp
    rwa [e] at h
  have hw0 := ReciprocityTheory.ChartRestriction.DS.HW.KType.w_ne_zero T
  set k := permK w with hk
  refine ⟨T.V, inferInstance, inferInstance, inferInstance, E, T.w, T.op k T.w, fun a b c d => hrel a b c d rfl rfl,
    fun x y => huni x y rfl, hw0, hhigh, ?_, ?_, ?_, ?_⟩
  · intro W hW hu
    have hW' : ∀ a b, (fun _ : Fin n => true) a = (fun _ : Fin n => true) b → ∀ v ∈ W,
        T.dτ (Matrix.single a b 1) v ∈ W := by
      intro a b _ v hv
      have h1 := hW a b v hv
      rw [hEval] at h1
      exact (W.add_mem_iff_left (W.smul_mem _ hv)).1 h1
    rcases ReciprocityTheory.ChartRestriction.DS.HW.KType.dτ_irred T W hW' with h | h
    · rw [h, Submodule.mem_bot] at hu
      exact absurd hu hw0
    · exact h
  · intro h0
    have hu : star (T.op k) * T.op k = 1 := Unitary.coe_star_mul_self _
    have := congrArg (fun G : T.V →L[ℂ] T.V => G T.w) hu
    simp only [ContinuousLinearMap.mul_apply, h0, map_zero] at this
    exact hw0 this.symm
  · intro x
    rw [hEval, unit_translate, T.w_wt x, if_pos rfl, map_smul, ← add_smul]
    congr 1
    push_cast
    ring
  · intro x y hxy
    have hne : w x ≠ w y := fun e => (ne_of_lt hxy) (w.injective e)
    rw [hEval, unit_translate, T.w_hw x y hxy rfl, if_neg hne]
    simp

end GlobalTheory.CompanionTheory.RealCount.Extremal
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHighestWeightModuleStatement
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_highest_weight_module : ∀ {n : ℕ} (κ : Fin n → ℝ), Antitone κ → ∀ s : ℝ, (∀ a, ∃ m : ℤ, κ a - s = m) →
    ∀ w : Equiv.Perm (Fin n),
    ∃ (Z : Type) (_ : NormedAddCommGroup Z) (_ : InnerProductSpace ℂ Z) (_ : FiniteDimensional ℂ Z)
      (E : Fin n → Fin n → Module.End ℂ Z) (u a : Z),
      Formalism.REAL.GlRel E ∧ (∀ x y (f g : Z), ⟪E x y f, g⟫_ℂ = ⟪f, E y x g⟫_ℂ) ∧ u ≠ 0 ∧
      Formalism.REAL.KHighest (fun _ => true) E κ u ∧
      (∀ W : Submodule ℂ Z, (∀ x y, ∀ f ∈ W, E x y f ∈ W) → u ∈ W → W = ⊤) ∧ a ≠ 0 ∧
      (∀ x, E (w x) (w x) a = ((κ x : ℝ) : ℂ) • a) ∧ ∀ x y, x < y → E (w x) (w y) a = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RealCount.Extremal.extremal_module | exact GlobalTheory.CompanionTheory.RealCount.Extremal.extremal_module | (intros; apply GlobalTheory.CompanionTheory.RealCount.Extremal.extremal_module <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CliffordVectorSpinWeight
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CliffordVectorSpinWeight
noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount

theorem spinM_vacuum_lowest : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ), IsCliff c →
    ∀ q : ι → ℂ, (∀ a b, a < b → c b a *ᵥ q = 0) →
    (∀ a, spinM c a a *ᵥ q = ((-(rhoV n a) : ℝ) : ℂ) • q) ∧ ∀ a b, a < b → spinM c b a *ᵥ q = 0 := by
  intro n ι _ _ c hc q hq
  obtain ⟨h1, _⟩ := hc
  have two : (2 : Matrix ι ι ℂ) *ᵥ q = (2 : ℂ) • q := by
    have : (2 : Matrix ι ι ℂ) = (2 : ℂ) • (1 : Matrix ι ι ℂ) := by
      rw [two_smul]; exact one_add_one_eq_two.symm
    rw [this, Matrix.smul_mulVec, Matrix.one_mulVec]
  have anti : ∀ a b d e, c a b *ᵥ (c d e *ᵥ q) =
      (if a = e ∧ b = d then (2 : ℂ) • q else 0) - c d e *ᵥ (c a b *ᵥ q) := by
    intro a b d e
    have h := congrArg (fun M => M *ᵥ q) (h1 a b d e)
    simp only [Matrix.add_mulVec, Matrix.mulVec_mulVec] at h
    simp only [Matrix.mulVec_mulVec]
    rw [eq_sub_iff_add_eq, h]
    split_ifs
    · exact two
    · simp
  have sumv : ∀ (a b : Fin n), (∑ e, c a e * c e b) *ᵥ q = ∑ e, c a e *ᵥ (c e b *ᵥ q) := by
    intro a b
    simp only [Matrix.mulVec_mulVec]
    exact map_sum (Matrix.mulVec.addMonoidHomLeft q) _ _
  have hT : ∀ a e : Fin n, c a e *ᵥ (c e a *ᵥ q) =
      (if e < a then (2 : ℂ) else if e = a then 1 else 0) • q := by
    intro a e
    rcases lt_trichotomy e a with h | h | h
    · rw [if_pos h, anti a e e a, hq e a h]
      simp
    · subst h
      have h2 := anti e e e e
      simp only [and_self, if_true] at h2
      have h3 : (2 : ℂ) • (c e e *ᵥ (c e e *ᵥ q)) = (2 : ℂ) • q := by
        rw [two_smul]
        nth_rewrite 1 [h2]
        rw [two_smul]
        abel
      have h4 := smul_right_injective (ι → ℂ) (two_ne_zero : (2 : ℂ) ≠ 0) h3
      simpa using h4
    · rw [if_neg (not_lt.mpr h.le), if_neg h.ne', hq a e h]
      simp
  have hs : ∀ a : Fin n, ∑ e : Fin n, (if e < a then (2 : ℂ) else if e = a then 1 else 0) =
      2 * ((a : ℕ) : ℂ) + 1 := by
    intro a
    have h0 : ∀ e : Fin n, (if e < a then (2 : ℂ) else if e = a then 1 else 0) =
        (if e < a then 2 else 0) + (if e = a then 1 else 0) := by
      intro e
      rcases lt_trichotomy e a with h | h | h
      · simp [h, h.ne]
      · simp [h]
      · simp [not_lt.mpr h.le, h.ne']
    simp only [h0]
    rw [sum_add_distrib, ← Finset.sum_filter]
    have h5 : univ.filter (fun e : Fin n => e < a) = Finset.Iio a := by ext; simp
    rw [h5]
    simp [Fin.card_Iio, mul_comm]
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · unfold spinM
    rw [if_pos rfl, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sumv]
    simp only [hT]
    rw [← Finset.sum_smul, hs, smul_smul, ← sub_smul]
    congr 1
    simp only [rhoV]
    push_cast
    ring
  · unfold spinM
    rw [if_neg hab.ne', sub_zero, Matrix.smul_mulVec, sumv]
    have : ∀ e : Fin n, c b e *ᵥ (c e a *ᵥ q) = 0 := by
      intro e
      rcases lt_trichotomy e a with h | h | h
      · rw [anti b e e a, if_neg (fun hh => hab.ne' hh.1), hq e b (h.trans hab)]
        simp
      · subst h
        rw [anti b e e e, if_neg (fun hh => hab.ne' hh.1), hq e b hab]
        simp
      · rw [hq a e h]
        simp
    simp [this]

end GlobalTheory.CompanionTheory.RealCount
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CliffordVectorSpinWeightStatement
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.clifford_vector_spin_weight : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ), IsCliff c →
    ∀ q : ι → ℂ, (∀ a b, a < b → c b a *ᵥ q = 0) →
    (∀ a, spinM c a a *ᵥ q = ((-(rhoV n a) : ℝ) : ℂ) • q) ∧ ∀ a b, a < b → spinM c b a *ᵥ q = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RealCount.spinM_vacuum_lowest | exact GlobalTheory.CompanionTheory.RealCount.spinM_vacuum_lowest | (intros; apply GlobalTheory.CompanionTheory.RealCount.spinM_vacuum_lowest <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Sl2SquareKillsVector
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Sl2SquareKillsVector
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount

theorem sl2_square_kills : ∀ {n : ℕ} {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (E : Fin n → Fin n → Module.End ℂ Z), Formalism.REAL.GlRel E →
    (∀ x y (f g : Z), ⟪E x y f, g⟫_ℂ = ⟪f, E y x g⟫_ℂ) → ∀ {i j : Fin n}, i ≠ j → ∀ {a : Z}, a ≠ 0 →
    ∀ {p r : ℝ}, E i i a = (p : ℂ) • a → E j j a = (r : ℂ) • a → (∃ m : ℤ, p - r = m) → -1 ≤ p - r →
    (E i j a = 0 ∨ E j i a = 0) → ((E i j) ^ 2) a = 0 := by
  intro n Z _ _ E hG hA i j hij a ha p r hp hr hm hd hor
  have hji : j ≠ i := hij.symm
  have c1 : ∀ v, E i j (E j i v) - E j i (E i j v) = E i i v - E j j v := by
    intro v
    have h := LinearMap.congr_fun (hG i j j i) v
    simpa [Module.End.mul_apply] using h
  have c2 : ∀ v, E i i (E i j v) - E i j (E i i v) = E i j v := by
    intro v
    have h := LinearMap.congr_fun (hG i i i j) v
    simpa [Module.End.mul_apply, hji] using h
  have c3 : ∀ v, E j j (E i j v) - E i j (E j j v) = - E i j v := by
    intro v
    have h := LinearMap.congr_fun (hG j j i j) v
    simpa [Module.End.mul_apply, hji] using h
  have hsq : ((E i j) ^ 2) a = E i j (E i j a) := by
    simp [pow_two, Module.End.mul_apply]
  rw [hsq]
  rcases hor with h | h
  · simp [h]
  have hYX : E j i (E i j a) = ((r : ℂ) - p) • a := by
    have h1 := c1 a
    rw [h, map_zero, hp, hr, zero_sub] at h1
    rw [sub_smul, ← neg_sub ((p : ℂ) • a), ← h1, neg_neg]
  have hn : ‖E i j a‖ ^ 2 = (r - p) * ‖a‖ ^ 2 := by
    have h1 : ⟪E i j a, E i j a⟫_ℂ = ((r : ℂ) - p) * ⟪a, a⟫_ℂ := by
      rw [hA, hYX, inner_smul_right]
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
    have h2 : (((‖E i j a‖ ^ 2 : ℝ)) : ℂ) = (((r - p) * ‖a‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      simpa using h1
    exact_mod_cast h2
  have hapos : 0 < ‖a‖ ^ 2 := by positivity
  have hle : 0 ≤ r - p := by
    by_contra hc
    have : (r - p) * ‖a‖ ^ 2 < 0 := mul_neg_of_neg_of_pos (not_le.mp hc) hapos
    nlinarith [sq_nonneg ‖E i j a‖]
  obtain ⟨m, hm⟩ := hm
  have hm1 : (-1 : ℤ) ≤ m := by
    have : ((-1 : ℤ) : ℝ) ≤ (m : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hm2 : m ≤ 0 := by
    have : (m : ℝ) ≤ ((0 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hcases : m = 0 ∨ m = -1 := by omega
  rcases hcases with h0 | h0
  · have hpr : r - p = 0 := by rw [h0] at hm; push_cast at hm; linarith
    rw [hpr, zero_mul] at hn
    have h3 : E i j a = 0 := by
      have : ‖E i j a‖ = 0 := by simpa using hn
      exact norm_eq_zero.mp this
    simp [h3]
  · have hpr : r - p = 1 := by rw [h0] at hm; push_cast at hm; linarith
    have hprC : (r : ℂ) - p = 1 := by exact_mod_cast hpr
    have hYX' : E j i (E i j a) = a := by rw [hYX, hprC, one_smul]
    have e1 : E i i (E i j a) = ((p : ℂ) + 1) • E i j a := by
      have h1 := c2 a
      rw [hp, map_smul] at h1
      rw [add_smul, one_smul, add_comm]
      exact sub_eq_iff_eq_add.mp h1
    have e2 : E j j (E i j a) = ((r : ℂ) - 1) • E i j a := by
      have h1 := c3 a
      rw [hr, map_smul] at h1
      rw [sub_smul, one_smul, sub_eq_add_neg, ← h1]
      abel
    have hY2 : E j i (E i j (E i j a)) = 0 := by
      have h1 := c1 (E i j a)
      rw [hYX', e1, e2] at h1
      have h2 : E j i (E i j (E i j a)) =
          (1 - (((p : ℂ) + 1) - ((r : ℂ) - 1))) • E i j a := by
        rw [sub_smul, sub_smul, one_smul, ← h1]
        abel
      have h3 : (1 - (((p : ℂ) + 1) - ((r : ℂ) - 1))) = 0 := by
        linear_combination hprC
      rw [h2, h3, zero_smul]
    have h4 : ⟪E i j (E i j a), E i j (E i j a)⟫_ℂ = 0 := by
      rw [hA, hY2, inner_zero_right]
    exact inner_self_eq_zero.mp h4

end GlobalTheory.CompanionTheory.RealCount
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Sl2SquareKillsVectorStatement
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sl2_square_kills_vector : ∀ {n : ℕ} {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (E : Fin n → Fin n → Module.End ℂ Z), Formalism.REAL.GlRel E →
    (∀ x y (f g : Z), ⟪E x y f, g⟫_ℂ = ⟪f, E y x g⟫_ℂ) → ∀ {i j : Fin n}, i ≠ j → ∀ {a : Z}, a ≠ 0 →
    ∀ {p r : ℝ}, E i i a = (p : ℂ) • a → E j j a = (r : ℂ) • a → (∃ m : ℤ, p - r = m) → -1 ≤ p - r →
    (E i j a = 0 ∨ E j i a = 0) → ((E i j) ^ 2) a = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RealCount.sl2_square_kills | exact GlobalTheory.CompanionTheory.RealCount.sl2_square_kills | (intros; apply GlobalTheory.CompanionTheory.RealCount.sl2_square_kills <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParthasarathyRaoVaradarajan
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

noncomputable section

namespace GlobalTheory.CompanionTheory.SpinPRV


open ReciprocityTheory.ChartRestriction.DS.HW in
lemma tens_single {n : ℕ} {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Fin n → Fin n → Module.End ℂ Z) (G : Fin n → Fin n → Matrix ι ι ℂ) (a b : Fin n) (z : Z) (i : ι) :
    tensAct A (matrixFamilyDual G) a b (WithLp.toLp 2 (Pi.single i z) : PiLp 2 (fun _ : ι => Z)) =
      (WithLp.toLp 2 (Pi.single i (A a b z)) : PiLp 2 (fun _ : ι => Z)) -
        ∑ j, G a b i j • (WithLp.toLp 2 (Pi.single j z) : PiLp 2 (fun _ : ι => Z)) := by
  ext k
  simp only [ReciprocityTheory.ChartRestriction.DS.HW.tensAct, ReciprocityTheory.ChartRestriction.DS.HW.matrixFamilyDual]
  by_cases hk : k = i
  · subst hk
    simp [Pi.single_apply, Finset.sum_apply, Matrix.neg_apply, Matrix.transpose_apply, sub_eq_add_neg]
  · simp [Pi.single_apply, hk, Finset.sum_apply, Matrix.neg_apply, Matrix.transpose_apply]

open ReciprocityTheory.ChartRestriction.DS.HW in
lemma tens_apply {n : ℕ} {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] {ι : Type} [Fintype ι]
    (A : Fin n → Fin n → Module.End ℂ Z) (D : Fin n → Fin n → Matrix ι ι ℂ) (a b : Fin n) (x : PiLp 2 (fun _ : ι => Z)) (i : ι) :
    tensAct A D a b x i = A a b (x i) + ∑ j, D a b i j • x j := by
  simp [ReciprocityTheory.ChartRestriction.DS.HW.tensAct]

lemma toLp_eq_sum_single {Z : Type} [NormedAddCommGroup Z] {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → Z) :
    (WithLp.toLp 2 f : PiLp 2 (fun _ : ι => Z)) = ∑ i, (WithLp.toLp 2 (Pi.single i (f i)) : PiLp 2 (fun _ : ι => Z)) := by
  ext k
  simp [Pi.single_apply]

private theorem tensAct_tensAct_apply {n : ℕ} {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] {ι : Type} [Fintype ι]
    (A : Fin n → Fin n → Module.End ℂ Z) (D : Fin n → Fin n → Matrix ι ι ℂ) (a b c d : Fin n)
    (x : PiLp 2 (fun _ : ι => Z)) (i : ι) :
    ReciprocityTheory.ChartRestriction.DS.HW.tensAct A D a b (ReciprocityTheory.ChartRestriction.DS.HW.tensAct A D c d x) i =
      A a b (A c d (x i)) + ∑ k, D c d i k • A a b (x k) + ∑ k, D a b i k • A c d (x k) +
        ∑ k, (D a b * D c d) i k • x k := by
  rw [tens_apply, tens_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [tens_apply, map_add (f := _), map_sum, map_smul, smul_add, Finset.sum_add_distrib, Finset.smul_sum,
    smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm (f := fun k j => (D a b i j * D c d j k) • x k)]
  abel

private theorem kRel_tensAct_of_glRel {n : ℕ} {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] {ι : Type} [Fintype ι]
    [DecidableEq ι] (A : Fin n → Fin n → Module.End ℂ Z) (D : Fin n → Fin n → Matrix ι ι ℂ)
    (hA : Formalism.REAL.GlRel A) (hD : Formalism.REAL.GlRel D) :
    CompanionTheory.D.DSIC.KRel (fun _ => true) (ReciprocityTheory.ChartRestriction.DS.HW.tensAct A D) := by
  intro a b c d _ _
  apply LinearMap.ext
  intro x
  ext i
  have e1 : A a b (A c d (x i)) - A c d (A a b (x i)) =
      ((if b = c then A a d else 0) - (if d = a then A c b else 0)) (x i) := by
    have := LinearMap.congr_fun (hA a b c d) (x i)
    simpa [Module.End.mul_apply] using this
  have e2 : ∑ k, (D a b * D c d) i k • x k - ∑ k, (D c d * D a b) i k • x k =
      ∑ k, ((if b = c then D a d else 0) - (if d = a then D c b else 0)) i k • x k := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← sub_smul, ← Matrix.sub_apply, hD a b c d]
  have hl : (ReciprocityTheory.ChartRestriction.DS.HW.tensAct A D a b * ReciprocityTheory.ChartRestriction.DS.HW.tensAct A D c d -
      ReciprocityTheory.ChartRestriction.DS.HW.tensAct A D c d * ReciprocityTheory.ChartRestriction.DS.HW.tensAct A D a b) x i =
      (A a b (A c d (x i)) - A c d (A a b (x i))) +
        (∑ k, (D a b * D c d) i k • x k - ∑ k, (D c d * D a b) i k • x k) := by
    simp only [LinearMap.sub_apply, Module.End.mul_apply, PiLp.sub_apply, tensAct_tensAct_apply]
    abel
  rw [hl, e1, e2]
  split_ifs <;> simp [tens_apply, Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib] <;> abel

private theorem kUnit_tensAct_of_adjoint {n : ℕ} {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] {ι : Type} [Fintype ι]
    (A : Fin n → Fin n → Module.End ℂ Z) (D : Fin n → Fin n → Matrix ι ι ℂ)
    (hA : ∀ a b (x y : Z), inner ℂ (A a b x) y = inner ℂ x (A b a y))
    (hD : ∀ a b i j, star (D a b i j) = D b a j i) :
    CompanionTheory.D.DSIC.KUnit (fun _ => true) (ReciprocityTheory.ChartRestriction.DS.HW.tensAct A D) := by
  intro a b _ x y
  simp only [PiLp.inner_apply, tens_apply, inner_add_left, inner_add_right, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, Finset.sum_add_distrib, hA, starRingEnd_apply, hD]
  congr 1
  exact Finset.sum_comm

private theorem glRel_ext1Dual {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Fin n → Fin n → Matrix ι ι ℂ) (hG : Formalism.REAL.GlRel G) :
    Formalism.REAL.GlRel (ReciprocityTheory.ChartRestriction.DS.HW.matrixFamilyDual G) := by
  intro a b c d
  simp only [ReciprocityTheory.ChartRestriction.DS.HW.matrixFamilyDual, neg_mul_neg, ← Matrix.transpose_mul]
  rw [← Matrix.transpose_sub,
    show G c d * G a b - G a b * G c d = -(G a b * G c d - G c d * G a b) by abel, hG a b c d]
  split_ifs <;> simp [Matrix.transpose_sub] <;> abel

open ReciprocityTheory.ChartRestriction.DS.HW in
theorem assemble {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ) (hc : IsCliff c)
    (q : ι → ℂ) (hq0 : q ≠ 0) (hq1 : ∀ a, spinM c a a *ᵥ q = ((-(rhoV n a) : ℝ) : ℂ) • q)
    (hq2 : ∀ a b, a < b → spinM c b a *ᵥ q = 0)
    (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (Kf : Fin n → Fin n → Module.End ℂ V)
    (S : Submodule ℂ V) (ν : Fin n → ℤ) (v : V) (hK : Formalism.REAL.GlRel Kf)
    (hKu : ∀ a b (x y : V), ⟪Kf a b x, y⟫_ℂ = ⟪x, Kf b a y⟫_ℂ) (hfd : FiniteDimensional ℂ S)
    (hst : ∀ a b, ∀ w ∈ S, Kf a b w ∈ S) (hvS : v ∈ S) (hv0 : v ≠ 0)
    (hv : Formalism.REAL.KHighest (fun _ => true) Kf (wtR ν) v) :
    ∃ w : Equiv.Perm (Fin n), Antitone (fun a => wtR ν (w a) - rhoV n (w a)) ∧ ∃ x : ι → V, x ≠ 0 ∧
        Formalism.REAL.KHighest (fun _ => true) (yF Kf c) (fun a => wtR ν (w a) - rhoV n (w a)) x := by
  classical
  have hdom : Antitone (wtR ν) :=
    GlobalTheory.CompanionTheory.RealCount.highestWeight_antitone_of_finiteDimensional_stable V Kf S (wtR ν) v hK hfd hst hvS hv0 hv
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin n), Antitone (fun a => wtR ν (σ a) - rhoV n (σ a)) := by
    refine ⟨Tuple.sort (fun a => -(wtR ν a - rhoV n a)), ?_⟩
    intro x y hxy
    have := Tuple.monotone_sort (fun a => -(wtR ν a - rhoV n a)) hxy
    simp only [Function.comp] at this
    linarith
  refine ⟨σ, hσ, ?_⟩
  obtain ⟨Z, iZ1, iZ2, iZ3, E, u, a0, hEgl, hEu, hu0, hu, hirr, ha0, haw, hah⟩ :=
    GlobalTheory.T.exists_highest_weight_module (fun a => wtR ν (σ a) - rhoV n (σ a)) hσ (-(((n : ℝ) - 1) / 2))
      (fun a => ⟨ν (σ a) + ((σ a : ℕ) : ℤ), by simp only [wtR, rhoV]; push_cast; ring⟩) σ
  have hay : ∀ y, E y y a0 = ((wtR ν y - rhoV n y : ℝ) : ℂ) • a0 := by
    intro y
    have := haw (σ.symm y)
    simpa using this
  have hadj : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → (E i j ^ 2) a0 = 0 := by
    intro i j hij
    have hlt : i < j := by rw [Fin.lt_def]; omega
    have hne : i ≠ j := ne_of_lt hlt
    refine GlobalTheory.T.sl2_square_kills_vector E hEgl hEu hne ha0 (hay i) (hay j) ⟨ν i - ν j - 1, ?_⟩ ?_ ?_
    · simp only [wtR, rhoV]; rw [hij]; push_cast; ring
    · have := hdom hlt.le
      simp only [wtR, rhoV] at this ⊢
      rw [hij]; push_cast; linarith
    · rcases lt_or_gt_of_ne (σ.symm.injective.ne hne) with h | h
      · left; simpa using hah _ _ h
      · right; simpa using hah _ _ h
  obtain ⟨φ, hφq, hφup, hφdiag⟩ := GlobalTheory.T.spin_tensor_highest_weight c hc q hq0 hq1 hq2 E hEgl (wtR ν) a0 hay hadj
  have hφsum : ∀ f : ι → ℂ, φ f = ∑ j, f j • φ (Pi.single j 1) := by
    intro f
    conv_lhs => rw [show f = ∑ j, f j • (Pi.single j 1 : ι → ℂ) by
      ext k; simp [Finset.sum_apply, Pi.single_apply]]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_smul]
  have hcol : ∀ (M : Matrix ι ι ℂ) (i : ι), ∑ j, M j i • φ (Pi.single j 1) = φ (M *ᵥ Pi.single i 1) := by
    intro M i
    rw [hφsum (M *ᵥ Pi.single i 1)]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  let t : PiLp 2 (fun _ : ι => Z) := WithLp.toLp 2 (fun i => φ (Pi.single i 1))
  have hETt : ∀ a b i, ReciprocityTheory.ChartRestriction.DS.HW.tensAct E (ReciprocityTheory.ChartRestriction.DS.HW.matrixFamilyDual (spinM c)) a b t i =
      E a b (φ (Pi.single i 1)) - φ (spinM c a b *ᵥ Pi.single i 1) := by
    intro a b i
    rw [tens_apply, ← hcol]
    simp [ReciprocityTheory.ChartRestriction.DS.HW.matrixFamilyDual, t, sub_eq_add_neg, Finset.sum_neg_distrib, neg_smul]
  have hthigh : Formalism.REAL.KHighest (fun _ => true)
      (ReciprocityTheory.ChartRestriction.DS.HW.tensAct E (ReciprocityTheory.ChartRestriction.DS.HW.matrixFamilyDual (spinM c))) (wtR ν) t := by
    refine ⟨fun a => ?_, fun a b hab _ => ?_⟩
    · ext i
      rw [hETt, hφdiag]
      simp [t]
    · ext i
      rw [hETt, hφup a b hab]
      simp
  have ht0 : t ≠ 0 := by
    intro h
    apply ha0
    rw [← hφq, hφsum]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    have : t j = 0 := by rw [h]; simp
    simp only [t, PiLp.toLp_apply] at this
    simp [this]
  have hDstar : ∀ a b i j, star (ReciprocityTheory.ChartRestriction.DS.HW.matrixFamilyDual (spinM c) a b i j) =
      ReciprocityTheory.ChartRestriction.DS.HW.matrixFamilyDual (spinM c) b a j i := by
    intro a b i j
    have := congrFun (congrFun ((GlobalTheory.T.spin_gl_relations_adjoint c hc).2 a b) i) j
    simp only [ReciprocityTheory.ChartRestriction.DS.HW.matrixFamilyDual, Matrix.neg_apply, Matrix.transpose_apply, star_neg,
      Matrix.conjTranspose_apply] at this ⊢
    rw [this]
  obtain ⟨ψ, hψt, hψeq⟩ := CompanionTheory.D.DSIC.hHWMap n (fun _ => true) (PiLp 2 (fun _ : ι => Z)) V
    (ReciprocityTheory.ChartRestriction.DS.HW.tensAct E (ReciprocityTheory.ChartRestriction.DS.HW.matrixFamilyDual (spinM c))) Kf (wtR ν) t v S
    (kRel_tensAct_of_glRel E _ hEgl (glRel_ext1Dual _ (GlobalTheory.T.spin_gl_relations_adjoint c hc).1))
    (kUnit_tensAct_of_adjoint E _ hEu hDstar) (fun a b c d _ _ => hK a b c d) (fun a b _ x y => hKu a b x y)
    ht0 hthigh hv hfd (fun a b _ w hw => hst a b w hw) hvS
  have hkey : ∀ a b (z : Z) (i : ι), ψ (WithLp.toLp 2 (Pi.single i (E a b z))) =
      Kf a b (ψ (WithLp.toLp 2 (Pi.single i z))) + ∑ j, spinM c a b i j • ψ (WithLp.toLp 2 (Pi.single j z)) := by
    intro a b z i
    have h1 := hψeq a b rfl (WithLp.toLp 2 (Pi.single i z))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [tens_single, map_sub, map_sum] at h1
    simp only [map_smul] at h1
    rw [← h1]
    abel
  have hsm : ∀ (r : ℂ) (z : Z) (i : ι), ψ (WithLp.toLp 2 (Pi.single i (r • z))) =
      r • ψ (WithLp.toLp 2 (Pi.single i z)) := by
    intro r z i
    rw [show (Pi.single i (r • z) : ι → Z) = r • Pi.single i z by ext k; simp [Pi.single_apply]]
    rw [WithLp.toLp_smul, map_smul]
  refine ⟨fun i => ψ (WithLp.toLp 2 (Pi.single i u)), ?_, ?_⟩
  · intro hx
    have hall : ∀ i, ψ (WithLp.toLp 2 (Pi.single i u)) = 0 := fun i => congrFun hx i
    let W : Submodule ℂ Z :=
      { carrier := {z | ∀ i, ψ (WithLp.toLp 2 (Pi.single i z)) = 0}
        add_mem' := by
          intro z1 z2 h1 h2 i
          simp only [Set.mem_setOf_eq] at h1 h2 ⊢
          rw [Pi.single_add, WithLp.toLp_add, map_add (f := _), h1 i, h2 i, add_zero]
        zero_mem' := by
          intro i
          simp
        smul_mem' := by
          intro r z h i
          simp only [Set.mem_setOf_eq] at h ⊢
          rw [hsm, h i, smul_zero] }
    have hstabW : ∀ (a b : Fin n), ∀ z ∈ W, E a b z ∈ W := by
      intro a b z hz
      have hz' : ∀ j, ψ (WithLp.toLp 2 (Pi.single j z)) = 0 := hz
      show ∀ i, ψ (WithLp.toLp 2 (Pi.single i (E a b z))) = 0
      intro i
      rw [hkey]
      simp only [hz', map_zero, smul_zero, Finset.sum_const_zero, add_zero]
    have huW : u ∈ W := hall
    have hWtop : W = ⊤ := hirr W hstabW huW
    apply hv0
    rw [← hψt]
    show ψ (WithLp.toLp 2 (fun i => φ (Pi.single i 1))) = 0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [toLp_eq_sum_single, map_sum]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have hmem : φ (Pi.single i 1) ∈ W := by rw [hWtop]; trivial
    exact hmem i
  · have hy : ∀ a b, yF Kf c a b (fun i => ψ (WithLp.toLp 2 (Pi.single i u))) =
        fun i => ψ (WithLp.toLp 2 (Pi.single i (E a b u))) := by
      intro a b
      funext i
      rw [hkey]
      rfl
    refine ⟨fun a => ?_, fun a b hab _ => ?_⟩
    · rw [hy, hu.1 a]
      funext i
      rw [hsm]
      rfl
    · rw [hy, hu.2 a b hab rfl]
      funext i
      simp

theorem spin_parthasarathy_rao_varadarajan : ∀ n : ℕ, ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (c : Fin n → Fin n → Matrix ι ι ℂ), IsCliff c ∧
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (Kf : Fin n → Fin n → Module.End ℂ V)
      (S : Submodule ℂ V) (ν : Fin n → ℤ) (v : V), Formalism.REAL.GlRel Kf →
      (∀ a b (x y : V), ⟪Kf a b x, y⟫_ℂ = ⟪x, Kf b a y⟫_ℂ) → FiniteDimensional ℂ S → (∀ a b, ∀ w ∈ S, Kf a b w ∈ S) →
      v ∈ S → v ≠ 0 → Formalism.REAL.KHighest (fun _ => true) Kf (wtR ν) v →
      ∃ w : Equiv.Perm (Fin n), Antitone (fun a => wtR ν (w a) - rhoV n (w a)) ∧ ∃ x : ι → V, x ≠ 0 ∧
        Formalism.REAL.KHighest (fun _ => true) (yF Kf c) (fun a => wtR ν (w a) - rhoV n (w a)) x := by
  intro n
  obtain ⟨ι, hF, hD, c, hc, q, hq0, hq⟩ := GlobalTheory.T.exists_clifford_lowest_vector n
  letI := hF
  letI := hD
  obtain ⟨h1, h2⟩ := GlobalTheory.T.clifford_vector_spin_weight c hc q hq
  refine ⟨ι, hF, hD, c, hc, ?_⟩
  intro V _ _ Kf S ν v hK hKu hfd hst hvS hv0 hv
  exact assemble c hc q hq0 h1 h2 V Kf S ν v hK hKu hfd hst hvS hv0 hv

end GlobalTheory.CompanionTheory.SpinPRV
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParthasarathyRaoVaradarajanStatement
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parthasarathy_rao_varadarajan : ∀ n : ℕ, ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (c : Fin n → Fin n → Matrix ι ι ℂ), IsCliff c ∧
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (Kf : Fin n → Fin n → Module.End ℂ V)
      (S : Submodule ℂ V) (ν : Fin n → ℤ) (v : V), Formalism.REAL.GlRel Kf →
      (∀ a b (x y : V), ⟪Kf a b x, y⟫_ℂ = ⟪x, Kf b a y⟫_ℂ) → FiniteDimensional ℂ S → (∀ a b, ∀ w ∈ S, Kf a b w ∈ S) →
      v ∈ S → v ≠ 0 → Formalism.REAL.KHighest (fun _ => true) Kf (wtR ν) v →
      ∃ w : Equiv.Perm (Fin n), Antitone (fun a => wtR ν (w a) - rhoV n (w a)) ∧ ∃ x : ι → V, x ≠ 0 ∧
        Formalism.REAL.KHighest (fun _ => true) (yF Kf c) (fun a => wtR ν (w a) - rhoV n (w a)) x := by
  first | exact @GlobalTheory.CompanionTheory.SpinPRV.spin_parthasarathy_rao_varadarajan | exact GlobalTheory.CompanionTheory.SpinPRV.spin_parthasarathy_rao_varadarajan | (intros; apply GlobalTheory.CompanionTheory.SpinPRV.spin_parthasarathy_rao_varadarajan <;> assumption)
end
