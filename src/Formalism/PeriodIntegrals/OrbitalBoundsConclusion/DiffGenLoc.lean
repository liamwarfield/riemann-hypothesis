module

public import Mathlib

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DiffGenLoc
section -- merged from Formalism.PeriodIntegrals.DiffGenLoc
noncomputable section

namespace PI.DiffGenLoc

open NumberField IsDedekindDomain

abbrev Fv (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) := v.adicCompletion F

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

def IsDiffVal (d : Fv F v) : Prop :=
  d ≠ 0 ∧ (∀ x ∈ differentIdeal ℤ (𝓞 F), Valued.v (algebraMap F (Fv F v) (x : F)) ≤ Valued.v d) ∧
    ∃ x ∈ differentIdeal ℤ (𝓞 F), Valued.v (algebraMap F (Fv F v) (x : F)) = Valued.v d

def DiffExists : Prop := ∃ d, IsDiffVal v d

end PI.DiffGenLoc
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDifferentGenerators.DiffExistsMain
noncomputable section

namespace PI.DiffGenLoc.UnitaryGroupMassFormula

open NumberField IsDedekindDomain WithZero

theorem val_alg {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) :
    Valued.v (algebraMap F (Fv F v) (x : F)) = v.intValuation x := by
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : F)).trans
      (HeightOneSpectrum.valuation_of_algebraMap v x)

theorem diffExists_main {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : DiffExists v := by
  classical
  have hI : differentIdeal ℤ (𝓞 F) ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨y, hyI, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hne : ∀ x : 𝓞 F, x ≠ 0 → v.intValuation x ≠ 0 := fun x hx => by
    exact v.intValuation_ne_zero x hx
  let f : 𝓞 F → ℕ := fun x =>
    if hx : x = 0 then 0 else (-(Multiplicative.toAdd (WithZero.unzero (hne x hx)))).toNat
  have hfdef : ∀ z (hz : z ≠ 0), f z = (-(Multiplicative.toAdd (WithZero.unzero (hne z hz)))).toNat :=
    fun z hz => dif_neg hz
  have key : ∀ z : 𝓞 F, ∀ hz : z ≠ 0,
      v.intValuation z = ((Multiplicative.ofAdd (-(f z : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro z hz
    have hu : ((WithZero.unzero (hne z hz) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = v.intValuation z :=
      WithZero.coe_unzero _
    have hle : Multiplicative.toAdd (WithZero.unzero (hne z hz)) ≤ 0 := by
      have h1 : ((WithZero.unzero (hne z hz) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤
          ((1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
        rw [hu, WithZero.coe_one]
        exact v.intValuation_le_one z
      rw [WithZero.coe_le_coe] at h1
      have h2 := Multiplicative.toAdd_le.2 h1
      simpa using h2
    rw [hfdef z hz, Int.toNat_of_nonneg (by linarith), neg_neg, ofAdd_toAdd, hu]
  have hP : ∃ n, ∃ x ∈ differentIdeal ℤ (𝓞 F), x ≠ 0 ∧ f x = n := ⟨_, y, hyI, hy0, rfl⟩
  obtain ⟨x₀, hx₀I, hx₀0, hfx₀⟩ := Nat.find_spec hP
  refine ⟨algebraMap F (Fv F v) (x₀ : F), ?_, ?_, x₀, hx₀I, rfl⟩
  · intro h
    apply hx₀0
    have h1 : ((x₀ : F)) = 0 := (algebraMap F (Fv F v)).injective (h.trans (map_zero _).symm)
    exact_mod_cast h1
  · intro x hxI
    rw [val_alg, val_alg]
    by_cases hx : x = 0
    · simp [hx]
    have hmin : Nat.find hP ≤ f x := Nat.find_min' hP ⟨x, hxI, hx, rfl⟩
    rw [key x hx, key x₀ hx₀0, WithZero.coe_le_coe, Multiplicative.ofAdd_le, neg_le_neg_iff, Nat.cast_le, hfx₀]
    exact hmin

end PI.DiffGenLoc.UnitaryGroupMassFormula
end
end

theorem diffExists {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) : PI.DiffGenLoc.DiffExists v :=
  PI.DiffGenLoc.UnitaryGroupMassFormula.diffExists_main v
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NormGramAtOrigin
section -- merged from Formalism.PeriodIntegrals.NormGramAtOrigin
noncomputable section

namespace PI.NormGramAtOrigin

section G

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def hform (σ : A →+* A) (J : Matrix n n A) (x y : n → A) : A := ∑ i, ∑ j, σ (x i) * J i j * y j

end G

def gram {E : Type} [Field E] (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Fin r → Fin n → E) :
    Matrix (Fin r) (Fin r) E := fun a b => hform σ J (X a) (X b)

def Statement : Prop :=
  ∀ (E : Type) [Field E] [StarRing E] [CharZero E] (n r : ℕ), r ≤ n →
    ∀ J : Matrix (Fin n) (Fin n) E, (∀ i j, star (J j i) = J i j) → J.det ≠ 0 →
      ∃ X : Fin r → Fin n → E, (gram (starRingEnd E) J X).det ≠ 0

end PI.NormGramAtOrigin
end
end

private lemma hform_add_right_orbital_bounds_conclusion {E : Type} [Field E] (σ : E →+* E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (x y z : Fin n → E) :
    PI.NormGramAtOrigin.hform σ J x (y + z) = PI.NormGramAtOrigin.hform σ J x y + PI.NormGramAtOrigin.hform σ J x z := by
  simp only [PI.NormGramAtOrigin.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma hform_smul_right_orbital_bounds_conclusion {E : Type} [Field E] (σ : E →+* E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) (c : E) :
    PI.NormGramAtOrigin.hform σ J x (c • y) = c * PI.NormGramAtOrigin.hform σ J x y := by
  simp only [PI.NormGramAtOrigin.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private lemma hform_sum_right' {E : Type} [Field E] (σ : E →+* E) {n k : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (f : Fin k → Fin n → E) :
    PI.NormGramAtOrigin.hform σ J x (∑ a, f a) = ∑ a, PI.NormGramAtOrigin.hform σ J x (f a) := by
  simp only [PI.NormGramAtOrigin.hform, Finset.sum_apply, Finset.mul_sum]
  calc _ = ∑ i, ∑ a, ∑ j, σ (x i) * J i j * f a j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

private lemma Hf_sub_right' {E : Type} [Field E] (σ : E →+* E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (x y z : Fin n → E) :
    PI.NormGramAtOrigin.hform σ J x (y - z) = PI.NormGramAtOrigin.hform σ J x y - PI.NormGramAtOrigin.hform σ J x z := by
  simp only [PI.NormGramAtOrigin.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private lemma hform_symm_of_involutive_of_hermitian {E : Type} [Field E] (σ : E →+* E) (hσ : ∀ a, σ (σ a) = a) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → E) :
    σ (PI.NormGramAtOrigin.hform σ J x y) = PI.NormGramAtOrigin.hform σ J y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [PI.NormGramAtOrigin.hform, map_sum, map_mul, hσ]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [hJ j i]; ring

private lemma hform_add_smul_self_ne_zero_of_isotropic_pair {E : Type} [Field E] [CharZero E] (σ : E →+* E) (hσ : ∀ a, σ (σ a) = a)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j) (w y : Fin n → E)
    (hw : PI.NormGramAtOrigin.hform σ J w w = 0) (hy : PI.NormGramAtOrigin.hform σ J y y = 0) (t : E)
    (ht : PI.NormGramAtOrigin.hform σ J w y = t) (ht0 : t ≠ 0) :
    PI.NormGramAtOrigin.hform σ J (w + σ t • y) (w + σ t • y) ≠ 0 := by
  have e1 : PI.NormGramAtOrigin.hform σ J w (w + σ t • y) = σ t * t := by
    rw [hform_add_right_orbital_bounds_conclusion, hform_smul_right_orbital_bounds_conclusion, hw, ht, zero_add]
  have e2 : PI.NormGramAtOrigin.hform σ J y w = σ t := by
    rw [← hform_symm_of_involutive_of_hermitian σ hσ J hJ w y, ht]
  have e3 : PI.NormGramAtOrigin.hform σ J y (w + σ t • y) = σ t := by
    rw [hform_add_right_orbital_bounds_conclusion, hform_smul_right_orbital_bounds_conclusion, hy, e2, mul_zero, add_zero]
  have e4 : PI.NormGramAtOrigin.hform σ J (w + σ t • y) w = t * σ t := by
    rw [← hform_symm_of_involutive_of_hermitian σ hσ J hJ w, e1, map_mul, hσ]
  have e5 : PI.NormGramAtOrigin.hform σ J (w + σ t • y) y = t := by
    rw [← hform_symm_of_involutive_of_hermitian σ hσ J hJ y, e3, hσ]
  rw [hform_add_right_orbital_bounds_conclusion, hform_smul_right_orbital_bounds_conclusion, e4, e5]
  have hs : σ t ≠ 0 := by
    intro h
    apply ht0
    rw [← hσ t, h, map_zero]
  have e6 : t * σ t + σ t * t = 2 * (t * σ t) := by ring
  rw [e6]
  exact mul_ne_zero two_ne_zero (mul_ne_zero ht0 hs)

private lemma exists_ne_zero_mulVec_eq_zero_of_lt {E : Type} [Field E] {k n : ℕ} (hk : k < n) (A : Fin k → Fin n → E) :
    ∃ y : Fin n → E, y ≠ 0 ∧ ∀ a, ∑ j, A a j * y j = 0 := by
  obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr
    (Matrix.det_eq_zero_of_row_eq_zero
      (A := Matrix.of fun (i j : Fin n) => if h : (i : ℕ) < k then A ⟨i, h⟩ j else 0)
      ⟨k, hk⟩ (fun j => by simp))
  refine ⟨y, hy0, fun a => ?_⟩
  have h := congrFun hy ⟨a, lt_trans a.isLt hk⟩
  simpa [Matrix.mulVec, dotProduct] using h

private lemma exists_hform_ne_zero_of_det_ne_zero {E : Type} [Field E] (σ : E →+* E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJd : J.det ≠ 0) (y : Fin n → E) (hy : y ≠ 0) :
    ∃ z : Fin n → E, PI.NormGramAtOrigin.hform σ J z y ≠ 0 := by
  have hJy : Matrix.mulVec J y ≠ 0 := fun h => hJd (Matrix.exists_mulVec_eq_zero_iff.mp ⟨y, hy, h⟩)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hJy
  refine ⟨Pi.single i 1, ?_⟩
  have e : PI.NormGramAtOrigin.hform σ J (Pi.single i 1) y = Matrix.mulVec J y i := by
    unfold PI.NormGramAtOrigin.hform
    rw [Finset.sum_eq_single i]
    · simp [Matrix.mulVec, dotProduct]
    · intro l _ hl
      simp [Pi.single_apply, hl]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [e]
  exact hi

private lemma hermC_ppos_col_castLE {E : Type} [Field E] (σ : E →+* E) (hσ : ∀ a, σ (σ a) = a) {n k : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j) (v : Fin k → Fin n → E)
    (hvo : ∀ a b, a ≠ b → PI.NormGramAtOrigin.hform σ J (v a) (v b) = 0)
    (hvd : ∀ a, PI.NormGramAtOrigin.hform σ J (v a) (v a) ≠ 0) (z y0 : Fin n → E)
    (hy0W : ∀ a, PI.NormGramAtOrigin.hform σ J (v a) y0 = 0) (hz : PI.NormGramAtOrigin.hform σ J z y0 ≠ 0) :
    ∃ p : Fin n → E, (∀ b, PI.NormGramAtOrigin.hform σ J (v b) p = 0) ∧ PI.NormGramAtOrigin.hform σ J p y0 ≠ 0 := by
  refine ⟨z - ∑ a, (PI.NormGramAtOrigin.hform σ J (v a) z / PI.NormGramAtOrigin.hform σ J (v a) (v a)) • v a,
    fun b => ?_, ?_⟩
  · rw [Hf_sub_right', hform_sum_right', Finset.sum_eq_single b]
    · rw [hform_smul_right_orbital_bounds_conclusion, div_mul_cancel₀ _ (hvd b), sub_self]
    · intro a _ hab
      rw [hform_smul_right_orbital_bounds_conclusion, hvo b a (Ne.symm hab), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ b) h
  · rw [← hform_symm_of_involutive_of_hermitian σ hσ J hJ y0, Hf_sub_right', hform_sum_right']
    have h0 : ∀ a, PI.NormGramAtOrigin.hform σ J y0
        ((PI.NormGramAtOrigin.hform σ J (v a) z / PI.NormGramAtOrigin.hform σ J (v a) (v a)) • v a) = 0 := by
      intro a
      rw [hform_smul_right_orbital_bounds_conclusion, ← hform_symm_of_involutive_of_hermitian σ hσ J hJ (v a) y0, hy0W a, map_zero, mul_zero]
    simp only [h0, Finset.sum_const_zero, sub_zero]
    rw [hform_symm_of_involutive_of_hermitian σ hσ J hJ]
    exact hz

private lemma Hf_e_e_eq_ite {E : Type} [Field E] [CharZero E] (σ : E →+* E) (hσ : ∀ a, σ (σ a) = a)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j) (hJd : J.det ≠ 0) :
    ∀ k, k ≤ n → ∃ v : Fin k → Fin n → E,
      (∀ a b, a ≠ b → PI.NormGramAtOrigin.hform σ J (v a) (v b) = 0) ∧
      ∀ a, PI.NormGramAtOrigin.hform σ J (v a) (v a) ≠ 0 := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨fun a => a.elim0, fun a => a.elim0, fun a => a.elim0⟩
  | succ k ih =>
    intro hk
    obtain ⟨v, hvo, hvd⟩ := ih (Nat.le_of_succ_le hk)
    obtain ⟨y0, hy0, hW0⟩ := exists_ne_zero_mulVec_eq_zero_of_lt (Nat.lt_of_succ_le hk) (fun a j => ∑ l, σ (v a l) * J l j)
    have hy0W : ∀ a, PI.NormGramAtOrigin.hform σ J (v a) y0 = 0 := by
      intro a
      calc _ = ∑ j, (∑ l, σ (v a l) * J l j) * y0 j := by
            simp only [PI.NormGramAtOrigin.hform, Finset.sum_mul]
            exact Finset.sum_comm
        _ = 0 := hW0 a
    obtain ⟨z, hz⟩ := exists_hform_ne_zero_of_det_ne_zero σ J hJd y0 hy0
    obtain ⟨p, hpW, hp⟩ := hermC_ppos_col_castLE σ hσ J hJ v hvo hvd z y0 hy0W hz
    have key : ∃ y, (∀ a, PI.NormGramAtOrigin.hform σ J (v a) y = 0) ∧
        PI.NormGramAtOrigin.hform σ J y y ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      refine hform_add_smul_self_ne_zero_of_isotropic_pair σ hσ J hJ p y0 (hcon p hpW) (hcon y0 hy0W) _ rfl hp (hcon _ fun a => ?_)
      rw [hform_add_right_orbital_bounds_conclusion, hform_smul_right_orbital_bounds_conclusion, hpW a, hy0W a, mul_zero, add_zero]
    obtain ⟨y, hyW, hyy⟩ := key
    refine ⟨Fin.snoc (α := fun _ => Fin n → E) v y, fun a b hab => ?_, fun a => ?_⟩
    · rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl <;>
        rcases Fin.eq_castSucc_or_eq_last b with ⟨b, rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc]
        exact hvo a b fun h => hab (congrArg Fin.castSucc h)
      · simp only [Fin.snoc_castSucc, Fin.snoc_last]
        exact hyW a
      · simp only [Fin.snoc_castSucc, Fin.snoc_last]
        rw [← hform_symm_of_involutive_of_hermitian σ hσ J hJ, hyW b, map_zero]
      · exact absurd rfl hab
    · rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc]
        exact hvd a
      · simp only [Fin.snoc_last]
        exact hyy

theorem exists_nondegenerate : PI.NormGramAtOrigin.Statement := by
  unfold PI.NormGramAtOrigin.Statement
  intro E _ _ _ n r hr J hJ hJd
  have hσ : ∀ a : E, starRingEnd E (starRingEnd E a) = a := fun a => by simp
  have hJ' : ∀ i j, starRingEnd E (J j i) = J i j := fun i j => by
    rw [starRingEnd_apply]
    exact hJ i j
  obtain ⟨v, hvo, hvd⟩ := Hf_e_e_eq_ite (starRingEnd E) hσ J hJ' hJd r hr
  refine ⟨v, ?_⟩
  have hg : PI.NormGramAtOrigin.gram (starRingEnd E) J v =
      Matrix.diagonal (fun a => PI.NormGramAtOrigin.hform (starRingEnd E) J (v a) (v a)) := by
    ext a b
    by_cases h : a = b
    · subst h
      simp [PI.NormGramAtOrigin.gram]
    · simp [PI.NormGramAtOrigin.gram, Matrix.diagonal_apply_ne _ h, hvo a b h]
  rw [hg, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun a _ => hvd a
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhProdConv
section -- merged from Formalism.PeriodIntegrals.PhProdConv
noncomputable section

open MeasureTheory NumberField
open scoped InnerProductSpace

namespace PI.PhProdConv

section Defs

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def PhConv (μ : Measure G) (ph m : G → ℂ) : Prop :=
  m 1 = 1 ∧ (∀ g, ph g⁻¹ = star (ph g)) ∧
    ∀ x y : G, Integrable (fun g => ph g * ph (x⁻¹ * g⁻¹ * y)) μ ∧
      ∫ g, ph g * ph (x⁻¹ * g⁻¹ * y) ∂μ = m x * ph y

end Defs

def ProdConv : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalGroup (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
    [∀ i, SecondCountableTopology (G i)] (μ : ∀ i, Measure (G i)) [∀ i, SigmaFinite (μ i)]
    [∀ i, (μ i).IsMulLeftInvariant] [∀ i, (μ i).IsInvInvariant] (ph m : ∀ i, G i → ℂ),
    (∀ i, Integrable (ph i) (μ i)) → (∀ i, PhConv (μ i) (ph i) (m i)) →
      Integrable (fun g : ∀ i, G i => ∏ i, ph i (g i)) (Measure.pi μ) ∧
      PhConv (Measure.pi μ) (fun g => ∏ i, ph i (g i)) (fun g => ∏ i, m i (g i))

end PI.PhProdConv
end
end

theorem isConvIdempotent_pi : PI.PhProdConv.ProdConv := by
  intro ι _ _ G _ _ _ _ _ _ μ _ _ _ ph m hint hconv
  refine ⟨MeasureTheory.Integrable.fintype_prod_dep hint, ?_⟩
  unfold PI.PhProdConv.PhConv
  refine ⟨?_, fun g => ?_, fun x y => ?_⟩
  · exact Finset.prod_eq_one (fun i _ => (hconv i).1)
  · change ∏ i, ph i ((g i)⁻¹) = starRingEnd ℂ (∏ i, ph i (g i))
    rw [map_prod]
    exact Finset.prod_congr rfl (fun i _ => (hconv i).2.1 (g i))
  · have key : (fun g : ∀ i, G i => (∏ i, ph i (g i)) * ∏ i, ph i ((x⁻¹ * g⁻¹ * y) i)) =
        fun g => ∏ i, (fun i (h : G i) => ph i h * ph i ((x i)⁻¹ * h⁻¹ * y i)) i (g i) := by
      funext g
      rw [← Finset.prod_mul_distrib]
      rfl
    change MeasureTheory.Integrable
        (fun g : ∀ i, G i => (∏ i, ph i (g i)) * ∏ i, ph i ((x⁻¹ * g⁻¹ * y) i))
        (MeasureTheory.Measure.pi μ) ∧
      ∫ g, (fun g : ∀ i, G i => (∏ i, ph i (g i)) * ∏ i, ph i ((x⁻¹ * g⁻¹ * y) i)) g
        ∂(MeasureTheory.Measure.pi μ) = (∏ i, m i (x i)) * ∏ i, ph i (y i)
    rw [key]
    refine ⟨MeasureTheory.Integrable.fintype_prod_dep
      (fun i => ((hconv i).2.2 (x i) (y i)).1), ?_⟩
    rw [MeasureTheory.integral_fintype_prod_eq_prod (𝕜 := ℂ)
      (fun i (h : G i) => ph i h * ph i ((x i)⁻¹ * h⁻¹ * y i)), ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => ((hconv i).2.2 (x i) (y i)).2)
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SumAntidiagonalTuple
section -- merged from Formalism.PeriodIntegrals.SumAntidiagonalTuple
namespace PI

def SumAntidiagonalTuple : Prop :=
  ∀ D T : ℕ, D < T →
    ∑ k ∈ Finset.range (T - D), (Finset.Nat.antidiagonalTuple D k).card = Nat.choose (T - 1) D

end PI
end

private theorem sum_range_add_choose_eq_choose_succ (E n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (k + E).choose E = (n + E + 1).choose (E + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, show n + 1 + E + 1 = (n + E + 1) + 1 by omega,
      Nat.choose_succ_succ (n + E + 1) E, show n + 1 + E = n + E + 1 by omega]
    simp only [Nat.succ_eq_add_one]
    omega

private theorem card_antidiagonal_tuple_succ_eq_sum_range (D k : ℕ) :
    (Finset.Nat.antidiagonalTuple (D + 1) k).card =
      ∑ i ∈ Finset.range (k + 1), (Finset.Nat.antidiagonalTuple D (k - i)).card := by
  calc (Finset.Nat.antidiagonalTuple (D + 1) k).card
      = ((Finset.range (k + 1)).sigma fun i => Finset.Nat.antidiagonalTuple D (k - i)).card := by
        refine Finset.card_nbij' (fun x => ⟨x 0, Fin.tail x⟩) (fun p => Fin.cons p.1 p.2)
          ?_ ?_ ?_ ?_
        · intro x hx
          simp only [Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple] at hx
          rw [Fin.sum_univ_succ] at hx
          simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range,
            Finset.Nat.mem_antidiagonalTuple, Fin.tail]
          omega
        · rintro ⟨i, y⟩ hp
          simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range,
            Finset.Nat.mem_antidiagonalTuple] at hp
          simp only [Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_succ,
            Fin.cons_zero, Fin.cons_succ]
          omega
        · intro x _
          simp
        · rintro ⟨i, y⟩ _
          simp
    _ = ∑ i ∈ Finset.range (k + 1), (Finset.Nat.antidiagonalTuple D (k - i)).card :=
        Finset.card_sigma _ _

private theorem card_antidiagonal_tuple_succ_eq_choose (D : ℕ) :
    ∀ k, (Finset.Nat.antidiagonalTuple (D + 1) k).card = (k + D).choose D := by
  induction D with
  | zero =>
    intro k
    rw [card_antidiagonal_tuple_succ_eq_sum_range, Finset.sum_eq_single k]
    · simp [Finset.Nat.antidiagonalTuple_zero_zero]
    · intro i hi hik
      simp only [Finset.mem_range] at hi
      obtain ⟨m, hm⟩ : ∃ m, k - i = m + 1 := ⟨k - i - 1, by omega⟩
      rw [hm, Finset.Nat.antidiagonalTuple_zero_succ, Finset.card_empty]
    · intro h
      simp at h
  | succ D ih =>
    intro k
    rw [card_antidiagonal_tuple_succ_eq_sum_range]
    simp only [ih]
    have h : ∑ j ∈ Finset.range (k + 1), (k - j + D).choose D =
        ∑ j ∈ Finset.range (k + 1), (j + D).choose D := by
      have := Finset.sum_range_reflect (fun i => (i + D).choose D) (k + 1)
      simpa only [Nat.add_sub_cancel] using this
    rw [h, sum_range_add_choose_eq_choose_succ, Nat.add_assoc]

theorem sum_antidiagonalTuple : PI.SumAntidiagonalTuple := by
  intro D T hDT
  cases D with
  | zero =>
    obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
    simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.choose_zero_right]
    rw [Finset.sum_range_succ']
    simp [Finset.Nat.antidiagonalTuple_zero_succ, Finset.Nat.antidiagonalTuple_zero_zero]
  | succ E =>
    obtain ⟨n, rfl⟩ : ∃ n, T = n + E + 2 := ⟨T - E - 2, by omega⟩
    have h1 : n + E + 2 - (E + 1) = n + 1 := by omega
    have h2 : n + E + 2 - 1 = n + E + 1 := by omega
    rw [h1, h2]
    simp only [card_antidiagonal_tuple_succ_eq_choose]
    exact sum_range_add_choose_eq_choose_succ E n
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.InertPrime
section -- merged from Formalism.PeriodIntegrals.InertPrime
open NumberField

namespace PI

def InertPrime : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (b : K) (d p : ℕ), b ^ 2 = -(d : K) → p.Prime →
    jacobiSym (-(d : ℤ)) p = -1 → (Ideal.span {(p : 𝓞 K)}).IsPrime

end PI
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertPrimeJacobi.NotIsSquareOfJacobi
open NumberField

namespace PI.InertPrimeWork

theorem not_isSquare_of_jacobi {d p : ℕ} (hp : p.Prime) (h : jacobiSym (-(d : ℤ)) p = -1) :
    ¬ IsSquare (((-(d : ℤ) : ℤ)) : ZMod p) := by
  haveI := Fact.mk hp
  rw [← jacobiSym.legendreSym.to_jacobiSym] at h
  exact (legendreSym.eq_neg_one_iff p).1 h

theorem inert (K : Type) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2) (b : K) (d p : ℕ)
    (hb : b ^ 2 = -(d : K)) (hp : p.Prime) (hj : jacobiSym (-(d : ℤ)) p = -1) :
    (Ideal.span {(p : 𝓞 K)}).IsPrime := by
  haveI := Fact.mk hp
  have hsq := not_isSquare_of_jacobi hp hj
  have hnormI : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
    rw [Ideal.absNorm_span_singleton]
    have e : ((p : 𝓞 K)) = algebraMap ℤ (𝓞 K) (p : ℤ) := by simp
    rw [e, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, hK]
    simp
  have hp1 : p ^ 2 ≠ 1 := by
    have := hp.one_lt
    nlinarith
  have hIne : Ideal.span {(p : 𝓞 K)} ≠ ⊤ := by
    intro h
    rw [h, Ideal.absNorm_top] at hnormI
    exact hp1 hnormI.symm
  obtain ⟨P, hPmax, hIP⟩ := Ideal.exists_le_maximal _ hIne
  have hdvd : Ideal.absNorm P ∣ p ^ 2 := hnormI ▸ Ideal.absNorm_dvd_absNorm_of_le hIP
  obtain ⟨k, hk, hPk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  interval_cases k
  · rw [pow_zero, Ideal.absNorm_eq_one_iff] at hPk
    exact absurd hPk hPmax.ne_top
  · exfalso
    rw [pow_one] at hPk
    have hP0 : P ≠ ⊥ := by
      rintro rfl
      rw [Ideal.absNorm_bot] at hPk
      exact hp.ne_zero hPk.symm
    haveI : Finite (𝓞 K ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0
    letI : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    have hcard : Fintype.card (𝓞 K ⧸ P) = p := by
      rw [Fintype.card_eq_nat_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hPk]
    haveI : CharP (𝓞 K ⧸ P) p := charP_of_card_eq_prime hcard
    let ψ : ZMod p →+* 𝓞 K ⧸ P := ZMod.castHom (dvd_refl p) _
    have hψi : Function.Injective ψ := ψ.injective
    have hψb : Function.Bijective ψ :=
      (Fintype.bijective_iff_injective_and_card ψ).2 ⟨hψi, by rw [ZMod.card, hcard]⟩
    have hbi : IsIntegral ℤ b := by
      refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), ?_, ?_⟩
      · exact Polynomial.monic_X_pow_add_C _ two_ne_zero
      · simp [Polynomial.eval₂_add, hb]
    let β : 𝓞 K := ⟨b, hbi⟩
    have hβ : β ^ 2 = -(d : 𝓞 K) := by
      apply RingOfIntegers.coe_injective
      push_cast
      exact hb
    obtain ⟨t, ht⟩ := hψb.2 (Ideal.Quotient.mk P β)
    apply hsq
    refine ⟨t, ?_⟩
    apply hψi
    rw [map_mul, ← sq, ht, ← map_pow, hβ]
    push_cast
    simp
  · rw [← hnormI] at hPk
    have hPI : P ∣ Ideal.span {(p : 𝓞 K)} := Ideal.dvd_iff_le.2 hIP
    obtain ⟨J, hJ⟩ := hPI
    have hJ1 : Ideal.absNorm J = 1 := by
      have h2 := congrArg Ideal.absNorm hJ
      rw [map_mul, hPk] at h2
      have hpos : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) ≠ 0 := by
        rw [hnormI]
        exact pow_ne_zero _ hp.ne_zero
      exact (Nat.mul_eq_left hpos).1 h2.symm
    rw [Ideal.absNorm_eq_one_iff] at hJ1
    rw [hJ, hJ1, Ideal.mul_top]
    exact hPmax.isPrime

end PI.InertPrimeWork
end

open NumberField

theorem isPrime_span_of_jacobi_neg_one : PI.InertPrime := by
  intro K _ _ hK b d p hb hp hj
  exact PI.InertPrimeWork.inert K hK b d p hb hp hj
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhSchurConv
section -- merged from Formalism.PeriodIntegrals.PhSchurConv
noncomputable section

open MeasureTheory NumberField
open scoped InnerProductSpace

namespace PI.PhSchurConv

section Defs

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsURep (ρ : G → (H →L[ℂ] H)) : Prop :=
  ρ 1 = 1 ∧ (∀ a b, ρ (a * b) = (ρ a).comp (ρ b)) ∧ (∀ g v, ‖ρ g v‖ = ‖v‖) ∧
    ∀ v, Continuous fun g => ρ g v

def IsFdegG (μ : Measure G) (σ : G → (H →L[ℂ] H)) (d : ℝ) : Prop :=
  0 < d ∧ ∀ v w v' w' : H,
    Integrable (fun g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ) μ ∧
    ∫ g, ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)

def coefM (σ : G → (H →L[ℂ] H)) (w : H) : G → ℂ := fun g => ⟪w, σ g w⟫_ℂ

def phOf (σ : G → (H →L[ℂ] H)) (w : H) (d : ℝ) : G → ℂ := fun g => (d : ℂ) * star (coefM σ w g)

def PhConv (μ : Measure G) (ph m : G → ℂ) : Prop :=
  m 1 = 1 ∧ (∀ g, ph g⁻¹ = star (ph g)) ∧
    ∀ x y : G, Integrable (fun g => ph g * ph (x⁻¹ * g⁻¹ * y)) μ ∧
      ∫ g, ph g * ph (x⁻¹ * g⁻¹ * y) ∂μ = m x * ph y

end Defs

def SchurConv : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (Hσ : Type) [NormedAddCommGroup Hσ] [InnerProductSpace ℂ Hσ]
    (σ : G → (Hσ →L[ℂ] Hσ)) (d : ℝ) (w : Hσ),
    IsURep σ → IsFdegG μ σ d → ‖w‖ = 1 →
      PhConv μ (phOf σ w d) (coefM σ w) ∧
      ∀ u u' : Hσ, Integrable (fun g => phOf σ w d g * ⟪u', σ g u⟫_ℂ) μ ∧
        ∫ g, phOf σ w d g * ⟪u', σ g u⟫_ℂ ∂μ = ⟪w, u⟫_ℂ * ⟪u', w⟫_ℂ

end PI.PhSchurConv
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurConvolution.MapMulApply
noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace PI.UnitaryGroupMassFormula.PhSchurConv.Main

open PI.PhSchurConv

theorem star_inner {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (a b : H) :
    star ⟪a, b⟫_ℂ = ⟪b, a⟫_ℂ := by
  exact inner_conj_symm b a

theorem map_mul_apply {G : Type} [Group G] [TopologicalSpace G]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : G → (H →L[ℂ] H)} (hU : IsURep σ) (a b : G) (v : H) : σ (a * b) v = σ a (σ b v) := by
  rw [hU.2.1 a b]
  rfl

theorem inner_map {G : Type} [Group G] [TopologicalSpace G]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : G → (H →L[ℂ] H)} (hU : IsURep σ) (g : G) (a b : H) : ⟪σ g a, σ g b⟫_ℂ = ⟪a, b⟫_ℂ := by
  let L : H →ₗᵢ[ℂ] H := ⟨(σ g).toLinearMap, hU.2.2.1 g⟩
  exact L.inner_map_map a b

theorem coef_inv {G : Type} [Group G] [TopologicalSpace G]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : G → (H →L[ℂ] H)} (hU : IsURep σ) (g : G) (w : H) :
    ⟪w, σ g⁻¹ w⟫_ℂ = star ⟪w, σ g w⟫_ℂ := by
  rw [star_inner, ← inner_map hU g w (σ g⁻¹ w), ← map_mul_apply hU, mul_inv_cancel, hU.1,
    ContinuousLinearMap.one_apply]

theorem coef_conv {G : Type} [Group G] [TopologicalSpace G]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : G → (H →L[ℂ] H)} (hU : IsURep σ) (g x y : G) (w : H) :
    ⟪w, σ (x⁻¹ * g⁻¹ * y) w⟫_ℂ = ⟪σ g (σ x w), σ y w⟫_ℂ := by
  have h1 : σ g (σ x w) = σ (g * x) w := (map_mul_apply hU g x w).symm
  rw [h1]
  symm
  calc ⟪σ (g * x) w, σ y w⟫_ℂ = ⟪σ (g * x)⁻¹ (σ (g * x) w), σ (g * x)⁻¹ (σ y w)⟫_ℂ := (inner_map hU _ _ _).symm
    _ = ⟪w, σ (x⁻¹ * g⁻¹ * y) w⟫_ℂ := by
      rw [← map_mul_apply hU, ← map_mul_apply hU, inv_mul_cancel, hU.1, ContinuousLinearMap.one_apply,
        mul_inv_rev]

end PI.UnitaryGroupMassFormula.PhSchurConv.Main
end
end

theorem schur_orthogonality_idempotent : PI.PhSchurConv.SchurConv := by
  open MeasureTheory in
  open scoped InnerProductSpace in
  intro G _ _ _ _ _ _ μ _ _ _ Hσ _ _ σ d w hU hF hw
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hF.1)
  have hstard : star (d : ℂ) = d := Complex.conj_ofReal d
  have hinv : (d : ℂ) * (d : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hd
  have h1 : σ 1 = 1 := hU.1
  refine ⟨?_, ?_⟩
  · unfold PI.PhSchurConv.PhConv
    refine ⟨?_, ?_, ?_⟩
    · simp only [PI.PhSchurConv.coefM]
      rw [h1, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K, hw]
      simp
    · intro g
      simp only [PI.PhSchurConv.phOf, PI.PhSchurConv.coefM]
      rw [(PI.UnitaryGroupMassFormula.PhSchurConv.Main.coef_inv hU)]
      simp only [star_mul', star_star, hstard]
      try ring
    · intro x y
      have key : ∀ g, PI.PhSchurConv.phOf σ w d g * PI.PhSchurConv.phOf σ w d (x⁻¹ * g⁻¹ * y)
          = ((d : ℂ) * d) * (⟪σ y w, σ g (σ x w)⟫_ℂ * star ⟪w, σ g w⟫_ℂ) := by
        intro g
        simp only [PI.PhSchurConv.phOf, PI.PhSchurConv.coefM]
        rw [(PI.UnitaryGroupMassFormula.PhSchurConv.Main.coef_conv hU), PI.UnitaryGroupMassFormula.PhSchurConv.Main.star_inner (σ g (σ x w)) (σ y w)]
        ring
      obtain ⟨hi, he⟩ := hF.2 (σ x w) (σ y w) w w
      simp_rw [key]
      refine ⟨hi.const_mul _, ?_⟩
      rw [integral_const_mul, he]
      simp only [PI.PhSchurConv.phOf, PI.PhSchurConv.coefM]
      rw [PI.UnitaryGroupMassFormula.PhSchurConv.Main.star_inner w (σ y w), div_eq_mul_inv]
      linear_combination (⟪w, σ x w⟫_ℂ * ⟪σ y w, w⟫_ℂ * d) * hinv
  · intro u u'
    have key : ∀ g, PI.PhSchurConv.phOf σ w d g * ⟪u', σ g u⟫_ℂ
        = (d : ℂ) * (⟪u', σ g u⟫_ℂ * star ⟪w, σ g w⟫_ℂ) := by
      intro g
      simp only [PI.PhSchurConv.phOf, PI.PhSchurConv.coefM]
      ring
    obtain ⟨hi, he⟩ := hF.2 u u' w w
    simp_rw [key]
    refine ⟨hi.const_mul _, ?_⟩
    rw [integral_const_mul, he, div_eq_mul_inv]
    linear_combination (⟪w, u⟫_ℂ * ⟪u', w⟫_ℂ) * hinv
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotNuSigma
section -- merged from Formalism.PeriodIntegrals.QuotNuSigma
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PI.QuotNuSigma

def Target : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μG : Measure G) [IsFiniteMeasureOnCompacts μG] (A B : Set G) (μA μB ν : Measure G),
    (SigmaFinite μA ∧ μA ≠ 0 ∧ μA Aᶜ = 0 ∧ ∀ s ∈ A, μA.map (fun x => s * x) = μA) →
    (SigmaFinite μB ∧ μB ≠ 0 ∧ μB Bᶜ = 0 ∧ ∀ s ∈ B, μB.map (fun x => s * x) = μB) →
    (∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (s * x) ∂((μA.prod μB).map (fun p => p.1 * p.2))) ∂ν) →
    SigmaFinite ν

end PI.QuotNuSigma
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientSigmaFiniteness.SigmaFiniteOfWeil
noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise

namespace PI.UnitaryGroupMassFormula.QuotNuSigma

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem pos_open_one (A : Set G) (μA : Measure G) (h0 : μA ≠ 0) (hc : μA Aᶜ = 0)
    (hinv : ∀ s ∈ A, μA.map (fun x => s * x) = μA) (U : Set G) (hU : IsOpen U) (h1 : (1 : G) ∈ U) :
    0 < μA U := by
  by_contra hpos
  have hU0 : μA U = 0 := nonpos_iff_eq_zero.1 (not_lt.1 hpos)
  let F : A → Set G := fun s => (fun x => (s : G)⁻¹ * x) ⁻¹' U
  have hFo : ∀ s, IsOpen (F s) := fun s => hU.preimage (continuous_const.mul continuous_id)
  have hF0 : ∀ s, μA (F s) = 0 := by
    intro s
    have hm := congrArg (fun m : Measure G => m (F s)) (hinv s s.2)
    rw [← hm, Measure.map_apply (measurable_const_mul _) (hFo s).measurableSet]
    have hpre : (fun x => (s : G) * x) ⁻¹' F s = U := by
      ext x
      simp [F]
    rw [hpre, hU0]
  obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable F hFo
  have hcov : A ⊆ ⋃ s ∈ T, F s := by
    intro a ha
    rw [hTU]
    exact Set.mem_iUnion.2 ⟨⟨a, ha⟩, by simp [F, h1]⟩
  have hnull : μA (⋃ s ∈ T, F s) = 0 := (measure_biUnion_null_iff hT).2 fun s _ => hF0 s
  have huniv : μA Set.univ = 0 := by
    refine measure_mono_null (fun x _ => ?_) (measure_union_null hnull hc)
    by_cases hx : x ∈ A
    · exact Or.inl (hcov hx)
    · exact Or.inr hx
  exact h0 (Measure.measure_univ_eq_zero.1 huniv)

theorem pos_open_one_mul (A B : Set G) (μA μB : Measure G) [SigmaFinite μB]
    (hA0 : μA ≠ 0) (hAc : μA Aᶜ = 0) (hAi : ∀ s ∈ A, μA.map (fun x => s * x) = μA)
    (hB0 : μB ≠ 0) (hBc : μB Bᶜ = 0) (hBi : ∀ s ∈ B, μB.map (fun x => s * x) = μB)
    (U : Set G) (hU : IsOpen U) (h1 : (1 : G) ∈ U) :
    0 < ((μA.prod μB).map (fun p : G × G => p.1 * p.2)) U := by
  obtain ⟨V, hVo, hV1, hVV⟩ := exists_open_nhds_one_mul_subset (hU.mem_nhds h1)
  have hApos := pos_open_one A μA hA0 hAc hAi V hVo hV1
  have hBpos := pos_open_one B μB hB0 hBc hBi V hVo hV1
  have hsub : V ×ˢ V ⊆ (fun p : G × G => p.1 * p.2) ⁻¹' U := fun p hp =>
    hVV (Set.mul_mem_mul hp.1 hp.2)
  calc (0 : ℝ≥0∞) < μA V * μB V := ENNReal.mul_pos hApos.ne' hBpos.ne'
    _ = (μA.prod μB) (V ×ˢ V) := (Measure.prod_prod V V).symm
    _ ≤ (μA.prod μB) ((fun p : G × G => p.1 * p.2) ⁻¹' U) := measure_mono hsub
    _ ≤ _ := Measure.le_map_apply measurable_mul.aemeasurable U

theorem sigmaFinite_of_weil [LocallyCompactSpace G] [T2Space G]
    (μG : Measure G) [IsFiniteMeasureOnCompacts μG] (A B : Set G) (μA μB ν : Measure G)
    (hA : SigmaFinite μA ∧ μA ≠ 0 ∧ μA Aᶜ = 0 ∧ ∀ s ∈ A, μA.map (fun x => s * x) = μA)
    (hB : SigmaFinite μB ∧ μB ≠ 0 ∧ μB Bᶜ = 0 ∧ ∀ s ∈ B, μB.map (fun x => s * x) = μB)
    (hW : ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (s * x) ∂((μA.prod μB).map (fun p => p.1 * p.2))) ∂ν) :
    SigmaFinite ν := by
  obtain ⟨hAσ, hA0, hAc, hAi⟩ := hA
  obtain ⟨hBσ, hB0, hBc, hBi⟩ := hB
  have := hAσ
  have := hBσ
  set ρ := (μA.prod μB).map (fun p : G × G => p.1 * p.2) with hρ
  have hK : ∀ x : G, ∃ K, IsCompact K ∧ K ∈ nhds x := fun x => exists_compact_mem_nhds x
  choose K hKc hKn using hK
  have hmeasK : ∀ x, MeasurableSet (K x) := fun x => (hKc x).isClosed.measurableSet
  let h : G → G → ℝ≥0∞ := fun x y => ∫⁻ s, (K x).indicator 1 (s * y) ∂ρ
  have hhm : ∀ x, Measurable (h x) := by
    intro x
    have hq : Measurable fun q : G × G => (K x).indicator (1 : G → ℝ≥0∞) (q.2 * q.1) :=
      (measurable_one.indicator (hmeasK x)).comp (measurable_snd.mul measurable_fst)
    exact hq.lintegral_prod_right'
  have hint : ∀ x, ∫⁻ y, h x y ∂ν = μG (K x) := by
    intro x
    show ∫⁻ y, ∫⁻ s, (K x).indicator 1 (s * y) ∂ρ ∂ν = μG (K x)
    rw [← hW _ (measurable_one.indicator (hmeasK x)), lintegral_indicator_one (hmeasK x)]
  have hpos : ∀ x y, y ∈ interior (K x) → 0 < h x y := by
    intro x y hy
    let O := (fun s : G => s * y) ⁻¹' interior (K x)
    have hOo : IsOpen O := isOpen_interior.preimage (continuous_id.mul continuous_const)
    have hO1 : (1 : G) ∈ O := by simp [O, hy]
    have hρO : 0 < ρ O := pos_open_one_mul A B μA μB hA0 hAc hAi hB0 hBc hBi O hOo hO1
    have hle : ∫⁻ s, O.indicator 1 s ∂ρ ≤ ∫⁻ s, (K x).indicator 1 (s * y) ∂ρ := by
      refine lintegral_mono fun s => ?_
      by_cases hs : s ∈ O
      · have hs' : s * y ∈ K x := interior_subset hs
        simp [Set.indicator_of_mem hs, Set.indicator_of_mem hs']
      · simp [hs]
    rw [lintegral_indicator_one hOo.measurableSet] at hle
    exact lt_of_lt_of_le hρO hle
  obtain ⟨T, hT, hTU⟩ :=
    TopologicalSpace.isOpen_iUnion_countable (fun x => interior (K x)) (fun _ => isOpen_interior)
  have := hT.to_subtype
  let E : T × ℕ → Set G := fun p => {y | ((p.2 : ℝ≥0∞) + 1)⁻¹ ≤ h p.1 y}
  refine Measure.sigmaFinite_of_countable (S := Set.range E) (Set.countable_range E) ?_ ?_
  · rintro _ ⟨⟨x, n⟩, rfl⟩
    have hne0 : ((n : ℝ≥0∞) + 1)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (by simp)
    have hneT : ((n : ℝ≥0∞) + 1)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (by simp)
    calc ν (E (x, n)) ≤ (∫⁻ y, h x y ∂ν) / ((n : ℝ≥0∞) + 1)⁻¹ :=
          meas_ge_le_lintegral_div (hhm x).aemeasurable hne0 hneT
      _ < ⊤ := by
        rw [hint]
        exact ENNReal.div_lt_top (hKc x).measure_lt_top.ne hne0
  · refine Set.eq_univ_of_forall fun y => ?_
    have hy : y ∈ ⋃ x ∈ T, interior (K x) := by
      rw [hTU]
      exact Set.mem_iUnion.2 ⟨y, mem_interior_iff_mem_nhds.2 (hKn y)⟩
    obtain ⟨x, hxT, hyx⟩ := Set.mem_iUnion₂.1 hy
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (hpos x y hyx).ne'
    refine Set.mem_sUnion.2 ⟨E (⟨x, hxT⟩, n), ⟨_, rfl⟩, ?_⟩
    show ((n : ℝ≥0∞) + 1)⁻¹ ≤ h x y
    exact le_trans (ENNReal.inv_le_inv.2 le_self_add) hn.le

end PI.UnitaryGroupMassFormula.QuotNuSigma
end
end

theorem quotient_sigma_finite : PI.QuotNuSigma.Target :=
  fun _ _ _ _ _ _ _ _ _ μG _ A B μA μB ν hA hB hW =>
    PI.UnitaryGroupMassFormula.QuotNuSigma.sigmaFinite_of_weil μG A B μA μB ν hA hB hW
end
