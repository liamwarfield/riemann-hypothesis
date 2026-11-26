module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegersCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormPowSubPowLe
namespace GlobalTheory.NormEvalSubBound

open Polynomial

section
variable {C : Type} [NormedField C] [IsUltrametricDist C]

lemma norm_pow_sub_pow_le {y a : C} (hy : ‖y‖ ≤ 1) (ha : ‖a‖ ≤ 1) (i : ℕ) :
    ‖y ^ i - a ^ i‖ ≤ ‖y - a‖ := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : y ^ (i + 1) - a ^ (i + 1) = y * (y ^ i - a ^ i) + (y - a) * a ^ i := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖y‖ * ‖y ^ i - a ^ i‖ ≤ 1 * ‖y - a‖ :=
            mul_le_mul hy ih (norm_nonneg _) zero_le_one
        _ = ‖y - a‖ := one_mul _
    · rw [norm_mul, norm_pow]
      calc ‖y - a‖ * ‖a‖ ^ i ≤ ‖y - a‖ * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) ha) (norm_nonneg _)
        _ = ‖y - a‖ := mul_one _

lemma norm_eval_sub_le (Q : C[X]) (hc : ∀ i, ‖Q.coeff i‖ ≤ 1) {y a : C} (hy : ‖y‖ ≤ 1)
    (ha : ‖a‖ ≤ 1) : ‖Q.eval y - Q.eval a‖ ≤ ‖y - a‖ := by
  rw [eval_eq_sum_range, eval_eq_sum_range, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
  rw [← mul_sub, norm_mul]
  calc ‖Q.coeff i‖ * ‖y ^ i - a ^ i‖ ≤ 1 * ‖y - a‖ :=
        mul_le_mul (hc i) (norm_pow_sub_pow_le hy ha i) (norm_nonneg _) zero_le_one
    _ = ‖y - a‖ := one_mul _

lemma norm_le_one_of_root (Q : C[X]) (hm : Q.Monic) (hc : ∀ i, ‖Q.coeff i‖ ≤ 1) {a : C}
    (h : Q.eval a = 0) : ‖a‖ ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  set n := Q.natDegree
  have hpos : 0 < ‖a‖ := lt_trans zero_lt_one hlt
  have hs : ‖∑ i ∈ Finset.range n, Q.coeff i * a ^ i‖ ≤ ‖a‖ ^ n / ‖a‖ := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    have hi' : i + 1 ≤ n := Finset.mem_range.mp hi
    rw [norm_mul, norm_pow, le_div_iff₀ hpos]
    calc ‖Q.coeff i‖ * ‖a‖ ^ i * ‖a‖ ≤ 1 * ‖a‖ ^ i * ‖a‖ := by
          gcongr
          exact hc i
      _ = ‖a‖ ^ (i + 1) := by ring
      _ ≤ ‖a‖ ^ n := pow_le_pow_right₀ hlt.le hi'
  have hlt2 : ‖a‖ ^ n / ‖a‖ < ‖a‖ ^ n := div_lt_self (by positivity) hlt
  have he : Q.eval a = a ^ n + ∑ i ∈ Finset.range n, Q.coeff i * a ^ i := by
    conv_lhs => rw [hm.as_sum]
    simp [eval_finsetSum, n]
  rw [h] at he
  have : a ^ n = -∑ i ∈ Finset.range n, Q.coeff i * a ^ i := by linear_combination -he
  have h3 : ‖a‖ ^ n = ‖∑ i ∈ Finset.range n, Q.coeff i * a ^ i‖ := by
    rw [← norm_pow, this, norm_neg]
  linarith
end

theorem main_theorem : (let d1 : {C : Type} → [inst : NormedField C] → [IsUltrametricDist C] → Subfield C → Subring C := @(fun {C : Type} [NormedField C] [IsUltrametricDist C] (F : Subfield C) ↦ Subfield.toSubring F ⊓ Valuation.integer NormedField.valuation); ∀ {C : Type} [inst : NormedField C] [inst_1 : IsUltrametricDist C] {F : Subfield C} [IsAlgClosed C] [inst_3 : IsLocalRing ↥(d1 F)], (∀ (x : C), ‖x‖ ≤ (1 : ℝ) → ∃ y ∈ F, ‖x - y‖ < (1 : ℝ)) → IsAlgClosed (IsLocalRing.ResidueField ↥(d1 F))) := by
  intro d1 C _ _ F _ _ hdense
  have mem : ∀ x : C, x ∈ d1 F ↔ x ∈ F ∧ ‖x‖ ≤ 1 := by
    intro x
    simp only [d1, Subring.mem_inf, Subfield.mem_toSubring, Valuation.mem_integer_iff,
      NormedField.valuation_apply]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by exact_mod_cast h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by exact_mod_cast h2⟩
  apply IsAlgClosed.of_exists_root
  intro p hmon hirr
  have hlift : p ∈ lifts (IsLocalRing.residue (d1 F)) :=
    (mem_lifts p).mpr (Polynomial.map_surjective _ IsLocalRing.residue_surjective p)
  obtain ⟨q, hqmap, hqdeg, hqmon⟩ := lifts_and_degree_eq_and_monic hlift hmon
  set Q : C[X] := q.map (d1 F).subtype with hQ
  have hQc : ∀ i, ‖Q.coeff i‖ ≤ 1 := fun i => by
    rw [hQ, coeff_map]; exact ((mem _).mp (q.coeff i).2).2
  have hQm : Q.Monic := hqmon.map _
  have hQdeg : Q.degree ≠ 0 := by
    rw [hQ, degree_map_eq_of_injective (Subring.subtype_injective _), hqdeg]
    exact (degree_pos_of_irreducible hirr).ne'
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root Q hQdeg
  have ha1 : ‖a‖ ≤ 1 := norm_le_one_of_root Q hQm hQc ha
  obtain ⟨y, hyF, hya⟩ := hdense a ha1
  have hy1 : ‖y‖ ≤ 1 := by
    have : y = a - (a - y) := by ring
    rw [this]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha1 ?_)
    rw [norm_neg]; exact hya.le
  let y' : d1 F := ⟨y, (mem y).mpr ⟨hyF, hy1⟩⟩
  refine ⟨IsLocalRing.residue _ y', ?_⟩
  rw [← hqmap, eval_map, eval₂_hom, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hval : ((q.eval y' : d1 F) : C) = Q.eval y := by
    rw [hQ, eval_map]
    exact (eval₂_hom (d1 F).subtype y').symm
  have hn : ‖((q.eval y' : d1 F) : C)‖ < 1 := by
    rw [hval]
    have : Q.eval y = Q.eval y - Q.eval a := by rw [IsRoot.def.mp ha, sub_zero]
    rw [this]
    refine lt_of_le_of_lt (norm_eval_sub_le Q hQc hy1 ha1) ?_
    rwa [norm_sub_rev]
  obtain ⟨v, huv⟩ := hu.exists_right_inv
  have h1 : ((q.eval y' : d1 F) : C) * (v : C) = 1 := by
    have := congrArg Subtype.val huv
    simpa using this
  have hv : ‖(v : C)‖ ≤ 1 := ((mem _).mp v.2).2
  have : ‖((q.eval y' : d1 F) : C) * (v : C)‖ < 1 := by
    rw [norm_mul]
    calc _ ≤ ‖((q.eval y' : d1 F) : C)‖ * 1 := mul_le_mul_of_nonneg_left hv (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hn
  rw [h1, norm_one] at this
  exact lt_irrefl _ this

end GlobalTheory.NormEvalSubBound
end

open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

noncomputable section

namespace GlobalTheory.BigInt

section General

variable {C : Type} [NormedField C] [IsUltrametricDist C]

theorem norm_le_one_of_root {R : Type} [CommRing R] (f : R →+* C) (hf : ∀ r, ‖f r‖ ≤ 1) {q : R[X]}
    (hq : q.Monic) {x : C} (hx : q.eval₂ f x = 0) : ‖x‖ ≤ 1 := by
  let v := NormedField.valuation (K := C)
  let g : R →+* v.integer := f.codRestrict v.integer fun r => hf r
  have hint : IsIntegral v.integer x := by
    refine ⟨q.map g, hq.map g, ?_⟩
    rw [eval₂_map]
    exact hx
  exact (Valuation.integer.integers v).mem_of_integral hint

def ints (F : Subfield C) : Subring C := F.toSubring ⊓ (NormedField.valuation (K := C)).integer

theorem mem_ints {F : Subfield C} {x : C} : x ∈ ints F ↔ x ∈ F ∧ ‖x‖ ≤ 1 := Iff.rfl

variable {F : Subfield C}

theorem div_mem_ints {x y : C} (hx : x ∈ F) (hy : y ∈ F) (h : ‖x‖ ≤ ‖y‖) : x / y ∈ ints F :=
  mem_ints.2 ⟨div_mem hx hy, by rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)⟩

theorem dvd_iff {x y : ints F} : y ∣ x ↔ ‖(x : C)‖ ≤ ‖(y : C)‖ := by
  constructor
  · rintro ⟨z, rfl⟩
    rw [Subring.coe_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (mem_ints.1 z.2).2
  · intro h
    by_cases hy : (y : C) = 0
    · have : x = 0 := Subtype.ext (by simpa [hy] using h)
      rw [this]; exact dvd_zero _
    · refine ⟨⟨x / y, div_mem_ints (mem_ints.1 x.2).1 (mem_ints.1 y.2).1 h⟩, Subtype.ext ?_⟩
      simp only [Subring.coe_mul]
      field_simp

theorem not_isUnit_iff {x : ints F} : ¬ IsUnit x ↔ ‖(x : C)‖ < 1 := by
  rw [isUnit_iff_dvd_one, dvd_iff]; simp

variable {π : ints F} (h0 : (π : C) ≠ 0) (h1 : ‖(π : C)‖ < 1)
  (hπ : ∀ y ∈ F, ‖y‖ < 1 → ‖y‖ ≤ ‖(π : C)‖)

include h0 h1 hπ

theorem irreducible_unif : Irreducible π := by
  refine ⟨not_isUnit_iff.2 h1, fun a b hab => ?_⟩
  by_contra hc
  rw [not_or, not_isUnit_iff, not_isUnit_iff] at hc
  have ha := hπ a (mem_ints.1 a.2).1 hc.1
  have e : ‖(π : C)‖ = ‖(a : C)‖ * ‖(b : C)‖ := by rw [hab, Subring.coe_mul, norm_mul]
  have hp := norm_pos_iff.2 h0
  have := hc.2
  have hb := norm_nonneg (b : C)
  nlinarith

theorem isDVR : IsDiscreteValuationRing (ints F) := by
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨π, irreducible_unif h0 h1 hπ, fun {x} hx => ?_⟩
  have hx0 : 0 < ‖(x : C)‖ := norm_pos_iff.2 fun h => hx (Subtype.ext h)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hx0 h1
  have key : ∀ N : ℕ, ∀ x : ints F, ‖(π : C)‖ ^ N < ‖(x : C)‖ → ∃ n, Associated (π ^ n) x := by
    intro N
    induction N with
    | zero => intro x hx; exact absurd (mem_ints.1 x.2).2 (by simpa using hx)
    | succ N ih =>
      intro x hx
      by_cases hu : IsUnit x
      · exact ⟨0, by rw [pow_zero]; exact associated_one_iff_isUnit.2 hu |>.symm⟩
      · obtain ⟨z, rfl⟩ := dvd_iff.2 (hπ x (mem_ints.1 x.2).1 (not_isUnit_iff.1 hu))
        rw [Subring.coe_mul, norm_mul, pow_succ'] at hx
        obtain ⟨n, hn⟩ := ih z (lt_of_mul_lt_mul_left hx (norm_nonneg _))
        exact ⟨n + 1, by rw [pow_succ']; exact hn.mul_left π⟩
  exact key N x hN

theorem mem_pow_iff [IsDiscreteValuationRing (ints F)] (n : ℕ) (x : ints F) :
    x ∈ IsLocalRing.maximalIdeal (ints F) ^ n ↔ ‖(x : C)‖ ≤ ‖(π : C)‖ ^ n := by
  rw [(irreducible_unif h0 h1 hπ).maximalIdeal_eq, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, dvd_iff, SubmonoidClass.coe_pow, norm_pow]

theorem isAdic [IsDiscreteValuationRing (ints F)] : IsAdic (IsLocalRing.maximalIdeal (ints F)) := by
  have hs : ∀ n : ℕ, ((IsLocalRing.maximalIdeal (ints F) ^ n : Ideal (ints F)) : Set (ints F)) =
      Metric.closedBall 0 (‖(π : C)‖ ^ n) := fun n => by
    ext x
    rw [SetLike.mem_coe, mem_pow_iff h0 h1 hπ, mem_closedBall_zero_iff]
    rfl
  rw [isAdic_iff]
  refine ⟨fun n => ?_, fun s hs' => ?_⟩
  · rw [hs]
    exact IsUltrametricDist.isOpen_closedBall _ (pow_pos (norm_pos_iff.2 h0) n).ne'
  · obtain ⟨ε, hε, h⟩ := Metric.mem_nhds_iff.1 hs'
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε h1
    exact ⟨n, by rw [hs]; exact (Metric.closedBall_subset_ball hn).trans h⟩

omit h0 h1 hπ

theorem isAlgClosed_res [IsAlgClosed C] [IsLocalRing (ints F)]
    (hF : ∀ x : C, ‖x‖ ≤ 1 → ∃ y ∈ F, ‖x - y‖ < 1) :
    IsAlgClosed (IsLocalRing.ResidueField (ints F)) := by
  first
  | (rename_i h_1 h_2 h_4 h_5; revert C h_1 h_2 F h_4 h_5 hF; exact @_root_.GlobalTheory.NormEvalSubBound.main_theorem)
  | exact @_root_.GlobalTheory.NormEvalSubBound.main_theorem
  | exact _root_.GlobalTheory.NormEvalSubBound.main_theorem
  | (apply _root_.GlobalTheory.NormEvalSubBound.main_theorem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormEvalSubBound.main_theorem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormEvalSubBound.main_theorem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormEvalSubBound.main_theorem ..)

theorem coe_ints_closure :
    (ints F.topologicalClosure : Set C) = closure {x | x ∈ F ∧ ‖x‖ ≤ 1} := by
  have hc : IsClopen (Metric.closedBall (0 : C) 1) :=
    IsUltrametricDist.isClopen_closedBall _ one_ne_zero
  have e : {x | x ∈ F ∧ ‖x‖ ≤ 1} = (F : Set C) ∩ Metric.closedBall (0 : C) 1 := by
    ext x; simp
  rw [e]
  apply Set.Subset.antisymm
  · intro x hx
    exact hc.isOpen.closure_inter ⟨(mem_ints.1 hx).1, by simpa using (mem_ints.1 hx).2⟩
  · intro x hx
    have := closure_inter_subset_inter_closure _ _ hx
    rw [hc.isClosed.closure_eq] at this
    exact mem_ints.2 ⟨this.1, by simpa using this.2⟩

end General

variable {l : ℕ} [Fact l.Prime]

open Loc

theorem exists_pow_norm (LL : FinExt l) :
    ∃ d : ℕ, 0 < d ∧ ∀ y ∈ LL.1 ⊔ MaximalUnramifiedExtension l, y ≠ 0 → ∃ n : ℤ, ‖y‖ ^ d = (l : ℝ) ^ n := by
  haveI := LL.2
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ_[l] ↥LL.1
  have hLL : IntermediateField.adjoin ℚ_[l] {(α : Om l)} = LL.1 := by
    have := congrArg (IntermediateField.map LL.1.val) hα
    rw [IntermediateField.adjoin_map, Set.image_singleton] at this
    rw [show (α : Om l) = LL.1.val α from rfl, this]
    ext x
    simp
  let E : IntermediateField ↥(MaximalUnramifiedExtension l) (Om l) := IntermediateField.adjoin ↥(MaximalUnramifiedExtension l) {(α : Om l)}
  have hE : E.restrictScalars ℚ_[l] = LL.1 ⊔ MaximalUnramifiedExtension l := by
    rw [IntermediateField.restrictScalars_adjoin_eq_sup, hLL, sup_comm]
  haveI : FiniteDimensional ↥(MaximalUnramifiedExtension l) ↥E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
  refine ⟨Module.finrank ↥(MaximalUnramifiedExtension l) ↥E, Module.finrank_pos, fun y hy hy0 => ?_⟩
  rw [← hE] at hy
  let y' : ↥E := ⟨y, hy⟩
  have h := Algebra.norm_eq_prod_embeddings ↥(MaximalUnramifiedExtension l) (Om l) y'
  have hn : ∀ σ : ↥E →ₐ[↥(MaximalUnramifiedExtension l)] Om l, ‖σ y'‖ = ‖y‖ := fun σ => by
    have h1 := minpoly.algHom_eq (σ.restrictScalars ℚ_[l]) σ.injective y'
    have h2 := minpoly.algHom_eq (E.val.restrictScalars ℚ_[l]) E.val.injective y'
    rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
    unfold spectralNorm
    exact congrArg spectralValue (h1.trans h2.symm)
  have h3 := congrArg norm h
  rw [norm_prod, Finset.prod_congr rfl fun σ _ => hn σ, Finset.prod_const, Finset.card_univ,
    AlgHom.card] at h3
  rw [← h3]
  refine GlobalTheory.UnramValue.norm_of_mem_Kur (Algebra.norm ↥(MaximalUnramifiedExtension l) y').2 ?_
  rw [← norm_ne_zero_iff]
  change ‖algebraMap ↥(MaximalUnramifiedExtension l) (Om l) (Algebra.norm ↥(MaximalUnramifiedExtension l) y')‖ ≠ 0
  rw [h3]
  exact pow_ne_zero _ (norm_ne_zero_iff.2 hy0)

theorem exists_unif (LL : FinExt l) :
    ∃ π ∈ LL.1 ⊔ MaximalUnramifiedExtension l, π ≠ 0 ∧ ‖π‖ < 1 ∧ ∀ y ∈ LL.1 ⊔ MaximalUnramifiedExtension l, ‖y‖ < 1 → ‖y‖ ≤ ‖π‖ := by
  classical
  have hp : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  obtain ⟨d, hd, H⟩ := exists_pow_norm LL
  have key : ∀ y ∈ LL.1 ⊔ MaximalUnramifiedExtension l, y ≠ 0 → ‖y‖ < 1 → ∃ k : ℕ, ‖y‖ ^ d = ((l : ℝ)⁻¹) ^ k := by
    intro y hy h0 h1
    obtain ⟨n, hn⟩ := H y hy h0
    have h2 : (l : ℝ) ^ n < 1 := by rw [← hn]; exact pow_lt_one₀ (norm_nonneg _) h1 hd.ne'
    rw [zpow_lt_one_iff_right₀ hl1] at h2
    obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat h2.le
    exact ⟨k, by rw [hn, zpow_neg, zpow_natCast, inv_pow]⟩
  have hex : ∃ k : ℕ, ∃ y ∈ LL.1 ⊔ MaximalUnramifiedExtension l, y ≠ 0 ∧ ‖y‖ < 1 ∧ ‖y‖ ^ d = ((l : ℝ)⁻¹) ^ k :=
    ⟨d, l, natCast_mem _ _, Nat.cast_ne_zero.2 hp.ne_zero, by
      rw [GlobalTheory.UnramValue.norm_l]; exact inv_lt_one_of_one_lt₀ hl1, by rw [GlobalTheory.UnramValue.norm_l]⟩
  obtain ⟨π, hπ, h0, h1, e⟩ := Nat.find_spec hex
  refine ⟨π, hπ, h0, h1, fun y hy hy1 => ?_⟩
  by_cases hy0 : y = 0
  · simp [hy0]
  obtain ⟨k, hk⟩ := key y hy hy0 hy1
  have hle : Nat.find hex ≤ k := Nat.find_min' hex ⟨y, hy, hy0, hy1, hk⟩
  refine le_of_pow_le_pow_left₀ hd.ne' (norm_nonneg _) ?_
  rw [hk, e]
  exact pow_le_pow_of_le_one (by positivity) (inv_lt_one_of_one_lt₀ hl1).le hle

def img (LL : FinExt l) : Subfield ℂ_[l] :=
  (LL.1 ⊔ MaximalUnramifiedExtension l).toSubfield.map (algebraMap (Om l) ℂ_[l])

theorem mem_img {LL : FinExt l} {x : ℂ_[l]} :
    x ∈ img LL ↔ ∃ y ∈ LL.1 ⊔ MaximalUnramifiedExtension l, (y : ℂ_[l]) = x := Iff.rfl

theorem exists_integers_completion : ∀ (l : ℕ) [Fact l.Prime] (LL : Loc.FinExt l), ∃ (O : Subring ℂ_[l]) (_ : IsDiscreteValuationRing ↥O), (∀ x : ↥(Loc.OL LL), (((x : ↥LL.1) : Loc.Om l) : ℂ_[l]) ∈ O) ∧ (∀ x ∈ O, ‖x‖ ≤ 1) ∧ (∀ x ∈ O, ∀ y ∈ O, ‖x‖ ≤ ‖y‖ → x / y ∈ O) ∧ IsAlgClosed (IsLocalRing.ResidueField ↥O) ∧ IsAdicComplete (IsLocalRing.maximalIdeal ↥O) ↥O ∧ IsAdic (IsLocalRing.maximalIdeal ↥O) ∧ (O : Set ℂ_[l]) = closure ((fun y : Loc.Om l => (y : ℂ_[l])) '' {y | y ∈ LL.1 ⊔ Loc.MaximalUnramifiedExtension l ∧ ‖y‖ ≤ 1}) := by
  intro l _ LL
  let F : Subfield ℂ_[l] := (img LL).topologicalClosure
  have hle : ∀ y ∈ LL.1 ⊔ MaximalUnramifiedExtension l, (y : ℂ_[l]) ∈ F := fun y hy =>
    (img LL).le_topologicalClosure (mem_img.2 ⟨y, hy, rfl⟩)
  obtain ⟨π, hπ, h0, h1, hmax⟩ := exists_unif LL
  have h1' : ‖(π : ℂ_[l])‖ < 1 := by rwa [PadicComplex.norm_extends]
  let π' : ints F := ⟨π, mem_ints.2 ⟨hle π hπ, h1'.le⟩⟩
  have h0' : (π' : ℂ_[l]) ≠ 0 := by
    rw [← norm_ne_zero_iff]
    change ‖(π : ℂ_[l])‖ ≠ 0
    rwa [PadicComplex.norm_extends, norm_ne_zero_iff]
  have hmax' : ∀ y ∈ F, ‖y‖ < 1 → ‖y‖ ≤ ‖(π' : ℂ_[l])‖ := by
    intro y hy hy1
    have hc : IsClosed {y : ℂ_[l] | ‖y‖ ≤ ‖(π : ℂ_[l])‖ ∨ 1 ≤ ‖y‖} :=
      (isClosed_le continuous_norm continuous_const).union
        (isClosed_le continuous_const continuous_norm)
    have := closure_minimal (s := (img LL : Set ℂ_[l])) (by
      rintro _ ⟨z, hz, rfl⟩
      change ‖(z : ℂ_[l])‖ ≤ ‖(π : ℂ_[l])‖ ∨ 1 ≤ ‖(z : ℂ_[l])‖
      simp only [PadicComplex.norm_extends]
      rcases lt_or_ge ‖z‖ 1 with h | h
      · exact Or.inl (hmax z hz h)
      · exact Or.inr h) hc hy
    exact this.resolve_right (not_le.2 hy1)
  haveI hdvr : IsDiscreteValuationRing (ints F) := isDVR (π := π') h0' h1' hmax'
  have had := isAdic (π := π') h0' h1' hmax'
  refine ⟨ints F, hdvr, fun x => mem_ints.2 ⟨hle _ (le_sup_left (a := LL.1) x.1.2), ?_⟩,
    fun x hx => (mem_ints.1 hx).2,
    fun x hx y hy h => div_mem_ints (mem_ints.1 hx).1 (mem_ints.1 hy).1 h,
    isAlgClosed_res fun x hx => ?_, ?_, had, ?_⟩
  · rw [PadicComplex.norm_extends]
    have hint : IsIntegral ℤ_[l] ((x : ↥LL.1) : Om l) :=
      (show IsIntegral ℤ_[l] (x : ↥LL.1) from x.2).map (LL.1.val.restrictScalars ℤ_[l])
    obtain ⟨q, hq, hx⟩ := hint
    exact norm_le_one_of_root _ (fun r => by
      rw [GlobalTheory.UnramValue.norm_algebraMap_int]; exact r.norm_le_one) hq hx
  · rcases hx.lt_or_eq with h | h
    · exact ⟨0, zero_mem _, by simpa using h⟩
    obtain ⟨y, hy⟩ := (UniformSpace.Completion.denseRange_coe (α := Om l)).exists_dist_lt x one_pos
    rw [dist_eq_norm] at hy
    have hy1 : ‖y‖ = 1 := by
      have e : (y : ℂ_[l]) = x + -(x - y) := by ring
      rw [← PadicComplex.norm_extends, e,
        IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg, h]; exact hy.ne'),
        norm_neg, h, max_eq_left hy.le]
    obtain ⟨ζ, m, hm, hlm, hζ, hn⟩ := GlobalTheory.MemLoc.FrobLaws.exists_root y hy1
    have hK : ζ ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, hζ⟩
    refine ⟨ζ, hle ζ (le_sup_right (a := LL.1) hK), ?_⟩
    have e : x - (ζ : ℂ_[l]) = (x - y) + ((y - ζ : Om l) : ℂ_[l]) := by
      rw [UniformSpace.Completion.coe_sub]; ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hy ?_)
    rwa [PadicComplex.norm_extends]
  · refine had.isAdicComplete_iff.2 ⟨?_, inferInstance⟩
    have : IsClosed (ints F : Set ℂ_[l]) := by rw [coe_ints_closure]; exact isClosed_closure
    exact this.completeSpace_coe
  · rw [coe_ints_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, h⟩
      exact ⟨y, ⟨hy, by rw [← PadicComplex.norm_extends]; exact h⟩, rfl⟩
    · rintro ⟨y, ⟨hy, h⟩, rfl⟩
      exact ⟨mem_img.2 ⟨y, hy, rfl⟩, by simpa using h⟩

end GlobalTheory.BigInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosureAdjoinUnitBallCoeffBound
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosureAdjoinUnitBallCoeffBound
open Polynomial

namespace GlobalTheory

theorem closure_adjoin_unitBall_coeff_bound : ∀ (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (PadicAlgCl l)) (ζ : PadicAlgCl l), IsIntegral ℚ_[l] ζ → ∃ (n : ℕ) (C : ℝ), ∀ x ∈ closure (algebraMap (PadicAlgCl l) ℂ_[l] '' ((F ⊔ IntermediateField.adjoin ℚ_[l] {ζ} : IntermediateField ℚ_[l] (PadicAlgCl l)) : Set (PadicAlgCl l))), ‖x‖ ≤ 1 → ∃ c : Fin n → ℂ_[l], (∀ i, c i ∈ closure (algebraMap (PadicAlgCl l) ℂ_[l] '' (F : Set (PadicAlgCl l))) ∧ ‖c i‖ ≤ C) ∧ x = ∑ i, c i * (algebraMap (PadicAlgCl l) ℂ_[l] ζ) ^ (i : ℕ) := by
  intro l _ F ζ hζ
  set ι := algebraMap (PadicAlgCl l) ℂ_[l] with hι
  let F0 : Subfield ℂ_[l] := (F.toSubfield.map ι).topologicalClosure
  have hF0 : (F0 : Set ℂ_[l]) = closure (ι '' (F : Set (PadicAlgCl l))) := rfl
  have hmemF : ∀ y ∈ F, ι y ∈ F0 := fun y hy =>
    Subfield.le_topologicalClosure _ ⟨y, hy, rfl⟩
  obtain ⟨r, hr⟩ := NontriviallyNormedField.non_trivial (α := ℚ_[l])
  have hrmem : ι (algebraMap ℚ_[l] (PadicAlgCl l) r) ∈ F0 := hmemF _ (F.algebraMap_mem r)
  have hrnorm : ‖ι (algebraMap ℚ_[l] (PadicAlgCl l) r)‖ = ‖r‖ := by
    rw [← PadicComplex.coe_eq, PadicComplex.norm_extends]
    exact PadicAlgCl.norm_extends l r
  letI : NontriviallyNormedField F0 :=
    { SubfieldClass.toNormedField F0 with
      non_trivial := ⟨⟨_, hrmem⟩, by
        show 1 < ‖ι (algebraMap ℚ_[l] (PadicAlgCl l) r)‖
        rw [hrnorm]; exact hr⟩ }
  haveI : CompleteSpace F0 := (Subfield.isClosed_topologicalClosure _).completeSpace_coe
  letI : NormedSpace F0 ℂ_[l] :=
    { norm_smul_le := fun a b => by
        show ‖(a : ℂ_[l]) * b‖ ≤ ‖(a : ℂ_[l])‖ * ‖b‖
        exact (norm_mul _ _).le }
  set z := ι ζ with hz
  set q := minpoly ℚ_[l] ζ with hq
  set n := q.natDegree with hn
  let g : ℚ_[l] →+* F0 := (ι.comp (algebraMap ℚ_[l] (PadicAlgCl l))).codRestrict F0
    (fun r => hmemF _ (F.algebraMap_mem r))
  let Q : F0[X] := q.map g
  have hQmonic : Q.Monic := (minpoly.monic hζ).map g
  have hQdeg : Q.natDegree = n := (minpoly.monic hζ).natDegree_map g
  have hQroot : aeval z Q = 0 := by
    have h1 : (algebraMap F0 ℂ_[l]).comp g = ι.comp (algebraMap ℚ_[l] (PadicAlgCl l)) := by
      ext; rfl
    rw [aeval_def, eval₂_map, h1, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]
  have hQ1 : Q ≠ 1 := by
    intro h
    have := congrArg natDegree h
    rw [hQdeg, natDegree_one] at this
    exact (minpoly.natDegree_pos hζ).ne' this
  let φ : (Fin n → F0) →ₗ[F0] ℂ_[l] := Fintype.linearCombination F0 (fun i : Fin n => z ^ (i : ℕ))
  have hpoly : ∀ p : F0[X], aeval z p ∈ LinearMap.range φ := by
    intro p
    rw [← aeval_modByMonic_eq_self_of_root (p := p) hQroot]
    have hd : (p %ₘ Q).natDegree < n := hQdeg ▸ natDegree_modByMonic_lt p hQmonic hQ1
    rw [aeval_eq_sum_range' hd, ← Fin.sum_univ_eq_sum_range (fun i => (p %ₘ Q).coeff i • z ^ i)]
    exact ⟨fun i => (p %ₘ Q).coeff i, by rw [Fintype.linearCombination_apply]⟩
  have hadj : ∀ y ∈ Algebra.adjoin F0 {z}, y ∈ LinearMap.range φ := by
    intro y hy
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨p, rfl⟩ := hy
    exact hpoly p
  let B : Subalgebra ℚ_[l] (PadicAlgCl l) :=
    { (Algebra.adjoin F0 {z}).toSubsemiring.comap ι with
      algebraMap_mem' := fun r => by
        show ι (algebraMap ℚ_[l] _ r) ∈ Algebra.adjoin F0 {z}
        exact (Algebra.adjoin F0 {z}).algebraMap_mem (⟨_, hmemF _ (F.algebraMap_mem r)⟩ : F0) }
  have hsub : ∀ y ∈ (F ⊔ IntermediateField.adjoin ℚ_[l] {ζ} : IntermediateField ℚ_[l] (PadicAlgCl l)),
      ι y ∈ Algebra.adjoin F0 {z} := by
    intro y hy
    have hle : (F ⊔ IntermediateField.adjoin ℚ_[l] {ζ}).toSubalgebra ≤ B := by
      rw [IntermediateField.sup_toSubalgebra_of_isAlgebraic_right]
      refine sup_le ?_ ?_
      · intro w hw
        exact (Algebra.adjoin F0 {z}).algebraMap_mem (⟨_, hmemF w hw⟩ : F0)
      · rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζ.isAlgebraic]
        refine Algebra.adjoin_le (Set.singleton_subset_iff.2 ?_)
        exact Algebra.subset_adjoin rfl
    exact hle hy
  have hclosed : IsClosed ((LinearMap.range φ : Submodule F0 ℂ_[l]) : Set ℂ_[l]) :=
    Submodule.closed_of_finiteDimensional _
  have hcl : closure (ι '' ((F ⊔ IntermediateField.adjoin ℚ_[l] {ζ} :
      IntermediateField ℚ_[l] (PadicAlgCl l)) : Set (PadicAlgCl l))) ⊆ LinearMap.range φ :=
    closure_minimal (by rintro _ ⟨y, hy, rfl⟩; exact hadj _ (hsub y hy)) hclosed
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.ker φ)
  have hψker : LinearMap.ker (φ.domRestrict W) = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun w hw => ?_
    exact Subtype.ext (Submodule.disjoint_def.1 hW.disjoint _ hw w.2)
  obtain ⟨C0, -, hC0⟩ := (φ.domRestrict W).exists_antilipschitzWith hψker
  refine ⟨n, C0, fun x hx hx1 => ?_⟩
  obtain ⟨v, hv⟩ := hcl hx
  obtain ⟨k, hk, w, hw, hkw⟩ := Submodule.mem_sup.1 (hW.sup_eq_top ▸ Submodule.mem_top (x := v))
  have hφw : φ w = x := by
    rw [← hv, ← hkw, map_add (f := _), LinearMap.mem_ker.1 hk, zero_add]
  have hwn : ‖w‖ ≤ C0 := by
    have h := hC0.le_mul_dist ⟨w, hw⟩ 0
    rw [map_zero, dist_zero_right, dist_zero_right] at h
    have h2 : ‖(φ.domRestrict W) ⟨w, hw⟩‖ = ‖x‖ := by
      rw [LinearMap.domRestrict_apply, hφw]
    rw [h2] at h
    calc ‖w‖ = ‖(⟨w, hw⟩ : W)‖ := rfl
      _ ≤ C0 * ‖x‖ := h
      _ ≤ C0 * 1 := mul_le_mul_of_nonneg_left hx1 C0.2
      _ = C0 := mul_one _
  refine ⟨fun i => (w i : ℂ_[l]), fun i => ⟨(w i).2, ?_⟩, ?_⟩
  · exact (norm_le_pi_norm w i).trans hwn
  · rw [← hφw, Fintype.linearCombination_apply]
    rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosureAdjoinUnitBallCoeffBoundStatement
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coeff_bounded_in_closure_of_norm_le_one : ∀ (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (PadicAlgCl l)) (ζ : PadicAlgCl l), IsIntegral ℚ_[l] ζ → ∃ (n : ℕ) (C : ℝ), ∀ x ∈ closure (algebraMap (PadicAlgCl l) ℂ_[l] '' ((F ⊔ IntermediateField.adjoin ℚ_[l] {ζ} : IntermediateField ℚ_[l] (PadicAlgCl l)) : Set (PadicAlgCl l))), ‖x‖ ≤ 1 → ∃ c : Fin n → ℂ_[l], (∀ i, c i ∈ closure (algebraMap (PadicAlgCl l) ℂ_[l] '' (F : Set (PadicAlgCl l))) ∧ ‖c i‖ ≤ C) ∧ x = ∑ i, c i * (algebraMap (PadicAlgCl l) ℂ_[l] ζ) ^ (i : ℕ) := by
  first | exact @GlobalTheory.closure_adjoin_unitBall_coeff_bound | exact GlobalTheory.closure_adjoin_unitBall_coeff_bound | (intros; apply GlobalTheory.closure_adjoin_unitBall_coeff_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCyclotomicUnramifiedCompletedIntegers
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.CycClosure

variable {l : ℕ} [Fact l.Prime]

theorem mem_clC {F : IntermediateField ℚ_[l] (PadicAlgCl l)} {x : ℂ_[l]} :
    x ∈ clC l F ↔ x ∈ closure (algebraMap (PadicAlgCl l) ℂ_[l] '' (F : Set (PadicAlgCl l))) ∧ ‖x‖ ≤ 1 := by
  simp only [clC, Subring.mem_inf]
  apply and_congr Iff.rfl
  change x ∈ PadicComplexInt l ↔ _
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm]
  exact (Valued.toNormedField.norm_le_one_iff).symm

theorem coe_clC (F : IntermediateField ℚ_[l] (PadicAlgCl l)) :
    (clC l F : Set ℂ_[l]) =
      closure ((fun y : PadicAlgCl l => (y : ℂ_[l])) '' {y | y ∈ F ∧ ‖y‖ ≤ 1}) := by
  have hc : IsClopen (Metric.closedBall (0 : ℂ_[l]) 1) :=
    IsUltrametricDist.isClopen_closedBall _ one_ne_zero
  have e : (fun y : PadicAlgCl l => (y : ℂ_[l])) '' {y | y ∈ F ∧ ‖y‖ ≤ 1} =
      (algebraMap (PadicAlgCl l) ℂ_[l] '' (F : Set (PadicAlgCl l))) ∩ Metric.closedBall 0 1 := by
    ext x
    constructor
    · rintro ⟨y, ⟨hy, h⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, by rw [mem_closedBall_zero_iff, PadicComplex.norm_extends]; exact h⟩
    · rintro ⟨⟨y, hy, rfl⟩, h⟩
      rw [mem_closedBall_zero_iff] at h
      exact ⟨y, ⟨hy, by rw [← PadicComplex.norm_extends]; exact h⟩, rfl⟩
  rw [e]
  apply Set.Subset.antisymm
  · intro x hx
    rw [SetLike.mem_coe, mem_clC] at hx
    exact hc.isOpen.closure_inter ⟨hx.1, by simpa using hx.2⟩
  · intro x hx
    have := closure_inter_subset_inter_closure _ _ hx
    rw [hc.isClosed.closure_eq] at this
    exact mem_clC.2 ⟨this.1, by simpa using this.2⟩

theorem clC_mono {F G : IntermediateField ℚ_[l] (PadicAlgCl l)} (h : F ≤ G) {x : ℂ_[l]}
    (hx : x ∈ clC l F) : x ∈ clC l G :=
  mem_clC.2 ⟨closure_mono (Set.image_mono h) (mem_clC.1 hx).1, (mem_clC.1 hx).2⟩

theorem clC_props (LL : Loc.FinExt l) (F : IntermediateField ℚ_[l] (PadicAlgCl l))
    (hF : LL.1 ⊔ Loc.MaximalUnramifiedExtension l = F) :
    ∃ _ : IsDiscreteValuationRing ↥(clC l F),
      IsAlgClosed (IsLocalRing.ResidueField ↥(clC l F)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal ↥(clC l F)) ↥(clC l F) ∧
      IsAdic (IsLocalRing.maximalIdeal ↥(clC l F)) ∧
      (∀ x ∈ clC l F, ∀ y ∈ clC l F, ‖x‖ ≤ ‖y‖ → x / y ∈ clC l F) := by
  subst hF
  obtain ⟨O, hdvr, -, -, hdiv, hres, hcomp, hadic, hO⟩ := GlobalTheory.BigInt.exists_integers_completion l LL
  have e : O = clC l (LL.1 ⊔ Loc.MaximalUnramifiedExtension l) := SetLike.coe_injective (hO.trans (coe_clC _).symm)
  subst e
  exact ⟨hdvr, hres, hcomp, hadic, hdiv⟩

theorem muK_spec (k : ℕ) : FiniteDimensional ℚ_[l] ↥(muK l k) ∧
    ∃ ζ : PadicAlgCl l, IsPrimitiveRoot ζ (l ^ k) ∧ muK l k = IntermediateField.adjoin ℚ_[l] {ζ} := by
  have hn : 0 < l ^ k := pow_pos (Fact.out : l.Prime).pos k
  haveI : NeZero (l ^ k) := ⟨hn.ne'⟩
  classical
  have hfin : ({x | x ^ (l ^ k) = 1} : Set (PadicAlgCl l)).Finite := by
    refine (Polynomial.nthRoots (l ^ k) (1 : PadicAlgCl l)).toFinset.finite_toSet.subset fun x hx => ?_
    simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hn]
    exact hx
  haveI := hfin.to_subtype
  refine ⟨IntermediateField.finiteDimensional_adjoin fun x hx =>
    ⟨X ^ (l ^ k) - C 1, monic_X_pow_sub_C 1 hn.ne', by simp [show x ^ (l ^ k) = 1 from hx]⟩, ?_⟩
  have hdeg : (cyclotomic (l ^ k) (PadicAlgCl l)).degree ≠ 0 := by
    rw [degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.2 hn).ne'
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root _ hdeg
  have hp : IsPrimitiveRoot ζ (l ^ k) := (isRoot_cyclotomic_iff).1 hζ
  refine ⟨ζ, hp, le_antisymm ?_ ?_⟩
  · rw [muK, IntermediateField.adjoin_le_iff]
    intro x hx
    have hx' : x ^ (l ^ k) = 1 := hx
    obtain ⟨i, -, rfl⟩ := hp.eq_pow_of_pow_eq_one hx'
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ_[l] ζ) _
  · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact IntermediateField.subset_adjoin _ _ hp.pow_eq_one

end GlobalTheory.CycClosure

namespace GlobalTheory.CycClosure

theorem exists_cyclotomic_integers : ∀ (l : ℕ) [Fact l.Prime] (K₀ L : Loc.FinExt l) (k : ℕ), ∃ _ : IsDiscreteValuationRing ↥(clC l (Kt l K₀ L ⊔ muK l k)), IsAlgClosed (IsLocalRing.ResidueField ↥(clC l (Kt l K₀ L ⊔ muK l k))) ∧ IsAdicComplete (IsLocalRing.maximalIdeal ↥(clC l (Kt l K₀ L ⊔ muK l k))) ↥(clC l (Kt l K₀ L ⊔ muK l k)) ∧ IsAdic (IsLocalRing.maximalIdeal ↥(clC l (Kt l K₀ L ⊔ muK l k))) ∧ (∀ x ∈ clC l (Kt l K₀ L ⊔ muK l k), ∀ y ∈ clC l (Kt l K₀ L ⊔ muK l k), ‖x‖ ≤ ‖y‖ → x / y ∈ clC l (Kt l K₀ L ⊔ muK l k)) ∧ muK l 0 = ⊥ ∧ (∃ T : Finset ℂ_[l], ∀ x, x ∈ clC l (Kt l K₀ L ⊔ muK l k) ↔ x ∈ Submodule.span ↥(clC l (Kt l K₀ L)) (T : Set ℂ_[l])) ∧ ∃ ζ ∈ clC l (Kt l K₀ L ⊔ muK l k), IsPrimitiveRoot ζ (l ^ k) ∧ ∀ x ∈ clC l (Kt l K₀ L ⊔ muK l k), ∃ (p : Polynomial ↥(clC l (Kt l K₀ L))) (d : ↥(clC l (Kt l K₀ L))), d ≠ 0 ∧ x * (d : ℂ_[l]) = Polynomial.aeval ζ p := by
  intro l _ K₀ L k
  have hp : l.Prime := Fact.out
  obtain ⟨hfd, ζ, hζ, hmu⟩ := muK_spec (l := l) k
  let LL : Loc.FinExt l := ⟨K₀.1 ⊔ L.1 ⊔ muK l k, by haveI := K₀.2; haveI := L.2; infer_instance⟩
  have hM : LL.1 ⊔ Loc.MaximalUnramifiedExtension l = Kt l K₀ L ⊔ muK l k := by
    simp only [LL, Kt]; exact sup_right_comm _ _ _
  let L0 : Loc.FinExt l := ⟨K₀.1 ⊔ L.1, by haveI := K₀.2; haveI := L.2; infer_instance⟩
  obtain ⟨hdvr, hres, hcomp, hadic, hdiv⟩ := clC_props LL _ hM
  obtain ⟨hdvr0, -, -, -, -⟩ := clC_props L0 (Kt l K₀ L) rfl
  have mu0 : muK l 0 = ⊥ := by
    rw [muK, eq_bot_iff, IntermediateField.adjoin_le_iff]
    intro x hx
    have : x = 1 := by simpa using hx
    rw [this]; exact one_mem _
  have hn : 0 < l ^ k := pow_pos hp.pos k
  have hint : IsIntegral ℚ_[l] ζ :=
    ⟨X ^ (l ^ k) - C 1, monic_X_pow_sub_C 1 hn.ne', by simp [hζ.pow_eq_one]⟩
  obtain ⟨n, Cb, hC⟩ := GlobalTheory.T.exists_coeff_bounded_in_closure_of_norm_le_one l (Kt l K₀ L) ζ hint
  have hB : ∀ x, x ∈ clC l (Kt l K₀ L ⊔ muK l k) ↔ x ∈ clC l (Kt l K₀ L ⊔ IntermediateField.adjoin ℚ_[l] {ζ}) := by
    intro x; rw [hmu]
  have hl : ‖(l : ℂ_[l])‖ < 1 := by
    rw [← map_natCast (algebraMap (PadicAlgCl l) ℂ_[l])]
    refine lt_of_eq_of_lt (PadicComplex.norm_extends l (l : PadicAlgCl l)) ?_
    rw [GlobalTheory.UnramValue.norm_l]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hl0 : (l : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (max Cb 1) by positivity) hl
  have cmem : ∀ c ∈ closure (algebraMap (PadicAlgCl l) ℂ_[l] '' ((Kt l K₀ L : IntermediateField ℚ_[l] (PadicAlgCl l)) : Set (PadicAlgCl l))),
      ‖c‖ ≤ Cb → (l : ℂ_[l]) ^ N * c ∈ clC l (Kt l K₀ L) := by
    intro c hc hcb
    refine mem_clC.2 ⟨map_mem_closure (continuous_const.mul continuous_id) hc ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨(l : PadicAlgCl l) ^ N * z, mul_mem (pow_mem (natCast_mem _ _) _) hz, ?_⟩
      simp
    · rw [norm_mul, norm_pow]
      have h1 : ‖c‖ ≤ max Cb 1 := hcb.trans (le_max_left _ _)
      have h2 : (0 : ℝ) < max Cb 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
      calc ‖(l : ℂ_[l])‖ ^ N * ‖c‖ ≤ ‖(l : ℂ_[l])‖ ^ N * max Cb 1 :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ 1 / max Cb 1 * max Cb 1 := mul_le_mul_of_nonneg_right hN.le h2.le
        _ = 1 := by field_simp
  set ζ' : ℂ_[l] := algebraMap (PadicAlgCl l) ℂ_[l] ζ with hζ'
  have hζn : ‖ζ‖ = 1 := by
    have := congrArg norm hζ.pow_eq_one
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
  have hζB : ζ' ∈ clC l (Kt l K₀ L ⊔ muK l k) := by
    rw [hB]
    refine mem_clC.2 ⟨subset_closure ⟨ζ, (le_sup_right : IntermediateField.adjoin ℚ_[l] {ζ} ≤ _)
      (IntermediateField.mem_adjoin_simple_self ℚ_[l] ζ), rfl⟩, ?_⟩
    exact ((PadicComplex.norm_extends l ζ).trans hζn).le
  have hAB : ∀ x ∈ clC l (Kt l K₀ L), x ∈ clC l (Kt l K₀ L ⊔ muK l k) := fun x hx => clC_mono le_sup_left hx
  have hlN : (l : ℂ_[l]) ^ N ∈ clC l (Kt l K₀ L) := pow_mem (natCast_mem _ _) _
  have rep : ∀ x ∈ clC l (Kt l K₀ L ⊔ muK l k), ∃ c : Fin n → ℂ_[l],
      (∀ i, (l : ℂ_[l]) ^ N * c i ∈ clC l (Kt l K₀ L)) ∧ x = ∑ i, c i * ζ' ^ (i : ℕ) := by
    intro x hx
    rw [hB] at hx
    obtain ⟨c, hc, e⟩ := hC x (mem_clC.1 hx).1 (mem_clC.1 hx).2
    exact ⟨c, fun i => cmem _ (hc i).1 (hc i).2, e⟩
  refine ⟨hdvr, hres, hcomp, hadic, hdiv, mu0, ?_, ζ', hζB, hζ.map_of_injective (algebraMap (PadicAlgCl l) ℂ_[l]).injective, ?_⟩
  · classical
    let g : Fin n → ℂ_[l] := fun i => ((l : ℂ_[l]) ^ N)⁻¹ * ζ' ^ (i : ℕ)
    let P : Submodule ↥(clC l (Kt l K₀ L)) ℂ_[l] := Submodule.span ↥(clC l (Kt l K₀ L)) (Set.range g)
    let B' : Submodule ↥(clC l (Kt l K₀ L)) ℂ_[l] :=
      { carrier := (clC l (Kt l K₀ L ⊔ muK l k) : Set ℂ_[l])
        add_mem' := fun ha hb => add_mem ha hb
        zero_mem' := zero_mem _
        smul_mem' := fun a x hx => by
          rw [Subring.smul_def, smul_eq_mul]
          exact mul_mem (hAB _ a.2) hx }
    have hBP : B' ≤ P := by
      intro x hx
      obtain ⟨c, hc, rfl⟩ := rep x hx
      refine Submodule.sum_mem _ fun i _ => ?_
      have := Submodule.smul_mem P (⟨(l : ℂ_[l]) ^ N * c i, hc i⟩ : ↥(clC l (Kt l K₀ L)))
        (Submodule.subset_span ⟨i, rfl⟩ : g i ∈ P)
      convert this using 1
      rw [Subring.smul_def, smul_eq_mul]
      change c i * ζ' ^ (i : ℕ) = ((l : ℂ_[l]) ^ N * c i) * (((l : ℂ_[l]) ^ N)⁻¹ * ζ' ^ (i : ℕ))
      field_simp
    haveI : IsNoetherian ↥(clC l (Kt l K₀ L)) ↥P :=
      isNoetherian_of_fg_of_noetherian P (Submodule.fg_span (Set.finite_range g))
    have hfg : B'.FG := by
      have h1 : (B'.comap P.subtype).FG := IsNoetherian.noetherian _
      have h2 := h1.map P.subtype
      rwa [Submodule.map_comap_subtype, inf_eq_right.2 hBP] at h2
    obtain ⟨T, hT⟩ := hfg
    exact ⟨T, fun x => by rw [hT]; rfl⟩
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := rep x hx
    refine ⟨∑ i : Fin n, monomial (i : ℕ) (⟨(l : ℂ_[l]) ^ N * c i, hc i⟩ : ↥(clC l (Kt l K₀ L))),
      ⟨(l : ℂ_[l]) ^ N, hlN⟩, fun h => pow_ne_zero N hl0 (congrArg Subtype.val h), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, aeval_monomial, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    change c i * ζ' ^ (i : ℕ) * (l : ℂ_[l]) ^ N = ((l : ℂ_[l]) ^ N * c i) * ζ' ^ (i : ℕ)
    ring

end GlobalTheory.CycClosure
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCyclotomicUnramifiedCompletedIntegersStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cyclotomic_unramified_completed_integers : ∀ (l : ℕ) [Fact l.Prime] (K₀ L : Loc.FinExt l) (k : ℕ), ∃ _ : IsDiscreteValuationRing ↥(clC l (Kt l K₀ L ⊔ muK l k)), IsAlgClosed (IsLocalRing.ResidueField ↥(clC l (Kt l K₀ L ⊔ muK l k))) ∧ IsAdicComplete (IsLocalRing.maximalIdeal ↥(clC l (Kt l K₀ L ⊔ muK l k))) ↥(clC l (Kt l K₀ L ⊔ muK l k)) ∧ IsAdic (IsLocalRing.maximalIdeal ↥(clC l (Kt l K₀ L ⊔ muK l k))) ∧ (∀ x ∈ clC l (Kt l K₀ L ⊔ muK l k), ∀ y ∈ clC l (Kt l K₀ L ⊔ muK l k), ‖x‖ ≤ ‖y‖ → x / y ∈ clC l (Kt l K₀ L ⊔ muK l k)) ∧ muK l 0 = ⊥ ∧ (∃ T : Finset ℂ_[l], ∀ x, x ∈ clC l (Kt l K₀ L ⊔ muK l k) ↔ x ∈ Submodule.span ↥(clC l (Kt l K₀ L)) (T : Set ℂ_[l])) ∧ ∃ ζ ∈ clC l (Kt l K₀ L ⊔ muK l k), IsPrimitiveRoot ζ (l ^ k) ∧ ∀ x ∈ clC l (Kt l K₀ L ⊔ muK l k), ∃ (p : Polynomial ↥(clC l (Kt l K₀ L))) (d : ↥(clC l (Kt l K₀ L))), d ≠ 0 ∧ x * (d : ℂ_[l]) = Polynomial.aeval ζ p := by
  first | exact @GlobalTheory.CycClosure.exists_cyclotomic_integers | exact GlobalTheory.CycClosure.exists_cyclotomic_integers | (intros; apply GlobalTheory.CycClosure.exists_cyclotomic_integers <;> assumption)
end
