module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsQuaternaryOfCoordinates
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareOfValuedSubOneLt
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsZeroCoordNeZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitValuedTernaryLtOne
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNonzeroIsotropic
universe u_1

namespace GlobalTheory.NonzeroIsotropic

open MvPolynomial

theorem quadForm_totalDegree_le {k : Type u_1} [Field k] (a : Fin 3 → Fin 3 → k) :
    (∑ i : Fin 3, ∑ j : Fin 3, C (a i j) * X i * X j : MvPolynomial (Fin 3) k).totalDegree ≤ 2 := by
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
  calc (C (a i j) * X i * X j : MvPolynomial (Fin 3) k).totalDegree
      ≤ (C (a i j) * X i : MvPolynomial (Fin 3) k).totalDegree + (X j : MvPolynomial (Fin 3) k).totalDegree :=
        totalDegree_mul _ _
    _ ≤ ((C (a i j) : MvPolynomial (Fin 3) k).totalDegree + (X i : MvPolynomial (Fin 3) k).totalDegree)
          + (X j : MvPolynomial (Fin 3) k).totalDegree := by gcongr; exact totalDegree_mul _ _
    _ = 2 := by simp [totalDegree_C, totalDegree_X]

theorem exists_nonzero_isotropic :
    ∀ {k : Type u_1} [inst : Field k] [Finite k] (a : Fin (3 : ℕ) → Fin (3 : ℕ) → k),
      ∃ (x : Fin (3 : ℕ) → k), x ≠ (0 : Fin (3 : ℕ) → k) ∧
        ∑ i : Fin (3 : ℕ), ∑ j : Fin (3 : ℕ), a i j * x i * x j = (0 : k) := by
  intro k _ _ a
  classical
  haveI : Fintype k := Fintype.ofFinite k
  obtain ⟨p, hp⟩ := CharP.exists k
  haveI := hp
  have hpp : p.Prime := by
    rcases CharP.char_is_prime_or_zero k p with h | h
    · exact h
    · subst h
      haveI : CharZero k := CharP.charP_to_charZero k
      exact absurd (Finite.of_injective (Nat.cast : ℕ → k) Nat.cast_injective) (by
        intro h; exact not_finite ℕ)
  set f : MvPolynomial (Fin 3) k := ∑ i : Fin 3, ∑ j : Fin 3, C (a i j) * X i * X j with hf
  have hdeg : f.totalDegree < Fintype.card (Fin 3) := by
    have : f.totalDegree ≤ 2 := quadForm_totalDegree_le a
    simp only [Fintype.card_fin]; omega
  have hdvd := char_dvd_card_solutions p hdeg
  have heval : ∀ x : Fin 3 → k, eval x f = ∑ i : Fin 3, ∑ j : Fin 3, a i j * x i * x j := by
    intro x; simp [hf]
  let z : { x : Fin 3 → k // eval x f = 0 } := ⟨0, by rw [heval]; simp⟩
  have hcard : 1 < Fintype.card { x : Fin 3 → k // eval x f = 0 } := by
    have hpos : 0 < Fintype.card { x : Fin 3 → k // eval x f = 0 } := Fintype.card_pos_iff.mpr ⟨z⟩
    have := Nat.le_of_dvd hpos hdvd
    have := hpp.two_le
    omega
  obtain ⟨y, hy⟩ := Fintype.exists_ne_of_one_lt_card hcard z
  refine ⟨y.1, fun h => hy (Subtype.ext h), ?_⟩
  rw [← heval]; exact y.2

end GlobalTheory.NonzeroIsotropic
end

open NumberField IsDedekindDomain
open scoped Matrix WithZero

namespace GlobalTheory.LocalQuad

namespace TernaryResidue


open MvPolynomial in
theorem exists_ne_zero_sum_eq_zero {k : Type*} [Field k] [Finite k] (a : Fin 3 → Fin 3 → k) :
    ∃ x : Fin 3 → k, x ≠ 0 ∧ ∑ i, ∑ j, a i j * x i * x j = 0 := by
  first
  | exact @_root_.GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic
  | exact _root_.GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic
  | (apply _root_.GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic ..)

end TernaryResidue

theorem exists_unit_valued_ternary_lt_one (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (c : Fin 3 → Fin 3 → v.adicCompletion F)
    (hc : ∀ i j, Valued.v (c i j) ≤ 1) :
    ∃ x : Fin 3 → v.adicCompletion F, (∀ i, Valued.v (x i) ≤ 1) ∧ (∃ i, Valued.v (x i) = 1) ∧
      Valued.v (∑ i, ∑ j, c i j * x i * x j) < 1 := by
  classical
  choose r hr using fun i j => GlobalTheory.Idele.exists_valued_sub_le v (hc i j) 1
  let ι : 𝓞 F →+* v.adicCompletion F :=
    (algebraMap F (v.adicCompletion F)).comp (algebraMap (𝓞 F) F)
  have hι : ∀ y : 𝓞 F, Valued.v (ι y) = v.valuation F (algebraMap (𝓞 F) F y) := fun y =>
    GlobalTheory.Idele.valued_algebraMap v _
  have hle : ∀ y : 𝓞 F, Valued.v (ι y) ≤ 1 := fun y => by
    rw [hι]; exact v.valuation_le_one y
  have hlt : ∀ y : 𝓞 F, Valued.v (ι y) < 1 ↔ y ∈ v.asIdeal := fun y => by
    rw [hι]; exact v.valuation_lt_one_iff_mem y
  have hr' : ∀ i j, Valued.v (c i j - ι (r i j)) < 1 := fun i j => by
    refine (hr i j).trans_lt ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  obtain ⟨x, hx0, hx⟩ := TernaryResidue.exists_ne_zero_sum_eq_zero
    (k := 𝓞 F ⧸ v.asIdeal) fun i j => Ideal.Quotient.mk v.asIdeal (r i j)
  choose y hy using fun i => Ideal.Quotient.mk_surjective (x i)
  refine ⟨fun i => ι (y i), fun i => hle _, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hx0
    refine ⟨i, le_antisymm (hle _) (not_lt.1 fun h => hi ?_)⟩
    rw [← hy i]
    exact Ideal.Quotient.eq_zero_iff_mem.2 ((hlt _).1 h)
  · have hmem : (∑ i, ∑ j, r i j * y i * y j) ∈ v.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hx]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, hy]
    have hsplit : ∑ i, ∑ j, c i j * ι (y i) * ι (y j) =
        ι (∑ i, ∑ j, r i j * y i * y j) +
          ∑ i, ∑ j, (c i j - ι (r i j)) * ι (y i) * ι (y j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hsplit]
    refine Valuation.map_add_lt _ ((hlt _).2 hmem) ?_
    refine Valuation.map_sum_lt _ one_ne_zero fun i _ => Valuation.map_sum_lt _ one_ne_zero
      fun j _ => ?_
    rw [map_mul, map_mul]
    exact (mul_le_of_le_one_right' (hle _)).trans_lt
      ((mul_le_of_le_one_right' (hle _)).trans_lt (hr' i j))

end GlobalTheory.LocalQuad
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRingHomAdicCompletion
open NumberField IsDedekindDomain
open scoped Matrix WithZero

theorem GlobalTheory.LocalQuad.exists_ringHom_adicCompletion (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] (w : HeightOneSpectrum (𝓞 L)) :
    ∃ (v : HeightOneSpectrum (𝓞 K)) (φ : v.adicCompletion K →+* w.adicCompletion L),
      ∀ x : K, φ (algebraMap K (v.adicCompletion K) x) =
        algebraMap L (w.adicCompletion L) (algebraMap K L x) := by
  let v : HeightOneSpectrum (𝓞 K) := w.under (𝓞 K)
  have : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have hc := (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver K L v w).continuous
  refine ⟨v, ((HeightOneSpectrum.adicCompletion.equiv L w).symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L))) hc)).comp
      (HeightOneSpectrum.adicCompletion.equiv K v).toRingHom, fun x => ?_⟩
  apply HeightOneSpectrum.adicCompletion.ext
  exact UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ x)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsZeroFiveOfValuation
open NumberField IsDedekindDomain
open scoped Matrix WithZero

namespace GlobalTheory.LocalQuad

namespace FiveVar

variable {K : Type*} [Field K] {n : Type*} [Fintype n]

def qf (a x : n → K) : K := ∑ i, a i * x i ^ 2

def bf (a x y : n → K) : K := ∑ i, 2 * a i * x i * y i

lemma qf_add (a x y : n → K) : qf a (x + y) = qf a x + bf a x y + qf a y := by
  simp only [qf, bf, ← Finset.sum_add_distrib, Pi.add_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma qf_smul (a x : n → K) (s : K) : qf a (s • x) = s ^ 2 * qf a x := by
  simp only [qf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma bf_smul_left (a x y : n → K) (s : K) : bf a (s • x) y = s * bf a x y := by
  simp only [bf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma bf_smul_right (a x y : n → K) (s : K) : bf a x (s • y) = s * bf a x y := by
  simp only [bf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma bf_add_left (a x y z : n → K) : bf a (x + y) z = bf a x z + bf a y z := by
  simp only [bf, ← Finset.sum_add_distrib, Pi.add_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma bf_self (a x : n → K) : bf a x x = 2 * qf a x := by
  simp only [bf, qf, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma qf_three (a p q r : n → K) (x : Fin 3 → K) (w : K) :
    qf a (x 0 • p + x 1 • q + x 2 • r) / w = ∑ i, ∑ j,
      (![![qf a p / w, bf a p q / w, bf a p r / w], ![0, qf a q / w, bf a q r / w],
        ![0, 0, qf a r / w]] : Fin 3 → Fin 3 → K) i j * x i * x j := by
  rw [qf_add, qf_add, bf_add_left]
  simp [Fin.sum_univ_three, qf_smul, bf_smul_left, bf_smul_right]
  ring

lemma val_bf_sq_le (h2 : (2 : K) ≠ 0) (v : Valuation K ℤᵐ⁰)
    (hsq : ∀ x : K, v (x - 1) < v 4 → IsSquare x) (a : n → K)
    (han : ∀ x, qf a x = 0 → x = 0) (x y : n → K) :
    v (bf a x y) ^ 2 ≤ v (qf a x) * v (qf a y) := by
  by_contra hlt
  rw [not_le] at hlt
  have hb : bf a x y ≠ 0 := by
    intro h
    rw [h] at hlt
    simp at hlt
  have hvb : v (bf a x y) ≠ 0 := by simpa using hb
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hv4 : v 4 ≠ 0 := by simpa using h4
  have hv4' : v 4 ≤ 1 := by
    have e : (4 : K) = 1 + 1 + 1 + 1 := by norm_num
    have h1 : v 1 ≤ 1 := (map_one v).le
    rw [e]
    exact v.map_add_le (v.map_add_le (v.map_add_le h1 h1) h1) h1
  have hx : qf a x ≠ 0 := by
    intro h
    apply hb
    rw [han x h]
    simp [bf]
  obtain ⟨s, hs⟩ := hsq (1 - 4 * (qf a x * qf a y) / bf a x y ^ 2) (by
    rw [sub_sub_cancel_left, Valuation.map_neg, map_div₀, map_mul, map_mul, map_pow,
      mul_div_assoc]
    have h1 : v (qf a x) * v (qf a y) / v (bf a x y) ^ 2 < 1 :=
      (div_lt_one₀ (pow_pos (zero_lt_iff.mpr hvb) 2)).mpr hlt
    calc v 4 * (v (qf a x) * v (qf a y) / v (bf a x y) ^ 2) < v 4 * 1 :=
          mul_lt_mul_of_pos_left h1 (zero_lt_iff.mpr hv4)
      _ = v 4 := mul_one _)
  set t := (-bf a x y + bf a x y * s) / (2 * qf a x) with ht
  have h0 : qf a (t • x + y) = 0 := by
    rw [qf_add, qf_smul, bf_smul_left, ht]
    have hs' : 4 * (qf a x * qf a y) = bf a x y ^ 2 * (1 - s * s) := by
      rw [← hs]; field_simp; ring
    have : qf a y = bf a x y ^ 2 * (1 - s * s) / (4 * qf a x) := by
      rw [← hs']; field_simp
    rw [this]
    have h4' : (4 : K) = 2 * 2 := by norm_num
    rw [h4']
    field_simp
    ring
  have hy : y = (-t) • x := by
    have := han _ h0
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_right this
  clear_value t
  subst hy
  rw [bf_smul_right, bf_self, qf_smul] at hlt
  have e : ((-t) * (2 * qf a x)) ^ 2 = 4 * (qf a x * ((-t) ^ 2 * qf a x)) := by ring
  rw [← map_pow, e, ← map_mul v (qf a x), map_mul v 4] at hlt
  exact absurd hlt (not_lt.mpr (mul_le_of_le_one_left' hv4'))

variable [DecidableEq n]

lemma val_det_le (h2 : (2 : K) ≠ 0) (v : Valuation K ℤᵐ⁰)
    (hsq : ∀ x : K, v (x - 1) < v 4 → IsSquare x) (a : n → K)
    (han : ∀ x, qf a x = 0 → x = 0) (P : Matrix n n K) :
    v (∏ i, 2 * a i) * v P.det ^ 2 ≤ ∏ i, v (qf a (P i)) := by
  have hB : P * Matrix.diagonal (fun i => 2 * a i) * Pᵀ =
      Matrix.of fun i j => bf a (P i) (P j) := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.of_apply, bf]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hd := congrArg Matrix.det hB
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at hd
  have e : v (∏ i, 2 * a i) * v P.det ^ 2 = v (P.det * (∏ i, 2 * a i) * P.det) := by
    rw [map_mul, map_mul, sq, mul_comm (v P.det) (v (∏ i, 2 * a i)), mul_assoc]
  rw [e, hd, Matrix.det_apply']
  apply Valuation.map_sum_le
  intro σ _
  have hε : v (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : K) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [map_mul, hε, one_mul, map_prod]
  apply le_of_pow_le_pow_left₀ (n := 2) two_ne_zero zero_le'
  rw [← Finset.prod_pow]
  calc ∏ i, v (Matrix.of (fun i j => bf a (P i) (P j)) (σ i) i) ^ 2
      ≤ ∏ i, (v (qf a (P (σ i))) * v (qf a (P i))) :=
        Finset.prod_le_prod' fun i _ => val_bf_sq_le h2 v hsq a han _ _
    _ = (∏ i, v (qf a (P i))) ^ 2 := by
        rw [Finset.prod_mul_distrib, Equiv.prod_comp σ (fun i => v (qf a (P i))), sq]

lemma exists_basis (h2 : (2 : K) ≠ 0) (v : Valuation K ℤᵐ⁰)
    (hsq : ∀ x : K, v (x - 1) < v 4 → IsSquare x) (a : n → K)
    (han : ∀ x, qf a x = 0 → x = 0) :
    ∃ P : Matrix n n K, (∀ j, qf a (P j) ≠ 0) ∧
      ∀ (c : n → K) (j : n), v (c j) ^ 2 * v (qf a (P j)) ≤ v (qf a (∑ k, c k • P k)) := by
  have hrow : ∀ P : Matrix n n K, P.det ≠ 0 → ∀ j, qf a (P j) ≠ 0 := by
    intro P hP j h
    exact hP (Matrix.det_eq_zero_of_row_eq_zero j fun k => congrFun (han _ h) k)
  have ha : ∀ i, a i ≠ 0 := by
    intro i h
    have := hrow 1 (by simp) i
    apply this
    unfold qf
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : i = k
    · subst hk; simp [h]
    · simp [Matrix.one_apply_ne hk]
  have hD : v (∏ i, 2 * a i) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => mul_ne_zero h2 (ha i)
  have hprod : ∀ P : Matrix n n K, P.det ≠ 0 → (∏ i, v (qf a (P i))) / v P.det ^ 2 ≠ 0 := by
    intro P hP
    refine div_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => ?_) (pow_ne_zero _ ?_)
    · rw [Valuation.ne_zero_iff]; exact hrow P hP i
    · rw [Valuation.ne_zero_iff]; exact hP
  obtain ⟨m, ⟨P, hP, hm⟩, hmin⟩ := Int.exists_least_of_bdd
    (P := fun z => ∃ P : Matrix n n K, P.det ≠ 0 ∧
      WithZero.log ((∏ i, v (qf a (P i))) / v P.det ^ 2) = z)
    ⟨WithZero.log (v (∏ i, 2 * a i)), by
      rintro z ⟨P, hP, rfl⟩
      rw [WithZero.log_le_log hD (hprod P hP), le_div_iff₀
        (pow_pos (zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr hP)) 2)]
      exact val_det_le h2 v hsq a han P⟩
    ⟨_, 1, by simp, rfl⟩
  refine ⟨P, hrow P hP, fun c j => ?_⟩
  by_cases hc : c j = 0
  · simp [hc]
  have hdet : (P.updateRow j (∑ k, c k • P k)).det = c j * P.det := by
    rw [Matrix.det_updateRow_sum, smul_eq_mul]
  have hP' : (P.updateRow j (∑ k, c k • P k)).det ≠ 0 := by
    rw [hdet]; exact mul_ne_zero hc hP
  have h := hmin _ ⟨_, hP', rfl⟩
  rw [← hm, WithZero.log_le_log (hprod P hP) (hprod _ hP'), hdet,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), Matrix.updateRow_self] at h
  have e : ∏ i ∈ Finset.univ.erase j, v (qf a (P.updateRow j (∑ k, c k • P k) i)) =
      ∏ i ∈ Finset.univ.erase j, v (qf a (P i)) :=
    Finset.prod_congr rfl fun i hi => by rw [Matrix.updateRow_ne (Finset.ne_of_mem_erase hi)]
  rw [e] at h
  have hR : 0 < ∏ i ∈ Finset.univ.erase j, v (qf a (P i)) :=
    zero_lt_iff.mpr (Finset.prod_ne_zero_iff.mpr fun i _ =>
      (Valuation.ne_zero_iff v).mpr (hrow P hP i))
  have hd : 0 < v P.det ^ 2 := pow_pos (zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr hP)) 2
  have hcj : 0 < v (c j) ^ 2 := pow_pos (zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr hc)) 2
  rw [map_mul, mul_pow, ← div_div, div_le_div_iff_of_pos_right hd, le_div_iff₀ hcj,
    mul_right_comm, mul_le_mul_iff_left₀ hR, mul_comm] at h
  exact h

lemma exists_three (f : Fin 5 → Bool) :
    ∃ i j k : Fin 5, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ f j = f i ∧ f k = f i := by
  revert f
  decide

lemma exists_scale (v : Valuation K ℤᵐ⁰) (hv : Function.Surjective v) {x y : K} (hx : x ≠ 0)
    (hy : y ≠ 0)
    (h : decide (Even (WithZero.log (v y))) = decide (Even (WithZero.log (v x)))) :
    ∃ u : K, v u ^ 2 * v y = v x := by
  have he : Even (WithZero.log (v x) - WithZero.log (v y)) := by
    rw [Int.even_sub]
    simpa [eq_comm] using h
  obtain ⟨m, hm⟩ := he
  obtain ⟨u, hu⟩ := hv (WithZero.exp m)
  refine ⟨u, ?_⟩
  rw [hu, ← WithZero.exp_log ((Valuation.ne_zero_iff v).mpr hx),
    ← WithZero.exp_log ((Valuation.ne_zero_iff v).mpr hy), sq, ← WithZero.exp_add,
    ← WithZero.exp_add]
  congr 1
  omega

end FiveVar


open FiveVar in
theorem exists_zero_five_of_valuation {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (v : Valuation K ℤᵐ⁰) (hv : Function.Surjective v)
    (hsq : ∀ x : K, v (x - 1) < v 4 → IsSquare x)
    (hcw : ∀ c : Fin 3 → Fin 3 → K, (∀ i j, v (c i j) ≤ 1) →
      ∃ x : Fin 3 → K, (∀ i, v (x i) ≤ 1) ∧ (∃ i, v (x i) = 1) ∧
        v (∑ i, ∑ j, c i j * x i * x j) < 1)
    (a : Fin 5 → K) : ∃ x : Fin 5 → K, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  by_contra hno
  have han : ∀ x, qf a x = 0 → x = 0 := by
    intro x hx
    by_contra h
    exact hno ⟨x, h, hx⟩
  obtain ⟨P, hP, hmin⟩ := exists_basis h2 v hsq a han
  obtain ⟨i, j, k, hij, hik, hjk, hj, hk⟩ :=
    exists_three fun i => decide (Even (WithZero.log (v (qf a (P i)))))
  obtain ⟨s, hs⟩ := exists_scale v hv (hP i) (hP j) hj
  obtain ⟨t, ht⟩ := exists_scale v hv (hP i) (hP k) hk
  set w := qf a (P i) with hw
  have hw0 : w ≠ 0 := hP i
  have hvw : 0 < v w := zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr hw0)
  have hq : ∀ x, v (qf a x) = v w → v (qf a x / w) ≤ 1 := by
    intro x hx
    rw [map_div₀, hx, div_self hvw.ne']
  have hb : ∀ x y, v (qf a x) = v w → v (qf a y) = v w → v (bf a x y / w) ≤ 1 := by
    intro x y hx hy
    rw [map_div₀, div_le_one₀ hvw]
    apply le_of_pow_le_pow_left₀ (n := 2) two_ne_zero zero_le'
    have := val_bf_sq_le h2 v hsq a han x y
    rwa [hx, hy, ← sq] at this
  have h0 : v (qf a (P i)) = v w := rfl
  have h1 : v (qf a (s • P j)) = v w := by rw [qf_smul, map_mul, map_pow, hs]
  have h2' : v (qf a (t • P k)) = v w := by rw [qf_smul, map_mul, map_pow, ht]
  obtain ⟨x, -, ⟨l, hl⟩, hx⟩ := hcw
    ![![qf a (P i) / w, bf a (P i) (s • P j) / w, bf a (P i) (t • P k) / w],
      ![0, qf a (s • P j) / w, bf a (s • P j) (t • P k) / w],
      ![0, 0, qf a (t • P k) / w]] (by
      intro p q
      fin_cases p <;> fin_cases q
      · exact hq _ h0
      · exact hb _ _ h0 h1
      · exact hb _ _ h0 h2'
      · simp
      · exact hq _ h1
      · exact hb _ _ h1 h2'
      · simp
      · simp
      · exact hq _ h2')
  set c : Fin 5 → K := Pi.single i (x 0) + Pi.single j (x 1 * s) + Pi.single k (x 2 * t) with hc
  have hsum : ∑ p, c p • P p = x 0 • P i + x 1 • s • P j + x 2 • t • P k := by
    simp only [hc, Pi.add_apply, add_smul, Finset.sum_add_distrib, Pi.single_apply, ite_smul,
      zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, smul_smul]
  have hlt : v (qf a (∑ p, c p • P p)) < v w := by
    rw [← div_lt_one₀ hvw, ← map_div₀]
    convert hx using 2
    rw [hsum]
    exact qf_three a _ _ _ x w
  fin_cases l
  · have := hmin c i
    have e : c i = x 0 := by simp [hc, hij, hik]
    have hl' : v (x 0) = 1 := hl
    rw [e, hl', one_pow, one_mul] at this
    exact absurd hlt (not_lt.mpr this)
  · have := hmin c j
    have e : c j = x 1 * s := by simp [hc, hij.symm, hjk]
    have hl' : v (x 1) = 1 := hl
    rw [e, map_mul, hl', one_mul, hs] at this
    exact absurd hlt (not_lt.mpr this)
  · have := hmin c k
    have e : c k = x 2 * t := by simp [hc, hik.symm, hjk.symm]
    have hl' : v (x 2) = 1 := hl
    rw [e, map_mul, hl', one_mul, ht] at this
    exact absurd hlt (not_lt.mpr this)

end GlobalTheory.LocalQuad
end

open NumberField IsDedekindDomain
open scoped Matrix WithZero

namespace GlobalTheory.LocalQuad

theorem isotropic_ternary_of_units (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (h2 : Valued.v (2 : v.adicCompletion F) = 1)
    (a : Fin 3 → v.adicCompletion F) (ha : ∀ i, Valued.v (a i) = 1) :
    ∃ x : Fin 3 → v.adicCompletion F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  classical
  obtain ⟨x, -, ⟨k, hk⟩, hx⟩ := exists_unit_valued_ternary_lt_one F v (Matrix.diagonal a) (by
    intro i j
    by_cases h : i = j
    · subst h; simp [ha]
    · simp [Matrix.diagonal_apply_ne _ h])
  have e : ∑ i, ∑ j, Matrix.diagonal a i j * x i * x j = ∑ i, a i * x i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Matrix.diagonal_apply_ne _ hj.symm]) (by simp)]
    simp [sq, mul_assoc]
  rw [e] at hx
  set q := ∑ i, a i * x i ^ 2 with hq
  have hu : Valued.v (a k * x k ^ 2) = 1 := by simp [ha, hk]
  have hu0 : a k * x k ^ 2 ≠ 0 := by
    intro h; rw [h] at hu; simp at hu
  have h4 : Valued.v (4 : v.adicCompletion F) = 1 := by
    rw [show (4 : v.adicCompletion F) = 2 * 2 by norm_num, map_mul, h2, mul_one]
  have hlt : Valued.v (1 - q / (a k * x k ^ 2) - 1) < 1 := by
    rw [sub_sub_cancel_left, Valuation.map_neg, map_div₀, hu, div_one]; exact hx
  obtain ⟨s, hs⟩ := isSquare_of_valued_sub_one_lt F v (1 - q / (a k * x k ^ 2)) (by rwa [h4])
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [hs] at hlt
    simp at hlt
  have hxk : x k ≠ 0 := by
    intro h; rw [h] at hk; simp at hk
  refine ⟨Function.update x k (x k * s), fun hc => ?_, ?_⟩
  · have := congrFun hc k
    simp [hs0, hxk] at this
  · have h1 : a k * x k ^ 2 * (s * s) = a k * x k ^ 2 - q := by
      rw [← hs, mul_sub, mul_one, mul_div_cancel₀ _ hu0]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at hq ⊢
    rw [Finset.sum_congr rfl (g := fun i => a i * x i ^ 2)
      (fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]), Function.update_self]
    linear_combination h1 - hq

theorem isotropic_adicCompletion_of_five_le (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {ι : Type*} [Fintype ι] (hι : 5 ≤ Fintype.card ι)
    (a : ι → v.adicCompletion F) :
    ∃ x : ι → v.adicCompletion F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  haveI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  obtain ⟨e⟩ : Nonempty (Fin 5 ↪ ι) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hι)
  exact isotropic_of_injective e e.injective
    (exists_zero_five_of_valuation two_ne_zero Valued.v (v.valuedAdicCompletion_surjective F)
      (isSquare_of_valued_sub_one_lt F v) (exists_unit_valued_ternary_lt_one F v) _)

theorem exists_norm_over_extension (H : GlobalTheory.Published.HasseNormSt) (F : Type) [Field F] [NumberField F]
    (L : Type) [Field L] [NumberField L] [Algebra F L] {α β γ : F} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hγ : γ ≠ 0) {s : L} (hs : s ^ 2 = algebraMap F L (α * β * γ))
    (hr : ∀ σ : F →+* ℝ, ∃ x y z t : ℝ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ t ≠ 0) ∧
      x ^ 2 - σ α * y ^ 2 - σ β * z ^ 2 + σ γ * t ^ 2 = 0)
    (hf : ∀ v : HeightOneSpectrum (𝓞 F), ∃ x y z t : v.adicCompletion F,
      (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ t ≠ 0) ∧
      x ^ 2 - algebraMap F _ α * y ^ 2 - algebraMap F _ β * z ^ 2 + algebraMap F _ γ * t ^ 2 = 0) :
    ∃ X Y : L, algebraMap F L β = X ^ 2 - algebraMap F L α * Y ^ 2 := by
  refine H L _ _ (by simpa using hα) (by simpa using hβ) (fun σ => ?_) (fun w => ?_)
  · obtain ⟨x, y, z, t, h0, h⟩ := hr (σ.comp (algebraMap F L))
    exact exists_norm_of_quaternary (s := σ s) (γ := σ (algebraMap F L γ)) (by simpa using hα)
      (by simpa using hβ) (by simpa using hγ) (by rw [← map_pow, hs]; simp) h0 h
  · haveI : CharZero (w.adicCompletion L) :=
      charZero_of_injective_algebraMap (algebraMap L (w.adicCompletion L)).injective
    obtain ⟨v, φ, hφ⟩ := exists_ringHom_adicCompletion F L w
    obtain ⟨x, y, z, t, h0, h⟩ := hf v
    refine exists_norm_of_quaternary (s := algebraMap L _ s)
      (γ := algebraMap L _ (algebraMap F L γ)) (x := φ x) (y := φ y) (z := φ z) (t := φ t)
      (by simpa using hα) (by simpa using hβ) (by simpa using hγ)
      (by rw [← map_pow, hs]; simp only [map_mul]) (by simpa using h0) ?_
    have := congrArg φ h
    simpa only [map_add (f := _), map_sub, map_mul, map_pow, hφ, map_zero] using this

theorem isotropic_four (H : GlobalTheory.Published.HasseNormSt) (F : Type) [Field F] [NumberField F]
    (a : Fin 4 → F) (ha : ∀ i, a i ≠ 0)
    (hr : ∀ σ : F →+* ℝ, ∃ x : Fin 4 → ℝ, x ≠ 0 ∧ ∑ i, σ (a i) * x i ^ 2 = 0)
    (hf : ∀ v : HeightOneSpectrum (𝓞 F), ∃ x : Fin 4 → v.adicCompletion F, x ≠ 0 ∧
      ∑ i, algebraMap F (v.adicCompletion F) (a i) * x i ^ 2 = 0) :
    ∃ x : Fin 4 → F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  rw [isotropic_four_iff (ha 0)]
  have hα : -(a 0 * a 1) ≠ 0 := by simp [ha]
  have hβ : -(a 0 * a 2) ≠ 0 := by simp [ha]
  have hγ : a 0 * a 3 ≠ 0 := by simp [ha]
  have hr' := fun σ : F →+* ℝ =>
    (isotropic_four_iff (a := fun i => σ (a i)) (by simpa using ha 0)).1 (hr σ)
  have hf' := fun v : HeightOneSpectrum (𝓞 F) =>
    (isotropic_four_iff (a := fun i => algebraMap F (v.adicCompletion F) (a i))
      (by simpa using ha 0)).1 (hf v)
  simp only [← map_mul, ← map_neg] at hr' hf'
  generalize -(a 0 * a 1) = α at *
  generalize -(a 0 * a 2) = β at *
  generalize a 0 * a 3 = γ at *
  by_cases hs : IsSquare (α * β * γ)
  · obtain ⟨s, hs⟩ := hs
    obtain ⟨X, Y, h⟩ := exists_norm_over_extension H F F hα hβ hγ (s := s)
      (by rw [hs, sq]; rfl) hr' hf'
    refine ⟨X, Y, 1, 0, by simp, ?_⟩
    change β = X ^ 2 - α * Y ^ 2 at h
    linear_combination -h
  · have : Fact (∀ r : F, r ^ 2 ≠ α * β * γ + 0 * r) :=
      ⟨fun r h => hs ⟨r, by linear_combination -h⟩⟩
    let L := QuadraticAlgebra F (α * β * γ) 0
    have : NumberField L := NumberField.of_module_finite F L
    obtain ⟨X, Y, h⟩ := exists_norm_over_extension H F L hα hβ hγ (s := ⟨0, 1⟩)
      (by ext <;> simp [sq, L]) hr' hf'
    have h1 := congrArg QuadraticAlgebra.re h
    have h2 := congrArg QuadraticAlgebra.im h
    simp [sq, L] at h1 h2
    refine exists_quaternary_of_coordinates hα hβ (X₀ := X.re) (X₁ := X.im) (Y₀ := Y.re)
      (Y₁ := Y.im) (by linear_combination h1) ?_
    linear_combination (-1 / 2 : F) * h2

end GlobalTheory.LocalQuad

namespace GlobalTheory.LocalQuad

theorem exists_value_isSquare_div (F : Type) [Field F] [NumberField F] {a a' : F} (ha : a ≠ 0)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (p q : (v : T) → v.1.adicCompletion F)
    (hpq : ∀ v, algebraMap F _ a * p v ^ 2 + algebraMap F _ a' * q v ^ 2 ≠ 0)
    (p' q' : (F →+* ℝ) → ℝ) (hpq' : ∀ σ, σ a * p' σ ^ 2 + σ a' * q' σ ^ 2 ≠ 0) :
    ∃ x y : F, a * x ^ 2 + a' * y ^ 2 ≠ 0 ∧
      (∀ v : T, IsSquare (algebraMap F (v.1.adicCompletion F) (a * x ^ 2 + a' * y ^ 2) /
        (algebraMap F _ a * p v ^ 2 + algebraMap F _ a' * q v ^ 2))) ∧
      ∀ σ : F →+* ℝ, IsSquare (σ (a * x ^ 2 + a' * y ^ 2) / (σ a * p' σ ^ 2 + σ a' * q' σ ^ 2)) := by
  have hd := (denseRange_finite_real F T).prodMap (denseRange_finite_real F T)
  have h4 : ∀ v : T, Valued.v (4 : v.1.adicCompletion F) ≠ 0 := by
    intro v
    haveI : CharZero (v.1.adicCompletion F) :=
      charZero_of_injective_algebraMap (algebraMap F (v.1.adicCompletion F)).injective
    simp
  have h41 : ∀ v : T, Valued.v (4 : v.1.adicCompletion F) ≤ 1 := by
    intro v
    have h2 : Valued.v (1 + 1 : v.1.adicCompletion F) ≤ 1 :=
      Valuation.map_add_le _ (by simp) (by simp)
    rw [show (4 : v.1.adicCompletion F) = (1 + 1) * (1 + 1) by norm_num, map_mul]
    exact mul_le_one' h2 h2
  let U : Set ((((v : T) → v.1.adicCompletion F) × ((F →+* ℝ) → ℝ)) ×
      (((v : T) → v.1.adicCompletion F) × ((F →+* ℝ) → ℝ))) := (⋂ v : T, {z | Valued.v ((algebraMap F _ a * z.1.1 v ^ 2 +
      algebraMap F _ a' * z.2.1 v ^ 2) / (algebraMap F _ a * p v ^ 2 + algebraMap F _ a' * q v ^ 2) - 1)
        < Valued.v (4 : v.1.adicCompletion F)}) ∩
    ⋂ σ : F →+* ℝ, {z | 0 < (σ a * z.1.2 σ ^ 2 + σ a' * z.2.2 σ ^ 2) /
      (σ a * p' σ ^ 2 + σ a' * q' σ ^ 2)}
  have hU : IsOpen U := by
    refine IsOpen.inter (isOpen_iInter_of_finite fun v => ?_) (isOpen_iInter_of_finite fun σ => ?_)
    · have ho : IsOpen {u : v.1.adicCompletion F | Valued.v u < Valued.v (4 : v.1.adicCompletion F)} := by
        have := Valued.isOpen_ball (v.1.adicCompletion F) (Valued.v.restrict (4 : v.1.adicCompletion F))
        simpa only [Valuation.restrict_lt_iff] using this
      exact ho.preimage (f := fun z : (((v : T) → v.1.adicCompletion F) × ((F →+* ℝ) → ℝ)) ×
      (((v : T) → v.1.adicCompletion F) × ((F →+* ℝ) → ℝ)) => (algebraMap F _ a * z.1.1 v ^ 2 +
        algebraMap F _ a' * z.2.1 v ^ 2) /
          (algebraMap F _ a * p v ^ 2 + algebraMap F _ a' * q v ^ 2) - 1) (by fun_prop)
    · exact isOpen_lt continuous_const (by fun_prop)
  obtain ⟨⟨x, y⟩, hT, hR⟩ := hd.exists_mem_open hU ⟨((p, p'), (q, q')), by
    refine ⟨Set.mem_iInter.2 fun v => ?_, Set.mem_iInter.2 fun σ => ?_⟩
    · simp only [Set.mem_setOf_eq]
      rw [div_self (hpq v), sub_self, map_zero]
      exact zero_lt_iff.2 (h4 v)
    · simp only [Set.mem_setOf_eq]
      rw [div_self (hpq' σ)]
      exact one_pos⟩
  replace hT : ∀ v : T, Valued.v (algebraMap F (v.1.adicCompletion F) (a * x ^ 2 + a' * y ^ 2) /
      (algebraMap F _ a * p v ^ 2 + algebraMap F _ a' * q v ^ 2) - 1) <
        Valued.v (4 : v.1.adicCompletion F) := by
    intro v
    simp only [map_add (f := _), map_mul, map_pow]
    exact Set.mem_iInter.1 hT v
  replace hR : ∀ σ : F →+* ℝ,
      0 < σ (a * x ^ 2 + a' * y ^ 2) / (σ a * p' σ ^ 2 + σ a' * q' σ ^ 2) := by
    intro σ
    simp only [map_add (f := _), map_mul, map_pow]
    exact Set.mem_iInter.1 hR σ
  by_cases h0 : a * x ^ 2 + a' * y ^ 2 = 0
  · refine ⟨1, 0, by simpa using ha, fun v => ?_, fun σ => ?_⟩
    · have := (hT v).trans_le (h41 v)
      simp [h0] at this
    · have := hR σ
      simp [h0] at this
  · exact ⟨x, y, h0, fun v => isSquare_of_valued_sub_one_lt F v _ (hT v),
      fun σ => Real.isSquare_iff.2 (hR σ).le⟩

theorem finite_setOf_valued_ne_one (F : Type) [Field F] [NumberField F] {c : F} (hc : c ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) |
      Valued.v (algebraMap F (v.adicCompletion F) c) ≠ 1}.Finite := by
  have h := (FinitePlace.hasFiniteMulSupport hc).preimage
    (f := FinitePlace.equivHeightOneSpectrum.symm)
    (FinitePlace.equivHeightOneSpectrum (K := F)).symm.injective.injOn
  refine h.subset fun v hv => ?_
  simp only [Set.mem_preimage, Function.mem_mulSupport,
    FinitePlace.equivHeightOneSpectrum_symm_apply]
  intro h1
  exact hv (le_antisymm (Valued.toNormedField.norm_le_one_iff.1 h1.le)
    (Valued.toNormedField.one_le_norm_iff.1 h1.ge))

theorem isotropic_add_four (H : GlobalTheory.Published.HasseNormSt) (F : Type) [Field F] [NumberField F] (n : ℕ)
    (a : Fin (n + 4) → F) (ha : ∀ i, a i ≠ 0)
    (hr : ∀ σ : F →+* ℝ, ∃ x : Fin (n + 4) → ℝ, x ≠ 0 ∧ ∑ i, σ (a i) * x i ^ 2 = 0)
    (hf : ∀ v : HeightOneSpectrum (𝓞 F), ∃ x : Fin (n + 4) → v.adicCompletion F, x ≠ 0 ∧
      ∑ i, algebraMap F (v.adicCompletion F) (a i) * x i ^ 2 = 0) :
    ∃ x : Fin (n + 4) → F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  induction n with
  | zero => exact isotropic_four H F a ha hr hf
  | succ n ih =>
    classical
    have split : ∀ (k : Type) [Field k] (φ : F →+* k),
        (∃ x : Fin (n + 1 + 4) → k, x ≠ 0 ∧ ∑ i, φ (a i) * x i ^ 2 = 0) →
        ∃ x y : k, φ (a 0) * x ^ 2 + φ (a 1) * y ^ 2 ≠ 0 ∧
          ∀ μ : F, IsSquare (φ μ / (φ (a 0) * x ^ 2 + φ (a 1) * y ^ 2)) →
          ∃ x : Fin (n + 4) → k, x ≠ 0 ∧
            ∑ i, φ ((Fin.cons μ fun j : Fin (n + 3) => a j.succ.succ : Fin (n + 4) → F) i) * x i ^ 2
              = 0 := by
      rintro k _ φ ⟨x, hx, h⟩
      haveI : CharZero k := (RingHom.charZero_iff φ.injective).1 inferInstance
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at h
      obtain ⟨X, Y, hXY, H⟩ := exists_value_isotropic (a := φ (a 0)) (a' := φ (a 1))
        (b := fun j : Fin (n + 2 + 1) => φ (a j.succ.succ)) (by simpa using ha 0)
        (by simpa using ha 1) (by simpa using ha _) (x := x 0) (y := x 1)
        (z := fun j => x j.succ.succ) (by
          by_contra hc
          push Not at hc
          apply hx
          funext i
          refine Fin.cases hc.1 (fun j => Fin.cases hc.2.1 (fun l => congrFun hc.2.2 l) j) i) h
      refine ⟨X, Y, hXY, fun μ hμ => ?_⟩
      refine (isotropic_succ_iff (n := n + 3)).2 ?_
      simpa using H _ hμ
    let e : Fin 3 → Fin (n + 3) := Fin.natAdd n
    have hT := (finite_setOf_valued_ne_one F (two_ne_zero (α := F))).union
      (Set.finite_iUnion fun i : Fin 3 => finite_setOf_valued_ne_one F (ha (e i).succ.succ))
    choose p q hpq hp using fun v : hT.toFinset => split _ _ (hf v.1)
    choose p' q' hpq' hp' using fun σ : F →+* ℝ => split _ _ (hr σ)
    obtain ⟨x, y, h0, h1, h2⟩ := exists_value_isSquare_div F (a' := a 1) (ha 0) _ p q hpq p' q' hpq'
    obtain ⟨t, z, hz0, hz⟩ := (isotropic_succ_iff (n := n + 3)).1 (ih
      (Fin.cons (a 0 * x ^ 2 + a 1 * y ^ 2) fun j : Fin (n + 3) => a j.succ.succ)
      (fun i => Fin.cases h0 (fun j => ha _) i) (fun σ => hp' σ _ (h2 σ)) (fun v => by
        by_cases hv : v ∈ hT.toFinset
        · exact hp ⟨v, hv⟩ _ (h1 ⟨v, hv⟩)
        · simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion,
            not_or, not_exists, not_not] at hv
          refine isotropic_of_injective (fun i => (e i).succ)
            ((Fin.succ_injective _).comp (Fin.natAdd_injective _ _)) ?_
          exact isotropic_ternary_of_units F v (by simpa only [map_ofNat] using hv.1) _ hv.2))
    simp only [Fin.cons_zero, Fin.cons_succ] at hz
    refine (isotropic_succ_iff (n := n + 4)).2 ⟨x * t, Fin.cons (y * t) z, ?_, ?_⟩
    · by_contra hc
      push Not at hc
      obtain ⟨hx, hy⟩ := hc
      have hy0 : y * t = 0 := by simpa using congrFun hy 0
      rcases hz0 with ht | hz0
      · rw [mul_eq_zero_iff_right ht] at hx hy0
        simp [hx, hy0] at h0
      · exact hz0 (funext fun i => by simpa using congrFun hy i.succ)
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.succ_zero_eq_one]
      linear_combination hz

theorem isotropic_of_locally_isotropic (H : GlobalTheory.Published.HasseNormSt) (F : Type) [Field F]
    [NumberField F] {ι : Type*} [Fintype ι] (hι : 4 ≤ Fintype.card ι) (a : ι → F)
    (ha : ∀ i, a i ≠ 0)
    (hr : ∀ σ : F →+* ℝ, ∃ x : ι → ℝ, x ≠ 0 ∧ ∑ i, σ (a i) * x i ^ 2 = 0)
    (hf : ∀ v : HeightOneSpectrum (𝓞 F), ∃ x : ι → v.adicCompletion F, x ≠ 0 ∧
      ∑ i, algebraMap F (v.adicCompletion F) (a i) * x i ^ 2 = 0) :
    ∃ x : ι → F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le' hι
  let e : ι ≃ Fin (n + 4) := Fintype.equivFinOfCardEq hn
  refine isotropic_of_injective e.symm e.symm.injective
    (isotropic_add_four H F n _ (fun i => ha _) (fun σ => ?_) (fun v => ?_))
  · exact isotropic_of_injective e e.injective (by simpa using hr σ)
  · exact isotropic_of_injective e e.injective (by simpa only [e.symm_apply_apply] using hf v)

theorem isotropic_of_indefinite (H : GlobalTheory.Published.HasseNormSt) (F : Type) [Field F] [NumberField F]
    {ι : Type*} [Fintype ι] (a : ι → F) (hι : 5 ≤ Fintype.card ι) (ha : ∀ i, a i ≠ 0)
    (hr : ∀ σ : F →+* ℝ, ∃ i j, σ (a i) < 0 ∧ 0 < σ (a j)) :
    ∃ x : ι → F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 :=
  isotropic_of_locally_isotropic H F (by omega) a ha
    (fun σ => by
      obtain ⟨i, j, hi, hj⟩ := hr σ
      exact isotropic_real (a := fun i => σ (a i)) hi hj)
    (fun v => isotropic_adicCompletion_of_five_le F v hι _)

theorem landherr_of_hasseNormSt (H : GlobalTheory.Published.HasseNormSt) : GlobalTheory.Published.Landherr :=
  landherr_of_isotropy fun F _ _ _ _ a hι ha hr => isotropic_of_indefinite H F a hι ha hr


end GlobalTheory.LocalQuad
