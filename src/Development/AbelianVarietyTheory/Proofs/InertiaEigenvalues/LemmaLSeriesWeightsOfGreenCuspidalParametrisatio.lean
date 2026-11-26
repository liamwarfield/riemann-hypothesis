module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCompatibleConjugationRepresentation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhIUnionTrans
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FirstComponentsBasisLocalLatticeSplit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceUnitriangularColumnVanishingIdempotentEqSum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeGaloisTrivialModUniformizer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraTracePatternIdempotentExchange

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraTracePatternIdempotentExchangeStatement
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupAlgebraTrace_patternIdempotent_exchange : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (N k s : ℕ), N = k + 2 * s + 1 → ∀ χ : Gn g N → ℂ, IsClass χ → tr (eJ g N k s ψ) χ = tr (eJ' g N k ψ) χ := by
  first | exact @GlobalTheory.GLq.tr_eJ_eq_tr_eJ' | exact GlobalTheory.GLq.tr_eJ_eq_tr_eJ' | (intros; apply GlobalTheory.GLq.tr_eJ_eq_tr_eJ' <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesWeightSquarefreeLabelGelfandG
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesWeightSquarefreeLabelGelfandG
namespace ProductIntervalSplit
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace CompanionTheory.Member.UnipotentCardinalityCoefficients

variable {g : ℕ} [Fact g.Prime]

theorem uni_one {N : ℕ} : IsUniUp (1 : Mt g N) := by
  intro a b
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact Matrix.one_apply_ne (ne_of_gt h)
  · subst h
    exact Matrix.one_apply_eq a

theorem entN_one {N : ℕ} (i j : ℕ) (h : i < j) : entN (1 : Mt g N) i j = 0 := by
  unfold entN
  split_ifs with hij
  · apply Matrix.one_apply_ne
    intro he
    have := congrArg Fin.val he
    simp only at this
    omega
  · rfl

private theorem card_filter_Gn_eq_card_filter_Mt_of_unipotent {N : ℕ} (P : Mt g N → Prop) (hU : ∀ M, P M → IsUniUp M) :
    (Finset.univ.filter fun u : Gn g N => P (u : Mt g N)).card =
      (Finset.univ.filter fun M : Mt g N => P M).card := by
  apply Finset.card_bij (fun (u : Gn g N) _ => u.1)
  · intro u hu
    simpa using hu
  · intro u _ v _ h
    exact Units.ext h
  · intro M hM
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
    have hdet : M.det = 1 := by
      rw [Matrix.det_of_isUpperTriangular (fun i j hij => ((hU M hM) i j).1 hij)]
      exact Finset.prod_eq_one fun i _ => ((hU M hM) i i).2 rfl
    have hu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (by rw [hdet]; exact isUnit_one)
    exact ⟨hu.unit, by simpa using hM, rfl⟩

private theorem card_filter_unipotent_eq_pow_card_free {N : ℕ} (Q : Fin N × Fin N → Prop) (P : Mt g N → Prop)
    (hP : ∀ M, P M ↔ IsUniUp M ∧ ∀ p : Fin N × Fin N, p.1 < p.2 → Q p → M p.1 p.2 = 0) :
    (Finset.univ.filter fun M : Mt g N => P M).card =
      g ^ (Finset.univ.filter fun p : Fin N × Fin N => p.1 < p.2 ∧ ¬ Q p).card := by
  set s := Finset.univ.filter fun p : Fin N × Fin N => p.1 < p.2 ∧ ¬ Q p with hs
  have hmem : ∀ p, p ∈ s ↔ p.1 < p.2 ∧ ¬ Q p := fun p => by simp [s]
  let e : {M : Mt g N // P M} ≃ (s → ZMod g) :=
    { toFun := fun M p => M.1 p.1.1 p.1.2
      invFun := fun v => ⟨Matrix.of fun i j => if i = j then 1 else if h : (i, j) ∈ s then v ⟨(i, j), h⟩ else 0, by
        refine (hP _).2 ⟨fun a b => ⟨fun hab => ?_, fun hab => ?_⟩, fun p hp hq => ?_⟩
        · have h1 : a ≠ b := ne_of_gt hab
          have h2 : (a, b) ∉ s := by
            rw [hmem]
            intro h
            exact absurd (lt_trans h.1 hab) (lt_irrefl _)
          simp [Matrix.of_apply, h1, h2]
        · simp [Matrix.of_apply, hab]
        · have h1 : p.1 ≠ p.2 := ne_of_lt hp
          have h2 : (p.1, p.2) ∉ s := by
            rw [hmem]
            exact fun h => h.2 hq
          simp [Matrix.of_apply, h1, h2]⟩
      left_inv := fun M => by
        apply Subtype.ext
        ext i j
        obtain ⟨hU, hZ⟩ := (hP M.1).1 M.2
        by_cases hij : i = j
        · subst hij
          simp [Matrix.of_apply, (hU i i).2 rfl]
        · by_cases hin : (i, j) ∈ s
          · simp [Matrix.of_apply, hij, hin]
          · simp only [Matrix.of_apply, hij, hin, if_false, dif_neg, not_false_eq_true]
            rcases lt_or_gt_of_ne hij with hlt | hgt
            · have hq : Q (i, j) := by
                by_contra hq
                exact hin ((hmem _).2 ⟨hlt, hq⟩)
              exact (hZ (i, j) hlt hq).symm
            · exact ((hU i j).1 hgt).symm
      right_inv := fun v => by
        funext p
        have hp := (hmem p.1).1 p.2
        have h1 : p.1.1 ≠ p.1.2 := ne_of_lt hp.1
        simp [Matrix.of_apply, h1, p.2] }
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fun, ZMod.card, Fintype.card_coe]

theorem card_uni {N : ℕ} (Q : Fin N × Fin N → Prop) (P : Mt g N → Prop)
    (hP : ∀ M, P M ↔ IsUniUp M ∧ ∀ p : Fin N × Fin N, p.1 < p.2 → Q p → M p.1 p.2 = 0) :
    (Finset.univ.filter fun u : Gn g N => P (u : Mt g N)).card =
      g ^ (Finset.univ.filter fun p : Fin N × Fin N => p.1 < p.2 ∧ ¬ Q p).card := by
  rw [card_filter_Gn_eq_card_filter_Mt_of_unipotent P (fun M hM => ((hP M).1 hM).1), card_filter_unipotent_eq_pow_card_free Q P hP]

theorem card_lt (N : ℕ) :
    (Finset.univ.filter fun p : Fin N × Fin N => p.1 < p.2).card = N * (N - 1) / 2 := by
  rw [Finset.card_filter, Fintype.sum_prod_type_right]
  have h : ∀ j : Fin N, (∑ i : Fin N, if i < j then 1 else 0) = (j : ℕ) := by
    intro j
    rw [← Finset.card_filter]
    simp_rw [Fin.lt_def]
    rw [Fin.card_filter_val_lt]
    exact min_eq_right j.2.le
  simp only [h]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id]

private theorem card_unipotent_upper_eq_pow' (N : ℕ) :
    (Finset.univ.filter fun u : Gn g N => IsUniUp (u : Mt g N)).card = g ^ (N * (N - 1) / 2) := by
  have h := card_uni (g := g) (N := N) (fun _ => False) IsUniUp (fun M => by simp)
  simp only [not_false_eq_true, and_true, card_lt] at h
  exact h

theorem eU_coeff_one (N : ℕ) (ψ : AddChar (ZMod g) ℂ) :
    (eU g N ψ).coeff 1 = ((g : ℂ) ^ (N * (N - 1) / 2))⁻¹ := by
  have hφ : (∑ i ∈ Finset.range (N - 1), entN (1 : Mt g N) i (i + 1)) = 0 :=
    Finset.sum_eq_zero fun i _ => entN_one i (i + 1) (Nat.lt_succ_self i)
  have h1 : (1 : Gn g N) ∈ Finset.univ.filter fun u : Gn g N => IsUniUp (u : Mt g N) := by
    simpa using (uni_one : IsUniUp (1 : Mt g N))
  unfold eU eDat
  simp only [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single,
    Finsupp.smul_apply, Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [Finset.sum_ite_eq_of_mem' _ _ _ h1]
  simp [hφ, card_unipotent_upper_eq_pow']

theorem wh_zero (ψ : AddChar (ZMod g) ℂ) : wh ψ (fun _ : Gn g 0 => (1 : ℂ)) = 1 := by
  unfold wh tr
  rw [Finset.sum_eq_single (1 : Gn g 0)]
  · rw [eU_coeff_one]
    simp
  · intro b _ hb
    exact absurd (Units.ext (Subsingleton.elim _ _)) hb
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem isClass_mul_right {G : Type} [Group G] {α : G → ℂ} (h : IsClass α) (c : ℂ) :
    IsClass fun x => α x * c := by
  intro x y
  show α (y * x * y⁻¹) * c = α x * c
  rw [h x y]

theorem isClass_mul_left {G : Type} [Group G] {α : G → ℂ} (h : IsClass α) (c : ℂ) :
    IsClass fun x => c * α x := by
  intro x y
  show c * α (y * x * y⁻¹) = c * α x
  rw [h x y]

theorem isChar_of_irr {G : Type} [Group G] {α : G → ℂ} (h : IsIrr α) : IsChar α := by
  obtain ⟨V, -, hV⟩ := h
  exact ⟨V, hV⟩

theorem wh_mul_left (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (α : Gn g n → ℂ) (c : ℂ) :
    wh ψ (fun x => c * α x) = c * wh ψ α := by
  unfold wh tr
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

theorem wh_hcL (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (L : List (Pc g))
    (hL : ∀ p ∈ L, IsChar p.2 ∧ wh ψ p.2 = 1) : wh ψ (hcL L (degL L)) = 1 := by
  induction L with
  | nil =>
    rw [hcL_nil]
    exact wh_zero ψ
  | cons p L ih =>
    have hp := hL p (List.mem_cons.2 (Or.inl rfl))
    have hrest : ∀ q ∈ L, IsChar q.2 ∧ wh ψ q.2 = 1 := fun q hq => hL q (List.mem_cons.2 (Or.inr hq))
    have ihL := ih hrest
    have hdeg : degL (p :: L) = p.1 + degL L := by simp [degL]
    have hclassL : IsClass (hcL L (degL L)) :=
      GlobalTheory.CharDec.isClass_of_isChar (GlobalTheory.GLqPerm.isChar_hcL L fun q hq => (hrest q hq).1)
    have hclassp : IsClass p.2 := GlobalTheory.CharDec.isClass_of_isChar hp.1
    rw [hcL_cons]
    unfold hc
    rw [GlobalTheory.GLq.WhMul.wh_hcT g ψ hψ p.1 (degL L) (degL (p :: L)) hdeg _
      (fun y => isClass_mul_right hclassp _) (fun x => isClass_mul_left hclassL _)]
    simp only [wh_mul_left, ihL, mul_one]
    exact hp.2

theorem prod_Icc_ne (n : ℕ) : ∏ i ∈ Finset.Icc 1 n, ((g : ℂ) ^ i - 1) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
  have hg : 2 ≤ g := (Fact.out : g.Prime).two_le
  have hlt : 1 < g ^ i := Nat.one_lt_pow (by omega) (by omega)
  intro h
  have h' : ((g ^ i : ℕ) : ℂ) = 1 := by
    push_cast
    linear_combination h
  norm_cast at h'
  omega

theorem card_Gn (n : ℕ) : (Fintype.card (Gn g n) : ℂ) =
    (g : ℂ) ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 1 n, ((g : ℂ) ^ i - 1) := by
  rw [GlobalTheory.GLq.HcDeg.card_GL_C, Finset.prod_pow_eq_pow_sum, Finset.sum_range_id]

theorem list_prod_split (L : List (Pc g))
    (hL : ∀ p ∈ L, 0 < p.1 ∧ p.2 1 = ∏ i ∈ Finset.Ico 1 p.1, ((g : ℂ) ^ i - 1)) :
    (L.map fun p => ∏ i ∈ Finset.Icc 1 p.1, ((g : ℂ) ^ i - 1)).prod =
      (L.map fun p => p.2 1).prod * (L.map fun p => (g : ℂ) ^ p.1 - 1).prod := by
  induction L with
  | nil => simp
  | cons p L ih =>
    have hp := hL p (List.mem_cons.2 (Or.inl rfl))
    have ih' := ih fun q hq => hL q (List.mem_cons.2 (Or.inr hq))
    simp only [List.map_cons, List.prod_cons, ih']
    have hsplit : ∏ i ∈ Finset.Icc 1 p.1, ((g : ℂ) ^ i - 1) =
        (∏ i ∈ Finset.Ico 1 p.1, ((g : ℂ) ^ i - 1)) * ((g : ℂ) ^ p.1 - 1) := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_succ_top (by omega : 1 ≤ p.1)]
    rw [hsplit, ← hp.2]
    ring

private theorem prod_pow_natDegree_sub_one_cast_eq (Q : List ((ZMod g)[X] × Pc g))
    (hQ : ∀ q ∈ Q, q.1.natDegree = q.2.1) :
    ((((Q.map Prod.fst).map fun P => (g : ℝ) ^ P.natDegree - 1).prod : ℝ) : ℂ) =
      ((Q.map Prod.snd).map fun p => (g : ℂ) ^ p.1 - 1).prod := by
  induction Q with
  | nil => simp
  | cons q Q ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [Complex.ofReal_mul, ih fun r hr => hQ r (List.mem_cons.2 (Or.inr hr)),
      hQ q (List.mem_cons.2 (Or.inl rfl))]
    push_cast
    ring

end CompanionTheory.Member.UnipotentCardinalityCoefficients

open CompanionTheory.Member.UnipotentCardinalityCoefficients in
theorem CompanionTheory.Member.harishChandraSeriesWeight_squarefree_label_unipotent : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → Green → ∀ (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (n : ℕ) (f : (ZMod g)[X]), f.Monic → f.natDegree = n → f.coeff 0 ≠ 0 → Squarefree f → wtC L (eU g n ψ) f = 1 / ((UniqueFactorizationMonoid.normalizedFactors f).map (fun P => (g : ℝ) ^ P.natDegree - 1)).prod := by
  intro g _ L hg hG ψ hψ n f hm hn h0 hs
  obtain ⟨Q, hQ, hfac, hdeg, hset⟩ := (GlobalTheory.GLq.Label.label_main g L hg hG n).2.2 f hm hn h0 hs
  subst hdeg
  set C := hcL (Q.map Prod.snd) (degL (Q.map Prod.snd)) with hC
  have hcusp : ∀ c ∈ Q.map Prod.snd,
      IsCusp c.2 ∧ c.2 1 = ∏ i ∈ Finset.Ico 1 c.1, ((g : ℂ) ^ i - 1) := by
    intro c hc
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hc
    exact ⟨(hQ q hq).1.2.1, (hQ q hq).2⟩
  have hwh : wh ψ C = 1 := wh_hcL ψ hψ _ fun c hc =>
    ⟨isChar_of_irr (hcusp c hc).1.2.1,
      GlobalTheory.GLq.wh_cusp_eq_one g ψ hψ c.1 c.2 (hcusp c hc).1 (hcusp c hc).2⟩
  have hser : eSerC L (degL (Q.map Prod.snd)) f = zOf C := by
    unfold eSerC
    rw [hset, finsum_mem_singleton]
  have hcoef : (eU g _ ψ * zOf C).coeff 1 = C 1 / (Fintype.card (Gn g (degL (Q.map Prod.snd))) : ℂ) * wh ψ C :=
    (GlobalTheory.GLq.trIdem (Gn g _) (eU g _ ψ) C).2.2
  have hdeg1 := GlobalTheory.GLq.HcDeg.hc_degree g (Q.map Prod.snd) _ rfl
  rw [list_prod_split _ fun c hc => ⟨(hcusp c hc).1.1, (hcusp c hc).2⟩] at hdeg1
  have hA : ((Q.map Prod.snd).map fun p => p.2 1).prod ≠ 0 := by
    refine List.prod_ne_zero ?_
    intro h0'
    obtain ⟨c, hc, hc0⟩ := List.mem_map.1 h0'
    rw [(hcusp c hc).2] at hc0
    exact GlobalTheory.GLq.green_deg_ne_zero (g := g) c.1 hc0
  have hI : ∏ i ∈ Finset.Icc 1 (degL (Q.map Prod.snd)), ((g : ℂ) ^ i - 1) ≠ 0 := prod_Icc_ne _
  have hBR := prod_pow_natDegree_sub_one_cast_eq Q fun q hq => (hQ q hq).1.1.2.2.2
  set B := ((Q.map Prod.snd).map fun p => (g : ℂ) ^ p.1 - 1).prod with hBdef
  have hB : B ≠ 0 := by
    intro h
    rw [h, mul_zero, mul_zero] at hdeg1
    exact mul_ne_zero hI hA hdeg1.symm
  have hC1 : C 1 = (∏ i ∈ Finset.Icc 1 (degL (Q.map Prod.snd)), ((g : ℂ) ^ i - 1)) / B := by
    rw [eq_div_iff hB]
    apply mul_right_cancel₀ hA
    linear_combination hdeg1
  unfold wtC
  rw [hser, hcoef, hwh, eU_coeff_one, card_Gn, hC1, ← hBR, ← hfac, Multiset.map_coe, Multiset.prod_coe]
  set R := ((Q.map Prod.fst).map fun P => (g : ℝ) ^ P.natDegree - 1).prod with hRdef
  have hR : R ≠ 0 := by
    intro h
    apply hB
    rw [← hBR, h, Complex.ofReal_zero]
  have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : g.Prime).ne_zero
  set k := degL (Q.map Prod.snd) * (degL (Q.map Prod.snd) - 1) / 2
  have key : (∏ i ∈ Finset.Icc 1 (degL (Q.map Prod.snd)), ((g : ℂ) ^ i - 1)) / (R : ℂ) /
      ((g : ℂ) ^ k * ∏ i ∈ Finset.Icc 1 (degL (Q.map Prod.snd)), ((g : ℂ) ^ i - 1)) * 1 =
        ((1 / ((g : ℝ) ^ k * R) : ℝ) : ℂ) := by
    have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR
    have hg' : (g : ℂ) ≠ 0 := by exact_mod_cast hg0
    push_cast
    field_simp
  have key2 : ((g : ℂ) ^ k)⁻¹ = ((((g : ℝ) ^ k)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [key, key2, Complex.ofReal_re, Complex.ofReal_re]
  field_simp

end

end ProductIntervalSplit
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
theorem _root_.GlobalTheory.Adopt.harishChandraSeriesWeight_squarefree_label_gelfandGraev : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → Green → ∀ (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (n : ℕ) (f : (ZMod g)[X]), f.Monic → f.natDegree = n → f.coeff 0 ≠ 0 → Squarefree f → wtC L (eU g n ψ) f = 1 / ((UniqueFactorizationMonoid.normalizedFactors f).map (fun P => (g : ℝ) ^ P.natDegree - 1)).prod := by
  exact ProductIntervalSplit.CompanionTheory.Member.harishChandraSeriesWeight_squarefree_label_unipotent

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesWeightSquarefreeLabelGelfandGStatement
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraSeriesWeight_squarefree_label_gelfandGraev : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → Green → ∀ (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (n : ℕ) (f : (ZMod g)[X]), f.Monic → f.natDegree = n → f.coeff 0 ≠ 0 → Squarefree f → wtC L (eU g n ψ) f = 1 / ((UniqueFactorizationMonoid.normalizedFactors f).map (fun P => (g : ℝ) ^ P.natDegree - 1)).prod := by
  first | exact @GlobalTheory.Adopt.harishChandraSeriesWeight_squarefree_label_gelfandGraev | exact GlobalTheory.Adopt.harishChandraSeriesWeight_squarefree_label_gelfandGraev | (intros; apply GlobalTheory.Adopt.harishChandraSeriesWeight_squarefree_label_gelfandGraev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesWeightLeSquarefree
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BernsteinZelevinskyDerivativeHarishChandraProducStatement
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bernsteinZelevinskyDerivative_harishChandraProduct : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (L : List (Pc g)) (n i : ℕ), degL L = n → i ≤ n → (∀ p ∈ L, IsCusp p.2 ∧ wh ψ p.2 = 1) → wh ψ (der ψ i (hcL L n)) = (((Finset.univ : Finset (Finset (Fin L.length))).filter (fun I => ∑ j ∈ I, (L.get j).1 = i)).card : ℂ) ∧ wh ψ (hcL L n) = 1 := by
  first | exact @GlobalTheory.GLq.Leibniz.main | exact GlobalTheory.GLq.Leibniz.main | (intros; apply GlobalTheory.GLq.Leibniz.main <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesWeightLeSquarefree
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

noncomputable section
namespace GlobalTheory.GLq.UpperWeight

def cnt {g : ℕ} (L : List (Pc g)) (i : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin L.length))).filter (fun I => ∑ j ∈ I, (L.get j).1 = i)).card

theorem sum_get_fst {g : ℕ} (L : List (Pc g)) : ∑ j : Fin L.length, (L.get j).1 = degL L := by
  induction L with
  | nil => simp [degL]
  | cons a L ih =>
    show ∑ j : Fin (L.length + 1), ((a :: L).get j).1 = _
    rw [Fin.sum_univ_succ]
    simp only [List.length_cons, List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, Fin.val_succ,
      List.getElem_cons_succ] at ih ⊢
    rw [ih]; simp [degL]

theorem comb_bound {g : ℕ} (L : List (Pc g)) (hg : 1 ≤ g) (hpos : ∀ p ∈ L, 0 < p.1) (k : ℕ) :
    (∑ i ∈ Finset.range k, (cnt L i : ℝ) * ((g : ℝ) ^ (k - i) - (g : ℝ) ^ (k - i - 1))) + cnt L k
      ≤ (1 + 1 / (g : ℝ)) ^ (degL L) * (g : ℝ) ^ k := by
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg
  set w : Finset (Fin L.length) → ℕ := fun I => ∑ j ∈ I, (L.get j).1 with hw
  set x : ℝ := 1 / (g : ℝ) with hx
  have hx0 : 0 ≤ x := by positivity

  have h1 : (∑ i ∈ Finset.range k, (cnt L i : ℝ) * ((g : ℝ) ^ (k - i) - (g : ℝ) ^ (k - i - 1))) + cnt L k
      ≤ ∑ i ∈ Finset.range (k + 1), (cnt L i : ℝ) * (g : ℝ) ^ (k - i) := by
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one]
    have hs : ∑ i ∈ Finset.range k, (cnt L i : ℝ) * ((g : ℝ) ^ (k - i) - (g : ℝ) ^ (k - i - 1))
        ≤ ∑ i ∈ Finset.range k, (cnt L i : ℝ) * (g : ℝ) ^ (k - i) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have : (0 : ℝ) ≤ (g : ℝ) ^ (k - i - 1) := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg (cnt L i))
    linarith

  have h2 : ∑ i ∈ Finset.range (k + 1), (cnt L i : ℝ) * (g : ℝ) ^ (k - i)
      = ∑ I : Finset (Fin L.length), if w I ≤ k then (g : ℝ) ^ (k - w I) else 0 := by
    have : ∀ i, (cnt L i : ℝ) = ∑ I : Finset (Fin L.length), if w I = i then (1 : ℝ) else 0 := by
      intro i
      simp only [cnt, Finset.sum_boole, hw]
    simp_rw [this, Finset.sum_mul, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_range, Nat.lt_succ_iff]

  have h3 : ∀ I : Finset (Fin L.length), (if w I ≤ k then (g : ℝ) ^ (k - w I) else 0) ≤ (g : ℝ) ^ k * x ^ w I := by
    intro I
    split_ifs with h
    · rw [pow_sub₀ _ hg0.ne' h, hx, one_div_pow, one_div]
    · positivity

  have h4 : ∑ I : Finset (Fin L.length), x ^ w I = ∏ j : Fin L.length, (1 + x ^ (L.get j).1) := by
    rw [Finset.prod_one_add, Finset.powerset_univ]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [hw, Finset.prod_pow_eq_pow_sum]
  have h5 : ∏ j : Fin L.length, (1 + x ^ (L.get j).1) ≤ (1 + x) ^ degL L := by
    rw [← sum_get_fst, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod₀ (fun j _ => by positivity) fun j _ => ?_
    have hj : 0 < (L.get j).1 := hpos _ (List.get_mem L j)
    have := pow_add_pow_le (zero_le_one' ℝ) hx0 hj.ne'
    simpa using this
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ ∑ I : Finset (Fin L.length), (g : ℝ) ^ k * x ^ w I := Finset.sum_le_sum fun I _ => h3 I
    _ = (g : ℝ) ^ k * ∏ j : Fin L.length, (1 + x ^ (L.get j).1) := by rw [← Finset.mul_sum, h4]
    _ ≤ (g : ℝ) ^ k * (1 + x) ^ degL L := by gcongr
    _ = _ := by rw [mul_comm]

theorem isClass_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsClass χ := by
  obtain ⟨V, -, hV⟩ := h
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

theorem wtC_eJ_le : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → Green → ∀ (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 →
    ∀ (N k s : ℕ), N = k + 2 * s + 1 → 1 ≤ k → ∀ f : (ZMod g)[X], f.Monic → f.natDegree = N → f.coeff 0 ≠ 0 →
    Squarefree f → wtC L (eJ g N k s ψ) f ≤ (1 + 1 / (g : ℝ)) ^ N * wtC L (eU g N ψ) f := by
  intro g _ L hg hG ψ hψ N k s hN hk f hm hd hc hsq
  obtain ⟨Q, hQ, -, hdeg, hset⟩ := (GlobalTheory.T.harishChandraSeriesLabel_exists_unique_GLn g L hg hG N).2.2 f hm hd hc hsq
  set τ := hcL (Q.map Prod.snd) N with hτ
  have hser : eSerC L N f = zOf τ := by
    unfold eSerC; rw [hset, finsum_mem_singleton]
  have hirr : IsIrr τ := by
    have : τ ∈ {χ : Gn g N → ℂ | IsIrr χ ∧ HasLabel L χ f} := by rw [hset]; rfl
    exact this.1
  have hcl := isClass_of_isIrr hirr
  obtain ⟨d, hdpos, hd1⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree (Gn g N) (eU g N ψ) τ).2.1 hirr
  have hL : ∀ p ∈ Q.map Prod.snd, IsCusp p.2 ∧ wh ψ p.2 = 1 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact ⟨(hQ q hq).1.2.1, GlobalTheory.T.whittakerDimension_cuspidal_greenDegree_eq_one g ψ hψ _ _ (hQ q hq).1.2.1 (hQ q hq).2⟩
  have hlb := fun i (hi : i ≤ N) => GlobalTheory.T.bernsteinZelevinskyDerivative_harishChandraProduct g ψ hψ (Q.map Prod.snd) N i hdeg hi hL
  have hwhU : tr (eU g N ψ) τ = 1 := (hlb 0 (Nat.zero_le _)).2
  have hkN : k < N := by omega
  set TR : ℝ := (∑ i ∈ Finset.range k, (cnt (Q.map Prod.snd) i : ℝ) * ((g : ℝ) ^ (k - i) - (g : ℝ) ^ (k - i - 1)))
    + cnt (Q.map Prod.snd) k with hTR
  have hJ : tr (eJ g N k s ψ) τ = (TR : ℂ) := by
    rw [GlobalTheory.T.groupAlgebraTrace_patternIdempotent_exchange g ψ hψ N k s hN τ hcl, GlobalTheory.T.trace_unitriangularColumnVanishingIdempotent_eq_sum_derivatives g ψ hψ N k hk hkN τ hcl, (hlb k hkN.le).1, hTR]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(hlb i (by simp at hi; omega)).1]
    rfl
  obtain ⟨-, hU1, hJ', -⟩ := GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g N k s ψ
  obtain ⟨-, hJ1⟩ := hJ' hN
  have hb := comb_bound (Q.map Prod.snd) (by omega) (fun p hp => (hL p hp).1.1) k
  rw [hdeg] at hb
  unfold wtC
  rw [hser, (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree _ (eJ g N k s ψ) τ).2.2, (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree _ (eU g N ψ) τ).2.2, hwhU, hJ, hJ1, hU1, hd1]
  set M := N * (N - 1) / 2
  set a : ℝ := (d : ℝ) / (Fintype.card (Gn g N) : ℝ) with ha
  set m : ℝ := ((g : ℝ) ^ M)⁻¹ with hm'
  have e1 : (d : ℂ) / (Fintype.card (Gn g N) : ℂ) * (TR : ℂ) = ((a * TR : ℝ) : ℂ) := by rw [ha]; push_cast; ring
  have e2 : (d : ℂ) / (Fintype.card (Gn g N) : ℂ) * 1 = ((a : ℝ) : ℂ) := by rw [ha]; push_cast; ring
  have e3 : (g : ℂ) ^ k * ((g : ℂ) ^ M)⁻¹ = (((g : ℝ) ^ k * m : ℝ) : ℂ) := by rw [hm']; push_cast; ring
  have e4 : ((g : ℂ) ^ M)⁻¹ = ((m : ℝ) : ℂ) := by rw [hm']; push_cast; ring
  rw [e1, e2, e3, e4, Complex.ofReal_re, Complex.ofReal_re, Complex.ofReal_re, Complex.ofReal_re]
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hgk : (0 : ℝ) < (g : ℝ) ^ k := by positivity
  have hm0 : 0 < m := by rw [hm']; positivity
  have ha0 : 0 < a := by
    rw [ha]; apply div_pos (by exact_mod_cast hdpos); exact_mod_cast Fintype.card_pos
  have hT : TR / (g : ℝ) ^ k ≤ (1 + 1 / (g : ℝ)) ^ N := by rw [div_le_iff₀ hgk]; exact hb
  calc a * TR / ((g : ℝ) ^ k * m) = (a / m) * (TR / (g : ℝ) ^ k) := by rw [div_mul_div_comm, mul_comm ((g : ℝ) ^ k) m]
    _ ≤ (a / m) * (1 + 1 / (g : ℝ)) ^ N := mul_le_mul_of_nonneg_left hT (by positivity)
    _ = (1 + 1 / (g : ℝ)) ^ N * (a / m) := by ring

end GlobalTheory.GLq.UpperWeight
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesWeightLeSquarefreeStatement
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraSeriesWeight_le_squarefree : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → Green → ∀ (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (N k s : ℕ), N = k + 2 * s + 1 → 1 ≤ k → ∀ f : (ZMod g)[X], f.Monic → f.natDegree = N → f.coeff 0 ≠ 0 → Squarefree f → wtC L (eJ g N k s ψ) f ≤ (1 + 1 / (g : ℝ)) ^ N * wtC L (eU g N ψ) f := by
  first | exact @GlobalTheory.GLq.UpperWeight.wtC_eJ_le | exact GlobalTheory.GLq.UpperWeight.wtC_eJ_le | (intros; apply GlobalTheory.GLq.UpperWeight.wtC_eJ_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesWeightLowerComparison
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicTraceGeWhittakerDimensionGLn
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicTraceGeWhittakerDimensionGLn
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.MirabolicComparison

theorem tr_add {G : Type} [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (f h : G → ℂ) :
    tr a (fun x => f x + h x) = tr a f + tr a h := by
  simp [tr, mul_add, Finset.sum_add_distrib]

theorem tr_mul_const {G : Type} [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (f : G → ℂ) (c : ℂ) :
    tr a (fun x => f x * c) = tr a f * c := by
  simp only [tr, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem tr_tr_list_nat {G H : Type} [Group G] [Fintype G] [Group H] [Fintype H]
    (a : MonoidAlgebra ℂ G) (b : MonoidAlgebra ℂ H) (ha : a * a = a) (hb : b * b = b) :
    ∀ L : List ((G → ℂ) × (H → ℂ)), (∀ p ∈ L, IsChar p.1 ∧ IsChar p.2) →
      ∃ n : ℕ, tr a (fun x => tr b (fun y => (L.map fun p => p.1 x * p.2 y).sum)) = n := by
  intro L
  induction L with
  | nil =>
    intro _
    exact ⟨0, by simp [tr]⟩
  | cons p L ih =>
    intro hL
    obtain ⟨m, hm⟩ := ih (fun q hq => hL q (List.mem_cons_of_mem _ hq))
    obtain ⟨n₁, hn₁⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree G a p.1).1 ha (hL p (List.mem_cons_self ..)).1
    obtain ⟨n₂, hn₂⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree H b p.2).1 hb (hL p (List.mem_cons_self ..)).2
    refine ⟨n₁ * n₂ + m, ?_⟩
    simp only [List.map_cons, List.sum_cons]
    rw [show (fun x => tr b (fun y => p.1 x * p.2 y + (L.map fun p => p.1 x * p.2 y).sum)) =
        (fun x => p.1 x * tr b p.2 + tr b (fun y => (L.map fun p => p.1 x * p.2 y).sum)) from by
      funext x
      rw [tr_add]
      congr 1
      simp only [tr, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring]
    rw [tr_add, tr_mul_const, hm, hn₁, hn₂]
    push_cast
    ring

end GlobalTheory.GLq.MirabolicComparison

namespace GlobalTheory.GLq.MirabolicComparison

theorem isClass_of_isChar {G : Type} [Group G] {χ : G → ℂ} (h : IsChar χ) : IsClass χ := by
  obtain ⟨V, hV⟩ := h
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

theorem isChar_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsChar χ := by
  obtain ⟨V, _, hV⟩ := h
  exact ⟨V, hV⟩

theorem wh_der_nat (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (N i : ℕ) (hi : i ≤ N)
    (χ : Gn g N → ℂ) (hχ : IsChar χ) : ∃ n : ℕ, wh ψ (der ψ i χ) = n := by
  obtain ⟨L, hL, hLeq⟩ := (GlobalTheory.T.harishChandra_induction_character_restriction_decomp g i (N - i) N (by omega)).2 χ hχ
  have hres : (fun h : Gn g i => wh ψ (res i (N - i) χ h)) =
      fun h => tr (eU g (N - i) ψ) (fun y => (L.map fun p => p.1 h * p.2 y).sum) := by
    funext h
    simp only [wh]
    congr 1
    funext y
    exact hLeq h y
  show ∃ n : ℕ, tr (eU g i ψ) (fun h => wh ψ (res i (N - i) χ h)) = n
  rw [hres]
  exact tr_tr_list_nat _ _ (GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g i 0 0 ψ).1 (GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g (N - i) 0 0 ψ).1 L
    (fun p hp => ⟨isChar_of_isIrr (hL p hp).1, isChar_of_isIrr (hL p hp).2⟩)

theorem wh_der_zero (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (N : ℕ) (χ : Gn g N → ℂ) :
    wh ψ (der ψ 0 χ) = wh ψ χ := by
  haveI : Subsingleton (Gn g 0) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
  have h1 : (eU g 0 ψ).coeff 1 = 1 := by
    rw [(GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g 0 0 0 ψ).2.1]; simp
  have hres : res 0 (N - 0) χ 1 = χ := by
    funext y
    change Gn g N at y
    simp only [res, Nat.zero_mul, pow_zero, inv_one, one_mul]
    rw [Finset.sum_eq_single y]
    · have : InPar 0 ((y : Gn g N) : Mt g N) ∧ tl 0 ((y : Gn g N) : Mt g N) = ((1 : Gn g 0) : Mt g 0) ∧
          br 0 (N - 0) ((y : Gn g N) : Mt g N) = ((y : Gn g (N - 0)) : Mt g (N - 0)) := by
        refine ⟨fun i j hj _ => absurd hj (Nat.not_lt_zero _), Subsingleton.elim _ _, ?_⟩
        funext i j
        simp [br, entN]
      rw [if_pos this]
    · intro x _ hx
      rw [if_neg]
      rintro ⟨_, _, hb⟩
      apply hx
      apply Units.ext
      rw [← hb]
      funext i j
      simp [br, entN]
    · intro h; exact absurd (Finset.mem_univ _) h
  show tr (eU g 0 ψ) (fun h => wh ψ (res 0 (N - 0) χ h)) = wh ψ χ
  simp only [tr]
  rw [Fintype.sum_subsingleton _ 1, h1, one_mul, hres]

end GlobalTheory.GLq.MirabolicComparison

namespace GlobalTheory.GLq.MirabolicComparison

theorem mirabolic_comparison : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (N k s : ℕ),
    N = k + 2 * s + 1 → 1 ≤ k → ∀ χ : Gn g N → ℂ, IsChar χ →
      ((g : ℝ) ^ k - (g : ℝ) ^ (k - 1)) * (wh ψ χ).re ≤ (tr (eJ g N k s ψ) χ).re := by
  intro g _ ψ hψ N k s hN hk χ hχ
  have hcl := isClass_of_isChar hχ
  rw [GlobalTheory.T.groupAlgebraTrace_patternIdempotent_exchange g ψ hψ N k s hN χ hcl, GlobalTheory.T.trace_unitriangularColumnVanishingIdempotent_eq_sum_derivatives g ψ hψ N k hk (by omega) χ hcl]
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast (Fact.out : g.Prime).one_lt.le
  have hterm : ∀ i a b, (wh ψ (der ψ i χ) * ((g : ℂ) ^ a - (g : ℂ) ^ b)).re =
      (wh ψ (der ψ i χ)).re * ((g : ℝ) ^ a - (g : ℝ) ^ b) := by
    intro i a b
    rw [show ((g : ℂ) ^ a - (g : ℂ) ^ b) = (((g : ℝ) ^ a - (g : ℝ) ^ b : ℝ) : ℂ) by push_cast; ring]
    exact Complex.re_mul_ofReal _ _
  have hnn : ∀ i, i ≤ N → 0 ≤ (wh ψ (der ψ i χ)).re := by
    intro i hi
    obtain ⟨n, hn⟩ := wh_der_nat g ψ N i hi χ hχ
    rw [hn]
    simp
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Finset.sum_range_succ', Complex.add_re, Complex.add_re, Complex.re_sum, hterm 0, wh_der_zero]
  have hrest : 0 ≤ ∑ i ∈ Finset.range k', (wh ψ (der ψ (i + 1) χ) *
      ((g : ℂ) ^ (k' + 1 - (i + 1)) - (g : ℂ) ^ (k' + 1 - (i + 1) - 1))).re := by
    apply Finset.sum_nonneg
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hterm]
    apply mul_nonneg (hnn _ (by omega))
    rw [sub_nonneg]
    exact pow_le_pow_right₀ hg1 (by omega)
  have hlast := hnn (k' + 1) (by omega)
  have h0 : (wh ψ χ).re * ((g : ℝ) ^ (k' + 1 - 0) - (g : ℝ) ^ (k' + 1 - 0 - 1)) =
      ((g : ℝ) ^ (k' + 1) - (g : ℝ) ^ (k' + 1 - 1)) * (wh ψ χ).re := by
    simp only [Nat.sub_zero]
    ring
  linarith

end GlobalTheory.GLq.MirabolicComparison
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicTraceGeWhittakerDimensionGLnStatement
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_trace_ge_whittakerDimension_GLn : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (N k s : ℕ), N = k + 2 * s + 1 → 1 ≤ k → ∀ χ : Gn g N → ℂ, IsChar χ → ((g : ℝ) ^ k - (g : ℝ) ^ (k - 1)) * (wh ψ χ).re ≤ (tr (eJ g N k s ψ) χ).re := by
  first | exact @GlobalTheory.GLq.MirabolicComparison.mirabolic_comparison | exact GlobalTheory.GLq.MirabolicComparison.mirabolic_comparison | (intros; apply GlobalTheory.GLq.MirabolicComparison.mirabolic_comparison <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesWeightLowerComparison
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.LowerWt

theorem coeff_mul_eSerC {g : ℕ} [Fact g.Prime] (L : LabelDatum g) {N : ℕ} (f : (ZMod g)[X])
    (a : MonoidAlgebra ℂ (Gn g N))
    (hfin : {χ : Gn g N → ℂ | IsIrr χ ∧ HasLabel L χ f}.Finite) :
    (a * eSerC L N f).coeff 1 = ∑ χ ∈ hfin.toFinset, χ 1 / (Fintype.card (Gn g N) : ℂ) * tr a χ := by
  unfold eSerC
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun χ _ => ?_
  exact ((GlobalTheory.GLq.trIdem (Gn g N) a χ).2.2)

theorem re_coeff_mul_eSerC {g : ℕ} [Fact g.Prime] (L : LabelDatum g) {N : ℕ} (f : (ZMod g)[X])
    (a : MonoidAlgebra ℂ (Gn g N))
    (hfin : {χ : Gn g N → ℂ | IsIrr χ ∧ HasLabel L χ f}.Finite) :
    ((a * eSerC L N f).coeff 1).re =
      ∑ χ ∈ hfin.toFinset, (χ 1).re / (Fintype.card (Gn g N) : ℝ) * (tr a χ).re := by
  rw [coeff_mul_eSerC L f a hfin, Complex.re_sum]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  have hI : IsIrr χ := ((Set.Finite.mem_toFinset hfin).1 hχ).1
  obtain ⟨d, -, hd⟩ := (GlobalTheory.GLq.trIdem (Gn g N) a χ).2.1 hI
  rw [hd]
  have : (d : ℂ) / (Fintype.card (Gn g N) : ℂ) = (((d : ℝ) / (Fintype.card (Gn g N) : ℝ) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [this, Complex.re_ofReal_mul]
  simp

theorem weight_nonneg {g : ℕ} [Fact g.Prime] (L : LabelDatum g) {N : ℕ} (f : (ZMod g)[X])
    (hfin : {χ : Gn g N → ℂ | IsIrr χ ∧ HasLabel L χ f}.Finite) (χ : Gn g N → ℂ) (hχ : χ ∈ hfin.toFinset) :
    0 ≤ (χ 1).re / (Fintype.card (Gn g N) : ℝ) := by
  have hI : IsIrr χ := ((Set.Finite.mem_toFinset hfin).1 hχ).1
  obtain ⟨d, -, hd⟩ := (GlobalTheory.GLq.trIdem (Gn g N) (1 : MonoidAlgebra ℂ (Gn g N)) χ).2.1 hI
  rw [hd]
  simp only [Complex.natCast_re]
  positivity

end GlobalTheory.GLq.LowerWt

theorem GlobalTheory.GLq.lowerWtComparison : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 →
    ∀ (N k s : ℕ), N = k + 2 * s + 1 → 1 ≤ k →
      ∀ f, (1 - 1 / (g : ℝ)) * wtC L (eU g N ψ) f ≤ wtC L (eJ g N k s ψ) f := by
  intro g _ L ψ hψ N k s hN hk f
  have hL8 := GlobalTheory.T.mirabolic_trace_ge_whittakerDimension_GLn g ψ hψ N k s hN hk
  obtain ⟨-, hU1, hJ, -⟩ := GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g N k s ψ
  obtain ⟨-, hJ1⟩ := hJ hN
  have hfin : {χ : Gn g N → ℂ | IsIrr χ ∧ HasLabel L χ f}.Finite :=
    (irr_finite_and_finsum_zOf_eq_one (Gn g N)).1.subset fun χ h => h.1
  set T := hfin.toFinset
  set c : (Gn g N → ℂ) → ℝ := fun χ => (χ 1).re / (Fintype.card (Gn g N) : ℝ) with hc
  set A := ∑ χ ∈ T, c χ * (tr (eU g N ψ) χ).re with hA
  set B := ∑ χ ∈ T, c χ * (tr (eJ g N k s ψ) χ).re with hB
  have hAeq : ((eU g N ψ * eSerC L N f).coeff 1).re = A := LowerWt.re_coeff_mul_eSerC L f _ hfin
  have hBeq : ((eJ g N k s ψ * eSerC L N f).coeff 1).re = B := LowerWt.re_coeff_mul_eSerC L f _ hfin
  have hG : (0 : ℝ) < g := by exact_mod_cast (Fact.out : g.Prime).pos
  set M := N * (N - 1) / 2
  have hU1r : ((eU g N ψ).coeff 1).re = ((g : ℝ) ^ M)⁻¹ := by
    rw [hU1]
    have : ((g : ℂ) ^ M)⁻¹ = ((((g : ℝ) ^ M)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.ofReal_re]
  have hJ1r : ((eJ g N k s ψ).coeff 1).re = (g : ℝ) ^ k * ((g : ℝ) ^ M)⁻¹ := by
    rw [hJ1]
    have : (g : ℂ) ^ k * ((g : ℂ) ^ M)⁻¹ = ((((g : ℝ) ^ k * ((g : ℝ) ^ M)⁻¹) : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.ofReal_re]
  have hBA : ((g : ℝ) ^ k - (g : ℝ) ^ (k - 1)) * A ≤ B := by
    rw [hA, hB, Finset.mul_sum]
    refine Finset.sum_le_sum fun χ hχ => ?_
    have h0 : 0 ≤ c χ := LowerWt.weight_nonneg L f hfin χ hχ
    have hI : IsIrr χ := ((Set.Finite.mem_toFinset hfin).1 hχ).1
    have hC : IsChar χ := by obtain ⟨V, -, hV⟩ := hI; exact ⟨V, hV⟩
    have h8 := hL8 χ hC
    unfold wh at h8
    calc ((g : ℝ) ^ k - (g : ℝ) ^ (k - 1)) * (c χ * (tr (eU g N ψ) χ).re)
        = c χ * (((g : ℝ) ^ k - (g : ℝ) ^ (k - 1)) * (tr (eU g N ψ) χ).re) := by ring
      _ ≤ c χ * (tr (eJ g N k s ψ) χ).re := mul_le_mul_of_nonneg_left h8 h0
  have hpow : (g : ℝ) ^ k - (g : ℝ) ^ (k - 1) = (g : ℝ) ^ k * (1 - 1 / (g : ℝ)) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    field_simp
  unfold wtC
  rw [hAeq, hBeq, hU1r, hJ1r]
  have hgk : (0 : ℝ) < (g : ℝ) ^ k := pow_pos hG k
  have hgM : (0 : ℝ) < (g : ℝ) ^ M := pow_pos hG M
  rw [hpow] at hBA
  rw [div_inv_eq_mul, le_div_iff₀ (mul_pos hgk (inv_pos.2 hgM))]
  calc (1 - 1 / (g : ℝ)) * (A * (g : ℝ) ^ M) * ((g : ℝ) ^ k * ((g : ℝ) ^ M)⁻¹)
      = (g : ℝ) ^ k * (1 - 1 / (g : ℝ)) * A * ((g : ℝ) ^ M * ((g : ℝ) ^ M)⁻¹) := by ring
    _ = (g : ℝ) ^ k * (1 - 1 / (g : ℝ)) * A := by rw [mul_inv_cancel₀ hgM.ne', mul_one]
    _ ≤ B := hBA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesWeightLowerComparisonStatement
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraSeriesWeight_lower_comparison : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (N k s : ℕ), N = k + 2 * s + 1 → 1 ≤ k → ∀ f, (1 - 1 / (g : ℝ)) * wtC L (eU g N ψ) f ≤ wtC L (eJ g N k s ψ) f := by
  first | exact @GlobalTheory.GLq.lowerWtComparison | exact GlobalTheory.GLq.lowerWtComparison | (intros; apply GlobalTheory.GLq.lowerWtComparison <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesWeightNonnegOfIdempotentGlnPr
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesWeightNonnegOfIdempotentGlnPr
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace CompanionTheory.Member.TraceCoefficientSum

variable {G : Type} [Group G] [Fintype G]

theorem coeff_zOf (χ : G → ℂ) (x : G) : (zOf χ).coeff x = χ 1 / (Fintype.card G : ℂ) * χ x⁻¹ := by
  simp [zOf, MonoidAlgebra.coeff_sum, Finsupp.single_apply]

theorem eq_sum_single (a : MonoidAlgebra ℂ G) : a = ∑ x, MonoidAlgebra.single x (a.coeff x) := by
  ext y
  simp [MonoidAlgebra.coeff_sum, Finsupp.single_apply]

theorem coeff_mul_zOf (a : MonoidAlgebra ℂ G) (χ : G → ℂ) :
    (a * zOf χ).coeff 1 = χ 1 / (Fintype.card G : ℂ) * ∑ x, a.coeff x * χ x := by
  conv_lhs => rw [eq_sum_single a]
  rw [Finset.sum_mul, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [MonoidAlgebra.coeff_single_mul_apply, coeff_zOf, mul_one, inv_inv]
  ring

theorem trace_alg (a : MonoidAlgebra ℂ G) (V : FDRep ℂ G) :
    ∑ x, a.coeff x * V.character x =
      LinearMap.trace ℂ V (Representation.asAlgebraHom (V.ρ : Representation ℂ G V) a) := by
  conv_rhs => rw [eq_sum_single a]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Representation.asAlgebraHom_single, map_smul, smul_eq_mul]
  rfl

theorem trace_nat (a : MonoidAlgebra ℂ G) (ha : a * a = a) (V : FDRep ℂ G) :
    ∃ m : ℕ, ∑ x, a.coeff x * V.character x = m := by
  have hi : IsIdempotentElem (Representation.asAlgebraHom (V.ρ : Representation ℂ G V) a) := by
    unfold IsIdempotentElem
    rw [← map_mul, ha]
  rw [trace_alg]
  exact ⟨_, (LinearMap.IsIdempotentElem.isProj_range _ hi).trace⟩

theorem re_nonneg (a : MonoidAlgebra ℂ G) (ha : a * a = a) (χ : G → ℂ) (hχ : IsIrr χ) :
    0 ≤ ((a * zOf χ).coeff 1).re := by
  obtain ⟨V, -, hV⟩ := hχ
  obtain ⟨m, hm⟩ := trace_nat a ha V
  rw [coeff_mul_zOf, ← hV 1, FDRep.char_one]
  simp only [← hV]
  rw [hm, ← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_natCast m,
    ← Complex.ofReal_div, ← Complex.ofReal_mul, Complex.ofReal_re]
  positivity

end CompanionTheory.Member.TraceCoefficientSum

theorem CompanionTheory.Member.harishChandraSeriesWeight_nonneg_of_idempotent : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (n : ℕ) (a : MonoidAlgebra ℂ (Gn g n)), a * a = a → 0 ≤ (a.coeff 1).re → ∀ f, 0 ≤ wtC L a f := by
  intro g _ L n a ha h1 f
  refine div_nonneg ?_ h1
  unfold eSerC
  refine finsum_mem_induction (fun b => 0 ≤ ((a * b).coeff 1).re) (by simp) ?_ ?_
  · intro x y hx hy
    rw [mul_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, Complex.add_re]
    exact add_nonneg hx hy
  · intro χ hχ
    exact CompanionTheory.Member.TraceCoefficientSum.re_nonneg a ha χ hχ.1

end

section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
theorem _root_.GlobalTheory.Adopt.harishChandraSeriesWeight_nonneg_of_idempotent_glnPrime : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (n : ℕ) (a : MonoidAlgebra ℂ (Gn g n)), a * a = a → 0 ≤ (a.coeff 1).re → ∀ f, 0 ≤ wtC L a f := by
  first | exact @CompanionTheory.Member.harishChandraSeriesWeight_nonneg_of_idempotent | exact CompanionTheory.Member.harishChandraSeriesWeight_nonneg_of_idempotent | (intros; apply CompanionTheory.Member.harishChandraSeriesWeight_nonneg_of_idempotent <;> assumption)

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesWeightNonnegOfIdempotentGlnPrStatement
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraSeriesWeight_nonneg_of_idempotent_glnPrime : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (n : ℕ) (a : MonoidAlgebra ℂ (Gn g n)), a * a = a → 0 ≤ (a.coeff 1).re → ∀ f, 0 ≤ wtC L a f := by
  first | exact @GlobalTheory.Adopt.harishChandraSeriesWeight_nonneg_of_idempotent_glnPrime | exact GlobalTheory.Adopt.harishChandraSeriesWeight_nonneg_of_idempotent_glnPrime | (intros; apply GlobalTheory.Adopt.harishChandraSeriesWeight_nonneg_of_idempotent_glnPrime <;> assumption)
end
end

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq

theorem five_le_typePrime (D : Formalism.BasicNotions.D7) (k : Fin 2) : 5 ≤ D.host.g k := by
  have hc := D.ntypes.g_cond k
  have h4 : D.host.g k % 4 = 1 := by
    rw [← Nat.mod_mod_of_dvd (D.host.g k)
      (show 4 ∣ D.host.QS * D.host.q * D.host.d from
        (((pow_dvd_pow 2 (Nat.le_add_left 2 _)).trans D.host.tower_dvd).mul_right _).mul_right _), hc]
  have := (D.host.g_prime k).two_le
  omega

theorem rank_eq_k_add_two_mul (R : Formalism.BasicNotions.Ranks) : R.r = R.k + 2 * (R.m / 2 - 1) + 1 := by
  obtain ⟨a, ha⟩ := R.m_even
  have := R.two_le_m
  unfold Formalism.BasicNotions.Ranks.r
  omega

theorem lemmaL_series_weights_of_greenCuspidalParametrisation : Green → ∀ D : Formalism.BasicNotions.D7, ESerTie D → admLq D := by
  intro hG D hT k ψ hψ
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨L, -, hL⟩ := hT k
  have hw : ∀ a f, wtOf D k a f = wtC L a f := by
    intro a f
    unfold wtOf wtC
    rw [hL f]
  have h5 := five_le_typePrime D k
  have hr := rank_eq_k_add_two_mul D.R
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  obtain ⟨hU, hU1, hJ, -⟩ := GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField (D.host.g k) D.R.r D.R.k (D.R.m / 2 - 1) ψ
  obtain ⟨hJ, hJ1⟩ := hJ hr
  simp only [hw]
  refine ⟨fun f => ⟨?_, ?_⟩, fun f hf hs => ?_, fun f _ => ?_, fun f hf hs => ?_⟩
  · refine GlobalTheory.T.harishChandraSeriesWeight_nonneg_of_idempotent_glnPrime _ L _ _ hU ?_ f
    change 0 ≤ ((eU (D.host.g k) D.R.r ψ).coeff 1).re
    rw [hU1, ← Nat.cast_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]
    positivity
  · refine GlobalTheory.T.harishChandraSeriesWeight_nonneg_of_idempotent_glnPrime _ L _ _ hJ ?_ f
    change 0 ≤ ((eJ (D.host.g k) D.R.r D.R.k (D.R.m / 2 - 1) ψ).coeff 1).re
    rw [hJ1, ← Nat.cast_pow, ← Nat.cast_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_natCast,
      ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re]
    positivity
  · exact GlobalTheory.T.harishChandraSeriesWeight_squarefree_label_gelfandGraev _ L h5 hG ψ hψ _ f hf.1 hf.2.1 hf.2.2 hs
  · exact GlobalTheory.T.harishChandraSeriesWeight_lower_comparison _ L ψ hψ _ _ _ hr hk f
  · exact GlobalTheory.T.harishChandraSeriesWeight_le_squarefree _ L h5 hG ψ hψ _ _ _ hr hk f hf.1 hf.2.1 hf.2.2 hs

end GlobalTheory.GLq
