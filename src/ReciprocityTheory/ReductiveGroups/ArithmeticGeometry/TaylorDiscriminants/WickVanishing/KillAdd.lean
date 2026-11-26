module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.NabTrans

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.FoldrIterateEqTG
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ETGMulQ
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.TB.G2.Gen

open ReciprocityTheory.ChartRestriction.G.TB.G2

variable {k : Type} [CommRing k] {S : Type} [CommRing S] {ι : Type}
  (D : ι → S → S) (κ : k →+* S)
  (hadd : ∀ l f g, D l (f + g) = D l f + D l g) (hC : ∀ l a, D l (κ a) = 0)
  (hmul : ∀ l f g, D l (f * g) = D l f * g + f * D l g)

def TG (w : List ι) (A : S) : S := w.foldr (fun l g => D l g) A

include hadd in
theorem D_zero (l : ι) : D l 0 = 0 := by
  simpa using hadd l 0 0

include hadd in
theorem D_list_sum (l : ι) (L : List S) : D l L.sum = (L.map (D l)).sum := by
  induction L with
  | nil => simpa using D_zero D hadd l
  | cons a L ih => simp [hadd, ih]

theorem TG_append (w w' : List ι) (A : S) : TG D (w ++ w') A = TG D w (TG D w' A) := by
  simp only [TG, List.foldr_append]

include hadd in
theorem TG_add (w : List ι) (A B : S) : TG D w (A + B) = TG D w A + TG D w B := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    show D l (TG D w (A + B)) = D l (TG D w A) + D l (TG D w B)
    rw [ih, hadd]

include hadd hmul in
theorem TG_mul (w : List ι) (A B : S) :
    TG D w (A * B) = ((splits w).map (fun p => TG D p.1 A * TG D p.2 B)).sum := by
  induction w with
  | nil => simp [TG, splits]
  | cons l w ih =>
    have e : ∀ (v : List ι) (X : S), TG D (l :: v) X = D l (TG D v X) := fun _ _ => rfl
    rw [e, ih, D_list_sum D hadd]
    simp only [splits, List.map_append, List.sum_append, List.map_map, Function.comp_def, e, hmul,
      List.sum_map_add]

section Q
variable (e : S →+* k) (c : ι → ι → k) (q : S)
  (hq0 : e q = 0) (hq1 : ∀ l, e (D l q) = 0) (hq2 : ∀ l l', D l (D l' q) = κ (c l l'))

include hadd hC hq2 in
theorem TG_q_long (w : List ι) (hw : 3 ≤ w.length) : TG D w q = 0 := by
  induction w with
  | nil => simp at hw
  | cons l w ih =>
    show D l (TG D w q) = 0
    rcases Nat.lt_or_ge w.length 3 with h | h
    · have h2 : w.length = 2 := by
        simp only [List.length_cons] at hw
        omega
      obtain ⟨y, z, rfl⟩ := List.length_eq_two.mp h2
      show D l (D y (D z q)) = 0
      rw [hq2, hC]
    · rw [ih h, D_zero D hadd]

variable (he : ∀ a, e (κ a) = a)

include hadd hC hq0 hq1 hq2 he in
theorem e_TG_q (b : List ι) : e (TG D b q) = ev2 c b := by
  match b with
  | [] => exact hq0
  | [x] => exact hq1 x
  | [x, y] =>
    show e (D x (D y q)) = c x y
    rw [hq2, he]
  | x :: y :: z :: r =>
    rw [TG_q_long (D := D) (κ := κ) (hadd := hadd) (hC := hC) (c := c) (q := q) (hq2 := hq2)
      (w := x :: y :: z :: r) (by simp)]
    exact map_zero e

include hadd hmul hC hq0 hq1 hq2 he in
theorem e_TG_mul_q (w : List ι) (A : S) :
    e (TG D w (A * q)) = ((splits w).map (fun p => e (TG D p.1 A) * ev2 c p.2)).sum := by
  simp only [TG_mul (D := D) (hadd := hadd) (hmul := hmul), map_list_sum, List.map_map,
    Function.comp_def, map_mul, e_TG_q (D := D) (κ := κ) (hadd := hadd) (hC := hC) (e := e) (c := c)
      (q := q) (hq0 := hq0) (hq1 := hq1) (hq2 := hq2) (he := he)]

end Q

end ReciprocityTheory.ChartRestriction.G.TB.G2.Gen
end
end

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.TB.G2.Gen

open ReciprocityTheory.ChartRestriction.G.TB.G2

variable {k : Type} [CommRing k] {S : Type} [CommRing S] {ι : Type}
  (D : ι → S → S) (κ : k →+* S)

def PolG [Fintype ι] (P : MvPolynomial ι k) (A : S) : S :=
  ∑ n ∈ P.support, κ (P.coeff n) * (Finset.univ : Finset ι).toList.foldr (fun l g => (D l)^[n l] g) A

theorem TG_replicate (n : ℕ) (l : ι) (A : S) : TG D (List.replicate n l) A = (D l)^[n] A := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, Function.iterate_succ_apply', ← ih]
    rfl

theorem foldr_iterate_eq_TG (Ls : List ι) (m : ι →₀ ℕ) (A : S) :
    Ls.foldr (fun l g => (D l)^[m l] g) A = TG D (word Ls m) A := by
  induction Ls with
  | nil => rfl
  | cons l Ls ih =>
    rw [List.foldr_cons, ih]
    have e : word (l :: Ls) m = List.replicate (m l) l ++ word Ls m := by simp [word]
    rw [e, TG_append, TG_replicate]

theorem e_PolG [Fintype ι] (e : S →+* k) (he : ∀ a, e (κ a) = a) (P : MvPolynomial ι k) (A : S) :
    e (PolG D κ P A) = (AddMonoidAlgebra.coeff P).sum
      (fun n a => a * e (TG D (word (Finset.univ : Finset ι).toList n) A)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [PolG, map_sum, map_mul, he, foldr_iterate_eq_TG]
  rfl

theorem half_gen [Algebra ℚ k] [Fintype ι]
    (hadd : ∀ l f g, D l (f + g) = D l f + D l g) (hC : ∀ l a, D l (κ a) = 0)
    (hmul : ∀ l f g, D l (f * g) = D l f * g + f * D l g)
    (e : S →+* k) (he : ∀ a, e (κ a) = a) (c : ι → ι → k) (q : S) (hc : ∀ l l', c l l' = c l' l)
    (hq0 : e q = 0) (hq1 : ∀ l, e (D l q) = 0) (hq2 : ∀ l l', D l (D l' q) = κ (c l l'))
    (P : MvPolynomial ι k) (A : S) :
    e (PolG D κ P (A * q)) = algebraMap ℚ k (1 / 2) * e (PolG D κ (secondOrder k c P) A) := by
  classical
  set ψ : List ι → k := fun w => e (TG D w A) with hψ
  rw [e_PolG D κ e he, e_PolG D κ e he]
  have h2 : (AddMonoidAlgebra.coeff (secondOrder k c P)).sum
      (fun n a => a * e (TG D (word (Finset.univ : Finset ι).toList n) A)) = lamW ψ (secondOrder k c P) := rfl
  rw [h2, lamW_secondOrder, Finsupp.mul_sum]
  refine Finsupp.sum_congr fun n _ => ?_
  rw [e_TG_mul_q D κ hadd hC hmul e c q hq0 hq1 hq2 he]
  have h3 := sum_splits_evalTwo_word c hc (Finset.univ : Finset ι).toList (Finset.nodup_toList _) n ψ
  have h4 : (algebraMap ℚ k (1 / 2)) * 2 = 1 := by
    rw [← map_ofNat (algebraMap ℚ k) 2, ← map_mul]; norm_num
  calc (AddMonoidAlgebra.coeff P) n * ((splits (word (Finset.univ : Finset ι).toList n)).map
        (fun p => e (TG D p.1 A) * ev2 c p.2)).sum
      = (AddMonoidAlgebra.coeff P) n * ((algebraMap ℚ k (1 / 2) * 2) *
          ((splits (word (Finset.univ : Finset ι).toList n)).map (fun p => ψ p.1 * ev2 c p.2)).sum) := by
        rw [h4, one_mul]
    _ = algebraMap ℚ k (1 / 2) * ((AddMonoidAlgebra.coeff P) n * rW ψ c n) := by
        rw [mul_assoc (algebraMap ℚ k (1 / 2)), h3]
        simp only [rW]
        ring

theorem kill_gen [Algebra ℚ k] [Fintype ι]
    (hadd : ∀ l f g, D l (f + g) = D l f + D l g) (hC : ∀ l a, D l (κ a) = 0)
    (hmul : ∀ l f g, D l (f * g) = D l f * g + f * D l g)
    (e : S →+* k) (he : ∀ a, e (κ a) = a) (c : ι → ι → k) (q : S) (hc : ∀ l l', c l l' = c l' l)
    (hq0 : e q = 0) (hq1 : ∀ l, e (D l q) = 0) (hq2 : ∀ l l', D l (D l' q) = κ (c l l'))
    (P : MvPolynomial ι k) (hP : secondOrder k c P = 0) (G Y : S) :
    e (PolG D κ P (G * (1 + q * Y))) = e (PolG D κ P G) := by
  have hsplit : G * (1 + q * Y) = G + G * Y * q := by ring
  have hlin : ∀ A B, PolG D κ P (A + B) = PolG D κ P A + PolG D κ P B := by
    intro A B
    simp only [PolG, foldr_iterate_eq_TG]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [TG_add, mul_add]
    exact hadd
  rw [hsplit, hlin, map_add (f := _), half_gen D κ hadd hC hmul e he c q hc hq0 hq1 hq2 P (G * Y), hP]
  simp [PolG]

end ReciprocityTheory.ChartRestriction.G.TB.G2.Gen
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.KillAddQ
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB

def QuadColDerivSt : Prop :=
  ∀ (k : Type) [CommRing k] (d n : ℕ) (β : Matrix (Fin d) (Fin d) k),
    constantCoeff (quadCol (n := n) β) = 0 ∧
    (∀ (u : Fin d → k) (b : Fin n), constantCoeff (dAdd u b (quadCol (n := n) β)) = 0) ∧
    ∀ (u v : Fin d → k) (b b' : Fin n), dAdd u b (dAdd v b' (quadCol (n := n) β)) =
      C (if b = b' then dotProduct u (β.mulVec v) + dotProduct v (β.mulVec u) else 0)

private theorem pderiv_X_eq_C_ite {k : Type} [CommRing k] {n d : ℕ} (p q : Fin n × Fin d) :
    MvPowerSeries.pderiv p (X q : PS k n d) = C (if q = p then (1 : k) else 0) := by
  classical
  rw [MvPowerSeries.pderiv_X, Pi.single_apply]
  split_ifs <;> simp

private theorem pderiv_C_mul' {k : Type} [CommRing k] {n d : ℕ} (p : Fin n × Fin d) (a : k)
    (Y : PS k n d) : MvPowerSeries.pderiv p (C a * Y) = C a * MvPowerSeries.pderiv p Y := by
  rw [Derivation.leibniz, MvPowerSeries.pderiv_C, smul_zero, add_zero, smul_eq_mul]

private theorem pderiv_C_mul_X_mul_X {k : Type} [CommRing k] {n d : ℕ} (p q r : Fin n × Fin d) (a : k) :
    MvPowerSeries.pderiv p (C a * X q * X r : PS k n d) =
      C (a * (if r = p then 1 else 0)) * X q + C (a * (if q = p then 1 else 0)) * X r := by
  rw [Derivation.leibniz, pderiv_C_mul', pderiv_X_eq_C_ite, pderiv_X_eq_C_ite, smul_eq_mul, smul_eq_mul,
    map_mul, map_mul]
  ring

private theorem sum_quadratic_column_indicator_eq_dotProduct_mulVec {k : Type} [CommRing k] {d n : ℕ} (β : Matrix (Fin d) (Fin d) k)
    (u v : Fin d → k) (b b' : Fin n) :
    (∑ m : Fin d, ∑ j : Fin d, ∑ c : Fin n, ∑ i : Fin d, ∑ l : Fin d,
      (u m * (v j * (β i l * (if ((c, l) : Fin n × Fin d) = (b', j) then 1 else 0)) *
          (if ((c, i) : Fin n × Fin d) = (b, m) then 1 else 0)) +
        u m * (v j * (β i l * (if ((c, i) : Fin n × Fin d) = (b', j) then 1 else 0)) *
          (if ((c, l) : Fin n × Fin d) = (b, m) then 1 else 0)))) =
      if b = b' then dotProduct u (β.mulVec v) + dotProduct v (β.mulVec u) else 0 := by
  by_cases hb : b = b'
  · subst hb
    simp only [Prod.mk.injEq, ite_and, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
      Finset.sum_add_distrib, if_true]
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  · rw [if_neg hb]
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ =>
      Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun l _ => ?_
    by_cases hc : c = b
    · subst hc
      simp [Prod.mk.injEq, hb]
    · simp [Prod.mk.injEq, hc]

theorem quadratic_column_derivative : QuadColDerivSt := by
  intro k _ d n β
  classical
  refine ⟨?_, ?_, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · simp [quadCol, map_sum]
  · intro u b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dAdd, quadCol, map_sum, pderiv_C_mul_X_mul_X, pderiv_C_mul', map_add (f := _), map_mul,
      MvPowerSeries.constantCoeff_X, mul_zero, add_zero, Finset.sum_const_zero]
  · intro u v b b'

    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dAdd, quadCol, map_sum, pderiv_C_mul_X_mul_X, pderiv_C_mul', map_add (f := _), Finset.mul_sum,
      mul_add, pderiv_X_eq_C_ite]
    simp only [← mul_assoc, ← map_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← map_add (f := _), ← map_sum]
    congr 1
    rw [← sum_quadratic_column_indicator_eq_dotProduct_mulVec β u v b b']
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun l _ => by ring

end ReciprocityTheory.ChartRestriction.G.TB
end
end

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.G2

theorem exp_factor {k : Type} [CommRing k] [Algebra ℚ k] {σ : Type} (f : MvPowerSeries σ k)
    (hf : constantCoeff f = 0) :
    ∃ Y : MvPowerSeries σ k, PowerSeries.subst f (PowerSeries.exp k) = 1 + f * Y := by
  have ha : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero hf

  set E : PowerSeries k := PowerSeries.mk fun n => algebraMap ℚ k (1 / ((n + 1).factorial : ℚ)) with hE
  have hexp : PowerSeries.exp k = 1 + PowerSeries.X * E := by
    ext n
    rcases n with _ | n
    · simp [PowerSeries.coeff_exp]
    · simp [PowerSeries.coeff_exp, hE, PowerSeries.coeff_succ_X_mul]
  refine ⟨PowerSeries.subst f E, ?_⟩
  rw [hexp, ← PowerSeries.coe_substAlgHom ha, map_add (f := _), map_one, map_mul,
    PowerSeries.coe_substAlgHom, PowerSeries.subst_X ha]

end ReciprocityTheory.ChartRestriction.G.TB.G2

namespace ReciprocityTheory.ChartRestriction.G.TB

open ReciprocityTheory.ChartRestriction.G.TB.G2

variable {k : Type} [CommRing k] {d n : ℕ}

theorem dAdd_add (u : Fin d → k) (b : Fin n) (f g : PS k n d) : dAdd u b (f + g) = dAdd u b f + dAdd u b g := by
  simp only [dAdd, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem dAdd_C (u : Fin d → k) (b : Fin n) (a : k) : dAdd u b (C a : PS k n d) = 0 := by
  unfold dAdd
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [show (C a : PS k n d) = algebraMap k (PS k n d) a from rfl, Derivation.map_algebraMap, mul_zero]

theorem dAdd_mul (u : Fin d → k) (b : Fin n) (f g : PS k n d) :
    dAdd u b (f * g) = dAdd u b f * g + f * dAdd u b g := by
  unfold dAdd
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  ring

theorem killAdd_of (hQ : QuadColDerivSt) : KillAddSt := by
  intro k _ _ d n ι _ u β P hP m g
  obtain ⟨h0, h1, h2⟩ := hQ k d n β
  obtain ⟨Y, hY⟩ := exp_factor (m • quadCol (n := n) β) (by simp [h0])
  have key := Gen.kill_gen (D := fun p : ι × Fin n => dAdd (u p.1) p.2) (κ := (C : k →+* PS k n d))
    (fun l f g => dAdd_add (u l.1) l.2 f g) (fun l a => dAdd_C (u l.1) l.2 a)
    (fun l f g => dAdd_mul (u l.1) l.2 f g) constantCoeff (fun a => by simp)
    (fun p p' : ι × Fin n => if p.2 = p'.2 then
      dotProduct (u p.1) (β.mulVec (u p'.1)) + dotProduct (u p'.1) (β.mulVec (u p.1)) else 0)
    (quadCol (n := n) β)
    (fun l l' => by
      by_cases h : l.2 = l'.2
      · rw [if_pos h, if_pos h.symm, add_comm]
      · rw [if_neg h, if_neg (Ne.symm h)])
    h0 (fun l => h1 (u l.1) l.2) (fun l l' => h2 (u l.1) (u l'.1) l.2 l'.2) P hP g (m • Y)
  have e : FB.expS k (m • quadCol (n := n) β) * g = g * (1 + quadCol (n := n) β * (m • Y)) := by
    rw [FB.expS, hY, mul_comm, smul_mul_assoc, mul_smul_comm]
  rw [e]
  exact key

end ReciprocityTheory.ChartRestriction.G.TB
