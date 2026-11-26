module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ColumnWordReductionOfFour

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ColumnConditionsOfNumericBounds
section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ValuationLambdaFieldProperties
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Kit

theorem valuation_lambda_field_properties (D : Formalism.BasicNotions.D7) (h : Formalism.MainNotions.CovariantDegrees.ValuationsAdditive D) (R : Type) [Field R] (ι : Type) (n : ℕ) [NeZero n]
    (LL : Letters ι) (S : Set ι) (F G : MvPolynomial (ι × Fin n) R) :
    valS LL S (F * G) = valS LL S F + valS LL S G ∧ min (valS LL S F) (valS LL S G) ≤ valS LL S (F + G) ∧
      lam1S LL S (F * G) = lam1S LL S F + lam1S LL S G ∧
      lam1S LL S (F + G) ≤ max (lam1S LL S F) (lam1S LL S G) := by
  obtain ⟨t, F', G', rfl, rfl⟩ := exists_finset_letters F G
  have hf : Function.Injective (fun i : {x // x ∈ t} => (i : ι)) := Subtype.val_injective
  have T := fun A => Formalism.MainNotions.SelectionLemmas.valuation_lowest_degree_rename R {x // x ∈ t} ι (fun i : {x // x ∈ t} => (i : ι)) n LL S A hf
  obtain ⟨v1, v2, v3, v4, -, -⟩ := h R {x // x ∈ t} (⟨fun i : {x // x ∈ t} => LL.vec i⟩ : Letters {x // x ∈ t}) n
    ((fun i : {x // x ∈ t} => (i : ι)) ⁻¹' S)
  rw [← map_mul, ← map_add (f := _), (T _).1, (T _).1, (T _).1, (T _).1, (T _).2, (T _).2, (T _).2, (T _).2]
  exact ⟨v1 _ _, v2 _ _, v3 _ _, v4 _ _⟩

variable {R : Type} [CommRing R] {ι : Type} {n : ℕ}

theorem suppIn_one (s : Set ℤ) (h0 : (0 : ℤ) ∈ s) (a : GLCoord R n) : SuppIn s (LaurentPolynomial.C a) := by
  have : LaurentPolynomial.C a = LaurentPolynomial.C a * LaurentPolynomial.T 0 := by simp
  rw [this]; exact SuppIn.C_mul_T _ _ h0

theorem sDegs_C (LL : Letters ι) (S : Set ι) (j : Fin n) (c : R) :
    ∀ k ∈ sDegs LL S j (C c : MvPolynomial (ι × Fin n) R), k ∈ ({0} : Set ℤ) := by
  classical
  refine sDegs_subset LL S j _ _ fun m => ?_
  have : twistSub LL S j (C c : MvPolynomial (ι × Fin n) R) = C (coefL R n c) := by simp [twistSub]
  rw [this, coeff_C]
  split_ifs
  · have h2 : coefL R n c =
        LaurentPolynomial.C (algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n) (C c)) := rfl
    rw [h2]; exact suppIn_one (R := R) (n := n) ({0} : Set ℤ) (Set.mem_singleton 0) _
  · exact SuppIn.zero _

theorem sDegs_X_out (LL : Letters ι) (S : Set ι) (j : Fin n) (v : ι × Fin n) (hv : v.1 ∉ S) :
    ∀ k ∈ sDegs LL S j (X v : MvPolynomial (ι × Fin n) R), k ∈ ({0} : Set ℤ) := by
  classical
  refine sDegs_subset LL S j _ _ fun m => ?_
  have : twistSub LL S j (X v : MvPolynomial (ι × Fin n) R) = X v := by simp [twistSub, hv]
  rw [this, coeff_X]
  split_ifs
  · have h1 : (1 : GLLaurent R n) = LaurentPolynomial.C 1 := by simp
    rw [h1]; exact suppIn_one (R := R) (n := n) ({0} : Set ℤ) (Set.mem_singleton 0) _
  · exact SuppIn.zero _

end Kit

section Kit2

variable (D : Formalism.BasicNotions.D7) (hV : Formalism.MainNotions.CovariantDegrees.ValuationsAdditive D) {R : Type} [Field R] {n : ℕ} [NeZero n] (S : Set ℤ)

include hV

theorem vg_mul {a b : ℤ} {P Q : MvPolynomial (ℤ × Fin n) R} (hP : (a : WithTop ℤ) ≤ valS LZ S P)
    (hQ : (b : WithTop ℤ) ≤ valS LZ S Q) : ((a + b : ℤ) : WithTop ℤ) ≤ valS LZ S (P * Q) := by
  rw [(valuation_lambda_field_properties D hV R ℤ n LZ S P Q).1, WithTop.coe_add]; exact add_le_add hP hQ

theorem lg_mul {a b : ℤ} {P Q : MvPolynomial (ℤ × Fin n) R} (hP : lam1S LZ S P ≤ (a : WithBot ℤ))
    (hQ : lam1S LZ S Q ≤ (b : WithBot ℤ)) : lam1S LZ S (P * Q) ≤ ((a + b : ℤ) : WithBot ℤ) := by
  rw [(valuation_lambda_field_properties D hV R ℤ n LZ S P Q).2.2.1, WithBot.coe_add]; exact add_le_add hP hQ

omit hV in
theorem vg_C (c : R) : ((0 : ℤ) : WithTop ℤ) ≤ valS LZ S (C c : MvPolynomial (ℤ × Fin n) R) :=
  (le_valS_iff LZ S _ 0).mpr fun k hk => by
    have := sDegs_C LZ S _ c k hk
    simp at this; omega

omit hV in
theorem lg_C (c : R) : lam1S LZ S (C c : MvPolynomial (ℤ × Fin n) R) ≤ ((0 : ℤ) : WithBot ℤ) :=
  (lowest_degree_le_iff LZ S _ 0).mpr fun k hk => by
    have := sDegs_C LZ S _ c k hk
    simp at this; omega

theorem vg_pow {a : ℤ} {P : MvPolynomial (ℤ × Fin n) R} (hP : (a : WithTop ℤ) ≤ valS LZ S P) (m : ℕ) :
    (((m : ℤ) * a : ℤ) : WithTop ℤ) ≤ valS LZ S (P ^ m) := by
  induction m with
  | zero => simpa using vg_C (n := n) S (1 : R)
  | succ m ih =>
    rw [pow_succ]
    have := vg_mul D hV S ih hP
    have e : (m : ℤ) * a + a = ((m + 1 : ℕ) : ℤ) * a := by push_cast; ring
    rwa [e] at this

theorem lg_pow {a : ℤ} {P : MvPolynomial (ℤ × Fin n) R} (hP : lam1S LZ S P ≤ (a : WithBot ℤ)) (m : ℕ) :
    lam1S LZ S (P ^ m) ≤ (((m : ℤ) * a : ℤ) : WithBot ℤ) := by
  induction m with
  | zero => simpa using lg_C (n := n) S (1 : R)
  | succ m ih =>
    rw [pow_succ]
    have := lg_mul D hV S ih hP
    have e : (m : ℤ) * a + a = ((m + 1 : ℕ) : ℤ) * a := by push_cast; ring
    rwa [e] at this

theorem vg_prod {κ : Type} (s : Finset κ) (f : κ → MvPolynomial (ℤ × Fin n) R) (a : κ → ℤ)
    (h : ∀ i ∈ s, (a i : WithTop ℤ) ≤ valS LZ S (f i)) :
    ((∑ i ∈ s, a i : ℤ) : WithTop ℤ) ≤ valS LZ S (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vg_C (n := n) S (1 : R)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact vg_mul D hV S (h i (Finset.mem_insert_self i s)) (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem lg_prod {κ : Type} (s : Finset κ) (f : κ → MvPolynomial (ℤ × Fin n) R) (a : κ → ℤ)
    (h : ∀ i ∈ s, lam1S LZ S (f i) ≤ (a i : WithBot ℤ)) :
    lam1S LZ S (∏ i ∈ s, f i) ≤ ((∑ i ∈ s, a i : ℤ) : WithBot ℤ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lg_C (n := n) S (1 : R)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact lg_mul D hV S (h i (Finset.mem_insert_self i s)) (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem vg_sum {κ : Type} (s : Finset κ) (f : κ → MvPolynomial (ℤ × Fin n) R) (a : ℤ)
    (h : ∀ i ∈ s, (a : WithTop ℤ) ≤ valS LZ S (f i)) : (a : WithTop ℤ) ≤ valS LZ S (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [valS, sDegs]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact le_trans (le_min (h i (Finset.mem_insert_self i s)) (ih fun k hk => h k (Finset.mem_insert_of_mem hk)))
      (valuation_lambda_field_properties D hV R ℤ n LZ S _ _).2.1

omit hV in
theorem vg_X (v : ℤ × Fin n) :
    (((if Even v.1 then 0 else -1 : ℤ)) : WithTop ℤ) ≤ valS LZ S (X v : MvPolynomial (ℤ × Fin n) R) := by
  by_cases hv : v.1 ∈ S
  · have hc := coord_clauses (R := R) LZ S v.1 hv v.2
    by_cases he : Even v.1
    · rw [if_pos he]; exact (hc.1 (by simp [LZ, he])).1
    · rw [if_neg he]; exact (hc.2 (by simp [LZ, he])).1
  · refine (le_valS_iff LZ S _ _).mpr fun k hk => ?_
    have := sDegs_X_out (R := R) LZ S _ v hv k hk
    simp at this
    split_ifs <;> omega

omit hV in
theorem lg_X (v : ℤ × Fin n) :
    lam1S LZ S (X v : MvPolynomial (ℤ × Fin n) R) ≤ (((if Even v.1 then 1 else 0 : ℤ)) : WithBot ℤ) := by
  by_cases hv : v.1 ∈ S
  · have hc := coord_clauses (R := R) LZ S v.1 hv v.2
    by_cases he : Even v.1
    · rw [if_pos he]; exact (hc.1 (by simp [LZ, he])).2
    · rw [if_neg he]; exact (hc.2 (by simp [LZ, he])).2
  · refine (lowest_degree_le_iff LZ S _ _).mpr fun k hk => ?_
    have := sDegs_X_out (R := R) LZ S _ v hv k hk
    simp at this
    split_ifs <;> omega

theorem vg_det (y : Fin n → ℤ) (hy : ∀ i, Even (y i)) :
    ((0 : ℤ) : WithTop ℤ) ≤
      valS LZ S (Matrix.det (Matrix.of fun a b : Fin n => (X (y a, b) : MvPolynomial (ℤ × Fin n) R))) := by
  rw [Matrix.det_apply]
  refine vg_sum D hV S _ _ 0 fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  have h1 : (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : MvPolynomial (ℤ × Fin n) R) = C (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) := by
    simp
  rw [h1]
  have h2 := vg_prod D hV S Finset.univ
    (fun i : Fin n => (Matrix.of fun a b : Fin n => (X (y a, b) : MvPolynomial (ℤ × Fin n) R)) (σ i) i) (fun _ => 0)
    (fun i _ => by
      have := vg_X (R := R) S (y (σ i), i)
      simpa [hy (σ i)] using this)
  have := vg_mul D hV S (vg_C (n := n) S (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R)) h2
  simpa using this

end Kit2

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

def LateIndexInjective : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → ∀ j, ∀ x ∈ X.toLate j,
    Function.Injective (X.row j x) ∧ ∀ i, X.row j x i ∈ X.F.letters j ∧ Even (X.row j x i) ∧ X.row j x i < x

def EllDegreeLePowerBound : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → ∀ j e, X.IsEll p K j e →
    X.dS K j e + X.dV K j e ≤ (r + K) * X.Ns * p ^ X.Rj p K j

def PowerExceedsMaxMultiplicity (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ j, X.mStar < p ^ X.Rj p K j

def ThresholdPowerLowerBound (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ j b, X.Step2 p K j b → ∀ x ∈ X.toLate j,
      X.th p j x ≤ ((p ^ X.Rj p K j : ℕ) : ℝ) * (X.thc p K j b x - (((r + K) * X.Ns : ℕ) : ℝ))

theorem mem_late {n' r : ℕ} [NeZero n'] (X : Dat n' r) (j x : ℤ) :
    x ∈ X.toLate j ↔ x ∈ X.F.letters j ∧ ¬ X.F.IsW j x := by
  simp only [Dat.toLate, Finset.mem_filter]

section AG

variable (D : Formalism.BasicNotions.D7) (hV : Formalism.MainNotions.CovariantDegrees.ValuationsAdditive D) {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ)
  [NeZero K] {R : Type} [Field R] (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) (S : Set ℤ)

include hV

theorem vg_ellP : ((-(X.dS K j e : ℤ) : ℤ) : WithTop ℤ) ≤ valS LZ S (X.ellP K R j e) := by
  have h := vg_prod D hV (R := R) S (X.toLate j)
    (fun x => ∏ c : Fin r, (MvPolynomial.X (x, c) : MvPolynomial (ℤ × Fin r) R) ^ e (x, Fin.castAdd K c))
    (fun x => ∑ c : Fin r, (e (x, Fin.castAdd K c) : ℤ) * (if Even x then 0 else -1))
    (fun x _ => vg_prod D hV S Finset.univ _ _ (fun c _ => vg_pow D hV S (vg_X (R := R) S (x, c)) _))
  have e1 : (∑ x ∈ X.toLate j, ∑ c : Fin r, (e (x, Fin.castAdd K c) : ℤ) * (if Even x then 0 else -1)) =
      -(X.dS K j e : ℤ) := by
    unfold Dat.dS
    push_cast
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  rw [e1] at h
  exact h

theorem lg_ellN : lam1S LZ S (X.ellN K R j e) ≤ (((X.dV K j e : ℤ) : ℤ) : WithBot ℤ) := by
  have h := lg_prod D hV (R := R) S (X.toLate j)
    (fun x => ∏ c : Fin K, (MvPolynomial.X (x, c) : MvPolynomial (ℤ × Fin K) R) ^ e (x, Fin.natAdd r c))
    (fun x => ∑ c : Fin K, (e (x, Fin.natAdd r c) : ℤ) * (if Even x then 1 else 0))
    (fun x _ => lg_prod D hV S Finset.univ _ _ (fun c _ => lg_pow D hV S (lg_X (R := R) S (x, c)) _))
  have e1 : (∑ x ∈ X.toLate j, ∑ c : Fin K, (e (x, Fin.natAdd r c) : ℤ) * (if Even x then 1 else 0)) =
      (X.dV K j e : ℤ) := by
    unfold Dat.dV
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  rw [e1] at h
  exact h

theorem vg_DlSeg (hev : ∀ x' ∈ X.toLate j, ∀ i, Even (X.row j x' i)) (x : ℤ) (hx : x ∈ X.toLate j)
    (hinj : Function.Injective (X.row j x)) (hS : ∀ i, X.row j x i ∈ S) :
    (((X.sg p K j x : ℤ) : ℤ) : WithTop ℤ) ≤ valS LZ S (X.DlSeg p K R j) := by
  classical
  have h := vg_prod D hV (R := R) S (X.toLate j) (fun x' => X.detPl R j x' ^ X.sg p K j x')
    (fun x' => if x' = x then (X.sg p K j x : ℤ) else 0) (fun x' hx' => by
      by_cases hxx : x' = x
      · subst hxx
        rw [if_pos rfl]
        have h1 : ((1 : ℤ) : WithTop ℤ) ≤ valS LZ S (X.detPl R j x') := by
          unfold Dat.detPl valS
          rw [sDegs_det LZ S _ (X.row j x') hinj (fun i => ⟨hS i, by simp [LZ, hev x' hx' i]⟩)]
          simp
        have := vg_pow D hV S h1 (X.sg p K j x')
        simpa using this
      · rw [if_neg hxx]
        have := vg_pow D hV S (vg_det D hV (R := R) S (X.row j x') (hev x' hx')) (X.sg p K j x')
        simpa [Dat.detPl] using this)
  rw [Finset.sum_ite_eq' (X.toLate j) x, if_pos hx] at h
  exact h

theorem vg_Aw (hev : ∀ x' ∈ X.toLate j, ∀ i, Even (X.row j x' i)) (x : ℤ) (hx : x ∈ X.toLate j)
    (hinj : Function.Injective (X.row j x)) (hS : ∀ i, X.row j x i ∈ S)
    (nu : Fin (segN X.F j + 1) → Fin r → ℤ) (I' : ℤ → Finset (Fin r)) (a : ℤ)
    (ha : (a : WithTop ℤ) ≤ valS LZ S (segRen X.F j R r (Psi R nu I'))) :
    ((((p ^ X.Rj p K j : ℕ) : ℤ) * a + -(X.dS K j e : ℤ) + (X.sg p K j x : ℤ) : ℤ) : WithTop ℤ) ≤
      valS LZ S (X.Aw p K R j e nu I') := by
  unfold Dat.Aw
  exact vg_mul D hV S (vg_mul D hV S (vg_pow D hV S ha _) (vg_ellP D hV X K j e S))
    (vg_DlSeg D hV X p K j S hev x hx hinj hS)

theorem lg_Gw (ka : Fin (segN X.F j + 1) → Fin K → ℤ) (I'' : ℤ → Finset (Fin K)) (a : ℤ)
    (ha : lam1S LZ S (segRen X.F j R K (Psi R ka I'')) ≤ (a : WithBot ℤ)) :
    lam1S LZ S (X.Gw p K R j e ka I'') ≤ ((((p ^ X.Rj p K j : ℕ) : ℤ) * a + (X.dV K j e : ℤ) : ℤ) : WithBot ℤ) := by
  unfold Dat.Gw
  exact lg_mul D hV S (lg_pow D hV S ha _) (lg_ellN D hV X K j e S)

end AG

theorem int_ineq (Q κ ν dS dV s mS kN : ℤ) (hQ : 0 ≤ Q) (h : κ + (kN + 1) ≤ ν) (hd : dS + dV ≤ kN * Q)
    (hm : mS < Q) : Q * κ + dV + (mS + s) ≤ Q * ν + -dS + s := by
  nlinarith [mul_le_mul_of_nonneg_left h hQ]

theorem geR_of_le {v : WithTop ℤ} {a : ℤ} {t : ℝ} (h : (a : WithTop ℤ) ≤ v) (ht : t ≤ (a : ℝ)) : geR v t := by
  unfold geR
  intro z hz
  rw [hz] at h
  have h' : a ≤ z := WithTop.coe_le_coe.mp h
  exact ht.trans (by exact_mod_cast h')

theorem column_conditions_of_numeric_bounds (D : Formalism.BasicNotions.D7) (hV : Formalism.MainNotions.CovariantDegrees.ValuationsAdditive D) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D) (C₀ : ℝ)
    (hRow : LateIndexInjective) (hN0 : EllDegreeLePowerBound) (hN1 : PowerExceedsMaxMultiplicity C₀) (hN2 : ThresholdPowerLowerBound C₀) : ColumnConditionsWithMargin C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S j b e q I' I'' hc x hx hW
  have : Fact p.Prime := ⟨hc.hX.prime⟩
  obtain ⟨i, rfl⟩ := segE_surj X.F j hx
  obtain ⟨nu, ka⟩ := q
  obtain ⟨b', b'', ⟨P1, h1⟩, ⟨P2, h2⟩, hcond⟩ := hc.hq
  have hI' := hc.hI'
  have hI'' := hc.hI''
  simp only at h1 h2 hcond hI' hI'' ⊢
  have hF3 : ∀ (N n : ℕ) [NeZero n] (LL : Letters (Fin N)) (B : Fin N → ℕ) (th M : Fin N → ℤ),
      Formalism.MainNotions.CovariantDegrees.A3at (FF O) N n LL B th M := fun N n _ LL B th M => (hA3 p O S N n LL B th M).2
  rw [← h1] at hI' hcond ⊢
  rw [← h2] at hI'' hcond ⊢
  have u1 := standard_polynomial_mem_bounds (segLL X.F j) b' (hF3 _ r _ b') P1 I' hI'
  have u2 := standard_polynomial_mem_bounds (segLL X.F j) b'' (hF3 _ K _ b'') P2 I'' hI''
  obtain ⟨sA1, sA2, -, -⟩ := seg_val X.F j (Psi (FF O) P1.mu I') i
  obtain ⟨-, -, sG3, sG4⟩ := seg_val X.F j (Psi (FF O) P2.mu I'') i
  obtain ⟨cE, cO, cR⟩ := (hcond i).2 hW
  have hxl : segE X.F j i ∈ X.toLate j := (mem_late X j _).mpr ⟨hx, hW⟩
  have hM : X.Mw p K j e P2.mu (segE X.F j i) = ((p ^ X.Rj p K j : ℕ) : ℤ) *
      (if Even (segE X.F j i) then P2.mu i.succ 0 else P2.mu i.castSucc 0) + (X.dV K j e : ℤ) :=
    (segE_strictMono X.F j).injective.extend_apply _ _ i
  have hrows := hRow p n' r K X hc.hX j
  have hev : ∀ x' ∈ X.toLate j, ∀ i, Even (X.row j x' i) := fun x' hx' i => ((hrows x' hx').2 i).2.1
  have hinj := (hrows _ hxl).1
  have hlt : ∀ a, X.row j (segE X.F j i) a < segE X.F j i := fun a => ((hrows _ hxl).2 a).2.2
  have n0 := hN0 p n' r K X hc.hX j e hc.he
  have n1 := hN1 p n' r K X hc.hX hc.hLa hc.hk j
  have n2 := hN2 p n' r K X hc.hX hc.hLa hc.hk j b hc.h2 _ hxl
  have n0' : (X.dS K j e : ℤ) + (X.dV K j e : ℤ) ≤ (((r + K) * X.Ns : ℕ) : ℤ) * ((p ^ X.Rj p K j : ℕ) : ℤ) := by
    exact_mod_cast n0
  have n1' : (X.mStar : ℤ) < ((p ^ X.Rj p K j : ℕ) : ℤ) := by exact_mod_cast n1
  have hm0 : (X.m0 K : ℤ) = (((r + K) * X.Ns : ℕ) : ℤ) + 1 := by unfold Dat.m0; push_cast; ring
  have vlt := vg_Aw D hV X p K (R := FF O) j e {y | y < segE X.F j i} hev _ hxl hinj hlt P1.mu I'
    (P1.mu i.castSucc (lastIdx r)) (by rw [sA2]; exact (u1.2 i.castSucc).1)
  have vle := vg_Aw D hV X p K (R := FF O) j e {y | y ≤ segE X.F j i} hev _ hxl hinj (fun a => (hlt a).le) P1.mu I'
    (P1.mu i.succ (lastIdx r)) (by rw [sA1]; exact (u1.2 i.succ).1)
  refine ⟨fun he => ⟨?_, ?_⟩, fun he => ⟨?_, ?_⟩, ?_⟩
  · rw [hM, if_pos he]
    exact lg_Gw D hV X p K j e _ P2.mu I'' _ (by rw [sG3]; exact (u2.2 i.succ).2)
  · refine le_trans (WithTop.coe_le_coe.mpr ?_) vlt
    rw [hM, if_pos he]
    unfold Dat.mg
    have hce := (cE he).1
    rw [hm0] at hce
    exact int_ineq _ _ _ _ _ _ _ _ (Int.natCast_nonneg _) hce n0' n1'
  · rw [hM, if_neg he]
    exact lg_Gw D hV X p K j e _ P2.mu I'' _ (by rw [sG4]; exact (u2.2 i.castSucc).2)
  · refine le_trans (WithTop.coe_le_coe.mpr ?_) vle
    rw [hM, if_neg he]
    unfold Dat.mg
    have hce := (cO he).1
    rw [hm0] at hce
    exact int_ineq _ _ _ _ _ _ _ _ (Int.natCast_nonneg _) hce n0' n1'
  · refine geR_of_le vlt ?_
    push_cast
    have hQ : (0 : ℝ) ≤ ((p : ℝ) ^ X.Rj p K j) := by positivity
    have n0r : (X.dS K j e : ℝ) + (X.dV K j e : ℝ) ≤ (((r : ℝ) + K) * X.Ns) * (p : ℝ) ^ X.Rj p K j := by
      exact_mod_cast n0
    have hdV : (0 : ℝ) ≤ (X.dV K j e : ℝ) := Nat.cast_nonneg _
    have hs : (0 : ℝ) ≤ (X.sg p K j (segE X.F j i) : ℝ) := Nat.cast_nonneg _
    push_cast at n2
    have := mul_le_mul_of_nonneg_left cR hQ
    nlinarith

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

def OldestLetterInSegment : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → ∀ j, ∀ x ∈ X.toLate j,
    X.F.oldest j x ∈ X.F.letters j ∧ (¬ X.F.IsW j (X.F.oldest j x) → X.F.oldest j x ∈ X.F.LLset j)

def OrderNumericBound (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ j, ∀ x ∈ X.toLate j,
      ((p ^ X.Rj p K j : ℕ) : ℝ) * X.oc p K j x + Dat.k (r := r) K * ((p ^ X.Rj p K j : ℕ) : ℝ) ≤ X.o p K j x

section Num

variable {p n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {X : Dat n' r}

theorem frame_zero_le {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) : ∀ i, i < r → F.fr j 0 ≤ F.fr j i := by
  intro i
  induction i with
  | zero => intro _; exact le_rfl
  | succ i ih => intro h; exact (ih (by omega)).trans (hV.2.2.1 j i h).le

theorem reflection_mem_Glev_castSucc {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) : F.fr (j - 1) 0 ∈ F.letters j := by
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have h1 := frame_zero_le hV (j - 1) (r - 1) (by omega)
  have h2 := hV.2.2.2.1 (j - 1)
  rw [sub_add_cancel] at h2
  have h3 := frame_zero_le hV j (r - 1) (by omega)
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨le_rfl, by omega⟩, (hV.2.2.2.2.1 (j - 1) 0 hr).1⟩

theorem mem_letters_bounds {F : Frames n' r} {j x : ℤ} (hx : x ∈ F.letters j) :
    F.fr (j - 1) 0 ≤ x ∧ x ≤ F.fr j (r - 1) ∧ posOf n' x ∈ F.TT := by
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc] at hx
  exact ⟨hx.1.1, hx.1.2, hx.2⟩

structure Basics (X : Dat n' r) (p K : ℕ) : Prop where
  p1 : (1 : ℝ) < p
  Ns1 : (1 : ℝ) ≤ X.Ns
  k5 : (5 : ℝ) ≤ Dat.k (r := r) K
  rk : (r : ℝ) ≤ Dat.k (r := r) K
  Q1 : (1 : ℝ) ≤ X.Q
  Y1 : (1 : ℝ) ≤ X.Y

theorem basics (hX : X.Hyp p K) : Basics X p K := by
  have hV := hX.valid
  have hw := reflection_mem_Glev_castSucc hV 0
  have hp : (13 : ℝ) ≤ p := by exact_mod_cast hX.p13
  have hc : 1 ≤ (X.F.letters 0).card := Finset.card_pos.mpr ⟨_, hw⟩
  have hNs : 1 ≤ X.Ns := hc.trans (hX.card 0)
  have hK := hX.NsK
  have hr := hX.r2
  have hQ := hX.twist 0 _ hw
  refine ⟨by linarith, by exact_mod_cast hNs, ?_, ?_, ?_, hX.Y1⟩
  · unfold Dat.k
    exact_mod_cast (by omega : 5 ≤ r + K)
  · unfold Dat.k
    exact_mod_cast (by omega : r ≤ r + K)
  · exact le_trans (one_le_pow₀ (by linarith : (1 : ℝ) ≤ p)) hQ

def Tj (X : Dat n' r) (p K : ℕ) (j : ℤ) : ℝ :=
  X.a / (8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0))

theorem den_pos (hX : X.Hyp p K) (j : ℤ) :
    0 < 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) := by
  have B := basics hX
  have h1 : (0 : ℝ) < p := by linarith [B.p1]
  have h2 : (0 : ℝ) < X.Y := by linarith [B.Y1]
  have h3 : (0 : ℝ) < Dat.k (r := r) K := by linarith [B.k5]
  have h4 : (0 : ℝ) < X.Ns := by linarith [B.Ns1]
  positivity

theorem Tj_ge (hX : X.Hyp p K) (j : ℤ) : 4 * (p : ℝ) * ((X.E₀ : ℝ) + X.mStar + 1) ≤ Tj X p K j := by
  have b := basics hX
  have hd := den_pos hX j
  have hw := reflection_mem_Glev_castSucc hX.valid j
  have hQ := hX.twist j _ hw
  have P3 := hX.P3
  have hY : 0 ≤ X.Y := by linarith [b.Y1]
  have hp0 : (0 : ℝ) ≤ p := by linarith [b.p1]
  have hdQ : (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) ≤ X.Q ^ 2 := hQ.trans (by nlinarith [b.Q1])
  have hk : Dat.k (r := r) K = ((r + K : ℕ) : ℝ) := rfl
  have hc : 0 ≤ (p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * ((X.E₀ : ℝ) + X.mStar + 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hp0 hY) (sq_nonneg _)) (Nat.cast_nonneg _))
      (by positivity)
  have hm := mul_le_mul_of_nonneg_left hdQ hc
  unfold Tj
  rw [le_div_iff₀ hd, hk]
  calc 4 * (p : ℝ) * ((X.E₀ : ℝ) + X.mStar + 1) * (8 * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0))
        = 32 * ((p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * ((X.E₀ : ℝ) + X.mStar + 1) * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0)) := by ring
    _ ≤ 32 * ((p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * ((X.E₀ : ℝ) + X.mStar + 1) * X.Q ^ 2) := by linarith
    _ = 32 * (p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * X.Q ^ 2 * ((X.E₀ : ℝ) + X.mStar + 1) := by ring
    _ ≤ X.a := P3

theorem pow_Rj_le (hX : X.Hyp p K) (j : ℤ) : ((p : ℝ) ^ X.Rj p K j) ≤ Tj X p K j := by
  have B := basics hX
  have hT := Tj_ge hX j
  have hT1 : (1 : ℝ) ≤ Tj X p K j := by
    have h0 : (0 : ℝ) ≤ (X.E₀ : ℝ) + X.mStar := by positivity
    nlinarith [B.p1]
  have hfl : ⌊Tj X p K j⌋₊ ≠ 0 := by
    have : 1 ≤ ⌊Tj X p K j⌋₊ := Nat.le_floor (by simpa using hT1)
    omega
  have h1 : p ^ X.Rj p K j ≤ ⌊Tj X p K j⌋₊ := Nat.pow_log_le_self p hfl
  have h2 : ((⌊Tj X p K j⌋₊ : ℕ) : ℝ) ≤ Tj X p K j := Nat.floor_le (by linarith)
  have h3 : ((p ^ X.Rj p K j : ℕ) : ℝ) ≤ ((⌊Tj X p K j⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at h3
  linarith

theorem lt_pow_Rj (hX : X.Hyp p K) (j : ℤ) : Tj X p K j < (p : ℝ) ^ (X.Rj p K j + 1) := by
  have h1 : ⌊Tj X p K j⌋₊ < p ^ (X.Rj p K j + 1) := Nat.lt_pow_succ_log_self hX.prime.one_lt _
  have h2 : Tj X p K j < (⌊Tj X p K j⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have h3 : ((⌊Tj X p K j⌋₊ : ℕ) : ℝ) + 1 ≤ ((p ^ (X.Rj p K j + 1) : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at h3
  linarith

theorem power_exceeds_max_multiplicity (C₀ : ℝ) : PowerExceedsMaxMultiplicity C₀ := by
  intro p n' r K _ _ _ X hX _ _ j
  have B := basics hX
  have h1 := Tj_ge hX j
  have h2 := lt_pow_Rj hX j
  rw [pow_succ] at h2
  have hp : (0 : ℝ) < p := by linarith [B.p1]
  have hE : (0 : ℝ) ≤ X.E₀ := Nat.cast_nonneg _
  have hm : (0 : ℝ) ≤ X.mStar := Nat.cast_nonneg _
  have h3 : 4 * ((X.E₀ : ℝ) + X.mStar + 1) < (p : ℝ) ^ X.Rj p K j := by
    by_contra hcon
    push_neg at hcon
    have := mul_le_mul_of_nonneg_right hcon hp.le
    nlinarith
  have h4 : (X.mStar : ℝ) < ((p ^ X.Rj p K j : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast h4

theorem l42b (hX : X.Hyp p K) (j y : ℤ) (hy : y ∈ X.F.letters j) :
    8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ (X.F.dist j y + X.Rj p K j) ≤ X.a := by
  have b := basics hX
  have hd := den_pos hX j
  have hy' := mem_letters_bounds hy
  have hdist : X.F.dist j y ≤ X.F.dist j (X.F.fr (j - 1) 0) := by
    unfold Frames.dist
    exact Int.toNat_le_toNat (by linarith [hy'.1])
  have hp1 : (1 : ℝ) ≤ p := b.p1.le
  have hpow : (p : ℝ) ^ X.F.dist j y ≤ (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) := pow_le_pow_right₀ hp1 hdist
  have hR := pow_Rj_le hX j
  have hY : 0 ≤ X.Y := by linarith [b.Y1]
  have hTa : 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) * Tj X p K j = X.a := by
    unfold Tj
    exact mul_div_cancel₀ _ hd.ne'
  have hc0 : 0 ≤ 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hY) (sq_nonneg _)) (Nat.cast_nonneg _)
  have hm := mul_le_mul_of_nonneg_left (mul_le_mul hpow hR (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)) hc0
  rw [pow_add]
  calc 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ X.F.dist j y * (p : ℝ) ^ X.Rj p K j)
      ≤ 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) * Tj X p K j) := hm
    _ = X.a := by rw [← hTa]; ring

end Num

end Formalism.MainNotions.SelectionLemmas.Pf
