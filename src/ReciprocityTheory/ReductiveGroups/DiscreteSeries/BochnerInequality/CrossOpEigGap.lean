module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Weights
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.KUnitB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Numerics

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.InnerCrossOpEigEqZero
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.BigCas
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.BigCasA
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.BigCasimir

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section AlgGen

variable {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool}

end AlgGen

section Slots

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem ofCoords_apply {X : Type*} [AddCommGroup X] [Module ℂ X] (k : ℕ)
    (f : (Fin k → Fin n × Fin n) → (X →ₗ[ℂ] M)) (x : X) (κ : Fin k → Fin n × Fin n) :
    (ofCoords k f x) κ = f κ x := rfl

theorem mAct_apply (k : ℕ) (a b : Fin n) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    mAct E k a b F κ = E a b (F κ) := rfl

theorem factorAd_apply (k : ℕ) (i : Fin k) (a b : Fin n) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    factorAd k i a b F κ =
      (if (κ i).1 = a then F (Function.update κ i (b, (κ i).2)) else 0) -
        (if (κ i).2 = b then F (Function.update κ i ((κ i).1, a)) else 0) := by
  show (ofCoords k _ F) κ = _
  rw [ofCoords_apply, LinearMap.sub_apply]
  split_ifs <;> rfl

theorem mem_ncV_iff {k : ℕ} {F : Big n k M} : F ∈ ncV ε V k ↔
    ∀ κ : Fin k → Fin n × Fin n, ((∀ i, ε (κ i).1 ≠ ε (κ i).2) → F κ ∈ V) ∧
      ((¬ ∀ i, ε (κ i).1 ≠ ε (κ i).2) → F κ = 0) := by
  simp only [ncV, Submodule.mem_iInf, Submodule.mem_comap]
  refine forall_congr' fun κ => ?_
  split_ifs with h <;> simp [h] <;> rfl

theorem factorAd_mem_ncV {k : ℕ} (i : Fin k) {a b : Fin n} (hab : ε a = ε b) {F : Big n k M}
    (hF : F ∈ ncV ε V k) : factorAd k i a b F ∈ ncV ε V k := by
  rw [mem_ncV_iff] at hF ⊢
  intro κ
  rcases hx : κ i with ⟨x, y⟩
  simp only [factorAd_apply, hx]
  constructor
  · intro hκ
    have hxy : ε x ≠ ε y := by simpa [hx] using hκ i
    refine Submodule.sub_mem _ ?_ ?_ <;> split_ifs with h <;> try exact Submodule.zero_mem _
    · refine (hF _).1 fun j => ?_
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self]; rw [← hab, ← h]; exact hxy
      · rw [Function.update_of_ne hj]; exact hκ j
    · refine (hF _).1 fun j => ?_
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self]; rw [hab, ← h]; exact hxy
      · rw [Function.update_of_ne hj]; exact hκ j
  · intro hκ
    push Not at hκ
    obtain ⟨j, hj⟩ := hκ
    have key : ∀ p : Fin n × Fin n, ε p.1 = ε p.2 → (¬ ∀ l, ε ((Function.update κ i p) l).1 ≠
        ε ((Function.update κ i p) l).2) := by
      intro p hp h
      by_cases hji : j = i
      · subst hji; exact h j (by simpa using hp)
      · exact h j (by rw [Function.update_of_ne hji]; exact hj)
    have hxy : j = i → ε x = ε y := by intro hji; subst hji; simpa [hx] using hj
    have hc : ∀ p : Fin n × Fin n, (j = i → ε p.1 = ε p.2) → F (Function.update κ i p) = 0 := by
      intro p hp
      by_cases hji : j = i
      · exact (hF _).2 (key p (hp hji))
      · refine (hF _).2 fun h => h j ?_
        rw [Function.update_of_ne hji]; exact hj
    rw [ite_eq_right_iff.2 ?_, ite_eq_right_iff.2 ?_, sub_zero]
    · intro h; subst h; exact hc _ fun hji => by show ε x = ε a; rw [hxy hji, ← hab]
    · intro h; subst h; exact hc _ fun hji => by show ε b = ε y; rw [← hab, hxy hji]

theorem mAct_mem_ncV (hV : IsKStableSub ε E V) (k : ℕ) {a b : Fin n} (hab : ε a = ε b)
    {F : Big n k M} (hF : F ∈ ncV ε V k) : mAct E k a b F ∈ ncV ε V k := by
  rw [mem_ncV_iff] at hF ⊢
  intro κ
  simp only [mAct_apply]
  exact ⟨fun h => hV a b hab _ ((hF κ).1 h), fun h => by rw [(hF κ).2 h, map_zero]⟩

end Slots

end ReciprocityTheory.ChartRestriction.DS.BigCasimir
end
end

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section BigCas

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem bcas_sum_apply {k : ℕ} {ι : Type*} (s : Finset ι) (G : ι → Big n k M)
    (κ : Fin k → Fin n × Fin n) : (∑ i ∈ s, G i) κ = ∑ i ∈ s, G i κ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, PiLp.add_apply, ih]

theorem casimirK_bAct (k : ℕ) :
    casimirK ε (bAct E k) = factorCasimir ε k + casimirK ε (mAct E k) + 2 • ∑ i, crossOp ε E k i := by
  have hc : ∀ (a b c d : Fin n) (i : Fin k),
      mAct E k a b * factorAd (M := M) k i c d = factorAd k i c d * mAct E k a b := by
    intro a b c d i
    refine LinearMap.ext fun F => PiLp.ext fun κ => ?_
    simp only [Module.End.mul_apply, mAct_apply, factorAd_apply]
    split_ifs <;> simp
  have hswap : ∀ g : Fin n → Fin n → Module.End ℂ (Big n k M),
      ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), g b a =
        ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), g a b := by
    intro g
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rcases eq_or_ne (ε a) (ε b) with h | h
    · simp [h]
    · simp [h, h.symm]
  have hX : ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
        mAct E k a b * ∑ i, factorAd (M := M) k i b a =
      ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
        (∑ i, factorAd (M := M) k i a b) * mAct E k b a := by
    have h1 := hswap (fun a b => (∑ i, factorAd (M := M) k i a b) * mAct E k b a)
    rw [← h1]
    simp only [Finset.mul_sum, Finset.sum_mul, hc]
  have hY : ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
        (∑ i, factorAd (M := M) k i a b) * mAct E k b a =
      ∑ i, ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), factorAd k i a b * mAct E k b a := by
    simp only [Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact Finset.sum_comm
  unfold factorCasimir crossOp bAct casimirK
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  rw [hX, hY, two_smul]
  abel

theorem casimirK_mAct_apply (k : ℕ) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    casimirK ε (mAct E k) F κ = casimirK ε E (F κ) := by
  unfold casimirK
  simp only [LinearMap.sum_apply, bcas_sum_apply, Module.End.mul_apply, mAct_apply]

theorem factorCasimir_ncV_one {F : Big n 1 M} (hF : F ∈ ncV ε V 1) :
    factorCasimir ε 1 F = (n : ℂ) • F := by
  classical
  have hz : ∀ x y : Fin n, ε x = ε y → F (fun _ => (x, y)) = 0 := by
    intro x y hxy
    unfold ncV at hF
    have h := (Submodule.mem_iInf _).1 hF (fun _ => (x, y))
    rw [Submodule.mem_comap] at h
    have hc : ¬ ∀ j : Fin 1, ε ((fun _ : Fin 1 => (x, y)) j).1 ≠ ε ((fun _ : Fin 1 => (x, y)) j).2 :=
      fun hall => hall 0 hxy
    rw [if_neg hc, Submodule.mem_bot] at h
    exact h
  have hupd : ∀ (κ : Fin 1 → Fin n × Fin n) (v : Fin n × Fin n),
      Function.update κ 0 v = fun _ => v := by
    intro κ v
    funext i
    rw [Subsingleton.elim i 0, Function.update_self]
  have hbool : ∀ x y w : Bool, x ≠ y → (y = w ↔ ¬ w = x) := by decide
  refine PiLp.ext fun κ => ?_
  obtain ⟨⟨p, q⟩, rfl⟩ : ∃ v, κ = fun _ => v :=
    ⟨κ 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  unfold factorCasimir casimirK
  simp only [LinearMap.sum_apply, bcas_sum_apply, Module.End.mul_apply, Fin.sum_univ_one,
    factorAd_apply, hupd]
  rw [PiLp.smul_apply]
  by_cases hpq : ε p = ε q
  · rw [hz p q hpq, smul_zero]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    by_cases h1 : p = a
    · subst h1
      by_cases h2 : q = b
      · subst h2
        simp [hz _ _ hpq, fun x => hz x x rfl]
      · simp [h2, hz _ _ hpq, fun x => hz x x rfl]
    · by_cases h2 : q = b
      · subst h2
        simp [h1, hz _ _ hpq, fun x => hz x x rfl]
      · simp [h1, h2, fun x => hz x x rfl]
  · have hpq' : p ≠ q := fun h => hpq (h ▸ rfl)
    trans ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
      ((if p = a then F (fun _ => (p, q)) else 0) + (if q = b then F (fun _ => (p, q)) else 0))
    · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      by_cases h1 : p = a
      · subst h1
        by_cases h2 : q = b
        · subst h2
          simp [hpq', Ne.symm hpq']
        · simp [h2, hpq', Ne.symm hpq']
      · by_cases h2 : q = b
        · subst h2
          simp [h1, hpq', Ne.symm hpq']
        · simp [h1, h2]
    · simp only [Finset.sum_add_distrib]
      have h1 : ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
          (if p = a then F (fun _ => (p, q)) else 0) =
          (univ.filter fun b => ε b = ε p).card • F (fun _ => (p, q)) := by
        rw [Finset.sum_eq_single p (fun a _ ha => by simp [Ne.symm ha]) (by simp)]
        simp
      have h2 : ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
          (if q = b then F (fun _ => (p, q)) else 0) =
          (univ.filter fun a => ε q = ε a).card • F (fun _ => (p, q)) := by
        simp only [Finset.sum_ite_eq, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← Finset.sum_filter, Finset.sum_const]
      have hcard : (univ.filter fun b => ε b = ε p).card + (univ.filter fun a => ε q = ε a).card
          = n := by
        have hf : (univ.filter fun a => ε q = ε a) = univ.filter fun a => ¬ (ε a = ε p) :=
          Finset.filter_congr fun a _ => hbool _ _ _ hpq
        rw [hf]
        first
          | rw [Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_univ, Fintype.card_fin]
          | rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
          | rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_neg _ _ _),
              Finset.filter_union_filter_neg_eq, Finset.card_univ, Fintype.card_fin]
          | rw [← Finset.card_union_eq_card_add_card.2 (Finset.disjoint_filter_filter_neg _ _ _),
              Finset.filter_union_filter_neg_eq, Finset.card_univ, Fintype.card_fin]
      rw [h1, h2, ← add_smul, hcard, Nat.cast_smul_eq_nsmul]

theorem factorCasimir_nonneg (k : ℕ) (F : Big n k M) :
    0 ≤ RCLike.re (inner ℂ (factorCasimir (M := M) ε k F) F) := by
  have hadj : ∀ (a b : Fin n) (X Y : Big n k M),
      inner ℂ ((∑ i, factorAd (M := M) k i a b) X) Y =
        inner ℂ X ((∑ i, factorAd (M := M) k i b a) Y) := by
    intro a b X Y
    simp only [LinearMap.sum_apply, sum_inner, inner_sum, factorAd_adjoint]
  unfold factorCasimir casimirK
  beta_reduce
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.sum_apply, sum_inner, map_sum]
  refine Finset.sum_nonneg fun a _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.sum_apply, sum_inner, map_sum]
  refine Finset.sum_nonneg fun b _ => ?_
  rw [Module.End.mul_apply, hadj]
  exact inner_self_nonneg

theorem crossOp_symm (hU : IsInfUnitary ε E) (k : ℕ) (i : Fin k) (F G : Big n k M) :
    inner ℂ (crossOp ε E k i F) G = inner ℂ F (crossOp ε E k i G) := by
  have hU' : ∀ (a b : Fin n) (x y : M),
      inner ℂ (E a b x) y = adjSign ε a b * inner ℂ x (E b a y) := hU
  have hm : ∀ (a b : Fin n) (X Y : Big n k M),
      inner ℂ (mAct E k a b X) Y = adjSign ε a b * inner ℂ X (mAct E k b a Y) := by
    intro a b X Y
    simp only [PiLp.inner_apply, mAct_apply, hU', Finset.mul_sum]
  have hc : ∀ (a b c d : Fin n),
      mAct E k a b * factorAd (M := M) k i c d = factorAd k i c d * mAct E k a b := by
    intro a b c d
    refine LinearMap.ext fun F => PiLp.ext fun κ => ?_
    simp only [Module.End.mul_apply, mAct_apply, factorAd_apply]
    split_ifs <;> simp
  have hswap : ∀ g : Fin n → Fin n → ℂ,
      ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), g b a =
        ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), g a b := by
    intro g
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rcases eq_or_ne (ε a) (ε b) with h | h
    · simp [h]
    · simp [h, h.symm]
  unfold crossOp
  simp only [LinearMap.sum_apply, sum_inner, inner_sum, Module.End.mul_apply]
  have h1 := hswap (fun a b => inner ℂ F (factorAd k i a b (mAct E k b a G)))
  rw [← h1]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  have hab : ε b = ε a := (Finset.mem_filter.1 hb).2
  rw [factorAd_adjoint, hm, show adjSign ε b a = 1 by simp [adjSign, hab], one_mul]
  congr 1
  exact LinearMap.congr_fun (hc a b b a) G

theorem crossOp_comm (hE : IsGlRep E) (k : ℕ) (i : Fin k) {a b : Fin n} (hab : ε a = ε b) :
    crossOp ε E k i * bAct E k a b = bAct E k a b * crossOp ε E k i := by
  classical
  have hmrel : ∀ a b c d : Fin n, mAct E k a b * mAct E k c d - mAct E k c d * mAct E k a b =
      (if b = c then mAct E k a d else 0) - (if d = a then mAct E k c b else 0) := by
    intro a b c d
    refine LinearMap.ext fun F => PiLp.ext fun κ => ?_
    have h := LinearMap.congr_fun (hE a b c d) (F κ)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    simp only [LinearMap.sub_apply, Module.End.mul_apply, PiLp.sub_apply, mAct_apply]
    rw [h]
    split_ifs <;> simp [mAct_apply]
  have hterm : ∀ c d : Fin n,
      (mAct E k a b + factorAd k i a b) * (factorAd k i c d * mAct E k d c) -
        (factorAd k i c d * mAct E k d c) * (mAct E k a b + factorAd k i a b) =
      factorAd k i c d * (mAct E k a b * mAct E k d c - mAct E k d c * mAct E k a b) +
        (factorAd k i a b * factorAd k i c d - factorAd k i c d * factorAd k i a b) * mAct E k d c := by
    intro c d
    have h1 := mAct_factorAd_comm (E := E) k i a b c d
    have h2 := mAct_factorAd_comm (E := E) k i d c a b
    calc _ = mAct E k a b * factorAd k i c d * mAct E k d c +
          factorAd k i a b * factorAd k i c d * mAct E k d c -
          factorAd k i c d * mAct E k d c * mAct E k a b -
          factorAd k i c d * (mAct E k d c * factorAd k i a b) := by noncomm_ring
      _ = _ := by
        rw [h1, h2]
        noncomm_ring
  have key : ∑ c, ∑ d ∈ univ.filter (fun d => ε d = ε c),
      (factorAd k i c d * ((if b = d then mAct E k a c else 0) - (if c = a then mAct E k d b else 0)) +
        ((if b = c then factorAd k i a d else 0) - (if d = a then factorAd k i c b else 0)) *
          mAct E k d c) = 0 := by
    simp [mul_sub, sub_mul, mul_ite, ite_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel, hab]
  have hmain : (mAct E k a b + factorAd k i a b) * crossOp ε E k i -
      crossOp ε E k i * (mAct E k a b + factorAd k i a b) = 0 := by
    unfold crossOp
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    rw [← key]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hterm, hmrel, factorAd_commutator]
  have hother : ∀ j ∈ univ.erase i,
      factorAd (M := M) k j a b * crossOp ε E k i = crossOp ε E k i * factorAd k j a b := by
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    unfold crossOp
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← mul_assoc, factorAd_comm_of_ne k hji, mul_assoc, ← mAct_factorAd_comm (E := E) k j d c a b,
      ← mul_assoc]
  have hsum : (∑ j ∈ univ.erase i, factorAd (M := M) k j a b) * crossOp ε E k i =
      crossOp ε E k i * ∑ j ∈ univ.erase i, factorAd k j a b := by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl hother
  have hsplit : bAct E k a b =
      (mAct E k a b + factorAd k i a b) + ∑ j ∈ univ.erase i, factorAd (M := M) k j a b := by
    unfold bAct
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    abel
  rw [hsplit, mul_add, add_mul, ← hsum]
  have h := sub_eq_zero.1 hmain
  rw [h]

theorem crossOp_mem_ncV (hV : IsKStableSub ε E V) (k : ℕ) (i : Fin k) {F : Big n k M}
    (hF : F ∈ ncV ε V k) : crossOp ε E k i F ∈ ncV ε V k := by
  classical
  have hmem : ∀ G : Big n k M, G ∈ ncV ε V k ↔
      ∀ κ, G κ ∈ (if ∀ j, ε (κ j).1 ≠ ε (κ j).2 then V else ⊥) := by
    intro G
    unfold ncV
    simp only [Submodule.mem_iInf, Submodule.mem_comap]
    exact Iff.rfl
  rw [hmem] at hF ⊢
  intro κ
  have hc : ∀ p : Fin n × Fin n, ε p.1 = ε (κ i).1 → ε p.2 = ε (κ i).2 →
      ((∀ j, ε ((Function.update κ i p) j).1 ≠ ε ((Function.update κ i p) j).2) ↔
        ∀ j, ε (κ j).1 ≠ ε (κ j).2) := by
    intro p h1 h2
    refine forall_congr' fun j => ?_
    by_cases hj : j = i
    · subst hj
      simp [Function.update_apply, h1, h2]
    · simp [Function.update_apply, hj]
  have hval : (crossOp ε E k i F) κ = ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
      ((if (κ i).1 = a then E b a (F (Function.update κ i (b, (κ i).2))) else 0) -
        (if (κ i).2 = b then E b a (F (Function.update κ i ((κ i).1, a))) else 0)) := by
    unfold crossOp
    simp only [LinearMap.sum_apply, bcas_sum_apply, Module.End.mul_apply, factorAd_apply,
      mAct_apply]
  rw [hval]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b hb => ?_
  have hab : ε b = ε a := (Finset.mem_filter.1 hb).2
  have hT : ∀ v ∈ (if (∀ j, ε (κ j).1 ≠ ε (κ j).2) then V else (⊥ : Submodule ℂ M)),
      E b a v ∈ (if (∀ j, ε (κ j).1 ≠ ε (κ j).2) then V else (⊥ : Submodule ℂ M)) := by
    intro v hv
    split_ifs at hv ⊢ with hcκ
    · exact hV b a hab v hv
    · rw [Submodule.mem_bot] at hv ⊢
      rw [hv, map_zero]
  refine Submodule.sub_mem _ ?_ ?_
  · by_cases h1 : (κ i).1 = a
    · rw [if_pos h1]
      refine hT _ ?_
      have hFκ := hF (Function.update κ i (b, (κ i).2))
      rwa [if_congr (hc (b, (κ i).2) (by show ε b = ε (κ i).1; rw [hab, h1]) rfl) rfl rfl]
        at hFκ
    · rw [if_neg h1]
      exact Submodule.zero_mem _
  · by_cases h2 : (κ i).2 = b
    · rw [if_pos h2]
      refine hT _ ?_
      have hFκ := hF (Function.update κ i ((κ i).1, a))
      rwa [if_congr (hc ((κ i).1, a) rfl (by show ε a = ε (κ i).2; rw [h2, hab])) rfl rfl]
        at hFκ
    · rw [if_neg h2]
      exact Submodule.zero_mem _

end BigCas

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section One

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

theorem Wm_le_ncV : Wm ε E V ≤ ncV ε V 1 := by
  unfold Wm
  exact iSup₂_le fun _ _ => inf_le_right

theorem inner_crossOp_eig_eq_zero (hU : IsInfUnitary ε E) {θ θ' : ℝ} (hθ : θ ≠ θ')
    {u v : Big n 1 M} (hu : crossOp ε E 1 0 u = (θ : ℂ) • u)
    (hv : crossOp ε E 1 0 v = (θ' : ℂ) • v) : inner ℂ u v = 0 := by
  have h := crossOp_symm hU 1 0 u v
  rw [hu, hv, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h
  have hne : (θ : ℂ) ≠ (θ' : ℂ) := by exact_mod_cast hθ
  by_contra h0
  exact hne (mul_right_cancel₀ h0 h)

theorem Wm_perp_Wp (hU : IsInfUnitary ε E) {x y : Big n 1 M} (hx : x ∈ Wm ε E V)
    (hy : y ∈ Wp ε E V) : inner ℂ x y = 0 := by
  have h : (Wm ε E V).IsOrtho (Wp ε E V) := by
    unfold Wm Wp
    refine Submodule.isOrtho_iSup_left.mpr fun θ => Submodule.isOrtho_iSup_left.mpr fun hθ =>
      Submodule.isOrtho_iSup_right.mpr fun θ' => Submodule.isOrtho_iSup_right.mpr fun hθ' => ?_
    rw [Submodule.isOrtho_iff_inner_eq]
    intro u hu v hv
    rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff] at hu hv
    exact inner_crossOp_eig_eq_zero hU (ne_of_lt (hθ.trans hθ')) hu.1 hv.1
  exact Submodule.isOrtho_iff_inner_eq.mp h x hx y hy

theorem mem_V_of_mem_ncV {k : ℕ} {F : Big n k M} (hF : F ∈ ncV ε V k)
    (κ : Fin k → Fin n × Fin n) : F κ ∈ V := by
  exact ncV_mem hF κ

private theorem casimirK_eq_casValK_smul_of_isKHWVec {X : Type*} [AddCommGroup X] [Module ℂ X]
    {A : Fin n → Fin n → Module.End ℂ X} (hA : IsGlRep A) {μ : Fin n → ℝ} {w : X}
    (hw : IsKHWVec ε A μ w) : casimirK ε A w = (casValK ε μ : ℂ) • w := by
  have hA' : ∀ a b c d : Fin n, A a b * A c d - A c d * A a b =
      (if b = c then A a d else 0) - (if d = a then A c b else 0) := hA
  have term : ∀ a b : Fin n, ε b = ε a → A a b (A b a w) =
      ((((if b = a then μ a ^ 2 else 0) + (if a < b then μ a - μ b else 0) : ℝ)) : ℂ) • w := by
    intro a b hab
    rcases lt_trichotomy b a with h | h | h
    · rw [hw.2 b a h hab, map_zero, if_neg (ne_of_lt h), if_neg (lt_asymm h)]
      simp
    · subst h
      rw [if_pos rfl, if_neg (lt_irrefl b), add_zero, hw.1 b, map_smul, hw.1 b, smul_smul,
        ← Complex.ofReal_mul, ← sq]
    · have e := LinearMap.congr_fun (hA' a b b a) w
      simp only [LinearMap.sub_apply, Module.End.mul_apply, eq_self_iff_true, if_true,
        hw.2 a b h hab.symm, map_zero, sub_zero] at e
      rw [e, if_neg (ne_of_gt h), if_pos h, hw.1 a, hw.1 b]
      simp [sub_smul]
  have hsum : casimirK ε A w = ((∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
      ((if b = a then μ a ^ 2 else 0) + (if a < b then μ a - μ b else 0)) : ℝ) : ℂ) • w := by
    simp only [casimirK, LinearMap.sum_apply, Module.End.mul_apply, Complex.ofReal_sum,
      Finset.sum_smul]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb =>
      term a b (Finset.mem_filter.mp hb).2
  have hA2 : ∀ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
      ((if b = a then μ a ^ 2 else 0) + (if a < b then μ a - μ b else 0)) =
      μ a ^ 2 + ((∑ b, if a < b ∧ ε b = ε a then μ a else 0) -
        ∑ b, if a < b ∧ ε b = ε a then μ b else 0) := by
    intro a
    rw [Finset.sum_filter, ← Finset.sum_sub_distrib]
    have h2 : μ a ^ 2 = ∑ b, (if b = a then μ a ^ 2 else 0) := by simp
    conv_rhs => rw [h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp_all
  have hC : (∑ a, ∑ b, if a < b ∧ ε b = ε a then μ b else 0) =
      ∑ a, ∑ b, if b < a ∧ ε b = ε a then μ a else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases h1 : b < a ∧ ε a = ε b
    · rw [if_pos h1, if_pos ⟨h1.1, h1.2.symm⟩]
    · rw [if_neg h1, if_neg fun h2 => h1 ⟨h2.1, h2.2.symm⟩]
  have hρ : ∀ a, 2 * rhoC ε a = (∑ b, if a < b ∧ ε b = ε a then (1 : ℝ) else 0) -
      ∑ b, if b < a ∧ ε b = ε a then (1 : ℝ) else 0 := by
    intro a
    simp only [rhoC]
    rw [Finset.sum_boole, Finset.sum_boole]
    ring
  have hR : casValK ε μ = ∑ a, (μ a ^ 2 + μ a * (2 * rhoC ε a)) := by
    simp only [casValK, nsq, dot, Pi.add_apply]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hsum, hR, Finset.sum_congr rfl fun a _ => hA2 a]
  congr 2
  simp only [hρ, mul_sub, Finset.mul_sum, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, hC]

theorem crossOp_khw (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V) {x : Big n 1 M} (hx : x ∈ ncV ε V 1) (hx0 : x ≠ 0)
    {ν : Fin n → ℝ} (hν : IsKHWVec ε (bAct E 1) ν x) :
    ∃ r s : Fin n, ε r ≠ ε s ∧ ν = lowK ε lam + root r s ∧
      (2 : ℂ) • crossOp ε E 1 0 x =
        ((casValK ε ν - n - casValK ε (lowK ε lam) : ℝ) : ℂ) • x := by
  obtain ⟨γ, hγ, hνγ⟩ := khw_big_weight hE hV hx hx0 hν
  refine ⟨(γ 0).1, (γ 0).2, hγ 0, ?_, ?_⟩
  · rw [Fin.sum_univ_one] at hνγ
    rw [← hνγ]
    abel
  · have hm : casimirK ε (mAct E 1) x = (casValK ε (lowK ε lam) : ℂ) • x := by
      ext κ
      rw [casimirK_mAct_apply, casimirK_irr hE hV _ (ncV_mem hx κ)]
      rfl
    have hcas := LinearMap.congr_fun (casimirK_bAct (ε := ε) (E := E) 1) x
    rw [casimirK_eq_casValK_smul_of_isKHWVec (bAct_isGlRep hE 1) hν] at hcas
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Fin.sum_univ_one, factorCasimir_ncV_one hx,
      hm, two_smul] at hcas
    rw [two_smul]
    push_cast
    rw [sub_smul, sub_smul, hcas]
    abel

theorem Wm_kStable (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V) : IsKStableSub ε (bAct E 1) (Wm ε E V) := by
  intro a b hab v hv
  have hVs : IsKStableSub ε E V := hV.2.1
  have hle : Wm ε E V ≤ (Wm ε E V).comap (bAct E 1 a b) := by
    unfold Wm
    refine iSup₂_le fun θ hθ x hx => ?_
    rw [Submodule.mem_comap]
    rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff] at hx
    have hc : crossOp ε E 1 0 (bAct E 1 a b x) = bAct E 1 a b (crossOp ε E 1 0 x) :=
      LinearMap.congr_fun (crossOp_comm hE 1 0 hab) x
    have hmem : bAct E 1 a b x ∈
        Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1 := by
      rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff]
      refine ⟨?_, ncV_kStable hVs 1 a b hab x hx.2⟩
      rw [hc, hx.1, map_smul]
    exact Submodule.mem_iSup_of_mem θ (Submodule.mem_iSup_of_mem hθ hmem)
  exact hle hv

end One

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section OneBAux

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

private lemma card_opposite_sign_above_add_below_le (e : Fin n → Bool) (a : Fin n) :
    ((univ.filter fun b => a < b ∧ e b ≠ e a).card : ℝ) +
      ((univ.filter fun b => b < a ∧ e b ≠ e a).card : ℝ) ≤
      ((univ.filter fun b => e b ≠ e a).card : ℝ) := by
  have hd : Disjoint (univ.filter fun b => a < b ∧ e b ≠ e a)
      (univ.filter fun b => b < a ∧ e b ≠ e a) := by
    rw [Finset.disjoint_filter]
    intro b _ h1 h2
    exact lt_asymm h1.1 h2.1
  rw [← Nat.cast_add, ← Finset.card_union_of_disjoint hd]
  exact_mod_cast Finset.card_le_card (fun b hb => by
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    rcases hb with h | h
    · exact h.2
    · exact h.2)

private lemma card_opposite_sign_add_le_of_ne (e : Fin n → Bool) {r s : Fin n} (hrs : e r ≠ e s) :
    ((univ.filter fun b => e b ≠ e r).card : ℝ) + ((univ.filter fun b => e b ≠ e s).card : ℝ) ≤ n := by
  have key : ∀ x y z : Bool, x ≠ y → x ≠ z → y ≠ z → False := by decide
  have hd : Disjoint (univ.filter fun b => e b ≠ e r) (univ.filter fun b => e b ≠ e s) := by
    rw [Finset.disjoint_filter]
    intro b _ h1 h2
    exact key _ _ _ h1 h2 hrs
  rw [← Nat.cast_add, ← Finset.card_union_of_disjoint hd]
  exact_mod_cast (Finset.card_le_univ _).trans (by simp)

theorem crossOp_eig_gap (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {θ : ℝ} {y : Big n 1 M}
    (hy : y ∈ Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1) (hy0 : y ≠ 0) :
    (0 < h - n + 1 ∧ h - n + 1 ≤ θ) ∨ (θ ≤ -h - 1 ∧ -h - 1 < 0) := by
  classical
  have hVfd : FiniteDimensional ℂ V := hV.1
  haveI := finiteDimensional_ncV (ε := ε) hVfd 1
  set S := Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1 with hSdef
  haveI hfd : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le inf_le_right

  have hSst : IsKStableSub ε (bAct E 1) S := by
    intro a b hab v hv
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff] at hv1 ⊢
      have hc := congrArg (fun T : Module.End ℂ (Big n 1 M) => T v) (crossOp_comm hE 1 0 hab)
      simp only [Module.End.mul_apply] at hc
      rw [hc, hv1, map_smul]
    · simp only [bAct, LinearMap.add_apply, LinearMap.sum_apply]
      exact Submodule.add_mem _ (BigCasimir.mAct_mem_ncV hV.2.1 1 hab hv2)
        (Submodule.sum_mem _ fun i _ => BigCasimir.factorAd_mem_ncV i hab hv2)

  have hCS : ∀ x ∈ S, casimirK ε (bAct E 1) x ∈ S := fun x hx => casimirK_mem_of_kStable hSst hx
  let T : Module.End ℂ S := (casimirK ε (bAct E 1)).restrict hCS
  haveI : Nontrivial S := ⟨⟨⟨y, hy⟩, 0, fun h => hy0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hvT := Module.End.mem_eigenspace_iff.1 hv.1
  have hx0 : (v : Big n 1 M) ≠ 0 := fun h => hv.2 (Subtype.ext h)
  have hxθ : casimirK ε (bAct E 1) (v : Big n 1 M) = c • (v : Big n 1 M) := congrArg Subtype.val hvT
  obtain ⟨w, hwS, hw0, -, μ, hμw, -⟩ :=
    eig_casimirK (bAct_isGlRep hE 1) (bAct_isKUnitary hU 1) hfd hSst v.2 hx0 hxθ
  obtain ⟨hw1, hw2⟩ := Submodule.mem_inf.1 hwS
  obtain ⟨r, s, hε, hμ, hcross⟩ := crossOp_khw hE hU hV hw2 hw0 hμw
  have hθw : crossOp ε E 1 0 w = (θ : ℂ) • w := Module.End.mem_eigenspace_iff.1 hw1
  rw [hθw, smul_smul] at hcross
  have h2 := smul_left_injective ℂ hw0 hcross
  have h2θ : 2 * θ = casValK ε μ - n - casValK ε (lowK ε lam) := by
    have h3 : ((2 * θ : ℝ) : ℂ) = ((casValK ε μ - n - casValK ε (lowK ε lam) : ℝ) : ℂ) := by
      rw [← h2]
      push_cast
      ring
    exact_mod_cast h3

  have hrs : r ≠ s := fun h => hε (congrArg ε h)
  have hroot : ∀ u : Fin n → ℝ, nsq (u + root r s) - nsq u = 2 * (u r - u s) + 2 := by
    intro u
    have hs : ∀ a, root r s a = (if a = r then (1 : ℝ) else 0) - (if a = s then 1 else 0) := fun a => by
      simp [root, Pi.single_apply]
    simp only [nsq, dot, Pi.add_apply, hs]
    rw [← Finset.sum_sub_distrib]
    have e : ∀ a, (u a + ((if a = r then (1 : ℝ) else 0) - (if a = s then 1 else 0))) *
        (u a + ((if a = r then (1 : ℝ) else 0) - (if a = s then 1 else 0))) - u a * u a =
        2 * (if a = r then u a else 0) - 2 * (if a = s then u a else 0) +
          (if a = r then (1 : ℝ) else 0) + (if a = s then (1 : ℝ) else 0) := fun a => by
      split_ifs with h1 h2 h2
      · exact absurd (h1.symm.trans h2) hrs
      all_goals ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hcas : casValK ε μ - casValK ε (lowK ε lam) =
      2 * ((lowK ε lam + rhoC ε) r - (lowK ε lam + rhoC ε) s) + 2 := by
    rw [hμ]
    unfold casValK
    rw [show lowK ε lam + root r s + rhoC ε = (lowK ε lam + rhoC ε) + root r s by abel]
    linarith [hroot (lowK ε lam + rhoC ε)]
  have hL : ∀ a, (lowK ε lam + rhoC ε) a = lam a + rhoN ε a := fun a => by simp [lowK]
  rw [hL r, hL s] at hcas
  have hθ : θ = (lam r + rhoN ε r) - (lam s + rhoN ε s) + 1 - n / 2 := by linarith

  have hrN : ∀ a, rhoN ε a = (((univ.filter fun b => a < b ∧ ε b ≠ ε a).card : ℝ) -
      ((univ.filter fun b => b < a ∧ ε b ≠ ε a).card : ℝ)) / 2 := fun a => rfl
  have hPr := card_opposite_sign_above_add_below_le ε r
  have hPs := card_opposite_sign_above_add_below_le ε s
  have hO := card_opposite_sign_add_le_of_ne ε hε
  have hpq : 1 ≤ (pOf ε : ℝ) ∧ 1 ≤ (qOf ε : ℝ) := by
    have key : ∀ x y c : Bool, x ≠ y → x ≠ c → y = c := by decide
    have hmem : ∀ c : Bool, ∃ a, ε a = c := fun c => by
      by_cases h1 : ε r = c
      · exact ⟨r, h1⟩
      · exact ⟨s, key _ _ _ hε h1⟩
    unfold pOf qOf
    obtain ⟨a1, ha1⟩ := hmem true
    obtain ⟨a2, ha2⟩ := hmem false
    exact ⟨Nat.one_le_cast.2 (Finset.card_pos.2 ⟨a1, by simp [ha1]⟩),
      Nat.one_le_cast.2 (Finset.card_pos.2 ⟨a2, by simp [ha2]⟩)⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpq1 : (1 : ℝ) * 1 ≤ (pOf ε : ℝ) * (qOf ε : ℝ) :=
    mul_le_mul hpq.1 hpq.2 zero_le_one (by linarith [hpq.1])
  have hnpq : (n : ℝ) * 1 ≤ (n : ℝ) * ((pOf ε : ℝ) * (qOf ε : ℝ)) := by
    rw [one_mul] at hpq1
    exact mul_le_mul_of_nonneg_left hpq1 hn0
  have hhn : (n : ℝ) + 1 < h := by nlinarith
  rcases le_abs'.1 (hh r s hε) with hcase | hcase
  ·
    have hlt : s < r := not_le.1 fun hle => absurd (hmono.antitone hle) (not_le.2 (by linarith))
    have h1 : (1 : ℝ) ≤ ((univ.filter fun b => s < b ∧ ε b ≠ ε s).card : ℝ) :=
      Nat.one_le_cast.2 (Finset.card_pos.2 ⟨r, by simp [hlt, hε]⟩)
    have h2' : (1 : ℝ) ≤ ((univ.filter fun b => b < r ∧ ε b ≠ ε r).card : ℝ) :=
      Nat.one_le_cast.2 (Finset.card_pos.2 ⟨s, by simp [hlt, Ne.symm hε]⟩)
    right
    refine ⟨?_, by linarith⟩
    rw [hθ, hrN r, hrN s]
    linarith
  ·
    have hlt : r < s := not_le.1 fun hle => absurd (hmono.antitone hle) (not_le.2 (by linarith))
    have h1 : (1 : ℝ) ≤ ((univ.filter fun b => r < b ∧ ε b ≠ ε r).card : ℝ) :=
      Nat.one_le_cast.2 (Finset.card_pos.2 ⟨s, by simp [hlt, Ne.symm hε]⟩)
    have h2' : (1 : ℝ) ≤ ((univ.filter fun b => b < s ∧ ε b ≠ ε s).card : ℝ) :=
      Nat.one_le_cast.2 (Finset.card_pos.2 ⟨r, by simp [hlt, hε]⟩)
    left
    refine ⟨by linarith, ?_⟩
    rw [hθ, hrN r, hrN s]
    linarith

end OneBAux

end ReciprocityTheory.ChartRestriction.DS
