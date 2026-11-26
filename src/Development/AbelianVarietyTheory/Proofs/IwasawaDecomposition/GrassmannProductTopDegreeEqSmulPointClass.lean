module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealConeCoveredByStarAtPoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RenVar
noncomputable section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GrassTop

def wt {ι : Type} (d : ι × ℕ →₀ ℕ) : ℕ := d.sum fun x i => x.2 * i

def rel (k : ℕ) : MvPolynomial (Bool × ℕ) ℝ :=
  ∑ a ∈ Finset.range (k + 1), C ((-1 : ℝ) ^ (k - a)) * X (true, a) * X (false, k - a)

def gens (p q : ℕ) : Set (MvPolynomial (Bool × ℕ) ℝ) :=
  {f | (∃ k, 1 ≤ k ∧ f = rel k) ∨ (∃ b, f = X (b, 0) - 1) ∨ (∃ k, p < k ∧ f = X (true, k)) ∨
    (∃ k, q < k ∧ f = X (false, k))}

def J (p q : ℕ) : Ideal (MvPolynomial (Bool × ℕ) ℝ) := Ideal.span (gens p q)

def basis (p q : ℕ) : Set (MvPolynomial (Bool × ℕ) ℝ) :=
  {f | (∃ d, wt d < p * q ∧ f = monomial d 1) ∨ f = X (true, p) ^ q}

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def renVar {H : Host E} (τ : GlobalTheory.AllWt.Psi H) (y : Bool × ℕ) : (E →+* ℂ) × ℕ :=
  (if y.1 then τ.1 else conjEmb τ.1, y.2)

def ren {H : Host E} (τ : GlobalTheory.AllWt.Psi H) :
    MvPolynomial (Bool × ℕ) ℝ →ₐ[ℝ] MvPolynomial ((E →+* ℂ) × ℕ) ℝ :=
  rename (renVar τ)

end GlobalTheory.GrassTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleFormEqMulPointClassValue
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleChernFormProdGrassmannianBasisCopies
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleChernFormProdGrassmannianBasisCopies
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

noncomputable section

namespace GlobalTheory.GrassTopProd

theorem wt_add {ι : Type} (a b : ι × ℕ →₀ ℕ) :
    GlobalTheory.GrassTop.wt (a + b) = GlobalTheory.GrassTop.wt a + GlobalTheory.GrassTop.wt b := by
  unfold GlobalTheory.GrassTop.wt
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)

theorem wt_sum {ι κ : Type} (s : Finset κ) (d : κ → ι × ℕ →₀ ℕ) :
    GlobalTheory.GrassTop.wt (∑ k ∈ s, d k) = ∑ k ∈ s, GlobalTheory.GrassTop.wt (d k) := by
  induction s using Finset.induction_on with
  | empty => simp [GlobalTheory.GrassTop.wt]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, wt_add, ih]

theorem wt_mapDomain {ι κ : Type} (f : ι × ℕ → κ × ℕ) (hf : ∀ x, (f x).2 = x.2) (d : ι × ℕ →₀ ℕ) :
    GlobalTheory.GrassTop.wt (d.mapDomain f) = GlobalTheory.GrassTop.wt d := by
  unfold GlobalTheory.GrassTop.wt
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by ring)]
  simp [hf]

theorem adm_apply_prod_ren_eq_ite_mul_pointPoly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (g : GlobalTheory.AllWt.Psi H → MvPolynomial (Bool × ℕ) ℝ), (∀ τ, g τ ∈ GlobalTheory.GrassTop.basis Dw.p Dw.q) →
    ∀ Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ, GlobalTheory.Schubert.admitted H Dw Θ →
    Θ (∏ τ, GlobalTheory.GrassTop.ren τ (g τ)) = (if ∀ τ, g τ = X (true, Dw.p) ^ Dw.q then
      (-1 : ℝ) ^ (Dw.p * Dw.q * Fintype.card (GlobalTheory.AllWt.Psi H)) else 0) * Θ (GlobalTheory.LieBase.pointPoly H Dw) := by
  intro E _ _ _ H Dw g hg Θ hΘ
  have hm : ∀ τ : GlobalTheory.AllWt.Psi H, Dw.mult τ.1 = Dw.p := fun τ => GlobalTheory.PointChern.mult_of_mem Dw τ.2
  split_ifs with hall
  · have h1 : ∏ τ, GlobalTheory.GrassTop.ren τ (g τ) = ∏ τ : GlobalTheory.AllWt.Psi H, X (τ.1, Dw.p) ^ Dw.q := by
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [hall τ, map_pow]
      simp [GlobalTheory.GrassTop.ren, GlobalTheory.GrassTop.renVar]
    have h2 : GlobalTheory.LieBase.pointPoly H Dw = C ((-1 : ℝ) ^ (Dw.p * Dw.q * Fintype.card (GlobalTheory.AllWt.Psi H))) *
        ∏ τ : GlobalTheory.AllWt.Psi H, X (τ.1, Dw.p) ^ Dw.q := by
      unfold GlobalTheory.LieBase.pointPoly
      rw [Finset.prod_congr rfl (fun τ _ => by rw [hm τ])]
      rw [show Dw.p + Dw.q - Dw.p = Dw.q by omega]
      simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← C_pow, ← pow_mul]
    rw [h1, h2, ← smul_eq_C_mul, LinearMap.map_smul, smul_eq_mul, ← mul_assoc, ← mul_pow]
    norm_num
  · push_neg at hall
    obtain ⟨σ, hσ⟩ := hall
    have key : ∀ τ, ∃ d : Bool × ℕ →₀ ℕ, GlobalTheory.GrassTop.wt d ≤ Dw.p * Dw.q ∧
        (g τ ≠ X (true, Dw.p) ^ Dw.q → GlobalTheory.GrassTop.wt d < Dw.p * Dw.q) ∧ g τ = monomial d 1 := by
      intro τ
      rcases hg τ with ⟨d, hd, he⟩ | he
      · exact ⟨d, hd.le, fun _ => hd, he⟩
      · refine ⟨Finsupp.single (true, Dw.p) Dw.q, ?_, fun h => absurd he h, ?_⟩
        · simp [GlobalTheory.GrassTop.wt, Finsupp.sum_single_index, mul_comm]
        · rw [he, X_pow_eq_monomial]
    choose d hd1 hd2 hd3 using key
    have hprod : ∏ τ, GlobalTheory.GrassTop.ren τ (g τ) =
        monomial (∑ τ, (d τ).mapDomain (GlobalTheory.GrassTop.renVar τ)) 1 := by
      rw [monomial_sum_one]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [hd3 τ, GlobalTheory.GrassTop.ren, rename_monomial]
    have hw : GlobalTheory.GrassTop.wt (∑ τ, (d τ).mapDomain (GlobalTheory.GrassTop.renVar τ)) <
        Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q) := by
      rw [wt_sum]
      calc ∑ τ, GlobalTheory.GrassTop.wt ((d τ).mapDomain (GlobalTheory.GrassTop.renVar τ))
          = ∑ τ, GlobalTheory.GrassTop.wt (d τ) :=
            Finset.sum_congr rfl fun τ _ => wt_mapDomain (GlobalTheory.GrassTop.renVar τ) (fun _ => rfl) (d τ)
        _ < ∑ _τ : GlobalTheory.AllWt.Psi H, Dw.p * Dw.q :=
            Finset.sum_lt_sum (fun τ _ => hd1 τ) ⟨σ, Finset.mem_univ _, hd2 σ hσ⟩
        _ = Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q) := by simp
    have h0 : Θ (monomial (∑ τ, (d τ).mapDomain (GlobalTheory.GrassTop.renVar τ)) 1) = 0 :=
      hΘ.2.2.2 (∑ τ, (d τ).mapDomain (GlobalTheory.GrassTop.renVar τ)) hw.ne
    rw [hprod, h0, zero_mul]

end GlobalTheory.GrassTopProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleChernFormProdGrassmannianBasisCopiesStatement
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissibleChernForm_prod_grassmannianBasisCopies : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (g : GlobalTheory.AllWt.Psi H → MvPolynomial (Bool × ℕ) ℝ), (∀ τ, g τ ∈ GlobalTheory.GrassTop.basis Dw.p Dw.q) → ∀ Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ, GlobalTheory.Schubert.admitted H Dw Θ → Θ (∏ τ, GlobalTheory.GrassTop.ren τ (g τ)) = (if ∀ τ, g τ = X (true, Dw.p) ^ Dw.q then (-1 : ℝ) ^ (Dw.p * Dw.q * Fintype.card (GlobalTheory.AllWt.Psi H)) else 0) * Θ (GlobalTheory.LieBase.pointPoly H Dw) := by
  first | exact @GlobalTheory.GrassTopProd.adm_apply_prod_ren_eq_ite_mul_pointPoly | exact GlobalTheory.GrassTopProd.adm_apply_prod_ren_eq_ite_mul_pointPoly | (intros; apply GlobalTheory.GrassTopProd.adm_apply_prod_ren_eq_ite_mul_pointPoly <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemGrassmannianRelationIdealSupMonomialSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemGrassmannianRelationIdealSupMonomialSpan
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

noncomputable section

namespace GlobalTheory.GrassTop

lemma rel_mem_J {p q k : ℕ} (hk : 1 ≤ k) : rel k ∈ J p q :=
  Ideal.subset_span (Or.inl ⟨k, hk, rfl⟩)

lemma X_zero_sub_one_mem_J {p q : ℕ} (b : Bool) :
    (X (b, 0) - 1 : MvPolynomial (Bool × ℕ) ℝ) ∈ J p q :=
  Ideal.subset_span (Or.inr (Or.inl ⟨b, rfl⟩))

lemma X_true_mem_J {p q k : ℕ} (hk : p < k) : (X (true, k) : MvPolynomial (Bool × ℕ) ℝ) ∈ J p q :=
  Ideal.subset_span (Or.inr (Or.inr (Or.inl ⟨k, hk, rfl⟩)))

lemma X_false_mem_J {p q k : ℕ} (hk : q < k) : (X (false, k) : MvPolynomial (Bool × ℕ) ℝ) ∈ J p q :=
  Ideal.subset_span (Or.inr (Or.inr (Or.inr ⟨k, hk, rfl⟩)))

lemma mem_of_neg_one_pow_mul {I : Ideal (MvPolynomial (Bool × ℕ) ℝ)} {x : MvPolynomial (Bool × ℕ) ℝ}
    (n : ℕ) (h : C ((-1 : ℝ) ^ n) * x ∈ I) : x ∈ I := by
  have := I.mul_mem_left (C ((-1 : ℝ) ^ n)) h
  rwa [← mul_assoc, ← C_mul, ← mul_pow, neg_one_mul, neg_neg, one_pow, C_1, one_mul] at this

lemma X_mul_X_mem_J {p q : ℕ} (hpq : 1 ≤ p + q) :
    (X (true, p) * X (false, q) : MvPolynomial (Bool × ℕ) ℝ) ∈ J p q := by
  have hrel := rel_mem_J (p := p) (q := q) hpq
  have hp : p ∈ Finset.range (p + q + 1) := Finset.mem_range.2 (by omega)
  rw [rel, ← Finset.add_sum_erase _ _ hp] at hrel
  have hrest : (∑ a ∈ (Finset.range (p + q + 1)).erase p,
      C ((-1 : ℝ) ^ (p + q - a)) * X (true, a) * X (false, p + q - a)) ∈ J p q := by
    refine Ideal.sum_mem _ fun a ha => ?_
    have hap := Finset.ne_of_mem_erase ha
    rcases lt_or_gt_of_ne hap with h | h
    · exact (J p q).mul_mem_left _ (X_false_mem_J (by omega))
    · exact (J p q).mul_mem_right _ ((J p q).mul_mem_left _ (X_true_mem_J h))
  have := (J p q).sub_mem hrel hrest
  rw [add_sub_cancel_right, Nat.add_sub_cancel_left, mul_assoc] at this
  exact mem_of_neg_one_pow_mul q this

lemma sub_C_eval_mem {I : Ideal (MvPolynomial (Bool × ℕ) ℝ)} (v : Bool × ℕ → ℝ)
    (hv : ∀ y, X y - C (v y) ∈ I) (P : MvPolynomial (Bool × ℕ) ℝ) : P - C (eval v P) ∈ I := by
  refine MvPolynomial.induction_on (motive := fun P => P - C (eval v P) ∈ I) P (fun a => ?_) (fun P Q hP hQ => ?_) (fun P y hP => ?_)
  · simp
  · have := I.add_mem hP hQ
    convert this using 1
    simp only [map_add (f := _)]; ring
  · have := I.add_mem (I.mul_mem_right (X y) hP) (I.mul_mem_left (C (eval v P)) (hv y))
    convert this using 1
    simp only [map_mul, eval_X]; ring

lemma X_false_mem_J_zero {q k : ℕ} (hk : 1 ≤ k) : (X (false, k) : MvPolynomial (Bool × ℕ) ℝ) ∈ J 0 q := by
  have hrel := rel_mem_J (p := 0) (q := q) hk
  rw [rel, Finset.sum_range_succ'] at hrel
  have hrest : (∑ i ∈ Finset.range k,
      C ((-1 : ℝ) ^ (k - (i + 1))) * X (true, i + 1) * X (false, k - (i + 1))) ∈ J 0 q :=
    Ideal.sum_mem _ fun i _ => (J 0 q).mul_mem_right _ ((J 0 q).mul_mem_left _ (X_true_mem_J (by omega)))
  have h0 := (J 0 q).sub_mem hrel hrest
  rw [add_sub_cancel_left, Nat.sub_zero] at h0
  have h1 := (J 0 q).sub_mem h0
    ((J 0 q).mul_mem_right (C ((-1 : ℝ) ^ k) * X (false, k)) (X_zero_sub_one_mem_J true))
  refine mem_of_neg_one_pow_mul k ?_
  convert h1 using 1
  ring

lemma X_true_mem_J_zero {p k : ℕ} (hk : 1 ≤ k) : (X (true, k) : MvPolynomial (Bool × ℕ) ℝ) ∈ J p 0 := by
  have hrel := rel_mem_J (p := p) (q := 0) hk
  rw [rel, Finset.sum_range_succ] at hrel
  have hrest : (∑ a ∈ Finset.range k,
      C ((-1 : ℝ) ^ (k - a)) * X (true, a) * X (false, k - a)) ∈ J p 0 :=
    Ideal.sum_mem _ fun a ha => (J p 0).mul_mem_left _ (X_false_mem_J (by simp at ha; omega))
  have h0 := (J p 0).sub_mem hrel hrest
  rw [add_sub_cancel_left, Nat.sub_self, pow_zero, C_1, one_mul] at h0
  have h1 := (J p 0).sub_mem h0 ((J p 0).mul_mem_left (X (true, k)) (X_zero_sub_one_mem_J false))
  convert h1 using 1
  ring

lemma hv_zero_left (q : ℕ) (y : Bool × ℕ) :
    X y - C (if y.2 = 0 then (1 : ℝ) else 0) ∈ J 0 q := by
  obtain ⟨b, k⟩ := y
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using X_zero_sub_one_mem_J (p := 0) (q := q) b
  · simp only [show k ≠ 0 by omega, if_false, C_0, sub_zero]
    cases b
    · exact X_false_mem_J_zero hk
    · exact X_true_mem_J hk

lemma hv_zero_right (p : ℕ) (y : Bool × ℕ) :
    X y - C (if y.2 = 0 then (1 : ℝ) else 0) ∈ J p 0 := by
  obtain ⟨b, k⟩ := y
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using X_zero_sub_one_mem_J (p := p) (q := 0) b
  · simp only [show k ≠ 0 by omega, if_false, C_0, sub_zero]
    cases b
    · exact X_false_mem_J hk
    · exact X_true_mem_J_zero hk

lemma base_left (q : ℕ) (h : MvPolynomial (Bool × ℕ) ℝ) :
    h ∈ (J 0 q).restrictScalars ℝ ⊔ Submodule.span ℝ (basis 0 q) := by
  have h1 := sub_C_eval_mem (fun y => if y.2 = 0 then (1 : ℝ) else 0) (hv_zero_left q) h
  set c := eval (fun y : Bool × ℕ => if y.2 = 0 then (1 : ℝ) else 0) h
  have hpow : (1 : MvPolynomial (Bool × ℕ) ℝ) - X (true, 0) ^ q ∈ J 0 q := by
    obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow (X (true, 0) : MvPolynomial (Bool × ℕ) ℝ) 1 q
    rw [one_pow] at hd
    have := (J 0 q).mul_mem_right d (X_zero_sub_one_mem_J true)
    rw [← hd] at this
    simpa using (J 0 q).neg_mem this
  have hdecomp : h = (h - C c + C c * (1 - X (true, 0) ^ q)) + c • X (true, 0) ^ q := by
    rw [smul_eq_C_mul]; ring
  rw [hdecomp]
  refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · rw [Submodule.restrictScalars_mem]
    exact (J 0 q).add_mem h1 ((J 0 q).mul_mem_left _ hpow)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr rfl))

lemma base_right (p : ℕ) (h : MvPolynomial (Bool × ℕ) ℝ) :
    h ∈ (J p 0).restrictScalars ℝ ⊔ Submodule.span ℝ (basis p 0) := by
  have h1 := sub_C_eval_mem (fun y => if y.2 = 0 then (1 : ℝ) else 0) (hv_zero_right p) h
  set c := eval (fun y : Bool × ℕ => if y.2 = 0 then (1 : ℝ) else 0) h
  have hdecomp : h = (h - C c) + c • X (true, p) ^ 0 := by
    rw [pow_zero, smul_eq_C_mul, mul_one]; ring
  rw [hdecomp]
  refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · rwa [Submodule.restrictScalars_mem]
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr rfl))

lemma J_le_succ_left (p q : ℕ) :
    J p q ≤ J (p + 1) q ⊔ Ideal.span {(X (true, p + 1) : MvPolynomial (Bool × ℕ) ℝ)} := by
  refine Ideal.span_le.2 ?_
  rintro f (⟨k, hk, rfl⟩ | ⟨b, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
  · exact Ideal.mem_sup_left (rel_mem_J hk)
  · exact Ideal.mem_sup_left (X_zero_sub_one_mem_J b)
  · rcases Nat.lt_or_ge (p + 1) k with h | h
    · exact Ideal.mem_sup_left (X_true_mem_J h)
    · obtain rfl : k = p + 1 := by omega
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  · exact Ideal.mem_sup_left (X_false_mem_J hk)

lemma J_le_succ_right (p q : ℕ) :
    J p q ≤ J p (q + 1) ⊔ Ideal.span {(X (false, q + 1) : MvPolynomial (Bool × ℕ) ℝ)} := by
  refine Ideal.span_le.2 ?_
  rintro f (⟨k, hk, rfl⟩ | ⟨b, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
  · exact Ideal.mem_sup_left (rel_mem_J hk)
  · exact Ideal.mem_sup_left (X_zero_sub_one_mem_J b)
  · exact Ideal.mem_sup_left (X_true_mem_J hk)
  · rcases Nat.lt_or_ge (q + 1) k with h | h
    · exact Ideal.mem_sup_left (X_false_mem_J h)
    · obtain rfl : k = q + 1 := by omega
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)

lemma wt_add_single (d : Bool × ℕ →₀ ℕ) (y : Bool × ℕ) :
    wt (d + Finsupp.single y 1) = wt d + y.2 := by
  unfold wt
  rw [Finsupp.sum_add_index' (fun _ => mul_zero _) (fun _ _ _ => mul_add _ _ _),
    Finsupp.sum_single_index (mul_zero _), mul_one]

lemma wt_single (y : Bool × ℕ) (n : ℕ) : wt (Finsupp.single y n) = y.2 * n := by
  unfold wt
  rw [Finsupp.sum_single_index (mul_zero _)]

lemma basis_subset_succ_left (p q : ℕ) : basis p (q + 1) ⊆ basis (p + 1) (q + 1) := by
  rintro f (⟨d, hd, rfl⟩ | rfl)
  · exact Or.inl ⟨d, lt_of_lt_of_le hd (Nat.mul_le_mul_right _ (Nat.le_succ p)), rfl⟩
  · refine Or.inl ⟨Finsupp.single (true, p) (q + 1), ?_, X_pow_eq_monomial⟩
    rw [wt_single]
    show p * (q + 1) < (p + 1) * (q + 1)
    nlinarith

lemma X_mul_span_basis (p q : ℕ) {s : MvPolynomial (Bool × ℕ) ℝ}
    (hs : s ∈ Submodule.span ℝ (basis (p + 1) q)) :
    X (true, p + 1) * s ∈ Submodule.span ℝ (basis (p + 1) (q + 1)) := by
  induction hs using Submodule.span_induction with
  | mem x hx =>
    apply Submodule.subset_span
    rcases hx with ⟨d, hd, rfl⟩ | rfl
    · refine Or.inl ⟨d + Finsupp.single (true, p + 1) 1, ?_, ?_⟩
      · rw [wt_add_single]
        show wt d + (p + 1) < (p + 1) * (q + 1)
        nlinarith
      · rw [add_comm d, monomial_single_add, pow_one]
    · exact Or.inr (by rw [pow_succ'])
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ a hx

lemma X_mul_mem (p q : ℕ) (f : MvPolynomial (Bool × ℕ) ℝ)
    (hf : f ∈ (J (p + 1) q).restrictScalars ℝ ⊔ Submodule.span ℝ (basis (p + 1) q)) :
    X (true, p + 1) * f ∈
      (J (p + 1) (q + 1)).restrictScalars ℝ ⊔ Submodule.span ℝ (basis (p + 1) (q + 1)) := by
  obtain ⟨j, hj, s, hs, rfl⟩ := Submodule.mem_sup.1 hf
  rw [mul_add]
  refine Submodule.add_mem _ (Submodule.mem_sup_left ?_)
    (Submodule.mem_sup_right (X_mul_span_basis p q hs))
  rw [Submodule.restrictScalars_mem] at hj ⊢
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (J_le_succ_right (p + 1) q hj)
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
  have hXX := X_mul_X_mem_J (p := p + 1) (q := q + 1) (by omega)
  have : X (true, p + 1) * (a + c * X (false, q + 1)) =
      X (true, p + 1) * a + c * (X (true, p + 1) * X (false, q + 1)) := by ring
  rw [this]
  exact (J _ _).add_mem ((J _ _).mul_mem_left _ ha) ((J _ _).mul_mem_left _ hXX)

theorem mem_rel_sup_span_low_or_top : ∀ (p q : ℕ) (h : MvPolynomial (Bool × ℕ) ℝ),
    h ∈ (J p q).restrictScalars ℝ ⊔ Submodule.span ℝ (basis p q) := by
  intro p
  induction p with
  | zero => exact base_left
  | succ p ihp =>
    intro q
    induction q with
    | zero => exact base_right (p + 1)
    | succ q ihq =>
      intro h
      obtain ⟨j, hj, s, hs, rfl⟩ := Submodule.mem_sup.1 (ihp (q + 1) h)
      rw [Submodule.restrictScalars_mem] at hj
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (J_le_succ_left p (q + 1) hj)
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
      refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.mem_sup_left ?_) ?_)
        (Submodule.mem_sup_right ?_)
      · rwa [Submodule.restrictScalars_mem]
      · rw [mul_comm]; exact X_mul_mem p q c (ihq c)
      · exact Submodule.span_mono (basis_subset_succ_left p q) hs

end GlobalTheory.GrassTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemGrassmannianRelationIdealSupMonomialSpanStatement
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_grassmannianRelationIdeal_sup_monomialSpan : ∀ (p q : ℕ) (h : MvPolynomial (Bool × ℕ) ℝ), h ∈ (GlobalTheory.GrassTop.J p q).restrictScalars ℝ ⊔ Submodule.span ℝ (GlobalTheory.GrassTop.basis p q) := by
  first | exact @GlobalTheory.GrassTop.mem_rel_sup_span_low_or_top | exact GlobalTheory.GrassTop.mem_rel_sup_span_low_or_top | (intros; apply GlobalTheory.GrassTop.mem_rel_sup_span_low_or_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleChernFormKillsGrassmannianRelationCopi
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleChernFormKillsGrassmannianRelationCopi
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.GrassTop

theorem ren_rel {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (τ : GlobalTheory.AllWt.Psi H) (k : ℕ) :
    ren τ (rel k) = GlobalTheory.PointChern.relPoly τ k := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [ren, rel, GlobalTheory.PointChern.relPoly, map_sum, renVar]

theorem admissibleChernForm_kills_grassmannianRelationCopies : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ), GlobalTheory.Schubert.admitted H Dw Θ →
    ∀ (τ : GlobalTheory.AllWt.Psi H) (j : MvPolynomial (Bool × ℕ) ℝ), j ∈ GlobalTheory.GrassTop.J Dw.p Dw.q →
    ∀ r : MvPolynomial ((E →+* ℂ) × ℕ) ℝ, Θ (r * GlobalTheory.GrassTop.ren τ j) = 0 := by
  intro E _ _ _ H Dw Θ hA τ j hj
  obtain ⟨h1, h2, h3, -⟩ := hA
  unfold J at hj
  induction hj using Submodule.span_induction with
  | mem x hx =>
    intro r
    rcases hx with ⟨k, hk, rfl⟩ | ⟨b, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    · rw [ren_rel, mul_comm]; exact h1 τ k hk r
    · rw [mul_comm]
      simp only [ren, map_sub, rename_X, map_one]
      exact h2 _ r
    · rw [mul_comm]
      simp only [ren, rename_X]
      have hm : Dw.mult τ.1 = Dw.p := GlobalTheory.PointChern.mult_of_mem Dw τ.2
      exact h3 _ _ (by simp only [renVar, if_true]; omega) r
    · rw [mul_comm]
      simp only [ren, rename_X]
      have hm : Dw.mult (conjEmb τ.1) = Dw.q := GlobalTheory.PointChern.mult_of_not_mem Dw (GlobalTheory.AllWt.conj_not_mem τ)
      exact h3 _ _ (by simp only [renVar]; simp only [Bool.false_eq_true, if_false]; omega) r
  | zero => intro r; simp
  | add x y _ _ hx hy => intro r; rw [map_add (f := _), mul_add, map_add (f := _), hx, hy, add_zero]
  | smul a x _ hx => intro r; rw [smul_eq_mul, map_mul (ren τ) a x, ← mul_assoc]; exact hx _

end GlobalTheory.GrassTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleChernFormKillsGrassmannianRelationCopiStatement
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adm_apply_mul_ren_eq_zero_of_mem_J : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ), GlobalTheory.Schubert.admitted H Dw Θ → ∀ (τ : GlobalTheory.AllWt.Psi H) (j : MvPolynomial (Bool × ℕ) ℝ), j ∈ GlobalTheory.GrassTop.J Dw.p Dw.q → ∀ r : MvPolynomial ((E →+* ℂ) × ℕ) ℝ, Θ (r * GlobalTheory.GrassTop.ren τ j) = 0 := by
  first | exact @GlobalTheory.GrassTop.admissibleChernForm_kills_grassmannianRelationCopies | exact GlobalTheory.GrassTop.admissibleChernForm_kills_grassmannianRelationCopies | (intros; apply GlobalTheory.GrassTop.admissibleChernForm_kills_grassmannianRelationCopies <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleFormEqMulPointClassValue
noncomputable section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.GrassTop

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def S (H : Host E) (Dw : Datum H) : Submodule ℝ (MvPolynomial ((E →+* ℂ) × ℕ) ℝ) where
  carrier := {P | ∃ β : ℝ, ∀ Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ, GlobalTheory.Schubert.admitted H Dw Θ →
    Θ P = β * Θ (GlobalTheory.LieBase.pointPoly H Dw)}
  zero_mem' := ⟨0, fun Θ _ => by simp⟩
  add_mem' := by
    rintro a b ⟨β, hβ⟩ ⟨β', hβ'⟩
    exact ⟨β + β', fun Θ h => by rw [map_add (f := _), hβ Θ h, hβ' Θ h]; ring⟩
  smul_mem' := by
    rintro c a ⟨β, hβ⟩
    exact ⟨c * β, fun Θ h => by rw [map_smul, hβ Θ h, smul_eq_mul]; ring⟩

theorem prod_update {H : Host E} (g : GlobalTheory.AllWt.Psi H → MvPolynomial (Bool × ℕ) ℝ) (σ : GlobalTheory.AllWt.Psi H)
    (h : MvPolynomial (Bool × ℕ) ℝ) :
    ∏ τ, ren τ (Function.update g σ h τ) = ren σ h * ∏ τ ∈ Finset.univ.erase σ, ren τ (g τ) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ σ), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun τ hτ => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hτ)]

theorem prod_ren_mem (H : Host E) (Dw : Datum H) (s : Finset (GlobalTheory.AllWt.Psi H)) :
    ∀ g : GlobalTheory.AllWt.Psi H → MvPolynomial (Bool × ℕ) ℝ, (∀ τ ∉ s, g τ ∈ basis Dw.p Dw.q) →
      ∏ τ, ren τ (g τ) ∈ S H Dw := by
  induction s using Finset.induction_on with
  | empty =>
    intro g hg
    exact ⟨_, GlobalTheory.T.admissibleChernForm_prod_grassmannianBasisCopies E H Dw g fun τ => hg τ (Finset.notMem_empty τ)⟩
  | insert σ s hσ ih =>
    intro g hg
    have key : ∀ h ∈ (J Dw.p Dw.q).restrictScalars ℝ ⊔ Submodule.span ℝ (basis Dw.p Dw.q),
        ren σ h * ∏ τ ∈ Finset.univ.erase σ, ren τ (g τ) ∈ S H Dw := by
      intro h hh
      obtain ⟨j, hj, b, hb, rfl⟩ := Submodule.mem_sup.1 hh
      rw [map_add (f := _), add_mul]
      refine add_mem ⟨0, fun Θ hΘ => ?_⟩ ?_
      · rw [zero_mul, mul_comm]
        exact GlobalTheory.T.adm_apply_mul_ren_eq_zero_of_mem_J E H Dw Θ hΘ σ j hj _
      · clear hh
        induction hb using Submodule.span_induction with
        | mem b hb =>
          rw [← prod_update]
          refine ih _ fun τ hτ => ?_
          by_cases e : τ = σ
          · subst e; rw [Function.update_self]; exact hb
          · rw [Function.update_of_ne e]; exact hg τ (by simp [e, hτ])
        | zero => simp
        | add x y _ _ hx hy => rw [map_add (f := _), add_mul]; exact add_mem hx hy
        | smul c x _ hx => rw [map_smul, smul_mul_assoc]; exact Submodule.smul_mem _ c hx
    have := key (g σ) (GlobalTheory.T.mem_grassmannianRelationIdeal_sup_monomialSpan _ _ _)
    rwa [← prod_update, Function.update_eq_self] at this

theorem var_eq {H : Host E} (x : (E →+* ℂ) × ℕ) : ∃ σ : GlobalTheory.AllWt.Psi H, ∃ y, x = renVar σ y := by
  by_cases h : x.1 (H.rt : E) = H.rt0
  · exact ⟨⟨x.1, h⟩, (true, x.2), by simp [renVar]⟩
  · refine ⟨⟨conjEmb x.1, GlobalTheory.AllWt.conj_mem h⟩, (false, x.2), ?_⟩
    simp [renVar, GlobalTheory.AllWt.conjEmb_conjEmb]

theorem mul_prod_ren_mem (H : Host E) (Dw : Datum H) (P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) :
    ∀ g : GlobalTheory.AllWt.Psi H → MvPolynomial (Bool × ℕ) ℝ, P * ∏ τ, ren τ (g τ) ∈ S H Dw := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    intro g
    rw [C_mul']
    exact Submodule.smul_mem _ a (prod_ren_mem H Dw Finset.univ g (by simp))
  | add a b ha hb => intro g; rw [add_mul]; exact add_mem (ha g) (hb g)
  | mul_X P x ih =>
    intro g
    obtain ⟨σ, y, rfl⟩ := var_eq (H := H) x
    have e : X (renVar σ y) * ∏ τ, ren τ (g τ) = ∏ τ, ren τ (Function.update g σ (X y * g σ) τ) := by
      rw [prod_update, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ σ), map_mul, ren, rename_X]
      ring
    rw [mul_assoc, e]
    exact ih _

end GlobalTheory.GrassTop

theorem GlobalTheory.GrassTop.span_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), ∃ β : ℝ, ∀ Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ,
      GlobalTheory.Schubert.admitted H Dw Θ → Θ P = β * Θ (GlobalTheory.LieBase.pointPoly H Dw) := by
  intro E _ _ _ H Dw P
  have := GlobalTheory.GrassTop.mul_prod_ren_mem H Dw P (fun _ => 1)
  simp only [map_one, Finset.prod_const_one, mul_one] at this
  exact this
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleFormEqMulPointClassValueStatement
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_form_eq_mul_point_class_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), ∃ β : ℝ, ∀ Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ, GlobalTheory.Schubert.admitted H Dw Θ → Θ P = β * Θ (GlobalTheory.LieBase.pointPoly H Dw) := by
  first | exact @GlobalTheory.GrassTop.span_point | exact GlobalTheory.GrassTop.span_point | (intros; apply GlobalTheory.GrassTop.span_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannProductTopDegreeEqSmulPointClass
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

namespace GlobalTheory.GrassTopDim

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem relIdeal_isHomogeneous (H : Host E) (Dw : Datum H) :
    (relIdeal H Dw).IsHomogeneous
      (weightedHomogeneousSubmodule ℝ (Prod.snd : (E →+* ℂ) × ℕ → ℕ)) := by
  apply Ideal.homogeneous_span
  rintro x ((⟨τ, rfl⟩ | ⟨τ, k, -, rfl⟩) | ⟨τ, k, -, rfl⟩)
  · refine ⟨0, ?_⟩
    refine sub_mem ?_ ?_
    · rw [mem_weightedHomogeneousSubmodule]
      exact isWeightedHomogeneous_X ℝ Prod.snd (τ, 0)
    · rw [mem_weightedHomogeneousSubmodule]
      exact isWeightedHomogeneous_one ℝ Prod.snd
  · refine ⟨k, ?_⟩
    rw [mem_weightedHomogeneousSubmodule]
    exact isWeightedHomogeneous_X ℝ Prod.snd (τ, k)
  · refine ⟨k, Submodule.sum_mem _ fun a ha => ?_⟩
    rw [mem_weightedHomogeneousSubmodule]
    have ha' : a ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
    have h := ((isWeightedHomogeneous_C Prod.snd ((-1 : ℝ) ^ (k - a))).mul
      (isWeightedHomogeneous_X ℝ Prod.snd (τ.1, a))).mul
      (isWeightedHomogeneous_X ℝ Prod.snd (conjEmb τ.1, k - a))
    convert h using 1
    simp only [zero_add]
    omega

theorem pointPoly_isWeightedHomogeneous (H : Host E) (Dw : Datum H) :
    IsWeightedHomogeneous Prod.snd (pointPoly H Dw) (Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q)) := by
  have h : ∀ τ ∈ (Finset.univ : Finset (GlobalTheory.AllWt.Psi H)), IsWeightedHomogeneous Prod.snd
      ((C ((-1 : ℝ) ^ Dw.mult τ.1) * X (τ.1, Dw.mult τ.1)) ^ (Dw.p + Dw.q - Dw.mult τ.1)) (Dw.p * Dw.q) := by
    intro τ _
    have hm : Dw.mult τ.1 = Dw.p := GlobalTheory.PointChern.mult_of_mem Dw τ.2
    have h1 := ((isWeightedHomogeneous_C Prod.snd ((-1 : ℝ) ^ Dw.mult τ.1)).mul
      (isWeightedHomogeneous_X ℝ Prod.snd (τ.1, Dw.mult τ.1))).pow (Dw.p + Dw.q - Dw.mult τ.1)
    convert h1 using 1
    simp only [hm, zero_add, Nat.add_sub_cancel_left]
    ring
  have h2 := IsWeightedHomogeneous.prod Finset.univ _ _ h
  rw [pointPoly]
  convert h2 using 1
  simp [Finset.sum_const, Finset.card_univ, smul_eq_mul]

theorem mem_of_forall_dual {V : Type} [AddCommGroup V] [Module ℝ V] (S : Submodule ℝ V) (v : V)
    (h : ∀ f : Module.Dual ℝ (V ⧸ S), f (S.mkQ v) = 0) : v ∈ S := by
  have := (Module.forall_dual_apply_eq_zero_iff ℝ (S.mkQ v)).1 h
  simpa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using this

theorem top_eq_smul_point : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ),
    IsWeightedHomogeneous Prod.snd Q (Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q)) →
      ∃ c : ℝ, Q - C c * pointPoly H Dw ∈ relIdeal H Dw := by
  intro E _ _ _ H Dw Q hQ
  obtain ⟨β, hβ⟩ := GlobalTheory.T.admissible_form_eq_mul_point_class_value E H Dw Q
  set D := Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q) with hD
  let N : Submodule ℝ (MvPolynomial ((E →+* ℂ) × ℕ) ℝ) := Submodule.span ℝ
    {f | ∃ d : (E →+* ℂ) × ℕ →₀ ℕ, (d.sum fun x i => x.2 * i) ≠ D ∧ f = monomial d 1}
  let S := (relIdeal H Dw).restrictScalars ℝ ⊔ N
  have hS : Q - C β * pointPoly H Dw ∈ S := by
    apply mem_of_forall_dual
    intro f
    let Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ := f ∘ₗ S.mkQ
    have hker : ∀ x ∈ S, Θ x = 0 := fun x hx => by
      simp [Θ, (Submodule.Quotient.mk_eq_zero _).2 hx]
    have hrel : ∀ x ∈ relIdeal H Dw, Θ x = 0 := fun x hx =>
      hker x (Submodule.mem_sup_left (by simpa using hx))
    have hadm : GlobalTheory.Schubert.admitted H Dw Θ := by
      refine ⟨fun τ k hk P => hrel _ ?_, fun τ P => hrel _ ?_, fun τ k hk P => hrel _ ?_,
        fun d hd => hker _ (Submodule.mem_sup_right (Submodule.subset_span ⟨d, hd, rfl⟩))⟩
      · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Or.inr ⟨τ, k, hk, rfl⟩))
      · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Or.inl (Or.inl ⟨τ, rfl⟩)))
      · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Or.inl (Or.inr ⟨τ, k, hk, rfl⟩)))
    show Θ (Q - C β * pointPoly H Dw) = 0
    rw [map_sub, hβ Θ hadm, C_mul', map_smul, smul_eq_mul, sub_self]
  obtain ⟨r, hr, n, hn, hrn⟩ := Submodule.mem_sup.1 hS
  have hn0 : ∀ n ∈ N, weightedHomogeneousComponent Prod.snd D n = 0 := by
    intro n hn
    induction hn using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨d, hd, rfl⟩ := hx
      refine weightedHomogeneousComponent_eq_zero' _ _ fun d' hd' => ?_
      rw [support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hd'
      subst hd'
      rw [Finsupp.weight_apply]
      intro h
      apply hd
      rw [← h]
      exact Finsupp.sum_congr fun x _ => by rw [smul_eq_mul, mul_comm]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, hx, smul_zero]
  have hhom : IsWeightedHomogeneous Prod.snd (Q - C β * pointPoly H Dw) D := by
    have h1 : Q ∈ weightedHomogeneousSubmodule ℝ Prod.snd D := (mem_weightedHomogeneousSubmodule _ _ _ _).2 hQ
    have h2 : pointPoly H Dw ∈ weightedHomogeneousSubmodule ℝ Prod.snd D :=
      (mem_weightedHomogeneousSubmodule _ _ _ _).2 (pointPoly_isWeightedHomogeneous H Dw)
    rw [← mem_weightedHomogeneousSubmodule, C_mul']
    exact sub_mem h1 (Submodule.smul_mem _ β h2)
  refine ⟨β, ?_⟩
  rw [← hhom.weightedHomogeneousComponent_same, ← hrn, map_add (f := _), hn0 n hn, add_zero]
  exact weightedHomogeneousComponent_mem_of_mem ℝ Prod.snd (relIdeal_isHomogeneous H Dw) (by simpa using hr) D

end GlobalTheory.GrassTopDim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannProductTopDegreeEqSmulPointClassStatement
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grassmannProduct_topDegree_eq_smul_pointClass : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), IsWeightedHomogeneous Prod.snd Q (Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q)) → ∃ c : ℝ, Q - C c * pointPoly H Dw ∈ relIdeal H Dw := by
  first | exact @GlobalTheory.GrassTopDim.top_eq_smul_point | exact GlobalTheory.GrassTopDim.top_eq_smul_point | (intros; apply GlobalTheory.GrassTopDim.top_eq_smul_point <;> assumption)
end
