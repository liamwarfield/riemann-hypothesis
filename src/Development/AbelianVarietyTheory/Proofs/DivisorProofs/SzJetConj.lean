module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointPairsLowerBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertFamilyWeierstrassTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsSideTer

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormHilbertEisensteinValueLeOfIntegralJ
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SzValueOfFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionValuationBoundRingClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionValuationBoundRingClosure
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)

namespace GlobalTheory.QFam.QSz

section

variable {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]} {N : ℕ}

theorem qAll_const {r : ℝ} {c : ℂ} (hc : Sz l lam r c) : QAll (Sz l lam r) N fun _ => c := by
  refine ⟨_, (GlobalTheory.T.hasQExpansionOfLevel_linear_operations N).2.2.2.1 c, fun n => ?_⟩
  by_cases h : n = 0
  · simpa only [h, if_true] using hc
  · simpa only [h, if_false] using (GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops l lam).1 r

theorem qAll_mono {r s : ℝ} {f : ℍ → ℂ} (h : r ≤ s) (hf : QAll (Sz l lam r) N f) : QAll (Sz l lam s) N f := by
  obtain ⟨a, ha, hs⟩ := hf
  exact ⟨a, ha, fun n => (GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops l lam).2.2.2.1 r s _ h (hs n)⟩

theorem qAll_add {r : ℝ} {f g : ℍ → ℂ} (hf : QAll (Sz l lam r) N f) (hg : QAll (Sz l lam r) N g) :
    QAll (Sz l lam r) N fun τ => f τ + g τ := by
  obtain ⟨a, ha, hs⟩ := hf
  obtain ⟨b, hb, ht⟩ := hg
  exact ⟨_, (GlobalTheory.T.hasQExpansionOfLevel_linear_operations N).1 f g a b ha hb, fun n => ((GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops l lam).2.1 r _ _ (hs n) (ht n)).1⟩

theorem qAll_sub {r : ℝ} {f g : ℍ → ℂ} (hf : QAll (Sz l lam r) N f) (hg : QAll (Sz l lam r) N g) :
    QAll (Sz l lam r) N fun τ => f τ - g τ := by
  obtain ⟨a, ha, hs⟩ := hf
  obtain ⟨b, hb, ht⟩ := hg
  exact ⟨_, (GlobalTheory.T.hasQExpansionOfLevel_linear_operations N).2.1 f g a b ha hb, fun n => ((GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops l lam).2.1 r _ _ (hs n) (ht n)).2⟩

theorem qAll_mul (hN : 0 < N) {r s : ℝ} {f g : ℍ → ℂ} (hf : QAll (Sz l lam r) N f) (hg : QAll (Sz l lam s) N g) :
    QAll (Sz l lam (r + s)) N fun τ => f τ * g τ := by
  obtain ⟨a, ha, hs⟩ := hf
  obtain ⟨b, hb, ht⟩ := hg
  refine ⟨_, GlobalTheory.T.hasQExpansionOfLevel_mul_of_pos_level N f g a b hN ha hb, fun n => ?_⟩
  exact (GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops l lam).2.2.2.2.2 _ _ _ (fun p : ℕ × ℕ => a p.1 * b p.2)
    fun p _ => (GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops l lam).2.2.1 r s _ _ (hs _) (ht _)

theorem qAll_one : QAll (Sz l lam 0) N fun _ => 1 :=
  qAll_const (by simpa using (GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops l lam).2.2.2.2.1 1)

theorem qAll_pow (hN : 0 < N) {r : ℝ} {f : ℍ → ℂ} (k : ℕ) (hf : QAll (Sz l lam r) N f) :
    QAll (Sz l lam (k * r)) N fun τ => f τ ^ k := by
  induction k with
  | zero => simpa using (qAll_one : QAll (Sz l lam 0) N fun _ => 1)
  | succ k ih =>
    have h := qAll_mul hN ih hf
    have e : ((k + 1 : ℕ) : ℝ) * r = k * r + r := by push_cast; ring
    rw [e]
    simpa only [pow_succ] using h

theorem qAll_sum {κ : Type} (t : Finset κ) {r : ℝ} {f : κ → ℍ → ℂ} (hf : ∀ k ∈ t, QAll (Sz l lam r) N (f k)) :
    QAll (Sz l lam r) N fun τ => ∑ k ∈ t, f k τ := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (qAll_const ((GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops l lam).1 r) : QAll (Sz l lam r) N fun _ => 0)
  | insert k t hk ih =>
    simp only [Finset.sum_insert hk]
    exact qAll_add (hf k (Finset.mem_insert_self k t)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem qAll_prod (hN : 0 < N) {κ : Type} (t : Finset κ) {r : κ → ℝ} {f : κ → ℍ → ℂ}
    (hf : ∀ k ∈ t, QAll (Sz l lam (r k)) N (f k)) :
    QAll (Sz l lam (∑ k ∈ t, r k)) N fun τ => ∏ k ∈ t, f k τ := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (qAll_one : QAll (Sz l lam 0) N fun _ => 1)
  | insert k t hk ih =>
    simp only [Finset.sum_insert hk, Finset.prod_insert hk]
    exact qAll_mul hN (hf k (Finset.mem_insert_self k t)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

end

theorem qAll_sz_ring : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), ∀ (N : ℕ), 0 < N → (∀ (r : ℝ) (c : ℂ), Sz l lam r c → QAll (Sz l lam r) N fun _ => c) ∧ (∀ (r s : ℝ) f, r ≤ s → QAll (Sz l lam r) N f → QAll (Sz l lam s) N f) ∧ (∀ (r : ℝ) f g, QAll (Sz l lam r) N f → QAll (Sz l lam r) N g → (QAll (Sz l lam r) N fun τ => f τ + g τ) ∧ QAll (Sz l lam r) N fun τ => f τ - g τ) ∧ (∀ (r s : ℝ) f g, QAll (Sz l lam r) N f → QAll (Sz l lam s) N g → QAll (Sz l lam (r + s)) N fun τ => f τ * g τ) ∧ (∀ (r : ℝ) f (k : ℕ), QAll (Sz l lam r) N f → QAll (Sz l lam (k * r)) N fun τ => f τ ^ k) ∧ (∀ (κ : Type) (t : Finset κ) (r : ℝ) (f : κ → ℍ → ℂ), (∀ k ∈ t, QAll (Sz l lam r) N (f k)) → QAll (Sz l lam r) N fun τ => ∑ k ∈ t, f k τ) ∧ (∀ (κ : Type) (t : Finset κ) (r : κ → ℝ) (f : κ → ℍ → ℂ), (∀ k ∈ t, QAll (Sz l lam (r k)) N (f k)) → QAll (Sz l lam (∑ k ∈ t, r k)) N fun τ => ∏ k ∈ t, f k τ) :=
  fun _ _ _ _ hN => ⟨fun _ _ h => qAll_const h, fun _ _ _ h hf => qAll_mono h hf,
    fun _ _ _ hf hg => ⟨qAll_add hf hg, qAll_sub hf hg⟩, fun _ _ _ _ hf hg => qAll_mul hN hf hg,
    fun _ _ k hf => qAll_pow hN k hf, fun _ t _ _ hf => qAll_sum t hf, fun _ t _ _ hf => qAll_prod hN t hf⟩

end GlobalTheory.QFam.QSz
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionValuationBoundRingClosureStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qExpansionValuationBound_ring_closure : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), ∀ (N : ℕ), 0 < N → (∀ (r : ℝ) (c : ℂ), Sz l lam r c → QAll (Sz l lam r) N fun _ => c) ∧ (∀ (r s : ℝ) f, r ≤ s → QAll (Sz l lam r) N f → QAll (Sz l lam s) N f) ∧ (∀ (r : ℝ) f g, QAll (Sz l lam r) N f → QAll (Sz l lam r) N g → (QAll (Sz l lam r) N fun τ => f τ + g τ) ∧ QAll (Sz l lam r) N fun τ => f τ - g τ) ∧ (∀ (r s : ℝ) f g, QAll (Sz l lam r) N f → QAll (Sz l lam s) N g → QAll (Sz l lam (r + s)) N fun τ => f τ * g τ) ∧ (∀ (r : ℝ) f (k : ℕ), QAll (Sz l lam r) N f → QAll (Sz l lam (k * r)) N fun τ => f τ ^ k) ∧ (∀ (κ : Type) (t : Finset κ) (r : ℝ) (f : κ → ℍ → ℂ), (∀ k ∈ t, QAll (Sz l lam r) N (f k)) → QAll (Sz l lam r) N fun τ => ∑ k ∈ t, f k τ) ∧ (∀ (κ : Type) (t : Finset κ) (r : κ → ℝ) (f : κ → ℍ → ℂ), (∀ k ∈ t, QAll (Sz l lam (r k)) N (f k)) → QAll (Sz l lam (∑ k ∈ t, r k)) N fun τ => ∏ k ∈ t, f k τ) := by
  first | exact @GlobalTheory.QFam.QSz.qAll_sz_ring | exact GlobalTheory.QFam.QSz.qAll_sz_ring | (intros; apply GlobalTheory.QFam.QSz.qAll_sz_ring <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastOfForallRatGt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastOfForallRatGt
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)

namespace GlobalTheory.QFam

theorem sz_of_forall_rat_gt : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]),
    ∀ (r : ℝ) (x : ℂ), (∀ q : ℚ, r < q → Sz l lam q x) → Sz l lam r x := by
  intro l hl lam r x h
  obtain ⟨q₀, hq₀⟩ := exists_rat_gt r
  obtain ⟨hx, -⟩ := h q₀ hq₀
  refine ⟨hx, ?_⟩
  by_contra hc
  rw [not_le] at hc
  have hl1 : (1 : ℝ) < (l : ℝ) := by exact_mod_cast hl.out.one_lt
  have hl0 : (0 : ℝ) < (l : ℝ) := lt_trans one_pos hl1
  have ht : 0 < ‖lam ⟨x, hx⟩‖ := lt_trans (Real.rpow_pos_of_pos hl0 r) hc
  have h1 : r < Real.logb l ‖lam ⟨x, hx⟩‖ := (Real.lt_logb_iff_rpow_lt hl1 ht).2 hc
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h1
  obtain ⟨_, hle⟩ := h q hq1
  exact absurd ((Real.lt_logb_iff_rpow_lt hl1 ht).1 hq2) (not_lt.2 hle)

end GlobalTheory.QFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastOfForallRatGtStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicValuationAtLeast_of_forall_rat_gt : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), ∀ (r : ℝ) (x : ℂ), (∀ q : ℚ, r < q → Sz l lam q x) → Sz l lam r x := by
  first | exact @GlobalTheory.QFam.sz_of_forall_rat_gt | exact GlobalTheory.QFam.sz_of_forall_rat_gt | (intros; apply GlobalTheory.QFam.sz_of_forall_rat_gt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegrallyClosedPadicIntegralSubring
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegrallyClosedPadicIntegralSubring
noncomputable section

open GlobalTheory.LatVal (Sz)
open Polynomial

namespace GlobalTheory.QFam.SzRing

variable (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l])

abbrev nval : Valuation ℂ_[l] NNReal := NormedField.valuation

theorem mem_integer_iff (y : ℂ_[l]) : y ∈ (nval l).integer ↔ ‖y‖ ≤ 1 := by
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
  exact Iff.rfl

def szRing : Subring ℂ :=
  ((nval l).integer.comap lam).map (algebraicClosure ℚ ℂ).val.toRingHom

theorem mem_szRing (x : ℂ) : x ∈ szRing l lam ↔ Sz l lam 0 x := by
  unfold szRing Sz
  rw [Real.rpow_zero]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, (mem_integer_iff l _).1 hy⟩
  · rintro ⟨h, hy⟩
    exact ⟨⟨x, h⟩, (mem_integer_iff l _).2 hy, rfl⟩

def toAlg : szRing l lam →+* algebraicClosure ℚ ℂ :=
  (szRing l lam).subtype.codRestrict (algebraicClosure ℚ ℂ) fun r => ((mem_szRing l lam r.1).1 r.2).1

theorem lam_toAlg_mem (r : szRing l lam) : (lam.comp (toAlg l lam)) r ∈ (nval l).integer := by
  obtain ⟨h, hr⟩ := (mem_szRing l lam r.1).1 r.2
  rw [Real.rpow_zero] at hr
  exact (mem_integer_iff l _).2 hr

theorem mem_szRing_of_isIntegral (x : ℂ) (hx : IsIntegral (szRing l lam) x) : x ∈ szRing l lam := by
  obtain ⟨p, hp, hpx⟩ := hx
  have hc : (algebraMap (algebraicClosure ℚ ℂ) ℂ).comp (toAlg l lam) = algebraMap (szRing l lam) ℂ :=
    RingHom.ext fun _ => rfl
  have h1 : IsIntegral (algebraicClosure ℚ ℂ) x :=
    ⟨p.map (toAlg l lam), hp.map _, by rw [eval₂_map, hc, hpx]⟩
  have : Algebra.IsIntegral ℚ (algebraicClosure ℚ ℂ) :=
    ⟨fun y => (isIntegral_algHom_iff (algebraicClosure ℚ ℂ).val Subtype.val_injective).1
      (mem_algebraicClosure_iff'.1 y.2)⟩
  have h2 : x ∈ algebraicClosure ℚ ℂ :=
    mem_algebraicClosure_iff'.2 (isIntegral_trans x h1)
  have h3 : eval₂ (toAlg l lam) ⟨x, h2⟩ p = 0 := by
    apply (algebraMap (algebraicClosure ℚ ℂ) ℂ).injective
    rw [hom_eval₂, hc, map_zero]
    exact hpx
  have h4 : eval₂ (lam.comp (toAlg l lam)) (lam ⟨x, h2⟩) p = 0 := by
    rw [← hom_eval₂, h3, map_zero]
  let g : szRing l lam →+* (nval l).integer :=
    (lam.comp (toAlg l lam)).codRestrict (nval l).integer (lam_toAlg_mem l lam)
  have hg : (algebraMap (nval l).integer ℂ_[l]).comp g = lam.comp (toAlg l lam) :=
    RingHom.ext fun _ => rfl
  have h5 : IsIntegral (nval l).integer (lam ⟨x, h2⟩) :=
    ⟨p.map g, hp.map _, by rw [eval₂_map, hg, h4]⟩
  have h6 := (Valuation.integer.integers (nval l)).mem_of_integral h5
  rw [mem_szRing]
  refine ⟨h2, ?_⟩
  rw [Real.rpow_zero]
  exact (mem_integer_iff l _).1 h6

end GlobalTheory.QFam.SzRing

theorem GlobalTheory.QFam.exists_szRing (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) :
    ∃ R : Subring ℂ, (∀ x, x ∈ R ↔ Sz l lam 0 x) ∧ ∀ x, IsIntegral R x → x ∈ R :=
  ⟨GlobalTheory.QFam.SzRing.szRing l lam, GlobalTheory.QFam.SzRing.mem_szRing l lam,
    GlobalTheory.QFam.SzRing.mem_szRing_of_isIntegral l lam⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegrallyClosedPadicIntegralSubringStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integrallyClosed_padicIntegralSubring : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), ∃ R : Subring ℂ, (∀ x, x ∈ R ↔ Sz l lam 0 x) ∧ ∀ x, IsIntegral R x → x ∈ R := by
  first | exact @GlobalTheory.QFam.exists_szRing | exact GlobalTheory.QFam.exists_szRing | (intros; apply GlobalTheory.QFam.exists_szRing <;> assumption)
end
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)

namespace GlobalTheory.QFam

theorem sz_value_of_family (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l])
    (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w N : ℕ) (f : ι → ℍ → ℂ) (r : ℝ) (τ₀ : ℍ) (Ω : ℂ)
    (hN : 0 < N) (hact : ActBij act) (hf : IsFam act w f) (hq : ∀ i, QAll (Sz l lam r) N (f i))
    (hj : Sz l lam 0 (jT τ₀)) (hΩ : Ω ^ 12 = DD τ₀) (i : ι) :
    Sz l lam r (f i τ₀ / Ω ^ w) := by
  refine GlobalTheory.T.algebraicValuationAtLeast_of_forall_rat_gt l lam r _ fun q hrq => ?_
  obtain ⟨c, hc0, hc, hc'⟩ := GlobalTheory.T.exists_algebraic_of_rational_valuation l lam q
  obtain ⟨R, hR, hcl⟩ := GlobalTheory.T.exists_integrallyClosed_padicIntegralSubring l lam
  obtain ⟨hconst, hmono, -, hmul, -⟩ := GlobalTheory.T.qExpansionValuationBound_ring_closure l lam N hN
  have hfam : IsFam act w fun i τ => c * f i τ := (GlobalTheory.T.isSLTwoPermutedModularFamily_algebra_closure ι act).2.2.1 w c f hf
  have hq' : ∀ i, QAll (· ∈ R) N fun τ => c * f i τ := fun i => by
    obtain ⟨a, ha, ha'⟩ := hmono _ 0 _ (by linarith) (hmul _ _ _ _ (hconst _ c hc) (hq i))
    exact ⟨a, ha, fun n => (hR _).2 (ha' n)⟩
  have hjR : IsIntegral R (jT τ₀) :=
    isIntegral_algebraMap (R := R) (A := ℂ) (x := ⟨jT τ₀, (hR _).2 hj⟩)
  have h0 : Sz l lam 0 (c * f i τ₀ / Ω ^ w) :=
    (hR _).1 (hcl _ (GlobalTheory.T.isIntegral_modularFamily_value_div_period_pow ι act w N _ R τ₀ Ω hN hact hfam hq' hjR hΩ i))
  have h1 := (GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops l lam).2.2.1 _ _ _ _ hc' h0
  have e : c⁻¹ * (c * f i τ₀ / Ω ^ w) = f i τ₀ / Ω ^ w := by
    rw [mul_div_assoc, inv_mul_cancel_left₀ hc0]
  rwa [add_zero, e] at h1

end GlobalTheory.QFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormHilbertEisensteinValueLeOfIntegralJ
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT)
open ModularForm (E₄ E₆)

namespace GlobalTheory.HilbFam

theorem size_values_hfun : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) [NeZero N] (L : Lat F), 1 ≤ s → HasLevel N L → ∀ [IsGalois ℚ F] (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (κ : Emb F → ℕ) (y : Fin 2 → ZMod N) (M M' b : ℕ) (e ρ₀ ρ : ℝ), 0 ≤ e → (∀ C, -(padicValRat l (z C / 2 ^ Module.finrank ℚ F) : ℝ) ≤ e) → ¬ l ∣ M → (∀ x ∈ stdLat F, ((M * l ^ b : ℕ) : 𝓞 F) • x ∈ L) → (∀ v ∈ L, ∀ (j : Fin 2) (i : Emb F), Sz l lam ρ₀ ((i (v j) : ℝ) : ℂ)) → Sz l lam ρ₀ (N : ℂ) → b + (padicValInt l (discr F) : ℝ) / Module.finrank ℚ F + ρ₀ ≤ ρ → 0 ≤ ρ → ¬ l ∣ M' → M' • y = 0 → y ≠ 0 →  ∀ (τ : ℍ) (ω : ℂ), Sz l lam 0 (jT τ) → ω ^ 12 = DD τ → Sz l lam (e + s * (padicValInt l (discr F) : ℝ) + 2 * s * b * Module.finrank ℚ F + (∑ i, κ i : ℕ) * ρ) (hfun (2 * s) L κ (wB N y) τ / ω ^ wt (2 * s) κ) := by
  intro hE F _ _ _ hf s N _ L hs hL _ z hz l _ lam κ y M M' b e ρ₀ ρ he hze hlM hML hLsz hNsz hρ hρ0 hlM' hMy hy τ ω hj hω
  have hA := GlobalTheory.WpFam.Act.rightActions N
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hfam := GlobalTheory.T.hilbert_family_weierstrass_twist hE F hf s N L hs hL y κ
  have hq := GlobalTheory.HilbFam.SizeGL.main hE F hf s N L hs hL z hz l lam κ y M M' b e ρ₀ ρ he hze hlM hML hLsz hNsz hρ hρ0 hlM' hMy hy
  have key := GlobalTheory.QFam.sz_value_of_family l lam (GL (Fin 2) (ZMod N)) (gact N 1) (wt (2 * s) κ) N _ _ τ ω hN
    ((hA.2.1 1).actBij) hfam hq hj hω 1
  simp only [Units.val_one, twist_one_of_hasLevel F N L hL, hA.2.2.2.1] at key
  exact key

end GlobalTheory.HilbFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormHilbertEisensteinValueLeOfIntegralJStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_hilbertEisensteinValue_le_of_integral_j : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) [NeZero N] (L : Lat F), 1 ≤ s → HasLevel N L → ∀ [IsGalois ℚ F] (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (κ : Emb F → ℕ) (y : Fin 2 → ZMod N) (M M' b : ℕ) (e ρ₀ ρ : ℝ), 0 ≤ e → (∀ C, -(padicValRat l (z C / 2 ^ Module.finrank ℚ F) : ℝ) ≤ e) → ¬ l ∣ M → (∀ x ∈ stdLat F, ((M * l ^ b : ℕ) : 𝓞 F) • x ∈ L) → (∀ v ∈ L, ∀ (j : Fin 2) (i : Emb F), Sz l lam ρ₀ ((i (v j) : ℝ) : ℂ)) → Sz l lam ρ₀ (N : ℂ) → b + (padicValInt l (discr F) : ℝ) / Module.finrank ℚ F + ρ₀ ≤ ρ → 0 ≤ ρ → ¬ l ∣ M' → M' • y = 0 → y ≠ 0 →  ∀ (τ : ℍ) (ω : ℂ), Sz l lam 0 (jT τ) → ω ^ 12 = DD τ → Sz l lam (e + s * (padicValInt l (discr F) : ℝ) + 2 * s * b * Module.finrank ℚ F + (∑ i, κ i : ℕ) * ρ) (hfun (2 * s) L κ (wB N y) τ / ω ^ wt (2 * s) κ) := by
  first | exact @GlobalTheory.HilbFam.size_values_hfun | exact GlobalTheory.HilbFam.size_values_hfun | (intros; apply GlobalTheory.HilbFam.size_values_hfun <;> assumption)
end
end

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT)
open ModularForm (E₄ E₆)

namespace GlobalTheory.HilbFam

theorem sz_jet_conj : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) [NeZero N] (L : Lat F), 1 ≤ s → HasLevel N L → ∀ [IsGalois ℚ F] (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (κ : Emb F → ℕ) (y : Fin 2 → ZMod N) (M M' b : ℕ) (e ρ₀ ρ : ℝ), 0 ≤ e → (∀ C, -(padicValRat l (z C / 2 ^ Module.finrank ℚ F) : ℝ) ≤ e) → ¬ l ∣ M → (∀ x ∈ stdLat F, ((M * l ^ b : ℕ) : 𝓞 F) • x ∈ L) → (∀ v ∈ L, ∀ (j : Fin 2) (i : Emb F), Sz l lam ρ₀ ((i (v j) : ℝ) : ℂ)) → Sz l lam ρ₀ (N : ℂ) → b + (padicValInt l (discr F) : ℝ) / Module.finrank ℚ F + ρ₀ ≤ ρ → 0 ≤ ρ → ¬ l ∣ M' → M' • y = 0 → y ≠ 0 →  ∀ (τ : ℍ) (ω : ℂ), Sz l lam 0 (jT τ) → ω ^ 12 = DD τ → ω ≠ 0 → Sz l lam ρ ((G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 + wp N y τ) / ω ^ 2) → Sz l lam (e + s * (padicValInt l (discr F) : ℝ) + 2 * s * b * Module.finrank ℚ F + (∑ i, κ i : ℕ) * ρ) (jet (2 * s) L κ τ 1 (starRingEnd ℂ (τ : ℂ) - τ) * ((Real.pi / τ.im : ℝ) : ℂ) ^ (∑ i, κ i) / (2 * Real.pi * Complex.I) ^ wt (2 * s) κ / ω ^ wt (2 * s) κ) := by
  intro hE F _ _ _ hF s N _ L hs hL _ z hz l _ lam κ y M M' b e ρ₀ ρ he hze hM hML hLv hN hρ hρ0 hM' hy hy0 τ ω hj hω hω0 hst
  obtain ⟨h0, hadd, hmul, hmono, hint, hsum⟩ := GlobalTheory.QFam.SzSum.sz_ring l lam
  have hpow : ∀ (x : ℂ) (n : ℕ), Sz l lam ρ x → Sz l lam (n * ρ) (x ^ n) := by
    intro x n hx
    induction n with
    | zero => simpa using hint 1
    | succ n ih =>
      have := hmul _ _ _ _ ih hx
      rw [pow_succ]
      convert this using 1
      push_cast
      ring
  have hneg : Sz l lam ρ (-((G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 + wp N y τ) / ω ^ 2)) := by
    simpa only [zero_sub] using (hadd ρ _ _ (h0 ρ) hst).2
  rw [GlobalTheory.T.eisenstein_jet_conj_direction_diagonal_expansion hE F hF s N L hs (Nat.pos_of_ne_zero (NeZero.ne N)) hL τ κ (wB N y), Finset.sum_div]
  refine hsum _ _ _ _ fun μ hμ ↦ ?_
  have hle : ∀ i, μ i ≤ κ i := Finset.mem_Iic.mp hμ
  have hs' : ∑ i, κ i = ∑ i, (κ i - μ i) + ∑ i, μ i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ (Nat.sub_add_cancel (hle i)).symm
  have hh := GlobalTheory.T.norm_hilbertEisensteinValue_le_of_integral_j hE F hF s N L hs hL z hz l lam μ y M M' b e ρ₀ ρ he hze hM hML hLv hN hρ hρ0 hM' hy hy0 τ ω hj hω
  have key := hmul _ _ _ _ (hmul _ _ _ _ (hint (∏ i, rco (2 * s) (κ i) (μ i))) (hpow _ (∑ i, (κ i - μ i)) hneg)) hh
  rw [GlobalTheory.wB_nonhol_correction N y τ]
  have hw : wt (2 * s) κ = 2 * (∑ i, (κ i - μ i)) + wt (2 * s) μ := by
    unfold wt
    rw [hs']
    ring
  convert key using 1
  · rw [hs']
    push_cast
    ring
  · rw [hw, pow_add, pow_mul, ← neg_div, div_pow]
    field_simp

end GlobalTheory.HilbFam
