module

public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.MemPolKIff
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideFurther

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.FockMonomialRight
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

variable {K : Type} [Field K]

section Elem

variable (v : AddValuation K (WithTop ℚ))

theorem vge_iff' (a : ℝ) (x : K) : vge v a x ↔ ∀ n : ℚ, v x = (n : WithTop ℚ) → a ≤ n := by
  unfold vge vR
  cases h : v x with
  | top => simp
  | coe m =>
    simp only [WithTop.map_coe, WithTop.coe_le_coe, WithTop.coe_inj]
    constructor
    · intro h1 n hn; rw [← hn]; exact h1
    · intro h1; exact h1 m rfl

theorem vge_zero' (a : ℝ) : vge v a (0 : K) := by
  rw [vge_iff']; intro n hn; rw [AddValuation.map_zero] at hn; exact absurd hn (by simp)

theorem vge_mono' {a b : ℝ} {x : K} (hab : b ≤ a) (h : vge v a x) : vge v b x := by
  rw [vge_iff'] at *; intro n hn; exact hab.trans (h n hn)

theorem vge_add' {a : ℝ} {x y : K} (hx : vge v a x) (hy : vge v a y) : vge v a (x + y) := by
  rw [vge_iff'] at *
  intro n hn
  have h := v.map_add x y
  rw [hn] at h
  rcases min_le_iff.mp h with h1 | h1
  · obtain ⟨m, hm, hmn⟩ := WithTop.le_coe_iff.mp h1
    exact (hx m hm).trans (by exact_mod_cast hmn)
  · obtain ⟨m, hm, hmn⟩ := WithTop.le_coe_iff.mp h1
    exact (hy m hm).trans (by exact_mod_cast hmn)

theorem vge_mul' {a b : ℝ} {x y : K} (hx : vge v a x) (hy : vge v b y) : vge v (a + b) (x * y) := by
  rw [vge_iff'] at *
  intro n hn
  rw [v.map_mul] at hn
  cases h1 : v x with
  | top => rw [h1] at hn; simp at hn
  | coe m =>
    cases h2 : v y with
    | top => rw [h2] at hn; simp at hn
    | coe k =>
      rw [h1, h2, ← WithTop.coe_add, WithTop.coe_inj] at hn
      have := hx m h1
      have := hy k h2
      rw [← hn]; push_cast; linarith

theorem vge_sum' {ι : Type} {a : ℝ} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, vge v a (f i)) :
    vge v a (∑ i ∈ s, f i) := by
  first | exact UpperTheory.Reformulated.B.Qh31.vge_sum .. | (apply UpperTheory.Reformulated.B.Qh31.vge_sum <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qh31.vge_sum <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh31.vge_sum <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qh31.vge_sum <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh31.vge_sum <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qh31.vge_sum K ‹_› v ι a s f h | exact @UpperTheory.Reformulated.B.Qh31.vge_sum K ‹_› v ι a s f | exact @UpperTheory.Reformulated.B.Qh31.vge_sum K ‹_› v ι a s | exact @UpperTheory.Reformulated.B.Qh31.vge_sum K ‹_› v ι a | exact @UpperTheory.Reformulated.B.Qh31.vge_sum K ‹_› v ι | exact @UpperTheory.Reformulated.B.Qh31.vge_sum K ‹_› v | exact @UpperTheory.Reformulated.B.Qh31.vge_sum K ‹_› | exact @UpperTheory.Reformulated.B.Qh31.vge_sum K

theorem fact_ne_zero' {σ : Type} (α : σ →₀ ℕ) : fact α ≠ 0 := by
  unfold fact Finsupp.prod
  exact Finset.prod_ne_zero_iff.mpr fun x _ => Nat.factorial_ne_zero _

theorem vge_vN' (n : ℕ) : vge v (vN v n) (n : K) := by
  rw [vge_iff']
  intro m hm
  unfold vN
  rw [hm]; simp

end Elem

section Fock

variable {σ : Type}

theorem fock_eq_sum_of (F G : MvPolynomial σ K) (s : Finset (σ →₀ ℕ))
    (h : ∀ α, F.coeff α ≠ 0 → G.coeff α ≠ 0 → α ∈ s) :
    fock F G = ∑ α ∈ s, F.coeff α * G.coeff α * (fact α : K) := by
  classical
  unfold fock
  have h1 : ∑ α ∈ F.support, F.coeff α * G.coeff α * (fact α : K) =
      ∑ α ∈ F.support ∪ s, F.coeff α * G.coeff α * (fact α : K) := by
    apply Finset.sum_subset Finset.subset_union_left
    intro α _ hα
    rw [notMem_support_iff.mp hα]; simp
  have h2 : ∑ α ∈ s, F.coeff α * G.coeff α * (fact α : K) =
      ∑ α ∈ F.support ∪ s, F.coeff α * G.coeff α * (fact α : K) := by
    apply Finset.sum_subset Finset.subset_union_right
    intro α _ hα
    by_cases hF : F.coeff α = 0
    · rw [hF]; simp
    · by_cases hG : G.coeff α = 0
      · rw [hG]; simp
      · exact absurd (h α hF hG) hα
  rw [h1, h2]

theorem fock_eq_sum (F G : MvPolynomial σ K) (s : Finset (σ →₀ ℕ))
    (h : F.support ⊆ s ∨ G.support ⊆ s) :
    fock F G = ∑ α ∈ s, F.coeff α * G.coeff α * (fact α : K) := by
  apply fock_eq_sum_of
  intro α hF hG
  rcases h with h | h
  · exact h (mem_support_iff.mpr hF)
  · exact h (mem_support_iff.mpr hG)

theorem fock_comm (F G : MvPolynomial σ K) : fock F G = fock G F := by
  rw [fock_eq_sum F G G.support (Or.inr (Finset.Subset.refl _))]
  unfold fock
  exact Finset.sum_congr rfl fun α _ => by ring

theorem fock_add_left (F F' G : MvPolynomial σ K) : fock (F + F') G = fock F G + fock F' G := by
  rw [fock_eq_sum (F + F') G G.support (Or.inr (Finset.Subset.refl _)),
    fock_eq_sum F G G.support (Or.inr (Finset.Subset.refl _)),
    fock_eq_sum F' G G.support (Or.inr (Finset.Subset.refl _)), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun α _ => by rw [MvPolynomial.coeff_add]; ring

theorem fock_add_right (F G G' : MvPolynomial σ K) : fock F (G + G') = fock F G + fock F G' := by
  rw [fock_comm, fock_add_left, fock_comm G, fock_comm G']

theorem fock_smul_left (c : K) (F G : MvPolynomial σ K) : fock (c • F) G = c * fock F G := by
  rw [fock_eq_sum (c • F) G G.support (Or.inr (Finset.Subset.refl _)),
    fock_eq_sum F G G.support (Or.inr (Finset.Subset.refl _)), Finset.mul_sum]
  exact Finset.sum_congr rfl fun α _ => by rw [coeff_smul, smul_eq_mul]; ring

theorem fock_smul_right (c : K) (F G : MvPolynomial σ K) : fock F (c • G) = c * fock F G := by
  rw [fock_comm, fock_smul_left, fock_comm]

theorem fock_zero_left (G : MvPolynomial σ K) : fock 0 G = 0 := by
  unfold fock; simp

theorem fock_neg_left (F G : MvPolynomial σ K) : fock (-F) G = -fock F G := by
  have := fock_smul_left (-1 : K) F G
  simpa using this

theorem fock_sub_left (F F' G : MvPolynomial σ K) : fock (F - F') G = fock F G - fock F' G := by
  rw [sub_eq_add_neg, fock_add_left, fock_neg_left, ← sub_eq_add_neg]

theorem fock_sum_left {ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ K) (G : MvPolynomial σ K) :
    fock (∑ i ∈ s, f i) G = ∑ i ∈ s, fock (f i) G := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fock_zero_left]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, fock_add_left, ih]

theorem fock_sum_right {ι : Type} (s : Finset ι) (F : MvPolynomial σ K) (f : ι → MvPolynomial σ K) :
    fock F (∑ i ∈ s, f i) = ∑ i ∈ s, fock F (f i) := by
  rw [fock_comm, fock_sum_left]
  exact Finset.sum_congr rfl fun i _ => fock_comm _ _

theorem fock_monomial_right (F : MvPolynomial σ K) (α : σ →₀ ℕ) (c : K) :
    fock F (monomial α c) = F.coeff α * c * (fact α : K) := by
  classical
  rw [fock_eq_sum F (monomial α c) {α} (Or.inr (support_monomial_subset)), Finset.sum_singleton,
    coeff_monomial, if_pos rfl]

theorem fock_eq_sum_right (F G : MvPolynomial σ K) :
    fock F G = ∑ α ∈ G.support, F.coeff α * G.coeff α * (fact α : K) :=
  fock_eq_sum F G G.support (Or.inr (Finset.Subset.refl _))

theorem dg_eq_sum_f (f : (σ →₀ ℕ) → K) (F : MvPolynomial σ K) :
    dg f F = ∑ α ∈ F.support, monomial α (f α * F.coeff α) := by
  conv_lhs => rw [← support_sum_monomial_coeff F]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun α _ => dg_monomial f α _

theorem support_dg_subset (f : (σ →₀ ℕ) → K) (F : MvPolynomial σ K) :
    (dg f F).support ⊆ F.support := by
  intro α hα
  rw [mem_support_iff, coeff_dg] at hα
  exact mem_support_iff.mpr (right_ne_zero_of_mul hα)

theorem gaAct_eq_dg (D : TwistData K) (G : MvPolynomial (D.OL × Fin D.r) K) :
    D.gaAct G = dg D.ga G := by
  rw [dg_eq_sum_f]; rfl

end Fock

section BB

variable (v : AddValuation K (WithTop ℚ)) {σ : Type}

theorem vge_sub_iff (a w : ℝ) (x : K) :
    vge v (a - w) x ↔ ((a : ℝ) : WithTop ℝ) ≤ vR v x + ((w : ℝ) : WithTop ℝ) := by
  unfold vge
  cases vR v x with
  | top => simp
  | coe y =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe, sub_le_iff_le_add]

theorem bge_iff (a : ℝ) (F : MvPolynomial σ K) :
    bge v a F ↔ ((a : ℝ) : WithTop ℝ) ≤ vBB v F := by
  unfold bge vBB
  rw [Finset.le_inf_iff]
  constructor
  · intro h α _
    exact (vge_sub_iff v a _ _).mp (h α)
  · intro h α
    by_cases hα : α ∈ F.support
    · exact (vge_sub_iff v a _ _).mpr (h α hα)
    · rw [notMem_support_iff.mp hα]; exact vge_zero' v _

theorem bge_mono {a b : ℝ} {F : MvPolynomial σ K} (hab : b ≤ a) (h : bge v a F) : bge v b F :=
  fun α => vge_mono' v (by linarith) (h α)

theorem bge_monomial {a : ℝ} (α : σ →₀ ℕ) {c : K} (hc : vge v a c) :
    bge v (a + vN v (fact α) / 2) (monomial α c) := fun β => by
  classical
  rw [coeff_monomial]
  split_ifs with h
  · rw [← h]; exact vge_mono' v (by linarith) hc
  · exact vge_zero' v _

theorem bge_dg {a b : ℝ} {f : (σ →₀ ℕ) → K} {F : MvPolynomial σ K} (hf : ∀ α, vge v a (f α))
    (hF : bge v b F) : bge v (a + b) (dg f F) := fun α => by
  rw [coeff_dg]
  exact vge_mono' v (by linarith) (vge_mul' v (hf α) (hF α))

theorem exists_of_vBB_zero (F : MvPolynomial σ K) (h : vBB v F = 0) :
    (∃ α ∈ F.support, vge v (-(vN v (fact α)) / 2) (F.coeff α) ∧
      vle v (-(vN v (fact α)) / 2) (F.coeff α)) ∧ bge v 0 F := by
  refine ⟨?_, (bge_iff v 0 F).mpr (by rw [h]; rfl)⟩
  have hne : F.support.Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    unfold vBB at h
    rw [hc, Finset.inf_empty] at h
    exact absurd h (by simp)
  obtain ⟨α, hα, hinf⟩ := Finset.exists_mem_eq_inf F.support hne
    (fun α => vR v (F.coeff α) + ((((v (fact α : K)).untopD 0 : ℚ) : ℝ) / 2 : ℝ))
  refine ⟨α, hα, ?_⟩
  have h0 : vR v (F.coeff α) + ((vN v (fact α) / 2 : ℝ) : WithTop ℝ) = 0 := by
    rw [← h]; exact hinf.symm
  unfold vge vle
  cases hx : vR v (F.coeff α) with
  | top => rw [hx] at h0; simp at h0
  | coe y =>
    rw [hx, ← WithTop.coe_add] at h0
    have h1 : y + vN v (fact α) / 2 = 0 := by exact_mod_cast h0
    have h2 : y = -(vN v (fact α)) / 2 := by linarith
    rw [h2]
    exact ⟨le_refl _, le_refl _⟩

theorem vge_fock {a b : ℝ} {F G : MvPolynomial σ K} (hF : bge v a F) (hG : bge v b G) :
    vge v (a + b) (fock F G) := by
  unfold fock
  apply vge_sum'
  intro α _
  have h1 := vge_mul' v (vge_mul' v (hF α) (hG α)) (vge_vN' v (fact α))
  exact vge_mono' v (by linarith) h1

end BB

end Formalism.MainNotions.PlaneGram
end
end

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}

section Generic

variable {L : Type} [Fintype L] [DecidableEq L] (sg : L → Bool) {r : ℕ} [NeZero r] (d : L → ℕ)

theorem fock_proj_right {W : Set (MvPolynomial (L × Fin r) K)}
    {π : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K}
    (hπ : IsFockProj (K := K) (r := r) d W π) {A G : MvPolynomial (L × Fin r) K}
    (hA : A ∈ PolK K r d) (hAW : A ∈ W) (hG : G ∈ PolK K r d) : fock A (π G) = fock A G := by
  have h := (hπ G hG).2.2.2 A hA hAW
  rw [fock_sub_left] at h
  rw [fock_comm A (π G), fock_comm A G]
  exact (sub_eq_zero.mp h).symm

theorem proj_preserves (hP : PROJ K v p C0) (hD : DVRHyp v p) {S S'' : Finset L} {th th'' : ℤ}
    {π : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K}
    (hπ : IsFockProj (K := K) (r := r) d (Aset sg S th) π)
    (hS : S ⊆ S'' ∨ S'' ⊆ S ∨ Disjoint S S'') {F : MvPolynomial (L × Fin r) K}
    (hF : F ∈ PolK K r d) (hFW : F ∈ Aset sg S'' th'') : π F ∈ Aset sg S'' th'' := by
  obtain ⟨⟨π'', hπ''⟩, -⟩ := hP hD L sg r d S'' th''
  have hfix : π'' F = F := (hπ'' F hF).2.2.1 hFW
  have hcomm : π (π'' F) = π'' (π F) := by
    rcases hS with h | h | h
    · exact ((hP hD L sg r d S th).2 π hπ).2.1 S'' (Or.inl h) th'' π'' hπ'' F hF
    · exact (((hP hD L sg r d S'' th'').2 π'' hπ'').2.1 S (Or.inl h) th π hπ F hF).symm
    · exact ((hP hD L sg r d S th).2 π hπ).2.1 S'' (Or.inr h) th'' π'' hπ'' F hF
  have hE : π F = π'' (π F) := by rw [← hcomm, hfix]
  rw [hE]
  exact (hπ'' (π F) (hπ F hF).1).2.1

theorem bge_proj (hP : PROJ K v p C0) (hD : DVRHyp v p) {S : Finset L} {th : ℤ}
    {π : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K}
    (hπ : IsFockProj (K := K) (r := r) d (Aset sg S th) π) {F : MvPolynomial (L × Fin r) K}
    (hF : F ∈ PolK K r d) {a : ℝ} (ha : bge v a F) :
    bge v (a - (r : ℝ) ^ 2 * lg p r (2 * ∑ i, d i)) (π F) := by
  rw [bge_iff] at ha ⊢
  have hb := ((hP hD L sg r d S th).2 π hπ).2.2 F hF
  have h2 := ha.trans hb
  generalize vBB v (π F) = x at h2 ⊢
  induction x using WithTop.recTopCoe with
  | top => exact le_top
  | coe x =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe] at h2
    rw [WithTop.coe_le_coe]
    linarith

theorem prodProj (hP : PROJ K v p C0) (hD : DVRHyp v p) {ι : Type} (s : Finset ι)
    (S : ι → Finset L) (th : ι → ℤ)
    (hpair : ∀ x ∈ s, ∀ y ∈ s, S x ⊆ S y ∨ S y ⊆ S x ∨ Disjoint (S x) (S y)) :
    ∃ Pr : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K,
      (∀ F ∈ PolK K r d, Pr F ∈ PolK K r d) ∧
      (∀ F ∈ PolK K r d, ∀ x ∈ s, Pr F ∈ Aset sg (S x) (th x)) ∧
      (∀ A ∈ PolK K r d, (∀ x ∈ s, A ∈ Aset sg (S x) (th x)) →
        ∀ G ∈ PolK K r d, fock A (Pr G) = fock A G) ∧
      (∀ F ∈ PolK K r d, ∀ a : ℝ, bge v a F →
        bge v (a - s.card * ((r : ℝ) ^ 2 * lg p r (2 * ∑ i, d i))) (Pr F)) ∧
      (∀ (S'' : Finset L) (th'' : ℤ), (∀ x ∈ s, S x ⊆ S'' ∨ Disjoint (S x) S'') →
        ∀ F ∈ PolK K r d, F ∈ Aset sg S'' th'' → Pr F ∈ Aset sg S'' th'') ∧
      (∀ i : L, sg i = true → (∀ x ∈ s, i ∉ S x) → ∀ (a : Fin r), ∀ F ∈ PolK K r d,
          Pr (X (i, a) * pderiv (i, a) F) = X (i, a) * pderiv (i, a) (Pr F)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨LinearMap.id, fun F hF => hF, fun F _ x hx => by simp at hx, fun A _ _ G _ => rfl, ?_,
      fun S'' th'' _ F _ hFW => hFW, fun i _ _ a F _ => rfl⟩
    intro F _ a ha
    simpa using ha
  | @insert x s hx ih =>
    have hpair' : ∀ y ∈ s, ∀ z ∈ s, S y ⊆ S z ∨ S z ⊆ S y ∨ Disjoint (S y) (S z) :=
      fun y hy z hz => hpair y (Finset.mem_insert_of_mem hy) z (Finset.mem_insert_of_mem hz)
    obtain ⟨Pr, h1, h2, h3, h4, h5, h6⟩ := ih hpair'
    obtain ⟨⟨πx, hπx⟩, -⟩ := hP hD L sg r d (S x) (th x)
    have hPx := (hP hD L sg r d (S x) (th x)).2 πx hπx
    refine ⟨πx ∘ₗ Pr, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro F hF
      exact (hπx _ (h1 F hF)).1
    · intro F hF y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact (hπx _ (h1 F hF)).2.1
      · exact proj_preserves sg d hP hD hπx
          (hpair _ (Finset.mem_insert_self _ s) y (Finset.mem_insert_of_mem hy)) (h1 F hF) (h2 F hF y hy)
    · intro A hA hAW G hG
      rw [LinearMap.comp_apply,
        fock_proj_right d hπx hA (hAW x (Finset.mem_insert_self x s)) (h1 G hG)]
      exact h3 A hA (fun y hy => hAW y (Finset.mem_insert_of_mem hy)) G hG
    · intro F hF a ha
      have hb := bge_proj sg d hP hD hπx (h1 F hF) (h4 F hF a ha)
      rw [LinearMap.comp_apply]
      refine bge_mono v ?_ hb
      rw [Finset.card_insert_eq_ite, if_neg hx]
      apply le_of_eq
      push_cast
      ring
    · intro S'' th'' hS F hF hFW
      have hPr := h5 S'' th'' (fun y hy => hS y (Finset.mem_insert_of_mem hy)) F hF hFW
      rw [LinearMap.comp_apply]
      rcases hS x (Finset.mem_insert_self x s) with h | h
      · exact proj_preserves sg d hP hD hπx (Or.inl h) (h1 F hF) hPr
      · exact proj_preserves sg d hP hD hπx (Or.inr (Or.inr h)) (h1 F hF) hPr
    · intro i hi hout a F hF
      rw [LinearMap.comp_apply, LinearMap.comp_apply,
        h6 i hi (fun y hy => hout y (Finset.mem_insert_of_mem hy)) a F hF]
      exact hPx.1 i hi (hout x (Finset.mem_insert_self x s)) a (Pr F) (h1 F hF)

end Generic

section Torus

variable {L : Type} [DecidableEq L] (sg : L → Bool) {r : ℕ}

theorem euler_eq_dg {σ : Type} (x : σ) (G : MvPolynomial σ K) :
    X x * pderiv x G = dg (fun ξ => (ξ x : K)) G := by
  refine MvPolynomial.induction_on' G (fun α c => ?_) (fun P Q hP hQ => ?_)
  · rw [MvPolynomial.X_mul_pderiv_monomial, dg_monomial, MvPolynomial.smul_monomial, nsmul_eq_mul]
  · rw [map_add (f := _), mul_add, hP, hQ, map_add (f := _)]

private theorem coeff_dg_eq_mul_coeff {σ : Type} (f : (σ →₀ ℕ) → K) (F : MvPolynomial σ K)
    (α : σ →₀ ℕ) : (dg f F).coeff α = f α * F.coeff α := by
  classical
  rw [dg_eq_sum_f, MvPolynomial.coeff_sum]
  by_cases h : α ∈ F.support
  · rw [Finset.sum_eq_single α (fun β _ hβ => by rw [MvPolynomial.coeff_monomial, if_neg hβ])
      (fun h' => absurd h h'), MvPolynomial.coeff_monomial, if_pos rfl]
  · have h0 : F.coeff α = 0 := by simpa using h
    rw [h0, mul_zero]
    exact Finset.sum_eq_zero (fun β hβ => by
      rw [MvPolynomial.coeff_monomial, if_neg (fun (e : β = α) => h (e ▸ hβ))])

theorem proj_keeps_letter (d : L → ℕ)
    (Pr : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K) (i : L)
    (hcomm : ∀ (a : Fin r), ∀ F ∈ PolK K r d,
      Pr (X (i, a) * pderiv (i, a) F) = X (i, a) * pderiv (i, a) (Pr F))
    (ζ : L × Fin r →₀ ℕ) (hζ : ∀ k, ldeg ζ k = d k) (ζ' : L × Fin r →₀ ℕ)
    (hζ' : ζ' ∈ (Pr (monomial ζ 1)).support) (a : Fin r) : ζ' (i, a) = ζ (i, a) := by
  classical
  have hmono : (monomial ζ (1 : K) : MvPolynomial (L × Fin r) K) ∈ PolK K r d := by
    rw [mem_PolK_iff]
    intro α hα k
    have hαζ : α = ζ := by
      by_contra hne
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial, if_neg (Ne.symm hne)] at hα
      exact hα rfl
    rw [hαζ]
    exact hζ k
  have h := hcomm a _ hmono
  rw [euler_eq_dg, euler_eq_dg] at h
  simp only [dg_monomial, mul_one] at h
  have h' := congrArg (fun G => AddMonoidAlgebra.coeff G ζ') h
  simp only [coeff_dg_eq_mul_coeff] at h'
  have hsm : (monomial ζ ((ζ (i, a) : ℕ) : K) : MvPolynomial (L × Fin r) K) =
      ((ζ (i, a) : ℕ) : K) • monomial ζ (1 : K) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hsm, map_smul, MvPolynomial.coeff_smul, smul_eq_mul] at h'
  have hne : (Pr (monomial ζ 1)).coeff ζ' ≠ 0 := by simpa using hζ'
  have hc := mul_right_cancel₀ hne h'
  exact_mod_cast hc.symm

end Torus

theorem prodProj_entries {L : Type} [Fintype L] [DecidableEq L] (sg : L → Bool) {r : ℕ} [NeZero r]
    (d : L → ℕ) {ι : Type} (s : Finset ι) (S : ι → Finset L)
    (Pr : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K)
    (h1 : ∀ F ∈ PolK K r d, Pr F ∈ PolK K r d)
    (h6 : ∀ i : L, sg i = true → (∀ x ∈ s, i ∉ S x) → ∀ (a : Fin r), ∀ F ∈ PolK K r d,
          Pr (X (i, a) * pderiv (i, a) F) = X (i, a) * pderiv (i, a) (Pr F))
    (ζ : L × Fin r →₀ ℕ) (hζ : ∀ k, ldeg ζ k = d k) (ζ' : L × Fin r →₀ ℕ)
    (hζ' : ζ' ∈ (Pr (monomial ζ 1)).support) :
    (∀ k, ldeg ζ' k = d k) ∧
      ∀ i, sg i = true → (∀ x ∈ s, i ∉ S x) → ∀ a, ζ' (i, a) = ζ (i, a) := by
  classical
  have hmono : (monomial ζ (1 : K) : MvPolynomial (L × Fin r) K) ∈ PolK K r d := by
    rw [mem_PolK_iff]
    intro α hα k
    have hαζ : α = ζ := by
      by_contra hne
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial, if_neg (Ne.symm hne)] at hα
      exact hα rfl
    rw [hαζ]
    exact hζ k
  exact ⟨fun k => (mem_PolK_iff d _).mp (h1 _ hmono) ζ' hζ' k,
    fun i hi hout a => proj_keeps_letter d Pr i (h6 i hi hout) ζ hζ ζ' hζ' a⟩

end Formalism.MainNotions.PlaneGram
