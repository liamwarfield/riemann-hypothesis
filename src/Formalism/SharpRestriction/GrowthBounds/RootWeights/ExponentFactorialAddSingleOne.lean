module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.PolynomialMemWeightSpaceIff
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.DegreeZeroWeightsBounded
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.V2repResIsGLRep

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.ExponentFactorialAddSingleOne
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem fock_form_finset_sum {σ : Type} (F G : MvPolynomial σ K) (s : Finset (σ →₀ ℕ)) (hs : F.support ⊆ s) :
    fock F G = ∑ m ∈ s, F.coeff m * G.coeff m * (expFact m : K) := by
  unfold fock
  refine Finset.sum_subset hs ?_
  intro m _ hm
  rw [MvPolynomial.mem_support_iff, not_not] at hm
  simp [hm]

theorem fock_form_symm {σ : Type} (F G : MvPolynomial σ K) : fock F G = fock G F := by
  classical
  rw [fock_form_finset_sum F G (F.support ∪ G.support) Finset.subset_union_left,
    fock_form_finset_sum G F (F.support ∪ G.support) Finset.subset_union_right]
  exact Finset.sum_congr rfl (fun m _ => by ring)

theorem fock_form_add_right {σ : Type} (F G G' : MvPolynomial σ K) : fock F (G + G') = fock F G + fock F G' := by
  unfold fock
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun m _ => by rw [MvPolynomial.coeff_add]; ring)

theorem fock_form_smul_right {σ : Type} (c : K) (F G : MvPolynomial σ K) : fock F (c • G) = c • fock F G := by
  unfold fock
  rw [smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun m _ => by rw [MvPolynomial.coeff_smul, smul_eq_mul]; ring)

def fockBilinear (K : Type) [Field K] (σ : Type) : MvPolynomial σ K →ₗ[K] MvPolynomial σ K →ₗ[K] K :=
  LinearMap.mk₂ K (fun F G => fock F G)
    (fun F F' G => by
      rw [fock_form_symm, fock_form_add_right, fock_form_symm G F, fock_form_symm G F'])
    (fun c F G => by rw [fock_form_symm, fock_form_smul_right, fock_form_symm G F])
    (fun F G G' => fock_form_add_right F G G')
    (fun c F G => fock_form_smul_right c F G)

theorem fockBilinear_apply {σ : Type} (F G : MvPolynomial σ K) : fockBilinear K σ F G = fock F G := rfl

theorem fock_form_monomial {σ : Type} (m : σ →₀ ℕ) (c : K) (G : MvPolynomial σ K) :
    fock (monomial m c) G = c * G.coeff m * (expFact m : K) := by
  classical
  rw [fock_form_finset_sum _ G {m} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl]

theorem exponent_factorial_add_single_one {σ : Type} [Fintype σ] (u : σ →₀ ℕ) (v : σ) :
    expFact (u + Finsupp.single v 1) = (u v + 1) * expFact u := by
  classical
  unfold expFact
  rw [Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero),
    Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero),
    Fintype.prod_eq_mul_prod_compl v, Fintype.prod_eq_mul_prod_compl v (fun i => (u i).factorial)]
  have h1 : ∀ i ∈ ({v}ᶜ : Finset σ),
      ((u + Finsupp.single v 1 : σ →₀ ℕ) i).factorial = (u i).factorial := by
    intro i hi
    rw [Finset.mem_compl, Finset.mem_singleton] at hi
    simp [Finsupp.single_apply, Ne.symm hi]
  rw [Finset.prod_congr rfl h1]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  ring

theorem fock_mul_adjoint_pderiv {σ : Type} [Fintype σ] (v : σ) (F G : MvPolynomial σ K) :
    fock (X v * F) G = fock F (pderiv v G) := by
  classical
  have addL : ∀ A B C : MvPolynomial σ K, fock (A + B) C = fock A C + fock B C := by
    intro A B C
    rw [fock_form_symm, fock_form_add_right, fock_form_symm C A, fock_form_symm C B]
  induction F using MvPolynomial.induction_on' with
  | monomial m c =>
    induction G using MvPolynomial.induction_on' with
    | monomial n d =>
      rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, MvPolynomial.pderiv_monomial,
        fock_form_monomial, fock_form_monomial, MvPolynomial.coeff_monomial,
        MvPolynomial.coeff_monomial, add_comm (Finsupp.single v 1) m, exponent_factorial_add_single_one]
      by_cases h : n = m + Finsupp.single v 1
      · subst h
        simp only [add_tsub_cancel_right, if_true, Finsupp.add_apply, Finsupp.single_eq_same]
        push_cast
        ring
      · rw [if_neg h]
        by_cases h' : n - Finsupp.single v 1 = m
        · have hv : n v = 0 := by
            by_contra hv
            apply h
            rw [← h', tsub_add_cancel_of_le]
            exact Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hv)
          simp [h', hv]
        · simp [h']
    | add G1 G2 h1 h2 => rw [fock_form_add_right, map_add (f := _), fock_form_add_right, h1, h2]
  | add F1 F2 h1 h2 => rw [mul_add, addL, addL, h1, h2]

theorem fock_pderiv_adjoint_mul {σ : Type} [Fintype σ] (v : σ) (F G : MvPolynomial σ K) :
    fock (pderiv v F) G = fock F (X v * G) := by
  rw [fock_form_symm, ← fock_mul_adjoint_pderiv, fock_form_symm]

theorem fock_form_contravariant (LL : Letters ι) (S : Set ι) (a b : Fin n) (F G : MvPolynomial (ι × Fin n) K) :
    fockBilinear K (ι × Fin n) (glOps K n LL S a b F) G = fockBilinear K (ι × Fin n) F (glOps K n LL S b a G) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [glOps, glAct, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  split_ifs with h1 h2
  · simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, fockBilinear_apply]
    rw [fock_mul_adjoint_pderiv, fock_pderiv_adjoint_mul]
  · simp only [LinearMap.neg_apply, map_neg, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      Derivation.coeFn_coe, fockBilinear_apply]
    rw [fock_mul_adjoint_pderiv, fock_pderiv_adjoint_mul]
  · simp

theorem polynomial_representation_holds : PolynomialGLRepresentation := by
  intro K _ _ ι _ n LL
  exact ⟨fun S => polynomial_isGLRep LL S, fun S S' hd a b c d => disjoint_letters_commute LL S S' hd a b c d,
    fun S S' hs a b => gl_operator_union_add LL S S' hs a b, fun S d a b F hF => gl_operator_preserves_multidegree LL S d a b F hF,
    fun d => homogeneous_multidegree_findim d, fun S mu F hF m hm => weight_vector_monomial_weight LL S mu F hF m hm,
    ⟨fockBilinear K (ι × Fin n), fun F G => rfl, fun S a b F G => fock_form_contravariant LL S a b F G⟩⟩

end Formalism.MainNotions.G.GLWeightTheory
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.ContravariantOrthogonalityHolds
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def loweringMonoid (E : GLOps n K V) : Submonoid (Module.End K V) :=
  Submonoid.closure {g | ∃ c d : Fin n, d < c ∧ g = E c d}

def hwvLoweringSpan (E : GLOps n K V) (mu : Fin n → ℤ) : Submodule K V :=
  Submodule.span K {x | ∃ u ∈ loweringMonoid E, ∃ w, IsHWV E mu w ∧ x = u w}

theorem isotypic_stable_operator (E : GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n) {x : V} (hx : x ∈ isoSub E mu) :
    E a b x ∈ isoSub E mu := by
  first | exact UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator .. | (apply UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› ‹_› ‹_› E mu a b x hx | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› ‹_› ‹_› E mu a b x | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› ‹_› ‹_› E mu a b | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› ‹_› ‹_› E mu a | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› ‹_› ‹_› E mu | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› ‹_› ‹_› E | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n

theorem hwv_lowering_span_lower (E : GLOps n K V) (mu : Fin n → ℤ) {a b : Fin n} (hab : b < a) {x : V}
    (hx : x ∈ hwvLoweringSpan E mu) : E a b x ∈ hwvLoweringSpan E mu := by
  first | exact UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower .. | (apply UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› ‹_› E mu a b hab x hx | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› ‹_› E mu a b hab x | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› ‹_› E mu a b hab | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› ‹_› E mu a b | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› ‹_› E mu a | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› ‹_› E mu | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› ‹_› E | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n

theorem lowering_word_hwv_operator_mem {E : GLOps n K V} (hE : IsGLRep E) (mu : Fin n → ℤ) {w : V} (hw : IsHWV E mu w)
    {u : Module.End K V} (hu : u ∈ loweringMonoid E) : ∀ c d : Fin n, E c d (u w) ∈ hwvLoweringSpan E mu := by
  unfold loweringMonoid at hu
  induction hu using Submonoid.closure_induction_left with
  | one =>
    intro c d
    rw [Module.End.one_apply]
    rcases lt_trichotomy c d with h | h | h
    · rw [hw.2.2 c d h]; exact Submodule.zero_mem _
    · subst h
      rw [(mem_weightSpace_iff_diagonal_rep E mu w).1 hw.2.1 c]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, (loweringMonoid E).one_mem, w, hw, rfl⟩)
    · exact Submodule.subset_span ⟨E c d, Submonoid.subset_closure ⟨c, d, h, rfl⟩, w, hw, rfl⟩
  | mul_left g hg y _ ih =>
    obtain ⟨b, a, hab, rfl⟩ := hg
    intro c d
    rw [Module.End.mul_apply, gl_commutation_apply hE c d b a (y w)]
    refine Submodule.sub_mem _ (Submodule.add_mem _ (hwv_lowering_span_lower E mu hab (ih c d)) ?_) ?_
    · split_ifs
      · exact ih c a
      · exact Submodule.zero_mem _
    · split_ifs
      · exact ih b d
      · exact Submodule.zero_mem _

theorem hwv_lowering_span_stable {E : GLOps n K V} (hE : IsGLRep E) (mu : Fin n → ℤ) (c d : Fin n) {x : V}
    (hx : x ∈ hwvLoweringSpan E mu) : E c d x ∈ hwvLoweringSpan E mu := by
  have hx' := hx
  unfold hwvLoweringSpan at hx'
  induction hx' using Submodule.span_induction with
  | mem x hx1 =>
    obtain ⟨u, hu, v, hv, rfl⟩ := hx1
    exact lowering_word_hwv_operator_mem hE mu hv hu c d
  | zero => simp
  | add x y hx1 hy1 hx2 hy2 =>
    rw [map_add (f := _)]; exact Submodule.add_mem _ (hx2 hx1) (hy2 hy1)
  | smul c x hx1 hx2 => rw [map_smul]; exact Submodule.smul_mem _ _ (hx2 hx1)

theorem isotypic_le_lowering_span {E : GLOps n K V} (hE : IsGLRep E) (mu : Fin n → ℤ) : isoSub E mu ≤ hwvLoweringSpan E mu := by
  unfold isoSub
  rw [Submodule.span_le]
  rintro x ⟨u, hu, v, hv, rfl⟩
  unfold Umon at hu
  induction hu using Submonoid.closure_induction_left with
  | one => exact Submodule.subset_span ⟨1, (loweringMonoid E).one_mem, v, hv, rfl⟩
  | mul_left g hg y _ ih =>
    obtain ⟨ab, rfl⟩ := hg
    exact hwv_lowering_span_stable hE mu ab.1 ab.2 ih

theorem hwv_orthogonal_lowering_span [CharZero K] {E : GLOps n K V} (B : V →ₗ[K] V →ₗ[K] K)
    (hB : ∀ a b x y, B (E a b x) y = B x (E b a y)) {lam mu : Fin n → ℤ} (hne : lam ≠ mu) {v : V}
    (hv : IsHWV E lam v) {z : V} (hz : z ∈ hwvLoweringSpan E mu) : B v z = 0 := by
  unfold hwvLoweringSpan at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, w, hw, rfl⟩ := hx
    unfold loweringMonoid at hu
    induction hu using Submonoid.closure_induction_left with
    | one =>
      rw [Module.End.one_apply]
      obtain ⟨a, ha⟩ : ∃ a, lam a ≠ mu a := by
        by_contra h
        push_neg at h
        exact hne (funext h)
      have h1 := hB a a v w
      rw [(mem_weightSpace_iff_diagonal_rep E lam v).1 hv.2.1 a, (mem_weightSpace_iff_diagonal_rep E mu w).1 hw.2.1 a, map_smul, map_smul,
        LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at h1
      have h2 : ((lam a : K) - (mu a : K)) * B v w = 0 := by rw [sub_mul, h1, sub_self]
      rcases mul_eq_zero.1 h2 with h3 | h3
      · exfalso; apply ha
        have : (lam a : K) = (mu a : K) := sub_eq_zero.1 h3
        exact_mod_cast this
      · exact h3
    | mul_left g hg y _ _ =>
      obtain ⟨c, d, hcd, rfl⟩ := hg
      rw [Module.End.mul_apply, ← hB d c v (y w), hv.2.2 d c hcd]
      simp
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

theorem contravariant_orthogonality_holds : ContravariantIsotypicOrthogonal := by
  intro K V _ _ _ _ n E hE B hB lam mu hne x hx
  unfold isoSub at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    unfold Umon at hu
    induction hu using Submonoid.closure_induction_left with
    | one =>
      intro y hy
      exact hwv_orthogonal_lowering_span B hB hne hv (isotypic_le_lowering_span hE mu hy)
    | mul_left g hg u' _ ih =>
      obtain ⟨ab, rfl⟩ := hg
      intro y hy
      rw [Module.End.mul_apply]
      show B (E ab.1 ab.2 (u' v)) y = 0
      rw [hB]
      exact ih _ (isotypic_stable_operator E mu _ _ hy)
  | zero => intro y _; simp
  | add x y _ _ hx hy => intro z hz; rw [map_add (f := _), LinearMap.add_apply, hx z hz, hy z hz, add_zero]
  | smul c x _ hx => intro z hz; rw [map_smul, LinearMap.smul_apply, hx z hz, smul_zero]

end Formalism.MainNotions.G.GLWeightTheory
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicProjectorLatticeScaling
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem monomial_exponent_le_multidegree {ι : Type*} {n : ℕ} (m : ι × Fin n →₀ ℕ) (l : ι) (a : Fin n) : m (l, a) ≤ multideg m l := by
  exact Finset.single_le_sum (f := fun c => m (l, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

theorem polynomial_weight_difference_le {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι) (d : ι → ℕ)
    (m m' : ι × Fin n →₀ ℕ) (hm : ∀ i, multideg m i = d i) (hm' : ∀ i, multideg m' i = d i) (a b : Fin n) :
    wtS LL S m a - wtS LL S m' b ≤ (degIn d S : ℤ) := by
  unfold wtS degIn
  rw [← Finset.sum_sub_distrib]
  push_cast
  refine Finset.sum_le_sum fun l _ => ?_
  have h1 := monomial_exponent_le_multidegree m l a
  have h2 := monomial_exponent_le_multidegree m' l b
  rw [hm l] at h1
  rw [hm' l] at h2
  split_ifs <;> omega

theorem prime_pow_smul_cast {O : Type} [CommRing O] [IsDomain O] {σ : Type} (p k : ℕ) (y : MvPolynomial σ (KK O)) :
    ((p : O) ^ k) • y = ((p : KK O) ^ k) • y := by
  rw [← algebraMap_smul (KK O) ((p : O) ^ k) y, map_pow, map_natCast]

theorem isotypic_projector_lattice_scaling (D : Formalism.BasicNotions.D7) (hDom : HighestWeightDominant) (hRes : SubrepRestrictionRep) (hPol : PolynomialGLRepresentation) (h13 : IsotypicProjectorTheoremField D)
    (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (S0 : UniformizedDVR p O)
    (hG : AdmissibleDVR p n' O) [CharZero (KK O)] (n : ℕ) (ι : Type) [Fintype ι] (LL : Letters ι) (S : Set ι)
    (d : ι → ℕ) (lam : Fin n → ℤ) (e : Module.End (KK O) (MvPolynomial (ι × Fin n) (KK O)))
    (he : IsIsoProj (glOps (KK O) n LL S) lam e) :
    (∀ F ∈ Pol (KK O) n d, e F ∈ Pol (KK O) n d) ∧
    ∀ L : Submodule O (MvPolynomial (ι × Fin n) (KK O)),
      (∀ u ∈ UZgens (glOps (KK O) n LL S), ∀ F ∈ L, u F ∈ L) → (latticeMultidegreePart L d).FG →
      MQ (K := KK O) (latticeMultidegreePart L d) = ⊤ →
      ∀ F ∈ Pol (KK O) n d, F ∈ L →
        ((p : KK O) ^ (N0 n * Nat.log p (2 * degIn d S + n - 1))) • e F ∈ L := by
  obtain ⟨hRep, -, -, hStab, hFD, hWt, -⟩ := hPol (KK O) ι n LL
  have hStabS : ∀ a b, ∀ x ∈ Pol (KK O) n d, glOps (KK O) n LL S a b x ∈ Pol (KK O) n d :=
    fun a b x hx => hStab S d a b x hx
  obtain ⟨hResRep, hResWt, hResDiv, hResBin, hResProj, hResZero⟩ :=
    hRes (KK O) (MvPolynomial (ι × Fin n) (KK O)) n (glOps (KK O) n LL S) (hRep S) (Pol (KK O) n d) hStabS
  obtain ⟨e', he'P, he'eq⟩ := hResProj lam e he
  have hPres : ∀ F ∈ Pol (KK O) n d, e F ∈ Pol (KK O) n d := by
    intro F hF
    have h := (e' ⟨F, hF⟩).2
    rwa [he'eq ⟨F, hF⟩] at h
  refine ⟨hPres, ?_⟩
  intro L hLst hFG hMQ F hF hFL
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hid : e F = F := by
      by_cases h0 : F = 0
      · rw [h0, map_zero]
      · apply he.1
        apply Submodule.subset_span
        refine ⟨1, Submonoid.one_mem _, F, ⟨h0, ?_, fun a => a.elim0⟩, by simp⟩
        simp [weightSp]
    rw [hid]
    simpa [N0] using hFL
  · have : NeZero n := ⟨hn.ne'⟩
    have : FiniteDimensional (KK O) (Pol (KK O) n d) := hFD d

    have hwt : ∀ (mu : Fin n → ℤ) (x : Pol (KK O) n d), x ≠ 0 →
        x ∈ weightSp (restrictStableOperators (glOps (KK O) n LL S) (Pol (KK O) n d) hStabS) mu →
        ∃ m : ι × Fin n →₀ ℕ, (∀ i, multideg m i = d i) ∧ wtS LL S m = mu := by
      intro mu x hx0 hx
      have hxV := (hResWt mu x).mp hx
      have hne : (x : MvPolynomial (ι × Fin n) (KK O)) ≠ 0 := by simpa using hx0
      obtain ⟨m, hm⟩ : (x : MvPolynomial (ι × Fin n) (KK O)).support.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr (by rwa [Ne, MvPolynomial.support_eq_empty])
      refine ⟨m, ?_, hWt S mu _ hxV m hm⟩
      have hx2 : (x : MvPolynomial (ι × Fin n) (KK O)) ∈
          MvPolynomial.restrictSupport (KK O) {m : ι × Fin n →₀ ℕ | ∀ i, multideg m i = d i} := x.2
      exact (show ((x : MvPolynomial (ι × Fin n) (KK O)).support : Set (ι × Fin n →₀ ℕ)) ⊆
        {m : ι × Fin n →₀ ℕ | ∀ i, multideg m i = d i} from hx2) hm
    by_cases hhw : ∃ v : Pol (KK O) n d,
        IsHWV (restrictStableOperators (glOps (KK O) n LL S) (Pol (KK O) n d) hStabS) lam v
    · have hdom : Dominant lam := by
        obtain ⟨v, hv⟩ := hhw
        exact hDom (KK O) (Pol (KK O) n d) n _ hResRep lam v hv
      have hWtBound : ellWt lam ≤ degIn d S := by
        obtain ⟨v, hv⟩ := hhw
        obtain ⟨m, hmd, hmw⟩ := hwt lam v hv.1 hv.2.1
        have h := polynomial_weight_difference_le LL S d m m hmd hmd 0 (lastIdx n)
        rw [hmw] at h
        unfold ellWt
        omega
      have hEllBound : ellOf (restrictStableOperators (glOps (KK O) n LL S) (Pol (KK O) n d) hStabS) ⊤ ≤ degIn d S := by
        unfold ellOf
        apply csSup_le'
        rintro k ⟨mu, hmu, nu, hnu, a, b, hab, hk⟩
        obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp (by simpa [wtsOf] using hmu)
        obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).mp (by simpa [wtsOf] using hnu)
        obtain ⟨m, hmd, hmw⟩ := hwt mu x hx0 hx
        obtain ⟨m', hmd', hmw'⟩ := hwt nu y hy0 hy
        have e1 := congrFun hk a
        have e2 := congrFun hk b
        simp [rootW, hab, Ne.symm hab] at e1 e2
        have d1 := polynomial_weight_difference_le LL S d m m hmd hmd a b
        have d2 := polynomial_weight_difference_le LL S d m' m' hmd' hmd' b a
        rw [hmw] at d1
        rw [hmw'] at d2
        omega
      have hLat : UZLattice (O := O) (restrictStableOperators (glOps (KK O) n LL S) (Pol (KK O) n d) hStabS)
          (latticeMultidegreePart L d) := by
        refine ⟨?_, hFG⟩
        intro u hu x hx
        rw [latticeMultidegreePart, Submodule.mem_comap] at hx ⊢
        rcases hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
        · change ((divPowE _ a b k x : Pol (KK O) n d) : MvPolynomial (ι × Fin n) (KK O)) ∈ L
          rw [hResDiv a b k x]
          exact hLst _ (Or.inl ⟨a, b, k, hab, rfl⟩) _ hx
        · change ((binomE _ a k x : Pol (KK O) n d) : MvPolynomial (ι × Fin n) (KK O)) ∈ L
          rw [hResBin a k x]
          exact hLst _ (Or.inr ⟨a, k, rfl⟩) _ hx
      have key := h13 p n' O S0 hG n (Pol (KK O) n d) _ hResRep (latticeMultidegreePart L d) hLat hMQ {lam}
        (by simpa using hdom) (fun _ => e') (by simpa using he'P) ⟨F, hF⟩ hFL
      simp only [Finset.sup_singleton, Finset.sum_singleton, hMQ] at key
      rw [latticeMultidegreePart, Submodule.mem_comap] at key
      have key' : ((p : O) ^ (N0 n * deF p n (ellOf (restrictStableOperators (glOps (KK O) n LL S) (Pol (KK O) n d) hStabS) ⊤
          + ellWt lam))) • e F ∈ L := by
        simpa [he'eq] using key
      have hle : N0 n * deF p n (ellOf (restrictStableOperators (glOps (KK O) n LL S) (Pol (KK O) n d) hStabS) ⊤ + ellWt lam)
          ≤ N0 n * Nat.log p (2 * degIn d S + n - 1) := by
        unfold deF
        exact Nat.mul_le_mul_left _ (Nat.log_mono_right (by omega))
      obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hle
      rw [hj, ← prime_pow_smul_cast p _ (e F), pow_add, mul_comm, mul_smul]
      exact L.smul_mem _ key'
    · have h0 : e F = 0 := hResZero lam e he hhw F hF
      rw [h0, smul_zero]
      exact L.zero_mem

end Formalism.MainNotions.G.GLWeightTheory
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.CrRootMem
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ}

def cr_Pos (n : ℕ) : AddSubmonoid (Fin n → ℤ) :=
  AddSubmonoid.closure {β | ∃ a b : Fin n, a < b ∧ β = rootW a b}

def cr_h (ν : Fin n → ℤ) : ℤ := ∑ a : Fin n, ∑ b : Fin n, if a < b then ν a - ν b else 0

def cr_c (ν : Fin n → ℤ) : ℤ := ∑ a, ν a ^ 2 + cr_h ν

theorem cr_ht_add (x y : Fin n → ℤ) : weightHeight' (x + y) = weightHeight' x + weightHeight' y := by
  simp only [weightHeight', Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem cr_ht_zero : weightHeight' (0 : Fin n → ℤ) = 0 := by simp [weightHeight']

theorem cr_ht_root (a b : Fin n) (h : a < b) : 0 < weightHeight' (rootW a b) := by
  have := v2rep_ht_root (0 : Fin n → ℤ) a b h
  rwa [zero_add, cr_ht_zero] at this

theorem cr_h_eq (ν : Fin n → ℤ) : cr_h ν = ∑ a : Fin n, ((n : ℤ) - 1 - 2 * (a.val : ℤ)) * ν a := by
  classical
  have h1 : ∀ a : Fin n, (∑ b : Fin n, if a < b then ν a else 0) = ((n : ℤ) - 1 - (a.val : ℤ)) * ν a := by
    intro a
    rw [← Finset.sum_filter, Finset.sum_const]
    have : (Finset.univ.filter fun b : Fin n => a < b) = Finset.Ioi a := by ext b; simp
    rw [this, Fin.card_Ioi, nsmul_eq_mul]
    have ha := a.isLt
    congr 1
    omega
  have h2 : ∀ b : Fin n, (∑ a : Fin n, if a < b then ν b else 0) = (b.val : ℤ) * ν b := by
    intro b
    rw [← Finset.sum_filter, Finset.sum_const]
    have : (Finset.univ.filter fun a : Fin n => a < b) = Finset.Iio b := by ext a; simp
    rw [this, Fin.card_Iio, nsmul_eq_mul]
  have h3 : cr_h ν = (∑ a : Fin n, ∑ b : Fin n, if a < b then ν a else 0) -
      ∑ a : Fin n, ∑ b : Fin n, if a < b then ν b else 0 := by
    rw [cr_h, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  rw [h3, Finset.sum_comm (f := fun a b : Fin n => if a < b then ν b else 0), Finset.sum_congr rfl fun a _ => h1 a,
    Finset.sum_congr rfl fun b _ => h2 b, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem cr_h_ht (ν : Fin n → ℤ) : cr_h ν = ((n : ℤ) - 1) * ∑ a, ν a + 2 * weightHeight' ν := by
  rw [cr_h_eq, weightHeight', Finset.mul_sum, mul_neg, Finset.mul_sum, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem cr_Pos_sum {β : Fin n → ℤ} (h : β ∈ cr_Pos n) : ∑ a, β a = 0 := by
  classical
  induction h using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨a, b, _, rfl⟩ := hx
    simp [rootW, Finset.sum_sub_distrib]
  | zero => simp
  | add x y _ _ hx hy => simp [Finset.sum_add_distrib, hx, hy]

theorem cr_Pos_ht {β : Fin n → ℤ} (h : β ∈ cr_Pos n) : 0 ≤ weightHeight' β := by
  induction h using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨a, b, hab, rfl⟩ := hx
    exact (cr_ht_root a b hab).le
  | zero => rw [cr_ht_zero]
  | add x y _ _ hx hy => rw [cr_ht_add]; omega

theorem cr_Pos_pair {ν β : Fin n → ℤ} (hν : Dominant ν) (h : β ∈ cr_Pos n) : 0 ≤ ∑ a, ν a * β a := by
  classical
  induction h using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨a, b, hab, rfl⟩ := hx
    have : ∑ c, ν c * rootW a b c = ν a - ν b := by
      simp [rootW, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
    rw [this]
    have := hν hab.le
    omega
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    omega

theorem cr_root_mem (a b : Fin n) (h : a < b) : rootW a b ∈ cr_Pos n :=
  AddSubmonoid.subset_closure ⟨a, b, h, rfl⟩

theorem cr_c_lt {lam mu : Fin n → ℤ} (hl : Dominant lam) (hm : Dominant mu) (h : lam - mu ∈ cr_Pos n)
    (hpos : 0 < weightHeight' (lam - mu)) : cr_c mu < cr_c lam := by
  have h1 := cr_Pos_pair hl h
  have h2 := cr_Pos_pair hm h
  have h3 := cr_Pos_sum h
  have e1 : cr_h lam - cr_h mu = 2 * weightHeight' (lam - mu) := by
    have hh : cr_h (lam - mu) = 2 * weightHeight' (lam - mu) := by rw [cr_h_ht, h3]; ring
    rw [← hh, cr_h_eq, cr_h_eq, cr_h_eq, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.sub_apply]
    ring
  have e2 : ∑ a, lam a ^ 2 - ∑ a, mu a ^ 2 = ∑ a, lam a * (lam - mu) a + ∑ a, mu a * (lam - mu) a := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.sub_apply]
    ring
  unfold cr_c
  omega

end Formalism.MainNotions.G.GLWeightTheory
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantProjectionDenominatorBound
section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantProjectionKillsNonzeroWeight
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem invariant_projection_kills_operator (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {K V : Type} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {n : ℕ} (E : GLOps n K V) (hE : IsGLRep E)
    (Inv : Module.End K V) (hInv : IsInvProj E Inv) (a b : Fin n) (x : V) : Inv (E a b x) = 0 := by
  have hs := gl_rep_shifts_weights hE
  have htop := sum_isotypic_top_of_weight_data D h2 E hE hs (findim_weights_bounded E) (weight_projections_integral_findim E)
  have hinv := trivial_isotypic_invariant_holds hE
  have hle : ∀ mu, isoSub E mu ≤ LinearMap.ker (Inv * E a b) := by
    intro mu y hy
    rw [LinearMap.mem_ker, Module.End.mul_apply]
    by_cases hmu : mu = 0
    · subst hmu
      obtain ⟨hy0, hyr⟩ := hinv y hy
      have : E a b y = 0 := by
        rcases lt_trichotomy a b with h | h | h
        · exact hyr a b h
        · subst h
          have := (mem_weightSpace_iff_diagonal_eigen E 0 y).1 hy0 a
          simpa using this
        · exact weight_zero_lowering_kills_raising hE hy0 b a (ne_of_lt h) (hyr b a h)
      rw [this, map_zero]
    · exact hInv.2 mu hmu _ (isotypic_stable_under_gl_operator E mu a b y hy)
  have : (⊤ : Submodule K V) ≤ LinearMap.ker (Inv * E a b) := by
    rw [← htop]
    exact iSup_le hle
  have h3 := this (Submodule.mem_top (x := x))
  rwa [LinearMap.mem_ker, Module.End.mul_apply] at h3

theorem invariant_projection_kills_nonzero_weight (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {K V : Type} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {n : ℕ} (E : GLOps n K V) (hE : IsGLRep E)
    (Inv : Module.End K V) (hInv : IsInvProj E Inv) (μ : Fin n → ℤ) (hμ : μ ≠ 0) (x : V)
    (hx : x ∈ weightSp E μ) : Inv x = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, μ a ≠ 0 := by
    by_contra h
    push Not at h
    exact hμ (funext h)
  have h1 := (mem_weightSpace_iff_diagonal_eigen E μ x).1 hx a
  have h2' : (μ a : K) ≠ 0 := by exact_mod_cast ha
  have h3 : x = E a a (((μ a : K))⁻¹ • x) := by
    rw [map_smul, h1, smul_smul, inv_mul_cancel₀ h2', one_smul]
  rw [h3]
  exact invariant_projection_kills_operator D h2 E hE Inv hInv a a _

theorem invariant_projection_through_zero_weight (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {K V : Type} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {n : ℕ} (E : GLOps n K V) (hE : IsGLRep E)
    (Inv : Module.End K V) (hInv : IsInvProj E Inv) (Θ : (Fin n → ℤ) → Module.End K V)
    (hΘ : ∀ μ ν, ∀ x ∈ weightSp E ν, Θ μ x = if ν = μ then x else 0) (x : V) : Inv x = Inv (Θ 0 x) := by
  classical
  obtain ⟨m, hm⟩ := findim_weights_bounded E
  set box : Finset (Fin n → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(m : ℤ)) m with hbox
  have hb : ∀ ν, weightSp E ν ≠ ⊥ → ν ∈ box := by
    intro ν hν
    rw [hbox, Fintype.mem_piFinset]
    intro a
    rw [Finset.mem_Icc]
    exact abs_le.1 (hm ν hν a)
  have hsum := sum_weight_projections_eq_self E hE Θ hΘ box hb x
  have h0 : (0 : Fin n → ℤ) ∈ box := by
    rw [hbox, Fintype.mem_piFinset]
    intro a
    rw [Finset.mem_Icc]
    constructor <;> simp
  conv_lhs => rw [← hsum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single_of_mem 0 h0]
  intro μ _ hμ
  exact invariant_projection_kills_nonzero_weight D h2 E hE Inv hInv μ hμ _ (weight_projection_mem_weightSpace E hE Θ hΘ μ x)

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def ExtremalProjectorProperties {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (L : ℕ) : Prop :=
  ∀ (c : Fin n) (u : V), u ∈ weightSp E 0 → (∀ a b : Fin n, a < c → b < c → E a b u = 0) →
    (∀ j, j < c → E j c (extremalProjector E c L u) = 0) ∧
    (∀ a b : Fin n, a < c → b < c → E a b (extremalProjector E c L u) = 0) ∧
    extremalProjector E c L u ∈ weightSp E 0 ∧
    ∃ w : Fin n → V, extremalProjector E c L u = u + ∑ i ∈ Finset.Iio c, E c i (w i)

theorem denominator_chain_bound (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (p : ℕ) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CharZero (KK O)] (n : ℕ) (V : Type) [AddCommGroup V]
    [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V] [FiniteDimensional (KK O) V]
    (E : GLOps n (KK O) V) (hE : IsGLRep E) (M : Submodule O V)
    (Inv : Module.End (KK O) V) (hInv : IsInvProj E Inv) (L de : ℕ) (hA : ExtremalProjectorProperties E L)
    (hB : ∀ (c : Fin n) (y : V), y ∈ M → ((p : O) ^ (c.val * de)) • extremalProjector E c L y ∈ M)
    (x0 : V) (hx0 : x0 ∈ weightSp E 0) (hxM : x0 ∈ M) (c : ℕ) (hc : c ≤ n) :
    ∃ y, y ∈ weightSp E 0 ∧ (∀ a b : Fin n, a.val < c → b.val < c → E a b y = 0) ∧ Inv y = Inv x0 ∧
      ((p : O) ^ ((∑ i ∈ range c, i) * de)) • y ∈ M := by
  induction c with
  | zero =>
    refine ⟨x0, hx0, fun a b ha _ => absurd ha (Nat.not_lt_zero _), rfl, ?_⟩
    simpa using hxM
  | succ c ih =>
    obtain ⟨y, hy0, hyk, hyI, hyM⟩ := ih (Nat.le_of_succ_le hc)
    have hcn : c < n := hc
    obtain ⟨cf, hcf⟩ : ∃ cf : Fin n, cf.val = c := ⟨⟨c, hcn⟩, rfl⟩
    obtain ⟨hA1, hA2, hA3, w, hw⟩ := hA cf y hy0 (fun a b ha hb =>
      hyk a b (by have := Fin.lt_def.mp ha; omega) (by have := Fin.lt_def.mp hb; omega))
    refine ⟨extremalProjector E cf L y, hA3, ?_, ?_, ?_⟩
    · intro a b ha hb
      rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha' | ha' <;>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb' | hb'
      · exact hA2 a b (Fin.lt_def.mpr (by omega)) (Fin.lt_def.mpr (by omega))
      · have hb2 : b = cf := Fin.ext (by omega)
        subst hb2
        exact hA1 a (Fin.lt_def.mpr (by omega))
      · have ha2 : a = cf := Fin.ext (by omega)
        subst ha2
        exact weight_zero_lowering_kills_raising hE hA3 b a (by rintro rfl; omega) (hA1 b (Fin.lt_def.mpr (by omega)))
      · have ha2 : a = cf := Fin.ext (by omega)
        have hb2 : b = cf := Fin.ext (by omega)
        rw [ha2, hb2]
        have h0 := hA3
        simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker] at h0
        simpa using h0 cf
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [hw, map_add (f := _), map_sum]
      simp only [invariant_projection_kills_operator D h2 E hE Inv hInv, Finset.sum_const_zero, add_zero]
      exact hyI
    · have hM2 := hB cf _ hyM
      rw [LinearMap.map_smul_of_tower, smul_smul, ← pow_add] at hM2
      have he : (∑ i ∈ range (c + 1), i) * de = cf.val * de + (∑ i ∈ range c, i) * de := by
        rw [Finset.sum_range_succ, hcf]; ring
      rw [he]
      exact hM2

theorem invariant_projection_denominator_bound (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (p : ℕ) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CharZero (KK O)] (n : ℕ) (V : Type) [AddCommGroup V]
    [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V] [FiniteDimensional (KK O) V]
    (E : GLOps n (KK O) V) (hE : IsGLRep E) (M : Submodule O V) (hM : UZStable (O := O) E M)
    (Inv : Module.End (KK O) V) (hInv : IsInvProj E Inv) (L de : ℕ) (hA : ExtremalProjectorProperties E L)
    (hB : ∀ (c : Fin n) (y : V), y ∈ M → ((p : O) ^ (c.val * de)) • extremalProjector E c L y ∈ M)
    (x : V) (hx : x ∈ M) : ((p : O) ^ (N0 n * de)) • Inv x ∈ M := by
  obtain ⟨Θ, hΘ1, hΘ2⟩ := weight_projections_integral_findim E
  obtain ⟨y, hy0, hyk, hyI, hyM⟩ := denominator_chain_bound D h2 p O n V E hE M Inv hInv L de hA hB (Θ 0 x)
    (weight_projection_mem_weightSpace E hE Θ hΘ2 0 x) (binomial_subring_preserves_lattice hM _ (hΘ1 0) x hx) n le_rfl
  have hInvy : Inv y = y := by
    by_cases hy : y = 0
    · rw [hy, map_zero]
    · apply hInv.1
      exact Submodule.subset_span ⟨1, one_mem _, y, ⟨hy, hy0, fun a b _ => hyk a b a.2 b.2⟩, rfl⟩
  rw [invariant_projection_through_zero_weight D h2 E hE Inv hInv Θ hΘ2 x, ← hyI, hInvy]
  rwa [Finset.sum_range_id] at hyM

end Formalism.MainNotions.G.GLWeightTheory
end
end
