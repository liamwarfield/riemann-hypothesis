module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AffineChartIdealPrimeAndSaturated
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsChart
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsMulMemOfAlgebraMapLocRingEqZero

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SymbolicPowerFromAffineChart
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SymbolicPowerFromAffineChart
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dehom

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (cycBlockWt cyc_exists_blockComponent cyc_isHomogeneous_of_isMultiHomogIdeal)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def mdeg (m : (Σ k, ι k) →₀ ℕ) : K → ℕ := fun k => ∑ i, m ⟨k, i⟩

theorem mdeg_add (m n : (Σ k, ι k) →₀ ℕ) : mdeg (m + n) = mdeg m + mdeg n := by
  funext k
  simp [mdeg, Finset.sum_add_distrib]


open Classical in
def part (b : K → ℕ) (s : MvPolynomial (Σ k, ι k) ℂ) : MvPolynomial (Σ k, ι k) ℂ :=
  ∑ m ∈ s.support.filter (fun m => mdeg m = b), monomial m (AddMonoidAlgebra.coeff s m)

open Classical in
theorem coeff_part (b : K → ℕ) (s : MvPolynomial (Σ k, ι k) ℂ) (m : (Σ k, ι k) →₀ ℕ) :
    AddMonoidAlgebra.coeff (part b s) m = if mdeg m = b then AddMonoidAlgebra.coeff s m else 0 := by
  unfold part
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases h : mdeg m = b
  · by_cases hs : m ∈ s.support
    · simp [h, hs]
    · have : AddMonoidAlgebra.coeff s m = 0 := by simpa using hs
      simp [this]
  · simp [h]

open Classical in
theorem sum_part (s : MvPolynomial (Σ k, ι k) ℂ) :
    ∑ b ∈ s.support.image mdeg, part b s = s := by
  unfold part
  rw [Finset.sum_fiberwise_of_maps_to (fun m hm => Finset.mem_image_of_mem _ hm)]
  exact s.support_sum_monomial_coeff

theorem isMultiHomog_part (b : K → ℕ) (s : MvPolynomial (Σ k, ι k) ℂ) :
    IsMultiHomog (part b s) b := by
  classical
  intro m hm k
  rw [mem_support_iff, coeff_part] at hm
  by_contra hk
  refine hm (if_neg fun h => hk ?_)
  exact congrFun h k

theorem isMultiHomog_mul {s f : MvPolynomial (Σ k, ι k) ℂ} {b a : K → ℕ}
    (hs : IsMultiHomog s b) (hf : IsMultiHomog f a) : IsMultiHomog (s * f) (b + a) := by
  classical
  intro m hm k
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.1 (support_mul s f hm)
  have := congrFun (mdeg_add m₁ m₂) k
  simp only [mdeg, Pi.add_apply] at this
  rw [this, hs m₁ h₁ k, hf m₂ h₂ k]
  rfl

theorem coeff_mul_eq_zero {r f : MvPolynomial (Σ k, ι k) ℂ} {b a : K → ℕ}
    (hr : ∀ m ∈ r.support, mdeg m ≠ b) (hf : IsMultiHomog f a) {m : (Σ k, ι k) →₀ ℕ}
    (hm : mdeg m = b + a) : AddMonoidAlgebra.coeff (r * f) m = 0 := by
  classical
  by_contra h
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.1 (support_mul r f (mem_support_iff.2 h))
  refine hr m₁ h₁ (funext fun k => ?_)
  have e := congrFun hm k
  have e' := congrFun (mdeg_add m₁ m₂) k
  have e'' : mdeg m₂ k = a k := hf m₂ h₂ k
  simp only [Pi.add_apply] at e e'
  omega

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem part_mul_mem [DecidableEq K] {I : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
    (hI : ∀ k, I.IsHomogeneous (weightedHomogeneousSubmodule ℂ (cycBlockWt (ι := ι) k)))
    {s f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ} (hf : IsMultiHomog f a) (h : s * f ∈ I)
    (b : K → ℕ) : part b s * f ∈ I := by
  classical
  obtain ⟨g, hgI, hg⟩ := cyc_exists_blockComponent hI (b + a) Finset.univ h
  have hgeq : g = part b s * f := by
    ext m
    rw [hg m]
    by_cases hm : mdeg m = b + a
    · have e : ∀ k ∈ (Finset.univ : Finset K), ∑ i, m ⟨k, i⟩ = (b + a) k :=
        fun k _ => congrFun hm k
      rw [if_pos e]
      have hr : ∀ m' ∈ (s - part b s).support, mdeg m' ≠ b := by
        intro m' hm' hb
        rw [mem_support_iff, coeff_sub, coeff_part, if_pos hb, sub_self] at hm'
        exact hm' rfl
      have e2 : s * f = part b s * f + (s - part b s) * f := by ring
      rw [e2, MvPolynomial.coeff_add, coeff_mul_eq_zero hr hf hm, add_zero]
    · have e : ¬ ∀ k ∈ (Finset.univ : Finset K), ∑ i, m ⟨k, i⟩ = (b + a) k :=
        fun h' => hm (funext fun k => h' k (Finset.mem_univ k))
      rw [if_neg e]
      by_contra hne
      exact hm (funext fun k => isMultiHomog_mul (isMultiHomog_part b s) hf m
        (mem_support_iff.2 (Ne.symm hne)) k)
  exact hgeq ▸ hgI

theorem isHomogeneous_pow {A : Type*} [CommRing A] {R : Type*} [CommRing R] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {I : Ideal A} (hI : I.IsHomogeneous 𝒜) (n : ℕ) :
    (I ^ n).IsHomogeneous 𝒜 := by
  induction n with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top]
    exact (⊤ : HomogeneousIdeal 𝒜).isHomogeneous
  | succ n ih =>
    rw [pow_succ]
    exact ih.mul hI

theorem ren_mem {S : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {p : (k : K) → ι k}
    {g : MvPolynomial (Σ k, ι k) ℂ} (hg : g ∈ ReciprocityTheory.AnForm.R.chartIdeal S p) :
    renR (Σ k, ι k) g ∈ ideal S p := by
  unfold ideal
  rw [mem_map_renR_iff, RingEquiv.symm_apply_apply]
  exact hg

theorem lift_sub_mem (S : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) (q : Σ k, ι k) :
    lift p q - renR (Σ k, ι k) (X q) ∈ ideal S p := by
  classical
  obtain ⟨k, i⟩ := q
  unfold lift
  split_ifs with h
  · simp only at h
    subst h
    have hm : (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ ReciprocityTheory.AnForm.R.chartIdeal S p :=
      Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
    have h2 : renR (Σ k, ι k) (X ⟨k, p k⟩ - 1) ∈ ideal S p := ren_mem hm
    have h3 := (ideal S p).neg_mem h2
    rw [map_sub, map_one, neg_sub] at h3
    exact h3
  · have : renR (Σ k, ι k) (X (⟨k, i⟩ : Σ k, ι k)) = X (Fintype.equivFin (Σ k, ι k) ⟨k, i⟩) := by
      simp [renameEquiv_apply]
    rw [this, sub_self]
    exact zero_mem _

theorem deh_sub_mem (S : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k)
    (g : MvPolynomial (Σ k, ι k) ℂ) :
    bind₁ (lift p) g - renR (Σ k, ι k) g ∈ ideal S p := by
  induction g using MvPolynomial.induction_on with
  | C c =>
    have e : renR (Σ k, ι k) (C c) = C c := by simp [renameEquiv_apply]
    rw [e, bind₁_C_right, sub_self]
    exact zero_mem _
  | add g h hg hh =>
    rw [map_add (f := _), map_add (f := _), add_sub_add_comm]
    exact add_mem hg hh
  | mul_X g q hg =>
    rw [map_mul, map_mul, bind₁_X_right]
    have e : bind₁ (lift p) g * lift p q - renR (Σ k, ι k) g * renR (Σ k, ι k) (X q) =
        (bind₁ (lift p) g - renR (Σ k, ι k) g) * lift p q +
          renR (Σ k, ι k) g * (lift p q - renR (Σ k, ι k) (X q)) := by ring
    rw [e]
    exact add_mem (Ideal.mul_mem_right _ _ hg) (Ideal.mul_mem_left _ _ (lift_sub_mem S p q))

theorem map_deh_le (S : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    Ideal.map (bind₁ (lift p) : _ →ₐ[ℂ] _) S ≤ ideal S p := by
  rw [Ideal.map_le_iff_le_comap]
  intro g hg
  have hm : renR (Σ k, ι k) g ∈ ideal S p := ren_mem (Ideal.mem_sup_left hg)
  rw [Ideal.mem_comap]
  have := add_mem (deh_sub_mem S p g) hm
  rwa [sub_add_cancel] at this

theorem relation_dehom : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k)
    (f s : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ) (n : ℕ), IsMultiHomogIdeal P →
    IsMultiHomogIdeal Q → Q.IsPrime → (∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) →
    IsMultiHomog f a → s ∉ Q → s * f ∈ Q ^ n ⊔ P →
    ∃ s' ∉ SncRes.ideal Q p, s' * bind₁ (SncRes.lift p) f ∈ SncRes.ideal Q p ^ n ⊔ SncRes.ideal P p := by
  intro K _ ι _ P Q p f s a n hP hQ hQp hX hf hs hrel
  classical
  have hI : ∀ k, (Q ^ n ⊔ P).IsHomogeneous
      (weightedHomogeneousSubmodule ℂ (cycBlockWt (ι := ι) k)) := fun k =>
    (isHomogeneous_pow _ (cyc_isHomogeneous_of_isMultiHomogIdeal hQ k) n).sup
      (cyc_isHomogeneous_of_isMultiHomogIdeal hP k)
  obtain ⟨b, hb⟩ : ∃ b, part b s ∉ Q := by
    by_contra hall
    push_neg at hall
    exact hs (sum_part s ▸ Ideal.sum_mem _ fun b _ => hall b)
  have hmem := part_mul_mem hI hf hrel b
  refine ⟨bind₁ (lift p) (part b s), ?_, ?_⟩
  · rw [((GlobalTheory.T.affine_chart_ideal_prime_and_saturated K ι Q p hQ hQp hX).2 _ b (isMultiHomog_part b s))]
    exact hb
  · have h1 := Ideal.mem_map_of_mem (bind₁ (lift p) : _ →ₐ[ℂ] _) hmem
    rw [map_mul, Ideal.map_sup, Ideal.map_pow] at h1
    exact (sup_le_sup (Ideal.pow_right_mono (map_deh_le Q p) n) (map_deh_le P p)) h1

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dehom
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SymbolicPowerFromAffineChartStatement
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symbolic_power_from_affine_chart : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) (f s : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ) (n : ℕ), IsMultiHomogIdeal P → IsMultiHomogIdeal Q → Q.IsPrime → (∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) → IsMultiHomog f a → s ∉ Q → s * f ∈ Q ^ n ⊔ P → ∃ s' ∉ SncRes.ideal Q p, s' * bind₁ (SncRes.lift p) f ∈ SncRes.ideal Q p ^ n ⊔ SncRes.ideal P p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dehom.relation_dehom | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dehom.relation_dehom | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dehom.relation_dehom <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncChartRegularWithBoundaryChoice
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncChartRegularWithBoundaryChoice
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.NearComp

open MvPolynomial ReciprocityTheory.AnForm.R

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_den_chPrime {m : ℕ} (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
    (r : MvPolynomial (Fin m) ℂ) :
    ∃ s : MvPolynomial (Fin m) ℂ, eval t s ≠ 0 ∧ ∀ w : Fin m → ℂ, (∀ h ∈ I, eval w h = 0) →
      eval w s ≠ 0 → eval w r = 0 → ∀ g ∈ Par.chPrime I t r, eval w g = 0 := by
  classical
  have hgen : ∀ g ∈ Par.chPrime I t r, ∃ u : MvPolynomial (Fin m) ℂ, eval t u ≠ 0 ∧
      ∀ w : Fin m → ℂ, (∀ h ∈ I, eval w h = 0) → eval w u ≠ 0 → eval w r = 0 → eval w g = 0 := by
    intro g hg
    have hg' : algebraMap _ (locRing I t) g ∈ Ideal.span {algebraMap _ (locRing I t) r} := hg
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hg'
    obtain ⟨c, b, hb, hcb⟩ := exists_mk_locRing I t a
    have h0 : algebraMap _ (locRing I t) (b * g - c * r) = 0 := by
      rw [map_sub, map_mul, map_mul, ← ha, ← hcb]
      ring
    obtain ⟨s, hs, hsI⟩ := IrreducibleComponentPreimages.exists_mul_mem_of_algebraMap_locRing_eq_zero I t h0
    refine ⟨s * b, ?_, fun w hw hsb hr => ?_⟩
    · rw [map_mul]
      exact mul_ne_zero hs hb
    · have h1 := hw _ hsI
      rw [map_mul] at hsb
      rw [map_mul, map_sub, map_mul, map_mul, hr, mul_zero, sub_zero, ← mul_assoc] at h1
      exact (mul_eq_zero.1 h1).resolve_left hsb
  obtain ⟨S, hS⟩ : (Par.chPrime I t r).FG := IsNoetherian.noetherian _
  have hSm : ∀ g ∈ S, g ∈ Par.chPrime I t r := fun g hg => hS ▸ Ideal.subset_span hg
  choose! u hu hu' using fun g (hg : g ∈ S) => hgen g (hSm g hg)
  refine ⟨∏ g ∈ S, u g, ?_, fun w hw hs hr g hg => ?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 hu
  · rw [map_prod] at hs
    have hle : Par.chPrime I t r ≤ RingHom.ker (eval w) := by
      rw [← hS, Ideal.span_le]
      intro f hf
      exact hu' f hf w hw (Finset.prod_ne_zero_iff.1 hs f hf) hr
    exact hle hg

theorem zero_iff {P Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hQ : IsMultiHomogIdeal Q)
    (p : (k : K) → ι k) (x : Pts P) (hx : x ∈ src P p) :
    (∀ f ∈ Q, eval (rep x) f = 0) ↔ ∀ h ∈ ideal Q p, eval (coord P p x) h = 0 := by
  have hiff := mem_conePts_iff_chartIdeal hQ p (rep x) hx
  constructor
  · intro h
    exact renPt_zero _ _ (hiff.1 ⟨(rep_mem x).1, h⟩)
  · intro h
    have h2 : rep x ∈ conePts Q := hiff.2 fun f hf => by
      rw [← eval_renC]
      exact h _ (Ideal.mem_map_of_mem _ hf)
    exact h2.2

theorem continuousOn_coord {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (p : (k : K) → ι k) :
    ContinuousOn (coord P p) (src P p) :=
  continuousOn_iff_continuous_domRestrict.2 (Top.isEmbedding_coord p).continuous

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.NearComp

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.NearComp.comp_eq_near : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ) (p : (k : K) → ι k) (x : SncRes.Pts P) (r : Fin e → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) (Jf : Finset (Fin e)) (σ : Fin e → Option (Fin (SncRes.rc P D))), IsMultiHomogIdeal P → IsMultiHomogIdeal D → x ∈ SncRes.src P p → (∀ h ∈ (SncRes.ideal P p), eval (SncRes.coord P p x) h = 0) → IsRegularLocalRing (locRing (SncRes.ideal P p) (SncRes.coord P p x)) → ringKrullDim (locRing (SncRes.ideal P p) (SncRes.coord P p x)) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing (SncRes.ideal P p) (SncRes.coord P p x)) (r l)) = Ideal.map (algebraMap _ (locRing (SncRes.ideal P p) (SncRes.coord P p x))) (ptIdeal (SncRes.coord P p x)) → (∀ l, σ l = none ↔ l ∉ Jf) → (∀ l k, σ l = some k → SncRes.ideal (SncRes.compIdeal P D k) p = SncRes.Par.chPrime (SncRes.ideal P p) (SncRes.coord P p x) (r l)) → (∀ k, (∀ g ∈ SncRes.compIdeal P D k, eval (SncRes.rep x) g = 0) → ∃ l ∈ Jf, σ l = some k) → ∃ O : Set (SncRes.Pts P), IsOpen O ∧ x ∈ O ∧ O ⊆ SncRes.src P p ∧ ∀ k, SncRes.comp P D k ∩ O = {x' ∈ O | ∃ l, σ l = some k ∧ eval (SncRes.coord P p x') (r l) = 0} := by
  intro K _ ι _ P D e p x r Jf σ hP hD hx _ _ _ _ _ hch hout
  classical
  have hQ : ∀ k, IsMultiHomogIdeal (SncRes.compIdeal P D k) := fun k =>
    MinHom.isMultiHomogIdeal_of_mem_minimalPrimes_sup K ι P D hP hD _ (SncRes.compIdeal_mem D k)
  choose s hst hsw using fun l =>
    SncRes.NearComp.exists_den_chPrime (SncRes.ideal P p) (SncRes.coord P p x) (r l)
  have hg : ∀ k, ∃ g, eval (SncRes.coord P p x) g ≠ 0 ∧
      ((∃ l, σ l = some k) ∨ g ∈ SncRes.ideal (SncRes.compIdeal P D k) p) := by
    intro k
    by_cases hk : ∃ l, σ l = some k
    · exact ⟨1, by simp, Or.inl hk⟩
    · have hnz : ¬ ∀ g ∈ SncRes.compIdeal P D k, eval (SncRes.rep x) g = 0 := fun h => by
        obtain ⟨l, -, hl⟩ := hout k h
        exact hk ⟨l, hl⟩
      have hn : ¬ ∀ h ∈ SncRes.ideal (SncRes.compIdeal P D k) p,
          eval (SncRes.coord P p x) h = 0 :=
        fun h => hnz ((SncRes.NearComp.zero_iff (hQ k) p x hx).2 h)
      push Not at hn
      obtain ⟨g, hg, hgt⟩ := hn
      exact ⟨g, hgt, Or.inr hg⟩
  choose g hgt hgk using hg
  let F := (∏ l, s l) * ∏ k, g k
  have hFw : ∀ w, eval w F ≠ 0 ↔ (∀ l, eval w (s l) ≠ 0) ∧ ∀ k, eval w (g k) ≠ 0 := by
    intro w
    simp only [F, map_mul, map_prod, ne_eq, mul_eq_zero, not_or, Finset.prod_eq_zero_iff,
      Finset.mem_univ, true_and, not_exists]
  refine ⟨SncRes.src P p ∩ SncRes.coord P p ⁻¹' {w | eval w F ≠ 0}, ?_,
    ⟨hx, (hFw _).2 ⟨hst, hgt⟩⟩, Set.inter_subset_left, fun k => ?_⟩
  · exact (SncRes.NearComp.continuousOn_coord p).isOpen_inter_preimage (SncRes.Top.isOpen_alt_bis p)
      (isOpen_ne_fun (MvPolynomial.continuous_eval F) continuous_const)
  · ext x'
    constructor
    · rintro ⟨hc, ho⟩
      refine ⟨ho, ?_⟩
      have hz := (SncRes.NearComp.zero_iff (hQ k) p x' ho.1).1 hc
      rcases hgk k with ⟨l, hl⟩ | hk
      · refine ⟨l, hl, hz _ ?_⟩
        rw [hch l k hl]
        exact Ideal.mem_comap.2 (Ideal.subset_span rfl)
      · exact absurd (hz _ hk) (((hFw _).1 ho.2).2 k)
    · rintro ⟨ho, l, hl, hr⟩
      refine ⟨?_, ho⟩
      refine (SncRes.NearComp.zero_iff (hQ k) p x' ho.1).2 ?_
      rw [hch l k hl]
      exact hsw l _ ((SncRes.NearComp.zero_iff hP p x' ho.1).1 (SncRes.rep_mem x').2)
        (((hFw _).1 ho.2).1 l) hr
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncChartRegularWithBoundaryChoiceStatement
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_chart_regular_with_boundary_choice : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ) (p : (k : K) → ι k) (x : SncRes.Pts P) (r : Fin e → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) (Jf : Finset (Fin e)) (σ : Fin e → Option (Fin (SncRes.rc P D))), IsMultiHomogIdeal P → IsMultiHomogIdeal D → x ∈ SncRes.src P p → (∀ h ∈ (SncRes.ideal P p), eval (SncRes.coord P p x) h = 0) → IsRegularLocalRing (locRing (SncRes.ideal P p) (SncRes.coord P p x)) → ringKrullDim (locRing (SncRes.ideal P p) (SncRes.coord P p x)) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing (SncRes.ideal P p) (SncRes.coord P p x)) (r l)) = Ideal.map (algebraMap _ (locRing (SncRes.ideal P p) (SncRes.coord P p x))) (ptIdeal (SncRes.coord P p x)) → (∀ l, σ l = none ↔ l ∉ Jf) → (∀ l k, σ l = some k → SncRes.ideal (SncRes.compIdeal P D k) p = SncRes.Par.chPrime (SncRes.ideal P p) (SncRes.coord P p x) (r l)) → (∀ k, (∀ g ∈ SncRes.compIdeal P D k, eval (SncRes.rep x) g = 0) → ∃ l ∈ Jf, σ l = some k) → ∃ O : Set (SncRes.Pts P), IsOpen O ∧ x ∈ O ∧ O ⊆ SncRes.src P p ∧ ∀ k, SncRes.comp P D k ∩ O = {x' ∈ O | ∃ l, σ l = some k ∧ eval (SncRes.coord P p x') (r l) = 0} := by
  intro K _ ι _ P D e p x r Jf σ hP hD hx _ _ _ _ _ hch hout
  classical
  have zero_iff {Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hQ : IsMultiHomogIdeal Q)
      (y : SncRes.Pts P) (hy : y ∈ SncRes.src P p) :
      (∀ f ∈ Q, eval (SncRes.rep y) f = 0) ↔
        ∀ h ∈ SncRes.ideal Q p, eval (SncRes.coord P p y) h = 0 := by
    have hchart := mem_conePts_iff_chartIdeal hQ p (SncRes.rep y) hy
    constructor
    · intro h
      exact renPt_zero _ _ (hchart.1 ⟨(SncRes.rep_mem y).1, h⟩)
    · intro h
      have hyQ : SncRes.rep y ∈ conePts Q := hchart.2 fun f hf => by
        rw [← eval_renC]
        exact h _ (Ideal.mem_map_of_mem _ hf)
      exact hyQ.2
  have norm_ne (y : SncRes.Pts P) (k : K) :
      ((∑ i, ‖SncRes.rep y ⟨k, i⟩‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (SncRes.Top.normSq_pos ((SncRes.rep_mem y).1 k)).ne'
  have mem_src_iff (y : SncRes.Pts P) :
      y ∈ SncRes.src P p ↔ ∀ k, y.1 ⟨k, (p k, p k)⟩ ≠ 0 := by
    refine forall_congr' fun k => ?_
    rw [← SncRes.proj_rep y]
    simp only [SncRes.proj, ne_eq, div_eq_zero_iff, norm_ne, or_false, mul_eq_zero,
      map_eq_zero, or_self]
  have hopen : IsOpen (SncRes.src P p) := by
    have heq : SncRes.src P p = ⋂ k, {y : SncRes.Pts P | y.1 ⟨k, (p k, p k)⟩ ≠ 0} := by
      ext y
      simp [mem_src_iff]
    rw [heq]
    exact isOpen_iInter_of_finite fun k =>
      isOpen_ne_fun ((continuous_apply _).comp continuous_subtype_val) continuous_const
  have hcoord : ContinuousOn (SncRes.coord P p) (SncRes.src P p) := by
    refine continuousOn_iff_continuous_domRestrict.2 (continuous_pi fun j => ?_)
    let q := (Fintype.equivFin (Σ k, ι k)).symm j
    have hratio (y : SncRes.src P p) :
        SncRes.coord P p y.1 j = y.1.1 ⟨q.1, (q.2, p q.1)⟩ / y.1.1 ⟨q.1, (p q.1, p q.1)⟩ := by
      have hstar : starRingEnd ℂ (SncRes.rep y.1 ⟨q.1, p q.1⟩) ≠ 0 := by
        simpa using y.2 q.1
      change affCoord p (SncRes.rep y.1) q = _
      rw [← SncRes.proj_rep y.1]
      simp only [SncRes.proj, affCoord]
      rw [div_div_div_cancel_right₀ (norm_ne y.1 q.1), mul_div_mul_right _ _ hstar]
    have hv (a : Σ k, ι k × ι k) : Continuous fun y : SncRes.src P p => y.1.1 a :=
      (continuous_apply a).comp (continuous_subtype_val.comp continuous_subtype_val)
    change Continuous (fun y : SncRes.src P p => SncRes.coord P p y.1 j)
    simp only [hratio]
    exact (hv ⟨q.1, (q.2, p q.1)⟩).div (hv ⟨q.1, (p q.1, p q.1)⟩)
      (fun y => (mem_src_iff y.1).1 y.2 q.1)
  have hQ (k) : IsMultiHomogIdeal (SncRes.compIdeal P D k) :=
    MinHom.isMultiHomogIdeal_of_mem_minimalPrimes_sup K ι P D hP hD _ (SncRes.compIdeal_mem D k)
  choose s hst hsw using fun l =>
    SncRes.NearComp.exists_den_chPrime (SncRes.ideal P p) (SncRes.coord P p x) (r l)
  have hg : ∀ k, ∃ g, eval (SncRes.coord P p x) g ≠ 0 ∧
      ((∃ l, σ l = some k) ∨ g ∈ SncRes.ideal (SncRes.compIdeal P D k) p) := by
    intro k
    by_cases hk : ∃ l, σ l = some k
    · exact ⟨1, by simp, Or.inl hk⟩
    · have hn : ¬ ∀ h ∈ SncRes.ideal (SncRes.compIdeal P D k) p,
          eval (SncRes.coord P p x) h = 0 := fun h => by
        obtain ⟨l, -, hl⟩ := hout k ((zero_iff (hQ k) x hx).2 h)
        exact hk ⟨l, hl⟩
      push Not at hn
      obtain ⟨g, hg, hgt⟩ := hn
      exact ⟨g, hgt, Or.inr hg⟩
  choose g hgt hgk using hg
  let F := (∏ l, s l) * ∏ k, g k
  have hFw : ∀ w, eval w F ≠ 0 ↔ (∀ l, eval w (s l) ≠ 0) ∧ ∀ k, eval w (g k) ≠ 0 := by
    intro w
    simp only [F, map_mul, map_prod, ne_eq, mul_eq_zero, not_or, Finset.prod_eq_zero_iff,
      Finset.mem_univ, true_and, not_exists]
  refine ⟨SncRes.src P p ∩ SncRes.coord P p ⁻¹' {w | eval w F ≠ 0}, ?_,
    ⟨hx, (hFw _).2 ⟨hst, hgt⟩⟩, Set.inter_subset_left, fun k => ?_⟩
  · exact hcoord.isOpen_inter_preimage hopen
      (isOpen_ne_fun (MvPolynomial.continuous_eval F) continuous_const)
  · ext y
    constructor
    · rintro ⟨hc, ho⟩
      refine ⟨ho, ?_⟩
      have hz := (zero_iff (hQ k) y ho.1).1 hc
      rcases hgk k with ⟨l, hl⟩ | hk
      · refine ⟨l, hl, hz _ ?_⟩
        rw [hch l k hl]
        exact Ideal.mem_comap.2 (Ideal.subset_span rfl)
      · exact absurd (hz _ hk) (((hFw _).1 ho.2).2 k)
    · rintro ⟨ho, l, hl, hr⟩
      refine ⟨(zero_iff (hQ k) y ho.1).2 ?_, ho⟩
      rw [hch l k hl]
      exact hsw l _ ((zero_iff hP y ho.1).1 (SncRes.rep_mem y).2)
        (((hFw _).1 ho.2).1 l) hr
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MemChartWOfContinuousPeriod
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MemChartWOfContinuousPeriod
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

namespace GlobalTheory.CompanionTheory.Ar.Cusp.CentrePeriods

variable {n a g : ℕ} {Λ : Type} [AddCommGroup Λ] {L : Flat.LogPeriods n a g Λ}
  {bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ} {A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ}
  {B : Fin a → Matrix (Fin g) (Fin g) ℤ} {c ρ : ℝ}

theorem exists_ball_det (h : IsChart L bas A T0 B c ρ) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ', (A z).det ≠ 0 := by
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  obtain ⟨ρ₂, K, hρ₂, -, hinv⟩ := GlobalTheory.CompanionTheory.Ar.RiemannLimit.inv n g A
    (h.A_cont.continuousAt (Metric.isOpen_ball.mem_nhds h0)) h.A_det
  exact ⟨min ρ₂ ρ, lt_min hρ₂ h.ρ_pos, min_le_right _ _,
    fun z hz => (hinv z (Metric.ball_subset_ball (min_le_left _ _) hz)).1⟩

theorem A_tendsto (h : IsChart L bas A T0 B c ρ) {zs : ℕ → Fin n → ℂ}
    (hz : Tendsto zs atTop (𝓝 0)) : Tendsto (fun m => A (zs m)) atTop (𝓝 (A 0)) := by
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  exact ((h.A_cont.continuousAt (Metric.isOpen_ball.mem_nhds h0)).tendsto).comp hz

theorem T_tendsto (h : IsChart L bas A T0 B c ρ) {zs : ℕ → Fin n → ℂ}
    (hz : Tendsto zs atTop (𝓝 0)) : Tendsto (fun m => T0 (zs m)) atTop (𝓝 (T0 0)) := by
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  exact ((h.T_cont.continuousAt (Metric.isOpen_ball.mem_nhds h0)).tendsto).comp hz

theorem inv_period (h : IsChart L bas A T0 B c ρ) {ρ' : ℝ}
    (hdet : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ', (A z).det ≠ 0) (w : Fin n → ℂ)
    (hw : w ∈ logCover L.a_le) (hz : expCover a w ∈ Metric.ball (0 : Fin n → ℂ) ρ') (x : Λ) :
    ((A (expCover a w))ᵀ)⁻¹ *ᵥ L.P w x =
      cst (uCo bas x) + tauAt L.a_le T0 B w *ᵥ cst (vCo bas x) := by
  rw [h.per w hw x, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (Ne.isUnit (by rw [det_transpose]; exact hdet _ hz)),
    Matrix.one_mulVec]

theorem tendsto_inv_mulVec (h : IsChart L bas A T0 B c ρ) {zs : ℕ → Fin n → ℂ}
    (hz : Tendsto zs atTop (𝓝 0)) {q : ℕ → Fin g → ℂ} {p : Fin g → ℂ}
    (hq : Tendsto q atTop (𝓝 p)) :
    Tendsto (fun m => ((A (zs m))ᵀ)⁻¹ *ᵥ q m) atTop (𝓝 (((A 0)ᵀ)⁻¹ *ᵥ p)) := by
  have hinv := tendsto_inv_transpose (A_tendsto h hz) h.A_det
  have hy := (((continuous_fst.matrix_mulVec continuous_snd :
    Continuous fun q : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) => q.1 *ᵥ q.2)).tendsto
      (((A 0)ᵀ)⁻¹, p)).comp (hinv.prodMk_nhds hq)
  exact hy.congr fun m => rfl

theorem ker_each (hB : ∀ j, ((B j).map (fun x : ℤ => (x : ℝ))).PosSemidef) (v : Fin g → ℝ)
    (hv : (∑ j, B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0) (j : Fin a) :
    (B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0 := by
  have hR : (∑ j, B j).map (fun x : ℤ => (x : ℝ)) = ∑ j, (B j).map (fun x : ℤ => (x : ℝ)) := by
    ext p q
    simp [Matrix.sum_apply]
  have h0 : v ⬝ᵥ ((∑ j, B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v) = 0 := by rw [hv]; simp
  rw [hR, Matrix.sum_mulVec, dotProduct_sum] at h0
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ v ⬝ᵥ ((B i).map (fun x : ℤ => (x : ℝ)) *ᵥ v) := fun i _ => by
    simpa using (hB i).dotProduct_mulVec_nonneg v
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 j (Finset.mem_univ j)
  exact ((hB j).dotProduct_mulVec_zero_iff).1 (by simpa using h1)

theorem lower_at_centre (h : IsChart L bas A T0 B c ρ) (v : Fin g → ℝ)
    (hv : (∑ j, B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0) :
    c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (((T0 0).map Complex.im) *ᵥ v) := by
  have := GlobalTheory.CompanionTheory.ChartBlockLower.im_lower_on_kernel n a g L.a_le (Metric.ball 0 ρ) T0 B c
    Metric.isOpen_ball (h.T_cont.mono (Metric.ball_subset_ball h.ρ_le)) h.B_psd h.c_pos h.im_lower
    0 (Metric.mem_ball_self h.ρ_pos) (fun _ => 0) (fun j hj => (hj rfl).elim) (fun _ _ => rfl) v
    (fun j _ => ker_each h.B_psd v hv j)
  simpa using this

theorem exp_cast (ha : a ≤ n) (w : Fin n → ℂ) (j : Fin a) :
    Complex.exp (w (Fin.castLE ha j)) = expCover a w (Fin.castLE ha j) := by
  have hj : (Fin.castLE ha j).val < a := j.2
  simp only [expCover, if_pos hj]

theorem extend_mem (h : IsChart L bas A T0 B c ρ) (x : Λ) (t : (Fin n → ℂ) → Fin g → ℂ)
    (ht : ContinuousAt t 0) (hP : ∀ w ∈ logCover L.a_le, L.P w x = t (expCover a w)) :
    x ∈ chartW bas B := by
  classical
  obtain ⟨ρ', hρ', hρle, hdet⟩ := exists_ball_det h
  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  set r : ℕ → ℝ := fun m => ρ'⁻¹ + m with hr
  set tm : ℕ → ℂ := fun m => ((r m / (2 * Real.pi) : ℝ) : ℂ) * Complex.I with htm
  set ws : ℕ → Fin n → ℂ := fun m k => if k.val < a then -(r m : ℂ) else 0 with hws
  have hrpos : ∀ m, 0 < r m := fun m => by
    have : 0 < ρ'⁻¹ := inv_pos.2 hρ'
    have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    simp only [hr]; linarith
  have hexpr : ∀ m, Real.exp (-(r m)) < ρ' := by
    intro m
    have h1 : r m + 1 ≤ Real.exp (r m) := Real.add_one_le_exp _
    have h3 : ρ'⁻¹ ≤ r m := by
      have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      simp only [hr]; linarith
    rw [Real.exp_neg]
    have h4 : ρ'⁻¹ < Real.exp (r m) := by linarith
    exact inv_lt_of_inv_lt₀ hρ' h4
  have hws_cast : ∀ m (j : Fin a), ws m (Fin.castLE L.a_le j) = -(r m : ℂ) := by
    intro m j
    have hj : (Fin.castLE L.a_le j).val < a := j.2
    simp only [hws, if_pos hj]
  have hws_mem : ∀ m, ws m ∈ logCover L.a_le := by
    intro m
    refine ⟨fun i => ?_, fun k hk => ?_⟩
    · rw [hws_cast]
      simp [hrpos m]
    · have hk' : ¬ k.val < a := not_lt.2 hk
      simp only [hws, if_neg hk']
      simp
  set zs : ℕ → Fin n → ℂ := fun m => expCover a (ws m) with hzs
  have hzs_k : ∀ m k, zs m k = if k.val < a then ((Real.exp (-(r m)) : ℝ) : ℂ) else 0 := by
    intro m k
    simp only [hzs, expCover, hws]
    by_cases hk : k.val < a
    · simp [hk]
    · simp [hk]
  have hzs_ball : ∀ m, zs m ∈ Metric.ball (0 : Fin n → ℂ) ρ' := by
    intro m
    rw [mem_ball_zero_iff, pi_norm_lt_iff hρ']
    intro k
    rw [hzs_k]
    split_ifs
    · rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]; exact hexpr m
    · simpa using hρ'
  have hrtop : Tendsto r atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have hzs_lim : Tendsto zs atTop (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro k
    simp only [hzs_k]
    by_cases hk : k.val < a
    · simp only [hk, if_true]
      have h1 : Tendsto (fun m => Real.exp (-(r m))) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hrtop)
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
      simpa only [Function.comp_def, Complex.ofReal_zero, Pi.zero_apply] using h2
    · simp only [hk, if_false]
      exact tendsto_const_nhds
  have hdiv : ∀ m, (-(r m : ℂ)) / (2 * Real.pi * Complex.I) = tm m := by
    intro m
    rw [div_eq_iff h2pi]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp only [htm]
    push_cast
    field_simp
    simp
  have hC : (∑ j, B j).map (fun x : ℤ => (x : ℂ)) = ∑ j, (B j).map (fun x : ℤ => (x : ℂ)) := by
    ext p q
    simp [Matrix.sum_apply]
  have hdec : ∀ m, tauAt L.a_le T0 B (ws m) =
      T0 (zs m) + tm m • (∑ j, B j).map (fun x : ℤ => (x : ℂ)) := by
    intro m
    have hsum : ∑ j, (ws m (Fin.castLE L.a_le j) / (2 * Real.pi * Complex.I)) •
        (B j).map (fun x : ℤ => (x : ℂ)) = tm m • (∑ j, B j).map (fun x : ℤ => (x : ℂ)) := by
      rw [hC, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hws_cast, hdiv]
    simp only [tauAt]
    rw [hsum]
  have him : Tendsto (fun m => (tm m).im) atTop atTop := by
    have h1 : ∀ m, (tm m).im = r m / (2 * Real.pi) := fun m => by
      simp only [htm, Complex.mul_I_im, Complex.ofReal_re]
    simp only [h1]
    exact hrtop.atTop_div_const (by positivity)
  have hYm : ∀ m, ((tauAt L.a_le T0 B (ws m)).map Complex.im -
      c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef := fun m =>
    h.im_lower _ (Metric.ball_subset_ball hρle (hzs_ball m))
      (fun j => ws m (Fin.castLE L.a_le j)) (fun j => exp_cast L.a_le (ws m) j)
  have hq := tendsto_inv_mulVec h hzs_lim (ht.tendsto.comp hzs_lim)
  have hy' : Tendsto (fun m => (fun k => ((uCo bas x k : ℤ) : ℂ)) +
      tauAt L.a_le T0 B (ws m) *ᵥ (fun k => ((vCo bas x k : ℤ) : ℂ))) atTop
      (𝓝 (((A 0)ᵀ)⁻¹ *ᵥ t 0)) := hq.congr fun m => by
    have := inv_period h hdet (ws m) (hws_mem m) (hzs_ball m) x
    rw [hP _ (hws_mem m)] at this
    exact this
  obtain ⟨u, v, hv, -, hev⟩ := GlobalTheory.T.siegel_limit_imag_bound g (∑ j, B j) (T0 0) (fun m => T0 (zs m))
    (fun m => tauAt L.a_le T0 B (ws m)) tm c (fun _ => uCo bas x) (fun _ => vCo bas x) _ h.c_pos
    (T_tendsto h hzs_lim) him hdec hYm (lower_at_centre h) hy'
  obtain ⟨m, hm⟩ := hev.exists
  have hvx : vCo bas x = v := hm.2
  rw [chartW, LinearMap.mem_ker, LinearMap.comp_apply, hvx, Matrix.mulVecLin_apply]
  exact hv

theorem limit_mem (h : IsChart L bas A T0 B c ρ) (ws : ℕ → Fin n → ℂ) (x : ℕ → Λ) (p : Fin g → ℂ)
    (hws : ∀ k, ws k ∈ logCover L.a_le)
    (hz : Tendsto (fun k => expCover a (ws k)) atTop (𝓝 0))
    (hp : Tendsto (fun k => L.P (ws k) (x k)) atTop (𝓝 p)) :
    ∃ x₀ : chartW bas B, p = chartPer bas A T0 B x₀ := by
  obtain ⟨ρ', hρ', hρle, hdet⟩ := exists_ball_det h
  have hU : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) ρ' := Metric.mem_ball_self hρ'
  have hq := tendsto_inv_mulVec h hz hp
  have key := GlobalTheory.CompanionTheory.PeriodLimit.limit_period n a g L.a_le (Metric.ball 0 ρ') T0 B c
    Metric.isOpen_ball (h.T_cont.mono (Metric.ball_subset_ball (hρle.trans h.ρ_le))) h.B_psd h.c_pos
    (fun z hz => h.im_lower z (Metric.ball_subset_ball hρle hz)) 0 hU (fun _ => 0)
    (fun j hj => (hj rfl).elim) (fun _ _ => rfl) (((A 0)ᵀ)⁻¹ *ᵥ p)
  obtain ⟨u, v, hv, hw⟩ := key (mem_closure_of_tendsto (hz.prodMk_nhds hq) (by
    filter_upwards [hz.eventually (Metric.isOpen_ball.mem_nhds hU)] with k hk
    exact ⟨hk, fun j => ws k (Fin.castLE L.a_le j), uCo bas (x k), vCo bas (x k),
      fun j => exp_cast L.a_le (ws k) j, inv_period h hdet _ (hws k) hk (x k)⟩))
  simp only [zero_div, zero_smul, Finset.sum_const_zero, add_zero] at hw
  have hw' : ((A 0)ᵀ)⁻¹ *ᵥ p = cst u + T0 0 *ᵥ cst v := hw
  refine ⟨⟨mk bas u v, ?_⟩, ?_⟩
  · rw [chartW, LinearMap.mem_ker, LinearMap.comp_apply, vCo_mk, Matrix.mulVecLin_apply,
      Matrix.sum_mulVec]
    exact Finset.sum_eq_zero fun j _ => hv j rfl
  · show p = (A 0)ᵀ *ᵥ (cst (uCo bas (mk bas u v)) + T0 0 *ᵥ cst (vCo bas (mk bas u v)))
    rw [uCo_mk, vCo_mk, ← hw', Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (Ne.isUnit (by rw [det_transpose]; exact h.A_det)),
      Matrix.one_mulVec]

theorem periods_at_centre : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c ρ : ℝ), IsChart L bas A T0 B c ρ → (∀ (x : Λ) (t : (Fin n → ℂ) → Fin g → ℂ), ContinuousAt t 0 → (∀ w ∈ logCover L.a_le, L.P w x = t (expCover a w)) → x ∈ chartW bas B) ∧ ∀ (ws : ℕ → Fin n → ℂ) (x : ℕ → Λ) (p : Fin g → ℂ), (∀ k, ws k ∈ logCover L.a_le) → Tendsto (fun k => expCover a (ws k)) atTop (𝓝 0) → Tendsto (fun k => L.P (ws k) (x k)) atTop (𝓝 p) → ∃ x₀ : chartW bas B, p = chartPer bas A T0 B x₀ :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ h =>
    ⟨fun x t ht hP => extend_mem h x t ht hP, fun ws x p hws hz hp => limit_mem h ws x p hws hz hp⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.CentrePeriods
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MemChartWOfContinuousPeriodStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_chartW_of_continuous_period : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c ρ : ℝ), IsChart L bas A T0 B c ρ → (∀ (x : Λ) (t : (Fin n → ℂ) → Fin g → ℂ), ContinuousAt t 0 → (∀ w ∈ logCover L.a_le, L.P w x = t (expCover a w)) → x ∈ chartW bas B) ∧ ∀ (ws : ℕ → Fin n → ℂ) (x : ℕ → Λ) (p : Fin g → ℂ), (∀ k, ws k ∈ logCover L.a_le) → Tendsto (fun k => expCover a (ws k)) atTop (𝓝 0) → Tendsto (fun k => L.P (ws k) (x k)) atTop (𝓝 p) → ∃ x₀ : chartW bas B, p = chartPer bas A T0 B x₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.CentrePeriods.periods_at_centre | exact GlobalTheory.CompanionTheory.Ar.Cusp.CentrePeriods.periods_at_centre | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.CentrePeriods.periods_at_centre <;> assumption)
end
end
