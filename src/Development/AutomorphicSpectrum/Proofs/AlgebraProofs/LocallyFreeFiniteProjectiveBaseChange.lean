module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHens

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeFiniteProjectiveBaseChange
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeFiniteProjectiveBaseChange
namespace GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj

open GlobalTheory.CompanionTheory.Ar.Num TensorProduct

variable {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {R : Subalgebra o Ω}
  {E : Type*} [AddCommGroup E] [Module Ω E]

theorem exists_pow_cover {k : ℕ} (f c : Fin k → R) (h : ∑ l, c l * f l = 1) (n : ℕ) :
    ∃ d : Fin k → R, ∑ l, d l * f l ^ n = 1 := by
  have h1 : Ideal.span (Set.range f) = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← h]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)
  have h2 := Ideal.span_pow_eq_top _ h1 n
  rw [← Set.range_comp, Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun] at h2
  exact h2

theorem exists_charts {r : ℕ} {L : Submodule R E} (h : LocFree R r L.toAddSubgroup) :
    ∃ (k : ℕ) (f c : Fin k → R) (B : Fin k → Module.Basis (Fin r) Ω E), ∑ l, c l * f l = 1 ∧
      (∀ l q, ∃ n : ℕ, (f l : Ω) ^ n • B l q ∈ L) ∧
      ∀ l q, ∀ e ∈ L, ∃ n : ℕ, (f l : Ω) ^ n * (B l).repr e q ∈ R := by
  classical
  obtain ⟨-, k, f, c, hf, hc, hs, hb⟩ := h
  choose b hli hsp hiff using hb
  refine ⟨k, fun l => ⟨f l, hf l⟩, fun l => ⟨c l, hc l⟩,
    fun l => Module.Basis.mk (hli l) (hsp l).ge, ?_, ?_, ?_⟩
  · apply Subtype.ext
    simpa using hs
  · intro l q
    rw [Module.Basis.mk_apply]
    refine (hiff l (b l q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, ?_⟩
    · by_cases hq : q' = q
      · subst hq; simp
      · simp [hq]
    · simp [Pi.single_apply]
  · intro l q e he
    obtain ⟨a, ha, rfl⟩ := (hiff l e).1 ⟨0, by simpa using he⟩
    obtain ⟨n, hn⟩ := ha q
    refine ⟨n, ?_⟩
    have : (Module.Basis.mk (hli l) (hsp l).ge).repr (∑ q, a q • b l q) q = a q := by
      have h2 : (∑ q, a q • b l q) = ∑ q, a q • (Module.Basis.mk (hli l) (hsp l).ge) q := by
        simp [Module.Basis.mk_apply]
      rw [h2, Module.Basis.repr_sum_self]
    rw [this]
    exact hn

theorem pow_smul_mem {L : Submodule R E} (f : R) {n m : ℕ} (hnm : n ≤ m) {e : E}
    (h : (f : Ω) ^ n • e ∈ L) : (f : Ω) ^ m • e ∈ L := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hnm
  have := L.smul_mem (f ^ j) h
  rw [pow_add, mul_smul]
  simpa [Subalgebra.smul_def] using this

theorem pow_mul_mem (f : R) {n m : ℕ} (hnm : n ≤ m) {a : Ω}
    (h : (f : Ω) ^ n * a ∈ R) : (f : Ω) ^ m * a ∈ R := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hnm
  rw [pow_add, mul_assoc]
  exact R.mul_mem (R.pow_mem f.2 j) h

theorem expand {k r : ℕ} (f d : Fin k → R) (B : Fin k → Module.Basis (Fin r) Ω E) (M N : ℕ)
    (hd : ∑ l, d l * f l ^ (M + N) = 1) (e : E) :
    ∑ i : Fin k × Fin r, ((d i.1 : Ω) * ((f i.1 : Ω) ^ M * (B i.1).repr e i.2)) •
      ((f i.1 : Ω) ^ N • B i.1 i.2) = e := by
  have hd' : ∑ l, (d l : Ω) * (f l : Ω) ^ (M + N) = 1 := by
    simpa using congrArg Subtype.val hd
  rw [Fintype.sum_prod_type]
  conv_rhs => rw [← one_smul Ω e, ← hd', Finset.sum_smul]
  refine Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← (B l).sum_repr e, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [smul_smul, smul_smul]
  congr 1
  ring

theorem exists_dualBasis {r : ℕ} {L : Submodule R E} (h : LocFree R r L.toAddSubgroup) :
    ∃ (k : ℕ) (φ : Fin k × Fin r → Module.Dual Ω E) (v : Fin k × Fin r → L),
      (∀ i, ∀ e ∈ L, φ i e ∈ R) ∧ ∀ e, ∑ i, φ i e • (v i : E) = e := by
  classical
  obtain ⟨k, f, c, B, hs, h1, h2⟩ := exists_charts h
  choose n hn using h1
  obtain ⟨N, hN⟩ : ∃ N, ∀ l q, n l q ≤ N := by
    obtain ⟨N, hN⟩ := (Set.finite_range fun i : Fin k × Fin r => n i.1 i.2).bddAbove
    exact ⟨N, fun l q => hN ⟨(l, q), rfl⟩⟩
  let v : Fin k × Fin r → L := fun i =>
    ⟨(f i.1 : Ω) ^ N • B i.1 i.2, pow_smul_mem _ (hN _ _) (hn _ _)⟩

  have hspan : ∀ e ∈ L, e ∈ Submodule.span R (Set.range fun i => (v i : E)) := by
    intro e he
    choose m hm using fun l q => h2 l q e he
    obtain ⟨M, hM⟩ := (Set.finite_range fun i : Fin k × Fin r => m i.1 i.2).bddAbove
    obtain ⟨d, hd⟩ := exists_pow_cover f c hs (M + N)
    rw [← expand f d B M N hd e]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hR : (d i.1 : Ω) * ((f i.1 : Ω) ^ M * (B i.1).repr e i.2) ∈ R :=
      R.mul_mem (d i.1).2 (pow_mul_mem _ (hM ⟨i, rfl⟩) (hm _ _))
    exact Submodule.smul_mem _ (⟨_, hR⟩ : R) (Submodule.subset_span ⟨i, rfl⟩)
  choose m hm using fun (i j : Fin k × Fin r) => h2 i.1 i.2 (v j) (v j).2
  obtain ⟨M, hM⟩ := (Set.finite_range fun i : (Fin k × Fin r) × (Fin k × Fin r) =>
    m i.1 i.2).bddAbove
  obtain ⟨d, hd⟩ := exists_pow_cover f c hs (M + N)
  refine ⟨k, fun i => ((d i.1 : Ω) * (f i.1 : Ω) ^ M) • (B i.1).coord i.2, v, ?_, ?_⟩
  · intro i e he
    have he' := hspan e he
    clear he
    induction he' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      have := R.mul_mem (d i.1).2 (pow_mul_mem _ (hM ⟨(i, j), rfl⟩) (hm i j))
      simpa [mul_assoc] using this
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact R.add_mem hx hy
    | smul a x _ hx =>
      rw [Subalgebra.smul_def, map_smul]
      exact R.mul_mem a.2 hx
  · intro e
    simpa [mul_assoc, v] using expand f d B M N hd e

section DualBasis

variable {ι : Type*} [Fintype ι] {L : Submodule R E} (φ : ι → Module.Dual Ω E) (v : ι → L)
  (hφ : ∀ i, ∀ e ∈ L, φ i e ∈ R) (hv : ∀ e, ∑ i, φ i e • (v i : E) = e)

include hφ hv

theorem sum_eq (x : L) : ∑ i, (⟨φ i x, hφ i x x.2⟩ : R) • v i = x := by
  apply Subtype.ext
  simpa [Subalgebra.smul_def] using hv x

theorem finite_projective : Module.Finite R L ∧ Module.Projective R L := by
  classical
  let s : L →ₗ[R] (ι → R) :=
    { toFun := fun x i => ⟨φ i x, hφ i x x.2⟩
      map_add' := fun x y => by ext i; simp
      map_smul' := fun a x => by ext i; simp [Subalgebra.smul_def] }
  let p : (ι → R) →ₗ[R] L := Fintype.linearCombination R v
  have hps : p ∘ₗ s = LinearMap.id := by
    ext1 x
    exact sum_eq φ v hφ hv x
  exact ⟨Module.Finite.of_surjective p fun x => ⟨s x, LinearMap.congr_fun hps x⟩,
    Module.Projective.of_split s p hps⟩

theorem isBaseChange : IsBaseChange Ω L.subtype := by
  let g : E →ₗ[Ω] Ω ⊗[R] L := ∑ i, (φ i).smulRight ((1 : Ω) ⊗ₜ[R] v i)
  have hg : ∀ e, g e = ∑ i, φ i e • ((1 : Ω) ⊗ₜ[R] v i) := by
    intro e
    simp [g]
  refine IsBaseChange.of_equiv (LinearEquiv.ofLinear (L.subtype.liftBaseChange Ω) g ?_ ?_) ?_
  · ext1 e
    simp [hg, hv]
  · ext x
    have : g x = (1 : Ω) ⊗ₜ[R] x := by
      rw [hg]
      conv_rhs => rw [← sum_eq φ v hφ hv x, tmul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [tmul_smul]
      rfl
    simpa using this
  · intro x
    simp

end DualBasis

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E : Type}
    [AddCommGroup E] [Module Ω E] (r : ℕ) (L : Submodule R E), LocFree R r L.toAddSubgroup →
      Module.Finite R L ∧ Module.Projective R L ∧ Module.finrank Ω E = r ∧
        IsBaseChange Ω L.subtype := by
  intro o Ω _ _ _ R E _ _ r L h
  obtain ⟨k, φ, v, hφ, hv⟩ := exists_dualBasis h
  refine ⟨(finite_projective φ v hφ hv).1, (finite_projective φ v hφ hv).2, ?_,
    isBaseChange φ v hφ hv⟩
  obtain ⟨k, f, c, B, hs, -⟩ := exists_charts h
  rcases k with _ | k
  · simp at hs
  · simpa using Module.finrank_eq_card_basis (B 0)

end GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeFiniteProjectiveBaseChangeStatement
open GlobalTheory.CompanionTheory.Ar.Num
alias GlobalTheory.T.locally_free_finite_projective_base_change := GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.main
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BundleDegreeEqSumValuations
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BundleDegreeEqSumValuations
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.DegFormula

theorem finite_det {K : Type} [Field K] (C : ACurve K) {V : Type} [AddCommGroup V] [Module K V]
    {L : C.I → AddSubgroup V} (b₀ : Module.Basis (Fin (Module.finrank K V)) K V)
    (b : C.I → Module.Basis (Fin (Module.finrank K V)) K V) (hL : IsBun C L)
    (h : ∀ i, IsLatOf C i (b i) (L i)) : {i | C.v i (b₀.det (b i)) ≠ 1}.Finite := by
  obtain ⟨c, hc⟩ := hL.2
  refine (hc.union (C.fin _ (b₀.isUnit_det c).ne_zero)).subset fun i hi => ?_
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hn
  refine hi ?_
  rw [← Module.Basis.det_mul_det _ c, map_mul, Inhab.v_det C hn.1 (h i), hn.2, mul_one]

theorem deg_formula : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (n : ℕ)
    (b₀ : Module.Basis (Fin n) K V) (b : C.I → Module.Basis (Fin n) K V), IsBun C L →
    (∀ i, IsLatOf C i (b i) (L i)) → {i | C.v i (b₀.det (b i)) ≠ 1}.Finite ∧
      deg C L = ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i (b₀.det (b i))) := by
  intro K _ C V _ _ _ L n b₀ b hL h
  have hn : n = Module.finrank K V := by
    simpa using (Module.finrank_eq_card_basis b₀).symm
  subst hn
  have hf := finite_det C b₀ b hL h
  refine ⟨hf, ?_⟩
  rw [Inhab.deg_eq C b h]
  have hx : (Module.finBasis K V).det b₀ ≠ 0 := ((Module.finBasis K V).isUnit_det b₀).ne_zero
  have key : ∀ i, (C.w i : ℤ) * WithZero.log (C.v i ((Module.finBasis K V).det (b i))) =
      (C.w i : ℤ) * WithZero.log (C.v i ((Module.finBasis K V).det b₀)) +
        (C.w i : ℤ) * WithZero.log (C.v i (b₀.det (b i))) := by
    intro i
    rw [← Module.Basis.det_mul_det _ b₀, map_mul,
      WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx)
        ((Valuation.ne_zero_iff _).2 (b₀.isUnit_det (b i)).ne_zero), mul_add]
  simp only [key]
  rw [finsum_add_distrib ((C.fin _ hx).subset fun i hi h1 => hi (by simp [h1]))
    (hf.subset fun i hi h1 => hi (by simp [h1])), C.prod _ hx, zero_add]

end GlobalTheory.CompanionTheory.Ar.Crv.DegFormula
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BundleDegreeEqSumValuationsStatement
open GlobalTheory.CompanionTheory.Ar.Crv
alias GlobalTheory.T.bundle_degree_eq_sum_valuations := GlobalTheory.CompanionTheory.Ar.Crv.DegFormula.deg_formula
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MemSpanOverOfMem
namespace GlobalTheory.CompanionTheory.Ar.Num.LocFreeBC

open GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {E : Type*} [AddCommGroup E] [Module Ω E]

theorem smul_mem_spanOver (R : Subalgebra o Ω) (S : Set E) {a : Ω} (ha : a ∈ R) {e : E}
    (he : e ∈ spanOver R S) : a • e ∈ spanOver R S := by
  unfold spanOver at he ⊢
  induction he using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, y, hy, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨a * c, R.mul_mem ha hc, y, hy, by rw [mul_smul]⟩
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem mem_spanOver_of_mem (R : Subalgebra o Ω) {S : Set E} {e : E} (he : e ∈ S) :
    e ∈ spanOver R S :=
  AddSubgroup.subset_closure ⟨1, R.one_mem, e, he, (one_smul _ _).symm⟩

theorem frac_add (R : Subalgebra o Ω) {f a b : Ω} (hf : f ∈ R) (ha : ∃ n : ℕ, f ^ n * a ∈ R)
    (hb : ∃ n : ℕ, f ^ n * b ∈ R) : ∃ n : ℕ, f ^ n * (a + b) ∈ R := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨m, hm⟩ := hb
  refine ⟨n + m, ?_⟩
  have : f ^ (n + m) * (a + b) = f ^ m * (f ^ n * a) + f ^ n * (f ^ m * b) := by ring
  rw [this]
  exact R.add_mem (R.mul_mem (R.pow_mem hf _) hn) (R.mul_mem (R.pow_mem hf _) hm)

theorem loc_add (R : Subalgebra o Ω) (L : AddSubgroup E) (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L)
    {f : Ω} (hf : f ∈ R) {x y : E} (hx : ∃ n : ℕ, f ^ n • x ∈ L) (hy : ∃ n : ℕ, f ^ n • y ∈ L) :
    ∃ n : ℕ, f ^ n • (x + y) ∈ L := by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨m, hm⟩ := hy
  refine ⟨n + m, ?_⟩
  have : f ^ (n + m) • (x + y) = f ^ m • (f ^ n • x) + f ^ n • (f ^ m • y) := by
    rw [smul_add, ← mul_smul, ← mul_smul, ← pow_add, ← pow_add, add_comm m n]
  rw [this]
  exact L.add_mem (hL _ (R.pow_mem hf _) _ hn) (hL _ (R.pow_mem hf _) _ hm)

theorem locFree_baseChange {o Ω Ω₁ : Type} [CommRing o] [Field Ω] [Field Ω₁] [Algebra o Ω]
    [Algebra o Ω₁] [Algebra Ω Ω₁] [IsScalarTower o Ω Ω₁] (R : Subalgebra o Ω)
    (R₁ : Subalgebra o Ω₁) (hR : ∀ a ∈ R, algebraMap Ω Ω₁ a ∈ R₁)
    {E E₁ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω₁ E₁] [Module Ω E₁]
    [IsScalarTower Ω Ω₁ E₁] (bc : E →ₗ[Ω] E₁) (hbc : IsBaseChange Ω₁ bc) (r : ℕ)
    (L : AddSubgroup E) (h : LocFree R r L) :
    LocFree R₁ r (spanOver R₁ (bc '' (L : Set E))) := by
  classical
  obtain ⟨hst, k, f, c, hf, hc, hsum, hloc⟩ := h
  have hst₁ : ∀ a ∈ R₁, ∀ e ∈ spanOver R₁ (bc '' (L : Set E)),
      a • e ∈ spanOver R₁ (bc '' (L : Set E)) := fun a ha e he => smul_mem_spanOver R₁ _ ha he
  refine ⟨hst₁, k, fun l => algebraMap Ω Ω₁ (f l), fun l => algebraMap Ω Ω₁ (c l),
    fun l => hR _ (hf l), fun l => hR _ (hc l), ?_, fun l => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [← map_mul, ← map_sum, hsum, map_one]
  obtain ⟨b, hli, hsp, hb⟩ := hloc l
  beta_reduce
  set F : Ω₁ := algebraMap Ω Ω₁ (f l) with hF
  have hF₁ : F ∈ R₁ := hR _ (hf l)
  let B : Module.Basis (Fin r) Ω E := Module.Basis.mk hli hsp.ge
  let B₁ : Module.Basis (Fin r) Ω₁ E₁ := IsBaseChange.basis B hbc
  have hB₁ : (fun q => bc (b q)) = B₁ := by
    funext q
    simp [B₁, B, IsBaseChange.basis_apply]
  have hB₁' : ∀ q, bc (b q) = B₁ q := fun q => congrFun hB₁ q
  refine ⟨B₁, B₁.linearIndependent, B₁.span_eq, fun e => ⟨?_, ?_⟩⟩
  · have key : ∀ x ∈ spanOver R₁ (bc '' (L : Set E)), ∃ a : Fin r → Ω₁,
        (∀ q, ∃ n : ℕ, F ^ n * a q ∈ R₁) ∧ x = ∑ q, a q • B₁ q := by
      intro x hx
      unfold spanOver at hx
      induction hx using AddSubgroup.closure_induction with
      | mem x hx =>
        obtain ⟨t, ht, _, ⟨y, hy, rfl⟩, rfl⟩ := hx
        obtain ⟨a, ha, rfl⟩ := (hb y).1 ⟨0, by simpa using hy⟩
        refine ⟨fun q => t * algebraMap Ω Ω₁ (a q), fun q => ?_, ?_⟩
        · obtain ⟨n, hn⟩ := ha q
          refine ⟨n, ?_⟩
          have := R₁.mul_mem ht (hR _ hn)
          rw [map_mul, map_pow] at this
          convert this using 1
          rw [hF]; ring
        set_option synthInstance.maxHeartbeats 100000 in
          · simp only [map_sum, map_smul, Finset.smul_sum, hB₁', mul_smul, algebraMap_smul]
      | zero => exact ⟨0, fun q => ⟨0, by simp⟩, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨a', ha', rfl⟩ := hy
        exact ⟨a + a', fun q => frac_add R₁ hF₁ (ha q) (ha' q),
          by simp [add_smul, Finset.sum_add_distrib]⟩
      | neg x _ hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        refine ⟨-a, fun q => ?_, by simp⟩
        obtain ⟨n, hn⟩ := ha q
        exact ⟨n, by simpa using R₁.neg_mem hn⟩
    rintro ⟨n, hn⟩
    by_cases h0 : F = 0
    · exact ⟨B₁.repr e, fun q => ⟨1, by simp [h0]⟩, (B₁.sum_repr e).symm⟩
    obtain ⟨a, ha, hea⟩ := key _ hn
    have hFn : F ^ n ≠ 0 := pow_ne_zero _ h0
    refine ⟨fun q => (F ^ n)⁻¹ * a q, fun q => ?_, ?_⟩
    · obtain ⟨m, hm⟩ := ha q
      refine ⟨m + n, ?_⟩
      convert hm using 1
      rw [pow_add]; field_simp
    · simp only [mul_smul, ← Finset.smul_sum]
      rw [← hea, inv_smul_smul₀ hFn]
  · rintro ⟨a, ha, rfl⟩
    refine Finset.sum_induction _
      (fun x : E₁ => ∃ n : ℕ, F ^ n • x ∈ spanOver R₁ (bc '' (L : Set E)))
      (fun x y hx hy => loc_add R₁ _ hst₁ hF₁ hx hy) ⟨0, by simp⟩ (fun q _ => ?_)
    obtain ⟨m, hm⟩ := (hb (b q)).2 ⟨Pi.single q 1, fun q' => ⟨0, by
      by_cases hq : q' = q
      · subst hq; simp
      · simp [hq]⟩, by simp [Pi.single_apply]⟩
    obtain ⟨n, hn⟩ := ha q
    refine ⟨n + m, ?_⟩
    have h1 : bc (f l ^ m • b q) ∈ spanOver R₁ (bc '' (L : Set E)) :=
      mem_spanOver_of_mem R₁ ⟨_, hm, rfl⟩
    have h2 := hst₁ _ hn _ h1
    rw [map_smul, hB₁', ← algebraMap_smul Ω₁ (f l ^ m), map_pow, ← hF, ← mul_smul] at h2
    rw [← mul_smul]
    convert h2 using 2
    ring

end GlobalTheory.CompanionTheory.Ar.Num.LocFreeBC
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigenProjectorsSplitAction
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigenProjectorsSplitAction
noncomputable section

open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Crv.SplitProj

open GlobalTheory.CompanionTheory.Ar.Crv

theorem exists_sum_tmul {O k : Type} [CommRing O] [Field k] (z : TensorProduct ℤ k O) :
    ∃ (m : ℕ) (c : Fin m → k) (a : Fin m → O), z = ∑ j, c j ⊗ₜ[ℤ] a j := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul c a => exact ⟨1, fun _ => c, fun _ => a, by simp⟩
  | add x y hx hy =>
    obtain ⟨m, c, a, rfl⟩ := hx
    obtain ⟨n, d, b, rfl⟩ := hy
    refine ⟨m + n, Fin.append c d, Fin.append a b, ?_⟩
    simp [Fin.sum_univ_add]

def splitMap {O k S : Type} [CommRing O] [Field k] (χ : S → (O →+* k)) :
    TensorProduct ℤ k O →ₐ[k] (S → k) :=
  Algebra.TensorProduct.lift (Algebra.ofId k (S → k))
    (Pi.algHom ℤ (fun _ : S => k) fun s => (χ s).toIntAlgHom) (fun _ _ => Commute.all _ _)

theorem splitMap_tmul {O k S : Type} [CommRing O] [Field k] (χ : S → (O →+* k)) (c : k) (a : O)
    (t : S) : splitMap χ (c ⊗ₜ[ℤ] a) t = c * χ t a := by
  simp [splitMap, Algebra.ofId_apply]

def actMap {K V O k : Type} [Field K] [AddCommGroup V] [Module K V] [CommRing O] [Field k]
    [Algebra k K] (ρ : O →+* Module.End K V) : TensorProduct ℤ k O →ₐ[ℤ] Module.End K V :=
  Algebra.TensorProduct.lift
    ((algebraMap K (Module.End K V)).comp (algebraMap k K)).toIntAlgHom ρ.toIntAlgHom
    (fun c a => show Commute (algebraMap K (Module.End K V) (algebraMap k K c)) (ρ a) from
      Algebra.commute_algebraMap_left _ _)

theorem actMap_tmul {K V O k : Type} [Field K] [AddCommGroup V] [Module K V] [CommRing O] [Field k]
    [Algebra k K] (ρ : O →+* Module.End K V) (c : k) (a : O) :
    actMap ρ (c ⊗ₜ[ℤ] a) = algebraMap k K c • ρ a := by
  rw [Algebra.smul_def]
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

theorem smul_mem_of_isBun {K : Type} [Field K] (C : ACurve K) {V : Type} [AddCommGroup V]
    [Module K V] {L : C.I → AddSubgroup V} (hL : IsBun C L) (i : C.I) {c : K}
    (hc : C.v i c ≤ 1) {x : V} (hx : x ∈ L i) : c • x ∈ L i := by
  obtain ⟨b, hb⟩ := hL.1 i
  refine (hb _).2 fun q => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
  exact mul_le_one' hc ((hb _).1 hx q)

theorem split_proj : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (L : C.I → AddSubgroup V) (O k S : Type) [CommRing O] [Field k]
    [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ →
    (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ ρ : O →+* Module.End K V, IsBun C L →
    (∀ a, IsHom C L L (ρ a)) →
    ∃ e : S → Module.End K V, (∀ s, IsHom C L L (e s)) ∧
      (∀ s x, e s x ∈ (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a)))) ∧
      (∀ s, ∀ x ∈ (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a))), e s x = x) ∧
      (∀ x, ∑ s, e s x = x) ∧
      ∀ s, ∃ (m : ℕ) (c : Fin m → k) (a : Fin m → O),
        (∀ t, ∑ j, c j * χ t (a j) = if t = s then 1 else 0) ∧
        e s = ∑ j, algebraMap k K (c j) • ρ (a j) := by
  intro K _ C V _ _ _ L O k S _ _ _ _ _ χ hχ hk ρ hL hρ
  have hinj : Function.Injective (splitMap χ) := hχ.1
  have hsurj : Function.Surjective (splitMap χ) := hχ.2
  choose z hz using fun s : S => hsurj (Pi.single s 1)
  choose m c a hza using fun s : S => exists_sum_tmul (z s)
  have he : ∀ s, actMap (k := k) ρ (z s) = ∑ j, algebraMap k K (c s j) • ρ (a s j) := by
    intro s
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hza s, map_sum]
    exact Finset.sum_congr rfl fun j _ => actMap_tmul ρ _ _
  have hcoef : ∀ s t, ∑ j, c s j * χ t (a s j) = if t = s then 1 else 0 := by
    intro s t
    have h := congrFun (hz s) t
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hza s, map_sum, Finset.sum_apply] at h
    simp only [splitMap_tmul] at h
    rw [h, Pi.single_apply]
  have hmul : ∀ s b, ρ b * actMap (k := k) ρ (z s) =
      algebraMap k K (χ s b) • actMap (k := k) ρ (z s) := by
    intro s b
    have h : ((1 : k) ⊗ₜ[ℤ] b) * z s = (χ s b ⊗ₜ[ℤ] (1 : O)) * z s := by
      apply hinj
      rw [map_mul, map_mul, hz s]
      funext t
      simp only [Pi.mul_apply, splitMap_tmul, Pi.single_apply]
      by_cases hts : t = s
      · subst hts; simp
      · simp [hts]
    have h' := congrArg (actMap (k := k) ρ) h
    rw [map_mul, map_mul, actMap_tmul, actMap_tmul] at h'
    simpa using h'
  have hsum : ∑ s, actMap (k := k) ρ (z s) = 1 := by
    have h : ∑ s, z s = 1 := by
      apply hinj
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_one]
      simp only [hz]
      funext t
      simp [Finset.sum_apply, Pi.single_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, h, map_one]
  refine ⟨fun s => actMap (k := k) ρ (z s), ?_, ?_, ?_, ?_, ?_⟩
  · intro s i x hx
    show actMap (k := k) ρ (z s) x ∈ L i
    rw [he s, LinearMap.sum_apply]
    exact sum_mem fun j _ => smul_mem_of_isBun C hL i (hk i _) (hρ _ i x hx)
  · intro s x
    simp only [eig, Submodule.mem_iInf, LinearMap.mem_ker]
    intro b
    have h := congrArg (fun f : Module.End K V => f x) (hmul s b)
    simpa [sub_eq_zero] using h
  · intro s x hx
    simp only [eig, Submodule.mem_iInf, LinearMap.mem_ker] at hx
    have hx' : ∀ b, ρ b x = algebraMap k K (χ s b) • x := fun b => by
      simpa [sub_eq_zero] using hx b
    show actMap (k := k) ρ (z s) x = x
    rw [he s, LinearMap.sum_apply]
    have : ∀ j, (algebraMap k K (c s j) • ρ (a s j)) x =
        algebraMap k K (c s j * χ s (a s j)) • x := fun j => by
      rw [LinearMap.smul_apply, hx', smul_smul, map_mul]
    simp only [this]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.sum_smul, ← map_sum, hcoef s s]
    simp
  · intro x
    have h := congrArg (fun f : Module.End K V => f x) hsum
    simpa [LinearMap.sum_apply] using h
  · intro s
    exact ⟨m s, c s, a s, hcoef s, he s⟩

end GlobalTheory.CompanionTheory.Ar.Crv.SplitProj
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigenProjectorsSplitActionStatement
open GlobalTheory.CompanionTheory.Ar.Crv
alias GlobalTheory.T.eigen_projectors_split_action := GlobalTheory.CompanionTheory.Ar.Crv.SplitProj.split_proj
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderContainsCharacters
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderContainsCharacters
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT.CharExt

variable {R : Type} [CommRing R] {T : Type} [CommGroup T] [Fintype T]
variable (K : Type) [Field K] [Algebra R K]

def dualOrder (A : Subalgebra R (T → R)) : Submodule R (T → K) where
  carrier := {l | ∀ f ∈ A, ∃ r : R, algebraMap R K r = ∑ t, l t * algebraMap R K (f t)}
  add_mem' := by
    rintro a b ha hb f hf
    obtain ⟨r, hr⟩ := ha f hf
    obtain ⟨s, hs⟩ := hb f hf
    exact ⟨r + s, by simp [add_mul, Finset.sum_add_distrib, hr, hs]⟩
  zero_mem' := fun f _ => ⟨0, by simp⟩
  smul_mem' := by
    rintro c a ha f hf
    obtain ⟨r, hr⟩ := ha f hf
    exact ⟨c * r, by simp [map_mul, hr, Finset.mul_sum, Algebra.smul_def, mul_assoc]⟩

variable {K}

def conv (l m : T → K) : T → K := fun t => ∑ x, l x * m (x⁻¹ * t)

lemma sum_conv_mul (l m g : T → K) :
    ∑ t, conv l m t * g t = ∑ x, ∑ y, l x * m y * g (x * y) := by
  simp only [conv, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact Fintype.sum_equiv (Equiv.mulLeft x⁻¹) _ _ (fun t => by simp)

lemma conv_mem {A : Subalgebra R (T → R)} (hc : ∀ f ∈ A, (fun z : T × T => f (z.1 * z.2)) ∈ prodSpan A)
    {l m : T → K} (hl : l ∈ dualOrder K A) (hm : m ∈ dualOrder K A) : conv l m ∈ dualOrder K A := by
  intro f hf
  have key : ∀ g ∈ prodSpan A, ∃ r : R, algebraMap R K r =
      ∑ x, ∑ y, l x * m y * algebraMap R K (g (x, y)) := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hg
      obtain ⟨r, hr⟩ := hl a ha
      obtain ⟨s, hs⟩ := hm b hb
      refine ⟨r * s, ?_⟩
      rw [map_mul, hr, hs, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      simp only [map_mul]; ring
    | zero => exact ⟨0, by simp⟩
    | add g h _ _ hg hh =>
      obtain ⟨r, hr⟩ := hg
      obtain ⟨s, hs⟩ := hh
      refine ⟨r + s, ?_⟩
      simp [hr, hs, mul_add, Finset.sum_add_distrib]
    | smul c g _ hg =>
      obtain ⟨r, hr⟩ := hg
      refine ⟨c * r, ?_⟩
      simp only [map_mul, hr, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      ring
  obtain ⟨r, hr⟩ := key _ (hc f hf)
  refine ⟨r, ?_⟩
  rw [hr, sum_conv_mul l m (fun t => algebraMap R K (f t))]

open Classical in
noncomputable def psi {A : Subalgebra R (T → R)} (d : R) (hd : ∀ f : T → R, d • f ∈ A) :
    Module.Dual R A →ₗ[R] (T → K) := by
  classical
  exact {
    toFun := fun l t => algebraMap R K (l ⟨d • Pi.single t 1, hd _⟩) / algebraMap R K d
    map_add' := by intros; ext; simp [add_div]
    map_smul' := by intros; ext; simp [mul_div_assoc, Algebra.smul_def] }

lemma psi_pair [FaithfulSMul R K] {A : Subalgebra R (T → R)} {d : R} (hd0 : d ≠ 0) (hd : ∀ f : T → R, d • f ∈ A)
    (l : Module.Dual R A) (f : T → R) (hf : f ∈ A) :
    ∑ t, psi (K := K) d hd l t * algebraMap R K (f t) = algebraMap R K (l ⟨f, hf⟩) := by
  classical
  have hdK : algebraMap R K d ≠ 0 := by
    simpa using (FaithfulSMul.algebraMap_injective R K).ne hd0
  have e : d • (⟨f, hf⟩ : A) = ∑ t, f t • (⟨d • Pi.single t 1, hd _⟩ : A) := by
    apply Subtype.ext
    funext s
    simp [Finset.sum_apply, Pi.single_apply, mul_comm]
  have e2 := congrArg (fun a => algebraMap R K (l a)) e
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_smul, map_sum, smul_eq_mul, map_mul] at e2
  simp only [psi, LinearMap.coe_mk, AddHom.coe_mk]
  rw [eq_comm, ← mul_right_inj' hdK, e2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  field_simp

lemma range_psi [FaithfulSMul R K] {A : Subalgebra R (T → R)} {d : R} (hd0 : d ≠ 0) (hd : ∀ f : T → R, d • f ∈ A) :
    LinearMap.range (psi (K := K) d hd) = dualOrder K A := by
  classical
  have hinj := FaithfulSMul.algebraMap_injective R K
  have hdK : algebraMap R K d ≠ 0 := by simpa using hinj.ne hd0
  apply le_antisymm
  · rintro _ ⟨l, rfl⟩ f hf
    exact ⟨l ⟨f, hf⟩, (psi_pair hd0 hd l f hf).symm⟩
  · intro l hl
    choose L hL using fun f : A => hl f.1 f.2
    let L' : Module.Dual R A :=
      { toFun := L
        map_add' := fun a b => hinj (by
          simp [hL, add_mul, mul_add, Finset.sum_add_distrib])
        map_smul' := fun c a => hinj (by
          simp [hL, Finset.mul_sum, mul_left_comm]) }
    refine ⟨L', ?_⟩
    funext t
    simp only [psi, LinearMap.coe_mk, AddHom.coe_mk]
    change algebraMap R K (L _) / _ = _
    rw [hL]
    simp [Pi.single_apply, div_eq_iff hdK, apply_ite (algebraMap R K)]

def pairWith (c : T → K) : (T → K) →ₗ[R] K where
  toFun l := ∑ t, l t * c t
  map_add' := by intros; simp [add_mul, Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.mul_sum, Algebra.smul_def, mul_assoc]

lemma pairWith_conv {c : T → K} (hc : ∀ x y, c (x * y) = c x * c y) (l m : T → K) :
    pairWith (R := R) c (conv l m) = pairWith (R := R) c l * pairWith (R := R) c m := by
  simp only [pairWith, LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_conv_mul, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [hc]; ring

lemma isIntegral_pairWith [FaithfulSMul R K] {A : Subalgebra R (T → R)} (hA : IsHopfOrder A)
    {c : T → K} (hc : ∀ x y, c (x * y) = c x * c y) (hc1 : c 1 = 1)
    {l : T → K} (hl : l ∈ dualOrder K A) : IsIntegral R (pairWith (R := R) c l) := by
  classical
  obtain ⟨d, hd0, hd⟩ := hA.full
  haveI := hA.finite
  haveI := hA.projective
  have hfg : (dualOrder K A).FG := by
    rw [← range_psi hd0 hd]
    rw [← Submodule.map_top]
    exact (Module.Finite.fg_top (R := R) (M := Module.Dual R A)).map _
  let M : Submodule R K := (dualOrder K A).map (pairWith (R := R) c)
  have hone : (1 : K) ∈ M := by
    refine ⟨Pi.single 1 1, ?_, ?_⟩
    · intro f _
      exact ⟨f 1, by simp [Pi.single_apply]⟩
    · simp [pairWith, Pi.single_apply, hc1]
  have hmul : ∀ x ∈ M, ∀ y ∈ M, x * y ∈ M := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ⟨conv a b, conv_mem hA.comul ha hb, pairWith_conv hc a b⟩
  let S : Subalgebra R K := M.toSubalgebra hone (fun x y hx hy => hmul x hx y hy)
  exact IsIntegral.of_mem_of_fg S (by simpa [S] using hfg.map _) _ ⟨l, hl, rfl⟩

end GlobalTheory.CompanionTheory.Ar.BT.CharExt

open GlobalTheory.CompanionTheory.Ar.BT.CharExt

theorem GlobalTheory.CompanionTheory.Ar.BT.char_mem_hopfOrder : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T]
    [IsIntegrallyClosed R] (A : Subalgebra R (T → R)), IsHopfOrder A →
    ∀ χ : T →* Rˣ, (fun t => ((χ t : Rˣ) : R)) ∈ A := by
  intro R _ _ T _ _ _ A hA χ
  classical
  cases nonempty_fintype T
  let K := FractionRing R
  have hinj := IsFractionRing.injective R K
  haveI : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).2 hinj
  obtain ⟨d, hd0, hd⟩ := hA.full
  haveI := hA.finite
  haveI := hA.projective
  obtain ⟨n, p, g, hp, hg, hpg⟩ := Module.Finite.exists_comp_eq_id_of_projective R A
  set c : T → R := fun t => ((χ t : Rˣ) : R) with hcdef
  let cK : T → K := fun t => algebraMap R K (c t)
  have hmul : ∀ x y, cK (x * y) = cK x * cK y := by
    intro x y; simp [cK, c]
  have h1 : cK 1 = 1 := by simp [cK, c]
  let x : A := ⟨d • c, hd c⟩
  have hr : ∀ i : Fin n, ∃ r : R, g x i = d * r := by
    intro i
    let li : Module.Dual R A := (LinearMap.proj i).comp g
    have hl : psi (K := K) d hd li ∈ dualOrder K A := by
      rw [← range_psi hd0 hd]; exact ⟨li, rfl⟩
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 (isIntegral_pairWith hA hmul h1 hl)
    refine ⟨r, hinj ?_⟩
    have := psi_pair (K := K) hd0 hd li (d • c) (hd c)
    change _ = algebraMap R K (li x) at this
    change algebraMap R K (li x) = _
    rw [← this, map_mul, hr]
    simp only [pairWith, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, cK]
    ring
  choose r hr using hr
  have hx : p (g x) = x := by
    have := LinearMap.congr_fun hpg x
    simpa using this
  rw [LinearMap.pi_apply_eq_sum_univ p (g x)] at hx
  simp only [hr, mul_smul, ← Finset.smul_sum] at hx
  have hc : c = ((∑ i, r i • p (fun j => if i = j then 1 else 0) : A) : T → R) := by
    funext t
    have e := congrArg (fun a : A => (a : T → R) t) hx
    apply mul_left_cancel₀ hd0
    exact e.symm
  rw [hc]
  exact Subtype.property _
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderContainsCharactersStatement
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct
alias GlobalTheory.T.hopf_order_contains_characters := GlobalTheory.CompanionTheory.Ar.BT.char_mem_hopfOrder
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsHenselianFlatOverPrime
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsHenselianFlatOverPrime
namespace GlobalTheory.CompanionTheory.CommAlg

theorem exists_flat_henselian_normal_over_prime :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (P : Ideal R) [P.IsPrime],
      ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : HenselianLocalRing R')
        (_ : Algebra R R'), IsIntegrallyClosed R' ∧ Module.Flat R R' ∧
          (IsLocalRing.maximalIdeal R').comap (algebraMap R R') = P := by
  exact @PositivityTheory.HtPt.Htat.hens_normal

end GlobalTheory.CompanionTheory.CommAlg
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsHenselianFlatOverPrimeStatement
alias GlobalTheory.T.exists_henselian_flat_over_prime := GlobalTheory.CompanionTheory.CommAlg.exists_flat_henselian_normal_over_prime
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderTranslationInvariant
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderTranslationInvariant
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT.HopfTranslate

theorem translate_mem_of_isHopfOrder : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (A : Subalgebra R (T → R)),
    IsHopfOrder A → ∀ f ∈ A, ∀ t, (fun h => f (t * h)) ∈ A := by
  intro R _ T _ A hA f hf t
  have key : ∀ g ∈ prodSpan A, (fun h => g (t, h)) ∈ A := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨a, -, b, hb, rfl⟩ := hg
      exact A.smul_mem hb (a t)
    | zero => exact A.zero_mem
    | add x y _ _ hx hy => exact A.add_mem hx hy
    | smul r x _ hx => exact A.smul_mem hx r
  exact key _ (hA.comul f hf)

end GlobalTheory.CompanionTheory.Ar.BT.HopfTranslate
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderTranslationInvariantStatement
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct
alias GlobalTheory.T.hopf_order_translation_invariant := GlobalTheory.CompanionTheory.Ar.BT.HopfTranslate.translate_mem_of_isHopfOrder
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExtensionOrderEqSpan
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExtensionOrderEqSpan
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT.ExtSpan

theorem extOrder_eq_span : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (R' : Type) [CommRing R'] (φ : R →+* R') (A : Subalgebra R (T → R)) (g : T → R'), g ∈ extOrder φ A ↔ g ∈ Submodule.span R' {g : T → R' | ∃ f ∈ A, g = fun t => φ (f t)} := by
  intro R _ T _ R' _ φ A g
  set S : Set (T → R') := {g : T → R' | ∃ f ∈ A, g = fun t => φ (f t)} with hS
  have hmul : ∀ {x y : T → R'}, x ∈ S → y ∈ S → x * y ∈ S := by
    rintro _ _ ⟨f1, hf1, rfl⟩ ⟨f2, hf2, rfl⟩
    exact ⟨f1 * f2, A.mul_mem hf1 hf2, by funext t; simp [map_mul]⟩
  have hone : (1 : T → R') ∈ S := ⟨1, A.one_mem, by funext t; simp⟩
  let M : Submonoid (T → R') := { carrier := S, mul_mem' := hmul, one_mem' := hone }
  have hcl : ((Submonoid.closure S : Submonoid (T → R')) : Set (T → R')) = S :=
    congrArg (fun N : Submonoid (T → R') => (N : Set (T → R'))) (Submonoid.closure_eq M)
  have hspan : Subalgebra.toSubmodule (Algebra.adjoin R' S) = Submodule.span R' S := by
    rw [Algebra.adjoin_eq_span, hcl]
  have hdef : extOrder φ A = Algebra.adjoin R' S := by
    rfl
  rw [hdef, ← Subalgebra.mem_toSubmodule, hspan]

end GlobalTheory.CompanionTheory.Ar.BT.ExtSpan
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExtensionOrderEqSpanStatement
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct
alias GlobalTheory.T.extension_order_eq_span := GlobalTheory.CompanionTheory.Ar.BT.ExtSpan.extOrder_eq_span
end
end
