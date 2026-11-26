module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BinaryHermitianRepresents

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeCoveringOfTraceDualLowerBound
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeCoveringOfTraceDualLowerBound
open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset

namespace GlobalTheory.TraceCover

variable {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]

theorem eq_zero_of_sum_re (a : InfinitePlace K → ℂ)
    (h : ∀ x : K, ∑ w, (w.embedding x * a w).re = 0) : a = 0 := by
  classical
  let F : mixedEmbedding.mixedSpace K →ₗ[ℝ] ℝ :=
    { toFun := fun z => ∑ w : InfinitePlace K, (z.2 ⟨w, IsTotallyComplex.isComplex w⟩ * a w).re
      map_add' := by
        intro x y
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        simp only [Prod.smul_snd, Pi.smul_apply, smul_mul_assoc, Complex.smul_re, smul_eq_mul,
          RingHom.id_apply, Finset.mul_sum] }
  have hF : F = 0 := by
    apply (mixedEmbedding.latticeBasis K).ext
    intro i
    rw [mixedEmbedding.latticeBasis_apply]
    simpa [F] using h _
  funext w
  have := LinearMap.congr_fun hF (0, Pi.single ⟨w, IsTotallyComplex.isComplex w⟩ (starRingEnd ℂ (a w)))
  simp only [F, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply] at this
  rw [Finset.sum_eq_single w] at this
  · rw [Pi.single_eq_same, mul_comm, Complex.mul_conj, Complex.ofReal_re] at this
    simpa using this
  · intro b _ hb
    rw [Pi.single_eq_of_ne (by simpa using hb)]
    simp
  · simp

theorem eq_zero_of_sum_re_lin {ι : Type} [Fintype ι] (g : InfinitePlace K → ((ι → ℂ) →ₗ[ℂ] ℂ))
    (h : ∀ y : ι → K, ∑ w, (g w (fun j => w.embedding (y j))).re = 0) (w : InfinitePlace K) :
    g w = 0 := by
  classical
  apply (Pi.basisFun ℂ ι).ext
  intro i
  have := eq_zero_of_sum_re (fun w => g w (Pi.single i 1)) (by
    intro x
    rw [← h (Pi.single i x)]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← smul_eq_mul, ← map_smul]
    congr 2
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj])
  simpa using congrFun this w

theorem trace_eq_sum (a : K) :
    ((Algebra.trace ℚ K a : ℚ) : ℝ) = ∑ w : InfinitePlace K, 2 * (w.embedding a).re := by
  classical
  have e := congrArg Complex.re (trace_eq_sum_embeddings ℂ (K := ℚ) (L := K) (x := a))
  simp only [eq_ratCast, Complex.ratCast_re, Complex.re_sum] at e
  rw [e, ← (RingHom.equivRatAlgHom (R := K) (S := ℂ)).sum_comp,
    ← Finset.univ.sum_fiberwise (fun φ : K →+* ℂ => InfinitePlace.mk φ)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have : ∀ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => InfinitePlace.mk φ = w),
      ((RingHom.equivRatAlgHom (R := K) (S := ℂ)) φ a).re = (w.embedding a).re := by
    intro φ hφ
    have h1 : InfinitePlace.mk φ = InfinitePlace.mk w.embedding := by
      rw [InfinitePlace.mk_embedding]; simpa using hφ
    rcases InfinitePlace.mk_eq_iff.1 h1 with h2 | h2
    · rw [← h2]; rfl
    · rw [← h2]; simp [RingHom.equivRatAlgHom]
  rw [Finset.sum_congr rfl this, Finset.sum_const, InfinitePlace.card_filter_mk_eq,
    (IsTotallyComplex.isComplex w).mult_eq_two]
  simp


omit [_root_.NumberField.IsTotallyComplex K] in
theorem exists_basis {ι : Type} [Fintype ι] (L : Submodule (𝓞 K) (ι → K)) (hfg : L.FG)
    (hsp : Submodule.span K (L : Set (ι → K)) = ⊤) :
    ∃ (κ : Type) (_ : Fintype κ) (b : Module.Basis κ ℚ (ι → K)),
      ∀ y, y ∈ Submodule.span ℤ (Set.range b) ↔ y ∈ L := by
  classical
  haveI : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.2 hfg
  haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 K) L
  haveI : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  let b0 := Module.Free.chooseBasis ℤ L
  let s : L →ₗ[ℤ] (ι → K) := L.subtype.restrictScalars ℤ
  have hs : Function.Injective s := Subtype.val_injective
  have hli : LinearIndependent ℤ (s ∘ b0) :=
    b0.linearIndependent.map' s (LinearMap.ker_eq_bot.2 hs)
  have hli' : LinearIndependent ℚ (s ∘ b0) := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hli
  have hmem : ∀ y, y ∈ Submodule.span ℤ (Set.range (s ∘ b0)) ↔ y ∈ L := by
    intro y
    rw [Set.range_comp, ← Submodule.map_span, b0.span_eq, Submodule.map_top]
    constructor
    · rintro ⟨z, rfl⟩; exact z.2
    · intro hy; exact ⟨⟨y, hy⟩, rfl⟩
  have hL : ∀ y ∈ L, y ∈ Submodule.span ℚ (Set.range (s ∘ b0)) := fun y hy =>
    Submodule.span_subset_span ℤ ℚ _ ((hmem y).2 hy)
  have htop : ⊤ ≤ Submodule.span ℚ (Set.range (s ∘ b0)) := by
    intro y _
    have hy : y ∈ Submodule.span K (L : Set (ι → K)) := by rw [hsp]; trivial
    have key : ∀ k : K, k • y ∈ Submodule.span ℚ (Set.range (s ∘ b0)) := by
      induction hy using Submodule.span_induction with
      | mem x hx =>
        intro k
        rw [← (integralBasis K).sum_repr k, Finset.sum_smul]
        refine Submodule.sum_mem _ fun i _ => ?_
        rw [smul_assoc]
        refine Submodule.smul_mem _ _ (hL _ ?_)
        rw [integralBasis_apply, algebraMap_smul]
        exact L.smul_mem _ hx
      | zero => intro k; simp
      | add x y _ _ hx hy => intro k; rw [smul_add]; exact Submodule.add_mem _ (hx trivial k) (hy trivial k)
      | smul a x _ hx => intro k; rw [smul_smul]; exact hx trivial _
    simpa using key 1
  refine ⟨_, inferInstance, Module.Basis.mk hli' htop, ?_⟩
  intro y
  rw [Module.Basis.coe_mk]
  exact hmem y


omit [_root_.NumberField.IsTotallyComplex K] in
theorem exists_trace_form {ι : Type} [Fintype ι] (φ : (ι → K) →ₗ[ℚ] ℚ) :
    ∃ f : ι → K, ∀ y, Algebra.trace ℚ K (f ⬝ᵥ y) = φ y := by
  classical
  let D := (Algebra.traceForm ℚ K).toDual (traceForm_nondegenerate ℚ K)
  refine ⟨fun i => D.symm (φ ∘ₗ LinearMap.single ℚ (fun _ => K) i), fun y => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [dotProduct, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [← Finset.univ_sum_single y, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Algebra.traceForm_apply]
  exact LinearMap.BilinForm.apply_toDual_symm_apply _ _

section Main

variable {ι ι' : Type} [Fintype ι] [Fintype ι']

noncomputable def rho (M : InfinitePlace K → ((ι → ℂ) ≃ₗ[ℂ] (ι' → ℂ))) :
    (ι → K) →ₗ[ℚ] PiLp 2 (fun _ : InfinitePlace K × ι' => ℂ) :=
  AddMonoidHom.toRatLinearMap
  { toFun := fun y => WithLp.toLp 2 (fun p => M p.1 (fun j => p.1.embedding (y j)) p.2)
    map_zero' := by
      ext p
      have : (fun j : ι => p.1.embedding ((0 : ι → K) j)) = 0 := by funext j; simp
      simp only [this, map_zero]; rfl
    map_add' := by
      intro x y
      ext p
      have : (fun j : ι => p.1.embedding ((x + y) j)) =
          (fun j => p.1.embedding (x j)) + (fun j => p.1.embedding (y j)) := by funext j; simp
      simp only [this, map_add (f := _)]; rfl }

noncomputable def form (M : InfinitePlace K → ((ι → ℂ) ≃ₗ[ℂ] (ι' → ℂ)))
    (u : PiLp 2 (fun _ : InfinitePlace K × ι' => ℂ)) (w : InfinitePlace K) : (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun z := (fun i => starRingEnd ℂ (u (w, i))) ⬝ᵥ M w z
  map_add' x y := by rw [map_add (f := _), dotProduct_add]
  map_smul' c x := by rw [map_smul, dotProduct_smul]; rfl

omit [_root_.NumberField.IsTotallyComplex K] [Fintype ι] in
theorem inner_rho (M : InfinitePlace K → ((ι → ℂ) ≃ₗ[ℂ] (ι' → ℂ)))
    (u : PiLp 2 (fun _ : InfinitePlace K × ι' => ℂ)) (y : ι → K) :
    inner ℝ (rho M y) u = ∑ w, (form M u w (fun j => w.embedding (y j))).re := by
  rw [real_inner_comm, PiLp.inner_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [form, LinearMap.coe_mk, AddHom.coe_mk, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.inner, mul_comm]
  rfl

omit [_root_.NumberField.IsTotallyComplex K] [Fintype ι] [NumberField K] in
theorem eq_zero_of_form (M : InfinitePlace K → ((ι → ℂ) ≃ₗ[ℂ] (ι' → ℂ)))
    (u : PiLp 2 (fun _ : InfinitePlace K × ι' => ℂ)) (h : ∀ w, form M u w = 0) : u = 0 := by
  classical
  ext ⟨w, i⟩
  have := LinearMap.congr_fun (h w) ((M w).symm (Pi.single i 1))
  simpa [form] using this

theorem finrank_eq (M : InfinitePlace K → ((ι → ℂ) ≃ₗ[ℂ] (ι' → ℂ))) :
    Module.finrank ℝ (PiLp 2 (fun _ : InfinitePlace K × ι' => ℂ)) =
      2 * (Fintype.card (InfinitePlace K) * Fintype.card ι) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
  have h := (M w).finrank_eq
  simp only [Module.finrank_fintype_fun_eq_card] at h
  rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq, Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, h, mul_comm]

theorem finrank_rat : Module.finrank ℚ (ι → K) =
      2 * (Fintype.card (InfinitePlace K) * Fintype.card ι) := by
  rw [Module.finrank_pi_fintype, IsTotallyComplex.finrank,
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero]
  simp; ring

theorem span_rho (M : InfinitePlace K → ((ι → ℂ) ≃ₗ[ℂ] (ι' → ℂ))) {κ : Type}
    (b : Module.Basis κ ℚ (ι → K)) : ⊤ ≤ Submodule.span ℝ (Set.range (rho M ∘ b)) := by
  rw [top_le_iff, ← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
  intro u hu
  apply eq_zero_of_form M
  apply eq_zero_of_sum_re_lin
  intro y
  rw [← inner_rho]
  apply (Submodule.mem_orthogonal _ _).1 hu
  apply Submodule.span_subset_span ℚ ℝ
  rw [Set.range_comp, ← Submodule.map_span, b.span_eq]
  exact ⟨y, trivial, rfl⟩

end Main

theorem cover : ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (ι ι' : Type) [Fintype ι] [Fintype ι'] (L : Submodule (𝓞 K) (ι → K)) (M : InfinitePlace K → ((ι → ℂ) ≃ₗ[ℂ] (ι' → ℂ))) (lam : ℝ), L.FG → Submodule.span K (L : Set (ι → K)) = ⊤ → 0 < lam → (∀ (f : ι → K) (c : InfinitePlace K → ι' → ℂ), f ≠ 0 → (∀ y ∈ L, ∃ m : ℤ, Algebra.trace ℚ K (f ⬝ᵥ y) = m) → (∀ (w : InfinitePlace K) (y : ι → ℂ), (fun i => w.embedding (f i)) ⬝ᵥ y = c w ⬝ᵥ M w y) → lam ^ 2 ≤ ∑ w, ∑ i, ‖c w i‖ ^ 2) → ∀ t : InfinitePlace K → ι' → ℂ, ∃ y ∈ L, Real.sqrt (∑ w, ∑ i, ‖t w i - M w (fun j => w.embedding (y j)) i‖ ^ 2) ≤ (Fintype.card (InfinitePlace K) : ℝ) * (Fintype.card ι : ℝ) / (2 * lam) := by
  intro K _ _ _ ι ι' _ _ L M lam hfg hsp hlam hdual t
  classical
  obtain ⟨κ, _, b, hb⟩ := exists_basis L hfg hsp
  have hcard : Fintype.card κ = Module.finrank ℝ (PiLp 2 (fun _ : InfinitePlace K × ι' => ℂ)) := by
    rw [finrank_eq M, ← finrank_rat, Module.finrank_eq_card_basis b]
  let B := basisOfTopLeSpanOfCardEqFinrank (rho M ∘ b) (span_rho M b) hcard
  have hB : ⇑B = rho M ∘ b := coe_basisOfTopLeSpanOfCardEqFinrank _ _ _
  have hΛ : ∀ x, x ∈ Submodule.span ℤ (Set.range B) ↔ ∃ y ∈ L, rho M y = x := by
    intro x
    have e : Set.range B = ((rho M).restrictScalars ℤ) '' Set.range b := by
      rw [hB, Set.range_comp]; rfl
    rw [e, ← Submodule.map_span, Submodule.mem_map]
    simp only [hb, LinearMap.restrictScalars_apply]
  obtain ⟨l, hl, hle⟩ := GlobalTheory.transferenceCover_holds (PiLp 2 (fun _ : InfinitePlace K × ι' => ℂ))
    (Submodule.span ℤ (Set.range B)) (2 * lam) (by positivity) (by
      intro u hu hint
      have hint' : ∀ y ∈ L, ∃ n : ℤ, inner ℝ (rho M y) u = (n : ℝ) :=
        fun y hy => hint _ ((hΛ _).2 ⟨y, hy, rfl⟩)
      choose m hm using fun k => hint' (b k) ((hb _).1 (Submodule.subset_span ⟨k, rfl⟩))
      obtain ⟨f, hf⟩ := exists_trace_form (b.constr ℚ (fun k => (m k : ℚ)))
      have hφ : ∀ y, ((b.constr ℚ (fun k => (m k : ℚ)) y : ℚ) : ℝ) = inner ℝ (rho M y) u := by
        have : (Algebra.linearMap ℚ ℝ) ∘ₗ b.constr ℚ (fun k => (m k : ℚ)) =
            (((innerₗ _).flip u).restrictScalars ℚ) ∘ₗ rho M := by
          apply b.ext
          intro k
          simp [← hm, real_inner_comm]
        intro y
        simpa [real_inner_comm] using LinearMap.congr_fun this y
      let d : (w : InfinitePlace K) → (ι → ℂ) →ₗ[ℂ] ℂ := fun w =>
        { toFun := fun z => (fun i => w.embedding (f i)) ⬝ᵥ z
          map_add' := fun x y => dotProduct_add _ _ _
          map_smul' := fun c x => by rw [dotProduct_smul]; rfl }
      have hz := eq_zero_of_sum_re_lin (fun w => (2 : ℂ) • d w - form M u w) (by
        intro y
        have h1 := hφ y
        rw [← hf, trace_eq_sum, inner_rho, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h1
        rw [← h1]
        refine Finset.sum_congr rfl fun w _ => ?_
        simp [d, dotProduct])
      have hz' : ∀ w z, (fun i => w.embedding (f i)) ⬝ᵥ z =
          (fun i => starRingEnd ℂ (u (w, i)) / 2) ⬝ᵥ M w z := by
        intro w z
        have h1 := LinearMap.congr_fun (hz w) z
        simp only [d, form, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.coe_mk,
          AddHom.coe_mk, LinearMap.zero_apply, smul_eq_mul, sub_eq_zero] at h1
        have h2 : (fun i => starRingEnd ℂ (u (w, i)) / 2) ⬝ᵥ M w z =
            ((fun i => starRingEnd ℂ (u (w, i))) ⬝ᵥ M w z) / 2 := by
          simp only [dotProduct, Finset.sum_div]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [h2, ← h1]; ring
      have hf0 : f ≠ 0 := by
        rintro rfl
        apply hu
        apply eq_zero_of_form M
        intro w
        have h1 := hz w
        have h2 : d w = 0 := by ext z; simp [d, dotProduct]
        simpa [h2] using h1
      have hl := hdual f (fun w i => starRingEnd ℂ (u (w, i)) / 2) hf0 (by
        intro y hy
        obtain ⟨n, hn⟩ := hint' y hy
        refine ⟨n, ?_⟩
        rw [← hφ, ← hf] at hn
        exact_mod_cast hn) hz'
      have hn : ‖u‖ ^ 2 = 4 * ∑ w, ∑ i, ‖starRingEnd ℂ (u (w, i)) / 2‖ ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type, Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp; ring
      apply le_of_sq_le_sq _ (norm_nonneg _) |>.trans le_rfl
      nlinarith) (WithLp.toLp 2 (fun p => t p.1 p.2))
  obtain ⟨y, hy, rfl⟩ := (hΛ _).1 hl
  refine ⟨y, hy, ?_⟩
  rw [finrank_eq M, PiLp.norm_eq_of_L2, Fintype.sum_prod_type] at hle
  rw [le_div_iff₀ (by positivity)]
  refine le_trans (le_of_eq ?_) (hle.trans (le_of_eq ?_))
  · rfl
  · push_cast; ring

end GlobalTheory.TraceCover
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeCoveringOfTraceDualLowerBoundStatement
open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_covering_of_trace_dual_lower_bound : ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (ι ι' : Type) [Fintype ι] [Fintype ι'] (L : Submodule (𝓞 K) (ι → K)) (M : InfinitePlace K → ((ι → ℂ) ≃ₗ[ℂ] (ι' → ℂ))) (lam : ℝ), L.FG → Submodule.span K (L : Set (ι → K)) = ⊤ → 0 < lam → (∀ (f : ι → K) (c : InfinitePlace K → ι' → ℂ), f ≠ 0 → (∀ y ∈ L, ∃ m : ℤ, Algebra.trace ℚ K (f ⬝ᵥ y) = m) → (∀ (w : InfinitePlace K) (y : ι → ℂ), (fun i => w.embedding (f i)) ⬝ᵥ y = c w ⬝ᵥ M w y) → lam ^ 2 ≤ ∑ w, ∑ i, ‖c w i‖ ^ 2) → ∀ t : InfinitePlace K → ι' → ℂ, ∃ y ∈ L, Real.sqrt (∑ w, ∑ i, ‖t w i - M w (fun j => w.embedding (y j)) i‖ ^ 2) ≤ (Fintype.card (InfinitePlace K) : ℝ) * (Fintype.card ι : ℝ) / (2 * lam) := by
  first | exact @GlobalTheory.TraceCover.cover | exact GlobalTheory.TraceCover.cover | (intros; apply GlobalTheory.TraceCover.cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DifferentSmulMemOfTraceIntegral
open NumberField
namespace GlobalTheory.TraceDualHom

theorem exists_linear_trace_eq (E : Type) [Field E] [NumberField E] (a : ℕ)
    (φ : (Fin a → E) →ₗ[ℚ] ℚ) :
    ∃ l : (Fin a → E) →ₗ[E] E, ∀ x, Algebra.trace ℚ E (l x) = φ x := by
  classical
  have h : ∀ i : Fin a, ∃ t : E, ∀ c : E, Algebra.trace ℚ E (t * c) = φ (Pi.single i c) := by
    intro i
    refine ⟨((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).symm
      (φ ∘ₗ LinearMap.single ℚ (fun _ => E) i), fun c => ?_⟩
    have := LinearMap.BilinForm.apply_toDual_symm_apply (hB := traceForm_nondegenerate ℚ E)
      (φ ∘ₗ LinearMap.single ℚ (fun _ => E) i) c
    exact this
  choose t ht using h
  refine ⟨∑ i, t i • LinearMap.proj i, fun x => ?_⟩
  conv_rhs => rw [← Finset.univ_sum_single x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [ht, map_sum]

theorem different_mul_mem (E : Type) [Field E] [NumberField E] (x : E)
    (hx : ∀ c : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (x * c) = m)
    (δ : 𝓞 E) (hδ : δ ∈ differentIdeal ℤ (𝓞 E)) : ∃ o : 𝓞 E, (o : E) = δ * x := by
  have h1 : (δ : E) ∈ IsLocalization.coeSubmodule E (differentIdeal ℤ (𝓞 E)) :=
    (IsLocalization.mem_coeSubmodule _ _).2 ⟨δ, hδ, rfl⟩
  rw [coeSubmodule_differentIdeal ℤ ℚ, Submodule.mem_div_iff_forall_mul_mem] at h1
  have h2 : x ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_traceDual]
    intro c hc
    obtain ⟨o, rfl⟩ := Submodule.mem_one.1 hc
    obtain ⟨m, hm⟩ := hx o
    exact ⟨m, by simpa using hm.symm⟩
  exact Submodule.mem_one.1 (h1 x h2)

theorem rat_span_eq_top (E : Type) [Field E] [NumberField E] (a : ℕ)
    (A : Submodule (𝓞 E) (Fin a → E)) (hA : Submodule.span E (A : Set (Fin a → E)) = ⊤) :
    Submodule.span ℚ (A : Set (Fin a → E)) = ⊤ := by
  have key : ∀ (e : E), ∀ x ∈ Submodule.span ℚ (A : Set (Fin a → E)),
      e • x ∈ Submodule.span ℚ (A : Set (Fin a → E)) := by
    intro e x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      rw [← (integralBasis E).sum_repr e, Finset.sum_smul]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [smul_assoc]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      rw [integralBasis_apply, algebraMap_smul]
      exact A.smul_mem _ hx
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
    | smul q x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Submodule.span E (A : Set (Fin a → E)) := hA ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => simp
  | add x y _ _ hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)
  | smul e x _ hx => exact key e x (hx trivial)

theorem mem_of_forall_rat_functional (E : Type) [Field E] [NumberField E] (a : ℕ)
    (A : Submodule (𝓞 E) (Fin a → E)) (hfg : A.FG)
    (hA : Submodule.span E (A : Set (Fin a → E)) = ⊤) (z : Fin a → E)
    (hz : ∀ φ : (Fin a → E) →ₗ[ℚ] ℚ, (∀ x ∈ A, ∃ m : ℤ, φ x = m) → ∃ m : ℤ, φ z = m) :
    z ∈ A := by
  haveI : Module.Finite (𝓞 E) A := Module.Finite.iff_fg.2 hfg
  haveI : Module.Finite ℤ A := Module.Finite.trans (𝓞 E) A
  haveI : Module.Free ℤ A := inferInstance
  let b := Module.Free.chooseBasis ℤ A
  let f : A →ₗ[ℤ] (Fin a → E) := A.subtype.restrictScalars ℤ
  have hli : LinearIndependent ℤ (f ∘ b) :=
    b.linearIndependent.map' f (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  have hliQ : LinearIndependent ℚ (f ∘ b) := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hli
  have hsp : ∀ x, x ∈ Submodule.span ℤ (Set.range (f ∘ b)) ↔ x ∈ A := by
    intro x
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top]
    constructor
    · rintro ⟨y, rfl⟩; exact y.2
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
  have htop : ⊤ ≤ Submodule.span ℚ (Set.range (f ∘ b)) := by
    rw [← rat_span_eq_top E a A hA, Submodule.span_le]
    intro x hx
    exact Submodule.span_le_restrictScalars ℤ ℚ _ ((hsp x).2 hx)
  let B := Module.Basis.mk hliQ htop
  have hB : Set.range B = Set.range (f ∘ b) := by simp [B]
  rw [← hsp, ← hB, Module.Basis.mem_span_iff_repr_mem]
  intro i
  obtain ⟨m, hm⟩ := hz (B.coord i) (fun x hx => by
    rw [← hsp, ← hB, Module.Basis.mem_span_iff_repr_mem] at hx
    obtain ⟨m, hm⟩ := hx i
    exact ⟨m, by simpa using hm.symm⟩)
  exact ⟨m, by simpa using hm.symm⟩

theorem different_smul_mem_of_trace_integral : ∀ (E : Type) [Field E] [NumberField E] (a b : ℕ) (A : Submodule (𝓞 E) (Fin a → E)) (Bm : Submodule (𝓞 E) (Fin b → E)), A.FG → Bm.FG → Submodule.span E (A : Set (Fin a → E)) = ⊤ → Submodule.span E (Bm : Set (Fin b → E)) = ⊤ → ∀ ψ : (Fin b → E) →ₗ[E] (Fin a → E), (∀ T : (Fin a → E) →ₗ[E] (Fin b → E), (∀ x ∈ A, T x ∈ Bm) → ∃ m : ℤ, Algebra.trace ℚ E (LinearMap.trace E _ (T ∘ₗ ψ)) = m) → ∀ δ ∈ differentIdeal ℤ (𝓞 E), ∀ y ∈ Bm, δ • ψ y ∈ A := by
  intro E _ _ a b A Bm hA _ hAs _ ψ hψ δ hδ y hy
  refine mem_of_forall_rat_functional E a A hA hAs _ fun φ hφ => ?_
  obtain ⟨l, hl⟩ := exists_linear_trace_eq E a φ
  obtain ⟨m, hm⟩ := hψ (((δ : E) • l).smulRight y) (fun x hx => by
    obtain ⟨o, ho⟩ := different_mul_mem E (l x) (fun c => by
      obtain ⟨m, hm⟩ := hφ (c • x) (A.smul_mem c hx)
      refine ⟨m, ?_⟩
      rw [← hm, ← hl, ← algebraMap_smul E c x, map_smul, smul_eq_mul, mul_comm]) δ hδ
    rw [LinearMap.smulRight_apply, LinearMap.smul_apply, smul_eq_mul, ← ho]
    exact Bm.smul_mem o hy)
  refine ⟨m, ?_⟩
  have e : (((δ : E) • l).smulRight y) ∘ₗ ψ = ((((δ : E) • l) ∘ₗ ψ).smulRight y) := rfl
  rw [e, LinearMap.trace_smulRight] at hm
  rw [← hm, ← hl, ← algebraMap_smul E δ (ψ y), map_smul]
  rfl

end GlobalTheory.TraceDualHom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsTer
namespace GlobalTheory.FiniteSumFlagMeasures

open NumberField

theorem main {K : Type} [Field K] [NumberField K] {b : ℕ}
    (B : Submodule (NumberField.RingOfIntegers K) (Fin b → K))
    (hB : Submodule.span K (↑B : Set (Fin b → K)) = ⊤) (v : Fin b → K) :
    ∃ (d : NumberField.RingOfIntegers K), d ≠ (0 : NumberField.RingOfIntegers K) ∧ d • v ∈ B := by
  have hv : v ∈ Submodule.span K (↑B : Set (Fin b → K)) := by rw [hB]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine B.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact B.smul_mem _ h₁
    · rw [mul_smul]; exact B.smul_mem _ h₂
  | smul c x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨⟨n, m⟩, hnm⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 K)) c
    simp only at hnm
    refine ⟨(m : 𝓞 K) * d, mul_ne_zero (nonZeroDivisors.coe_ne_zero m) hd, ?_⟩
    have key : ((m : 𝓞 K) * d) • (c • x) = n • (d • x) := by
      rw [← algebraMap_smul K ((m : 𝓞 K) * d), ← algebraMap_smul K n, ← algebraMap_smul K d,
        smul_smul, smul_smul, map_mul, ← hnm]
      ring_nf
    rw [key]; exact B.smul_mem _ h

end GlobalTheory.FiniteSumFlagMeasures
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticePairVolumeBounds
open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset
namespace GlobalTheory.HomCover

def toMat {R : Type} {a b : ℕ} (y : Fin b × Fin a → R) : Matrix (Fin b) (Fin a) R :=
  Matrix.of fun i j => y (i, j)

theorem toMat_add {R : Type} [Add R] {a b : ℕ} (y z : Fin b × Fin a → R) :
    toMat (y + z) = toMat y + toMat z := rfl

theorem toMat_smul {S R : Type} [SMul S R] {a b : ℕ} (s : S) (y : Fin b × Fin a → R) :
    toMat (s • y) = s • toMat y := rfl

theorem toMat_entries {R : Type} {a b : ℕ} (φ : Matrix (Fin b) (Fin a) R) :
    toMat (fun p : Fin b × Fin a => φ p.1 p.2) = φ := rfl

theorem dot_eq_trace {R : Type} [CommRing R] {a b : ℕ} (f y : Fin b × Fin a → R) :
    f ⬝ᵥ y = Matrix.trace (toMat y * (toMat f)ᵀ) := by
  simp [dotProduct, Matrix.trace, Matrix.mul_apply, toMat, Fintype.sum_prod_type, mul_comm]

def homLat {K : Type} [Field K] [NumberField K] {a b : ℕ} (A : Submodule (𝓞 K) (Fin a → K))
    (B : Submodule (𝓞 K) (Fin b → K)) : Submodule (𝓞 K) (Fin b × Fin a → K) where
  carrier := {y | ∀ x ∈ A, toMat y *ᵥ x ∈ B}
  add_mem' := fun {y z} hy hz x hx => by
    rw [toMat_add, Matrix.add_mulVec]; exact B.add_mem (hy x hx) (hz x hx)
  zero_mem' := fun x hx => by
    have : toMat (0 : Fin b × Fin a → K) = 0 := rfl
    rw [this, Matrix.zero_mulVec]; exact B.zero_mem
  smul_mem' := fun s y hy x hx => by
    rw [toMat_smul, Matrix.smul_mulVec]; exact B.smul_mem s (hy x hx)

theorem homLat_fg {K : Type} [Field K] [NumberField K] {a b : ℕ}
    (A : Submodule (𝓞 K) (Fin a → K)) (B : Submodule (𝓞 K) (Fin b → K)) (hA : A.FG) (hB : B.FG)
    (hAs : Submodule.span K (A : Set (Fin a → K)) = ⊤) : (homLat A B).FG := by
  obtain ⟨s, rfl⟩ := hA
  let F : (Fin b × Fin a → K) →ₗ[𝓞 K] (s → Fin b → K) :=
    { toFun := fun y x => toMat y *ᵥ x
      map_add' := fun y z => by ext1 x; simp [toMat_add, Matrix.add_mulVec]
      map_smul' := fun c y => by ext1 x; simp [toMat_smul, Matrix.smul_mulVec] }
  have hF : Function.Injective F := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    rw [Submodule.span_span_of_tower] at hAs
    have : Matrix.toLin' (toMat y) = 0 := by
      refine LinearMap.ext_on hAs fun x hx => ?_
      exact congrFun hy ⟨x, hx⟩
    have h0 : toMat y = 0 := by simpa using this
    funext p
    exact congrFun (congrFun h0 p.1) p.2
  refine Submodule.fg_of_fg_map_injective F hF ?_
  have hP : (Submodule.pi Set.univ (fun _ : s => B)).FG := Submodule.fg_pi fun _ => hB
  refine hP.of_le ?_
  rintro _ ⟨y, hy, rfl⟩ x _
  exact hy x (Submodule.subset_span x.2)

theorem exists_smul_mem {K : Type} [Field K] [NumberField K] {b : ℕ}
    (B : Submodule (𝓞 K) (Fin b → K)) (hBs : Submodule.span K (B : Set (Fin b → K)) = ⊤)
    (v : Fin b → K) : ∃ d : 𝓞 K, d ≠ 0 ∧ d • v ∈ B := by
  first
  | exact @_root_.GlobalTheory.FiniteSumFlagMeasures.main
  | exact _root_.GlobalTheory.FiniteSumFlagMeasures.main
  | (apply _root_.GlobalTheory.FiniteSumFlagMeasures.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteSumFlagMeasures.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteSumFlagMeasures.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteSumFlagMeasures.main ..)

theorem homLat_span {K : Type} [Field K] [NumberField K] {a b : ℕ}
    (A : Submodule (𝓞 K) (Fin a → K)) (B : Submodule (𝓞 K) (Fin b → K)) (hA : A.FG)
    (hBs : Submodule.span K (B : Set (Fin b → K)) = ⊤) :
    Submodule.span K (homLat A B : Set (Fin b × Fin a → K)) = ⊤ := by
  classical
  obtain ⟨s, rfl⟩ := hA
  rw [eq_top_iff]
  intro y _
  choose d hd0 hd using fun x : Fin a → K => exists_smul_mem B hBs (toMat y *ᵥ x)
  have hD : ∏ x ∈ s, d x ≠ 0 := Finset.prod_ne_zero_iff.2 fun x _ => hd0 x
  have hmem : (∏ x ∈ s, d x) • y ∈ homLat (Submodule.span (𝓞 K) (s : Set (Fin a → K))) B := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      rw [toMat_smul, Matrix.smul_mulVec, ← Finset.prod_erase_mul s d hx, mul_smul]
      exact B.smul_mem _ (hd x)
    | zero => simp
    | add x z _ _ hx hz => rw [Matrix.mulVec_add]; exact B.add_mem hx hz
    | smul c x _ hx => rw [Matrix.mulVec_smul]; exact B.smul_mem _ hx
  have h1 : algebraMap (𝓞 K) K (∏ x ∈ s, d x) ≠ 0 := by
    rwa [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
  have : y = (algebraMap (𝓞 K) K (∏ x ∈ s, d x))⁻¹ • ((∏ x ∈ s, d x) • y) := by
    rw [← algebraMap_smul K (∏ x ∈ s, d x) y, smul_smul, inv_mul_cancel₀ h1, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

noncomputable def frameEquiv {a b : ℕ} (P : Matrix (Fin b) (Fin b) ℂ) (Q : Matrix (Fin a) (Fin a) ℂ)
    (hP : IsUnit P.det) (hQ : IsUnit Q.det) :
    (Fin b × Fin a → ℂ) ≃ₗ[ℂ] (Fin b × Fin a → ℂ) where
  toFun y p := (P⁻¹ * toMat y * Q) p.1 p.2
  invFun y p := (P * toMat y * Q⁻¹) p.1 p.2
  map_add' y z := by
    funext p; rw [toMat_add, Matrix.mul_add, Matrix.add_mul]; rfl
  map_smul' c y := by
    funext p; rw [toMat_smul, Matrix.mul_smul, Matrix.smul_mul]; rfl
  left_inv y := by
    funext p
    simp only [toMat_entries]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hQ,
      Matrix.mul_nonsing_inv_cancel_left _ _ hP]
    rfl
  right_inv y := by
    funext p
    simp only [toMat_entries]
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ hQ,
      Matrix.nonsing_inv_mul_cancel_left _ _ hP]
    rfl

theorem toMat_frameEquiv {a b : ℕ} (P : Matrix (Fin b) (Fin b) ℂ) (Q : Matrix (Fin a) (Fin a) ℂ)
    (hP : IsUnit P.det) (hQ : IsUnit Q.det) (y : Fin b × Fin a → ℂ) :
    toMat (frameEquiv P Q hP hQ y) = P⁻¹ * toMat y * Q := rfl

theorem dual_coord {a b : ℕ} (P : Matrix (Fin b) (Fin b) ℂ) (Q : Matrix (Fin a) (Fin a) ℂ)
    (hP : IsUnit P.det) (hQ : IsUnit Q.det) (f c : Fin b × Fin a → ℂ)
    (h : ∀ y, f ⬝ᵥ y = c ⬝ᵥ frameEquiv P Q hP hQ y) :
    c = fun p => (Q⁻¹ * (toMat f)ᵀ * P) p.2 p.1 := by
  refine dotProduct_eq _ _ fun z => ?_
  obtain ⟨y, rfl⟩ := (frameEquiv P Q hP hQ).surjective z
  rw [← h, dot_eq_trace, dot_eq_trace, toMat_frameEquiv]
  have : (toMat fun p : Fin b × Fin a => (Q⁻¹ * (toMat f)ᵀ * P) p.2 p.1)ᵀ
      = Q⁻¹ * (toMat f)ᵀ * P := rfl
  rw [this, ← Matrix.mul_assoc, Matrix.trace_mul_comm _ P]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ hQ, Matrix.mul_nonsing_inv_cancel_left _ _ hP]

theorem exists_hom_near :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (a b : ℕ)
      (X : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
      (X' : InfinitePlace K → Matrix (Fin b) (Fin b) ℂ)
      (A : Submodule (𝓞 K) (Fin a → K)) (B : Submodule (𝓞 K) (Fin b → K)) (lo hi : ℝ),
      (∀ w, IsUnit (X w).det) → (∀ w, IsUnit (X' w).det) → A.FG → B.FG →
      Submodule.span K (A : Set (Fin a → K)) = ⊤ →
      Submodule.span K (B : Set (Fin b → K)) = ⊤ → 0 < lo → 0 < hi →
      (∀ N, N ≤ A → N ≠ ⊥ → lo ≤ Formalism.HN.size (Pi.basisFun K (Fin a)) X N) →
      Formalism.HN.largestSize (Pi.basisFun K (Fin b)) X' B ≤ hi →
      ∀ T : InfinitePlace K → Matrix (Fin b) (Fin a) ℂ,
        ∃ φ : Matrix (Fin b) (Fin a) K, (∀ y ∈ A, φ *ᵥ y ∈ B) ∧
          Real.sqrt (∑ w, ∑ i, ∑ j, ‖(T w - (X' w)⁻¹ * φ.map w.embedding * X w) i j‖ ^ 2) ≤
            (a : ℝ) * b * Real.sqrt (Formalism.HN.nPl K) *
              |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HN.nPl K : ℝ))) * hi / (2 * lo) := by
  intro K _ _ _ _ a b X X' A B lo hi hX hX' hA hB hAs hBs hlo hhi hlow hup T
  set rd : ℝ := |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HN.nPl K : ℝ))) with hrd
  have hrd0 : 0 < rd := Real.rpow_pos_of_pos (abs_pos.2 (by exact_mod_cast discr_ne_zero K)) _
  have hn : (Fintype.card (InfinitePlace K) : ℝ) = (Formalism.HN.nPl K : ℝ) := rfl
  have hn0 : (0 : ℝ) < Formalism.HN.nPl K := by
    rw [← hn]; exact_mod_cast Fintype.card_pos
  have hs0 : 0 < Real.sqrt (Formalism.HN.nPl K) := Real.sqrt_pos.2 hn0
  have hss : Real.sqrt (Formalism.HN.nPl K) ^ 2 = Formalism.HN.nPl K := Real.sq_sqrt hn0.le
  obtain ⟨y, hy, hle⟩ := GlobalTheory.T.lattice_covering_of_trace_dual_lower_bound K (Fin b × Fin a) (Fin b × Fin a) (homLat A B)
    (fun w => frameEquiv (X' w) (X w) (hX' w) (hX w)) (Real.sqrt (Formalism.HN.nPl K) * (lo / (rd * hi)))
    (homLat_fg A B hA hB hAs) (homLat_span A B hA hBs) (by positivity)
    (fun f c hf hint hc => by
      have hc' : ∀ w, c w = fun p => ((X w)⁻¹ * ((toMat f)ᵀ).map w.embedding * X' w) p.2 p.1 :=
        fun w => by
          have h := dual_coord (X' w) (X w) (hX' w) (hX w) (fun i => w.embedding (f i)) (c w) (hc w)
          have e : (toMat fun i => w.embedding (f i))ᵀ = ((toMat f)ᵀ).map w.embedding := by
            ext i j; rfl
          rw [e] at h
          exact h
      have h1 : ∃ y ∈ B, (toMat f)ᵀ *ᵥ y ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        have : Matrix.toLin' (toMat f)ᵀ = 0 := LinearMap.ext_on hBs fun x hx => hcon x hx
        have h0 : (toMat f)ᵀ = 0 := by simpa using this
        apply hf
        funext p
        exact congrFun (congrFun h0 p.2) p.1
      have h2 := GlobalTheory.TraceDualHom.different_smul_mem_of_trace_integral K a b A B hA hB hAs hBs
        (Matrix.toLin' (toMat f)ᵀ) (fun S hS => by
          obtain ⟨φ, rfl⟩ := Matrix.toLin'.surjective S
          obtain ⟨m, hm⟩ := hint (fun p => φ p.1 p.2) hS
          refine ⟨m, ?_⟩
          rw [← hm, ← Matrix.toLin'_mul, Matrix.trace_toLin'_eq, dot_eq_trace, toMat_entries])
      have h3 : (Formalism.HN.nPl K : ℝ) * (lo / (rd * hi)) ^ 2 ≤
          ∑ w, ∑ i, ∑ j, ‖((X w)⁻¹ * ((toMat f)ᵀ).map w.embedding * X' w) i j‖ ^ 2 := by
        let ψ := (toMat f)ᵀ
        let φ := Matrix.toLin' ψ
        let A' := B.map (φ.restrictScalars (𝓞 K))
        have hA'fg : A'.FG := hB.map _
        obtain ⟨y, hyB, hy⟩ := h1
        have hA'0 : A' ≠ ⊥ := by
          intro h
          have hy' : φ y ∈ A' := ⟨y, hyB, rfl⟩
          rw [h] at hy'
          exact hy hy'
        have hB0 : B ≠ ⊥ := by
          intro h
          apply hA'0
          simp [A', h]
        have hd : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
        have hleast : lo / rd ≤ Formalism.HN.leastSize (Pi.basisFun K (Fin a)) X A' := by
          refine le_csInf ⟨_, A', le_rfl, hA'0, rfl⟩ ?_
          rintro _ ⟨N, hN, hN0, rfl⟩
          have hNfg : N.FG := Submodule.FG.of_le hA'fg hN
          have hle : differentIdeal ℤ (𝓞 K) • N ≤ A := by
            refine Submodule.smul_le.2 fun δ hδ v hv => ?_
            obtain ⟨z, hz, rfl⟩ := hN hv
            exact h2 δ hδ z hz
          have hspan := Formalism.HN.DualPolygon.twist_span_smul N _ hd
          have hne : differentIdeal ℤ (𝓞 K) • N ≠ ⊥ := by
            intro h
            rw [h] at hspan
            apply hN0
            rw [eq_bot_iff]
            intro v hv
            have hv' : v ∈ Submodule.span K (N : Set (Fin a → K)) :=
              Submodule.subset_span hv
            rw [← hspan] at hv'
            simpa using hv'
          have hsize : Formalism.HN.size (Pi.basisFun K (Fin a)) X
              (differentIdeal ℤ (𝓞 K) • N) =
                Formalism.HN.size (Pi.basisFun K (Fin a)) X N * rd := by
            have hrk : Formalism.HN.rkK (differentIdeal ℤ (𝓞 K) • N) =
                Formalism.HN.rkK N := by
              unfold Formalism.HN.rkK
              rw [hspan]
            have hnorm : (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) =
                |(discr K : ℝ)| := by
              rw [NumberField.absNorm_differentIdeal K (𝓞 K), Nat.cast_natAbs, Int.cast_abs]
            have hj : (Formalism.HN.rkK N : ℝ) ≠ 0 := by
              exact_mod_cast (Formalism.LFunctionChainParameters.slopeLatticeData.rkK_pos hN0).ne'
            unfold Formalism.HN.size rd
            rw [Formalism.LFunctionChainParameters.slopeLatticeData.ht_ideal _ X hX hNfg hd,
              hrk, hnorm, Real.mul_rpow
                (Formalism.LFunctionChainParameters.slopeLatticeData.ht_pos _ X hX hNfg).le
                (pow_nonneg (abs_nonneg (discr K : ℝ)) (Formalism.HN.rkK N)),
              ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
            congr 2
            field_simp [hn0.ne', hj]
          rw [div_le_iff₀ hrd0, ← hsize]
          exact hlow _ hle hne
        have hLpos : 0 < Formalism.HN.largestSize (Pi.basisFun K (Fin b)) X' B := by
          rw [(Formalism.HN.sizeMu K _ _ (Pi.basisFun K (Fin b)) X' hX' B hB hB0).2.2.2.2.1]
          exact Real.exp_pos _
        let opNorm := fun w => Formalism.HN.opNormAt (Pi.basisFun K (Fin b)) X'
          (Pi.basisFun K (Fin a)) X w φ
        have hgeom : lo / (rd * hi) ≤
            (∏ w, opNorm w) ^ ((1 : ℝ) / (Formalism.HN.nPl K : ℝ)) := by
          refine le_trans ?_ (Formalism.HN.sizeIneq K _ _ _ _
            (Pi.basisFun K (Fin b)) X' (Pi.basisFun K (Fin a)) X hX' hX φ B A'
            hB hA'fg le_rfl hA'0)
          rw [← div_div]
          exact div_le_div₀ ((div_pos hlo hrd0).le.trans hleast) hleast hLpos hup
        calc
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) hgeom 2) (Nat.cast_nonneg _)
          _ ≤ _ := _root_.GlobalTheory.DualBound.card_mul_geom_sq_le opNorm
            (fun w => norm_nonneg _)
          _ ≤ _ := by
            refine Finset.sum_le_sum fun w _ => ?_
            have hmatrix : LinearMap.toMatrix (Pi.basisFun K (Fin b)) (Pi.basisFun K (Fin a))
                φ = ψ := by ext i j; simp [φ]
            unfold opNorm Formalism.HN.opNormAt
            rw [hmatrix]
            exact _root_.GlobalTheory.DualBound.opNorm_sq_le_hs _
      rw [mul_pow, hss]
      refine h3.trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [hc' w, Fintype.sum_prod_type, Finset.sum_comm])
    (fun w p => T w p.1 p.2)
  refine ⟨toMat y, hy, ?_⟩
  have e1 : ∑ w, ∑ i, ∑ j, ‖(T w - (X' w)⁻¹ * (toMat y).map w.embedding * X w) i j‖ ^ 2
      = ∑ w, ∑ p : Fin b × Fin a, ‖T w p.1 p.2 -
        frameEquiv (X' w) (X w) (hX' w) (hX w) (fun j => w.embedding (y j)) p‖ ^ 2 := by
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Fintype.sum_prod_type]
    rfl
  rw [e1]
  refine hle.trans (le_of_eq ?_)
  rw [hn, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  push_cast
  set r := Real.sqrt (Formalism.HN.nPl K)
  rw [← hss]
  field_simp

end GlobalTheory.HomCover
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticePairVolumeBoundsStatement
open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset
open GlobalTheory.HomCover in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_pair_volume_bounds :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (a b : ℕ)
      (X : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
      (X' : InfinitePlace K → Matrix (Fin b) (Fin b) ℂ)
      (A : Submodule (𝓞 K) (Fin a → K)) (B : Submodule (𝓞 K) (Fin b → K)) (lo hi : ℝ),
      (∀ w, IsUnit (X w).det) → (∀ w, IsUnit (X' w).det) → A.FG → B.FG →
      Submodule.span K (A : Set (Fin a → K)) = ⊤ →
      Submodule.span K (B : Set (Fin b → K)) = ⊤ → 0 < lo → 0 < hi →
      (∀ N, N ≤ A → N ≠ ⊥ → lo ≤ Formalism.HN.size (Pi.basisFun K (Fin a)) X N) →
      Formalism.HN.largestSize (Pi.basisFun K (Fin b)) X' B ≤ hi →
      ∀ T : InfinitePlace K → Matrix (Fin b) (Fin a) ℂ,
        ∃ φ : Matrix (Fin b) (Fin a) K, (∀ y ∈ A, φ *ᵥ y ∈ B) ∧
          Real.sqrt (∑ w, ∑ i, ∑ j, ‖(T w - (X' w)⁻¹ * φ.map w.embedding * X w) i j‖ ^ 2) ≤
            (a : ℝ) * b * Real.sqrt (Formalism.HN.nPl K) *
              |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HN.nPl K : ℝ))) * hi / (2 * lo) := by
  exact @_root_.GlobalTheory.HomCover.exists_hom_near
end
