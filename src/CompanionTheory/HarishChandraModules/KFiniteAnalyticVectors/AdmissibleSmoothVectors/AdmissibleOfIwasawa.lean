module

public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinOfPI
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaAll
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Garding

@[expose] public section

section -- merged from CompanionTheory.HarishChandraModules.BesselParameterIntegrals.InPCommutatorOfInK
namespace CompanionTheory.D.Upq

open Matrix NormedSpace PI.UpqRep
open scoped Matrix.Norms.L2Operator Manifold

section General

variable {m : Type*} [Fintype m] [DecidableEq m] {J : Matrix m m ℂ}

end General

section UJ

variable {n : ℕ} (ε : Fin n → Bool)

theorem isCompact_Kset : IsCompact (Kset ε) := by
  have hcl : IsClosed (Kset ε) := by
    change IsClosed ((Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) ∩
      {u | u * Jm ε = Jm ε * u})
    refine IsClosed.inter ?_ ?_
    · have : (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) =
          {u | star u * u = 1} := by ext u; exact Matrix.mem_unitaryGroup_iff'
      rw [this]
      exact isClosed_eq (continuous_star.matrix_mul continuous_id) continuous_const
    · exact isClosed_eq (continuous_id.matrix_mul continuous_const)
        (continuous_const.matrix_mul continuous_id)
  have hB : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hB.of_isClosed_subset hcl ?_
  rintro u ⟨hu, -⟩ i - j -
  simpa using entry_norm_bound_of_unitary hu i j

theorem isCompact_KG : IsCompact (KG ε : Set (UJ ε)) := by
  have hE := (isClosedEmbeddingMatrix n ε).1
  have : (KG ε : Set (UJ ε)) = (fun g : UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
      Matrix (Fin n) (Fin n) ℂ)) ⁻¹' Kset ε := rfl
  rw [this]
  exact hE.isCompact_preimage (isCompact_Kset ε)

instance compactSpace_KG : CompactSpace (KG ε) :=
  isCompact_iff_compactSpace.1 (isCompact_KG ε)

end UJ

end CompanionTheory.D.Upq
end

section -- merged from CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwasawaDecompositionSecondModel
namespace CompanionTheory.D.gk.admitted

theorem iwasawa_decomposition_second_model : IwaHpk := fun _ _ ε _ _ => iwasawa_decomposition_unitary_group _ ε

end CompanionTheory.D.gk.admitted
end

section -- merged from CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Transfer
open MeasureTheory Matrix
open scoped Kronecker Pointwise

noncomputable section

namespace CompanionTheory.D.gk.admitted

namespace PrismTransfer

section Closure

variable {G : Type} [Group G] {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

def sumRep (ρ : G →* Matrix ι ι ℂ) (ρ' : G →* Matrix ι' ι' ℂ) : G →* Matrix (ι ⊕ ι') (ι ⊕ ι') ℂ where
  toFun x := fromBlocks (ρ x) 0 0 (ρ' x)
  map_one' := by simp
  map_mul' x y := by simp [fromBlocks_multiply]

def tensRep (ρ : G →* Matrix ι ι ℂ) (ρ' : G →* Matrix ι' ι' ℂ) : G →* Matrix (ι × ι') (ι × ι') ℂ where
  toFun x := ρ x ⊗ₖ ρ' x
  map_one' := by simp
  map_mul' x y := by simp [mul_kronecker_mul]

def conjRep (ρ : G →* Matrix ι ι ℂ) : G →* Matrix ι ι ℂ where
  toFun x := (ρ x).map (starRingEnd ℂ)
  map_one' := by simp
  map_mul' x y := by simp [Matrix.map_mul]

variable [TopologicalSpace G] {st : G → G} {S : Set G} {ρ : G →* Matrix ι ι ℂ} {ρ' : G →* Matrix ι' ι' ℂ}

theorem isGood_sum (h : IsGood st S ρ) (h' : IsGood st S ρ') : IsGood st S (sumRep ρ ρ') where
  cont := Continuous.matrix_fromBlocks h.cont continuous_const continuous_const h'.cont
  adj g := by
    change fromBlocks (ρ (st g)) 0 0 (ρ' (st g)) = (fromBlocks (ρ g) 0 0 (ρ' g))ᴴ
    simp [fromBlocks_conjTranspose, h.adj, h'.adj]
  tri := by
    obtain ⟨a, ha, ha'⟩ := h.tri
    obtain ⟨b, hb, hb'⟩ := h'.tri
    refine ⟨Sum.elim (fun i => 2 * a i) (fun j => 2 * b j + 1), ?_, ?_⟩
    · rintro (i | i) (j | j) hij <;> simp only [Sum.elim_inl, Sum.elim_inr] at hij
      · rw [ha (show a i = a j by omega)]
      · omega
      · omega
      · rw [hb (show b i = b j by omega)]
    · intro s hs
      change (fromBlocks (ρ s) 0 0 (ρ' s)).BlockTriangular _
      rintro (i | i) (j | j) hij <;> simp only [Sum.elim_inl, Sum.elim_inr] at hij
      · exact ha' s hs (show a j < a i by omega)
      · rfl
      · rfl
      · exact hb' s hs (show b j < b i by omega)

theorem pair_mono {a b c d : ℕ} (h : a ≤ c) (h' : b ≤ d) : Nat.pair a b ≤ Nat.pair c d := by
  have h1 : Nat.pair a b ≤ Nat.pair c b := by
    rcases h.eq_or_lt with rfl | h
    · exact le_rfl
    · exact (Nat.pair_lt_pair_left b h).le
  have h2 : Nat.pair c b ≤ Nat.pair c d := by
    rcases h'.eq_or_lt with rfl | h'
    · exact le_rfl
    · exact (Nat.pair_lt_pair_right c h').le
  exact h1.trans h2

theorem isGood_tens (h : IsGood st S ρ) (h' : IsGood st S ρ') : IsGood st S (tensRep ρ ρ') where
  cont := by
    refine continuous_matrix fun i j => ?_
    exact (h.cont.matrix_elem i.1 j.1).mul (h'.cont.matrix_elem i.2 j.2)
  adj g := by
    change ρ (st g) ⊗ₖ ρ' (st g) = (ρ g ⊗ₖ ρ' g)ᴴ
    rw [conjTranspose_kronecker, h.adj, h'.adj]
  tri := by
    obtain ⟨a, ha, ha'⟩ := h.tri
    obtain ⟨b, hb, hb'⟩ := h'.tri
    refine ⟨fun p => Nat.pair (a p.1) (b p.2), ?_, ?_⟩
    · intro p q hpq
      obtain ⟨h1, h2⟩ := Nat.pair_eq_pair.1 hpq
      exact Prod.ext (ha h1) (hb h2)
    · intro s hs p q hpq
      change ρ s p.1 q.1 * ρ' s p.2 q.2 = 0
      by_cases h1 : a q.1 < a p.1
      · rw [ha' s hs h1, zero_mul]
      by_cases h2 : b q.2 < b p.2
      · rw [hb' s hs h2, mul_zero]
      exact absurd (pair_mono (not_lt.1 h1) (not_lt.1 h2)) (not_le.2 hpq)

theorem isGood_conj (h : IsGood st S ρ) : IsGood st S (conjRep ρ) where
  cont := by
    refine continuous_matrix fun i j => ?_
    exact Complex.continuous_conj.comp (h.cont.matrix_elem i j)
  adj g := by
    change (ρ (st g)).map (starRingEnd ℂ) = ((ρ g).map (starRingEnd ℂ))ᴴ
    rw [h.adj]
    ext i j
    simp
  tri := by
    obtain ⟨a, ha, ha'⟩ := h.tri
    refine ⟨a, ha, fun s hs i j hij => ?_⟩
    change starRingEnd ℂ (ρ s i j) = 0
    rw [ha' s hs hij, map_zero]

theorem isGood_one : IsGood st S (1 : G →* Matrix Unit Unit ℂ) where
  cont := continuous_const
  adj g := by simp
  tri := ⟨fun _ => 0, fun _ _ _ => rfl, fun _ _ _ _ h => absurd h (lt_irrefl _)⟩

omit [DecidableEq ι] [DecidableEq ι'] in
theorem coef_kronecker (A : Matrix ι ι ℂ) (B : Matrix ι' ι' ℂ) (a b : ι → ℂ) (a' b' : ι' → ℂ) :
    (fun p : ι × ι' => a p.1 * a' p.2) ⬝ᵥ ((A ⊗ₖ B) *ᵥ fun p : ι × ι' => b p.1 * b' p.2) =
      (a ⬝ᵥ (A *ᵥ b)) * (a' ⬝ᵥ (B *ᵥ b')) := by
  have : ((A ⊗ₖ B) *ᵥ fun p : ι × ι' => b p.1 * b' p.2) = fun p => (A *ᵥ b) p.1 * (B *ᵥ b') p.2 := by
    funext p
    simp only [mulVec, dotProduct, Fintype.sum_prod_type, Finset.sum_mul_sum, kroneckerMap_apply]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [this]
  simp only [dotProduct, Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

def coefAlg (st : G → G) (S : Set G) (C : Set G) : StarSubalgebra ℂ C(C, ℂ) where
  carrier := {f | ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (τ : G →* Matrix κ κ ℂ) (a b : κ → ℂ),
    IsGood st S τ ∧ ∀ x : C, f x = a ⬝ᵥ (τ x *ᵥ b)}
  mul_mem' := by
    rintro f g ⟨κ, _, _, τ, a, b, h, hf⟩ ⟨κ', _, _, τ', a', b', h', hg⟩
    refine ⟨κ × κ', inferInstance, inferInstance, tensRep τ τ', fun p => a p.1 * a' p.2,
      fun p => b p.1 * b' p.2, isGood_tens h h', fun x => ?_⟩
    rw [ContinuousMap.mul_apply, hf, hg]
    exact (coef_kronecker _ _ _ _ _ _).symm
  add_mem' := by
    rintro f g ⟨κ, _, _, τ, a, b, h, hf⟩ ⟨κ', _, _, τ', a', b', h', hg⟩
    refine ⟨κ ⊕ κ', inferInstance, inferInstance, sumRep τ τ', Sum.elim a a', Sum.elim b b',
      isGood_sum h h', fun x => ?_⟩
    rw [ContinuousMap.add_apply, hf, hg]
    change _ = Sum.elim a a' ⬝ᵥ (fromBlocks (τ x) 0 0 (τ' x) *ᵥ Sum.elim b b')
    simp [fromBlocks_mulVec, sumElim_dotProduct_sumElim]
  algebraMap_mem' c := by
    refine ⟨Unit, inferInstance, inferInstance, 1, fun _ => c, fun _ => 1, isGood_one, fun x => ?_⟩
    simp [dotProduct]
  star_mem' := by
    rintro f ⟨κ, _, _, τ, a, b, h, hf⟩
    refine ⟨κ, inferInstance, inferInstance, conjRep τ, star a, star b, isGood_conj h, fun x => ?_⟩
    rw [ContinuousMap.star_apply, hf]
    change _ = star a ⬝ᵥ ((τ x).map (starRingEnd ℂ) *ᵥ star b)
    simp [dotProduct, mulVec, mul_comm]

theorem coefAlg_separates (h : IsGood st S ρ) (hi : Function.Injective ρ) (C : Set G) :
    (coefAlg st S C).SeparatesPoints := by
  intro x y hxy
  have : ρ x ≠ ρ y := fun e => hxy (Subtype.ext (hi e))
  obtain ⟨i, j, hij⟩ : ∃ i j, ρ x i j ≠ ρ y i j := by
    by_contra hc
    push Not at hc
    exact this (Matrix.ext hc)
  refine ⟨fun z : C => ρ z i j, ⟨⟨fun z : C => ρ z i j,
    (h.cont.matrix_elem i j).comp continuous_subtype_val⟩, ?_, rfl⟩, hij⟩
  refine ⟨ι, inferInstance, inferInstance, ρ, Pi.single i 1, Pi.single j 1, h, fun z => ?_⟩
  simp

theorem exists_approx (h : IsGood st S ρ) (hi : Function.Injective ρ) {C : Set G} (hC : IsCompact C)
    {Φ : G → ℂ} (hΦ : Continuous Φ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (τ : G →* Matrix κ κ ℂ) (a b : κ → ℂ),
      IsGood st S τ ∧ ∀ x ∈ C, ‖Φ x - a ⬝ᵥ (τ x *ᵥ b)‖ ≤ δ := by
  have : CompactSpace C := isCompact_iff_compactSpace.1 hC
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (coefAlg_separates h hi C)
  let F : C(C, ℂ) := ⟨fun x => Φ x, hΦ.comp continuous_subtype_val⟩
  have hF : F ∈ closure (coefAlg st S C : Set C(C, ℂ)) := by
    have : F ∈ (coefAlg st S C).topologicalClosure := by rw [htop]; trivial
    exact this
  obtain ⟨f, ⟨κ, _, _, τ, a, b, hτ, hf⟩, hd⟩ := Metric.mem_closure_iff.1 hF δ hδ
  refine ⟨κ, inferInstance, inferInstance, τ, a, b, hτ, fun x hx => ?_⟩
  have := (ContinuousMap.dist_apply_le_dist (f := F) (g := f) ⟨x, hx⟩).trans hd.le
  rw [dist_eq_norm, hf] at this
  exact this

end Closure

section Bound

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {K : Subgroup G} [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
  (e : K → ℂ)

structure IsFam (Φ : G → ℂ) (F : List G → G → ℂ) : Prop where
  cont₀ : Continuous Φ
  cont : ∀ l, Continuous (F l)
  nil : ∀ x, F [] x = ∫ k : K, e k * Φ (x * k) ∂μ
  cons : ∀ a l x, F (a :: l) x = ∫ k : K, e k * F l (x * k * a) ∂μ

variable {μ e}

omit [IsTopologicalGroup G] in
theorem integrable_of_cont {V : Type} [NormedAddCommGroup V] [SecondCountableTopology K] {f : K → V}
    (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem IsFam.sub [SecondCountableTopology K] (he : Continuous e) {Φ Φ' : G → ℂ} {F F' : List G → G → ℂ}
    (h : IsFam μ e Φ F) (h' : IsFam μ e Φ' F') :
    IsFam μ e (fun x => Φ x - Φ' x) (fun l x => F l x - F' l x) where
  cont₀ := h.cont₀.sub h'.cont₀
  cont l := (h.cont l).sub (h'.cont l)
  nil x := by
    have h1 := h.cont₀
    have h2 := h'.cont₀
    rw [h.nil, h'.nil, ← integral_sub (integrable_of_cont (by fun_prop)) (integrable_of_cont (by fun_prop))]
    simp only [mul_sub]
  cons a l x := by
    have h1 := h.cont l
    have h2 := h'.cont l
    rw [h.cons, h'.cons, ← integral_sub (integrable_of_cont (by fun_prop)) (integrable_of_cont (by fun_prop))]
    simp only [mul_sub]

omit [IsTopologicalGroup G] in
theorem norm_avg_le [SecondCountableTopology K] (he : Continuous e) {f : K → ℂ} {δ : ℝ} (hf : ∀ k, ‖f k‖ ≤ δ) :
    ‖∫ k, e k * f k ∂μ‖ ≤ (∫ k, ‖e k‖ ∂μ) * δ := by
  rw [← integral_mul_const]
  refine norm_integral_le_of_norm_le (integrable_of_cont (by fun_prop)) (ae_of_all _ fun k => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hf k) (norm_nonneg _)

theorem exists_bound [SecondCountableTopology K] (he : Continuous e) (l : List G) :
    ∀ C : Set G, IsCompact C → ∃ C' : Set G, IsCompact C' ∧ ∀ Φ F, IsFam μ e Φ F → ∀ δ : ℝ,
      (∀ y ∈ C', ‖Φ y‖ ≤ δ) → ∀ x ∈ C, ‖F l x‖ ≤ (∫ k, ‖e k‖ ∂μ) ^ (l.length + 1) * δ := by
  have hK : IsCompact (K : Set G) := isCompact_iff_compactSpace.2 ‹_›
  induction l with
  | nil =>
    intro C hC
    refine ⟨C * (K : Set G), hC.mul hK, fun Φ F h δ hδ x hx => ?_⟩
    rw [h.nil]
    simpa using norm_avg_le (μ := μ) he fun k => hδ _ (Set.mul_mem_mul hx k.2)
  | cons a l ih =>
    intro C hC
    obtain ⟨C', hC', H⟩ := ih (C * (K : Set G) * {a}) ((hC.mul hK).mul isCompact_singleton)
    refine ⟨C', hC', fun Φ F h δ hδ x hx => ?_⟩
    rw [h.cons, List.length_cons, pow_succ', mul_assoc]
    exact norm_avg_le he fun k => H Φ F h δ hδ _ (Set.mul_mem_mul (Set.mul_mem_mul hx k.2) rfl)

omit [IsTopologicalGroup G] in
theorem isFam_rep [SecondCountableTopology K] (he : Continuous e) {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [CompleteSpace V] (τ : G →* Module.End ℂ V) (h1 : ∀ x, Continuous (τ x))
    (h2 : ∀ v, Continuous fun x => τ x v) (E : Module.End ℂ V) (hE : ∀ u, E u = ∫ k : K, e k • τ k u ∂μ)
    (ℓ : V →L[ℂ] ℂ) (u : V) :
    IsFam μ e (fun x => ℓ (τ x u)) (fun l x => ℓ (τ x (word E (l.map τ) u))) := by
  have key : ∀ x w, ℓ (τ x (E w)) = ∫ k : K, e k * ℓ (τ (x * k) w) ∂μ := by
    intro x w
    have hw := h2 w
    have := (ℓ.comp ⟨τ x, h1 x⟩).integral_comp_comm (μ := μ) (φ := fun k : K => e k • τ k w)
      (integrable_of_cont (he.smul (hw.comp continuous_subtype_val)))
    rw [hE]
    refine Eq.trans this.symm ?_
    simp
  refine ⟨ℓ.continuous.comp (h2 u), fun l => ℓ.continuous.comp (h2 _), fun x => key x u, fun a l x => ?_⟩
  simp only [List.map_cons, word_cons, Module.End.mul_apply]
  rw [key]
  simp

end Bound

theorem apply_stdPoly {G V : Type} [AddCommGroup V] [Module ℂ V] (τ : G → Module.End ℂ V) (E : Module.End ℂ V)
    {M : ℕ} (g : Fin M → G) (ℓ : V →ₗ[ℂ] ℂ) (u : V) :
    ℓ (stdPoly E (fun i => τ (g i)) u) = ∑ π : Equiv.Perm (Fin M),
      ((Equiv.Perm.sign π : ℤ) : ℂ) * ℓ (word E ((List.ofFn fun i => g (π i)).map τ) u) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [stdPoly, LinearMap.sum_apply, map_sum, List.map_ofFn, Function.comp_def, Module.End.mul_apply,
    Module.End.intCast_apply, map_zsmul, zsmul_eq_mul]

end PrismTransfer

open PrismTransfer

theorem transfer_holds : Transfer := by
  intro G _ _ _ _ _ K _ _ _ μ _ st S ι₀ _ _ ρ₀ hρ₀ hi e he M g hgood H _ _ _ σ hσ E hE
  have : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  set B : ℝ := ∫ k, ‖e k‖ ∂μ with hB
  choose C hC hbd using fun π : Equiv.Perm (Fin M) =>
    exists_bound (μ := μ) he (List.ofFn fun i => g (π i)) {1} isCompact_singleton
  have hCU : IsCompact (⋃ π, C π) := isCompact_iUnion hC
  let φ : (H →L[ℂ] H) →+* Module.End ℂ H := ContinuousLinearMap.toLinearMapRingHom
  let σ' : G →* Module.End ℂ H := φ.toMonoidHom.comp σ
  ext v
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ) fun ℓ => ?_
  have hF := isFam_rep (μ := μ) he σ' (fun x => (σ x).continuous) hσ (φ E) hE ℓ v
  have hmap : stdPoly E (fun i => σ (g i)) v = stdPoly (φ E) (fun i => σ' (g i)) v := by
    change φ (stdPoly E fun i => σ (g i)) v = _
    rw [map_stdPoly]
    rfl
  rw [hmap]
  have main : ∀ δ : ℝ, 0 < δ → ‖ℓ (stdPoly (φ E) (fun i => σ' (g i)) v)‖ ≤
      (Fintype.card (Equiv.Perm (Fin M)) * B ^ (M + 1)) * δ := by
    intro δ hδ
    obtain ⟨κ, _, _, τ, a, b, hτ, hap⟩ := exists_approx hρ₀ hi hCU hF.cont₀ hδ
    let τ' : G →* Module.End ℂ (κ → ℂ) := (Matrix.toLinAlgEquiv' : Matrix κ κ ℂ ≃ₐ[ℂ] _).toMonoidHom.comp τ
    have hc : ∀ u : κ → ℂ, Continuous fun x => τ x *ᵥ u := fun u => hτ.cont.matrix_mulVec continuous_const
    have hint : ∀ u : κ → ℂ, Integrable (fun k : K => e k • (τ k *ᵥ u)) μ := fun u =>
      integrable_of_cont (he.smul ((hc u).comp continuous_subtype_val))
    let E' : Module.End ℂ (κ → ℂ) :=
      { toFun := fun u => ∫ k : K, e k • (τ k *ᵥ u) ∂μ
        map_add' := fun u w => by
          rw [← integral_add (hint u) (hint w)]
          simp only [mulVec_add, smul_add]
        map_smul' := fun c u => by
          rw [RingHom.id_apply, ← integral_smul]
          simp only [mulVec_smul, smul_comm c] }
    let ℓ' : (κ → ℂ) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (dotProductBilin ℂ ℂ a)
    have hF' := isFam_rep (μ := μ) he τ' (fun x => (τ' x).continuous_of_finiteDimensional) hc E'
      (fun _ => rfl) ℓ' b
    have hz : stdPoly E' (fun i => τ' (g i)) = 0 := hgood κ τ hτ E' fun _ => rfl
    have e1 := apply_stdPoly σ' (φ E) g (ℓ : H →ₗ[ℂ] ℂ) v
    have e2 := apply_stdPoly τ' E' g (ℓ' : (κ → ℂ) →ₗ[ℂ] ℂ) b
    rw [hz, LinearMap.zero_apply, map_zero] at e2
    have e3 : ℓ (stdPoly (φ E) (fun i => σ' (g i)) v) = ∑ π : Equiv.Perm (Fin M),
        ((Equiv.Perm.sign π : ℤ) : ℂ) * (ℓ (word (φ E) ((List.ofFn fun i => g (π i)).map σ') v) -
          ℓ' (word E' ((List.ofFn fun i => g (π i)).map τ') b)) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      exact e1.trans (by rw [← sub_zero (Finset.sum _ _), e2]; rfl)
    rw [e3]
    refine (norm_sum_le _ _).trans ?_
    rw [mul_assoc, ← nsmul_eq_mul, ← Finset.card_univ]
    refine Finset.sum_le_card_nsmul _ _ _ fun π _ => ?_
    have hs : ‖((Equiv.Perm.sign π : ℤ) : ℂ)‖ = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
    rw [norm_mul, hs, one_mul]
    have := hbd π _ _ (hF.sub he hF') δ
      (fun y hy => hap y (Set.mem_iUnion.2 ⟨π, hy⟩)) 1 rfl
    simpa only [map_one, Module.End.one_apply, List.length_ofFn] using this
  rw [← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set D : ℝ := Fintype.card (Equiv.Perm (Fin M)) * B ^ (M + 1)
  have hD : 0 ≤ D := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (integral_nonneg fun _ => norm_nonneg _) _)
  refine (main (ε / (D + 1)) (by positivity)).trans ?_
  rw [zero_add, mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith

end CompanionTheory.D.gk.admitted
end
end

section -- merged from CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.GoodPI
open MeasureTheory Matrix

noncomputable section

namespace CompanionTheory.D.gk.admitted

section Lin

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_common_eigenvector (h : ι → ℕ) (hinj : Function.Injective h) (W : Submodule ℂ (ι → ℂ))
    (hW : W ≠ ⊥) : ∃ w₀ ∈ W, w₀ ≠ 0 ∧ ∀ A : Matrix ι ι ℂ, A.BlockTriangular h → (∀ w ∈ W, A *ᵥ w ∈ W) →
      ∃ c : ℂ, A *ᵥ w₀ = c • w₀ := by
  classical
  have hex : ∃ n : ℕ, ∃ w ∈ W, w ≠ 0 ∧ ∀ i, n ≤ h i → w i = 0 := by
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    refine ⟨Finset.univ.sup h + 1, w, hw, hw0, fun i hi => ?_⟩
    have : h i ≤ Finset.univ.sup h := Finset.le_sup (Finset.mem_univ i)
    omega
  obtain ⟨w₀, hw₀, hne, hz⟩ := Nat.find_spec hex
  have hpos : Nat.find hex ≠ 0 := by
    intro h0
    apply hne
    funext i
    exact hz i (by omega)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  have hmin : ∀ w ∈ W, (∀ i, m ≤ h i → w i = 0) → w = 0 := by
    intro w hw hw'
    by_contra hw0
    exact Nat.find_min hex (show m < Nat.find hex by omega) ⟨w, hw, hw0, hw'⟩
  have hj : ∃ j, h j = m := by
    by_contra hno
    apply hne
    refine hmin w₀ hw₀ fun i hi => hz i ?_
    have : h i ≠ m := fun e => hno ⟨i, e⟩
    omega
  obtain ⟨j, hj⟩ := hj
  refine ⟨w₀, hw₀, hne, fun A hA hAW => ⟨A j j, ?_⟩⟩
  rw [← sub_eq_zero]
  refine hmin _ (W.sub_mem (hAW _ hw₀) (W.smul_mem _ hw₀)) fun i hi => ?_
  have key : (A *ᵥ w₀) i = A i j * w₀ j := by
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_single j (fun k _ hk => ?_) (by simp)
    have hkj : h k ≠ m := fun e => hk (hinj (e.trans hj.symm))
    rcases lt_or_ge (h k) (h i) with h1 | h1
    · rw [hA h1, zero_mul]
    · rw [hz k (by omega), mul_zero]
  rw [Pi.sub_apply, key, Pi.smul_apply, smul_eq_mul]
  by_cases hij : i = j
  · rw [hij, sub_self]
  · have him : h i ≠ m := fun e => hij (hinj (e.trans hj.symm))
    rw [hA (show h j < h i by omega), hz i (by omega)]
    simp

def perp (T : Submodule ℂ (ι → ℂ)) : Submodule ℂ (ι → ℂ) where
  carrier := {y | ∀ x ∈ T, star y ⬝ᵥ x = 0}
  add_mem' := by
    intro a b ha hb x hx
    rw [star_add, add_dotProduct, ha x hx, hb x hx, add_zero]
  zero_mem' := by
    intro x _
    simp
  smul_mem' := by
    intro c a ha x hx
    rw [star_smul, smul_dotProduct, ha x hx, smul_zero]

theorem perp_ne_bot (T : Submodule ℂ (ι → ℂ)) (hT : T ≠ ⊤) : perp T ≠ ⊥ := by
  obtain ⟨f, hf, hle⟩ := T.exists_le_ker_of_lt_top hT.lt_top
  have hfx : ∀ x, f x = (fun i => f (Pi.single i 1)) ⬝ᵥ x := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
    congr 2
    funext j
    simp [Pi.single_apply, eq_comm]
  intro hb
  have hy : (star fun i => f (Pi.single i 1) : ι → ℂ) ∈ perp T := by
    intro x hx
    rw [star_star, ← hfx]
    exact hle hx
  rw [hb, Submodule.mem_bot, star_eq_zero] at hy
  apply hf
  refine LinearMap.ext fun x => ?_
  rw [hfx, hy]
  simp

omit [DecidableEq ι] in
open ComplexOrder in
theorem eq_zero_of_mem_perp {T : Submodule ℂ (ι → ℂ)} {y : ι → ℂ} (h1 : y ∈ T) (h2 : y ∈ perp T) : y = 0 :=
  dotProduct_star_self_eq_zero.1 (h2 y h1)

theorem eq_top_of_minimal {G : Type} (A : G → Matrix ι ι ℂ) (hadj : ∀ g, ∃ g', A g' = (A g)ᴴ)
    (N : Submodule ℂ (ι → ℂ))
    (hN : ∀ W : Submodule ℂ (ι → ℂ), W ≠ ⊥ → (∀ g, ∀ w ∈ W, A g *ᵥ w ∈ W) →
      (∀ U : Submodule ℂ (ι → ℂ), U ≠ ⊥ → (∀ g, ∀ w ∈ U, A g *ᵥ w ∈ U) → U ≤ W → U = W) → W ≤ N) :
    N = ⊤ := by
  set T : Submodule ℂ (ι → ℂ) := sSup {W | (∀ g, ∀ w ∈ W, A g *ᵥ w ∈ W) ∧ W ≤ N} with hT
  have hTN : T ≤ N := sSup_le fun W hW => hW.2
  have hTs : ∀ g, ∀ w ∈ T, A g *ᵥ w ∈ T := by
    intro g
    have : T ≤ T.comap (Matrix.toLin' (A g)) := by
      refine sSup_le fun W hW w hw => ?_
      have hWT : W ≤ T := le_sSup hW
      simpa using hWT (hW.1 g w hw)
    intro w hw
    simpa using this hw
  have hPs : ∀ g, ∀ w ∈ perp T, A g *ᵥ w ∈ perp T := by
    intro g w hw x hx
    obtain ⟨g', hg'⟩ := hadj g
    rw [star_mulVec, ← dotProduct_mulVec, ← hg']
    exact hw _ (hTs g' x hx)
  by_contra hne
  have hTne : T ≠ ⊤ := fun e => hne (top_le_iff.1 (e ▸ hTN))
  obtain ⟨W, ⟨hW0, hWs, hWP⟩, hmin⟩ := (wellFounded_lt (α := Submodule ℂ (ι → ℂ))).has_min
    {W | W ≠ ⊥ ∧ (∀ g, ∀ w ∈ W, A g *ᵥ w ∈ W) ∧ W ≤ perp T} ⟨perp T, perp_ne_bot T hTne, hPs, le_rfl⟩
  have hWN : W ≤ N := hN W hW0 hWs fun U hU0 hUs hUW => by
    by_contra hUne
    exact hmin U ⟨hU0, hUs, hUW.trans hWP⟩ (lt_of_le_of_ne hUW hUne)
  have hWT : W ≤ T := le_sSup ⟨hWs, hWN⟩
  apply hW0
  rw [eq_bot_iff]
  intro y hy
  exact eq_zero_of_mem_perp (hWT hy) (hWP hy)

omit [DecidableEq ι] in
theorem integral_mem_of_forall_mem {X : Type} [MeasurableSpace X] (μ : Measure X) (W : Submodule ℂ (ι → ℂ))
    (f : X → ι → ℂ) (hf : Integrable f μ) (hW : ∀ x, f x ∈ W) : ∫ x, f x ∂μ ∈ W := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  rw [Submodule.mem_dualAnnihilator] at hφ
  have := (LinearMap.toContinuousLinearMap φ).integral_comp_comm hf
  simp only [LinearMap.coe_toContinuousLinearMap'] at this
  rw [← this]
  simp [fun x => hφ _ (hW x)]

end Lin

theorem goodPI_of (hS : SmallPI) : GoodPI := by
  intro G _ _ _ _ _ K _ _ _ μ _ _ st S hKS e d M he hfin hM ι _ _ ρ hρ E hE g
  obtain ⟨φ, hφc, hφ⟩ := hfin
  obtain ⟨h, hinj, htri⟩ := hρ.tri
  rw [← LinearMap.ker_eq_top]
  refine eq_top_of_minimal (fun x => ρ x) (fun x => ⟨st x, hρ.adj x⟩) _ fun W hW0 hWs hmin => ?_
  obtain ⟨w₀, hw₀, hne, heig⟩ := exists_common_eigenvector h hinj W hW0
  have hcont : Continuous fun x : K => ρ x *ᵥ w₀ :=
    (hρ.cont.comp continuous_subtype_val).matrix_mulVec continuous_const
  have hint : ∀ i, Integrable (fun x : K => φ i x • (ρ x *ᵥ w₀)) μ := fun i =>
    ((hφc i).smul hcont).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  set θ : Fin d → ι → ℂ := fun i => ∫ x : K, φ i x • (ρ x *ᵥ w₀) ∂μ with hθ
  set U : Submodule ℂ (ι → ℂ) := Submodule.span ℂ (Set.range fun k : K => ρ k *ᵥ w₀) with hU
  have hUW : U = W := by
    refine hmin U ?_ ?_ ?_
    · intro hb
      have : w₀ ∈ U := Submodule.subset_span ⟨1, by simp⟩
      rw [hb, Submodule.mem_bot] at this
      exact hne this
    · intro x
      have : U ≤ U.comap (Matrix.toLin' (ρ x)) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨k, rfl⟩
        obtain ⟨k', hk', s, hs, hks⟩ := hKS (x * k)
        obtain ⟨c, hc⟩ := heig (ρ s) (htri s hs) (hWs s)
        have e1 : ρ x *ᵥ (ρ k *ᵥ w₀) = c • (ρ k' *ᵥ w₀) := by
          rw [mulVec_mulVec, ← map_mul, hks, map_mul, ← mulVec_mulVec, hc, mulVec_smul]
        show Matrix.toLin' (ρ x) (ρ k *ᵥ w₀) ∈ U
        rw [Matrix.toLin'_apply, e1]
        exact U.smul_mem _ (Submodule.subset_span ⟨⟨k', hk'⟩, rfl⟩)
      intro w hw
      simpa using this hw
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      exact hWs k w₀ hw₀
  set Y : Submodule ℂ (ι → ℂ) := Submodule.span ℂ (Set.range θ) with hY
  have hYW : Y ≤ W := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact integral_mem_of_forall_mem μ W _ (hint i) fun x => W.smul_mem _ (hWs x w₀ hw₀)
  have hEY : W ≤ Y.comap E := by
    rw [← hUW]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    obtain ⟨c, hc⟩ := hφ k
    have e1 : E (ρ k *ᵥ w₀) = ∑ i, c i • θ i := by
      rw [hE, ← integral_mul_right_eq_self _ k⁻¹]
      have : ∀ x : K, e (x * k⁻¹) • (ρ ((x * k⁻¹ : K) : G) *ᵥ (ρ k *ᵥ w₀)) =
          ∑ i, c i • (φ i x • (ρ x *ᵥ w₀)) := by
        intro x
        rw [mulVec_mulVec, ← map_mul, hc, Finset.sum_smul]
        simp [smul_smul]
      simp only [this]
      rw [integral_finsetSum (f := fun i (x : K) => c i • (φ i x • (ρ x *ᵥ w₀))) _
        fun i _ => (hint i).smul (c i)]
      simp only [integral_smul, hθ]
    show E (ρ k *ᵥ w₀) ∈ Y
    rw [e1]
    exact Y.sum_mem fun i _ => Y.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have hrk : Module.finrank ℂ Y ≤ d := by
    have := finrank_range_le_card (R := ℂ) θ
    rwa [Fintype.card_fin] at this
  intro w hw
  exact hS (ι → ℂ) W Y hYW E (fun w hw => hEY hw) M
    (lt_of_le_of_lt (Nat.pow_le_pow_left hrk 2) hM) _ (fun i w hw => by simpa using hWs (g i) w hw) w hw

end CompanionTheory.D.gk.admitted
end
end

section -- merged from CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfFiniteRank
open MeasureTheory Matrix
open scoped ContDiff

noncomputable section

namespace CompanionTheory.D.gk.admitted

open PI.UpqRep

variable {n : ℕ} {ε : Fin n → Bool}

theorem exists_elt {m : Matrix (Fin n) (Fin n) ℂ} (hm : m ∈ UJset ε) : ∃ g : UJ ε, toM g = m := by
  have : m ∈ Set.range (coeMatrixAlt ε) := by rw [range_coeMatrix]; exact hm
  exact this

theorem conjTranspose_mem {m : Matrix (Fin n) (Fin n) ℂ} (hm : m ∈ UJset ε) : mᴴ ∈ UJset ε := by
  have h1 := mul_eq_one_comm.1 (coeMatrix_left_inv ε m hm)
  show mᴴᴴ * Jm ε * mᴴ = Jm ε
  rw [Matrix.conjTranspose_conjTranspose]
  calc m * Jm ε * mᴴ = m * (Jm ε * mᴴ * Jm ε) * Jm ε := by
        simp only [Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]
    _ = Jm ε := by rw [h1, Matrix.one_mul]

theorem Kset_sub {m : Matrix (Fin n) (Fin n) ℂ} (hm : m ∈ Kset ε) : m ∈ UJset ε := by
  have h1 : mᴴ * m = 1 := Matrix.mem_unitaryGroup_iff'.1 hm.1
  show mᴴ * Jm ε * m = Jm ε
  rw [Matrix.mul_assoc, ← hm.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem continuous_toM : Continuous (toM : UJ ε → Matrix (Fin n) (Fin n) ℂ) := continuous_coeMatrix ε

def homUJ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) : UJ ε →* (H →L[ℂ] H) where
  toFun g := σ (toM g)
  map_one' := hσ.1.1
  map_mul' a b := hσ.1.2 _ a.2 _ b.2

def stdU (ε : Fin n → Bool) {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    UJ ε →* Matrix (Fin n) (Fin n) ℂ where
  toFun g := Uᴴ * toM g * U
  map_one' := by
    have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
    show Uᴴ * 1 * U = 1
    rw [Matrix.mul_one, h1]
  map_mul' a b := by
    have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
    show Uᴴ * (toM a * toM b) * U = _
    calc Uᴴ * (toM a * toM b) * U = Uᴴ * toM a * (U * Uᴴ) * toM b * U := by
          rw [h1]; simp only [Matrix.mul_assoc, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem admissible_of_finite_rank (h1 : FinOfPI) (h2 : GoodPI) (h3 : Transfer) (h4 : ExistsAvg) (h5 : Iwa ε) : AdmUJ ε := by
  intro H _ _ _ σ hσ hirr S _ hS v hv
  obtain ⟨U, hU, hiwa⟩ := h5
  let μ : Measure (KG ε) := (Measure.haar : Measure (KG ε)).inv
  have hμ : IsFiniteMeasure μ := CompactSpace.isFiniteMeasure
  have hsc : SecondCountableTopology (KG ε) := TopologicalSpace.Subtype.secondCountableTopology _
  have hiso : ∀ g u, ‖homUJ hσ g u‖ = ‖u‖ := fun g u => hσ.2.1 _ g.2 u
  have hc : ∀ u, Continuous fun g => homUJ hσ g u := fun u =>
    (hσ.2.2 u).comp_continuous continuous_toM fun g => g.2
  obtain ⟨e, E, he, hfin, hE, hEv⟩ := h4 (KG ε) μ H ((homUJ hσ).comp (KG ε).subtype) (fun k u => hiso k u)
    (fun u => (hc u).comp continuous_subtype_val) S (fun k u hu => hS _ k.2 u hu) v hv
  choose st hst using fun g : UJ ε => exists_elt (conjTranspose_mem (m := toM g) g.2)
  let Tr : Set (UJ ε) := {s | (stdU ε hU s).BlockTriangular id}
  have hgood : IsGood st Tr (stdU ε hU) := by
    refine ⟨(continuous_const.matrix_mul continuous_toM).matrix_mul continuous_const, fun g => ?_,
      Fin.val, Fin.val_injective, fun s hs i j hij => hs hij⟩
    show Uᴴ * toM (st g) * U = (Uᴴ * toM g * U)ᴴ
    rw [hst]
    simp [Matrix.mul_assoc]
  have hinj : Function.Injective (stdU ε hU) := by
    intro a b hab
    have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
    have key : ∀ g : UJ ε, U * stdU ε hU g * Uᴴ = toM g := fun g => by
      show U * (Uᴴ * toM g * U) * Uᴴ = _
      calc U * (Uᴴ * toM g * U) * Uᴴ = (U * Uᴴ) * toM g * (U * Uᴴ) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [h1, Matrix.one_mul, Matrix.mul_one]
    exact injective_coeMatrix ε ((key a).symm.trans (hab ▸ key b))
  have hKS : ∀ g : UJ ε, ∃ k ∈ KG ε, ∃ s ∈ Tr, g = k * s := by
    intro g
    obtain ⟨k, hk, s, hs, hg, ht⟩ := hiwa (toM g) g.2
    obtain ⟨k, rfl⟩ := exists_elt (Kset_sub hk)
    obtain ⟨s, rfl⟩ := exists_elt hs
    exact ⟨k, hk, s, ht, injective_coeMatrix ε hg⟩
  have hPI : ∀ g : Fin (Module.finrank ℂ S ^ 2 + 1) → UJ ε, stdPoly E (fun i => homUJ hσ (g i)) = 0 := fun g =>
    h3 (UJ ε) (KG ε) μ st Tr (Fin n) (stdU ε hU) hgood hinj e he _ g
      (fun ι _ _ ρ hρ E' hE' => h2 (UJ ε) (KG ε) μ st Tr hKS e _ _ he hfin (Nat.lt_succ_self _) ι ρ hρ E' hE' g)
      H (homUJ hσ) hc E hE
  obtain ⟨hfd, hrk⟩ := h1 (UJ ε) H (homUJ hσ) hiso (fun S' hcl hS' => hirr S' hcl fun g hg u hu => by
    obtain ⟨g, rfl⟩ := exists_elt hg
    exact hS' g u hu) E _ hPI
  refine ⟨_, hfd, hrk, ⟨v, hEv⟩, ?_⟩
  rintro T hT _ ⟨u, rfl⟩
  refine ⟨T u, ?_⟩
  show E (T u) = T (E u)
  rw [hE, hE, ← T.integral_comp_comm]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    show e k • σ (toMK k) (T u) = T (e k • σ (toMK k) u)
    rw [map_smul, hT _ k.2]
  · exact (he.smul ((hc u).comp continuous_subtype_val)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem smooth_of_adm (hA : AdmUJ ε) (hG : GardingFin) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    (hirr : IsIrredOn (UJset ε) σ) {v : H} (hv : IsKFin ε σ v) : SmoothOnH (Jm ε) fun g => σ g v := by
  obtain ⟨S, _, hvS, hS⟩ := hv
  obtain ⟨Y, _, -, hvY, hY⟩ := hA H σ hσ hirr S hS v hvS
  exact hG n ε H σ hσ Y hY v hvY

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem smoothOnH_conj {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {A B P : Matrix (Fin n) (Fin n) ℂ}
    (hP : IsUnit P) (hAB : Pᴴ * A * P = B) {f : Matrix (Fin n) (Fin n) ℂ → E}
    (h : SmoothOnH A fun g => f (P⁻¹ * g * P)) : SmoothOnH B f := by
  have hd := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hd
  have hmem : ∀ g, inUH B g → inUH A (P * g * P⁻¹) := by
    intro g hg
    unfold inUH at hg ⊢
    have h3 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    calc (P * g * P⁻¹)ᴴ * A * (P * g * P⁻¹) = (P⁻¹)ᴴ * (gᴴ * (Pᴴ * A * P) * g) * P⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = ((P⁻¹)ᴴ * Pᴴ) * A * (P * P⁻¹) := by rw [hAB, hg, ← hAB]; simp only [Matrix.mul_assoc]
      _ = A := by rw [h3, h1, Matrix.one_mul, Matrix.mul_one]
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun g => P * g * P⁻¹
      map_add' := fun a b => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c a => by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }
  have hL : ContDiff ℝ ∞ fun g : Matrix (Fin n) (Fin n) ℂ => P * g * P⁻¹ := (LinearMap.toContinuousLinearMap L).contDiff
  intro g₀ hg₀
  obtain ⟨V, F, hV, hgV, hF, hfF⟩ := h _ (hmem g₀ hg₀)
  refine ⟨(fun g => P * g * P⁻¹) ⁻¹' V, fun g => F (P * g * P⁻¹), hV.preimage hL.continuous, hgV,
    hF.comp hL.contDiffOn fun g hg => hg, fun g hg hgB => ?_⟩
  refine Eq.trans ?_ (hfF _ hg (hmem g hgB))
  show f g = f (P⁻¹ * (P * g * P⁻¹) * P)
  congr 1
  calc g = (P⁻¹ * P) * g * (P⁻¹ * P) := by rw [h2, Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem kFinSmooth_of (h1 : FinOfPI) (h2 : GoodPI) (h3 : Transfer) (h4 : ExistsAvg) (h5 : IwaHpk) (h6 : GardingFin) :
    PI.KFinSmooth := by
  intro k r ε lam H _ _ _ σ _ hσ v hv
  obtain ⟨P, hP, hDS⟩ := hσ
  obtain ⟨S, hSf, hvS, hS⟩ := hv
  have hPP : Pᴴ * P = 1 := Matrix.mem_unitaryGroup_iff'.1 hP.2
  have hPP' : P * Pᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hP.2
  have hinv : P⁻¹ = Pᴴ := Matrix.inv_eq_left_inv hPP
  refine smoothOnH_conj hP.1.1 hP.1.2 (smooth_of_adm (admissible_of_finite_rank h1 h2 h3 h4 (h5 k r ε P hP)) h6
    (σ := fun g => σ (P⁻¹ * g * P)) hDS.2.2.1 hDS.2.2.2.1 ⟨S, hSf, hvS, fun g hg x hx => hS _ ⟨?_, ?_⟩ x hx⟩)
  · have hg' : gᴴ * Jm ε * g = Jm ε := Kset_sub hg
    show (P⁻¹ * g * P)ᴴ * Hpk k r * (P⁻¹ * g * P) = Hpk k r
    rw [hinv, ← hP.1.2]
    calc (Pᴴ * g * P)ᴴ * (Pᴴ * Jm ε * P) * (Pᴴ * g * P) = Pᴴ * (gᴴ * (P * Pᴴ) * Jm ε * (P * Pᴴ) * g) * P := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = _ := by rw [hPP', Matrix.mul_one, Matrix.mul_one, hg']
  · rw [hinv]
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (Unitary.star_mem hP.2) hg.1) hP.2

end CompanionTheory.D.gk.admitted
end
end

section -- merged from CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.ExistsAvg
open MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.gk.admitted

section

variable {K : Type} [Group K] [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {μ : Measure K} [IsFiniteMeasure μ]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : K →* (H →L[ℂ] H)}

theorem integrable_cont {F : Type} [NormedAddCommGroup F] {f : K → F} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem exists_avg (hiso : ∀ g v, ‖σ g v‖ = ‖v‖) (hc : ∀ v, Continuous fun x => σ x v) {e : K → ℂ}
    (he : Continuous e) : ∃ E : H →L[ℂ] H, ∀ u, E u = ∫ k, e k • σ k u ∂μ := by
  let L : H →ₗ[ℂ] H :=
    { toFun := fun u => ∫ k, e k • σ k u ∂μ
      map_add' := fun u w => by
        simp only [map_add (f := _), smul_add]
        exact integral_add (integrable_cont (he.smul (hc u))) (integrable_cont (he.smul (hc w)))
      map_smul' := fun c u => by
        simp only [map_smul, RingHom.id_apply, smul_comm _ c]
        exact integral_smul _ _ }
  refine ⟨L.mkContinuous (∫ k, ‖e k‖ ∂μ) fun u => ?_, fun u => rfl⟩
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp only [norm_smul, hiso]
  exact integral_mul_const _ _

end

theorem exists_averaging_operator : ExistsAvg := by
  intro K _ _ _ _ _ _ _ _ μ _ _ H _ _ _ σ hiso hc S _ hS v hv
  have hcoef : ∀ a b : H, Continuous fun x => ⟪σ x a, b⟫_ℂ := fun a b => (hc a).inner continuous_const
  have hint : ∀ b : H, Integrable (fun x => ⟪σ x v, b⟫_ℂ • σ x v) μ := fun b =>
    integrable_cont ((hcoef v b).smul (hc v))
  have hScl : CompleteSpace S := FiniteDimensional.complete ℂ S

  let L : H →ₗ[ℂ] H :=
    { toFun := fun b => ∫ x, ⟪σ x v, b⟫_ℂ • σ x v ∂μ
      map_add' := fun a b => by
        simp only [inner_add_right, add_smul]
        exact integral_add (hint a) (hint b)
      map_smul' := fun c b => by
        simp only [inner_smul_right, RingHom.id_apply, mul_smul]
        exact integral_smul _ _ }
  have hinner : ∀ w b, ⟪w, L b⟫_ℂ = ∫ x, ⟪σ x v, b⟫_ℂ * ⟪w, σ x v⟫_ℂ ∂μ := by
    intro w b
    change ⟪w, ∫ x, ⟪σ x v, b⟫_ℂ • σ x v ∂μ⟫_ℂ = _
    rw [← integral_inner (hint b)]
    simp only [inner_smul_right]
  have hLS : ∀ b, L b ∈ S := by
    intro b
    rw [← Submodule.orthogonal_orthogonal S, Submodule.mem_orthogonal]
    intro w hw
    rw [hinner]
    have : ∀ x, ⟪w, σ x v⟫_ℂ = 0 := fun x => Submodule.inner_left_of_mem_orthogonal (hS x v hv) hw
    simp [this]
  have hzero : ∀ w, ⟪w, L w⟫_ℂ = 0 → ⟪w, v⟫_ℂ = 0 := by
    intro w hw
    rw [hinner] at hw
    have e1 : ∀ x, ⟪σ x v, w⟫_ℂ * ⟪w, σ x v⟫_ℂ = ((‖⟪σ x v, w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      intro x
      rw [← inner_conj_symm w, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [e1] at hw
    rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at hw
    have hcont : Continuous fun x => ‖⟪σ x v, w⟫_ℂ‖ ^ 2 := (hcoef v w).norm.pow 2
    have h1 := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) (integrable_cont hcont)).1 hw
    have h2 : ‖⟪σ 1 v, w⟫_ℂ‖ ^ 2 = 0 := congrFun ((hcont.ae_eq_iff_eq μ continuous_const).1 h1) 1
    simp only [map_one, ContinuousLinearMap.one_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      pow_eq_zero_iff, norm_eq_zero] at h2
    exact inner_eq_zero_symm.1 h2
  set R : Submodule ℂ H := S.map L with hR
  have hRc : CompleteSpace R := FiniteDimensional.complete ℂ R
  have hvR : v ∈ R := by
    set w := v - R.starProjection v with hw
    have hwo : w ∈ Rᗮ := R.sub_starProjection_mem_orthogonal v
    have hp : R.starProjection v ∈ R := R.starProjection_apply_mem v
    have hRS : R ≤ S := by rintro _ ⟨b, -, rfl⟩; exact hLS b
    have hwS : w ∈ S := S.sub_mem hv (hRS hp)
    have h1 : ⟪w, v⟫_ℂ = 0 := hzero w (Submodule.inner_left_of_mem_orthogonal (K := R) (Submodule.mem_map_of_mem hwS) hwo)
    have h2 : ⟪w, R.starProjection v⟫_ℂ = 0 := Submodule.inner_left_of_mem_orthogonal hp hwo
    have h3 : ⟪w, w⟫_ℂ = 0 := by
      conv_lhs => rw [hw, inner_sub_right, ← hw]
      rw [h1, h2, sub_zero]
    rw [inner_self_eq_zero, hw, sub_eq_zero] at h3
    rw [h3]; exact hp
  obtain ⟨b, -, hb⟩ := hvR
  obtain ⟨E, hE⟩ := exists_avg (μ := μ) hiso hc (hcoef v b)
  refine ⟨fun x => ⟪σ x v, b⟫_ℂ, E, hcoef v b, ?_, hE, by rw [hE]; exact hb⟩
  let B := Module.finBasis ℂ S
  refine ⟨fun i x => ⟪σ x (B i), b⟫_ℂ, fun i => hcoef _ b, fun k => ?_⟩
  refine ⟨fun i => (starRingEnd ℂ) (B.repr ⟨σ k⁻¹ v, hS _ v hv⟩ i), fun x => ?_⟩
  have e1 : σ k⁻¹ v = ∑ i, B.repr ⟨σ k⁻¹ v, hS _ v hv⟩ i • (B i : H) := by
    have := congrArg Subtype.val (B.sum_repr ⟨σ k⁻¹ v, hS _ v hv⟩)
    rw [Submodule.coe_sum] at this
    exact this.symm
  show ⟪σ (x * k⁻¹) v, b⟫_ℂ = _
  rw [map_mul, ContinuousLinearMap.mul_apply]
  conv_lhs => rw [e1]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, sum_inner, inner_smul_left]

end CompanionTheory.D.gk.admitted
end
end

namespace CompanionTheory.D.gk.admitted

theorem admissible_of_iwasawa {n : ℕ} {ε : Fin n → Bool} (h : Iwa ε) : AdmUJ ε :=
  admissible_of_finite_rank finite_rank_of_irreducible_unitary (goodPI_of small_irreducible_representation) transfer_holds exists_averaging_operator h

theorem k_finite_smooth : PI.KFinSmooth :=
  kFinSmooth_of finite_rank_of_irreducible_unitary (goodPI_of small_irreducible_representation) transfer_holds exists_averaging_operator iwasawa_decomposition_second_model garding_finite_smooth_vectors

end CompanionTheory.D.gk.admitted
