module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory

namespace GlobalTheory.SmGL.CuspMax

theorem subsingleton_jacquet_of_conj {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) {N N' : Subgroup G} (g : G) (h : ∀ u ∈ N, g * u * g⁻¹ ∈ N')
    (hN : Subsingleton (Jacquet π N)) : Subsingleton (Jacquet π N') := by
  have h1 : twKer π N 1 = ⊤ := Submodule.Quotient.subsingleton_iff.1 hN
  refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun v _ => ?_)
  have h2 : twKer π N 1 ≤ (twKer π N' 1).comap (π g) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, w, rfl⟩
    refine Submodule.subset_span ⟨⟨_, h u u.2⟩, π g w, ?_⟩
    simp [← Module.End.mul_apply, ← map_mul]
  have h3 : π g⁻¹ v ∈ twKer π N 1 := h1 ▸ Submodule.mem_top
  have h4 : π g (π g⁻¹ v) ∈ twKer π N' 1 := h2 h3
  simpa [← Module.End.mul_apply, ← map_mul] using h4

variable {R : Type} [CommRing R] {α β n : Type} {m : α → Type} {m' : β → Type}
  [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype β] [LinearOrder β] [∀ a, Fintype (m' a)] [∀ a, DecidableEq (m' a)]
  [Fintype n] [DecidableEq n]

theorem mem_unipRad_iff_entries {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ unipRad R e ↔ ∀ i j, ¬ blk e i < blk e j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j := by
  rw [mem_unipRad]
  constructor
  · rintro ⟨h1, h2⟩ i j hij
    rcases (not_lt.1 hij).lt_or_eq with h | h
    · rw [mem_parab.1 h1 i j h, Matrix.one_apply_ne]
      rintro rfl
      exact lt_irrefl _ h
    · obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
      obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
      obtain rfl : b = a := by simpa using h
      rw [h2]
      simp [Matrix.one_apply]
  · intro h
    refine ⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩
    · rw [h i j hij.not_gt, Matrix.one_apply_ne]
      rintro rfl
      exact lt_irrefl _ hij
    · rw [h _ _ (by simp)]
      simp [Matrix.one_apply]

theorem unipRad_ne_bot_iff [Nontrivial R] {e : (Σ a, m a) ≃ n} :
    unipRad R e ≠ ⊥ ↔ ∃ i j, blk e i < blk e j := by
  constructor
  · intro h
    by_contra hc
    refine h ((Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_)
    ext i j
    exact mem_unipRad_iff_entries.1 hu i j fun hij => hc ⟨i, j, hij⟩
  · rintro ⟨i, j, hij⟩ hb
    have hne : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hij
    let u : GL n R := ⟨Matrix.transvection i j 1, Matrix.transvection i j (-1),
      by rw [Matrix.transvection_mul_transvection_same _ _ hne]; simp,
      by rw [Matrix.transvection_mul_transvection_same _ _ hne]; simp⟩
    have hu : u ∈ unipRad R e := mem_unipRad_iff_entries.2 fun a b hab => by
      show Matrix.transvection i j (1 : R) a b = _
      rw [Matrix.transvection, Matrix.add_apply, Matrix.single_apply_of_ne, add_zero]
      rintro ⟨rfl, rfl⟩
      exact hab hij
    rw [hb, Subgroup.mem_bot] at hu
    have : Matrix.transvection i j (1 : R) i j = (1 : Matrix n n R) i j :=
      congrArg (fun g : GL n R => (g : Matrix n n R) i j) hu
    simp [Matrix.transvection] at this

theorem subsingleton_jacquet_of_perm {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL n R) V) {e : (Σ a, m a) ≃ n} {e' : (Σ a, m' a) ≃ n} (σ : Equiv.Perm n)
    (h : ∀ i j, blk e (σ i) < blk e (σ j) → blk e' i < blk e' j)
    (hN : Subsingleton (Jacquet π (unipRad R e))) : Subsingleton (Jacquet π (unipRad R e')) := by
  let g : GL n R := ⟨σ.toPEquiv.toMatrix, σ.symm.toPEquiv.toMatrix,
    by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp,
    by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp⟩
  refine subsingleton_jacquet_of_conj π g (fun u hu => ?_) hN
  refine mem_unipRad_iff_entries.2 fun i j hij => ?_
  show (σ.toPEquiv.toMatrix * (u : Matrix n n R) * σ.symm.toPEquiv.toMatrix : Matrix n n R) i j = _
  rw [PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_mul]
  simp only [Matrix.submatrix_apply, id, Equiv.symm_symm]
  rw [mem_unipRad_iff_entries.1 hu _ _ fun hh => hij (h i j hh)]
  simp [Matrix.one_apply]

theorem isCuspidal_iff_maximal (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) :
    IsCuspidal π ↔ IsSmooth π ∧ ∀ (r t : ℕ) (h : r + t = N), 0 < r → 0 < t →
      Subsingleton (Jacquet π (unipRad k (two (stdSum h)))) := by
  refine and_congr_right fun _ => ⟨fun H r t h hr ht => ?_, fun H s d e he => ?_⟩
  · let f : Fin N → Fin 2 := fun i => if blk (two (stdSum h)) i then 1 else 0
    let e : (Σ a : Fin 2, Fin (Fintype.card {i // f i = a})) ≃ Fin N :=
      (Equiv.sigmaCongrRight fun a => (Fintype.equivFin {i // f i = a}).symm).trans
        (Equiv.sigmaFiberEquiv f)
    have hb : ∀ i, blk e i = f i := fun i => rfl
    have hlt : ∀ i j, blk e i < blk e j ↔ blk (two (stdSum h)) i < blk (two (stdSum h)) j := by
      intro i j
      rw [hb, hb]
      simp only [f]
      cases blk (two (stdSum h)) i <;> cases blk (two (stdSum h)) j <;> decide
    refine subsingleton_jacquet_of_perm π (e := e) 1 (fun i j hij => (hlt i j).1 hij)
      (H 2 _ e (unipRad_ne_bot_iff.2 ⟨two (stdSum h) ⟨false, ⟨0, hr⟩⟩, two (stdSum h) ⟨true, ⟨0, ht⟩⟩,
        (hlt _ _).2 ?_⟩))
    rw [blk_apply, blk_apply]
    decide
  · obtain ⟨i₀, j₀, hij⟩ := unipRad_ne_bot_iff.1 he
    let p : Fin N → Prop := fun i => blk e i ≤ blk e i₀
    have hsum : Fintype.card {i // p i} + Fintype.card {i // ¬ p i} = N := by
      rw [← Fintype.card_sum, Fintype.card_congr (Equiv.sumCompl p), Fintype.card_fin]
    let τ : Fin (Fintype.card {i // p i}) ⊕ Fin (Fintype.card {i // ¬ p i}) ≃ Fin N :=
      (Equiv.sumCongr (Fintype.equivFin _).symm (Fintype.equivFin _).symm).trans (Equiv.sumCompl p)
    refine subsingleton_jacquet_of_perm π (τ.symm.trans (stdSum hsum)) (fun i j hh => ?_)
      (H _ _ hsum (Fintype.card_pos_iff.2 ⟨⟨i₀, le_rfl⟩⟩) (Fintype.card_pos_iff.2 ⟨⟨j₀, hij.not_ge⟩⟩))
    obtain ⟨i, rfl⟩ := τ.surjective i
    obtain ⟨j, rfl⟩ := τ.surjective j
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply] at hh
    rcases i with i | i <;> rcases j with j | j
    · rw [← two_false, ← two_false, blk_apply, blk_apply] at hh
      exact absurd hh (by decide)
    · have h1 : p (τ (.inl i)) := ((Fintype.equivFin {i // p i}).symm i).2
      have h2 : ¬ p (τ (.inr j)) := ((Fintype.equivFin {i // ¬ p i}).symm j).2
      exact lt_of_le_of_lt h1 (not_le.1 h2)
    · rw [← two_false, ← two_true, blk_apply, blk_apply] at hh
      exact absurd hh (by decide)
    · rw [← two_true, ← two_true, blk_apply, blk_apply] at hh
      exact absurd hh (by decide)

end GlobalTheory.SmGL.CuspMax
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology

noncomputable section
namespace GlobalTheory.SplitWeil.FourierPi

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]

def box (n : Type*) (s : kˣ) : Set (n → k) := Set.univ.pi fun _ => cball s

omit [DecidableEq n] in
theorem isOpen_box (s : kˣ) : IsOpen (box n s) :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball s

omit [Fintype n] [DecidableEq n] in
theorem isCompact_box (s : kˣ) : IsCompact (box n s) :=
  isCompact_univ_pi fun _ => isCompact_cball s

omit [DecidableEq n] in
theorem exists_box_subset {U : Set (n → k)} (hU : U ∈ 𝓝 (0 : n → k)) : ∃ s : kˣ, box n s ⊆ U := by
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨I, t, ht, hsub⟩ := hU
  have h1 : (⋂ i, t i) ∈ 𝓝 (0 : k) := Filter.iInter_mem.mpr ht
  obtain ⟨s, hs⟩ := exists_cball_subset h1
  exact ⟨s, fun x hx => hsub fun i _ => Set.mem_iInter.mp (hs (hx i trivial)) i⟩

omit [DecidableEq n] in
theorem exists_box_invariant {f : (n → k) → ℂ} (hf : f ∈ SB (n → k)) :
    ∃ s : kˣ, ∀ t ∈ box n s, ∀ x, f (x + t) = f x := by
  have h1 : ∀ᶠ t in 𝓝 (0 : n → k), ∀ x ∈ tsupport f, f (x + t) = f x := by
    refine IsCompact.eventually_forall_of_forall_eventually hf.2 fun x _ => ?_
    have h2 : IsLocallyConstant fun q : (n → k) × (n → k) => (f (q.2 + q.1), f q.2) :=
      (hf.1.comp_continuous (by fun_prop)).prodMk (hf.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, x)] with q hq
    simp only [Prod.mk.injEq, add_zero] at hq
    rw [hq.1, hq.2]
  obtain ⟨s, hs⟩ := exists_box_subset h1
  refine ⟨s, fun t ht x => ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact hs ht x hx
  by_cases hx' : x + t ∈ tsupport f
  · have := hs (show -t ∈ box n s from fun i _ => neg_mem_cball (ht i trivial)) _ hx'
    rw [← this, add_neg_cancel_right]
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

omit [DecidableEq n] in
theorem continuous_dot : Continuous fun q : (n → k) × (n → k) => q.1 ⬝ᵥ q.2 :=
  continuous_fst.dotProduct continuous_snd

variable {ψ : AddChar k Circle} {c : kˣ}
variable [MeasurableSpace k] [BorelSpace k]

theorem fourier_eq_zero_pi (μ : Measure (n → k)) [μ.IsAddRightInvariant] (h : HasConductor ψ c) {s : kˣ}
    {f : (n → k) → ℂ} (hs : ∀ t ∈ box n s, ∀ x, f (x + t) = f x) {y : n → k} (hy : y ∉ box n (c * s⁻¹)) :
    ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ = 0 := by
  haveI := secondCountable k
  obtain ⟨i, hi⟩ : ∃ i, y i ∉ cball (c * s⁻¹) := by
    by_contra hne
    push Not at hne
    exact hy fun i _ => hne i
  obtain ⟨t, ht, hne⟩ := h.exists_ne_one s hi
  have hbox : (Pi.single i t : n → k) ∈ box n s := by
    intro j _
    by_cases hj : j = i
    · subst hj; simpa using ht
    · simp [Pi.single_eq_of_ne hj, cball]
  have h1 := integral_add_right_eq_self (μ := μ) (fun x => f x * (ψ (x ⬝ᵥ y) : ℂ)) (Pi.single i t)
  have h2 : ∀ x, f (x + Pi.single i t) * (ψ ((x + Pi.single i t) ⬝ᵥ y) : ℂ) =
      (ψ (t * y i) : ℂ) * (f x * (ψ (x ⬝ᵥ y) : ℂ)) := by
    intro x
    rw [hs _ hbox, add_dotProduct, single_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul]; ring
  simp only [h2, integral_const_mul] at h1
  have h3 : (ψ (t * y i) : ℂ) - 1 ≠ 0 := fun h4 => hne (Circle.ext (by simpa using sub_eq_zero.mp h4))
  refine (mul_eq_zero.mp ?_).resolve_left h3
  rw [sub_mul, h1, one_mul, sub_self]

theorem fourier_indicator_pi (μ : Measure (n → k)) [μ.IsAddRightInvariant] (h : HasConductor ψ c) (s : kˣ)
    (x : n → k) :
    ∫ y, (box n (c * s⁻¹)).indicator (fun _ => (1 : ℂ)) y * (ψ (y ⬝ᵥ x) : ℂ) ∂μ =
      (box n s).indicator (fun _ => (μ.real (box n (c * s⁻¹)) : ℂ)) x := by
  haveI := secondCountable k
  by_cases hx : x ∈ box n s
  · rw [Set.indicator_of_mem hx]
    have : ∀ y, (box n (c * s⁻¹)).indicator (fun _ => (1 : ℂ)) y * (ψ (y ⬝ᵥ x) : ℂ) =
        (box n (c * s⁻¹)).indicator (fun _ => (1 : ℂ)) y := by
      intro y
      by_cases hy : y ∈ box n (c * s⁻¹)
      · have h1 : y ⬝ᵥ x ∈ cball c := by
          show valuation k (∑ i, y i * x i) ≤ valuation k (c : k)
          refine Valuation.map_sum_le (valuation k) fun i _ => ?_
          have h2 : valuation k (y i * x i) ≤ valuation k (((c * s⁻¹ : kˣ) : k) * s) := by
            rw [map_mul, map_mul]
            exact mul_le_mul' (hy i trivial) (hx i trivial)
          rwa [← Units.val_mul, inv_mul_cancel_right] at h2
        rw [h.eq_one h1, Circle.coe_one, mul_one]
      · simp [Set.indicator_of_notMem hy]
    simp only [this]
    rw [integral_indicator_const _ (isOpen_box _).measurableSet]
    simp
  · rw [Set.indicator_of_notMem hx]
    refine fourier_eq_zero_pi μ h (s := c * s⁻¹) (fun t ht y => ?_) (by simpa using hx)
    by_cases hy : y ∈ box n (c * s⁻¹)
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem
        (show y + t ∈ box n (c * s⁻¹) from fun i _ => add_mem_cball (hy i trivial) (ht i trivial))]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem]
      intro h1
      exact hy fun i _ => by simpa using add_mem_cball (h1 i trivial) (neg_mem_cball (ht i trivial))

theorem fourier_mem_SB (μ : Measure (n → k)) [μ.IsAddRightInvariant] (h : HasConductor ψ c)
    {f : (n → k) → ℂ} (hf : f ∈ SB (n → k)) :
    (fun y : n → k => ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) ∈ SB (n → k) := by
  haveI := t2Space k
  obtain ⟨s, hs⟩ := exists_box_invariant hf
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun y => ?_,
    HasCompactSupport.intro (isCompact_box (c * s⁻¹)) fun y hy => fourier_eq_zero_pi μ h hs hy⟩
  have h1 : ∀ᶠ z in 𝓝 y, ∀ x ∈ tsupport f, ψ (x ⬝ᵥ z) = ψ (x ⬝ᵥ y) := by
    refine IsCompact.eventually_forall_of_forall_eventually hf.2 fun x _ => ?_
    have h2 : IsLocallyConstant fun q : (n → k) × (n → k) => (ψ (q.2 ⬝ᵥ q.1), ψ (q.2 ⬝ᵥ y)) :=
      (h.isLocallyConstant.comp_continuous (continuous_snd.dotProduct continuous_fst)).prodMk
        (h.isLocallyConstant.comp_continuous (continuous_snd.dotProduct continuous_const))
    filter_upwards [h2.eventually_eq (y, x)] with q hq
    simp only [Prod.mk.injEq] at hq
    rw [hq.1, hq.2]
  filter_upwards [h1] with z hz
  congr 1
  funext x
  by_cases hx : x ∈ tsupport f
  · rw [hz x hx]
  · simp [image_eq_zero_of_notMem_tsupport hx]

theorem fourier_inversion_pi (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (h : HasConductor ψ c)
    {f : (n → k) → ℂ} (hf : f ∈ SB (n → k)) :
    ∃ s : kˣ, ∫ y, (∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) ∂μ =
      ((μ.real (box n s) * μ.real (box n (c * s⁻¹)) : ℝ) : ℂ) * f 0 := by
  haveI := secondCountable k
  haveI := t2Space k
  obtain ⟨s, hs⟩ := exists_box_invariant hf
  refine ⟨s, ?_⟩
  set e : (n → k) → ℂ := (box n (c * s⁻¹)).indicator (fun _ => (1 : ℂ)) with he
  have h1 : ∀ y, ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ = ∫ x, f x * (e y * (ψ (y ⬝ᵥ x) : ℂ)) ∂μ := by
    intro y
    by_cases hy : y ∈ box n (c * s⁻¹)
    · simp [he, Set.indicator_of_mem hy, dotProduct_comm y]
    · simp [he, Set.indicator_of_notMem hy, fourier_eq_zero_pi μ h hs hy]
  have hei : Integrable e μ :=
    (integrable_indicator_iff (isOpen_box _).measurableSet).mpr
      (integrableOn_const (isCompact_box _).measure_lt_top.ne)
  have hfi : Integrable f μ := hf.1.continuous.integrable_of_hasCompactSupport hf.2
  have hint : Integrable (Function.uncurry fun y x => f x * (e y * (ψ (y ⬝ᵥ x) : ℂ))) (μ.prod μ) := by
    have h2 := (hei.mul_prod hfi).mul_bdd (c := 1) (g := fun q : (n → k) × (n → k) => (ψ (q.1 ⬝ᵥ q.2) : ℂ))
      (Continuous.aestronglyMeasurable
        (continuous_subtype_val.comp (h.continuous.comp continuous_dot)))
      (Filter.Eventually.of_forall fun q => (Circle.norm_coe _).le)
    refine h2.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [Function.uncurry]
    ring
  simp only [h1]
  rw [integral_integral_swap hint]
  simp only [integral_const_mul, he, fourier_indicator_pi μ h s]
  have h3 : ∀ x, f x * (box n s).indicator (fun _ => (μ.real (box n (c * s⁻¹)) : ℂ)) x =
      (box n s).indicator (fun _ => (μ.real (box n (c * s⁻¹)) : ℂ) * f 0) x := by
    intro x
    by_cases hx : x ∈ box n s
    · have := hs x hx 0
      rw [zero_add] at this
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, this, mul_comm]
    · simp [Set.indicator_of_notMem hx]
  simp only [h3]
  rw [integral_indicator_const _ (isOpen_box _).measurableSet, Complex.real_smul, ← mul_assoc,
    ← Complex.ofReal_mul]

theorem vol_mul_vol_dual {ν : Measure k} (h : HasConductor ψ c) (hν : IsSelfDual ψ ν) (s : kˣ) :
    ν.real (cball s) * ν.real (cball (c * s⁻¹)) = 1 := by
  haveI := hν.1
  haveI := t2Space k
  have hcl : IsClopen (cball (1 : kˣ)) := ⟨(isCompact_cball 1).isClosed, isOpen_cball 1⟩
  have hf : (cball (1 : kˣ)).indicator (fun _ => (1 : ℂ)) ∈ SB k := by
    refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_,
      HasCompactSupport.intro (isCompact_cball 1) fun y hy => Set.indicator_of_notMem hy _⟩
    by_cases hx : x ∈ cball (1 : kˣ)
    · filter_upwards [hcl.isOpen.mem_nhds hx] with z hz
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hz]
    · filter_upwards [hcl.compl.isOpen.mem_nhds hx] with z hz
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hz]
  have h1 := (fourier_inversion ν h hf).symm.trans (hν.2 _ hf)
  rw [Set.indicator_of_mem (by simp [cball]), mul_one] at h1
  have h2 : ν.real (𝒪[k] : Set k) ^ 2 * nabs k c = 1 := by exact_mod_cast h1
  have h4 : nabs k c = nabs k s * nabs k (c * s⁻¹) := by
    rw [← nabs_mul, mul_comm, inv_mul_cancel_right]
  rw [measureReal_cball, measureReal_cball, ← h2, h4]; ring

theorem fourier_pi_of_conductor {ν : Measure k} (h : HasConductor ψ c) (hν : IsSelfDual ψ ν)
    {f : (n → k) → ℂ} (hf : f ∈ SB (n → k)) :
    (fun y : n → k => ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) ∈ SB (n → k) ∧
      ∫ y : n → k, (∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) ∂(Measure.pi fun _ => ν) = f 0 := by
  haveI := hν.1
  haveI := secondCountable k
  haveI := t2Space k
  refine ⟨fourier_mem_SB _ h hf, ?_⟩
  obtain ⟨s, hs⟩ := fourier_inversion_pi (Measure.pi fun _ : n => ν) h hf
  have hb : ∀ r : kˣ, (Measure.pi fun _ : n => ν).real (box n r) = ν.real (cball r) ^ Fintype.card n := by
    intro r
    simp [Measure.real, box, Measure.pi_pi]
  rw [hs, hb, hb, ← mul_pow, vol_mul_vol_dual h hν]
  simp

theorem fourier_pi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν), ∀ f ∈ SB (n → k), (fun y : n → k => ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) ∈ SB (n → k) ∧ ∫ y : n → k, (∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) ∂(Measure.pi fun _ => ν) = f 0 := by
  intro k _ _ _ _ _ _ n _ _ ψ hc h1 ν hν f hf
  obtain ⟨c, h⟩ := (GlobalTheory.SplitWeil.conductor_exists k).1 ψ hc h1
  exact fourier_pi_of_conductor h hν hf

end GlobalTheory.SplitWeil.FourierPi
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPiStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_transform_inversion_localFieldPi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν), ∀ f ∈ SB (n → k), (fun y : n → k => ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) ∈ SB (n → k) ∧ ∫ y : n → k, (∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) ∂(Measure.pi fun _ => ν) = f 0 := by
  first | exact @GlobalTheory.SplitWeil.FourierPi.fourier_pi | exact GlobalTheory.SplitWeil.FourierPi.fourier_pi | (intros; apply GlobalTheory.SplitWeil.FourierPi.fourier_pi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory

namespace GlobalTheory.SmGL.Placing

section General

variable {F G M V : Type} [Field F] [Group G] [Group M] [AddCommGroup V] [Module F V]

def indLeft [TopologicalSpace G] [IsTopologicalGroup G] {P Q : Subgroup G}
    {σ : Representation F P V} {τ : Representation F Q V} (w : G)
    (h : ∀ q : Q, ∃ p : P, (p : G) = w * q * w⁻¹ ∧ σ p = τ q) :
    smoothPart (ind P σ) →ₗ[F] smoothPart (ind Q τ) where
  toFun f := ⟨⟨fun g => f.1.1 (w * g), fun q g => by
      obtain ⟨p, hp, hs⟩ := h q
      have : w * (q * g) = p * (w * g) := by rw [hp]; group
      show f.1.1 (w * (q * g)) = τ q (f.1.1 (w * g))
      rw [this, f.1.2 p, hs]⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset
      (IsOpen.mem_nhds f.2 (by simp)) fun g hg => by
        have hg' : ind P σ g f.1 = f.1 := hg
        apply Subtype.ext
        funext x
        have := congrFun (congrArg Subtype.val hg') (w * x)
        show f.1.1 (w * (x * g)) = f.1.1 (w * x)
        rw [← mul_assoc]
        exact this)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem _root_.GlobalTheory.SmGL.Placing.smInd_equiv [TopologicalSpace G] [IsTopologicalGroup G]
    {P Q : Subgroup G}
    {σ : Representation F P V} {τ : Representation F Q V} (w : G)
    (h : ∀ q : Q, ∃ p : P, (p : G) = w * q * w⁻¹ ∧ σ p = τ q)
    (h' : ∀ p : P, ∃ q : Q, (q : G) = w⁻¹ * p * w⁻¹⁻¹ ∧ τ q = σ p) :
    Nonempty ((_root_.GlobalTheory.PRep.smInd P σ).Equiv (_root_.GlobalTheory.PRep.smInd Q τ)) := by
  refine ⟨Representation.Equiv.mk
    { _root_.GlobalTheory.SmGL.Placing.indLeft w h with
      invFun := _root_.GlobalTheory.SmGL.Placing.indLeft w⁻¹ h'
      left_inv := fun f => ?_
      right_inv := fun f => ?_ } fun g => ?_⟩
  · refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    exact congrArg f.1.1 (mul_inv_cancel_left w x)
  · refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    exact congrArg f.1.1 (inv_mul_cancel_left w x)
  · refine LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => ?_))
    exact congrArg f.1.1 (mul_assoc w x g)

lemma _root_.GlobalTheory.SmGL.Placing.twKer_le (π : Representation F G V)
    {N N' : Subgroup G} (w : G) (h : ∀ u ∈ N, w * u * w⁻¹ ∈ N') :
    _root_.GlobalTheory.PRep.twKer π N 1 ≤ (_root_.GlobalTheory.PRep.twKer π N' 1).comap (π w) := by
  unfold _root_.GlobalTheory.PRep.twKer
  rw [Submodule.span_le]
  rintro _ ⟨u, v, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap]
  refine Submodule.subset_span ⟨⟨w * u * w⁻¹, h u u.2⟩, π w v, ?_⟩
  simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, map_mul, Module.End.mul_apply]
  rw [← Module.End.mul_apply (π w⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem _root_.GlobalTheory.SmGL.Placing.jacquet_equiv (π : Representation F G V) {N N' : Subgroup G}
    {s s' : M →* G}
    (hs : ∀ g, s g ∈ Subgroup.normalizer (N : Set G))
    (hs' : ∀ g, s' g ∈ Subgroup.normalizer (N' : Set G)) (χ : M →* Fˣ) (w : G)
    (h : ∀ u ∈ N, w * u * w⁻¹ ∈ N') (h' : ∀ u ∈ N', w⁻¹ * u * w⁻¹⁻¹ ∈ N)
    (hw : ∀ g, w * s g * w⁻¹ = s' g) :
    Nonempty ((_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.PRep.jacquet π N s hs) χ).Equiv
      (_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.PRep.jacquet π N' s' hs') χ)) := by
  have hK := _root_.GlobalTheory.SmGL.Placing.twKer_le π w h
  have hK' := _root_.GlobalTheory.SmGL.Placing.twKer_le π w⁻¹ h'
  have hinv : ∀ a b : G, a * b = 1 → ∀ v, π a (π b v) = v := fun a b hab v => by
    rw [← Module.End.mul_apply, ← map_mul, hab, map_one, Module.End.one_apply]
  let eq : _root_.GlobalTheory.PRep.Jacquet π N ≃ₗ[F] _root_.GlobalTheory.PRep.Jacquet π N' :=
    LinearEquiv.ofLinear ((_root_.GlobalTheory.PRep.twKer π N 1).mapQ _ (π w) hK)
      ((_root_.GlobalTheory.PRep.twKer π N' 1).mapQ _ (π w⁻¹) hK')
      (Submodule.linearMap_qext _ (LinearMap.ext fun v => by
        simp [hinv w w⁻¹ (mul_inv_cancel w)]))
      (Submodule.linearMap_qext _ (LinearMap.ext fun v => by
        simp [hinv w⁻¹ w (inv_mul_cancel w)]))
  refine ⟨Representation.Equiv.mk eq fun g => ?_⟩
  refine LinearMap.ext fun x => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (_root_.GlobalTheory.PRep.twKer π N 1) x
  have hv : π w (π (s g) v) = π (s' g) (π w v) := by
    rw [← hw g, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      hinv w⁻¹ w (inv_mul_cancel w)]
  simp [eq, _root_.GlobalTheory.SmGL.twist, _root_.GlobalTheory.PRep.jacquet, hv]

end General

section Blocks

variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

def Moves {ι : Type} (e e' : ι ≃ n) (w : GL n R) : Prop :=
  ∀ (g : GL n R) x y, ((w * g * w⁻¹ : GL n R) : Matrix n n R) (e' x) (e' y) =
    (g : Matrix n n R) (e x) (e y)

theorem _root_.GlobalTheory.SmGL.Placing.exists_moves {ι : Type} (e e' : ι ≃ n) :
    ∃ w : GL n R, _root_.GlobalTheory.SmGL.Placing.Moves e e' w := by
  let σ : n ≃ n := e.symm.trans e'
  refine ⟨⟨σ.symm.toPEquiv.toMatrix, σ.toPEquiv.toMatrix, ?_, ?_⟩, fun g x y => ?_⟩
  · rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  · rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  · simp [σ, Units.inv_mk, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]

variable {e e' : (Σ a, m a) ≃ n} {w : GL n R}

end Blocks

section
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

private theorem moves_inv_of_moves {ι : Type} {e e' : ι ≃ n} {w : GL n R}
    (hw : _root_.GlobalTheory.SmGL.Placing.Moves e e' w) : _root_.GlobalTheory.SmGL.Placing.Moves e' e w⁻¹ := by
  intro g x y
  have := hw (w⁻¹ * g * w⁻¹⁻¹) x y
  rw [← this]
  congr 2
  group

variable {e e' : (Σ a, m a) ≃ n} {w : GL n R} in
private theorem conj_mem_parab_of_moves (hw : _root_.GlobalTheory.SmGL.Placing.Moves e e' w)
    {g : GL n R} (hg : g ∈ _root_.GlobalTheory.SmGL.parab R e) :
    w * g * w⁻¹ ∈ _root_.GlobalTheory.SmGL.parab R e' := by
  have hg' : Matrix.BlockTriangular (g : Matrix n n R) (_root_.GlobalTheory.SmGL.blk e) := hg
  change Matrix.BlockTriangular _ (_root_.GlobalTheory.SmGL.blk e')
  intro i j hij
  obtain ⟨x, rfl⟩ := e'.surjective i
  obtain ⟨y, rfl⟩ := e'.surjective j
  rw [hw]
  exact hg' (by simpa [_root_.GlobalTheory.SmGL.blk] using hij)

variable {e e' : (Σ a, m a) ≃ n} {w : GL n R} in
private theorem leviProj_conj_of_moves (hw : _root_.GlobalTheory.SmGL.Placing.Moves e e' w)
    (p : _root_.GlobalTheory.SmGL.parab R e) :
    _root_.GlobalTheory.SmGL.leviProj R e' ⟨w * p * w⁻¹, conj_mem_parab_of_moves hw p.2⟩ =
      _root_.GlobalTheory.SmGL.leviProj R e p := by
  refine funext fun a => Units.ext (Matrix.ext fun i j => ?_)
  simpa [_root_.GlobalTheory.SmGL.leviProj, _root_.GlobalTheory.SmGL.diagBlock] using hw (p : GL n R) ⟨a, i⟩ ⟨a, j⟩

variable {e e' : (Σ a, m a) ≃ n} {w : GL n R} in
private theorem conj_mem_unipRad_of_moves (hw : _root_.GlobalTheory.SmGL.Placing.Moves e e' w)
    {u : GL n R} (hu : u ∈ _root_.GlobalTheory.SmGL.unipRad R e) :
    w * u * w⁻¹ ∈ _root_.GlobalTheory.SmGL.unipRad R e' := by
  have hP := _root_.GlobalTheory.SmGL.unipRad_le_parab R e hu
  have h1 := (_root_.GlobalTheory.SmGL.coe_mem_unipRad R (p := ⟨u, hP⟩)).1 hu
  exact (_root_.GlobalTheory.SmGL.coe_mem_unipRad R
    (p := ⟨w * u * w⁻¹, conj_mem_parab_of_moves hw hP⟩)).2
    ((leviProj_conj_of_moves hw ⟨u, hP⟩).trans h1)

variable {e e' : (Σ a, m a) ≃ n} {w : GL n R} in
private theorem leviEmb_conj_of_moves (hw : _root_.GlobalTheory.SmGL.Placing.Moves e e' w)
    (x : _root_.GlobalTheory.SmGL.Levi R m) :
    w * _root_.GlobalTheory.SmGL.leviEmb R e x * w⁻¹ = _root_.GlobalTheory.SmGL.leviEmb R e' x := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  obtain ⟨p, rfl⟩ := e'.surjective i
  obtain ⟨q, rfl⟩ := e'.surjective j
  rw [hw]
  simp [_root_.GlobalTheory.SmGL.leviEmb, Matrix.reindex_apply]
end

theorem _root_.GlobalTheory.SmGL.Placing.parInd_jac_placing : ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α]
    [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    (e e' : (Σ a, m a) ≃ n) (V : Type) [AddCommGroup V] [Module ℂ V],
    (∀ ρ : Representation ℂ (_root_.GlobalTheory.SmGL.Levi k m) V,
      Nonempty ((_root_.GlobalTheory.SmGL.parInd e ρ).Equiv (_root_.GlobalTheory.SmGL.parInd e' ρ))) ∧
    ∀ π : Representation ℂ (GL n k) V,
      Nonempty ((_root_.GlobalTheory.SmGL.jac e π).Equiv (_root_.GlobalTheory.SmGL.jac e' π)) := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e e' V _ _
  refine ⟨fun ρ => ?_, fun π => ?_⟩
  · obtain ⟨w, hw⟩ := _root_.GlobalTheory.SmGL.Placing.exists_moves (R := k) e' e
    have hw' := moves_inv_of_moves hw
    exact _root_.GlobalTheory.SmGL.Placing.smInd_equiv w
      (fun q => ⟨⟨_, conj_mem_parab_of_moves hw q.2⟩, rfl, by
        simp only [MonoidHom.comp_apply]
        rw [leviProj_conj_of_moves hw q]⟩)
      (fun p => ⟨⟨_, conj_mem_parab_of_moves hw' p.2⟩, rfl, by
        simp only [MonoidHom.comp_apply]
        rw [leviProj_conj_of_moves hw' p]⟩)
  · obtain ⟨w, hw⟩ := _root_.GlobalTheory.SmGL.Placing.exists_moves (R := k) e e'
    have hw' := moves_inv_of_moves hw
    exact _root_.GlobalTheory.SmGL.Placing.jacquet_equiv π _ _ _ w
      (fun u hu => conj_mem_unipRad_of_moves hw hu)
      (fun u hu => conj_mem_unipRad_of_moves hw' hu)
      (leviEmb_conj_of_moves hw)

end GlobalTheory.SmGL.Placing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrix
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Kronecker

namespace GlobalTheory.SplitWeil

theorem map_curry_symm_pi_pi {X a b : Type} [MeasurableSpace X] [Fintype a] [Fintype b] (ν : Measure X)
    [SigmaFinite ν] :
    Measure.map (MeasurableEquiv.curry b a X).symm (Measure.pi fun _ : b => Measure.pi fun _ : a => ν) =
      Measure.pi fun _ : b × a => ν := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (MeasurableEquiv.curry b a X).symm.measurable (MeasurableSet.univ_pi hs)]
  have hpre : (MeasurableEquiv.curry b a X).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi fun i : b => Set.univ.pi fun j : a => s (i, j) := by
    ext x
    simp [MeasurableEquiv.coe_curry_symm, Prod.forall]
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  (ν : Measure k) [ν.IsAddHaarMeasure]

omit [MeasurableSpace k] [BorelSpace k] in
theorem nabs_pos' (x : kˣ) : 0 < nabs k x := by
  show (0 : ℝ) < ((distribHaarChar k x : NNReal) : ℝ)
  exact NNReal.coe_pos.mpr distribHaarChar_pos

private lemma measurable_mulVec' {ι : Type} [Fintype ι] (M : Matrix ι ι k) : Measurable M.mulVec := by
  have : SecondCountableTopology k := secondCountable k
  exact (Continuous.matrix_mulVec continuous_const continuous_id).measurable

private lemma map_diagonal_mulVec_measure_pi (D : a → k) (u : kˣ) (hu : (u : k) = (Matrix.diagonal D).det) :
    Measure.map (Matrix.diagonal D).mulVec (Measure.pi fun _ : a => ν) =
      distribHaarChar k u⁻¹ • Measure.pi fun _ : a => ν := by
  have : SecondCountableTopology k := secondCountable k
  have hD : ∀ i, D i ≠ 0 := by
    intro i hi
    have h0 : (u : k) ≠ 0 := u.ne_zero
    rw [hu, Matrix.det_diagonal] at h0
    exact h0 (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  let e : a → kˣ := fun i => Units.mk0 (D i) (hD i)
  have hue : u = ∏ i, e i := by
    ext
    rw [hu, Matrix.det_diagonal, Units.coe_prod]
    rfl
  have hm := measurable_mulVec' (Matrix.diagonal D)
  have E : distribHaarChar k u • Measure.map (Matrix.diagonal D).mulVec (Measure.pi fun _ : a => ν) =
      Measure.pi fun _ : a => ν := by
    refine (Measure.pi_eq fun s hs => ?_).symm
    rw [Measure.smul_apply, Measure.map_apply hm (MeasurableSet.univ_pi hs)]
    have hpre : (Matrix.diagonal D).mulVec ⁻¹' Set.univ.pi s =
        Set.univ.pi fun i => (fun x : k => e i • x) ⁻¹' s i := by
      ext x
      simp [Matrix.mulVec_diagonal, Units.smul_def, e]
    rw [hpre, Measure.pi_pi, hue, map_prod, ENNReal.smul_def, smul_eq_mul, ENNReal.ofNNReal_finsetProd,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Set.preimage_smul, ← distribHaarChar_mul ν (e i)⁻¹, ← mul_assoc, ← ENNReal.coe_mul, ← map_mul, mul_inv_cancel,
      map_one, ENNReal.coe_one, one_mul]
  calc Measure.map (Matrix.diagonal D).mulVec (Measure.pi fun _ : a => ν)
      = (distribHaarChar k u⁻¹ * distribHaarChar k u) •
          Measure.map (Matrix.diagonal D).mulVec (Measure.pi fun _ : a => ν) := by
        rw [← map_mul, inv_mul_cancel, map_one, one_smul]
    _ = distribHaarChar k u⁻¹ • Measure.pi fun _ : a => ν := by rw [mul_smul, E]

private lemma map_transvection_mulVec_measure_pi (t : Matrix.TransvectionStruct a k) :
    Measure.map t.toMatrix.mulVec (Measure.pi fun _ : a => ν) = Measure.pi fun _ : a => ν := by
  have : SecondCountableTopology k := secondCountable k
  obtain ⟨i, j, hij, c⟩ := t
  show Measure.map (Matrix.transvection i j c).mulVec (Measure.pi fun _ : a => ν) = Measure.pi fun _ : a => ν
  have hm := measurable_mulVec' (Matrix.transvection i j c)
  have key : ∀ (x : a → k) (y : k), (Matrix.transvection i j c).mulVec (Function.update x i y) =
      Function.update x i (y + c * x j) := by
    intro x y
    ext l
    by_cases hl : l = i
    · subst hl
      simp [Matrix.transvection, Matrix.mulVec, dotProduct, Matrix.single_apply, add_mul,
        Finset.sum_add_distrib, Matrix.one_apply, Function.update_of_ne hij.symm]
    · simp [Matrix.transvection, Matrix.mulVec, dotProduct, Matrix.single_apply, add_mul,
        Finset.sum_add_distrib, Matrix.one_apply, Function.update_of_ne hl, Ne.symm hl]
  refine (Measure.pi_eq fun s hs => ?_).symm
  have hbox : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  have hind : Measurable ((Set.univ.pi s).indicator (1 : (a → k) → ENNReal)) := measurable_one.indicator hbox
  rw [← Measure.pi_pi, ← lintegral_indicator_one hbox, ← lintegral_indicator_one hbox,
    lintegral_map hind hm]
  refine lintegral_eq_of_lmarginal_eq {i} (hind.comp hm) hind ?_
  ext x
  rw [lmarginal_singleton, lmarginal_singleton]
  simp only [Function.comp_apply, key]
  exact lintegral_add_right_eq_self (fun y => (Set.univ.pi s).indicator 1 (Function.update x i y)) (c * x j)

private lemma map_mulVec_measure_pi_eq_distribHaarChar_smul {M : Matrix a a k} (hM : M.det ≠ 0) (u : kˣ) (hu : (u : k) = M.det) :
    Measure.map M.mulVec (Measure.pi fun _ : a => ν) = distribHaarChar k u⁻¹ • Measure.pi fun _ : a => ν := by
  have : SecondCountableTopology k := secondCountable k
  revert u
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => ∀ u : kˣ, (u : k) = M.det →
      Measure.map M.mulVec (Measure.pi fun _ : a => ν) = distribHaarChar k u⁻¹ • Measure.pi fun _ : a => ν)
    M hM ?_ ?_ ?_
  · intro D _ u hu
    exact map_diagonal_mulVec_measure_pi ν D u hu
  · intro t u hu
    have h1 : u = 1 := Units.ext (by rw [hu, Matrix.TransvectionStruct.det, Units.val_one])
    rw [h1, inv_one, map_one, one_smul, map_transvection_mulVec_measure_pi ν t]
  · intro A B hA hB IA IB u hu
    have hfun : (A * B).mulVec = A.mulVec ∘ B.mulVec := by
      funext x
      simp [Matrix.mulVec_mulVec]
    have hinv : u⁻¹ = (Units.mk0 _ hB)⁻¹ * (Units.mk0 _ hA)⁻¹ := by
      rw [← mul_inv]
      congr 1
      ext
      simp [hu, Matrix.det_mul, mul_comm]
    rw [hfun, ← Measure.map_map (measurable_mulVec' A) (measurable_mulVec' B), IB (Units.mk0 _ hB) rfl,
      Measure.map_smul _ (measurable_mulVec' A).aemeasurable, IA (Units.mk0 _ hA) rfl,
      hinv, map_mul, mul_smul]

private lemma integral_comp_mulVec_eq_nabs_inv_smul {M : Matrix a a k} (hM : M.det ≠ 0) (u : kˣ) (hu : (u : k) = M.det)
    (f : (a → k) → ℂ) :
    ∫ x, f (M.mulVec x) ∂(Measure.pi fun _ : a => ν) =
      ((nabs k u)⁻¹ : ℝ) • ∫ x, f x ∂(Measure.pi fun _ : a => ν) := by
  have : SecondCountableTopology k := secondCountable k
  have hdet : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  let e : (a → k) ≃ᵐ (a → k) :=
    { toFun := M.mulVec
      invFun := M⁻¹.mulVec
      left_inv := fun x => by simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet]
      right_inv := fun x => by simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet]
      measurable_toFun := measurable_mulVec' M
      measurable_invFun := measurable_mulVec' M⁻¹ }
  have h1 : ∫ x, f (M.mulVec x) ∂(Measure.pi fun _ : a => ν) =
      ∫ y, f y ∂(Measure.map e (Measure.pi fun _ : a => ν)) := (e.measurableEmbedding.integral_map f).symm
  have h2 : (e : (a → k) → (a → k)) = M.mulVec := rfl
  rw [h1, h2, map_mulVec_measure_pi_eq_distribHaarChar_smul ν hM u hu, integral_smul_nnreal_measure, map_inv, NNReal.smul_def,
    NNReal.coe_inv]
  rfl

theorem integral_comp_mulVec_eq_smul (g : GL a k) (f : (a → k) → ℂ) :
    ∫ x, f (g.val.mulVec x) ∂(Measure.pi fun _ => ν) =
      ((nabs k (Matrix.GeneralLinearGroup.det g))⁻¹ : ℝ) • ∫ x, f x ∂(Measure.pi fun _ => ν) := by
  exact integral_comp_mulVec_eq_nabs_inv_smul ν (Matrix.GeneralLinearGroup.det g).ne_zero _ rfl f

omit [BorelSpace k] [DecidableEq a] [DecidableEq b] in
theorem integral_volM_eq_pi (Φ : Matrix b a k → ℂ) :
    ∫ x, Φ x ∂(volM ν b a) = ∫ y, Φ (Matrix.of (Function.curry y)) ∂(Measure.pi fun _ : b × a => ν) := by
  have : SecondCountableTopology k := secondCountable k
  rw [← map_curry_symm_pi_pi ν, (MeasurableEquiv.curry b a k).symm.measurableEmbedding.integral_map]
  rfl

private lemma mul_of_curry_mul_eq_of_curry_kronecker_mulVec (g : GL a k) (h : GL b k) (y : b × a → k) :
    h.val * Matrix.of (Function.curry y) * g.val =
      Matrix.of (Function.curry ((h.val ⊗ₖ g.valᵀ).mulVec y)) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, Function.curry_apply, Matrix.mulVec, dotProduct,
    Matrix.kroneckerMap_apply, Matrix.transpose_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  ring

theorem integral_comp_mul_mul_volM (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ) :
    ∫ x, Φ (h.val * x * g.val) ∂(volM ν b a) =
      (nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card a : ℝ)) *
        nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card b : ℝ))) • ∫ x, Φ x ∂(volM ν b a) := by
  have hK : (h.val ⊗ₖ g.valᵀ).det ≠ 0 := by
    rw [Matrix.det_kronecker, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ (Matrix.GeneralLinearGroup.det h).ne_zero)
      (pow_ne_zero _ (Matrix.GeneralLinearGroup.det g).ne_zero)
  set u : kˣ := Matrix.GeneralLinearGroup.det h ^ Fintype.card a *
    Matrix.GeneralLinearGroup.det g ^ Fintype.card b with hu_def
  have hu : (u : k) = (h.val ⊗ₖ g.valᵀ).det := by
    rw [Matrix.det_kronecker, Matrix.det_transpose, hu_def, Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val]
    rfl
  rw [integral_volM_eq_pi ν (fun x => Φ (h.val * x * g.val)), integral_volM_eq_pi ν Φ]
  simp only [mul_of_curry_mul_eq_of_curry_kronecker_mulVec g h]
  rw [integral_comp_mulVec_eq_nabs_inv_smul ν hK u hu (fun y => Φ (Matrix.of (Function.curry y)))]
  congr 1
  have hn : nabs k u = nabs k (Matrix.GeneralLinearGroup.det h) ^ Fintype.card a *
      nabs k (Matrix.GeneralLinearGroup.det g) ^ Fintype.card b := by
    simp only [nabs, hu_def, map_mul, map_pow, NNReal.coe_mul, NNReal.coe_pow]
  rw [hn, mul_inv, Real.rpow_neg (nabs_pos' _).le, Real.rpow_neg (nabs_pos' _).le, Real.rpow_natCast,
    Real.rpow_natCast]

theorem linear_change_of_variables : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (ν : Measure k) [ν.IsAddHaarMeasure], (∀ (g : GL a k) (f : (a → k) → ℂ), ∫ x, f (g.val.mulVec x) ∂(Measure.pi fun _ => ν) = ((nabs k (Matrix.GeneralLinearGroup.det g))⁻¹ : ℝ) • ∫ x, f x ∂(Measure.pi fun _ => ν)) ∧ ∀ (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ), ∫ x, Φ (h.val * x * g.val) ∂(volM ν b a) = (nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card a : ℝ)) * nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card b : ℝ))) • ∫ x, Φ x ∂(volM ν b a) := by
  intro k _ _ _ _ _ _ a b _ _ _ _ ν _
  exact ⟨fun g f => integral_comp_mulVec_eq_smul ν g f, fun g h Φ => integral_comp_mul_mul_volM ν g h Φ⟩

end GlobalTheory.SplitWeil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrixStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_change_of_variables_localField_matrix : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (ν : Measure k) [ν.IsAddHaarMeasure], (∀ (g : GL a k) (f : (a → k) → ℂ), ∫ x, f (g.val.mulVec x) ∂(Measure.pi fun _ => ν) = ((nabs k (Matrix.GeneralLinearGroup.det g))⁻¹ : ℝ) • ∫ x, f x ∂(Measure.pi fun _ => ν)) ∧ ∀ (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ), ∫ x, Φ (h.val * x * g.val) ∂(volM ν b a) = (nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card a : ℝ)) * nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card b : ℝ))) • ∫ x, Φ x ∂(volM ν b a) := by
  first | exact @GlobalTheory.SplitWeil.linear_change_of_variables | exact GlobalTheory.SplitWeil.linear_change_of_variables | (intros; apply GlobalTheory.SplitWeil.linear_change_of_variables <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne
noncomputable section

open GlobalTheory.SplitWeil GlobalTheory.SmGL

namespace GlobalTheory.SatakeBound

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def IsBorelSph (γ : Fin n → ℂ) (φ : GL (Fin n) k → ℂ) : Prop :=
  (∀ g : GL (Fin n) k, ∀ x ∈ KO k (Fin n), φ (g * x) = φ g) ∧
    ∀ b ∈ borel k (Fin n), ∀ t : Fin n → kˣ,
      (∀ i, (b : Matrix (Fin n) (Fin n) k) i i = t i) → φ b = ∏ i, γ i ^ ord k (t i)

def HasBoundedSums (φ : GL (Fin n) k → ℂ) : Prop :=
  ∀ S : Finset (GL (Fin n) k ⧸ KO k (Fin n)), (∀ x ∈ KO k (Fin n), ∀ c ∈ S, x • c ∈ S) →
    ‖∑ c ∈ S, φ c.out‖ ≤ S.card

theorem isBorelSph_one : IsBorelSph k (n := n) (fun _ => 1) fun _ => 1 :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ => by simp⟩

end GlobalTheory.SatakeBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactModStabilizer
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.PairingOne

section Alg
variable {k : Type*} [Field k] {m : Type*} [Fintype m] [DecidableEq m]

end Alg

variable {k : Type*} [Field k] [ValuativeRel k] {m : Type*} [Fintype m] [DecidableEq m]

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isCompact_bounded (t : ValueGroupWithZero k) :
    IsCompact {w : GL m k | (∀ a b, valuation k (w.val a b) ≤ t) ∧ ∀ a b, valuation k ((w⁻¹).val a b) ≤ t} := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hK : IsCompact {A : Matrix m m k | ∀ i j, valuation k (A i j) ≤ t} := by
    have h : IsCompact (Set.pi Set.univ fun _ : m => Set.pi Set.univ fun _ : m => {x : k | valuation k x ≤ t}) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k t
    have e : {A : Matrix m m k | ∀ i j, valuation k (A i j) ≤ t} =
        (Set.pi Set.univ fun _ : m => Set.pi Set.univ fun _ : m => {x : k | valuation k x ≤ t}) :=
      Set.ext fun x => ⟨fun hx i _ j _ => hx i j, fun hx i j => hx i trivial j trivial⟩
    rw [e]; exact h
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix m m k)).isCompact_preimage
    (hK.prod (hK.image MulOpposite.continuous_op))
  convert h using 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply,
    Set.mem_prod, (MulOpposite.op_injective).mem_set_image]

end GlobalTheory.PairingOne
end
end
