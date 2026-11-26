module

public import Mathlib

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideFurther
theorem UpperTheory.Reformulated.B.Yla6.main :
    ∀ {a b c d : Type} [inst : Fintype b] [inst_1 : Fintype c] (A : Matrix a b ℂ) (M : Matrix b c ℂ) (B : Matrix c d ℂ)
      {α μ β : ℝ},
      (∀ (i : a) (j : b), ‖A i j‖ ≤ α) →
        (∀ (i : b) (j : c), ‖M i j‖ ≤ μ) →
          (∀ (i : c) (j : d), ‖B i j‖ ≤ β) →
            ∀ (i : a) (j : d), ‖(A * M * B) i j‖ ≤ (↑(Fintype.card b) : ℝ) * (↑(Fintype.card c) : ℝ) * (α * μ * β) := by
  intro a b c d _ _ A M B α μ β hA hM hB i j
  have h1 : ‖(A * M * B) i j‖ ≤ ∑ l : c, ∑ k : b, ‖A i k‖ * ‖M k l‖ * ‖B l j‖ := by
    simp_rw [Matrix.mul_apply, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => (norm_sum_le _ _).trans ?_)
    simp [norm_mul]
  have h2 : ∀ l : c, ∀ k : b, ‖A i k‖ * ‖M k l‖ * ‖B l j‖ ≤ α * μ * β := by
    intro l k
    have ha : 0 ≤ α := (norm_nonneg _).trans (hA i k)
    have hm : 0 ≤ μ := (norm_nonneg _).trans (hM k l)
    exact mul_le_mul (mul_le_mul (hA i k) (hM k l) (norm_nonneg _) ha) (hB l j) (norm_nonneg _)
      (mul_nonneg ha hm)
  calc ‖(A * M * B) i j‖ ≤ ∑ l : c, ∑ k : b, ‖A i k‖ * ‖M k l‖ * ‖B l j‖ := h1
    _ ≤ ∑ _l : c, ∑ _k : b, α * μ * β :=
        Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun k _ => h2 l k
    _ = (↑(Fintype.card b) : ℝ) * (↑(Fintype.card c) : ℝ) * (α * μ * β) := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntRing
noncomputable def UpperTheory.Reformulated.B.CapelliIdentity₂.intRing :
    (p : ℕ) → [inst : Fact (Nat.Prime p)] → Subring ℂ_[p] :=
  fun p _ =>
    { carrier := {x : ℂ_[p] | ‖x‖ ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        have ha' : ‖a‖ ≤ 1 := ha
        have hb' : ‖b‖ ≤ 1 := hb
        show ‖a * b‖ ≤ 1
        rw [norm_mul]
        exact mul_le_one₀ ha' (norm_nonneg b) hb'
      one_mem' := by
        show ‖(1 : ℂ_[p])‖ ≤ 1
        exact norm_one.le
      add_mem' := fun {a b} ha hb =>
        (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
      zero_mem' := by
        show ‖(0 : ℂ_[p])‖ ≤ 1
        rw [norm_zero]
        exact zero_le_one
      neg_mem' := fun {a} ha => by
        show ‖-a‖ ≤ 1
        rw [norm_neg]
        exact ha }
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BallSubgroup
noncomputable def UpperTheory.Reformulated.B.BallSubgroup.ball :
    (L : Type) → [inst : NontriviallyNormedField L] → [IsUltrametricDist L] → ValuationSubring L :=
  fun L _ _ =>
    { carrier := {x : L | ‖x‖ ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [norm_mul]
        exact mul_le_one₀ ha (norm_nonneg b) hb
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rwa [norm_neg]
      mem_or_inv_mem' := fun x => by
        simp only [Set.mem_setOf_eq]
        rcases le_total ‖x‖ 1 with h | h
        · exact Or.inl h
        · right
          rw [norm_inv]
          exact inv_le_one_of_one_le₀ h }
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CardinalityOfBand
noncomputable def UpperTheory.Reformulated.B.CardinalityOfBand.band :
    (m : Nat) → Nat → Nat → Fin m → Bool :=
    fun (m a b : Nat) (i : Fin m) ↦
      @Decidable.decide (And (@LE.le Nat instLENat a (@Fin.val m i)) (@LT.lt Nat instLTNat (@Fin.val m i) b))
        (@instDecidableAnd (@LE.le Nat instLENat a (@Fin.val m i)) (@LT.lt Nat instLTNat (@Fin.val m i) b)
          (a.decLe (@Fin.val m i)) ((@Fin.val m i).decLt b))

theorem UpperTheory.Reformulated.B.CardinalityOfBand.card_band :
    ∀ (m a b : Nat),
      @LE.le Nat instLENat b m →
        @Eq Nat (@Finset.card (Fin m) {i : Fin m | @Eq Bool (UpperTheory.Reformulated.B.CardinalityOfBand.band m a b i) Bool.true})
          (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) b a) := by
  intro m a b hb
  rw [← Nat.card_Ico a b, ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext x
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
    Finset.mem_Ico, UpperTheory.Reformulated.B.CardinalityOfBand.band, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hx
    exact ⟨⟨x, lt_of_lt_of_le hx.2 hb⟩, hx, rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InPApplyEqZero
noncomputable def UpperTheory.Reformulated.B.Qh16.Jm :
    {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ :=
    fun {n : ℕ} (ε : Fin n → Bool) ↦ Matrix.diagonal fun (a : Fin n) ↦ if ε a = Bool.true then (1 : ℂ) else (-1 : ℂ)

noncomputable def UpperTheory.Reformulated.B.Qh16.inG :
    {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ → Prop :=
    fun {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) ↦
      X.conjTranspose * UpperTheory.Reformulated.B.Qh16.Jm ε + UpperTheory.Reformulated.B.Qh16.Jm ε * X = (0 : Matrix (Fin n) (Fin n) ℂ)

noncomputable def UpperTheory.Reformulated.B.Qh16.inP :
    {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ → Prop :=
    fun {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) ↦
      UpperTheory.Reformulated.B.Qh16.inG ε X ∧ X * UpperTheory.Reformulated.B.Qh16.Jm ε = -(UpperTheory.Reformulated.B.Qh16.Jm ε * X)

theorem UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero :
    ∀ {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ},
      UpperTheory.Reformulated.B.Qh16.inP ε X → ∀ {a b : Fin n}, ε a = ε b → X a b = (0 : ℂ) := by
  intro n ε X h a b hab
  have h1 := congrFun (congrFun h.2 a) b
  unfold UpperTheory.Reformulated.B.Qh16.Jm at h1
  rw [Matrix.neg_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, hab] at h1
  split_ifs at h1
  · linear_combination (1 / 2 : ℂ) * h1
  · linear_combination (-1 / 2 : ℂ) * h1
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideLast
theorem UpperTheory.Reformulated.B.Yoa3.exists_perm_of_map_eq :
    ∀ {n : ℕ} {z z' : Fin n → ℂˣ},
      Multiset.map (fun (i : Fin n) ↦ (↑(z i) : ℂ)) Finset.univ.val =
          Multiset.map (fun (i : Fin n) ↦ (↑(z' i) : ℂ)) Finset.univ.val →
        ∃ (σ : Equiv.Perm (Fin n)), z' = z ∘ (⇑σ : Fin n → Fin n) := by
  classical
  intro n z z' h
  have key : ∀ (w : Fin n → ℂˣ) (c : ℂ),
      Fintype.card {i : Fin n // (w i : ℂ) = c} =
        Multiset.count c (Multiset.map (fun (i : Fin n) ↦ (↑(w i) : ℂ)) Finset.univ.val) := by
    intro w c
    rw [Multiset.count_map, Fintype.card_subtype, Finset.card_def, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr (fun _ _ => eq_comm)
  have hc : ∀ c : ℂ, Fintype.card {i : Fin n // (z' i : ℂ) = c} =
      Fintype.card {i : Fin n // (z i : ℂ) = c} := by
    intro c
    rw [key, key, h]
  let e : ∀ c : ℂ, {i : Fin n // (z' i : ℂ) = c} ≃ {i : Fin n // (z i : ℂ) = c} :=
    fun c => Fintype.equivOfCardEq (hc c)
  refine ⟨Equiv.ofFiberEquiv (f := fun i => (z' i : ℂ)) (g := fun i => (z i : ℂ)) e, ?_⟩
  funext i
  apply Units.ext
  exact (Equiv.ofFiberEquiv_map (f := fun i => (z' i : ℂ)) (g := fun i => (z i : ℂ)) e i).symm
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormRingALe
noncomputable def UpperTheory.Reformulated.B.Qi27.muPrime :
    (l : ℕ) → [inst : Fact (Nat.Prime l)] → Set ℂ_[l] :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ {ζ : ℂ_[l] | ∃ (n : ℕ), (0 : ℕ) < n ∧ ¬l ∣ n ∧ ζ ^ n = (1 : ℂ_[l])}

noncomputable def UpperTheory.Reformulated.B.Qi27.ringA :
    (l : ℕ) → [inst : Fact (Nat.Prime l)] → Subring ℂ_[l] :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ Subring.closure (UpperTheory.Reformulated.B.Qi27.muPrime l)

theorem UpperTheory.Reformulated.B.Qi27.norm_ringA_le :
    ∀ {l : ℕ} [hl : Fact (Nat.Prime l)] {x : ℂ_[l]}, x ∈ UpperTheory.Reformulated.B.Qi27.ringA l → ‖x‖ ≤ (1 : ℝ) := by
  intro l hl x hx
  unfold UpperTheory.Reformulated.B.Qi27.ringA at hx
  induction hx using Subring.closure_induction with
  | mem y hy =>
    obtain ⟨n, hn, -, h⟩ := hy
    have h1 : ‖y‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg y) hn.ne').1 h1).le
  | zero => simp
  | one => simp
  | add a b _ _ ha hb => exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  | neg a _ ha => simpa using ha
  | mul a b _ _ ha hb =>
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg b) hb
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MapCastMono
noncomputable def UpperTheory.Reformulated.B.Qh31.vR :
    {K : Type} → [inst : Field K] → AddValuation K (WithTop ℚ) → K → WithTop ℝ :=
    fun {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) (x : K) ↦
      WithTop.map (fun (n : ℚ) ↦ (↑n : ℝ)) ((v : K → WithTop ℚ) x)

noncomputable def UpperTheory.Reformulated.B.Qh31.vge :
    {K : Type} → [inst : Field K] → AddValuation K (WithTop ℚ) → ℝ → K → Prop :=
    fun {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) (a : ℝ) (x : K) ↦ (↑a : WithTop ℝ) ≤ UpperTheory.Reformulated.B.Qh31.vR v x

private theorem UpperTheory.Reformulated.B.Qh31.map_cast_mono :
    Monotone (WithTop.map (fun (n : ℚ) ↦ (↑n : ℝ))) :=
  Monotone.withTop_map (fun _ _ h ↦ Rat.cast_le.mpr h)

theorem UpperTheory.Reformulated.B.Qh31.vge_sum :
    ∀ {K : Type} [inst : Field K] (v : AddValuation K (WithTop ℚ)) {ι : Type} {a : ℝ} (s : Finset ι) (f : ι → K),
      (∀ i ∈ s, UpperTheory.Reformulated.B.Qh31.vge v a (f i)) → UpperTheory.Reformulated.B.Qh31.vge v a (∑ i ∈ s, f i) := by
  intro K _ v ι a s f h
  refine Finset.sum_induction f (UpperTheory.Reformulated.B.Qh31.vge v a) ?_ ?_ h
  · intro x y hx hy
    unfold UpperTheory.Reformulated.B.Qh31.vge UpperTheory.Reformulated.B.Qh31.vR at *
    rcases min_le_iff.mp (v.map_add x y) with hxy | hxy
    · exact hx.trans (UpperTheory.Reformulated.B.Qh31.map_cast_mono hxy)
    · exact hy.trans (UpperTheory.Reformulated.B.Qh31.map_cast_mono hxy)
  · unfold UpperTheory.Reformulated.B.Qh31.vge UpperTheory.Reformulated.B.Qh31.vR
    rw [v.map_zero, WithTop.map_top]
    exact le_top
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerBis
noncomputable def UpperTheory.Reformulated.B.PadicComplexRingOfIntegers.intRing :
    (p : ℕ) → [inst : Fact (Nat.Prime p)] → Subring ℂ_[p] :=
  fun p _ =>
    { carrier := {x : ℂ_[p] | ‖x‖ ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        have ha' : ‖a‖ ≤ 1 := ha
        have hb' : ‖b‖ ≤ 1 := hb
        show ‖a * b‖ ≤ 1
        rw [norm_mul]
        exact mul_le_one₀ ha' (norm_nonneg b) hb'
      one_mem' := by
        show ‖(1 : ℂ_[p])‖ ≤ 1
        exact norm_one.le
      add_mem' := fun {a b} ha hb => by
        have ha' : ‖a‖ ≤ 1 := ha
        have hb' : ‖b‖ ≤ 1 := hb
        show ‖a + b‖ ≤ 1
        exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha' hb')
      zero_mem' := by
        show ‖(0 : ℂ_[p])‖ ≤ 1
        rw [norm_zero]
        exact zero_le_one
      neg_mem' := fun {a} ha => by
        have ha' : ‖a‖ ≤ 1 := ha
        show ‖-a‖ ≤ 1
        rwa [norm_neg] }
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FInt
namespace YhaHelp
open MeasureTheory Set Real

private lemma F_int {c : ℝ} (hc : 0 < c) :
    Integrable ((Ici (0:ℝ)).indicator (fun x : ℝ => exp (-c * x))) := by
  rw [integrable_indicator_iff measurableSet_Ici]
  exact (exp_neg_integrableOn_Ioi (-1) hc).mono_set (fun x hx => by
    simp only [mem_Ici, mem_Ioi] at *; linarith)

end YhaHelp

theorem UpperTheory.Reformulated.B.Yha4.main :
    ∀ {c : ℝ}, (0 : ℝ) < c → MeasureTheory.Integrable (fun (x : ℝ) ↦ Real.exp (-c * |x|)) MeasureTheory.MeasureSpace.volume := by
  intro c hc
  have hF := YhaHelp.F_int hc
  have hG := hF.comp_neg
  refine (hF.add hG).mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simp only [Pi.add_apply, Set.indicator, Set.mem_Ici, Left.nonneg_neg_iff]
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h, if_pos h]
    split_ifs
    · linarith [Real.exp_pos (-c * -x)]
    · simp
  · rw [abs_of_neg h, if_neg (not_le.mpr h), if_pos h.le]
    simp
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BallRing
noncomputable def UpperTheory.Reformulated.B.ClosedUnitBallSubring.ballRing :
    (K : Type) → [inst : NormedField K] → [IsUltrametricDist K] → Subring K :=
  fun K _ _ =>
    { carrier := {x : K | ‖x‖ ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        have ha' : ‖a‖ ≤ 1 := ha
        have hb' : ‖b‖ ≤ 1 := hb
        show ‖a * b‖ ≤ 1
        rw [norm_mul]
        exact mul_le_one₀ ha' (norm_nonneg b) hb'
      one_mem' := by
        show ‖(1 : K)‖ ≤ 1
        exact norm_one.le
      add_mem' := fun {a b} ha hb => by
        have ha' : ‖a‖ ≤ 1 := ha
        have hb' : ‖b‖ ≤ 1 := hb
        show ‖a + b‖ ≤ 1
        exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha' hb')
      zero_mem' := by
        show ‖(0 : K)‖ ≤ 1
        rw [norm_zero]
        exact zero_le_one
      neg_mem' := fun {a} ha => by
        have ha' : ‖a‖ ≤ 1 := ha
        show ‖-a‖ ≤ 1
        rw [norm_neg]
        exact ha' }
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FirstStatementA
theorem UpperTheory.Reformulated.B.FirstStatementA.main :
    ∀ {E : Type} [inst : Field E]
    [NumberField E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)),
    ∀ x ∈ Submodule.span E (↑L : Set (Fin n → E)), ∃ (m : ℤ), m ≠ (0 : ℤ) ∧ m • x ∈ L := by
  intro E _ _ n L x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ h1 h2 =>
    obtain ⟨a, ha, hya⟩ := h1
    obtain ⟨b, hb, hzb⟩ := h2
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have e : (a * b) • (y + z) = b • (a • y) + a • (b • z) := by
      rw [smul_add, mul_smul, mul_smul, smul_comm a b y]
    rw [e]
    exact L.add_mem (L.smul_of_tower_mem b hya) (L.smul_of_tower_mem a hzb)
  | smul c y _ h =>
    obtain ⟨a, ha, hya⟩ := h
    have halg : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)
    obtain ⟨d, hd, hint⟩ := halg.exists_integral_multiple
    refine ⟨d * a, mul_ne_zero hd ha, ?_⟩
    let r : NumberField.RingOfIntegers E := ⟨d • c, hint⟩
    have e : (d * a) • (c • y) = r • (a • y) := by
      have : r • (a • y) = (d • c) • (a • y) := rfl
      rw [this, mul_smul, smul_comm a c y, smul_assoc]
    rw [e]
    exact L.smul_mem r hya
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RightCosetSpaceCompact
@[reducible] noncomputable def UpperTheory.Reformulated.B.RightCosetSpaceCompact.RightCosetSpace.{u_1} :
    {G : Type u_1} → [inst : Group G] → Subgroup G → Type u_1 :=
    fun {G : Type u_1} [Group G] (Γ : Subgroup G) ↦ Quotient (MulAction.orbitRel (↥Γ) G)

noncomputable def UpperTheory.Reformulated.B.RightCosetSpaceCompact.mk.{u_1} :
    {G : Type u_1} → [inst : Group G] → (Γ : Subgroup G) → G → UpperTheory.Reformulated.B.RightCosetSpaceCompact.RightCosetSpace Γ :=
    fun {G : Type u_1} [Group G] (Γ : Subgroup G) ↦ Quotient.mk (MulAction.orbitRel (↥Γ) G)

theorem UpperTheory.Reformulated.B.RightCosetSpaceCompact.exists_isCompact_subset_mk_image.{u_1} :
    ∀ {G : Type u_1} [inst : Group G] (Γ : Subgroup G) [inst_1 : TopologicalSpace G] [IsTopologicalGroup G]
      [LocallyCompactSpace G] {K : Set (UpperTheory.Reformulated.B.RightCosetSpaceCompact.RightCosetSpace Γ)},
      IsCompact K → ∃ (D : Set G), IsCompact D ∧ K ⊆ UpperTheory.Reformulated.B.RightCosetSpaceCompact.mk Γ '' D := by
  intro G _ Γ _ _ _ K hK
  have hopen : IsOpenMap (UpperTheory.Reformulated.B.RightCosetSpaceCompact.mk Γ) :=
    isOpenMap_quotient_mk'_mul (Γ := ↥Γ) (T := G)
  refine hK.induction_on
    (p := fun S => ∃ D : Set G, IsCompact D ∧ S ⊆ UpperTheory.Reformulated.B.RightCosetSpaceCompact.mk Γ '' D) ?_ ?_ ?_ ?_
  · exact ⟨∅, isCompact_empty, Set.empty_subset _⟩
  · rintro s t hst ⟨D, hD, htD⟩
    exact ⟨D, hD, hst.trans htD⟩
  · rintro s t ⟨D, hD, hsD⟩ ⟨E, hE, htE⟩
    refine ⟨D ∪ E, hD.union hE, ?_⟩
    rw [Set.image_union]
    exact Set.union_subset_union hsD htE
  · intro x _
    obtain ⟨g, rfl⟩ : ∃ g : G, UpperTheory.Reformulated.B.RightCosetSpaceCompact.mk Γ g = x := Quotient.exists_rep x
    obtain ⟨D, hD, hgD⟩ := exists_compact_mem_nhds g
    exact ⟨_, mem_nhdsWithin_of_mem_nhds (hopen.image_mem_nhds hgD), D, hD, subset_rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerLast
theorem UpperTheory.Reformulated.B.Qf31.isCompact_box :
    ∀ {L : Type} [inst : NontriviallyNormedField L] [IsUltrametricDist L] {m : ℕ}
    [ProperSpace L] (c : Matrix (Fin m) (Fin m) L) (r : ℝ),
    IsCompact
      {g : GL (Fin m) L |
        (∀ (i j : Fin m), ‖(↑g : Matrix (Fin m) (Fin m) L) i j - c i j‖ ≤ r) ∧
          ∀ (i j : Fin m), ‖(↑g⁻¹ : Matrix (Fin m) (Fin m) L) i j - c i j‖ ≤ r} := by
  intro L _ _ m _ c r
  have hK : IsCompact {A : Matrix (Fin m) (Fin m) L | ∀ i j, ‖A i j - c i j‖ ≤ r} := by
    have h : IsCompact (Set.univ.pi fun i : Fin m =>
        Set.univ.pi fun j : Fin m => Metric.closedBall (c i j) r) :=
      isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_closedBall (c i j) r
    have e : {A : Matrix (Fin m) (Fin m) L | ∀ i j, ‖A i j - c i j‖ ≤ r} =
        (Set.univ.pi fun i : Fin m =>
          Set.univ.pi fun j : Fin m => Metric.closedBall (c i j) r) := by
      ext A
      constructor
      · intro hA i _ j _
        exact mem_closedBall_iff_norm.2 (hA i j)
      · intro hA i j
        exact mem_closedBall_iff_norm.1 (hA i (Set.mem_univ i) j (Set.mem_univ j))
    rw [e]
    exact h
  have hK' : IsCompact (MulOpposite.unop ⁻¹'
      {A : Matrix (Fin m) (Fin m) L | ∀ i j, ‖A i j - c i j‖ ≤ r}) :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin m) (Fin m) L)).symm.isCompact_preimage.2 hK
  exact (Units.isClosedEmbedding_embedProduct
    (α := Matrix (Fin m) (Fin m) L)).isCompact_preimage (hK.prod hK')
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PolyInMul
noncomputable def UpperTheory.Reformulated.B.Qk18.PolyIn :
    {R : Type} → [inst : Ring R] → [Algebra ℂ R] → (ℂ → R) → ℕ → Prop :=
    fun {R : Type} [Ring R] [Algebra ℂ R] (f : ℂ → R) (d : ℕ) ↦
      ∃ (a : ℕ → R), ∀ (s : ℂ), f s = ∑ k ∈ Finset.range (d + (1 : ℕ)), s ^ k • a k

theorem UpperTheory.Reformulated.B.Qk18.polyIn_mul :
    ∀ {R : Type} [inst : Ring R] [inst_1 : Algebra ℂ R] {f g : ℂ → R} {d₁ d₂ : ℕ},
      UpperTheory.Reformulated.B.Qk18.PolyIn f d₁ →
        UpperTheory.Reformulated.B.Qk18.PolyIn g d₂ → UpperTheory.Reformulated.B.Qk18.PolyIn (fun (t : ℂ) ↦ f t * g t) (d₁ + d₂) := by
  intro R _ _ f g d₁ d₂ hf hg
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨fun n => ∑ i ∈ Finset.range (d₁ + 1), ∑ j ∈ Finset.range (d₂ + 1),
    if i + j = n then a i * b j else 0, fun s => ?_⟩
  show f s * g s = _
  rw [ha s, hb s, Finset.sum_mul_sum]
  simp only [Finset.smul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hmem : i + j ∈ Finset.range (d₁ + d₂ + 1) := by
    rw [Finset.mem_range] at hi hj ⊢
    omega
  rw [Finset.sum_eq_single_of_mem (i + j) hmem]
  · rw [if_pos rfl, smul_mul_smul_comm, pow_add]
  · intro k _ hk
    rw [if_neg (Ne.symm hk), smul_zero]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExLift
theorem UpperTheory.Reformulated.B.Qj6.ex_lift :
    ∀ {M Ω C : Type} [inst : Field M] [NumberField M] [inst_2 : Field Ω]
    [CharZero Ω] [IsAlgClosed Ω] [inst_5 : Field C] [CharZero C] (j : Ω →+* C) (f : M →+* C),
    ∃ (g : M →+* Ω), ∀ (x : M), (j : Ω → C) ((g : M → Ω) x) = (f : M → C) x := by
  intro M Ω C _ _ _ _ _ _ _ j f
  have key : ∀ x : M, f x ∈ j.fieldRange := by
    intro x
    have hx : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
    have hs : ((minpoly ℚ x).map (algebraMap ℚ Ω)).Splits := IsAlgClosed.splits _
    have hm : ((minpoly ℚ x).map (algebraMap ℚ Ω)).map j = (minpoly ℚ x).map (algebraMap ℚ C) := by
      rw [Polynomial.map_map]
      congr 1
      exact Subsingleton.elim _ _
    have hne : ((minpoly ℚ x).map (algebraMap ℚ Ω)).map j ≠ 0 := by
      rw [hm]
      exact ((minpoly.monic hx).map _).ne_zero
    have hr : f x ∈ (((minpoly ℚ x).map (algebraMap ℚ Ω)).map j).roots := by
      rw [Polynomial.mem_roots hne, hm, Polynomial.IsRoot.def, Polynomial.eval_map_algebraMap]
      have h := Polynomial.aeval_algHom_apply f.toRatAlgHom x (minpoly ℚ x)
      rw [minpoly.aeval, map_zero] at h
      exact h
    rw [hs.roots_map, Multiset.mem_map] at hr
    obtain ⟨y, -, hy⟩ := hr
    exact ⟨y, hy⟩
  choose g hg using fun x => RingHom.mem_fieldRange.mp (key x)
  refine ⟨{ toFun := g, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hg⟩
  · exact j.injective (by simp [hg])
  · intro a b
    exact j.injective (by simp [hg])
  · exact j.injective (by simp [hg])
  · intro a b
    exact j.injective (by simp [hg])
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.GradedSpanProducts
noncomputable def UpperTheory.Reformulated.B.GradedSpanProducts.gradedSpan.{u_1} :
    {Ω : Type u_1} → [inst : CommRing Ω] → {q r : ℕ} → (Fin q → Ω) → (Fin r → ℕ) → (Fin r → Ω) → ℕ → AddSubgroup Ω :=
    fun {Ω : Type u_1} [CommRing Ω] {q r : ℕ} (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω) (n : ℕ) ↦
      AddSubgroup.closure
        {x : Ω | ∃ (l : Fin r) (μ : Fin q → ℕ), d l + ∑ j : Fin q, μ j = n ∧ x = t l * ∏ j : Fin q, w j ^ μ j}

@[reducible] noncomputable def UpperTheory.Reformulated.B.GradedSpanProducts.pc :
    {Ω : Type} → [inst : Field Ω] → {q : ℕ} → (Fin q → Ω) → ℕ → AddSubgroup Ω :=
    fun {Ω : Type} [Field Ω] {q : ℕ} (w : Fin q → Ω) (n : ℕ) ↦
      UpperTheory.Reformulated.B.GradedSpanProducts.gradedSpan w (fun (x : Fin (1 : ℕ)) ↦ (0 : ℕ)) (fun (x : Fin (1 : ℕ)) ↦ (1 : Ω)) n

theorem UpperTheory.Reformulated.B.GradedSpanProducts.pc_mul :
    ∀ {Ω : Type} [inst : Field Ω] {q : ℕ} (w : Fin q → Ω) {a b : ℕ} {x z : Ω},
      x ∈ UpperTheory.Reformulated.B.GradedSpanProducts.pc w a → z ∈ UpperTheory.Reformulated.B.GradedSpanProducts.pc w b → x * z ∈ UpperTheory.Reformulated.B.GradedSpanProducts.pc w (a + b) := by
  intro Ω _ q w a b x z hx hz
  unfold UpperTheory.Reformulated.B.GradedSpanProducts.pc UpperTheory.Reformulated.B.GradedSpanProducts.gradedSpan at *
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨l, μ, hμ, rfl⟩ := hx
      obtain ⟨_, ν, hν, rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨l, fun j => μ j + ν j, ?_, ?_⟩
      · simp only [zero_add] at hμ hν ⊢
        rw [Finset.sum_add_distrib, hμ, hν]
      · simp only [one_mul, pow_add, Finset.prod_mul_distrib]
    | zero => rw [mul_zero]; exact AddSubgroup.zero_mem _
    | add y z _ _ h1 h2 => rw [mul_add]; exact AddSubgroup.add_mem _ h1 h2
    | neg z _ h => rw [mul_neg]; exact AddSubgroup.neg_mem _ h
  | zero => rw [zero_mul]; exact AddSubgroup.zero_mem _
  | add x y _ _ h1 h2 => rw [add_mul]; exact AddSubgroup.add_mem _ h1 h2
  | neg x _ h => rw [neg_mul]; exact AddSubgroup.neg_mem _ h
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SmulMemOfSpanEqTop
theorem UpperTheory.Reformulated.B.SmulMemOfSpanEqTop.exists_ne_zero_smul_mem_of_span_eq_top :
    ∀ {A : Type} [inst : CommRing A] [IsDomain A]
    {K : Type} [inst_2 : Field K] [inst_3 : Algebra A K] [IsFractionRing A K] {V : Type} [inst_5 : AddCommGroup V]
    [inst_6 : _root_.Module K V] [inst_7 : _root_.Module A V] [IsScalarTower A K V] (M : Submodule A V),
    Submodule.span K (↑M : Set V) = ⊤ → ∀ (v : V), ∃ (d : A), d ≠ (0 : A) ∧ d • v ∈ M := by
  intro A _ _ K _ _ _ V _ _ _ _ M hM v
  have hv : v ∈ Submodule.span K (↑M : Set V) := hM ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact M.zero_mem⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨a, ha, hax⟩ := ihx
    obtain ⟨b, hb, hby⟩ := ihy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact M.smul_mem b hax
    · rw [mul_smul]
      exact M.smul_mem a hby
  | smul k x _ ih =>
    obtain ⟨a, ha, hax⟩ := ih
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := A) k
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hqK : algebraMap A K q ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hq0
    refine ⟨a * q, mul_ne_zero ha hq0, ?_⟩
    have key : (a * q) • ((algebraMap A K p / algebraMap A K q) • x) = p • (a • x) := by
      rw [← algebraMap_smul K (a * q), ← algebraMap_smul K a, ← algebraMap_smul K p,
        smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [key]
    exact M.smul_mem p hax
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConvSqLe
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qj8.E :
    ℕ → Type :=
    fun (d : ℕ) ↦ EuclideanSpace ℝ (Fin d)

theorem UpperTheory.Reformulated.B.Qj8.conv_sq_le :
    ∀ {d : ℕ} (k g : UpperTheory.Reformulated.B.Qj8.E d → ENNReal),
      Measurable k →
        Measurable g →
          ∀ (ξ : UpperTheory.Reformulated.B.Qj8.E d),
            (∫⁻ (η : UpperTheory.Reformulated.B.Qj8.E d), k (ξ - η) * g η) ^ (2 : ℕ) ≤
              (∫⁻ (ζ : UpperTheory.Reformulated.B.Qj8.E d), k ζ) * ∫⁻ (η : UpperTheory.Reformulated.B.Qj8.E d), k (ξ - η) * g η ^ (2 : ℕ) := by
  intro d k g hk hg ξ
  have hk' : Measurable (fun η : UpperTheory.Reformulated.B.Qj8.E d => k (ξ - η)) :=
    hk.comp (measurable_const.sub measurable_id)
  have hh : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hsq : ∀ a : ENNReal, (a ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = a := by
    intro a
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hsq' : ∀ a : ENNReal, (a ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = a := by
    intro a
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have H := ENNReal.lintegral_mul_norm_pow_le (μ := MeasureTheory.volume)
    (f := fun η : UpperTheory.Reformulated.B.Qj8.E d => k (ξ - η))
    (g := fun η : UpperTheory.Reformulated.B.Qj8.E d => k (ξ - η) * g η ^ (2 : ℕ))
    hk'.aemeasurable (hk'.mul (hg.pow_const 2)).aemeasurable hh hh (by norm_num)
  have hpt : ∀ η : UpperTheory.Reformulated.B.Qj8.E d,
      k (ξ - η) ^ (1 / 2 : ℝ) * (k (ξ - η) * g η ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = k (ξ - η) * g η := by
    intro η
    rw [ENNReal.mul_rpow_of_nonneg _ _ hh, hsq', ← mul_assoc, ← pow_two, hsq]
  simp only [hpt] at H
  rw [MeasureTheory.lintegral_sub_left_eq_self k ξ] at H
  calc _ ≤ _ := pow_le_pow_left₀ bot_le H 2
    _ = _ := by rw [mul_pow, hsq, hsq]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.KeyLemmaStatement
namespace CoprimeTimesDvdPowFactorization

private theorem key (g m : ℕ) (hm : 0 < m) :
    (m / Nat.gcd m (g ^ m)).Coprime g := by
  set d := Nat.gcd m (g ^ m) with hd
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left _ hm
  have hcop : (m / d).Coprime (g ^ m / d) := Nat.coprime_div_gcd_div_gcd hdpos
  apply Nat.coprime_of_dvd
  intro p hp hpc hpg
  have hpn : ¬ p ∣ g ^ m / d := by
    intro h
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.Coprime.coprime_dvd_left hpc hcop) h
  have hdg : d ∣ g ^ m := Nat.gcd_dvd_right _ _
  have hdm : d ∣ m := Nat.gcd_dvd_left _ _
  have hpm : p ^ m ∣ d * (g ^ m / d) := by
    rw [Nat.mul_div_cancel' hdg]
    exact pow_dvd_pow_of_dvd hpg m
  have hcp : Nat.Coprime (p ^ m) (g ^ m / d) :=
    Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn)
  have hpd : p ^ m ∣ d := hcp.dvd_of_dvd_mul_right hpm
  have hall : p ^ m * p ∣ d * (m / d) := Nat.mul_dvd_mul hpd hpc
  rw [Nat.mul_div_cancel' hdm, ← pow_succ] at hall
  have hle : p ^ (m + 1) ≤ m := Nat.le_of_dvd hm hall
  have h1 : m < 2 ^ m := Nat.lt_two_pow_self
  have h2 : 2 ^ m ≤ p ^ m := Nat.pow_le_pow_left hp.two_le m
  have h3 : p ^ m ≤ p ^ (m + 1) := Nat.pow_le_pow_right hp.pos (Nat.le_succ m)
  omega

end CoprimeTimesDvdPowFactorization

theorem UpperTheory.Reformulated.B.ExistsCoprimeMulDvdPow.main :
    ∀ (g m : ℕ),
    (0 : ℕ) < m → ∃ (c : ℕ) (d : ℕ), m = c * d ∧ c.Coprime g ∧ d ∣ g ^ m := by
  intro g m hm
  refine ⟨m / Nat.gcd m (g ^ m), Nat.gcd m (g ^ m), ?_, CoprimeTimesDvdPowFactorization.key g m hm, Nat.gcd_dvd_right _ _⟩
  exact (Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsExpansion
private lemma UpperTheory.Reformulated.B.Qn12.step {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (y c : ι → R) (p e x a : R) (j : ι) (hy : y j = x - a) (hc : p = e + ∑ i, c i * y i) :
    p * x = e * a + ∑ i, (c i * a + if i = j then p else 0) * y i := by
  have h1 : ∑ i, (c i * a + if i = j then p else 0) * y i = (∑ i, c i * y i) * a + p * y j := by
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Finset.sum_mul, mul_right_comm]
  rw [h1, hy]
  linear_combination a * hc

private lemma UpperTheory.Reformulated.B.Qn12.step_add {R ι : Type*} [CommRing R] [Fintype ι]
    (y c d : ι → R) (p r e f : R) (hc : p = e + ∑ i, c i * y i) (hd : r = f + ∑ i, d i * y i) :
    p + r = (e + f) + ∑ i, (c i + d i) * y i := by
  simp only [add_mul, Finset.sum_add_distrib]
  linear_combination hc + hd

theorem UpperTheory.Reformulated.B.Qn12.exists_expansion :
    ∀ {n : ℕ} (q : Fin n → ℂ)
    (p : MvPolynomial (Fin n) ℂ),
    ∃ (c : Fin n → MvPolynomial (Fin n) ℂ),
      p =
        (MvPolynomial.C : ℂ → MvPolynomial (Fin n) ℂ) ((MvPolynomial.eval q : MvPolynomial (Fin n) ℂ → ℂ) p) +
          ∑ i : Fin n, c i * (MvPolynomial.X i - (MvPolynomial.C : ℂ → MvPolynomial (Fin n) ℂ) (q i)) := by
  intro n q p
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨0, by simp⟩
  | add p r hp hr =>
    obtain ⟨c, hc⟩ := hp
    obtain ⟨d, hd⟩ := hr
    refine ⟨fun i => c i + d i, ?_⟩
    rw [map_add (f := _), map_add (f := _)]
    exact UpperTheory.Reformulated.B.Qn12.step_add _ c d p r _ _ hc hd
  | mul_X p j hp =>
    obtain ⟨c, hc⟩ := hp
    refine ⟨fun i => c i * MvPolynomial.C (q j) + if i = j then p else 0, ?_⟩
    rw [map_mul, MvPolynomial.eval_X, map_mul]
    exact UpperTheory.Reformulated.B.Qn12.step (fun i => MvPolynomial.X i - MvPolynomial.C (q i)) c p _ _ _ j rfl hc
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqOneOfForallZpow
private theorem UpperTheory.Reformulated.B.Qk23.half_le_re {w : ℂ} (h : ‖w⁻¹ - 1‖ < 1) : (1 / 2 : ℝ) ≤ w.re := by
  have hw : w ≠ 0 := by
    rintro rfl
    simp at h
  have e : w⁻¹ - 1 = (1 - w) / w := by field_simp
  rw [e, norm_div, div_lt_one (norm_pos_iff.mpr hw)] at h
  have h2 : ‖1 - w‖ ^ 2 < ‖w‖ ^ 2 := by
    have := norm_nonneg (1 - w)
    nlinarith
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply] at h2
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im] at h2
  nlinarith

theorem UpperTheory.Reformulated.B.Qk23.eq_one_of_forall_zpow :
    ∀ {z : ℂ}, (∀ (k : ℤ), ‖z ^ k - (1 : ℂ)‖ < (1 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  by_contra hz
  have hd : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have hre : ∀ k : ℕ, (1 / 2 : ℝ) ≤ (z ^ k).re := by
    intro k
    apply UpperTheory.Reformulated.B.Qk23.half_le_re
    have := h (-(k : ℤ))
    rwa [zpow_neg, zpow_natCast] at this
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / ‖z - 1‖)
  rw [div_lt_iff₀ hd] at hn
  have h1 : (n : ℝ) * (1 / 2) ≤ ‖∑ k ∈ Finset.range n, z ^ k‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [Complex.re_sum]
    have := Finset.card_nsmul_le_sum (Finset.range n) (fun k => (z ^ k).re) (1 / 2 : ℝ)
      (fun k _ => hre k)
    rwa [Finset.card_range, nsmul_eq_mul] at this
  have h2 : ‖∑ k ∈ Finset.range n, z ^ k‖ * ‖z - 1‖ < 1 := by
    rw [← norm_mul, geom_sum_mul]
    have := h (n : ℤ)
    rwa [zpow_natCast] at this
  have h3 := mul_le_mul_of_nonneg_right h1 hd.le
  linarith
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BoxBounds
noncomputable def UpperTheory.Reformulated.B.BoxBounds.box :
    {K : Type} → [inst : Field K] → {i : ℕ} → K → Submodule (NumberField.RingOfIntegers K) (Fin i → K) :=
    fun {K : Type} [Field K] {i : ℕ} (c : K) ↦ Submodule.pi Set.univ fun (x : Fin i) ↦ NumberField.RingOfIntegers K ∙ c

theorem UpperTheory.Reformulated.B.BoxBounds.exists_box_le :
    ∀ {K : Type} [inst : Field K] [NumberField K] {i : ℕ} (L : Submodule (NumberField.RingOfIntegers K) (Fin i → K)),
      Submodule.span K (↑L : Set (Fin i → K)) = ⊤ →
        ∃ (e : NumberField.RingOfIntegers K),
          e ≠ (0 : NumberField.RingOfIntegers K) ∧
            UpperTheory.Reformulated.B.BoxBounds.box
                ((Algebra.algebraMap (NumberField.RingOfIntegers K) K : NumberField.RingOfIntegers K → K) e) ≤
              L := by
  intro K _ _ i L hL
  classical
  have h : ∀ j : Fin i, ∃ t : nonZeroDivisors (NumberField.RingOfIntegers K),
      (t : NumberField.RingOfIntegers K) • (Pi.single j (1 : K) : Fin i → K) ∈ L := by
    intro j
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
      (nonZeroDivisors (NumberField.RingOfIntegers K)) K (↑L : Set (Fin i → K))
      (Pi.single j (1 : K)) (hL ▸ Submodule.mem_top)
    rw [Submodule.span_eq] at ht
    exact ⟨t, ht⟩
  choose t ht using h
  refine ⟨∏ j, (t j : NumberField.RingOfIntegers K),
    Finset.prod_ne_zero_iff.mpr fun j _ => nonZeroDivisors.coe_ne_zero (t j), ?_⟩
  intro x hx
  rw [← Finset.univ_sum_single x]
  refine L.sum_mem fun j _ => ?_
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (Submodule.mem_pi.mp hx j (Set.mem_univ j))
  obtain ⟨u, hu⟩ : (t j : NumberField.RingOfIntegers K) ∣ ∏ k, (t k : NumberField.RingOfIntegers K) :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  have hj : (Pi.single j (x j) : Fin i → K)
      = (a * u) • (t j : NumberField.RingOfIntegers K) • (Pi.single j (1 : K) : Fin i → K) := by
    rw [← ha, hu, smul_smul, ← Pi.single_smul, Algebra.algebraMap_eq_smul_one, smul_smul]
    congr 2
    ring
  rw [hj]
  exact L.smul_mem _ (ht j)
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OddSpanVariable
theorem UpperTheory.Reformulated.B.PowerSeriesMemSpanIndexedVariables.ep_odd_span_X :
    ∀ {O σ ι : Type} [inst : CommRing O] (e : ι → σ) (s : Finset ι)
    (f : MvPowerSeries σ O),
    (∀ (n : σ →₀ ℕ),
        (∀ i ∈ s, (n : σ → ℕ) (e i) = (0 : ℕ)) → (MvPowerSeries.coeff n : MvPowerSeries σ O → O) f = (0 : O)) →
      f ∈ Ideal.span (Set.range fun (i : ι) ↦ MvPowerSeries.X (e i)) := by
  intro O σ ι inst e s
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro f hf
    have h0 : f = 0 := by
      ext n
      simpa using hf n (by simp)
    rw [h0]
    exact Ideal.zero_mem _
  | insert a s _ ih =>
    intro f hf
    let g : MvPowerSeries σ O := fun n => if n (e a) = 0 then MvPowerSeries.coeff n f else 0
    have hg : ∀ n : σ →₀ ℕ, MvPowerSeries.coeff n g
        = if n (e a) = 0 then MvPowerSeries.coeff n f else 0 := fun _ => rfl
    have h1 : g ∈ Ideal.span (Set.range fun (i : ι) ↦ (MvPowerSeries.X (e i) : MvPowerSeries σ O)) := by
      refine ih g fun n hn => ?_
      rw [hg]
      split_ifs with h
      · refine hf n fun i hi => ?_
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact h
        · exact hn i hi
      · rfl
    have h2 : (MvPowerSeries.X (e a) : MvPowerSeries σ O) ∣ f - g := by
      rw [MvPowerSeries.X_dvd_iff]
      intro n hn
      rw [map_sub, hg, if_pos hn, sub_self]
    have h3 : f - g ∈ Ideal.span
        (Set.range fun (i : ι) ↦ (MvPowerSeries.X (e i) : MvPowerSeries σ O)) :=
      Ideal.mem_of_dvd _ h2 (Ideal.subset_span ⟨a, rfl⟩)
    have h4 := Ideal.add_mem _ h3 h1
    rwa [sub_add_cancel] at h4
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PairedCharacterCondition
noncomputable def UpperTheory.Reformulated.B.PairedCharacterCondition.TrScale :
    Prop :=
    ∀ (K : Type) [inst : Field K] [NumberField K] (V : Type) [inst_2 : AddCommGroup V] [inst_3 : _root_.Module K V]
      [inst_4 : _root_.Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
      (M : Submodule (NumberField.RingOfIntegers K) V),
      Submodule.span K (↑M : Set V) = ⊤ → ∀ (f : V), ∃ (m : ℤ), m ≠ (0 : ℤ) ∧ (↑m : K) • f ∈ M

theorem UpperTheory.Reformulated.B.PairedCharacterCondition.tr_scale :
    UpperTheory.Reformulated.B.PairedCharacterCondition.TrScale := by
  intro K _ _ V _ _ _ _ M hM f
  have key : ∀ (c : K), IsIntegral ℤ c → ∀ x ∈ M, c • x ∈ M := by
    intro c hc x hx
    obtain ⟨r, rfl⟩ : ∃ r : NumberField.RingOfIntegers K, algebraMap _ K r = c := ⟨⟨c, hc⟩, rfl⟩
    rw [algebraMap_smul]
    exact M.smul_mem r hx
  have hint : ∀ n : ℤ, IsIntegral ℤ (n : K) := fun n => isIntegral_algebraMap (R := ℤ) (x := n)
  have hf : f ∈ Submodule.span K (↑M : Set V) := hM ▸ Submodule.mem_top
  induction hf using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have e : ((a * b : ℤ) : K) • (x + y) = (b : K) • ((a : K) • x) + (a : K) • ((b : K) • y) := by
      rw [smul_add, smul_smul, smul_smul, Int.cast_mul, mul_comm (b : K)]
    rw [e]
    exact M.add_mem (key _ (hint b) _ hx) (key _ (hint a) _ hy)
  | smul c x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    have halg : IsAlgebraic ℤ c :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic c)
    obtain ⟨b, hb, hc⟩ := halg.exists_integral_multiple
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have e : ((a * b : ℤ) : K) • (c • x) = (b • c) • ((a : K) • x) := by
      rw [smul_smul, smul_smul, Int.cast_mul, zsmul_eq_mul]
      congr 1
      ring
    rw [e]
    exact key _ hc _ hx
end