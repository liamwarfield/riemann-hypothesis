module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SummableNormSiegelThetaSeriesTerms
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SummableProdPi
namespace GlobalTheory.SummableProdPi

theorem summable_prod_pi {J A : Type} [inst : Fintype J] (f : J → A → ℝ)
    (h0 : ∀ (j : J) (a : A), (0 : ℝ) ≤ f j a) (hs : ∀ j : J, Summable (f j)) :
    Summable fun (n : J → A) ↦ ∏ j : J, f j (n j) := by
  classical
  have hnn : ∀ n : J → A, 0 ≤ ∏ j : J, f j (n j) :=
    fun n => Finset.prod_nonneg fun j _ => h0 j (n j)
  refine summable_of_sum_le (c := ∏ j : J, ∑' a, f j a) hnn fun s => ?_
  have hsub : s ⊆ Fintype.piFinset (fun j : J => s.image (fun n : J → A => n j)) := by
    intro n hn
    rw [Fintype.mem_piFinset]
    intro j
    exact Finset.mem_image_of_mem _ hn
  calc ∑ n ∈ s, ∏ j : J, f j (n j)
      ≤ ∑ n ∈ Fintype.piFinset (fun j : J => s.image (fun n : J → A => n j)),
          ∏ j : J, f j (n j) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => hnn n
    _ = ∏ j : J, ∑ a ∈ s.image (fun n : J → A => n j), f j a :=
        (Finset.prod_univ_sum (fun j : J => s.image (fun n : J → A => n j)) f).symm
    _ ≤ ∏ j : J, ∑' a, f j a := by
        apply Finset.prod_le_prod₀
        · intro j _
          exact Finset.sum_nonneg fun a _ => h0 j a
        · intro j _
          exact (hs j).sum_le_tsum _ fun a _ => h0 j a

end GlobalTheory.SummableProdPi
end

open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.SiegelSum

theorem summable_pi_prod {J A : Type} [Fintype J] (f : J → A → ℝ) (h0 : ∀ j a, 0 ≤ f j a)
    (hs : ∀ j, Summable (f j)) : Summable fun n : J → A => ∏ j, f j (n j) := by
  first
  | exact @_root_.GlobalTheory.SummableProdPi.summable_prod_pi
  | exact _root_.GlobalTheory.SummableProdPi.summable_prod_pi
  | (apply _root_.GlobalTheory.SummableProdPi.summable_prod_pi <;> assumption)
  | (intros; apply _root_.GlobalTheory.SummableProdPi.summable_prod_pi <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SummableProdPi.summable_prod_pi <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SummableProdPi.summable_prod_pi ..)

theorem exists_mul_dotProduct_le {ι : Type} [Fintype ι] {Y : Matrix ι ι ℝ} (hY : Y.PosDef) :
    ∃ c > 0, ∀ x : ι → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (Y *ᵥ x) := by
  have hc : Continuous fun x : ι → ℝ => x ⬝ᵥ (Y *ᵥ x) := by
    simp only [dotProduct, mulVec]
    fun_prop
  obtain ⟨c, hc0, hcl⟩ := (isCompact_sphere (0 : ι → ℝ) 1).exists_forall_le'
    hc.continuousOn (a := 0) (fun q hq => by
      have hx0 : q ≠ 0 := by
        intro h0
        simp [h0] at hq
      simpa using hY.dotProduct_mulVec_pos hx0)
  refine ⟨c / (Fintype.card ι + 1), by positivity, fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h1 := hcl (‖x‖⁻¹ • x) (by simp [norm_smul, hn.ne'])
  simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h1
  have h2 : c * ‖x‖ ^ 2 ≤ x ⬝ᵥ (Y *ᵥ x) := by
    have := mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖x‖)
    refine this.trans_eq ?_
    field_simp
  have h3 : x ⬝ᵥ x ≤ (Fintype.card ι + 1) * ‖x‖ ^ 2 := by
    have : x ⬝ᵥ x ≤ ∑ _i : ι, ‖x‖ ^ 2 := Finset.sum_le_sum fun i _ => by
      have := norm_le_pi_norm x i
      rw [Real.norm_eq_abs] at this
      rw [← sq, ← sq_abs]
      gcongr
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    nlinarith [sq_nonneg ‖x‖]
  calc c / (Fintype.card ι + 1) * (x ⬝ᵥ x) ≤ c / (Fintype.card ι + 1) *
        ((Fintype.card ι + 1) * ‖x‖ ^ 2) := by gcongr
    _ = c * ‖x‖ ^ 2 := by field_simp
    _ ≤ _ := h2

theorem exists_int_of_intM {κ ι : Type} [Fintype κ] [Fintype ι] {R : ℕ} (hR : 0 < R)
    {x : Matrix κ ι ℚ} (hx : IntM ((R : ℚ) • x)) :
    ∃ n : κ → ι → ℤ, x = Matrix.of fun k i => (n k i : ℚ) / R := by
  have : ∀ k i, ∃ n : ℤ, (n : ℚ) = R * x k i := fun k i => by
    have := IsIntegrallyClosed.isIntegral_iff.1 (hx k i)
    simpa using this
  choose n hn using this
  refine ⟨n, ?_⟩
  ext k i
  have : (R : ℚ) ≠ 0 := by positivity
  simp only [of_apply, hn]
  field_simp

theorem exists_bound {κ ι : Type} [Fintype κ] [Fintype ι] {R : ℕ} (hR : 0 < R)
    {φ : Matrix κ ι ℚ → ℂ} (h : HasLevel R φ) : ∃ M, ∀ x, ‖φ x‖ ≤ M := by
  classical
  let g : (κ → ι → Fin (R * R)) → ℝ := fun r => ‖φ (Matrix.of fun k i => ((r k i : ℕ) : ℚ) / R)‖
  refine ⟨∑ r, g r, fun x => ?_⟩
  by_cases hx : φ x = 0
  · rw [hx, norm_zero]; exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  obtain ⟨n, rfl⟩ := exists_int_of_intM hR (h.1 x hx)
  have hRR : (0 : ℤ) < (R : ℤ) * R := by positivity
  let r : κ → ι → Fin (R * R) := fun k i => ⟨(n k i % (R * R)).toNat, by
    have := Int.emod_lt_of_pos (n k i) hRR
    have := Int.emod_nonneg (n k i) hRR.ne'
    zify; rw [Int.toNat_of_nonneg this]; assumption⟩
  have key := h.2 (Matrix.of fun k i => ((r k i : ℕ) : ℚ) / R)
    (Matrix.of fun k i => ((n k i / (R * R) : ℤ) : ℚ)) (fun k i => isIntegral_algebraMap (x := n k i / (R * R)))
  have he : (Matrix.of fun k i => (n k i : ℚ) / R) =
      (Matrix.of fun k i => ((r k i : ℕ) : ℚ) / R) +
        (R : ℚ) • (Matrix.of fun k i => ((n k i / (R * R) : ℤ) : ℚ)) := by
    ext k i
    have h1 : (((r k i : ℕ) : ℤ)) = n k i % (R * R) :=
      Int.toNat_of_nonneg (Int.emod_nonneg (n k i) hRR.ne')
    have h2 := Int.emod_add_mul_ediv (n k i) (R * R)
    rw [← h1] at h2
    have h3 : ((r k i : ℕ) : ℚ) + R * R * ((n k i / (R * R) : ℤ) : ℚ) = n k i := by
      exact_mod_cast h2
    have : (R : ℚ) ≠ 0 := by positivity
    simp only [of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← h3]
    field_simp
  rw [he, key]
  exact Finset.single_le_sum (f := g) (fun _ _ => norm_nonneg _) (Finset.mem_univ r)

theorem sum_le_im {ι : Type} [Fintype ι] {τ : Matrix ι ι ℂ} {c S : ℝ}
    (hc : ∀ x : ι → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (τ.map Complex.im *ᵥ x)) (ζ : ι → ℂ)
    (hS : ∀ i, |(ζ i).im| ≤ S) (v : ι → ℚ) :
    ∑ i, (c * (v i : ℝ) ^ 2 - 2 * S * |(v i : ℝ)|) ≤
      (qv v ⬝ᵥ τ *ᵥ qv v + 2 * (qv v ⬝ᵥ ζ)).im := by
  have h1 : (qv v ⬝ᵥ τ *ᵥ qv v).im =
      (fun i => (v i : ℝ)) ⬝ᵥ (τ.map Complex.im *ᵥ fun i => (v i : ℝ)) := by
    simp [dotProduct, mulVec, qv, Complex.im_sum, Complex.re_sum]
  have h2 : (2 * (qv v ⬝ᵥ ζ)).im = ∑ i, 2 * ((v i : ℝ) * (ζ i).im) := by
    simp [dotProduct, qv, Complex.im_sum, Finset.mul_sum]
  rw [Complex.add_im, h1, h2, Finset.sum_sub_distrib, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  refine add_le_add (le_trans (le_of_eq ?_) (hc _)) (Finset.sum_le_sum fun i _ => ?_)
  · simp [dotProduct, Finset.mul_sum, sq]
  · have h3 := neg_abs_le ((v i : ℝ) * (ζ i).im)
    rw [abs_mul] at h3
    nlinarith [hS i, abs_nonneg (v i : ℝ)]

theorem summable_norm_thetaTerm : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (φ : Matrix κ ι ℚ → ℂ), IsSB φ → ∀ τ ∈ Siegel ι, ∀ ζ : κ → ι → ℂ, Summable fun x : Matrix κ ι ℚ => ‖φ x * cexp (π * I * ∑ k, (qv (x k) ⬝ᵥ τ *ᵥ qv (x k) + 2 * (qv (x k) ⬝ᵥ ζ k)))‖ := by
  intro κ ι _ _ _ φ ⟨R, hR, h⟩ τ hτ ζ
  obtain ⟨M, hM⟩ := exists_bound hR h
  obtain ⟨c, hc0, hc⟩ := exists_mul_dotProduct_le hτ.2
  have hR0 : (R : ℝ) ≠ 0 := by positivity
  have hS : ∀ k i, |(ζ k i).im| ≤ ‖ζ‖ := fun k i =>
    (Complex.abs_im_le_norm _).trans ((norm_le_pi_norm (ζ k) i).trans (norm_le_pi_norm ζ k))
  let e : (κ → ι → ℤ) → Matrix κ ι ℚ := fun n => Matrix.of fun k i => (n k i : ℚ) / R
  have he : Function.Injective e := by
    intro m n hmn
    funext k i
    have h1 : (m k i : ℚ) / R = (n k i : ℚ) / R := congrFun (congrFun hmn k) i
    have : (R : ℚ) ≠ 0 := by positivity
    exact_mod_cast (div_left_inj' this).1 h1
  refine (he.summable_iff fun x hx => ?_).1 ?_
  · have : φ x = 0 := by
      by_contra h0
      obtain ⟨n, hn⟩ := exists_int_of_intM hR (h.1 x h0)
      exact hx ⟨n, hn.symm⟩
    simp [this]
  let f : ℤ → ℝ := fun n => Real.exp (-π * (c / R ^ 2 * n ^ 2 - 2 * (‖ζ‖ / R) * |n|))
  have hf : Summable f := by
    simpa [f] using summable_pow_mul_jacobiTheta₂_term_bound (‖ζ‖ / R)
      (T := c / R ^ 2) (by positivity) 0
  have hs : Summable fun n : κ → ι → ℤ => ∏ k, ∏ i, f (n k i) :=
    summable_pi_prod (fun (_ : κ) (m : ι → ℤ) => ∏ i, f (m i))
      (fun _ _ => Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)
      fun _ => summable_pi_prod (fun _ => f) (fun _ _ => (Real.exp_pos _).le) fun _ => hf
  refine (hs.mul_left M).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
  simp only [Function.comp_apply, norm_mul]
  refine mul_le_mul (hM _) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hM 0))
  simp only [f, ← Real.exp_sum, Complex.norm_exp, Real.exp_le_exp, ← Finset.mul_sum]
  have h1 : ∀ z : ℂ, (π * I * z).re = -π * z.im := fun z => by simp
  rw [h1, Complex.im_sum]
  refine mul_le_mul_of_nonpos_left (Finset.sum_le_sum fun k _ => ?_) (by linarith [Real.pi_pos])
  refine le_trans (le_of_eq ?_) (sum_le_im hc (ζ k) (hS k) (e n k))
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [e, of_apply, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, abs_div, Nat.abs_cast,
    Int.cast_abs]
  field_simp

end GlobalTheory.SW.SiegelSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FinsumQuotientOfLe
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.HaarLevel

noncomputable section

open NumberField

theorem finsum_quotient_of_le {A : Type} [AddCommGroup A] {s t : AddSubgroup A} (h : s ≤ t)
    (hn : s.relIndex t ≠ 0) (φ : A → ℂ) (hφ : ∀ x, ∀ y ∈ t, φ (x + y) = φ x)
    (hf : (Function.support fun q : A ⧸ t => φ q.out).Finite) :
    ∑ᶠ q : A ⧸ s, φ q.out = (s.relIndex t : ℂ) * ∑ᶠ q : A ⧸ t, φ q.out := by
  classical
  set e := AddSubgroup.quotientEquivProdOfLE h
  haveI : Finite (t ⧸ s.addSubgroupOf t) := Nat.finite_of_card_ne_zero hn
  haveI : Fintype (t ⧸ s.addSubgroupOf t) := Fintype.ofFinite _
  have h1 : ∀ q : A ⧸ s, φ q.out = φ (e q).1.out := by
    intro q
    have h2 : (e q).1 = (q.out : A ⧸ t) := by
      conv_lhs => rw [← QuotientAddGroup.out_eq' q]
      rfl
    have h3 : ((e q).1.out : A ⧸ t) = (q.out : A ⧸ t) := by
      rw [QuotientAddGroup.out_eq', h2]
    have := hφ (e q).1.out _ (QuotientAddGroup.eq.1 h3)
    rw [← this]; congr 1; abel
  simp_rw [h1]
  rw [finsum_comp_equiv e (f := fun p => φ p.1.out),
    finsum_eq_sum_of_support_subset (s := hf.toFinset ×ˢ Finset.univ), finsum_eq_sum _ hf,
    Finset.sum_product, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun q _ => ?_
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [AddSubgroup.relIndex, AddSubgroup.index, Nat.card_eq_fintype_card]
  · intro p hp
    simpa using hp

variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]

def incl (K κ ι : Type) [Field K] : Matrix κ ι (𝓞 K) →+ Matrix κ ι K :=
  (algebraMap (𝓞 K) K).toAddMonoidHom.mapMatrix

omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem intM_iff (x : Matrix κ ι K) : IntM x ↔ ∃ y, incl K κ ι y = x := by
  constructor
  · intro h
    exact ⟨fun k i => ⟨x k i, h k i⟩, rfl⟩
  · rintro ⟨y, rfl⟩ k i
    exact (y k i).2

omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem incl_inj : Function.Injective (incl K κ ι) := fun a b h => by
  ext k i
  exact congrFun (congrFun h k) i

omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem perSub_eq_range (R : ℕ) :
    perSub K κ ι R = ((incl K κ ι).comp (nsmulAddMonoidHom R)).range := by
  have : {x | ∃ y : Matrix κ ι K, IntM y ∧ x = (R : K) • y} =
      (((incl K κ ι).comp (nsmulAddMonoidHom R)).range : Set (Matrix κ ι K)) := by
    ext z
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, AddMonoidHom.mem_range, AddMonoidHom.comp_apply,
      nsmulAddMonoidHom_apply, map_nsmul, intM_iff, Nat.cast_smul_eq_nsmul]
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩; exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩; exact ⟨_, ⟨y, rfl⟩, rfl⟩
  rw [perSub, this, AddSubgroup.closure_eq]

omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem mem_perSub (R : ℕ) (x : Matrix κ ι K) :
    x ∈ perSub K κ ι R ↔ ∃ y, R • incl K κ ι y = x := by
  rw [perSub_eq_range]
  simp only [AddMonoidHom.mem_range, AddMonoidHom.comp_apply, nsmulAddMonoidHom_apply, map_nsmul]

theorem index_nsmul (R : ℕ) : (nsmulAddMonoidHom R : Matrix κ ι (𝓞 K) →+ _).range.index =
    R ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) := by
  rw [AddSubgroup.index_range_nsmul, Module.finrank_matrix, RingOfIntegers.rank]
  ring

omit [Fintype κ] [Fintype ι] in
theorem nsmul_cancel {R : ℕ} (hR : 0 < R) {x y : Matrix κ ι K} : R • x = R • y ↔ x = y := by
  rw [← Nat.cast_smul_eq_nsmul K, ← Nat.cast_smul_eq_nsmul K]
  exact (smul_right_injective _ (by exact_mod_cast hR.ne')).eq_iff

theorem relIndex_perSub (R S : ℕ) (hR : 0 < R) :
    (perSub K κ ι (R * S)).relIndex (perSub K κ ι R) =
      S ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) := by
  rw [perSub_eq_range R, ← AddSubgroup.index_comap, ← index_nsmul]
  congr 1
  ext y
  simp only [AddSubgroup.mem_comap, mem_perSub, AddMonoidHom.mem_range, AddMonoidHom.comp_apply,
    nsmulAddMonoidHom_apply]
  refine exists_congr fun z => ?_
  rw [mul_smul, map_nsmul, nsmul_cancel hR, ← map_nsmul, incl_inj.eq_iff]

omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem perSub_le (R S : ℕ) : perSub K κ ι (R * S) ≤ perSub K κ ι R := by
  intro x hx
  obtain ⟨y, rfl⟩ := (mem_perSub _ _).1 hx
  exact (mem_perSub _ _).2 ⟨S • y, by rw [map_nsmul, mul_smul]⟩

omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem periodic {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) (x : Matrix κ ι K) :
    ∀ y ∈ perSub K κ ι R, φ (x + y) = φ x := by
  intro y hy
  obtain ⟨z, rfl⟩ := (mem_perSub _ _).1 hy
  rw [← Nat.cast_smul_eq_nsmul K]
  exact h.2 x _ ((intM_iff _).2 ⟨z, rfl⟩)

theorem finite_support {R : ℕ} {φ : Matrix κ ι K → ℂ} (hR : 0 < R) (h : HasLevel R φ) :
    (Function.support fun q : Matrix κ ι K ⧸ perSub K κ ι R => φ q.out).Finite := by
  have hK : (R : K) ≠ 0 := by exact_mod_cast hR.ne'
  set f : Matrix κ ι (𝓞 K) →+ Matrix κ ι K ⧸ perSub K κ ι R :=
    (QuotientAddGroup.mk' (perSub K κ ι R)).comp
      ((DistribSMul.toAddMonoidHom (Matrix κ ι K) (R : K)⁻¹).comp (incl K κ ι)) with hf
  have hfa : ∀ y, f y = (((R : K)⁻¹ • incl K κ ι y : Matrix κ ι K) :
    Matrix κ ι K ⧸ perSub K κ ι R) := fun _ => rfl
  have hker : (nsmulAddMonoidHom (R * R) : Matrix κ ι (𝓞 K) →+ _).range ≤ f.ker := by
    rintro _ ⟨y, rfl⟩
    rw [AddMonoidHom.mem_ker, hfa, QuotientAddGroup.eq_zero_iff, mem_perSub]
    refine ⟨y, ?_⟩
    rw [nsmulAddMonoidHom_apply, map_nsmul, mul_smul, ← Nat.cast_smul_eq_nsmul K R (R • _),
      smul_smul, inv_mul_cancel₀ hK, one_smul]
  have hcard : Nat.card f.range ≠ 0 := by
    rw [← AddSubgroup.index_ker]
    refine ne_zero_of_dvd_ne_zero ?_ (AddSubgroup.index_dvd_of_le hker)
    rw [index_nsmul]
    positivity
  have hfin : Finite f.range := Nat.finite_of_card_ne_zero hcard
  refine (Set.toFinite (f.range : Set (Matrix κ ι K ⧸ perSub K κ ι R))).subset fun q hq => ?_
  obtain ⟨y, hy⟩ := (intM_iff _).1 (h.1 _ hq)
  refine ⟨y, ?_⟩
  rw [hfa, hy, smul_smul, inv_mul_cancel₀ hK, one_smul, QuotientAddGroup.out_eq']

theorem haarAt_mul {R : ℕ} {φ : Matrix κ ι K → ℂ} (hR : 0 < R) (h : HasLevel R φ) {S : ℕ}
    (hS : 0 < S) : haarAt (R * S) φ = haarAt R φ := by
  have hS' : (S : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  rw [haarAt, haarAt, finsum_quotient_of_le (perSub_le R S)
    (by rw [relIndex_perSub R S hR]; positivity) φ (periodic h) (finite_support hR h),
    relIndex_perSub R S hR]
  push_cast
  rw [mul_pow]
  field_simp

end

end GlobalTheory.SW.HaarLevel

namespace GlobalTheory.SW

theorem haar_eq_haarAt : ∀ (K κ ι : Type) [Field K] [NumberField K] [Fintype κ] [Fintype ι] (R : ℕ) (φ : Matrix κ ι K → ℂ), 0 < R → HasLevel R φ → haar φ = haarAt R φ ∧ (Function.support fun q : Matrix κ ι K ⧸ perSub K κ ι R => φ q.out).Finite := by
  intro K κ ι _ _ _ _ R φ hR h
  refine ⟨?_, HaarLevel.finite_support hR h⟩
  have hs : IsSB φ := ⟨R, hR, h⟩
  rw [haar, dite_eq_left hs, ← HaarLevel.haarAt_mul hR h hs.choose_spec.1,
    ← HaarLevel.haarAt_mul hs.choose_spec.1 hs.choose_spec.2 hR, mul_comm]

end GlobalTheory.SW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticSiegelActionMemUpperHalfSpaceAndCocycl
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticSiegelActionMemUpperHalfSpaceAndCocycl
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SiegelAction

open scoped ComplexOrder

variable {ι : Type} [Fintype ι] [DecidableEq ι]


omit [DecidableEq ι] in
theorem posDef_ofReal {Y : Matrix ι ι ℝ} (h : Y.PosDef) :
    (Y.map (fun t => (t : ℂ))).PosDef := by
  have hs : ∀ i j, Y i j = Y j i := fun i j => by
    have := congrFun (congrFun h.isHermitian j) i
    simpa using this
  have hH : (Y.map (fun t => (t : ℂ))).IsHermitian := by
    ext i j
    simp [hs i j]
  refine PosDef.of_dotProduct_mulVec_pos hH fun v hv => ?_
  have hre : (star v ⬝ᵥ (Y.map (fun t => (t : ℂ))) *ᵥ v).re =
      star (fun i => (v i).re) ⬝ᵥ Y *ᵥ (fun i => (v i).re) +
      star (fun i => (v i).im) ⬝ᵥ Y *ᵥ (fun i => (v i).im) := by
    simp [dotProduct, mulVec, Finset.mul_sum, Finset.sum_add_distrib]
  have him : (star v ⬝ᵥ (Y.map (fun t => (t : ℂ))) *ᵥ v).im = 0 := by
    have := hH.im_star_dotProduct_mulVec_self v
    simpa using this
  rw [Complex.pos_iff, hre, him]
  refine ⟨?_, rfl⟩
  by_cases h1 : (fun i => (v i).re) = 0
  · have h2 : (fun i => (v i).im) ≠ 0 := fun h2 => hv (by
      ext i
      exact Complex.ext (congrFun h1 i) (congrFun h2 i))
    exact add_pos_of_nonneg_of_pos (h.posSemidef.dotProduct_mulVec_nonneg _)
      (h.dotProduct_mulVec_pos h2)
  · exact add_pos_of_pos_of_nonneg (h.dotProduct_mulVec_pos h1)
      (h.posSemidef.dotProduct_mulVec_nonneg _)


omit [DecidableEq ι] in
theorem posDef_of_ofReal {Y : Matrix ι ι ℝ} (h : (Y.map (fun t => (t : ℂ))).PosDef) :
    Y.PosDef := by
  have hH : Y.IsHermitian := by
    ext i j
    have := congrFun (congrFun h.isHermitian i) j
    simpa using this
  refine PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
  have hv : (fun i => (x i : ℂ)) ≠ 0 := fun h0 => hx (by
    ext i
    simpa using congrFun h0 i)
  have := (Complex.pos_iff.1 (h.dotProduct_mulVec_pos hv)).1
  simpa [dotProduct, mulVec, Finset.mul_sum] using this

omit [Fintype ι] [DecidableEq ι] in
theorem sub_conj_eq (τ : Matrix ι ι ℂ) :
    τ - τ.map conj = (2 * I) • τ.map (fun z => (z.im : ℂ)) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Complex.sub_conj]
  push_cast
  ring

theorem block_identity {A B C D τ τ' : Matrix ι ι ℂ}
    (h : fromBlocks A B C D ∈ symplecticGroup ι ℂ) (hτ : τ.IsSymm) :
    (A * τ + B)ᵀ * (C * τ' + D) - (C * τ + D)ᵀ * (A * τ' + B) = τ - τ' := by
  obtain ⟨h1, h2, h3⟩ := SymplecticGroup.fromBlocks_mem_iff.1 h
  have h4 : Dᵀ * A - Bᵀ * C = 1 := by simpa using congrArg transpose h3
  have : (A * τ + B)ᵀ * (C * τ' + D) - (C * τ + D)ᵀ * (A * τ' + B) =
      τ * (Aᵀ * C - Cᵀ * A) * τ' + τ * (Aᵀ * D - Cᵀ * B) - (Dᵀ * A - Bᵀ * C) * τ' +
        (Bᵀ * D - Dᵀ * B) := by
    simp only [transpose_add, transpose_mul, hτ.eq]
    noncomm_ring
  rw [this, h1, h2, h3, h4]
  simp

theorem act_complex {A B C D τ : Matrix ι ι ℂ}
    (h : fromBlocks A B C D ∈ symplecticGroup ι ℂ) (hA : A.map conj = A) (hB : B.map conj = B)
    (hC : C.map conj = C) (hD : D.map conj = D) (hτ : τ ∈ Siegel ι) :
    (C * τ + D).det ≠ 0 ∧ (A * τ + B) * (C * τ + D)⁻¹ ∈ Siegel ι ∧ ((C * τ + D)⁻¹ * C).IsSymm ∧
      (C * τ + D)ᵀ * ((A * τ + B) * (C * τ + D)⁻¹).map (fun z => (z.im : ℂ)) *
        (C * τ + D).map conj = τ.map (fun z => (z.im : ℂ)) := by
  obtain ⟨hs, hp⟩ := hτ
  have hY : (τ.map (fun z => (z.im : ℂ))).PosDef := posDef_ofReal hp
  have e1 := block_identity (τ' := τ) h hs
  have e2 := block_identity (τ' := τ.map conj) h hs
  have cP : (A * τ + B).map conj = A * τ.map conj + B := by
    rw [Matrix.map_add _ (map_add conj), Matrix.map_mul, hA, hB]
  have cQ : (C * τ + D).map conj = C * τ.map conj + D := by
    rw [Matrix.map_add _ (map_add conj), Matrix.map_mul, hC, hD]
  have e3 : C * (C * τ + D)ᵀ = (C * τ + D) * Cᵀ := by
    have ht := SymplecticGroup.transpose_mem h
    rw [fromBlocks_transpose] at ht
    obtain ⟨-, h2, -⟩ := SymplecticGroup.fromBlocks_mem_iff.1 ht
    simp only [transpose_transpose] at h2
    simp only [transpose_add, transpose_mul, hs.eq, Matrix.mul_add, Matrix.add_mul, h2,
      Matrix.mul_assoc]
  rw [← cP, ← cQ, sub_conj_eq] at e2
  rw [sub_self, sub_eq_zero] at e1
  generalize A * τ + B = P at *
  generalize C * τ + D = Q at *
  have h2I : (2 * I : ℂ) ≠ 0 := by simp
  have hQt : (Q.map conj)ᴴ = Qᵀ := by
    ext i j; simp
  have hdet : Q.det ≠ 0 := by
    intro h0
    have h0' : (Q.map conj).det = 0 := by
      have := RingHom.map_det (starRingEnd ℂ) Q
      rw [h0, map_zero] at this
      exact this.symm
    obtain ⟨v, hv, hQv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0'
    have hQv' : star v ᵥ* Qᵀ = 0 := by
      rw [← hQt, ← star_mulVec, hQv, star_zero]
    have hpos := hY.dotProduct_mulVec_pos hv
    have := congrArg (fun M => star v ⬝ᵥ M *ᵥ v) e2
    simp only [sub_mulVec, ← mulVec_mulVec, hQv, mulVec_zero, dotProduct_sub, dotProduct_zero,
      smul_mulVec, dotProduct_smul, smul_eq_mul] at this
    rw [dotProduct_mulVec (star v) Qᵀ, hQv', zero_dotProduct, sub_zero] at this
    exact hpos.ne' ((mul_eq_zero.1 this.symm).resolve_left h2I)
  have hu : IsUnit Q.det := hdet.isUnit
  have hut : IsUnit Qᵀ.det := by rwa [det_transpose]
  have hWQ : P * Q⁻¹ * Q = P := nonsing_inv_mul_cancel_right _ _ hu
  have hQW : Qᵀ * (P * Q⁻¹) = Pᵀ := by
    rw [← Matrix.mul_assoc, ← e1, mul_nonsing_inv_cancel_right _ _ hu]
  have hWs : (P * Q⁻¹).IsSymm := by
    rw [IsSymm, transpose_mul, transpose_nonsing_inv, ← hQW, nonsing_inv_mul_cancel_left _ _ hut]
  have hcW : (P * Q⁻¹).map conj * Q.map conj = P.map conj := by
    rw [← Matrix.map_mul, hWQ]
  have key : Qᵀ * (P * Q⁻¹).map (fun z => (z.im : ℂ)) * Q.map conj =
      τ.map (fun z => (z.im : ℂ)) := by
    apply smul_right_injective _ h2I
    simp only
    rw [← e2, ← Matrix.smul_mul, ← Matrix.mul_smul, ← sub_conj_eq, Matrix.mul_sub, Matrix.sub_mul,
      hQW, Matrix.mul_assoc Qᵀ, hcW]
  refine ⟨hdet, ⟨hWs, posDef_of_ofReal ?_⟩, ?_, key⟩
  · have huc : IsUnit (Q.map conj) := by
      rw [isUnit_iff_isUnit_det]
      have := RingHom.map_det (starRingEnd ℂ) Q
      exact this ▸ hu.map (starRingEnd ℂ)
    refine (Matrix.IsUnit.posDef_star_left_conjugate_iff huc).1 ?_
    rw [star_eq_conjTranspose, hQt]
    rw [← key] at hY
    exact hY
  · rw [IsSymm, transpose_mul, transpose_nonsing_inv]
    calc Cᵀ * Qᵀ⁻¹ = Q⁻¹ * (Q * Cᵀ) * Qᵀ⁻¹ := by rw [nonsing_inv_mul_cancel_left _ _ hu]
      _ = Q⁻¹ * C := by
        rw [← e3, Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hut]

theorem qm_conj {α β : Type} (A : Matrix α β ℚ) : (qm A).map conj = qm A := by
  ext i j; simp [qm]

theorem qm_add {α β : Type} (A B : Matrix α β ℚ) : qm (A + B) = qm A + qm B := by
  ext i j; simp [qm]

theorem qm_mul {α β γ : Type} [Fintype β] (A : Matrix α β ℚ) (B : Matrix β γ ℚ) :
    qm (A * B) = qm A * qm B := by
  ext i j; simp [qm, Matrix.mul_apply]

theorem qm_blocks_mem {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} (h : σ ∈ symplecticGroup ι ℚ) :
    fromBlocks (qm σ.toBlocks₁₁) (qm σ.toBlocks₁₂) (qm σ.toBlocks₂₁) (qm σ.toBlocks₂₂) ∈
      symplecticGroup ι ℂ := by
  have := SymplecticGroup.map_mem h (Rat.castHom ℂ)
  rw [← fromBlocks_toBlocks σ, fromBlocks_map] at this
  exact this

omit [DecidableEq ι] in
theorem toBlocks_mul (σ' σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) :
    (σ' * σ).toBlocks₁₁ = σ'.toBlocks₁₁ * σ.toBlocks₁₁ + σ'.toBlocks₁₂ * σ.toBlocks₂₁ ∧
    (σ' * σ).toBlocks₁₂ = σ'.toBlocks₁₁ * σ.toBlocks₁₂ + σ'.toBlocks₁₂ * σ.toBlocks₂₂ ∧
    (σ' * σ).toBlocks₂₁ = σ'.toBlocks₂₁ * σ.toBlocks₁₁ + σ'.toBlocks₂₂ * σ.toBlocks₂₁ ∧
    (σ' * σ).toBlocks₂₂ = σ'.toBlocks₂₁ * σ.toBlocks₁₂ + σ'.toBlocks₂₂ * σ.toBlocks₂₂ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;>
    simp [toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂, Matrix.mul_apply]

theorem symplectic_action : ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), σ ∈ Matrix.symplecticGroup ι ℚ → ∀ τ ∈ Siegel ι,
    (spDen σ τ).det ≠ 0 ∧ spAct σ τ ∈ Siegel ι ∧ ((spDen σ τ)⁻¹ * qm σ.toBlocks₂₁).IsSymm ∧
    (spDen σ τ)ᵀ * (spAct σ τ).map (fun z => (z.im : ℂ)) * (spDen σ τ).map conj =
      τ.map (fun z => (z.im : ℂ)) ∧
    ∀ σ' ∈ Matrix.symplecticGroup ι ℚ, spDen (σ' * σ) τ = spDen σ' (spAct σ τ) * spDen σ τ ∧
      spAct (σ' * σ) τ = spAct σ' (spAct σ τ) := by
  intro ι _ _ σ hσ τ hτ
  obtain ⟨h1, h2, h3, h4⟩ := act_complex (qm_blocks_mem hσ) (qm_conj _) (qm_conj _) (qm_conj _)
    (qm_conj _) hτ
  refine ⟨h1, h2, h3, h4, fun σ' _ => ?_⟩
  have hu : IsUnit (spDen σ τ).det := h1.isUnit
  have hWQ : spAct σ τ * spDen σ τ = qm σ.toBlocks₁₁ * τ + qm σ.toBlocks₁₂ :=
    nonsing_inv_mul_cancel_right _ _ hu
  obtain ⟨m1, m2, m3, m4⟩ := toBlocks_mul σ' σ
  have gen : ∀ X Y : Matrix ι ι ℚ,
      qm (X * σ.toBlocks₁₁ + Y * σ.toBlocks₂₁) * τ + qm (X * σ.toBlocks₁₂ + Y * σ.toBlocks₂₂) =
        (qm X * spAct σ τ + qm Y) * spDen σ τ := by
    intro X Y
    rw [Matrix.add_mul (qm X * spAct σ τ), Matrix.mul_assoc, hWQ]
    simp only [qm_add, qm_mul, spDen]
    noncomm_ring
  have hden : spDen (σ' * σ) τ = spDen σ' (spAct σ τ) * spDen σ τ := by
    rw [spDen, m3, m4, gen]; rfl
  refine ⟨hden, ?_⟩
  rw [spAct, hden, m1, m2, gen, Matrix.mul_inv_rev, Matrix.mul_assoc,
    mul_nonsing_inv_cancel_left _ _ hu]
  rfl

end GlobalTheory.SiegelAction
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplecticSiegelAction_mem_upperHalfSpace_and_cocycle : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), σ ∈ Matrix.symplecticGroup ι ℚ → ∀ τ ∈ Siegel ι, (spDen σ τ).det ≠ 0 ∧ spAct σ τ ∈ Siegel ι ∧ ((spDen σ τ)⁻¹ * qm σ.toBlocks₂₁).IsSymm ∧ (spDen σ τ)ᵀ * (spAct σ τ).map (fun z => (z.im : ℂ)) * (spDen σ τ).map conj = τ.map (fun z => (z.im : ℂ)) ∧ ∀ σ' ∈ Matrix.symplecticGroup ι ℚ, spDen (σ' * σ) τ = spDen σ' (spAct σ τ) * spDen σ τ ∧ spAct (σ' * σ) τ = spAct σ' (spAct σ τ) := by
  first | exact @GlobalTheory.SiegelAction.symplectic_action | exact GlobalTheory.SiegelAction.symplectic_action | (intros; apply GlobalTheory.SiegelAction.symplectic_action <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FoldrHolDEqIteratedFDeriv
open Complex
open scoped ComplexConjugate

namespace GlobalTheory.Ker.CreOp

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

noncomputable def holD (v : W) (Φ : W → ℂ) (z : W) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ Φ z v - I * fderiv ℝ Φ z (I • v))

theorem contDiff_fderiv_apply {Φ : W → ℂ} (h : ContDiff ℝ (⊤ : ℕ∞) Φ) (v : W) :
    ContDiff ℝ (⊤ : ℕ∞) fun z => fderiv ℝ Φ z v := (contDiff_infty_iff_fderiv.1 h).2.clm_apply contDiff_const

theorem contDiff_holD {Φ : W → ℂ} (h : ContDiff ℝ (⊤ : ℕ∞) Φ) (v : W) :
    ContDiff ℝ (⊤ : ℕ∞) (holD v Φ) := by
  show ContDiff ℝ _ fun z => (1 / 2 : ℂ) * (fderiv ℝ Φ z v - I * fderiv ℝ Φ z (I • v))
  exact contDiff_const.mul
    ((contDiff_fderiv_apply h v).sub (contDiff_const.mul (contDiff_fderiv_apply h (I • v))))

theorem holD_add {Φ Ψ : W → ℂ} (h : Differentiable ℝ Φ) (h' : Differentiable ℝ Ψ) (v : W) :
    holD v (fun z => Φ z + Ψ z) = fun z => holD v Φ z + holD v Ψ z := by
  funext z
  have hs : HasFDerivAt (fun y => Φ y + Ψ y) (fderiv ℝ Φ z + fderiv ℝ Ψ z) z :=
    (h z).hasFDerivAt.add (h' z).hasFDerivAt
  simp only [holD, hs.fderiv, ContinuousLinearMap.add_apply]
  ring

theorem exists_clm_of_antilinear [FiniteDimensional ℂ W] {lam : W → ℂ}
    (h1 : ∀ a b, lam (a + b) = lam a + lam b) (h2 : ∀ (t : ℂ) a, lam (t • a) = conj t * lam a) :
    ∃ T : W →L[ℝ] ℂ, lam = T := by
  have hr : ∀ (r : ℝ) (a : W), lam (r • a) = r • lam a := by
    intro r a
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) r a, h2]
    simp [Complex.real_smul]
  have : FiniteDimensional ℝ W := Module.Finite.trans ℂ W
  exact ⟨LinearMap.toContinuousLinearMap
    ({ toFun := lam, map_add' := h1, map_smul' := fun r a => by rw [RingHom.id_apply]; exact hr r a }
      : W →ₗ[ℝ] ℂ), rfl⟩

theorem holD_mul (T : W →L[ℝ] ℂ) (h2 : ∀ a, T (I • a) = -I * T a) {Φ : W → ℂ}
    (h : Differentiable ℝ Φ) (v : W) :
    holD v (fun z => T z * Φ z) = fun z => T z * holD v Φ z := by
  funext z
  have hT : HasFDerivAt (fun y => T y * Φ y) (T z • fderiv ℝ Φ z + Φ z • T) z :=
    T.hasFDerivAt.mul (h z).hasFDerivAt
  simp only [holD, hT.fderiv, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, h2]
  linear_combination (1 / 2 : ℂ) * Φ z * T v * I_sq

theorem holD_of_differentiableAt {Φ : W → ℂ} {z : W} (h : DifferentiableAt ℂ Φ z) (v : W) :
    holD v Φ z = fderiv ℂ Φ z v := by
  have e : fderiv ℝ Φ z = (fderiv ℂ Φ z).restrictScalars ℝ := h.fderiv_restrictScalars ℝ
  simp only [holD, e, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.map_smul,
    smul_eq_mul]
  linear_combination (-(1 / 2) : ℂ) * fderiv ℂ Φ z v * I_sq

variable {σ : Type} (u : σ → W)

theorem contDiff_foldr_holD {Φ : W → ℂ} (h : ContDiff ℝ (⊤ : ℕ∞) Φ) (M : List σ) :
    ContDiff ℝ (⊤ : ℕ∞) (M.foldr (fun l => holD (u l)) Φ) := by
  induction M with
  | nil => exact h
  | cons l M ih => exact contDiff_holD ih (u l)

theorem foldr_holD_eq_iteratedFDeriv [FiniteDimensional ℂ W] {θ : W → ℂ}
    (hθ : Differentiable ℂ θ) (M : List σ) :
    M.foldr (fun l => holD (u l)) θ =
      fun z => iteratedFDeriv ℂ M.length θ z fun k => u (M.get k) := by
  have hθ' : ContDiff ℂ ⊤ θ := GlobalTheory.SCV.contDiff_of_differentiable hθ ⊤
  induction M with
  | nil => funext z; simp
  | cons l M ih =>
    have hA : Differentiable ℂ (iteratedFDeriv ℂ M.length θ) :=
      hθ'.differentiable_iteratedFDeriv (WithTop.coe_lt_top _)
    funext z
    simp only [List.foldr_cons]
    rw [ih, holD_of_differentiableAt ((hA z).continuousMultilinear_apply_const _),
      fderiv_continuousMultilinear_apply_const_apply (hA z)]
    rfl

private theorem contDiff_list_sum_mul (R : List ((W →L[ℝ] ℂ) × (W → ℂ)))
    (hR : ∀ p ∈ R, ContDiff ℝ (⊤ : ℕ∞) p.2) :
    ContDiff ℝ (⊤ : ℕ∞) fun z => (R.map fun p => p.1 z * p.2 z).sum := by
  induction R with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact contDiff_const
  | cons p R ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (p.1.contDiff.mul (hR p (by simp))).add (ih fun q hq => hR q (by simp [hq]))

private theorem holD_list_sum_mul (R : List ((W →L[ℝ] ℂ) × (W → ℂ)))
    (hR : ∀ p ∈ R, (∀ a, p.1 (I • a) = -I * p.1 a) ∧ ContDiff ℝ (⊤ : ℕ∞) p.2) (v : W) :
    holD v (fun z => (R.map fun p => p.1 z * p.2 z).sum) =
      fun z => (R.map fun p => p.1 z * holD v p.2 z).sum := by
  induction R with
  | nil => funext z; simp [holD]
  | cons p R ih =>
    have hp := hR p (by simp)
    have hR' : ∀ q ∈ R, (∀ a, q.1 (I • a) = -I * q.1 a) ∧ ContDiff ℝ (⊤ : ℕ∞) q.2 :=
      fun q hq => hR q (by simp [hq])
    have hS := contDiff_list_sum_mul R fun q hq => (hR' q hq).2
    have hd : Differentiable ℝ p.2 := (contDiff_infty_iff_fderiv.1 hp.2).1
    simp only [List.map_cons, List.sum_cons]
    rw [holD_add (show Differentiable ℝ fun z => p.1 z * p.2 z from p.1.differentiable.mul hd)
      (contDiff_infty_iff_fderiv.1 hS).1,
      holD_mul p.1 hp.1 hd, ih hR']

theorem foldr_creation_zero : ∀ (σ W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] (u : σ → W) (lam : σ → W → ℂ) (θ : W → ℂ),
    (∀ l, (∀ a b, lam l (a + b) = lam l a + lam l b) ∧
      ∀ (t : ℂ) a, lam l (t • a) = conj t * lam l a) → Differentiable ℂ θ →
    ∀ Dl : σ → (W → ℂ) → W → ℂ,
      (∀ l Φ z, Dl l Φ z = lam l z * Φ z +
        (1 / 2 : ℂ) * (fderiv ℝ Φ z (u l) - I * fderiv ℝ Φ z (I • u l))) →
      ∀ L : List σ, ContDiff ℝ (⊤ : ℕ∞) (L.foldr Dl θ) ∧
        L.foldr Dl θ 0 = iteratedFDeriv ℂ L.length θ 0 fun k => u (L.get k) := by
  intro σ W _ _ _ u lam θ hlam hθ Dl hDl L
  choose T hT using fun l => exists_clm_of_antilinear (hlam l).1 (hlam l).2
  have hTI : ∀ l a, T l (I • a) = -I * T l a := by
    intro l a
    rw [← hT l, (hlam l).2, Complex.conj_I]
  have hθs : ContDiff ℝ (⊤ : ℕ∞) θ :=
    (GlobalTheory.SCV.contDiff_of_differentiable hθ _).restrict_scalars ℝ
  have step : ∀ l Φ, Dl l Φ = fun z => T l z * Φ z + holD (u l) Φ z := by
    intro l Φ
    funext z
    rw [hDl, ← hT l]
    rfl
  have hsm : ∀ L : List σ, ContDiff ℝ (⊤ : ℕ∞) (L.foldr Dl θ) := by
    intro L
    induction L with
    | nil => exact hθs
    | cons l L ih =>
      simp only [List.foldr_cons]
      rw [step]
      exact ((T l).contDiff.mul ih).add (contDiff_holD ih (u l))
  have key : ∀ L : List σ, ∃ R : List ((W →L[ℝ] ℂ) × (W → ℂ)),
      (∀ p ∈ R, (∀ a, p.1 (I • a) = -I * p.1 a) ∧ ContDiff ℝ (⊤ : ℕ∞) p.2) ∧
      L.foldr Dl θ = fun z =>
        L.foldr (fun l => holD (u l)) θ z + (R.map fun p => p.1 z * p.2 z).sum := by
    intro L
    induction L with
    | nil => exact ⟨[], by simp, by funext z; simp⟩
    | cons l L ih =>
      obtain ⟨R, hR, hE⟩ := ih
      refine ⟨(T l, L.foldr Dl θ) :: R.map (fun p => (p.1, holD (u l) p.2)), ?_, ?_⟩
      · intro p hp
        simp only [List.mem_cons, List.mem_map] at hp
        rcases hp with rfl | ⟨q, hq, rfl⟩
        · exact ⟨hTI l, hsm L⟩
        · exact ⟨(hR q hq).1, contDiff_holD (hR q hq).2 (u l)⟩
      · have hD := contDiff_foldr_holD u hθs L
        have hS := contDiff_list_sum_mul R fun p hp => (hR p hp).2
        have e : holD (u l) (L.foldr Dl θ) = fun z =>
            holD (u l) (L.foldr (fun l => holD (u l)) θ) z +
              (R.map fun p => p.1 z * holD (u l) p.2 z).sum := by
          rw [hE, holD_add (contDiff_infty_iff_fderiv.1 hD).1 (contDiff_infty_iff_fderiv.1 hS).1,
            holD_list_sum_mul R hR (u l)]
        funext z
        simp only [List.foldr_cons, step, e, List.map_cons, List.map_map, List.sum_cons,
          Function.comp_def]
        ring
  refine ⟨hsm L, ?_⟩
  obtain ⟨R, -, hE⟩ := key L
  have h0 : (R.map fun p => p.1 0 * p.2 0).sum = 0 :=
    List.sum_eq_zero fun x hx => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
      simp
  rw [hE]
  simp only [h0, add_zero]
  rw [foldr_holD_eq_iteratedFDeriv u hθ L]

end GlobalTheory.Ker.CreOp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplecticActionOfPeriodLatticeMap
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplecticActionOfPeriodLatticeMap
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SymplecticPeriods

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_symplectic_rows (F : ((ι → ℚ) × (ι → ℚ)) →ₗ[ℚ] ((ι → ℚ) × (ι → ℚ)))
    (hF : ∀ u v, (F u).1 ⬝ᵥ (F v).2 - (F u).2 ⬝ᵥ (F v).1 = u.1 ⬝ᵥ v.2 - u.2 ⬝ᵥ v.1) :
    ∃ σ ∈ Matrix.symplecticGroup ι ℚ, ∀ j,
      F (fun i => σ j (Sum.inr i), fun i => σ j (Sum.inl i)) =
        (fun i => (Pi.single j 1 : ι ⊕ ι → ℚ) (Sum.inr i),
          fun i => (Pi.single j 1 : ι ⊕ ι → ℚ) (Sum.inl i)) := by
  classical

  have hinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h0 : ∀ v : (ι → ℚ) × (ι → ℚ), u.1 ⬝ᵥ v.2 - u.2 ⬝ᵥ v.1 = 0 := fun v => by
      rw [← hF, hu]; simp
    ext i
    · simpa using h0 (0, Pi.single i 1)
    · simpa using h0 (Pi.single i 1, 0)
  have hsurj : Function.Surjective F := LinearMap.injective_iff_surjective.mp hinj

  choose r hr using fun j : ι ⊕ ι => hsurj
    ((fun i => (Pi.single j 1 : ι ⊕ ι → ℚ) (Sum.inr i)), fun i => (Pi.single j 1 : ι ⊕ ι → ℚ) (Sum.inl i))
  let σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ := Matrix.of fun j => Sum.elim (fun i => (r j).2 i) (fun i => (r j).1 i)
  have hrow : ∀ j, ((fun i => σ j (Sum.inr i)), (fun i => σ j (Sum.inl i))) = r j := fun j => rfl
  refine ⟨σ, ?_, fun j => by rw [hrow]; exact hr j⟩
  rw [SymplecticGroup.mem_iff]
  ext a b

  have e1 : (σ * Matrix.J ι ℚ * σᵀ) a b = (r a).1 ⬝ᵥ (r b).2 - (r a).2 ⬝ᵥ (r b).1 := by
    simp [Matrix.mul_apply, Matrix.J, Fintype.sum_sum_type, σ, dotProduct, Matrix.one_apply,
      Finset.sum_neg_distrib, sub_eq_add_neg, add_comm, Function.swap]
  rw [e1, ← hF, hr, hr]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Matrix.J, dotProduct, Pi.single_apply, Matrix.one_apply, eq_comm]

theorem exists_symplectic_action (ι : Type) [Fintype ι] [DecidableEq ι]
    (F : ((ι → ℚ) × (ι → ℚ)) →ₗ[ℚ] ((ι → ℚ) × (ι → ℚ)))
    (hF : ∀ u v, (F u).1 ⬝ᵥ (F v).2 - (F u).2 ⬝ᵥ (F v).1 = u.1 ⬝ᵥ v.2 - u.2 ⬝ᵥ v.1) :
    ∃ σ ∈ Matrix.symplecticGroup ι ℚ, ∀ τ ∈ Siegel ι, ∀ τ' M : Matrix ι ι ℂ, τ'.IsSymm →
      (∀ u, M *ᵥ (qv u.1 + τ *ᵥ qv u.2) = qv (F u).1 + τ' *ᵥ qv (F u).2) →
      τ' = spAct σ τ ∧ M = ((spDen σ τ)⁻¹)ᵀ := by
  obtain ⟨σ, hσ, hrows⟩ := exists_symplectic_rows F hF
  refine ⟨σ, hσ, fun τ hτ τ' M hτ' hM => ?_⟩
  have hτs : τ.IsSymm := hτ.1
  set X := spDen σ τ with hX
  set Y := qm σ.toBlocks₁₁ * τ + qm σ.toBlocks₁₂ with hY

  have colX : ∀ k, (fun l => Xᵀ l k) =
      qv (fun i => σ (Sum.inr k) (Sum.inr i)) + τ *ᵥ qv (fun i => σ (Sum.inr k) (Sum.inl i)) := by
    intro k; funext l
    simp only [hX, spDen, Matrix.transpose_apply, Matrix.add_apply, Matrix.mul_apply, qm, Matrix.map_apply,
      Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.of_apply, Pi.add_apply, qv, Matrix.mulVec, dotProduct]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hτs.apply m l, mul_comm]
  have columnBlock : ∀ k, (fun l => Yᵀ l k) =
      qv (fun i => σ (Sum.inl k) (Sum.inr i)) + τ *ᵥ qv (fun i => σ (Sum.inl k) (Sum.inl i)) := by
    intro k; funext l
    simp only [hY, Matrix.transpose_apply, Matrix.add_apply, Matrix.mul_apply, qm, Matrix.map_apply,
      Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.of_apply, Pi.add_apply, qv, Matrix.mulVec, dotProduct]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hτs.apply m l, mul_comm]

  have hA : M * Xᵀ = 1 := by
    ext i k
    have h := hM (fun i => σ (Sum.inr k) (Sum.inr i), fun i => σ (Sum.inr k) (Sum.inl i))
    rw [hrows (Sum.inr k), ← colX k] at h
    rw [show (M * Xᵀ) i k = (M *ᵥ fun l => Xᵀ l k) i from rfl, congrFun h i]
    simp [qv, Pi.single_apply, Matrix.one_apply, Matrix.mulVec, dotProduct]
    split_ifs <;> simp
  have hB : τ' = M * Yᵀ := by
    ext i k
    have h := hM (fun i => σ (Sum.inl k) (Sum.inr i), fun i => σ (Sum.inl k) (Sum.inl i))
    rw [hrows (Sum.inl k), ← columnBlock k] at h
    rw [show (M * Yᵀ) i k = (M *ᵥ fun l => Yᵀ l k) i from rfl, congrFun h i]
    simp [qv, Pi.single_apply, Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single k (fun j _ hj => by simp [hj]) (by simp)]
    simp
  have hMeq : M = (X⁻¹)ᵀ := by
    rw [Matrix.transpose_nonsing_inv, Matrix.inv_eq_left_inv hA]
  refine ⟨?_, hMeq⟩
  calc τ' = τ'ᵀ := hτ'.eq.symm
    _ = (M * Yᵀ)ᵀ := by rw [← hB]
    _ = Y * Mᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    _ = spAct σ τ := by rw [hMeq, Matrix.transpose_transpose]; rfl

end GlobalTheory.SymplecticPeriods
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplecticActionOfPeriodLatticeMapStatement
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplectic_action_of_period_lattice_map : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : ((ι → ℚ) × (ι → ℚ)) →ₗ[ℚ] ((ι → ℚ) × (ι → ℚ))), (∀ u v, (F u).1 ⬝ᵥ (F v).2 - (F u).2 ⬝ᵥ (F v).1 = u.1 ⬝ᵥ v.2 - u.2 ⬝ᵥ v.1) → ∃ σ ∈ Matrix.symplecticGroup ι ℚ, ∀ τ ∈ Siegel ι, ∀ τ' M : Matrix ι ι ℂ, τ'.IsSymm → (∀ u, M *ᵥ (qv u.1 + τ *ᵥ qv u.2) = qv (F u).1 + τ' *ᵥ qv (F u).2) → τ' = spAct σ τ ∧ M = ((spDen σ τ)⁻¹)ᵀ := by
  first | exact @GlobalTheory.SymplecticPeriods.exists_symplectic_action | exact GlobalTheory.SymplecticPeriods.exists_symplectic_action | (intros; apply GlobalTheory.SymplecticPeriods.exists_symplectic_action <;> assumption)
end
end
